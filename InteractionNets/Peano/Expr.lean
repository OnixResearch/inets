import InteractionNets.Peano.GExpr

/-! # Every expression of additions, multiplications and powers

Expressions built from numerals with `+`, `*` and `^` (`Peano.PExpr`).
Each is an expression over operators (`PExpr.toG`), with the adder, the
multiplier and the power as operators, and with the same net, value and
cost; so every theorem on expressions over operators holds for it:
the net computes the value in exactly `PExpr.cost` interactions
(`PExpr.good`), on the machine under any schedule (`PExpr.rest`) and
under fair ones (`PExpr.fair`), and it can be run and read
(`PExpr.run_sound`, `PExpr.run_complete`).
-/

namespace INet

namespace Peano

open Core

/-! ### Expressions -/

/-- **Expressions**: numerals, additions, multiplications and powers.
`pow b e` is `b` to the power `e`. -/
inductive PExpr
  | lit (n : Nat)
  | add (e₁ e₂ : PExpr)
  | mul (e₁ e₂ : PExpr)
  | pow (b e : PExpr)

/-- The value of an expression. -/
def PExpr.eval : PExpr → Nat
  | .lit n => n
  | .add e₁ e₂ => e₁.eval + e₂.eval
  | .mul e₁ e₂ => e₁.eval * e₂.eval
  | .pow b e => b.eval ^ e.eval

/-- The interactions of an expression: for each addition, one more than
the value of its first argument; for each multiplication, `prodCost` of
the values of its two arguments; for each power, `powCost` of the values
of the exponent and the base. -/
def PExpr.cost : PExpr → Nat
  | .lit _ => 0
  | .add e₁ e₂ => e₁.cost + e₂.cost + (e₁.eval + 1)
  | .mul e₁ e₂ => e₁.cost + e₂.cost + prodCost e₁.eval e₂.eval
  | .pow b e => e.cost + b.cost + powCost e.eval b.eval

/-- The free port that carries the result. -/
def PExpr.res : PExpr → Port
  | .lit _ => ([0], 0)
  | .add _ _ => ([0, 2], 0)
  | .mul _ _ => ([0, 2], 0)
  | .pow _ _ => ([0, 2], 0)

/-- **The net of an expression.**  A numeral is its net.  An addition, a
multiplication or a power is the nets of its two arguments and an
operator that waits, side by side, with the result of each argument wired
to a port of the operator; for a power the exponent is the first. -/
def PExpr.net : PExpr → XNet Peano
  | .lit n => Peano.lit n
  | .add e₁ e₂ => opNet Peano.add e₁.net e₂.net e₁.res e₂.res
  | .mul e₁ e₂ => opNet Peano.mul e₁.net e₂.net e₁.res e₂.res
  | .pow b e => opNet Peano.pow e.net b.net e.res b.res

/-! ### As expressions over operators -/

/-- An expression of `+`, `*` and `^` as an expression over operators;
for a power the exponent is the first argument. -/
def PExpr.toG : PExpr → GExpr
  | .lit n => .lit n
  | .add e₁ e₂ => .app2 addOp e₁.toG e₂.toG
  | .mul e₁ e₂ => .app2 mulOp e₁.toG e₂.toG
  | .pow b e => .app2 powOp e.toG b.toG

theorem PExpr.toG_eval : ∀ e : PExpr, e.toG.eval = e.eval
  | .lit _ => rfl
  | .add e₁ e₂ => by
    show e₁.toG.eval + e₂.toG.eval = e₁.eval + e₂.eval
    rw [e₁.toG_eval, e₂.toG_eval]
  | .mul e₁ e₂ => by
    show e₁.toG.eval * e₂.toG.eval = e₁.eval * e₂.eval
    rw [e₁.toG_eval, e₂.toG_eval]
  | .pow b e => by
    show b.toG.eval ^ e.toG.eval = b.eval ^ e.eval
    rw [b.toG_eval, e.toG_eval]

theorem PExpr.toG_cost : ∀ e : PExpr, e.toG.cost = e.cost
  | .lit _ => rfl
  | .add e₁ e₂ => by
    show e₁.toG.cost + e₂.toG.cost + (e₁.toG.eval + 1) = e₁.cost + e₂.cost + (e₁.eval + 1)
    rw [e₁.toG_cost, e₂.toG_cost, e₁.toG_eval]
  | .mul e₁ e₂ => by
    show e₁.toG.cost + e₂.toG.cost + prodCost e₁.toG.eval e₂.toG.eval =
      e₁.cost + e₂.cost + prodCost e₁.eval e₂.eval
    rw [e₁.toG_cost, e₂.toG_cost, e₁.toG_eval, e₂.toG_eval]
  | .pow b e => by
    show e.toG.cost + b.toG.cost + powCost e.toG.eval b.toG.eval =
      e.cost + b.cost + powCost e.eval b.eval
    rw [e.toG_cost, b.toG_cost, e.toG_eval, b.toG_eval]

theorem PExpr.toG_res : ∀ e : PExpr, e.toG.res = e.res
  | .lit _ => rfl
  | .add _ _ => rfl
  | .mul _ _ => rfl
  | .pow _ _ => rfl

/-- **The same nets.** -/
theorem PExpr.toG_net : ∀ e : PExpr, e.toG.net = e.net
  | .lit _ => rfl
  | .add e₁ e₂ => by
    show opNet Peano.add e₁.toG.net e₂.toG.net e₁.toG.res e₂.toG.res =
      opNet Peano.add e₁.net e₂.net e₁.res e₂.res
    rw [e₁.toG_net, e₂.toG_net, e₁.toG_res, e₂.toG_res]
  | .mul e₁ e₂ => by
    show opNet Peano.mul e₁.toG.net e₂.toG.net e₁.toG.res e₂.toG.res =
      opNet Peano.mul e₁.net e₂.net e₁.res e₂.res
    rw [e₁.toG_net, e₂.toG_net, e₁.toG_res, e₂.toG_res]
  | .pow b e => by
    show opNet Peano.pow e.toG.net b.toG.net e.toG.res b.toG.res =
      opNet Peano.pow e.net b.net e.res b.res
    rw [e.toG_net, b.toG_net, e.toG_res, b.toG_res]

/-- **The net of an expression is well formed and computes its value**,
in the interactions counted by `PExpr.cost`. -/
theorem PExpr.good (e : PExpr) : e.net.toNet.WF ar ∧ Evals e.net.toNet e.cost e.eval e.res := by
  rw [← e.toG_net, ← e.toG_cost, ← e.toG_eval, ← e.toG_res]
  exact e.toG.good

/-- **Every expression comes out right, whatever the threads do.**  With
any number of threads and any schedule, a run on the net of an expression
that is at rest has made the interactions counted by `PExpr.cost`, and
the memory has the numeral of the value on the free port. -/
theorem PExpr.rest (e : PExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  rw [← e.toG_net] at hr ⊢
  rw [← e.toG_cost, ← e.toG_res, ← e.toG_eval]
  exact e.toG.rest hnt σ hr

/-- **Every expression under a fair schedule.** -/
theorem PExpr.fair (e : PExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  rw [← e.toG_net, ← e.toG_cost, ← e.toG_res, ← e.toG_eval]
  exact e.toG.fair hnt σ hfair

/-- **Run an expression.**  `nt` threads take turns on the net of the
expression for `steps` actions; if they are then at rest, the numeral on
the free port is read. -/
def PExpr.run (e : PExpr) (nt steps : Nat) : Option Nat :=
  XNet.runRead xsys zero succ e.net e.res nt steps

theorem PExpr.run_toG (e : PExpr) (nt steps : Nat) : e.toG.run nt steps = e.run nt steps := by
  show XNet.runRead xsys zero succ e.toG.net e.toG.res nt steps = _
  rw [e.toG_net, e.toG_res]
  rfl

/-- **Whatever the run returns is the value of the expression.** -/
theorem PExpr.run_sound (e : PExpr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.run nt steps = some v) : v = e.eval := by
  rw [← e.run_toG] at h
  rw [← e.toG_eval]
  exact e.toG.run_sound hnt h

/-- **Given enough actions, the run returns the value of the
expression.** -/
theorem PExpr.run_complete (e : PExpr) {nt : Nat} (hnt : 0 < nt) :
    ∃ s₀, ∀ s, s₀ ≤ s → e.run nt s = some e.eval := by
  obtain ⟨s₀, h⟩ := e.toG.run_complete hnt
  refine ⟨s₀, fun s hs => ?_⟩
  rw [← e.run_toG, ← e.toG_eval]
  exact h s hs

/-! ### Examples -/

/-- `(2 + 1) * (3 * 2)` has the value 18 and costs 81 interactions. -/
example : (PExpr.mul (.add (.lit 2) (.lit 1)) (.mul (.lit 3) (.lit 2))).eval = 18 ∧
    (PExpr.mul (.add (.lit 2) (.lit 1)) (.mul (.lit 3) (.lit 2))).cost = 81 := by
  decide

set_option maxRecDepth 100000 in
/-- `(2 * 2) + 1` on the machine, two threads taking turns: after 1000
actions both are at rest and they have made 23 interactions, the cost of
the expression. -/
example :
    ((XMach.init (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).net 2).trace xsys
      (fun j => j % 2) 1000).1.resting = true ∧
    ((XMach.init (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).net 2).trace xsys
      (fun j => j % 2) 1000).2 = 23 ∧
    (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).cost = 23 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `(2 * 2) + 1` run by two threads taking turns: after 1000 actions
they are at rest and the result read is `5`. -/
example : (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).run 2 1000 = some 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `2 * (1 + 2)` run by three threads taking turns: after 1500 actions
they are at rest and the result read is `6`. -/
example : (PExpr.mul (.lit 2) (.add (.lit 1) (.lit 2))).run 3 1500 = some 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `2 ^ (1 + 1)` run by two threads taking turns: after 2500 actions
they are at rest and the result read is `4`. -/
example : (PExpr.pow (.lit 2) (.add (.lit 1) (.lit 1))).run 2 2500 = some 4 := by
  decide +kernel

end Peano

end INet
