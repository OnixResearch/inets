import InteractionNets.PeanoBound

/-! # Two agents added with nothing but their rules

The lazy caterer `cater`, `c 0 = 1` and `c (S x) = c x + S x`, and the
triangular numbers `tri`, `t 0 = 0` and `t (S x) = t x + S x`.  Each was
added to the system with two rules and nothing else; its theorem is the
theorem on recursion on the predecessor (`Peano.prim_computes`) applied
to its rules, with the theorem on constants for the zero and the adder
as combiner, and the theorems for the machine and for expressions follow
from the general ones.
-/

namespace INet

namespace Peano

/-! ### A new agent: the lazy caterer

The agent `cater` was added to the system with two rules and nothing
else: on a zero the rule of the factorial, and on a successor the rule
`Peano.caterSucc`, `c (S x) = c x + S x`.  The number `c n` is the most
pieces a pancake can be cut into with `n` straight cuts, `n (n + 1) / 2 + 1`
(`Peano.two_mul_cate`).  Its proof is the theorem on recursion on the
predecessor, with the adder as combiner. -/

/-- The lazy caterer's numbers. -/
def cate : Nat → Nat
  | 0 => 1
  | n + 1 => cate n + (n + 1)

/-- In closed form: `2 c n = n (n + 1) + 2`. -/
theorem two_mul_cate : ∀ n, 2 * cate n = n * (n + 1) + 2
  | 0 => rfl
  | n + 1 => by
    have ih := two_mul_cate n
    have e₁ : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (n + 1) := Nat.mul_succ _ _
    have e₂ : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := Nat.succ_mul _ _
    have e : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by omega
    show 2 * (cate n + (n + 1)) = (n + 1) * (n + 1 + 1) + 2
    rw [Nat.mul_add, ih, e]
    omega

/-- Its number of interactions: on a zero, one; on a successor, one, the
copy of the rest, the rest, and the addition. -/
def caterCost : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1 + 1 + caterCost n + (cate n + 1)

/-- The rule written for it is the template. -/
theorem caterSucc_eq : caterSucc = primSucc cater add := rfl

theorem rule_cater_succ : system.rule cater succ = some (primSucc cater add).toX.toRhs := rfl
theorem rule_cater_zero : system.rule cater zero = some facZero.toX.toRhs := rfl

theorem prim_cate (n : Nat) : prim 1 (fun m n => m + n) n = cate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show prim _ _ n + (n + 1) = cate n + (n + 1)
    rw [ih]

theorem primCost_cate (n : Nat) :
    primCost 1 (fun m _ => m + 1) 1 (fun m n => m + n) n = caterCost n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show n + 1 + 1 + primCost _ _ _ _ n + (prim _ _ n + 1) = caterCost (n + 1)
    rw [ih, prim_cate]
    rfl

/-- **The lazy caterer computes its numbers**, in any net, in
`caterCost n` steps: the theorem on recursion on the predecessor, with
the rule of the factorial on a zero and the adder as combiner. -/
theorem cater_computes : Computes1 cater cate caterCost :=
  (prim_computes rule_cater_succ ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ (zero1_facZero rule_cater_zero (by decide)) add_combines).congr
    prim_cate primCost_cate

/-- The net for `c 3`, with the result on the free port `([0], 0)`. -/
def caterThree : XNet Peano :=
  XNet.ofWires [([1], cater), ([2], succ), ([3], succ), ([4], succ), ([5], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([2], 1), ([3], 0)), (([3], 1), ([4], 0)), (([4], 1), ([5], 0)),
      (([1], 1), ([0], 0))]

/-- The reducer stops on `c 3` after `caterCost 3 = 20` steps, on seven
successors and a zero: `c 3 = 7`. -/
example : (caterThree.normalize xsys 100).map (fun r => (r.2, r.1.agents.map (·.2))) =
    some (caterCost 3, [succ, succ, succ, zero, succ, succ, succ, succ]) := by
  decide +kernel

example : cate 3 = 7 := rfl

/-- **The lazy caterer on the machine**: with any number of threads and
any schedule, a run on the net for `c n` that is at rest has made exactly
`caterCost n` interactions and holds the numeral `c n`. -/
theorem cater_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (unaryNet cater n) nt).trace xsys σ i).2 = caterCost n ∧
      IsNum ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (cate n) :=
  unary_rest cater_computes rfl (by decide) n hnt σ hr

/-- **The lazy caterer under any fair schedule**: the run comes to rest
after `caterCost n` interactions with the numeral `c n` in memory. -/
theorem cater_fair (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (unaryNet cater n) nt).trace xsys σ i).2 = caterCost n ∧
      IsNum ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (cate n) :=
  unary_fair cater_computes rfl (by decide) n hnt σ hfair


/-- The lazy caterer, through the theorem on recursion. -/
def caterOp : Op1 := Op1.ofComputes cater_computes rfl (by decide) (by decide)


/-! ### Examples -/

/-- `3! + c 2` has the value `10` and costs `70` interactions: `52` for
the factorial, `11` for the caterer and `7` for the addition. -/
example : (GExpr.app2 addOp (.app1 facOp (.lit 3)) (.app1 caterOp (.lit 2))).eval = 10 ∧
    (GExpr.app2 addOp (.app1 facOp (.lit 3)) (.app1 caterOp (.lit 2))).cost = 70 := by
  decide

set_option maxRecDepth 100000 in
/-- `c 2 + 2!` run by two threads taking turns: after 2500 actions they
are at rest and the result read is `6`. -/
example : (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).run 2 2500 =
    some 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same on the machine: after 2500 actions both threads are at rest
and they have made 41 interactions, the cost of the expression. -/
example :
    ((XMach.init (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).net 2).trace
      xsys (fun j => j % 2) 2500).1.resting = true ∧
    ((XMach.init (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).net 2).trace
      xsys (fun j => j % 2) 2500).2 = 41 ∧
    (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).cost = 41 := by
  decide +kernel


/-! ### A new agent with a new constant: the triangular numbers

The agent `tri` was added to the system with two rules: on a zero a new
zero on the result (`Peano.triZero`), a rule no other agent has, and on a
successor `t (S x) = t x + S x` (`Peano.triSucc`).  Its theorem is the
theorem on recursion on the predecessor, with `Peano.zero1_const` for
the zero and the adder as combiner. -/

/-- The triangular numbers. -/
def triN : Nat → Nat
  | 0 => 0
  | n + 1 => triN n + (n + 1)

/-- In closed form: `2 t n = n (n + 1)`. -/
theorem two_mul_triN : ∀ n, 2 * triN n = n * (n + 1)
  | 0 => rfl
  | n + 1 => by
    have ih := two_mul_triN n
    have e₁ : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (n + 1) := Nat.mul_succ _ _
    have e₂ : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := Nat.succ_mul _ _
    show 2 * (triN n + (n + 1)) = (n + 1) * (n + 1 + 1)
    rw [Nat.mul_add, ih]
    omega

/-- Its number of interactions: on a zero, one; on a successor, one, the
copy of the rest, the rest, and the addition. -/
def triCost : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1 + 1 + triCost n + (triN n + 1)

/-- The rule written for it on a successor is the template. -/
theorem triSucc_eq : triSucc = primSucc tri add := rfl

theorem prim_tri (n : Nat) : prim 0 (fun m n => m + n) n = triN n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show prim _ _ n + (n + 1) = triN n + (n + 1)
    rw [ih]

theorem primCost_tri (n : Nat) :
    primCost 1 (fun m _ => m + 1) 0 (fun m n => m + n) n = triCost n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show n + 1 + 1 + primCost _ _ _ _ n + (prim _ _ n + 1) = triCost (n + 1)
    rw [ih, prim_tri]
    rfl

/-- **The triangular numbers are computed**, in any net, in `triCost n`
steps: the theorem on recursion on the predecessor, with the theorem on
constants for the zero and the adder as combiner. -/
theorem tri_computes : Computes1 tri triN triCost :=
  (prim_computes (show system.rule tri succ = some (primSucc tri add).toX.toRhs from rfl)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (zero1_const (show system.rule tri zero = some triZero.toX.toRhs from rfl) (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide))
    add_combines).congr prim_tri primCost_tri

/-- The triangular numbers as an operator. -/
def triOp : Op1 := Op1.ofComputes tri_computes rfl (by decide) (by decide)

/-- **The triangular numbers on the machine**: with any number of threads
and any schedule, a run on the net for `t n` that is at rest has made
exactly `triCost n` interactions and holds `t n`. -/
theorem tri_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (unaryNet tri n) nt).trace xsys σ i).2 = triCost n ∧
      IsNum ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (triN n) :=
  triOp.rest n hnt σ hr

/-- **The triangular numbers under any fair schedule.** -/
theorem tri_fair (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (unaryNet tri n) nt).trace xsys σ i).2 = triCost n ∧
      IsNum ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (triN n) :=
  triOp.fair n hnt σ hfair

/-- The reducer on the net for `t 4` stops after `triCost 4` steps on ten
successors and a zero: `t 4 = 10`. -/
example : ((unaryNet tri 4).normalize xsys 200).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) =
    some (triCost 4, 10, 1, 11) := by
  decide +kernel

/-- `t (2 + 1) * 3!`, an expression with all of them: `6 * 6 = 36`. -/
example : (GExpr.app2 mulOp (.app1 triOp (.app2 addOp (.lit 2) (.lit 1)))
    (.app1 facOp (.lit 3))).eval = 36 := by
  decide

end Peano

end INet
