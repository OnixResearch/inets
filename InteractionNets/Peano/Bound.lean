import InteractionNets.Peano.Expr
import InteractionNets.Core.Bound

/-! # How many actions an expression of `Peano` takes

The rules of `Peano` are bounded (`Peano.xsys_bounded`), so the bounds
on actions hold for its expressions (`Peano.GExpr.rest_by`,
`Peano.GExpr.run_by`, `Peano.PExpr.run_by`).
-/

namespace INet

namespace Peano

open Core

/-- **The rules of `Peano` are bounded**: at most four new agents and
twelve ports. -/
theorem xsys_bounded : xsys.Bounded 4 12 := by
  intro α β R h
  cases α <;> cases β <;> (cases h <;> decide)

/-- **The net of an expression lists no name twice.** -/
theorem GExpr.net_nodup (e : GExpr) : (e.net.agents.map Prod.fst).Nodup := Core.GExpr.net_nodup e

/-- **How many actions an expression takes**, in `Peano`. -/
theorem GExpr.rest_by (e : GExpr) {nt : Nat} (hnt : 0 < nt) :
    ∀ i, nt * ((nt + e.cost) * e.net.passBound e.cost 4 12 + e.cost * (4 + 12 + 1) + 1) ≤ i →
      ((XMach.init e.net nt).trace xsys (fun j => j % nt) i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys (fun j => j % nt) i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys (fun j => j % nt) i).1.mem.toNet e.res
        e.eval :=
  Core.GExpr.rest_by xsys_bounded e hnt

/-- **The same for any schedule with a window**, in `Peano`. -/
theorem GExpr.rest_within (e : GExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {W : Nat}
    (hwin : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + W ∧ σ j = u) :
    ∀ i, W * ((nt + e.cost) * e.net.passBound e.cost 4 12 + e.cost * (4 + 12 + 1) + 1) ≤ i →
      ((XMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval :=
  Core.GExpr.rest_within xsys_bounded e hnt σ hwin

/-- **How many actions are enough to run an expression and read its
value**, in `Peano`. -/
theorem GExpr.run_by (e : GExpr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((nt + e.cost) * e.net.passBound e.cost 4 12 + e.cost * (4 + 12 + 1) + 1) ≤ s)
    (h₂ : e.net.wires.length + 12 * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.run nt s = some e.eval :=
  Core.GExpr.run_by xsys_bounded e hnt s h₁ h₂ h₃

/-- **The same for the expressions of `+`, `*` and `^`.** -/
theorem PExpr.run_by (e : PExpr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((nt + e.cost) * e.net.passBound e.cost 4 12 + e.cost * (4 + 12 + 1) + 1) ≤ s)
    (h₂ : e.net.wires.length + 12 * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.run nt s = some e.eval := by
  have h := GExpr.run_by e.toG hnt s (by rw [e.toG_cost, e.toG_net]; exact h₁)
    (by rw [e.toG_cost, e.toG_net]; exact h₂) (by rw [e.toG_eval]; exact h₃)
  rw [e.toG_eval] at h
  show XNet.runRead xsys zero succ e.net e.res nt s = some e.eval
  rw [← e.toG_net, ← e.toG_res]
  exact h

set_option maxRecDepth 100000 in
/-- `2! + 1` run by two threads taking turns, with the factorial as an
operator of one argument: after 1500 actions they are at rest and the
result read is `3`. -/
example : (Core.GExpr.app2 addOp (.app1 facOp (.lit 2)) (.lit 1) : GExpr).run 2 1500 =
    some 3 := by
  decide +kernel

end Peano

end INet
