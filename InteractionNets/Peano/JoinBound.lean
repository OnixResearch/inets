import InteractionNets.Peano.Bound
import InteractionNets.Core.JoinBound

/-! # Expressions of `Peano` run by `WMach` and `JMach`

`Peano.PExpr.wrun` and `Peano.PExpr.jrun` run the net of an expression of
`+`, `*` and `^` with `WMach` or `JMach`, threads taking turns, and read the
value at rest.  Whatever they return is the value, and they return it after
a number of actions stated before the run (`Peano.PExpr.wrun_by`,
`Peano.PExpr.jrun_by`).
-/

namespace INet

namespace Peano

open Core

/-- **Run an expression of `+`, `*` and `^` with `WMach`.** -/
def PExpr.wrun (e : PExpr) (nt steps : Nat) : Option Nat :=
  XNet.wrunRead xsys zero succ e.net e.res nt steps

/-- **Run an expression of `+`, `*` and `^` with `JMach`.** -/
def PExpr.jrun (e : PExpr) (nt steps : Nat) : Option Nat :=
  XNet.jrunRead xsys zero succ e.net e.res nt steps

theorem PExpr.wrun_toG (e : PExpr) (nt steps : Nat) : e.toG.wrun nt steps = e.wrun nt steps := by
  show XNet.wrunRead xsys zero succ e.toG.net e.toG.res nt steps = _
  rw [e.toG_net, e.toG_res]
  rfl

theorem PExpr.jrun_toG (e : PExpr) (nt steps : Nat) : e.toG.jrun nt steps = e.jrun nt steps := by
  show XNet.jrunRead xsys zero succ e.toG.net e.toG.res nt steps = _
  rw [e.toG_net, e.toG_res]
  rfl

/-- **Whatever `JMach` returns is the value of the expression.** -/
theorem PExpr.jrun_sound (e : PExpr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.jrun nt steps = some v) : v = e.eval := by
  rw [← e.jrun_toG] at h
  rw [← e.toG_eval]
  exact GExpr.jrun_sound e.toG hnt h

/-- **Whatever `WMach` returns is the value of the expression.** -/
theorem PExpr.wrun_sound (e : PExpr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.wrun nt steps = some v) : v = e.eval := by
  rw [← e.wrun_toG] at h
  rw [← e.toG_eval]
  exact GExpr.wrun_sound e.toG hnt h

/-- **How many actions are enough to run an expression of `+`, `*` and `^`
with `WMach` and read its value.** -/
theorem PExpr.wrun_by (e : PExpr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((7 * e.net.agents.length + (e.net.wires.length + 12 * e.cost)) +
          e.cost * (4 + 12 + 1) +
          e.cost * (7 * (e.net.agents.length + (4 - 2) * e.cost) +
            (e.net.wires.length + 12 * e.cost)) +
          (7 * (4 * e.cost) + (e.net.wires.length + 12 * e.cost)) + 1) ≤ s)
    (h₂ : e.net.wires.length + 12 * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.wrun nt s = some e.eval := by
  have h := GExpr.wrun_by xsys_bounded e.toG hnt s (by rw [e.toG_cost, e.toG_net]; exact h₁)
    (by rw [e.toG_cost, e.toG_net]; exact h₂) (by rw [e.toG_eval]; exact h₃)
  rw [e.toG_eval, e.wrun_toG] at h
  exact h

/-- **How many actions are enough to run an expression of `+`, `*` and `^`
with `JMach` and read its value.** -/
theorem PExpr.jrun_by (e : PExpr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((7 * e.net.agents.length + (e.net.wires.length + 12 * e.cost)) +
          e.cost * (4 + 12 + 1) +
          e.cost * (7 * (e.net.agents.length + (4 - 2) * e.cost) +
            (e.net.wires.length + 12 * e.cost) +
            12 * (3 * (e.net.wires.length + 12 * e.cost) + 12)) +
          (7 * (4 * e.cost) + (e.net.wires.length + 12 * e.cost)) + 1) ≤ s)
    (h₂ : e.net.wires.length + 12 * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.jrun nt s = some e.eval := by
  have h := GExpr.jrun_by xsys_bounded e.toG hnt s (by rw [e.toG_cost, e.toG_net]; exact h₁)
    (by rw [e.toG_cost, e.toG_net]; exact h₂) (by rw [e.toG_eval]; exact h₃)
  rw [e.toG_eval, e.jrun_toG] at h
  exact h

set_option maxRecDepth 100000 in
/-- `2 * 3` run by `JMach`, two threads taking turns: after 1,100 actions
they are at rest and the result read is `6`. -/
example : (PExpr.mul (.lit 2) (.lit 3)).jrun 2 1100 = some 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `2 ^ 3` run by `JMach`, two threads taking turns: after 4,000 actions
they are at rest and the result read is `8`. -/
example : (PExpr.pow (.lit 2) (.lit 3)).jrun 2 4000 = some 8 := by
  decide +kernel

end Peano

end INet
