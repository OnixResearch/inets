import InteractionNets.Arith.Run
import InteractionNets.JoinRun
import InteractionNets.JoinBound
import InteractionNets.Arith.WorkBound

/-! # Running an expression of additions with `JMach`

`Expr.jrun` runs the net of an expression with `JMach`, threads taking
turns, and reads the value when they are at rest.  Whatever it returns is
the value (`Expr.jrun_sound`), and it returns the value after a number of
actions stated in the size of the expression, its steps and its additions
(`Expr.jrun_by`), with no run evaluated: the claims that join are at most
the additions (`JMach.joined_le_census`).
-/

namespace INet

namespace Arith

/-- **Run an expression with `JMach`.** -/
def Expr.jrun (e : Expr) (nt steps : Nat) : Option Nat :=
  XNet.jrunRead xsys zero succ e.net e.res nt steps

/-- **Whatever the run returns is the value of the expression.** -/
theorem Expr.jrun_sound (e : Expr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.jrun nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  exact XNet.jrunRead_sound (zero := zero) (succ := succ) xsys (by decide) (Nat.le_refl 1) hX
    hs (normal_of_no_add hno) hA hnt h

/-- **How many actions are enough to run an expression of additions with
`JMach` and read its value**, `nt` threads taking turns. -/
theorem Expr.jrun_by (e : Expr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((7 * e.net.agents.length + (e.net.wires.length + 8 * e.cost)) +
          e.cost * (2 + 8 + 1) +
          e.adds * (7 * (e.net.agents.length + (2 - 2) * e.cost) +
            (e.net.wires.length + 8 * e.cost) +
            8 * (3 * (e.net.wires.length + 8 * e.cost) + 12)) +
          (7 * (2 * e.cost) + (e.net.wires.length + 8 * e.cost)) + 1) ≤ s)
    (h₂ : e.net.wires.length + 8 * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.jrun nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  have hnd := Expr.net_nodup e
  exact XNet.jrunRead_bound (zero := zero) (succ := succ) (by decide) hX hnd hnt xsys_bounded hs
    (normal_of_no_add hno) hA (m := e.adds) (fun j => by
      have h := JMach.joined_le_census census_add hX hnd hnt (fun j => j % nt) j
      rw [Expr.net_adds] at h
      exact h) s h₁ h₂ h₃

/-- `(2 + 3) + (1 + 4)` run by three threads taking turns: after 700
actions they are at rest and the result read is `10`. -/
theorem Checks.Arith.JoinRun.c1
    : (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).jrun 3 700 = some 10 := by
  decide +kernel


set_option maxRecDepth 100000 in
/-- `((5 + 0) + 0) + 0`, where every addition ends with a claim that joins,
run by two threads taking turns: after 1,200 actions they are at rest and
the result read is `5`. -/
theorem Checks.Arith.JoinRun.c2
    : (Expr.add (.add (.add (.lit 5) (.lit 0)) (.lit 0)) (.lit 0)).jrun 2 1200 = some 5 := by
  decide +kernel

end Arith

end INet
