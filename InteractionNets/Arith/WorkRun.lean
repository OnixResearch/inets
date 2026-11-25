import InteractionNets.Arith.WorkBound
import InteractionNets.WorkRun

/-! # Running an expression of additions with `WMach`

`Expr.wrun` runs the net of an expression with `WMach`, threads taking
turns, and reads the value when they are at rest.  Whatever it returns is
the value (`Expr.wrun_sound`), and it returns the value after a number of
actions stated in the size of the expression, its steps and its additions
(`Expr.wrun_by`): the claims that join interface ports are at most the
additions (`WMach.joined_le_census`), so no run needs to be evaluated to
know it.  For `Expr.run`, on `XMach`, the bound grows as the square of the
steps (`Expr.run_by`); here the square is in the additions only.
-/

namespace INet

namespace Arith

/-- **Run an expression with `WMach`.** -/
def Expr.wrun (e : Expr) (nt steps : Nat) : Option Nat :=
  XNet.wrunRead xsys zero succ e.net e.res nt steps

/-- **Whatever the run returns is the value of the expression.** -/
theorem Expr.wrun_sound (e : Expr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.wrun nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  exact XNet.wrunRead_sound (zero := zero) (succ := succ) xsys (by decide) (Nat.le_refl 1) hX
    hs (normal_of_no_add hno) hA hnt h

/-- **How many actions are enough to run an expression of additions with
`WMach` and read its value**, `nt` threads taking turns. -/
theorem Expr.wrun_by (e : Expr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((7 * e.net.agents.length + (e.net.wires.length + 8 * e.cost)) +
          e.cost * (2 + 8 + 1) +
          e.adds * (7 * (e.net.agents.length + (2 - 2) * e.cost) +
            (e.net.wires.length + 8 * e.cost)) +
          (7 * (2 * e.cost) + (e.net.wires.length + 8 * e.cost)) + 1) ≤ s)
    (h₂ : e.net.wires.length + 8 * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.wrun nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  have hnd := Expr.net_nodup e
  exact XNet.wrunRead_bound (zero := zero) (succ := succ) (by decide) hX hnd hnt xsys_bounded hs
    (normal_of_no_add hno) hA (m := e.adds) (fun j => by
      have h := WMach.joined_le_census census_add hX hnd hnt (fun j => j % nt) j
      rw [Expr.net_adds] at h
      exact h) s h₁ h₂ h₃

/-- `(2 + 3) + (1 + 4)` run by three threads taking turns: after 700
actions they are at rest and the result read is `10`. -/
theorem _root_.INet.Checks.Arith.WorkRun.c1
    : (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).wrun 3 700 = some 10 := by
  decide +kernel

end Arith

end INet
