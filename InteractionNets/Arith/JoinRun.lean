import InteractionNets.Arith.Run
import InteractionNets.JoinRun

/-! # Running an expression of additions with `JMach`

`Expr.jrun` runs the net of an expression with `JMach`, threads taking
turns, and reads the value when they are at rest.  Whatever it returns is
the value (`Expr.jrun_sound`).
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

/-- `(2 + 3) + (1 + 4)` run by three threads taking turns: after 700
actions they are at rest and the result read is `10`. -/
example : (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).jrun 3 700 = some 10 := by
  decide +kernel


set_option maxRecDepth 100000 in
/-- `((5 + 0) + 0) + 0`, where every addition ends with a claim that joins,
run by two threads taking turns: after 1,200 actions they are at rest and
the result read is `5`. -/
example : (Expr.add (.add (.add (.lit 5) (.lit 0)) (.lit 0)) (.lit 0)).jrun 2 1200 = some 5 := by
  decide +kernel

end Arith

end INet
