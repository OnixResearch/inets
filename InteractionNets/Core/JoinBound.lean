import InteractionNets.Core.Bound
import InteractionNets.JoinBound

/-! # Expressions run by the programs that recheck only what a rule touched

In any system with the core, the net of an expression can be run by
`WMach` or by `JMach`, threads taking turns, and the value read when they
are at rest.  Whatever either returns is the value (`Core.GExpr.wrun_sound`,
`Core.GExpr.jrun_sound`), and each returns it after a number of actions
stated in the size of the net, the number of threads, the cost of the
expression and a bound on the rules (`Core.GExpr.wrun_by`,
`Core.GExpr.jrun_by`), with no evaluated run: at most every claim joins
interface ports.
-/

namespace INet

namespace Core

variable {S : Type} [DecidableEq S] {xsys : XSys S} {zero succ dup era : S}
  [K : Core xsys.sys zero succ dup era]

include K

/-- **Run an expression with `WMach`.** -/
def GExpr.wrun (e : GExpr xsys) (nt steps : Nat) : Option Nat :=
  XNet.wrunRead xsys zero succ e.net e.res nt steps

/-- **Run an expression with `JMach`.** -/
def GExpr.jrun (e : GExpr xsys) (nt steps : Nat) : Option Nat :=
  XNet.jrunRead xsys zero succ e.net e.res nt steps

/-- **Whatever `WMach` returns is the value of the expression.** -/
theorem GExpr.wrun_sound (e : GExpr xsys) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.wrun nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  exact XNet.wrunRead_sound (zero := zero) (succ := succ) xsys K.zero_ne_succ
    (Nat.le_of_eq K.ar_succ.symm) hX hs
    (normal_of_numerals hag : Normal (Step xsys.sys) _) hA hnt h

/-- **Whatever `JMach` returns is the value of the expression.** -/
theorem GExpr.jrun_sound (e : GExpr xsys) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.jrun nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  exact XNet.jrunRead_sound (zero := zero) (succ := succ) xsys K.zero_ne_succ
    (Nat.le_of_eq K.ar_succ.symm) hX hs
    (normal_of_numerals hag : Normal (Step xsys.sys) _) hA hnt h

/-- **How many actions are enough to run an expression with `WMach` and
read its value**, `nt` threads taking turns: the bound of
`WMach.fair_bound_all` with a window of one action per thread. -/
theorem GExpr.wrun_by {C D : Nat} (hb : xsys.Bounded C D) (e : GExpr xsys) {nt : Nat}
    (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((7 * e.net.agents.length + (e.net.wires.length + D * e.cost)) +
          e.cost * (C + D + 1) +
          e.cost * (7 * (e.net.agents.length + (C - 2) * e.cost) +
            (e.net.wires.length + D * e.cost)) +
          (7 * (C * e.cost) + (e.net.wires.length + D * e.cost)) + 1) ≤ s)
    (h₂ : e.net.wires.length + D * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.wrun nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  refine XNet.wrunRead_bound (zero := zero) (succ := succ) K.zero_ne_succ hX (GExpr.net_nodup e)
    hnt hb hs (normal_of_numerals hag : Normal (Step xsys.sys) _) hA (m := e.cost)
    (fun i => ?_) s h₁ h₂ h₃
  have run := WMach.trace_run xsys (fun j => j % nt) (WMach.init e.net nt) i
  rw [WMach.init_toMach] at run
  exact Nat.le_trans (WMach.joined_le _ _ i)
    (run.claims_le hX hs (normal_of_numerals hag : Normal (Step xsys.sys) _))

/-- **How many actions are enough to run an expression with `JMach` and
read its value**, `nt` threads taking turns: the bound of
`JMach.fair_bound_all` with a window of one action per thread. -/
theorem GExpr.jrun_by {C D : Nat} (hb : xsys.Bounded C D) (e : GExpr xsys) {nt : Nat}
    (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((7 * e.net.agents.length + (e.net.wires.length + D * e.cost)) +
          e.cost * (C + D + 1) +
          e.cost * (7 * (e.net.agents.length + (C - 2) * e.cost) +
            (e.net.wires.length + D * e.cost) +
            D * (3 * (e.net.wires.length + D * e.cost) + 12)) +
          (7 * (C * e.cost) + (e.net.wires.length + D * e.cost)) + 1) ≤ s)
    (h₂ : e.net.wires.length + D * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.jrun nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  refine XNet.jrunRead_bound (zero := zero) (succ := succ) K.zero_ne_succ hX (GExpr.net_nodup e)
    hnt hb hs (normal_of_numerals hag : Normal (Step xsys.sys) _) hA (m := e.cost)
    (fun i => ?_) s h₁ h₂ h₃
  have run := JMach.trace_run xsys (fun j => j % nt) (JMach.init e.net nt) i
  rw [JMach.init_toMach] at run
  exact Nat.le_trans (JMach.joined_le _ _ i)
    (run.claims_le hX hs (normal_of_numerals hag : Normal (Step xsys.sys) _))

end Core

end INet
