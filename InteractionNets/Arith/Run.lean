import InteractionNets.Arith.Expr
import InteractionNets.ReadBack

/-! # Running an expression and reading the result

The memories that the nets of expressions leave have wires of several
segments, which `readNat` does not follow.  `XNet.readNum`, of
`ReadBack`, does: it goes along the wire from a port as a thread does,
to the principal port of an agent, and reads the numeral there.

`Expr.run` lets a number of threads take turns on the net of an
expression for a number of actions and, if they are then at rest, reads
the result (`XNet.runRead`).  Whatever it returns is the value of the
expression (`Expr.run_sound`), and given enough actions it returns the
value (`Expr.run_complete`).
-/

namespace INet

namespace Arith

/-! ### Running an expression -/

/-- At rest the memory holds a well-formed net. -/
theorem Expr.rest_wf (e : Expr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet.WF ar := by
  obtain ⟨hX, -, N', hs, -, hno⟩ := Expr.good e
  have hn' := normal_of_no_add hno
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init e.net nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e', -⟩ := (hu hs).2 hn'
  have e'' : N' = ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet := e'
  rw [← e'']
  exact Steps.wf hX hs

/-- **Run an expression.**  `nt` threads take turns on the net of the
expression for `steps` actions; if they are then at rest, the numeral on
the free port is read. -/
def Expr.run (e : Expr) (nt steps : Nat) : Option Nat :=
  XNet.runRead xsys zero succ e.net e.res nt steps

/-- **Whatever the run returns is the value of the expression.** -/
theorem Expr.run_sound (e : Expr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.run nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  exact XNet.runRead_sound (zero := zero) (succ := succ) xsys (by decide) (Nat.le_refl 1) hX hs
      (normal_of_no_add hno) hA
    hnt h

/-- **Given enough actions, the run returns the value of the
expression.**  Threads that take turns are scheduled fairly, so they come
to rest; from then on the memory does not change, and the numeral on the
free port is read. -/
theorem Expr.run_complete (e : Expr) {nt : Nat} (hnt : 0 < nt) :
    ∃ s₀, ∀ s, s₀ ≤ s → e.run nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  exact XNet.runRead_complete (zero := zero) (succ := succ) xsys (by decide) hX hs
      (normal_of_no_add hno) hA hnt

/-- `1 + 1` run by two threads taking turns: after 200 actions they are
at rest and the result read is `2`. -/
theorem _root_.INet.Checks.Arith.Run.c1 : (Expr.add (.lit 1) (.lit 1)).run 2 200 = some 2 := by
  decide +kernel

/-- `(2 + 3) + (1 + 4)` run by three threads taking turns: after 700
actions they are at rest and the result read is `10`. -/
theorem _root_.INet.Checks.Arith.Run.c2
    : (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).run 3 700 = some 10 := by
  decide +kernel

end Arith

end INet
