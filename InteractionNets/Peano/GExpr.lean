import InteractionNets.Peano.Run
import InteractionNets.Core.GExpr

/-! # Expressions over the operators of `Peano`

The adder, the multiplier, the power and the factorial as operators
(`Peano.addOp`, `Peano.mulOp`, `Peano.powOp`, `Peano.facOp`).
-/

namespace INet

namespace Peano

open Core

/-- **The rules of `Peano` give every new agent a side.** -/
theorem system_sided : system.Sided := by
  intro α β R hR j
  cases α <;> cases β <;> cases hR <;> rfl

/-- A net of `Peano` that computes a number. -/
abbrev Evals (N : Net Peano) (s v : Nat) (p : Port) : Prop := Core.Evals xsys N s v p

/-- Expressions over operators of `Peano`. -/
abbrev GExpr := Core.GExpr xsys

/-- Operators of `Peano`. -/
abbrev Op1 := Core.Op1 xsys
abbrev Op2 := Core.Op2 xsys

/-- A numeral of `Peano`. -/
abbrev lit (n : Nat) : XNet Peano := Core.lit zero succ n

/-- **The adder is an operator**, by its own theorem. -/
def addOp : Op2 :=
  ⟨add, fun m n => m + n, fun m _ => m + 1, rfl, by decide, by decide,
    fun u => add_steps' rules ⟨u.wf, u.ha, u.fst, u.snd, u.out, u.free, u.only⟩⟩

/-- The multiplier, through the theorem on recursion. -/
def mulOp : Op2 := Op2.ofComputes mul_computes rfl (by decide) (by decide)

/-- The power, through the theorem on recursion: the first argument is
the exponent. -/
def powOp : Op2 := Op2.ofComputes pow_computes rfl (by decide) (by decide)

/-- The factorial, through the theorem on recursion. -/
def facOp : Op1 := Op1.ofComputes fac_computes rfl (by decide) (by decide)

/-- **Addition on the machine**, as a case: a run on the net for `m + n`
that is at rest has made exactly `m + 1` interactions and holds
`m + n`. -/
theorem sum_rest (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (binaryNet add m n) nt).trace xsys σ i).2 = m + 1 ∧
      IsNum ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (m + n) :=
  addOp.rest m n hnt σ hr

/-- **Addition under any fair schedule**, as a case. -/
theorem sum_fair (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (binaryNet add m n) nt).trace xsys σ i).2 = m + 1 ∧
      IsNum ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (m + n) :=
  addOp.fair m n hnt σ hfair

end Peano

end INet
