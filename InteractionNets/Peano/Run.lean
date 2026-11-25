import InteractionNets.Peano.Rec
import InteractionNets.Core.Run

/-! # The machine on the agents of `Peano`

`Peano.fac_rest`, `Peano.prod_rest`, `Peano.power_rest` and the fair
versions, from the theorems for the machine.
-/

namespace INet

namespace Peano

open Core

/-- The situation of an agent of one argument of `Peano`. -/
abbrev Unary (op : Peano) (N : Net Peano) (a : Id) (n : Nat) (r : Port) : Prop :=
  Core.Unary system op N a n r

/-- The situation of an agent of two arguments of `Peano`. -/
abbrev Binary (op : Peano) (N : Net Peano) (a : Id) (m n : Nat) (r : Port) : Prop :=
  Core.Binary system op N a m n r

/-- The net for `op n`, in `Peano`. -/
abbrev unaryNet (op : Peano) (n : Nat) : XNet Peano := Core.unaryNet zero succ op n

/-- The net for `op m n`, in `Peano`. -/
abbrev binaryNet (op : Peano) (m n : Nat) : XNet Peano := Core.binaryNet zero succ op m n

/-- The symbols of `Arith` as symbols of `Peano`. -/
abbrev ofArithAt (op : Peano) : Arith → Peano := Core.ofArithAt zero op

/-! ### The factorial -/

/-- The net for `n!`. -/
def facNet (n : Nat) : XNet Peano := unaryNet fac n

/-- **Factorials on the machine**, as a case. -/
theorem fac_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (facNet n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (facNet n) nt).trace xsys σ i).2 = facCost n ∧
      IsNum ((XMach.init (facNet n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (fact n) := by
  exact unary_rest fac_computes rfl (by decide) n hnt σ hr

/-- **Factorials under any fair schedule**, as a case. -/
theorem fac_fair (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (facNet n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (facNet n) nt).trace xsys σ i).2 = facCost n ∧
      IsNum ((XMach.init (facNet n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (fact n) := by
  exact unary_fair fac_computes rfl (by decide) n hnt σ hfair

/-- The net for `m * n`. -/
def prod (m n : Nat) : XNet Peano := binaryNet mul m n

/-- The net for `b ^ e`, with the exponent first. -/
def power (e b : Nat) : XNet Peano := binaryNet pow e b

/-- **Multiplication on the machine**, as a case, through the multiplier
derived from the theorem on recursion. -/
theorem prod_rest (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (prod m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (prod m n) nt).trace xsys σ i).2 = prodCost m n ∧
      IsNum ((XMach.init (prod m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m * n) := by
  exact binary_rest mul_computes rfl (by decide) (by decide) m n hnt σ hr

/-- **Powers on the machine**, as a case. -/
theorem power_rest (e b : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (power e b) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (power e b) nt).trace xsys σ i).2 = powCost e b ∧
      IsNum ((XMach.init (power e b) nt).trace xsys σ i).1.mem.toNet ([0], 0) (b ^ e) := by
  exact binary_rest pow_computes rfl (by decide) (by decide) e b hnt σ hr

/-- **Multiplication under any fair schedule**, as a case. -/
theorem prod_fair (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (prod m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (prod m n) nt).trace xsys σ i).2 = prodCost m n ∧
      IsNum ((XMach.init (prod m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m * n) := by
  exact binary_fair mul_computes rfl (by decide) (by decide) m n hnt σ hfair

/-- **Powers under any fair schedule**, as a case. -/
theorem power_fair (e b : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (power e b) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (power e b) nt).trace xsys σ i).2 = powCost e b ∧
      IsNum ((XMach.init (power e b) nt).trace xsys σ i).1.mem.toNet ([0], 0) (b ^ e) := by
  exact binary_fair pow_computes rfl (by decide) (by decide) e b hnt σ hfair

/-- The count for `2 * 3` is the 23 steps that the reducer takes. -/
theorem _root_.INet.Checks.Peano.Run.c1 : prodCost 2 3 = 23 := by decide

/-- The reducer on the net for `2 * 3` stops after 23 steps on a net whose
agents are six successors and a zero. -/
theorem _root_.INet.Checks.Peano.Run.c2 : ((prod 2 3).normalize xsys 100).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length)) = some (23, 6, 1) := by
  decide +kernel

/-- The reducer on the net for `2 ^ 3` stops after `powCost 3 2 = 75`
steps on eight successors and a zero. -/
theorem _root_.INet.Checks.Peano.Run.c3 : ((power 3 2).normalize xsys 200).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) = some (75, 8, 1, 9) := by
  decide +kernel

/-- `3! = 6`, in 52 interactions, and the reducer agrees. -/
theorem _root_.INet.Checks.Peano.Run.c4 : fact 3 = 6 ∧ facCost 3 = 52 := by decide

theorem _root_.INet.Checks.Peano.Run.c5 : ((facNet 3).normalize xsys 200).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) = some (52, 6, 1, 7) := by
  decide +kernel

end Peano

end INet
