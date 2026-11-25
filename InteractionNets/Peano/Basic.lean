import InteractionNets.Peano
import InteractionNets.Core.Basic

/-! # `Peano` has the core

The copier and the eraser of `Peano` (`Peano.copyRules`, `Peano.erase`,
`Peano.copy_fresh`), its instance of the core (`Peano.core`), the costs of
its agents, and two small runs.
-/

namespace INet

namespace Peano

open Addition (gone)

/-- The port `p` is wired to the numeral `k`. -/
abbrev IsNum (N : Net Peano) (p : Port) (k : Nat) : Prop := Addition.IsNum ar zero succ N p k

/-- The agents of a numeral, from its head down. -/
abbrev NumList (N : Net Peano) (i : Id) (l : List Id) : Prop :=
  Addition.NumList ar zero succ N i l

/-- Above the port `x` there are `j` successors, the last of which has its
principal port wired to `r`. -/
abbrev Tower (N : Net Peano) (x : Port) (j : Nat) (r : Port) : Prop :=
  Addition.Tower ar succ N x j r

/-- The port `p` is wired to the numeral `k`, all of whose agents satisfy
`Q`. -/
abbrev IsNumQ (N : Net Peano) (Q : Id → Prop) (p : Port) (k : Nat) : Prop :=
  Addition.IsNumQ ar zero succ N Q p k

/-- A tower all of whose agents satisfy `Q`. -/
abbrev TowerQ (N : Net Peano) (Q : Id → Prop) (x : Port) (j : Nat) (r : Port) : Prop :=
  Addition.TowerQ ar succ N Q x j r

theorem rule_era_zero : system.rule era zero = some eraZero.toX.toRhs := rfl
theorem rule_era_succ : system.rule era succ = some eraSucc.toX.toRhs := rfl
theorem rule_dup_zero : system.rule dup zero = some dupZero.toX.toRhs := rfl
theorem rule_dup_succ : system.rule dup succ = some dupSucc.toX.toRhs := rfl

/-- **`Peano` has a copier and an eraser.** -/
theorem copyRules : Copies.Rules system zero succ dup era :=
  ⟨by decide, by decide, by decide, by decide, rfl, rfl, rfl, rfl⟩

/-- **Erasing a numeral**, in `Peano`. -/
theorem erase : ∀ (l : List Id) {N : Net Peano} {e h : Id}, N.WF ar → N.agent e era →
    N.Paired ar (e, 0) (h, 0) → NumList N h l →
    ∃ N', Steps (Step system) l.length N N' ∧ N.Keeps ar (gone N e l) N' ∧
      ∀ i γ, N'.agent i γ → N.agent i γ ∧ i ≠ e ∧ ¬ i ∈ l :=
  Copies.erase copyRules

/-- **Copying a numeral**, in `Peano`. -/
theorem copy_fresh {N : Net Peano} {d h : Id} {l : List Id} {p₁ p₂ : Port} {n : Nat}
    (hN : N.WF ar) (hd : N.agent d dup) (hp : N.Paired ar (d, 0) (h, 0)) (hl : NumList N h l)
    (hlen : l.length = n + 1) (h₁ : N.Paired ar (d, 1) p₁) (h₂ : N.Paired ar (d, 2) p₂)
    (hp₁ : p₁.1 ≠ d ∧ ¬ p₁.1 ∈ l) (hp₂ : p₂.1 ≠ d ∧ ¬ p₂.1 ∈ l) :
    ∃ N', Steps (Step system) (n + 1) N N' ∧ IsNumQ N' (fun i => ¬ N.Used i) p₁ n ∧
      IsNumQ N' (fun i => ¬ N.Used i) p₂ n ∧ N.Keeps ar (gone N d l) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ d) :=
  Copies.copy_fresh copyRules hN hd hp hl hlen h₁ h₂ hp₁ hp₂

/-- The same, without the statement about the agents of the copies. -/
theorem copy {N : Net Peano} {d h : Id} {l : List Id} {p₁ p₂ : Port} {n : Nat}
    (hN : N.WF ar) (hd : N.agent d dup) (hp : N.Paired ar (d, 0) (h, 0)) (hl : NumList N h l)
    (hlen : l.length = n + 1) (h₁ : N.Paired ar (d, 1) p₁) (h₂ : N.Paired ar (d, 2) p₂)
    (hp₁ : p₁.1 ≠ d ∧ ¬ p₁.1 ∈ l) (hp₂ : p₂.1 ≠ d ∧ ¬ p₂.1 ∈ l) :
    ∃ N', Steps (Step system) (n + 1) N N' ∧ IsNum N' p₁ n ∧ IsNum N' p₂ n ∧
      N.Keeps ar (gone N d l) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ d) :=
  Copies.copy copyRules hN hd hp hl hlen h₁ h₂ hp₁ hp₂


/-! ### Two small runs -/

/-- An eraser on the numeral `2`, and nothing else. -/
def eraseTwo : XNet Peano :=
  XNet.ofWires [([1], era), ([2], succ), ([3], succ), ([4], zero)] []
    [(([1], 0), ([2], 0)), (([2], 1), ([3], 0)), (([3], 1), ([4], 0))]

/-- The reducer stops after three steps with no agent and no wire. -/
theorem _root_.INet.Checks.Peano.Basic.c1 : (eraseTwo.normalize xsys 20).map
    (fun r => (r.2, r.1.agents.length, r.1.wires.length)) = some (3, 0, 0) := by
  decide +kernel

/-- A copier on the numeral `2`, with its copies on two free ports. -/
def copyTwo : XNet Peano :=
  XNet.ofWires [([1], dup), ([2], succ), ([3], succ), ([4], zero)] [([0], 0), ([5], 0)]
    [(([1], 0), ([2], 0)), (([2], 1), ([3], 0)), (([3], 1), ([4], 0)),
      (([1], 1), ([0], 0)), (([1], 2), ([5], 0))]

/-- The reducer stops after three steps with four successors and two
zeros. -/
theorem _root_.INet.Checks.Peano.Basic.c2
    : (copyTwo.normalize xsys 20).map (fun r => (r.2, r.1.agents.map (·.2))) =
    some (3, [succ, succ, succ, succ, zero, zero]) := by
  decide +kernel

end Peano

namespace Peano

open Core
open Addition (gone gone2)

/-- The number of interactions of `b ^ e`: on the zero, one and the
erasure of the base; on a successor, one, the copy of the base, the power
for the rest and the multiplication. -/
def powCost : Nat → Nat → Nat
  | 0, b => b + 1 + 1
  | e + 1, b => b + 1 + 1 + powCost e b + prodCost b (b ^ e)

/-! ### `Peano` has the core -/

/-- **`Peano` has numerals, a copier and an eraser.** -/
instance core : Core system zero succ dup era :=
  { copyRules with
    numerals := by rintro α β (rfl | rfl) (rfl | rfl) <;> rfl
    ar_zero := rfl
    ar_succ := rfl
    zero_ne_succ := by decide
    sided := by
      intro α β R hR j
      cases α <;> cases β <;> cases hR <;> rfl }

/-- **An agent of `Peano` that computes a function of two numerals.** -/
abbrev Computes2 (op : Peano) (f c : Nat → Nat → Nat) : Prop := Core.Computes2 system op f c

/-- **An agent of `Peano` that computes a function of one numeral.** -/
abbrev Computes1 (op : Peano) (f c : Nat → Nat) : Prop := Core.Computes1 system op f c

/-- The situation of an addition in `Peano`. -/
abbrev Sum (N : Net Peano) (a : Id) (m n : Nat) (r : Port) : Prop := Core.Sum system add N a m n r

/-- The factorial of a number. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)

/-- The number of interactions of `n!`: on the zero, one; on a successor,
one, the copy of the rest, the factorial of the rest and the
multiplication. -/
def facCost : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1 + 1 + facCost n + prodCost (fact n) (n + 1)

theorem rule_mul_zero : system.rule mul zero = some mulZero.toX.toRhs := rfl
theorem rule_mul_succ : system.rule mul succ = some mulSucc.toX.toRhs := rfl
theorem rule_pow_zero : system.rule pow zero = some powZero.toX.toRhs := rfl
theorem rule_pow_succ : system.rule pow succ = some powSucc.toX.toRhs := rfl
theorem rule_fac_zero : system.rule fac zero = some facZero.toX.toRhs := rfl
theorem rule_fac_succ : system.rule fac succ = some facSucc.toX.toRhs := rfl

end Peano

end INet
