import InteractionNets.PeanoCopy

/-! # What the agents of `Peano` share

Small facts about names in nets of `Peano`, what it is for an agent to
compute (`Peano.Computes1`, `Peano.Computes2`), the adder alone
(`Core.add_steps'`), the costs of the multiplier, the power and the
factorial, and the building of nets by putting successors on wires.
The theorems that the agents compute are in `PeanoRec`, by recursion
proved once.
-/

namespace INet

section Building

variable {S : Type}

/-- Put an agent with the symbol `γ` on the wire that leaves the port
`p`. -/
def XNet.pushOn (X : XNet S) (γ : S) (p : Port) (u : Id) : XNet S :=
  match assoc p X.wires with
  | some q => X.insert1 u γ p q
  | none => X

/-- The identifiers in use are the one-element lists of the numbers below
`b`. -/
def XNet.Below (X : XNet S) (b : Nat) : Prop :=
  ∀ i, X.toNet.Used i → ∃ j, j < b ∧ i = [j]

theorem XNet.Below.fresh {X : XNet S} {b : Nat} (hb : X.Below b) (l : List Nat) :
    ¬ X.toNet.Used (l ++ [b]) := by
  intro hu
  obtain ⟨j, hj, e⟩ := hb _ hu
  have := (Arith.append_singleton e).2
  omega

theorem XNet.Below.fresh' {X : XNet S} {b : Nat} (hb : X.Below b) (l : List Nat) (i : Id)
    (α : S) (hi : X.toNet.agent i α) : [b] ≠ l ++ i := by
  intro e
  obtain ⟨j, hj, rfl⟩ := hb i (.inl ⟨α, hi⟩)
  have := (Arith.append_singleton e.symm).2
  omega

theorem XNet.pushOn_eq {ar : S → Nat} {X : XNet S} (hX : X.Ok ar) {p q : Port}
    (h : X.toNet.Paired ar p q) (γ : S) (u : Id) : X.pushOn γ p u = X.insert1 u γ p q := by
  have e : assoc p X.wires = some q := hX.exact.assoc_eq hX.1.wiring (hX.link_iff.2 h)
  unfold XNet.pushOn
  rw [e]

theorem XNet.Below.pushOn {ar : S → Nat} {X : XNet S} {b : Nat} (hb : X.Below b)
    (hX : X.Ok ar) {p q : Port} (h : X.toNet.Paired ar p q) (γ : S) :
    (X.pushOn γ p [b]).Below (b + 1) := by
  intro i hi
  rw [XNet.pushOn_eq hX h, XNet.insert1_toNet] at hi
  rcases Net.used_insert1 (hX.link_iff.2 h) hX.1.symm hi with hu | rfl
  · obtain ⟨j, hj, e⟩ := hb i hu
    exact ⟨j, by omega, e⟩
  · exact ⟨b, by omega, rfl⟩

/-- The identifiers of a finite net. -/
def XNet.usedIds (X : XNet S) : List Id :=
  X.agents.map (·.1) ++ X.wires.map (·.1.1) ++ X.free.map (·.1)

theorem XNet.mem_usedIds {X : XNet S} {i : Id} (h : X.toNet.Used i) : i ∈ X.usedIds := by
  unfold XNet.usedIds
  rcases h with ⟨γ, hγ⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨(i, γ), hγ, rfl⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨((i, k), q), hl, rfl⟩))
  · exact List.mem_append_right _ (List.mem_map.2 ⟨(i, k), hf, rfl⟩)

/-- A numeral is still there after a successor is put on a wire that
leaves none of its auxiliary ports. -/
theorem Addition.Num.insert1 {ar : S → Nat} {zero succ : S} {N : Net S} {u : Id} {p q : Port}
    (hm' : (N.insert1 u succ p q).Matching ar) (hm : N.Matching ar)
    (hp : ∀ i, N.agent i succ → (i, 1) ≠ p) (hq : ∀ i : Id, (i, 1) ≠ q) :
    ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ N i k →
      Addition.Num ar zero succ (N.insert1 u succ p q) i k
  | 0, _, hz => .inl hz
  | _ + 1, i, ⟨hs, i', hp', hn⟩ =>
    ⟨.inl hs, i', hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hp', hp i hs, hq i⟩),
      Addition.Num.insert1 hm' hm hp hq hn⟩

end Building

/-- **A system with numerals, a copier and an eraser**: the symbols are
apart, the system has the rules of the copier and the eraser, and no rule
for two numerals.  The symbols are given by the system. -/
class Core {S : Type} (system : System S) (zero succ dup era : outParam S) : Prop
    extends Copies.Rules system zero succ dup era where
  numerals : ∀ α β, (α = zero ∨ α = succ) → (β = zero ∨ β = succ) → system.rule α β = none
  ar_zero : system.ar zero = 0
  ar_succ : system.ar succ = 1
  zero_ne_succ : zero ≠ succ
  sided : system.Sided

namespace Core

open Addition (gone gone2)

variable {S : Type}

/-! ### The shape of the theorems -/

/-- **An agent that computes a function of two numerals, in any net.** -/
def Computes2 (system : System S) {zero succ dup era : S} [Core system zero succ dup era]
    (op : S) (f c : Nat → Nat → Nat) : Prop :=
  ∀ (l₁ : List Id) {N : Net S} {a h₁ h₂ : Id} {l₂ : List Id} {r : Port} {m n : Nat},
    N.WF system.ar → N.agent a op → N.Paired system.ar (a, 0) (h₁, 0) → Addition.NumList system.ar zero succ N h₁ l₁ →
    N.Paired system.ar (a, 1) (h₂, 0) → Addition.NumList system.ar zero succ N h₂ l₂ → N.Paired system.ar (a, 2) r →
    r.1 ≠ a ∧ ¬ r.1 ∈ l₁ ∧ ¬ r.1 ∈ l₂ → l₁.length = m + 1 → l₂.length = n + 1 →
    ∃ N', Steps (Step system) (c m n) N N' ∧
      Addition.IsNumQ system.ar zero succ N' (fun i => ¬ N.Used i) r (f m n) ∧ N.Keeps system.ar (gone2 N a l₁ l₂) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)

/-- **An agent that computes a function of one numeral, in any net.** -/
def Computes1 (system : System S) {zero succ dup era : S} [Core system zero succ dup era]
    (op : S) (f c : Nat → Nat) : Prop :=
  ∀ (l : List Id) {N : Net S} {a h : Id} {r : Port} {n : Nat},
    N.WF system.ar → N.agent a op → N.Paired system.ar (a, 0) (h, 0) → Addition.NumList system.ar zero succ N h l →
    N.Paired system.ar (a, 1) r → r.1 ≠ a ∧ ¬ r.1 ∈ l → l.length = n + 1 →
    ∃ N', Steps (Step system) (c n) N N' ∧
      Addition.IsNumQ system.ar zero succ N' (fun i => ¬ N.Used i) r (f n) ∧ N.Keeps system.ar (gone N a l) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)

/-- **The situation of an addition.**  The adder `a` has the numerals `m`
and `n` as arguments and the free port `r` as result, and the net has no
other agents than the adder and the successors and zeros. -/
structure Sum (system : System S) {zero succ dup era : S} [Core system zero succ dup era]
    (add : S) (N : Net S) (a : Id) (m n : Nat) (r : Port) : Prop where
  wf : N.WF system.ar
  ha : N.agent a add
  fst : Addition.IsNum system.ar zero succ N (a, 0) m
  snd : Addition.IsNum system.ar zero succ N (a, 1) n
  out : N.Paired system.ar (a, 2) r
  free : N.free r
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = a

section

variable {system : System S} {zero succ dup era : S} [K : Core system zero succ dup era]

local notation "ar" => system.ar
local notation "NumList" => Addition.NumList system.ar zero succ
local notation "IsNum" => Addition.IsNum system.ar zero succ

/-! ### Small facts about names -/

theorem ne_of_agent {N : Net S} (hN : N.WF ar) {i j : Id} {α β : S}
    (hi : N.agent i α) (hj : N.agent j β) (h : α ≠ β) : i ≠ j := by
  rintro rfl
  exact h (hN.agent_fun hi hj)

theorem not_gone {N : Net S} {d i : Id} {l : List Id} (h1 : i ≠ d) (h2 : ¬ i ∈ l)
    (h3 : N.Used i) : ¬ gone N d l i := by
  rintro (e | hm | hu)
  · exact h1 e
  · exact h2 hm
  · exact hu h3

include K in
/-- A net whose agents are zeros and successors is normal. -/
theorem normal_of_numerals {N : Net S} (h : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ) :
    Normal (Step system) N := by
  rintro N' ⟨a, b, α, β, R, red, -⟩
  have hr := red.rule
  rw [K.numerals α β (h a α red.ha) (h b β red.hb)] at hr
  cases hr

/-- The agents of a numeral are in use. -/
theorem numList_used {N : Net S} {h : Id} {l : List Id} (hl : NumList N h l) {j : Id}
    (hj : j ∈ l) : N.Used j :=
  (hl.label j hj).elim (fun h => .inl ⟨_, h⟩) fun h => .inl ⟨_, h⟩

theorem not_gone2 {N : Net S} {a i : Id} {l₁ l₂ : List Id} (h1 : i ≠ a) (h2 : ¬ i ∈ l₁)
    (h3 : ¬ i ∈ l₂) (h4 : N.Used i) : ¬ gone2 N a l₁ l₂ i := by
  rintro (e | hm | hm | hu)
  · exact h1 e
  · exact h2 hm
  · exact h3 hm
  · exact hu h4

/-- **The run of an addition**, in this system: in `m + 1` steps the net
becomes one that has the numeral `m + n` on the result port and whose
agents are successors and zeros. -/
theorem add_steps' {add : S} (HA : Addition.Rules system zero succ add) {a : Id} {m : Nat}
    (c : Sum system add N a m n r) :
    ∃ N', Steps (Step system) (m + 1) N N' ∧ IsNum N' r (m + n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ := by
  have hN := c.wf
  obtain ⟨h, hph, hnh⟩ := c.fst
  obtain ⟨l, hl, el⟩ := Addition.Num.list hnh
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  have cA : Addition.Adding ar zero succ add N (fun _ => True) a 0 h l n r :=
    ⟨hN, c.ha, hph, hl, Addition.IsNum.isNumQ c.snd, ⟨r, c.out, rfl⟩, ⟨.inr (.inr ⟨r.2, c.free⟩),
      fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ c.ha), hrl⟩, fun _ _ => trivial⟩
  obtain ⟨N', sts, inum, -, hag⟩ := Addition.Adding.run HA l cA el
  rw [el] at sts
  rw [Nat.zero_add] at inum
  refine ⟨N', sts, inum.isNum, fun i γ hi => ?_⟩
  rcases hag i γ hi with hsu | ⟨hi₀, hne⟩
  · exact .inr hsu
  · rcases c.only i γ hi₀ with hz | hsu | e
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e hne

end

end Core

namespace Peano

open Core
open Addition (gone gone2)

/-- The number of interactions of `m * n`. -/
def prodCost (m n : Nat) : Nat := (m + 1) * (n + 2) + m * (n + 1)

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
