/-! # Abstract rewriting

Results about an arbitrary relation `r : A → A → Prop`, with no reference to
nets: from the one-step diamond property on terms satisfying an invariant
(`StrongConfluent`), confluence with equal path lengths (`confluence`),
uniqueness of normal forms and of the length of every reduction to them
(`normal_unique`), and the bound that no reduction is longer than one that
reaches a normal form (`bounded`).

This module imports nothing, so a development with its own step relation
can import it alone.
-/

namespace INet

universe u

section Rewriting

variable {A : Type u} {P : A → Prop} {r : A → A → Prop}

/-- `Steps r n a b`: `a` rewrites to `b` in exactly `n` steps of `r`. -/
inductive Steps (r : A → A → Prop) : Nat → A → A → Prop
  | refl (a : A) : Steps r 0 a a
  | head {n : Nat} {a b c : A} : r a b → Steps r n b c → Steps r (n + 1) a c

theorem Steps.single {a b : A} (h : r a b) : Steps r 1 a b :=
  .head h (.refl b)

theorem Steps.trans {n m : Nat} {a b c : A}
    (h₁ : Steps r n a b) (h₂ : Steps r m b c) : Steps r (n + m) a c := by
  induction h₁ with
  | refl a => simpa using h₂
  | head h _ ih =>
    rw [Nat.add_right_comm]
    exact .head h (ih h₂)

/-- A term is normal when no step leaves it. -/
def Normal (r : A → A → Prop) (a : A) : Prop := ∀ b, ¬ r a b

theorem Steps.of_normal {n : Nat} {a b : A} (ha : Normal r a) (h : Steps r n a b) :
    n = 0 ∧ a = b := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | head h _ => exact absurd h (ha _)

/-- Strong confluence of `r` on the terms satisfying an invariant `P`:
two different one-step reducts of the same term are joined by one step each. -/
structure StrongConfluent (P : A → Prop) (r : A → A → Prop) : Prop where
  inv : ∀ {a b}, P a → r a b → P b
  diamond : ∀ {a b c}, P a → r a b → r a c → b = c ∨ ∃ d, r b d ∧ r c d

namespace StrongConfluent

theorem inv_steps (h : StrongConfluent P r) {n : Nat} {a b : A}
    (ha : P a) (hs : Steps r n a b) : P b := by
  induction hs with
  | refl => exact ha
  | head h₁ _ ih => exact ih (h.inv ha h₁)

theorem strip (h : StrongConfluent P r) {m : Nat} {a b c : A}
    (ha : P a) (hab : r a b) (hac : Steps r m a c) :
    ∃ d k l, Steps r k b d ∧ Steps r l c d ∧ 1 + k = m + l := by
  induction hac generalizing b with
  | refl a => exact ⟨b, 0, 1, .refl b, .single hab, rfl⟩
  | @head m a c₁ c hac₁ hrest ih =>
    rcases h.diamond ha hab hac₁ with rfl | ⟨e, hbe, hce⟩
    · exact ⟨c, m, 0, hrest, .refl c, by omega⟩
    · obtain ⟨d, k, l, hk, hl, e⟩ := ih (h.inv ha hac₁) hce
      exact ⟨d, k + 1, l, .head hbe hk, hl, by omega⟩

/-- Confluence with step counts: two reductions of the same term can be
completed to a common reduct, and the two completed paths have equal length. -/
theorem confluence (h : StrongConfluent P r) {n m : Nat} {a b c : A}
    (ha : P a) (h₁ : Steps r n a b) (h₂ : Steps r m a c) :
    ∃ d k l, Steps r k b d ∧ Steps r l c d ∧ n + k = m + l := by
  induction h₁ generalizing m c with
  | refl a => exact ⟨c, m, 0, h₂, .refl c, by omega⟩
  | @head n a a₁ b hab hrest ih =>
    obtain ⟨d₁, k₁, l₁, hk₁, hl₁, e₁⟩ := h.strip ha hab h₂
    obtain ⟨d, k, l, hk, hl, e⟩ := ih (h.inv ha hab) hk₁
    exact ⟨d, k, l₁ + l, hk, hl₁.trans hl, by omega⟩

theorem normal_unique (h : StrongConfluent P r) {n m : Nat} {a b c : A}
    (ha : P a) (h₁ : Steps r n a b) (h₂ : Steps r m a c)
    (hb : Normal r b) (hc : Normal r c) : b = c ∧ n = m := by
  obtain ⟨d, k, l, hk, hl, e⟩ := h.confluence ha h₁ h₂
  obtain ⟨rfl, rfl⟩ := hk.of_normal hb
  obtain ⟨rfl, rfl⟩ := hl.of_normal hc
  exact ⟨rfl, by omega⟩

theorem bounded (h : StrongConfluent P r) {n m : Nat} {a b c : A}
    (ha : P a) (h₁ : Steps r n a b) (hb : Normal r b) (h₂ : Steps r m a c) :
    m ≤ n ∧ Steps r (n - m) c b := by
  obtain ⟨d, k, l, hk, hl, e⟩ := h.confluence ha h₁ h₂
  obtain ⟨rfl, rfl⟩ := hk.of_normal hb
  have hl' : l = n - m := by omega
  exact ⟨by omega, hl' ▸ hl⟩

end StrongConfluent

end Rewriting

end INet
