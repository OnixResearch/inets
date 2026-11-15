import InteractionNets.JoinFast

/-! # How long a walk takes

The two sides of a walk move in turn, the first side first, and a side that
is no longer going lets the other move.  If the first side goes for `r₁`
segments and the second for `r₂`, the walk has found what it finds after
`r₁ + r₂` advances (`JWalk.found_by`); if the side that goes for fewer
segments stops (rather than reaching a principal port), it has found it
after at most twice as many (`JWalk.found_stop₁`, `JWalk.found_stop₂`).
-/

namespace INet

variable {S : Type}

/-- `n` segments along one side. -/
def JCur.iter (X : XNet S) (o : Port) : Nat → JCur S → JCur S
  | 0, c => c
  | n + 1, c => (JCur.iter X o n c).next X o

theorem JCur.next_rest {X : XNet S} {o : Port} {c : JCur S} (h : c.going = false) :
    c.next X o = c := by
  cases c with
  | go _ _ => cases h
  | prin _ _ => rfl
  | stop => rfl

/-- A side that has stopped going stays as it is. -/
theorem JCur.iter_rest {X : XNet S} {o : Port} {c : JCur S} {r : Nat}
    (h : (JCur.iter X o r c).going = false) : ∀ i, r ≤ i → JCur.iter X o i c = JCur.iter X o r c
  | i, hi => by
    induction i with
    | zero =>
      obtain rfl : r = 0 := by omega
      rfl
    | succ i ih =>
      rcases Nat.lt_or_ge i r with h' | h'
      · obtain rfl : r = i + 1 := by omega
        rfl
      · show (JCur.iter X o i c).next X o = _
        rw [ih h']
        exact JCur.next_rest h

theorem JWalk.iter_succ (X : XNet S) : ∀ (n : Nat) (w : JWalk S),
    JWalk.iter X (n + 1) w = (JWalk.iter X n w).advance X
  | 0, _ => rfl
  | n + 1, w => JWalk.iter_succ X n (w.advance X)

/-- A walk both of whose sides are done has found what it finds. -/
theorem JWalk.found_rest {w : JWalk S} (h₁ : w.c₁.going = false) (h₂ : w.c₂.going = false) :
    w.found ≠ none := by
  obtain ⟨s₁, s₂, c₁, c₂, t⟩ := w
  dsimp only at h₁ h₂
  cases c₁ with
  | go _ _ => cases h₁
  | stop => simp [JWalk.found]
  | prin i γ =>
    cases c₂ with
    | go _ _ => cases h₂
    | stop => simp [JWalk.found]
    | prin _ _ => simp [JWalk.found]

/-- Where a walk is after `n` advances: `a` segments along the first side
and `b` along the second, with `a + b = n`. -/
theorem JWalk.iter_shape (X : XNet S) (w : JWalk S) {r₁ r₂ : Nat}
    (h₁ : ∀ i, (JCur.iter X w.s₂ i w.c₁).going = true ↔ i < r₁)
    (h₂ : ∀ i, (JCur.iter X w.s₁ i w.c₂).going = true ↔ i < r₂) :
    ∀ n, ∃ a b t, JWalk.iter X n w =
        ⟨w.s₁, w.s₂, JCur.iter X w.s₂ a w.c₁, JCur.iter X w.s₁ b w.c₂, t⟩ ∧
      a + b = n ∧ a ≤ r₁ ∧ (b ≤ r₂ ∨ a = r₁)
  | 0 => ⟨0, 0, w.turn, rfl, rfl, Nat.zero_le _, .inl (Nat.zero_le _)⟩
  | n + 1 => by
    obtain ⟨a, b, t, e, hab, ha, hb⟩ := JWalk.iter_shape X w h₁ h₂ n
    rw [JWalk.iter_succ, e]
    unfold JWalk.advance
    dsimp only
    split
    · rename_i hc
      have hg : (JCur.iter X w.s₂ a w.c₁).going = true := by
        simp only [Bool.and_eq_true] at hc
        exact hc.1
      have := (h₁ a).1 hg
      exact ⟨a + 1, b, false, rfl, by omega, by omega, by omega⟩
    · rename_i hc
      refine ⟨a, b + 1, true, rfl, by omega, ha, ?_⟩
      cases hg : (JCur.iter X w.s₂ a w.c₁).going
      · have : ¬ a < r₁ := fun h => by rw [(h₁ a).2 h] at hg; cases hg
        exact .inr (by omega)
      · rw [hg] at hc
        cases ht : t <;> rw [ht] at hc
        · cases hg₂ : (JCur.iter X w.s₁ b w.c₂).going
          · rw [hg₂] at hc
            exact absurd rfl hc
          · have := (h₂ b).1 hg₂
            exact .inl (by omega)
        · exact absurd rfl hc

/-- **A walk has found what it finds after `r₁ + r₂` advances.** -/
theorem JWalk.found_by (X : XNet S) (w : JWalk S) {r₁ r₂ : Nat}
    (h₁ : ∀ i, (JCur.iter X w.s₂ i w.c₁).going = true ↔ i < r₁)
    (h₂ : ∀ i, (JCur.iter X w.s₁ i w.c₂).going = true ↔ i < r₂) :
    (JWalk.iter X (r₁ + r₂) w).found ≠ none := by
  obtain ⟨a, b, t, e, hab, ha, hb⟩ := JWalk.iter_shape X w h₁ h₂ (r₁ + r₂)
  rw [e]
  apply JWalk.found_rest
  · show (JCur.iter X w.s₂ a w.c₁).going = false
    cases hg : (JCur.iter X w.s₂ a w.c₁).going
    · rfl
    · have := (h₁ a).1 hg
      omega
  · show (JCur.iter X w.s₁ b w.c₂).going = false
    cases hg : (JCur.iter X w.s₁ b w.c₂).going
    · rfl
    · have := (h₂ b).1 hg
      omega

/-- While both sides are going, they take turns, the first side first. -/
theorem JWalk.iter_both (X : XNet S) (w : JWalk S) (ht : w.turn = true) {r₁ r₂ : Nat}
    (h₁ : ∀ i, (JCur.iter X w.s₂ i w.c₁).going = true ↔ i < r₁)
    (h₂ : ∀ i, (JCur.iter X w.s₁ i w.c₂).going = true ↔ i < r₂) :
    ∀ n, (∀ m, m < n → (m + 1) / 2 < r₁ ∧ m / 2 < r₂) →
      JWalk.iter X n w = ⟨w.s₁, w.s₂, JCur.iter X w.s₂ ((n + 1) / 2) w.c₁,
        JCur.iter X w.s₁ (n / 2) w.c₂, decide (n % 2 = 0)⟩
  | 0, _ => by
    obtain ⟨s₁, s₂, c₁, c₂, t⟩ := w
    dsimp only at ht
    subst ht
    rfl
  | n + 1, hm => by
    rw [JWalk.iter_succ, JWalk.iter_both X w ht h₁ h₂ n (fun m hm' => hm m (by omega))]
    obtain ⟨hn₁, hn₂⟩ := hm n (by omega)
    have g₁ := (h₁ _).2 hn₁
    have g₂ := (h₂ _).2 hn₂
    unfold JWalk.advance
    dsimp only
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · rw [ite_pos' (by simp [g₁, hp])]
      have e₁ : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have e₂ : (n + 1) / 2 = n / 2 := by omega
      have e₃ : (n + 1) % 2 = 1 := by omega
      rw [e₁, e₂, e₃]
      rfl
    · rw [ite_neg' (by simp [g₂, hp])]
      have e₁ : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      have e₂ : (n + 1) / 2 = n / 2 + 1 := by omega
      have e₃ : (n + 1) % 2 = 0 := by omega
      rw [e₁, e₂, e₃]
      rfl

/-- **If the first side stops after `r₁` segments, no more than the second
side goes, the walk has found what it finds after `2 r₁ - 1` advances.** -/
theorem JWalk.found_stop₁ (X : XNet S) (w : JWalk S) (ht : w.turn = true) {r₁ r₂ : Nat}
    (h₁ : ∀ i, (JCur.iter X w.s₂ i w.c₁).going = true ↔ i < r₁)
    (h₂ : ∀ i, (JCur.iter X w.s₁ i w.c₂).going = true ↔ i < r₂)
    (hr : r₁ ≤ r₂) (hp : 1 ≤ r₁) (hs : JCur.iter X w.s₂ r₁ w.c₁ = .stop) :
    (JWalk.iter X (2 * r₁ - 1) w).found ≠ none := by
  rw [JWalk.iter_both X w ht h₁ h₂ _ (fun m hm => ⟨by omega, by omega⟩)]
  have e : (2 * r₁ - 1 + 1) / 2 = r₁ := by omega
  rw [e, hs]
  simp [JWalk.found]

/-- **If the second side stops after `r₂` segments, fewer than the first
side goes, the walk has found what it finds after `2 r₂` advances.** -/
theorem JWalk.found_stop₂ (X : XNet S) (w : JWalk S) (ht : w.turn = true) {r₁ r₂ : Nat}
    (h₁ : ∀ i, (JCur.iter X w.s₂ i w.c₁).going = true ↔ i < r₁)
    (h₂ : ∀ i, (JCur.iter X w.s₁ i w.c₂).going = true ↔ i < r₂)
    (hr : r₂ < r₁) (hs : JCur.iter X w.s₁ r₂ w.c₂ = .stop) :
    (JWalk.iter X (2 * r₂) w).found ≠ none := by
  rw [JWalk.iter_both X w ht h₁ h₂ _ (fun m hm => ⟨by omega, by omega⟩)]
  have e : 2 * r₂ / 2 = r₂ := by omega
  rw [e, hs]
  cases JCur.iter X w.s₂ ((2 * r₂ + 1) / 2) w.c₁ <;> simp [JWalk.found]

/-- The point a side has reached. -/
def JCur.pt : JCur S → Port
  | .go _ c => c
  | _ => ([], 0)

section Side

variable {ar : S → Nat} {N : Net S} {X : XNet S} {o p : Port}

/-- The `i`-th point of the side that starts at `p`, coming from `o`. -/
def sidePt (X : XNet S) (o p : Port) (i : Nat) : Port := (JCur.iter X o i (.go o p)).pt

theorem going_pred {c : JCur S} {i : Nat} (h : (JCur.iter X o (i + 1) c).going = true) :
    (JCur.iter X o i c).going = true := by
  cases hg : (JCur.iter X o i c).going
  · have e : JCur.iter X o (i + 1) c = JCur.iter X o i c := JCur.next_rest hg
    rw [e, hg] at h
    cases h
  · rfl

/-- **While a side goes, it goes along a path**: its points are linked one
to the next, they are different, and none is the start of the other side. -/
theorem side_go (hN : N.WF ar) (hX : X.Like N) (hpo : N.link p o) :
    ∀ i, (JCur.iter X o i (.go o p)).going = true →
      JCur.iter X o i (.go o p) =
          .go (if i = 0 then o else sidePt X o p (i - 1)) (sidePt X o p i) ∧
        (∀ k, k < i → N.link (sidePt X o p k) (sidePt X o p (k + 1))) ∧
        (∀ k l, k ≤ i → l ≤ i → sidePt X o p k = sidePt X o p l → k = l) ∧
        (∀ k, k ≤ i → sidePt X o p k ≠ o)
  | 0, _ => by
    refine ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _), fun k l hk hl _ => by omega,
      fun k hk e => ?_⟩
    obtain rfl : k = 0 := by omega
    change p = o at e
    subst e
    exact hN.irrefl hpo
  | i + 1, hg => by
    obtain ⟨e, hl, hi, ho⟩ := side_go hN hX hpo i (going_pred hg)
    -- the point before, linked to the point reached
    have hprev : N.link (sidePt X o p i) (if i = 0 then o else sidePt X o p (i - 1)) := by
      split
      · rename_i h0
        subst h0
        exact hpo
      · rename_i h0
        have := hl (i - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        exact hN.symm this
    have hs : JCur.iter X o (i + 1) (.go o p) =
        JCur.next X o (.go (if i = 0 then o else sidePt X o p (i - 1)) (sidePt X o p i)) := by
      show (JCur.iter X o i (.go o p)).next X o = _
      rw [e]
    rw [hs] at hg
    unfold JCur.next at hg hs
    dsimp only at hg hs
    cases hns : nextSeg X.wires (sidePt X o p i) (if i = 0 then o else sidePt X o p (i - 1)) with
    | none =>
      exfalso
      rw [hns] at hg
      dsimp only at hg
      split at hg
      · split at hg <;> cases hg
      · cases hg
    | some n =>
      rw [hns] at hg hs
      dsimp only at hg hs
      by_cases hno : n = o
      · rw [ite_pos' hno] at hg
        cases hg
      rw [ite_neg' hno] at hs
      obtain ⟨hmem, hnp⟩ := nextSeg_spec hns
      have hln : N.link (sidePt X o p i) n := (hX.2 _ _).1 hmem
      have hpt : sidePt X o p (i + 1) = n := by
        show (JCur.iter X o (i + 1) (.go o p)).pt = n
        rw [hs]
        rfl
      have hfresh : ∀ k, k ≤ i → n ≠ sidePt X o p k := by
        intro k hk hnk
        rcases Nat.lt_or_ge k i with hki | hki
        · by_cases hk1 : k + 1 = i
          · apply hnp
            rw [hnk, ite_neg' (by omega)]
            congr 1
            omega
          · -- three different points linked to the `k`-th
            have hA : N.link (sidePt X o p k) (if k = 0 then o else sidePt X o p (k - 1)) := by
              split
              · rename_i h0
                subst h0
                exact hpo
              · have := hl (k - 1) (by omega)
                rw [Nat.sub_add_cancel (by omega)] at this
                exact hN.symm this
            have hB : N.link (sidePt X o p k) (sidePt X o p (k + 1)) := hl k (by omega)
            have hC : N.link (sidePt X o p k) (sidePt X o p i) := hN.symm (hnk ▸ hln)
            rcases hN.deg hA hB hC with h | h | h
            · split at h
              · exact ho (k + 1) (by omega) h.symm
              · exact absurd (hi _ _ (by omega) (by omega) h) (by omega)
            · split at h
              · exact ho i (Nat.le_refl _) h.symm
              · exact absurd (hi _ _ (by omega) (by omega) h) (by omega)
            · exact absurd (hi _ _ (by omega) (by omega) h) (by omega)
        · obtain rfl : k = i := by omega
          exact hN.irrefl (hnk ▸ hln)
      refine ⟨?_, fun k hk => ?_, fun k l hk hl' ekl => ?_, fun k hk => ?_⟩
      · rw [hs, hpt, ite_neg' (by omega)]
        rfl
      · rcases Nat.lt_or_ge k i with h | h
        · exact hl k h
        · obtain rfl : k = i := by omega
          rw [hpt]
          exact hln
      · rcases Nat.lt_or_ge k (i + 1) with h₁ | h₁ <;> rcases Nat.lt_or_ge l (i + 1) with h₂ | h₂
        · exact hi k l (by omega) (by omega) ekl
        · obtain rfl : l = i + 1 := by omega
          rw [hpt] at ekl
          exact absurd ekl.symm (hfresh k (by omega))
        · obtain rfl : k = i + 1 := by omega
          rw [hpt] at ekl
          exact absurd ekl (hfresh l (by omega))
        · omega
      · rcases Nat.lt_or_ge k (i + 1) with h | h
        · exact ho k (by omega)
        · obtain rfl : k = i + 1 := by omega
          rw [hpt]
          exact hno

theorem first_false_aux (P : Nat → Bool) : ∀ n, (∀ i, i ≤ n → P i = true) ∨
    ∃ r, r ≤ n ∧ P r = false ∧ ∀ i, i < r → P i = true
  | 0 => by
    cases h : P 0
    · exact .inr ⟨0, Nat.le_refl _, h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
    · refine .inl fun i hi => ?_
      obtain rfl : i = 0 := by omega
      exact h
  | n + 1 => by
    rcases first_false_aux P n with hall | ⟨r, hr, hf, hl⟩
    · cases h : P (n + 1)
      · exact .inr ⟨n + 1, Nat.le_refl _, h, fun i hi => hall i (by omega)⟩
      · refine .inl fun i hi => ?_
        rcases Nat.lt_or_ge i (n + 1) with h' | h'
        · exact hall i (by omega)
        · obtain rfl : i = n + 1 := by omega
          exact h
    · exact .inr ⟨r, by omega, hf, hl⟩

/-- The first place where a test fails, if it fails somewhere. -/
theorem first_false (P : Nat → Bool) (n : Nat) (h : P n = false) :
    ∃ r, r ≤ n ∧ P r = false ∧ ∀ i, i < r → P i = true := by
  rcases first_false_aux P n with hall | hr
  · rw [hall n (Nat.le_refl _)] at h
    cases h
  · exact hr

/-- **A side goes for some number `r` of segments, at most the number of
segments of a list holding every segment.** -/
theorem side_len (hN : N.WF ar) (hX : X.Like N) (hpo : N.link p o) {W : List (Port × Port)}
    (hW : ∀ {u v}, N.link u v → (u, v) ∈ W) :
    ∃ r, 1 ≤ r ∧ r ≤ W.length ∧ ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r := by
  have bound : ∀ i, (JCur.iter X o i (.go o p)).going = true → i < W.length := by
    intro i hg
    obtain ⟨-, hl, hi, -⟩ := side_go hN hX hpo i hg
    have hnd : ((List.range (i + 1)).map (sidePt X o p)).Nodup := by
      unfold List.Nodup
      rw [List.pairwise_map]
      exact List.nodup_range.imp_of_mem fun hk hl' hne e =>
        hne (hi _ _ (by simp at hk; omega) (by simp at hl'; omega) e)
    have hsub : (List.range (i + 1)).map (sidePt X o p) ⊆ W.map Prod.fst := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      simp only [List.mem_range] at hk
      have hlk : ∃ y, N.link (sidePt X o p k) y := by
        rcases Nat.lt_or_ge k i with h | h
        · exact ⟨_, hl k h⟩
        · obtain rfl : k = i := by omega
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · subst h0
            exact ⟨o, hpo⟩
          · have := hl (k - 1) (by omega)
            rw [Nat.sub_add_cancel h0] at this
            exact ⟨_, hN.symm this⟩
      obtain ⟨y, hy⟩ := hlk
      exact List.mem_map.2 ⟨_, hW hy, rfl⟩
    have := hnd.length_le_of_subset hsub
    simp at this
    omega
  obtain ⟨r, hr, hfirst, hgo⟩ := first_false (fun i => (JCur.iter X o i (.go o p)).going)
    W.length (by
      cases hg : (JCur.iter X o W.length (.go o p)).going
      · rfl
      · exact absurd (bound _ hg) (Nat.lt_irrefl _))
  refine ⟨r, ?_, hr, fun i => ⟨fun hg => ?_, fun hi => hgo i hi⟩⟩
  · rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      cases hfirst
    · exact h
  · rcases Nat.lt_or_ge i r with h | h
    · exact h
    · rw [JCur.iter_rest hfirst i h, hfirst] at hg
      cases hg

/-- **How a side ends**, after its last point `f i`: either the segment on
from there leads to the start of the other side, and the side stops (a
loop), or there is no segment on, and the side stops or has reached the
principal port of an agent. -/
theorem side_end (hN : N.WF ar) (hX : X.Like N) (hpo : N.link p o) {r : Nat} (hr : 1 ≤ r)
    (h : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r) :
    (N.link (sidePt X o p (r - 1)) o ∧
        o ≠ (if r - 1 = 0 then o else sidePt X o p (r - 1 - 1)) ∧
        JCur.iter X o r (.go o p) = .stop) ∨
      ((∀ n, N.link (sidePt X o p (r - 1)) n →
          n = (if r - 1 = 0 then o else sidePt X o p (r - 1 - 1))) ∧
        (JCur.iter X o r (.go o p) = .stop ∨
          ∃ γ, JCur.iter X o r (.go o p) = .prin (sidePt X o p (r - 1)).1 γ ∧
            (sidePt X o p (r - 1)).2 = 0 ∧ N.agent (sidePt X o p (r - 1)).1 γ)) := by
  obtain ⟨e, -⟩ := side_go hN hX hpo (r - 1) ((h _).2 (by omega))
  have hs : JCur.iter X o r (.go o p) = JCur.next X o
      (.go (if r - 1 = 0 then o else sidePt X o p (r - 1 - 1)) (sidePt X o p (r - 1))) := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    show (JCur.iter X o r' (.go o p)).next X o = _
    simp only [Nat.add_sub_cancel] at e ⊢
    rw [e]
  unfold JCur.next at hs
  dsimp only at hs
  cases hns : nextSeg X.wires (sidePt X o p (r - 1))
      (if r - 1 = 0 then o else sidePt X o p (r - 1 - 1)) with
  | some n =>
    rw [hns] at hs
    dsimp only at hs
    obtain ⟨hmem, hnp⟩ := nextSeg_spec hns
    by_cases hno : n = o
    · subst hno
      exact .inl ⟨(hX.2 _ _).1 hmem, hnp, by rw [hs, ite_pos' rfl]⟩
    · exfalso
      rw [ite_neg' hno] at hs
      have := (h r).1
      rw [hs] at this
      exact absurd (this rfl) (Nat.lt_irrefl _)
  | none =>
    rw [hns] at hs
    dsimp only at hs
    refine .inr ⟨fun n hn => ?_, ?_⟩
    · exact Classical.byContradiction fun hne => nextSeg_ne_none ((hX.2 _ _).2 hn) hne hns
    · split at hs
      · rename_i h0
        cases hag : assoc (sidePt X o p (r - 1)).1 X.agents with
        | none =>
          rw [hag] at hs
          exact .inl hs
        | some γ =>
          rw [hag] at hs
          exact .inr ⟨γ, hs, h0, (hX.1 _ _).1 (assoc_mem hag)⟩
      · exact .inl hs

end Side

end INet
