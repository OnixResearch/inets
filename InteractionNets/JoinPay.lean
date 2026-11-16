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

/-- The point a side came from before its `i`-th point. -/
def sidePrev (X : XNet S) (o p : Port) (i : Nat) : Port :=
  if i = 0 then o else sidePt X o p (i - 1)

/-- **A side that ends without a loop is all its points can reach**: every
point linked to one of them is the one before or the one after. -/
theorem side_nb (hN : N.WF ar) (hX : X.Like N) (hpo : N.link p o) {r : Nat} (hr : 1 ≤ r)
    (h : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r)
    (hend : ∀ n, N.link (sidePt X o p (r - 1)) n → n = sidePrev X o p (r - 1)) :
    ∀ i n, i ≤ r - 1 → N.link (sidePt X o p i) n →
      n = sidePrev X o p i ∨ (i < r - 1 ∧ n = sidePt X o p (i + 1)) := by
  obtain ⟨-, hl, hi, ho⟩ := side_go hN hX hpo (r - 1) ((h _).2 (by omega))
  intro i n hir hn
  rcases Nat.lt_or_ge i (r - 1) with hlt | hge
  · have hA : N.link (sidePt X o p i) (sidePrev X o p i) := by
      unfold sidePrev
      split
      · rename_i h0
        subst h0
        exact hpo
      · have := hl (i - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        exact hN.symm this
    have hB := hl i hlt
    rcases hN.deg hA hB hn with e | e | e
    · exfalso
      unfold sidePrev at e
      split at e
      · exact ho (i + 1) (by omega) e.symm
      · exact absurd (hi _ _ (by omega) (by omega) e) (by omega)
    · exact .inl e.symm
    · exact .inr ⟨hlt, e.symm⟩
  · obtain rfl : i = r - 1 := by omega
    exact .inl (hend n hn)

/-- **Two sides that start at the two ends of a segment, one of which ends
without a loop, meet no point in common.** -/
theorem sides_apart (hN : N.WF ar) (hX : X.Like N) (hpo : N.link p o) {r r' : Nat}
    (hr : 1 ≤ r) (h : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r)
    (h' : ∀ i, (JCur.iter X p i (.go p o)).going = true ↔ i < r')
    (hend : ∀ n, N.link (sidePt X o p (r - 1)) n → n = sidePrev X o p (r - 1)) :
    ∀ l, l < r' → ∀ k, k ≤ r - 1 → sidePt X p o l ≠ sidePt X o p k := by
  have hop : N.link o p := hN.symm hpo
  obtain ⟨-, hl, hi, ho⟩ := side_go hN hX hpo (r - 1) ((h _).2 (by omega))
  have nb := side_nb hN hX hpo hr h hend
  intro l
  induction l with
  | zero =>
    intro _ k _ e
    exact ho k (by omega) e.symm
  | succ l ih =>
    intro hl' k hk e
    obtain ⟨-, hl₂, hi₂, ho₂⟩ := side_go hN hX hop (l + 1) ((h' _).2 hl')
    have hlink : N.link (sidePt X o p k) (sidePt X p o l) := e ▸ hN.symm (hl₂ l (by omega))
    rcases nb k _ hk hlink with e' | ⟨hk', e'⟩
    · unfold sidePrev at e'
      split at e'
      · rename_i h0
        subst h0
        cases l with
        | zero => exact ho₂ 1 (Nat.le_refl _) e
        | succ l =>
          -- the other side came back to its start
          have : sidePt X p o (l + 1) = sidePt X p o 0 := e'
          exact absurd (hi₂ _ _ (by omega) (by omega) this) (by omega)
      · exact ih (by omega) (k - 1) (by omega) e'
    · exact ih (by omega) (k + 1) (by omega) e'

/-- Before its last point, a side meets only the point before and the
point after. -/
theorem side_mid (hN : N.WF ar) (hX : X.Like N) (hpo : N.link p o) {r : Nat}
    (h : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r) {i : Nat} (hi : i < r - 1)
    {n : Port} (hn : N.link (sidePt X o p i) n) :
    n = sidePrev X o p i ∨ n = sidePt X o p (i + 1) := by
  obtain ⟨-, hl, hin, ho⟩ := side_go hN hX hpo (r - 1) ((h _).2 (by omega))
  have hA : N.link (sidePt X o p i) (sidePrev X o p i) := by
    unfold sidePrev
    split
    · rename_i h0
      subst h0
      exact hpo
    · have := hl (i - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at this
      exact hN.symm this
  rcases hN.deg hA (hl i hi) hn with e | e | e
  · exfalso
    unfold sidePrev at e
    split at e
    · exact ho (i + 1) (by omega) e.symm
    · exact absurd (hin _ _ (by omega) (by omega) e) (by omega)
  · exact .inl e.symm
  · exact .inr e.symm

end Side

section Pay

variable {ar : S → Nat} {G N : Net S} {X : XNet S} {p o : Port}

/-- The net `N` is `G` with a segment added between `p` and `o`, two
points that lie on one segment of `G` at most, neither of them a principal
port. -/
structure Joined (G N : Net S) (p o : Port) : Prop where
  link : ∀ u v, N.link u v ↔ G.link u v ∨ (u = p ∧ v = o) ∨ (u = o ∧ v = p)
  endp : ∀ x y, G.link p x → G.link p y → x = y
  endo : ∀ x y, G.link o x → G.link o y → x = y
  p0 : p.2 ≠ 0
  o0 : o.2 ≠ 0

theorem Joined.swap (hJ : Joined G N p o) : Joined G N o p :=
  ⟨fun u v => by
    rw [hJ.link]
    constructor
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h), hJ.endo, hJ.endp, hJ.o0, hJ.p0⟩

theorem Joined.le (hJ : Joined G N p o) {u v : Port} (h : G.link u v) : N.link u v :=
  (hJ.link u v).2 (.inl h)

theorem Joined.pair (hJ : Joined G N p o) : N.link p o :=
  (hJ.link p o).2 (.inr (.inl ⟨rfl, rfl⟩))

/-- A segment of `N` between two points other than `o` is a segment of `G`. -/
theorem Joined.old (hJ : Joined G N p o) {u v : Port} (h : N.link u v) (hu : u ≠ o)
    (hv : v ≠ o) : G.link u v := by
  rcases (hJ.link u v).1 h with h | ⟨-, e⟩ | ⟨e, -⟩
  · exact h
  · exact absurd e hv
  · exact absurd e hu

theorem Joined.old' (hJ : Joined G N p o) {u v : Port} (h : N.link u v)
    (h₁ : ¬ (u = p ∧ v = o)) (h₂ : ¬ (u = o ∧ v = p)) : G.link u v := by
  rcases (hJ.link u v).1 h with h | h | h
  · exact h
  · exact absurd h h₁
  · exact absurd h h₂

/-- **A side that ends without a loop, after two points at least, runs
along a path of `G` that a trail cannot leave.** -/
theorem side_isPath (hN : N.WF ar) (hJ : Joined G N p o) (hX : X.Like N) {r : Nat}
    (hr : 2 ≤ r) (h : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r)
    (hend : ∀ n, N.link (sidePt X o p (r - 1)) n → n = sidePrev X o p (r - 1)) :
    IsPath G.link (sidePt X o p) (r - 1) := by
  obtain ⟨-, hl, hi, ho⟩ := side_go hN hX hJ.pair (r - 1) ((h _).2 (by omega))
  have nb := side_nb hN hX hJ.pair (by omega) h hend
  have gl : ∀ i, i < r - 1 → G.link (sidePt X o p i) (sidePt X o p (i + 1)) :=
    fun i hi' => hJ.old (hl i hi') (ho i (by omega)) (ho (i + 1) (by omega))
  refine ⟨gl, hi, fun i n hir hn => ?_⟩
  rcases nb i n hir (hJ.le hn) with e | ⟨hlt, e⟩
  · unfold sidePrev at e
    split at e
    · rename_i h0
      subst h0 e
      exfalso
      have := hJ.endp _ _ hn (gl 0 (by omega))
      exact ho 1 (by omega) this.symm
    · exact .inl ⟨by omega, e⟩
  · exact .inr ⟨hlt, e⟩

/-- **A side that meets the other start runs, with that start, along a
path of `G` that a trail cannot leave**, of two points at least before it. -/
theorem loop_isPath (hN : N.WF ar) (hJ : Joined G N p o) (hX : X.Like N) {r : Nat}
    (hr : 1 ≤ r) (h : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r)
    (hlo : N.link (sidePt X o p (r - 1)) o) (hpr : o ≠ sidePrev X o p (r - 1)) :
    2 ≤ r ∧ IsPath G.link (fun i => if i ≤ r - 1 then sidePt X o p i else o) r := by
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with h' | h'
    · obtain rfl : r = 1 := by omega
      exfalso
      simp [sidePrev] at hpr
    · exact h'
  obtain ⟨-, hl, hi, ho⟩ := side_go hN hX hJ.pair (r - 1) ((h _).2 (by omega))
  have gl : ∀ i, i < r - 1 → G.link (sidePt X o p i) (sidePt X o p (i + 1)) :=
    fun i hi' => hJ.old (hl i hi') (ho i (by omega)) (ho (i + 1) (by omega))
  have glast : G.link (sidePt X o p (r - 1)) o := by
    rcases (hJ.link _ _).1 hlo with h' | ⟨e, -⟩ | ⟨e, -⟩
    · exact h'
    · exact absurd (hi _ 0 (Nat.le_refl _) (by omega) e) (by omega)
    · exact absurd e (ho _ (Nat.le_refl _))
  refine ⟨hr2, fun i hi' => ?_, fun a b ha hb e => ?_, fun i n hir hn => ?_⟩
  · rcases Nat.lt_or_ge i (r - 1) with h₁ | h₁
    · rw [ite_pos' (by omega), ite_pos' (by omega)]
      exact gl i h₁
    · obtain rfl : i = r - 1 := by omega
      rw [ite_pos' (Nat.le_refl _), ite_neg' (by omega)]
      exact glast
  · split at e <;> split at e
    · exact hi a b (by omega) (by omega) e
    · exact absurd e (ho a (by omega))
    · exact absurd e.symm (ho b (by omega))
    · omega
  · split at hn
    · rename_i hir'
      have hN' := hJ.le hn
      have first : i = 0 → n ≠ o := by
        rintro rfl rfl
        have := hJ.endp _ _ hn (gl 0 (by omega))
        exact ho 1 (by omega) this.symm
      rcases Nat.lt_or_ge i (r - 1) with h₁ | h₁
      · rcases side_mid hN hX hJ.pair h h₁ hN' with e | e
        · unfold sidePrev at e
          split at e
          · rename_i h0
            exact absurd e (first h0)
          · refine .inl ⟨by omega, ?_⟩
            rw [ite_pos' (by omega)]
            exact e
        · refine .inr ⟨by omega, ?_⟩
          rw [ite_pos' (by omega)]
          exact e
      · obtain rfl : i = r - 1 := by omega
        have hA : N.link (sidePt X o p (r - 1)) (sidePrev X o p (r - 1)) := by
          unfold sidePrev
          rw [ite_neg' (by omega)]
          have := hl (r - 1 - 1) (by omega)
          rw [Nat.sub_add_cancel (by omega)] at this
          exact hN.symm this
        rcases hN.deg hA hlo hN' with e | e | e
        · exact absurd e.symm hpr
        · refine .inl ⟨by omega, ?_⟩
          rw [ite_pos' (by omega), ← e]
          unfold sidePrev
          rw [ite_neg' (by omega)]
        · refine .inr ⟨by omega, ?_⟩
          rw [ite_neg' (by omega)]
          exact e.symm
    · obtain rfl : i = r := by omega
      have hfp : sidePt X o p (i - 1) ≠ p := fun e =>
        absurd (hi _ 0 (Nat.le_refl _) (by omega) e) (by omega)
      have g' : G.link o (sidePt X o p (i - 1)) :=
        hJ.old' (hN.symm hlo) (fun ⟨_, e⟩ => ho _ (Nat.le_refl _) e) (fun ⟨_, e⟩ => hfp e)
      refine .inl ⟨by omega, ?_⟩
      rw [ite_pos' (Nat.le_refl _)]
      exact hJ.endo _ _ hn g'

/-- **The measure that pays for the walks**: four times the sum of the
logarithms of the longest trails from the first points of the entries of
`W`, twice the sum of the longest trails from the principal ports of the
names of `l`, and twice the number of entries of `W` whose first point
lies on a cycle. -/
noncomputable def payΦ (K : Nat) (W : List (Port × Port)) (l : List Id) (G : Net S) : Nat :=
  4 * (W.map fun e => Nat.log2 (lfar G.link K e.1)).sum +
    2 * (l.map fun i => lfar G.link K (i, 0)).sum +
    2 * (W.map fun e => cycAt G.link e.1).sum

theorem payΦ_mono {K : Nat} {W : List (Port × Port)} {l : List Id} {G N : Net S}
    (h : ∀ {u v}, G.link u v → N.link u v) : payΦ K W l G ≤ payΦ K W l N := by
  unfold payΦ
  have h₁ := sum_mono W _ _ fun e _ => log2_mono (lfar_mono (L := G.link) (L' := N.link) h K e.1)
  have h₂ := sum_mono l _ _ fun i _ => lfar_mono (L := G.link) (L' := N.link) h K (i, 0)
  have h₃ := sum_mono W _ _ fun e _ => cycAt_mono (L := G.link) (L' := N.link) h e.1
  omega

theorem JCur.rest_cases {c : JCur S} (h : c.going = false) :
    c = .stop ∨ ∃ i γ, c = .prin i γ := by
  cases c with
  | go _ _ => cases h
  | prin i γ => exact .inr ⟨i, γ, rfl⟩
  | stop => exact .inl rfl

/-- **What one side of a walk gains**, when it goes for `r` segments, no
more than the other side: if it stops, the measure grows by `2 r` (less
two); if it reaches a principal port, by `2 r` and twice the length of the
other side (less two). -/
theorem side_gain (hN : N.WF ar) (hJ : Joined G N p o) (hX : X.Like N) {K : Nat}
    {W : List (Port × Port)} {l : List Id} (hW : ∀ {u v}, N.link u v → (u, v) ∈ W)
    (hWK : W.length ≤ K) (hl : ∀ i γ, N.agent i γ → i ∈ l) {r r' : Nat} (hr : 1 ≤ r)
    (h : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r)
    (h' : ∀ i, (JCur.iter X p i (.go p o)).going = true ↔ i < r') (hrr : r ≤ r') :
    (JCur.iter X o r (.go o p) = .stop → 2 * r + payΦ K W l G ≤ 2 + payΦ K W l N) ∧
      (∀ i γ, JCur.iter X o r (.go o p) = .prin i γ →
        2 * r + 2 * r' + payΦ K W l G ≤ 2 + payΦ K W l N) := by
  have hmono := payΦ_mono (K := K) (W := W) (l := l) (fun {u v} h => hJ.le (u := u) (v := v) h)
  have hkey : ∀ {x y}, N.link x y → ∃ e, e ∈ W ∧ e.1 = x := fun hxy => ⟨_, hW hxy, rfl⟩
  have hA := sum_mono W (fun e => Nat.log2 (lfar G.link K e.1))
    (fun e => Nat.log2 (lfar N.link K e.1))
    fun e _ => log2_mono (lfar_mono (L := G.link) (L' := N.link) hJ.le K e.1)
  have hB := sum_mono l (fun i => lfar G.link K (i, 0)) (fun i => lfar N.link K (i, 0))
    fun i _ => lfar_mono (L := G.link) (L' := N.link) hJ.le K (i, 0)
  have hC := sum_mono W (fun e => cycAt G.link e.1) (fun e => cycAt N.link e.1)
    fun e _ => cycAt_mono (L := G.link) (L' := N.link) hJ.le e.1
  rcases side_end hN hX hJ.pair hr h with ⟨hlo, hpr, hst⟩ | ⟨hend, hfin⟩
  · -- a loop: its points come to lie on a cycle
    obtain ⟨hr2, P⟩ := loop_isPath hN hJ hX hr h hlo hpr
    have hw : N.link ((fun i => if i ≤ r - 1 then sidePt X o p i else o) r)
        ((fun i => if i ≤ r - 1 then sidePt X o p i else o) 0) := by
      simp only
      rw [ite_neg' (by omega), ite_pos' (Nat.zero_le _)]
      exact hN.symm hJ.pair
    have hk : ∀ i, i ≤ r → ∃ e, e ∈ W ∧
        e.1 = (fun i => if i ≤ r - 1 then sidePt X o p i else o) i := by
      intro i hi
      rcases Nat.lt_or_ge i r with h₁ | h₁
      · exact hkey (hJ.le (P.link i h₁))
      · obtain rfl : i = r := by omega
        have := P.link (i - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        exact hkey (hN.symm (hJ.le this))
    have := cyc_gain P hr2 hJ.le hw hk
    refine ⟨fun _ => ?_, fun i γ hp => by rw [hst] at hp; cases hp⟩
    unfold payΦ
    omega
  · rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · -- one point: the side stops at once
      obtain rfl : r = 1 := by omega
      have hst : JCur.iter X o 1 (.go o p) = .stop := by
        rcases hfin with e | ⟨γ, -, h0, -⟩
        · exact e
        · exact absurd h0 hJ.p0
      refine ⟨fun _ => by omega, fun i γ hp => by rw [hst] at hp; cases hp⟩
    · have P := side_isPath hN hJ hX hr2 h hend
      have hr' : 1 ≤ r' := by omega
      obtain ⟨-, hgl, hgi, -⟩ := side_go hN hX (hN.symm hJ.pair) (r' - 1) ((h' _).2 (by omega))
      have hap : ∀ i j, i ≤ r - 1 → j ≤ r' - 1 → sidePt X o p i ≠ sidePt X p o j :=
        fun i j hi hj e => sides_apart hN hX hJ.pair hr h h' hend j (by omega) i hi e.symm
      have hfg : N.link (sidePt X o p 0) (sidePt X p o 0) := hJ.pair
      have hk : ∀ i, i ≤ r - 1 → ∃ e, e ∈ W ∧ e.1 = sidePt X o p i := by
        intro i hi
        rcases Nat.lt_or_ge i (r - 1) with h₁ | h₁
        · exact hkey (hJ.le (P.link i h₁))
        · obtain rfl : i = r - 1 := by omega
          have := P.link (r - 1 - 1) (by omega)
          rw [Nat.sub_add_cancel (by omega)] at this
          exact hkey (hN.symm (hJ.le this))
      have hlog := log_gain P hJ.le hN.symm hfg hgl hgi hap (by omega) hW hWK hk
      refine ⟨fun _ => ?_, fun i γ hp => ?_⟩
      · unfold payΦ
        omega
      · rcases hfin with e | ⟨γ', e, h0, hag⟩
        · rw [e] at hp
          cases hp
        · rw [e] at hp
          cases hp
          have hend' := end_gain P hN.symm hJ.le hfg hgl hgi hap hW hWK
          have ept : sidePt X o p (r - 1) = ((sidePt X o p (r - 1)).1, 0) := Prod.ext rfl h0
          rw [ept] at hend'
          have hB' := sum_gain_one l (fun i => lfar G.link K (i, 0)) (fun i => lfar N.link K (i, 0))
            (hl _ _ hag) (fun i _ => lfar_mono (L := G.link) (L' := N.link) hJ.le K (i, 0)) hend'
          unfold payΦ
          omega

/-- **The walk of a joined segment is paid for by the growth of the
measure**, with three to spare: on a memory holding `N`, which is `G` with
the segment added, the walk finds what it finds within `n` advances, where
`n + 1` is at most three and the growth of `payΦ` from `G` to `N`. -/
theorem walk_pays (hN : N.WF ar) (hJ : Joined G N p o) (hX : X.Like N) {K : Nat}
    {W : List (Port × Port)} {l : List Id} (hW : ∀ {u v}, N.link u v → (u, v) ∈ W)
    (hWK : W.length ≤ K) (hl : ∀ i γ, N.agent i γ → i ∈ l) :
    ∃ n, 1 ≤ n ∧ n + 1 + payΦ K W l G ≤ 3 + payΦ K W l N ∧
      (JWalk.iter X n (JWalk.start p o)).found ≠ none := by
  obtain ⟨r₁, hr₁, -, h₁⟩ := side_len hN hX hJ.pair hW
  obtain ⟨r₂, hr₂, -, h₂⟩ := side_len hN hX (hN.symm hJ.pair) hW
  have hJ' := hJ.swap
  rcases Nat.lt_or_ge r₂ r₁ with hlt | hle
  · obtain ⟨gs, gp⟩ := side_gain hN hJ' hX hW hWK hl hr₂ h₂ h₁ (by omega)
    have hng : (JCur.iter X p r₂ (.go p o)).going = false := by
      cases hg : (JCur.iter X p r₂ (.go p o)).going
      · rfl
      · exact absurd ((h₂ _).1 hg) (Nat.lt_irrefl _)
    rcases JCur.rest_cases hng with hs | ⟨i, γ, hp⟩
    · have := gs hs
      exact ⟨2 * r₂, by omega, by omega,
        JWalk.found_stop₂ X (JWalk.start p o) rfl h₁ h₂ hlt hs⟩
    · have := gp i γ hp
      exact ⟨r₁ + r₂, by omega, by omega, JWalk.found_by X (JWalk.start p o) h₁ h₂⟩
  · obtain ⟨gs, gp⟩ := side_gain hN hJ hX hW hWK hl hr₁ h₁ h₂ hle
    have hng : (JCur.iter X o r₁ (.go o p)).going = false := by
      cases hg : (JCur.iter X o r₁ (.go o p)).going
      · rfl
      · exact absurd ((h₁ _).1 hg) (Nat.lt_irrefl _)
    rcases JCur.rest_cases hng with hs | ⟨i, γ, hp⟩
    · have := gs hs
      exact ⟨2 * r₁ - 1, by omega, by omega,
        JWalk.found_stop₁ X (JWalk.start p o) rfl h₁ h₂ hle hr₁ hs⟩
    · have := gp i γ hp
      exact ⟨r₁ + r₂, by omega, by omega, JWalk.found_by X (JWalk.start p o) h₁ h₂⟩

end Pay

section Run

variable [DecidableEq S] {xs : XSys S}

/-- **Every rule that joins a segment does nothing else**: firing it adds
the joined segment to the net and nothing more, between two points that lie
on one segment at most and are not principal ports. -/
def XSys.PureJoin (xs : XSys S) : Prop :=
  ∀ (G : Net S) (a b : Id) (α β : S) (R : XRhs S) (p q : Port), G.WF xs.sys.ar →
    xs.rule α β = some R → Redex xs.sys G a b α β R.toRhs →
    R.joinPairs xs.sys.ar a b α β = [(p, q)] → Joined G (G.fire a b R.toRhs) p q

omit [DecidableEq S] in
/-- How many segments a rule joins does not depend on the names of the
pair. -/
theorem XRhs.joinPairs_length (R : XRhs S) (ar : S → Nat) (a b a' b' : Id) (α β : S) :
    (R.joinPairs ar a b α β).length = (R.joinPairs ar a' b' α β).length := by
  unfold XRhs.joinPairs
  induction ifcPorts ar α β with
  | nil => rfl
  | cons x L ih =>
    simp only [List.filterMap_cons]
    cases R.wire x with
    | none => exact ih
    | some y =>
      dsimp only
      by_cases hc : (!y.isNew && decide (x.rank < y.rank)) = true
      · rw [ite_pos' hc, ite_pos' hc]
        simp only [List.length_cons, ih]
      · rw [ite_neg' hc, ite_neg' hc]
        exact ih

omit [DecidableEq S] in
/-- One join at most, checked on one pair of names. -/
theorem XSys.oneJoin_of
    (h : ∀ α β R, xs.rule α β = some R → (R.joinPairs xs.sys.ar [] [] α β).length ≤ 1) :
    xs.OneJoin := fun α β R a b hR => by
  rw [XRhs.joinPairs_length R xs.sys.ar a b [] [] α β]
  exact h α β R hR

omit [DecidableEq S] in
/-- **The joins of a system do nothing else** when every rule that joins
interface ports writes no agent: then every segment it writes joins two
interface ports, and when it joins one pair only, it is that one. -/
theorem XSys.pureJoin_of
    (hb : ∀ α β R, xs.rule α β = some R → R.joins xs.sys.ar α β = true → R.slots = []) :
    xs.PureJoin := by
  intro G a b α β R p q hG hR rg hjp
  have hwf : R.toRhs.WF xs.sys.ar α β := xs.sys.rule_wf (by rw [xs.rule_spec, hR]; rfl)
  have hmem : (p, q) ∈ R.joinPairs xs.sys.ar a b α β := by rw [hjp]; exact List.mem_singleton_self _
  have hsl := hb α β R hR (XRhs.joins_of_mem hmem)
  have nolab : ∀ o j, R.lab o j = none := by
    intro o j
    cases hl : R.lab o j with
    | none => rfl
    | some γ =>
      have := xs.slots_spec hR hl
      rw [hsl] at this
      exact absurd this List.not_mem_nil
  have ifc : ∀ {x y}, R.wire x = some y → ∃ s k, x = .ifc s k ∧ k < xs.sys.ar (sel α β s) := by
    intro x y hw
    have hv := hwf.valid (x := x) (y := y) hw
    cases x with
    | ifc s k => exact ⟨s, k, rfl, hv⟩
    | new o j k =>
      obtain ⟨γ, hγ, -⟩ := hv
      have : R.toRhs.lab o j = none := nolab o j
      rw [this] at hγ
      cases hγ
  obtain ⟨s, k, s', k', hw, hx, rfl, rfl⟩ := XRhs.mem_joinPairs hmem
  obtain ⟨s₀, k₀, e₀, hk⟩ := ifc hw
  cases e₀
  obtain ⟨s₁, k₁, e₁, hk'⟩ := ifc (hwf.symm (x := .ifc s k) (y := .ifc s' k') hw)
  cases e₁
  have hagent : ∀ s, G.agent (sel a b s) (sel α β s) := by
    intro s
    cases s
    · exact rg.ha
    · exact rg.hb
  have hend : ∀ s k, k < xs.sys.ar (sel α β s) → ∀ x y, G.link (emb a b (.ifc s k)) x →
      G.link (emb a b (.ifc s k)) y → x = y := by
    intro s k hk x y hx hy
    exact hG.end_unique (.inr ⟨sel α β s, hagent s, by simp only [emb]; omega⟩) hx hy
  refine ⟨fun u v => ⟨fun h => ?_, fun h => ?_⟩, hend s k hk, hend s' k' hk',
    by simp [emb], by simp [emb]⟩
  · rcases h with h | ⟨x, y, hxy, rfl, rfl⟩
    · exact .inl h
    · obtain ⟨s₂, k₂, rfl, -⟩ := ifc hxy
      obtain ⟨s₃, k₃, rfl, -⟩ := ifc (hwf.symm (x := .ifc s₂ k₂) (y := y) hxy)
      rcases XRhs.joinPairs_of_wire (a := a) (b := b) hwf hxy with hm | hm
      · rw [hjp] at hm
        obtain ⟨e₁, e₂⟩ := Prod.mk.inj (List.mem_singleton.1 hm)
        exact .inr (.inl ⟨e₁, e₂⟩)
      · rw [hjp] at hm
        obtain ⟨e₁, e₂⟩ := Prod.mk.inj (List.mem_singleton.1 hm)
        exact .inr (.inr ⟨e₂, e₁⟩)
  · rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl h
    · exact .inr ⟨_, _, hw, rfl, rfl⟩
    · exact .inr ⟨_, _, hwf.symm (x := .ifc s k) (y := .ifc s' k') hw, rfl, rfl⟩

/-- What the measure needs of a goal: it is well formed, `W` holds its
segments, and `l` the names of its agents. -/
def PayOk (ar : S → Nat) (W : List (Port × Port)) (l : List Id) (G : Net S) : Prop :=
  G.WF ar ∧ (∀ u v, G.link u v → (u, v) ∈ W) ∧ ∀ i γ, G.agent i γ → i ∈ l

omit [DecidableEq S] in
/-- **A system whose joining rules join and do nothing else pays its walks
with `payΦ`, three per claim.** -/
theorem XSys.walkPaid_payΦ (hP : xs.PureJoin) {K : Nat} {W : List (Port × Port)}
    {l : List Id} (hWK : W.length ≤ K) :
    xs.WalkPaid (payΦ K W l) 3 (PayOk xs.sys.ar W l) := by
  intro G a b α β R hG hG' hR rg
  have hle : ∀ {u v}, G.link u v → (G.fire a b R.toRhs).link u v := fun h => .inl h
  refine ⟨Nat.le_trans (payΦ_mono hle) (Nat.le_add_left _ _), fun p q hj X hX => ?_⟩
  exact walk_pays hG'.1 (hP G a b α β R p q hG.1 hR rg hj) hX (fun h => hG'.2.1 _ _ h) hWK
    hG'.2.2

/-- **The walks of one thread cost three per claim and the growth of
`payΦ`**, along a run of a system whose rules join one segment at most and
do nothing else when they join, while `W` holds the segments and `l` the
names of the agents of every goal. -/
theorem JMach.walked_payΦ (hJ : xs.OneJoin) (hP : xs.PureJoin) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {K : Nat} {W : List (Port × Port)} {l : List Id}
    (hWK : W.length ≤ K) {i : Nat}
    (hok : ∀ j, j ≤ i → PayOk xs.sys.ar W l
      ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal) :
    JMach.walked xs (fun _ => 0) (JMach.init X 1) i + payΦ K W l X.toNet ≤
      3 * ((JMach.init X 1).trace xs (fun _ => 0) i).2 +
        payΦ K W l ((JMach.init X 1).trace xs (fun _ => 0) i).1.toMach.goal :=
  JMach.walked_le hJ (XSys.walkPaid_payΦ hP hWK) hX hok

theorem sum_map_const {α : Type} (W : List α) (c : Nat) :
    (W.map fun _ => c).sum = W.length * c := by
  induction W with
  | nil => simp
  | cons e W ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
    omega

omit [DecidableEq S] in
/-- **The measure is at most `4 |W| log (K + 1) + 2 |l| (K + 1) + 2 |W|`.** -/
theorem payΦ_le (K : Nat) (W : List (Port × Port)) (l : List Id) (G : Net S) :
    payΦ K W l G ≤ 4 * (W.length * Nat.log2 (K + 1)) + 2 * (l.length * (K + 1)) +
      2 * W.length := by
  unfold payΦ
  have h₁ : (W.map fun e => Nat.log2 (lfar G.link K e.1)).sum ≤ W.length * Nat.log2 (K + 1) := by
    have := sum_mono W (fun e => Nat.log2 (lfar G.link K e.1)) (fun _ => Nat.log2 (K + 1))
      fun e _ => log2_mono (lfar_le K e.1)
    rwa [sum_map_const] at this
  have h₂ : (l.map fun i => lfar G.link K (i, 0)).sum ≤ l.length * (K + 1) := by
    have := sum_mono l (fun i => lfar G.link K (i, 0)) (fun _ => K + 1)
      fun i _ => lfar_le K (i, 0)
    rwa [sum_map_const] at this
  have h₃ : (W.map fun e => cycAt G.link e.1).sum ≤ W.length := by
    have := sum_mono W (fun e => cycAt G.link e.1) (fun _ => 1) fun e _ => cycAt_le_one _ _
    rwa [sum_map_const, Nat.mul_one] at this
  omega

/-- **The walks of one thread, along the whole of a run, cost at most
`3 n + 4 K log (K + 1) + 2 K (K + 1) + 2 K`**, where `n` is the number of
steps to the normal form and `K = |wires| + D n` bounds its segments, for a
system whose rules join one segment at most and do nothing else when they
join. -/
theorem JMach.walked_bound (hJ : xs.OneJoin) (hP : xs.PureJoin) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (i : Nat) :
    JMach.walked xs (fun _ => 0) (JMach.init X 1) i ≤
      3 * n + 4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        2 * ((X.wires.length + D * n) * (X.wires.length + D * n + 1)) +
        2 * (X.wires.length + D * n) := by
  have live := JMach.trace_live (xs := xs) (fun _ => 0) (JMach.init_live hX Nat.one_pos)
  have run : ∀ i, MRun xs.sys ((JMach.init X 1).trace xs (fun _ => 0) i).2 (Mach.init X.toNet)
      ((JMach.init X 1).trace xs (fun _ => 0) i).1.toMach := by
    intro i
    have h := JMach.trace_run xs (fun _ => 0) (JMach.init X 1) i
    rw [JMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((JMach.init X 1).trace xs (fun _ => 0) i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  have ahead : ∀ i, ((JMach.init X 1).trace xs (fun _ => 0) i).1.toW.toX.Ahead N' :=
    fun i => XMach.ahead_of_run (M := ((JMach.init X 1).trace xs (fun _ => 0) i).1.toW.toX)
      (live i).inv hX (run i) hs hn
  have hH := XNet.normal_sized hX hb hs hn
  generalize X.wires.length + D * n = K at hH ⊢
  obtain ⟨W, hWK, hWl⟩ := hH.fin
  let l : List Id := W.map fun e => e.1.1
  have hok : ∀ j, j ≤ i → PayOk xs.sys.ar W l
      ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal := by
    intro j _
    have hG := (live j).inv.wf
    refine ⟨hG, fun u v h => hWl ((ahead j).link h), fun k γ hk => ?_⟩
    obtain ⟨q, hq⟩ := hG.end_wired (p := (k, 0)) (.inr ⟨γ, hk, Nat.zero_le _⟩)
    exact List.mem_map.2 ⟨_, hWl ((ahead j).link hq), rfl⟩
  have h := JMach.walked_payΦ hJ hP hX hWK hok
  have hle := payΦ_le K W l ((JMach.init X 1).trace xs (fun _ => 0) i).1.toMach.goal
  have hl : l.length = W.length := List.length_map _
  have hmul₁ : W.length * Nat.log2 (K + 1) ≤ K * Nat.log2 (K + 1) := Nat.mul_le_mul_right _ hWK
  have hmul₂ : l.length * (K + 1) ≤ K * (K + 1) := by rw [hl]; exact Nat.mul_le_mul_right _ hWK
  have hmul₃ : 3 * ((JMach.init X 1).trace xs (fun _ => 0) i).2 ≤ 3 * n :=
    Nat.mul_le_mul_left _ (bound i)
  omega

end Run

end INet
