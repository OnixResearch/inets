import InteractionNets.Fair

/-! # Longest trails on a path

In a wiring where a point lies on two segments at most, a path whose two
ends lie on no other segment is the whole of what a trail from one of its
points can reach: a trail from the `j`-th point of a path of `t + 1` points
goes one way along it and has at most `max (j + 1) (t - j + 1)` points
(`IsPath.trail_le`), so the longest trail from that point is that long at
most (`IsPath.lfar_le`).  This is what bounds, before a rule joins two
wires, how far one can go from a point of one of them; after the join one
can go on along the other, and when the two are of comparable length the
longest trail from the far half of the shorter one at least doubles.
-/

namespace INet

section PathFar

variable {V : Type} {L L' : V → V → Prop}

/-- The number of points of the longest trail of `L` from `u`, up to
`K + 1`. -/
noncomputable def lfar (L : V → V → Prop) (K : Nat) (u : V) : Nat :=
  supBelow (fun n => ∃ vs, Trail L u vs ∧ vs.length = n) (K + 1)

theorem Net.far_eq_lfar {S : Type} (H : Net S) (K : Nat) (u : Port) :
    H.far K u = lfar H.link K u := rfl

theorem supBelow_le_of {P : Nat → Prop} {m : Nat} (h : ∀ n, P n → n ≤ m) :
    ∀ B, supBelow P B ≤ m
  | 0 => Nat.zero_le _
  | B + 1 => by
    unfold supBelow
    split
    · rename_i hP
      exact h _ hP
    · exact supBelow_le_of h B

/-- A trail that fits under the cap is no longer than the longest. -/
theorem Trail.le_lfar {u : V} {vs : List V} (t : Trail L u vs) {K : Nat}
    (hK : vs.length ≤ K + 1) : vs.length ≤ lfar L K u :=
  le_supBelow ⟨vs, t, rfl⟩ hK

/-- **More segments, longer trails.** -/
theorem lfar_mono (h : ∀ {p q}, L p q → L' p q) (K : Nat) (u : V) :
    lfar L K u ≤ lfar L' K u :=
  supBelow_mono (fun _ ⟨vs, t, e⟩ => ⟨vs, t.mono h, e⟩) (K + 1)

theorem lfar_le (K : Nat) (u : V) : lfar L K u ≤ K + 1 := supBelow_le _ _

/-- `f 0, f 1, …, f t` is a path of `L` that a trail cannot leave: its
consecutive points are linked, they are different, and every point of `L`
linked to one of them is the one before or the one after. -/
structure IsPath (L : V → V → Prop) (f : Nat → V) (t : Nat) : Prop where
  link : ∀ i, i < t → L (f i) (f (i + 1))
  inj : ∀ i j, i ≤ t → j ≤ t → f i = f j → i = j
  nb : ∀ i q, i ≤ t → L (f i) q → (0 < i ∧ q = f (i - 1)) ∨ (i < t ∧ q = f (i + 1))

/-- **A path whose ends lie on no other segment is one a trail cannot
leave**, when a point lies on two segments at most. -/
theorem IsPath.of_ends (hs : ∀ {p q}, L p q → L q p)
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z) {f : Nat → V} {t : Nat}
    (hl : ∀ i, i < t → L (f i) (f (i + 1))) (hi : ∀ i j, i ≤ t → j ≤ t → f i = f j → i = j)
    (h0 : ∀ q, L (f 0) q → 0 < t ∧ q = f 1) (ht : ∀ q, L (f t) q → 0 < t ∧ q = f (t - 1)) :
    IsPath L f t := by
  refine ⟨hl, hi, fun i q hit hq => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · obtain ⟨htp, rfl⟩ := h0 q hq
    exact .inr ⟨htp, rfl⟩
  by_cases hit' : i = t
  · subst hit'
    obtain ⟨-, rfl⟩ := ht q hq
    exact .inl ⟨hpos, rfl⟩
  have hlt : i < t := Nat.lt_of_le_of_ne hit hit'
  have hprev : L (f i) (f (i - 1)) := by
    have := hl (i - 1) (by omega)
    rw [Nat.sub_add_cancel hpos] at this
    exact hs this
  have hnext := hl i hlt
  rcases hd hq hprev hnext with e | e | e
  · exact .inl ⟨hpos, e⟩
  · exact .inr ⟨hlt, e⟩
  · exact absurd (hi (i - 1) (i + 1) (by omega) (by omega) e) (by omega)

/-- What a trail from the `j`-th point of a path looks like: it has gone
`n` points down the path or `n` points up it, its last point is the
`n`-th, and it has met every point of that stretch. -/
theorem IsPath.trail_shape {f : Nat → V} {t : Nat} (P : IsPath L f t) {j : Nat} (hj : j ≤ t) :
    ∀ {vs : List V}, Trail L (f j) vs →
      ∃ n, vs.length = n + 1 ∧
        ((n ≤ j ∧ vs.head? = some (f (j - n)) ∧ ∀ k, k ≤ n → f (j - k) ∈ vs) ∨
         (j + n ≤ t ∧ vs.head? = some (f (j + n)) ∧ ∀ k, k ≤ n → f (j + k) ∈ vs)) := by
  intro vs tr
  induction tr with
  | start =>
    refine ⟨0, rfl, .inl ⟨Nat.zero_le _, by simp, fun k hk => ?_⟩⟩
    obtain rfl : k = 0 := by omega
    simp
  | @step c q vs₀ tr' hl hf ih =>
    obtain ⟨n, hlen, hshape⟩ := ih
    rcases hshape with ⟨hn, hh, hall⟩ | ⟨hn, hh, hall⟩
    · have hc : c = f (j - n) := by
        simp only [List.head?_cons] at hh
        exact Option.some.inj hh
      subst hc
      rcases P.nb (j - n) q (by omega) hl with ⟨hpos, rfl⟩ | ⟨hlt, rfl⟩
      · refine ⟨n + 1, by simp only [List.length_cons] at hlen ⊢; omega, .inl ⟨by omega, ?_, fun k hk => ?_⟩⟩
        · simp only [List.head?_cons]
          congr 2
        · rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
          · exact List.mem_cons_of_mem _ (hall k (by omega))
          · obtain rfl : k = n + 1 := by omega
            have : j - (n + 1) = j - n - 1 := by omega
            rw [this]
            exact List.mem_cons_self
      · rcases Nat.eq_zero_or_pos n with rfl | hnp
        · refine ⟨1, by simp only [List.length_cons] at hlen ⊢; omega, .inr ⟨by omega, by simp, fun k hk => ?_⟩⟩
          rcases Nat.eq_zero_or_pos k with rfl | hkp
          · exact List.mem_cons_of_mem _ (by simp at hall ⊢)
          · obtain rfl : k = 1 := by omega
            simp
        · exfalso
          apply hf
          have hm := hall (n - 1) (by omega)
          have e : j - (n - 1) = j - n + 1 := by omega
          rw [e] at hm
          exact hm
    · have hc : c = f (j + n) := by
        simp only [List.head?_cons] at hh
        exact Option.some.inj hh
      subst hc
      rcases P.nb (j + n) q (by omega) hl with ⟨hpos, rfl⟩ | ⟨hlt, rfl⟩
      · rcases Nat.eq_zero_or_pos n with rfl | hnp
        · refine ⟨1, by simp only [List.length_cons] at hlen ⊢; omega, .inl ⟨by omega, ?_, fun k hk => ?_⟩⟩
          · simp only [List.head?_cons, Nat.add_zero]
          · rcases Nat.eq_zero_or_pos k with rfl | hkp
            · exact List.mem_cons_of_mem _ (by simp at hall ⊢)
            · obtain rfl : k = 1 := by omega
              simp
        · exfalso
          apply hf
          have hm := hall (n - 1) (by omega)
          have e : j + (n - 1) = j + n - 1 := by omega
          rw [e] at hm
          exact hm
      · refine ⟨n + 1, by simp only [List.length_cons] at hlen ⊢; omega, .inr ⟨by omega, by simp [Nat.add_assoc], fun k hk => ?_⟩⟩
        rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
        · exact List.mem_cons_of_mem _ (hall k (by omega))
        · obtain rfl : k = n + 1 := by omega
          rw [← Nat.add_assoc]
          exact List.mem_cons_self

/-- **A trail from the `j`-th point of a path has at most
`max (j + 1) (t - j + 1)` points.** -/
theorem IsPath.trail_le {f : Nat → V} {t : Nat} (P : IsPath L f t) {j : Nat} (hj : j ≤ t)
    {vs : List V} (tr : Trail L (f j) vs) : vs.length ≤ max (j + 1) (t - j + 1) := by
  obtain ⟨n, hlen, h | h⟩ := P.trail_shape hj tr
  · have := h.1
    omega
  · have := h.1
    omega

/-- **The longest trail from the `j`-th point of a path has at most
`max (j + 1) (t - j + 1)` points.** -/
theorem IsPath.lfar_le {f : Nat → V} {t : Nat} (P : IsPath L f t) {j : Nat} (hj : j ≤ t)
    (K : Nat) : lfar L K (f j) ≤ max (j + 1) (t - j + 1) :=
  supBelow_le_of (fun _ ⟨_, tr, e⟩ => e ▸ P.trail_le hj tr) (K + 1)

end PathFar

end INet
