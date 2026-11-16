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
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z)
    {f : Nat → V} {t : Nat}
    (hl : ∀ i, i < t → L (f i) (f (i + 1)))
    (hi : ∀ i j, i ≤ t → j ≤ t → f i = f j → i = j)
    (h0 : ∀ q, L (f 0) q → 0 < t ∧ q = f 1)
    (ht : ∀ q, L (f t) q → 0 < t ∧ q = f (t - 1)) :
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
         (j + n ≤ t ∧ vs.head? = some (f (j + n)) ∧
           ∀ k, k ≤ n → f (j + k) ∈ vs)) := by
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
      · refine ⟨n + 1, by simp only [List.length_cons] at hlen ⊢; omega,
          .inl ⟨by omega, ?_, fun k hk => ?_⟩⟩
        · simp only [List.head?_cons]
          congr 2
        · rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
          · exact List.mem_cons_of_mem _ (hall k (by omega))
          · obtain rfl : k = n + 1 := by omega
            have : j - (n + 1) = j - n - 1 := by omega
            rw [this]
            exact List.mem_cons_self
      · rcases Nat.eq_zero_or_pos n with rfl | hnp
        · refine ⟨1, by simp only [List.length_cons] at hlen ⊢; omega,
            .inr ⟨by omega, by simp, fun k hk => ?_⟩⟩
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
        · refine ⟨1, by simp only [List.length_cons] at hlen ⊢; omega,
            .inl ⟨by omega, ?_, fun k hk => ?_⟩⟩
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
      · refine ⟨n + 1, by simp only [List.length_cons] at hlen ⊢; omega,
          .inr ⟨by omega, by simp [Nat.add_assoc], fun k hk => ?_⟩⟩
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

/-- The points `f t, …, f 1, f 0`. -/
def pathList (f : Nat → V) : Nat → List V
  | 0 => [f 0]
  | t + 1 => f (t + 1) :: pathList f t

theorem mem_pathList {f : Nat → V} {x : V} : ∀ {t}, x ∈ pathList f t → ∃ k, k ≤ t ∧ x = f k
  | 0, h => ⟨0, Nat.le_refl _, List.mem_singleton.1 h⟩
  | t + 1, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨t + 1, Nat.le_refl _, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := mem_pathList h
      exact ⟨k, by omega, rfl⟩

theorem length_pathList (f : Nat → V) : ∀ t, (pathList f t).length = t + 1
  | 0 => rfl
  | t + 1 => by simp [pathList, length_pathList f t]

/-- **Points linked one to the next, all different, make a trail.** -/
theorem Trail.of_chain {f : Nat → V} : ∀ t, (∀ i, i < t → L (f i) (f (i + 1))) →
    (∀ i j, i ≤ t → j ≤ t → f i = f j → i = j) → Trail L (f 0) (pathList f t)
  | 0, _, _ => .start
  | t + 1, hl, hi => by
    have tr := Trail.of_chain t (fun i h => hl i (by omega))
      (fun i j h₁ h₂ e => hi i j (by omega) (by omega) e)
    show Trail L (f 0) (f (t + 1) :: pathList f t)
    have hne : f (t + 1) ∉ pathList f t := fun h => by
      obtain ⟨k, hk, e⟩ := mem_pathList h
      have := hi _ _ (by omega) (by omega) e
      omega
    cases t with
    | zero => exact .step tr (hl 0 (by omega)) hne
    | succ t => exact .step tr (hl (t + 1) (by omega)) hne

/-- **The longest trail from the start of a chain is at least as long as
the chain**, when the chain fits under the cap. -/
theorem lfar_ge_chain {f : Nat → V} {t K : Nat} (hl : ∀ i, i < t → L (f i) (f (i + 1)))
    (hi : ∀ i j, i ≤ t → j ≤ t → f i = f j → i = j) (hK : t + 1 ≤ K + 1) :
    t + 1 ≤ lfar L K (f 0) := by
  have := (Trail.of_chain t hl hi).le_lfar (K := K) (by rw [length_pathList]; exact hK)
  rwa [length_pathList] at this

/-- A trail of one point: the longest trail has a point at least. -/
theorem one_le_lfar (K : Nat) (u : V) : 1 ≤ lfar L K u :=
  (Trail.start (L := L) (u := u)).le_lfar (by simp)

theorem log2_mono {x y : Nat} (h : y ≤ x) : Nat.log2 y ≤ Nat.log2 x := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [Nat.log2_zero]
  · exact (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le (by omega)) h)

theorem log2_double {x y : Nat} (hy : 1 ≤ y) (h : 2 * y ≤ x) : Nat.log2 y + 1 ≤ Nat.log2 x := by
  refine (Nat.le_log2 (by omega)).2 ?_
  have := Nat.log2_self_le (n := y) (by omega)
  rw [Nat.pow_succ]
  omega

/-- **A sum over a list gains one for each of some different values met as
the keys of its entries, when no entry loses and the entries at those keys
gain one.** -/
theorem sum_gain {α β : Type} [DecidableEq β] (W : List α) (key : α → β) (f g : α → Nat)
    (D : List β) (hD : D.Nodup) (hin : ∀ x, x ∈ D → ∃ e, e ∈ W ∧ key e = x)
    (hle : ∀ e, e ∈ W → f e ≤ g e) (hgain : ∀ e, e ∈ W → key e ∈ D → f e + 1 ≤ g e) :
    (W.map f).sum + D.length ≤ (W.map g).sum := by
  have count : ∀ W : List α, (∀ e, e ∈ W → f e ≤ g e) → (∀ e, e ∈ W → key e ∈ D → f e + 1 ≤ g e) →
      (W.map f).sum + (W.filter fun e => decide (key e ∈ D)).length ≤ (W.map g).sum := by
    intro W
    induction W with
    | nil => intros; simp
    | cons e W ih =>
      intro h₁ h₂
      have := ih (fun e' h => h₁ e' (List.mem_cons_of_mem _ h))
        (fun e' h => h₂ e' (List.mem_cons_of_mem _ h))
      have he := h₁ e List.mem_cons_self
      by_cases hk : key e ∈ D
      · have := h₂ e List.mem_cons_self hk
        simp [hk]
        omega
      · simp [hk]
        omega
  have hsub : D ⊆ (W.filter fun e => decide (key e ∈ D)).map key := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hin x hx
    exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simpa using hx⟩, rfl⟩
  have := hD.length_le_of_subset hsub
  rw [List.length_map] at this
  have := count W hle hgain
  omega

theorem sum_mono {α : Type} (W : List α) (f g : α → Nat) (h : ∀ e, e ∈ W → f e ≤ g e) :
    (W.map f).sum ≤ (W.map g).sum := by
  induction W with
  | nil => simp
  | cons e W ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h e List.mem_cons_self) (ih fun e' h' => h e' (List.mem_cons_of_mem _ h'))

/-- The point lies on a cycle: a trail of three points at least from it
ends at a point linked back to it. -/
def OnCycle (L : V → V → Prop) (u : V) : Prop :=
  ∃ v vs, Trail L u (v :: vs) ∧ 2 ≤ vs.length ∧ L v u

/-- `1` on a cycle, `0` elsewhere. -/
noncomputable def cycAt (L : V → V → Prop) (u : V) : Nat := by
  classical
  exact if OnCycle L u then 1 else 0

theorem cycAt_le_one (L : V → V → Prop) (u : V) : cycAt L u ≤ 1 := by
  unfold cycAt
  split <;> omega

theorem cycAt_mono (h : ∀ {p q}, L p q → L' p q) (u : V) : cycAt L u ≤ cycAt L' u := by
  unfold cycAt
  split
  · rename_i hc
    obtain ⟨v, vs, t, hl, hv⟩ := hc
    split
    · exact Nat.le_refl _
    · rename_i hn
      exact absurd ⟨v, vs, t.mono h, hl, h hv⟩ hn
  · exact Nat.zero_le _

/-- **No point of a path that a trail cannot leave lies on a cycle.** -/
theorem IsPath.not_onCycle {f : Nat → V} {t : Nat} (P : IsPath L f t) {j : Nat} (hj : j ≤ t) :
    ¬ OnCycle L (f j) := by
  rintro ⟨v, vs, tr, hl, hv⟩
  obtain ⟨n, hlen, h | h⟩ := P.trail_shape hj tr
  · obtain ⟨hn, hh, -⟩ := h
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [List.length_cons] at hlen
    rcases P.nb (j - n) (f j) (by omega) hv with ⟨hpos, e⟩ | ⟨hlt, e⟩
    · have := P.inj _ _ hj (by omega) e
      omega
    · have := P.inj _ _ hj (by omega) e
      omega
  · obtain ⟨hn, hh, -⟩ := h
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [List.length_cons] at hlen
    rcases P.nb (j + n) (f j) hn hv with ⟨-, e⟩ | ⟨hlt, e⟩
    · have := P.inj _ _ hj (by omega) e
      omega
    · have := P.inj _ _ hj (by omega) e
      omega

theorem IsPath.cycAt {f : Nat → V} {t : Nat} (P : IsPath L f t) {j : Nat} (hj : j ≤ t) :
    cycAt L (f j) = 0 := by
  unfold INet.cycAt
  split
  · rename_i hc
    exact absurd hc (P.not_onCycle hj)
  · rfl

/-- **Every point of a closed chain of three points at least lies on a
cycle.** -/
theorem onCycle_of_ring {f : Nat → V} {t : Nat} (ht : 2 ≤ t)
    (hl : ∀ i, i < t → L (f i) (f (i + 1))) (hw : L (f t) (f 0))
    (hi : ∀ i j, i ≤ t → j ≤ t → f i = f j → i = j) {j : Nat} (hj : j ≤ t) :
    OnCycle L (f j) := by
  -- go round from `f j`
  let g : Nat → V := fun k => if j + k ≤ t then f (j + k) else f (j + k - t - 1)
  have hg0 : g 0 = f j := by simp [g, hj]
  have gl : ∀ i, i < t → L (g i) (g (i + 1)) := by
    intro i hi'
    simp only [g]
    by_cases h₁ : j + (i + 1) ≤ t
    · rw [ite_pos' (by omega), ite_pos' h₁]
      have := hl (j + i) (by omega)
      rwa [Nat.add_assoc] at this
    · by_cases h₂ : j + i ≤ t
      · rw [ite_pos' h₂, ite_neg' h₁]
        obtain rfl : j + i = t := by omega
        have e : j + (i + 1) - (j + i) - 1 = 0 := by omega
        rw [e]
        exact hw
      · rw [ite_neg' h₂, ite_neg' h₁]
        have := hl (j + i - t - 1) (by omega)
        have e : j + i - t - 1 + 1 = j + (i + 1) - t - 1 := by omega
        rwa [e] at this
  have gi : ∀ a b, a ≤ t → b ≤ t → g a = g b → a = b := by
    intro a b ha hb e
    simp only [g] at e
    split at e <;> split at e
    · have := hi _ _ (by omega) (by omega) e
      omega
    · have := hi _ _ (by omega) (by omega) e
      omega
    · have := hi _ _ (by omega) (by omega) e
      omega
    · have := hi _ _ (by omega) (by omega) e
      omega
  have tr := Trail.of_chain t gl gi
  rw [hg0] at tr
  cases t with
  | zero => omega
  | succ t =>
    refine ⟨g (t + 1), pathList g t, tr, by rw [length_pathList]; omega, ?_⟩
    rw [← hg0]
    simp only [g]
    by_cases h₁ : j + (t + 1) ≤ t + 1
    · obtain rfl : j = 0 := by omega
      rw [ite_pos' h₁]
      simpa using hw
    · rw [ite_neg' h₁]
      have := hl (j - 1) (by omega)
      have e₁ : j + (t + 1) - (t + 1) - 1 = j - 1 := by omega
      have e₂ : j - 1 + 1 = j := by omega
      rw [e₂] at this
      rw [e₁, ite_pos' (by omega)]
      simpa using this

theorem cycAt_ring {f : Nat → V} {t : Nat} (ht : 2 ≤ t)
    (hl : ∀ i, i < t → L (f i) (f (i + 1))) (hw : L (f t) (f 0))
    (hi : ∀ i j, i ≤ t → j ≤ t → f i = f j → i = j) {j : Nat} (hj : j ≤ t) :
    cycAt L (f j) = 1 := by
  unfold cycAt
  split
  · rfl
  · rename_i hc
    exact absurd (onCycle_of_ring ht hl hw hi hj) hc

/-- A sum over a list gains `d` when one entry gains `d` and none loses. -/
theorem sum_gain_one {α : Type} (W : List α) (f g : α → Nat) {e₀ : α} (he : e₀ ∈ W) {d : Nat}
    (hle : ∀ e, e ∈ W → f e ≤ g e) (hd : f e₀ + d ≤ g e₀) :
    (W.map f).sum + d ≤ (W.map g).sum := by
  induction W with
  | nil => exact absurd he List.not_mem_nil
  | cons e W ih =>
    simp only [List.map_cons, List.sum_cons]
    have hm := sum_mono W f g fun e' h => hle e' (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.1 he with rfl | he'
    · omega
    · have := ih he' fun e' h => hle e' (List.mem_cons_of_mem _ h)
      have := hle e List.mem_cons_self
      omega

section Doubling

variable [DecidableEq V] {W : List (V × V)}

/-- **The longest trail from each point of the far half of a path doubles
when the path is joined at its start to another at least as long**: so
the sum over a list of the logarithms of the longest trails from the first
points of its entries gains one for each point of that half. -/
theorem log_gain {f g : Nat → V} {m m' K : Nat} (P : IsPath L f m) (hLL : ∀ {u v}, L u v → L' u v)
    (hs' : ∀ {u v}, L' u v → L' v u)
    (hfg : L' (f 0) (g 0)) (hg : ∀ i, i < m' → L' (g i) (g (i + 1)))
    (hgi : ∀ i j, i ≤ m' → j ≤ m' → g i = g j → i = j)
    (hap : ∀ i j, i ≤ m → j ≤ m' → f i ≠ g j) (hm : m ≤ m')
    (hW : ∀ {u v}, L' u v → (u, v) ∈ W) (hWK : W.length ≤ K)
    (hkey : ∀ i, i ≤ m → ∃ e, e ∈ W ∧ e.1 = f i) :
    (W.map fun e => Nat.log2 (lfar L K e.1)).sum + (m / 2 + 1) ≤
      (W.map fun e => Nat.log2 (lfar L' K e.1)).sum := by
  -- the points of the far half
  let j₀ := m - m / 2
  let D := (List.range (m / 2 + 1)).map fun k => f (j₀ + k)
  have hD : D.Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.nodup_range.imp_of_mem fun hk hl hne e =>
      hne (by have := P.inj _ _ (by simp at hk; omega) (by simp at hl; omega) e; omega)
  have hDlen : D.length = m / 2 + 1 := by simp [D]
  have hmemD : ∀ x, x ∈ D → ∃ j, j₀ ≤ j ∧ j ≤ m ∧ x = f j := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    simp only [List.mem_range] at hk
    exact ⟨j₀ + k, by omega, by omega, rfl⟩
  -- the chain from `f j` back to the start, then along the other path
  have gain : ∀ j, j₀ ≤ j → j ≤ m → Nat.log2 (lfar L K (f j)) + 1 ≤ Nat.log2 (lfar L' K (f j)) := by
    intro j hj₁ hj₂
    let h : Nat → V := fun k => if k ≤ j then f (j - k) else g (k - j - 1)
    have hl : ∀ i, i < j + 1 + m' → L' (h i) (h (i + 1)) := by
      intro i hi
      simp only [h]
      by_cases h₁ : i + 1 ≤ j
      · rw [ite_pos' (by omega), ite_pos' h₁]
        have := P.link (j - (i + 1)) (by omega)
        have e : j - (i + 1) + 1 = j - i := by omega
        rw [e] at this
        exact hs' (hLL this)
      · by_cases h₂ : i ≤ j
        · obtain rfl : i = j := by omega
          rw [ite_pos' (Nat.le_refl _), ite_neg' (by omega), Nat.sub_self]
          simpa using hfg
        · rw [ite_neg' h₂, ite_neg' (by omega)]
          have := hg (i - j - 1) (by omega)
          have e : i - j - 1 + 1 = i + 1 - j - 1 := by omega
          rwa [e] at this
    have hi : ∀ a b, a ≤ j + 1 + m' → b ≤ j + 1 + m' → h a = h b → a = b := by
      intro a b ha hb e
      simp only [h] at e
      split at e <;> split at e
      · have := P.inj _ _ (by omega) (by omega) e
        omega
      · exact absurd e (hap _ _ (by omega) (by omega))
      · exact absurd e.symm (hap _ _ (by omega) (by omega))
      · have := hgi _ _ (by omega) (by omega) e
        omega
    have tr := Trail.of_chain (L := L') (j + 1 + m') hl hi
    have h0 : h 0 = f j := by simp [h]
    rw [h0] at tr
    have hlen := tr.length_le W hW
    rw [length_pathList] at hlen
    have hge := tr.le_lfar (K := K) (by rw [length_pathList]; omega)
    rw [length_pathList] at hge
    have hle := P.lfar_le (j := j) hj₂ K (L := L)
    have hmax : max (j + 1) (m - j + 1) = j + 1 := by
      simp only [Nat.max_def]
      split <;> omega
    rw [hmax] at hle
    exact log2_double (one_le_lfar K _) (by omega)
  have hin : ∀ x, x ∈ D → ∃ e, e ∈ W ∧ Prod.fst e = x := by
    intro x hx
    obtain ⟨j, -, hj, rfl⟩ := hmemD x hx
    exact hkey j hj
  have := sum_gain W Prod.fst (fun e => Nat.log2 (lfar L K e.1))
    (fun e => Nat.log2 (lfar L' K e.1)) D hD hin
    (fun e _ => log2_mono (lfar_mono hLL K e.1))
    (fun e _ hk => by
      obtain ⟨j, hj₁, hj₂, hx⟩ := hmemD e.1 hk
      rw [hx]
      exact gain j hj₁ hj₂)
  rw [hDlen] at this
  exact this

/-- **The longest trail from the end of a path, joined at its start to
another path, grows by the length of the other path.** -/
theorem end_gain {f g : Nat → V} {m m' K : Nat} (P : IsPath L f m)
    (hs' : ∀ {u v}, L' u v → L' v u) (hLL : ∀ {u v}, L u v → L' u v)
    (hfg : L' (f 0) (g 0)) (hg : ∀ i, i < m' → L' (g i) (g (i + 1)))
    (hgi : ∀ i j, i ≤ m' → j ≤ m' → g i = g j → i = j)
    (hap : ∀ i j, i ≤ m → j ≤ m' → f i ≠ g j)
    (hW : ∀ {u v}, L' u v → (u, v) ∈ W) (hWK : W.length ≤ K) :
    lfar L K (f m) + (m' + 1) ≤ lfar L' K (f m) := by
  let h : Nat → V := fun k => if k ≤ m then f (m - k) else g (k - m - 1)
  have hl : ∀ i, i < m + 1 + m' → L' (h i) (h (i + 1)) := by
    intro i hi
    simp only [h]
    by_cases h₁ : i + 1 ≤ m
    · rw [ite_pos' (by omega), ite_pos' h₁]
      have := P.link (m - (i + 1)) (by omega)
      have e : m - (i + 1) + 1 = m - i := by omega
      rw [e] at this
      exact hs' (hLL this)
    · by_cases h₂ : i ≤ m
      · obtain rfl : i = m := by omega
        rw [ite_pos' (Nat.le_refl _), ite_neg' (by omega), Nat.sub_self]
        simpa using hfg
      · rw [ite_neg' h₂, ite_neg' (by omega)]
        have := hg (i - m - 1) (by omega)
        have e : i - m - 1 + 1 = i + 1 - m - 1 := by omega
        rwa [e] at this
  have hi : ∀ a b, a ≤ m + 1 + m' → b ≤ m + 1 + m' → h a = h b → a = b := by
    intro a b ha hb e
    simp only [h] at e
    split at e <;> split at e
    · have := P.inj _ _ (by omega) (by omega) e
      omega
    · exact absurd e (hap _ _ (by omega) (by omega))
    · exact absurd e.symm (hap _ _ (by omega) (by omega))
    · have := hgi _ _ (by omega) (by omega) e
      omega
  have tr := Trail.of_chain (L := L') (m + 1 + m') hl hi
  have h0 : h 0 = f m := by simp [h]
  rw [h0] at tr
  have hlen := tr.length_le W hW
  rw [length_pathList] at hlen
  have hge := tr.le_lfar (K := K) (by rw [length_pathList]; omega)
  rw [length_pathList] at hge
  have hle := P.lfar_le (j := m) (Nat.le_refl _) K (L := L)
  have hmax : max (m + 1) (m - m + 1) = m + 1 := by
    simp only [Nat.max_def]
    split <;> omega
  rw [hmax] at hle
  omega

/-- **The points of a path that a closed ring of new segments makes into a
cycle each gain one in the count of points on cycles.** -/
theorem cyc_gain {d : Nat → V} {t : Nat} (P : IsPath L d t) (ht : 2 ≤ t)
    (hLL : ∀ {u v}, L u v → L' u v) (hw : L' (d t) (d 0))
    (hkey : ∀ i, i ≤ t → ∃ e, e ∈ W ∧ e.1 = d i) :
    (W.map fun e => cycAt L e.1).sum + (t + 1) ≤ (W.map fun e => cycAt L' e.1).sum := by
  let D := (List.range (t + 1)).map d
  have hD : D.Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.nodup_range.imp_of_mem fun hk hl hne e =>
      hne (P.inj _ _ (by simp at hk; omega) (by simp at hl; omega) e)
  have hDlen : D.length = t + 1 := by simp [D]
  have := sum_gain W Prod.fst (fun e => cycAt L e.1) (fun e => cycAt L' e.1) D hD
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact hkey k (by simp at hk; omega))
    (fun e _ => cycAt_mono hLL e.1)
    (fun e _ hk => by
      obtain ⟨k, hk, hx⟩ := List.mem_map.1 hk
      simp only [List.mem_range] at hk
      show cycAt L e.1 + 1 ≤ cycAt L' e.1
      rw [← hx, P.cycAt (by omega),
        cycAt_ring ht (fun i hi => hLL (P.link i hi)) hw P.inj (by omega)]
      exact Nat.le_refl _)
  rw [hDlen] at this
  exact this

end Doubling

end PathFar

end INet
