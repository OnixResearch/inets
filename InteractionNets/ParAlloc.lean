import InteractionNets.ParNames

/-! # Reusing names: an allocator for the parallel rounds

`XNet.packRun` renames the whole net after each round, the free ports
included.  Here a round renames only what it has to: a name of one cell
held before the round is kept, and every other name, a new agent's, gets a
number no name kept is using, below the length of the list of identifiers
of the net (`XNet.reuseName`).  Such numbers are always available
(`XNet.spare_length`), so this is a renaming (`XNet.reuse_renaming`).

From the short form of a net the run (`XNet.reuseRun`) fires the pairs of
`XNet.parRun` in its rounds and stops when it does, on the result of
`XNet.parRun` renamed by a renaming that is `XNet.shortName` on the free
ports (`XNet.reuseRun_map`); the free ports keep their names throughout
(`XNet.reuseRun_free`), so the result can be read at the ports of the
short form; and every name it holds is one cell, a number below the
longest list of identifiers held in the run (`XNet.reuseRun_names`,
`XNet.reusePeak`). -/

namespace INet

variable {S : Type}

theorem length_filter_add_not {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter fun a => !p a).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_add_not p l
    cases h : p a <;> simp [h] <;> omega

/-- A name the allocator keeps: one cell, held before the round. -/
def XNet.Kept (Y : XNet S) (i : Id) : Prop := i.length = 1 ∧ i ∈ Y.allIds

instance (Y : XNet S) (i : Id) : Decidable (Y.Kept i) := by
  unfold XNet.Kept; infer_instance

/-- The names of `Z` the allocator renames, with repetitions. -/
def XNet.moved (Y Z : XNet S) : List Id := Z.allIds.filter fun j => !decide (Y.Kept j)

/-- The numbers below the length of the list of identifiers of `Z` that no
kept name of `Z` uses. -/
def XNet.spare (Y Z : XNet S) : List Nat :=
  (List.range Z.allIds.length).filter fun k => !decide (Y.Kept [k] ∧ [k] ∈ Z.allIds)

/-- **The allocator**: keep a name of one cell held in `Y`; give any other
name of `Z` a spare number, the `m`-th for the `m`-th name moved. -/
def XNet.reuseName (Y Z : XNet S) (i : Id) : Id :=
  if Y.Kept i then i else
    match firstIdx (Y.moved Z) i with
    | some m => [(Y.spare Z).getD m 0]
    | none => i

/-- **There are always enough spare numbers.** -/
theorem XNet.spare_length (Y Z : XNet S) : (Y.moved Z).length ≤ (Y.spare Z).length := by
  have h₁ := length_filter_add_not (fun j => decide (Y.Kept j)) Z.allIds
  have h₂ := length_filter_add_not (fun k => decide (Y.Kept [k] ∧ [k] ∈ Z.allIds))
    (List.range Z.allIds.length)
  rw [List.length_range] at h₂
  have hR : ((List.range Z.allIds.length).filter
      fun k => decide (Y.Kept [k] ∧ [k] ∈ Z.allIds)).length ≤
      (Z.allIds.filter fun j => decide (Y.Kept j)).length := by
    have hn : (((List.range Z.allIds.length).filter
        fun k => decide (Y.Kept [k] ∧ [k] ∈ Z.allIds)).map fun k => [k]).Nodup := by
      refine List.pairwise_map.2 ((List.nodup_range.sublist List.filter_sublist).imp ?_)
      intro a b hne e
      exact hne (List.cons.inj e).1
    have hs := List.Nodup.length_le_of_subset
        (l₂ := Z.allIds.filter fun j => decide (Y.Kept j)) hn (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      obtain ⟨-, hk⟩ := List.mem_filter.1 hk
      have hk := of_decide_eq_true hk
      exact List.mem_filter.2 ⟨hk.2, decide_eq_true hk.1⟩)
    rwa [List.length_map] at hs
  unfold XNet.moved XNet.spare
  omega

theorem XNet.reuseName_kept {Y Z : XNet S} {i : Id} (h : Y.Kept i) : Y.reuseName Z i = i := by
  unfold XNet.reuseName
  rw [ite_pos' h]

/-- A name moved goes to a spare number, given by its place among the names
moved. -/
theorem XNet.reuseName_moved {Y Z : XNet S} {i : Id} (hi : i ∈ Z.allIds) (h : ¬ Y.Kept i) :
    ∃ m, ∃ hm : m < (Y.spare Z).length,
      Y.reuseName Z i = [(Y.spare Z)[m]] ∧ (Y.moved Z)[m]? = some i := by
  have hmem : i ∈ Y.moved Z := List.mem_filter.2 ⟨hi, by simp [h]⟩
  obtain ⟨m, hm⟩ := firstIdx_mem hmem
  have hg := firstIdx_get hm
  have hl : m < (Y.moved Z).length := (List.getElem?_eq_some_iff.1 hg).1
  have hm' : m < (Y.spare Z).length := Nat.lt_of_lt_of_le hl (XNet.spare_length Y Z)
  refine ⟨m, hm', ?_, hg⟩
  unfold XNet.reuseName
  rw [ite_neg' h, hm]
  simp [List.getD_eq_getElem?_getD, hm']

/-- Every name of `Z` goes to a name of one cell: a kept name of `Y`, or a
number below the length of the list of identifiers of `Z`. -/
theorem XNet.reuseName_small {Y Z : XNet S} {i : Id} (hi : i ∈ Z.allIds) :
    ∃ k, Y.reuseName Z i = [k] ∧ (k < Z.allIds.length ∨ [k] ∈ Y.allIds) := by
  by_cases h : Y.Kept i
  · obtain ⟨k, rfl⟩ := List.length_eq_one_iff.1 h.1
    exact ⟨k, XNet.reuseName_kept h, .inr h.2⟩
  · obtain ⟨m, hm, e, -⟩ := XNet.reuseName_moved hi h
    refine ⟨_, e, .inl ?_⟩
    have := List.getElem_mem (l := Y.spare Z) hm
    exact List.mem_range.1 (List.mem_filter.1 this).1

/-- **The allocator is a renaming.** -/
theorem XNet.reuse_renaming (Y Z : XNet S) : Renaming (Y.reuseName Z) Z.toNet where
  inj := fun {i j} hi hj e => by
    have hi := XNet.used_ids hi
    have hj := XNet.used_ids hj
    have spare_free : ∀ {m} (hm : m < (Y.spare Z).length) {i}, i ∈ Z.allIds → Y.Kept i →
        i ≠ [(Y.spare Z)[m]] := by
      intro m hm i hi hk e
      have := (List.mem_filter.1 (List.getElem_mem (l := Y.spare Z) hm)).2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
      exact this ⟨e ▸ hk, e ▸ hi⟩
    by_cases hki : Y.Kept i <;> by_cases hkj : Y.Kept j
    · rwa [XNet.reuseName_kept hki, XNet.reuseName_kept hkj] at e
    · obtain ⟨m, hm, ej, -⟩ := XNet.reuseName_moved hj hkj
      rw [XNet.reuseName_kept hki, ej] at e
      exact absurd e (spare_free hm hi hki)
    · obtain ⟨m, hm, ei, -⟩ := XNet.reuseName_moved hi hki
      rw [XNet.reuseName_kept hkj, ei] at e
      exact absurd e.symm (spare_free hm hj hkj)
    · obtain ⟨m, hm, ei, gi⟩ := XNet.reuseName_moved hi hki
      obtain ⟨m', hm', ej, gj⟩ := XNet.reuseName_moved hj hkj
      rw [ei, ej] at e
      have hnd : (Y.spare Z).Nodup := List.nodup_range.sublist List.filter_sublist
      obtain rfl := hnd.eq_of_getElem_eq hm hm' (List.cons.inj e).1
      rw [gi] at gj
      exact Option.some.inj gj
  fresh := fun {a α i} l ha hi e => by
    obtain ⟨k, ek, -⟩ := XNet.reuseName_small (Y := Y) (XNet.used_ids hi)
    obtain ⟨k', ek', -⟩ := XNet.reuseName_small (Y := Y) (XNet.used_ids (X := Z) (.inl ⟨α, ha⟩))
    rw [ek, ek'] at e
    have := congrArg List.length e
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero (by omega)

/-! ### The run -/

variable {xs : XSys S} {X Y : XNet S}

/-- Rounds of `XNet.parStep`, each followed by the allocator. -/
def XNet.reuseRun (xs : XSys S) : Nat → XNet S → XNet S × Nat
  | 0, X => (X, 0)
  | n + 1, X =>
    if (X.parStep xs).2 = 0 then (X, 0)
    else ((XNet.reuseRun xs n ((X.parStep xs).1.map (X.reuseName (X.parStep xs).1))).1,
      (X.parStep xs).2 +
        (XNet.reuseRun xs n ((X.parStep xs).1.map (X.reuseName (X.parStep xs).1))).2)

/-- The longest list of identifiers held in the run. -/
def XNet.reusePeak (xs : XSys S) : Nat → XNet S → Nat
  | 0, X => X.allIds.length
  | n + 1, X =>
    if (X.parStep xs).2 = 0 then X.allIds.length
    else max X.allIds.length
      (XNet.reusePeak xs n ((X.parStep xs).1.map (X.reuseName (X.parStep xs).1)))

theorem XNet.reusePeak_ge (xs : XSys S) : ∀ (n : Nat) (X : XNet S),
    X.allIds.length ≤ X.reusePeak xs n
  | 0, _ => Nat.le_refl _
  | n + 1, X => by
    unfold XNet.reusePeak
    split
    · exact Nat.le_refl _
    · exact Nat.le_max_left _ _

theorem XNet.fireList_free (ar : S → Nat) :
    ∀ (rs : List (XRedex S)) (X : XNet S), (X.fireList ar rs).free = X.free
  | [], _ => rfl
  | _ :: rs, _ => (XNet.fireList_free ar rs _).trans rfl

theorem XNet.parStep_free (X : XNet S) : (X.parStep xs).1.free = X.free :=
  XNet.fireList_free _ _ _

/-- Every name of the net is one cell holding a number below `P`. -/
def XNet.Small (P : Nat) (X : XNet S) : Prop := ∀ i ∈ X.allIds, ∃ k, i = [k] ∧ k < P

theorem XNet.Small.mono {P Q : Nat} (h : X.Small P) (hPQ : P ≤ Q) : X.Small Q := fun i hi => by
  obtain ⟨k, e, hk⟩ := h i hi
  exact ⟨k, e, by omega⟩

/-- A round and the allocator keep the names small, up to the longer of the
two lists of identifiers. -/
theorem XNet.reuse_small {P : Nat} (h : X.Small P) :
    ((X.parStep xs).1.map (X.reuseName (X.parStep xs).1)).Small
      (max P (X.parStep xs).1.allIds.length) := by
  intro i hi
  rw [XNet.allIds_map] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  obtain ⟨k, e, hk⟩ := XNet.reuseName_small (Y := X) hj
  refine ⟨k, e, ?_⟩
  rcases hk with hk | hk
  · omega
  · obtain ⟨k', e', hk'⟩ := h _ hk
    obtain rfl := (List.cons.inj e').1
    omega

/-- The free ports of a net with small names keep their names. -/
theorem XNet.reuse_free {P : Nat} (h : X.Small P) :
    ((X.parStep xs).1.map (X.reuseName (X.parStep xs).1)).free = X.free := by
  show ((X.parStep xs).1.free.map (mapPort _)) = X.free
  rw [XNet.parStep_free]
  refine (List.map_congr_left fun p hp => ?_).trans (List.map_id _)
  have hm : p.1 ∈ X.allIds :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  obtain ⟨k, e, -⟩ := h _ hm
  have hk : X.Kept p.1 := ⟨by rw [e]; rfl, hm⟩
  exact Prod.ext (XNet.reuseName_kept hk) rfl

/-- **Small names**: if the names of the input are one cell, below the
length of its list of identifiers, every name the run holds is one cell,
below the longest list of identifiers held in the run. -/
theorem XNet.reuseRun_names (xs : XSys S) :
    ∀ (n : Nat) (X : XNet S) (P : Nat), X.Small P →
      (X.reuseRun xs n).1.Small (max P (X.reusePeak xs n))
  | 0, X, P, h => h.mono (Nat.le_max_left _ _)
  | n + 1, X, P, h => by
    unfold XNet.reuseRun XNet.reusePeak
    split
    · exact h.mono (Nat.le_max_left _ _)
    · have ih := XNet.reuseRun_names xs n _ _ (XNet.reuse_small (xs := xs) h)
      have hge := XNet.reusePeak_ge xs n
        ((X.parStep xs).1.map (X.reuseName (X.parStep xs).1))
      rw [XNet.allIds_map, List.length_map] at hge
      refine ih.mono ?_
      omega

/-- **The free ports keep their names** throughout the run, if the names of
the input are small. -/
theorem XNet.reuseRun_free (xs : XSys S) :
    ∀ (n : Nat) (X : XNet S) (P : Nat), X.Small P → (X.reuseRun xs n).1.free = X.free
  | 0, _, _, _ => rfl
  | n + 1, X, P, h => by
    unfold XNet.reuseRun
    split
    · rfl
    · exact (XNet.reuseRun_free xs n _ _ (XNet.reuse_small (xs := xs) h)).trans
        (XNet.reuse_free h)

theorem Net.map_map (f g : Id → Id) (N : Net S) : (N.map f).map g = N.map (g ∘ f) := by
  refine Net.ext' (fun i γ => ⟨?_, ?_⟩) (fun p q => ⟨?_, ?_⟩) (fun p => ⟨?_, ?_⟩)
  · rintro ⟨_, rfl, i', rfl, h⟩
    exact ⟨i', rfl, h⟩
  · rintro ⟨i', rfl, h⟩
    exact ⟨f i', rfl, i', rfl, h⟩
  · rintro ⟨_, _, rfl, rfl, p', q', rfl, rfl, h⟩
    exact ⟨p', q', rfl, rfl, h⟩
  · rintro ⟨p', q', rfl, rfl, h⟩
    exact ⟨mapPort f p', mapPort f q', rfl, rfl, p', q', rfl, rfl, h⟩
  · rintro ⟨_, rfl, p', rfl, h⟩
    exact ⟨p', rfl, h⟩
  · rintro ⟨p', rfl, h⟩
    exact ⟨mapPort f p', rfl, p', rfl, h⟩

theorem Net.used_of_map {N : Net S} {f : Id → Id} {i : Id} (h : N.Used i) :
    (N.map f).Used (f i) := by
  rcases h with ⟨γ, hg⟩ | ⟨k, q, hl⟩ | ⟨k, hfr⟩
  · exact .inl ⟨γ, i, rfl, hg⟩
  · exact .inr (.inl ⟨k, mapPort f q, (i, k), q, rfl, rfl, hl⟩)
  · exact .inr (.inr ⟨k, (i, k), rfl, hfr⟩)

/-- A renaming of a renamed net, after the first, is a renaming. -/
theorem Renaming.comp {N : Net S} {f g : Id → Id} (hf : Renaming f N)
    (hg : Renaming g (N.map f)) : Renaming (g ∘ f) N where
  inj := fun hi hj e => hf.inj hi hj (hg.inj (Net.used_of_map hi) (Net.used_of_map hj) e)
  fresh := fun l ha hi e => hg.fresh l ⟨_, rfl, ha⟩ (Net.used_of_map hi) e

/-- A net equal to a renaming of a net in the invariant is in it. -/
theorem XNet.ok_of_map {f : Id → Id} (hX : X.Ok xs.sys.ar) (hf : Renaming f X.toNet)
    (e : Y.toNet = X.toNet.map f) : Y.Ok xs.sys.ar := by
  refine ⟨e ▸ hf.wf_map hX.1, ?_⟩
  rw [e, hf.compact_map hX.1, hX.2]

/-- **The run is the parallel run on reused names.**  Started on a renaming
of a net whose names are small, it fires the pairs of `XNet.parRun`, stops
exactly when it does, and ends on the result of `XNet.parRun` renamed by a
renaming that agrees with the first on the free ports. -/
theorem XNet.reuseRun_map (n : Nat) {f : Id → Id} {P : Nat} (hX : X.Ok xs.sys.ar)
    (hf : Renaming f X.toNet) (e : Y.toNet = X.toNet.map f) (hs : Y.Small P) :
    (Y.reuseRun xs n).2 = (X.parRun xs n).2 ∧
      ((Y.reuseRun xs n).1.step xs = none ↔ (X.parRun xs n).1.step xs = none) ∧
      ∃ g, Renaming g (X.parRun xs n).1.toNet ∧ (∀ p ∈ X.free, g p.1 = f p.1) ∧
        (Y.reuseRun xs n).1.toNet = (X.parRun xs n).1.toNet.map g := by
  induction n generalizing X Y f P with
  | zero =>
    have hY := XNet.ok_of_map hX hf e
    obtain ⟨hn, -⟩ := XNet.parStep_map hX hY hf e
    refine ⟨rfl, ?_, f, hf, fun _ _ => rfl, e⟩
    show Y.step xs = none ↔ X.step xs = none
    rw [← XNet.parStep_zero_iff, ← XNet.parStep_zero_iff, hn]
  | succ n ih =>
    have hY := XNet.ok_of_map hX hf e
    obtain ⟨hn, g₁, hg₁, agree₁, eg₁⟩ := XNet.parStep_map hX hY hf e
    unfold XNet.reuseRun XNet.parRun
    by_cases h0 : (X.parStep xs).2 = 0
    · have h0' : (Y.parStep xs).2 = 0 := hn ▸ h0
      rw [ite_pos' h0, ite_pos' h0']
      refine ⟨rfl, ?_, f, hf, fun _ _ => rfl, e⟩
      rw [← XNet.parStep_zero_iff, ← XNet.parStep_zero_iff, h0, h0']
    · have h0' : ¬ (Y.parStep xs).2 = 0 := hn ▸ h0
      rw [ite_neg' h0, ite_neg' h0']
      obtain ⟨-, hX'⟩ := XNet.parStep_spec (xs := xs) hX
      have hh : Renaming (Y.reuseName (Y.parStep xs).1) ((X.parStep xs).1.toNet.map g₁) := by
        rw [← eg₁]
        exact XNet.reuse_renaming _ _
      have e' : ((Y.parStep xs).1.map (Y.reuseName (Y.parStep xs).1)).toNet =
          (X.parStep xs).1.toNet.map (Y.reuseName (Y.parStep xs).1 ∘ g₁) := by
        rw [XNet.map_toNet, eg₁, Net.map_map]
      obtain ⟨ec, hstop, g, hg, agree, eg⟩ :=
        ih hX' (hg₁.comp hh) e' (XNet.reuse_small (xs := xs) hs)
      refine ⟨by rw [ec, hn], hstop, g, hg, fun p hp => ?_, eg⟩
      rw [agree p ((XNet.parStep_free X).symm ▸ hp)]
      show Y.reuseName (Y.parStep xs).1 (g₁ p.1) = f p.1
      rw [agree₁ p.1 (.inr (.inr ⟨p.2, hp⟩))]
      have hfy : mapPort f p ∈ Y.free := by
        show Y.toNet.free (mapPort f p)
        rw [e]
        exact ⟨p, rfl, hp⟩
      have hm : f p.1 ∈ Y.allIds :=
        List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨_, hfy, rfl⟩))
      obtain ⟨k, ek, -⟩ := hs _ hm
      exact XNet.reuseName_kept ⟨by rw [ek]; rfl, hm⟩

/-- **The parallel run on reused names, from the short form.**  It fires
the pairs of `XNet.parRun` in its rounds and stops exactly when it does, on
the result of `XNet.parRun` renamed by a renaming that is `XNet.shortName`
on the free ports; the free ports keep the names of the short form
throughout; and every name it holds is one cell, a number below the
longest list of identifiers held in the run. -/
theorem XNet.reuseRun_short (n : Nat) (hX : X.Ok xs.sys.ar) :
    (X.short.reuseRun xs n).2 = (X.parRun xs n).2 ∧
      ((X.short.reuseRun xs n).1.step xs = none ↔ (X.parRun xs n).1.step xs = none) ∧
      (∃ g, Renaming g (X.parRun xs n).1.toNet ∧ (∀ p ∈ X.free, g p.1 = X.shortName p.1) ∧
        (X.short.reuseRun xs n).1.toNet = (X.parRun xs n).1.toNet.map g) ∧
      (X.short.reuseRun xs n).1.free = X.short.free ∧
      (X.short.reuseRun xs n).1.Small (X.short.reusePeak xs n) := by
  have hs : X.short.Small X.short.allIds.length := XNet.short_small X
  obtain ⟨ec, hstop, hmap⟩ :=
    XNet.reuseRun_map n hX (XNet.short_renaming X) (XNet.short_toNet X) hs
  refine ⟨ec, hstop, hmap, XNet.reuseRun_free xs n _ _ hs, ?_⟩
  have hn := XNet.reuseRun_names xs n _ _ hs
  have hge := XNet.reusePeak_ge xs n X.short
  exact hn.mono (by omega)

end INet
