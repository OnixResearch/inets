import InteractionNets.Packed

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### A persistent ordered memory

The lazy lists need a note of every death, a clock to compare with, and a
log that is packed.  All three come from keeping the agents in a list
that cannot forget.  Here the agents are the entries of a persistent map
ordered by stamp, the live ones and no others: writing an agent inserts
it, taking it out erases it, and a copy of the map is the list of the
agents as it stands.  A thread that takes the agents afresh keeps the map
it finds and works through its own copy from the largest key down.
Nothing is marked dead, dropped or packed. -/

section TreeLemmas

variable {V : Type}

theorem tget_insert (t : Std.TreeMap Nat V) (k a : Nat) (v : V) :
    (t.insert k v)[a]? = if k = a then some v else t[a]? := by
  rw [Std.TreeMap.getElem?_insert]
  simp

theorem tget_erase (t : Std.TreeMap Nat V) (k a : Nat) :
    (t.erase k)[a]? = if k = a then none else t[a]? := by
  rw [Std.TreeMap.getElem?_erase]
  simp

theorem tget_empty (a : Nat) : (∅ : Std.TreeMap Nat V)[a]? = none :=
  Std.TreeMap.getElem?_emptyc

theorem tmem_toList (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (k, v) ∈ t.toList ↔ t[k]? = some v :=
  Std.TreeMap.mem_toList_iff_getElem?_eq_some

/-- The list of an ordered map goes up in its keys. -/
theorem tsorted (t : Std.TreeMap Nat V) : t.toList.Pairwise (fun a b => a.1 < b.1) :=
  (Std.TreeMap.ordered_keys_toList (t := t)).imp fun hab => Nat.compare_eq_lt.1 hab

theorem tmax_none (t : Std.TreeMap Nat V) (h : t.maxKey? = none) : t.toList = [] := by
  have h1 : t.isEmpty = true := Std.TreeMap.maxKey?_eq_none_iff.1 h
  have h2 := Std.TreeMap.isEmpty_toList (t := t)
  rw [h1] at h2
  exact List.isEmpty_iff.1 h2

theorem tmax_some (t : Std.TreeMap Nat V) {s : Nat} (h : t.maxKey? = some s) :
    (∃ v, t[s]? = some v) ∧ ∀ k v, t[k]? = some v → k ≤ s := by
  obtain ⟨hm, hall⟩ := Std.TreeMap.maxKey?_eq_some_iff_mem_and_forall.1 h
  refine ⟨Option.isSome_iff_exists.1 (Std.TreeMap.mem_iff_isSome_getElem?.1 hm), fun k v hk => ?_⟩
  have hk' : k ∈ t := Std.TreeMap.mem_iff_isSome_getElem?.2 (by rw [hk]; rfl)
  exact Nat.isLE_compare.1 (hall k hk')

/-- Two lists that go up in their keys and have the same entries are the
same list. -/
theorem sorted_ext : ∀ {l₁ l₂ : List (Nat × V)}, l₁.Pairwise (fun a b => a.1 < b.1) →
    l₂.Pairwise (fun a b => a.1 < b.1) → (∀ e, e ∈ l₁ ↔ e ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) List.not_mem_nil
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    obtain ⟨ha, h₁'⟩ := List.pairwise_cons.1 h₁
    obtain ⟨hb, h₂'⟩ := List.pairwise_cons.1 h₂
    have eab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | hm
      · exact e
      · rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e | hm'
        · exact e.symm
        · have := hb a hm
          have := ha b hm'
          omega
    subst eab
    have ht : ∀ e, e ∈ l₁ ↔ e ∈ l₂ := fun e => by
      constructor
      · intro he
        rcases List.mem_cons.1 ((h e).1 (List.mem_cons_of_mem _ he)) with e' | hm
        · subst e'
          exact absurd (ha _ he) (Nat.lt_irrefl _)
        · exact hm
      · intro he
        rcases List.mem_cons.1 ((h e).2 (List.mem_cons_of_mem _ he)) with e' | hm
        · subst e'
          exact absurd (hb _ he) (Nat.lt_irrefl _)
        · exact hm
    rw [sorted_ext h₁' h₂' ht]

/-- Inserting above every key puts the entry at the end of the list. -/
theorem toList_insert_max (t : Std.TreeMap Nat V) {s : Nat}
    (hs : ∀ k v, t[k]? = some v → k < s) (v : V) :
    (t.insert s v).toList = t.toList ++ [(s, v)] := by
  apply sorted_ext (tsorted _)
  · rw [List.pairwise_append]
    refine ⟨tsorted t, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    obtain ⟨k, w⟩ := a
    exact hs k w ((tmem_toList t k w).1 ha)
  · intro e
    obtain ⟨k, w⟩ := e
    rw [tmem_toList, tget_insert, List.mem_append, tmem_toList, List.mem_singleton]
    by_cases e : s = k
    · rw [ite_pos' e]
      subst e
      constructor
      · intro h
        cases h
        exact .inr rfl
      · rintro (h | h)
        · exact absurd (hs _ _ h) (Nat.lt_irrefl _)
        · cases h
          rfl
    · rw [ite_neg' e]
      constructor
      · exact .inl
      · rintro (h | h)
        · exact h
        · cases h
          exact absurd rfl e

/-- Erasing a key takes its entry out of the list. -/
theorem toList_erase (t : Std.TreeMap Nat V) (s : Nat) :
    (t.erase s).toList = t.toList.filter fun e => decide (e.1 ≠ s) := by
  apply sorted_ext (tsorted _) ((tsorted t).sublist List.filter_sublist)
  intro e
  obtain ⟨k, w⟩ := e
  rw [tmem_toList, tget_erase, List.mem_filter, tmem_toList]
  by_cases e : s = k
  · rw [ite_pos' e]
    constructor
    · intro h
      cases h
    · rintro ⟨-, h⟩
      exact absurd e.symm (by simpa using h)
  · rw [ite_neg' e]
    constructor
    · intro h
      exact ⟨h, by simpa using fun h' : k = s => e h'.symm⟩
    · exact fun h => h.1

/-- The entry with the largest key is the last of the list. -/
theorem toList_max (t : Std.TreeMap Nat V) {s : Nat} (h : t.maxKey? = some s) :
    ∃ v, t[s]? = some v ∧ t.toList = (t.erase s).toList ++ [(s, v)] := by
  obtain ⟨⟨v, hv⟩, hall⟩ := tmax_some t h
  refine ⟨v, hv, ?_⟩
  apply sorted_ext (tsorted _)
  · rw [List.pairwise_append]
    refine ⟨tsorted _, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    obtain ⟨k, w⟩ := a
    have hk := (tmem_toList _ k w).1 ha
    rw [tget_erase] at hk
    by_cases e : s = k
    · rw [ite_pos' e] at hk
      cases hk
    · rw [ite_neg' e] at hk
      have := hall k w hk
      show k < s
      omega
  · intro e
    obtain ⟨k, w⟩ := e
    rw [tmem_toList, List.mem_append, tmem_toList, tget_erase, List.mem_singleton]
    by_cases e : s = k
    · rw [ite_pos' e]
      subst e
      constructor
      · intro h
        rw [hv] at h
        cases h
        exact .inr rfl
      · rintro (h | h)
        · cases h
        · cases h
          exact hv
    · rw [ite_neg' e]
      constructor
      · exact .inl
      · rintro (h | h)
        · exact h
        · cases h
          exact absurd rfl e

end TreeLemmas

section Ordered

variable [DecidableEq S]

/-- The entries of an ordered map, the largest key first. -/
def treeList (t : Std.TreeMap Nat (Id × S)) : List (Id × S) := t.toList.reverse.map (·.2)

omit [DecidableEq S] in
theorem mem_treeList (t : Std.TreeMap Nat (Id × S)) (e : Id × S) :
    e ∈ treeList t ↔ ∃ s : Nat, t[s]? = some e := by
  constructor
  · intro h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    exact ⟨c.1, (tmem_toList t c.1 c.2).1 (List.mem_reverse.1 hc)⟩
  · rintro ⟨s, hs⟩
    exact List.mem_map.2 ⟨(s, e), List.mem_reverse.2 ((tmem_toList t s e).2 hs), rfl⟩

omit [DecidableEq S] in
theorem treeList_insert_max (t : Std.TreeMap Nat (Id × S)) {s : Nat}
    (hs : ∀ (k : Nat) v, t[k]? = some v → k < s) (v : Id × S) :
    treeList (t.insert s v) = v :: treeList t := by
  unfold treeList
  rw [toList_insert_max t hs v, List.reverse_append]
  rfl

omit [DecidableEq S] in
theorem treeList_max (t : Std.TreeMap Nat (Id × S)) {s : Nat} (h : t.maxKey? = some s) :
    ∃ v, t[s]? = some v ∧ treeList t = v :: treeList (t.erase s) := by
  obtain ⟨v, hv, e⟩ := toList_max t h
  refine ⟨v, hv, ?_⟩
  unfold treeList
  rw [e, List.reverse_append]
  rfl

omit [DecidableEq S] in
theorem treeList_none (t : Std.TreeMap Nat (Id × S)) (h : t.maxKey? = none) :
    treeList t = [] := by
  unfold treeList
  rw [tmax_none t h]
  rfl

omit [DecidableEq S] in
theorem treeList_empty : treeList (∅ : Std.TreeMap Nat (Id × S)) = [] := by
  have e : (∅ : Std.TreeMap Nat (Id × S)).toList = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun c hc => by
      have := (tmem_toList _ c.1 c.2).1 hc
      rw [tget_empty] at this
      cases this
  unfold treeList
  rw [e]
  rfl

omit [DecidableEq S] in
theorem treeList_length (t : Std.TreeMap Nat (Id × S)) : (treeList t).length = t.size := by
  unfold treeList
  rw [List.length_map, List.length_reverse, Std.TreeMap.length_toList]

/-- **A memory on a persistent ordered map.**  The agents are the entries
of a map ordered by stamp, the live ones and no others; a hash map from
the names says under which stamp an agent is.  Writing an agent inserts
it, taking it out erases it, and a copy of the map is the list of the
agents as it stands: the map is persistent, so a copy stays what it was
when the memory goes on. -/
structure TMem (S : Type) where
  cells : Std.TreeMap Nat (Id × S)
  stamp : Nat
  live : Std.HashMap Id (Nat × S)
  free : List Port
  wires : List (Port × Port)
  nbrs : Std.HashMap Port (List Port)

/-- The memory of lists that it stands for. -/
def TMem.toX (H : TMem S) : XNet S := ⟨treeList H.cells, H.free, H.wires⟩

/-- The symbol of an agent: one lookup. -/
def TMem.sym (H : TMem S) (i : Id) : Option S := (H.live[i]?).map (·.2)

/-- The neighbours of a port: one lookup. -/
def TMem.nb (H : TMem S) (p : Port) : List Port := (H.nbrs[p]?).getD []

/-- The two maps of the agents say the same, the stamps are below the next
stamp, and the map of the neighbours lists the neighbours. -/
structure TMem.Ok (H : TMem S) : Prop where
  lt : ∀ (k : Nat) v, H.cells[k]? = some v → k < H.stamp
  fwd : ∀ (i : Id) (s : Nat) γ, H.live[i]? = some (s, γ) → H.cells[s]? = some (i, γ)
  bwd : ∀ (s : Nat) (i : Id) γ, H.cells[s]? = some (i, γ) → H.live[i]? = some (s, γ)
  nbrs : ∀ p, H.nb p = nbOf H.wires p

omit [DecidableEq S] in
/-- One lookup in the map of the names is the lookup in the list of
agents. -/
theorem TMem.Ok.sym {H : TMem S} (h : H.Ok) (i : Id) : H.sym i = assoc i H.toX.agents := by
  cases hl : H.live[i]? with
  | none =>
    have e : H.sym i = none := by
      show (H.live[i]?).map (·.2) = none
      rw [hl]
      rfl
    rw [e]
    refine (assoc_none_of_not_mem i _ fun hm => ?_).symm
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
    obtain ⟨s, hs⟩ := (mem_treeList H.cells c).1 hc
    have := h.bwd s c.1 c.2 hs
    rw [hl] at this
    cases this
  | some v =>
    obtain ⟨s, γ⟩ := v
    have e : H.sym i = some γ := by
      show (H.live[i]?).map (·.2) = some γ
      rw [hl]
      rfl
    rw [e]
    refine (assoc_eq_of_unique ((mem_treeList H.cells (i, γ)).2 ⟨s, h.fwd i s γ hl⟩)
      fun γ' hm => ?_).symm
    obtain ⟨s', hs'⟩ := (mem_treeList H.cells (i, γ')).1 hm
    have := h.bwd s' i γ' hs'
    rw [hl] at this
    cases this
    rfl

omit [DecidableEq S] in
theorem TMem.Ok.first {H : TMem S} (h : H.Ok) (p : Port) :
    (H.nb p).head? = assoc p H.toX.wires := by
  rw [h.nbrs p]
  exact (assoc_nbOf H.wires p).symm

omit [DecidableEq S] in
theorem TMem.Ok.next {H : TMem S} (h : H.Ok) (c p : Port) :
    (H.nb c).find? (fun q => decide (q ≠ p)) = nextSeg H.toX.wires c p := by
  rw [h.nbrs c]
  exact (nextSeg_nbOf H.wires c p).symm

/-- Take an agent out: two erasures. -/
def TMem.take (H : TMem S) (a : Id) : TMem S :=
  match H.live[a]? with
  | some v => ⟨H.cells.erase v.1, H.stamp, H.live.erase a, H.free, H.wires, H.nbrs⟩
  | none => H

/-- Write an agent: two insertions. -/
def TMem.put (H : TMem S) (i : Id) (γ : S) : TMem S :=
  ⟨H.cells.insert H.stamp (i, γ), H.stamp + 1, H.live.insert i (H.stamp, γ), H.free,
    H.wires, H.nbrs⟩

/-- Write a segment. -/
def TMem.link (H : TMem S) (p q : Port) : TMem S :=
  ⟨H.cells, H.stamp, H.live, H.free, (p, q) :: H.wires, H.nbrs.insert p (pushNb q (H.nb p))⟩

omit [DecidableEq S] in
theorem TMem.take_spec {H : TMem S} (h : H.Ok) (a : Id) :
    (H.take a).toX = H.toX.takeAgent a ∧ (H.take a).Ok := by
  cases hl : H.live[a]? with
  | none =>
    have e : H.take a = H := by
      unfold TMem.take
      rw [hl]
    rw [e]
    refine ⟨?_, h⟩
    have ef : (treeList H.cells).filter (fun c => decide (c.1 ≠ a)) = treeList H.cells :=
      List.filter_eq_self.2 fun c hc => by
        obtain ⟨s, hs⟩ := (mem_treeList H.cells c).1 hc
        have hb := h.bwd s c.1 c.2 hs
        have : c.1 ≠ a := fun ea => by
          rw [ea, hl] at hb
          cases hb
        simpa using this
    show (⟨treeList H.cells, H.free, H.wires⟩ : XNet S) =
      ⟨(treeList H.cells).filter fun c => decide (c.1 ≠ a), H.free, H.wires⟩
    rw [ef]
  | some v =>
    obtain ⟨s₀, γ₀⟩ := v
    have e : H.take a = ⟨H.cells.erase s₀, H.stamp, H.live.erase a, H.free, H.wires,
        H.nbrs⟩ := by
      unfold TMem.take
      rw [hl]
    have hc₀ := h.fwd a s₀ γ₀ hl
    rw [e]
    refine ⟨?_, ⟨fun k v hk => ?_, fun i s γ hi => ?_, fun s i γ hs => ?_, h.nbrs⟩⟩
    · have hcong : H.cells.toList.filter (fun c => decide (c.1 ≠ s₀)) =
          H.cells.toList.filter (fun c => decide (c.2.1 ≠ a)) :=
        List.filter_congr fun c hc => by
          obtain ⟨k, j, δ⟩ := c
          have hk := (tmem_toList H.cells k (j, δ)).1 hc
          have hb := h.bwd k j δ hk
          by_cases ek : k = s₀
          · have ej : j = a := by
              rw [ek, hc₀] at hk
              cases hk
              rfl
            simp [ek, ej]
          · have ej : j ≠ a := fun ej => by
              rw [ej, hl] at hb
              cases hb
              exact ek rfl
            simp [ek, ej]
      show (⟨treeList (H.cells.erase s₀), H.free, H.wires⟩ : XNet S) =
        ⟨(treeList H.cells).filter fun c => decide (c.1 ≠ a), H.free, H.wires⟩
      have et : treeList (H.cells.erase s₀) =
          (treeList H.cells).filter fun c => decide (c.1 ≠ a) := by
        unfold treeList
        rw [toList_erase, hcong, List.filter_map, List.filter_reverse]
        rfl
      rw [et]
    · have hk' : (H.cells.erase s₀)[k]? = some v := hk
      rw [tget_erase] at hk'
      by_cases ee : s₀ = k
      · rw [ite_pos' ee] at hk'
        cases hk'
      · rw [ite_neg' ee] at hk'
        exact h.lt k v hk'
    · have hi' : (H.live.erase a)[i]? = some (s, γ) := hi
      rw [hget_erase] at hi'
      by_cases ee : a = i
      · rw [ite_pos' ee] at hi'
        cases hi'
      · rw [ite_neg' ee] at hi'
        have hc := h.fwd i s γ hi'
        show (H.cells.erase s₀)[s]? = some (i, γ)
        rw [tget_erase]
        have ne : ¬ s₀ = s := fun es => by
          rw [← es, hc₀] at hc
          cases hc
          exact ee rfl
        rw [ite_neg' ne]
        exact hc
    · have hs' : (H.cells.erase s₀)[s]? = some (i, γ) := hs
      rw [tget_erase] at hs'
      by_cases ee : s₀ = s
      · rw [ite_pos' ee] at hs'
        cases hs'
      · rw [ite_neg' ee] at hs'
        have hb := h.bwd s i γ hs'
        show (H.live.erase a)[i]? = some (s, γ)
        rw [hget_erase]
        have ne : ¬ a = i := fun ea => by
          rw [← ea, hl] at hb
          cases hb
          exact ee rfl
        rw [ite_neg' ne]
        exact hb

omit [DecidableEq S] in
theorem TMem.toX_put {H : TMem S} (h : H.Ok) (i : Id) (γ : S) :
    (H.put i γ).toX = H.toX.putAgent i γ := by
  show (⟨treeList (H.cells.insert H.stamp (i, γ)), H.free, H.wires⟩ : XNet S) =
    ⟨(i, γ) :: treeList H.cells, H.free, H.wires⟩
  rw [treeList_insert_max H.cells h.lt (i, γ)]

omit [DecidableEq S] in
theorem TMem.Ok.put {H : TMem S} (h : H.Ok) {i : Id} (hi : assoc i H.toX.agents = none)
    (γ : S) : (H.put i γ).Ok := by
  have hn : H.live[i]? = none := by
    have e := h.sym i
    rw [hi] at e
    cases hl : H.live[i]? with
    | none => rfl
    | some v =>
      have e' : (H.live[i]?).map (·.2) = none := e
      rw [hl] at e'
      cases e'
  refine ⟨fun k v hk => ?_, fun j s δ hj => ?_, fun s j δ hs => ?_, h.nbrs⟩
  · have hk' : (H.cells.insert H.stamp (i, γ))[k]? = some v := hk
    rw [tget_insert] at hk'
    show k < H.stamp + 1
    by_cases ee : H.stamp = k
    · omega
    · rw [ite_neg' ee] at hk'
      have := h.lt k v hk'
      omega
  · have hj' : (H.live.insert i (H.stamp, γ))[j]? = some (s, δ) := hj
    rw [hget_insert] at hj'
    show (H.cells.insert H.stamp (i, γ))[s]? = some (j, δ)
    rw [tget_insert]
    by_cases ee : i = j
    · rw [ite_pos' ee] at hj'
      cases hj'
      rw [ite_pos' rfl, ee]
    · rw [ite_neg' ee] at hj'
      have hc := h.fwd j s δ hj'
      have := h.lt s _ hc
      rw [ite_neg' (by omega)]
      exact hc
  · have hs' : (H.cells.insert H.stamp (i, γ))[s]? = some (j, δ) := hs
    rw [tget_insert] at hs'
    show (H.live.insert i (H.stamp, γ))[j]? = some (s, δ)
    rw [hget_insert]
    by_cases ee : H.stamp = s
    · rw [ite_pos' ee] at hs'
      cases hs'
      rw [ite_pos' rfl, ee]
    · rw [ite_neg' ee] at hs'
      have hb := h.bwd s j δ hs'
      have ne : ¬ i = j := fun ei => by
        rw [← ei, hn] at hb
        cases hb
      rw [ite_neg' ne]
      exact hb

omit [DecidableEq S] in
theorem TMem.Ok.link {H : TMem S} (h : H.Ok) (p q : Port) : (H.link p q).Ok :=
  ⟨h.lt, h.fwd, h.bwd, fun p' => by
    show ((H.nbrs.insert p (pushNb q (H.nb p)))[p']?).getD [] =
      if p = p' then pushNb q (nbOf H.wires p') else nbOf H.wires p'
    rw [hget_insert]
    by_cases e : p = p'
    · rw [ite_pos' e, ite_pos' e, h.nbrs, e]
      rfl
    · rw [ite_neg' e, ite_neg' e]
      exact h.nbrs p'⟩

/-- A memory with no agents and no segments. -/
def TMem.empty (free : List Port) : TMem S := ⟨∅, 0, ∅, free, [], ∅⟩

omit [DecidableEq S] in
theorem TMem.empty_ok (free : List Port) : (TMem.empty free : TMem S).Ok := by
  refine ⟨fun k v hk => ?_, fun i s γ hl => ?_, fun s i γ hs => ?_, fun p => ?_⟩
  · have hk' : (∅ : Std.TreeMap Nat (Id × S))[k]? = some v := hk
    rw [tget_empty] at hk'
    cases hk'
  · have hl' : (∅ : Std.HashMap Id (Nat × S))[i]? = some (s, γ) := hl
    rw [Std.HashMap.getElem?_empty] at hl'
    cases hl'
  · have hs' : (∅ : Std.TreeMap Nat (Id × S))[s]? = some (i, γ) := hs
    rw [tget_empty] at hs'
    cases hs'
  · show ((∅ : Std.HashMap Port (List Port))[p]?).getD [] = []
    rw [Std.HashMap.getElem?_empty]
    rfl

/-- The memory of a net: its agents written one by one, the last first,
then its segments. -/
def TMem.ofX (X : XNet S) : TMem S :=
  X.wires.foldr (fun e H => H.link e.1 e.2)
    (X.agents.foldr (fun e H => H.put e.1 e.2) (TMem.empty X.free))

omit [DecidableEq S] in
theorem TMem.ofX_agents (free : List Port) : ∀ l : List (Id × S), (l.map Prod.fst).Nodup →
    (l.foldr (fun e H => H.put e.1 e.2) (TMem.empty free)).Ok ∧
      (l.foldr (fun e H => H.put e.1 e.2) (TMem.empty free)).toX = ⟨l, free, []⟩
  | [], _ => ⟨TMem.empty_ok free, by
      show (⟨treeList (∅ : Std.TreeMap Nat (Id × S)), free, []⟩ : XNet S) = _
      rw [treeList_empty]⟩
  | (i, γ) :: l, hnd => by
    have hnd' : i ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    obtain ⟨ok, e⟩ := TMem.ofX_agents free l hnd'.2
    have hi : assoc i (l.foldr (fun e H => H.put e.1 e.2) (TMem.empty free)).toX.agents =
        none := by
      rw [e]
      exact assoc_none_of_not_mem i l hnd'.1
    refine ⟨ok.put hi γ, ?_⟩
    show ((l.foldr (fun e H => H.put e.1 e.2) (TMem.empty free)).put i γ).toX = _
    rw [TMem.toX_put ok, e]
    rfl

omit [DecidableEq S] in
theorem TMem.ofX_links (H₀ : TMem S) (h₀ : H₀.Ok) : ∀ ws : List (Port × Port),
    (ws.foldr (fun e H => H.link e.1 e.2) H₀).Ok ∧
      (ws.foldr (fun e H => H.link e.1 e.2) H₀).toX =
        ⟨H₀.toX.agents, H₀.toX.free, ws ++ H₀.toX.wires⟩
  | [] => ⟨h₀, rfl⟩
  | (p, q) :: ws => by
    obtain ⟨ok, e⟩ := TMem.ofX_links H₀ h₀ ws
    refine ⟨ok.link p q, ?_⟩
    show (((ws.foldr (fun e H => H.link e.1 e.2) H₀).toX).putLink p q) = _
    rw [e]
    rfl

omit [DecidableEq S] in
/-- The memory of a net stands for the net, when no agent is listed
twice. -/
theorem TMem.ofX_toX {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) :
    (TMem.ofX X).Ok ∧ (TMem.ofX X).toX = X := by
  obtain ⟨ok, e⟩ := TMem.ofX_agents X.free X.agents hnd
  obtain ⟨ok', e'⟩ := TMem.ofX_links _ ok X.wires
  refine ⟨ok', ?_⟩
  show (X.wires.foldr (fun e H => H.link e.1 e.2)
    (X.agents.foldr (fun e H => H.put e.1 e.2) (TMem.empty X.free))).toX = X
  rw [e', e]
  show (⟨X.agents, X.free, X.wires ++ []⟩ : XNet S) = X
  rw [List.append_nil]

/-- **A thread on the ordered memory**: the agents still to try, as a map
of its own, and its state.  It tries the entry with the largest key
first. -/
structure TThread (S : Type) where
  todo : Std.TreeMap Nat (Id × S)
  st : TState S

/-- The thread gives up an attempt. -/
def TThread.fail (T : TThread S) : TThread S := ⟨T.todo, .idle⟩

/-- The thread of the program on lists that it stands for. -/
def TThread.toX (T : TThread S) : XThread S := ⟨treeList T.todo, T.st⟩

/-- **One action of a thread on the ordered memory.**  The action of the
indexed program, except that an idle thread takes the entry with the
largest key out of its own map, and a thread that has written a right-hand
side takes the map of the memory as it stands. -/
def TMach.act (xs : XSys S) (H : TMem S) (T : TThread S) : TMem S × TThread S × Nat :=
  match T.st with
  | .idle =>
    match T.todo.maxKey? with
    | none => (H, T, 0)
    | some s =>
      match T.todo[s]? with
      | some e =>
        if H.sym e.1 = some e.2 then (H, ⟨T.todo.erase s, .look e.1 e.2⟩, 0)
        else (H, ⟨T.todo.erase s, .idle⟩, 0)
      | none => (H, T, 0)
  | .look a α =>
    match (H.nb (a, 0)).head? with
    | some q => (H, ⟨T.todo, .seek a α (a, 0) q⟩, 0)
    | none => (H, T.fail, 0)
  | .seek a α p c =>
    match (if c.2 = 0 then H.sym c.1 else none) with
    | some β =>
      if a ≠ c.1 ∧ (xs.rule α β).isSome then (H, ⟨T.todo, .ready a c.1 α β⟩, 0)
      else (H, T.fail, 0)
    | none =>
      match (H.nb c).find? (fun q => decide (q ≠ p)) with
      | some q => (H, ⟨T.todo, .seek a α c q⟩, 0)
      | none => (H, T.fail, 0)
  | .ready a b α β =>
    if H.sym a = some α then (H.take a, ⟨T.todo, .half a b α β⟩, 0)
    else (H, T.fail, 0)
  | .half a b α β =>
    match (if H.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (H.take b, ⟨T.todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1)
    | none => (H.put a α, T.fail, 0)
  | .write ((i, γ) :: as) ls => (H.put i γ, ⟨T.todo, .write as ls⟩, 0)
  | .write [] ((p, q) :: ls) => (H.link p q, ⟨T.todo, .write [] ls⟩, 0)
  | .write [] [] => (H, ⟨H.cells, .idle⟩, 0)

/-- **The action on the ordered memory is the action of the program.** -/
theorem TMach.act_sim (xs : XSys S) {H : TMem S} (h : H.Ok) (T : TThread S)
    (hnd : ((XMach.act xs H.toX T.toX).1.agents.map Prod.fst).Nodup) :
    (TMach.act xs H T).1.toX = (XMach.act xs H.toX T.toX).1 ∧
      (TMach.act xs H T).2.1.toX = (XMach.act xs H.toX T.toX).2.1 ∧
      (TMach.act xs H T).2.2 = (XMach.act xs H.toX T.toX).2.2 ∧ (TMach.act xs H T).1.Ok := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases hmax : todo.maxKey? with
    | none =>
      have eL : TMach.act xs H ⟨todo, .idle⟩ = (H, ⟨todo, .idle⟩, 0) := by
        unfold TMach.act
        dsimp only
        rw [hmax]
      have eT : TThread.toX ⟨todo, .idle⟩ = ⟨[], .idle⟩ := by
        show (⟨treeList todo, .idle⟩ : XThread S) = _
        rw [treeList_none todo hmax]
      rw [eL]
      show H.toX = (XMach.act xs H.toX (TThread.toX ⟨todo, .idle⟩)).1 ∧
        TThread.toX ⟨todo, .idle⟩ = (XMach.act xs H.toX (TThread.toX ⟨todo, .idle⟩)).2.1 ∧
        0 = (XMach.act xs H.toX (TThread.toX ⟨todo, .idle⟩)).2.2 ∧ H.Ok
      rw [eT]
      exact ⟨rfl, rfl, rfl, h⟩
    | some s =>
      obtain ⟨e, he, hl⟩ := treeList_max todo hmax
      have eL : TMach.act xs H ⟨todo, .idle⟩ =
          (if H.sym e.1 = some e.2 then (H, ⟨todo.erase s, .look e.1 e.2⟩, 0)
            else (H, ⟨todo.erase s, .idle⟩, 0)) := by
        unfold TMach.act
        dsimp only
        rw [hmax]
        dsimp only
        rw [he]
      have eT : TThread.toX ⟨todo, .idle⟩ = ⟨e :: treeList (todo.erase s), .idle⟩ := by
        show (⟨treeList todo, .idle⟩ : XThread S) = _
        rw [hl]
      have eX : XMach.act xs H.toX ⟨e :: treeList (todo.erase s), .idle⟩ =
          (if assoc e.1 H.toX.agents = some e.2 then
            (H.toX, ⟨treeList (todo.erase s), .look e.1 e.2⟩, 0)
          else (H.toX, ⟨treeList (todo.erase s), .idle⟩, 0)) := rfl
      rw [eL, eT, eX, h.sym e.1]
      by_cases hs : assoc e.1 H.toX.agents = some e.2
      · rw [ite_pos' hs, ite_pos' hs]
        exact ⟨rfl, rfl, rfl, h⟩
      · rw [ite_neg' hs, ite_neg' hs]
        exact ⟨rfl, rfl, rfl, h⟩
  | look a α =>
    have eT : TThread.toX ⟨todo, .look a α⟩ = ⟨treeList todo, .look a α⟩ := rfl
    rw [eT]
    unfold TMach.act XMach.act
    dsimp only
    rw [h.first (a, 0)]
    cases assoc (a, 0) H.toX.wires <;> exact ⟨rfl, rfl, rfl, h⟩
  | seek a α p c =>
    have eT : TThread.toX ⟨todo, .seek a α p c⟩ = ⟨treeList todo, .seek a α p c⟩ := rfl
    rw [eT]
    unfold TMach.act XMach.act
    dsimp only
    rw [h.sym c.1, h.next c p]
    cases (if c.2 = 0 then assoc c.1 H.toX.agents else none) with
    | some β =>
      dsimp only
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β).isSome
      · rw [ite_pos' hc, ite_pos' hc]
        exact ⟨rfl, rfl, rfl, h⟩
      · rw [ite_neg' hc, ite_neg' hc]
        exact ⟨rfl, rfl, rfl, h⟩
    | none =>
      dsimp only
      cases nextSeg H.toX.wires c p <;> exact ⟨rfl, rfl, rfl, h⟩
  | ready a b α β =>
    have eT : TThread.toX ⟨todo, .ready a b α β⟩ = ⟨treeList todo, .ready a b α β⟩ := rfl
    rw [eT]
    unfold TMach.act XMach.act
    dsimp only
    rw [h.sym a]
    by_cases hc : assoc a H.toX.agents = some α
    · rw [ite_pos' hc, ite_pos' hc]
      obtain ⟨tx, o⟩ := TMem.take_spec h a
      exact ⟨tx, rfl, rfl, o⟩
    · rw [ite_neg' hc, ite_neg' hc]
      exact ⟨rfl, rfl, rfl, h⟩
  | half a b α β =>
    have eT : TThread.toX ⟨todo, .half a b α β⟩ = ⟨treeList todo, .half a b α β⟩ := rfl
    rw [eT] at hnd ⊢
    unfold XMach.act at hnd
    dsimp only at hnd
    unfold TMach.act XMach.act
    dsimp only
    rw [h.sym b]
    cases hR : (if assoc b H.toX.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      obtain ⟨tx, o⟩ := TMem.take_spec h b
      exact ⟨tx, rfl, rfl, o⟩
    | none =>
      rw [hR] at hnd
      exact ⟨TMem.toX_put h a α, rfl, rfl, h.put (assoc_none_of_nodup_cons hnd) α⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨TMem.toX_put h i γ, rfl, rfl, h.put (assoc_none_of_nodup_cons hnd) γ⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨rfl, rfl, rfl, h.link p q⟩
      | nil => exact ⟨rfl, rfl, rfl, h⟩

/-- The program on the ordered memory: the memory and the threads. -/
structure TMach (S : Type) where
  mem : TMem S
  ths : List (TThread S)

/-- The program on lists that it stands for. -/
def TMach.toX (M : TMach S) : XMach S := ⟨M.mem.toX, M.ths.map TThread.toX⟩

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def TMach.step (xs : XSys S) (M : TMach S) (t : Nat) : TMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(TMach.act xs M.mem T).1, M.ths.set t (TMach.act xs M.mem T).2.1⟩,
      (TMach.act xs M.mem T).2.2)
  | none => (M, 0)

/-- The run under an unending schedule. -/
def TMach.trace (xs : XSys S) (σ : Nat → Nat) (M : TMach S) : Nat → TMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((TMach.trace xs σ M i).1.step xs (σ i)).1,
      (TMach.trace xs σ M i).2 + ((TMach.trace xs σ M i).1.step xs (σ i)).2)

/-- A list as an ordered map: its first entry has the largest key. -/
def treeOf : List (Id × S) → Std.TreeMap Nat (Id × S)
  | [] => ∅
  | e :: l => (treeOf l).insert l.length e

omit [DecidableEq S] in
theorem treeOf_spec : ∀ l : List (Id × S),
    (∀ (k : Nat) v, (treeOf l)[k]? = some v → k < l.length) ∧ treeList (treeOf l) = l
  | [] => ⟨fun k v hk => (by
      have hk' : (∅ : Std.TreeMap Nat (Id × S))[k]? = some v := hk
      rw [tget_empty] at hk'
      cases hk'), treeList_empty⟩
  | e :: l => by
    obtain ⟨lt, tl⟩ := treeOf_spec l
    refine ⟨fun k v hk => ?_, ?_⟩
    · have hk' : ((treeOf l).insert l.length e)[k]? = some v := hk
      rw [tget_insert] at hk'
      show k < l.length + 1
      by_cases ee : l.length = k
      · omega
      · rw [ite_neg' ee] at hk'
        have := lt k v hk'
        omega
    · show treeList ((treeOf l).insert l.length e) = e :: l
      rw [treeList_insert_max _ lt e, tl]

/-- The program before it starts.  Thread `t` has all the agents, from the
`t`-th on. -/
def TMach.init (X : XNet S) (n : Nat) : TMach S :=
  ⟨TMem.ofX X, (List.range n).map fun t =>
    ⟨treeOf (X.agents.drop t ++ X.agents.take t), .idle⟩⟩

omit [DecidableEq S] in
theorem TMach.init_toX {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (TMach.init X n).toX = XMach.init X n := by
  show (⟨(TMem.ofX X).toX, ((List.range n).map _).map TThread.toX⟩ : XMach S) =
    ⟨X, (List.range n).map _⟩
  rw [(TMem.ofX_toX hnd).2, List.map_map]
  refine congrArg (XMach.mk X) (List.map_congr_left fun t _ => ?_)
  show (⟨treeList (treeOf (X.agents.drop t ++ X.agents.take t)), .idle⟩ : XThread S) = _
  rw [(treeOf_spec _).2]

/-- One action on the ordered memory is one action of the program. -/
theorem TMach.step_sim (xs : XSys S) {M : TMach S} (h : M.mem.Ok) (t : Nat)
    (hnd : ((M.toX.step xs t).1.mem.agents.map Prod.fst).Nodup) :
    (M.step xs t).1.toX = (M.toX.step xs t).1 ∧ (M.step xs t).2 = (M.toX.step xs t).2 ∧
      (M.step xs t).1.mem.Ok := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold TMach.step
      rw [ht]
    have ht' : M.toX.ths[t]? = none := by
      show (M.ths.map TThread.toX)[t]? = none
      rw [List.getElem?_map, ht]
      rfl
    have e₂ : M.toX.step xs t = (M.toX, 0) := by
      unfold XMach.step
      rw [ht']
    rw [e₁, e₂]
    exact ⟨rfl, rfl, h⟩
  | some T =>
    have ht' : M.toX.ths[t]? = some T.toX := by
      show (M.ths.map TThread.toX)[t]? = _
      rw [List.getElem?_map, ht]
      rfl
    have e₂ : M.toX.step xs t = (⟨(XMach.act xs M.mem.toX T.toX).1,
        (M.ths.map TThread.toX).set t (XMach.act xs M.mem.toX T.toX).2.1⟩,
        (XMach.act xs M.mem.toX T.toX).2.2) := XMach.step_eq ht' rfl
    rw [e₂] at hnd
    obtain ⟨a, b, c, d⟩ := TMach.act_sim xs h T hnd
    have e₁ : M.step xs t = (⟨(TMach.act xs M.mem T).1,
        M.ths.set t (TMach.act xs M.mem T).2.1⟩, (TMach.act xs M.mem T).2.2) := by
      unfold TMach.step
      rw [ht]
    rw [e₁, e₂]
    refine ⟨?_, c, d⟩
    show (⟨(TMach.act xs M.mem T).1.toX,
      (M.ths.set t (TMach.act xs M.mem T).2.1).map TThread.toX⟩ : XMach S) = _
    rw [List.map_set, a, b]

variable {xs : XSys S}

/-- **The program on the ordered memory runs as the program does.** -/
theorem TMach.trace_sim {M : TMach S} (h : M.mem.Ok) (hL : M.toX.Live xs)
    (hnd : (M.toX.mem.agents.map Prod.fst).Nodup) (σ : Nat → Nat) :
    ∀ i, (M.trace xs σ i).1.toX = (M.toX.trace xs σ i).1 ∧
      (M.trace xs σ i).2 = (M.toX.trace xs σ i).2 ∧ (M.trace xs σ i).1.mem.Ok := by
  have live := XMach.trace_live (xs := xs) σ hL
  have nd : ∀ i, ((M.toX.trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact XMach.step_nodup (live i) ih (σ i)
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl, h⟩
  | succ i ih =>
    obtain ⟨a, b, c⟩ := ih
    have hn : (((M.trace xs σ i).1.toX.step xs (σ i)).1.mem.agents.map Prod.fst).Nodup := by
      rw [a]
      exact nd (i + 1)
    obtain ⟨a', b', c'⟩ := TMach.step_sim xs c (σ i) hn
    refine ⟨?_, ?_, c'⟩
    · show ((M.trace xs σ i).1.step xs (σ i)).1.toX = ((M.toX.trace xs σ i).1.step xs (σ i)).1
      rw [a', a]
    · show (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2 =
        (M.toX.trace xs σ i).2 + ((M.toX.trace xs σ i).1.step xs (σ i)).2
      rw [b', b, a]

/-- The run from a net: the program on the ordered memory stands for the
program on lists at every action. -/
theorem TMach.init_sim {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((TMach.init X nt).trace xs σ i).1.toX = ((XMach.init X nt).trace xs σ i).1 ∧
      ((TMach.init X nt).trace xs σ i).2 = ((XMach.init X nt).trace xs σ i).2 ∧
      ((TMach.init X nt).trace xs σ i).1.mem.Ok := by
  have e := TMach.init_toX hnd nt
  have hL : (TMach.init X nt).toX.Live xs := by
    rw [e]
    exact XMach.init_live hX hnt
  have hn : ((TMach.init X nt).toX.mem.agents.map Prod.fst).Nodup := by
    rw [e]
    exact hnd
  have k := TMach.trace_sim (TMem.ofX_toX hnd).1 hL hn σ i
  rw [e] at k
  exact k

/-- **Under a fair schedule the program on the ordered memory comes to
rest with the normal form.** -/
theorem TMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((TMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((TMach.init X nt).trace xs σ i).2 = n ∧
      ((TMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  obtain ⟨i₀, h⟩ := XMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨a, b, -⟩ := TMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((TMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- **The bound on the length of a fair run holds on the ordered
memory.** -/
theorem TMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((n + 1) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((TMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((TMach.init X nt).trace xs σ i).2 = n ∧
      ((TMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  intro i hi
  obtain ⟨a, b, -⟩ := TMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := XMach.fair_bound hX hnd hnt hb hs hn σ hfair i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((TMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- **What an action costs on the ordered memory**: one for the action,
one for each operation on a map, one for each cell of a list of neighbours
it reads, one for each cell of a segment it writes.  An idle thread finds
the largest key of its map, reads the entry, erases it and looks the agent
up.  Taking the agents afresh costs one.  A thread at rest costs
nothing. -/
def TMach.cost (xs : XSys S) (H : TMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo.maxKey? with
    | none => 0
    | some _ => 5
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c)
    else 2 + findCells p (H.nb c)
  | .ready a _ α _ => 2 + if H.sym a = some α then 2 else 0
  | .half a b α β =>
    2 + if H.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 2 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 2
      else 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- The same cost, told from the lists of the program. -/
def XMach.tcost (xs : XSys S) (X : XNet S) (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | _ :: _ => 5
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then
      2 + if (assoc c.1 X.agents).isSome then 0 else 1 + findCells p (nbOf X.wires c)
    else 2 + findCells p (nbOf X.wires c)
  | .ready a _ α _ => 2 + if assoc a X.agents = some α then 2 else 0
  | .half a b α β =>
    2 + if assoc b X.agents = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 2 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 2
      else 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- The cost on the ordered memory is the cost told from the lists. -/
theorem TMach.cost_shadow (xs : XSys S) {H : TMem S} (h : H.Ok) (T : TThread S) :
    TMach.cost xs H T = XMach.tcost xs H.toX T.toX := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold TMach.cost XMach.tcost TThread.toX
    dsimp only
    cases hmax : todo.maxKey? with
    | none => rw [treeList_none todo hmax]
    | some s =>
      obtain ⟨e, -, hl⟩ := treeList_max todo hmax
      rw [hl]
  | look a α => rfl
  | seek a α p c =>
    show (if c.2 = 0 then 2 + (if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c))
      else 2 + findCells p (H.nb c)) = _
    rw [h.sym c.1, h.nbrs c]
    rfl
  | ready a b α β =>
    show (2 + if H.sym a = some α then 2 else 0) = _
    rw [h.sym a]
    rfl
  | half a b α β =>
    unfold TMach.cost XMach.tcost TThread.toX
    dsimp only
    rw [h.sym b]
  | write as ls =>
    cases as with
    | cons e as => rfl
    | nil =>
      cases ls with
      | cons e ls => rfl
      | nil => rfl

/-- **On the ordered memory every action costs a constant**: the size of a
rule and six, at most, whatever the size of the memory; a rest costs
nothing. -/
theorem XMach.tcost_le {C D : Nat} (hb : xs.Bounded C D) (X : XNet S) (T : XThread S) :
    XMach.tcost xs X T ≤ (C + D + 6) * T.busy := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.zero_le _
    | cons e rest =>
      show 5 ≤ (C + D + 6) * 1
      omega
  | look a α =>
    show 3 ≤ (C + D + 6) * 1
    omega
  | seek a α p c =>
    have hf := findCells_nbOf X.wires c p
    show (if c.2 = 0 then 2 + (if (assoc c.1 X.agents).isSome then 0
        else 1 + findCells p (nbOf X.wires c))
      else 2 + findCells p (nbOf X.wires c)) ≤ (C + D + 6) * 1
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    show 2 + (if assoc a X.agents = some α then 2 else 0) ≤ (C + D + 6) * 1
    split <;> omega
  | half a b α β =>
    have eb : (⟨todo, .half a b α β⟩ : XThread S).busy = 1 := rfl
    rw [eb]
    unfold XMach.tcost
    dsimp only
    split
    · split
      · rename_i R hR
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        show 2 + (2 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length) ≤ _
        omega
      · omega
    · omega
  | write as ls =>
    cases as with
    | cons e as =>
      show 3 ≤ (C + D + 6) * 1
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        show 6 ≤ (C + D + 6) * 1
        omega
      | nil =>
        show 1 ≤ (C + D + 6) * 1
        omega

/-- What the action of thread `t` costs. -/
def TMach.stepCost (xs : XSys S) (M : TMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => TMach.cost xs M.mem T
  | none => 0

/-- **The running time on the ordered memory** of the first `i` actions of
a run. -/
def TMach.time (xs : XSys S) (σ : Nat → Nat) (M : TMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => TMach.time xs σ M i + (M.trace xs σ i).1.stepCost xs (σ i)

/-- What the action of thread `t` costs on the ordered memory, told from
the lists. -/
def XMach.stepTcost (xs : XSys S) (M : XMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => XMach.tcost xs M.mem T
  | none => 0

/-- The time on the ordered memory, told from the lists. -/
def XMach.ttime (xs : XSys S) (σ : Nat → Nat) (M : XMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => XMach.ttime xs σ M i + (M.trace xs σ i).1.stepTcost xs (σ i)

theorem TMach.stepCost_shadow (xs : XSys S) {M : TMach S} (h : M.mem.Ok) (t : Nat) :
    M.stepCost xs t = M.toX.stepTcost xs t := by
  have hm : M.toX.ths[t]? = (M.ths[t]?).map TThread.toX := by
    show (M.ths.map TThread.toX)[t]? = _
    rw [List.getElem?_map]
  unfold TMach.stepCost XMach.stepTcost
  rw [hm]
  cases M.ths[t]? with
  | none => rfl
  | some T => exact TMach.cost_shadow xs h T

/-- **The time on the ordered memory can be computed on lists**, with no
state but that of the program on lists. -/
theorem TMach.time_eq {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (TMach.init X nt).time xs σ i = (XMach.init X nt).ttime xs σ i
  | 0 => rfl
  | i + 1 => by
    obtain ⟨a, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    have hs := TMach.stepCost_shadow xs ok (σ i)
    rw [a] at hs
    show (TMach.init X nt).time xs σ i + ((TMach.init X nt).trace xs σ i).1.stepCost xs (σ i) =
      (XMach.init X nt).ttime xs σ i + ((XMach.init X nt).trace xs σ i).1.stepTcost xs (σ i)
    rw [hs, TMach.time_eq hX hnd hnt σ i]

theorem XMach.ttime_le_work {C D : Nat} (hb : xs.Bounded C D) (σ : Nat → Nat) (M : XMach S) :
    ∀ i, M.ttime xs σ i ≤ (C + D + 6) * M.work xs σ i
  | 0 => Nat.zero_le _
  | i + 1 => by
    have ih := XMach.ttime_le_work hb σ M i
    have hs : (M.trace xs σ i).1.stepTcost xs (σ i) ≤
        (C + D + 6) * (M.trace xs σ i).1.stepTally XThread.busy (σ i) := by
      unfold XMach.stepTcost XMach.stepTally
      cases (M.trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.zero_le _
      | some T => exact XMach.tcost_le hb _ T
    show M.ttime xs σ i + (M.trace xs σ i).1.stepTcost xs (σ i) ≤
      (C + D + 6) * (M.work xs σ i + (M.trace xs σ i).1.stepTally XThread.busy (σ i))
    rw [Nat.mul_add]
    omega

/-- **The time on the ordered memory is the work, up to a constant.**  On
every run from a well-formed net in which no agent is listed twice,
whatever the schedule, the time is at most

    (C + D + 6)

for each action that is not a rest, and nothing else: no list is read to
take the agents afresh, no dead cell is dropped, nothing is packed. -/
theorem TMach.time_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) (σ : Nat → Nat) (i : Nat) :
    (TMach.init X nt).time xs σ i ≤ (C + D + 6) * (XMach.init X nt).work xs σ i := by
  rw [TMach.time_eq hX hnd hnt σ i]
  exact XMach.ttime_le_work hb σ _ i

/-- **A bound on the running time on the ordered memory, whatever the
schedule**: the bound on the actions that are not rests, times
`C + D + 6`. -/
theorem TMach.time_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    (TMach.init X nt).time xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) * (C + D + 6) := by
  have h₁ := TMach.time_le_work (xs := xs) hX hnd hnt hb σ i
  have h₂ := Nat.mul_le_mul_left (C + D + 6) (XMach.work_le hX hnd hnt hb hs hn σ i)
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  omega

/-- Once the program is at rest the time on the ordered memory stays what
it is. -/
theorem XMach.ttime_rest {M : XMach S} (σ : Nat → Nat) {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) : ∀ d, M.ttime xs σ (B + d) = M.ttime xs σ B
  | 0 => rfl
  | d + 1 => by
    have hr := XMach.resting_trace (xs := xs) σ h d
    have z : (M.trace xs σ (B + d)).1.stepTcost xs (σ (B + d)) = 0 := by
      unfold XMach.stepTcost
      split
      · rename_i T hT
        rw [XThread.eq_rest (List.all_eq_true.1 hr T (List.mem_of_getElem? hT))]
        rfl
      · rfl
    show M.ttime xs σ (B + d) + (M.trace xs σ (B + d)).1.stepTcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact XMach.ttime_rest σ h d

/-- **The memory holds one cell for each agent**, at every action of every
run. -/
theorem TMach.cells_size {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((TMach.init X nt).trace xs σ i).1.mem.cells.size =
      ((XMach.init X nt).trace xs σ i).1.mem.agents.length := by
  obtain ⟨a, -, -⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
  rw [← a]
  exact (treeList_length _).symm

/-- An action leaves a thread with a map no larger than the one it had, or
with the map of the memory. -/
theorem TMach.act_todo (xs : XSys S) (H : TMem S) (T : TThread S) :
    (TMach.act xs H T).2.1.todo.size ≤ T.todo.size ∨ (TMach.act xs H T).2.1.todo = H.cells := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold TMach.act
    dsimp only
    split
    · exact .inl (Nat.le_refl _)
    · split
      · split <;> exact .inl Std.TreeMap.size_erase_le
      · exact .inl (Nat.le_refl _)
  | look a α =>
    unfold TMach.act
    dsimp only
    split <;> exact .inl (Nat.le_refl _)
  | seek a α p c =>
    unfold TMach.act
    dsimp only
    split
    · split <;> exact .inl (Nat.le_refl _)
    · split <;> exact .inl (Nat.le_refl _)
  | ready a b α β =>
    unfold TMach.act
    dsimp only
    split <;> exact .inl (Nat.le_refl _)
  | half a b α β =>
    unfold TMach.act
    dsimp only
    split <;> exact .inl (Nat.le_refl _)
  | write as ls =>
    cases as with
    | cons e as => exact .inl (Nat.le_refl _)
    | nil =>
      cases ls with
      | cons e ls => exact .inl (Nat.le_refl _)
      | nil => exact .inr rfl

/-- **No thread holds more than the memory can.**  Under the hypotheses of
`IMach.time_bound`, at every action of every run the map of each thread
has at most `X.agents.length + C * n` entries. -/
theorem TMach.todo_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, ∀ T, T ∈ ((TMach.init X nt).trace xs σ i).1.ths →
      T.todo.size ≤ X.agents.length + C * n := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero =>
    intro T hT
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
    show (treeOf (X.agents.drop t ++ X.agents.take t)).size ≤ _
    rw [← treeList_length, (treeOf_spec _).2, List.length_append, List.length_drop,
      List.length_take]
    omega
  | succ i ih =>
    intro T hT
    have hcs := TMach.cells_size (xs := xs) hX hnd hnt σ i
    obtain ⟨hA, -, -⟩ := hΦ i
    cases ht : ((TMach.init X nt).trace xs σ i).1.ths[σ i]? with
    | none =>
      have e : ((TMach.init X nt).trace xs σ i).1.step xs (σ i) =
          (((TMach.init X nt).trace xs σ i).1, 0) := by
        unfold TMach.step
        rw [ht]
      have hT' : T ∈ (((TMach.init X nt).trace xs σ i).1.step xs (σ i)).1.ths := hT
      rw [e] at hT'
      exact ih T hT'
    | some U =>
      have e : ((TMach.init X nt).trace xs σ i).1.step xs (σ i) =
          (⟨(TMach.act xs ((TMach.init X nt).trace xs σ i).1.mem U).1,
            ((TMach.init X nt).trace xs σ i).1.ths.set (σ i)
              (TMach.act xs ((TMach.init X nt).trace xs σ i).1.mem U).2.1⟩,
            (TMach.act xs ((TMach.init X nt).trace xs σ i).1.mem U).2.2) := by
        unfold TMach.step
        rw [ht]
      have hT' : T ∈ (((TMach.init X nt).trace xs σ i).1.step xs (σ i)).1.ths := hT
      rw [e] at hT'
      rcases List.mem_or_eq_of_mem_set hT' with hold | rfl
      · exact ih T hold
      · rcases TMach.act_todo xs ((TMach.init X nt).trace xs σ i).1.mem U with hle | heq
        · exact Nat.le_trans hle (ih U (List.mem_of_getElem? ht))
        · rw [heq, hcs]
          exact hA

end Ordered

/-! ### The ordered memory, the depth of the map charged

`TMach.time` counts an operation on a map as one.  On an ordered map an
operation follows a path from the root, and the path grows as the
logarithm of the size.  Here an operation on an ordered map of `n` entries
is charged `lg n`, one more than the number of binary digits of `n`, and
the bound on the time is redone with that charge.  An operation on a hash
map still counts one. -/

/-- The binary digits of `n`, computed with `f` halvings at most. -/
def lgAux : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else lgAux f (n / 2) + 1

/-- **What an operation on an ordered map of `n` entries is charged**: one
for each binary digit of `n`, and one. -/
def lg (n : Nat) : Nat := lgAux n n + 1

theorem lgAux_mono : ∀ (f g a b : Nat), a ≤ b → a ≤ f → b ≤ g → lgAux f a ≤ lgAux g b
  | 0, _, _, _, _, _, _ => Nat.zero_le _
  | f + 1, g, a, b, hab, haf, hbg => by
    by_cases ha : a = 0
    · show (if a = 0 then 0 else lgAux f (a / 2) + 1) ≤ _
      rw [ite_pos' ha]
      exact Nat.zero_le _
    · have hb : b ≠ 0 := by omega
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      show (if a = 0 then 0 else lgAux f (a / 2) + 1) ≤
        (if b = 0 then 0 else lgAux g' (b / 2) + 1)
      rw [ite_neg' ha, ite_neg' hb]
      have ih := lgAux_mono f g' (a / 2) (b / 2) (Nat.div_le_div_right hab) (by omega)
        (by omega)
      omega

/-- A larger map is charged no less. -/
theorem lg_mono {a b : Nat} (h : a ≤ b) : lg a ≤ lg b :=
  Nat.succ_le_succ (lgAux_mono a b a b h (Nat.le_refl a) (Nat.le_refl b))

theorem lg_pos (n : Nat) : 1 ≤ lg n := Nat.succ_le_succ (Nat.zero_le _)

theorem lgAux_le : ∀ (f n k : Nat), n < 2 ^ k → lgAux f n ≤ k
  | 0, _, _, _ => Nat.zero_le _
  | f + 1, n, k, h => by
    by_cases hn : n = 0
    · show (if n = 0 then 0 else lgAux f (n / 2) + 1) ≤ k
      rw [ite_pos' hn]
      exact Nat.zero_le _
    · show (if n = 0 then 0 else lgAux f (n / 2) + 1) ≤ k
      rw [ite_neg' hn]
      cases k with
      | zero =>
        have : n < 1 := h
        omega
      | succ k =>
        have e : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
        have ih := lgAux_le f (n / 2) k (by omega)
        omega

/-- **The charge is no more than the logarithm and two**: a map of fewer
than `2 ^ k` entries is charged `k + 1` at most. -/
theorem lg_le {n k : Nat} (h : n < 2 ^ k) : lg n ≤ k + 1 :=
  Nat.succ_le_succ (lgAux_le n n k h)

theorem lt_pow_lgAux : ∀ (f n : Nat), n ≤ f → n < 2 ^ lgAux f n
  | 0, n, h => by
    have : n = 0 := by omega
    subst this
    exact Nat.one_pos
  | f + 1, n, h => by
    by_cases hn : n = 0
    · subst hn
      exact Nat.two_pow_pos _
    · show n < 2 ^ (if n = 0 then 0 else lgAux f (n / 2) + 1)
      rw [ite_neg' hn]
      have e : 2 ^ (lgAux f (n / 2) + 1) = 2 ^ lgAux f (n / 2) * 2 := Nat.pow_succ 2 _
      have ih := lt_pow_lgAux f (n / 2) (by omega)
      omega

/-- **The charge is no less than the depth of any binary tree of that many
entries, and one**: `2 ^ (lg n - 1)` exceeds `n`. -/
theorem lt_pow_lg (n : Nat) : 2 * n < 2 ^ lg n := by
  have e : 2 ^ (lgAux n n + 1) = 2 ^ lgAux n n * 2 := Nat.pow_succ 2 _
  have h := lt_pow_lgAux n n (Nat.le_refl n)
  show 2 * n < 2 ^ (lgAux n n + 1)
  omega

section TreeLog

variable [DecidableEq S] {xs : XSys S}

/-- **What an action costs on the ordered memory when the ordered map is
charged for its depth**: as `TMach.cost`, but each operation on an ordered
map is charged `lg` of the size of the map, where an operation on a hash
map is charged one.  An idle thread makes three operations on its own
map; taking an agent out or writing one makes one on the map of the
memory. -/
def TMach.lgcost (xs : XSys S) (H : TMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo.maxKey? with
    | none => 0
    | some _ => 2 + 3 * lg T.todo.size
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c)
    else 2 + findCells p (H.nb c)
  | .ready a _ α _ => 2 + if H.sym a = some α then 1 + lg H.cells.size else 0
  | .half a b α β =>
    2 + if H.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          1 + lg H.cells.size + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length
        | none => 1 + lg H.cells.size
      else 1 + lg H.cells.size
  | .write (_ :: _) _ => 2 + lg H.cells.size
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- The same cost, told from the lists of the program: the maps have as
many entries as the lists they stand for. -/
def XMach.lgcost (xs : XSys S) (X : XNet S) (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | _ :: _ => 2 + 3 * lg T.todo.length
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then
      2 + if (assoc c.1 X.agents).isSome then 0 else 1 + findCells p (nbOf X.wires c)
    else 2 + findCells p (nbOf X.wires c)
  | .ready a _ α _ => 2 + if assoc a X.agents = some α then 1 + lg X.agents.length else 0
  | .half a b α β =>
    2 + if assoc b X.agents = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          1 + lg X.agents.length + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length
        | none => 1 + lg X.agents.length
      else 1 + lg X.agents.length
  | .write (_ :: _) _ => 2 + lg X.agents.length
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

theorem TMach.lgcost_shadow (xs : XSys S) {H : TMem S} (h : H.Ok) (T : TThread S) :
    TMach.lgcost xs H T = XMach.lgcost xs H.toX T.toX := by
  obtain ⟨todo, s⟩ := T
  have hsz : H.cells.size = H.toX.agents.length := (treeList_length H.cells).symm
  cases s with
  | idle =>
    unfold TMach.lgcost XMach.lgcost TThread.toX
    dsimp only
    cases hmax : todo.maxKey? with
    | none => rw [treeList_none todo hmax]
    | some s =>
      obtain ⟨e, -, hl⟩ := treeList_max todo hmax
      rw [← treeList_length todo, hl]
  | look a α => rfl
  | seek a α p c =>
    show (if c.2 = 0 then 2 + (if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c))
      else 2 + findCells p (H.nb c)) = _
    rw [h.sym c.1, h.nbrs c]
    rfl
  | ready a b α β =>
    show (2 + if H.sym a = some α then 1 + lg H.cells.size else 0) = _
    rw [h.sym a, hsz]
    rfl
  | half a b α β =>
    unfold TMach.lgcost XMach.lgcost TThread.toX
    dsimp only
    rw [h.sym b, hsz]
  | write as ls =>
    cases as with
    | cons e as =>
      show 2 + lg H.cells.size = 2 + lg H.toX.agents.length
      rw [hsz]
    | nil =>
      cases ls with
      | cons e ls => rfl
      | nil => rfl

/-- **With the depth of the map charged, an action costs the size of a
rule, three, and three times the charge for the largest map.** -/
theorem XMach.lgcost_le {C D : Nat} (hb : xs.Bounded C D) (X : XNet S) (T : XThread S)
    {m : Nat} (hx : X.agents.length ≤ m) (ht : T.todo.length ≤ m) :
    XMach.lgcost xs X T ≤ (C + D + 3 + 3 * lg m) * T.busy := by
  have h₁ := lg_mono hx
  have h₂ := lg_mono ht
  have h₃ := lg_pos m
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.zero_le _
    | cons e rest =>
      show 2 + 3 * lg (e :: rest).length ≤ (C + D + 3 + 3 * lg m) * 1
      have : lg (e :: rest).length ≤ lg m := h₂
      omega
  | look a α =>
    show 3 ≤ (C + D + 3 + 3 * lg m) * 1
    omega
  | seek a α p c =>
    have hf := findCells_nbOf X.wires c p
    show (if c.2 = 0 then 2 + (if (assoc c.1 X.agents).isSome then 0
        else 1 + findCells p (nbOf X.wires c))
      else 2 + findCells p (nbOf X.wires c)) ≤ (C + D + 3 + 3 * lg m) * 1
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    show 2 + (if assoc a X.agents = some α then 1 + lg X.agents.length else 0) ≤
      (C + D + 3 + 3 * lg m) * 1
    split <;> omega
  | half a b α β =>
    have eb : (⟨todo, .half a b α β⟩ : XThread S).busy = 1 := rfl
    rw [eb]
    unfold XMach.lgcost
    dsimp only
    split
    · split
      · rename_i R hR
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        show 2 + (1 + lg X.agents.length + (R.newAgents a b).length +
          (R.newLinks xs.sys.ar a b α β).length) ≤ _
        omega
      · show 2 + (1 + lg X.agents.length) ≤ (C + D + 3 + 3 * lg m) * 1
        omega
    · show 2 + (1 + lg X.agents.length) ≤ (C + D + 3 + 3 * lg m) * 1
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      show 2 + lg X.agents.length ≤ (C + D + 3 + 3 * lg m) * 1
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        show 6 ≤ (C + D + 3 + 3 * lg m) * 1
        omega
      | nil =>
        show 1 ≤ (C + D + 3 + 3 * lg m) * 1
        omega

/-- What the action of thread `t` costs, the depth of the map charged. -/
def TMach.stepLgcost (xs : XSys S) (M : TMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => TMach.lgcost xs M.mem T
  | none => 0

/-- **The running time on the ordered memory, the depth of the map
charged.** -/
def TMach.lgtime (xs : XSys S) (σ : Nat → Nat) (M : TMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => TMach.lgtime xs σ M i + (M.trace xs σ i).1.stepLgcost xs (σ i)

/-- The same, told from the lists. -/
def XMach.stepLgcost (xs : XSys S) (M : XMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => XMach.lgcost xs M.mem T
  | none => 0

/-- The same, told from the lists. -/
def XMach.lgtime (xs : XSys S) (σ : Nat → Nat) (M : XMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => XMach.lgtime xs σ M i + (M.trace xs σ i).1.stepLgcost xs (σ i)

theorem TMach.stepLgcost_shadow (xs : XSys S) {M : TMach S} (h : M.mem.Ok) (t : Nat) :
    M.stepLgcost xs t = M.toX.stepLgcost xs t := by
  have hm : M.toX.ths[t]? = (M.ths[t]?).map TThread.toX := by
    show (M.ths.map TThread.toX)[t]? = _
    rw [List.getElem?_map]
  unfold TMach.stepLgcost XMach.stepLgcost
  rw [hm]
  cases M.ths[t]? with
  | none => rfl
  | some T => exact TMach.lgcost_shadow xs h T

/-- The time with the depth charged can be computed on lists. -/
theorem TMach.lgtime_eq {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (TMach.init X nt).lgtime xs σ i = (XMach.init X nt).lgtime xs σ i
  | 0 => rfl
  | i + 1 => by
    obtain ⟨a, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    have hs := TMach.stepLgcost_shadow xs ok (σ i)
    rw [a] at hs
    show (TMach.init X nt).lgtime xs σ i +
        ((TMach.init X nt).trace xs σ i).1.stepLgcost xs (σ i) =
      (XMach.init X nt).lgtime xs σ i + ((XMach.init X nt).trace xs σ i).1.stepLgcost xs (σ i)
    rw [hs, TMach.lgtime_eq hX hnd hnt σ i]

/-- **The time on the ordered memory with the depth of the map charged.**
Under the hypotheses of `IMach.time_bound`, on every run the time is at
most

    C + D + 3 + 3 * lg (X.agents.length + C * n)

for each action that is not a rest: the size of a rule, a constant, and
three operations on a map that never has more entries than the memory can
hold. -/
theorem TMach.lgtime_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (TMach.init X nt).lgtime xs σ i ≤
      (C + D + 3 + 3 * lg (X.agents.length + C * n)) * (XMach.init X nt).work xs σ i := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have htodo := TMach.todo_le (xs := xs) hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨a, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨hA, -, -⟩ := hΦ i
    have hm : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
        (((TMach.init X nt).trace xs σ i).1.ths[σ i]?).map TThread.toX := by
      rw [← a]
      show (((TMach.init X nt).trace xs σ i).1.ths.map TThread.toX)[σ i]? = _
      rw [List.getElem?_map]
    have emem : ((TMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    have hstep : ((TMach.init X nt).trace xs σ i).1.stepLgcost xs (σ i) ≤
        (C + D + 3 + 3 * lg (X.agents.length + C * n)) *
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i) := by
      unfold TMach.stepLgcost XMach.stepTally
      rw [hm]
      cases hT : ((TMach.init X nt).trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.zero_le _
      | some T =>
        have hsz := htodo i T (List.mem_of_getElem? hT)
        show TMach.lgcost xs ((TMach.init X nt).trace xs σ i).1.mem T ≤
          (C + D + 3 + 3 * lg (X.agents.length + C * n)) * T.toX.busy
        rw [TMach.lgcost_shadow xs ok T, emem]
        refine XMach.lgcost_le hb _ _ hA ?_
        show (treeList T.todo).length ≤ _
        rw [treeList_length]
        exact hsz
    show (TMach.init X nt).lgtime xs σ i +
        ((TMach.init X nt).trace xs σ i).1.stepLgcost xs (σ i) ≤
      (C + D + 3 + 3 * lg (X.agents.length + C * n)) *
        ((XMach.init X nt).work xs σ i +
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i))
    rw [Nat.mul_add]
    omega

/-- **A bound on the running time on the ordered memory, the depth of the
map charged, whatever the schedule**: the bound on the actions that are
not rests, times `C + D + 3 + 3 * lg (X.agents.length + C * n)`.  On lists
the second factor is the size of the memory; here it is its logarithm. -/
theorem TMach.lgtime_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    (TMach.init X nt).lgtime xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) *
        (C + D + 3 + 3 * lg (X.agents.length + C * n)) := by
  have h₁ := TMach.lgtime_le_work (xs := xs) hX hnd hnt hb hs hn σ i
  have h₂ := Nat.mul_le_mul_left (C + D + 3 + 3 * lg (X.agents.length + C * n))
    (XMach.work_le hX hnd hnt hb hs hn σ i)
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  omega

/-- Once the program is at rest this time stays what it is. -/
theorem XMach.lgtime_rest {M : XMach S} (σ : Nat → Nat) {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) : ∀ d, M.lgtime xs σ (B + d) = M.lgtime xs σ B
  | 0 => rfl
  | d + 1 => by
    have hr := XMach.resting_trace (xs := xs) σ h d
    have z : (M.trace xs σ (B + d)).1.stepLgcost xs (σ (B + d)) = 0 := by
      unfold XMach.stepLgcost
      split
      · rename_i T hT
        rw [XThread.eq_rest (List.all_eq_true.1 hr T (List.mem_of_getElem? hT))]
        rfl
      · rfl
    show M.lgtime xs σ (B + d) + (M.trace xs σ (B + d)).1.stepLgcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact XMach.lgtime_rest σ h d

/-- Charging the depth of the map never lowers the cost of an action. -/
theorem XMach.tcost_le_lgcost (xs : XSys S) (X : XNet S) (T : XThread S) :
    XMach.tcost xs X T ≤ XMach.lgcost xs X T := by
  have h₁ := lg_pos X.agents.length
  have h₂ := lg_pos T.todo.length
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.le_refl _
    | cons e rest =>
      show 5 ≤ 2 + 3 * lg (e :: rest).length
      have : 1 ≤ lg (e :: rest).length := h₂
      omega
  | look a α => exact Nat.le_refl _
  | seek a α p c => exact Nat.le_refl _
  | ready a b α β =>
    show 2 + (if assoc a X.agents = some α then 2 else 0) ≤
      2 + (if assoc a X.agents = some α then 1 + lg X.agents.length else 0)
    split <;> omega
  | half a b α β =>
    unfold XMach.tcost XMach.lgcost
    dsimp only
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · rw [ite_pos' hc, ite_pos' hc]
      cases xs.rule α β with
      | none =>
        show 2 + 2 ≤ 2 + (1 + lg X.agents.length)
        omega
      | some R =>
        show 2 + (2 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length) ≤
          2 + (1 + lg X.agents.length + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length)
        omega
    · rw [ite_neg' hc, ite_neg' hc]
      show 2 + 2 ≤ 2 + (1 + lg X.agents.length)
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      show 3 ≤ 2 + lg X.agents.length
      omega
    | nil =>
      cases ls with
      | cons e ls => exact Nat.le_refl _
      | nil => exact Nat.le_refl _

/-- **Charging the depth of the map multiplies the cost of an action by
the charge for the largest map at most.** -/
theorem XMach.lgcost_le_tcost (xs : XSys S) (X : XNet S) (T : XThread S) {m : Nat}
    (hx : X.agents.length ≤ m) (ht : T.todo.length ≤ m) :
    XMach.lgcost xs X T ≤ lg m * XMach.tcost xs X T := by
  have h₁ := lg_mono hx
  have h₂ := lg_mono ht
  have h₃ := lg_pos m
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.zero_le _
    | cons e rest =>
      show 2 + 3 * lg (e :: rest).length ≤ lg m * 5
      have : lg (e :: rest).length ≤ lg m := h₂
      omega
  | look a α =>
    show 3 ≤ lg m * 3
    omega
  | seek a α p c => exact Nat.le_mul_of_pos_left _ h₃
  | ready a b α β =>
    show 2 + (if assoc a X.agents = some α then 1 + lg X.agents.length else 0) ≤
      lg m * (2 + (if assoc a X.agents = some α then 2 else 0))
    split
    · show 2 + (1 + lg X.agents.length) ≤ lg m * 4
      omega
    · show 2 + 0 ≤ lg m * 2
      omega
  | half a b α β =>
    unfold XMach.tcost XMach.lgcost
    dsimp only
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · rw [ite_pos' hc, ite_pos' hc]
      cases xs.rule α β with
      | none =>
        show 2 + (1 + lg X.agents.length) ≤ lg m * 4
        omega
      | some R =>
        have e : lg m * (2 + (2 + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length)) =
            lg m * 4 + lg m * (R.newAgents a b).length +
              lg m * (R.newLinks xs.sys.ar a b α β).length := by
          rw [show 2 + (2 + (R.newAgents a b).length +
              (R.newLinks xs.sys.ar a b α β).length) =
            4 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length by omega,
            Nat.mul_add, Nat.mul_add]
        have ha := Nat.le_mul_of_pos_left (R.newAgents a b).length h₃
        have hl := Nat.le_mul_of_pos_left (R.newLinks xs.sys.ar a b α β).length h₃
        show 2 + (1 + lg X.agents.length + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length) ≤
          lg m * (2 + (2 + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length))
        rw [e]
        omega
    · rw [ite_neg' hc, ite_neg' hc]
      show 2 + (1 + lg X.agents.length) ≤ lg m * 4
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      show 2 + lg X.agents.length ≤ lg m * 3
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        show 6 ≤ lg m * 6
        omega
      | nil =>
        show 1 ≤ lg m * 1
        omega

/-- On lists: charging the depth never lowers the time. -/
theorem XMach.ttime_le_lgtime (xs : XSys S) (σ : Nat → Nat) (M : XMach S) :
    ∀ i, M.ttime xs σ i ≤ M.lgtime xs σ i
  | 0 => Nat.le_refl _
  | i + 1 => by
    have ih := XMach.ttime_le_lgtime xs σ M i
    have hstep : (M.trace xs σ i).1.stepTcost xs (σ i) ≤
        (M.trace xs σ i).1.stepLgcost xs (σ i) := by
      unfold XMach.stepTcost XMach.stepLgcost
      cases (M.trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.le_refl _
      | some T => exact XMach.tcost_le_lgcost xs _ T
    show M.ttime xs σ i + (M.trace xs σ i).1.stepTcost xs (σ i) ≤
      M.lgtime xs σ i + (M.trace xs σ i).1.stepLgcost xs (σ i)
    omega

/-- **Charging the depth of the map never lowers the time**, on any run. -/
theorem TMach.time_le_lgtime {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    (TMach.init X nt).time xs σ i ≤ (TMach.init X nt).lgtime xs σ i := by
  rw [TMach.time_eq hX hnd hnt σ i, TMach.lgtime_eq hX hnd hnt σ i]
  exact XMach.ttime_le_lgtime xs σ _ i

/-- **Charging the depth of the map multiplies the time by the charge for
the largest map at most.**  Under the hypotheses of `IMach.time_bound`, on
every run the time with the depth charged is at most
`lg (X.agents.length + C * n)` times the time with every operation counted
one. -/
theorem TMach.lgtime_le_time {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (TMach.init X nt).lgtime xs σ i ≤
      lg (X.agents.length + C * n) * (TMach.init X nt).time xs σ i := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have htodo := TMach.todo_le (xs := xs) hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨a, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨hA, -, -⟩ := hΦ i
    have emem : ((TMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    have hstep : ((TMach.init X nt).trace xs σ i).1.stepLgcost xs (σ i) ≤
        lg (X.agents.length + C * n) *
          ((TMach.init X nt).trace xs σ i).1.stepCost xs (σ i) := by
      unfold TMach.stepLgcost TMach.stepCost
      cases hT : ((TMach.init X nt).trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.zero_le _
      | some T =>
        have hsz := htodo i T (List.mem_of_getElem? hT)
        show TMach.lgcost xs ((TMach.init X nt).trace xs σ i).1.mem T ≤
          lg (X.agents.length + C * n) *
            TMach.cost xs ((TMach.init X nt).trace xs σ i).1.mem T
        rw [TMach.lgcost_shadow xs ok T, TMach.cost_shadow xs ok T, emem]
        refine XMach.lgcost_le_tcost xs _ _ hA ?_
        show (treeList T.todo).length ≤ _
        rw [treeList_length]
        exact hsz
    show (TMach.init X nt).lgtime xs σ i +
        ((TMach.init X nt).trace xs σ i).1.stepLgcost xs (σ i) ≤
      lg (X.agents.length + C * n) *
        ((TMach.init X nt).time xs σ i +
          ((TMach.init X nt).trace xs σ i).1.stepCost xs (σ i))
    rw [Nat.mul_add]
    omega

end TreeLog

/-! ### The depth of the trees of the library

`lg` charges the depth of a perfectly balanced tree.  The ordered maps of
the program are those of the library, `Std.TreeMap`, whose trees are
balanced by weight: at a node whose sides hold two entries or more,
neither side has more than three times the other.  The library proves
that balance of every map it returns.  From it, the depth of the tree is
under three times `lg` of its size, and no binary tree is shallower than
`lg` less one.  So the time with each operation charged the depth of the
tree it works on is within a factor three of the time with `lg`
charged. -/

open Std.DTreeMap.Internal in
/-- **The depth of a tree of the library**: the nodes on the longest path
from the root. -/
def implDepth {α : Type} {β : α → Type} : Impl α β → Nat
  | .leaf => 0
  | .inner _ _ _ l r => max (implDepth l) (implDepth r) + 1

theorem pow43_step {h a s : Nat} (ih : 4 ^ h ≤ 3 ^ h * (a + 1)) (hs : 4 * (a + 1) ≤ 3 * s) :
    4 ^ (h + 1) ≤ 3 ^ (h + 1) * s :=
  calc 4 ^ (h + 1) = 4 ^ h * 4 := Nat.pow_succ 4 h
    _ ≤ 3 ^ h * (a + 1) * 4 := Nat.mul_le_mul_right 4 ih
    _ = 3 ^ h * ((a + 1) * 4) := Nat.mul_assoc _ _ _
    _ ≤ 3 ^ h * (3 * s) := Nat.mul_le_mul_left _ (by omega)
    _ = 3 ^ h * 3 * s := (Nat.mul_assoc _ _ _).symm
    _ = 3 ^ (h + 1) * s := by rw [Nat.pow_succ 3 h]

open Std.DTreeMap.Internal in
/-- **A tree of the library is not deep.**  Its balance keeps each side of
a node under three quarters of the node, so that the depth `d` of a tree
of `n` entries has `(4 / 3) ^ d ≤ n + 1`. -/
theorem implDepth_pow {α : Type} {β : α → Type} {t : Impl α β} (h : t.Balanced) :
    4 ^ implDepth t ≤ 3 ^ implDepth t * (t.size + 1) := by
  induction h with
  | leaf => exact Nat.le_refl _
  | @inner sz k v l r hl hr hb hsz ihl ihr =>
    have hb' : l.size + r.size ≤ 1 ∨ l.size ≤ 3 * r.size ∧ r.size ≤ 3 * l.size := hb
    show 4 ^ (max (implDepth l) (implDepth r) + 1) ≤
      3 ^ (max (implDepth l) (implDepth r) + 1) * (sz + 1)
    by_cases c : implDepth r ≤ implDepth l
    · rw [Nat.max_eq_left c]
      exact pow43_step ihl (by omega)
    · rw [Nat.max_eq_right (by omega)]
      exact pow43_step ihr (by omega)

open Std.DTreeMap.Internal in
/-- No binary tree is shallower than the digits of its size. -/
theorem implDepth_ge {α : Type} {β : α → Type} {t : Impl α β} (h : t.Balanced) :
    t.size + 1 ≤ 2 ^ implDepth t := by
  induction h with
  | leaf => exact Nat.le_refl _
  | @inner sz k v l r hl hr hb hsz ihl ihr =>
    have p₁ : 2 ^ implDepth l ≤ 2 ^ max (implDepth l) (implDepth r) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)
    have p₂ : 2 ^ implDepth r ≤ 2 ^ max (implDepth l) (implDepth r) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
    have e : 2 ^ (max (implDepth l) (implDepth r) + 1) =
        2 ^ max (implDepth l) (implDepth r) * 2 := Nat.pow_succ 2 _
    show sz + 1 ≤ 2 ^ (max (implDepth l) (implDepth r) + 1)
    omega

theorem pow_mix : ∀ (k r : Nat), 3 ^ (3 * k + r) * 2 ^ k ≤ 4 ^ (3 * k + r)
  | 0, r => by
    show 3 ^ (3 * 0 + r) * 1 ≤ 4 ^ (3 * 0 + r)
    rw [Nat.mul_one]
    exact Nat.pow_le_pow_left (by decide) _
  | k + 1, r => by
    have ih := pow_mix k r
    have e₃ : 3 ^ (3 * (k + 1) + r) = 3 ^ (3 * k + r) * 3 ^ 3 := by
      rw [show 3 * (k + 1) + r = (3 * k + r) + 3 by omega]
      exact Nat.pow_add 3 _ 3
    have e₄ : 4 ^ (3 * (k + 1) + r) = 4 ^ (3 * k + r) * 4 ^ 3 := by
      rw [show 3 * (k + 1) + r = (3 * k + r) + 3 by omega]
      exact Nat.pow_add 4 _ 3
    have e₂ : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    rw [e₃, e₄, e₂, Nat.mul_mul_mul_comm]
    exact Nat.mul_le_mul ih (by decide)

/-- **From the balance to the charge**: a depth `d` with
`(4 / 3) ^ d ≤ n + 1` is under three times `lg n`. -/
theorem depth_lt_of_pow {h n : Nat} (hp : 4 ^ h ≤ 3 ^ h * (n + 1)) : h < 3 * lg n := by
  have hm : 3 ^ h * 2 ^ (h / 3) ≤ 4 ^ h := by
    have := pow_mix (h / 3) (h % 3)
    rwa [Nat.div_add_mod] at this
  have h₂ : 2 ^ (h / 3) ≤ n + 1 :=
    Nat.le_of_mul_le_mul_left (Nat.le_trans hm hp) (Nat.pow_pos (by decide))
  have hn := lt_pow_lgAux n n (Nat.le_refl n)
  have hk : h / 3 ≤ lgAux n n := by
    by_cases c : h / 3 ≤ lgAux n n
    · exact c
    · have := Nat.pow_lt_pow_right (a := 2) (by decide) (Nat.lt_of_not_le c)
      omega
  show h < 3 * (lgAux n n + 1)
  omega

/-- **The depth of the tree an ordered map is kept in.** -/
def tdepth {V : Type} (t : Std.TreeMap Nat V) : Nat := implDepth t.inner.inner

/-- **The tree of an ordered map of the library is under three times as
deep as the charge**: `tdepth t < 3 * lg t.size`, whatever the operations
that made the map. -/
theorem tdepth_lt {V : Type} (t : Std.TreeMap Nat V) : tdepth t < 3 * lg t.size :=
  depth_lt_of_pow (implDepth_pow t.inner.wf.balanced)

/-- **And no shallower than the charge less one.** -/
theorem lg_le_tdepth {V : Type} (t : Std.TreeMap Nat V) : lg t.size ≤ tdepth t + 1 :=
  lg_le (implDepth_ge t.inner.wf.balanced)

section TreeDepth

variable [DecidableEq S] {xs : XSys S}

/-- **What an action costs on the ordered memory when an operation on an
ordered map is charged the depth of its tree**, and one: as
`TMach.lgcost`, with the depth of the tree the map is kept in where that
has `lg` of its size. -/
def TMach.dcost (xs : XSys S) (H : TMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo.maxKey? with
    | none => 0
    | some _ => 2 + 3 * (tdepth T.todo + 1)
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c)
    else 2 + findCells p (H.nb c)
  | .ready a _ α _ => 2 + if H.sym a = some α then 1 + (tdepth H.cells + 1) else 0
  | .half a b α β =>
    2 + if H.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          1 + (tdepth H.cells + 1) + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length
        | none => 1 + (tdepth H.cells + 1)
      else 1 + (tdepth H.cells + 1)
  | .write (_ :: _) _ => 2 + (tdepth H.cells + 1)
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- The charge by the digits of the size is never more than the charge by
the depth. -/
theorem TMach.lgcost_le_dcost (xs : XSys S) (H : TMem S) (T : TThread S) :
    TMach.lgcost xs H T ≤ TMach.dcost xs H T := by
  have h₁ := lg_le_tdepth H.cells
  have h₂ := lg_le_tdepth T.todo
  obtain ⟨todo, s⟩ := T
  have h₂' : lg todo.size ≤ tdepth todo + 1 := h₂
  cases s with
  | idle =>
    unfold TMach.lgcost TMach.dcost
    dsimp only
    cases todo.maxKey? with
    | none => exact Nat.le_refl _
    | some s =>
      show 2 + 3 * lg todo.size ≤ 2 + 3 * (tdepth todo + 1)
      omega
  | look a α => exact Nat.le_refl _
  | seek a α p c => exact Nat.le_refl _
  | ready a b α β =>
    show 2 + (if H.sym a = some α then 1 + lg H.cells.size else 0) ≤
      2 + (if H.sym a = some α then 1 + (tdepth H.cells + 1) else 0)
    by_cases hc : H.sym a = some α
    · rw [ite_pos' hc, ite_pos' hc]
      omega
    · rw [ite_neg' hc, ite_neg' hc]
      exact Nat.le_refl _
  | half a b α β =>
    unfold TMach.lgcost TMach.dcost
    dsimp only
    by_cases hc : H.sym b = some β ∧ a ≠ b
    · rw [ite_pos' hc, ite_pos' hc]
      cases xs.rule α β with
      | none =>
        show 2 + (1 + lg H.cells.size) ≤ 2 + (1 + (tdepth H.cells + 1))
        omega
      | some R =>
        show 2 + (1 + lg H.cells.size + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length) ≤
          2 + (1 + (tdepth H.cells + 1) + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length)
        omega
    · rw [ite_neg' hc, ite_neg' hc]
      show 2 + (1 + lg H.cells.size) ≤ 2 + (1 + (tdepth H.cells + 1))
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      show 2 + lg H.cells.size ≤ 2 + (tdepth H.cells + 1)
      omega
    | nil =>
      cases ls with
      | cons e ls => exact Nat.le_refl _
      | nil => exact Nat.le_refl _

/-- **And the charge by the depth is at most three times the charge by the
digits of the size.** -/
theorem TMach.dcost_le_lgcost (xs : XSys S) (H : TMem S) (T : TThread S) :
    TMach.dcost xs H T ≤ 3 * TMach.lgcost xs H T := by
  have h₁ := tdepth_lt H.cells
  have h₂ := tdepth_lt T.todo
  obtain ⟨todo, s⟩ := T
  have h₂' : tdepth todo < 3 * lg todo.size := h₂
  cases s with
  | idle =>
    unfold TMach.lgcost TMach.dcost
    dsimp only
    cases todo.maxKey? with
    | none => exact Nat.zero_le _
    | some s =>
      show 2 + 3 * (tdepth todo + 1) ≤ 3 * (2 + 3 * lg todo.size)
      omega
  | look a α =>
    show 3 ≤ 3 * 3
    omega
  | seek a α p c => exact Nat.le_mul_of_pos_left _ (by decide)
  | ready a b α β =>
    show 2 + (if H.sym a = some α then 1 + (tdepth H.cells + 1) else 0) ≤
      3 * (2 + (if H.sym a = some α then 1 + lg H.cells.size else 0))
    by_cases hc : H.sym a = some α
    · rw [ite_pos' hc, ite_pos' hc]
      omega
    · rw [ite_neg' hc, ite_neg' hc]
      omega
  | half a b α β =>
    unfold TMach.lgcost TMach.dcost
    dsimp only
    by_cases hc : H.sym b = some β ∧ a ≠ b
    · rw [ite_pos' hc, ite_pos' hc]
      cases xs.rule α β with
      | none =>
        show 2 + (1 + (tdepth H.cells + 1)) ≤ 3 * (2 + (1 + lg H.cells.size))
        omega
      | some R =>
        show 2 + (1 + (tdepth H.cells + 1) + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length) ≤
          3 * (2 + (1 + lg H.cells.size + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length))
        omega
    · rw [ite_neg' hc, ite_neg' hc]
      show 2 + (1 + (tdepth H.cells + 1)) ≤ 3 * (2 + (1 + lg H.cells.size))
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      show 2 + (tdepth H.cells + 1) ≤ 3 * (2 + lg H.cells.size)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        show 6 ≤ 3 * 6
        omega
      | nil =>
        show 1 ≤ 3 * 1
        omega

/-- **With the depth of the trees charged, an action costs the size of a
rule, three, and three times the deepest tree.** -/
theorem TMach.dcost_le {C D : Nat} (hb : xs.Bounded C D) {H : TMem S} (h : H.Ok)
    (T : TThread S) {k : Nat} (hc : tdepth H.cells + 1 ≤ k) (ht : tdepth T.todo + 1 ≤ k) :
    TMach.dcost xs H T ≤ (C + D + 3 + 3 * k) * T.toX.busy := by
  obtain ⟨todo, s⟩ := T
  have ht' : tdepth todo + 1 ≤ k := ht
  cases s with
  | idle =>
    cases hmax : todo.maxKey? with
    | none =>
      have e : TMach.dcost xs H ⟨todo, .idle⟩ = 0 := by
        unfold TMach.dcost
        dsimp only
        rw [hmax]
      rw [e]
      exact Nat.zero_le _
    | some s =>
      obtain ⟨v, -, hl⟩ := treeList_max todo hmax
      have e : TMach.dcost xs H ⟨todo, .idle⟩ = 2 + 3 * (tdepth todo + 1) := by
        unfold TMach.dcost
        dsimp only
        rw [hmax]
      have eb : (TThread.toX (⟨todo, .idle⟩ : TThread S)).busy = 1 := by
        show XThread.busy ⟨treeList todo, .idle⟩ = 1
        rw [hl]
        rfl
      rw [e, eb]
      omega
  | look a α =>
    show 3 ≤ (C + D + 3 + 3 * k) * 1
    omega
  | seek a α p c =>
    have hf : findCells p (nbOf H.wires c) ≤ 2 := findCells_nbOf H.wires c p
    show (if c.2 = 0 then 2 + (if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c))
      else 2 + findCells p (H.nb c)) ≤ (C + D + 3 + 3 * k) * 1
    rw [h.nbrs c]
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    show 2 + (if H.sym a = some α then 1 + (tdepth H.cells + 1) else 0) ≤
      (C + D + 3 + 3 * k) * 1
    split <;> omega
  | half a b α β =>
    have eb : (TThread.toX (⟨todo, .half a b α β⟩ : TThread S)).busy = 1 := rfl
    rw [eb]
    unfold TMach.dcost
    dsimp only
    split
    · split
      · rename_i R hR
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        show 2 + (1 + (tdepth H.cells + 1) + (R.newAgents a b).length +
          (R.newLinks xs.sys.ar a b α β).length) ≤ (C + D + 3 + 3 * k) * 1
        omega
      · show 2 + (1 + (tdepth H.cells + 1)) ≤ (C + D + 3 + 3 * k) * 1
        omega
    · show 2 + (1 + (tdepth H.cells + 1)) ≤ (C + D + 3 + 3 * k) * 1
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      show 2 + (tdepth H.cells + 1) ≤ (C + D + 3 + 3 * k) * 1
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        show 6 ≤ (C + D + 3 + 3 * k) * 1
        omega
      | nil =>
        show 1 ≤ (C + D + 3 + 3 * k) * 1
        omega

/-- What the action of thread `t` costs, the depth of the trees charged. -/
def TMach.stepDcost (xs : XSys S) (M : TMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => TMach.dcost xs M.mem T
  | none => 0

/-- **The running time on the ordered memory, the depth of the trees
charged.**  It is told from the trees the run builds, not from their
sizes. -/
def TMach.dtime (xs : XSys S) (σ : Nat → Nat) (M : TMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => TMach.dtime xs σ M i + (M.trace xs σ i).1.stepDcost xs (σ i)

/-- **The time by the depth of the trees is between the time by the
digits of the sizes and three times it**, on every run from every state:
first half. -/
theorem TMach.lgtime_le_dtime (xs : XSys S) (σ : Nat → Nat) (M : TMach S) :
    ∀ i, M.lgtime xs σ i ≤ M.dtime xs σ i
  | 0 => Nat.le_refl _
  | i + 1 => by
    have ih := TMach.lgtime_le_dtime xs σ M i
    have hstep : (M.trace xs σ i).1.stepLgcost xs (σ i) ≤
        (M.trace xs σ i).1.stepDcost xs (σ i) := by
      unfold TMach.stepLgcost TMach.stepDcost
      cases (M.trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.le_refl _
      | some T => exact TMach.lgcost_le_dcost xs _ T
    show M.lgtime xs σ i + (M.trace xs σ i).1.stepLgcost xs (σ i) ≤
      M.dtime xs σ i + (M.trace xs σ i).1.stepDcost xs (σ i)
    omega

/-- Second half: the time by the depth of the trees is at most three
times the time by the digits of the sizes. -/
theorem TMach.dtime_le_lgtime (xs : XSys S) (σ : Nat → Nat) (M : TMach S) :
    ∀ i, M.dtime xs σ i ≤ 3 * M.lgtime xs σ i
  | 0 => Nat.zero_le _
  | i + 1 => by
    have ih := TMach.dtime_le_lgtime xs σ M i
    have hstep : (M.trace xs σ i).1.stepDcost xs (σ i) ≤
        3 * (M.trace xs σ i).1.stepLgcost xs (σ i) := by
      unfold TMach.stepLgcost TMach.stepDcost
      cases (M.trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.zero_le _
      | some T => exact TMach.dcost_le_lgcost xs _ T
    show M.dtime xs σ i + (M.trace xs σ i).1.stepDcost xs (σ i) ≤
      3 * (M.lgtime xs σ i + (M.trace xs σ i).1.stepLgcost xs (σ i))
    omega

/-- **The time on the ordered memory, the depth of the trees charged.**
Under the hypotheses of `IMach.time_bound`, on every run the time is at
most

    C + D + 3 + 9 * lg (X.agents.length + C * n)

for each action that is not a rest: three operations on trees that are
under three times as deep as `lg` of what the memory can hold. -/
theorem TMach.dtime_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (TMach.init X nt).dtime xs σ i ≤
      (C + D + 3 + 9 * lg (X.agents.length + C * n)) * (XMach.init X nt).work xs σ i := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have htodo := TMach.todo_le (xs := xs) hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨a, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨hA, -, -⟩ := hΦ i
    have hm : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
        (((TMach.init X nt).trace xs σ i).1.ths[σ i]?).map TThread.toX := by
      rw [← a]
      show (((TMach.init X nt).trace xs σ i).1.ths.map TThread.toX)[σ i]? = _
      rw [List.getElem?_map]
    have emem : ((TMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    have hcells : ((TMach.init X nt).trace xs σ i).1.mem.cells.size ≤
        X.agents.length + C * n := by
      rw [← treeList_length]
      show ((TMach.init X nt).trace xs σ i).1.mem.toX.agents.length ≤ _
      rw [emem]
      exact hA
    have hd := tdepth_lt ((TMach.init X nt).trace xs σ i).1.mem.cells
    have hmono := lg_mono hcells
    have hstep : ((TMach.init X nt).trace xs σ i).1.stepDcost xs (σ i) ≤
        (C + D + 3 + 9 * lg (X.agents.length + C * n)) *
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i) := by
      unfold TMach.stepDcost XMach.stepTally
      rw [hm]
      cases hT : ((TMach.init X nt).trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.zero_le _
      | some T =>
        have hsz := lg_mono (htodo i T (List.mem_of_getElem? hT))
        have hdT := tdepth_lt T.todo
        have e : C + D + 3 + 9 * lg (X.agents.length + C * n) =
            C + D + 3 + 3 * (3 * lg (X.agents.length + C * n)) := by omega
        show TMach.dcost xs ((TMach.init X nt).trace xs σ i).1.mem T ≤
          (C + D + 3 + 9 * lg (X.agents.length + C * n)) * T.toX.busy
        rw [e]
        exact TMach.dcost_le hb ok T (by omega) (by omega)
    show (TMach.init X nt).dtime xs σ i +
        ((TMach.init X nt).trace xs σ i).1.stepDcost xs (σ i) ≤
      (C + D + 3 + 9 * lg (X.agents.length + C * n)) *
        ((XMach.init X nt).work xs σ i +
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i))
    rw [Nat.mul_add]
    omega

/-- **A bound on the running time on the ordered memory, the depth of the
trees charged, whatever the schedule.** -/
theorem TMach.dtime_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    (TMach.init X nt).dtime xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) *
        (C + D + 3 + 9 * lg (X.agents.length + C * n)) := by
  have h₁ := TMach.dtime_le_work (xs := xs) hX hnd hnt hb hs hn σ i
  have h₂ := Nat.mul_le_mul_left (C + D + 3 + 9 * lg (X.agents.length + C * n))
    (XMach.work_le hX hnd hnt hb hs hn σ i)
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  omega

end TreeDepth

end INet
