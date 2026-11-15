import InteractionNets.HashMap

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### An indexed memory for the program with threads

The program with threads reads lists: a lookup of an agent or of a segment
walks the list, and taking an agent out copies it.  Here the same program
runs on a memory with two hash maps, one from the names of the agents to
their symbols and one from each port to its neighbours, so that every
lookup is one operation on a map.  The agents are kept in a log as well,
the latest first, because a thread that has written a right-hand side
takes the list of agents afresh; an agent taken out stays in the log as a
dead cell until the log is packed.  The program on the indexed memory is
proved to do, action by action, what the program on lists does, so the
theorems about that program hold for it, and its running time is bounded
in operations on the maps. -/

section Indexed

variable [DecidableEq S]

omit [DecidableEq S] in
theorem assoc_filter_ne (a i : Id) : ∀ l : List (Id × S),
    assoc i (l.filter fun e => decide (e.1 ≠ a)) = if a = i then none else assoc i l
  | [] => by
    show (none : Option S) = if a = i then none else none
    split <;> rfl
  | (k, v) :: l => by
    have ih := assoc_filter_ne a i l
    by_cases hk : k = a
    · rw [List.filter_cons_of_neg (by simpa using hk), ih]
      by_cases hai : a = i
      · rw [ite_pos' hai, ite_pos' hai]
      · rw [ite_neg' hai, ite_neg' hai]
        show assoc i l = if k = i then some v else assoc i l
        rw [ite_neg' (fun h => hai (hk.symm.trans h))]
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      show (if k = i then some v else assoc i (l.filter fun e => decide (e.1 ≠ a))) =
        if a = i then none else if k = i then some v else assoc i l
      rw [ih]
      by_cases hki : k = i
      · rw [ite_pos' hki, ite_pos' hki, ite_neg' (fun h => hk (hki.trans h.symm))]
      · rw [ite_neg' hki, ite_neg' hki]

/-- Add a neighbour at the front, unless it is there already. -/
def pushNb (q : Port) (l : List Port) : List Port := if l.head? = some q then l else q :: l

/-- The neighbours of a port in a list of segments, the latest first, none
twice in a row. -/
def nbOf : List (Port × Port) → Port → List Port
  | [], _ => []
  | e :: ws, c => if e.1 = c then pushNb e.2 (nbOf ws c) else nbOf ws c

theorem pushNb_head (q : Port) (l : List Port) : (pushNb q l).head? = some q := by
  unfold pushNb
  split
  · assumption
  · rfl

/-- The first neighbour is what a lookup in the list finds. -/
theorem assoc_nbOf : ∀ (ws : List (Port × Port)) (c : Port), assoc c ws = (nbOf ws c).head?
  | [], _ => rfl
  | (p, q) :: ws, c => by
    show (if p = c then some q else assoc c ws) =
      (if p = c then pushNb q (nbOf ws c) else nbOf ws c).head?
    by_cases h : p = c
    · rw [ite_pos' h, ite_pos' h, pushNb_head]
    · rw [ite_neg' h, ite_neg' h]
      exact assoc_nbOf ws c

theorem find_pushNb_pos {p q : Port} (hq : q ≠ p) (l : List Port) :
    (pushNb q l).find? (fun x => decide (x ≠ p)) = some q := by
  unfold pushNb
  split
  · rename_i h
    cases l with
    | nil => cases h
    | cons x l' =>
      have e : x = q := Option.some.inj h
      rw [e]
      exact List.find?_cons_of_pos (by simpa using hq)
  · exact List.find?_cons_of_pos (by simpa using hq)

theorem find_pushNb_neg {p q : Port} (hq : q = p) (l : List Port) :
    (pushNb q l).find? (fun x => decide (x ≠ p)) = l.find? (fun x => decide (x ≠ p)) := by
  unfold pushNb
  split
  · rfl
  · exact List.find?_cons_of_neg (by simpa using hq)

/-- The first neighbour other than `p` is what the search in the list
finds. -/
theorem nextSeg_nbOf : ∀ (ws : List (Port × Port)) (c p : Port),
    nextSeg ws c p = (nbOf ws c).find? (fun q => decide (q ≠ p))
  | [], _, _ => rfl
  | e :: ws, c, p => by
    have ih := nextSeg_nbOf ws c p
    show (if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg ws c p) =
      (if e.1 = c then pushNb e.2 (nbOf ws c) else nbOf ws c).find? _
    by_cases h : e.1 = c
    · rw [ite_pos' h]
      by_cases hq : e.2 ≠ p
      · rw [ite_pos' ⟨h, hq⟩]
        exact (find_pushNb_pos hq _).symm
      · rw [ite_neg' (fun hh => hq hh.2), ih]
        exact (find_pushNb_neg (Decidable.of_not_not hq) _).symm
    · rw [ite_neg' h, ite_neg' (fun hh => h hh.1)]
      exact ih

theorem nbOf_front : ∀ (ws : List (Port × Port)) (c : Port) {a b : Port} {t : List Port},
    nbOf ws c = a :: b :: t → a ≠ b
  | [], _, _, _, _, h => by cases h
  | e :: ws, c, a, b, t, h => by
    have h' : (if e.1 = c then pushNb e.2 (nbOf ws c) else nbOf ws c) = a :: b :: t := h
    by_cases hc : e.1 = c
    · rw [ite_pos' hc] at h'
      unfold pushNb at h'
      split at h'
      · exact nbOf_front ws c h'
      · rename_i hh
        obtain ⟨e₁, e₂⟩ := List.cons.inj h'
        intro hab
        apply hh
        rw [e₂, e₁, hab]
        rfl
    · rw [ite_neg' hc] at h'
      exact nbOf_front ws c h'

/-- The cells that the search for a neighbour other than `p` reads. -/
def findCells (p : Port) : List Port → Nat
  | [] => 0
  | q :: l => if q ≠ p then 1 else findCells p l + 1

/-- In a list of neighbours the search reads two cells at most. -/
theorem findCells_nbOf (ws : List (Port × Port)) (c p : Port) :
    findCells p (nbOf ws c) ≤ 2 := by
  have hf := fun {a b t} => nbOf_front ws c (a := a) (b := b) (t := t)
  cases h : nbOf ws c with
  | nil => exact Nat.zero_le _
  | cons a l =>
    show (if a ≠ p then 1 else findCells p l + 1) ≤ 2
    by_cases ha : a ≠ p
    · rw [ite_pos' ha]
      omega
    · rw [ite_neg' ha]
      cases l with
      | nil => exact Nat.le_succ 1
      | cons b t =>
        have hab := hf h
        have hb : b ≠ p := fun e => hab ((Decidable.of_not_not ha).trans e.symm)
        show (if b ≠ p then 1 else findCells p t + 1) + 1 ≤ 2
        rw [ite_pos' hb]
        exact Nat.le_refl 2

omit [DecidableEq S] in
theorem assoc_none_of_not_mem (i : Id) : ∀ l : List (Id × S), i ∉ l.map Prod.fst →
    assoc i l = none
  | [], _ => rfl
  | (k, v) :: l, h => by
    have hk : k ≠ i := fun e => h (e ▸ List.mem_cons_self)
    show (if k = i then some v else assoc i l) = none
    rw [ite_neg' hk]
    exact assoc_none_of_not_mem i l fun hm => h (List.mem_cons_of_mem _ hm)

/-- **An indexed memory.**  The agents are cells of a log, each with a
stamp, the latest first; a hash map from the names to the stamp and the
symbol says which cell of the log is the agent of that name now, and a cell
that the map does not point at is dead.  The segments are a list, and a
second hash map gives the neighbours of every port. -/
structure IMem (S : Type) where
  log : List (Nat × Id × S)
  stamp : Nat
  live : Std.HashMap Id (Nat × S)
  free : List Port
  wires : List (Port × Port)
  nbrs : Std.HashMap Port (List Port)

/-- A cell of the log is live when the map points at it. -/
def IMem.isLive (H : IMem S) (e : Nat × Id × S) : Bool :=
  decide (H.live[e.2.1]? = some (e.1, e.2.2))

/-- The memory of lists that it stands for: the live cells of the log, in
their order, and the segments. -/
def IMem.toX (H : IMem S) : XNet S :=
  ⟨(H.log.filter H.isLive).map (·.2), H.free, H.wires⟩

/-- The symbol of an agent: one lookup. -/
def IMem.sym (H : IMem S) (i : Id) : Option S := (H.live[i]?).map (·.2)

/-- The neighbours of a port: one lookup. -/
def IMem.nb (H : IMem S) (p : Port) : List Port := (H.nbrs[p]?).getD []

/-- The maps say what the lists say: stamps are below the next stamp, the
map of the agents points into the log, and the map of the neighbours lists
the neighbours. -/
structure IMem.Ok (H : IMem S) : Prop where
  lt : ∀ e ∈ H.log, e.1 < H.stamp
  mem : ∀ i s γ, H.live[i]? = some (s, γ) → (s, i, γ) ∈ H.log
  nbrs : ∀ p, H.nb p = nbOf H.wires p

theorem IMem.isLive_iff (H : IMem S) (s : Nat) (j : Id) (δ : S) :
    H.isLive (s, j, δ) = true ↔ H.live[j]? = some (s, δ) := decide_eq_true_iff

theorem IMem.assoc_sound (H : IMem S) (i : Id) : ∀ (l : List (Nat × Id × S)) (γ : S),
    assoc i ((l.filter H.isLive).map (·.2)) = some γ → H.sym i = some γ
  | [], _, h => by cases h
  | (s, j, δ) :: l, γ, h => by
    by_cases he : H.isLive (s, j, δ) = true
    · rw [List.filter_cons_of_pos he] at h
      have h' : (if j = i then some δ else assoc i ((l.filter H.isLive).map (·.2))) =
          some γ := h
      by_cases hi : j = i
      · rw [ite_pos' hi] at h'
        have hl := (H.isLive_iff s j δ).1 he
        rw [hi] at hl
        show (H.live[i]?).map (·.2) = some γ
        rw [hl]
        exact h'
      · rw [ite_neg' hi] at h'
        exact IMem.assoc_sound H i l γ h'
    · rw [List.filter_cons_of_neg he] at h
      exact IMem.assoc_sound H i l γ h

theorem IMem.assoc_complete (H : IMem S) (i : Id) {s : Nat} {γ : S}
    (hl : H.live[i]? = some (s, γ)) : ∀ l : List (Nat × Id × S), (s, i, γ) ∈ l →
      assoc i ((l.filter H.isLive).map (·.2)) = some γ
  | [], h => by cases h
  | (s', j, δ) :: l, h => by
    by_cases he : H.isLive (s', j, δ) = true
    · rw [List.filter_cons_of_pos he]
      show (if j = i then some δ else assoc i ((l.filter H.isLive).map (·.2))) = some γ
      by_cases hi : j = i
      · rw [ite_pos' hi]
        have hl' := (H.isLive_iff s' j δ).1 he
        rw [hi, hl] at hl'
        cases hl'
        rfl
      · rw [ite_neg' hi]
        rcases List.mem_cons.1 h with e | h'
        · cases e
          exact absurd rfl hi
        · exact IMem.assoc_complete H i hl l h'
    · rw [List.filter_cons_of_neg he]
      rcases List.mem_cons.1 h with e | h'
      · cases e
        exact absurd ((H.isLive_iff s i γ).2 hl) he
      · exact IMem.assoc_complete H i hl l h'

/-- **One lookup in the map is the lookup in the list of agents.** -/
theorem IMem.Ok.sym {H : IMem S} (h : H.Ok) (i : Id) : H.sym i = assoc i H.toX.agents := by
  cases hl : H.live[i]? with
  | none =>
    have e : H.sym i = none := by
      show (H.live[i]?).map (·.2) = none
      rw [hl]
      rfl
    rw [e]
    cases ha : assoc i H.toX.agents with
    | none => rfl
    | some γ =>
      have := H.assoc_sound i H.log γ ha
      rw [e] at this
      cases this
  | some v =>
    obtain ⟨s, γ⟩ := v
    have e : H.sym i = some γ := by
      show (H.live[i]?).map (·.2) = some γ
      rw [hl]
      rfl
    rw [e]
    exact (H.assoc_complete i hl H.log (h.mem i s γ hl)).symm

/-- The first neighbour is the lookup in the list of segments. -/
theorem IMem.Ok.first {H : IMem S} (h : H.Ok) (p : Port) :
    (H.nb p).head? = assoc p H.toX.wires := by
  rw [h.nbrs p]
  exact (assoc_nbOf H.wires p).symm

/-- The first neighbour other than `p` is the search in the list of
segments. -/
theorem IMem.Ok.next {H : IMem S} (h : H.Ok) (c p : Port) :
    (H.nb c).find? (fun q => decide (q ≠ p)) = nextSeg H.toX.wires c p := by
  rw [h.nbrs c]
  exact (nextSeg_nbOf H.wires c p).symm

/-- Take an agent out: one erasure. -/
def IMem.take (H : IMem S) (a : Id) : IMem S :=
  ⟨H.log, H.stamp, H.live.erase a, H.free, H.wires, H.nbrs⟩

/-- Write an agent: one cell at the front of the log, one insertion. -/
def IMem.put (H : IMem S) (i : Id) (γ : S) : IMem S :=
  ⟨(H.stamp, i, γ) :: H.log, H.stamp + 1, H.live.insert i (H.stamp, γ), H.free, H.wires,
    H.nbrs⟩

/-- Write a segment: one cell, and one more neighbour of its first end. -/
def IMem.link (H : IMem S) (p q : Port) : IMem S :=
  ⟨H.log, H.stamp, H.live, H.free, (p, q) :: H.wires, H.nbrs.insert p (pushNb q (H.nb p))⟩

/-- Drop the dead cells of the log. -/
def IMem.pack (H : IMem S) : IMem S :=
  ⟨H.log.filter H.isLive, H.stamp, H.live, H.free, H.wires, H.nbrs⟩

theorem IMem.toX_take (H : IMem S) (a : Id) : (H.take a).toX = H.toX.takeAgent a := by
  have key : ∀ l : List (Nat × Id × S), (l.filter (H.take a).isLive).map (·.2) =
      ((l.filter H.isLive).map (·.2)).filter fun e => decide (e.1 ≠ a) := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih =>
      obtain ⟨s, j, δ⟩ := e
      have hl : (H.take a).isLive (s, j, δ) =
          decide ((if a = j then none else H.live[j]?) = some (s, δ)) := by
        show decide ((H.live.erase a)[j]? = some (s, δ)) = _
        rw [hget_erase]
      by_cases hj : a = j
      · have h₁ : ¬ (H.take a).isLive (s, j, δ) = true := by
          rw [hl, ite_pos' hj]
          simp
        rw [List.filter_cons_of_neg h₁, ih]
        by_cases h₂ : H.isLive (s, j, δ) = true
        · rw [List.filter_cons_of_pos h₂]
          show _ = ((j, δ) :: (l.filter H.isLive).map (·.2)).filter fun e => decide (e.1 ≠ a)
          rw [List.filter_cons_of_neg (by simpa using hj.symm)]
        · rw [List.filter_cons_of_neg h₂]
      · have h₁ : (H.take a).isLive (s, j, δ) = H.isLive (s, j, δ) := by
          rw [hl, ite_neg' hj]
          rfl
        by_cases h₂ : H.isLive (s, j, δ) = true
        · rw [List.filter_cons_of_pos (h₁.trans h₂), List.filter_cons_of_pos h₂]
          show (j, δ) :: (l.filter (H.take a).isLive).map (·.2) =
            ((j, δ) :: (l.filter H.isLive).map (·.2)).filter fun e => decide (e.1 ≠ a)
          rw [List.filter_cons_of_pos (by simpa using fun e : j = a => hj e.symm), ih]
        · rw [List.filter_cons_of_neg (fun h => h₂ (h₁.symm.trans h)),
            List.filter_cons_of_neg h₂, ih]
  show (⟨(H.log.filter (H.take a).isLive).map (·.2), H.free, H.wires⟩ : XNet S) =
    ⟨((H.log.filter H.isLive).map (·.2)).filter fun e => decide (e.1 ≠ a), H.free, H.wires⟩
  rw [key]

omit [DecidableEq S] in
theorem IMem.Ok.take {H : IMem S} (h : H.Ok) (a : Id) : (H.take a).Ok :=
  ⟨h.lt, fun i s γ hl => by
    have hl' : (H.live.erase a)[i]? = some (s, γ) := hl
    rw [hget_erase] at hl'
    by_cases e : a = i
    · rw [ite_pos' e] at hl'
      cases hl'
    · rw [ite_neg' e] at hl'
      exact h.mem i s γ hl', h.nbrs⟩

/-- Writing an agent that is not in memory puts it at the front. -/
theorem IMem.toX_put {H : IMem S} (h : H.Ok) {i : Id} (hi : assoc i H.toX.agents = none)
    (γ : S) : (H.put i γ).toX = H.toX.putAgent i γ := by
  have hn : H.live[i]? = none := by
    have e := h.sym i
    rw [hi] at e
    cases hl : H.live[i]? with
    | none => rfl
    | some v =>
      have e' : (H.live[i]?).map (·.2) = none := e
      rw [hl] at e'
      cases e'
  have hl : ∀ (s : Nat) (j : Id) (δ : S), (H.put i γ).isLive (s, j, δ) =
      decide ((if i = j then some (H.stamp, γ) else H.live[j]?) = some (s, δ)) := by
    intro s j δ
    show decide ((H.live.insert i (H.stamp, γ))[j]? = some (s, δ)) = _
    rw [hget_insert]
  have h₀ : (H.put i γ).isLive (H.stamp, i, γ) = true := by
    rw [hl, ite_pos' rfl]
    exact decide_eq_true rfl
  have h₁ : H.log.filter (H.put i γ).isLive = H.log.filter H.isLive := by
    apply List.filter_congr
    intro e he
    obtain ⟨s, j, δ⟩ := e
    rw [hl]
    by_cases hj : i = j
    · rw [ite_pos' hj]
      have hs : s < H.stamp := h.lt _ he
      have e₁ : decide (some (H.stamp, γ) = some (s, δ)) = false := by
        apply decide_eq_false
        intro e
        cases e
        exact Nat.lt_irrefl _ hs
      have e₂ : H.isLive (s, j, δ) = false := by
        show decide (H.live[j]? = some (s, δ)) = false
        rw [← hj, hn]
        exact decide_eq_false (fun e => by cases e)
      rw [e₁, e₂]
    · rw [ite_neg' hj]
      rfl
  show (⟨(((H.stamp, i, γ) :: H.log).filter (H.put i γ).isLive).map (·.2), H.free, H.wires⟩ :
    XNet S) = ⟨(i, γ) :: (H.log.filter H.isLive).map (·.2), H.free, H.wires⟩
  rw [List.filter_cons_of_pos h₀, h₁]
  rfl

omit [DecidableEq S] in
theorem IMem.Ok.put {H : IMem S} (h : H.Ok) (i : Id) (γ : S) : (H.put i γ).Ok :=
  ⟨fun e he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (h.lt e he'), fun j s δ hl => by
    have hl' : (H.live.insert i (H.stamp, γ))[j]? = some (s, δ) := hl
    rw [hget_insert] at hl'
    by_cases e : i = j
    · rw [ite_pos' e] at hl'
      cases hl'
      rw [← e]
      exact List.mem_cons_self
    · rw [ite_neg' e] at hl'
      exact List.mem_cons_of_mem _ (h.mem j s δ hl'), h.nbrs⟩

theorem IMem.toX_link (H : IMem S) (p q : Port) : (H.link p q).toX = H.toX.putLink p q := rfl

omit [DecidableEq S] in
theorem IMem.Ok.link {H : IMem S} (h : H.Ok) (p q : Port) : (H.link p q).Ok :=
  ⟨h.lt, h.mem, fun p' => by
    show ((H.nbrs.insert p (pushNb q (H.nb p)))[p']?).getD [] =
      if p = p' then pushNb q (nbOf H.wires p') else nbOf H.wires p'
    rw [hget_insert]
    by_cases e : p = p'
    · rw [ite_pos' e, ite_pos' e, h.nbrs, e]
      rfl
    · rw [ite_neg' e, ite_neg' e]
      exact h.nbrs p'⟩

theorem IMem.toX_pack (H : IMem S) : H.pack.toX = H.toX := by
  have e : (H.log.filter H.isLive).filter H.isLive = H.log.filter H.isLive :=
    List.filter_eq_self.2 fun a ha => (List.mem_filter.1 ha).2
  show (⟨((H.log.filter H.isLive).filter H.isLive).map (·.2), H.free, H.wires⟩ : XNet S) = _
  rw [e]
  rfl

theorem IMem.Ok.pack {H : IMem S} (h : H.Ok) : H.pack.Ok :=
  ⟨fun e he => h.lt e (List.mem_filter.1 he).1, fun i s γ hl =>
    List.mem_filter.2 ⟨h.mem i s γ hl, (H.isLive_iff s i γ).2 hl⟩, h.nbrs⟩

/-- After packing the log holds the agents and nothing else. -/
theorem IMem.pack_length (H : IMem S) : H.pack.log.length = H.toX.agents.length :=
  (List.length_map (f := fun e : Nat × Id × S => e.2)).symm

/-- A memory with no agents and no segments. -/
def IMem.empty (free : List Port) : IMem S := ⟨[], 0, ∅, free, [], ∅⟩

omit [DecidableEq S] in
theorem IMem.empty_ok (free : List Port) : (IMem.empty free : IMem S).Ok := by
  refine ⟨fun _ he => (by cases he), fun i s γ hl => ?_, fun p => ?_⟩
  · have hl' : (∅ : Std.HashMap Id (Nat × S))[i]? = some (s, γ) := hl
    rw [Std.HashMap.getElem?_empty] at hl'
    cases hl'
  · show ((∅ : Std.HashMap Port (List Port))[p]?).getD [] = []
    rw [Std.HashMap.getElem?_empty]
    rfl

/-- **The indexed memory of a net**: its agents written one by one, the
last first, then its segments. -/
def IMem.ofX (X : XNet S) : IMem S :=
  X.wires.foldr (fun e H => H.link e.1 e.2)
    (X.agents.foldr (fun e H => H.put e.1 e.2) (IMem.empty X.free))

theorem IMem.ofX_agents (free : List Port) : ∀ l : List (Id × S), (l.map Prod.fst).Nodup →
    (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).Ok ∧
      (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).toX = ⟨l, free, []⟩ ∧
      (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).log.length = l.length
  | [], _ => ⟨IMem.empty_ok free, rfl, rfl⟩
  | (i, γ) :: l, hnd => by
    have hnd' : i ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    obtain ⟨ok, e, len⟩ := IMem.ofX_agents free l hnd'.2
    have hi : assoc i (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).toX.agents =
        none := by
      rw [e]
      exact assoc_none_of_not_mem i l hnd'.1
    refine ⟨ok.put i γ, ?_, ?_⟩
    · show ((l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).put i γ).toX = _
      rw [IMem.toX_put ok hi, e]
      rfl
    · show (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).log.length + 1 = l.length + 1
      rw [len]

theorem IMem.ofX_links (H₀ : IMem S) (h₀ : H₀.Ok) : ∀ ws : List (Port × Port),
    (ws.foldr (fun e H => H.link e.1 e.2) H₀).Ok ∧
      (ws.foldr (fun e H => H.link e.1 e.2) H₀).toX =
        ⟨H₀.toX.agents, H₀.toX.free, ws ++ H₀.toX.wires⟩ ∧
      (ws.foldr (fun e H => H.link e.1 e.2) H₀).log = H₀.log
  | [] => ⟨h₀, rfl, rfl⟩
  | (p, q) :: ws => by
    obtain ⟨ok, e, len⟩ := IMem.ofX_links H₀ h₀ ws
    refine ⟨ok.link p q, ?_, len⟩
    show ((ws.foldr (fun e H => H.link e.1 e.2) H₀).link p q).toX = _
    rw [IMem.toX_link, e]
    rfl

/-- **The indexed memory of a net stands for the net**, when no agent is
listed twice. -/
theorem IMem.ofX_toX {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) :
    (IMem.ofX X).Ok ∧ (IMem.ofX X).toX = X ∧ (IMem.ofX X).log.length = X.agents.length := by
  obtain ⟨ok, e, len⟩ := IMem.ofX_agents X.free X.agents hnd
  obtain ⟨ok', e', len'⟩ := IMem.ofX_links _ ok X.wires
  refine ⟨ok', ?_, ?_⟩
  · show (X.wires.foldr (fun e H => H.link e.1 e.2)
      (X.agents.foldr (fun e H => H.put e.1 e.2) (IMem.empty X.free))).toX = X
    rw [e', e]
    show (⟨X.agents, X.free, X.wires ++ []⟩ : XNet S) = X
    rw [List.append_nil]
  · show (X.wires.foldr (fun e H => H.link e.1 e.2)
      (X.agents.foldr (fun e H => H.put e.1 e.2) (IMem.empty X.free))).log.length = _
    rw [len', len]

/-- **One action of a thread on the indexed memory**: the action of the
program, with every lookup in a list replaced by a lookup in a map.  When a
thread has written a right-hand side it packs the log and takes the agents
afresh from it. -/
def IMach.act (xs : XSys S) (H : IMem S) (T : XThread S) : IMem S × XThread S × Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => (H, T, 0)
    | e :: rest =>
      if H.sym e.1 = some e.2 then (H, ⟨rest, .look e.1 e.2⟩, 0)
      else (H, ⟨rest, .idle⟩, 0)
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
  | .write [] [] => (H.pack, ⟨H.pack.log.map (·.2), .idle⟩, 0)

omit [DecidableEq S] in
theorem assoc_none_of_nodup_cons {i : Id} {γ : S} {l : List (Id × S)}
    (h : (((i, γ) :: l).map Prod.fst).Nodup) : assoc i l = none :=
  assoc_none_of_not_mem i l (List.nodup_cons.1 h).1

/-- **The indexed action is the action of the program**: on a memory whose
maps say what its lists say, it does to the memory of lists that it stands
for what the program does, leaves the thread in the same state, claims as
often, and keeps the maps right.  The one condition is that the program
does not write an agent that is in memory already, which it never does. -/
theorem IMach.act_sim (xs : XSys S) {H : IMem S} (h : H.Ok) (T : XThread S)
    (hnd : ((XMach.act xs H.toX T).1.agents.map Prod.fst).Nodup) :
    (IMach.act xs H T).1.toX = (XMach.act xs H.toX T).1 ∧
      (IMach.act xs H T).2 = (XMach.act xs H.toX T).2 ∧ (IMach.act xs H T).1.Ok := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact ⟨rfl, rfl, h⟩
    | cons e rest =>
      unfold IMach.act XMach.act
      dsimp only
      rw [h.sym e.1]
      by_cases hc : assoc e.1 H.toX.agents = some e.2
      · rw [ite_pos' hc, ite_pos' hc]
        exact ⟨rfl, rfl, h⟩
      · rw [ite_neg' hc, ite_neg' hc]
        exact ⟨rfl, rfl, h⟩
  | look a α =>
    unfold IMach.act XMach.act
    dsimp only
    rw [h.first (a, 0)]
    cases assoc (a, 0) H.toX.wires <;> exact ⟨rfl, rfl, h⟩
  | seek a α p c =>
    unfold IMach.act XMach.act
    dsimp only
    rw [h.sym c.1, h.next c p]
    cases (if c.2 = 0 then assoc c.1 H.toX.agents else none) with
    | some β =>
      dsimp only
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β).isSome
      · rw [ite_pos' hc, ite_pos' hc]
        exact ⟨rfl, rfl, h⟩
      · rw [ite_neg' hc, ite_neg' hc]
        exact ⟨rfl, rfl, h⟩
    | none =>
      dsimp only
      cases nextSeg H.toX.wires c p <;> exact ⟨rfl, rfl, h⟩
  | ready a b α β =>
    unfold IMach.act XMach.act
    dsimp only
    rw [h.sym a]
    by_cases hc : assoc a H.toX.agents = some α
    · rw [ite_pos' hc, ite_pos' hc]
      exact ⟨H.toX_take a, rfl, h.take a⟩
    · rw [ite_neg' hc, ite_neg' hc]
      exact ⟨rfl, rfl, h⟩
  | half a b α β =>
    unfold XMach.act at hnd
    dsimp only at hnd
    unfold IMach.act XMach.act
    dsimp only
    rw [h.sym b]
    cases hR : (if assoc b H.toX.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R => exact ⟨H.toX_take b, rfl, h.take b⟩
    | none =>
      rw [hR] at hnd
      exact ⟨IMem.toX_put h (assoc_none_of_nodup_cons hnd) α, rfl, h.put a α⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨IMem.toX_put h (assoc_none_of_nodup_cons hnd) γ, rfl, h.put i γ⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨H.toX_link p q, rfl, h.link p q⟩
      | nil =>
        refine ⟨H.toX_pack, ?_, h.pack⟩
        show ((⟨H.pack.log.map (·.2), .idle⟩ : XThread S), 0) = (⟨H.toX.agents, .idle⟩, 0)
        rfl

/-- The program on the indexed memory: the memory and the threads. -/
structure IMach (S : Type) where
  mem : IMem S
  ths : List (XThread S)

/-- The program on lists that it stands for. -/
def IMach.toX (M : IMach S) : XMach S := ⟨M.mem.toX, M.ths⟩

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def IMach.step (xs : XSys S) (M : IMach S) (t : Nat) : IMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(IMach.act xs M.mem T).1, M.ths.set t (IMach.act xs M.mem T).2.1⟩,
      (IMach.act xs M.mem T).2.2)
  | none => (M, 0)

/-- The run under an unending schedule: the state and the number of claims
after `i` actions. -/
def IMach.trace (xs : XSys S) (σ : Nat → Nat) (M : IMach S) : Nat → IMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((IMach.trace xs σ M i).1.step xs (σ i)).1,
      (IMach.trace xs σ M i).2 + ((IMach.trace xs σ M i).1.step xs (σ i)).2)

/-- The program before it starts: the indexed memory of the net, and the
threads of the program on lists. -/
def IMach.init (X : XNet S) (n : Nat) : IMach S := ⟨IMem.ofX X, (XMach.init X n).ths⟩

theorem IMach.init_toX {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (IMach.init X n).toX = XMach.init X n := by
  show (⟨(IMem.ofX X).toX, (XMach.init X n).ths⟩ : XMach S) = XMach.init X n
  rw [(IMem.ofX_toX hnd).2.1]
  rfl

/-- One action of the indexed program is one action of the program. -/
theorem IMach.step_sim (xs : XSys S) {M : IMach S} (h : M.mem.Ok) (t : Nat)
    (hnd : ((M.toX.step xs t).1.mem.agents.map Prod.fst).Nodup) :
    (M.step xs t).1.toX = (M.toX.step xs t).1 ∧ (M.step xs t).2 = (M.toX.step xs t).2 ∧
      (M.step xs t).1.mem.Ok := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold IMach.step
      rw [ht]
    have ht' : M.toX.ths[t]? = none := ht
    have e₂ : M.toX.step xs t = (M.toX, 0) := by
      unfold XMach.step
      rw [ht']
    rw [e₁, e₂]
    exact ⟨rfl, rfl, h⟩
  | some T =>
    have ht' : M.toX.ths[t]? = some T := ht
    have e₂ : M.toX.step xs t = (⟨(XMach.act xs M.mem.toX T).1,
        M.ths.set t (XMach.act xs M.mem.toX T).2.1⟩, (XMach.act xs M.mem.toX T).2.2) :=
      XMach.step_eq ht' rfl
    rw [e₂] at hnd
    obtain ⟨a, b, c⟩ := IMach.act_sim xs h T hnd
    have e₁ : M.step xs t = (⟨(IMach.act xs M.mem T).1,
        M.ths.set t (IMach.act xs M.mem T).2.1⟩, (IMach.act xs M.mem T).2.2) := by
      unfold IMach.step
      rw [ht]
    rw [e₁, e₂]
    refine ⟨?_, ?_, c⟩
    · show (⟨(IMach.act xs M.mem T).1.toX, M.ths.set t (IMach.act xs M.mem T).2.1⟩ :
        XMach S) = ⟨(XMach.act xs M.mem.toX T).1, M.ths.set t (XMach.act xs M.mem.toX T).2.1⟩
      rw [a, b]
    · show (IMach.act xs M.mem T).2.2 = (XMach.act xs M.mem.toX T).2.2
      rw [b]

variable {xs : XSys S}

/-- **The indexed program runs as the program does.**  From a memory whose
maps say what its lists say and in which no agent is listed twice, under
any schedule, after any number of actions the indexed program stands for
the state of the program on lists, has claimed as often, and its maps are
right. -/
theorem IMach.trace_sim {M : IMach S} (h : M.mem.Ok) (hL : M.toX.Live xs)
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
    obtain ⟨a', b', c'⟩ := IMach.step_sim xs c (σ i) hn
    refine ⟨?_, ?_, c'⟩
    · show ((M.trace xs σ i).1.step xs (σ i)).1.toX = ((M.toX.trace xs σ i).1.step xs (σ i)).1
      rw [a', a]
    · show (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2 =
        (M.toX.trace xs σ i).2 + ((M.toX.trace xs σ i).1.step xs (σ i)).2
      rw [b', b, a]

/-- The run from a net: the indexed program stands for the program on
lists at every action. -/
theorem IMach.init_sim {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((IMach.init X nt).trace xs σ i).1.toX = ((XMach.init X nt).trace xs σ i).1 ∧
      ((IMach.init X nt).trace xs σ i).2 = ((XMach.init X nt).trace xs σ i).2 ∧
      ((IMach.init X nt).trace xs σ i).1.mem.Ok := by
  have e := IMach.init_toX hnd nt
  have hL : (IMach.init X nt).toX.Live xs := by
    rw [e]
    exact XMach.init_live hX hnt
  have hn : ((IMach.init X nt).toX.mem.agents.map Prod.fst).Nodup := by
    rw [e]
    exact hnd
  have k := IMach.trace_sim (IMem.ofX_toX hnd).1 hL hn σ i
  rw [e] at k
  exact k

/-- **Under a fair schedule the indexed program comes to rest with the
normal form.**  Take a well-formed net in which no agent is listed twice,
with a normal form `n` steps away, at least one thread, and any unending
schedule in which every thread keeps being scheduled.  From some action on
every thread is idle with an empty list, `n` claims have been made, and
the indexed memory stands for the normal form. -/
theorem IMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((IMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((IMach.init X nt).trace xs σ i).2 = n ∧
      ((IMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  obtain ⟨i₀, h⟩ := XMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨a, b, -⟩ := IMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((IMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- **The bound on the length of a fair run holds on the indexed memory.**
With every thread scheduled in every window of `F` actions, the indexed
program is at rest with the normal form after `F` times

    (n + 1) * X.passBound n C D + n * (C + D + 1) + 1

actions, as the program on lists is. -/
theorem IMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((n + 1) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((IMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((IMach.init X nt).trace xs σ i).2 = n ∧
      ((IMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  intro i hi
  obtain ⟨a, b, -⟩ := IMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := XMach.fair_bound hX hnd hnt hb hs hn σ hfair i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((IMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- Only a rest costs nothing. -/
theorem XMach.cost_zero {X : XNet S} {T : XThread S} (h : XMach.cost xs X T = 0) :
    T = ⟨[], .idle⟩ := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => rfl
    | cons e rest =>
      have h' : 1 + assocCells e.1 X.agents = 0 := h
      omega
  | look a α =>
    have h' : 1 + assocCells (a, 0) X.wires = 0 := h
    omega
  | seek a α p c =>
    have h' : (if c.2 = 0 then 1 + assocCells c.1 X.agents +
        (if (assoc c.1 X.agents).isSome then 0 else nextSegCells X.wires c p)
      else 1 + nextSegCells X.wires c p) = 0 := h
    split at h' <;> omega
  | ready a b α β =>
    have h' : 1 + assocCells a X.agents +
      (if assoc a X.agents = some α then X.agents.length else 0) = 0 := h
    omega
  | half a b α β =>
    unfold XMach.cost at h
    dsimp only at h
    omega
  | write as ls =>
    cases as with
    | cons e as =>
      have h' : 1 = 0 := h
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        have h' : 1 = 0 := h
        omega
      | nil =>
        have h' : 1 + X.agents.length = 0 := h
        omega

/-- A thread that has written a right-hand side and is about to take the
agents afresh. -/
def TState.fin : TState S → Nat
  | .write [] [] => 1
  | _ => 0

/-- A thread that is writing. -/
def TState.writes : TState S → Nat
  | .write _ _ => 1
  | _ => 0

/-- A thread takes the agents afresh only after a claim of its own. -/
theorem XMach.act_fin (xs : XSys S) (X : XNet S) (T : XThread S) :
    T.st.fin + (XMach.act xs X T).2.1.st.writes ≤ T.st.writes + (XMach.act xs X T).2.2 := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.le_refl _
    | cons e rest =>
      unfold XMach.act
      dsimp only
      split <;> exact Nat.le_refl _
  | look a α =>
    unfold XMach.act
    dsimp only
    split <;> exact Nat.le_refl _
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    split
    · split <;> exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  | ready a b α β =>
    unfold XMach.act
    dsimp only
    split <;> exact Nat.le_refl _
  | half a b α β =>
    unfold XMach.act
    dsimp only
    split <;> exact Nat.le_refl _
  | write as ls =>
    cases as with
    | cons e as => exact Nat.le_refl _
    | nil =>
      cases ls with
      | cons e ls => exact Nat.le_refl _
      | nil => exact Nat.le_refl _

omit [DecidableEq S] in
theorem threadOf_none {ths : List (XThread S)} {t : Nat} (h : ths[t]? = none) :
    threadOf ths t = .idle := by
  unfold threadOf
  rw [h]

theorem XMach.step_fin (xs : XSys S) (M : XMach S) (t : Nat) :
    (threadOf M.ths t).fin + total (fun T => T.st.writes) (M.step xs t).1.ths ≤
      total (fun T => T.st.writes) M.ths + (M.step xs t).2 := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold XMach.step
      rw [ht]
    rw [e, threadOf_none ht]
    show 0 + total (fun T => T.st.writes) M.ths ≤ total (fun T => T.st.writes) M.ths + 0
    omega
  | some T =>
    rw [XMach.step_eq ht rfl, threadOf_eq ht]
    have ts := total_set (fun T => T.st.writes) M.ths t T (XMach.act xs M.mem T).2.1 ht
    have hf := XMach.act_fin xs M.mem T
    show T.st.fin + total (fun T => T.st.writes) (M.ths.set t (XMach.act xs M.mem T).2.1) ≤
      total (fun T => T.st.writes) M.ths + (XMach.act xs M.mem T).2.2
    have ts' : total (fun T => T.st.writes) (M.ths.set t (XMach.act xs M.mem T).2.1) +
        T.st.writes = total (fun T => T.st.writes) M.ths +
          (XMach.act xs M.mem T).2.1.st.writes := ts
    omega

/-- The number of times the threads take the agents afresh in the first `i`
actions of a run. -/
def XMach.packs (xs : XSys S) (σ : Nat → Nat) (M : XMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => XMach.packs xs σ M i + (threadOf (M.trace xs σ i).1.ths (σ i)).fin

theorem XMach.packs_le (σ : Nat → Nat) (M : XMach S) :
    ∀ i, M.packs xs σ i + total (fun T => T.st.writes) (M.trace xs σ i).1.ths ≤
      total (fun T => T.st.writes) M.ths + (M.trace xs σ i).2
  | 0 => by
    show 0 + total (fun T => T.st.writes) M.ths ≤ total (fun T => T.st.writes) M.ths + 0
    omega
  | i + 1 => by
    have ih := XMach.packs_le σ M i
    have hs := XMach.step_fin xs (M.trace xs σ i).1 (σ i)
    show M.packs xs σ i + (threadOf (M.trace xs σ i).1.ths (σ i)).fin +
        total (fun T => T.st.writes) ((M.trace xs σ i).1.step xs (σ i)).1.ths ≤
      total (fun T => T.st.writes) M.ths +
        ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2)
    omega

/-- **The agents are taken afresh once for each claim at most.** -/
theorem XMach.packs_le_claims (X : XNet S) (nt : Nat) (σ : Nat → Nat) (i : Nat) :
    (XMach.init X nt).packs xs σ i ≤ ((XMach.init X nt).trace xs σ i).2 := by
  have h := XMach.packs_le (xs := xs) σ (XMach.init X nt) i
  have z : total (fun T => T.st.writes) (XMach.init X nt).ths ≤
      (XMach.init X nt).ths.length * 0 :=
    total_le_mul fun T hT => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      exact Nat.le_refl 0
  rw [Nat.mul_zero] at z
  omega

/-- **A measure of the work that is left.**  Take a well-formed net in
which no agent is listed twice, with a normal form `n` steps away, rules
that write at most `C` agents and `D` segments, `nt` threads, at least
one, and any schedule.  There is a measure that starts at no more than

    (nt + n) * X.passBound n C D + n * (C + D + 1)

and that every action which is not a rest brings down; a rest leaves the
program and the measure as they are.  So at most that many actions are not
rests.  Along the run the memory never lists more than the agents of the
net and `C - 2` more for each of the `n` claims (a claim takes two agents
out), and at most `n` claims are made. -/
theorem XMach.work_measure {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∃ Φ : Nat → Nat, Φ 0 ≤ (nt + n) * X.passBound n C D + n * (C + D + 1) ∧
      ∀ i, ((XMach.init X nt).trace xs σ i).1.mem.agents.length ≤ X.agents.length + (C - 2) * n ∧
        ((XMach.init X nt).trace xs σ i).2 ≤ n ∧
        ((((XMach.init X nt).trace xs σ i).1.step xs (σ i) =
              (((XMach.init X nt).trace xs σ i).1, 0) ∧
            ((XMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = 0 ∧ Φ (i + 1) = Φ i) ∨
          Φ (i + 1) < Φ i) := by
  have live := XMach.trace_live (xs := xs) σ (XMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((XMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((XMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := XMach.trace_run xs σ (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((XMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  obtain ⟨is, ih⟩ := XMach.init_sizes X nt
  have sizes := XMach.seq_sizes (xs := xs) ((XMach.init X nt).trace xs σ) σ (fun _ => rfl)
    live hb (W := X.wires.length) (A₀ := X.agents.length)
    ⟨Nat.le_trans (Nat.le_of_eq is) (Nat.le_add_right _ _),
      Nat.le_trans (Nat.le_of_eq ih) (Nat.le_add_right _ _)⟩
  have hA : ∀ i, ((XMach.init X nt).trace xs σ i).1.heads ≤ X.agents.length + (C - 2) * n :=
    fun i => Nat.le_trans (sizes i).2
      (Nat.add_le_add_left (Nat.mul_le_mul_left (C - 2) (bound i)) _)
  have nd : ∀ i, (((XMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact XMach.step_nodup (live i) ih (σ i)
  have hH := XNet.normal_sized hX hb hs hn
  have ahead : ∀ i, ((XMach.init X nt).trace xs σ i).1.Ahead N' :=
    fun i => XMach.ahead_of_run (live i).inv hX (run i) hs hn
  refine ⟨fun i => ((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
        (X.agents.length + (C - 2) * n) +
      (n - ((XMach.init X nt).trace xs σ i).2) *
        (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1), ?_,
    fun i => ⟨Nat.le_trans (Nat.le_add_right _ _) (hA i), bound i, ?_⟩⟩
  · have e0 := XMach.init_energyIn X nt N' (X.wires.length + D * n) (X.agents.length + (C - 2) * n)
    obtain ⟨-, pr⟩ := Steps.links hX hs
    have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
    have hscan : N'.scan (X.wires.length + D * n) X.agents ≤
        7 * X.agents.length + (X.wires.length + D * n) :=
      Net.scan_le hH X.agents hnd fun e he q q' h h' =>
        hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
          (pr (.inl ⟨e.2, hag e he⟩) h')
    have hsc : nt * N'.scan (X.wires.length + D * n) X.agents ≤ nt * X.passBound n C D :=
      Nat.mul_le_mul_left nt (Nat.le_trans hscan (by
        show 7 * X.agents.length + (X.wires.length + D * n) ≤
          7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)
        omega))
    have e1 : C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1 =
        X.passBound n C D + (C + D + 1) := by
      show _ = 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + (C + D + 1)
      omega
    show (XMach.init X nt).energyIn N' (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
      (n - 0) * (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) ≤
      (nt + n) * X.passBound n C D + n * (C + D + 1)
    rw [Nat.sub_zero, e1, Nat.mul_add n (X.passBound n C D) (C + D + 1),
      Nat.add_mul nt n (X.passBound n C D)]
    omega
  · have hb1 : ((XMach.init X nt).trace xs σ i).2 +
        (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2 ≤ n := bound (i + 1)
    rcases XMach.step_work (live i) (nd i) hb hH (ahead i) (hA i) (σ i) with
      ⟨e, hz⟩ | ⟨h1, hce⟩ | ⟨h0, hlt⟩
    · refine .inl ⟨e, hz, ?_⟩
      show (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.energyIn N'
            (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
          (n - (((XMach.init X nt).trace xs σ i).2 +
            (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) *
            (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) =
          ((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + (C - 2) * n) +
          (n - ((XMach.init X nt).trace xs σ i).2) *
            (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1)
      rw [e]
      rfl
    · refine .inr ?_
      show (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.energyIn N'
            (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
          (n - (((XMach.init X nt).trace xs σ i).2 +
            (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) *
            (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) <
          ((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + (C - 2) * n) +
          (n - ((XMach.init X nt).trace xs σ i).2) *
            (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1)
      have e1 : n - ((XMach.init X nt).trace xs σ i).2 =
          (n - (((XMach.init X nt).trace xs σ i).2 +
            (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) + 1 := by omega
      rw [e1, Nat.add_mul, Nat.one_mul]
      omega
    · refine .inr ?_
      show (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.energyIn N'
            (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
          (n - (((XMach.init X nt).trace xs σ i).2 +
            (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) *
            (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) <
          ((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + (C - 2) * n) +
          (n - ((XMach.init X nt).trace xs σ i).2) *
            (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1)
      rw [h0]
      exact Nat.add_lt_add_right hlt _

/-- **What an action costs on the indexed memory**: one for the action, one
for each operation on a map, one for each cell of a list of neighbours it
reads, one for each cell it writes, and, when it takes the agents afresh,
the whole log and the cells of the fresh list.  A thread at rest costs
nothing. -/
def IMach.cost (xs : XSys S) (H : IMem S) (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | _ :: _ => 2
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c)
    else 2 + findCells p (H.nb c)
  | .ready a _ α _ => 2 + if H.sym a = some α then 1 else 0
  | .half a b α β =>
    2 + if H.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 1 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 2
      else 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1 + H.log.length + H.pack.log.length

/-- **An action costs a constant**, the size of a rule and seven, whatever
the size of the memory; the log grows by one cell at most.  The one
exception is taking the agents afresh, which costs the log and leaves it
with the agents only. -/
theorem IMach.cost_le {C D : Nat} (hb : xs.Bounded C D) {H : IMem S} (h : H.Ok)
    (T : XThread S) :
    IMach.cost xs H T + (IMach.act xs H T).1.log.length ≤
      H.log.length + (C + D + 7) + T.st.fin * (2 * H.toX.agents.length) := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil =>
      show 0 + H.log.length ≤ H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
      omega
    | cons e rest =>
      have e₁ : (IMach.act xs H ⟨e :: rest, .idle⟩).1 = H := by
        unfold IMach.act
        dsimp only
        split <;> rfl
      rw [e₁]
      show 2 + H.log.length ≤ H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
      omega
  | look a α =>
    have e₁ : (IMach.act xs H ⟨todo, .look a α⟩).1 = H := by
      unfold IMach.act
      dsimp only
      split <;> rfl
    rw [e₁]
    show 3 + H.log.length ≤ H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
    omega
  | seek a α p c =>
    have e₁ : (IMach.act xs H ⟨todo, .seek a α p c⟩).1 = H := by
      unfold IMach.act
      dsimp only
      split
      · split <;> rfl
      · split <;> rfl
    rw [e₁]
    have hf := findCells_nbOf H.wires c p
    rw [← h.nbrs c] at hf
    show (if c.2 = 0 then 2 + (if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c))
      else 2 + findCells p (H.nb c)) + H.log.length ≤
        H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    unfold IMach.act IMach.cost
    dsimp only
    by_cases hc : H.sym a = some α
    · rw [ite_pos' hc, ite_pos' hc]
      show 2 + 1 + H.log.length ≤ H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
      omega
    · rw [ite_neg' hc, ite_neg' hc]
      show 2 + 0 + H.log.length ≤ H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
      omega
  | half a b α β =>
    unfold IMach.act IMach.cost
    dsimp only
    by_cases hc : H.sym b = some β ∧ a ≠ b
    · rw [ite_pos' hc, ite_pos' hc]
      cases hR : xs.rule α β with
      | none =>
        show 2 + 2 + (H.log.length + 1) ≤
          H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
        omega
      | some R =>
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        show 2 + (1 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length) +
          H.log.length ≤ H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
        omega
    · rw [ite_neg' hc, ite_neg' hc]
      show 2 + 2 + (H.log.length + 1) ≤
        H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show 3 + (H.log.length + 1) ≤
        H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 6 + H.log.length ≤ H.log.length + (C + D + 7) + 0 * (2 * H.toX.agents.length)
        omega
      | nil =>
        show 1 + H.log.length + H.pack.log.length + H.pack.log.length ≤
          H.log.length + (C + D + 7) + 1 * (2 * H.toX.agents.length)
        rw [H.pack_length]
        omega

/-- What the action of thread `t` costs. -/
def IMach.stepCost (xs : XSys S) (M : IMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => IMach.cost xs M.mem T
  | none => 0

theorem IMach.stepCost_le {C D : Nat} (hb : xs.Bounded C D) {M : IMach S} (h : M.mem.Ok)
    (t : Nat) :
    M.stepCost xs t + (M.step xs t).1.mem.log.length ≤
      M.mem.log.length + (C + D + 7) +
        (threadOf M.ths t).fin * (2 * M.mem.toX.agents.length) := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold IMach.step
      rw [ht]
    have e₂ : M.stepCost xs t = 0 := by
      unfold IMach.stepCost
      rw [ht]
    rw [e₁, e₂, threadOf_none ht]
    show 0 + M.mem.log.length ≤ M.mem.log.length + (C + D + 7) +
      0 * (2 * M.mem.toX.agents.length)
    omega
  | some T =>
    have e₁ : M.step xs t = (⟨(IMach.act xs M.mem T).1,
        M.ths.set t (IMach.act xs M.mem T).2.1⟩, (IMach.act xs M.mem T).2.2) := by
      unfold IMach.step
      rw [ht]
    have e₂ : M.stepCost xs t = IMach.cost xs M.mem T := by
      unfold IMach.stepCost
      rw [ht]
    rw [e₁, e₂, threadOf_eq ht]
    exact IMach.cost_le hb h T

/-- A rest of the program is a rest of the indexed program. -/
theorem IMach.step_rest {M : IMach S} {t : Nat} (hz : M.toX.stepCost xs t = 0) :
    M.stepCost xs t = 0 ∧ M.step xs t = (M, 0) ∧ (threadOf M.ths t).fin = 0 := by
  cases ht : M.ths[t]? with
  | none =>
    refine ⟨?_, ?_, ?_⟩
    · unfold IMach.stepCost
      rw [ht]
    · unfold IMach.step
      rw [ht]
    · rw [threadOf_none ht]
      rfl
  | some T =>
    have ht' : M.toX.ths[t]? = some T := ht
    have hz' : XMach.cost xs M.mem.toX T = 0 := by
      unfold XMach.stepCost at hz
      rw [ht'] at hz
      exact hz
    have eT := XMach.cost_zero hz'
    subst eT
    refine ⟨?_, ?_, ?_⟩
    · unfold IMach.stepCost
      rw [ht]
      rfl
    · unfold IMach.step
      rw [ht]
      show ((⟨M.mem, M.ths.set t ⟨[], .idle⟩⟩ : IMach S), 0) = (M, 0)
      rw [set_self M.ths t _ ht]
    · rw [threadOf_eq ht]
      rfl

/-- **The running time on the indexed memory** of the first `i` actions of
a run. -/
def IMach.time (xs : XSys S) (σ : Nat → Nat) (M : IMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => IMach.time xs σ M i + (M.trace xs σ i).1.stepCost xs (σ i)

/-- A cost with a constant part, paid only when a measure goes down, and a
part `L` paid only when a counter goes up, adds up to at most the constant
times the measure at the start and `L` times the counter. -/
theorem paid_two (τ Φ μ : Nat → Nat) (c L : Nat)
    (h : ∀ i, (τ (i + 1) = τ i ∧ Φ (i + 1) = Φ i ∧ μ (i + 1) = μ i) ∨
      (τ (i + 1) + μ i * L ≤ τ i + c + μ (i + 1) * L ∧ Φ (i + 1) < Φ i)) :
    ∀ i, τ i + c * Φ i + μ 0 * L ≤ τ 0 + c * Φ 0 + μ i * L
  | 0 => Nat.le_refl _
  | i + 1 => by
    have ih := paid_two τ Φ μ c L h i
    rcases h i with ⟨e₁, e₂, e₃⟩ | ⟨h₁, h₂⟩
    · rw [e₁, e₂, e₃]
      exact ih
    · have h₃ := Nat.mul_le_mul_left c (Nat.succ_le_of_lt h₂)
      rw [Nat.mul_succ] at h₃
      omega

/-- **A bound on the running time on the indexed memory, whatever the
schedule.**  Take a well-formed net in which no agent is listed twice, with
a normal form `n` steps away, rules that write at most `C` agents and `D`
segments, and `nt` threads, at least one.  However the threads are
scheduled, the run never takes more time than

    ((nt + n) * X.passBound n C D + n * (C + D + 1)) * (C + D + 7)

the actions that are not rests, each at a cost that does not depend on the
size of the memory, and

    (2 * n + 1) * (X.agents.length + (C - 2) * n)

for taking the agents afresh, once for each claim.  On lists the first
factor is the same and the second is the size of the memory. -/
theorem IMach.time_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (IMach.init X nt).time xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) * (C + D + 7) +
        (2 * n + 1) * (X.agents.length + (C - 2) * n) := by
  obtain ⟨Φ, hΦ0, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have sim := IMach.init_sim (xs := xs) hX hnd hnt σ
  have key := paid_two
    (fun i => (IMach.init X nt).time xs σ i +
      ((IMach.init X nt).trace xs σ i).1.mem.log.length) Φ
    (fun i => (XMach.init X nt).packs xs σ i) (C + D + 7)
    (2 * (X.agents.length + (C - 2) * n)) (fun i => by
      obtain ⟨a, -, ok⟩ := sim i
      obtain ⟨hA, -, hw⟩ := hΦ i
      have eths : ((IMach.init X nt).trace xs σ i).1.ths =
          ((XMach.init X nt).trace xs σ i).1.ths := congrArg XMach.ths a
      have emem : ((IMach.init X nt).trace xs σ i).1.mem.toX =
          ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
      rcases hw with ⟨-, hz, hΦe⟩ | hlt
      · rw [← a] at hz
        obtain ⟨z₁, z₂, z₃⟩ := IMach.step_rest hz
        rw [eths] at z₃
        refine .inl ⟨?_, hΦe, ?_⟩
        · show (IMach.init X nt).time xs σ i +
              ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) +
              (((IMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.log.length =
            (IMach.init X nt).time xs σ i +
              ((IMach.init X nt).trace xs σ i).1.mem.log.length
          rw [z₁, z₂]
          rfl
        · show (XMach.init X nt).packs xs σ i +
              (threadOf ((XMach.init X nt).trace xs σ i).1.ths (σ i)).fin =
            (XMach.init X nt).packs xs σ i
          rw [z₃]
          rfl
      · refine .inr ⟨?_, hlt⟩
        have hc := IMach.stepCost_le hb ok (σ i)
        rw [eths, emem] at hc
        have hm := Nat.mul_le_mul_left
          (threadOf ((XMach.init X nt).trace xs σ i).1.ths (σ i)).fin
          (Nat.mul_le_mul_left 2 hA)
        show (IMach.init X nt).time xs σ i +
              ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) +
              (((IMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.log.length +
            (XMach.init X nt).packs xs σ i * (2 * (X.agents.length + (C - 2) * n)) ≤
          (IMach.init X nt).time xs σ i +
              ((IMach.init X nt).trace xs σ i).1.mem.log.length + (C + D + 7) +
            ((XMach.init X nt).packs xs σ i +
              (threadOf ((XMach.init X nt).trace xs σ i).1.ths (σ i)).fin) *
              (2 * (X.agents.length + (C - 2) * n))
        rw [Nat.add_mul]
        omega)
  intro i
  have k := key i
  have k' : (IMach.init X nt).time xs σ i +
        ((IMach.init X nt).trace xs σ i).1.mem.log.length + (C + D + 7) * Φ i +
        0 * (2 * (X.agents.length + (C - 2) * n)) ≤
      0 + (IMem.ofX X).log.length + (C + D + 7) * Φ 0 +
        (XMach.init X nt).packs xs σ i * (2 * (X.agents.length + (C - 2) * n)) := k
  rw [(IMem.ofX_toX hnd).2.2] at k'
  have hp : (XMach.init X nt).packs xs σ i ≤ n :=
    Nat.le_trans (XMach.packs_le_claims X nt σ i) (hΦ i).2.1
  have h₁ := Nat.mul_le_mul_right (2 * (X.agents.length + (C - 2) * n)) hp
  have h₂ := Nat.mul_le_mul_left (C + D + 7) hΦ0
  have e : (2 * n + 1) * (X.agents.length + (C - 2) * n) =
      n * (2 * (X.agents.length + (C - 2) * n)) + (X.agents.length + (C - 2) * n) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm 2 n, Nat.mul_assoc]
  rw [e, Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  omega

omit [DecidableEq S] in
theorem TState.fin_cases (s : TState S) : s.fin = 0 ∨ s.fin = 1 := by
  cases s with
  | idle => exact .inl rfl
  | look a α => exact .inl rfl
  | seek a α p c => exact .inl rfl
  | ready a b α β => exact .inl rfl
  | half a b α β => exact .inl rfl
  | write as ls =>
    cases as with
    | cons e as => exact .inl rfl
    | nil =>
      cases ls with
      | cons e ls => exact .inl rfl
      | nil => exact .inr rfl

/-- Taking the agents afresh costs the list of agents on lists too. -/
theorem XMach.cost_fin (X : XNet S) (T : XThread S) :
    T.st.fin * (1 + X.agents.length) ≤ XMach.cost xs X T := by
  obtain ⟨todo, s⟩ := T
  have z : ∀ c : Nat, 0 * (1 + X.agents.length) ≤ c := fun c => by
    rw [Nat.zero_mul]
    exact Nat.zero_le c
  cases s with
  | idle => exact z _
  | look a α => exact z _
  | seek a α p c => exact z _
  | ready a b α β => exact z _
  | half a b α β => exact z _
  | write as ls =>
    cases as with
    | cons e as => exact z _
    | nil =>
      cases ls with
      | cons e ls => exact z _
      | nil =>
        show 1 * (1 + X.agents.length) ≤ 1 + X.agents.length
        omega

/-- **An action on the indexed memory costs at most a constant times what
it costs on lists**, the size of a rule and nine, with the cells it adds
to the log counted in. -/
theorem IMach.cost_le_list {C D : Nat} (hb : xs.Bounded C D) {H : IMem S} (h : H.Ok)
    (T : XThread S) :
    IMach.cost xs H T + (IMach.act xs H T).1.log.length ≤
      H.log.length + (C + D + 9) * XMach.cost xs H.toX T := by
  have h1 := IMach.cost_le hb h T
  by_cases hz : XMach.cost xs H.toX T = 0
  · have eT := XMach.cost_zero hz
    subst eT
    show 0 + H.log.length ≤ H.log.length + (C + D + 9) * XMach.cost xs H.toX ⟨[], .idle⟩
    omega
  · have hx : 1 ≤ XMach.cost xs H.toX T := by omega
    have hf := XMach.cost_fin (xs := xs) H.toX T
    rcases TState.fin_cases T.st with f0 | f1
    · rw [f0] at h1
      have h2 := Nat.mul_le_mul_left (C + D + 9) hx
      omega
    · rw [f1] at h1 hf
      have h2 := Nat.mul_le_mul_left (C + D + 9) hf
      rw [Nat.one_mul, Nat.mul_add, Nat.mul_one] at h2
      have h3 := Nat.mul_le_mul_right H.toX.agents.length (show 2 ≤ C + D + 9 by omega)
      omega

theorem IMach.stepCost_le_list {C D : Nat} (hb : xs.Bounded C D) {M : IMach S}
    (h : M.mem.Ok) (t : Nat) :
    M.stepCost xs t + (M.step xs t).1.mem.log.length ≤
      M.mem.log.length + (C + D + 9) * M.toX.stepCost xs t := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold IMach.step
      rw [ht]
    have e₂ : M.stepCost xs t = 0 := by
      unfold IMach.stepCost
      rw [ht]
    rw [e₁, e₂]
    show 0 + M.mem.log.length ≤ M.mem.log.length + (C + D + 9) * M.toX.stepCost xs t
    omega
  | some T =>
    have ht' : M.toX.ths[t]? = some T := ht
    have e₁ : M.step xs t = (⟨(IMach.act xs M.mem T).1,
        M.ths.set t (IMach.act xs M.mem T).2.1⟩, (IMach.act xs M.mem T).2.2) := by
      unfold IMach.step
      rw [ht]
    have e₂ : M.stepCost xs t = IMach.cost xs M.mem T := by
      unfold IMach.stepCost
      rw [ht]
    have e₃ : M.toX.stepCost xs t = XMach.cost xs M.mem.toX T := by
      unfold XMach.stepCost
      rw [ht']
      rfl
    rw [e₁, e₂, e₃]
    exact IMach.cost_le_list hb h T

/-- **The indexed program is never slower than the program on lists by
more than a constant.**  On every run, whatever the net, the schedule and
the number of actions, the time on the indexed memory is at most the
agents of the net and

    (C + D + 9)

times the time the same run takes on lists.  No normal form is needed. -/
theorem IMach.time_le_list {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) (σ : Nat → Nat) :
    ∀ i, (IMach.init X nt).time xs σ i +
        ((IMach.init X nt).trace xs σ i).1.mem.log.length ≤
      X.agents.length + (C + D + 9) * (XMach.init X nt).time xs σ i
  | 0 => by
    show 0 + (IMem.ofX X).log.length ≤ X.agents.length + (C + D + 9) * 0
    rw [(IMem.ofX_toX hnd).2.2]
    omega
  | i + 1 => by
    have ih := IMach.time_le_list hX hnd hnt hb σ i
    obtain ⟨a, -, ok⟩ := IMach.init_sim (xs := xs) hX hnd hnt σ i
    have hs := IMach.stepCost_le_list hb ok (σ i)
    rw [a] at hs
    show (IMach.init X nt).time xs σ i +
          ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) +
        (((IMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.log.length ≤
      X.agents.length + (C + D + 9) * ((XMach.init X nt).time xs σ i +
        ((XMach.init X nt).trace xs σ i).1.stepCost xs (σ i))
    rw [Nat.mul_add]
    omega

/-- The least an action costs on the indexed memory, whatever is in it. -/
def XThread.least (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | _ :: _ => 2
  | .look _ _ => 3
  | .seek _ _ _ _ => 2
  | .ready _ _ _ _ => 2
  | .half _ _ _ _ => 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

theorem IMach.least_le (xs : XSys S) (H : IMem S) (T : XThread S) :
    T.least ≤ IMach.cost xs H T := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.le_refl 0
    | cons e rest => exact Nat.le_refl 2
  | look a α => exact Nat.le_refl 3
  | seek a α p c =>
    show 2 ≤ (if c.2 = 0 then 2 + (if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c))
      else 2 + findCells p (H.nb c))
    split <;> omega
  | ready a b α β =>
    show 2 ≤ 2 + if H.sym a = some α then 1 else 0
    omega
  | half a b α β =>
    unfold IMach.cost
    dsimp only
    exact Nat.le_add_right 2 _
  | write as ls =>
    cases as with
    | cons e as => exact Nat.le_refl 3
    | nil =>
      cases ls with
      | cons e ls => exact Nat.le_refl 6
      | nil =>
        show 1 ≤ 1 + H.log.length + H.pack.log.length
        omega

/-- What the next `j` actions of a thread come to at a rate `κ` for each
state it is in, as long as the memory stays as it is. -/
def XThread.tally (κ : XThread S → Nat) (xs : XSys S) (X : XNet S) : XThread S → Nat → Nat
  | _, 0 => 0
  | T, j + 1 => κ T + XThread.tally κ xs X (XMach.act xs X T).2.1 j

theorem XThread.tally_add (κ : XThread S → Nat) (xs : XSys S) (X : XNet S) :
    ∀ (a b : Nat) (T : XThread S),
      T.tally κ xs X (a + b) = T.tally κ xs X a + (T.after xs X a).tally κ xs X b
  | 0, b, T => by
    rw [Nat.zero_add]
    show _ = 0 + _
    rw [Nat.zero_add]
    rfl
  | a + 1, b, T => by
    have ih := XThread.tally_add κ xs X a b (XMach.act xs X T).2.1
    have e : a + 1 + b = a + b + 1 := by omega
    rw [e]
    show κ T + XThread.tally κ xs X (XMach.act xs X T).2.1 (a + b) =
      κ T + XThread.tally κ xs X (XMach.act xs X T).2.1 a +
        (XThread.after xs X (XMach.act xs X T).2.1 a).tally κ xs X b
    rw [ih]
    omega

theorem XThread.tally_succ (κ : XThread S → Nat) (xs : XSys S) (X : XNet S) (j : Nat)
    (T : XThread S) :
    T.tally κ xs X (j + 1) = T.tally κ xs X j + κ (T.after xs X j) := by
  rw [XThread.tally_add κ xs X j 1 T]
  show _ = _ + (κ (T.after xs X j) + 0)
  rfl

theorem XThread.tally_mono (κ : XThread S → Nat) (xs : XSys S) (X : XNet S) (T : XThread S)
    {a b : Nat} (h : a ≤ b) : T.tally κ xs X a ≤ T.tally κ xs X b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  rw [XThread.tally_add]
  exact Nat.le_add_right _ _

/-- What the action of thread `t` comes to at the rate `κ`. -/
def XMach.stepTally (κ : XThread S → Nat) (M : XMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => κ T
  | none => 0

/-- What the first `i` actions of a run come to at the rate `κ`. -/
def XMach.tally (κ : XThread S → Nat) (xs : XSys S) (σ : Nat → Nat) (M : XMach S) :
    Nat → Nat
  | 0 => 0
  | i + 1 => XMach.tally κ xs σ M i + (M.trace xs σ i).1.stepTally κ (σ i)

/-- What thread `t` comes to after `h` actions of its own, the memory
staying as it is. -/
def XMach.tallyAt (κ : XThread S → Nat) (xs : XSys S) (M : XMach S) (t h : Nat) : Nat :=
  match M.ths[t]? with
  | some T => T.tally κ xs M.mem h
  | none => 0

/-- For threads that only read, a run comes to what each thread comes to
on its own, added up, whatever the schedule and the rate. -/
theorem XMach.tally_reads (κ : XThread S → Nat) {M : XMach S} (σ : Nat → Nat)
    (hR : ∀ T, T ∈ M.ths → T.Reads xs M.mem) :
    ∀ i, M.tally κ xs σ i = sumTo (fun t => M.tallyAt κ xs t (hits σ t i)) M.ths.length
  | 0 => by
    have z : ∀ m, sumTo (fun t => M.tallyAt κ xs t (hits σ t 0)) m = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        show sumTo (fun t => M.tallyAt κ xs t (hits σ t 0)) m + M.tallyAt κ xs m 0 = 0
        rw [ih]
        unfold XMach.tallyAt
        split <;> rfl
    rw [z]
    rfl
  | i + 1 => by
    obtain ⟨-, hl, ht⟩ := XMach.trace_reads (xs := xs) σ hR i
    have ih := XMach.tally_reads κ σ hR i
    have hd : M.tallyAt κ xs (σ i) (hits σ (σ i) (i + 1)) =
        M.tallyAt κ xs (σ i) (hits σ (σ i) i) + (M.trace xs σ i).1.stepTally κ (σ i) ∧
        (¬ σ i < M.ths.length → (M.trace xs σ i).1.stepTally κ (σ i) = 0) := by
      cases hs : M.ths[σ i]? with
      | none =>
        have hn : (M.trace xs σ i).1.ths[σ i]? = none := by
          rw [List.getElem?_eq_none_iff] at hs ⊢
          rw [hl]
          exact hs
        have z : (M.trace xs σ i).1.stepTally κ (σ i) = 0 := by
          unfold XMach.stepTally
          rw [hn]
        refine ⟨?_, fun _ => z⟩
        rw [z]
        unfold XMach.tallyAt
        rw [hs]
      | some T =>
        have hU := ht (σ i) T hs
        have c : (M.trace xs σ i).1.stepTally κ (σ i) =
            κ (T.after xs M.mem (hits σ (σ i) i)) := by
          unfold XMach.stepTally
          rw [hU]
        refine ⟨?_, fun h => absurd (List.getElem?_eq_some_iff.1 hs).1 h⟩
        rw [c]
        unfold XMach.tallyAt
        rw [hs]
        show T.tally κ xs M.mem (hits σ (σ i) i + if σ i = σ i then 1 else 0) = _
        rw [ite_pos' rfl, XThread.tally_succ]
    have hb := sumTo_bump (g := fun t => M.tallyAt κ xs t (hits σ t i))
      (g' := fun t => M.tallyAt κ xs t (hits σ t (i + 1))) (s := σ i)
      (d := (M.trace xs σ i).1.stepTally κ (σ i))
      (fun t hne => by
        show M.tallyAt κ xs t (hits σ t i + if σ i = t then 1 else 0) = _
        rw [ite_neg' (Ne.symm hne)]
        rfl)
      hd.1 M.ths.length
    show M.tally κ xs σ i + (M.trace xs σ i).1.stepTally κ (σ i) = _
    rw [hb, ih]
    by_cases hlt : σ i < M.ths.length
    · rw [ite_pos' hlt]
    · rw [ite_neg' hlt, hd.2 hlt]

/-- If no thread writes, and each comes to `L` or more before it can be at
rest, the run has come to `L` for each thread, or more, when it is at
rest. -/
theorem XMach.tally_ge_rest (κ : XThread S → Nat) {M : XMach S} (σ : Nat → Nat)
    (hR : ∀ T, T ∈ M.ths → T.Reads xs M.mem) {L : Nat}
    (hL : ∀ T, T ∈ M.ths → ∃ j, (∀ j', j' < j → T.after xs M.mem j' ≠ ⟨[], .idle⟩) ∧
      L ≤ T.tally κ xs M.mem j) :
    ∀ i, (M.trace xs σ i).1.resting = true → M.ths.length * L ≤ M.tally κ xs σ i := by
  intro i hr
  obtain ⟨-, -, ht⟩ := XMach.trace_reads (xs := xs) σ hR i
  rw [XMach.tally_reads κ σ hR i]
  refine sumTo_ge _ fun t hlt => ?_
  have hT : M.ths[t]? = some M.ths[t] := List.getElem?_eq_getElem hlt
  obtain ⟨j, lo, hj⟩ := hL _ (List.mem_of_getElem? hT)
  have hrest : (M.ths[t]).after xs M.mem (hits σ t i) = ⟨[], .idle⟩ :=
    XThread.eq_rest (List.all_eq_true.1 hr _ (List.mem_of_getElem? (ht t _ hT)))
  have hge : j ≤ hits σ t i := by
    rcases Nat.lt_or_ge (hits σ t i) j with h | h
    · exact absurd hrest (lo _ h)
    · exact h
  show L ≤ M.tallyAt κ xs t (hits σ t i)
  unfold XMach.tallyAt
  rw [hT]
  exact Nat.le_trans hj (XThread.tally_mono κ xs M.mem _ hge)

/-- **The time on the indexed memory is at least what the actions come to
at their least cost.** -/
theorem IMach.time_ge_least {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (XMach.init X nt).tally XThread.least xs σ i ≤ (IMach.init X nt).time xs σ i
  | 0 => Nat.le_refl 0
  | i + 1 => by
    have ih := IMach.time_ge_least hX hnd hnt σ i
    obtain ⟨a, -, -⟩ := IMach.init_sim (xs := xs) hX hnd hnt σ i
    have eths : ((IMach.init X nt).trace xs σ i).1.ths =
        ((XMach.init X nt).trace xs σ i).1.ths := congrArg XMach.ths a
    have hs : ((XMach.init X nt).trace xs σ i).1.stepTally XThread.least (σ i) ≤
        ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) := by
      unfold XMach.stepTally IMach.stepCost
      rw [eths]
      cases ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
      | some T => exact IMach.least_le xs _ T
      | none => exact Nat.le_refl 0
    show (XMach.init X nt).tally XThread.least xs σ i +
        ((XMach.init X nt).trace xs σ i).1.stepTally XThread.least (σ i) ≤
      (IMach.init X nt).time xs σ i + ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i)
    omega

/-- An agent that leads to a port which is not the principal port of an
agent in memory takes three actions, which cost seven or more on the
indexed memory. -/
theorem XThread.least_inert {X : XNet S} {e : Id × S} (rest : List (Id × S))
    (h : X.Inert e) :
    (⟨e :: rest, .idle⟩ : XThread S).tally XThread.least xs X 3 = 7 ∧
      (⟨e :: rest, .idle⟩ : XThread S).after xs X 3 = ⟨rest, .idle⟩ := by
  obtain ⟨h₁, q, h₂, h₃, h₄⟩ := h
  have a₁ : XMach.act xs X ⟨e :: rest, .idle⟩ = (X, ⟨rest, .look e.1 e.2⟩, 0) :=
    XMach.act_idle_pos h₁
  have a₂ : XMach.act xs X ⟨rest, .look e.1 e.2⟩ =
      (X, ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩, 0) := XMach.act_look h₂
  have a₃ : XMach.act xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩ = (X, ⟨rest, .idle⟩, 0) :=
    XMach.act_seek_stop h₃ h₄
  constructor
  · show XThread.least ⟨e :: rest, .idle⟩ +
        (XThread.least (XMach.act xs X ⟨e :: rest, .idle⟩).2.1 +
          (XThread.least (XMach.act xs X (XMach.act xs X ⟨e :: rest, .idle⟩).2.1).2.1 + 0)) = 7
    rw [a₁]
    show XThread.least ⟨e :: rest, .idle⟩ + (XThread.least ⟨rest, .look e.1 e.2⟩ +
      (XThread.least (XMach.act xs X ⟨rest, .look e.1 e.2⟩).2.1 + 0)) = 7
    rw [a₂]
    rfl
  · show XThread.after xs X (XMach.act xs X (XMach.act xs X
      (XMach.act xs X ⟨e :: rest, .idle⟩).2.1).2.1).2.1 0 = _
    rw [a₁]
    show XThread.after xs X (XMach.act xs X (XMach.act xs X ⟨rest, .look e.1 e.2⟩).2.1).2.1 0 = _
    rw [a₂]
    show XThread.after xs X (XMach.act xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩).2.1 0 = _
    rw [a₃]
    rfl

/-- A pass over such agents costs seven for each on the indexed memory, or
more. -/
theorem XThread.least_inert_pass {X : XNet S} (rest : List (Id × S)) :
    ∀ (l : List (Id × S)), (∀ e, e ∈ l → X.Inert e) →
      7 * l.length ≤ (⟨l ++ rest, .idle⟩ : XThread S).tally XThread.least xs X (3 * l.length)
  | [], _ => Nat.le_refl 0
  | e :: l, h => by
    obtain ⟨c, a⟩ := XThread.least_inert (xs := xs) (l ++ rest) (h e List.mem_cons_self)
    have ih := XThread.least_inert_pass rest l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have e1 : 3 * (e :: l).length = 3 + 3 * l.length := by
      show 3 * (l.length + 1) = _
      omega
    have e2 : 7 * (e :: l).length = 7 * l.length + 7 := by
      show 7 * (l.length + 1) = _
      omega
    rw [e1, e2]
    show _ ≤ (⟨e :: (l ++ rest), .idle⟩ : XThread S).tally XThread.least xs X (3 + 3 * l.length)
    rw [XThread.tally_add, a, c]
    omega

/-- One for a thread that is not at rest. -/
def XThread.busy (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | _ :: _ => 1
  | .look _ _ => 1
  | .seek _ _ _ _ => 1
  | .ready _ _ _ _ => 1
  | .half _ _ _ _ => 1
  | .write _ _ => 1

omit [DecidableEq S] in
theorem XThread.busy_le (T : XThread S) : T.busy ≤ 1 := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.zero_le 1
    | cons e rest => exact Nat.le_refl 1
  | look a α => exact Nat.le_refl 1
  | seek a α p c => exact Nat.le_refl 1
  | ready a b α β => exact Nat.le_refl 1
  | half a b α β => exact Nat.le_refl 1
  | write as ls => exact Nat.le_refl 1

omit [DecidableEq S] in
/-- An action that is not a rest costs two or more on the indexed memory,
except taking the agents afresh, which may cost one. -/
theorem XThread.busy_least (T : XThread S) : 2 * T.busy ≤ T.least + T.st.fin := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.le_refl 0
    | cons e rest => exact Nat.le_refl 2
  | look a α => exact Nat.le_succ 2
  | seek a α p c => exact Nat.le_refl 2
  | ready a b α β => exact Nat.le_refl 2
  | half a b α β => exact Nat.le_refl 2
  | write as ls =>
    cases as with
    | cons e as => exact Nat.le_succ 2
    | nil =>
      cases ls with
      | cons e ls =>
        show 2 ≤ 6
        omega
      | nil => exact Nat.le_refl 2

theorem XThread.busy_rest {X : XNet S} {T : XThread S} (h : XMach.cost xs X T = 0) :
    T.busy = 0 := by
  rw [XMach.cost_zero h]
  rfl

theorem XThread.busy_cost {X : XNet S} {T : XThread S} (h : XMach.cost xs X T ≠ 0) :
    T.busy = 1 := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact absurd rfl h
    | cons e rest => rfl
  | look a α => rfl
  | seek a α p c => rfl
  | ready a b α β => rfl
  | half a b α β => rfl
  | write as ls => rfl

theorem XMach.stepTally_busy_rest {M : XMach S} {t : Nat} (h : M.stepCost xs t = 0) :
    M.stepTally XThread.busy t = 0 := by
  unfold XMach.stepCost at h
  unfold XMach.stepTally
  cases ht : M.ths[t]? with
  | none => rfl
  | some T =>
    rw [ht] at h
    exact XThread.busy_rest h

theorem XMach.stepTally_busy_cost {M : XMach S} {t : Nat} (h : M.stepCost xs t ≠ 0) :
    M.stepTally XThread.busy t = 1 := by
  unfold XMach.stepCost at h
  unfold XMach.stepTally
  cases ht : M.ths[t]? with
  | none =>
    rw [ht] at h
    exact absurd rfl h
  | some T =>
    rw [ht] at h
    exact XThread.busy_cost h

omit [DecidableEq S] in
theorem XMach.stepTally_busy_le (M : XMach S) (t : Nat) :
    M.stepTally XThread.busy t ≤ 1 := by
  unfold XMach.stepTally
  split
  · exact XThread.busy_le _
  · exact Nat.zero_le 1

omit [DecidableEq S] in
theorem XMach.stepTally_busy_least (M : XMach S) (t : Nat) :
    2 * M.stepTally XThread.busy t ≤
      M.stepTally XThread.least t + (threadOf M.ths t).fin := by
  cases ht : M.ths[t]? with
  | none =>
    unfold XMach.stepTally
    rw [ht]
    exact Nat.zero_le _
  | some T =>
    rw [threadOf_eq ht]
    unfold XMach.stepTally
    rw [ht]
    exact XThread.busy_least T

omit [DecidableEq S] in
theorem XMach.stepTally_busy_resting {M : XMach S} (h : M.resting = true) (t : Nat) :
    M.stepTally XThread.busy t = 0 := by
  unfold XMach.stepTally
  split
  · rename_i T hT
    rw [XThread.eq_rest (List.all_eq_true.1 h T (List.mem_of_getElem? hT))]
    rfl
  · rfl

/-- **The work of a run**: how many of its first `i` actions are not
rests. -/
def XMach.work (xs : XSys S) (σ : Nat → Nat) (M : XMach S) (i : Nat) : Nat :=
  M.tally XThread.busy xs σ i

theorem XMach.work_mono (σ : Nat → Nat) (M : XMach S) {a b : Nat} (h : a ≤ b) :
    M.work xs σ a ≤ M.work xs σ b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have ih' := ih (Nat.le_add_right a d)
    show M.work xs σ a ≤ M.work xs σ (a + d) +
      (M.trace xs σ (a + d)).1.stepTally XThread.busy (σ (a + d))
    omega

/-- Once the program is at rest its work stays what it is. -/
theorem XMach.work_rest {M : XMach S} (σ : Nat → Nat) {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) : ∀ d, M.work xs σ (B + d) = M.work xs σ B
  | 0 => rfl
  | d + 1 => by
    show M.work xs σ (B + d) + (M.trace xs σ (B + d)).1.stepTally XThread.busy (σ (B + d)) = _
    rw [XMach.stepTally_busy_resting (XMach.resting_trace σ h d), Nat.add_zero]
    exact XMach.work_rest σ h d

omit [DecidableEq S] in
theorem XMach.stepTally_busy_single {M : XMach S} (hl : M.ths.length = 1)
    (hr : ¬ M.resting = true) : M.stepTally XThread.busy 0 = 1 := by
  obtain ⟨mem, ths⟩ := M
  cases ths with
  | nil => cases hl
  | cons T tl =>
    cases tl with
    | cons U tl =>
      have hl' : tl.length + 1 + 1 = 1 := hl
      omega
    | nil =>
      obtain ⟨todo, s⟩ := T
      cases s with
      | idle =>
        cases todo with
        | nil => exact absurd rfl hr
        | cons e rest => rfl
      | look a α => rfl
      | seek a α p c => rfl
      | ready a b α β => rfl
      | half a b α β => rfl
      | write as ls => rfl

/-- One thread alone is at work at every action until it rests. -/
theorem XMach.work_single {X : XNet S} {T : XThread S} {K : Nat}
    (h : ∀ i, i < K → ¬ ((⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) i).1.resting = true) :
    ∀ i, i ≤ K → (⟨X, [T]⟩ : XMach S).work xs (fun _ => 0) i = i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := XMach.work_single h i (Nat.le_of_succ_le hi)
    have hl : ((⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) i).1.ths.length = 1 :=
      XMach.trace_length xs _ _ i
    show (⟨X, [T]⟩ : XMach S).work xs (fun _ => 0) i +
      ((⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) i).1.stepTally XThread.busy 0 = i + 1
    rw [ih, XMach.stepTally_busy_single hl (h i hi)]

/-- **The actions that are not rests are bounded, whatever the
schedule.**  Take a well-formed net in which no agent is listed twice,
with a normal form `n` steps away, rules that write at most `C` agents and
`D` segments, and `nt` threads, at least one.  However the threads are
scheduled, fairly or not, at most

    (nt + n) * X.passBound n C D + n * (C + D + 1)

of their actions are not rests. -/
theorem XMach.work_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (XMach.init X nt).work xs σ i ≤
      (nt + n) * X.passBound n C D + n * (C + D + 1) := by
  obtain ⟨Φ, hΦ0, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have key : ∀ i, (XMach.init X nt).work xs σ i + Φ i ≤ Φ 0 := by
    intro i
    induction i with
    | zero =>
      show 0 + Φ 0 ≤ Φ 0
      omega
    | succ i ih =>
      obtain ⟨-, -, hw⟩ := hΦ i
      show (XMach.init X nt).work xs σ i +
        ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i) + Φ (i + 1) ≤ Φ 0
      rcases hw with ⟨-, hz, he⟩ | hlt
      · rw [XMach.stepTally_busy_rest hz, he]
        exact ih
      · have := XMach.stepTally_busy_le ((XMach.init X nt).trace xs σ i).1 (σ i)
        omega
  intro i
  have := key i
  omega

theorem XMach.work_least (σ : Nat → Nat) (M : XMach S) :
    ∀ i, 2 * M.work xs σ i ≤ M.tally XThread.least xs σ i + M.packs xs σ i
  | 0 => Nat.le_refl 0
  | i + 1 => by
    have ih := XMach.work_least σ M i
    have hs := XMach.stepTally_busy_least (M.trace xs σ i).1 (σ i)
    show 2 * (M.work xs σ i + (M.trace xs σ i).1.stepTally XThread.busy (σ i)) ≤
      M.tally XThread.least xs σ i + (M.trace xs σ i).1.stepTally XThread.least (σ i) +
        (M.packs xs σ i + (threadOf (M.trace xs σ i).1.ths (σ i)).fin)
    omega

/-- **The indexed time is at least twice the work, less one for each
claim**: every action that is not a rest costs two or more, except taking
the agents afresh, which happens once for each claim at most. -/
theorem IMach.time_ge_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (i : Nat) :
    2 * (XMach.init X nt).work xs σ i ≤
      (IMach.init X nt).time xs σ i + ((XMach.init X nt).trace xs σ i).2 := by
  have h₁ := XMach.work_least (xs := xs) σ (XMach.init X nt) i
  have h₂ := IMach.time_ge_least hX hnd hnt σ i
  have h₃ := XMach.packs_le_claims (xs := xs) X nt σ i
  omega

/-- **The indexed time is the work, up to a constant, and the fresh
lists.**  Under the hypotheses of `IMach.time_bound`, on every run the
time on the indexed memory is at most the agents of the net,

    (C + D + 7)

for each action that is not a rest, and twice the agents the memory can
hold for each claim made so far. -/
theorem IMach.time_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (IMach.init X nt).time xs σ i ≤
      X.agents.length + (C + D + 7) * (XMach.init X nt).work xs σ i +
        2 * (X.agents.length + (C - 2) * n) * ((XMach.init X nt).trace xs σ i).2 := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have sim := IMach.init_sim (xs := xs) hX hnd hnt σ
  have key : ∀ i, (IMach.init X nt).time xs σ i +
        ((IMach.init X nt).trace xs σ i).1.mem.log.length ≤
      X.agents.length + (C + D + 7) * (XMach.init X nt).work xs σ i +
        (XMach.init X nt).packs xs σ i * (2 * (X.agents.length + (C - 2) * n)) := by
    intro i
    induction i with
    | zero =>
      show 0 + (IMem.ofX X).log.length ≤
        X.agents.length + (C + D + 7) * 0 + 0 * (2 * (X.agents.length + (C - 2) * n))
      rw [(IMem.ofX_toX hnd).2.2]
      omega
    | succ i ih =>
      obtain ⟨a, -, ok⟩ := sim i
      obtain ⟨hA, -, -⟩ := hΦ i
      have eths : ((IMach.init X nt).trace xs σ i).1.ths =
          ((XMach.init X nt).trace xs σ i).1.ths := congrArg XMach.ths a
      have emem : ((IMach.init X nt).trace xs σ i).1.mem.toX =
          ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
      show (IMach.init X nt).time xs σ i +
            ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) +
          (((IMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.log.length ≤
        X.agents.length + (C + D + 7) * ((XMach.init X nt).work xs σ i +
            ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i)) +
          ((XMach.init X nt).packs xs σ i +
            (threadOf ((XMach.init X nt).trace xs σ i).1.ths (σ i)).fin) *
            (2 * (X.agents.length + (C - 2) * n))
      by_cases hz : ((XMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = 0
      · have hb0 := XMach.stepTally_busy_rest hz
        rw [← a] at hz
        obtain ⟨z₁, z₂, z₃⟩ := IMach.step_rest hz
        rw [eths] at z₃
        rw [z₁, z₂, z₃, hb0]
        exact ih
      · have hb1 := XMach.stepTally_busy_cost hz
        have hc := IMach.stepCost_le hb ok (σ i)
        rw [eths, emem] at hc
        have hm := Nat.mul_le_mul_left
          (threadOf ((XMach.init X nt).trace xs σ i).1.ths (σ i)).fin
          (Nat.mul_le_mul_left 2 hA)
        rw [hb1, Nat.mul_add (C + D + 7), Nat.add_mul ((XMach.init X nt).packs xs σ i)]
        omega
  intro i
  have k := key i
  have hp := Nat.mul_le_mul_right (2 * (X.agents.length + (C - 2) * n))
    (XMach.packs_le_claims (xs := xs) X nt σ i)
  rw [Nat.mul_comm (2 * (X.agents.length + (C - 2) * n))]
  omega

/-- **What an action costs on the indexed memory, told from the lists**:
the cost of `IMach.cost`, with the lookups done in the lists that the maps
stand for and the length of the log given. -/
def XMach.icost (xs : XSys S) (X : XNet S) (ℓ : Nat) (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | _ :: _ => 2
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then
      2 + if (assoc c.1 X.agents).isSome then 0 else 1 + findCells p (nbOf X.wires c)
    else 2 + findCells p (nbOf X.wires c)
  | .ready a _ α _ => 2 + if assoc a X.agents = some α then 1 else 0
  | .half a b α β =>
    2 + if assoc b X.agents = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 1 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 2
      else 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1 + ℓ + X.agents.length

/-- The length of the log after an action, told from the lists. -/
def XMach.ilog (xs : XSys S) (X : XNet S) (ℓ : Nat) (T : XThread S) : Nat :=
  match T.st with
  | .idle => ℓ
  | .look _ _ => ℓ
  | .seek _ _ _ _ => ℓ
  | .ready _ _ _ _ => ℓ
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some _ => ℓ
    | none => ℓ + 1
  | .write (_ :: _) _ => ℓ + 1
  | .write [] (_ :: _) => ℓ
  | .write [] [] => X.agents.length

/-- The cost told from the lists is the cost on the indexed memory. -/
theorem IMach.cost_shadow (xs : XSys S) {H : IMem S} (h : H.Ok) (T : XThread S) :
    IMach.cost xs H T = XMach.icost xs H.toX H.log.length T := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => rfl
    | cons e rest => rfl
  | look a α => rfl
  | seek a α p c =>
    show (if c.2 = 0 then 2 + (if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c))
      else 2 + findCells p (H.nb c)) = _
    rw [h.sym c.1, h.nbrs c]
    rfl
  | ready a b α β =>
    show (2 + if H.sym a = some α then 1 else 0) = _
    rw [h.sym a]
    rfl
  | half a b α β =>
    unfold IMach.cost XMach.icost
    dsimp only
    rw [h.sym b]
  | write as ls =>
    cases as with
    | cons e as => rfl
    | nil =>
      cases ls with
      | cons e ls => rfl
      | nil =>
        show 1 + H.log.length + H.pack.log.length = 1 + H.log.length + H.toX.agents.length
        rw [H.pack_length]

/-- The log told from the lists is the log of the indexed memory. -/
theorem IMach.act_shadow (xs : XSys S) {H : IMem S} (h : H.Ok) (T : XThread S) :
    (IMach.act xs H T).1.log.length = XMach.ilog xs H.toX H.log.length T := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => rfl
    | cons e rest =>
      unfold IMach.act
      dsimp only
      split <;> rfl
  | look a α =>
    unfold IMach.act
    dsimp only
    split <;> rfl
  | seek a α p c =>
    unfold IMach.act
    dsimp only
    split
    · split <;> rfl
    · split <;> rfl
  | ready a b α β =>
    unfold IMach.act
    dsimp only
    split <;> rfl
  | half a b α β =>
    unfold IMach.act XMach.ilog
    dsimp only
    rw [h.sym b]
    cases (if assoc b H.toX.agents = some β ∧ a ≠ b then xs.rule α β else none) <;> rfl
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      rfl
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        rfl
      | nil => exact H.pack_length

/-- The part of the time on the indexed memory that goes to taking the
agents afresh. -/
def IMach.fresh (xs : XSys S) (σ : Nat → Nat) (M : IMach S) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    IMach.fresh xs σ M i +
      (threadOf (M.trace xs σ i).1.ths (σ i)).fin * (M.trace xs σ i).1.stepCost xs (σ i)

/-- **A run on the indexed memory, told from the lists**: what the first
`i` actions cost, the length of the log after them, and the part of the
cost that went to taking the agents afresh, computed along the run of the
program on lists from the length of the log at the start. -/
def XMach.shadow (xs : XSys S) (σ : Nat → Nat) (M : XMach S) (ℓ₀ : Nat) :
    Nat → Nat × Nat × Nat
  | 0 => (0, ℓ₀, 0)
  | i + 1 =>
    match (M.trace xs σ i).1.ths[σ i]? with
    | some T =>
      ((XMach.shadow xs σ M ℓ₀ i).1 +
          XMach.icost xs (M.trace xs σ i).1.mem (XMach.shadow xs σ M ℓ₀ i).2.1 T,
        XMach.ilog xs (M.trace xs σ i).1.mem (XMach.shadow xs σ M ℓ₀ i).2.1 T,
        (XMach.shadow xs σ M ℓ₀ i).2.2 +
          T.st.fin * XMach.icost xs (M.trace xs σ i).1.mem (XMach.shadow xs σ M ℓ₀ i).2.1 T)
    | none => XMach.shadow xs σ M ℓ₀ i

/-- **The indexed time can be computed on lists.**  On every run from a
well-formed net in which no agent is listed twice, the time of the indexed
program, the length of its log and the part of the time that goes to
taking the agents afresh are what `XMach.shadow` computes along the run of
the program on lists.  Hashing does not enter, so the kernel can evaluate
it. -/
theorem IMach.time_shadow {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (IMach.init X nt).time xs σ i =
        ((XMach.init X nt).shadow xs σ X.agents.length i).1 ∧
      ((IMach.init X nt).trace xs σ i).1.mem.log.length =
        ((XMach.init X nt).shadow xs σ X.agents.length i).2.1 ∧
      (IMach.init X nt).fresh xs σ i =
        ((XMach.init X nt).shadow xs σ X.agents.length i).2.2
  | 0 => ⟨rfl, (IMem.ofX_toX hnd).2.2, rfl⟩
  | i + 1 => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := IMach.time_shadow hX hnd hnt σ i
    obtain ⟨a, -, ok⟩ := IMach.init_sim (xs := xs) hX hnd hnt σ i
    have eths : ((IMach.init X nt).trace xs σ i).1.ths =
        ((XMach.init X nt).trace xs σ i).1.ths := congrArg XMach.ths a
    have emem : ((IMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    cases hT : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
    | none =>
      have hT' : ((IMach.init X nt).trace xs σ i).1.ths[σ i]? = none := by
        rw [eths]
        exact hT
      have es : (XMach.init X nt).shadow xs σ X.agents.length (i + 1) =
          (XMach.init X nt).shadow xs σ X.agents.length i := by
        show (match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
          | some T => _
          | none => (XMach.init X nt).shadow xs σ X.agents.length i) = _
        rw [hT]
      have e₁ : ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = 0 := by
        unfold IMach.stepCost
        rw [hT']
      have e₂ : ((IMach.init X nt).trace xs σ i).1.step xs (σ i) =
          (((IMach.init X nt).trace xs σ i).1, 0) := by
        unfold IMach.step
        rw [hT']
      rw [es]
      refine ⟨?_, ?_, ?_⟩
      · show (IMach.init X nt).time xs σ i +
          ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [e₁, ih₁]
        rfl
      · show (((IMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.log.length = _
        rw [e₂]
        exact ih₂
      · show (IMach.init X nt).fresh xs σ i +
          (threadOf ((IMach.init X nt).trace xs σ i).1.ths (σ i)).fin *
            ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [e₁, ih₃]
        rfl
    | some T =>
      have hT' : ((IMach.init X nt).trace xs σ i).1.ths[σ i]? = some T := by
        rw [eths]
        exact hT
      have es : (XMach.init X nt).shadow xs σ X.agents.length (i + 1) =
          (((XMach.init X nt).shadow xs σ X.agents.length i).1 +
              XMach.icost xs ((XMach.init X nt).trace xs σ i).1.mem
                ((XMach.init X nt).shadow xs σ X.agents.length i).2.1 T,
            XMach.ilog xs ((XMach.init X nt).trace xs σ i).1.mem
              ((XMach.init X nt).shadow xs σ X.agents.length i).2.1 T,
            ((XMach.init X nt).shadow xs σ X.agents.length i).2.2 +
              T.st.fin * XMach.icost xs ((XMach.init X nt).trace xs σ i).1.mem
                ((XMach.init X nt).shadow xs σ X.agents.length i).2.1 T) := by
        show (match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
          | some T =>
            (((XMach.init X nt).shadow xs σ X.agents.length i).1 +
                XMach.icost xs ((XMach.init X nt).trace xs σ i).1.mem
                  ((XMach.init X nt).shadow xs σ X.agents.length i).2.1 T,
              XMach.ilog xs ((XMach.init X nt).trace xs σ i).1.mem
                ((XMach.init X nt).shadow xs σ X.agents.length i).2.1 T,
              ((XMach.init X nt).shadow xs σ X.agents.length i).2.2 +
                T.st.fin * XMach.icost xs ((XMach.init X nt).trace xs σ i).1.mem
                  ((XMach.init X nt).shadow xs σ X.agents.length i).2.1 T)
          | none => (XMach.init X nt).shadow xs σ X.agents.length i) = _
        rw [hT]
      have e₁ : ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) =
          IMach.cost xs ((IMach.init X nt).trace xs σ i).1.mem T := by
        unfold IMach.stepCost
        rw [hT']
      have e₂ : ((IMach.init X nt).trace xs σ i).1.step xs (σ i) =
          (⟨(IMach.act xs ((IMach.init X nt).trace xs σ i).1.mem T).1,
            ((IMach.init X nt).trace xs σ i).1.ths.set (σ i)
              (IMach.act xs ((IMach.init X nt).trace xs σ i).1.mem T).2.1⟩,
            (IMach.act xs ((IMach.init X nt).trace xs σ i).1.mem T).2.2) := by
        unfold IMach.step
        rw [hT']
      have c₁ := IMach.cost_shadow xs ok T
      have c₂ := IMach.act_shadow xs ok T
      rw [emem, ih₂] at c₁ c₂
      rw [es]
      refine ⟨?_, ?_, ?_⟩
      · show (IMach.init X nt).time xs σ i +
          ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [e₁, c₁, ih₁]
      · show (((IMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.log.length = _
        rw [e₂]
        exact c₂
      · show (IMach.init X nt).fresh xs σ i +
          (threadOf ((IMach.init X nt).trace xs σ i).1.ths (σ i)).fin *
            ((IMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [threadOf_eq hT', e₁, c₁, ih₃]

/-- Once the program is at rest its time on the indexed memory stays what
it is. -/
theorem IMach.time_rest {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {B : Nat} (h : ((XMach.init X nt).trace xs σ B).1.resting = true) :
    ∀ d, (IMach.init X nt).time xs σ (B + d) = (IMach.init X nt).time xs σ B
  | 0 => rfl
  | d + 1 => by
    obtain ⟨a, -, -⟩ := IMach.init_sim (xs := xs) hX hnd hnt σ (B + d)
    have hz := XMach.stepCost_rest (xs := xs) (XMach.resting_trace σ h d) (σ (B + d))
    rw [← a] at hz
    show (IMach.init X nt).time xs σ (B + d) +
      ((IMach.init X nt).trace xs σ (B + d)).1.stepCost xs (σ (B + d)) = _
    rw [(IMach.step_rest hz).1, Nat.add_zero]
    exact IMach.time_rest hX hnd hnt σ h d

end Indexed

end INet
