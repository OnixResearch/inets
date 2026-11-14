import InteractionNets.Indexed

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### Lazy lists for the program with threads

On the indexed memory a thread that has written a right-hand side reads
the whole log to take the agents afresh, and on a long run that is where
the time goes.  Here it takes the log as it stands and notes the time.  A
third map says when each dead cell died, so that the thread can tell, when
it comes to a cell, whether the cell was dead already when it took the
list; such cells it drops.  The log is never packed.  The program is
proved to do, action by action, what the program on lists does. -/

section Lazy

variable [DecidableEq S]

/-- Let the clock of the memory tick. -/
def IMem.tick (H : IMem S) : IMem S :=
  ⟨H.log, H.stamp + 1, H.live, H.free, H.wires, H.nbrs⟩

omit [DecidableEq S] in
theorem IMem.Ok.tick {H : IMem S} (h : H.Ok) : H.tick.Ok :=
  ⟨fun e he => Nat.lt_succ_of_lt (h.lt e he), h.mem, h.nbrs⟩

theorem IMem.Ok.live_none {H : IMem S} (h : H.Ok) {i : Id}
    (hi : assoc i H.toX.agents = none) : H.live[i]? = none := by
  have e := h.sym i
  rw [hi] at e
  cases hl : H.live[i]? with
  | none => rfl
  | some v =>
    have e' : (H.live[i]?).map (·.2) = none := e
    rw [hl] at e'
    cases e'

/-- **A memory with lazy lists**: the indexed memory, never packed, with a
third map that says when each dead cell of the log died.  The stamp of the
memory serves as a clock: it ticks whenever an agent is written or taken
out. -/
structure LMem (S : Type) where
  core : IMem S
  dead : Std.HashMap Nat Nat

/-- The memory of lists that it stands for. -/
abbrev LMem.toX (L : LMem S) : XNet S := L.core.toX

/-- Was the cell not dead yet when the clock stood at `t₀`? -/
def LMem.seen (L : LMem S) (t₀ : Nat) (c : Nat × Id × S) : Bool :=
  match L.dead[c.1]? with
  | none => true
  | some d => decide (t₀ ≤ d)

/-- Take an agent out: one erasure, and a note of the time. -/
def LMem.take (L : LMem S) (a : Id) : LMem S :=
  ⟨(L.core.take a).tick,
    match L.core.live[a]? with
    | some v => L.dead.insert v.1 L.core.stamp
    | none => L.dead⟩

/-- Write an agent. -/
def LMem.put (L : LMem S) (i : Id) (γ : S) : LMem S := ⟨L.core.put i γ, L.dead⟩

/-- Write a segment. -/
def LMem.link (L : LMem S) (p q : Port) : LMem S := ⟨L.core.link p q, L.dead⟩

/-- The maps say what the lists say; no two cells of the log have the same
stamp; a death is noted for a cell that was written before, at a time that
has passed; and the cells without a noted death are the live ones. -/
structure LMem.Ok (L : LMem S) : Prop where
  core : L.core.Ok
  uniq : ∀ c, c ∈ L.core.log → ∀ c', c' ∈ L.core.log → c.1 = c'.1 → c = c'
  born : ∀ s d, L.dead[s]? = some d → s < L.core.stamp ∧ d < L.core.stamp
  gone : ∀ s i γ, (s, i, γ) ∈ L.core.log →
    (L.core.live[i]? = some (s, γ) ↔ L.dead[s]? = none)

omit [DecidableEq S] in
theorem LMem.take_dead_none {L : LMem S} {a : Id} (hl : L.core.live[a]? = none) :
    (L.take a).dead = L.dead := by
  show (match L.core.live[a]? with
    | some v => L.dead.insert v.1 L.core.stamp
    | none => L.dead) = _
  rw [hl]

omit [DecidableEq S] in
theorem LMem.take_dead_some {L : LMem S} {a : Id} {s₀ : Nat} {γ₀ : S}
    (hl : L.core.live[a]? = some (s₀, γ₀)) :
    (L.take a).dead = L.dead.insert s₀ L.core.stamp := by
  show (match L.core.live[a]? with
    | some v => L.dead.insert v.1 L.core.stamp
    | none => L.dead) = _
  rw [hl]

omit [DecidableEq S] in
theorem LMem.Ok.take {L : LMem S} (h : L.Ok) (a : Id) : (L.take a).Ok := by
  have hlive : ∀ j, (L.take a).core.live[j]? = if a = j then none else L.core.live[j]? :=
    fun j => by
      show (L.core.live.erase a)[j]? = _
      rw [hget_erase]
  cases hl : L.core.live[a]? with
  | none =>
    have hd := LMem.take_dead_none hl
    refine ⟨(h.core.take a).tick, h.uniq, fun s d hs => ?_, fun s i γ hc => ?_⟩
    · rw [hd] at hs
      obtain ⟨h1, h2⟩ := h.born s d hs
      exact ⟨Nat.lt_succ_of_lt h1, Nat.lt_succ_of_lt h2⟩
    · rw [hlive i, hd]
      by_cases e : a = i
      · rw [ite_pos' e]
        have hn : ¬ L.core.live[i]? = some (s, γ) := by
          rw [← e, hl]
          exact fun h' => by cases h'
        exact ⟨fun h' => (by cases h'), fun h' => absurd ((h.gone s i γ hc).2 h') hn⟩
      · rw [ite_neg' e]
        exact h.gone s i γ hc
  | some v =>
    obtain ⟨s₀, γ₀⟩ := v
    have hd := LMem.take_dead_some hl
    have hc₀ : (s₀, a, γ₀) ∈ L.core.log := h.core.mem a s₀ γ₀ hl
    refine ⟨(h.core.take a).tick, h.uniq, fun s d hs => ?_, fun s i γ hc => ?_⟩
    · rw [hd, hget_insert] at hs
      by_cases e : s₀ = s
      · rw [ite_pos' e] at hs
        cases hs
        exact ⟨e ▸ Nat.lt_succ_of_lt (h.core.lt _ hc₀), Nat.lt_succ_self _⟩
      · rw [ite_neg' e] at hs
        obtain ⟨h1, h2⟩ := h.born s d hs
        exact ⟨Nat.lt_succ_of_lt h1, Nat.lt_succ_of_lt h2⟩
    · rw [hlive i, hd, hget_insert]
      by_cases e : a = i
      · rw [ite_pos' e]
        refine ⟨fun h' => (by cases h'), fun h' => ?_⟩
        by_cases e' : s₀ = s
        · rw [ite_pos' e'] at h'
          cases h'
        · rw [ite_neg' e'] at h'
          have hl' := (h.gone s i γ hc).2 h'
          rw [← e, hl] at hl'
          cases hl'
          exact absurd rfl e'
      · rw [ite_neg' e]
        have e' : ¬ s₀ = s := fun es => by
          have hcc := h.uniq _ hc₀ _ hc es
          cases hcc
          exact e rfl
        rw [ite_neg' e']
        exact h.gone s i γ hc

theorem LMem.Ok.put {L : LMem S} (h : L.Ok) {i : Id} (hi : assoc i L.toX.agents = none)
    (γ : S) : (L.put i γ).Ok := by
  have hn : L.core.live[i]? = none := h.core.live_none hi
  have hlive : ∀ j, (L.put i γ).core.live[j]? =
      if i = j then some (L.core.stamp, γ) else L.core.live[j]? := fun j => by
    show (L.core.live.insert i (L.core.stamp, γ))[j]? = _
    rw [hget_insert]
  refine ⟨h.core.put i γ, fun c hc c' hc' e => ?_, fun s d hs => ?_, fun s j δ hc => ?_⟩
  · rcases List.mem_cons.1 hc with rfl | hc
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · rfl
      · have := h.core.lt c' hc'
        have e' : L.core.stamp = c'.1 := e
        omega
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · have := h.core.lt c hc
        have e' : c.1 = L.core.stamp := e
        omega
      · exact h.uniq c hc c' hc' e
  · obtain ⟨h1, h2⟩ := h.born s d hs
    exact ⟨Nat.lt_succ_of_lt h1, Nat.lt_succ_of_lt h2⟩
  · have hdead : (L.put i γ).dead[s]? = L.dead[s]? := rfl
    rw [hlive j, hdead]
    rcases List.mem_cons.1 hc with e | hc
    · cases e
      rw [ite_pos' rfl]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      cases hd : L.dead[L.core.stamp]? with
      | none => rfl
      | some d => exact absurd (h.born _ d hd).1 (Nat.lt_irrefl _)
    · have hs : s < L.core.stamp := h.core.lt _ hc
      by_cases e : i = j
      · rw [ite_pos' e]
        refine ⟨fun h' => ?_, fun h' => ?_⟩
        · cases h'
          exact absurd hs (Nat.lt_irrefl _)
        · have hl := (h.gone s j δ hc).2 h'
          rw [← e, hn] at hl
          cases hl
      · rw [ite_neg' e]
        exact h.gone s j δ hc

omit [DecidableEq S] in
theorem LMem.Ok.link {L : LMem S} (h : L.Ok) (p q : Port) : (L.link p q).Ok :=
  ⟨h.core.link p q, h.uniq, h.born, h.gone⟩

omit [DecidableEq S] in
/-- A death noted now does not change what an earlier clock saw. -/
theorem LMem.seen_take {L : LMem S} (h : L.Ok) (a : Id) {t₀ : Nat} (ht : t₀ ≤ L.core.stamp)
    (c : Nat × Id × S) : (L.take a).seen t₀ c = L.seen t₀ c := by
  cases hl : L.core.live[a]? with
  | none =>
    show (match (L.take a).dead[c.1]? with
      | none => true
      | some d => decide (t₀ ≤ d)) = _
    rw [LMem.take_dead_none hl]
    rfl
  | some v =>
    obtain ⟨s₀, γ₀⟩ := v
    have hc₀ := h.core.mem a s₀ γ₀ hl
    have hd₀ : L.dead[s₀]? = none := (h.gone s₀ a γ₀ hc₀).1 hl
    show (match (L.take a).dead[c.1]? with
      | none => true
      | some d => decide (t₀ ≤ d)) = (match L.dead[c.1]? with
      | none => true
      | some d => decide (t₀ ≤ d))
    rw [LMem.take_dead_some hl, hget_insert]
    by_cases e : s₀ = c.1
    · rw [ite_pos' e, ← e, hd₀]
      exact decide_eq_true ht
    · rw [ite_neg' e]

/-- What the clock sees now is what is live. -/
theorem LMem.seen_now {L : LMem S} (h : L.Ok) :
    ∀ c, c ∈ L.core.log → L.seen L.core.stamp c = L.core.isLive c := by
  intro c hc
  obtain ⟨s, i, γ⟩ := c
  have g := h.gone s i γ hc
  show (match L.dead[s]? with
    | none => true
    | some d => decide (L.core.stamp ≤ d)) = decide (L.core.live[i]? = some (s, γ))
  cases hd : L.dead[s]? with
  | none => exact (decide_eq_true (g.2 hd)).symm
  | some d =>
    have hlt := (h.born s d hd).2
    have hn : ¬ L.core.live[i]? = some (s, γ) := fun hl => by
      have := g.1 hl
      rw [hd] at this
      cases this
    show decide (L.core.stamp ≤ d) = _
    rw [decide_eq_false (Nat.not_le.2 hlt), decide_eq_false hn]

/-- One memory keeps what another saw: its clock is not behind, and every
earlier clock sees in it what it saw. -/
structure LMem.Keeps (L L' : LMem S) : Prop where
  stamp : L.core.stamp ≤ L'.core.stamp
  seen : ∀ t₀, t₀ ≤ L.core.stamp → ∀ c, L'.seen t₀ c = L.seen t₀ c

omit [DecidableEq S] in
theorem LMem.Keeps.refl (L : LMem S) : L.Keeps L := ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

omit [DecidableEq S] in
theorem LMem.Keeps.take {L : LMem S} (h : L.Ok) (a : Id) : L.Keeps (L.take a) :=
  ⟨Nat.le_succ _, fun _ ht c => LMem.seen_take h a ht c⟩

omit [DecidableEq S] in
theorem LMem.Keeps.put (L : LMem S) (i : Id) (γ : S) : L.Keeps (L.put i γ) :=
  ⟨Nat.le_succ _, fun _ _ _ => rfl⟩

omit [DecidableEq S] in
theorem LMem.Keeps.link (L : LMem S) (p q : Port) : L.Keeps (L.link p q) :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

omit [DecidableEq S] in
theorem IMem.links_live (H₀ : IMem S) : ∀ ws : List (Port × Port),
    (ws.foldr (fun e H => H.link e.1 e.2) H₀).live = H₀.live ∧
      (ws.foldr (fun e H => H.link e.1 e.2) H₀).stamp = H₀.stamp
  | [] => ⟨rfl, rfl⟩
  | _ :: ws => IMem.links_live H₀ ws

/-- In the indexed memory of a net every cell of the log is live, no two
have the same stamp, and the log lists the agents. -/
theorem IMem.ofX_cells (free : List Port) : ∀ l : List (Id × S), (l.map Prod.fst).Nodup →
    (∀ c, c ∈ (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).log →
      ∀ c', c' ∈ (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).log →
        c.1 = c'.1 → c = c') ∧
    (∀ s i γ, (s, i, γ) ∈ (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).log →
      (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).live[i]? = some (s, γ)) ∧
    (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).log.map (·.2) = l
  | [], _ => ⟨fun _ hc => (by cases hc), fun _ _ _ hc => (by cases hc), rfl⟩
  | (i, γ) :: l, hnd => by
    have hnd' : i ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    obtain ⟨ok, e, -⟩ := IMem.ofX_agents free l hnd'.2
    obtain ⟨u, lv, mp⟩ := IMem.ofX_cells free l hnd'.2
    have hi : assoc i (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).toX.agents =
        none := by
      rw [e]
      exact assoc_none_of_not_mem i l hnd'.1
    have hn := ok.live_none hi
    refine ⟨fun c hc c' hc' ee => ?_, fun s j δ hc => ?_, ?_⟩
    · rcases List.mem_cons.1 hc with rfl | hc
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · rfl
        · have := ok.lt c' hc'
          have e' : (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).stamp = c'.1 := ee
          omega
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · have := ok.lt c hc
          have e' : c.1 = (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).stamp := ee
          omega
        · exact u c hc c' hc' ee
    · show ((l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).live.insert i
        ((l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).stamp, γ))[j]? = some (s, δ)
      rw [hget_insert]
      rcases List.mem_cons.1 hc with ee | hc
      · cases ee
        rw [ite_pos' rfl]
      · have hl := lv s j δ hc
        have ne : ¬ i = j := fun ee => by
          rw [← ee, hn] at hl
          cases hl
        rw [ite_neg' ne]
        exact hl
    · show (i, γ) :: (l.foldr (fun e H => H.put e.1 e.2) (IMem.empty free)).log.map (·.2) = _
      rw [mp]

/-- The lazy memory of a net. -/
def LMem.ofX (X : XNet S) : LMem S := ⟨IMem.ofX X, ∅⟩

theorem LMem.ofX_ok {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) :
    (LMem.ofX X).Ok ∧ (IMem.ofX X).log.map (·.2) = X.agents := by
  obtain ⟨ok, -, -⟩ := IMem.ofX_toX hnd
  obtain ⟨u, lv, mp⟩ := IMem.ofX_cells X.free X.agents hnd
  obtain ⟨-, -, lg⟩ := IMem.ofX_links
    (X.agents.foldr (fun e H => H.put e.1 e.2) (IMem.empty X.free))
    (IMem.ofX_agents X.free X.agents hnd).1 X.wires
  obtain ⟨lvv, -⟩ := IMem.links_live
    (X.agents.foldr (fun e H => H.put e.1 e.2) (IMem.empty X.free)) X.wires
  have elog : (IMem.ofX X).log =
      (X.agents.foldr (fun e H => H.put e.1 e.2) (IMem.empty X.free)).log := lg
  have elive : (IMem.ofX X).live =
      (X.agents.foldr (fun e H => H.put e.1 e.2) (IMem.empty X.free)).live := lvv
  have hempty : ∀ s : Nat, (LMem.ofX X).dead[s]? = none := fun s => by
    show (∅ : Std.HashMap Nat Nat)[s]? = none
    exact Std.HashMap.getElem?_empty
  refine ⟨⟨ok, ?_, fun s d hs => ?_, fun s i γ hc => ?_⟩, ?_⟩
  · show ∀ c, c ∈ (IMem.ofX X).log → ∀ c', c' ∈ (IMem.ofX X).log → c.1 = c'.1 → c = c'
    rw [elog]
    exact u
  · rw [hempty s] at hs
    cases hs
  · have hc' : (s, i, γ) ∈ (IMem.ofX X).log := hc
    rw [elog] at hc'
    have hl : (IMem.ofX X).live[i]? = some (s, γ) := by
      rw [elive]
      exact lv s i γ hc'
    exact ⟨fun _ => hempty s, fun _ => hl⟩
  · rw [elog]
    exact mp

/-- Dropping the cells at the front that fail a test leaves a list with
nothing that passes, or one that starts with the first cell that passes. -/
theorem dropWhile_not_spec {A : Type} (p : A → Bool) : ∀ l : List A,
    (l.dropWhile (fun c => !p c) = [] ∧ l.filter p = []) ∨
      ∃ c rest, l.dropWhile (fun c => !p c) = c :: rest ∧ p c = true ∧
        l.filter p = c :: rest.filter p
  | [] => .inl ⟨rfl, rfl⟩
  | x :: l => by
    by_cases hx : p x = true
    · refine .inr ⟨x, l, ?_, hx, List.filter_cons_of_pos hx⟩
      exact List.dropWhile_cons_of_neg (by simpa using hx)
    · have e₁ : (x :: l).dropWhile (fun c => !p c) = l.dropWhile (fun c => !p c) :=
        List.dropWhile_cons_of_pos (by simpa using hx)
      have e₂ : (x :: l).filter p = l.filter p := List.filter_cons_of_neg hx
      rw [e₁, e₂]
      exact dropWhile_not_spec p l

/-- **A thread with a lazy list**: the cells still to try, as they stood in
the log when the thread took them, the time at which it took them, and its
state.  A cell that was dead by then is not one the thread is to try; it
finds that out when it comes to the cell. -/
structure LThread (S : Type) where
  raw : List (Nat × Id × S)
  snap : Nat
  st : TState S

/-- The thread gives up an attempt. -/
def LThread.fail (T : LThread S) : LThread S := ⟨T.raw, T.snap, .idle⟩

/-- The thread of the program on lists that it stands for: its list is the
cells that were not dead when it took them. -/
def LThread.toX (L : LMem S) (T : LThread S) : XThread S :=
  ⟨(T.raw.filter (L.seen T.snap)).map (·.2), T.st⟩

omit [DecidableEq S] in
/-- What a thread stands for does not change when the memory keeps what its
clock saw. -/
theorem LThread.toX_keeps {L L' : LMem S} (k : L.Keeps L') {T : LThread S}
    (hT : T.snap ≤ L.core.stamp) : T.toX L' = T.toX L := by
  have e : L'.seen T.snap = L.seen T.snap := funext (k.seen T.snap hT)
  show (⟨(T.raw.filter (L'.seen T.snap)).map (·.2), T.st⟩ : XThread S) =
    ⟨(T.raw.filter (L.seen T.snap)).map (·.2), T.st⟩
  rw [e]

/-- **One action of a thread with a lazy list.**  The action of the
indexed program, except in two places.  An idle thread first drops the
cells at the front of its list that were dead when it took the list.  A
thread that has written a right-hand side takes the log as it is, with the
time, and reads none of it. -/
def LMach.act (xs : XSys S) (L : LMem S) (T : LThread S) : LMem S × LThread S × Nat :=
  match T.st with
  | .idle =>
    match T.raw.dropWhile (fun c => !L.seen T.snap c) with
    | [] => (L, ⟨[], T.snap, .idle⟩, 0)
    | c :: rest =>
      if L.core.sym c.2.1 = some c.2.2 then (L, ⟨rest, T.snap, .look c.2.1 c.2.2⟩, 0)
      else (L, ⟨rest, T.snap, .idle⟩, 0)
  | .look a α =>
    match (L.core.nb (a, 0)).head? with
    | some q => (L, ⟨T.raw, T.snap, .seek a α (a, 0) q⟩, 0)
    | none => (L, T.fail, 0)
  | .seek a α p c =>
    match (if c.2 = 0 then L.core.sym c.1 else none) with
    | some β =>
      if a ≠ c.1 ∧ (xs.rule α β).isSome then (L, ⟨T.raw, T.snap, .ready a c.1 α β⟩, 0)
      else (L, T.fail, 0)
    | none =>
      match (L.core.nb c).find? (fun q => decide (q ≠ p)) with
      | some q => (L, ⟨T.raw, T.snap, .seek a α c q⟩, 0)
      | none => (L, T.fail, 0)
  | .ready a b α β =>
    if L.core.sym a = some α then (L.take a, ⟨T.raw, T.snap, .half a b α β⟩, 0)
    else (L, T.fail, 0)
  | .half a b α β =>
    match (if L.core.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (L.take b,
        ⟨T.raw, T.snap, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1)
    | none => (L.put a α, T.fail, 0)
  | .write ((i, γ) :: as) ls => (L.put i γ, ⟨T.raw, T.snap, .write as ls⟩, 0)
  | .write [] ((p, q) :: ls) => (L.link p q, ⟨T.raw, T.snap, .write [] ls⟩, 0)
  | .write [] [] => (L, ⟨L.core.log, L.core.stamp, .idle⟩, 0)

/-- **The lazy action is the action of the program.**  On a memory whose
maps are right, for a thread that took its list no later than now, the
action does to the memory of lists what the program does, leaves the
thread standing for the thread of the program, claims as often, keeps the
maps right, and keeps what every earlier clock saw, so that the other
threads stand for what they stood for. -/
theorem LMach.act_sim (xs : XSys S) {L : LMem S} (h : L.Ok) (T : LThread S)
    (hT : T.snap ≤ L.core.stamp)
    (hnd : ((XMach.act xs L.toX (T.toX L)).1.agents.map Prod.fst).Nodup) :
    (LMach.act xs L T).1.toX = (XMach.act xs L.toX (T.toX L)).1 ∧
      (LMach.act xs L T).2.1.toX (LMach.act xs L T).1 = (XMach.act xs L.toX (T.toX L)).2.1 ∧
      (LMach.act xs L T).2.2 = (XMach.act xs L.toX (T.toX L)).2.2 ∧
      (LMach.act xs L T).1.Ok ∧
      (LMach.act xs L T).2.1.snap ≤ (LMach.act xs L T).1.core.stamp ∧
      L.Keeps (LMach.act xs L T).1 := by
  obtain ⟨raw, snap, s⟩ := T
  have hT' : snap ≤ L.core.stamp := hT
  cases s with
  | idle =>
    rcases dropWhile_not_spec (L.seen snap) raw with ⟨hd, hf⟩ | ⟨c, rest, hd, -, hf⟩
    · have eL : LMach.act xs L ⟨raw, snap, .idle⟩ = (L, ⟨[], snap, .idle⟩, 0) := by
        unfold LMach.act
        dsimp only
        rw [hd]
      have eT : LThread.toX L ⟨raw, snap, .idle⟩ = ⟨[], .idle⟩ := by
        show (⟨(raw.filter (L.seen snap)).map (·.2), .idle⟩ : XThread S) = _
        rw [hf]
        rfl
      rw [eL, eT]
      exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
    · have eL : LMach.act xs L ⟨raw, snap, .idle⟩ =
          (if L.core.sym c.2.1 = some c.2.2 then (L, ⟨rest, snap, .look c.2.1 c.2.2⟩, 0)
            else (L, ⟨rest, snap, .idle⟩, 0)) := by
        unfold LMach.act
        dsimp only
        rw [hd]
      have eT : LThread.toX L ⟨raw, snap, .idle⟩ =
          ⟨c.2 :: (rest.filter (L.seen snap)).map (·.2), .idle⟩ := by
        show (⟨(raw.filter (L.seen snap)).map (·.2), .idle⟩ : XThread S) = _
        rw [hf]
        rfl
      have eX : XMach.act xs L.toX ⟨c.2 :: (rest.filter (L.seen snap)).map (·.2), .idle⟩ =
          (if assoc c.2.1 L.toX.agents = some c.2.2 then
            (L.toX, ⟨(rest.filter (L.seen snap)).map (·.2), .look c.2.1 c.2.2⟩, 0)
          else (L.toX, ⟨(rest.filter (L.seen snap)).map (·.2), .idle⟩, 0)) := rfl
      rw [eL, eT, eX, h.core.sym c.2.1]
      by_cases hs : assoc c.2.1 L.toX.agents = some c.2.2
      · rw [ite_pos' hs, ite_pos' hs]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
      · rw [ite_neg' hs, ite_neg' hs]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
  | look a α =>
    have eT : LThread.toX L ⟨raw, snap, .look a α⟩ =
        ⟨(raw.filter (L.seen snap)).map (·.2), .look a α⟩ := rfl
    rw [eT]
    unfold LMach.act XMach.act
    dsimp only
    rw [h.core.first (a, 0)]
    cases assoc (a, 0) L.core.toX.wires <;>
      exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
  | seek a α p c =>
    have eT : LThread.toX L ⟨raw, snap, .seek a α p c⟩ =
        ⟨(raw.filter (L.seen snap)).map (·.2), .seek a α p c⟩ := rfl
    rw [eT]
    unfold LMach.act XMach.act
    dsimp only
    rw [h.core.sym c.1, h.core.next c p]
    cases (if c.2 = 0 then assoc c.1 L.core.toX.agents else none) with
    | some β =>
      dsimp only
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β).isSome
      · rw [ite_pos' hc, ite_pos' hc]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
      · rw [ite_neg' hc, ite_neg' hc]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
    | none =>
      dsimp only
      cases nextSeg L.core.toX.wires c p <;>
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
  | ready a b α β =>
    have eT : LThread.toX L ⟨raw, snap, .ready a b α β⟩ =
        ⟨(raw.filter (L.seen snap)).map (·.2), .ready a b α β⟩ := rfl
    rw [eT]
    unfold LMach.act XMach.act
    dsimp only
    rw [h.core.sym a]
    by_cases hc : assoc a L.core.toX.agents = some α
    · rw [ite_pos' hc, ite_pos' hc]
      exact ⟨L.core.toX_take a, LThread.toX_keeps (.take h a) hT', rfl, h.take a,
        Nat.le_succ_of_le hT', .take h a⟩
    · rw [ite_neg' hc, ite_neg' hc]
      exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl L⟩
  | half a b α β =>
    have eT : LThread.toX L ⟨raw, snap, .half a b α β⟩ =
        ⟨(raw.filter (L.seen snap)).map (·.2), .half a b α β⟩ := rfl
    rw [eT] at hnd ⊢
    unfold XMach.act at hnd
    dsimp only at hnd
    unfold LMach.act XMach.act
    dsimp only
    rw [h.core.sym b]
    cases hR : (if assoc b L.core.toX.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      exact ⟨L.core.toX_take b, LThread.toX_keeps (.take h b) hT', rfl, h.take b,
        Nat.le_succ_of_le hT', .take h b⟩
    | none =>
      rw [hR] at hnd
      have hi := assoc_none_of_nodup_cons hnd
      exact ⟨IMem.toX_put h.core hi α, LThread.toX_keeps (.put L a α) hT', rfl, h.put hi α,
        Nat.le_succ_of_le hT', .put L a α⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have hi := assoc_none_of_nodup_cons hnd
      exact ⟨IMem.toX_put h.core hi γ, LThread.toX_keeps (.put L i γ) hT', rfl, h.put hi γ,
        Nat.le_succ_of_le hT', .put L i γ⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨L.core.toX_link p q, LThread.toX_keeps (.link L p q) hT', rfl, h.link p q,
          hT', .link L p q⟩
      | nil =>
        refine ⟨rfl, ?_, rfl, h, Nat.le_refl _, LMem.Keeps.refl L⟩
        show (⟨(L.core.log.filter (L.seen L.core.stamp)).map (·.2), .idle⟩ : XThread S) =
          ⟨L.core.toX.agents, .idle⟩
        rw [List.filter_congr (LMem.seen_now h)]
        rfl

/-- The program with lazy lists: the memory and the threads. -/
structure LMach (S : Type) where
  mem : LMem S
  ths : List (LThread S)

/-- The program on lists that it stands for. -/
def LMach.toX (M : LMach S) : XMach S := ⟨M.mem.toX, M.ths.map (LThread.toX M.mem)⟩

/-- The maps are right and no thread took its list later than now. -/
structure LMach.Ok (M : LMach S) : Prop where
  mem : M.mem.Ok
  snap : ∀ T, T ∈ M.ths → T.snap ≤ M.mem.core.stamp

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def LMach.step (xs : XSys S) (M : LMach S) (t : Nat) : LMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(LMach.act xs M.mem T).1, M.ths.set t (LMach.act xs M.mem T).2.1⟩,
      (LMach.act xs M.mem T).2.2)
  | none => (M, 0)

/-- The run under an unending schedule: the state and the number of claims
after `i` actions. -/
def LMach.trace (xs : XSys S) (σ : Nat → Nat) (M : LMach S) : Nat → LMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((LMach.trace xs σ M i).1.step xs (σ i)).1,
      (LMach.trace xs σ M i).2 + ((LMach.trace xs σ M i).1.step xs (σ i)).2)

/-- The program before it starts.  Thread `t` has the log from its `t`-th
cell on, then the cells before it. -/
def LMach.init (X : XNet S) (n : Nat) : LMach S :=
  ⟨LMem.ofX X, (List.range n).map fun t =>
    ⟨(IMem.ofX X).log.drop t ++ (IMem.ofX X).log.take t, (IMem.ofX X).stamp, .idle⟩⟩

theorem LMach.init_ok {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (LMach.init X n).Ok := by
  refine ⟨(LMem.ofX_ok hnd).1, fun T hT => ?_⟩
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
  exact Nat.le_refl _

theorem LMach.init_toX {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (LMach.init X n).toX = XMach.init X n := by
  have hseen : ∀ (t₀ : Nat) (c : Nat × Id × S), (LMem.ofX X).seen t₀ c = true := by
    intro t₀ c
    show (match (∅ : Std.HashMap Nat Nat)[c.1]? with
      | none => true
      | some d => decide (t₀ ≤ d)) = true
    rw [Std.HashMap.getElem?_empty]
  have hlog := (LMem.ofX_ok hnd).2
  have hth : ∀ t, LThread.toX (LMem.ofX X)
      ⟨(IMem.ofX X).log.drop t ++ (IMem.ofX X).log.take t, (IMem.ofX X).stamp, .idle⟩ =
      ⟨X.agents.drop t ++ X.agents.take t, .idle⟩ := by
    intro t
    show (⟨(((IMem.ofX X).log.drop t ++ (IMem.ofX X).log.take t).filter
      ((LMem.ofX X).seen (IMem.ofX X).stamp)).map (·.2), .idle⟩ : XThread S) = _
    rw [List.filter_eq_self.2 fun c _ => hseen _ c, List.map_append, List.map_drop,
      List.map_take, hlog]
  show (⟨(IMem.ofX X).toX, ((List.range n).map _).map (LThread.toX (LMem.ofX X))⟩ :
    XMach S) = ⟨X, (List.range n).map _⟩
  rw [(IMem.ofX_toX hnd).2.1, List.map_map]
  exact congrArg (XMach.mk X) (List.map_congr_left fun t _ => hth t)

/-- One action of the lazy program is one action of the program. -/
theorem LMach.step_sim (xs : XSys S) {M : LMach S} (h : M.Ok) (t : Nat)
    (hnd : ((M.toX.step xs t).1.mem.agents.map Prod.fst).Nodup) :
    (M.step xs t).1.toX = (M.toX.step xs t).1 ∧ (M.step xs t).2 = (M.toX.step xs t).2 ∧
      (M.step xs t).1.Ok := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold LMach.step
      rw [ht]
    have ht' : M.toX.ths[t]? = none := by
      show (M.ths.map (LThread.toX M.mem))[t]? = none
      rw [List.getElem?_map, ht]
      rfl
    have e₂ : M.toX.step xs t = (M.toX, 0) := by
      unfold XMach.step
      rw [ht']
    rw [e₁, e₂]
    exact ⟨rfl, rfl, h⟩
  | some T =>
    have ht' : M.toX.ths[t]? = some (T.toX M.mem) := by
      show (M.ths.map (LThread.toX M.mem))[t]? = _
      rw [List.getElem?_map, ht]
      rfl
    have e₂ : M.toX.step xs t = (⟨(XMach.act xs M.mem.toX (T.toX M.mem)).1,
        (M.ths.map (LThread.toX M.mem)).set t (XMach.act xs M.mem.toX (T.toX M.mem)).2.1⟩,
        (XMach.act xs M.mem.toX (T.toX M.mem)).2.2) := XMach.step_eq ht' rfl
    rw [e₂] at hnd
    have hTm := List.mem_of_getElem? ht
    obtain ⟨a, b, c, d, e, k⟩ := LMach.act_sim xs h.mem T (h.snap T hTm) hnd
    have e₁ : M.step xs t = (⟨(LMach.act xs M.mem T).1,
        M.ths.set t (LMach.act xs M.mem T).2.1⟩, (LMach.act xs M.mem T).2.2) := by
      unfold LMach.step
      rw [ht]
    have em : M.ths.map (LThread.toX (LMach.act xs M.mem T).1) =
        M.ths.map (LThread.toX M.mem) :=
      List.map_congr_left fun U hU => LThread.toX_keeps k (h.snap U hU)
    rw [e₁, e₂]
    refine ⟨?_, c, d, fun U hU => ?_⟩
    · show (⟨(LMach.act xs M.mem T).1.toX,
        (M.ths.set t (LMach.act xs M.mem T).2.1).map (LThread.toX (LMach.act xs M.mem T).1)⟩ :
          XMach S) = _
      rw [List.map_set, em, a, b]
    · rcases List.mem_or_eq_of_mem_set hU with hU' | rfl
      · exact Nat.le_trans (h.snap U hU') k.stamp
      · exact e

variable {xs : XSys S}

/-- **The lazy program runs as the program does.**  From a state whose maps
are right and in which no agent is listed twice, under any schedule, after
any number of actions the lazy program stands for the state of the program
on lists and has claimed as often. -/
theorem LMach.trace_sim {M : LMach S} (h : M.Ok) (hL : M.toX.Live xs)
    (hnd : (M.toX.mem.agents.map Prod.fst).Nodup) (σ : Nat → Nat) :
    ∀ i, (M.trace xs σ i).1.toX = (M.toX.trace xs σ i).1 ∧
      (M.trace xs σ i).2 = (M.toX.trace xs σ i).2 ∧ (M.trace xs σ i).1.Ok := by
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
    obtain ⟨a', b', c'⟩ := LMach.step_sim xs c (σ i) hn
    refine ⟨?_, ?_, c'⟩
    · show ((M.trace xs σ i).1.step xs (σ i)).1.toX = ((M.toX.trace xs σ i).1.step xs (σ i)).1
      rw [a', a]
    · show (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2 =
        (M.toX.trace xs σ i).2 + ((M.toX.trace xs σ i).1.step xs (σ i)).2
      rw [b', b, a]

/-- The run from a net: the lazy program stands for the program on lists
at every action. -/
theorem LMach.init_sim {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((LMach.init X nt).trace xs σ i).1.toX = ((XMach.init X nt).trace xs σ i).1 ∧
      ((LMach.init X nt).trace xs σ i).2 = ((XMach.init X nt).trace xs σ i).2 ∧
      ((LMach.init X nt).trace xs σ i).1.Ok := by
  have e := LMach.init_toX hnd nt
  have hL : (LMach.init X nt).toX.Live xs := by
    rw [e]
    exact XMach.init_live hX hnt
  have hn : ((LMach.init X nt).toX.mem.agents.map Prod.fst).Nodup := by
    rw [e]
    exact hnd
  have k := LMach.trace_sim (LMach.init_ok hnd nt) hL hn σ i
  rw [e] at k
  exact k

/-- **Under a fair schedule the lazy program comes to rest with the normal
form**, as the program on lists does. -/
theorem LMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((LMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((LMach.init X nt).trace xs σ i).2 = n ∧
      ((LMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  obtain ⟨i₀, h⟩ := XMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨a, b, -⟩ := LMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((LMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- **The bound on the length of a fair run holds for the lazy program.** -/
theorem LMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((n + 1) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((LMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((LMach.init X nt).trace xs σ i).2 = n ∧
      ((LMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  intro i hi
  obtain ⟨a, b, -⟩ := LMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := XMach.fair_bound hX hnd hnt hb hs hn σ hfair i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((LMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- The cells an idle thread drops from the front of its list: those that
were dead when it took the list. -/
def LThread.skips (L : LMem S) (T : LThread S) : Nat :=
  match T.st with
  | .idle => T.raw.length - (T.raw.dropWhile (fun c => !L.seen T.snap c)).length
  | .look _ _ => 0
  | .seek _ _ _ _ => 0
  | .ready _ _ _ _ => 0
  | .half _ _ _ _ => 0
  | .write _ _ => 0

/-- What an idle thread pays when it drops `k` cells: one for each, and
three more if it finds a cell to try, for the action, for that cell and
for the lookup of its agent; one more for the action if it finds none; and
nothing if its list was empty. -/
def idleCost (found : Bool) (k : Nat) : Nat :=
  if found then k + 3 else if k = 0 then 0 else k + 1

/-- **What an action costs with lazy lists**: one for the action, one for
each operation on a map, one for each cell of a list of neighbours it
reads, and one for each cell it writes.  An idle thread looks up every cell
it drops and the one it stops at.  Taking the agents afresh costs one. -/
def LMach.cost (xs : XSys S) (L : LMem S) (T : LThread S) : Nat :=
  match T.st with
  | .idle =>
    idleCost (!(T.raw.dropWhile (fun c => !L.seen T.snap c)).isEmpty)
      (T.raw.length - (T.raw.dropWhile (fun c => !L.seen T.snap c)).length)
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (L.core.sym c.1).isSome then 0 else 1 + findCells p (L.core.nb c)
    else 2 + findCells p (L.core.nb c)
  | .ready a _ α _ => 2 + if L.core.sym a = some α then 2 else 0
  | .half a b α β =>
    2 + if L.core.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 2 + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 2
      else 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- Taking the agents afresh costs one, whatever the size of the memory. -/
theorem LMach.cost_fresh (xs : XSys S) (L : LMem S) (raw : List (Nat × Id × S)) (snap : Nat) :
    LMach.cost xs L ⟨raw, snap, .write [] []⟩ = 1 := rfl

/-- **An action costs a constant and the cells it drops.**  With lazy
lists an action that is not a rest costs at most the size of a rule and
eight, and two for each dead cell an idle thread drops; a rest costs only
the cells dropped. -/
theorem LMach.cost_le {C D : Nat} (hb : xs.Bounded C D) {L : LMem S} (h : L.Ok)
    (T : LThread S) :
    LMach.cost xs L T ≤ (C + D + 8) * (T.toX L).busy + 2 * T.skips L := by
  obtain ⟨raw, snap, s⟩ := T
  cases s with
  | idle =>
    rcases dropWhile_not_spec (L.seen snap) raw with ⟨hd, hf⟩ | ⟨c, rest, hd, -, hf⟩
    · have eT : LThread.toX L ⟨raw, snap, .idle⟩ = ⟨[], .idle⟩ := by
        show (⟨(raw.filter (L.seen snap)).map (·.2), .idle⟩ : XThread S) = _
        rw [hf]
        rfl
      rw [eT]
      unfold LMach.cost LThread.skips idleCost
      dsimp only
      rw [hd]
      show (if raw.length - 0 = 0 then 0 else raw.length - 0 + 1) ≤
        (C + D + 8) * 0 + 2 * (raw.length - 0)
      split <;> omega
    · have eT : LThread.toX L ⟨raw, snap, .idle⟩ =
          ⟨c.2 :: (rest.filter (L.seen snap)).map (·.2), .idle⟩ := by
        show (⟨(raw.filter (L.seen snap)).map (·.2), .idle⟩ : XThread S) = _
        rw [hf]
        rfl
      rw [eT]
      unfold LMach.cost LThread.skips idleCost
      dsimp only
      rw [hd]
      show raw.length - (rest.length + 1) + 3 ≤
        (C + D + 8) * 1 + 2 * (raw.length - (rest.length + 1))
      omega
  | look a α =>
    show 3 ≤ (C + D + 8) * 1 + 2 * 0
    omega
  | seek a α p c =>
    have hf := findCells_nbOf L.core.wires c p
    rw [← h.core.nbrs c] at hf
    show (if c.2 = 0 then 2 + (if (L.core.sym c.1).isSome then 0
        else 1 + findCells p (L.core.nb c))
      else 2 + findCells p (L.core.nb c)) ≤ (C + D + 8) * 1 + 2 * 0
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    show 2 + (if L.core.sym a = some α then 2 else 0) ≤ (C + D + 8) * 1 + 2 * 0
    split <;> omega
  | half a b α β =>
    have eb : (LThread.toX L ⟨raw, snap, .half a b α β⟩).busy = 1 := rfl
    have es : LThread.skips L ⟨raw, snap, .half a b α β⟩ = 0 := rfl
    rw [eb, es]
    unfold LMach.cost
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
      show 3 ≤ (C + D + 8) * 1 + 2 * 0
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        show 6 ≤ (C + D + 8) * 1 + 2 * 0
        omega
      | nil =>
        show 1 ≤ (C + D + 8) * 1 + 2 * 0
        omega

/-- What the action of thread `t` costs. -/
def LMach.stepCost (xs : XSys S) (M : LMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => LMach.cost xs M.mem T
  | none => 0

/-- The cells the action of thread `t` drops. -/
def LMach.stepSkips (M : LMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => T.skips M.mem
  | none => 0

theorem LMach.stepCost_le {C D : Nat} (hb : xs.Bounded C D) {M : LMach S} (h : M.Ok)
    (t : Nat) :
    M.stepCost xs t ≤ (C + D + 8) * M.toX.stepTally XThread.busy t + 2 * M.stepSkips t := by
  have hm : M.toX.ths[t]? = (M.ths[t]?).map (LThread.toX M.mem) := by
    show (M.ths.map (LThread.toX M.mem))[t]? = _
    rw [List.getElem?_map]
  unfold LMach.stepCost LMach.stepSkips XMach.stepTally
  rw [hm]
  cases M.ths[t]? with
  | none => exact Nat.zero_le _
  | some T => exact LMach.cost_le hb h.mem T

/-- **The running time with lazy lists** of the first `i` actions of a
run. -/
def LMach.time (xs : XSys S) (σ : Nat → Nat) (M : LMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => LMach.time xs σ M i + (M.trace xs σ i).1.stepCost xs (σ i)

/-- The dead cells the threads drop in the first `i` actions of a run. -/
def LMach.skips (xs : XSys S) (σ : Nat → Nat) (M : LMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => LMach.skips xs σ M i + (M.trace xs σ i).1.stepSkips (σ i)

/-- **The time with lazy lists is the work, up to a constant, and the dead
cells dropped.**  On every run from a well-formed net in which no agent is
listed twice, whatever the schedule, the time is at most

    (C + D + 8)

for each action that is not a rest and two for each dead cell that a
thread drops from its list.  Nothing is paid for taking the agents afresh
beyond one for the action, and no normal form is needed. -/
theorem LMach.time_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) (σ : Nat → Nat) :
    ∀ i, (LMach.init X nt).time xs σ i ≤
      (C + D + 8) * (XMach.init X nt).work xs σ i + 2 * (LMach.init X nt).skips xs σ i
  | 0 => Nat.zero_le _
  | i + 1 => by
    have ih := LMach.time_le_work hX hnd hnt hb σ i
    obtain ⟨a, -, ok⟩ := LMach.init_sim (xs := xs) hX hnd hnt σ i
    have hs := LMach.stepCost_le hb ok (σ i)
    rw [a] at hs
    show (LMach.init X nt).time xs σ i + ((LMach.init X nt).trace xs σ i).1.stepCost xs (σ i) ≤
      (C + D + 8) * ((XMach.init X nt).work xs σ i +
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i)) +
        2 * ((LMach.init X nt).skips xs σ i +
          ((LMach.init X nt).trace xs σ i).1.stepSkips (σ i))
    rw [Nat.mul_add (C + D + 8)]
    omega

theorem dropWhile_map_not {A : Type} (f : A → Bool) : ∀ l : List A,
    (l.map f).dropWhile (fun b => !b) = (l.dropWhile fun c => !f c).map f
  | [] => rfl
  | x :: l => by
    by_cases hx : f x = true
    · have e₁ : (x :: l).dropWhile (fun c => !f c) = x :: l :=
        List.dropWhile_cons_of_neg (by simpa using hx)
      have e₂ : ((x :: l).map f).dropWhile (fun b => !b) = (x :: l).map f :=
        List.dropWhile_cons_of_neg (by simpa using hx)
      rw [e₁, e₂]
    · have e₁ : (x :: l).dropWhile (fun c => !f c) = l.dropWhile (fun c => !f c) :=
        List.dropWhile_cons_of_pos (by simpa using hx)
      have e₂ : ((x :: l).map f).dropWhile (fun b => !b) = (l.map f).dropWhile (fun b => !b) :=
        List.dropWhile_cons_of_pos (by simpa using hx)
      rw [e₁, e₂]
      exact dropWhile_map_not f l

/-- The cells of the log by name, each with a mark that says whether it is
live. -/
def LMem.flags (L : LMem S) : List (Id × Bool) :=
  L.core.log.map fun c => (c.2.1, L.core.isLive c)

/-- The list of a thread as marks: whether each cell was live when the
thread took the list. -/
def LThread.flags (L : LMem S) (T : LThread S) : List Bool := T.raw.map (L.seen T.snap)

omit [DecidableEq S] in
theorem LThread.flags_keeps {L L' : LMem S} (k : L.Keeps L') {T : LThread S}
    (hT : T.snap ≤ L.core.stamp) : T.flags L' = T.flags L := by
  have e : L'.seen T.snap = L.seen T.snap := funext (k.seen T.snap hT)
  show T.raw.map (L'.seen T.snap) = T.raw.map (L.seen T.snap)
  rw [e]

theorem LMem.flags_take (L : LMem S) (a : Id) :
    (L.take a).flags = L.flags.map fun e => (e.1, e.2 && decide (e.1 ≠ a)) := by
  show L.core.log.map (fun c => (c.2.1, (L.take a).core.isLive c)) =
    (L.core.log.map fun c => (c.2.1, L.core.isLive c)).map
      fun e => (e.1, e.2 && decide (e.1 ≠ a))
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  obtain ⟨s, j, δ⟩ := c
  have hl : (L.take a).core.isLive (s, j, δ) =
      decide ((if a = j then none else L.core.live[j]?) = some (s, δ)) := by
    show decide ((L.core.live.erase a)[j]? = some (s, δ)) = _
    rw [hget_erase]
  show ((j, (L.take a).core.isLive (s, j, δ)) : Id × Bool) =
    (j, L.core.isLive (s, j, δ) && decide (j ≠ a))
  rw [hl]
  by_cases e : a = j
  · rw [ite_pos' e]
    have e₁ : decide ((none : Option (Nat × S)) = some (s, δ)) = false :=
      decide_eq_false (fun h => by cases h)
    have e₂ : decide (j ≠ a) = false := decide_eq_false (fun h => h e.symm)
    rw [e₁, e₂, Bool.and_false]
  · rw [ite_neg' e]
    have e₂ : decide (j ≠ a) = true := decide_eq_true (fun h => e h.symm)
    rw [e₂, Bool.and_true]
    rfl

theorem LMem.flags_put {L : LMem S} (h : L.Ok) {i : Id}
    (hi : assoc i L.toX.agents = none) (γ : S) : (L.put i γ).flags = (i, true) :: L.flags := by
  have hn : L.core.live[i]? = none := h.core.live_none hi
  have hl : ∀ (s : Nat) (j : Id) (δ : S), (L.put i γ).core.isLive (s, j, δ) =
      decide ((if i = j then some (L.core.stamp, γ) else L.core.live[j]?) = some (s, δ)) := by
    intro s j δ
    show decide ((L.core.live.insert i (L.core.stamp, γ))[j]? = some (s, δ)) = _
    rw [hget_insert]
  have h₀ : (L.put i γ).core.isLive (L.core.stamp, i, γ) = true := by
    rw [hl, ite_pos' rfl]
    exact decide_eq_true rfl
  show ((i, (L.put i γ).core.isLive (L.core.stamp, i, γ)) : Id × Bool) ::
      L.core.log.map (fun c => (c.2.1, (L.put i γ).core.isLive c)) =
    (i, true) :: L.core.log.map fun c => (c.2.1, L.core.isLive c)
  rw [h₀]
  refine congrArg _ (List.map_congr_left fun c hc => ?_)
  obtain ⟨s, j, δ⟩ := c
  have hs : s < L.core.stamp := h.core.lt _ hc
  show ((j, (L.put i γ).core.isLive (s, j, δ)) : Id × Bool) = (j, L.core.isLive (s, j, δ))
  rw [hl]
  by_cases hj : i = j
  · rw [ite_pos' hj]
    have e₁ : decide (some (L.core.stamp, γ) = some (s, δ)) = false := by
      apply decide_eq_false
      intro e
      cases e
      exact Nat.lt_irrefl _ hs
    have e₂ : L.core.isLive (s, j, δ) = false := by
      show decide (L.core.live[j]? = some (s, δ)) = false
      rw [← hj, hn]
      exact decide_eq_false (fun e => by cases e)
    rw [e₁, e₂]
  · rw [ite_neg' hj]
    rfl

/-- What an action costs with lazy lists, told from the lists of the
program and the marks of the thread. -/
def XMach.jcost (xs : XSys S) (X : XNet S) (fs : List Bool) (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    idleCost (!(fs.dropWhile (fun b => !b)).isEmpty)
      (fs.length - (fs.dropWhile (fun b => !b)).length)
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

/-- The cells an idle thread drops, told from its marks. -/
def XMach.jskips (fs : List Bool) (T : XThread S) : Nat :=
  match T.st with
  | .idle => fs.length - (fs.dropWhile (fun b => !b)).length
  | .look _ _ => 0
  | .seek _ _ _ _ => 0
  | .ready _ _ _ _ => 0
  | .half _ _ _ _ => 0
  | .write _ _ => 0

/-- The marks of a thread after its action. -/
def XMach.jflags (lf : List (Id × Bool)) (fs : List Bool) (T : XThread S) : List Bool :=
  match T.st with
  | .idle => (fs.dropWhile (fun b => !b)).tail
  | .look _ _ => fs
  | .seek _ _ _ _ => fs
  | .ready _ _ _ _ => fs
  | .half _ _ _ _ => fs
  | .write (_ :: _) _ => fs
  | .write [] (_ :: _) => fs
  | .write [] [] => lf.map (·.2)

/-- The marks of the log after an action. -/
def XMach.jlog (xs : XSys S) (X : XNet S) (lf : List (Id × Bool)) (T : XThread S) :
    List (Id × Bool) :=
  match T.st with
  | .idle => lf
  | .look _ _ => lf
  | .seek _ _ _ _ => lf
  | .ready a _ α _ =>
    if assoc a X.agents = some α then lf.map fun e => (e.1, e.2 && decide (e.1 ≠ a)) else lf
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some _ => lf.map fun e => (e.1, e.2 && decide (e.1 ≠ b))
    | none => (a, true) :: lf
  | .write (e :: _) _ => (e.1, true) :: lf
  | .write [] (_ :: _) => lf
  | .write [] [] => lf

/-- **An action with lazy lists, told from the lists**: its cost, the cells
it drops, and the marks of the log and of the thread after it are what the
functions above compute from the lists of the program and the marks. -/
theorem LMach.act_shadow (xs : XSys S) {L : LMem S} (h : L.Ok) (T : LThread S)
    (hT : T.snap ≤ L.core.stamp)
    (hnd : ((XMach.act xs L.toX (T.toX L)).1.agents.map Prod.fst).Nodup) :
    LMach.cost xs L T = XMach.jcost xs L.toX (T.flags L) (T.toX L) ∧
      T.skips L = XMach.jskips (T.flags L) (T.toX L) ∧
      (LMach.act xs L T).1.flags = XMach.jlog xs L.toX L.flags (T.toX L) ∧
      (LMach.act xs L T).2.1.flags (LMach.act xs L T).1 =
        XMach.jflags L.flags (T.flags L) (T.toX L) := by
  obtain ⟨raw, snap, s⟩ := T
  have hT' : snap ≤ L.core.stamp := hT
  cases s with
  | idle =>
    have hdm := dropWhile_map_not (L.seen snap) raw
    have hsk : raw.length - (raw.dropWhile fun c => !L.seen snap c).length =
        (raw.map (L.seen snap)).length -
          ((raw.map (L.seen snap)).dropWhile fun b => !b).length := by
      rw [hdm, List.length_map, List.length_map]
    have hem : (raw.dropWhile fun c => !L.seen snap c).isEmpty =
        ((raw.map (L.seen snap)).dropWhile fun b => !b).isEmpty := by
      rw [hdm]
      cases raw.dropWhile fun c => !L.seen snap c <;> rfl
    refine ⟨?_, hsk, ?_, ?_⟩
    · show idleCost (!(raw.dropWhile fun c => !L.seen snap c).isEmpty)
          (raw.length - (raw.dropWhile fun c => !L.seen snap c).length) =
        idleCost (!((raw.map (L.seen snap)).dropWhile fun b => !b).isEmpty)
          ((raw.map (L.seen snap)).length -
            ((raw.map (L.seen snap)).dropWhile fun b => !b).length)
      rw [hsk, hem]
    · have e : (LMach.act xs L ⟨raw, snap, .idle⟩).1 = L := by
        unfold LMach.act
        dsimp only
        split
        · rfl
        · split <;> rfl
      rw [e]
      rfl
    · show LThread.flags (LMach.act xs L ⟨raw, snap, .idle⟩).1
          (LMach.act xs L ⟨raw, snap, .idle⟩).2.1 =
        ((raw.map (L.seen snap)).dropWhile fun b => !b).tail
      rw [hdm]
      unfold LMach.act
      dsimp only
      split
      · rename_i hd
        rw [hd]
        rfl
      · rename_i c rest hd
        rw [hd]
        split <;> rfl
  | look a α =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have e : (LMach.act xs L ⟨raw, snap, .look a α⟩).1 = L := by
        unfold LMach.act
        dsimp only
        split <;> rfl
      rw [e]
      rfl
    · unfold LMach.act
      dsimp only
      split <;> rfl
  | seek a α p c =>
    refine ⟨?_, rfl, ?_, ?_⟩
    · show (if c.2 = 0 then 2 + (if (L.core.sym c.1).isSome then 0
          else 1 + findCells p (L.core.nb c))
        else 2 + findCells p (L.core.nb c)) = _
      rw [h.core.sym c.1, h.core.nbrs c]
      rfl
    · have e : (LMach.act xs L ⟨raw, snap, .seek a α p c⟩).1 = L := by
        unfold LMach.act
        dsimp only
        split
        · split <;> rfl
        · split <;> rfl
      rw [e]
      rfl
    · unfold LMach.act
      dsimp only
      split
      · split <;> rfl
      · split <;> rfl
  | ready a b α β =>
    refine ⟨?_, rfl, ?_, ?_⟩
    · show (2 + if L.core.sym a = some α then 2 else 0) = _
      rw [h.core.sym a]
      rfl
    · have eT : LThread.toX L ⟨raw, snap, .ready a b α β⟩ =
          ⟨(raw.filter (L.seen snap)).map (·.2), .ready a b α β⟩ := rfl
      rw [eT]
      unfold LMach.act XMach.jlog
      dsimp only
      rw [h.core.sym a]
      by_cases hc : assoc a L.core.toX.agents = some α
      · rw [ite_pos' hc, ite_pos' hc]
        exact L.flags_take a
      · rw [ite_neg' hc, ite_neg' hc]
    · unfold LMach.act
      dsimp only
      by_cases hc : L.core.sym a = some α
      · rw [ite_pos' hc]
        exact LThread.flags_keeps (.take h a) hT'
      · rw [ite_neg' hc]
        rfl
  | half a b α β =>
    have eT : LThread.toX L ⟨raw, snap, .half a b α β⟩ =
        ⟨(raw.filter (L.seen snap)).map (·.2), .half a b α β⟩ := rfl
    rw [eT] at hnd
    unfold XMach.act at hnd
    dsimp only at hnd
    refine ⟨?_, rfl, ?_, ?_⟩
    · unfold LMach.cost XMach.jcost
      dsimp only
      rw [h.core.sym b]
      rfl
    · rw [eT]
      unfold LMach.act XMach.jlog
      dsimp only
      rw [h.core.sym b]
      cases hR : (if assoc b L.core.toX.agents = some β ∧ a ≠ b then xs.rule α β else none) with
      | some R => exact L.flags_take b
      | none =>
        rw [hR] at hnd
        exact LMem.flags_put h (assoc_none_of_nodup_cons hnd) α
    · unfold LMach.act
      dsimp only
      cases (if L.core.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
      | some R => exact LThread.flags_keeps (.take h b) hT'
      | none => exact LThread.flags_keeps (.put L a α) hT'
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨rfl, rfl, LMem.flags_put h (assoc_none_of_nodup_cons hnd) γ,
        LThread.flags_keeps (.put L i γ) hT'⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨rfl, rfl, rfl, LThread.flags_keeps (.link L p q) hT'⟩
      | nil =>
        refine ⟨rfl, rfl, rfl, ?_⟩
        show L.core.log.map (L.seen L.core.stamp) =
          (L.core.log.map fun c => (c.2.1, L.core.isLive c)).map (·.2)
        rw [List.map_map]
        exact List.map_congr_left (LMem.seen_now h)

/-- **A run with lazy lists, told from the lists**: what the first `i`
actions cost, the dead cells they drop, the marks of the log and the marks
of every thread after them, computed along the run of the program on
lists.  At the start every agent of the net is a live cell and every
thread has them all. -/
def XMach.lazyRun (xs : XSys S) (σ : Nat → Nat) (X : XNet S) (nt : Nat) :
    Nat → Nat × Nat × List (Id × Bool) × List (List Bool)
  | 0 => (0, 0, X.agents.map fun e => (e.1, true),
      (List.range nt).map fun _ => List.replicate X.agents.length true)
  | i + 1 =>
    match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
    | some T =>
      ((XMach.lazyRun xs σ X nt i).1 +
          XMach.jcost xs ((XMach.init X nt).trace xs σ i).1.mem
            (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
        (XMach.lazyRun xs σ X nt i).2.1 +
          XMach.jskips (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
        XMach.jlog xs ((XMach.init X nt).trace xs σ i).1.mem
          (XMach.lazyRun xs σ X nt i).2.2.1 T,
        (XMach.lazyRun xs σ X nt i).2.2.2.set (σ i)
          (XMach.jflags (XMach.lazyRun xs σ X nt i).2.2.1
            (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD []) T))
    | none => XMach.lazyRun xs σ X nt i

/-- One action of the lazy program, told from the lists. -/
theorem LMach.step_shadow (xs : XSys S) {M : LMach S} (h : M.Ok) {t : Nat} {T : LThread S}
    (ht : M.ths[t]? = some T)
    (hnd : ((XMach.act xs M.mem.toX (T.toX M.mem)).1.agents.map Prod.fst).Nodup) :
    M.stepCost xs t = XMach.jcost xs M.mem.toX (T.flags M.mem) (T.toX M.mem) ∧
      M.stepSkips t = XMach.jskips (T.flags M.mem) (T.toX M.mem) ∧
      (M.step xs t).1.mem.flags = XMach.jlog xs M.mem.toX M.mem.flags (T.toX M.mem) ∧
      (M.step xs t).1.ths.map (LThread.flags (M.step xs t).1.mem) =
        (M.ths.map (LThread.flags M.mem)).set t
          (XMach.jflags M.mem.flags (T.flags M.mem) (T.toX M.mem)) := by
  have hT := h.snap T (List.mem_of_getElem? ht)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := LMach.act_shadow xs h.mem T hT hnd
  obtain ⟨-, -, -, -, -, k⟩ := LMach.act_sim xs h.mem T hT hnd
  have e₁ : M.step xs t = (⟨(LMach.act xs M.mem T).1,
      M.ths.set t (LMach.act xs M.mem T).2.1⟩, (LMach.act xs M.mem T).2.2) := by
    unfold LMach.step
    rw [ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LMach.stepCost
    rw [ht]
    exact c₁
  · unfold LMach.stepSkips
    rw [ht]
    exact c₂
  · rw [e₁]
    exact c₃
  · rw [e₁]
    have em : M.ths.map (LThread.flags (LMach.act xs M.mem T).1) =
        M.ths.map (LThread.flags M.mem) :=
      List.map_congr_left fun U hU => LThread.flags_keeps k (h.snap U hU)
    show (M.ths.set t (LMach.act xs M.mem T).2.1).map
      (LThread.flags (LMach.act xs M.mem T).1) = _
    rw [List.map_set, em, c₄]

theorem map_true_replicate {A : Type} (f : A → Bool) (hf : ∀ c, f c = true) :
    ∀ l : List A, l.map f = List.replicate l.length true
  | [] => rfl
  | x :: l => by
    show f x :: l.map f = true :: List.replicate l.length true
    rw [hf x, map_true_replicate f hf l]

/-- **The time with lazy lists can be computed on lists.**  On every run
from a well-formed net in which no agent is listed twice, the time of the
lazy program, the dead cells it drops, and the marks of its log and of its
threads are what `XMach.lazyRun` computes along the run of the program on
lists.  Hashing does not enter, so the kernel can evaluate it. -/
theorem LMach.time_shadow {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (LMach.init X nt).time xs σ i = (XMach.lazyRun xs σ X nt i).1 ∧
      (LMach.init X nt).skips xs σ i = (XMach.lazyRun xs σ X nt i).2.1 ∧
      ((LMach.init X nt).trace xs σ i).1.mem.flags = (XMach.lazyRun xs σ X nt i).2.2.1 ∧
      ((LMach.init X nt).trace xs σ i).1.ths.map
          (LThread.flags ((LMach.init X nt).trace xs σ i).1.mem) =
        (XMach.lazyRun xs σ X nt i).2.2.2
  | 0 => by
    obtain ⟨ok, hlog⟩ := LMem.ofX_ok hnd
    have hempty : ∀ s : Nat, (LMem.ofX X).dead[s]? = none := fun s => by
      show (∅ : Std.HashMap Nat Nat)[s]? = none
      exact Std.HashMap.getElem?_empty
    have hseen : ∀ (t₀ : Nat) (c : Nat × Id × S), (LMem.ofX X).seen t₀ c = true := by
      intro t₀ c
      show (match (LMem.ofX X).dead[c.1]? with
        | none => true
        | some d => decide (t₀ ≤ d)) = true
      rw [hempty]
    have hlen : (IMem.ofX X).log.length = X.agents.length := by
      have := congrArg List.length hlog
      rw [List.length_map] at this
      exact this
    refine ⟨rfl, rfl, ?_, ?_⟩
    · show (IMem.ofX X).log.map (fun c => (c.2.1, (IMem.ofX X).isLive c)) =
        X.agents.map fun e => (e.1, true)
      have e : (IMem.ofX X).log.map (fun c => (c.2.1, (IMem.ofX X).isLive c)) =
          (IMem.ofX X).log.map fun c => (c.2.1, true) := by
        apply List.map_congr_left
        intro c hc
        obtain ⟨s, i, γ⟩ := c
        have hl := (ok.gone s i γ hc).2 (hempty s)
        have : (IMem.ofX X).isLive (s, i, γ) = true := ((IMem.ofX X).isLive_iff s i γ).2 hl
        show ((i, (IMem.ofX X).isLive (s, i, γ)) : Id × Bool) = (i, true)
        rw [this]
      rw [e, ← hlog, List.map_map]
      rfl
    · show ((List.range nt).map _).map (LThread.flags (LMem.ofX X)) =
        (List.range nt).map fun _ => List.replicate X.agents.length true
      rw [List.map_map]
      apply List.map_congr_left
      intro t _
      show ((IMem.ofX X).log.drop t ++ (IMem.ofX X).log.take t).map
        ((LMem.ofX X).seen (IMem.ofX X).stamp) = _
      rw [map_true_replicate _ (hseen _), List.length_append, List.length_drop,
        List.length_take, hlen]
      have e : X.agents.length - t + min t X.agents.length = X.agents.length := by omega
      rw [e]
  | i + 1 => by
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := LMach.time_shadow hX hnd hnt σ i
    obtain ⟨a, -, ok⟩ := LMach.init_sim (xs := xs) hX hnd hnt σ i
    have live := XMach.trace_live (xs := xs) σ (XMach.init_live (X := X) hX hnt)
    have nd : ∀ j, (((XMach.init X nt).trace xs σ j).1.mem.agents.map Prod.fst).Nodup := by
      intro j
      induction j with
      | zero => exact hnd
      | succ j ih => exact XMach.step_nodup (live j) ih (σ j)
    have emem : ((LMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    have hm : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
        (((LMach.init X nt).trace xs σ i).1.ths[σ i]?).map
          (LThread.toX ((LMach.init X nt).trace xs σ i).1.mem) := by
      rw [← a]
      show (((LMach.init X nt).trace xs σ i).1.ths.map _)[σ i]? = _
      rw [List.getElem?_map]
    cases hT : ((LMach.init X nt).trace xs σ i).1.ths[σ i]? with
    | none =>
      rw [hT] at hm
      have hm' : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? = none := hm
      have es : XMach.lazyRun xs σ X nt (i + 1) = XMach.lazyRun xs σ X nt i := by
        show (match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
          | some T => _
          | none => XMach.lazyRun xs σ X nt i) = _
        rw [hm']
      have e₁ : ((LMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = 0 := by
        unfold LMach.stepCost
        rw [hT]
      have e₂ : ((LMach.init X nt).trace xs σ i).1.stepSkips (σ i) = 0 := by
        unfold LMach.stepSkips
        rw [hT]
      have e₃ : ((LMach.init X nt).trace xs σ i).1.step xs (σ i) =
          (((LMach.init X nt).trace xs σ i).1, 0) := by
        unfold LMach.step
        rw [hT]
      rw [es]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show (LMach.init X nt).time xs σ i +
          ((LMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [e₁, ih₁]
        rfl
      · show (LMach.init X nt).skips xs σ i +
          ((LMach.init X nt).trace xs σ i).1.stepSkips (σ i) = _
        rw [e₂, ih₂]
        rfl
      · show (((LMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.flags = _
        rw [e₃]
        exact ih₃
      · show (((LMach.init X nt).trace xs σ i).1.step xs (σ i)).1.ths.map
          (LThread.flags (((LMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem) = _
        rw [e₃]
        exact ih₄
    | some T =>
      rw [hT] at hm
      have hm' : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
          some (T.toX ((LMach.init X nt).trace xs σ i).1.mem) := hm
      have hfl : ((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD [] =
          T.flags ((LMach.init X nt).trace xs σ i).1.mem := by
        rw [← ih₄, List.getElem?_map, hT]
        rfl
      have hstep : (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem =
          (XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
            (T.toX ((LMach.init X nt).trace xs σ i).1.mem)).1 := by
        have e : ((XMach.init X nt).trace xs σ i).1.step xs (σ i) =
            (⟨(XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
                (T.toX ((LMach.init X nt).trace xs σ i).1.mem)).1,
              ((XMach.init X nt).trace xs σ i).1.ths.set (σ i)
                (XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
                  (T.toX ((LMach.init X nt).trace xs σ i).1.mem)).2.1⟩,
              (XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
                (T.toX ((LMach.init X nt).trace xs σ i).1.mem)).2.2) :=
          XMach.step_eq hm' rfl
        rw [e]
      have hn : ((XMach.act xs ((LMach.init X nt).trace xs σ i).1.mem.toX
          (T.toX ((LMach.init X nt).trace xs σ i).1.mem)).1.agents.map Prod.fst).Nodup := by
        rw [emem, ← hstep]
        exact nd (i + 1)
      obtain ⟨s₁, s₂, s₃, s₄⟩ := LMach.step_shadow xs ok hT hn
      rw [emem] at s₁ s₃
      have es : XMach.lazyRun xs σ X nt (i + 1) =
          ((XMach.lazyRun xs σ X nt i).1 +
              XMach.jcost xs ((XMach.init X nt).trace xs σ i).1.mem
                (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD [])
                (T.toX ((LMach.init X nt).trace xs σ i).1.mem),
            (XMach.lazyRun xs σ X nt i).2.1 +
              XMach.jskips (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD [])
                (T.toX ((LMach.init X nt).trace xs σ i).1.mem),
            XMach.jlog xs ((XMach.init X nt).trace xs σ i).1.mem
              (XMach.lazyRun xs σ X nt i).2.2.1
              (T.toX ((LMach.init X nt).trace xs σ i).1.mem),
            (XMach.lazyRun xs σ X nt i).2.2.2.set (σ i)
              (XMach.jflags (XMach.lazyRun xs σ X nt i).2.2.1
                (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD [])
                (T.toX ((LMach.init X nt).trace xs σ i).1.mem))) := by
        show (match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
          | some T =>
            ((XMach.lazyRun xs σ X nt i).1 +
                XMach.jcost xs ((XMach.init X nt).trace xs σ i).1.mem
                  (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
              (XMach.lazyRun xs σ X nt i).2.1 +
                XMach.jskips (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
              XMach.jlog xs ((XMach.init X nt).trace xs σ i).1.mem
                (XMach.lazyRun xs σ X nt i).2.2.1 T,
              (XMach.lazyRun xs σ X nt i).2.2.2.set (σ i)
                (XMach.jflags (XMach.lazyRun xs σ X nt i).2.2.1
                  (((XMach.lazyRun xs σ X nt i).2.2.2[σ i]?).getD []) T))
          | none => XMach.lazyRun xs σ X nt i) = _
        rw [hm']
      rw [es, hfl]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show (LMach.init X nt).time xs σ i +
          ((LMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [s₁, ih₁]
      · show (LMach.init X nt).skips xs σ i +
          ((LMach.init X nt).trace xs σ i).1.stepSkips (σ i) = _
        rw [s₂, ih₂]
      · show (((LMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.flags = _
        rw [s₃, ih₃]
      · show (((LMach.init X nt).trace xs σ i).1.step xs (σ i)).1.ths.map
          (LThread.flags (((LMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem) = _
        rw [s₄, ih₃, ih₄]

/-- Every thread is idle with nothing left in its list, dead cells
included. -/
def LMach.resting (M : LMach S) : Bool := M.ths.all fun T => T.raw.isEmpty && T.st.isIdle

theorem LMach.step_resting (xs : XSys S) {M : LMach S} (h : M.resting = true) (t : Nat) :
    M.step xs t = (M, 0) ∧ M.stepCost xs t = 0 := by
  cases ht : M.ths[t]? with
  | none =>
    refine ⟨?_, ?_⟩
    · unfold LMach.step
      rw [ht]
    · unfold LMach.stepCost
      rw [ht]
  | some T =>
    have hT := List.all_eq_true.1 h T (List.mem_of_getElem? ht)
    obtain ⟨raw, snap, s⟩ := T
    cases raw with
    | cons x r => cases hT
    | nil =>
      cases s with
      | idle =>
        refine ⟨?_, ?_⟩
        · unfold LMach.step
          rw [ht]
          show ((⟨M.mem, M.ths.set t ⟨[], snap, .idle⟩⟩ : LMach S), 0) = (M, 0)
          rw [set_self M.ths t _ ht]
        · unfold LMach.stepCost
          rw [ht]
          rfl
      | look a α => cases hT
      | seek a α p c => cases hT
      | ready a b α β => cases hT
      | half a b α β => cases hT
      | write as ls => cases hT

/-- Once the lazy program is at rest it stays as it is, and so does its
time. -/
theorem LMach.time_rest {M : LMach S} (σ : Nat → Nat) {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) :
    ∀ d, (M.trace xs σ (B + d)).1 = (M.trace xs σ B).1 ∧
      M.time xs σ (B + d) = M.time xs σ B
  | 0 => ⟨rfl, rfl⟩
  | d + 1 => by
    obtain ⟨e₁, e₂⟩ := LMach.time_rest σ h d
    have hr : (M.trace xs σ (B + d)).1.resting = true := by
      rw [e₁]
      exact h
    obtain ⟨s₁, s₂⟩ := LMach.step_resting xs hr (σ (B + d))
    refine ⟨?_, ?_⟩
    · show ((M.trace xs σ (B + d)).1.step xs (σ (B + d))).1 = _
      rw [s₁]
      exact e₁
    · show M.time xs σ (B + d) + (M.trace xs σ (B + d)).1.stepCost xs (σ (B + d)) = _
      rw [s₂, Nat.add_zero]
      exact e₂

/-- The lazy program is at rest when the program it stands for is and the
marks of every thread are used up. -/
theorem LMach.resting_of_flags {M : LMach S} (hX : M.toX.resting = true)
    (hf : (M.ths.map (LThread.flags M.mem)).all List.isEmpty = true) : M.resting = true := by
  refine List.all_eq_true.2 fun T hT => ?_
  have h₁ : (T.flags M.mem).isEmpty = true :=
    List.all_eq_true.1 hf _ (List.mem_map_of_mem hT)
  have h₂ : ((T.toX M.mem).todo.isEmpty && (T.toX M.mem).st.isIdle) = true :=
    List.all_eq_true.1 hX _ (List.mem_map_of_mem hT)
  have h₃ : T.st.isIdle = true := (Bool.and_eq_true _ _ ▸ h₂ : _ ∧ _).2
  have h₄ : T.raw.isEmpty = true := by
    obtain ⟨raw, snap, s⟩ := T
    cases raw with
    | nil => rfl
    | cons x r => cases h₁
  rw [h₃, h₄]
  rfl

end Lazy

end INet
