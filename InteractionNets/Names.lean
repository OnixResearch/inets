import InteractionNets.Counted

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### New names

A claim names the agents it creates after the two that fire.  Here it is
proved that those names are new to the whole state of the program: no
agent, no segment, no thread has them.  It follows from the reservation of
names in well-formed nets and from an invariant of the program, that every
name a thread holds stays known to the memory. -/

section FreshNames

variable [DecidableEq S] {xs : XSys S}

/-- A name is that of an agent of the memory. -/
def XNet.IsAgent (X : XNet S) (i : Id) : Prop := ∃ γ, (i, γ) ∈ X.agents

/-- A name is on a segment of the memory. -/
def XNet.OnWire (X : XNet S) (i : Id) : Prop := ∃ e ∈ X.wires, e.1.1 = i ∨ e.2.1 = i

/-- The names a thread has in hand are known to the memory: the agent it
looks at is there or is on a segment, and once it has followed a segment
every name it holds is on one. -/
def TState.Wired (X : XNet S) : TState S → Prop
  | .idle => True
  | .look a _ => X.IsAgent a ∨ X.OnWire a
  | .seek a _ p c => X.OnWire a ∧ X.OnWire p.1 ∧ X.OnWire c.1
  | .ready a b _ _ => X.OnWire a ∧ X.OnWire b
  | .half a b _ _ => X.OnWire a ∧ X.OnWire b
  | .write _ _ => True

/-- Every name of a thread's list is an agent or on a segment. -/
def XThread.Wired (X : XNet S) (T : XThread S) : Prop :=
  (∀ e ∈ T.todo, X.IsAgent e.1 ∨ X.OnWire e.1) ∧ T.st.Wired X

/-- The second memory still knows the names of the first. -/
def XNet.Keeps (X X' : XNet S) : Prop :=
  (∀ i, X.IsAgent i → X'.IsAgent i ∨ X'.OnWire i) ∧ ∀ i, X.OnWire i → X'.OnWire i

omit [DecidableEq S] in
theorem XNet.Keeps.refl (X : XNet S) : X.Keeps X := ⟨fun _ h => .inl h, fun _ h => h⟩

omit [DecidableEq S] in
theorem XNet.Keeps.take {X : XNet S} {a : Id} (h : X.OnWire a) : X.Keeps (X.takeAgent a) := by
  refine ⟨fun i hi => ?_, fun _ hw => hw⟩
  obtain ⟨γ, hγ⟩ := hi
  by_cases e : i = a
  · rw [e]
    exact .inr h
  · exact .inl ⟨γ, List.mem_filter.2 ⟨hγ, decide_eq_true e⟩⟩

omit [DecidableEq S] in
theorem XNet.Keeps.put (X : XNet S) (i : Id) (γ : S) : X.Keeps (X.putAgent i γ) :=
  ⟨fun _ h => .inl ⟨h.choose, List.mem_cons_of_mem _ h.choose_spec⟩, fun _ hw => hw⟩

omit [DecidableEq S] in
theorem XNet.Keeps.link (X : XNet S) (p q : Port) : X.Keeps (X.putLink p q) := by
  refine ⟨fun _ h => .inl h, fun i hw => ?_⟩
  obtain ⟨e, he, h⟩ := hw
  exact ⟨e, List.mem_cons_of_mem _ he, h⟩

omit [DecidableEq S] in
theorem TState.Wired.keep {X X' : XNet S} (hk : X.Keeps X') {s : TState S} (h : s.Wired X) :
    s.Wired X' := by
  cases s with
  | idle => trivial
  | look a α =>
    rcases h with h | h
    · exact hk.1 a h
    · exact .inr (hk.2 a h)
  | seek a α p c => exact ⟨hk.2 _ h.1, hk.2 _ h.2.1, hk.2 _ h.2.2⟩
  | ready a b α β => exact ⟨hk.2 _ h.1, hk.2 _ h.2⟩
  | half a b α β => exact ⟨hk.2 _ h.1, hk.2 _ h.2⟩
  | write as ls => trivial

omit [DecidableEq S] in
theorem XThread.Wired.keep {X X' : XNet S} (hk : X.Keeps X') {T : XThread S} (h : T.Wired X) :
    T.Wired X' := by
  refine ⟨fun e he => ?_, h.2.keep hk⟩
  rcases h.1 e he with h' | h'
  · exact hk.1 _ h'
  · exact .inr (hk.2 _ h')

/-- **An action keeps the names known**: the memory after it still knows
every name it knew, and the thread holds only names the memory knows. -/
theorem XMach.act_wired (xs : XSys S) {X : XNet S} {T : XThread S} (hT : T.Wired X) :
    X.Keeps (XMach.act xs X T).1 ∧ (XMach.act xs X T).2.1.Wired (XMach.act xs X T).1 := by
  obtain ⟨todo, st⟩ := T
  obtain ⟨hTd, hTs⟩ := hT
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨.refl X, hTd, trivial⟩
    | cons e rest =>
      cases hact : XMach.act xs X ⟨e :: rest, .idle⟩ with
      | mk X' r =>
        obtain ⟨T', k⟩ := r
        unfold XMach.act at hact
        dsimp only at hact
        have hr : ∀ x ∈ rest, X.IsAgent x.1 ∨ X.OnWire x.1 :=
          fun x hx => hTd x (List.mem_cons_of_mem _ hx)
        split at hact
        · cases hact
          exact ⟨.refl X, hr, hTd e List.mem_cons_self⟩
        · cases hact
          exact ⟨.refl X, hr, trivial⟩
  | look a α =>
    cases hact : XMach.act xs X ⟨todo, .look a α⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · rename_i q hq
        cases hact
        have hm := assoc_mem hq
        exact ⟨.refl X, hTd, ⟨_, hm, .inl rfl⟩, ⟨_, hm, .inl rfl⟩, ⟨_, hm, .inr rfl⟩⟩
      · cases hact
        exact ⟨.refl X, hTd, trivial⟩
  | seek a α p c =>
    obtain ⟨ha, hp, hc⟩ : X.OnWire a ∧ X.OnWire p.1 ∧ X.OnWire c.1 := hTs
    cases hact : XMach.act xs X ⟨todo, .seek a α p c⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · split at hact
        · cases hact
          exact ⟨.refl X, hTd, ha, hc⟩
        · cases hact
          exact ⟨.refl X, hTd, trivial⟩
      · split at hact
        · rename_i q hq
          cases hact
          exact ⟨.refl X, hTd, ha, hc, ⟨_, (nextSeg_spec hq).1, .inr rfl⟩⟩
        · cases hact
          exact ⟨.refl X, hTd, trivial⟩
  | ready a b α β =>
    obtain ⟨ha, hb⟩ : X.OnWire a ∧ X.OnWire b := hTs
    cases hact : XMach.act xs X ⟨todo, .ready a b α β⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · cases hact
        have hk : X.Keeps (X.takeAgent a) := .take ha
        exact ⟨hk, (XThread.Wired.keep hk (T := ⟨todo, .idle⟩) ⟨hTd, trivial⟩).1, ha, hb⟩
      · cases hact
        exact ⟨.refl X, hTd, trivial⟩
  | half a b α β =>
    obtain ⟨ha, hb⟩ : X.OnWire a ∧ X.OnWire b := hTs
    cases hact : XMach.act xs X ⟨todo, .half a b α β⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · cases hact
        have hk : X.Keeps (X.takeAgent b) := .take hb
        exact ⟨hk, (XThread.Wired.keep hk (T := ⟨todo, .idle⟩) ⟨hTd, trivial⟩).1, trivial⟩
      · cases hact
        have hk : X.Keeps (X.putAgent a α) := .put X a α
        exact ⟨hk, (XThread.Wired.keep hk (T := ⟨todo, .idle⟩) ⟨hTd, trivial⟩).1, trivial⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have hk : X.Keeps (X.putAgent i γ) := .put X i γ
      exact ⟨hk, (XThread.Wired.keep hk (T := ⟨todo, .idle⟩) ⟨hTd, trivial⟩).1, trivial⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have hk : X.Keeps (X.putLink p q) := .link X p q
        exact ⟨hk, (XThread.Wired.keep hk (T := ⟨todo, .idle⟩) ⟨hTd, trivial⟩).1, trivial⟩
      | nil => exact ⟨.refl X, fun e he => .inl ⟨e.2, he⟩, trivial⟩

/-- Every thread holds only names the memory knows. -/
def XMach.Wired (M : XMach S) : Prop := ∀ T ∈ M.ths, T.Wired M.mem

theorem XMach.step_wired (xs : XSys S) {M : XMach S} (h : M.Wired) (t : Nat) :
    (M.step xs t).1.Wired := by
  unfold XMach.step
  cases hT : M.ths[t]? with
  | none => exact h
  | some T =>
    obtain ⟨hk, hw⟩ := XMach.act_wired xs (h T (List.mem_of_getElem? hT))
    intro T' hT'
    have hT'' : T' ∈ M.ths.set t (XMach.act xs M.mem T).2.1 := hT'
    rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
    · exact (h T' hm).keep hk
    · exact hw

theorem XMach.trace_wired (σ : Nat → Nat) {M : XMach S} (h : M.Wired) :
    ∀ i, (M.trace xs σ i).1.Wired
  | 0 => h
  | i + 1 => XMach.step_wired xs (XMach.trace_wired σ h i) (σ i)

omit [DecidableEq S] in
theorem XMach.init_wired (X : XNet S) (nt : Nat) : (XMach.init X nt).Wired := by
  intro T hT
  have hT' : T ∈ (List.range nt).map fun t =>
      (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S) := hT
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT'
  refine ⟨fun e he => ?_, trivial⟩
  have he' : e ∈ X.agents.drop t ++ X.agents.take t := he
  rcases List.mem_append.1 he' with h | h
  · exact .inl ⟨e.2, List.mem_of_mem_drop h⟩
  · exact .inl ⟨e.2, List.mem_of_mem_take h⟩

/-- A name is in the hand of a thread. -/
def TState.Mentions : TState S → Id → Prop
  | .idle, _ => False
  | .look a _, i => i = a
  | .seek a _ p c, i => i = a ∨ i = p.1 ∨ i = c.1
  | .ready a b _ _, i => i = a ∨ i = b
  | .half a b _ _, i => i = a ∨ i = b
  | .write as ls, i => (∃ e ∈ as, e.1 = i) ∨ ∃ e ∈ ls, e.1.1 = i ∨ e.2.1 = i

/-- **A name occurs in the state of the program**: as an agent, on a
segment, in the list of a thread, or in its hand. -/
def XMach.Mentions (M : XMach S) (i : Id) : Prop :=
  M.mem.IsAgent i ∨ M.mem.OnWire i ∨
    ∃ T ∈ M.ths, (∃ e ∈ T.todo, e.1 = i) ∨ T.st.Mentions i

omit [DecidableEq S] in
/-- **The names a claim gives are new to the whole state.**  When a
thread holds `a`, finds its partner `b` in the memory and a rule for the
pair, no name of an agent that the rule creates occurs anywhere: not as an
agent, not on a segment, not in the list or the hand of any thread, not
among the agents and segments still to be written. -/
theorem XMach.claim_fresh {M : XMach S} (hL : M.Live xs) (hW : M.Wired) {t : Nat}
    {todo : List (Id × S)} {a b : Id} {α β : S} {R : XRhs S}
    (hT : M.ths[t]? = some ⟨todo, .half a b α β⟩) (hb : (b, β) ∈ M.mem.agents)
    (hne : a ≠ b) (hr : xs.rule α β = some R) {j : Id} {γ : S}
    (hj : (j, γ) ∈ R.newAgents a b) : ¬ M.Mentions j := by
  have hwf := hL.inv.wf
  have ha' : M.toMach.goal.agent a α := by
    refine .inl (.inr ⟨t, ?_⟩)
    show (threadOf M.ths t).held a α
    rw [threadOf_eq hT]
    exact ⟨rfl, rfl⟩
  have hb' : M.toMach.goal.agent b β := .inl (.inl hb)
  obtain ⟨o, jj, rfl, -⟩ := (xs.writes hne hr).2.agent.1 hj
  have hU : ¬ M.toMach.goal.Used (child a b o jj) := by
    intro hu
    rcases par_eq a b o with e | e
    · have hu' : M.toMach.goal.Used ([slot o jj] ++ a) := by
        show M.toMach.goal.Used (slot o jj :: a)
        rw [← e]
        exact hu
      cases hwf.fresh [slot o jj] ha' hu'
    · have hu' : M.toMach.goal.Used ([slot o jj] ++ b) := by
        show M.toMach.goal.Used (slot o jj :: b)
        rw [← e]
        exact hu
      cases hwf.fresh [slot o jj] hb' hu'
  have agentU : ∀ i, M.mem.IsAgent i → M.toMach.goal.Used i :=
    fun i h => .inl ⟨h.choose, .inl (.inl h.choose_spec)⟩
  have wireU : ∀ i, M.mem.OnWire i → M.toMach.goal.Used i := by
    intro i h
    obtain ⟨e, he, h'⟩ := h
    obtain ⟨p, q⟩ := e
    have hl : M.toMach.goal.link p q := .inl he
    rcases h' with h' | h'
    · obtain ⟨pi, pk⟩ := p
      have e' : pi = i := h'
      rw [← e']
      exact .inr (.inl ⟨pk, q, hl⟩)
    · obtain ⟨qi, qk⟩ := q
      have e' : qi = i := h'
      rw [← e']
      exact .inr (.inl ⟨qk, p, hwf.symm hl⟩)
  intro hm
  rcases hm with h | h | ⟨T', hT', h⟩
  · exact hU (agentU _ h)
  · exact hU (wireU _ h)
  · have hw := hW T' hT'
    rcases h with ⟨e, he, e'⟩ | h
    · rw [← e'] at hU
      rcases hw.1 e he with h' | h'
      · exact hU (agentU _ h')
      · exact hU (wireU _ h')
    · obtain ⟨todo', st'⟩ := T'
      obtain ⟨u, hu⟩ := List.getElem?_of_mem hT'
      have hw2 : st'.Wired M.mem := hw.2
      cases st' with
      | idle => exact h
      | look a' α' =>
        have e' : child a b o jj = a' := h
        rw [e'] at hU
        rcases hw2 with h' | h'
        · exact hU (agentU _ h')
        · exact hU (wireU _ h')
      | seek a' α' p c =>
        have h' : child a b o jj = a' ∨ child a b o jj = p.1 ∨ child a b o jj = c.1 := h
        rcases h' with e' | e' | e' <;> rw [e'] at hU
        · exact hU (wireU _ hw2.1)
        · exact hU (wireU _ hw2.2.1)
        · exact hU (wireU _ hw2.2.2)
      | ready a' b' α' β' =>
        have h' : child a b o jj = a' ∨ child a b o jj = b' := h
        rcases h' with e' | e' <;> rw [e'] at hU
        · exact hU (wireU _ hw2.1)
        · exact hU (wireU _ hw2.2)
      | half a' b' α' β' =>
        have h' : child a b o jj = a' ∨ child a b o jj = b' := h
        rcases h' with e' | e' <;> rw [e'] at hU
        · exact hU (wireU _ hw2.1)
        · exact hU (wireU _ hw2.2)
      | write as ls =>
        have eth : threadOf M.ths u = TState.write as ls := threadOf_eq hu
        have h' : (∃ e ∈ as, e.1 = child a b o jj) ∨
            ∃ e ∈ ls, e.1.1 = child a b o jj ∨ e.2.1 = child a b o jj := h
        rcases h' with ⟨e, he, e'⟩ | ⟨e, he, e'⟩
        · obtain ⟨i, δ⟩ := e
          have e'' : i = child a b o jj := e'
          rw [← e''] at hU
          refine hU (.inl ⟨δ, .inr ⟨u, ?_⟩⟩)
          show (threadOf M.ths u).pendA i δ
          rw [eth]
          exact he
        · obtain ⟨p, q⟩ := e
          have hl : M.toMach.goal.link p q := by
            refine .inr ⟨u, ?_⟩
            show (threadOf M.ths u).pendL p q
            rw [eth]
            exact he
          rcases e' with e' | e'
          · obtain ⟨pi, pk⟩ := p
            have e'' : pi = child a b o jj := e'
            rw [← e''] at hU
            exact hU (.inr (.inl ⟨pk, q, hl⟩))
          · obtain ⟨qi, qk⟩ := q
            have e'' : qi = child a b o jj := e'
            rw [← e''] at hU
            exact hU (.inr (.inl ⟨qk, p, hwf.symm hl⟩))

/-- **Along a run, a claim never gives a name that the program already
has.**  From a well-formed net, under any schedule: whenever a thread
holds `a` and its partner `b` is in the memory with a rule for the pair,
the names of the agents the rule creates occur nowhere in the state. -/
theorem XMach.fresh_names {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) (i : Nat) {t : Nat} {todo : List (Id × S)} {a b : Id} {α β : S}
    {R : XRhs S}
    (hT : ((XMach.init X nt).trace xs σ i).1.ths[t]? = some ⟨todo, .half a b α β⟩)
    (hb : (b, β) ∈ ((XMach.init X nt).trace xs σ i).1.mem.agents) (hne : a ≠ b)
    (hr : xs.rule α β = some R) {j : Id} {γ : S} (hj : (j, γ) ∈ R.newAgents a b) :
    ¬ ((XMach.init X nt).trace xs σ i).1.Mentions j :=
  XMach.claim_fresh (XMach.trace_live σ (XMach.init_live hX hnt) i)
    (XMach.trace_wired σ (XMach.init_wired X nt) i) hT hb hne hr hj

end FreshNames

/-! ### The program does not depend on the names

An action of a thread looks names up and compares them; it never looks
inside one, except to name the agents a claim creates.  So if the memory
and the thread are renamed by a map that keeps apart the names they hold,
the action does the same thing on the renamed state. -/

section RenameAct

variable [DecidableEq S] {xs : XSys S}

/-- A renaming of the names a thread has in hand. -/
def TState.map (f : Id → Id) : TState S → TState S
  | .idle => .idle
  | .look a α => .look (f a) α
  | .seek a α p c => .seek (f a) α (f p.1, p.2) (f c.1, c.2)
  | .ready a b α β => .ready (f a) (f b) α β
  | .half a b α β => .half (f a) (f b) α β
  | .write as ls =>
    .write (as.map fun e => (f e.1, e.2))
      (ls.map fun e => ((f e.1.1, e.1.2), (f e.2.1, e.2.2)))

/-- A renaming of a thread. -/
def XThread.map (f : Id → Id) (T : XThread S) : XThread S :=
  ⟨T.todo.map fun e => (f e.1, e.2), T.st.map f⟩

theorem assoc_map_inj {V : Type} {f : Id → Id} {P : Id → Prop}
    (hf : ∀ i j, P i → P j → f i = f j → i = j) {a : Id} (ha : P a) :
    ∀ (l : List (Id × V)), (∀ e ∈ l, P e.1) →
      assoc (f a) (l.map fun e => (f e.1, e.2)) = assoc a l
  | [], _ => rfl
  | (k, v) :: l, h => by
    have hk : P k := h (k, v) List.mem_cons_self
    have ih := assoc_map_inj hf ha l (fun e he => h e (List.mem_cons_of_mem _ he))
    show (if f k = f a then some v else assoc (f a) (l.map fun e => (f e.1, e.2))) =
      if k = a then some v else assoc a l
    by_cases e : k = a
    · rw [ite_pos' e, ite_pos' (congrArg f e)]
    · rw [ite_neg' e, ite_neg' (fun e' => e (hf k a hk ha e')), ih]

theorem port_map_inj {f : Id → Id} {P : Id → Prop}
    (hf : ∀ i j, P i → P j → f i = f j → i = j) {p q : Port} (hp : P p.1) (hq : P q.1) :
    ((f p.1, p.2) : Port) = (f q.1, q.2) ↔ p = q := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    obtain ⟨pi, pk⟩ := p
    obtain ⟨qi, qk⟩ := q
    have e₁ : pi = qi := hf pi qi hp hq h₁
    have e₂ : pk = qk := h₂
    rw [e₁, e₂]
  · intro h
    rw [h]

theorem assoc_port_map {f : Id → Id} {P : Id → Prop}
    (hf : ∀ i j, P i → P j → f i = f j → i = j) {p : Port} (hp : P p.1) :
    ∀ (l : List (Port × Port)), (∀ e ∈ l, P e.1.1) →
      assoc ((f p.1, p.2) : Port) (l.map fun e => ((f e.1.1, e.1.2), (f e.2.1, e.2.2))) =
        (assoc p l).map fun q => (f q.1, q.2)
  | [], _ => rfl
  | (k, v) :: l, h => by
    have hk : P k.1 := h (k, v) List.mem_cons_self
    have ih := assoc_port_map hf hp l (fun e he => h e (List.mem_cons_of_mem _ he))
    show (if ((f k.1, k.2) : Port) = (f p.1, p.2) then some ((f v.1, v.2) : Port)
        else assoc ((f p.1, p.2) : Port)
          (l.map fun e => ((f e.1.1, e.1.2), (f e.2.1, e.2.2)))) =
      (if k = p then some v else assoc p l).map fun q => (f q.1, q.2)
    by_cases e : k = p
    · rw [ite_pos' e, ite_pos' ((port_map_inj hf hk hp).2 e)]
      rfl
    · rw [ite_neg' e, ite_neg' (fun e' => e ((port_map_inj hf hk hp).1 e')), ih]

theorem nextSeg_map {f : Id → Id} {P : Id → Prop}
    (hf : ∀ i j, P i → P j → f i = f j → i = j) {c p : Port} (hc : P c.1) (hp : P p.1) :
    ∀ (l : List (Port × Port)), (∀ e ∈ l, P e.1.1 ∧ P e.2.1) →
      nextSeg (l.map fun e => ((f e.1.1, e.1.2), (f e.2.1, e.2.2))) (f c.1, c.2) (f p.1, p.2) =
        (nextSeg l c p).map fun q => (f q.1, q.2)
  | [], _ => rfl
  | e :: l, h => by
    obtain ⟨h₁, h₂⟩ := h e List.mem_cons_self
    have ih := nextSeg_map hf hc hp l (fun e he => h e (List.mem_cons_of_mem _ he))
    show (if ((f e.1.1, e.1.2) : Port) = (f c.1, c.2) ∧ ((f e.2.1, e.2.2) : Port) ≠ (f p.1, p.2)
        then some ((f e.2.1, e.2.2) : Port)
        else nextSeg (l.map fun e => ((f e.1.1, e.1.2), (f e.2.1, e.2.2))) (f c.1, c.2)
          (f p.1, p.2)) =
      (if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg l c p).map fun q => (f q.1, q.2)
    by_cases hcnd : e.1 = c ∧ e.2 ≠ p
    · have hcnd' : ((f e.1.1, e.1.2) : Port) = (f c.1, c.2) ∧
          ((f e.2.1, e.2.2) : Port) ≠ (f p.1, p.2) :=
        ⟨(port_map_inj hf h₁ hc).2 hcnd.1, fun e' => hcnd.2 ((port_map_inj hf h₂ hp).1 e')⟩
      rw [ite_pos' hcnd, ite_pos' hcnd']
      rfl
    · have hcnd' : ¬ (((f e.1.1, e.1.2) : Port) = (f c.1, c.2) ∧
          ((f e.2.1, e.2.2) : Port) ≠ (f p.1, p.2)) := fun hh =>
        hcnd ⟨(port_map_inj hf h₁ hc).1 hh.1, fun e' => hh.2 ((port_map_inj hf h₂ hp).2 e')⟩
      rw [ite_neg' hcnd, ite_neg' hcnd', ih]

omit [DecidableEq S] in
theorem XNet.takeAgent_map {f : Id → Id} {P : Id → Prop}
    (hf : ∀ i j, P i → P j → f i = f j → i = j) {X : XNet S} (hA : ∀ e ∈ X.agents, P e.1)
    {a : Id} (ha : P a) : (X.map f).takeAgent (f a) = (X.takeAgent a).map f := by
  have h : ∀ (l : List (Id × S)), (∀ e ∈ l, P e.1) →
      (l.map fun e => (f e.1, e.2)).filter (fun e => decide (e.1 ≠ f a)) =
        (l.filter fun e => decide (e.1 ≠ a)).map fun e => (f e.1, e.2) := by
    intro l hl
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x hx
    show decide (f x.1 ≠ f a) = decide (x.1 ≠ a)
    exact decide_eq_decide.2
      ⟨fun h e => h (congrArg f e), fun h e => h (hf x.1 a (hl x hx) ha e)⟩
  show (⟨(X.agents.map fun e => (f e.1, e.2)).filter (fun e => decide (e.1 ≠ f a)),
      X.free.map (mapPort f), X.wires.map fun e => (mapPort f e.1, mapPort f e.2)⟩ : XNet S) =
    ⟨(X.agents.filter fun e => decide (e.1 ≠ a)).map fun e => (f e.1, e.2),
      X.free.map (mapPort f), X.wires.map fun e => (mapPort f e.1, mapPort f e.2)⟩
  rw [h X.agents hA]

/-- **An action does not depend on the names.**  Rename the memory and the
thread by a map that keeps apart the names they hold.  Then the action
leaves the renamed memory and claims as before; and unless it claims, it
leaves the renamed thread.  A claim names new agents after the two that
fire, so there the thread holds names that depend on the renaming. -/
theorem XMach.act_map (xs : XSys S) {f : Id → Id} {P : Id → Prop}
    (hf : ∀ i j, P i → P j → f i = f j → i = j) {X : XNet S} {T : XThread S}
    (hA : ∀ e ∈ X.agents, P e.1) (hW : ∀ e ∈ X.wires, P e.1.1 ∧ P e.2.1)
    (hTd : ∀ e ∈ T.todo, P e.1) (hTs : ∀ i, T.st.Mentions i → P i) :
    (XMach.act xs (X.map f) (T.map f)).1 = (XMach.act xs X T).1.map f ∧
      (XMach.act xs (X.map f) (T.map f)).2.2 = (XMach.act xs X T).2.2 ∧
      ((XMach.act xs X T).2.2 = 0 →
        (XMach.act xs (X.map f) (T.map f)).2.1 = (XMach.act xs X T).2.1.map f) := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨rfl, rfl, fun _ => rfl⟩
    | cons e rest =>
      have he : P e.1 := hTd e List.mem_cons_self
      have eR : XMach.act xs X ⟨e :: rest, .idle⟩ =
          if assoc e.1 X.agents = some e.2 then (X, ⟨rest, .look e.1 e.2⟩, 0)
          else (X, ⟨rest, .idle⟩, 0) := rfl
      have eL : XMach.act xs (X.map f) (XThread.map f ⟨e :: rest, .idle⟩) =
          if assoc e.1 X.agents = some e.2 then
            (X.map f, ⟨rest.map fun e => (f e.1, e.2), .look (f e.1) e.2⟩, 0)
          else (X.map f, ⟨rest.map fun e => (f e.1, e.2), .idle⟩, 0) := by
        rw [← assoc_map_inj hf he X.agents hA]
        rfl
      rw [eL, eR]
      by_cases h : assoc e.1 X.agents = some e.2
      · rw [ite_pos' h, ite_pos' h]
        exact ⟨rfl, rfl, fun _ => rfl⟩
      · rw [ite_neg' h, ite_neg' h]
        exact ⟨rfl, rfl, fun _ => rfl⟩
  | look a α =>
    have ha : P a := hTs a rfl
    have eR : XMach.act xs X ⟨todo, .look a α⟩ =
        match assoc ((a, 0) : Port) X.wires with
        | some q => (X, ⟨todo, .seek a α (a, 0) q⟩, 0)
        | none => (X, ⟨todo, .idle⟩, 0) := rfl
    have eL : XMach.act xs (X.map f) (XThread.map f ⟨todo, .look a α⟩) =
        match (assoc ((a, 0) : Port) X.wires).map fun q => ((f q.1, q.2) : Port) with
        | some q => (X.map f, ⟨todo.map fun e => (f e.1, e.2), .seek (f a) α (f a, 0) q⟩, 0)
        | none => (X.map f, ⟨todo.map fun e => (f e.1, e.2), .idle⟩, 0) := by
      rw [← assoc_port_map hf (p := (a, 0)) ha X.wires (fun e he => (hW e he).1)]
      rfl
    rw [eL, eR]
    cases assoc ((a, 0) : Port) X.wires with
    | none => exact ⟨rfl, rfl, fun _ => rfl⟩
    | some q => exact ⟨rfl, rfl, fun _ => rfl⟩
  | seek a α p c =>
    have ha : P a := hTs a (.inl rfl)
    have hp : P p.1 := hTs p.1 (.inr (.inl rfl))
    have hc : P c.1 := hTs c.1 (.inr (.inr rfl))
    have hne : (f a ≠ f c.1) ↔ (a ≠ c.1) :=
      ⟨fun h e => h (congrArg f e), fun h e => h (hf a c.1 ha hc e)⟩
    have eR : XMach.act xs X ⟨todo, .seek a α p c⟩ =
        match (if c.2 = 0 then assoc c.1 X.agents else none) with
        | some β =>
          if a ≠ c.1 ∧ (xs.rule α β).isSome then (X, ⟨todo, .ready a c.1 α β⟩, 0)
          else (X, ⟨todo, .idle⟩, 0)
        | none =>
          match nextSeg X.wires c p with
          | some q => (X, ⟨todo, .seek a α c q⟩, 0)
          | none => (X, ⟨todo, .idle⟩, 0) := rfl
    have eL : XMach.act xs (X.map f) (XThread.map f ⟨todo, .seek a α p c⟩) =
        match (if c.2 = 0 then assoc c.1 X.agents else none) with
        | some β =>
          if f a ≠ f c.1 ∧ (xs.rule α β).isSome then
            (X.map f, ⟨todo.map fun e => (f e.1, e.2), .ready (f a) (f c.1) α β⟩, 0)
          else (X.map f, ⟨todo.map fun e => (f e.1, e.2), .idle⟩, 0)
        | none =>
          match (nextSeg X.wires c p).map fun q => ((f q.1, q.2) : Port) with
          | some q =>
            (X.map f, ⟨todo.map fun e => (f e.1, e.2), .seek (f a) α (f c.1, c.2) q⟩, 0)
          | none => (X.map f, ⟨todo.map fun e => (f e.1, e.2), .idle⟩, 0) := by
      rw [← assoc_map_inj hf hc X.agents hA, ← nextSeg_map hf hc hp X.wires hW]
      rfl
    rw [eL, eR]
    cases (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some β =>
      dsimp only
      by_cases h : a ≠ c.1 ∧ (xs.rule α β).isSome
      · have h' : f a ≠ f c.1 ∧ (xs.rule α β).isSome := ⟨hne.2 h.1, h.2⟩
        rw [ite_pos' h, ite_pos' h']
        exact ⟨rfl, rfl, fun _ => rfl⟩
      · have h' : ¬ (f a ≠ f c.1 ∧ (xs.rule α β).isSome) := fun hh => h ⟨hne.1 hh.1, hh.2⟩
        rw [ite_neg' h, ite_neg' h']
        exact ⟨rfl, rfl, fun _ => rfl⟩
    | none =>
      dsimp only
      cases nextSeg X.wires c p with
      | none => exact ⟨rfl, rfl, fun _ => rfl⟩
      | some q => exact ⟨rfl, rfl, fun _ => rfl⟩
  | ready a b α β =>
    have ha : P a := hTs a (.inl rfl)
    have eR : XMach.act xs X ⟨todo, .ready a b α β⟩ =
        if assoc a X.agents = some α then (X.takeAgent a, ⟨todo, .half a b α β⟩, 0)
        else (X, ⟨todo, .idle⟩, 0) := rfl
    have eL : XMach.act xs (X.map f) (XThread.map f ⟨todo, .ready a b α β⟩) =
        if assoc a X.agents = some α then
          ((X.map f).takeAgent (f a),
            ⟨todo.map fun e => (f e.1, e.2), .half (f a) (f b) α β⟩, 0)
        else (X.map f, ⟨todo.map fun e => (f e.1, e.2), .idle⟩, 0) := by
      rw [← assoc_map_inj hf ha X.agents hA]
      rfl
    rw [eL, eR]
    by_cases h : assoc a X.agents = some α
    · rw [ite_pos' h, ite_pos' h]
      exact ⟨XNet.takeAgent_map hf hA ha, rfl, fun _ => rfl⟩
    · rw [ite_neg' h, ite_neg' h]
      exact ⟨rfl, rfl, fun _ => rfl⟩
  | half a b α β =>
    have ha : P a := hTs a (.inl rfl)
    have hb : P b := hTs b (.inr rfl)
    have hne : (f a ≠ f b) ↔ (a ≠ b) :=
      ⟨fun h e => h (congrArg f e), fun h e => h (hf a b ha hb e)⟩
    have eR : XMach.act xs X ⟨todo, .half a b α β⟩ =
        match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
        | some R =>
          (X.takeAgent b,
            ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1)
        | none => (X.putAgent a α, ⟨todo, .idle⟩, 0) := rfl
    have eL : XMach.act xs (X.map f) (XThread.map f ⟨todo, .half a b α β⟩) =
        match (if assoc b X.agents = some β ∧ f a ≠ f b then xs.rule α β else none) with
        | some R =>
          ((X.map f).takeAgent (f b),
            ⟨todo.map fun e => (f e.1, e.2),
              .write (R.newAgents (f a) (f b)) (R.newLinks xs.sys.ar (f a) (f b) α β)⟩, 1)
        | none => ((X.map f).putAgent (f a) α, ⟨todo.map fun e => (f e.1, e.2), .idle⟩, 0) := by
      rw [← assoc_map_inj hf hb X.agents hA]
      rfl
    rw [eL, eR]
    by_cases h : assoc b X.agents = some β ∧ a ≠ b
    · have h' : assoc b X.agents = some β ∧ f a ≠ f b := ⟨h.1, hne.2 h.2⟩
      rw [ite_pos' h, ite_pos' h']
      cases xs.rule α β with
      | none => exact ⟨rfl, rfl, fun _ => rfl⟩
      | some R => exact ⟨XNet.takeAgent_map hf hA hb, rfl, fun h => by cases h⟩
    · have h' : ¬ (assoc b X.agents = some β ∧ f a ≠ f b) := fun hh => h ⟨hh.1, hne.1 hh.2⟩
      rw [ite_neg' h, ite_neg' h']
      exact ⟨rfl, rfl, fun _ => rfl⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨rfl, rfl, fun _ => rfl⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨rfl, rfl, fun _ => rfl⟩
      | nil => exact ⟨rfl, rfl, fun _ => rfl⟩

end RenameAct

/-! ### Numbered names

The program on lists names a new agent by the names of the two agents
that met, with one more cell in front, so its names grow with the run.
Here is the same program with a counter: a claim names the agents it
creates by the next numbers.  Its names are numbers of one cell, or names
of the net it started from.

It does what the named program does.  The two states are not equal, and
no fixed renaming relates the two runs: the renaming is carried along, and
each claim extends it by the names of the agents created.  A claim never
gives a name that the state already has (`XMach.child_fresh`), so the
extended renaming still keeps the names apart, and an action does the same
on a renamed state (`XMach.act_map`). -/

theorem dedupFst_sub {A B : Type} [DecidableEq A] :
    ∀ (l : List (A × B)) (x : A × B), x ∈ dedupFst l → x ∈ l
  | [], _, h => h
  | e :: l, x, h => by
    unfold dedupFst at h
    split at h
    · exact List.mem_cons_of_mem _ (dedupFst_sub l x h)
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (dedupFst_sub l x h')

/-- Keeping one pair for each name commutes with a renaming that keeps the
names of the list apart. -/
theorem dedupFst_map {A A' B : Type} [DecidableEq A] [DecidableEq A'] (h : A → A') :
    ∀ (l : List (A × B)), (∀ x ∈ l, ∀ y ∈ l, h x.1 = h y.1 → x.1 = y.1) →
      dedupFst (l.map fun e => (h e.1, e.2)) = (dedupFst l).map fun e => (h e.1, e.2)
  | [], _ => rfl
  | e :: l, hinj => by
    have ih := dedupFst_map h l
      (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    have hm : (h e.1 ∈ ((dedupFst l).map fun e => (h e.1, e.2)).map Prod.fst) ↔
        (e.1 ∈ (dedupFst l).map Prod.fst) := by
      constructor
      · intro hh
        obtain ⟨y', hy', ey'⟩ := List.mem_map.1 hh
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hy'
        have e' : h y.1 = h e.1 := ey'
        exact List.mem_map.2 ⟨y, hy,
          hinj y (List.mem_cons_of_mem _ (dedupFst_sub l y hy)) e List.mem_cons_self e'⟩
      · intro hh
        obtain ⟨y, hy, ey⟩ := List.mem_map.1 hh
        refine List.mem_map.2 ⟨(h y.1, y.2), List.mem_map.2 ⟨y, hy, rfl⟩, ?_⟩
        show h y.1 = h e.1
        rw [ey]
    have eL : dedupFst ((e :: l).map fun e => (h e.1, e.2)) =
        if h e.1 ∈ (dedupFst (l.map fun e => (h e.1, e.2))).map Prod.fst then
          dedupFst (l.map fun e => (h e.1, e.2))
        else (h e.1, e.2) :: dedupFst (l.map fun e => (h e.1, e.2)) := rfl
    have eR : dedupFst (e :: l) =
        if e.1 ∈ (dedupFst l).map Prod.fst then dedupFst l else e :: dedupFst l := rfl
    rw [eL, eR, ih]
    by_cases c : e.1 ∈ (dedupFst l).map Prod.fst
    · rw [ite_pos' c, ite_pos' (hm.2 c)]
    · rw [ite_neg' c, ite_neg' (fun c' => c (hm.1 c'))]
      rfl

theorem filterMap_congr' {A B : Type} {f g : A → Option B} :
    ∀ (l : List A), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    have ih := filterMap_congr' l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self, ih]

theorem le_foldr_max : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr max 0
  | [], _, h => by cases h
  | y :: l, x, h => by
    show x ≤ max y (l.foldr max 0)
    rcases List.mem_cons.1 h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max l x h') (Nat.le_max_right _ _)

/-- A number for each owner of a new agent. -/
def ocode : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

theorem ocode_lt (o : Option Bool) : ocode o < 3 := by
  cases o with
  | none => exact Nat.le_of_ble_eq_true rfl
  | some s => cases s <;> exact Nat.le_of_ble_eq_true rfl

/-- **The numbered name of a new agent**: one cell, a number above every
number given before. -/
def numName (cnt : Nat) (o : Option Bool) (j : Nat) : Id := [cnt + (3 * j + ocode o)]

theorem numName_inj {cnt : Nat} {o o' : Option Bool} {j j' : Nat}
    (h : numName cnt o j = numName cnt o' j') : o = o' ∧ j = j' := by
  have e : cnt + (3 * j + ocode o) = cnt + (3 * j' + ocode o') := by
    injection h
  have h₁ := ocode_lt o
  have h₂ := ocode_lt o'
  have ej : j = j' := by omega
  have eo : ocode o = ocode o' := by omega
  refine ⟨?_, ej⟩
  revert eo
  cases o with
  | none =>
    cases o' with
    | none => intro _; rfl
    | some s => cases s <;> intro h <;> exact absurd h (by decide)
  | some s =>
    cases o' with
    | none => cases s <;> intro h <;> exact absurd h (by decide)
    | some s' => cases s <;> cases s' <;> intro h <;> first | rfl | exact absurd h (by decide)

section Numbered

/-- The numbers a rule needs for its new agents. -/
def XRhs.span (R : XRhs S) : Nat := (R.slots.map fun e => 3 * e.2 + ocode e.1 + 1).foldr max 0

theorem XRhs.lt_span (R : XRhs S) {o : Option Bool} {j : Nat} (h : (o, j) ∈ R.slots) :
    3 * j + ocode o < R.span :=
  le_foldr_max _ _ (List.mem_map.2 ⟨(o, j), h, rfl⟩)

/-- Where a port of the right-hand side lands when the new agents are
numbered from `cnt`. -/
def embN (a b : Id) (cnt : Nat) : LPort → Port
  | .ifc s k => (sel a b s, k + 1)
  | .new o j k => (numName cnt o j, k)

/-- **The agents to write, numbered from `cnt`.** -/
def XRhs.numAgents (R : XRhs S) (cnt : Nat) : List (Id × S) :=
  dedupFst (R.slots.filterMap fun e => (R.lab e.1 e.2).map fun γ => (numName cnt e.1 e.2, γ))

/-- **The segments to write, the new agents numbered from `cnt`.** -/
def XRhs.numLinks (R : XRhs S) (ar : S → Nat) (a b : Id) (cnt : Nat) (α β : S) :
    List (Port × Port) :=
  (ifcPorts ar α β ++ R.newPorts ar).filterMap fun x =>
    match R.wire x with
    | some y => some (embN a b cnt x, embN a b cnt y)
    | none => none

/-- **The named agents are the numbered ones renamed**, by any map that
sends the numbered names to the names of the children. -/
theorem XRhs.newAgents_num (R : XRhs S) {a' b' : Id} (hne : a' ≠ b') (cnt : Nat)
    {h : Id → Id} (hh : ∀ o j, h (numName cnt o j) = child a' b' o j) :
    R.newAgents a' b' = (R.numAgents cnt).map fun e => (h e.1, e.2) := by
  have e₁ : childList a' b' R.lab R.slots =
      (R.slots.filterMap fun e => (R.lab e.1 e.2).map fun γ => (numName cnt e.1 e.2, γ)).map
        fun e => (h e.1, e.2) := by
    rw [List.map_filterMap]
    unfold childList
    refine filterMap_congr' _ (fun e _ => ?_)
    cases R.lab e.1 e.2 with
    | none => rfl
    | some γ =>
      show some (child a' b' e.1 e.2, γ) = some (h (numName cnt e.1 e.2), γ)
      rw [hh]
  show dedupFst (childList a' b' R.lab R.slots) = _
  rw [e₁]
  refine dedupFst_map h _ (fun x hx y hy exy => ?_)
  obtain ⟨ex, -, hex⟩ := List.mem_filterMap.1 hx
  obtain ⟨ey, -, hey⟩ := List.mem_filterMap.1 hy
  cases hlx : R.lab ex.1 ex.2 with
  | none =>
    rw [hlx] at hex
    cases hex
  | some γx =>
    cases hly : R.lab ey.1 ey.2 with
    | none =>
      rw [hly] at hey
      cases hey
    | some γy =>
      rw [hlx] at hex
      rw [hly] at hey
      have e₂ : x = (numName cnt ex.1 ex.2, γx) := (Option.some.inj hex).symm
      have e₃ : y = (numName cnt ey.1 ey.2, γy) := (Option.some.inj hey).symm
      rw [e₂, e₃] at exy
      have exy' : h (numName cnt ex.1 ex.2) = h (numName cnt ey.1 ey.2) := exy
      rw [hh, hh] at exy'
      obtain ⟨eo, ej⟩ := child_inj' hne exy'
      rw [e₂, e₃]
      show numName cnt ex.1 ex.2 = numName cnt ey.1 ey.2
      rw [eo, ej]

/-- **The named segments are the numbered ones renamed.** -/
theorem XRhs.newLinks_num (R : XRhs S) (ar : S → Nat) {a b a' b' : Id} (cnt : Nat) (α β : S)
    {h : Id → Id} (ha : h a = a') (hb : h b = b')
    (hh : ∀ o j, h (numName cnt o j) = child a' b' o j) :
    R.newLinks ar a' b' α β =
      (R.numLinks ar a b cnt α β).map fun e => ((h e.1.1, e.1.2), (h e.2.1, e.2.2)) := by
  have he : ∀ x : LPort, emb a' b' x = (h (embN a b cnt x).1, (embN a b cnt x).2) := by
    intro x
    cases x with
    | ifc s k =>
      cases s
      · show ((a', k + 1) : Port) = (h a, k + 1)
        rw [ha]
      · show ((b', k + 1) : Port) = (h b, k + 1)
        rw [hb]
    | new o j k =>
      show ((child a' b' o j, k) : Port) = (h (numName cnt o j), k)
      rw [hh]
  unfold XRhs.numLinks
  rw [List.map_filterMap]
  show (ifcPorts ar α β ++ R.newPorts ar).filterMap _ = _
  refine filterMap_congr' _ (fun x _ => ?_)
  cases R.wire x with
  | none => rfl
  | some y =>
    show some (emb a' b' x, emb a' b' y) = some ((h (embN a b cnt x).1, (embN a b cnt x).2),
      (h (embN a b cnt y).1, (embN a b cnt y).2))
    rw [he x, he y]

/-- The names of the numbered agents are numbered names of slots of the
rule. -/
theorem XRhs.numAgents_name (R : XRhs S) (cnt : Nat) {e : Id × S} (he : e ∈ R.numAgents cnt) :
    ∃ o j, (o, j) ∈ R.slots ∧ e.1 = numName cnt o j := by
  obtain ⟨s, hs, hes⟩ := List.mem_filterMap.1 (dedupFst_sub _ e he)
  cases hl : R.lab s.1 s.2 with
  | none =>
    rw [hl] at hes
    cases hes
  | some γ =>
    rw [hl] at hes
    have e' : e = (numName cnt s.1 s.2, γ) := (Option.some.inj hes).symm
    exact ⟨s.1, s.2, hs, by rw [e']⟩

/-- A wire of a rule of the system arrives at a slot of the rule. -/
theorem XSys.wire_slots (xs : XSys S) {α β : S} {R : XRhs S} (hr : xs.rule α β = some R)
    {x : LPort} {o : Option Bool} {j k : Nat} (hw : R.wire x = some (.new o j k)) :
    (o, j) ∈ R.slots := by
  have h : xs.sys.rule α β = some R.toRhs := by
    rw [xs.rule_spec, hr]
    rfl
  have hwf := xs.sys.rule_wf h
  have hl : R.toRhs.link x (.new o j k) := hw
  obtain ⟨γ, hγ, -⟩ := hwf.valid (hwf.symm hl)
  exact xs.slots_spec hr hγ

/-- The names on the numbered segments are those of the two that fire and
numbered names of slots of the rule. -/
theorem XSys.numLinks_name (xs : XSys S) {α β : S} {R : XRhs S} (hr : xs.rule α β = some R)
    (a b : Id) (cnt : Nat) {e : Port × Port} (he : e ∈ R.numLinks xs.sys.ar a b cnt α β) :
    (e.1.1 = a ∨ e.1.1 = b ∨ ∃ o j, (o, j) ∈ R.slots ∧ e.1.1 = numName cnt o j) ∧
      (e.2.1 = a ∨ e.2.1 = b ∨ ∃ o j, (o, j) ∈ R.slots ∧ e.2.1 = numName cnt o j) := by
  have hname : ∀ x : LPort, (∀ o j k, x = .new o j k → (o, j) ∈ R.slots) →
      ((embN a b cnt x).1 = a ∨ (embN a b cnt x).1 = b ∨
        ∃ o j, (o, j) ∈ R.slots ∧ (embN a b cnt x).1 = numName cnt o j) := by
    intro x hx
    cases x with
    | ifc s k =>
      cases s
      · exact .inl rfl
      · exact .inr (.inl rfl)
    | new o j k => exact .inr (.inr ⟨o, j, hx o j k rfl, rfl⟩)
  obtain ⟨x, hx, hex⟩ := List.mem_filterMap.1 he
  cases hw : R.wire x with
  | none =>
    rw [hw] at hex
    cases hex
  | some y =>
    rw [hw] at hex
    have e' : e = (embN a b cnt x, embN a b cnt y) := (Option.some.inj hex).symm
    rw [e']
    refine ⟨hname x ?_, hname y ?_⟩
    · intro o j k exo
      rcases List.mem_append.1 hx with h' | h'
      · obtain ⟨_, _, e''⟩ : ∃ s k', x = .ifc s k' := by
          unfold ifcPorts at h'
          rcases List.mem_append.1 h' with h'' | h''
          · obtain ⟨k', -, e3⟩ := List.mem_map.1 h''
            exact ⟨false, k', e3.symm⟩
          · obtain ⟨k', -, e3⟩ := List.mem_map.1 h''
            exact ⟨true, k', e3.symm⟩
        rw [e''] at exo
        cases exo
      · obtain ⟨o', j', k', γ, e'', hs, -, -⟩ := XRhs.mem_newPorts.1 h'
        rw [e''] at exo
        injection exo with e₁ e₂ e₃
        rw [← e₁, ← e₂]
        exact hs
    · intro o j k eyo
      rw [eyo] at hw
      exact xs.wire_slots hr hw

end Numbered

section Closure

variable [DecidableEq S] {xs : XSys S}

/-- Every name of the memory satisfies `Q`. -/
def XNet.All (Q : Id → Prop) (X : XNet S) : Prop :=
  (∀ e ∈ X.agents, Q e.1) ∧ ∀ e ∈ X.wires, Q e.1.1 ∧ Q e.2.1

/-- Every name of the thread satisfies `Q`. -/
def XThread.All (Q : Id → Prop) (T : XThread S) : Prop :=
  (∀ e ∈ T.todo, Q e.1) ∧ ∀ i, T.st.Mentions i → Q i

omit [DecidableEq S] in
theorem XNet.All.take {Q : Id → Prop} {X : XNet S} (h : X.All Q) (a : Id) :
    (X.takeAgent a).All Q :=
  ⟨fun e he => h.1 e (List.mem_filter.1 he).1, h.2⟩

omit [DecidableEq S] in
theorem XNet.All.put {Q : Id → Prop} {X : XNet S} (h : X.All Q) {i : Id} (hi : Q i) (γ : S) :
    (X.putAgent i γ).All Q := by
  refine ⟨fun e he => ?_, h.2⟩
  have he' : e ∈ (i, γ) :: X.agents := he
  rcases List.mem_cons.1 he' with rfl | he''
  · exact hi
  · exact h.1 e he''

omit [DecidableEq S] in
theorem XNet.All.link {Q : Id → Prop} {X : XNet S} (h : X.All Q) {p q : Port} (hp : Q p.1)
    (hq : Q q.1) : (X.putLink p q).All Q := by
  refine ⟨h.1, fun e he => ?_⟩
  have he' : e ∈ (p, q) :: X.wires := he
  rcases List.mem_cons.1 he' with rfl | he''
  · exact ⟨hp, hq⟩
  · exact h.2 e he''

/-- **An action brings in no name, unless it claims.**  If every name of
the memory and of the thread satisfies `Q`, so does every name of the
memory after the action, and of the thread unless the action claims. -/
theorem XMach.act_all (xs : XSys S) {Q : Id → Prop} {X : XNet S} {T : XThread S}
    (hX : X.All Q) (hT : T.All Q) :
    (XMach.act xs X T).1.All Q ∧
      ((XMach.act xs X T).2.2 = 0 → (XMach.act xs X T).2.1.All Q) := by
  obtain ⟨todo, st⟩ := T
  obtain ⟨hTd, hTs⟩ := hT
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨hX, fun _ => ⟨hTd, hTs⟩⟩
    | cons e rest =>
      cases hact : XMach.act xs X ⟨e :: rest, .idle⟩ with
      | mk X' r =>
        obtain ⟨T', k⟩ := r
        unfold XMach.act at hact
        dsimp only at hact
        have hr : ∀ x ∈ rest, Q x.1 := fun x hx => hTd x (List.mem_cons_of_mem _ hx)
        split at hact
        · cases hact
          refine ⟨hX, fun _ => ⟨hr, fun i hi => ?_⟩⟩
          have e' : i = e.1 := hi
          rw [e']
          exact hTd e List.mem_cons_self
        · cases hact
          exact ⟨hX, fun _ => ⟨hr, fun i hi => absurd hi id⟩⟩
  | look a α =>
    have ha : Q a := hTs a rfl
    cases hact : XMach.act xs X ⟨todo, .look a α⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · rename_i q hq
        cases hact
        have hq' := (hX.2 _ (assoc_mem hq)).2
        refine ⟨hX, fun _ => ⟨hTd, fun i hi => ?_⟩⟩
        have hi' : i = a ∨ i = a ∨ i = q.1 := hi
        rcases hi' with e' | e' | e' <;> rw [e']
        · exact ha
        · exact ha
        · exact hq'
      · cases hact
        exact ⟨hX, fun _ => ⟨hTd, fun i hi => absurd hi id⟩⟩
  | seek a α p c =>
    have ha : Q a := hTs a (.inl rfl)
    have hc : Q c.1 := hTs c.1 (.inr (.inr rfl))
    cases hact : XMach.act xs X ⟨todo, .seek a α p c⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · split at hact
        · cases hact
          refine ⟨hX, fun _ => ⟨hTd, fun i hi => ?_⟩⟩
          have hi' : i = a ∨ i = c.1 := hi
          rcases hi' with e' | e' <;> rw [e']
          · exact ha
          · exact hc
        · cases hact
          exact ⟨hX, fun _ => ⟨hTd, fun i hi => absurd hi id⟩⟩
      · split at hact
        · rename_i q hq
          cases hact
          have hq' := (hX.2 _ (nextSeg_spec hq).1).2
          refine ⟨hX, fun _ => ⟨hTd, fun i hi => ?_⟩⟩
          have hi' : i = a ∨ i = c.1 ∨ i = q.1 := hi
          rcases hi' with e' | e' | e' <;> rw [e']
          · exact ha
          · exact hc
          · exact hq'
        · cases hact
          exact ⟨hX, fun _ => ⟨hTd, fun i hi => absurd hi id⟩⟩
  | ready a b α β =>
    have ha : Q a := hTs a (.inl rfl)
    have hb : Q b := hTs b (.inr rfl)
    cases hact : XMach.act xs X ⟨todo, .ready a b α β⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · cases hact
        refine ⟨hX.take a, fun _ => ⟨hTd, fun i hi => ?_⟩⟩
        have hi' : i = a ∨ i = b := hi
        rcases hi' with e' | e' <;> rw [e']
        · exact ha
        · exact hb
      · cases hact
        exact ⟨hX, fun _ => ⟨hTd, fun i hi => absurd hi id⟩⟩
  | half a b α β =>
    have ha : Q a := hTs a (.inl rfl)
    cases hact : XMach.act xs X ⟨todo, .half a b α β⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · cases hact
        exact ⟨hX.take b, fun h => by cases h⟩
      · cases hact
        exact ⟨hX.put ha α, fun _ => ⟨hTd, fun i hi => absurd hi id⟩⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      refine ⟨hX.put (hTs i (.inl ⟨(i, γ), List.mem_cons_self, rfl⟩)) γ,
        fun _ => ⟨hTd, fun j hj => ?_⟩⟩
      have hj' : (∃ e ∈ as, e.1 = j) ∨ ∃ e ∈ ls, e.1.1 = j ∨ e.2.1 = j := hj
      rcases hj' with ⟨e, he, e'⟩ | ⟨e, he, e'⟩
      · exact hTs j (.inl ⟨e, List.mem_cons_of_mem _ he, e'⟩)
      · exact hTs j (.inr ⟨e, he, e'⟩)
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have hp : Q p.1 := hTs p.1 (.inr ⟨(p, q), List.mem_cons_self, .inl rfl⟩)
        have hq : Q q.1 := hTs q.1 (.inr ⟨(p, q), List.mem_cons_self, .inr rfl⟩)
        refine ⟨hX.link hp hq, fun _ => ⟨hTd, fun j hj => ?_⟩⟩
        have hj' : (∃ e ∈ ([] : List (Id × S)), e.1 = j) ∨ ∃ e ∈ ls, e.1.1 = j ∨ e.2.1 = j := hj
        rcases hj' with ⟨e, he, -⟩ | ⟨e, he, e'⟩
        · cases he
        · exact hTs j (.inr ⟨e, List.mem_cons_of_mem _ he, e'⟩)
      | nil => exact ⟨hX, fun _ => ⟨hX.1, fun i hi => absurd hi id⟩⟩

omit [DecidableEq S] in
theorem XNet.map_congr {f g : Id → Id} {X : XNet S} (hA : ∀ e ∈ X.agents, f e.1 = g e.1)
    (hW : ∀ e ∈ X.wires, f e.1.1 = g e.1.1 ∧ f e.2.1 = g e.2.1)
    (hF : ∀ p ∈ X.free, f p.1 = g p.1) : X.map f = X.map g := by
  show (⟨X.agents.map fun e => (f e.1, e.2), X.free.map (mapPort f),
      X.wires.map fun e => (mapPort f e.1, mapPort f e.2)⟩ : XNet S) =
    ⟨X.agents.map fun e => (g e.1, e.2), X.free.map (mapPort g),
      X.wires.map fun e => (mapPort g e.1, mapPort g e.2)⟩
  have e₁ : (X.agents.map fun e => (f e.1, e.2)) = X.agents.map fun e => (g e.1, e.2) :=
    List.map_congr_left (fun e he => by rw [hA e he])
  have e₂ : X.free.map (mapPort f) = X.free.map (mapPort g) :=
    List.map_congr_left (fun p hp => by
      show ((f p.1, p.2) : Port) = (g p.1, p.2)
      rw [hF p hp])
  have e₃ : (X.wires.map fun e => (mapPort f e.1, mapPort f e.2)) =
      X.wires.map fun e => (mapPort g e.1, mapPort g e.2) :=
    List.map_congr_left (fun e he => by
      show (((f e.1.1, e.1.2), (f e.2.1, e.2.2)) : Port × Port) =
        ((g e.1.1, e.1.2), (g e.2.1, e.2.2))
      rw [(hW e he).1, (hW e he).2])
  rw [e₁, e₂, e₃]

omit [DecidableEq S] in
theorem TState.map_congr {f g : Id → Id} {s : TState S} (h : ∀ i, s.Mentions i → f i = g i) :
    s.map f = s.map g := by
  cases s with
  | idle => rfl
  | look a α =>
    show TState.look (f a) α = .look (g a) α
    rw [h a rfl]
  | seek a α p c =>
    show TState.seek (f a) α (f p.1, p.2) (f c.1, c.2) = .seek (g a) α (g p.1, p.2) (g c.1, c.2)
    rw [h a (.inl rfl), h p.1 (.inr (.inl rfl)), h c.1 (.inr (.inr rfl))]
  | ready a b α β =>
    show TState.ready (f a) (f b) α β = .ready (g a) (g b) α β
    rw [h a (.inl rfl), h b (.inr rfl)]
  | half a b α β =>
    show TState.half (f a) (f b) α β = .half (g a) (g b) α β
    rw [h a (.inl rfl), h b (.inr rfl)]
  | write as ls =>
    have e₁ : (as.map fun e => (f e.1, e.2)) = as.map fun e => (g e.1, e.2) :=
      List.map_congr_left (fun e he => by rw [h e.1 (.inl ⟨e, he, rfl⟩)])
    have e₂ : (ls.map fun e => ((f e.1.1, e.1.2), (f e.2.1, e.2.2))) =
        ls.map fun e => ((g e.1.1, e.1.2), (g e.2.1, e.2.2)) :=
      List.map_congr_left (fun e he => by
        rw [h e.1.1 (.inr ⟨e, he, .inl rfl⟩), h e.2.1 (.inr ⟨e, he, .inr rfl⟩)])
    show TState.write (as.map fun e => (f e.1, e.2))
        (ls.map fun e => ((f e.1.1, e.1.2), (f e.2.1, e.2.2))) =
      .write (as.map fun e => (g e.1, e.2)) (ls.map fun e => ((g e.1.1, e.1.2), (g e.2.1, e.2.2)))
    rw [e₁, e₂]

omit [DecidableEq S] in
theorem XThread.map_congr {f g : Id → Id} {T : XThread S} (hd : ∀ e ∈ T.todo, f e.1 = g e.1)
    (hs : ∀ i, T.st.Mentions i → f i = g i) : T.map f = T.map g := by
  have e₁ : (T.todo.map fun e => (f e.1, e.2)) = T.todo.map fun e => (g e.1, e.2) :=
    List.map_congr_left (fun e he => by rw [hd e he])
  show (⟨T.todo.map fun e => (f e.1, e.2), T.st.map f⟩ : XThread S) =
    ⟨T.todo.map fun e => (g e.1, e.2), T.st.map g⟩
  rw [e₁, TState.map_congr hs]

omit [DecidableEq S] in
/-- **Every name the program holds is in use in the net it stands for.** -/
theorem XMach.mentions_used {M : XMach S} (hL : M.Live xs) (hW : M.Wired) {i : Id}
    (h : M.Mentions i) : M.toMach.goal.Used i := by
  have hwf := hL.inv.wf
  have agentU : ∀ i, M.mem.IsAgent i → M.toMach.goal.Used i :=
    fun i h => .inl ⟨h.choose, .inl (.inl h.choose_spec)⟩
  have linkU : ∀ {p q : Port}, M.toMach.goal.link p q →
      M.toMach.goal.Used p.1 ∧ M.toMach.goal.Used q.1 := by
    intro p q hl
    obtain ⟨pi, pk⟩ := p
    obtain ⟨qi, qk⟩ := q
    exact ⟨.inr (.inl ⟨pk, (qi, qk), hl⟩), .inr (.inl ⟨qk, (pi, pk), hwf.symm hl⟩)⟩
  have wireU : ∀ i, M.mem.OnWire i → M.toMach.goal.Used i := by
    intro i h
    obtain ⟨e, he, h'⟩ := h
    obtain ⟨p, q⟩ := e
    have hl : M.toMach.goal.link p q := .inl he
    rcases h' with h' | h'
    · have e' : p.1 = i := h'
      rw [← e']
      exact (linkU hl).1
    · have e' : q.1 = i := h'
      rw [← e']
      exact (linkU hl).2
  rcases h with h | h | ⟨T', hT', h⟩
  · exact agentU _ h
  · exact wireU _ h
  · have hw := hW T' hT'
    rcases h with ⟨e, he, e'⟩ | h
    · rw [← e']
      rcases hw.1 e he with h' | h'
      · exact agentU _ h'
      · exact wireU _ h'
    · obtain ⟨todo', st'⟩ := T'
      obtain ⟨u, hu⟩ := List.getElem?_of_mem hT'
      have hw2 : st'.Wired M.mem := hw.2
      cases st' with
      | idle => exact absurd h id
      | look a' α' =>
        have e' : i = a' := h
        rw [e']
        rcases hw2 with h' | h'
        · exact agentU _ h'
        · exact wireU _ h'
      | seek a' α' p c =>
        have h' : i = a' ∨ i = p.1 ∨ i = c.1 := h
        rcases h' with e' | e' | e' <;> rw [e']
        · exact wireU _ hw2.1
        · exact wireU _ hw2.2.1
        · exact wireU _ hw2.2.2
      | ready a' b' α' β' =>
        have h' : i = a' ∨ i = b' := h
        rcases h' with e' | e' <;> rw [e']
        · exact wireU _ hw2.1
        · exact wireU _ hw2.2
      | half a' b' α' β' =>
        have h' : i = a' ∨ i = b' := h
        rcases h' with e' | e' <;> rw [e']
        · exact wireU _ hw2.1
        · exact wireU _ hw2.2
      | write as ls =>
        have eth : threadOf M.ths u = TState.write as ls := threadOf_eq hu
        have h' : (∃ e ∈ as, e.1 = i) ∨ ∃ e ∈ ls, e.1.1 = i ∨ e.2.1 = i := h
        rcases h' with ⟨e, he, e'⟩ | ⟨e, he, e'⟩
        · obtain ⟨i', δ⟩ := e
          have e'' : i' = i := e'
          rw [← e'']
          refine .inl ⟨δ, .inr ⟨u, ?_⟩⟩
          show (threadOf M.ths u).pendA i' δ
          rw [eth]
          exact he
        · obtain ⟨p, q⟩ := e
          have hl : M.toMach.goal.link p q := by
            refine .inr ⟨u, ?_⟩
            show (threadOf M.ths u).pendL p q
            rw [eth]
            exact he
          rcases e' with e' | e'
          · have e'' : p.1 = i := e'
            rw [← e'']
            exact (linkU hl).1
          · have e'' : q.1 = i := e'
            rw [← e'']
            exact (linkU hl).2

omit [DecidableEq S] in
/-- **No name that a child of the two that fire could bear is held by the
program**, whatever the slot. -/
theorem XMach.child_fresh {M : XMach S} (hL : M.Live xs) (hW : M.Wired) {t : Nat}
    {todo : List (Id × S)} {a b : Id} {α β : S}
    (hT : M.ths[t]? = some ⟨todo, .half a b α β⟩) (hb : (b, β) ∈ M.mem.agents)
    (o : Option Bool) (jj : Nat) : ¬ M.Mentions (child a b o jj) := by
  intro hm
  have hu := XMach.mentions_used hL hW hm
  have hwf := hL.inv.wf
  have ha' : M.toMach.goal.agent a α := by
    refine .inl (.inr ⟨t, ?_⟩)
    show (threadOf M.ths t).held a α
    rw [threadOf_eq hT]
    exact ⟨rfl, rfl⟩
  have hb' : M.toMach.goal.agent b β := .inl (.inl hb)
  rcases par_eq a b o with e | e
  · have hu' : M.toMach.goal.Used ([slot o jj] ++ a) := by
      show M.toMach.goal.Used (slot o jj :: a)
      rw [← e]
      exact hu
    cases hwf.fresh [slot o jj] ha' hu'
  · have hu' : M.toMach.goal.Used ([slot o jj] ++ b) := by
      show M.toMach.goal.Used (slot o jj :: b)
      rw [← e]
      exact hu
    cases hwf.fresh [slot o jj] hb' hu'

end Closure

/-- The owner that a number stands for. -/
def odecode (n : Nat) : Option Bool :=
  if n % 3 = 0 then none else if n % 3 = 1 then some false else some true

theorem odecode_ocode (o : Option Bool) (j : Nat) :
    odecode (3 * j + ocode o) = o ∧ (3 * j + ocode o) / 3 = j := by
  cases o with
  | none =>
    refine ⟨?_, by show (3 * j + 0) / 3 = j; omega⟩
    show (if (3 * j + 0) % 3 = 0 then none
      else if (3 * j + 0) % 3 = 1 then some false else some true) = none
    rw [ite_pos' (by omega)]
  | some s =>
    cases s
    · refine ⟨?_, by show (3 * j + 1) / 3 = j; omega⟩
      show (if (3 * j + 1) % 3 = 0 then none
        else if (3 * j + 1) % 3 = 1 then some false else some true) = some false
      rw [ite_neg' (by omega), ite_pos' (by omega)]
    · refine ⟨?_, by show (3 * j + 2) / 3 = j; omega⟩
      show (if (3 * j + 2) % 3 = 0 then none
        else if (3 * j + 2) % 3 = 1 then some false else some true) = some true
      rw [ite_neg' (by omega), ite_neg' (by omega)]

/-- **A renaming carried over a claim**: the numbers from `cnt` on go to
the names that the children of `a'` and `b'` bear, and every other name
goes where it went. -/
def extName (g : Id → Id) (cnt : Nat) (a' b' : Id) : Id → Id
  | [k] => if cnt ≤ k then child a' b' (odecode (k - cnt)) ((k - cnt) / 3) else g [k]
  | i => g i

theorem extName_num (g : Id → Id) (cnt : Nat) (a' b' : Id) (o : Option Bool) (j : Nat) :
    extName g cnt a' b' (numName cnt o j) = child a' b' o j := by
  show (if cnt ≤ cnt + (3 * j + ocode o) then
      child a' b' (odecode (cnt + (3 * j + ocode o) - cnt)) ((cnt + (3 * j + ocode o) - cnt) / 3)
    else g [cnt + (3 * j + ocode o)]) = child a' b' o j
  rw [ite_pos' (Nat.le_add_right _ _), Nat.add_sub_cancel_left, (odecode_ocode o j).1,
    (odecode_ocode o j).2]

theorem extName_old {g : Id → Id} {cnt : Nat} {a' b' : Id} :
    ∀ {i : Id}, (∀ k, i = [k] → k < cnt) → extName g cnt a' b' i = g i
  | [], _ => rfl
  | [k], h => by
    show (if cnt ≤ k then child a' b' (odecode (k - cnt)) ((k - cnt) / 3) else g [k]) = g [k]
    rw [ite_neg' (Nat.not_le.2 (h k rfl))]
  | _ :: _ :: _, _ => rfl

section NumberedProgram

variable [DecidableEq S] {xs : XSys S}

theorem XMach.act_free (xs : XSys S) (X : XNet S) (T : XThread S) :
    (XMach.act xs X T).1.free = X.free := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => rfl
    | cons e rest =>
      unfold XMach.act
      dsimp only
      split <;> rfl
  | look a α =>
    unfold XMach.act
    dsimp only
    split <;> rfl
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    repeat' split
    all_goals rfl
  | ready a b α β =>
    unfold XMach.act
    dsimp only
    split <;> rfl
  | half a b α β =>
    unfold XMach.act
    dsimp only
    split <;> rfl
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
      | nil => rfl

/-- An action claims only from the state in which a thread holds one agent
and has found the other, and only when a rule applies. -/
theorem XMach.act_zero_or_claim (xs : XSys S) (X : XNet S) (T : XThread S) :
    (XMach.act xs X T).2.2 = 0 ∨ ∃ a b α β R, T.st = .half a b α β ∧
      (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact .inl rfl
    | cons e rest =>
      refine .inl ?_
      unfold XMach.act
      dsimp only
      split <;> rfl
  | look a α =>
    refine .inl ?_
    unfold XMach.act
    dsimp only
    split <;> rfl
  | seek a α p c =>
    refine .inl ?_
    unfold XMach.act
    dsimp only
    repeat' split
    all_goals rfl
  | ready a b α β =>
    refine .inl ?_
    unfold XMach.act
    dsimp only
    split <;> rfl
  | half a b α β =>
    cases h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | none => exact .inl (congrArg (fun r => r.2.2) (XMach.act_half_none h))
    | some R => exact .inr ⟨a, b, α, β, R, rfl, h⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact .inl rfl
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact .inl rfl
      | nil => exact .inl rfl

/-- **One action of the numbered program.**  The action of the program on
lists, but a claim names the new agents by numbers: one cell each, from
the counter `cnt` on, and the counter moves past them.  The last number
is the new counter. -/
def YMach.act (xs : XSys S) (X : XNet S) (cnt : Nat) (T : XThread S) :
    XNet S × XThread S × Nat × Nat :=
  match T.st with
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (X.takeAgent b,
        ⟨T.todo, .write (R.numAgents cnt) (R.numLinks xs.sys.ar a b cnt α β)⟩, 1, cnt + R.span)
    | none => (X.putAgent a α, T.fail, 0, cnt)
  | _ => ((XMach.act xs X T).1, (XMach.act xs X T).2.1, (XMach.act xs X T).2.2, cnt)

theorem YMach.act_zero {X : XNet S} {T : XThread S} (cnt : Nat)
    (h0 : (XMach.act xs X T).2.2 = 0) :
    YMach.act xs X cnt T = ((XMach.act xs X T).1, (XMach.act xs X T).2.1, 0, cnt) := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | half a b α β =>
    cases h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | none =>
      have e₁ : YMach.act xs X cnt ⟨todo, .half a b α β⟩ =
          (X.putAgent a α, ⟨todo, .idle⟩, 0, cnt) := by
        unfold YMach.act
        dsimp only
        rw [h] <;> rfl
      rw [e₁, XMach.act_half_none h]
    | some R =>
      rw [XMach.act_half h] at h0
      cases h0
  | idle =>
    show ((XMach.act xs X ⟨todo, .idle⟩).1, (XMach.act xs X ⟨todo, .idle⟩).2.1,
      (XMach.act xs X ⟨todo, .idle⟩).2.2, cnt) = _
    rw [h0]
  | look a α =>
    show ((XMach.act xs X ⟨todo, .look a α⟩).1, (XMach.act xs X ⟨todo, .look a α⟩).2.1,
      (XMach.act xs X ⟨todo, .look a α⟩).2.2, cnt) = _
    rw [h0]
  | seek a α p c =>
    show ((XMach.act xs X ⟨todo, .seek a α p c⟩).1, (XMach.act xs X ⟨todo, .seek a α p c⟩).2.1,
      (XMach.act xs X ⟨todo, .seek a α p c⟩).2.2, cnt) = _
    rw [h0]
  | ready a b α β =>
    show ((XMach.act xs X ⟨todo, .ready a b α β⟩).1,
      (XMach.act xs X ⟨todo, .ready a b α β⟩).2.1,
      (XMach.act xs X ⟨todo, .ready a b α β⟩).2.2, cnt) = _
    rw [h0]
  | write as ls =>
    show ((XMach.act xs X ⟨todo, .write as ls⟩).1, (XMach.act xs X ⟨todo, .write as ls⟩).2.1,
      (XMach.act xs X ⟨todo, .write as ls⟩).2.2, cnt) = _
    rw [h0]

theorem YMach.act_claim {X : XNet S} {todo : List (Id × S)} {a b : Id} {α β : S} {R : XRhs S}
    (cnt : Nat)
    (h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    YMach.act xs X cnt ⟨todo, .half a b α β⟩ =
      (X.takeAgent b,
        ⟨todo, .write (R.numAgents cnt) (R.numLinks xs.sys.ar a b cnt α β)⟩, 1, cnt + R.span) := by
  unfold YMach.act
  dsimp only
  rw [h]

/-- The state of the numbered program: the memory, the threads, and the
next number. -/
structure YMach (S : Type) where
  mem : XNet S
  ths : List (XThread S)
  cnt : Nat

/-- The state without the counter. -/
def YMach.toX (M : YMach S) : XMach S := ⟨M.mem, M.ths⟩

/-- One action of thread `t` of the numbered program. -/
def YMach.step (xs : XSys S) (M : YMach S) (t : Nat) : YMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(YMach.act xs M.mem M.cnt T).1, M.ths.set t (YMach.act xs M.mem M.cnt T).2.1,
        (YMach.act xs M.mem M.cnt T).2.2.2⟩, (YMach.act xs M.mem M.cnt T).2.2.1)
  | none => (M, 0)

/-- The run of the numbered program under an unending schedule. -/
def YMach.trace (xs : XSys S) (σ : Nat → Nat) (M : YMach S) : Nat → YMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((YMach.trace xs σ M i).1.step xs (σ i)).1,
      (YMach.trace xs σ M i).2 + ((YMach.trace xs σ M i).1.step xs (σ i)).2)

/-- The names of a memory. -/
def XNet.names (X : XNet S) : List Id :=
  X.agents.map (·.1) ++ X.wires.map (·.1.1) ++ X.wires.map (·.2.1) ++ X.free.map (·.1)

/-- A number above every cell of every name of the memory. -/
def XNet.top (X : XNet S) : Nat := (X.names.flatten.map (· + 1)).foldr max 0

omit [DecidableEq S] in
theorem XNet.lt_top {X : XNet S} {k : Nat} (h : [k] ∈ X.names) : k < X.top :=
  le_foldr_max _ _ (List.mem_map.2 ⟨k, List.mem_flatten.2 ⟨[k], h, List.mem_cons_self⟩, rfl⟩)

/-- **The numbered program before it starts**: the memory and the threads
of the program on lists, and a counter above every number in a name of the
net. -/
def YMach.init (X : XNet S) (n : Nat) : YMach S := ⟨X, (XMach.init X n).ths, X.top⟩

/-- A renaming of the whole state of the program. -/
def XMach.map (g : Id → Id) (M : XMach S) : XMach S :=
  ⟨M.mem.map g, M.ths.map (XThread.map g)⟩

/-- A name occurs in the state, or names a free port. -/
def XMach.Has (M : XMach S) (i : Id) : Prop := M.Mentions i ∨ ∃ p ∈ M.mem.free, p.1 = i

/-- Every name of the state satisfies `Q`. -/
def XMach.All (Q : Id → Prop) (M : XMach S) : Prop := M.mem.All Q ∧ ∀ T ∈ M.ths, T.All Q

omit [DecidableEq S] in
theorem XMach.all_mentions (M : XMach S) : M.All M.Mentions :=
  ⟨⟨fun e he => .inl ⟨e.2, he⟩,
      fun e he => ⟨.inr (.inl ⟨e, he, .inl rfl⟩), .inr (.inl ⟨e, he, .inr rfl⟩)⟩⟩,
    fun T hT => ⟨fun e he => .inr (.inr ⟨T, hT, .inl ⟨e, he, rfl⟩⟩),
      fun _ hi => .inr (.inr ⟨T, hT, .inr hi⟩)⟩⟩

omit [DecidableEq S] in
theorem XMach.All.of_mentions {Q : Id → Prop} {M : XMach S} (h : M.All Q) {i : Id}
    (hi : M.Mentions i) : Q i := by
  rcases hi with ⟨γ, hγ⟩ | ⟨e, he, h'⟩ | ⟨T, hT, h'⟩
  · exact h.1.1 (i, γ) hγ
  · rcases h' with e' | e' <;> rw [← e']
    · exact (h.1.2 e he).1
    · exact (h.1.2 e he).2
  · rcases h' with ⟨e, he, e'⟩ | h'
    · rw [← e']
      exact (h.2 T hT).1 e he
    · exact (h.2 T hT).2 i h'

omit [DecidableEq S] in
theorem XNet.All.mono {Q Q' : Id → Prop} (hq : ∀ i, Q i → Q' i) {X : XNet S} (h : X.All Q) :
    X.All Q' :=
  ⟨fun e he => hq _ (h.1 e he), fun e he => ⟨hq _ (h.2 e he).1, hq _ (h.2 e he).2⟩⟩

omit [DecidableEq S] in
theorem XThread.All.mono {Q Q' : Id → Prop} (hq : ∀ i, Q i → Q' i) {T : XThread S}
    (h : T.All Q) : T.All Q' :=
  ⟨fun e he => hq _ (h.1 e he), fun i hi => hq _ (h.2 i hi)⟩

omit [DecidableEq S] in
theorem TState.mentions_map (g : Id → Id) {s : TState S} {i : Id} (h : s.Mentions i) :
    (s.map g).Mentions (g i) := by
  cases s with
  | idle => exact h
  | look a α =>
    have e : i = a := h
    exact congrArg g e
  | seek a α p c =>
    have h' : i = a ∨ i = p.1 ∨ i = c.1 := h
    rcases h' with e | e | e
    · exact .inl (congrArg g e)
    · exact .inr (.inl (congrArg g e))
    · exact .inr (.inr (congrArg g e))
  | ready a b α β =>
    have h' : i = a ∨ i = b := h
    rcases h' with e | e
    · exact .inl (congrArg g e)
    · exact .inr (congrArg g e)
  | half a b α β =>
    have h' : i = a ∨ i = b := h
    rcases h' with e | e
    · exact .inl (congrArg g e)
    · exact .inr (congrArg g e)
  | write as ls =>
    have h' : (∃ e ∈ as, e.1 = i) ∨ ∃ e ∈ ls, e.1.1 = i ∨ e.2.1 = i := h
    rcases h' with ⟨e, he, e'⟩ | ⟨e, he, e'⟩
    · exact .inl ⟨(g e.1, e.2), List.mem_map.2 ⟨e, he, rfl⟩, congrArg g e'⟩
    · refine .inr ⟨((g e.1.1, e.1.2), (g e.2.1, e.2.2)), List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩
      rcases e' with e' | e'
      · exact .inl (congrArg g e')
      · exact .inr (congrArg g e')

omit [DecidableEq S] in
/-- A name of the state is renamed to a name of the renamed state. -/
theorem XMach.mentions_map (g : Id → Id) {M : XMach S} {i : Id} (h : M.Mentions i) :
    (M.map g).Mentions (g i) := by
  rcases h with ⟨γ, hγ⟩ | ⟨e, he, h'⟩ | ⟨T, hT, h'⟩
  · exact .inl ⟨γ, List.mem_map.2 ⟨(i, γ), hγ, rfl⟩⟩
  · refine .inr (.inl ⟨(mapPort g e.1, mapPort g e.2), List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩)
    rcases h' with e' | e'
    · exact .inl (congrArg g e')
    · exact .inr (congrArg g e')
  · refine .inr (.inr ⟨T.map g, List.mem_map.2 ⟨T, hT, rfl⟩, ?_⟩)
    rcases h' with ⟨e, he, e'⟩ | h'
    · exact .inl ⟨(g e.1, e.2), List.mem_map.2 ⟨e, he, rfl⟩, congrArg g e'⟩
    · exact .inr (TState.mentions_map g h')

/-- **The numbered state stands for the named one.**  The named state is
the numbered one renamed by `g`; `g` keeps the names of the numbered state
apart; and every one-cell name of the numbered state is below the
counter. -/
structure YMach.Rel (g : Id → Id) (Y : YMach S) (X : XMach S) : Prop where
  eq : X = Y.toX.map g
  inj : ∀ i j, Y.toX.Mentions i → Y.toX.Mentions j → g i = g j → i = j
  low : ∀ k, Y.toX.Has [k] → k < Y.cnt

end NumberedProgram

section NumberedSim

variable [DecidableEq S] {xs : XSys S}

/-- **One action of the numbered program is one action of the named
one.**  If the numbered state stands for the named one, then after the
same thread acts in both, the numbered state still stands for the named
one, by a renaming that is carried over the claim if there was one; and
both claimed, or neither did. -/
theorem YMach.step_rel (xs : XSys S) {Y : YMach S} {X : XMach S} {g : Id → Id}
    (h : Y.Rel g X) (hL : X.Live xs) (hW : X.Wired) (t : Nat) :
    ∃ g', (Y.step xs t).1.Rel g' (X.step xs t).1 ∧ (Y.step xs t).2 = (X.step xs t).2 := by
  obtain ⟨rfl, hinj, hlow⟩ := h
  cases hT : Y.ths[t]? with
  | none =>
    have e₁ : Y.step xs t = (Y, 0) := by
      unfold YMach.step
      rw [hT]
    have hXT : (Y.toX.map g).ths[t]? = none := by
      show (Y.ths.map (XThread.map g))[t]? = none
      rw [List.getElem?_map, hT]
      rfl
    have e₂ : (Y.toX.map g).step xs t = (Y.toX.map g, 0) := by
      unfold XMach.step
      rw [hXT]
    rw [e₁, e₂]
    exact ⟨g, ⟨rfl, hinj, hlow⟩, rfl⟩
  | some T =>
    have hTm : T ∈ Y.ths := List.mem_of_getElem? hT
    have hXT : (Y.toX.map g).ths[t]? = some (T.map g) := by
      show (Y.ths.map (XThread.map g))[t]? = some (T.map g)
      rw [List.getElem?_map, hT]
      rfl
    have hall := XMach.all_mentions Y.toX
    have am : (XMach.act xs (Y.mem.map g) (T.map g)).1 = (XMach.act xs Y.mem T).1.map g ∧
        (XMach.act xs (Y.mem.map g) (T.map g)).2.2 = (XMach.act xs Y.mem T).2.2 ∧
        ((XMach.act xs Y.mem T).2.2 = 0 →
          (XMach.act xs (Y.mem.map g) (T.map g)).2.1 = (XMach.act xs Y.mem T).2.1.map g) :=
      XMach.act_map xs hinj hall.1.1 hall.1.2 (hall.2 T hTm).1 (hall.2 T hTm).2
    obtain ⟨am1, am2, am3⟩ := am
    have eY0 : Y.step xs t =
        (⟨(YMach.act xs Y.mem Y.cnt T).1, Y.ths.set t (YMach.act xs Y.mem Y.cnt T).2.1,
          (YMach.act xs Y.mem Y.cnt T).2.2.2⟩, (YMach.act xs Y.mem Y.cnt T).2.2.1) := by
      unfold YMach.step
      rw [hT] <;> rfl
    have eX : (Y.toX.map g).step xs t =
        (⟨(XMach.act xs (Y.mem.map g) (T.map g)).1,
          (Y.ths.map (XThread.map g)).set t (XMach.act xs (Y.mem.map g) (T.map g)).2.1⟩,
          (XMach.act xs (Y.mem.map g) (T.map g)).2.2) := by
      unfold XMach.step
      rw [hXT] <;> rfl
    rcases XMach.act_zero_or_claim xs Y.mem T with h0 | ⟨a, b, α, β, R, hst, hR⟩
    · have eY : Y.step xs t =
          (⟨(XMach.act xs Y.mem T).1, Y.ths.set t (XMach.act xs Y.mem T).2.1, Y.cnt⟩, 0) := by
        rw [eY0, YMach.act_zero Y.cnt h0]
      have hnew : (⟨(XMach.act xs Y.mem T).1,
          Y.ths.set t (XMach.act xs Y.mem T).2.1⟩ : XMach S).All Y.toX.Mentions := by
        obtain ⟨b1, b2⟩ := XMach.act_all xs hall.1 (hall.2 T hTm)
        refine ⟨b1, fun T' hT' => ?_⟩
        have hT'' : T' ∈ Y.ths.set t (XMach.act xs Y.mem T).2.1 := hT'
        rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
        · exact hall.2 T' hm
        · exact b2 h0
      refine ⟨g, ?_, ?_⟩
      · rw [eX, eY]
        refine ⟨?_, fun i j hi hj => hinj i j (hnew.of_mentions hi) (hnew.of_mentions hj),
          fun k hk => ?_⟩
        · show (⟨(XMach.act xs (Y.mem.map g) (T.map g)).1,
              (Y.ths.map (XThread.map g)).set t
                (XMach.act xs (Y.mem.map g) (T.map g)).2.1⟩ : XMach S) =
            ⟨(XMach.act xs Y.mem T).1.map g,
              (Y.ths.set t (XMach.act xs Y.mem T).2.1).map (XThread.map g)⟩
          rw [am1, am3 h0, List.map_set]
        · rcases hk with hk | ⟨p, hp, ep⟩
          · exact hlow k (.inl (hnew.of_mentions hk))
          · have hp' : p ∈ (XMach.act xs Y.mem T).1.free := hp
            rw [XMach.act_free xs Y.mem T] at hp'
            exact hlow k (.inr ⟨p, hp', ep⟩)
      · rw [eX, eY]
        show 0 = (XMach.act xs (Y.mem.map g) (T.map g)).2.2
        rw [am2, h0]
    · obtain ⟨todo, st⟩ := T
      have hst' : st = .half a b α β := hst
      subst hst'
      have hP := (hall.2 _ hTm).2
      have hPa : Y.toX.Mentions a := hP a (.inl rfl)
      have hPb : Y.toX.Mentions b := hP b (.inr rfl)
      have hc : assoc b Y.mem.agents = some β ∧ a ≠ b := by
        by_cases c : assoc b Y.mem.agents = some β ∧ a ≠ b
        · exact c
        · rw [ite_neg' c] at hR
          cases hR
      have hr : xs.rule α β = some R := by
        rw [ite_pos' hc] at hR
        exact hR
      have hne' : g a ≠ g b := fun e => hc.2 (hinj a b hPa hPb e)
      have hbX : assoc (g b) (Y.mem.map g).agents = some β := by
        show assoc (g b) (Y.mem.agents.map fun e => (g e.1, e.2)) = some β
        rw [assoc_map_inj hinj hPb Y.mem.agents hall.1.1]
        exact hc.1
      have hRX : (if assoc (g b) (Y.mem.map g).agents = some β ∧ g a ≠ g b then xs.rule α β
          else none) = some R := by
        rw [ite_pos' ⟨hbX, hne'⟩]
        exact hr
      have eAX : XMach.act xs (Y.mem.map g) (XThread.map g ⟨todo, .half a b α β⟩) =
          ((Y.mem.map g).takeAgent (g b),
            ⟨todo.map fun e => (g e.1, e.2),
              .write (R.newAgents (g a) (g b)) (R.newLinks xs.sys.ar (g a) (g b) α β)⟩, 1) :=
        XMach.act_half hRX
      have hold : ∀ i, Y.toX.Has i → extName g Y.cnt (g a) (g b) i = g i :=
        fun i hi => extName_old (fun k e => hlow k (by rw [← e]; exact hi))
      have eY : Y.step xs t =
          (⟨Y.mem.takeAgent b,
            Y.ths.set t ⟨todo, .write (R.numAgents Y.cnt) (R.numLinks xs.sys.ar a b Y.cnt α β)⟩,
            Y.cnt + R.span⟩, 1) := by
        rw [eY0, YMach.act_claim Y.cnt hR]
      have hnewT : (⟨todo, .write (R.numAgents Y.cnt)
          (R.numLinks xs.sys.ar a b Y.cnt α β)⟩ : XThread S).All
          (fun i => Y.toX.Mentions i ∨ ∃ o j, (o, j) ∈ R.slots ∧ i = numName Y.cnt o j) := by
        refine ⟨fun e he => .inl ((hall.2 _ hTm).1 e he), fun i hi => ?_⟩
        have hi' : (∃ e ∈ R.numAgents Y.cnt, e.1 = i) ∨
            ∃ e ∈ R.numLinks xs.sys.ar a b Y.cnt α β, e.1.1 = i ∨ e.2.1 = i := hi
        rcases hi' with ⟨e, he, e'⟩ | ⟨e, he, e'⟩
        · obtain ⟨o, j, hs, en⟩ := R.numAgents_name Y.cnt he
          exact .inr ⟨o, j, hs, by rw [← e', en]⟩
        · obtain ⟨n1, n2⟩ := xs.numLinks_name hr a b Y.cnt he
          rcases e' with e' | e'
          · rw [← e']
            rcases n1 with n | n | ⟨o, j, hs, en⟩
            · rw [n]
              exact .inl hPa
            · rw [n]
              exact .inl hPb
            · exact .inr ⟨o, j, hs, en⟩
          · rw [← e']
            rcases n2 with n | n | ⟨o, j, hs, en⟩
            · rw [n]
              exact .inl hPa
            · rw [n]
              exact .inl hPb
            · exact .inr ⟨o, j, hs, en⟩
      have hnew : (⟨Y.mem.takeAgent b,
          Y.ths.set t ⟨todo, .write (R.numAgents Y.cnt)
            (R.numLinks xs.sys.ar a b Y.cnt α β)⟩⟩ : XMach S).All
          (fun i => Y.toX.Mentions i ∨ ∃ o j, (o, j) ∈ R.slots ∧ i = numName Y.cnt o j) := by
        refine ⟨(hall.1.take b).mono (fun _ h => .inl h), fun T' hT' => ?_⟩
        have hT'' : T' ∈ Y.ths.set t ⟨todo, .write (R.numAgents Y.cnt)
            (R.numLinks xs.sys.ar a b Y.cnt α β)⟩ := hT'
        rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
        · exact (hall.2 T' hm).mono (fun _ h => .inl h)
        · exact hnewT
      have hfresh : ∀ o j, ¬ (Y.toX.map g).Mentions (child (g a) (g b) o j) :=
        fun o j => XMach.child_fresh hL hW (todo := todo.map fun e => (g e.1, e.2))
          (a := g a) (b := g b) (α := α) (β := β) hXT (assoc_mem hbX) o j
      refine ⟨extName g Y.cnt (g a) (g b), ?_, ?_⟩
      · rw [eX, eY]
        refine ⟨?_, ?_, ?_⟩
        · rw [eAX]
          show (⟨(Y.mem.map g).takeAgent (g b), (Y.ths.map (XThread.map g)).set t
              ⟨todo.map fun e => (g e.1, e.2),
                .write (R.newAgents (g a) (g b))
                  (R.newLinks xs.sys.ar (g a) (g b) α β)⟩⟩ : XMach S) =
            ⟨(Y.mem.takeAgent b).map (extName g Y.cnt (g a) (g b)),
              (Y.ths.set t ⟨todo, .write (R.numAgents Y.cnt)
                (R.numLinks xs.sys.ar a b Y.cnt α β)⟩).map
                (XThread.map (extName g Y.cnt (g a) (g b)))⟩
          have m1a : (Y.mem.takeAgent b).map (extName g Y.cnt (g a) (g b)) =
              (Y.mem.takeAgent b).map g :=
            XNet.map_congr (X := Y.mem.takeAgent b)
              (fun e he => by
                have he' : e ∈ Y.mem.agents.filter (fun e => decide (e.1 ≠ b)) := he
                exact hold _ (.inl (.inl ⟨e.2, (List.mem_filter.1 he').1⟩)))
              (fun e he => ⟨hold _ (.inl (.inr (.inl ⟨e, he, .inl rfl⟩))),
                hold _ (.inl (.inr (.inl ⟨e, he, .inr rfl⟩)))⟩)
              (fun p hp => hold _ (.inr ⟨p, hp, rfl⟩))
          have m1b : (Y.mem.map g).takeAgent (g b) = (Y.mem.takeAgent b).map g :=
            XNet.takeAgent_map hinj hall.1.1 hPb
          have m1 : (Y.mem.takeAgent b).map (extName g Y.cnt (g a) (g b)) =
              (Y.mem.map g).takeAgent (g b) := m1a.trans m1b.symm
          have m2 : Y.ths.map (XThread.map (extName g Y.cnt (g a) (g b))) =
              Y.ths.map (XThread.map g) :=
            List.map_congr_left (fun T' hT' => XThread.map_congr
              (fun e he => hold _ (.inl (.inr (.inr ⟨T', hT', .inl ⟨e, he, rfl⟩⟩))))
              (fun i hi => hold _ (.inl (.inr (.inr ⟨T', hT', .inr hi⟩)))))
          have m3 : XThread.map (extName g Y.cnt (g a) (g b))
              ⟨todo, .write (R.numAgents Y.cnt) (R.numLinks xs.sys.ar a b Y.cnt α β)⟩ =
              ⟨todo.map fun e => (g e.1, e.2),
                .write (R.newAgents (g a) (g b)) (R.newLinks xs.sys.ar (g a) (g b) α β)⟩ := by
            have t1 : (todo.map fun e => (extName g Y.cnt (g a) (g b) e.1, e.2)) =
                todo.map fun e => (g e.1, e.2) :=
              List.map_congr_left (fun e he => by
                rw [hold _ (.inl ((hall.2 _ hTm).1 e he))])
            show (⟨todo.map fun e => (extName g Y.cnt (g a) (g b) e.1, e.2),
              .write ((R.numAgents Y.cnt).map fun e => (extName g Y.cnt (g a) (g b) e.1, e.2))
                ((R.numLinks xs.sys.ar a b Y.cnt α β).map fun e =>
                  ((extName g Y.cnt (g a) (g b) e.1.1, e.1.2),
                    (extName g Y.cnt (g a) (g b) e.2.1, e.2.2)))⟩ : XThread S) = _
            rw [t1, ← R.newAgents_num hne' Y.cnt (extName_num g Y.cnt (g a) (g b)),
              ← R.newLinks_num xs.sys.ar Y.cnt α β (hold a (.inl hPa)) (hold b (.inl hPb))
                (extName_num g Y.cnt (g a) (g b))]
          rw [List.map_set, m1, m2, m3]
        · intro i j hi hj e
          have hi' := hnew.of_mentions hi
          have hj' := hnew.of_mentions hj
          rcases hi' with hi' | ⟨o, jj, -, rfl⟩ <;> rcases hj' with hj' | ⟨o', jj', -, rfl⟩
          · rw [hold i (.inl hi'), hold j (.inl hj')] at e
            exact hinj i j hi' hj' e
          · rw [hold i (.inl hi'), extName_num] at e
            have hm := XMach.mentions_map g hi'
            rw [e] at hm
            exact absurd hm (hfresh o' jj')
          · rw [extName_num, hold j (.inl hj')] at e
            have hm := XMach.mentions_map g hj'
            rw [← e] at hm
            exact absurd hm (hfresh o jj)
          · rw [extName_num, extName_num] at e
            obtain ⟨eo, ej⟩ := child_inj' hne' e
            rw [eo, ej]
        · intro k hk
          show k < Y.cnt + R.span
          rcases hk with hk | ⟨p, hp, ep⟩
          · rcases hnew.of_mentions hk with hk' | ⟨o, j, hs, en⟩
            · exact Nat.lt_of_lt_of_le (hlow k (.inl hk')) (Nat.le_add_right _ _)
            · have e' : k = Y.cnt + (3 * j + ocode o) := by
                injection en
              have := R.lt_span hs
              omega
          · exact Nat.lt_of_lt_of_le (hlow k (.inr ⟨p, hp, ep⟩)) (Nat.le_add_right _ _)
      · rw [eX, eY]
        show 1 = (XMach.act xs (Y.mem.map g) (XThread.map g ⟨todo, .half a b α β⟩)).2.2
        rw [eAX]

omit [DecidableEq S] in
theorem XNet.map_id' (X : XNet S) : X.map (fun i => i) = X := by
  show (⟨X.agents.map fun e => (e.1, e.2), X.free.map (mapPort fun i => i),
    X.wires.map fun e => (mapPort (fun i => i) e.1, mapPort (fun i => i) e.2)⟩ : XNet S) = X
  have e₁ : (X.agents.map fun e => (e.1, e.2)) = X.agents := List.map_id X.agents
  have e₂ : X.free.map (mapPort fun i => i) = X.free := List.map_id X.free
  have e₃ : (X.wires.map fun e => (mapPort (fun i => i) e.1, mapPort (fun i => i) e.2)) =
      X.wires := List.map_id X.wires
  rw [e₁, e₂, e₃]

omit [DecidableEq S] in
theorem XThread.map_id' (T : XThread S) : T.map (fun i => i) = T := by
  obtain ⟨todo, st⟩ := T
  have e₁ : (todo.map fun e => (e.1, e.2)) = todo := List.map_id todo
  have e₂ : st.map (fun i => i) = st := by
    cases st with
    | idle => rfl
    | look a α => rfl
    | seek a α p c => rfl
    | ready a b α β => rfl
    | half a b α β => rfl
    | write as ls =>
      have a₁ : (as.map fun e => (e.1, e.2)) = as := List.map_id as
      have a₂ : (ls.map fun e => ((e.1.1, e.1.2), (e.2.1, e.2.2))) = ls := List.map_id ls
      show TState.write (as.map fun e => (e.1, e.2))
        (ls.map fun e => ((e.1.1, e.1.2), (e.2.1, e.2.2))) = .write as ls
      rw [a₁, a₂]
  show (⟨todo.map fun e => (e.1, e.2), st.map fun i => i⟩ : XThread S) = ⟨todo, st⟩
  rw [e₁, e₂]

omit [DecidableEq S] in
/-- Before they start, the numbered program stands for the named one, by
the renaming that changes nothing. -/
theorem YMach.init_rel (X : XNet S) (n : Nat) :
    (YMach.init X n).Rel (fun i => i) (XMach.init X n) := by
  refine ⟨?_, fun i j _ _ e => e, fun k hk => ?_⟩
  · have e₁ : (XMach.init X n).ths.map (XThread.map fun i => i) = (XMach.init X n).ths := by
      have : ∀ l : List (XThread S), l.map (XThread.map fun i => i) = l := by
        intro l
        induction l with
        | nil => rfl
        | cons T l ih => rw [List.map_cons, XThread.map_id', ih]
      exact this _
    show XMach.init X n = ⟨X.map (fun i => i), (XMach.init X n).ths.map (XThread.map fun i => i)⟩
    rw [XNet.map_id', e₁]
    rfl
  · show k < X.top
    apply XNet.lt_top
    rcases hk with (⟨γ, hγ⟩ | ⟨e, he, h'⟩ | ⟨T, hT, h'⟩) | ⟨p, hp, ep⟩
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨([k], γ), hγ, rfl⟩)))
    · rcases h' with e' | e'
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.2 ⟨e, he, e'⟩)))
      · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨e, he, e'⟩))
    · have hT' : T ∈ (List.range n).map fun t =>
          (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S) := hT
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hT'
      rcases h' with ⟨e, he, e'⟩ | h'
      · have he' : e ∈ X.agents.drop u ++ X.agents.take u := he
        have hm : e ∈ X.agents := by
          rcases List.mem_append.1 he' with h | h
          · exact List.mem_of_mem_drop h
          · exact List.mem_of_mem_take h
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨e, hm, e'⟩)))
      · exact absurd h' id
    · exact List.mem_append_right _ (List.mem_map.2 ⟨p, hp, ep⟩)

/-- **The numbered program follows the named one**, action by action,
under any schedule: at every moment the named state is the numbered state
renamed, by a renaming that keeps its names apart, and both have claimed
as often. -/
theorem YMach.trace_rel {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) :
    ∀ i, ∃ g, ((YMach.init X nt).trace xs σ i).1.Rel g ((XMach.init X nt).trace xs σ i).1 ∧
      ((YMach.init X nt).trace xs σ i).2 = ((XMach.init X nt).trace xs σ i).2
  | 0 => ⟨fun i => i, YMach.init_rel X nt, rfl⟩
  | i + 1 => by
    obtain ⟨g, hr, hc⟩ := YMach.trace_rel hX hnt σ i
    obtain ⟨g', hr', hc'⟩ := YMach.step_rel xs hr
      (XMach.trace_live σ (XMach.init_live hX hnt) i)
      (XMach.trace_wired σ (XMach.init_wired X nt) i) (σ i)
    refine ⟨g', hr', ?_⟩
    show ((YMach.init X nt).trace xs σ i).2 +
        (((YMach.init X nt).trace xs σ i).1.step xs (σ i)).2 =
      ((XMach.init X nt).trace xs σ i).2 + (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2
    rw [hc, hc']

omit [DecidableEq S] in
theorem XMach.resting_map (g : Id → Id) (M : XMach S) : (M.map g).resting = M.resting := by
  have h : ∀ l : List (XThread S),
      (l.map (XThread.map g)).all (fun T => T.todo.isEmpty && T.st.isIdle) =
        l.all (fun T => T.todo.isEmpty && T.st.isIdle) := by
    intro l
    induction l with
    | nil => rfl
    | cons T l ih =>
      have e : ((XThread.map g T).todo.isEmpty && (XThread.map g T).st.isIdle) =
          (T.todo.isEmpty && T.st.isIdle) := by
        obtain ⟨todo, st⟩ := T
        cases todo <;> cases st <;> rfl
      rw [List.map_cons, List.all_cons, List.all_cons, e, ih]
  exact h M.ths

/-- **Under a fair schedule the numbered program comes to rest with the
normal form, up to the names.**  From some moment on every thread rests,
the claims are as many as the steps to the normal form, and the memory,
renamed by a map that keeps its names apart, is the normal form. -/
theorem YMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ∃ g,
      (∀ a b, ((YMach.init X nt).trace xs σ i).1.toX.Mentions a →
        ((YMach.init X nt).trace xs σ i).1.toX.Mentions b → g a = g b → a = b) ∧
      ((YMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((YMach.init X nt).trace xs σ i).2 = n ∧
      (((YMach.init X nt).trace xs σ i).1.mem.map g).toNet = N' := by
  obtain ⟨i₀, h⟩ := XMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨g, hr, hc⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
  obtain ⟨r, c, m⟩ := h i hi
  refine ⟨g, hr.inj, ?_, ?_, ?_⟩
  · rw [hr.eq, XMach.resting_map] at r
    exact r
  · rw [hc]
    exact c
  · have e : ((XMach.init X nt).trace xs σ i).1.mem =
        ((YMach.init X nt).trace xs σ i).1.mem.map g := congrArg XMach.mem hr.eq
    rw [← e]
    exact m

end NumberedSim

section NumberedShort

variable [DecidableEq S] {xs : XSys S}

/-- **An action of the numbered program does not lengthen the names**:
what it adds are numbers, of one cell. -/
theorem YMach.step_names (xs : XSys S) {Y : YMach S} {L : Nat} (hL : 1 ≤ L)
    (h : Y.toX.NamesLe L) (t : Nat) : (Y.step xs t).1.toX.NamesLe L := by
  cases hT : Y.ths[t]? with
  | none =>
    have e₁ : Y.step xs t = (Y, 0) := by
      unfold YMach.step
      rw [hT]
    rw [e₁]
    exact h
  | some T =>
    have hTm : T ∈ Y.ths := List.mem_of_getElem? hT
    have eY0 : Y.step xs t =
        (⟨(YMach.act xs Y.mem Y.cnt T).1, Y.ths.set t (YMach.act xs Y.mem Y.cnt T).2.1,
          (YMach.act xs Y.mem Y.cnt T).2.2.2⟩, (YMach.act xs Y.mem Y.cnt T).2.2.1) := by
      unfold YMach.step
      rw [hT] <;> rfl
    rcases XMach.act_zero_or_claim xs Y.mem T with h0 | ⟨a, b, α, β, R, hst, hR⟩
    · have hn : (XMach.act xs Y.mem T).1.NamesLe (L + (XMach.act xs Y.mem T).2.2) ∧
          (XMach.act xs Y.mem T).2.1.NamesLe (L + (XMach.act xs Y.mem T).2.2) :=
        XMach.act_names xs h.1 (h.2 T hTm)
      rw [h0] at hn
      rw [eY0, YMach.act_zero Y.cnt h0]
      refine ⟨hn.1, fun T' hT' => ?_⟩
      have hT'' : T' ∈ Y.ths.set t (XMach.act xs Y.mem T).2.1 := hT'
      rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
      · exact h.2 T' hm
      · exact hn.2
    · obtain ⟨todo, st⟩ := T
      have hst' : st = .half a b α β := hst
      subst hst'
      have hc : assoc b Y.mem.agents = some β ∧ a ≠ b := by
        by_cases c : assoc b Y.mem.agents = some β ∧ a ≠ b
        · exact c
        · rw [ite_neg' c] at hR
          cases hR
      have hr : xs.rule α β = some R := by
        rw [ite_pos' hc] at hR
        exact hR
      have hT0 : (∀ e ∈ todo, e.1.length ≤ L) ∧ a.length ≤ L ∧ b.length ≤ L := h.2 _ hTm
      rw [eY0, YMach.act_claim Y.cnt hR]
      refine ⟨h.1.take b, fun T' hT' => ?_⟩
      have hT'' : T' ∈ Y.ths.set t ⟨todo, .write (R.numAgents Y.cnt)
          (R.numLinks xs.sys.ar a b Y.cnt α β)⟩ := hT'
      rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
      · exact h.2 T' hm
      · refine ⟨hT0.1, fun e he => ?_, fun e he => ?_⟩
        · obtain ⟨o, j, -, en⟩ := R.numAgents_name Y.cnt he
          rw [en]
          exact hL
        · obtain ⟨n1, n2⟩ := xs.numLinks_name hr a b Y.cnt he
          refine ⟨?_, ?_⟩
          · rcases n1 with n | n | ⟨o, j, -, en⟩
            · rw [n]
              exact hT0.2.1
            · rw [n]
              exact hT0.2.2
            · rw [en]
              exact hL
          · rcases n2 with n | n | ⟨o, j, -, en⟩
            · rw [n]
              exact hT0.2.1
            · rw [n]
              exact hT0.2.2
            · rw [en]
              exact hL

theorem YMach.trace_names (σ : Nat → Nat) {Y : YMach S} {L : Nat} (hL : 1 ≤ L)
    (h : Y.toX.NamesLe L) : ∀ i, (Y.trace xs σ i).1.toX.NamesLe L
  | 0 => h
  | i + 1 => YMach.step_names xs hL (YMach.trace_names σ hL h i) (σ i)

/-- **Numbered names stay short.**  Under any schedule, and however long
the run, no name of the numbered program has more cells than the longest
name of the net it started from, or than one.  (The named program's names
grow by a cell with each claim: `XMach.names_le`.) -/
theorem YMach.names_le {X : XNet S} {L : Nat} (hX : X.NamesLe L) (nt : Nat) (σ : Nat → Nat)
    (i : Nat) : ((YMach.init X nt).trace xs σ i).1.toX.NamesLe (max L 1) :=
  YMach.trace_names (Y := YMach.init X nt) (L := max L 1) σ (Nat.le_max_right _ _)
    (XMach.init_names (L := max L 1) (hX.mono (Nat.le_max_left _ _)) nt) i

end NumberedShort

/-! ### Numbered names on ordered maps

The numbered program on ordered maps alone, with every operation counted.
It runs as the numbered program on lists does, so its state, renamed, is
the state of the named program at every moment.  Its keys are numbers of
one cell or names of the net, so an operation on a map no longer costs
more as the run goes on: the bound on the time has `max L 1` where the
named program had `L + n`. -/

theorem nodup_of_map' {A B : Type} (f : A → B) : ∀ l : List A, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    have h' : (f x :: l.map f).Nodup := h
    obtain ⟨h1, h2⟩ := List.nodup_cons.1 h'
    exact List.nodup_cons.2
      ⟨fun hm => h1 (List.mem_map.2 ⟨x, hm, rfl⟩), nodup_of_map' f l h2⟩

section NumberedOrdered

variable [DecidableEq S] {xs : XSys S}

/-- **One action of the numbered program on ordered maps alone.**  The
action of `OMach.act`, but a claim names the new agents by numbers, from
the counter on, and the counter moves past them. -/
def ZMach.act (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S) :
    OMem S × TThread S × Nat × Nat :=
  match T.st with
  | .half a b α β =>
    match (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (O.take b,
        ⟨T.todo, .write (R.numAgents cnt) (R.numLinks xs.sys.ar a b cnt α β)⟩, 1, cnt + R.span)
    | none => (O.put a α, T.fail, 0, cnt)
  | _ => ((OMach.act xs O T).1, (OMach.act xs O T).2.1, (OMach.act xs O T).2.2, cnt)

theorem ZMach.act_half {O : OMem S} {todo : Std.TreeMap Nat (Id × S)} {a b : Id} {α β : S}
    {R : XRhs S} (cnt : Nat)
    (h : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    ZMach.act xs O cnt ⟨todo, .half a b α β⟩ =
      (O.take b,
        ⟨todo, .write (R.numAgents cnt) (R.numLinks xs.sys.ar a b cnt α β)⟩, 1, cnt + R.span) := by
  unfold ZMach.act
  dsimp only
  rw [h]

theorem ZMach.act_half_none {O : OMem S} {todo : Std.TreeMap Nat (Id × S)} {a b : Id}
    {α β : S} (cnt : Nat)
    (h : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) = none) :
    ZMach.act xs O cnt ⟨todo, .half a b α β⟩ = (O.put a α, ⟨todo, .idle⟩, 0, cnt) := by
  unfold ZMach.act
  dsimp only
  rw [h] <;> rfl

theorem OMach.act_half {O : OMem S} {todo : Std.TreeMap Nat (Id × S)} {a b : Id} {α β : S}
    {R : XRhs S} (h : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    OMach.act xs O ⟨todo, .half a b α β⟩ =
      (O.take b, ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) := by
  unfold OMach.act
  dsimp only
  rw [h]

theorem OMach.act_half_none {O : OMem S} {todo : Std.TreeMap Nat (Id × S)} {a b : Id}
    {α β : S} (h : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) = none) :
    OMach.act xs O ⟨todo, .half a b α β⟩ = (O.put a α, ⟨todo, .idle⟩, 0) := by
  unfold OMach.act
  dsimp only
  rw [h] <;> rfl

/-- **The numbered action leaves the memory that the named action
leaves.**  They differ only in the names that the thread will write. -/
theorem ZMach.act_mem (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S) :
    (ZMach.act xs O cnt T).1 = (OMach.act xs O T).1 := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | half a b α β =>
    cases h : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | none => rw [ZMach.act_half_none cnt h, OMach.act_half_none h]
    | some R => rw [ZMach.act_half cnt h, OMach.act_half h]
  | idle => rfl
  | look a α => rfl
  | seek a α p c => rfl
  | ready a b α β => rfl
  | write as ls => rfl

omit [DecidableEq S] in
theorem OMem.Agree.toX {O : OMem S} {H : TMem S} (h : O.Agree H) : O.toX = H.toX := by
  show (⟨treeList O.cells, O.free, O.wires⟩ : XNet S) = ⟨treeList H.cells, H.free, H.wires⟩
  rw [h.cells, h.free, h.wires]

/-- **The numbered action on ordered maps alone is the numbered action on
lists.**  On a memory that answers as an ordered memory in order, it
leaves such a memory again, standing for the memory of lists that the
action on lists leaves; the thread, the claim and the counter agree. -/
theorem ZMach.act_sim (xs : XSys S) {O : OMem S} {H : TMem S} (h : O.Agree H) (hk : H.Ok)
    (cnt : Nat) (T : TThread S)
    (hnd : ((YMach.act xs H.toX cnt T.toX).1.agents.map Prod.fst).Nodup) :
    (∃ H', (ZMach.act xs O cnt T).1.Agree H' ∧ H'.Ok ∧
        H'.toX = (YMach.act xs H.toX cnt T.toX).1) ∧
      (ZMach.act xs O cnt T).2.1.toX = (YMach.act xs H.toX cnt T.toX).2.1 ∧
      (ZMach.act xs O cnt T).2.2 = (YMach.act xs H.toX cnt T.toX).2.2 := by
  have gen : ZMach.act xs O cnt T =
        ((OMach.act xs O T).1, (OMach.act xs O T).2.1, (OMach.act xs O T).2.2, cnt) →
      YMach.act xs H.toX cnt T.toX =
        ((XMach.act xs H.toX T.toX).1, (XMach.act xs H.toX T.toX).2.1,
          (XMach.act xs H.toX T.toX).2.2, cnt) →
      ((YMach.act xs H.toX cnt T.toX).1.agents.map Prod.fst).Nodup →
      (∃ H', (ZMach.act xs O cnt T).1.Agree H' ∧ H'.Ok ∧
          H'.toX = (YMach.act xs H.toX cnt T.toX).1) ∧
        (ZMach.act xs O cnt T).2.1.toX = (YMach.act xs H.toX cnt T.toX).2.1 ∧
        (ZMach.act xs O cnt T).2.2 = (YMach.act xs H.toX cnt T.toX).2.2 := by
    intro eZ eY hn
    rw [eY] at hn
    obtain ⟨a1, a2⟩ := OMach.act_agree xs h T
    obtain ⟨b1, b2, b3, b4⟩ := TMach.act_sim xs hk T hn
    rw [eZ, eY]
    refine ⟨⟨(TMach.act xs H T).1, a1, b4, b1⟩, ?_, ?_⟩
    · show (OMach.act xs O T).2.1.toX = (XMach.act xs H.toX T.toX).2.1
      rw [a2, b2]
    · show ((OMach.act xs O T).2.2, cnt) = ((XMach.act xs H.toX T.toX).2.2, cnt)
      rw [a2, b3]
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle => exact gen rfl rfl hnd
  | look a α => exact gen rfl rfl hnd
  | seek a α p c => exact gen rfl rfl hnd
  | ready a b α β => exact gen rfl rfl hnd
  | write as ls => exact gen rfl rfl hnd
  | half a b α β =>
    have es : O.sym b = assoc b H.toX.agents := (h.sym b).trans (hk.sym b)
    cases hR : (if assoc b H.toX.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | none =>
      have hRO : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) = none := by
        rw [es]
        exact hR
      have eX : XMach.act xs H.toX ⟨treeList todo, .half a b α β⟩ =
          (H.toX.putAgent a α, ⟨treeList todo, .idle⟩, 0) := XMach.act_half_none hR
      have eY : YMach.act xs H.toX cnt (TThread.toX ⟨todo, .half a b α β⟩) =
          (H.toX.putAgent a α, ⟨treeList todo, .idle⟩, 0, cnt) := by
        have e := YMach.act_zero (xs := xs) (X := H.toX)
          (T := ⟨treeList todo, .half a b α β⟩) cnt (congrArg (fun r => r.2.2) eX)
        rw [eX] at e
        exact e
      rw [eY] at hnd
      rw [eY, ZMach.act_half_none cnt hRO]
      have hnd' : (a :: H.toX.agents.map Prod.fst).Nodup := hnd
      have hi : assoc a H.toX.agents = none :=
        assoc_none_of_not_mem a _ (List.nodup_cons.1 hnd').1
      exact ⟨⟨H.put a α, h.put a α, hk.put hi α, TMem.toX_put hk a α⟩, rfl, rfl⟩
    | some R =>
      have hRO : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) = some R := by
        rw [es]
        exact hR
      have eY : YMach.act xs H.toX cnt (TThread.toX ⟨todo, .half a b α β⟩) =
          (H.toX.takeAgent b,
            ⟨treeList todo, .write (R.numAgents cnt) (R.numLinks xs.sys.ar a b cnt α β)⟩,
            1, cnt + R.span) := YMach.act_claim cnt hR
      rw [eY, ZMach.act_half cnt hRO]
      exact ⟨⟨H.take b, h.take b, (TMem.take_spec hk b).2, (TMem.take_spec hk b).1⟩, rfl, rfl⟩

/-- The state of the numbered program on ordered maps alone. -/
structure ZMach (S : Type) where
  mem : OMem S
  ths : List (TThread S)
  cnt : Nat

/-- The numbered program on lists that it stands for. -/
def ZMach.toY (M : ZMach S) : YMach S := ⟨M.mem.toX, M.ths.map TThread.toX, M.cnt⟩

/-- One action of thread `t`. -/
def ZMach.step (xs : XSys S) (M : ZMach S) (t : Nat) : ZMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(ZMach.act xs M.mem M.cnt T).1, M.ths.set t (ZMach.act xs M.mem M.cnt T).2.1,
        (ZMach.act xs M.mem M.cnt T).2.2.2⟩, (ZMach.act xs M.mem M.cnt T).2.2.1)
  | none => (M, 0)

/-- The run under an unending schedule. -/
def ZMach.trace (xs : XSys S) (σ : Nat → Nat) (M : ZMach S) : Nat → ZMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((ZMach.trace xs σ M i).1.step xs (σ i)).1,
      (ZMach.trace xs σ M i).2 + ((ZMach.trace xs σ M i).1.step xs (σ i)).2)

/-- **The numbered program on ordered maps alone, before it starts.** -/
def ZMach.init (X : XNet S) (n : Nat) : ZMach S := ⟨OMem.ofX X, (OMach.init X n).ths, X.top⟩

/-- One action on ordered maps alone is one action of the numbered
program on lists. -/
theorem ZMach.step_sim (xs : XSys S) {Z : ZMach S} {H : TMem S} (hA : Z.mem.Agree H)
    (hk : H.Ok) (t : Nat)
    (hnd : ((Z.toY.step xs t).1.mem.agents.map Prod.fst).Nodup) :
    (Z.step xs t).1.toY = (Z.toY.step xs t).1 ∧ (Z.step xs t).2 = (Z.toY.step xs t).2 ∧
      ∃ H', (Z.step xs t).1.mem.Agree H' ∧ H'.Ok := by
  cases hT : Z.ths[t]? with
  | none =>
    have e₁ : Z.step xs t = (Z, 0) := by
      unfold ZMach.step
      rw [hT]
    have hT' : Z.toY.ths[t]? = none := by
      show (Z.ths.map TThread.toX)[t]? = none
      rw [List.getElem?_map, hT]
      rfl
    have e₂ : Z.toY.step xs t = (Z.toY, 0) := by
      unfold YMach.step
      rw [hT']
    rw [e₁, e₂]
    exact ⟨rfl, rfl, H, hA, hk⟩
  | some T =>
    have hT' : Z.toY.ths[t]? = some T.toX := by
      show (Z.ths.map TThread.toX)[t]? = _
      rw [List.getElem?_map, hT]
      rfl
    have eX : Z.mem.toX = H.toX := hA.toX
    have e₂ : Z.toY.step xs t =
        (⟨(YMach.act xs H.toX Z.cnt T.toX).1,
          (Z.ths.map TThread.toX).set t (YMach.act xs H.toX Z.cnt T.toX).2.1,
          (YMach.act xs H.toX Z.cnt T.toX).2.2.2⟩, (YMach.act xs H.toX Z.cnt T.toX).2.2.1) := by
      rw [← eX]
      unfold YMach.step
      rw [hT'] <;> rfl
    have e₁ : Z.step xs t =
        (⟨(ZMach.act xs Z.mem Z.cnt T).1, Z.ths.set t (ZMach.act xs Z.mem Z.cnt T).2.1,
          (ZMach.act xs Z.mem Z.cnt T).2.2.2⟩, (ZMach.act xs Z.mem Z.cnt T).2.2.1) := by
      unfold ZMach.step
      rw [hT] <;> rfl
    rw [e₂] at hnd
    obtain ⟨⟨H', a1, a2, a3⟩, b, c⟩ := ZMach.act_sim xs hA hk Z.cnt T hnd
    rw [e₁, e₂]
    refine ⟨?_, ?_, H', a1, a2⟩
    · show (⟨(ZMach.act xs Z.mem Z.cnt T).1.toX,
          (Z.ths.set t (ZMach.act xs Z.mem Z.cnt T).2.1).map TThread.toX,
          (ZMach.act xs Z.mem Z.cnt T).2.2.2⟩ : YMach S) =
        ⟨(YMach.act xs H.toX Z.cnt T.toX).1,
          (Z.ths.map TThread.toX).set t (YMach.act xs H.toX Z.cnt T.toX).2.1,
          (YMach.act xs H.toX Z.cnt T.toX).2.2.2⟩
      rw [List.map_set, a1.toX, a3, b, c]
    · show (ZMach.act xs Z.mem Z.cnt T).2.2.1 = (YMach.act xs H.toX Z.cnt T.toX).2.2.1
      rw [c]

omit [DecidableEq S] in
theorem ZMach.init_toY {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (ZMach.init X n).toY = YMach.init X n := by
  have e : (OMach.init X n).toX = XMach.init X n :=
    (OMach.init_agree X n).toX.trans (TMach.init_toX hnd n)
  have e₁ : (OMem.ofX X).toX = X := congrArg XMach.mem e
  have e₂ : (OMach.init X n).ths.map TThread.toX = (XMach.init X n).ths :=
    congrArg XMach.ths e
  show (⟨(OMem.ofX X).toX, (OMach.init X n).ths.map TThread.toX, X.top⟩ : YMach S) =
    ⟨X, (XMach.init X n).ths, X.top⟩
  rw [e₁, e₂]

/-- The numbered program never has two agents of one name. -/
theorem YMach.trace_nodup {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    (((YMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
  have live := XMach.trace_live (xs := xs) σ (XMach.init_live hX hnt)
  have nd : ∀ i, (((XMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact XMach.step_nodup (live i) ih (σ i)
  obtain ⟨g, hr, -⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
  have h := nd i
  rw [hr.eq] at h
  have h' : ((((YMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).map g).Nodup := by
    have e : ((((YMach.init X nt).trace xs σ i).1.mem.agents.map fun e => (g e.1, e.2)).map
        Prod.fst) = (((YMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).map g := by
      rw [List.map_map, List.map_map]
      rfl
    rw [← e]
    exact h
  exact nodup_of_map' g _ h'

/-- **The numbered program on ordered maps alone runs as the numbered
program on lists does**, action by action, under any schedule. -/
theorem ZMach.trace_sim {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, ((ZMach.init X nt).trace xs σ i).1.toY = ((YMach.init X nt).trace xs σ i).1 ∧
      ((ZMach.init X nt).trace xs σ i).2 = ((YMach.init X nt).trace xs σ i).2 ∧
      ∃ H, ((ZMach.init X nt).trace xs σ i).1.mem.Agree H ∧ H.Ok
  | 0 => ⟨ZMach.init_toY hnd nt, rfl, TMem.ofX X, OMem.ofX_agree X, (TMem.ofX_toX hnd).1⟩
  | i + 1 => by
    obtain ⟨a, b, H, hA, hk⟩ := ZMach.trace_sim hX hnd hnt σ i
    have hn : ((((ZMach.init X nt).trace xs σ i).1.toY.step xs (σ i)).1.mem.agents.map
        Prod.fst).Nodup := by
      rw [a]
      exact YMach.trace_nodup hX hnd hnt σ (i + 1)
    obtain ⟨a', b', c'⟩ := ZMach.step_sim xs hA hk (σ i) hn
    refine ⟨?_, ?_, c'⟩
    · show (((ZMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toY =
        (((YMach.init X nt).trace xs σ i).1.step xs (σ i)).1
      rw [a', a]
    · show ((ZMach.init X nt).trace xs σ i).2 +
          (((ZMach.init X nt).trace xs σ i).1.step xs (σ i)).2 =
        ((YMach.init X nt).trace xs σ i).2 +
          (((YMach.init X nt).trace xs σ i).1.step xs (σ i)).2
      rw [b', b, a]

/-- **The numbered program on ordered maps alone follows the named program
on lists**: at every moment of every run its state, read as lists and
renamed by a map that keeps its names apart, is the state of the named
program, and both have claimed as often. -/
theorem ZMach.trace_rel {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ∃ g, ((ZMach.init X nt).trace xs σ i).1.toY.Rel g ((XMach.init X nt).trace xs σ i).1 ∧
      ((ZMach.init X nt).trace xs σ i).2 = ((XMach.init X nt).trace xs σ i).2 := by
  obtain ⟨a, b, -⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
  obtain ⟨g, hr, hc⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
  refine ⟨g, ?_, b.trans hc⟩
  rw [a]
  exact hr

/-- **Under a fair schedule the numbered program on ordered maps alone
comes to rest with the normal form, up to the names.** -/
theorem ZMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ∃ g,
      (∀ a b, ((ZMach.init X nt).trace xs σ i).1.toY.toX.Mentions a →
        ((ZMach.init X nt).trace xs σ i).1.toY.toX.Mentions b → g a = g b → a = b) ∧
      ((ZMach.init X nt).trace xs σ i).1.toY.toX.resting = true ∧
      ((ZMach.init X nt).trace xs σ i).2 = n ∧
      (((ZMach.init X nt).trace xs σ i).1.mem.toX.map g).toNet = N' := by
  obtain ⟨i₀, h⟩ := YMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨a, b, -⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
  obtain ⟨g, inj, r, c, m⟩ := h i hi
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [a]
    exact inj
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((ZMach.init X nt).trace xs σ i).1.mem.toX =
        ((YMach.init X nt).trace xs σ i).1.mem := congrArg YMach.mem a
    rw [e]
    exact m

/-- **On ordered maps alone the numbered names stay short.** -/
theorem ZMach.names_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {L : Nat}
    (hL : X.NamesLe L) (σ : Nat → Nat) (i : Nat) :
    ((ZMach.init X nt).trace xs σ i).1.toY.toX.NamesLe (max L 1) := by
  obtain ⟨a, -, -⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
  rw [a]
  exact YMach.names_le hL nt σ i

end NumberedOrdered

theorem filterMap_length_isSome {A B C : Type} {f : A → Option B} {g : A → Option C} :
    ∀ l : List A, (∀ x ∈ l, (f x).isSome = (g x).isSome) →
      (l.filterMap f).length = (l.filterMap g).length
  | [], _ => rfl
  | x :: l, h => by
    have ih := filterMap_length_isSome l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    cases hf : f x with
    | none =>
      cases hg : g x with
      | none =>
        rw [List.filterMap_cons_none hf, List.filterMap_cons_none hg]
        exact ih
      | some c =>
        rw [hf, hg] at hx
        cases hx
    | some b =>
      cases hg : g x with
      | none =>
        rw [hf, hg] at hx
        cases hx
      | some c =>
        rw [List.filterMap_cons_some hf, List.filterMap_cons_some hg, List.length_cons,
          List.length_cons, ih]

section NumberedCost

variable [DecidableEq S] {xs : XSys S}

omit [DecidableEq S] in
/-- A numbered claim writes as many agents as the named one. -/
theorem XRhs.numAgents_length (R : XRhs S) {a b : Id} (hne : a ≠ b) (cnt : Nat) :
    (R.numAgents cnt).length = (R.newAgents a b).length := by
  rw [R.newAgents_num hne cnt (extName_num (fun i => i) cnt a b), List.length_map]

omit [DecidableEq S] in
/-- A numbered claim writes as many segments as the named one. -/
theorem XRhs.numLinks_length (R : XRhs S) (ar : S → Nat) (a b : Id) (cnt : Nat) (α β : S) :
    (R.numLinks ar a b cnt α β).length = (R.newLinks ar a b α β).length := by
  show ((ifcPorts ar α β ++ R.newPorts ar).filterMap _).length =
    ((ifcPorts ar α β ++ R.newPorts ar).filterMap _).length
  refine filterMap_length_isSome _ (fun x _ => ?_)
  dsimp only
  cases R.wire x <;> rfl

/-- **What an action of the numbered program costs, everything counted.**
As `OMach.fcost`: every call of an operation on a map, every cell that a
comparison of two keys reads, every node built.  A claim pays for the
agents and segments it lists, as before, and one more for the counter. -/
def ZMach.fcost (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S) : Nat :=
  match T.st with
  | .half a b α β =>
    1 + O.symF b + if O.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          O.takeF b + 1 + (R.numAgents cnt).length + (R.numLinks xs.sys.ar a b cnt α β).length
        | none => O.putF a α
      else O.putF a α
  | _ => OMach.fcost xs O T

/-- On the same memory and thread, the numbered action costs what the
named one costs, and one more when the thread is not at rest. -/
theorem ZMach.fcost_le_named (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S) :
    ZMach.fcost xs O cnt T ≤ OMach.fcost xs O T + T.toX.busy := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle => exact Nat.le_add_right _ _
  | look a α => exact Nat.le_add_right _ _
  | seek a α p c => exact Nat.le_add_right _ _
  | ready a b α β => exact Nat.le_add_right _ _
  | write as ls => exact Nat.le_add_right _ _
  | half a b α β =>
    show ZMach.fcost xs O cnt ⟨todo, .half a b α β⟩ ≤
      OMach.fcost xs O ⟨todo, .half a b α β⟩ + 1
    unfold ZMach.fcost OMach.fcost
    dsimp only
    by_cases c : O.sym b = some β ∧ a ≠ b
    · rw [ite_pos' c, ite_pos' c]
      cases hr : xs.rule α β with
      | none =>
        dsimp only
        omega
      | some R =>
        show 1 + O.symF b + (O.takeF b + 1 + (R.numAgents cnt).length +
            (R.numLinks xs.sys.ar a b cnt α β).length) ≤
          1 + O.symF b + (O.takeF b + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length) + 1
        have e₁ := R.numAgents_length c.2 cnt
        have e₂ := R.numLinks_length xs.sys.ar a b cnt α β
        omega
    · rw [ite_neg' c, ite_neg' c]
      omega

/-- **Everything counted, a numbered action costs the size of a rule,
five, and four operations**, each at most `L + 6` for each level of a tree
under `Dm` deep, when no name the thread has in hand is longer than `L`. -/
theorem ZMach.fcost_le {C D : Nat} (hb : xs.Bounded C D) (O : OMem S) (cnt : Nat)
    (T : TThread S) {Dm L : Nat} (hc : tdepth O.cells + 1 ≤ Dm) (hl : ndepth O.live + 1 ≤ Dm)
    (hn : ndepth O.nbrs + 1 ≤ Dm) (ht : tdepth T.todo + 1 ≤ Dm)
    (hf : ∀ p c, findCells p (O.nb c) ≤ 2) (hN : T.toX.NamesLe L) :
    ZMach.fcost xs O cnt T ≤ (C + D + 5 + 4 * ((L + 6) * Dm)) * T.toX.busy := by
  have h₁ := ZMach.fcost_le_named xs O cnt T
  have h₂ := OMach.fcost_le hb O T hc hl hn ht hf hN
  have e₀ : C + D + 5 + 4 * ((L + 6) * Dm) = (C + D + 4 + 4 * ((L + 6) * Dm)) + 1 := by omega
  have e : (C + D + 5 + 4 * ((L + 6) * Dm)) * T.toX.busy =
      (C + D + 4 + 4 * ((L + 6) * Dm)) * T.toX.busy + T.toX.busy := by
    rw [e₀, Nat.add_mul, Nat.one_mul]
  omega

omit [DecidableEq S] in
theorem XThread.busy_map (g : Id → Id) (T : XThread S) : (T.map g).busy = T.busy := by
  obtain ⟨todo, st⟩ := T
  cases st <;> cases todo <;> rfl

/-- What the action of thread `t` of the numbered program costs. -/
def ZMach.stepFcost (xs : XSys S) (M : ZMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => ZMach.fcost xs M.mem M.cnt T
  | none => 0

/-- **The running time of the numbered program on ordered maps alone,
everything counted.** -/
def ZMach.ftime (xs : XSys S) (σ : Nat → Nat) (M : ZMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => ZMach.ftime xs σ M i + (M.trace xs σ i).1.stepFcost xs (σ i)

theorem ZMach.step_sized (xs : XSys S) {M : ZMach S} (h : M.mem.Sized) (t : Nat) :
    (M.step xs t).1.mem.Sized := by
  unfold ZMach.step
  cases M.ths[t]? with
  | none => exact h
  | some T =>
    show (ZMach.act xs M.mem M.cnt T).1.Sized
    rw [ZMach.act_mem]
    exact OMach.act_sized xs h T

theorem ZMach.trace_sized (xs : XSys S) (σ : Nat → Nat) {M : ZMach S} (h : M.mem.Sized) :
    ∀ i, (M.trace xs σ i).1.mem.Sized
  | 0 => h
  | i + 1 => ZMach.step_sized xs (ZMach.trace_sized xs σ h i) (σ i)

/-- **What one action of the numbered program costs, against the named
program.**  When the numbered state, renamed, is a state `M` of the named
program whose memory holds at most `A` agents and `W` segments, the action
of thread `t` costs at most the size of a rule, five, and four operations
on trees of depth under `3 * lg (A + W)` with keys of at most `L + 1`
cells, if thread `t` of `M` is not at rest, and nothing if it is. -/
theorem ZMach.stepFcost_le {C D : Nat} (hb : xs.Bounded C D) {Z : ZMach S} {H : TMem S}
    (hA : Z.mem.Agree H) (hk : H.Ok) (hsz : Z.mem.Sized) {g : Id → Id} {M : XMach S}
    (hM : M = Z.toY.toX.map g) {L A W : Nat} (hN : Z.toY.toX.NamesLe L)
    (hAg : M.mem.agents.length ≤ A) (hW : M.mem.wires.length ≤ W)
    (htd : ∀ T ∈ M.ths, T.todo.length ≤ A) (t : Nat) :
    Z.stepFcost xs t ≤
      (C + D + 5 + 4 * ((L + 6) * (3 * lg (A + W)))) * M.stepTally XThread.busy t := by
  subst hM
  have hcells : Z.mem.cells.size ≤ A := by
    rw [← treeList_length]
    have e : ((treeList Z.mem.cells).map fun e => (g e.1, e.2)).length ≤ A := hAg
    rw [List.length_map] at e
    exact e
  have hwires : Z.mem.wires.length ≤ W := by
    have e : (Z.mem.wires.map fun e => (mapPort g e.1, mapPort g e.2)).length ≤ W := hW
    rw [List.length_map] at e
    exact e
  have hm : (Z.toY.toX.map g).ths[t]? = (Z.ths[t]?).map fun T => T.toX.map g := by
    show ((Z.ths.map TThread.toX).map (XThread.map g))[t]? = _
    rw [List.getElem?_map, List.getElem?_map]
    cases Z.ths[t]? <;> rfl
  have d₁ := tdepth_lt Z.mem.cells
  have d₂ := ndepth_lt Z.mem.live
  have d₃ := ndepth_lt Z.mem.nbrs
  have m₁ := lg_mono (Nat.le_trans hcells (Nat.le_add_right _ W))
  have m₂ := lg_mono (Nat.le_trans (Nat.le_trans hsz.live hcells) (Nat.le_add_right _ W))
  have m₃ := lg_mono (Nat.le_trans (Nat.le_trans hsz.nbrs hwires) (Nat.le_add_left _ A))
  have hfc : ∀ p c, findCells p (Z.mem.nb c) ≤ 2 := by
    intro p c
    rw [hA.nb c, hk.nbrs c]
    exact findCells_nbOf _ c p
  unfold ZMach.stepFcost XMach.stepTally
  rw [hm]
  cases hT : Z.ths[t]? with
  | none => exact Nat.zero_le _
  | some T =>
    have hTm : T ∈ Z.ths := List.mem_of_getElem? hT
    have hTX : T.toX.map g ∈ (Z.toY.toX.map g).ths :=
      List.mem_map.2 ⟨T.toX, List.mem_map.2 ⟨T, hTm, rfl⟩, rfl⟩
    have htodo : T.todo.size ≤ A := by
      have e : ((treeList T.todo).map fun e => (g e.1, e.2)).length ≤ A := htd _ hTX
      rw [List.length_map, treeList_length] at e
      exact e
    have m₄ := lg_mono (Nat.le_trans htodo (Nat.le_add_right _ W))
    have d₄ := tdepth_lt T.todo
    have hNT : T.toX.NamesLe L := hN.2 T.toX (List.mem_map.2 ⟨T, hTm, rfl⟩)
    have hb' := ZMach.fcost_le hb Z.mem Z.cnt T (Dm := 3 * lg (A + W)) (by omega) (by omega)
      (by omega) (by omega) hfc hNT
    show ZMach.fcost xs Z.mem Z.cnt T ≤
      (C + D + 5 + 4 * ((L + 6) * (3 * lg (A + W)))) * (T.toX.map g).busy
    rw [XThread.busy_map]
    exact hb'

/-- **The running time of the numbered program, everything counted, is
its work times a cost that does not grow with the length of the run.**
Under any schedule each action that is not a rest costs at most

    C + D + 5 + 4 * ((max L 1 + 6) * (3 * lg m))

with `m` what the memory can hold, `X.agents.length + C * n +
(X.wires.length + D * n)`.  The names are numbers, of one cell, or names
of the net: the factor `L + n` of the named program is `max L 1` here. -/
theorem ZMach.ftime_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {L : Nat} (hL : X.NamesLe L) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (ZMach.init X nt).ftime xs σ i ≤
      (C + D + 5 + 4 * ((max L 1 + 6) *
          (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))) *
        (XMach.init X nt).work xs σ i := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have htodo := TMach.todo_le (xs := xs) hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨a, -, H, hA, hk⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨g, hr, -⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
    obtain ⟨tsim, -, -⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨hAg, -, -⟩ := hΦ i
    replace hAg := Nat.le_trans hAg
      (Nat.add_le_add_left (Nat.mul_le_mul_right n (Nat.sub_le C 2)) _)
    have hW := XMach.wires_le (xs := xs) hX hnt hb hs hn σ i
    have hNm := ZMach.names_le (xs := xs) hX hnd hnt hL σ i
    have sz := ZMach.trace_sized xs σ (M := ZMach.init X nt) (OMem.ofX_sized X) i
    have hXtodo : ∀ T ∈ ((XMach.init X nt).trace xs σ i).1.ths,
        T.todo.length ≤ X.agents.length + C * n := by
      intro T hT
      rw [← tsim] at hT
      have hT' : T ∈ ((TMach.init X nt).trace xs σ i).1.ths.map TThread.toX := hT
      obtain ⟨T', hT'', rfl⟩ := List.mem_map.1 hT'
      have h := htodo i T' hT''
      show (treeList T'.todo).length ≤ _
      rw [treeList_length]
      exact h
    have hM : ((XMach.init X nt).trace xs σ i).1 =
        ((ZMach.init X nt).trace xs σ i).1.toY.toX.map g := by
      rw [a]
      exact hr.eq
    have hstep := ZMach.stepFcost_le (xs := xs) hb hA hk sz hM hNm hAg hW hXtodo (σ i)
    show (ZMach.init X nt).ftime xs σ i +
        ((ZMach.init X nt).trace xs σ i).1.stepFcost xs (σ i) ≤
      (C + D + 5 + 4 * ((max L 1 + 6) *
          (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))) *
        ((XMach.init X nt).work xs σ i +
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i))
    rw [Nat.mul_add]
    omega

/-- **A bound on the running time of the numbered program on ordered maps
alone, everything counted, whatever the schedule.**  The length of the
run does not enter the cost of an action any more. -/
theorem ZMach.ftime_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {L : Nat} (hL : X.NamesLe L) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (i : Nat) :
    (ZMach.init X nt).ftime xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) *
        (C + D + 5 + 4 * ((max L 1 + 6) *
          (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))) := by
  have h₁ := ZMach.ftime_le_work (xs := xs) hX hnd hnt hb hL hs hn σ i
  have h₂ := Nat.mul_le_mul_left
    (C + D + 5 + 4 * ((max L 1 + 6) *
      (3 * lg (X.agents.length + C * n + (X.wires.length + D * n)))))
    (XMach.work_le hX hnd hnt hb hs hn σ i)
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  omega

/-- The program on ordered maps alone with the same memory and threads. -/
def ZMach.toO (M : ZMach S) : OMach S := ⟨M.mem, M.ths⟩

theorem ZMach.step_rest (xs : XSys S) {M : ZMach S} (h : M.toO.resting = true) (t : Nat) :
    M.step xs t = (M, 0) := by
  unfold ZMach.step
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := OMach.rest_thread (M := M.toO) h hT
    have e : OMach.act xs M.mem ⟨todo, .idle⟩ = (M.mem, ⟨todo, .idle⟩, 0) := by
      unfold OMach.act
      dsimp only
      rw [hmax]
    have e' : ZMach.act xs M.mem M.cnt ⟨todo, .idle⟩ = (M.mem, ⟨todo, .idle⟩, 0, M.cnt) := by
      show ((OMach.act xs M.mem ⟨todo, .idle⟩).1, (OMach.act xs M.mem ⟨todo, .idle⟩).2.1,
        (OMach.act xs M.mem ⟨todo, .idle⟩).2.2, M.cnt) = _
      rw [e]
    show ((⟨(ZMach.act xs M.mem M.cnt ⟨todo, .idle⟩).1,
      M.ths.set t (ZMach.act xs M.mem M.cnt ⟨todo, .idle⟩).2.1,
      (ZMach.act xs M.mem M.cnt ⟨todo, .idle⟩).2.2.2⟩ : ZMach S),
        (ZMach.act xs M.mem M.cnt ⟨todo, .idle⟩).2.2.1) = (M, 0)
    rw [e']
    show ((⟨M.mem, M.ths.set t ⟨todo, .idle⟩, M.cnt⟩ : ZMach S), 0) = (M, 0)
    rw [set_self M.ths t _ hT]

theorem ZMach.trace_rest (σ : Nat → Nat) {M : ZMach S} {B : Nat}
    (h : (M.trace xs σ B).1.toO.resting = true) :
    ∀ d, M.trace xs σ (B + d) = M.trace xs σ B
  | 0 => rfl
  | d + 1 => by
    show (((M.trace xs σ (B + d)).1.step xs (σ (B + d))).1,
      (M.trace xs σ (B + d)).2 + ((M.trace xs σ (B + d)).1.step xs (σ (B + d))).2) = _
    rw [ZMach.trace_rest σ h d, ZMach.step_rest xs h] <;> rfl

theorem ZMach.stepFcost_rest (xs : XSys S) {M : ZMach S} (h : M.toO.resting = true)
    (t : Nat) : M.stepFcost xs t = 0 := by
  unfold ZMach.stepFcost
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := OMach.rest_thread (M := M.toO) h hT
    show OMach.fcost xs M.mem ⟨todo, .idle⟩ = 0
    unfold OMach.fcost
    dsimp only
    rw [hmax]

/-- Once the numbered program is at rest its time stays what it is. -/
theorem ZMach.ftime_rest (σ : Nat → Nat) {M : ZMach S} {B : Nat}
    (h : (M.trace xs σ B).1.toO.resting = true) :
    ∀ d, M.ftime xs σ (B + d) = M.ftime xs σ B
  | 0 => rfl
  | d + 1 => by
    have z : (M.trace xs σ (B + d)).1.stepFcost xs (σ (B + d)) = 0 := by
      rw [ZMach.trace_rest σ h d]
      exact ZMach.stepFcost_rest xs h _
    show M.ftime xs σ (B + d) + (M.trace xs σ (B + d)).1.stepFcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact ZMach.ftime_rest σ h d

end NumberedCost

end INet
