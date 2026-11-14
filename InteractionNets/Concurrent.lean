import InteractionNets.Renaming

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## Concurrent execution

Firings need not be atomic.  In the model below a firing is *claimed* in one
atomic action, which deletes the two agents of an active pair, and is then
carried out by separate writes, one new agent or one new segment at a time.
The writes of different firings interleave arbitrarily, and a pair may be
claimed as soon as it is visible, while earlier firings are still being
written.  Every such execution is a sequential reduction with one step per
claim, so its result is the normal form. -/

section Concurrent

section WalkTerm

variable {V : Type u} {L L' G : V → V → Prop} {T T' TG : V → Prop}

/-- A walk survives when segments and terminals are added, as long as all
of them belong to a wiring in which a terminal lies on one segment only: a
point with two neighbours on the walk cannot have become a terminal. -/
theorem Walk.mono_term (hL : ∀ {p q}, L p q → L' p q) (hG : ∀ {p q}, L p q → G p q)
    (hs : ∀ {p q}, G p q → G q p) (hT : ∀ {p}, T' p → TG p)
    (hu : ∀ {p q r}, TG p → G p q → G p r → q = r)
    {u v x y : V} (w : Walk L T u v x y) : Walk L' T' u v x y := by
  induction w with
  | single h => exact .single (hL h)
  | cons h _ hw w ih =>
    exact .cons (hL h) (fun hT' => hw (hu (hT hT') (hG w.link_first) (hs (hG h)))) hw ih

end WalkTerm


/-- A state of a concurrent execution: the net as written so far, and the
net that will be there once all the firings claimed so far are written. -/
structure CState (S : Type) where
  now : Net S
  goal : Net S

/-- Delete two agents. -/
def Net.claim (N : Net S) (a b : Id) : Net S where
  agent i γ := N.agent i γ ∧ i ≠ a ∧ i ≠ b
  link := N.link
  free := N.free

/-- Write one agent. -/
def Net.addAgent (N : Net S) (i : Id) (γ : S) : Net S where
  agent j δ := N.agent j δ ∨ (j = i ∧ δ = γ)
  link := N.link
  free := N.free

/-- Write one segment, in one direction. -/
def Net.addLink (N : Net S) (p q : Port) : Net S where
  agent := N.agent
  link x y := N.link x y ∨ (x = p ∧ y = q)
  free := N.free

/-- One atomic action.  The number is `1` for a claim and `0` for a write. -/
inductive Conc (sys : System S) : Nat → CState S → CState S → Prop
  /-- Claim an active pair of the net as written so far. -/
  | claim {st : CState S} {a b : Id} {α β : S} {R : Rhs S} :
      Redex sys st.now a b α β R → Conc sys 1 st ⟨st.now.claim a b, st.goal.fire a b R⟩
  /-- Write an agent that is still missing. -/
  | agent {st : CState S} {i : Id} {γ : S} :
      st.goal.agent i γ → ¬ st.now.agent i γ → Conc sys 0 st ⟨st.now.addAgent i γ, st.goal⟩
  /-- Write a segment that is still missing. -/
  | link {st : CState S} {p q : Port} :
      st.goal.link p q → ¬ st.now.link p q → Conc sys 0 st ⟨st.now.addLink p q, st.goal⟩

/-- `Run sys k st st'`: an execution from `st` to `st'` with `k` claims. -/
inductive Run (sys : System S) : Nat → CState S → CState S → Prop
  | refl (st : CState S) : Run sys 0 st st
  | step {c k : Nat} {st st' st'' : CState S} :
      Conc sys c st st' → Run sys k st' st'' → Run sys (c + k) st st''

theorem Run.trans {k k' : Nat} {st st' st'' : CState S} (h : Run sys k st st')
    (h' : Run sys k' st' st'') : Run sys (k + k') st st'' := by
  induction h with
  | refl st =>
    rw [Nat.zero_add]
    exact h'
  | step hc _ ih =>
    rw [Nat.add_assoc]
    exact .step hc (ih h')

/-- What has been written so far is part of the goal, and the goal is well
formed. -/
structure CState.Sound (ar : S → Nat) (st : CState S) : Prop where
  wf : st.goal.WF ar
  agent : ∀ {i γ}, st.now.agent i γ → st.goal.agent i γ
  link : ∀ {p q}, st.now.link p q → st.goal.link p q
  free : st.now.free = st.goal.free

theorem CState.Sound.refl {ar : S → Nat} {N : Net S} (hN : N.WF ar) :
    CState.Sound ar ⟨N, N⟩ :=
  ⟨hN, fun h => h, fun h => h, rfl⟩

variable {st st' : CState S} {a b : Id} {α β : S} {R : Rhs S}

theorem CState.Sound.end_goal (h : st.Sound sys.ar) {p : Port} (hp : st.now.End sys.ar p) :
    st.goal.End sys.ar p := by
  rcases hp with hf | ⟨γ, hg, hk⟩
  · exact .inl (h.free ▸ hf)
  · exact .inr ⟨γ, h.agent hg, hk⟩

/-- **A pair that looks active is active**: an active pair of the net as
written so far is an active pair of the goal. -/
theorem CState.Sound.redex (h : st.Sound sys.ar) (r : Redex sys st.now a b α β R) :
    Redex sys st.goal a b α β R where
  ha := h.agent r.ha
  hb := h.agent r.hb
  ne := r.ne
  conn := by
    obtain ⟨v, x, w⟩ := r.conn
    exact ⟨v, x, w.mono_term (fun hl => h.link hl) (fun hl => h.link hl) h.wf.symm
      (fun hT => hT) h.wf.end_unique⟩
  rule := r.rule

/-- An action preserves soundness, and moves the goal by one sequential
step if it is a claim, and not at all if it is a write. -/
theorem Conc.sound {c : Nat} (h : st.Sound sys.ar) (hc : Conc sys c st st') :
    st'.Sound sys.ar ∧ Steps (Step sys) c st.goal st'.goal := by
  cases hc with
  | claim r =>
    have s : Step sys st.goal (st.goal.fire _ _ _) := ⟨_, _, _, _, _, h.redex r, rfl⟩
    exact ⟨⟨Step.wf h.wf s, fun hi => .inl ⟨h.agent hi.1, hi.2.1, hi.2.2⟩,
      fun hl => .inl (h.link hl), h.free⟩, .single s⟩
  | agent hi _ =>
    refine ⟨⟨h.wf, ?_, h.link, h.free⟩, .refl _⟩
    rintro j δ (hj | ⟨rfl, rfl⟩)
    · exact h.agent hj
    · exact hi
  | link hl _ =>
    refine ⟨⟨h.wf, h.agent, ?_, h.free⟩, .refl _⟩
    rintro x y (hxy | ⟨rfl, rfl⟩)
    · exact h.link hxy
    · exact hl

theorem Run.sound {k : Nat} (h : st.Sound sys.ar) (hr : Run sys k st st') :
    st'.Sound sys.ar ∧ Steps (Step sys) k st.goal st'.goal := by
  induction hr with
  | refl st => exact ⟨h, .refl _⟩
  | step hc _ ih =>
    obtain ⟨h₁, s₁⟩ := hc.sound h
    obtain ⟨h₂, s₂⟩ := ih h₁
    exact ⟨h₂, s₁.trans s₂⟩

/-- **Every concurrent execution is a sequential reduction**, with one step
per claim, of the net it started from to its goal. -/
theorem Run.sequential {k : Nat} (hN : N.WF sys.ar) (hr : Run sys k ⟨N, N⟩ st) :
    Steps (Step sys) k N st.goal :=
  (hr.sound (CState.Sound.refl hN)).2

/-- Nothing left to do: no pair to claim and nothing to write. -/
def CState.Terminal (sys : System S) (st : CState S) : Prop :=
  ∀ c st', ¬ Conc sys c st st'

/-- When nothing is left to do, everything is written and the net is
normal. -/
theorem CState.Sound.terminal (h : st.Sound sys.ar) (ht : st.Terminal sys) :
    st.now = st.goal ∧ Normal (Step sys) st.goal := by
  have e : st.now = st.goal := by
    apply Net.ext'
    · exact fun i γ => ⟨h.agent, fun hg => Classical.byContradiction fun hn => ht 0 _ (.agent hg hn)⟩
    · exact fun p q => ⟨h.link, fun hg => Classical.byContradiction fun hn => ht 0 _ (.link hg hn)⟩
    · exact fun p => by rw [h.free]
  refine ⟨e, ?_⟩
  rintro N' ⟨a, b, α, β, R, r, -⟩
  rw [← e] at r
  exact ht 1 _ (.claim r)

/-- **A concurrent execution that has nothing left to do has computed the
normal form**: everything is written, the net is normal, the number of claims
is the length of every reduction to normal form, and no sequential reduction
is longer or ends at another normal form. -/
theorem Run.terminal {k : Nat} (hN : N.WF sys.ar) (hr : Run sys k ⟨N, N⟩ st)
    (ht : st.Terminal sys) :
    st.now = st.goal ∧ Steps (Step sys) k N st.now ∧ Normal (Step sys) st.now ∧
      ∀ {m : Nat} {N' : Net S}, Steps (Step sys) m N N' →
        m ≤ k ∧ (Normal (Step sys) N' → N' = st.now ∧ m = k) := by
  obtain ⟨hs, sts⟩ := hr.sound (CState.Sound.refl hN)
  obtain ⟨e, hn⟩ := hs.terminal ht
  rw [e]
  refine ⟨rfl, sts, hn, fun {m N'} h' => ⟨(reduction_bounded hN sts hn h').1, fun hn' => ?_⟩⟩
  exact normal_form_unique hN h' sts hn' hn

/-- Two concurrent executions of the same net that have nothing left to do
have written the same net, with the same number of claims. -/
theorem Run.confluent {k k' : Nat} {st₁ st₂ : CState S} (hN : N.WF sys.ar)
    (h₁ : Run sys k ⟨N, N⟩ st₁) (h₂ : Run sys k' ⟨N, N⟩ st₂)
    (t₁ : st₁.Terminal sys) (t₂ : st₂.Terminal sys) : st₁.now = st₂.now ∧ k = k' := by
  obtain ⟨-, s₁, n₁, -⟩ := h₁.terminal hN t₁
  obtain ⟨-, s₂, n₂, -⟩ := h₂.terminal hN t₂
  exact normal_form_unique hN s₁ s₂ n₁ n₂

/-- **Claims do not interfere**: a visible active pair stays visible, whatever
the other actions, for as long as its agents have not been claimed.  So an
active pair need not be detected atomically. -/
theorem Conc.persist {c : Nat} (h : st.Sound sys.ar) (hc : Conc sys c st st')
    (r : Redex sys st.now a b α β R) (ha : st'.now.agent a α) :
    Redex sys st'.now a b α β R := by
  have h' := (hc.sound h).1
  have rg := h.redex r
  cases hc with
  | @claim _ c' d γ δ R' r' =>
    have rg' := h.redex r'
    have hac : a ≠ c' := ha.2.1
    have had : a ≠ d := ha.2.2
    have hbc : b ≠ c' := by
      rintro rfl
      obtain ⟨R₁, r₁, -⟩ := rg.flip h.wf
      exact had (r₁.partner_unique rg' h.wf)
    have hbd : b ≠ d := by
      rintro rfl
      obtain ⟨R₁, r₁, -⟩ := rg.flip h.wf
      obtain ⟨R₂, r₂, -⟩ := rg'.flip h.wf
      exact hac (r₁.partner_unique r₂ h.wf)
    refine ⟨ha, ⟨r.hb, hbc, hbd⟩, r.ne, ?_, r.rule⟩
    obtain ⟨v, x, w⟩ := r.conn
    refine ⟨v, x, w.mono (fun hl => hl) (fun _ hv hE => hv ?_)⟩
    rcases hE with hf | ⟨ε, hg, hk⟩
    · exact .inl hf
    · exact .inr ⟨ε, hg.1, hk⟩
  | agent hi hn =>
    refine ⟨ha, .inl r.hb, r.ne, ?_, r.rule⟩
    obtain ⟨v, x, w⟩ := r.conn
    exact ⟨v, x, w.mono_term (fun hl => hl) (fun hl => h.link hl) h.wf.symm
      (fun hT => h'.end_goal hT) h.wf.end_unique⟩
  | link hl hn =>
    refine ⟨ha, r.hb, r.ne, ?_, r.rule⟩
    obtain ⟨v, x, w⟩ := r.conn
    exact ⟨v, x, w.mono_term (fun hl => .inl hl) (fun hl => h.link hl) h.wf.symm
      (fun hT => h'.end_goal hT) h.wf.end_unique⟩

/-- Writes can supply any finite list of missing agents. -/
theorem Run.flush_agents (goal : Net S) (as : List (Id × S)) :
    ∀ now : Net S, ∃ now', Run sys 0 ⟨now, goal⟩ ⟨now', goal⟩ ∧ now'.link = now.link ∧
      now'.free = now.free ∧ (∀ {i γ}, now.agent i γ → now'.agent i γ) ∧
      (∀ {i γ}, now'.agent i γ → now.agent i γ ∨ goal.agent i γ) ∧
      ∀ e ∈ as, goal.agent e.1 e.2 → now'.agent e.1 e.2 := by
  induction as with
  | nil =>
    exact fun now => ⟨now, .refl _, rfl, rfl, fun h => h, fun h => .inl h,
      fun e he => absurd he List.not_mem_nil⟩
  | cons e as ih =>
    intro now
    by_cases hc : goal.agent e.1 e.2 ∧ ¬ now.agent e.1 e.2
    · obtain ⟨now', hr, el, ef, h₁, h₂, h₃⟩ := ih (now.addAgent e.1 e.2)
      refine ⟨now', .step (.agent (st := ⟨now, goal⟩) hc.1 hc.2) hr, el, ef,
        fun h => h₁ (.inl h), ?_, ?_⟩
      · intro i γ h
        rcases h₂ h with (h | ⟨rfl, rfl⟩) | h
        · exact .inl h
        · exact .inr hc.1
        · exact .inr h
      · intro e' he' hg
        rcases List.mem_cons.1 he' with rfl | he'
        · exact h₁ (.inr ⟨rfl, rfl⟩)
        · exact h₃ e' he' hg
    · obtain ⟨now', hr, el, ef, h₁, h₂, h₃⟩ := ih now
      refine ⟨now', hr, el, ef, h₁, h₂, ?_⟩
      intro e' he' hg
      rcases List.mem_cons.1 he' with rfl | he'
      · exact h₁ (Classical.byContradiction fun hn => hc ⟨hg, hn⟩)
      · exact h₃ e' he' hg

/-- Writes can supply any finite list of missing segments. -/
theorem Run.flush_links (goal : Net S) (ws : List (Port × Port)) :
    ∀ now : Net S, ∃ now', Run sys 0 ⟨now, goal⟩ ⟨now', goal⟩ ∧ now'.agent = now.agent ∧
      now'.free = now.free ∧ (∀ {p q}, now.link p q → now'.link p q) ∧
      (∀ {p q}, now'.link p q → now.link p q ∨ goal.link p q) ∧
      ∀ e ∈ ws, goal.link e.1 e.2 → now'.link e.1 e.2 := by
  induction ws with
  | nil =>
    exact fun now => ⟨now, .refl _, rfl, rfl, fun h => h, fun h => .inl h,
      fun e he => absurd he List.not_mem_nil⟩
  | cons e ws ih =>
    intro now
    by_cases hc : goal.link e.1 e.2 ∧ ¬ now.link e.1 e.2
    · obtain ⟨now', hr, ea, ef, h₁, h₂, h₃⟩ := ih (now.addLink e.1 e.2)
      refine ⟨now', .step (.link (st := ⟨now, goal⟩) hc.1 hc.2) hr, ea, ef,
        fun h => h₁ (.inl h), ?_, ?_⟩
      · intro p q h
        rcases h₂ h with (h | ⟨rfl, rfl⟩) | h
        · exact .inl h
        · exact .inr hc.1
        · exact .inr h
      · intro e' he' hg
        rcases List.mem_cons.1 he' with rfl | he'
        · exact h₁ (.inr ⟨rfl, rfl⟩)
        · exact h₃ e' he' hg
    · obtain ⟨now', hr, ea, ef, h₁, h₂, h₃⟩ := ih now
      refine ⟨now', hr, ea, ef, h₁, h₂, ?_⟩
      intro e' he' hg
      rcases List.mem_cons.1 he' with rfl | he'
      · exact h₁ (Classical.byContradiction fun hn => hc ⟨hg, hn⟩)
      · exact h₃ e' he' hg

/-- **Writes can always be completed** when finitely many are missing: the
execution can go on, by writes alone, until everything is written. -/
theorem Run.flush (h : st.Sound sys.ar) (as : List (Id × S)) (ws : List (Port × Port))
    (ha : ∀ i γ, st.goal.agent i γ → st.now.agent i γ ∨ (i, γ) ∈ as)
    (hl : ∀ p q, st.goal.link p q → st.now.link p q ∨ (p, q) ∈ ws) :
    Run sys 0 st ⟨st.goal, st.goal⟩ := by
  obtain ⟨now₁, r₁, el, ef, a₁, a₂, a₃⟩ := Run.flush_agents (sys := sys) st.goal as st.now
  obtain ⟨now₂, r₂, ea', ef', l₁, l₂, l₃⟩ := Run.flush_links (sys := sys) st.goal ws now₁
  have e : now₂ = st.goal := by
    apply Net.ext'
    · intro i γ
      rw [ea']
      constructor
      · intro hi
        rcases a₂ hi with hi | hi
        · exact h.agent hi
        · exact hi
      · intro hg
        rcases ha i γ hg with hi | hm
        · exact a₁ hi
        · exact a₃ _ hm hg
    · intro p q
      constructor
      · intro hpq
        rcases l₂ hpq with hpq | hpq
        · rw [el] at hpq
          exact h.link hpq
        · exact hpq
      · intro hg
        rcases hl p q hg with hpq | hm
        · rw [← el] at hpq
          exact l₁ hpq
        · exact l₃ _ hm hg
    · intro p
      rw [ef', ef, h.free]
  have r := r₁.trans r₂
  rw [e] at r
  exact r

/-- A right-hand side with finitely many agents and wires. -/
def Rhs.Fin (R : Rhs S) : Prop :=
  ∃ (ls : List (Option Bool × Nat)) (ws : List (LPort × LPort)),
    (∀ o j γ, R.lab o j = some γ → (o, j) ∈ ls) ∧ ∀ x y, R.link x y → (x, y) ∈ ws

/-- A sequential step with a finite rule is a concurrent execution: one
claim, then the writes. -/
theorem Redex.run (hN : N.WF sys.ar) (r : Redex sys N a b α β R) (hf : R.Fin) :
    Run sys 1 ⟨N, N⟩ ⟨N.fire a b R, N.fire a b R⟩ := by
  obtain ⟨ls, ws, hls, hws⟩ := hf
  have hc : Conc sys 1 ⟨N, N⟩ ⟨N.claim a b, N.fire a b R⟩ := .claim r
  have hs := (hc.sound (CState.Sound.refl hN)).1
  have ha : ∀ i γ, (N.fire a b R).agent i γ → (N.claim a b).agent i γ ∨
      (i, γ) ∈ ls.filterMap fun e => (R.lab e.1 e.2).map fun γ => (child a b e.1 e.2, γ) := by
    rintro i γ (h | ⟨o, j, rfl, hl⟩)
    · exact .inl h
    · exact .inr (List.mem_filterMap.2 ⟨(o, j), hls o j γ hl, by simp [hl]⟩)
  have hl : ∀ p q, (N.fire a b R).link p q → (N.claim a b).link p q ∨
      (p, q) ∈ ws.map fun e => (emb a b e.1, emb a b e.2) := by
    rintro p q (h | ⟨x, y, hxy, rfl, rfl⟩)
    · exact .inl h
    · exact .inr (List.mem_map.2 ⟨(x, y), hws x y hxy, rfl⟩)
  exact .step hc (Run.flush hs _ _ ha hl)

/-- **Every sequential reduction is a concurrent execution**, when the
rules are finite. -/
theorem Steps.run (hfin : ∀ {α β : S} {R : Rhs S}, sys.rule α β = some R → R.Fin) {n : Nat}
    {N' : Net S} (hN : N.WF sys.ar) (h : Steps (Step sys) n N N') :
    Run sys n ⟨N, N⟩ ⟨N', N'⟩ := by
  induction h with
  | refl N => exact .refl _
  | head h₁ _ ih =>
    obtain ⟨a, b, α, β, R, r, rfl⟩ := h₁
    have hr := (r.run hN (hfin r.rule)).trans (ih (Step.wf hN ⟨_, _, _, _, _, r, rfl⟩))
    rw [Nat.add_comm] at hr
    exact hr

end Concurrent

/-! ## A machine with shared memory

`Conc` keeps, next to the net as written so far, the net that will be there
once everything is written, and its claim sees an active pair all at once.
The machine below has neither.  Its state is the memory and one private
state for each thread.  A thread looks for an active pair by reading one cell
at a time: an agent, then the segments of the wire that leaves its principal
port, then the agent at the other end.  It takes the two agents with two
compare-and-swaps, and gives the first one back if it does not get the
second.  It then writes the right-hand side from a private list, one cell at
a time.  Every action reads or writes a single cell of memory, and the
threads are interleaved in any order.

`MStep.sim` shows that an action of the machine is an action of `Conc` or
changes nothing that `Conc` sees.  So whatever the schedule and the number
of threads, the machine computes the normal form, with one claim for each
step of the sequential reduction (`MRun.final`). -/

section Machine

/-- Empty the cell of agent `a`. -/
def Net.take (N : Net S) (a : Id) : Net S where
  agent i γ := N.agent i γ ∧ i ≠ a
  link := N.link
  free := N.free

/-- The private state of a thread. -/
inductive TState (S : Type) where
  /-- Nothing in hand. -/
  | idle
  /-- Has read that agent `a` carries `α`. -/
  | look (a : Id) (α : S)
  /-- Is following the wire that leaves the principal port of `a`, and has
  arrived at `cur` from `prev`. -/
  | seek (a : Id) (α : S) (prev cur : Port)
  /-- Has read that the wire ends on the principal port of `b`, which
  carries `β`. -/
  | ready (a b : Id) (α β : S)
  /-- Has taken `a`, and not yet `b`. -/
  | half (a b : Id) (α β : S)
  /-- Has taken both, and has these agents and segments left to write. -/
  | write (as : List (Id × S)) (ls : List (Port × Port))

/-- The states of a thread that is still looking. -/
def TState.Passive : TState S → Prop
  | .look _ _ => True
  | .seek _ _ _ _ => True
  | .ready _ _ _ _ => True
  | _ => False

/-- The agent that a thread has taken out of memory and may still give
back. -/
def TState.held : TState S → Id → S → Prop
  | .half a _ α _, i, γ => i = a ∧ γ = α
  | _, _, _ => False

/-- The agents that a thread has left to write. -/
def TState.pendA : TState S → Id → S → Prop
  | .write as _, i, γ => (i, γ) ∈ as
  | _, _, _ => False

/-- The segments that a thread has left to write. -/
def TState.pendL : TState S → Port → Port → Prop
  | .write _ ls, p, q => (p, q) ∈ ls
  | _, _, _ => False

/-- A machine: the shared memory, and the private state of each thread. -/
structure Mach (S : Type) where
  mem : Net S
  th : Nat → TState S

/-- Change the state of thread `t`. -/
def upd (th : Nat → TState S) (t : Nat) (s : TState S) : Nat → TState S :=
  fun u => if u = t then s else th u

theorem upd_same (th : Nat → TState S) (t : Nat) (s : TState S) : upd th t s t = s := by
  show (if t = t then s else th t) = s
  split
  · rfl
  · rename_i h
    exact absurd rfl h

theorem upd_ne (th : Nat → TState S) (s : TState S) {t u : Nat} (h : u ≠ t) :
    upd th t s u = th u := by
  show (if u = t then s else th u) = th u
  split
  · rename_i h'
    exact absurd h' h
  · rfl

/-- The lists `as` and `ls` are the new agents and the new segments of a
firing of `a` and `b` with right-hand side `R`, each agent listed once. -/
structure Writes (a b : Id) (R : Rhs S) (as : List (Id × S)) (ls : List (Port × Port)) :
    Prop where
  agent : ∀ {i γ}, (i, γ) ∈ as ↔ ∃ o j, i = child a b o j ∧ R.lab o j = some γ
  nodup : (as.map Prod.fst).Nodup
  link : ∀ {p q}, (p, q) ∈ ls ↔ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y

/-- One action of one thread.  The number is `1` for the compare-and-swap
that completes a claim and `0` for every other action. -/
inductive MStep (sys : System S) : Nat → Mach S → Mach S → Prop
  /-- Read an agent cell. -/
  | look {M : Mach S} {t : Nat} {a : Id} {α : S} :
      M.th t = .idle → M.mem.agent a α →
      MStep sys 0 M ⟨M.mem, upd M.th t (.look a α)⟩
  /-- Read the segment that leaves the principal port. -/
  | first {M : Mach S} {t : Nat} {a : Id} {α : S} {q : Port} :
      M.th t = .look a α → M.mem.link (a, 0) q →
      MStep sys 0 M ⟨M.mem, upd M.th t (.seek a α (a, 0) q)⟩
  /-- Read the next segment of the wire. -/
  | next {M : Mach S} {t : Nat} {a : Id} {α : S} {p c q : Port} :
      M.th t = .seek a α p c → M.mem.link c q → q ≠ p →
      MStep sys 0 M ⟨M.mem, upd M.th t (.seek a α c q)⟩
  /-- Read the agent cell at the other end of the wire. -/
  | found {M : Mach S} {t : Nat} {a b : Id} {α β : S} {p : Port} :
      M.th t = .seek a α p (b, 0) → M.mem.agent b β →
      MStep sys 0 M ⟨M.mem, upd M.th t (.ready a b α β)⟩
  /-- Give up looking. -/
  | quit {M : Mach S} {t : Nat} :
      (M.th t).Passive → MStep sys 0 M ⟨M.mem, upd M.th t .idle⟩
  /-- Compare-and-swap the first agent out of memory. -/
  | cas₁ {M : Mach S} {t : Nat} {a b : Id} {α β : S} :
      M.th t = .ready a b α β → M.mem.agent a α →
      MStep sys 0 M ⟨M.mem.take a, upd M.th t (.half a b α β)⟩
  /-- Write the first agent back. -/
  | undo {M : Mach S} {t : Nat} {a b : Id} {α β : S} :
      M.th t = .half a b α β →
      MStep sys 0 M ⟨M.mem.addAgent a α, upd M.th t .idle⟩
  /-- Compare-and-swap the second agent out of memory: the pair is claimed,
  and the thread loads the right-hand side of the rule. -/
  | cas₂ {M : Mach S} {t : Nat} {a b : Id} {α β : S} {R : Rhs S} {as : List (Id × S)}
      {ls : List (Port × Port)} :
      M.th t = .half a b α β → M.mem.agent b β → a ≠ b → sys.rule α β = some R →
      Writes a b R as ls →
      MStep sys 1 M ⟨M.mem.take b, upd M.th t (.write as ls)⟩
  /-- Write an agent cell. -/
  | agent {M : Mach S} {t : Nat} {i : Id} {γ : S} {as : List (Id × S)}
      {ls : List (Port × Port)} :
      M.th t = .write ((i, γ) :: as) ls →
      MStep sys 0 M ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩
  /-- Write a segment cell. -/
  | link {M : Mach S} {t : Nat} {p q : Port} {as : List (Id × S)}
      {ls : List (Port × Port)} :
      M.th t = .write as ((p, q) :: ls) →
      MStep sys 0 M ⟨M.mem.addLink p q, upd M.th t (.write as ls)⟩
  /-- Nothing left to write. -/
  | done {M : Mach S} {t : Nat} :
      M.th t = .write [] [] → MStep sys 0 M ⟨M.mem, upd M.th t .idle⟩

/-- `MRun sys k M M'`: an execution of the machine with `k` claims. -/
inductive MRun (sys : System S) : Nat → Mach S → Mach S → Prop
  | refl (M : Mach S) : MRun sys 0 M M
  | step {c k : Nat} {M M' M'' : Mach S} :
      MStep sys c M M' → MRun sys k M' M'' → MRun sys (c + k) M M''

theorem MRun.trans {k k' : Nat} {M M' M'' : Mach S} (h : MRun sys k M M')
    (h' : MRun sys k' M' M'') : MRun sys (k + k') M M'' := by
  induction h with
  | refl M =>
    rw [Nat.zero_add]
    exact h'
  | step hc _ ih =>
    rw [Nat.add_assoc]
    exact .step hc (ih h')

/-! ### What `Conc` sees of the machine -/

/-- The net as written so far, for `Conc`: the memory, and the agents that
threads have taken and may still give back. -/
def Mach.now (M : Mach S) : Net S where
  agent i γ := M.mem.agent i γ ∨ ∃ t, (M.th t).held i γ
  link := M.mem.link
  free := M.mem.free

/-- The goal: the net as written so far, and what the threads have left to
write. -/
def Mach.goal (M : Mach S) : Net S where
  agent i γ := M.now.agent i γ ∨ ∃ t, (M.th t).pendA i γ
  link p q := M.mem.link p q ∨ ∃ t, (M.th t).pendL p q
  free := M.mem.free

/-- The state of `Conc` that a state of the machine stands for. -/
def Mach.abs (M : Mach S) : CState S := ⟨M.now, M.goal⟩

theorem ex_upd {th : Nat → TState S} {t : Nat} {s : TState S} {P : TState S → Prop} :
    (∃ u, P (upd th t s u)) ↔ P s ∨ ∃ u, u ≠ t ∧ P (th u) := by
  constructor
  · rintro ⟨u, h⟩
    by_cases hu : u = t
    · rw [hu, upd_same] at h
      exact .inl h
    · rw [upd_ne _ _ hu] at h
      exact .inr ⟨u, hu, h⟩
  · rintro (h | ⟨u, hu, h⟩)
    · exact ⟨t, by rw [upd_same]; exact h⟩
    · exact ⟨u, by rw [upd_ne _ _ hu]; exact h⟩

theorem ex_split {th : Nat → TState S} (t : Nat) {P : TState S → Prop} :
    (∃ u, P (th u)) ↔ P (th t) ∨ ∃ u, u ≠ t ∧ P (th u) := by
  constructor
  · rintro ⟨u, h⟩
    by_cases hu : u = t
    · rw [hu] at h
      exact .inl h
    · exact .inr ⟨u, hu, h⟩
  · rintro (h | ⟨u, -, h⟩)
    · exact ⟨t, h⟩
    · exact ⟨u, h⟩

theorem upd_imp {th : Nat → TState S} {t : Nat} {s : TState S} {P : TState S → Prop}
    (h : P s → P (th t)) {u : Nat} (hu : P (upd th t s u)) : P (th u) := by
  by_cases e : u = t
  · rw [e, upd_same] at hu
    rw [e]
    exact h hu
  · rw [upd_ne _ _ e] at hu
    exact hu

theorem unique_upd {th : Nat → TState S} {t : Nat} {s : TState S}
    {P : TState S → Id → S → Prop}
    (hold : ∀ {u u' i γ γ'}, P (th u) i γ → P (th u') i γ' → u = u')
    (hnew : ∀ {u i γ γ'}, u ≠ t → P s i γ → ¬ P (th u) i γ')
    {u u' : Nat} {i : Id} {γ γ' : S} (h₁ : P (upd th t s u) i γ)
    (h₂ : P (upd th t s u') i γ') : u = u' := by
  by_cases hu : u = t <;> by_cases hu' : u' = t
  · rw [hu, hu']
  · rw [hu, upd_same] at h₁
    rw [upd_ne _ _ hu'] at h₂
    exact absurd h₂ (hnew hu' h₁)
  · rw [upd_ne _ _ hu] at h₁
    rw [hu', upd_same] at h₂
    exact absurd h₁ (hnew hu h₂)
  · rw [upd_ne _ _ hu] at h₁
    rw [upd_ne _ _ hu'] at h₂
    exact hold h₁ h₂

theorem Mach.now_upd {m : Net S} {th : Nat → TState S} {t : Nat} {s : TState S} {i : Id}
    {γ : S} : (Mach.now ⟨m, upd th t s⟩).agent i γ ↔
      m.agent i γ ∨ s.held i γ ∨ ∃ u, u ≠ t ∧ (th u).held i γ :=
  or_congr Iff.rfl (ex_upd (P := fun s => s.held i γ))

theorem Mach.now_split (M : Mach S) (t : Nat) {i : Id} {γ : S} :
    M.now.agent i γ ↔
      M.mem.agent i γ ∨ (M.th t).held i γ ∨ ∃ u, u ≠ t ∧ (M.th u).held i γ :=
  or_congr Iff.rfl (ex_split t (P := fun s => s.held i γ))

theorem Mach.goal_agent_upd {m : Net S} {th : Nat → TState S} {t : Nat} {s : TState S}
    {i : Id} {γ : S} : (Mach.goal ⟨m, upd th t s⟩).agent i γ ↔
      (Mach.now ⟨m, upd th t s⟩).agent i γ ∨ s.pendA i γ ∨ ∃ u, u ≠ t ∧ (th u).pendA i γ :=
  or_congr Iff.rfl (ex_upd (P := fun s => s.pendA i γ))

theorem Mach.goal_agent_split (M : Mach S) (t : Nat) {i : Id} {γ : S} :
    M.goal.agent i γ ↔
      M.now.agent i γ ∨ (M.th t).pendA i γ ∨ ∃ u, u ≠ t ∧ (M.th u).pendA i γ :=
  or_congr Iff.rfl (ex_split t (P := fun s => s.pendA i γ))

theorem Mach.goal_link_upd {m : Net S} {th : Nat → TState S} {t : Nat} {s : TState S}
    {p q : Port} : (Mach.goal ⟨m, upd th t s⟩).link p q ↔
      m.link p q ∨ s.pendL p q ∨ ∃ u, u ≠ t ∧ (th u).pendL p q :=
  or_congr Iff.rfl (ex_upd (P := fun s => s.pendL p q))

theorem Mach.goal_link_split (M : Mach S) (t : Nat) {p q : Port} :
    M.goal.link p q ↔
      M.mem.link p q ∨ (M.th t).pendL p q ∨ ∃ u, u ≠ t ∧ (M.th u).pendL p q :=
  or_congr Iff.rfl (ex_split t (P := fun s => s.pendL p q))

/-! ### The invariant -/

/-- What a thread knows stays true of the memory: the segments it has read
are there, and the agent it has taken is not. -/
def TState.Ok (m : Net S) : TState S → Prop
  | .seek a _ p c => ∃ v, Walk m.link (fun _ => False) (a, 0) v p c
  | .ready a b _ _ => Conn m.link (fun _ => False) (a, 0) (b, 0)
  | .half a b _ _ => Conn m.link (fun _ => False) (a, 0) (b, 0) ∧ ∀ δ, ¬ m.agent a δ
  | .write as _ => (as.map Prod.fst).Nodup
  | _ => True

theorem TState.Ok.mono {m m' : Net S} {s : TState S} (h : s.Ok m)
    (hl : ∀ {p q}, m.link p q → m'.link p q)
    (ha : ∀ {i γ δ}, s.held i γ → ¬ m.agent i δ → ¬ m'.agent i δ) : s.Ok m' := by
  cases s with
  | idle => exact h
  | look a α => exact h
  | seek a α p c =>
    obtain ⟨v, w⟩ := h
    exact ⟨v, w.mono hl (fun _ hn => hn)⟩
  | ready a b α β =>
    obtain ⟨v, x, w⟩ := h
    exact ⟨v, x, w.mono hl (fun _ hn => hn)⟩
  | half a b α β =>
    obtain ⟨⟨v, x, w⟩, hn⟩ := h
    exact ⟨⟨v, x, w.mono hl (fun _ hn => hn)⟩, fun δ => ha ⟨rfl, rfl⟩ (hn δ)⟩
  | write as ls => exact h

theorem TState.Ok.not_mem {m : Net S} {s : TState S} (h : s.Ok m) {i : Id} {γ : S}
    (hh : s.held i γ) (δ : S) : ¬ m.agent i δ := by
  cases s with
  | half a b α β =>
    obtain ⟨rfl, rfl⟩ := hh
    exact h.2 δ
  | idle => exact False.elim hh
  | look a α => exact False.elim hh
  | seek a α p c => exact False.elim hh
  | ready a b α β => exact False.elim hh
  | write as ls => exact False.elim hh

theorem ok_upd {m : Net S} {th : Nat → TState S} {t : Nat} {s : TState S} (hs : s.Ok m)
    (ho : ∀ u, u ≠ t → (th u).Ok m) (u : Nat) : (upd th t s u).Ok m := by
  by_cases hu : u = t
  · rw [hu, upd_same]
    exact hs
  · rw [upd_ne _ _ hu]
    exact ho u hu

/-- The invariant of the machine. -/
structure Mach.Inv (sys : System S) (M : Mach S) : Prop where
  /-- The goal is a well-formed net. -/
  wf : M.goal.WF sys.ar
  ok : ∀ t, (M.th t).Ok M.mem
  /-- An agent is taken by one thread at most. -/
  held_unique : ∀ {t t' i γ γ'}, (M.th t).held i γ → (M.th t').held i γ' → t = t'
  /-- An agent that is still to be written is not there yet. -/
  pend_fresh : ∀ {t i γ} (δ : S), (M.th t).pendA i γ → ¬ M.now.agent i δ
  /-- An agent is to be written by one thread at most. -/
  pend_unique : ∀ {t t' i γ γ'}, (M.th t).pendA i γ → (M.th t').pendA i γ' → t = t'

variable {M M' : Mach S} {a b : Id} {α β : S} {R : Rhs S}

theorem Mach.Inv.sound (h : M.Inv sys) : M.abs.Sound sys.ar :=
  ⟨h.wf, fun hi => .inl hi, fun hl => .inl hl, rfl⟩

theorem Mach.Inv.ok_of (h : M.Inv sys) {t : Nat} {s : TState S} (e : M.th t = s) :
    s.Ok M.mem :=
  e ▸ h.ok t

/-- The thread holds nothing and has nothing left to write. -/
def TState.Bare (s : TState S) : Prop :=
  (∀ i γ, ¬ s.held i γ) ∧ (∀ i γ, ¬ s.pendA i γ) ∧ ∀ p q, ¬ s.pendL p q

theorem TState.bare_idle : (TState.idle : TState S).Bare :=
  ⟨fun _ _ x => x, fun _ _ x => x, fun _ _ x => x⟩

theorem TState.bare_done : (TState.write [] [] : TState S).Bare :=
  ⟨fun _ _ x => x, fun _ _ x => List.not_mem_nil x, fun _ _ x => List.not_mem_nil x⟩

theorem TState.Passive.bare {s : TState S} (h : s.Passive) : s.Bare := by
  cases s with
  | idle => exact False.elim h
  | look a α => exact ⟨fun _ _ x => x, fun _ _ x => x, fun _ _ x => x⟩
  | seek a α p c => exact ⟨fun _ _ x => x, fun _ _ x => x, fun _ _ x => x⟩
  | ready a b α β => exact ⟨fun _ _ x => x, fun _ _ x => x, fun _ _ x => x⟩
  | half a b α β => exact False.elim h
  | write as ls => exact False.elim h

/-- A thread that holds nothing and owes nothing, before and after, has
changed nothing that `Conc` sees. -/
theorem Mach.Inv.calm (h : M.Inv sys) {t : Nat} {s : TState S} (h₀ : (M.th t).Bare)
    (h₁ : s.Bare) (hok : s.Ok M.mem) :
    Mach.Inv sys ⟨M.mem, upd M.th t s⟩ ∧
      Run sys 0 M.abs (Mach.abs ⟨M.mem, upd M.th t s⟩) := by
  have hh : ∀ i γ, s.held i γ ↔ (M.th t).held i γ := fun i γ =>
    ⟨fun x => absurd x (h₁.1 i γ), fun x => absurd x (h₀.1 i γ)⟩
  have ha : ∀ i γ, s.pendA i γ ↔ (M.th t).pendA i γ := fun i γ =>
    ⟨fun x => absurd x (h₁.2.1 i γ), fun x => absurd x (h₀.2.1 i γ)⟩
  have hl : ∀ p q, s.pendL p q ↔ (M.th t).pendL p q := fun p q =>
    ⟨fun x => absurd x (h₁.2.2 p q), fun x => absurd x (h₀.2.2 p q)⟩
  have en : Mach.now ⟨M.mem, upd M.th t s⟩ = M.now := by
    apply Net.ext'
    · intro i γ
      rw [Mach.now_upd, Mach.now_split M t, hh]
    · exact fun _ _ => Iff.rfl
    · exact fun _ => Iff.rfl
  have eg : Mach.goal ⟨M.mem, upd M.th t s⟩ = M.goal := by
    apply Net.ext'
    · intro i γ
      rw [Mach.goal_agent_upd, en, Mach.goal_agent_split M t, ha]
    · intro p q
      rw [Mach.goal_link_upd, Mach.goal_link_split M t, hl]
    · exact fun _ => Iff.rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (Mach.goal ⟨M.mem, upd M.th t s⟩).WF sys.ar
    rw [eg]
    exact h.wf
  · exact ok_upd hok fun u _ => h.ok u
  · intro u u' i γ γ' x y
    exact h.held_unique (upd_imp (P := fun s => s.held i γ) (hh i γ).1 x)
      (upd_imp (P := fun s => s.held i γ') (hh i γ').1 y)
  · intro u i γ δ x
    show ¬ (Mach.now ⟨M.mem, upd M.th t s⟩).agent i δ
    rw [en]
    exact h.pend_fresh δ (upd_imp (P := fun s => s.pendA i γ) (ha i γ).1 x)
  · intro u u' i γ γ' x y
    exact h.pend_unique (upd_imp (P := fun s => s.pendA i γ) (ha i γ).1 x)
      (upd_imp (P := fun s => s.pendA i γ') (ha i γ').1 y)
  · show Run sys 0 M.abs ⟨Mach.now ⟨M.mem, upd M.th t s⟩, Mach.goal ⟨M.mem, upd M.th t s⟩⟩
    rw [en, eg]
    exact .refl _

/-- The thread owes nothing. -/
def TState.NoPend (s : TState S) : Prop :=
  (∀ i γ, ¬ s.pendA i γ) ∧ ∀ p q, ¬ s.pendL p q

theorem Mach.goal_of_now {m : Net S} {t : Nat} {s : TState S}
    (hn : Mach.now ⟨m, upd M.th t s⟩ = M.now) (hl : ∀ p q, m.link p q ↔ M.mem.link p q)
    (hf : ∀ p, m.free p ↔ M.mem.free p) (h₀ : (M.th t).NoPend) (h₁ : s.NoPend) :
    Mach.goal ⟨m, upd M.th t s⟩ = M.goal := by
  have ha : ∀ i γ, s.pendA i γ ↔ (M.th t).pendA i γ := fun i γ =>
    ⟨fun x => absurd x (h₁.1 i γ), fun x => absurd x (h₀.1 i γ)⟩
  have hp : ∀ p q, s.pendL p q ↔ (M.th t).pendL p q := fun p q =>
    ⟨fun x => absurd x (h₁.2 p q), fun x => absurd x (h₀.2 p q)⟩
  apply Net.ext'
  · intro i γ
    rw [Mach.goal_agent_upd, hn, Mach.goal_agent_split M t, ha]
  · intro p q
    rw [Mach.goal_link_upd, Mach.goal_link_split M t, hl, hp]
  · exact hf

/-- **The machine refines `Conc`**: an action of the machine keeps the
invariant, and is an action of `Conc` on the state it stands for, or leaves
that state unchanged. -/
theorem MStep.sim {c : Nat} (h : M.Inv sys) (hs : MStep sys c M M') :
    M'.Inv sys ∧ Run sys c M.abs M'.abs := by
  cases hs with
  | @look _ t a α e hm =>
    exact h.calm (by rw [e]; exact TState.bare_idle) (TState.Passive.bare trivial) trivial
  | @first _ t a α q e hl =>
    exact h.calm (by rw [e]; exact TState.Passive.bare trivial) (TState.Passive.bare trivial)
      ⟨q, .single hl⟩
  | @next _ t a α p c' q e hl hq =>
    obtain ⟨v, w⟩ := h.ok_of e
    exact h.calm (by rw [e]; exact TState.Passive.bare trivial) (TState.Passive.bare trivial)
      ⟨v, w.snoc (fun x => x) hl hq⟩
  | @found _ t a b α β p e hm =>
    obtain ⟨v, w⟩ := h.ok_of e
    exact h.calm (by rw [e]; exact TState.Passive.bare trivial) (TState.Passive.bare trivial)
      ⟨v, p, w⟩
  | @quit _ t hp =>
    exact h.calm (TState.Passive.bare hp) TState.bare_idle trivial
  | @done _ t e =>
    exact h.calm (by rw [e]; exact TState.bare_done) TState.bare_idle trivial
  | @cas₁ _ t a b α β e hm =>
    have hfun : ∀ {δ}, M.mem.agent a δ → δ = α := fun hd =>
      h.wf.agent_fun (.inl (.inl hd)) (.inl (.inl hm))
    have hnow : Mach.now ⟨M.mem.take a, upd M.th t (.half a b α β)⟩ = M.now := by
      apply Net.ext'
      · intro i γ
        rw [Mach.now_upd, Mach.now_split M t, e]
        constructor
        · rintro (⟨hi, -⟩ | ⟨rfl, rfl⟩ | ho)
          · exact .inl hi
          · exact .inl hm
          · exact .inr (.inr ho)
        · rintro (hi | hf | ho)
          · by_cases hia : i = a
            · rw [hia] at hi
              exact .inr (.inl ⟨hia, hfun hi⟩)
            · exact .inl ⟨hi, hia⟩
          · exact False.elim hf
          · exact .inr (.inr ho)
      · exact fun _ _ => Iff.rfl
      · exact fun _ => Iff.rfl
    have hgoal : Mach.goal ⟨M.mem.take a, upd M.th t (.half a b α β)⟩ = M.goal :=
      Mach.goal_of_now hnow (fun _ _ => Iff.rfl) (fun _ => Iff.rfl)
        (by rw [e]; exact ⟨fun _ _ x => x, fun _ _ x => x⟩) ⟨fun _ _ x => x, fun _ _ x => x⟩
    have hnp : ∀ i γ, (TState.half a b α β).pendA i γ → (M.th t).pendA i γ :=
      fun _ _ x => False.elim x
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show (Mach.goal ⟨M.mem.take a, upd M.th t (.half a b α β)⟩).WF sys.ar
      rw [hgoal]
      exact h.wf
    · exact ok_upd ⟨h.ok_of e, fun δ hd => hd.2 rfl⟩ fun u _ =>
        (h.ok u).mono (fun hl => hl) (fun _ hn hd => hn hd.1)
    · intro u u' i γ γ' x y
      refine unique_upd (P := TState.held) h.held_unique ?_ x y
      rintro u i γ γ' - ⟨rfl, rfl⟩ hu
      exact (h.ok u).not_mem hu _ hm
    · intro u i γ δ x
      show ¬ (Mach.now ⟨M.mem.take a, upd M.th t (.half a b α β)⟩).agent i δ
      rw [hnow]
      exact h.pend_fresh δ (upd_imp (P := fun s => s.pendA i γ) (hnp i γ) x)
    · intro u u' i γ γ' x y
      exact h.pend_unique (upd_imp (P := fun s => s.pendA i γ) (hnp i γ) x)
        (upd_imp (P := fun s => s.pendA i γ') (hnp i γ') y)
    · show Run sys 0 M.abs ⟨Mach.now ⟨M.mem.take a, upd M.th t (.half a b α β)⟩,
        Mach.goal ⟨M.mem.take a, upd M.th t (.half a b α β)⟩⟩
      rw [hnow, hgoal]
      exact .refl _
  | @undo _ t a b α β e =>
    have hheld : (M.th t).held a α := by
      rw [e]
      exact ⟨rfl, rfl⟩
    have hnow : Mach.now ⟨M.mem.addAgent a α, upd M.th t .idle⟩ = M.now := by
      apply Net.ext'
      · intro i γ
        rw [Mach.now_upd, Mach.now_split M t, e]
        constructor
        · rintro ((hi | hx) | hf | ho)
          · exact .inl hi
          · exact .inr (.inl hx)
          · exact False.elim hf
          · exact .inr (.inr ho)
        · rintro (hi | hx | ho)
          · exact .inl (.inl hi)
          · exact .inl (.inr hx)
          · exact .inr (.inr ho)
      · exact fun _ _ => Iff.rfl
      · exact fun _ => Iff.rfl
    have hgoal : Mach.goal ⟨M.mem.addAgent a α, upd M.th t .idle⟩ = M.goal :=
      Mach.goal_of_now hnow (fun _ _ => Iff.rfl) (fun _ => Iff.rfl)
        (by rw [e]; exact ⟨fun _ _ x => x, fun _ _ x => x⟩) ⟨fun _ _ x => x, fun _ _ x => x⟩
    have hnh : ∀ i γ, (TState.idle : TState S).held i γ → (M.th t).held i γ :=
      fun _ _ x => False.elim x
    have hnp : ∀ i γ, (TState.idle : TState S).pendA i γ → (M.th t).pendA i γ :=
      fun _ _ x => False.elim x
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show (Mach.goal ⟨M.mem.addAgent a α, upd M.th t .idle⟩).WF sys.ar
      rw [hgoal]
      exact h.wf
    · refine ok_upd trivial fun u hu => (h.ok u).mono (fun hl => hl) ?_
      rintro i γ δ hh hn (hd | ⟨rfl, -⟩)
      · exact hn hd
      · exact hu (h.held_unique hh hheld)
    · intro u u' i γ γ' x y
      exact h.held_unique (upd_imp (P := fun s => s.held i γ) (hnh i γ) x)
        (upd_imp (P := fun s => s.held i γ') (hnh i γ') y)
    · intro u i γ δ x
      show ¬ (Mach.now ⟨M.mem.addAgent a α, upd M.th t .idle⟩).agent i δ
      rw [hnow]
      exact h.pend_fresh δ (upd_imp (P := fun s => s.pendA i γ) (hnp i γ) x)
    · intro u u' i γ γ' x y
      exact h.pend_unique (upd_imp (P := fun s => s.pendA i γ) (hnp i γ) x)
        (upd_imp (P := fun s => s.pendA i γ') (hnp i γ') y)
    · show Run sys 0 M.abs ⟨Mach.now ⟨M.mem.addAgent a α, upd M.th t .idle⟩,
        Mach.goal ⟨M.mem.addAgent a α, upd M.th t .idle⟩⟩
      rw [hnow, hgoal]
      exact .refl _
  | @cas₂ _ t a b α β R as ls e hm hne hr hw =>
    obtain ⟨⟨v, x, w⟩, hna⟩ := h.ok_of e
    have hheld : (M.th t).held a α := by
      rw [e]
      exact ⟨rfl, rfl⟩
    have ha : M.now.agent a α := .inr ⟨t, hheld⟩
    have hb : M.now.agent b β := .inl hm
    have r : Redex sys M.now a b α β R :=
      ⟨ha, hb, hne, ⟨v, x, w.mono_term (fun hl => hl) (fun hl => .inl hl) h.wf.symm
        (fun hT => h.sound.end_goal hT) h.wf.end_unique⟩, hr⟩
    have rg := h.sound.redex r
    have site : Site sys.ar M.goal a b α β := ⟨h.wf, rg.ha, rg.hb, rg.ne, rg.conn⟩
    have hnow : Mach.now ⟨M.mem.take b, upd M.th t (.write as ls)⟩ = M.now.claim a b := by
      apply Net.ext'
      · intro i γ
        show _ ↔ M.now.agent i γ ∧ i ≠ a ∧ i ≠ b
        rw [Mach.now_upd, Mach.now_split M t, e]
        constructor
        · rintro (⟨hi, hib⟩ | hf | ⟨u, hu, hh⟩)
          · exact ⟨.inl hi, fun hia => hna γ (hia ▸ hi), hib⟩
          · exact False.elim hf
          · refine ⟨.inr (.inr ⟨u, hu, hh⟩), fun hia => ?_, fun hib => ?_⟩
            · rw [hia] at hh
              exact hu (h.held_unique hh hheld)
            · rw [hib] at hh
              exact (h.ok u).not_mem hh β hm
        · rintro ⟨hi | ⟨hia, -⟩ | ho, hia', hib⟩
          · exact .inl ⟨hi, hib⟩
          · exact absurd hia hia'
          · exact .inr (.inr ho)
      · exact fun _ _ => Iff.rfl
      · exact fun _ => Iff.rfl
    have hgoal : Mach.goal ⟨M.mem.take b, upd M.th t (.write as ls)⟩ = M.goal.fire a b R := by
      apply Net.ext'
      · intro i γ
        show _ ↔ (M.goal.agent i γ ∧ i ≠ a ∧ i ≠ b) ∨
          ∃ o j, i = child a b o j ∧ R.lab o j = some γ
        rw [Mach.goal_agent_upd, hnow, Mach.goal_agent_split M t, e]
        constructor
        · rintro (⟨hi, hia, hib⟩ | hp | ⟨u, hu, hp⟩)
          · exact .inl ⟨.inl hi, hia, hib⟩
          · exact .inr (hw.agent.1 hp)
          · refine .inl ⟨.inr (.inr ⟨u, hu, hp⟩), fun hia => ?_, fun hib => ?_⟩
            · rw [hia] at hp
              exact h.pend_fresh α hp ha
            · rw [hib] at hp
              exact h.pend_fresh β hp hb
        · rintro (⟨hi | hf | ho, hia, hib⟩ | hx)
          · exact .inl ⟨hi, hia, hib⟩
          · exact False.elim hf
          · exact .inr (.inr ho)
          · exact .inr (.inl (hw.agent.2 hx))
      · intro p q
        show _ ↔ M.goal.link p q ∨ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y
        rw [Mach.goal_link_upd, Mach.goal_link_split M t, e]
        constructor
        · rintro (hl | hp | ho)
          · exact .inl (.inl hl)
          · exact .inr (hw.link.1 hp)
          · exact .inl (.inr (.inr ho))
        · rintro ((hl | hf | ho) | hx)
          · exact .inl hl
          · exact False.elim hf
          · exact .inr (.inr ho)
          · exact .inr (.inl (hw.link.2 hx))
      · exact fun _ => Iff.rfl
    have hc : Conc sys 1 M.abs ⟨M.now.claim a b, M.goal.fire a b R⟩ := .claim r
    have hs' := (hc.sound h.sound).1
    have hnh : ∀ i γ, (TState.write as ls).held i γ → (M.th t).held i γ :=
      fun _ _ x => False.elim x
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show (Mach.goal ⟨M.mem.take b, upd M.th t (.write as ls)⟩).WF sys.ar
      rw [hgoal]
      exact hs'.wf
    · exact ok_upd hw.nodup fun u _ => (h.ok u).mono (fun hl => hl) (fun _ hn hd => hn hd.1)
    · intro u u' i γ γ' x y
      exact h.held_unique (upd_imp (P := fun s => s.held i γ) (hnh i γ) x)
        (upd_imp (P := fun s => s.held i γ') (hnh i γ') y)
    · intro u i γ δ x
      show ¬ (Mach.now ⟨M.mem.take b, upd M.th t (.write as ls)⟩).agent i δ
      rw [hnow]
      rintro ⟨hi, -, -⟩
      by_cases hu : u = t
      · rw [hu] at x
        have x' : (upd M.th t (.write as ls) t).pendA i γ := x
        rw [upd_same] at x'
        obtain ⟨o, j, rfl, -⟩ := hw.agent.1 x'
        exact site.not_used_child o j (.inl ⟨δ, .inl hi⟩)
      · have x' : (upd M.th t (.write as ls) u).pendA i γ := x
        rw [upd_ne _ _ hu] at x'
        exact h.pend_fresh δ x' hi
    · intro u u' i γ γ' x y
      refine unique_upd (P := TState.pendA) h.pend_unique ?_ x y
      intro u i γ γ' _ hp hp'
      obtain ⟨o, j, rfl, -⟩ := hw.agent.1 hp
      exact site.not_used_child o j (.inl ⟨γ', .inr ⟨u, hp'⟩⟩)
    · show Run sys 1 M.abs ⟨Mach.now ⟨M.mem.take b, upd M.th t (.write as ls)⟩,
        Mach.goal ⟨M.mem.take b, upd M.th t (.write as ls)⟩⟩
      rw [hnow, hgoal]
      exact .step hc (.refl _)
  | @agent _ t i γ as ls e =>
    have hpend : (M.th t).pendA i γ := by
      rw [e]
      exact List.mem_cons_self
    have hfresh : ∀ δ, ¬ M.now.agent i δ := fun δ => h.pend_fresh δ hpend
    have hnd : (i :: as.map Prod.fst).Nodup := h.ok_of e
    obtain ⟨hni, hnd'⟩ := List.nodup_cons.1 hnd
    have hsub : ∀ j δ, (TState.write as ls).pendA j δ → (M.th t).pendA j δ := by
      intro j δ x
      rw [e]
      exact List.mem_cons_of_mem _ x
    have hnh : ∀ j δ, (TState.write as ls).held j δ → (M.th t).held j δ :=
      fun _ _ x => False.elim x
    have hnow : Mach.now ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩ =
        M.now.addAgent i γ := by
      apply Net.ext'
      · intro j δ
        show _ ↔ M.now.agent j δ ∨ (j = i ∧ δ = γ)
        rw [Mach.now_upd, Mach.now_split M t, e]
        constructor
        · rintro ((hj | hx) | hf | ho)
          · exact .inl (.inl hj)
          · exact .inr hx
          · exact False.elim hf
          · exact .inl (.inr (.inr ho))
        · rintro ((hj | hf | ho) | hx)
          · exact .inl (.inl hj)
          · exact False.elim hf
          · exact .inr (.inr ho)
          · exact .inl (.inr hx)
      · exact fun _ _ => Iff.rfl
      · exact fun _ => Iff.rfl
    have hgoal : Mach.goal ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩ = M.goal := by
      apply Net.ext'
      · intro j δ
        rw [Mach.goal_agent_upd, hnow, Mach.goal_agent_split M t, e]
        constructor
        · rintro ((hj | ⟨rfl, rfl⟩) | hp | ho)
          · exact .inl hj
          · exact .inr (.inl List.mem_cons_self)
          · exact .inr (.inl (List.mem_cons_of_mem _ hp))
          · exact .inr (.inr ho)
        · rintro (hj | hp | ho)
          · exact .inl (.inl hj)
          · rcases List.mem_cons.1 hp with he | hp
            · exact .inl (.inr ⟨(Prod.mk.inj he).1, (Prod.mk.inj he).2⟩)
            · exact .inr (.inl hp)
          · exact .inr (.inr ho)
      · intro p q
        rw [Mach.goal_link_upd, Mach.goal_link_split M t, e]
        exact Iff.rfl
      · exact fun _ => Iff.rfl
    have hc : Conc sys 0 M.abs ⟨M.now.addAgent i γ, M.goal⟩ :=
      .agent (st := M.abs) (.inr ⟨t, hpend⟩) (hfresh γ)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show (Mach.goal ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩).WF sys.ar
      rw [hgoal]
      exact h.wf
    · refine ok_upd hnd' fun u _ => (h.ok u).mono (fun hl => hl) ?_
      rintro j γ' δ hh hn (hd | ⟨rfl, -⟩)
      · exact hn hd
      · exact hfresh γ' (.inr ⟨u, hh⟩)
    · intro u u' j δ δ' x y
      exact h.held_unique (upd_imp (P := fun s => s.held j δ) (hnh j δ) x)
        (upd_imp (P := fun s => s.held j δ') (hnh j δ') y)
    · intro u j δ δ' x
      show ¬ (Mach.now ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩).agent j δ'
      rw [hnow]
      rintro (hj | ⟨rfl, -⟩)
      · exact h.pend_fresh δ' (upd_imp (P := fun s => s.pendA j δ) (hsub j δ) x) hj
      · by_cases hu : u = t
        · rw [hu] at x
          have x' : (upd M.th t (.write as ls) t).pendA j δ := x
          rw [upd_same] at x'
          exact hni (List.mem_map.2 ⟨(j, δ), x', rfl⟩)
        · have x' : (upd M.th t (.write as ls) u).pendA j δ := x
          rw [upd_ne _ _ hu] at x'
          exact hu (h.pend_unique x' hpend)
    · intro u u' j δ δ' x y
      exact h.pend_unique (upd_imp (P := fun s => s.pendA j δ) (hsub j δ) x)
        (upd_imp (P := fun s => s.pendA j δ') (hsub j δ') y)
    · show Run sys 0 M.abs ⟨Mach.now ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩,
        Mach.goal ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩⟩
      rw [hnow, hgoal]
      exact .step hc (.refl _)
  | @link _ t p q as ls e =>
    have hpend : (M.th t).pendL p q := by
      rw [e]
      exact List.mem_cons_self
    have hnd : (as.map Prod.fst).Nodup := h.ok_of e
    have hsub : ∀ j δ, (TState.write as ls).pendA j δ → (M.th t).pendA j δ := by
      intro j δ x
      rw [e]
      exact x
    have hnh : ∀ j δ, (TState.write as ls).held j δ → (M.th t).held j δ :=
      fun _ _ x => False.elim x
    have hnow : Mach.now ⟨M.mem.addLink p q, upd M.th t (.write as ls)⟩ =
        M.now.addLink p q := by
      apply Net.ext'
      · intro j δ
        show _ ↔ M.now.agent j δ
        rw [Mach.now_upd, Mach.now_split M t, e]
        exact Iff.rfl
      · exact fun _ _ => Iff.rfl
      · exact fun _ => Iff.rfl
    have hgoal : Mach.goal ⟨M.mem.addLink p q, upd M.th t (.write as ls)⟩ = M.goal := by
      apply Net.ext'
      · intro j δ
        rw [Mach.goal_agent_upd, hnow, Mach.goal_agent_split M t, e]
        exact Iff.rfl
      · intro x y
        rw [Mach.goal_link_upd, Mach.goal_link_split M t, e]
        constructor
        · rintro ((hl | ⟨rfl, rfl⟩) | hp | ho)
          · exact .inl hl
          · exact .inr (.inl List.mem_cons_self)
          · exact .inr (.inl (List.mem_cons_of_mem _ hp))
          · exact .inr (.inr ho)
        · rintro (hl | hp | ho)
          · exact .inl (.inl hl)
          · rcases List.mem_cons.1 hp with he | hp
            · exact .inl (.inr ⟨(Prod.mk.inj he).1, (Prod.mk.inj he).2⟩)
            · exact .inr (.inl hp)
          · exact .inr (.inr ho)
      · exact fun _ => Iff.rfl
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show (Mach.goal ⟨M.mem.addLink p q, upd M.th t (.write as ls)⟩).WF sys.ar
      rw [hgoal]
      exact h.wf
    · exact ok_upd hnd fun u _ => (h.ok u).mono (fun hl => .inl hl) (fun _ hn hd => hn hd)
    · intro u u' j δ δ' x y
      exact h.held_unique (upd_imp (P := fun s => s.held j δ) (hnh j δ) x)
        (upd_imp (P := fun s => s.held j δ') (hnh j δ') y)
    · intro u j δ δ' x
      show ¬ (Mach.now ⟨M.mem.addLink p q, upd M.th t (.write as ls)⟩).agent j δ'
      rw [hnow]
      exact h.pend_fresh δ' (upd_imp (P := fun s => s.pendA j δ) (hsub j δ) x)
    · intro u u' j δ δ' x y
      exact h.pend_unique (upd_imp (P := fun s => s.pendA j δ) (hsub j δ) x)
        (upd_imp (P := fun s => s.pendA j δ') (hsub j δ') y)
    · show Run sys 0 M.abs ⟨Mach.now ⟨M.mem.addLink p q, upd M.th t (.write as ls)⟩,
        Mach.goal ⟨M.mem.addLink p q, upd M.th t (.write as ls)⟩⟩
      rw [hnow, hgoal]
      by_cases hc : M.now.link p q
      · have e' : M.now.addLink p q = M.now := by
          apply Net.ext'
          · exact fun _ _ => Iff.rfl
          · intro x y
            constructor
            · rintro (hl | ⟨rfl, rfl⟩)
              · exact hl
              · exact hc
            · exact fun hl => .inl hl
          · exact fun _ => Iff.rfl
        rw [e']
        exact .refl _
      · exact .step (.link (st := M.abs) (.inr ⟨t, hpend⟩) hc) (.refl _)

theorem MRun.sim {k : Nat} (h : M.Inv sys) (hr : MRun sys k M M') :
    M'.Inv sys ∧ Run sys k M.abs M'.abs := by
  induction hr with
  | refl M => exact ⟨h, .refl _⟩
  | step hs _ ih =>
    obtain ⟨h₁, r₁⟩ := hs.sim h
    obtain ⟨h₂, r₂⟩ := ih h₁
    exact ⟨h₂, r₁.trans r₂⟩

/-! ### Every schedule computes the normal form -/

/-- The machine before it starts: the net in memory, and every thread
idle. -/
def Mach.init (N : Net S) : Mach S := ⟨N, fun _ => .idle⟩

/-- Every thread is idle. -/
def Mach.Quiet (M : Mach S) : Prop := ∀ t, M.th t = .idle

/-- When every thread is idle, `Conc` sees the memory and nothing else. -/
theorem Mach.Quiet.abs (hq : M.Quiet) : M.abs = ⟨M.mem, M.mem⟩ := by
  have en : M.now = M.mem := by
    apply Net.ext'
    · intro i γ
      constructor
      · rintro (hi | ⟨t, ht⟩)
        · exact hi
        · rw [hq t] at ht
          exact False.elim ht
      · exact fun hi => .inl hi
    · exact fun _ _ => Iff.rfl
    · exact fun _ => Iff.rfl
  have eg : M.goal = M.mem := by
    apply Net.ext'
    · intro i γ
      constructor
      · rintro ((hi | ⟨t, ht⟩) | ⟨t, ht⟩)
        · exact hi
        · rw [hq t] at ht
          exact False.elim ht
        · rw [hq t] at ht
          exact False.elim ht
      · exact fun hi => .inl (.inl hi)
    · intro p q
      constructor
      · rintro (hl | ⟨t, ht⟩)
        · exact hl
        · rw [hq t] at ht
          exact False.elim ht
      · exact fun hl => .inl hl
    · exact fun _ => Iff.rfl
  show (⟨M.now, M.goal⟩ : CState S) = _
  rw [en, eg]

theorem Mach.init_quiet (N : Net S) : (Mach.init N).Quiet := fun _ => rfl

theorem Mach.init_inv (hN : N.WF sys.ar) : (Mach.init N).Inv sys where
  wf := by
    have e : (Mach.init N).goal = N := congrArg CState.goal (Mach.init_quiet N).abs
    rw [e]
    exact hN
  ok := fun _ => trivial
  held_unique := fun x _ => False.elim x
  pend_fresh := fun _ x => False.elim x
  pend_unique := fun x _ => False.elim x

/-- An execution of the machine from a well-formed net is an execution of
`Conc`, with the same number of claims. -/
theorem MRun.run {k : Nat} (hN : N.WF sys.ar) (hr : MRun sys k (Mach.init N) M) :
    M.Inv sys ∧ Run sys k ⟨N, N⟩ M.abs := by
  have h := hr.sim (Mach.init_inv hN)
  rw [(Mach.init_quiet N).abs] at h
  exact h

/-- **Every execution of the machine is a sequential reduction**, with one
step for each claim, of the net it started from to the net that memory will
hold once the threads have written what they have left to write. -/
theorem MRun.sequential {k : Nat} (hN : N.WF sys.ar) (hr : MRun sys k (Mach.init N) M) :
    Steps (Step sys) k N M.goal :=
  (hr.run hN).2.sequential hN

/-- When every thread is idle, the memory is the net reached by that
reduction. -/
theorem MRun.quiet {k : Nat} (hN : N.WF sys.ar) (hr : MRun sys k (Mach.init N) M)
    (hq : M.Quiet) : Steps (Step sys) k N M.mem := by
  have h := hr.sequential hN
  have e : M.goal = M.mem := congrArg CState.goal hq.abs
  rw [e] at h
  exact h

/-- **Whatever the schedule, the machine computes the normal form.**  If
every thread is idle and the memory holds no active pair, then the memory is
the normal form of the net the machine started from, the number of claims is
the length of every reduction to it, and no sequential reduction is longer
or ends at another normal form. -/
theorem MRun.final {k : Nat} (hN : N.WF sys.ar) (hr : MRun sys k (Mach.init N) M)
    (hq : M.Quiet) (hn : Normal (Step sys) M.mem) :
    Steps (Step sys) k N M.mem ∧ ∀ {m : Nat} {N' : Net S}, Steps (Step sys) m N N' →
      m ≤ k ∧ (Normal (Step sys) N' → N' = M.mem ∧ m = k) := by
  have sts := hr.quiet hN hq
  exact ⟨sts, fun h' => ⟨(reduction_bounded hN sts hn h').1,
    fun hn' => normal_form_unique hN h' sts hn' hn⟩⟩

/-- Two executions of the machine on the same net, with any schedules and
any numbers of threads, end with the same memory and the same number of
claims. -/
theorem MRun.confluent {k k' : Nat} {M₁ M₂ : Mach S} (hN : N.WF sys.ar)
    (h₁ : MRun sys k (Mach.init N) M₁) (h₂ : MRun sys k' (Mach.init N) M₂)
    (q₁ : M₁.Quiet) (q₂ : M₂.Quiet) (n₁ : Normal (Step sys) M₁.mem)
    (n₂ : Normal (Step sys) M₂.mem) : M₁.mem = M₂.mem ∧ k = k' :=
  normal_form_unique hN (h₁.quiet hN q₁) (h₂.quiet hN q₂) n₁ n₂

/-- No execution of the machine makes more claims than the sequential
reduction has steps. -/
theorem MRun.claims_le {n k : Nat} {N' : Net S} (hN : N.WF sys.ar)
    (hs : Steps (Step sys) n N N') (hn : Normal (Step sys) N')
    (hr : MRun sys k (Mach.init N) M) : k ≤ n :=
  (reduction_bounded hN hs hn (hr.sequential hN)).1

/-- If an execution of the machine ends with every thread idle after as many
claims as the reduction to normal form has steps, then the memory holds the
normal form. -/
theorem MRun.quiet_eq {n : Nat} {N' : Net S} (hN : N.WF sys.ar)
    (hs : Steps (Step sys) n N N') (hn : Normal (Step sys) N')
    (hr : MRun sys n (Mach.init N) M) (hq : M.Quiet) : M.mem = N' := by
  obtain ⟨-, rest⟩ := reduction_bounded hN hs hn (hr.quiet hN hq)
  rw [Nat.sub_self] at rest
  cases rest
  rfl

/-! ### No thread is ever stuck

The theorems above hold for every schedule.  The ones below say that the
machine can always go on: a thread can finish what it has started without
the help of any other thread, and an idle thread can fire any active pair
that is visible in memory, whatever the other threads are in the middle
of. -/

theorem Mach.flush_links {t : Nat} : ∀ (ls : List (Port × Port)) (M : Mach S),
    M.th t = .write [] ls → ∃ M', MRun sys 0 M M' ∧ M'.th t = .idle ∧
      (∀ u, u ≠ t → M'.th u = M.th u) ∧ M'.mem.agent = M.mem.agent ∧
      (∀ p q, M'.mem.link p q ↔ M.mem.link p q ∨ (p, q) ∈ ls) ∧ M'.mem.free = M.mem.free
  | [], M, e =>
    ⟨⟨M.mem, upd M.th t .idle⟩, .step (.done e) (.refl _), upd_same _ _ _,
      fun _ hu => upd_ne _ _ hu, rfl,
      fun _ _ => ⟨fun hl => .inl hl, fun hl => hl.elim id fun x => absurd x List.not_mem_nil⟩,
      rfl⟩
  | (p, q) :: ls, M, e => by
    obtain ⟨M', hr, h₁, h₂, h₃, h₄, h₅⟩ := Mach.flush_links ls
      ⟨M.mem.addLink p q, upd M.th t (.write [] ls)⟩ (upd_same _ _ _)
    refine ⟨M', .step (.link e) hr, h₁, fun u hu => (h₂ u hu).trans (upd_ne _ _ hu), h₃,
      fun x y => ?_, h₅⟩
    rw [h₄]
    constructor
    · rintro ((hl | ⟨rfl, rfl⟩) | hm)
      · exact .inl hl
      · exact .inr List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ hm)
    · rintro (hl | hm)
      · exact .inl (.inl hl)
      · rcases List.mem_cons.1 hm with he | hm
        · exact .inl (.inr ⟨(Prod.mk.inj he).1, (Prod.mk.inj he).2⟩)
        · exact .inr hm

/-- A thread can write everything it has left to write. -/
theorem Mach.flush {t : Nat} (ls : List (Port × Port)) : ∀ (as : List (Id × S)) (M : Mach S),
    M.th t = .write as ls → ∃ M', MRun sys 0 M M' ∧ M'.th t = .idle ∧
      (∀ u, u ≠ t → M'.th u = M.th u) ∧
      (∀ i γ, M'.mem.agent i γ ↔ M.mem.agent i γ ∨ (i, γ) ∈ as) ∧
      (∀ p q, M'.mem.link p q ↔ M.mem.link p q ∨ (p, q) ∈ ls) ∧ M'.mem.free = M.mem.free
  | [], M, e => by
    obtain ⟨M', hr, h₁, h₂, h₃, h₄, h₅⟩ := Mach.flush_links (sys := sys) ls M e
    refine ⟨M', hr, h₁, h₂, fun i γ => ?_, h₄, h₅⟩
    rw [h₃]
    exact ⟨fun hi => .inl hi, fun hi => hi.elim id fun x => absurd x List.not_mem_nil⟩
  | (i, γ) :: as, M, e => by
    obtain ⟨M', hr, h₁, h₂, h₃, h₄, h₅⟩ := Mach.flush ls as
      ⟨M.mem.addAgent i γ, upd M.th t (.write as ls)⟩ (upd_same _ _ _)
    refine ⟨M', .step (.agent e) hr, h₁, fun u hu => (h₂ u hu).trans (upd_ne _ _ hu),
      fun j δ => ?_, h₄, h₅⟩
    rw [h₃]
    constructor
    · rintro ((hj | ⟨rfl, rfl⟩) | hm)
      · exact .inl hj
      · exact .inr List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ hm)
    · rintro (hj | hm)
      · exact .inl (.inl hj)
      · rcases List.mem_cons.1 hm with he | hm
        · exact .inl (.inr ⟨(Prod.mk.inj he).1, (Prod.mk.inj he).2⟩)
        · exact .inr hm

/-- **A thread can always finish alone**: from any state of the machine, a
thread reaches its idle state by its own actions, without a claim and
without any other thread moving. -/
theorem Mach.settle (sys : System S) (M : Mach S) (t : Nat) :
    ∃ M', MRun sys 0 M M' ∧ M'.th t = .idle ∧ ∀ u, u ≠ t → M'.th u = M.th u := by
  cases hs : M.th t with
  | idle => exact ⟨M, .refl _, hs, fun _ _ => rfl⟩
  | look a α =>
    exact ⟨⟨M.mem, upd M.th t .idle⟩, .step (.quit (t := t) (by rw [hs]; trivial)) (.refl _),
      upd_same _ _ _, fun _ hu => upd_ne _ _ hu⟩
  | seek a α p c =>
    exact ⟨⟨M.mem, upd M.th t .idle⟩, .step (.quit (t := t) (by rw [hs]; trivial)) (.refl _),
      upd_same _ _ _, fun _ hu => upd_ne _ _ hu⟩
  | ready a b α β =>
    exact ⟨⟨M.mem, upd M.th t .idle⟩, .step (.quit (t := t) (by rw [hs]; trivial)) (.refl _),
      upd_same _ _ _, fun _ hu => upd_ne _ _ hu⟩
  | half a b α β =>
    exact ⟨⟨M.mem.addAgent a α, upd M.th t .idle⟩, .step (.undo hs) (.refl _),
      upd_same _ _ _, fun _ hu => upd_ne _ _ hu⟩
  | write as ls =>
    obtain ⟨M', hr, h₁, h₂, -⟩ := Mach.flush (sys := sys) ls as M hs
    exact ⟨M', hr, h₁, h₂⟩

/-- A thread can follow a wire to its end, one segment at a time. -/
theorem Mach.follow {m : Net S} {T : Port → Prop} {t : Nat} {a : Id} {α : S}
    {u v x y : Port} (w : Walk m.link T u v x y) :
    ∀ (th : Nat → TState S) (p : Port), th t = .seek a α p u → v ≠ p →
      ∃ th', MRun sys 0 ⟨m, th⟩ ⟨m, th'⟩ ∧ th' t = .seek a α x y ∧
        ∀ u', u' ≠ t → th' u' = th u' := by
  induction w with
  | single hl =>
    intro th p e hv
    exact ⟨_, .step (.next (M := ⟨m, th⟩) e hl hv) (.refl _), upd_same _ _ _,
      fun _ hu => upd_ne _ _ hu⟩
  | cons hl _ hne _ ih =>
    intro th p e hv
    obtain ⟨th', hr, h₁, h₂⟩ := ih (upd th t (.seek a α _ _)) _ (upd_same _ _ _) hne
    exact ⟨th', .step (.next (M := ⟨m, th⟩) e hl hv) hr, h₁,
      fun u' hu => (h₂ u' hu).trans (upd_ne _ _ hu)⟩

theorem Mach.reach {m : Net S} {T : Port → Prop} {t : Nat} {a : Id} {α : S} {v x y : Port}
    (w : Walk m.link T (a, 0) v x y) (th : Nat → TState S) (e : th t = .look a α) :
    ∃ th', MRun sys 0 ⟨m, th⟩ ⟨m, th'⟩ ∧ th' t = .seek a α x y ∧
      ∀ u', u' ≠ t → th' u' = th u' := by
  cases w with
  | single hl =>
    exact ⟨_, .step (.first (M := ⟨m, th⟩) e hl) (.refl _), upd_same _ _ _,
      fun _ hu => upd_ne _ _ hu⟩
  | cons hl _ hne w' =>
    obtain ⟨th', hr, h₁, h₂⟩ := Mach.follow (sys := sys) w'
      (upd th t (.seek a α (a, 0) _)) _ (upd_same _ _ _) hne
    exact ⟨th', .step (.first (M := ⟨m, th⟩) e hl) hr, h₁,
      fun u' hu => (h₂ u' hu).trans (upd_ne _ _ hu)⟩

/-- Distinct new agents get distinct names, as soon as the two fired agents
are distinct. -/
theorem child_inj' {a b : Id} (hne : a ≠ b) {o o' : Option Bool} {j j' : Nat}
    (e : child a b o j = child a b o' j') : o = o' ∧ j = j' := by
  have e' : slot o j :: par a b o = slot o' j' :: par a b o' := e
  obtain ⟨e₁, e₂⟩ := List.cons.inj e'
  cases o with
  | none =>
    cases o' with
    | none => exact ⟨rfl, by simp only [slot] at e₁; omega⟩
    | some s' => simp only [slot] at e₁; omega
  | some s =>
    cases o' with
    | none => simp only [slot] at e₁; omega
    | some s' =>
      have es : s = s' := by
        cases s <;> cases s' <;>
          first | rfl | exact absurd e₂ hne | exact absurd e₂.symm hne
      rw [es] at e₁ ⊢
      exact ⟨rfl, by simp only [slot] at e₁; omega⟩

/-- The elements of a list that satisfy a property form a list. -/
theorem exists_sublist {A : Type} (P : A → Prop) :
    ∀ l : List A, ∃ l' : List A, ∀ x, x ∈ l' ↔ x ∈ l ∧ P x
  | [] => ⟨[], fun _ => ⟨fun h => absurd h List.not_mem_nil, fun h => h.1⟩⟩
  | e :: l => by
    obtain ⟨l', h⟩ := exists_sublist P l
    by_cases he : P e
    · refine ⟨e :: l', fun x => ?_⟩
      rw [List.mem_cons, List.mem_cons, h]
      constructor
      · rintro (hx | ⟨hx, hp⟩)
        · exact ⟨.inl hx, hx ▸ he⟩
        · exact ⟨.inr hx, hp⟩
      · rintro ⟨hx | hx, hp⟩
        · exact .inl hx
        · exact .inr ⟨hx, hp⟩
    · refine ⟨l', fun x => ?_⟩
      rw [List.mem_cons, h]
      constructor
      · rintro ⟨hx, hp⟩
        exact ⟨.inr hx, hp⟩
      · rintro ⟨hx | hx, hp⟩
        · exact absurd (hx ▸ hp) he
        · exact ⟨hx, hp⟩

/-- A list of pairs in which a first component determines the second can be
listed without repeating a first component. -/
theorem exists_nodup_fst {A B : Type} : ∀ l : List (A × B),
    (∀ i γ γ', (i, γ) ∈ l → (i, γ') ∈ l → γ = γ') →
    ∃ l' : List (A × B), (l'.map Prod.fst).Nodup ∧ ∀ e, e ∈ l' ↔ e ∈ l
  | [], _ => ⟨[], List.nodup_nil, fun _ => Iff.rfl⟩
  | e :: l, hf => by
    obtain ⟨l', hn, hm⟩ := exists_nodup_fst l fun i γ γ' h₁ h₂ =>
      hf i γ γ' (List.mem_cons_of_mem _ h₁) (List.mem_cons_of_mem _ h₂)
    by_cases he : e.1 ∈ l'.map Prod.fst
    · refine ⟨l', hn, fun x =>
        ⟨fun hx => List.mem_cons_of_mem _ ((hm x).1 hx), fun hx => ?_⟩⟩
      rcases List.mem_cons.1 hx with hx | hx
      · obtain ⟨e', he', ee⟩ := List.mem_map.1 he
        have h₁ : (e.1, e'.2) ∈ l := by
          rw [← ee]
          exact (hm e').1 he'
        have e2 : e'.2 = e.2 :=
          hf e.1 e'.2 e.2 (List.mem_cons_of_mem _ h₁) List.mem_cons_self
        have e3 : e' = e := Prod.ext ee e2
        rw [hx, ← e3]
        exact he'
      · exact (hm x).2 hx
    · refine ⟨e :: l', List.nodup_cons.2 ⟨he, hn⟩, fun x => ?_⟩
      rw [List.mem_cons, List.mem_cons, hm]

/-- The new agents of a firing of `a` and `b`, from the labels of the
right-hand side and a list of its slots. -/
def childList (a b : Id) (lab : Option Bool → Nat → Option S)
    (slots : List (Option Bool × Nat)) : List (Id × S) :=
  slots.filterMap fun e => (lab e.1 e.2).map fun γ => (child a b e.1 e.2, γ)

theorem mem_childList {a b : Id} {lab : Option Bool → Nat → Option S}
    {slots : List (Option Bool × Nat)} (hs : ∀ o j γ, lab o j = some γ → (o, j) ∈ slots)
    (i : Id) (γ : S) :
    (i, γ) ∈ childList a b lab slots ↔ ∃ o j, i = child a b o j ∧ lab o j = some γ := by
  constructor
  · intro hm
    obtain ⟨⟨o, j⟩, -, he⟩ := List.mem_filterMap.1 hm
    cases hl : lab o j with
    | none =>
      rw [hl] at he
      cases he
    | some δ =>
      rw [hl] at he
      have e' : (child a b o j, δ) = (i, γ) := Option.some.inj he
      exact ⟨o, j, (Prod.mk.inj e').1.symm, hl.trans (congrArg some (Prod.mk.inj e').2)⟩
  · rintro ⟨o, j, rfl, hl⟩
    exact List.mem_filterMap.2 ⟨(o, j), hs o j γ hl, by simp [hl]⟩

/-- A name in that list comes with one symbol. -/
theorem childList_fun {a b : Id} (hne : a ≠ b) {lab : Option Bool → Nat → Option S}
    {slots : List (Option Bool × Nat)} (hs : ∀ o j γ, lab o j = some γ → (o, j) ∈ slots)
    (i : Id) (γ γ' : S) (h₁ : (i, γ) ∈ childList a b lab slots)
    (h₂ : (i, γ') ∈ childList a b lab slots) : γ = γ' := by
  obtain ⟨o, j, e₁, l₁⟩ := (mem_childList hs i γ).1 h₁
  obtain ⟨o', j', e₂, l₂⟩ := (mem_childList hs i γ').1 h₂
  obtain ⟨eo, ej⟩ := child_inj' hne (e₁.symm.trans e₂)
  rw [eo, ej, l₂] at l₁
  exact (Option.some.inj l₁).symm

/-- A finite right-hand side can be listed. -/
theorem Writes.exists {a b : Id} (hne : a ≠ b) {R : Rhs S} (hf : R.Fin) :
    ∃ as ls, Writes a b R as ls := by
  obtain ⟨ls₀, ws₀, hls, hws⟩ := hf
  have key := mem_childList (a := a) (b := b) hls
  obtain ⟨as, hn, hm⟩ := exists_nodup_fst _ (childList_fun hne hls)
  obtain ⟨ws, hws'⟩ := exists_sublist (fun e : LPort × LPort => R.link e.1 e.2) ws₀
  refine ⟨as, ws.map fun e => (emb a b e.1, emb a b e.2),
    ⟨fun {i γ} => (hm (i, γ)).trans (key i γ), hn, fun {p q} => ?_⟩⟩
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hx, he⟩ := List.mem_map.1 h
    exact ⟨x, y, ((hws' (x, y)).1 hx).2, (Prod.mk.inj he).1.symm, (Prod.mk.inj he).2.symm⟩
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    exact List.mem_map.2 ⟨(x, y), (hws' (x, y)).2 ⟨hws x y hxy, hxy⟩, rfl⟩

/-- **An idle thread can fire any active pair that is visible in memory**,
by its own actions and whatever the other threads are in the middle of: it
reads the pair, takes its two agents, writes the right-hand side, and is
idle again. -/
theorem Mach.fire {t : Nat} (ht : M.th t = .idle) (r : Redex sys M.mem a b α β R)
    (hf : R.Fin) : ∃ M', MRun sys 1 M M' ∧ M'.mem = M.mem.fire a b R ∧ M'.th = M.th := by
  obtain ⟨m, th⟩ := M
  obtain ⟨v, x, w⟩ := r.conn
  obtain ⟨as, ls, hw⟩ := Writes.exists r.ne hf
  have s₁ : MStep sys 0 ⟨m, th⟩ ⟨m, upd th t (.look a α)⟩ := .look ht r.ha
  obtain ⟨th₂, r₂, e₂, o₂⟩ := Mach.reach (sys := sys) w (upd th t (.look a α))
    (upd_same _ _ _)
  have s₃ : MStep sys 0 ⟨m, th₂⟩ ⟨m, upd th₂ t (.ready a b α β)⟩ := .found e₂ r.hb
  have s₄ : MStep sys 0 ⟨m, upd th₂ t (.ready a b α β)⟩
      ⟨m.take a, upd (upd th₂ t (.ready a b α β)) t (.half a b α β)⟩ :=
    .cas₁ (upd_same _ _ _) r.ha
  have s₅ : MStep sys 1 ⟨m.take a, upd (upd th₂ t (.ready a b α β)) t (.half a b α β)⟩
      ⟨(m.take a).take b,
        upd (upd (upd th₂ t (.ready a b α β)) t (.half a b α β)) t (.write as ls)⟩ :=
    .cas₂ (upd_same _ _ _) ⟨r.hb, fun e => r.ne e.symm⟩ r.ne r.rule hw
  obtain ⟨M', r₆, h₁, h₂, h₃, h₄, h₅⟩ := Mach.flush (sys := sys) ls as
    ⟨(m.take a).take b,
      upd (upd (upd th₂ t (.ready a b α β)) t (.half a b α β)) t (.write as ls)⟩
    (upd_same _ _ _)
  refine ⟨M', .step s₁ (r₂.trans (.step s₃ (.step s₄ (.step s₅ r₆)))), ?_, ?_⟩
  · apply Net.ext'
    · intro i γ
      rw [h₃]
      constructor
      · rintro (⟨⟨hi, hia⟩, hib⟩ | hm)
        · exact .inl ⟨hi, hia, hib⟩
        · exact .inr (hw.agent.1 hm)
      · rintro (⟨hi, hia, hib⟩ | hx)
        · exact .inl ⟨⟨hi, hia⟩, hib⟩
        · exact .inr (hw.agent.2 hx)
    · intro p q
      rw [h₄]
      constructor
      · rintro (hl | hm)
        · exact .inl hl
        · exact .inr (hw.link.1 hm)
      · rintro (hl | hx)
        · exact .inl hl
        · exact .inr (hw.link.2 hx)
    · intro p
      have e : M'.mem.free p ↔ ((m.take a).take b).free p := by rw [h₅]
      exact e
  · funext u
    by_cases hu : u = t
    · rw [hu, h₁]
      exact ht.symm
    · rw [h₂ u hu]
      show upd (upd (upd th₂ t (.ready a b α β)) t (.half a b α β)) t (.write as ls) u = th u
      rw [upd_ne _ _ hu, upd_ne _ _ hu, upd_ne _ _ hu, o₂ u hu, upd_ne _ _ hu]

/-- **The machine can perform every sequential reduction**, with a single
thread, when the rules are finite. -/
theorem Steps.mrun (hfin : ∀ {α β : S} {R : Rhs S}, sys.rule α β = some R → R.Fin) {n : Nat}
    {N' : Net S} (h : Steps (Step sys) n N N') : MRun sys n (Mach.init N) (Mach.init N') := by
  induction h with
  | refl N => exact .refl _
  | @head _ N₀ _ _ h₁ _ ih =>
    obtain ⟨a, b, α, β, R, r, rfl⟩ := h₁
    obtain ⟨M', hr, hm, ht⟩ := Mach.fire (M := Mach.init N₀) (t := 0) rfl r (hfin r.rule)
    have e : M' = Mach.init (N₀.fire a b R) := by
      obtain ⟨m, th⟩ := M'
      exact congr (congrArg Mach.mk hm) ht
    rw [e] at hr
    have h' := hr.trans ih
    rw [Nat.add_comm] at h'
    exact h'

/-- An action changes the state of one thread. -/
theorem MStep.th_eq {c : Nat} (hs : MStep sys c M M') : ∃ t s, M'.th = upd M.th t s := by
  cases hs <;> exact ⟨_, _, rfl⟩

/-- Finitely many threads are busy at any time. -/
theorem MRun.busy {k : Nat} (hr : MRun sys k M M')
    (h : ∃ ts : List Nat, ∀ u, u ∉ ts → M.th u = .idle) :
    ∃ ts : List Nat, ∀ u, u ∉ ts → M'.th u = .idle := by
  induction hr with
  | refl M => exact h
  | step hs _ ih =>
    obtain ⟨ts, hts⟩ := h
    obtain ⟨t, s, e⟩ := hs.th_eq
    refine ih ⟨t :: ts, fun u hu => ?_⟩
    have hut : u ≠ t := fun e' => hu (by rw [e']; exact List.mem_cons_self)
    rw [e, upd_ne _ _ hut]
    exact hts u fun hm => hu (List.mem_cons_of_mem _ hm)

theorem Mach.settle_all (sys : System S) : ∀ (ts : List Nat) (M : Mach S),
    ∃ M', MRun sys 0 M M' ∧ (∀ u, u ∈ ts → M'.th u = .idle) ∧
      ∀ u, u ∉ ts → M'.th u = M.th u
  | [], M => ⟨M, .refl _, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | t :: ts, M => by
    obtain ⟨M₁, r₁, h₁, o₁⟩ := Mach.settle sys M t
    obtain ⟨M₂, r₂, h₂, o₂⟩ := Mach.settle_all sys ts M₁
    refine ⟨M₂, r₁.trans r₂, fun u hu => ?_, fun u hu => ?_⟩
    · by_cases hm : u ∈ ts
      · exact h₂ u hm
      · rcases List.mem_cons.1 hu with e | hu
        · rw [o₂ u hm, e]
          exact h₁
        · exact absurd hu hm
    · have hne : u ≠ t := fun e => hu (by rw [e]; exact List.mem_cons_self)
      rw [o₂ u (fun hm => hu (List.mem_cons_of_mem _ hm)), o₁ u hne]

/-- **The normal form stays within reach.**  From every state that the
machine can get into, whatever the schedule so far, some continuation ends
with every thread idle and the normal form in memory, and it makes exactly
the claims that are missing.  So no schedule leads the machine into a state
where it is stuck or from which it can only go wrong. -/
theorem MRun.complete (hfin : ∀ {α β : S} {R : Rhs S}, sys.rule α β = some R → R.Fin)
    {n k : Nat} {N' : Net S} (hN : N.WF sys.ar) (hs : Steps (Step sys) n N N')
    (hn : Normal (Step sys) N') (hr : MRun sys k (Mach.init N) M) :
    ∃ M', MRun sys (n - k) M M' ∧ M'.Quiet ∧ M'.mem = N' := by
  obtain ⟨ts, hts⟩ := hr.busy ⟨[], fun _ _ => rfl⟩
  obtain ⟨M₁, r₁, h₁, o₁⟩ := Mach.settle_all sys ts M
  have hq : M₁.Quiet := by
    intro u
    by_cases hu : u ∈ ts
    · exact h₁ u hu
    · rw [o₁ u hu]
      exact hts u hu
  have r₀ : MRun sys k (Mach.init N) M₁ := by
    have h := hr.trans r₁
    rw [Nat.add_zero] at h
    exact h
  have s₁ := r₀.quiet hN hq
  obtain ⟨-, s₂⟩ := reduction_bounded hN hs hn s₁
  have e : M₁ = Mach.init M₁.mem := by
    obtain ⟨m, th⟩ := M₁
    exact congrArg (Mach.mk m) (funext hq)
  have r₂ := Steps.mrun hfin s₂
  rw [← e] at r₂
  have h := r₁.trans r₂
  rw [Nat.zero_add] at h
  exact ⟨_, h, Mach.init_quiet N', rfl⟩

end Machine

end INet
