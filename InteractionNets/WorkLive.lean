import InteractionNets.WorkList
import InteractionNets.Fair

namespace INet

variable {S : Type}

/-! # The program that rechecks only what a rule touched does not rest early

The argument of `XMach.Live` carries over, with one change.  There a
thread that is writing answers for every active pair, because it will take
a fresh list of all agents.  Here only a thread writing the right-hand side
of a rule that joins two interface ports does.  Any other writer answers
for a pair through its list, which holds the agents it is writing: an
active pair made by its claim has one of them in it (`Redex.of_fire`), and
a thread that finds one of its segments missing has found one of them,
because the thread writes its segments before its agents and every segment
of such a rule ends at a new agent (`WMach.Live.own`). -/

section WLive

variable [DecidableEq S] {xs : XSys S}

/-- The machine of `XMach` with the same memory and the same states. -/
def WMach.toX (M : WMach S) : XMach S := ⟨M.mem, M.ths.map WThread.toX⟩

omit [DecidableEq S] in
theorem WMach.get_toX {M : WMach S} {u : Nat} {U' : XThread S}
    (h : M.toX.ths[u]? = some U') : ∃ U, M.ths[u]? = some U ∧ U.toX = U' := by
  have h' : (M.ths.map WThread.toX)[u]? = some U' := h
  rw [List.getElem?_map] at h'
  cases hu : M.ths[u]? with
  | none =>
    rw [hu] at h'
    cases h'
  | some U =>
    rw [hu] at h'
    exact ⟨U, rfl, Option.some.inj h'⟩

/-- The thread answers for the pair of `a` and `b`: it is writing a rule
that joins interface ports (and will take a fresh list), or one of the two
is in its list, or it is attempting one of them. -/
def WThread.Answers (T : WThread S) (a b : Id) (α β : S) : Prop :=
  (T.st.writing ∧ T.again = true) ∨ (a, α) ∈ T.todo ∨ (b, β) ∈ T.todo ∨
    T.st.target = some a ∨ T.st.target = some b

omit [DecidableEq S] in
theorem WThread.Answers.symm {T : WThread S} {a b : Id} {α β : S} (h : T.Answers a b α β) :
    T.Answers b a β α := by
  rcases h with h | h | h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr (.inr h)))
  · exact .inr (.inr (.inr (.inl h)))

omit [DecidableEq S] in
theorem WThread.Answers.carry {T T₁ : WThread S} {a b : Id} {α β : S}
    (h : T.Answers a b α β) (hT₁ : T₁.todo = T.todo) (htg : T₁.st.target = T.st.target)
    (hnw : ¬ T.st.writing) : T₁.Answers a b α β := by
  rcases h with h | h | h | h | h
  · exact absurd h.1 hnw
  · exact .inr (.inl (by rw [hT₁]; exact h))
  · exact .inr (.inr (.inl (by rw [hT₁]; exact h)))
  · exact .inr (.inr (.inr (.inl (htg.trans h))))
  · exact .inr (.inr (.inr (.inr (htg.trans h))))

/-- After an action of thread `t`, which leaves it as `T₁`, someone answers
for the pair. -/
def WNewAns (ths : List (WThread S)) (t : Nat) (T₁ : WThread S) (a b : Id) (α β : S) : Prop :=
  T₁.Answers a b α β ∨ ∃ (u : Nat) (U : WThread S), u ≠ t ∧ ths[u]? = some U ∧ U.Answers a b α β

omit [DecidableEq S] in
theorem WNewAns.symm {ths : List (WThread S)} {t : Nat} {T₁ : WThread S} {a b : Id} {α β : S}
    (h : WNewAns ths t T₁ a b α β) : WNewAns ths t T₁ b a β α := by
  rcases h with h | ⟨u, U, hne, hu, hA⟩
  · exact .inl h.symm
  · exact .inr ⟨u, U, hne, hu, hA.symm⟩

/-- The invariant. -/
structure WMach.Live (xs : XSys S) (M : WMach S) : Prop where
  inv : M.toMach.Inv xs.sys
  /-- Every active pair of the goal with a rule is answered for. -/
  cov : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
    ∃ (t : Nat) (T : WThread S), M.ths[t]? = some T ∧ T.Answers a b α β
  /-- What the threads have read is still true. -/
  sane : ∀ (t : Nat) (T : WThread S), M.ths[t]? = some T → T.st.Sane M.toMach.goal
  /-- A writer has the agents it is writing in its list. -/
  kids : ∀ (t : Nat) (T : WThread S), M.ths[t]? = some T → ∀ i γ, T.st.pendA i γ →
    (i, γ) ∈ T.todo
  /-- A segment that a writer of a rule that joins no interface ports has
  still to write ends at a port of an agent it has still to write. -/
  own : ∀ (t : Nat) (T : WThread S), M.ths[t]? = some T → T.again = false → ∀ p q,
    T.st.pendL p q → ∃ i γ k, T.st.pendA i γ ∧ k ≤ xs.sys.ar γ ∧ (p = (i, k) ∨ q = (i, k))
omit [DecidableEq S] in
theorem WMach.Live.ok {M : WMach S} (hL : M.Live xs) {t : Nat} {T : WThread S}
    (ht : M.ths[t]? = some T) : T.st.Ok M.mem.toNet := by
  have h : (threadOf (M.ths.map WThread.toX) t).Ok M.mem.toNet := hL.inv.ok t
  rw [threadOf_map_eq ht] at h
  exact h
omit [DecidableEq S] in
theorem WMach.Live.lift {M : WMach S} (hL : M.Live xs) {u v x y : Port}
    (w : Walk M.mem.toNet.link (fun _ => False) u v x y) :
    Walk M.toMach.goal.link (M.toMach.goal.End xs.sys.ar) u v x y :=
  w.mono_term (fun hl => .inl hl) (fun hl => .inl hl) hL.inv.wf.symm (fun hT => hT)
    hL.inv.wf.end_unique

omit [DecidableEq S] in
/-- An agent of the goal is in memory, or held by a thread, or still to be
written by one. -/
theorem WMach.goal_agent {M : WMach S} {i : Id} {γ : S} (h : M.toMach.goal.agent i γ) :
    (i, γ) ∈ M.mem.agents ∨
      (∃ (u : Nat) (U : WThread S), M.ths[u]? = some U ∧ U.st.held i γ) ∨
      ∃ (u : Nat) (U : WThread S), M.ths[u]? = some U ∧ U.st.pendA i γ := by
  rcases XMach.goal_agent (M := M.toX) h with hm | ⟨u, U', hu, hU⟩ | ⟨u, U', hu, hU⟩
  · exact .inl hm
  · obtain ⟨U, hu', rfl⟩ := WMach.get_toX hu
    exact .inr (.inl ⟨u, U, hu', hU⟩)
  · obtain ⟨U, hu', rfl⟩ := WMach.get_toX hu
    exact .inr (.inr ⟨u, U, hu', hU⟩)

omit [DecidableEq S] in
theorem WMach.goal_link {M : WMach S} {p q : Port} (h : M.toMach.goal.link p q) :
    (p, q) ∈ M.mem.wires ∨
      ∃ (u : Nat) (U : WThread S), M.ths[u]? = some U ∧ U.st.pendL p q := by
  rcases XMach.goal_link (M := M.toX) h with hm | ⟨u, U', hu, hU⟩
  · exact .inl hm
  · obtain ⟨U, hu', rfl⟩ := WMach.get_toX hu
    exact .inr ⟨u, U, hu', hU⟩

omit [DecidableEq S] in
/-- An agent of the pair that is not in memory is held by another thread,
which attempts it, or is still to be written by another thread, which has
it in its list. -/
theorem WMach.Live.ans_of_agent {M : WMach S} (hL : M.Live xs) {t : Nat} {T : WThread S}
    (ht : M.ths[t]? = some T) {a b : Id} {α β : S} {i : Id} {γ : S}
    (hi : (i = a ∧ γ = α) ∨ (i = b ∧ γ = β))
    (hg : M.toMach.goal.agent i γ) (hnm : (i, γ) ∉ M.mem.agents) (hT : ¬ T.st.held i γ)
    (hTp : ¬ T.st.pendA i γ) (T₁ : WThread S) : WNewAns M.ths t T₁ a b α β := by
  rcases WMach.goal_agent hg with hm | ⟨u, U, hu, hU⟩ | ⟨u, U, hu, hU⟩
  · exact absurd hm hnm
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hT (Option.some.inj hu ▸ hU)
    refine .inr ⟨u, U, hne, hu, ?_⟩
    rcases hi with ⟨e, -⟩ | ⟨e, -⟩
    · exact .inr (.inr (.inr (.inl (e ▸ TState.held_target hU))))
    · exact .inr (.inr (.inr (.inr (e ▸ TState.held_target hU))))
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hTp (Option.some.inj hu ▸ hU)
    have hk := hL.kids u U hu i γ hU
    refine .inr ⟨u, U, hne, hu, ?_⟩
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inr (.inl hk)
    · exact .inr (.inr (.inl hk))

omit [DecidableEq S] in
/-- A segment of the goal that is not in memory is still to be written by
another thread.  If that thread writes a rule that joins interface ports it
answers for every pair; otherwise the segment ends at a port of an agent it
is writing, which is an end of the goal.  When every end of the segment
that is an end of the goal is a principal port of the pair, that agent is
in the pair, and in the writer's list. -/
theorem WMach.Live.ans_of_link {M : WMach S} (hL : M.Live xs) {t : Nat} {T : WThread S}
    (ht : M.ths[t]? = some T) {a b : Id} {α β : S} {R : Rhs S}
    (r : Redex xs.sys M.toMach.goal a b α β R) {p q : Port} (hg : M.toMach.goal.link p q)
    (hnm : (p, q) ∉ M.mem.wires) (hTp : ¬ T.st.pendL p q)
    (hon : ∀ z, (z = p ∨ z = q) → M.toMach.goal.End xs.sys.ar z → z = (a, 0) ∨ z = (b, 0))
    (T₁ : WThread S) : WNewAns M.ths t T₁ a b α β := by
  have hG := hL.inv.wf
  rcases WMach.goal_link hg with hm | ⟨u, U, hu, hU⟩
  · exact absurd hm hnm
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hTp (Option.some.inj hu ▸ hU)
    refine .inr ⟨u, U, hne, hu, ?_⟩
    cases hag : U.again with
    | true => exact .inl ⟨TState.pendL_writing hU, hag⟩
    | false =>
      obtain ⟨i, γ, k, hpa, hk, hz⟩ := hL.own u U hu hag p q hU
      have hgi : M.toMach.goal.agent i γ := by
        refine .inr ⟨u, ?_⟩
        show (threadOf (M.ths.map WThread.toX) u).pendA i γ
        rw [threadOf_map_eq hu]
        exact hpa
      have hE : M.toMach.goal.End xs.sys.ar (i, k) := .inr ⟨γ, hgi, hk⟩
      have hm := hL.kids u U hu i γ hpa
      rcases hon (i, k) (hz.imp (fun e => e.symm) (fun e => e.symm)) hE with e | e
      · obtain ⟨rfl, -⟩ := Prod.mk.inj e
        rw [hG.agent_fun hgi r.ha] at hm
        exact .inr (.inl hm)
      · obtain ⟨rfl, -⟩ := Prod.mk.inj e
        rw [hG.agent_fun hgi r.hb] at hm
        exact .inr (.inr (.inl hm))

omit [DecidableEq S] in
/-- When an attempt fails, the pairs the thread answered for through its
list are still answered for by it; only the agent it was attempting needs
another answer. -/
theorem WMach.Live.ans_of_fail {M : WMach S} (hL : M.Live xs) {t : Nat} {T T₁ : WThread S}
    (hT₁ : T₁.todo = T.todo) (hnw : ¬ T.st.writing)
    (h : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R → T.st.target = some a →
      WNewAns M.ths t T₁ a b α β) :
    ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R → T.Answers a b α β →
      WNewAns M.ths t T₁ a b α β := by
  intro a b α β R r hA
  rcases hA with hw | hm | hm | htg | htg
  · exact absurd hw.1 hnw
  · exact .inl (.inr (.inl (by rw [hT₁]; exact hm)))
  · exact .inl (.inr (.inr (.inl (by rw [hT₁]; exact hm))))
  · exact h a b α β R r htg
  · obtain ⟨R', r', -⟩ := r.flip hL.inv.wf
    exact (h b a β α R' r' htg).symm

theorem WMach.step_eq {M : WMach S} {t : Nat} {T T₁ : WThread S} {X₁ : XNet S} {c : Nat}
    (ht : M.ths[t]? = some T) (hact : WMach.act xs M.mem T = (X₁, T₁, c)) :
    M.step xs t = (⟨X₁, M.ths.set t T₁⟩, c) := by
  unfold WMach.step
  rw [ht]
  dsimp only
  rw [hact]

/-- An action that makes no claim keeps the invariant, if the thread is
still answered for and still keeps its list and its segments as it should. -/
theorem WMach.Live.step_zero {M : WMach S} (hL : M.Live xs) {t : Nat} {T T₁ : WThread S}
    {X₁ : XNet S} (ht : M.ths[t]? = some T) (hact : WMach.act xs M.mem T = (X₁, T₁, 0))
    (hsane : T₁.st.Sane M.toMach.goal)
    (hkids : ∀ i γ, T₁.st.pendA i γ → (i, γ) ∈ T₁.todo)
    (hown : T₁.again = false → ∀ p q, T₁.st.pendL p q →
      ∃ i γ k, T₁.st.pendA i γ ∧ k ≤ xs.sys.ar γ ∧ (p = (i, k) ∨ q = (i, k)))
    (hans : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R → T.Answers a b α β →
      WNewAns M.ths t T₁ a b α β) : (M.step xs t).1.Live xs := by
  have es := WMach.step_eq ht hact
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
  have hbase : (WMach.toMach ⟨X₁, M.ths.set t T₁⟩).Inv xs.sys ∧
      (WMach.toMach ⟨X₁, M.ths.set t T₁⟩).goal = M.toMach.goal := by
    have h := WMach.step_sim xs M t
    rw [es] at h
    rcases h with ⟨e₁, -⟩ | hs
    · have e₁' : WMach.toMach ⟨X₁, M.ths.set t T₁⟩ = M.toMach := e₁
      rw [e₁']
      exact ⟨hL.inv, rfl⟩
    · obtain ⟨hi, hr⟩ := MStep.sim hL.inv hs
      exact ⟨hi, hr.goal_zero rfl⟩
  obtain ⟨hinv, hg⟩ := hbase
  have get : ∀ {u : Nat} {U : WThread S}, (M.ths.set t T₁)[u]? = some U →
      (u = t ∧ U = T₁) ∨ (u ≠ t ∧ M.ths[u]? = some U) := by
    intro u U hu
    by_cases hut : u = t
    · rw [hut, List.getElem?_set_self hlt] at hu
      exact .inl ⟨hut, (Option.some.inj hu).symm⟩
    · rw [List.getElem?_set_ne (Ne.symm hut)] at hu
      exact .inr ⟨hut, hu⟩
  rw [es]
  show WMach.Live xs ⟨X₁, M.ths.set t T₁⟩
  refine ⟨hinv, ?_, ?_, ?_, ?_⟩
  · intro a b α β R r
    rw [hg] at r
    show ∃ (u : Nat) (U : WThread S), (M.ths.set t T₁)[u]? = some U ∧ U.Answers a b α β
    obtain ⟨u, U, hu, hA⟩ := hL.cov a b α β R r
    by_cases hut : u = t
    · rw [hut, ht] at hu
      rw [← Option.some.inj hu] at hA
      rcases hans a b α β R r hA with h | ⟨u', U', hne, hu', hA'⟩
      · exact ⟨t, T₁, List.getElem?_set_self hlt, h⟩
      · exact ⟨u', U', by rw [List.getElem?_set_ne (Ne.symm hne)]; exact hu', hA'⟩
    · exact ⟨u, U, by rw [List.getElem?_set_ne (Ne.symm hut)]; exact hu, hA⟩
  · intro u U hu
    rw [hg]
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hsane
    · exact hL.sane u U hu'
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hkids
    · exact hL.kids u U hu'
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hown
    · exact hL.own u U hu'

omit [DecidableEq S] in
/-- A claim fires the pair it claims, in the goal. -/
theorem Mach.Inv.cas₂_goal {sys : System S} {M : Mach S} (h : M.Inv sys) {t : Nat}
    {a b : Id} {α β : S} {R : Rhs S} {as : List (Id × S)} {ls : List (Port × Port)}
    (e : M.th t = .half a b α β) (hm : M.mem.agent b β) (hne : a ≠ b)
    (hr : sys.rule α β = some R) (hw : Writes a b R as ls) :
    Redex sys M.goal a b α β R ∧
      Mach.goal ⟨M.mem.take b, upd M.th t (.write as ls)⟩ = M.goal.fire a b R := by
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
  refine ⟨rg, ?_⟩
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

omit [DecidableEq S] in
/-- A rule that does not join interface ports by the test of the program
joins none. -/
theorem XRhs.noJoin_of_joins {R : XRhs S} {ar : S → Nat} {α β : S}
    (hwf : R.toRhs.WF ar α β) (h : R.joins ar α β = false) : R.toRhs.NoJoin := by
  intro x y hxy
  cases x with
  | new o j k => exact .inl trivial
  | ifc s k =>
    cases y with
    | new o j k' => exact .inr trivial
    | ifc s' k' =>
      exfalso
      have hv : k < ar (sel α β s) := hwf.valid hxy
      have hmem : LPort.ifc s k ∈ ifcPorts ar α β := mem_ifcPorts.2 ⟨s, k, rfl, hv⟩
      have hw : R.wire (.ifc s k) = some (.ifc s' k') := hxy
      have : R.joins ar α β = true := by
        unfold XRhs.joins
        rw [List.any_eq_true]
        exact ⟨_, hmem, by rw [hw]; rfl⟩
      rw [h] at this
      cases this

omit [DecidableEq S] in
/-- The point after the first of a walk is its last, if it is a terminal. -/
theorem Walk.term_second {V : Type} {L : V → V → Prop} {T : V → Prop} {u v x y : V}
    (w : Walk L T u v x y) (hv : T v) : v = y := by
  cases w with
  | single _ => rfl
  | cons _ hT _ _ => exact absurd hv hT

omit [DecidableEq S] in
/-- A walk that has not reached a terminal can be continued along the walk
with the same first segment that reaches one, and if the next point is a
terminal it is the last. -/
theorem Walk.extend' {V : Type} {L : V → V → Prop} {T : V → Prop} (hW : Wiring L T)
    {u v p c x y : V} (w₁ : Walk L T u v p c) (w₂ : Walk L T u v x y) (hc : ¬ T c)
    (hy : T y) : ∃ q, L c q ∧ q ≠ p ∧ (T q → q = y) := by
  induction w₁ generalizing x y with
  | single h =>
    cases w₂ with
    | single _ => exact absurd hy hc
    | cons _ _ hne w => exact ⟨_, w.link_first, hne, fun hq => Walk.term_second w hq⟩
  | cons h hT hne w ih =>
    cases w₂ with
    | single _ => exact absurd hy hT
    | cons _ _ hne' w' =>
      rcases hW.deg (hW.symm h) w.link_first w'.link_first with e | e | e
      · exact absurd e.symm hne
      · exact absurd e.symm hne'
      · subst e
        exact ih w' hc hy

theorem WMach.act_half_some {X : XNet S} {T : WThread S} {a b : Id} {α β : S} {R : XRhs S}
    (hs : T.st = .half a b α β)
    (h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    WMach.act xs X T = (X.takeAgent b, ⟨R.newAgents a b ++ T.todo,
      .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β),
      R.joins xs.sys.ar α β⟩, 1) := by
  obtain ⟨todo, st, again⟩ := T
  dsimp only at hs
  subst hs
  unfold WMach.act
  dsimp only
  rw [h]

/-- **A claim keeps the invariant.**  If the rule joins interface ports the
thread answers for every pair; otherwise a new active pair has a new agent
in it, which is in the thread's list. -/
theorem WMach.Live.step_claim {M : WMach S} (hL : M.Live xs) {t : Nat} {T : WThread S}
    (ht : M.ths[t]? = some T) {a₀ b₀ : Id} {α₀ β₀ : S} {R : XRhs S}
    (hs : T.st = .half a₀ b₀ α₀ β₀)
    (hh : (if assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ then xs.rule α₀ β₀ else none) = some R) :
    (M.step xs t).1.Live xs := by
  have hact := WMach.act_half_some (xs := xs) (X := M.mem) hs hh
  have es := WMach.step_eq ht hact
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
  have hc : assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ := by
    split at hh
    · rename_i hc
      exact hc
    · cases hh
  have hR : xs.rule α₀ β₀ = some R := by
    rw [ite_pos' hc] at hh
    exact hh
  obtain ⟨hsys, hw⟩ := xs.writes hc.2 hR
  have hG := hL.inv.wf
  have hRwf := xs.sys.rule_wf hsys
  have e : M.toMach.th t = .half a₀ b₀ α₀ β₀ := by
    rw [← hs]
    exact threadOf_map_eq ht
  obtain ⟨rg, eg⟩ := hL.inv.cas₂_goal e (assoc_mem hc.1) hc.2 hsys hw
  let T₁ : WThread S := ⟨R.newAgents a₀ b₀ ++ T.todo,
    .write (R.newAgents a₀ b₀) (R.newLinks xs.sys.ar a₀ b₀ α₀ β₀),
    R.joins xs.sys.ar α₀ β₀⟩
  have hm1 : (M.ths.set t T₁).map WThread.toX = (M.ths.map WThread.toX).set t T₁.toX := by
    rw [List.map_set]
  have hmx : (M.ths.map WThread.toX)[t]? = some T.toX := by
    rw [List.getElem?_map, ht]
    rfl
  have eM : WMach.toMach ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩ =
      ⟨M.toMach.mem.take b₀, upd M.toMach.th t
        (.write (R.newAgents a₀ b₀) (R.newLinks xs.sys.ar a₀ b₀ α₀ β₀))⟩ := by
    show Mach.mk (M.mem.takeAgent b₀).toNet (threadOf ((M.ths.set t T₁).map WThread.toX)) = _
    rw [hm1, threadOf_set hmx, XNet.takeAgent_toNet]
    rfl
  have eg' : (WMach.toMach ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩).goal =
      M.toMach.goal.fire a₀ b₀ R.toRhs := by
    rw [eM]
    exact eg
  have hinv : (WMach.toMach ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩).Inv xs.sys := by
    have h := WMach.step_sim xs M t
    rw [es] at h
    rcases h with ⟨-, e₂⟩ | hs'
    · cases e₂
    · exact (MStep.sim hL.inv hs').1
  have get : ∀ {u : Nat} {U : WThread S}, (M.ths.set t T₁)[u]? = some U →
      (u = t ∧ U = T₁) ∨ (u ≠ t ∧ M.ths[u]? = some U) := by
    intro u U hu
    by_cases hut : u = t
    · rw [hut, List.getElem?_set_self hlt] at hu
      exact .inl ⟨hut, (Option.some.inj hu).symm⟩
    · rw [List.getElem?_set_ne (Ne.symm hut)] at hu
      exact .inr ⟨hut, hu⟩
  have site : Site xs.sys.ar M.toMach.goal a₀ b₀ α₀ β₀ := ⟨hG, rg.ha, rg.hb, rg.ne, rg.conn⟩
  -- the agents of the goal after the claim that are new are the thread's
  have newKid : ∀ {i : Id} {γ : S}, (M.toMach.goal.fire a₀ b₀ R.toRhs).agent i γ →
      (∃ o j, i = child a₀ b₀ o j) → (i, γ) ∈ R.newAgents a₀ b₀ := by
    intro i γ h ⟨o, j, ei⟩
    rcases h with ⟨hi, -, -⟩ | hx
    · exact absurd (ei ▸ .inl ⟨γ, hi⟩) (site.not_used_child o j)
    · exact hw.agent.2 hx
  have gone : ∀ {γ : S}, ¬ (M.toMach.goal.fire a₀ b₀ R.toRhs).agent a₀ γ := by
    intro γ h
    rcases h with ⟨-, h, -⟩ | ⟨o, j, ei, -⟩
    · exact h rfl
    · exact site.not_used_child o j (ei ▸ site.used_sel false)
  have gone' : ∀ {γ : S}, ¬ (M.toMach.goal.fire a₀ b₀ R.toRhs).agent b₀ γ := by
    intro γ h
    rcases h with ⟨-, -, h⟩ | ⟨o, j, ei, -⟩
    · exact h rfl
    · exact site.not_used_child o j (ei ▸ site.used_sel true)
  rw [es]
  show WMach.Live xs ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩
  refine ⟨hinv, ?_, ?_, ?_, ?_⟩
  · intro a b α β R' r'
    rw [eg'] at r'
    show ∃ (u : Nat) (U : WThread S), (M.ths.set t T₁)[u]? = some U ∧ U.Answers a b α β
    cases hj : (R.joins xs.sys.ar α₀ β₀) with
    | true => exact ⟨t, T₁, List.getElem?_set_self hlt, .inl ⟨trivial, hj⟩⟩
    | false =>
      have hj' : R.joins xs.sys.ar α₀ β₀ = false := hj
      have hNJ := XRhs.noJoin_of_joins hRwf hj'
      rcases Redex.of_fire hG rg hNJ r' with r | hka | hkb
      · obtain ⟨u, U, hu, hA⟩ := hL.cov a b α β R' r
        by_cases hut : u = t
        · rw [hut, ht] at hu
          obtain rfl := Option.some.inj hu
          refine ⟨t, T₁, List.getElem?_set_self hlt, ?_⟩
          rcases hA with hw' | hm | hm | htg | htg
          · rw [hs] at hw'
            exact False.elim hw'.1
          · exact .inr (.inl (List.mem_append_right _ hm))
          · exact .inr (.inr (.inl (List.mem_append_right _ hm)))
          · rw [hs] at htg
            obtain rfl : a₀ = a := Option.some.inj htg
            exact absurd r'.ha gone
          · rw [hs] at htg
            obtain rfl : a₀ = b := Option.some.inj htg
            exact absurd r'.hb gone
        · exact ⟨u, U, by rw [List.getElem?_set_ne (Ne.symm hut)]; exact hu, hA⟩
      · exact ⟨t, T₁, List.getElem?_set_self hlt,
          .inr (.inl (List.mem_append_left _ (newKid r'.ha hka)))⟩
      · exact ⟨t, T₁, List.getElem?_set_self hlt,
          .inr (.inr (.inl (List.mem_append_left _ (newKid r'.hb hkb))))⟩
  · intro u U hu
    rw [eg']
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact TState.sane_of_writing _ trivial
    · exact TState.Sane.fire hG (fun hl => .inl hl) rg (hL.ok hu') (hL.sane u U hu')
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · intro i γ hp
      exact List.mem_append_left _ hp
    · exact hL.kids u U hu'
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · intro hj p q hp
      have hj' : R.joins xs.sys.ar α₀ β₀ = false := hj
      obtain ⟨x, y, hxy, rfl, rfl⟩ := hw.link.1 hp
      rcases XRhs.noJoin_of_joins hRwf hj' x y hxy with hx | hy
      · cases x with
        | ifc s k => exact False.elim hx
        | new o j k =>
          obtain ⟨γ, hl, hk⟩ := (hRwf.valid hxy : R.toRhs.Valid xs.sys.ar α₀ β₀ (.new o j k))
          exact ⟨child a₀ b₀ o j, γ, k, hw.agent.2 ⟨o, j, rfl, hl⟩, hk, .inl rfl⟩
      · cases y with
        | ifc s k => exact False.elim hy
        | new o j k =>
          obtain ⟨γ, hl, hk⟩ :=
            (hRwf.valid (hRwf.symm hxy) : R.toRhs.Valid xs.sys.ar α₀ β₀ (.new o j k))
          exact ⟨child a₀ b₀ o j, γ, k, hw.agent.2 ⟨o, j, rfl, hl⟩, hk, .inr rfl⟩
    · exact hL.own u U hu'

/-- Away from writing and claiming, the program acts as `XMach`, and keeps
whether it must take a fresh list. -/
theorem WMach.act_lift {X X₁ : XNet S} {todo : List (Id × S)} {st : TState S} {again : Bool}
    {T₁ : XThread S} (hst : ∀ as ls, st ≠ .write as ls)
    (h : XMach.act xs X ⟨todo, st⟩ = (X₁, T₁, 0)) :
    WMach.act xs X ⟨todo, st, again⟩ = (X₁, ⟨T₁.todo, T₁.st, again⟩, 0) := by
  rcases WMach.act_agree xs X ⟨todo, st, again⟩ hst with e | ⟨a, b, α, β, R, -, -, -, ex⟩
  · have e' : WMach.act xs X ⟨todo, st, again⟩ = ((XMach.act xs X ⟨todo, st⟩).1,
        ⟨(XMach.act xs X ⟨todo, st⟩).2.1.todo, (XMach.act xs X ⟨todo, st⟩).2.1.st, again⟩,
        (XMach.act xs X ⟨todo, st⟩).2.2) := e
    rw [e', h]
  · have ex' : XMach.act xs X ⟨todo, st⟩ = (X.takeAgent b,
        ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) := ex
    rw [ex'] at h
    cases h

/-- **Every action keeps the invariant.** -/
theorem WMach.step_live {M : WMach S} (hL : M.Live xs) (t : Nat) :
    (M.step xs t).1.Live xs := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold WMach.step
      rw [ht]
    rw [e]
    exact hL
  | some T =>
    have hG := hL.inv.wf
    have memG : ∀ {i : Id} {γ : S}, (i, γ) ∈ M.mem.agents → M.toMach.goal.agent i γ :=
      fun h => .inl (.inl h)
    have assocG : ∀ {i : Id} {γ : S}, (i, γ) ∈ M.mem.agents →
        assoc i M.mem.agents = some γ :=
      fun h => assoc_eq_of_unique h fun γ' h' => hG.agent_fun (memG h') (memG h)
    have hS := hL.sane t T ht
    have hok := hL.ok ht
    obtain ⟨todo, s, again⟩ := T
    -- states that are not writing have nothing pending
    have noA : ∀ {st : TState S}, ¬ st.writing → ∀ i γ, ¬ st.pendA i γ :=
      fun hn i γ h => hn (TState.pendA_writing h)
    have noL : ∀ {st : TState S}, ¬ st.writing → ∀ p q, ¬ st.pendL p q :=
      fun hn p q h => hn (TState.pendL_writing h)
    have zero : ∀ {X₁ : XNet S} {T₁ : WThread S}, WMach.act xs M.mem ⟨todo, s, again⟩ =
        (X₁, T₁, 0) → T₁.st.Sane M.toMach.goal → ¬ T₁.st.writing →
        (∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
          WThread.Answers ⟨todo, s, again⟩ a b α β → WNewAns M.ths t T₁ a b α β) →
        (M.step xs t).1.Live xs :=
      fun hact hsane hnw hans => hL.step_zero ht hact hsane
        (fun i γ h => absurd h (noA hnw i γ)) (fun _ p q h => absurd h (noL hnw p q)) hans
    cases s with
    | idle =>
      cases todo with
      | nil =>
        refine zero (WMach.act_lift (fun _ _ h => by cases h) rfl) trivial (fun x => x)
          fun a b α β R _ hA => .inl hA
      | cons e rest =>
        by_cases he : assoc e.1 M.mem.agents = some e.2
        · refine zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_idle_pos he))
            ⟨.inl ⟨e.2, memG (assoc_mem he)⟩,
              fun α' h' => hG.agent_fun h' (memG (assoc_mem he)),
              fun q q' h h' => hG.end_unique
                (.inr ⟨e.2, memG (assoc_mem he), Nat.zero_le _⟩) h h'⟩ (fun x => x) ?_
          intro a b α β R _ hA
          rcases hA with hw | hm | hm | htg | htg
          · exact False.elim hw.1
          · rcases List.mem_cons.1 hm with heq | hm
            · exact .inl (.inr (.inr (.inr (.inl
                (congrArg (fun x : Id × S => some x.1) heq).symm))))
            · exact .inl (.inr (.inl hm))
          · rcases List.mem_cons.1 hm with heq | hm
            · exact .inl (.inr (.inr (.inr (.inr
                (congrArg (fun x : Id × S => some x.1) heq).symm))))
            · exact .inl (.inr (.inr (.inl hm)))
          · cases htg
          · cases htg
        · refine zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_idle_neg he))
            trivial (fun x => x) ?_
          intro a b α β R r hA
          rcases hA with hw | hm | hm | htg | htg
          · exact False.elim hw.1
          · rcases List.mem_cons.1 hm with heq | hm
            · have hnm : (a, α) ∉ M.mem.agents := fun h => he (by rw [← heq]; exact assocG h)
              exact hL.ans_of_agent ht (.inl ⟨rfl, rfl⟩) r.ha hnm (fun x => x) (fun x => x) _
            · exact .inl (.inr (.inl hm))
          · rcases List.mem_cons.1 hm with heq | hm
            · have hnm : (b, β) ∉ M.mem.agents := fun h => he (by rw [← heq]; exact assocG h)
              exact hL.ans_of_agent ht (.inr ⟨rfl, rfl⟩) r.hb hnm (fun x => x) (fun x => x) _
            · exact .inl (.inr (.inr (.inl hm)))
          · cases htg
          · cases htg
    | look a₀ α₀ =>
      cases hv : assoc (a₀, 0) M.mem.wires with
      | some q =>
        have hl : M.toMach.goal.link (a₀, 0) q := .inl (assoc_mem hv)
        have hf : q ∉ [((a₀, 0) : Port)] := by
          intro h
          rw [List.mem_singleton.1 h] at hl
          exact hG.irrefl hl
        exact zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_look hv))
          ⟨hS.1, hS.2.1, hS.2.2, [], .step .start hl hf⟩ (fun x => x)
          fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
      | none =>
        refine zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_look_none hv))
          trivial (fun x => x)
          (hL.ans_of_fail (T := ⟨todo, .look a₀ α₀, again⟩) rfl (fun x => x) ?_)
        intro a b α β R r htg
        have ea : a = a₀ := (Option.some.inj htg).symm
        subst ea
        obtain ⟨q, hq⟩ := hG.end_wired r.end_left
        refine hL.ans_of_link ht r hq (fun hm => ?_) (fun x => x) ?_ _
        · obtain ⟨q', e'⟩ := assoc_of_mem hm
          rw [hv] at e'
          cases e'
        · intro z hz hE
          rcases hz with ez | ez
          · exact .inl ez
          · rw [ez] at hE ⊢
            obtain ⟨v₂, x₂, w₂⟩ := r.conn
            have ev : q = v₂ := hG.end_unique r.end_left hq w₂.link_first
            subst ev
            exact .inr (Walk.term_second w₂ hE)
    | seek a₀ α₀ p c =>
      obtain ⟨v, w⟩ := hok
      have w' := hL.lift w
      cases hsc : (if c.2 = 0 then assoc c.1 M.mem.agents else none) with
      | some β' =>
        have hq : c.2 = 0 ∧ assoc c.1 M.mem.agents = some β' := by
          split at hsc
          · rename_i h0
            exact ⟨h0, hsc⟩
          · cases hsc
        by_cases hc : a₀ ≠ c.1 ∧ (xs.rule α₀ β').isSome
        · exact zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_seek_found hsc hc))
            ⟨hS.1, fun α' h' => ⟨hS.2.1 α' h', memG (assoc_mem hq.2)⟩⟩ (fun x => x)
            fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
        · refine zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_seek_norule hsc hc))
            trivial (fun x => x)
            (hL.ans_of_fail (T := ⟨todo, .seek a₀ α₀ p c, again⟩) rfl (fun x => x) ?_)
          intro a b α β R r htg
          have ea : a = a₀ := (Option.some.inj htg).symm
          subst ea
          exfalso
          have hEc : M.toMach.goal.End xs.sys.ar c :=
            .inr ⟨β', memG (assoc_mem hq.2), by rw [hq.1]; exact Nat.zero_le _⟩
          have ec : c = (b, 0) :=
            Net.Conn.det hG r.end_left hEc r.end_right ⟨v, p, w'⟩ r.conn
          have eb : c.1 = b := congrArg Prod.fst ec
          have hb' : M.toMach.goal.agent c.1 β := by
            rw [eb]
            exact r.hb
          have eβ : β' = β := hG.agent_fun (memG (assoc_mem hq.2)) hb'
          have eα : α = α₀ := hS.2.1 α r.ha
          apply hc
          rw [eb, eβ, ← eα]
          exact ⟨r.ne, XSys.rule_isSome r⟩
      | none =>
        cases hns : nextSeg M.mem.wires c p with
        | some q =>
          obtain ⟨hl, hqp⟩ := nextSeg_spec hns
          have hlG : M.toMach.goal.link c q := .inl hl
          obtain ⟨vs, tr⟩ := hS.2.2.2
          exact zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_seek_next hsc hns))
            ⟨hS.1, hS.2.1, hS.2.2.1, p :: vs, .step tr hlG
              (Trail.fresh hG.symm hG.irrefl hG.deg hS.2.2.1 tr hlG hqp)⟩ (fun x => x)
            fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
        | none =>
          refine zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_seek_stop hsc hns))
            trivial (fun x => x)
            (hL.ans_of_fail (T := ⟨todo, .seek a₀ α₀ p c, again⟩) rfl (fun x => x) ?_)
          intro a b α β R r htg
          have ea : a = a₀ := (Option.some.inj htg).symm
          subst ea
          by_cases hEc : M.toMach.goal.End xs.sys.ar c
          · have ec : c = (b, 0) :=
              Net.Conn.det hG r.end_left hEc r.end_right ⟨v, p, w'⟩ r.conn
            have hnb : (b, β) ∉ M.mem.agents := by
              intro hm
              rw [ec, ite_pos' rfl] at hsc
              have hsc' : assoc b M.mem.agents = none := hsc
              rw [assocG hm] at hsc'
              cases hsc'
            exact hL.ans_of_agent ht (.inr ⟨rfl, rfl⟩) r.hb hnb (fun x => x) (fun x => x) _
          · obtain ⟨v₂, x₂, w₂⟩ := r.conn
            have ev : v₂ = v := hG.end_unique r.end_left w₂.link_first w'.link_first
            subst ev
            obtain ⟨q, hq, hqp, hqy⟩ := Walk.extend' hG.wiring w' w₂ hEc r.end_right
            refine hL.ans_of_link ht r hq (fun hm => ?_) (fun x => x) ?_ _
            · exact nextSeg_ne_none hm hqp hns
            · intro z hz hE
              rcases hz with ez | ez
              · rw [ez] at hE
                exact absurd hE hEc
              · rw [ez] at hE ⊢
                exact .inr (hqy hE)
    | ready a₀ b₀ α₀ β₀ =>
      by_cases ha : assoc a₀ M.mem.agents = some α₀
      · exact zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_ready ha)) hS
          (fun x => x) fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
      · refine zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_ready_neg ha))
          trivial (fun x => x)
          (hL.ans_of_fail (T := ⟨todo, .ready a₀ b₀ α₀ β₀, again⟩) rfl (fun x => x) ?_)
        intro a b α β R r htg
        have ea : a = a₀ := (Option.some.inj htg).symm
        subst ea
        have eα : α = α₀ := (hS.2 α r.ha).1
        subst eα
        exact hL.ans_of_agent ht (.inl ⟨rfl, rfl⟩) r.ha (fun hm => ha (assocG hm))
          (fun x => x) (fun x => x) _
    | half a₀ b₀ α₀ β₀ =>
      cases hh : (if assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ then xs.rule α₀ β₀
          else none) with
      | some R => exact hL.step_claim ht rfl hh
      | none =>
        refine zero (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_half_none hh))
          trivial (fun x => x)
          (hL.ans_of_fail (T := ⟨todo, .half a₀ b₀ α₀ β₀, again⟩) rfl (fun x => x) ?_)
        intro a b α β R r htg
        have ea : a = a₀ := (Option.some.inj htg).symm
        subst ea
        obtain ⟨eα, hb₀⟩ := hS.2 α r.ha
        subst eα
        obtain ⟨v, x, w⟩ := hok.1
        have hEb₀ : M.toMach.goal.End xs.sys.ar (b₀, 0) := .inr ⟨β₀, hb₀, Nat.zero_le _⟩
        have eb : b = b₀ := (congrArg Prod.fst
          (Net.Conn.det hG r.end_left hEb₀ r.end_right ⟨v, x, hL.lift w⟩ r.conn)).symm
        subst eb
        have eβ : β = β₀ := hG.agent_fun r.hb hb₀
        subst eβ
        have hnb : (b, β) ∉ M.mem.agents := by
          intro hm
          rw [ite_pos' ⟨assocG hm, r.ne⟩] at hh
          have h1 := XSys.rule_isSome r
          rw [hh] at h1
          cases h1
        exact hL.ans_of_agent ht (.inr ⟨rfl, rfl⟩) r.hb hnb (fun x => r.ne x.1.symm)
          (fun x => x) _
    | write as ls =>
      have keep : ∀ a b α β, WThread.Answers ⟨todo, .write as ls, again⟩ a b α β →
          ∀ as' ls', WThread.Answers ⟨todo, .write as' ls', again⟩ a b α β := by
        intro a b α β hA as' ls'
        rcases hA with hw | hm | hm | htg | htg
        · exact .inl ⟨trivial, hw.2⟩
        · exact .inr (.inl hm)
        · exact .inr (.inr (.inl hm))
        · cases htg
        · cases htg
      cases ls with
      | cons l ls =>
        obtain ⟨p, q⟩ := l
        refine hL.step_zero ht rfl trivial (fun i γ h => hL.kids t _ ht i γ h) ?_
          fun a b α β R _ hA => .inl (keep a b α β hA as ls)
        intro hag p' q' hp
        obtain ⟨i, γ, k, h1, h2, h3⟩ :=
          hL.own t _ ht hag p' q' (List.mem_cons_of_mem _ hp)
        exact ⟨i, γ, k, h1, h2, h3⟩
      | nil =>
        cases as with
        | cons e as =>
          obtain ⟨i, γ⟩ := e
          refine hL.step_zero ht rfl trivial
            (fun i' γ' h => hL.kids t _ ht i' γ' (List.mem_cons_of_mem _ h))
            (fun _ p q h => absurd h List.not_mem_nil)
            fun a b α β R _ hA => .inl (keep a b α β hA as [])
        | nil =>
          cases hag : again with
          | true =>
            have hact : WMach.act xs M.mem ⟨todo, .write [] [], again⟩ =
                (M.mem, ⟨M.mem.agents, .idle, false⟩, 0) := by
              unfold WMach.act
              dsimp only
              rw [hag]
              rfl
            refine hL.step_zero ht hact trivial (fun i γ h => False.elim h)
              (fun _ p q h => False.elim h) ?_
            intro a b α β R r _
            by_cases hm : (a, α) ∈ M.mem.agents
            · exact .inl (.inr (.inl hm))
            · exact hL.ans_of_agent ht (.inl ⟨rfl, rfl⟩) r.ha hm (fun x => x)
                (fun x => List.not_mem_nil x) _
          | false =>
            have hact : WMach.act xs M.mem ⟨todo, .write [] [], again⟩ =
                (M.mem, ⟨todo, .idle, false⟩, 0) := by
              unfold WMach.act
              dsimp only
              rw [hag]
              rfl
            refine hL.step_zero ht hact trivial (fun i γ h => False.elim h)
              (fun _ p q h => False.elim h) ?_
            intro a b α β R r hA
            rcases hA with hw | hm | hm | htg | htg
            · rw [hag] at hw
              cases hw.2
            · exact .inl (.inr (.inl hm))
            · exact .inl (.inr (.inr (.inl hm)))
            · cases htg
            · cases htg

/-- The invariant holds along every run. -/
theorem WMach.exec_live : ∀ (σ : List Nat) {M : WMach S}, M.Live xs → (M.exec xs σ).1.Live xs
  | [], _, h => h
  | t :: σ, _, h => WMach.exec_live σ (WMach.step_live h t)

omit [DecidableEq S] in
theorem WMach.init_thread (X : XNet S) {nt u : Nat} (hu : u < nt) :
    (WMach.init X nt).ths[u]? = some ⟨X.agents.drop u ++ X.agents.take u, .idle, false⟩ := by
  show ((List.range nt).map fun t =>
    (⟨X.agents.drop t ++ X.agents.take t, .idle, false⟩ : WThread S))[u]? = _
  rw [List.getElem?_map, List.getElem?_range hu]
  rfl

omit [DecidableEq S] in
theorem WMach.init_live {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt) :
    (WMach.init X nt).Live xs := by
  have e : (WMach.init X nt).toMach = Mach.init X.toNet := WMach.init_toMach X nt
  have eg : (WMach.init X nt).toMach.goal = X.toNet := by
    rw [e]
    exact congrArg CState.goal (Mach.init_quiet X.toNet).abs
  have idle : ∀ {u : Nat} {U : WThread S}, (WMach.init X nt).ths[u]? = some U →
      U.st = .idle := by
    intro u U hu
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hu)
    rfl
  refine ⟨by rw [e]; exact Mach.init_inv hX, ?_, ?_, ?_, ?_⟩
  · intro a b α β R r
    rw [eg] at r
    exact ⟨0, _, WMach.init_thread X hnt, .inr (.inl (List.mem_append_left _ r.ha))⟩
  · intro u U hu
    rw [idle hu]
    trivial
  · intro u U hu i γ h
    rw [idle hu] at h
    exact False.elim h
  · intro u U hu _ p q h
    rw [idle hu] at h
    exact False.elim h

omit [DecidableEq S] in
/-- **The threads do not all rest while there is work.**  When every thread
is idle with an empty list, the memory holds no active pair with a rule. -/
theorem WMach.Live.rest {M : WMach S} (hL : M.Live xs) (hr : M.resting = true) :
    M.toMach.Quiet ∧ Normal (Step xs.sys) M.mem.toNet := by
  have hall : ∀ T, T ∈ M.ths → T.todo = [] ∧ T.st = .idle := by
    intro T hT
    have h : (T.todo.isEmpty && T.st.isIdle) = true := List.all_eq_true.1 hr T hT
    obtain ⟨todo, st, again⟩ := T
    cases todo with
    | cons e rest => cases h
    | nil =>
      cases st with
      | idle => exact ⟨rfl, rfl⟩
      | look a α => cases h
      | seek a α p c => cases h
      | ready a b α β => cases h
      | half a b α β => cases h
      | write as ls => cases h
  have hq : M.toMach.Quiet := by
    intro u
    show threadOf (M.ths.map WThread.toX) u = .idle
    unfold threadOf
    split
    · rename_i T hT
      obtain ⟨U, hU, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hT)
      exact (hall U hU).2
    · rfl
  refine ⟨hq, ?_⟩
  have eg : M.toMach.goal = M.mem.toNet := congrArg CState.goal hq.abs
  rintro N' ⟨a, b, α, β, R, r, -⟩
  rw [← eg] at r
  obtain ⟨t, T, ht, hA⟩ := hL.cov a b α β R r
  obtain ⟨h₁, h₂⟩ := hall T (List.mem_of_getElem? ht)
  rcases hA with hw | hm | hm | htg | htg
  · rw [h₂] at hw
    exact hw.1
  · rw [h₁] at hm
    exact absurd hm List.not_mem_nil
  · rw [h₁] at hm
    exact absurd hm List.not_mem_nil
  · rw [h₂] at htg
    cases htg
  · rw [h₂] at htg
    cases htg

/-- **A run that ends with every thread at rest has computed the normal
form**, whatever the schedule and the number of threads: the memory holds
the normal form, and the claims are as many as the steps of the sequential
reduction. -/
theorem WMach.exec_rest {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : List Nat)
    (hr : ((WMach.init X nt).exec xs σ).1.resting = true) :
    ((WMach.init X nt).exec xs σ).2 = n ∧ ((WMach.init X nt).exec xs σ).1.mem.toNet = N' := by
  obtain ⟨hq, hnorm⟩ := (WMach.exec_live σ (WMach.init_live hX hnt)).rest hr
  obtain ⟨-, hu⟩ := (WMach.exec_mrun xs X nt σ).final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨e₂.symm, e₁.symm⟩

end WLive

end INet
