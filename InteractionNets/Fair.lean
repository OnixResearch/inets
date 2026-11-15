import InteractionNets.Program

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### The threads cannot all rest too early

Under any schedule, with attempts of different threads overlapping in any
way, the threads cannot all come to rest while an active pair with a rule is
left.  The invariant: for every such pair of the goal, some thread still
answers for it.  It is writing (and will take a fresh list of agents), or
one of the two agents is in its list, or it is in the middle of an attempt
on one of them.  When an attempt on an agent fails, it is because of
another thread, which holds the other agent or has not finished writing the
wire between them, and that thread answers for the pair from then on. -/

section Live

/-- The agent a thread is attempting. -/
def TState.target : TState S → Option Id
  | .look a _ => some a
  | .seek a _ _ _ => some a
  | .ready a _ _ _ => some a
  | .half a _ _ _ => some a
  | _ => none

/-- The thread has claimed a pair and is writing. -/
def TState.writing : TState S → Prop
  | .write _ _ => True
  | _ => False

/-- What a thread in the middle of an attempt has read stays true of the
goal: the agent it attempts, if it is still there, carries the symbol it
read, and then so does the partner it found.  The principal port it started
from lies on one segment only, and the ports it has visited form a trail. -/
def TState.Sane (G : Net S) : TState S → Prop
  | .look a α => G.Used a ∧ (∀ α', G.agent a α' → α' = α) ∧
      ∀ q q', G.link (a, 0) q → G.link (a, 0) q' → q = q'
  | .seek a α p c => G.Used a ∧ (∀ α', G.agent a α' → α' = α) ∧
      (∀ q q', G.link (a, 0) q → G.link (a, 0) q' → q = q') ∧
      ∃ vs, Trail G.link (a, 0) (c :: p :: vs)
  | .ready a b α β => G.Used a ∧ ∀ α', G.agent a α' → α' = α ∧ G.agent b β
  | .half a b α β => G.Used a ∧ ∀ α', G.agent a α' → α' = α ∧ G.agent b β
  | _ => True

theorem TState.held_target {s : TState S} {i : Id} {γ : S} (h : s.held i γ) :
    s.target = some i := by
  cases s with
  | half a b α β =>
    obtain ⟨e, -⟩ := h
    rw [e]
    rfl
  | idle => exact False.elim h
  | look a α => exact False.elim h
  | seek a α p c => exact False.elim h
  | ready a b α β => exact False.elim h
  | write as ls => exact False.elim h

theorem TState.pendA_writing {s : TState S} {i : Id} {γ : S} (h : s.pendA i γ) : s.writing := by
  cases s with
  | write as ls => trivial
  | idle => exact False.elim h
  | look a α => exact False.elim h
  | seek a α p c => exact False.elim h
  | ready a b α β => exact False.elim h
  | half a b α β => exact False.elim h

theorem TState.pendL_writing {s : TState S} {p q : Port} (h : s.pendL p q) : s.writing := by
  cases s with
  | write as ls => trivial
  | idle => exact False.elim h
  | look a α => exact False.elim h
  | seek a α p c => exact False.elim h
  | ready a b α β => exact False.elim h
  | half a b α β => exact False.elim h

theorem TState.sane_of_writing {s : TState S} (G : Net S) (h : s.writing) : s.Sane G := by
  cases s with
  | write as ls => trivial
  | idle => trivial
  | look a α => exact False.elim h
  | seek a α p c => exact False.elim h
  | ready a b α β => exact False.elim h
  | half a b α β => exact False.elim h

/-- A claim by another thread does not disturb what a thread has read. -/
theorem TState.Sane.fire {G m : Net S} {s : TState S} (hG : G.WF sys.ar)
    (hm : ∀ {p q}, m.link p q → G.link p q) {c d : Id} {γ δ : S} {R : Rhs S}
    (r : Redex sys G c d γ δ R) (hok : s.Ok m) (hs : s.Sane G) : s.Sane (G.fire c d R) := by
  have site : Site sys.ar G c d γ δ := ⟨hG, r.ha, r.hb, r.ne, r.conn⟩
  have key : ∀ {a : Id}, G.Used a → ∀ α', (G.fire c d R).agent a α' →
      G.agent a α' ∧ a ≠ c ∧ a ≠ d := by
    intro a hU α' h'
    rcases h' with h' | ⟨o, j, e, -⟩
    · exact h'
    · exact absurd (e ▸ hU) (site.not_used_child o j)
  have part : ∀ (a b : Id) (α β : S), G.Used a →
      (∀ α', G.agent a α' → α' = α ∧ G.agent b β) →
      Conn m.link (fun _ => False) (a, 0) (b, 0) →
      ∀ α', (G.fire c d R).agent a α' → α' = α ∧ (G.fire c d R).agent b β := by
    intro a b α β hU h₀ hc α' h'
    obtain ⟨h₁, hac, had⟩ := key hU α' h'
    obtain ⟨eα, hb⟩ := h₀ α' h₁
    obtain ⟨v, x, w⟩ := hc
    have conn : G.Conn sys.ar (a, 0) (b, 0) :=
      ⟨v, x, w.mono_term hm hm hG.symm (fun hT => hT) hG.end_unique⟩
    have hEa : G.End sys.ar (a, 0) := .inr ⟨α', h₁, Nat.zero_le _⟩
    have hEb : G.End sys.ar (b, 0) := .inr ⟨β, hb, Nat.zero_le _⟩
    refine ⟨eα, .inl ⟨hb, fun hbc => ?_, fun hbd => ?_⟩⟩
    · have r1 : G.Conn sys.ar (b, 0) (d, 0) := by
        rw [hbc]
        exact r.conn
      exact had (congrArg Prod.fst
        (Net.Conn.det hG hEb hEa r.end_right (Net.Conn.symm hG conn) r1))
    · have r1 : G.Conn sys.ar (b, 0) (c, 0) := by
        rw [hbd]
        exact Net.Conn.symm hG r.conn
      exact hac (congrArg Prod.fst
        (Net.Conn.det hG hEb hEa r.end_left (Net.Conn.symm hG conn) r1))
  have old : ∀ {a : Id}, G.Used a → ∀ q, (G.fire c d R).link (a, 0) q → G.link (a, 0) q := by
    intro a hU q h'
    rcases h' with h' | ⟨x, y, -, e, -⟩
    · exact h'
    · cases x with
      | ifc s k =>
        have e2 : (0 : Nat) = k + 1 := congrArg Prod.snd e
        omega
      | new o j k =>
        have e1 : a = child c d o j := congrArg Prod.fst e
        exact absurd (e1 ▸ hU) (site.not_used_child o j)
  cases s with
  | idle => trivial
  | write as ls => trivial
  | look a α =>
    exact ⟨Net.used_fire hG hs.1 c d R, fun α' h' => hs.2.1 α' (key hs.1 α' h').1,
      fun q q' h h' => hs.2.2 q q' (old hs.1 q h) (old hs.1 q' h')⟩
  | seek a α p q =>
    obtain ⟨vs, tr⟩ := hs.2.2.2
    exact ⟨Net.used_fire hG hs.1 c d R, fun α' h' => hs.2.1 α' (key hs.1 α' h').1,
      fun q₁ q₂ h h' => hs.2.2.1 q₁ q₂ (old hs.1 q₁ h) (old hs.1 q₂ h'),
      vs, tr.mono fun h => .inl h⟩
  | ready a b α β => exact ⟨Net.used_fire hG hs.1 c d R, part a b α β hs.1 hs.2 hok⟩
  | half a b α β => exact ⟨Net.used_fire hG hs.1 c d R, part a b α β hs.1 hs.2 hok.1⟩

/-- The thread answers for the pair of `a` and `b`: it is writing, or one
of the two is in its list, or it is attempting one of them. -/
def XThread.Answers (T : XThread S) (a b : Id) (α β : S) : Prop :=
  T.st.writing ∨ (a, α) ∈ T.todo ∨ (b, β) ∈ T.todo ∨ T.st.target = some a ∨
    T.st.target = some b

theorem XThread.Answers.symm {T : XThread S} {a b : Id} {α β : S} (h : T.Answers a b α β) :
    T.Answers b a β α := by
  rcases h with h | h | h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr (.inr h)))
  · exact .inr (.inr (.inr (.inl h)))

theorem XThread.Answers.carry {T T₁ : XThread S} {a b : Id} {α β : S}
    (h : T.Answers a b α β) (hT₁ : T₁.todo = T.todo) (htg : T₁.st.target = T.st.target)
    (hnw : ¬ T.st.writing) : T₁.Answers a b α β := by
  rcases h with h | h | h | h | h
  · exact absurd h hnw
  · exact .inr (.inl (by rw [hT₁]; exact h))
  · exact .inr (.inr (.inl (by rw [hT₁]; exact h)))
  · exact .inr (.inr (.inr (.inl (htg.trans h))))
  · exact .inr (.inr (.inr (.inr (htg.trans h))))

/-- After an action of thread `t`, which leaves it in state `T₁`, someone
answers for the pair: that thread, or another one. -/
def NewAns (ths : List (XThread S)) (t : Nat) (T₁ : XThread S) (a b : Id) (α β : S) : Prop :=
  T₁.Answers a b α β ∨
    ∃ (u : Nat) (U : XThread S), u ≠ t ∧ ths[u]? = some U ∧ U.Answers a b α β

theorem NewAns.symm {ths : List (XThread S)} {t : Nat} {T₁ : XThread S} {a b : Id} {α β : S}
    (h : NewAns ths t T₁ a b α β) : NewAns ths t T₁ b a β α := by
  rcases h with h | ⟨u, U, hne, hu, hA⟩
  · exact .inl h.symm
  · exact .inr ⟨u, U, hne, hu, hA.symm⟩

theorem threadOf_some {ths : List (XThread S)} {u : Nat} {P : TState S → Prop}
    (h : P (threadOf ths u)) (hi : ¬ P .idle) : ∃ U, ths[u]? = some U ∧ P U.st := by
  unfold threadOf at h
  cases hu : ths[u]? with
  | none =>
    rw [hu] at h
    exact absurd h hi
  | some U =>
    rw [hu] at h
    exact ⟨U, rfl, h⟩

/-- An agent of the goal is in memory, or held by a thread, or still to be
written by one. -/
theorem XMach.goal_agent {M : XMach S} {i : Id} {γ : S} (h : M.toMach.goal.agent i γ) :
    (i, γ) ∈ M.mem.agents ∨
      (∃ (u : Nat) (U : XThread S), M.ths[u]? = some U ∧ U.st.held i γ) ∨
      ∃ (u : Nat) (U : XThread S), M.ths[u]? = some U ∧ U.st.pendA i γ := by
  rcases h with (hm | ⟨u, hh⟩) | ⟨u, hp⟩
  · exact .inl hm
  · obtain ⟨U, hu, hU⟩ := threadOf_some (P := fun s => s.held i γ) hh (fun x => x)
    exact .inr (.inl ⟨u, U, hu, hU⟩)
  · obtain ⟨U, hu, hU⟩ := threadOf_some (P := fun s => s.pendA i γ) hp (fun x => x)
    exact .inr (.inr ⟨u, U, hu, hU⟩)

theorem XMach.goal_link {M : XMach S} {p q : Port} (h : M.toMach.goal.link p q) :
    (p, q) ∈ M.mem.wires ∨
      ∃ (u : Nat) (U : XThread S), M.ths[u]? = some U ∧ U.st.pendL p q := by
  rcases h with hm | ⟨u, hp⟩
  · exact .inl hm
  · obtain ⟨U, hu, hU⟩ := threadOf_some (P := fun s => s.pendL p q) hp (fun x => x)
    exact .inr ⟨u, U, hu, hU⟩

/-- An agent of the pair that is not in memory is held or still to be
written by another thread, which answers for the pair. -/
theorem ans_of_agent {M : XMach S} {t : Nat} {T : XThread S} (ht : M.ths[t]? = some T)
    {a b : Id} {α β : S} {i : Id} {γ : S} (hi : i = a ∨ i = b)
    (hg : M.toMach.goal.agent i γ) (hnm : (i, γ) ∉ M.mem.agents) (hT : ¬ T.st.held i γ)
    (hTp : ¬ T.st.pendA i γ) (T₁ : XThread S) : NewAns M.ths t T₁ a b α β := by
  rcases XMach.goal_agent hg with hm | ⟨u, U, hu, hU⟩ | ⟨u, U, hu, hU⟩
  · exact absurd hm hnm
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hT (Option.some.inj hu ▸ hU)
    refine .inr ⟨u, U, hne, hu, ?_⟩
    rcases hi with e | e
    · exact .inr (.inr (.inr (.inl (e ▸ TState.held_target hU))))
    · exact .inr (.inr (.inr (.inr (e ▸ TState.held_target hU))))
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hTp (Option.some.inj hu ▸ hU)
    exact .inr ⟨u, U, hne, hu, .inl (TState.pendA_writing hU)⟩

/-- A segment of the goal that is not in memory is still to be written by
another thread, which answers for every pair. -/
theorem ans_of_link {M : XMach S} {t : Nat} {T : XThread S} (ht : M.ths[t]? = some T)
    {a b : Id} {α β : S} {p q : Port} (hg : M.toMach.goal.link p q)
    (hnm : (p, q) ∉ M.mem.wires) (hTp : ¬ T.st.pendL p q) (T₁ : XThread S) :
    NewAns M.ths t T₁ a b α β := by
  rcases XMach.goal_link hg with hm | ⟨u, U, hu, hU⟩
  · exact absurd hm hnm
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hTp (Option.some.inj hu ▸ hU)
    exact .inr ⟨u, U, hne, hu, .inl (TState.pendL_writing hU)⟩

variable {xs : XSys S}

/-- The invariant: the machine it stands for satisfies its own invariant,
every active pair of the goal that has a rule is answered for, and what the
threads have read is still true. -/
structure XMach.Live (xs : XSys S) (M : XMach S) : Prop where
  inv : M.toMach.Inv xs.sys
  cov : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
    ∃ (t : Nat) (T : XThread S), M.ths[t]? = some T ∧ T.Answers a b α β
  sane : ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T → T.st.Sane M.toMach.goal

theorem XMach.Live.ok {M : XMach S} (hL : M.Live xs) {t : Nat} {T : XThread S}
    (ht : M.ths[t]? = some T) : T.st.Ok M.mem.toNet := by
  have h : (threadOf M.ths t).Ok M.mem.toNet := hL.inv.ok t
  rw [threadOf_eq ht] at h
  exact h

theorem XMach.Live.lift {M : XMach S} (hL : M.Live xs) {u v x y : Port}
    (w : Walk M.mem.toNet.link (fun _ => False) u v x y) :
    Walk M.toMach.goal.link (M.toMach.goal.End xs.sys.ar) u v x y :=
  w.mono_term (fun hl => .inl hl) (fun hl => .inl hl) hL.inv.wf.symm (fun hT => hT)
    hL.inv.wf.end_unique

theorem XSys.rule_isSome {N : Net S} {a b : Id} {α β : S} {R : Rhs S}
    (r : Redex xs.sys N a b α β R) : (xs.rule α β).isSome := by
  have h := r.rule
  rw [xs.rule_spec] at h
  cases hx : xs.rule α β with
  | none =>
    rw [hx] at h
    cases h
  | some R' => rfl

/-- When an attempt fails, the pairs the thread answered for through its
list are still answered for by it; only the agent it was attempting needs
another answer. -/
theorem XMach.ans_of_fail {M : XMach S} (hL : M.Live xs) {t : Nat} {T T₁ : XThread S}
    (hT₁ : T₁.todo = T.todo) (hnw : ¬ T.st.writing)
    (h : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R → T.st.target = some a →
      NewAns M.ths t T₁ a b α β) :
    ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R → T.Answers a b α β →
      NewAns M.ths t T₁ a b α β := by
  intro a b α β R r hA
  rcases hA with hw | hm | hm | htg | htg
  · exact absurd hw hnw
  · exact .inl (.inr (.inl (by rw [hT₁]; exact hm)))
  · exact .inl (.inr (.inr (.inl (by rw [hT₁]; exact hm))))
  · exact h a b α β R r htg
  · obtain ⟨R', r', -⟩ := r.flip hL.inv.wf
    exact (h b a β α R' r' htg).symm

theorem nextSeg_ne_none : ∀ {ws : List (Port × Port)} {c p q : Port}, (c, q) ∈ ws → q ≠ p →
    nextSeg ws c p ≠ none
  | [], _, _, _, h, _ => absurd h List.not_mem_nil
  | e :: ws, c, p, q, h, hq => by
    unfold nextSeg
    split
    · intro x
      cases x
    · rename_i hc
      rcases List.mem_cons.1 h with he | h'
      · have h1 : e.1 = c := congrArg Prod.fst he.symm
        have h2 : e.2 = q := congrArg Prod.snd he.symm
        exact absurd ⟨h1, fun h3 => hq (h2 ▸ h3)⟩ hc
      · exact nextSeg_ne_none h' hq

variable [DecidableEq S]

theorem XMach.act_look_none {X : XNet S} {todo : List (Id × S)} {a : Id} {α : S}
    (h : assoc (a, 0) X.wires = none) :
    XMach.act xs X ⟨todo, .look a α⟩ = (X, ⟨todo, .idle⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i q' hq'
    rw [h] at hq'
    cases hq'
  · rfl

theorem XMach.act_ready_neg {X : XNet S} {todo : List (Id × S)} {a b : Id} {α β : S}
    (h : ¬ assoc a X.agents = some α) :
    XMach.act xs X ⟨todo, .ready a b α β⟩ = (X, ⟨todo, .idle⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i hp
    exact absurd hp h
  · rfl

theorem XMach.act_half_none {X : XNet S} {todo : List (Id × S)} {a b : Id} {α β : S}
    (h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = none) :
    XMach.act xs X ⟨todo, .half a b α β⟩ = (X.putAgent a α, ⟨todo, .idle⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i R' hR'
    rw [h] at hR'
    cases hR'
  · rfl

theorem XMach.step_eq {M : XMach S} {t : Nat} {T T₁ : XThread S} {X₁ : XNet S} {c : Nat}
    (ht : M.ths[t]? = some T) (hact : XMach.act xs M.mem T = (X₁, T₁, c)) :
    M.step xs t = (⟨X₁, M.ths.set t T₁⟩, c) := by
  unfold XMach.step
  rw [ht]
  dsimp only
  rw [hact]

/-- An action that makes no claim keeps the invariant, if the thread is
still answered for. -/
theorem XMach.Live.step_zero {M : XMach S} (hL : M.Live xs) {t : Nat} {T T₁ : XThread S}
    {X₁ : XNet S} (ht : M.ths[t]? = some T) (hact : XMach.act xs M.mem T = (X₁, T₁, 0))
    (hsane : T₁.st.Sane M.toMach.goal)
    (hans : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R → T.Answers a b α β →
      NewAns M.ths t T₁ a b α β) : (M.step xs t).1.Live xs := by
  have es := XMach.step_eq ht hact
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
  have hbase : (XMach.toMach ⟨X₁, M.ths.set t T₁⟩).Inv xs.sys ∧
      (XMach.toMach ⟨X₁, M.ths.set t T₁⟩).goal = M.toMach.goal := by
    have h := XMach.step_sim xs M t
    rw [es] at h
    rcases h with ⟨e₁, -⟩ | hs
    · have e₁' : XMach.toMach ⟨X₁, M.ths.set t T₁⟩ = M.toMach := e₁
      rw [e₁']
      exact ⟨hL.inv, rfl⟩
    · obtain ⟨hi, hr⟩ := MStep.sim hL.inv hs
      exact ⟨hi, hr.goal_zero rfl⟩
  obtain ⟨hinv, hg⟩ := hbase
  rw [es]
  show XMach.Live xs ⟨X₁, M.ths.set t T₁⟩
  refine ⟨hinv, ?_, ?_⟩
  · intro a b α β R r
    rw [hg] at r
    show ∃ (u : Nat) (U : XThread S), (M.ths.set t T₁)[u]? = some U ∧ U.Answers a b α β
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
    have hu' : (M.ths.set t T₁)[u]? = some U := hu
    by_cases hut : u = t
    · rw [hut, List.getElem?_set_self hlt] at hu'
      rw [← Option.some.inj hu']
      exact hsane
    · rw [List.getElem?_set_ne (Ne.symm hut)] at hu'
      exact hL.sane u U hu'

/-- A claim keeps the invariant: the thread that made it answers for every
pair. -/
theorem XMach.Live.step_claim {M : XMach S} (hL : M.Live xs) {t : Nat} {T T₁ : XThread S}
    {X₁ : XNet S} (ht : M.ths[t]? = some T) (hact : XMach.act xs M.mem T = (X₁, T₁, 1))
    (hw : T₁.st.writing) : (M.step xs t).1.Live xs := by
  have es := XMach.step_eq ht hact
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
  have h := XMach.step_sim xs M t
  rw [es] at h
  rcases h with ⟨-, e₂⟩ | hs
  · have e₂' : (1 : Nat) = 0 := e₂
    omega
  · obtain ⟨hinv, hr⟩ := MStep.sim hL.inv hs
    obtain ⟨a, b, α, β, R, r, eg⟩ := hr.one_claim rfl hL.inv.sound
    have eg' : (XMach.toMach ⟨X₁, M.ths.set t T₁⟩).goal = M.toMach.goal.fire a b R := eg
    rw [es]
    show XMach.Live xs ⟨X₁, M.ths.set t T₁⟩
    refine ⟨hinv, fun a' b' α' β' R' _ => ⟨t, T₁, List.getElem?_set_self hlt, .inl hw⟩, ?_⟩
    intro u U hu
    rw [eg']
    have hu' : (M.ths.set t T₁)[u]? = some U := hu
    by_cases hut : u = t
    · rw [hut, List.getElem?_set_self hlt] at hu'
      rw [← Option.some.inj hu']
      exact TState.sane_of_writing _ hw
    · rw [List.getElem?_set_ne (Ne.symm hut)] at hu'
      exact TState.Sane.fire hL.inv.wf (fun hl => .inl hl) r (hL.ok hu') (hL.sane u U hu')

/-- **Every action keeps the invariant.** -/
theorem XMach.step_live {M : XMach S} (hL : M.Live xs) (t : Nat) :
    (M.step xs t).1.Live xs := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold XMach.step
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
    obtain ⟨todo, s⟩ := T
    cases s with
    | idle =>
      cases todo with
      | nil => exact hL.step_zero ht rfl trivial fun a b α β R _ hA => .inl hA
      | cons e rest =>
        by_cases he : assoc e.1 M.mem.agents = some e.2
        · refine hL.step_zero ht (XMach.act_idle_pos he)
            ⟨.inl ⟨e.2, memG (assoc_mem he)⟩,
              fun α' h' => hG.agent_fun h' (memG (assoc_mem he)),
              fun q q' h h' => hG.end_unique
                (.inr ⟨e.2, memG (assoc_mem he), Nat.zero_le _⟩) h h'⟩ ?_
          intro a b α β R _ hA
          rcases hA with hw | hm | hm | htg | htg
          · exact False.elim hw
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
        · refine hL.step_zero ht (XMach.act_idle_neg he) trivial ?_
          intro a b α β R r hA
          rcases hA with hw | hm | hm | htg | htg
          · exact False.elim hw
          · rcases List.mem_cons.1 hm with heq | hm
            · have hnm : (a, α) ∉ M.mem.agents := fun h => he (by rw [← heq]; exact assocG h)
              exact ans_of_agent ht (.inl rfl) r.ha hnm (fun x => x) (fun x => x) _
            · exact .inl (.inr (.inl hm))
          · rcases List.mem_cons.1 hm with heq | hm
            · have hnm : (b, β) ∉ M.mem.agents := fun h => he (by rw [← heq]; exact assocG h)
              exact ans_of_agent ht (.inr rfl) r.hb hnm (fun x => x) (fun x => x) _
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
        exact hL.step_zero ht (XMach.act_look hv)
          ⟨hS.1, hS.2.1, hS.2.2, [], .step .start hl hf⟩
          fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
      | none =>
        refine hL.step_zero ht (XMach.act_look_none hv) trivial
          (XMach.ans_of_fail hL (T := ⟨todo, .look a₀ α₀⟩) rfl
            (fun x => x) ?_)
        intro a b α β R r htg
        have ea : a = a₀ := (Option.some.inj htg).symm
        subst ea
        obtain ⟨q, hq⟩ := hG.end_wired r.end_left
        refine ans_of_link ht hq (fun hm => ?_) (fun x => x) _
        obtain ⟨q', e'⟩ := assoc_of_mem hm
        rw [hv] at e'
        cases e'
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
        · exact hL.step_zero ht (XMach.act_seek_found hsc hc)
            ⟨hS.1, fun α' h' => ⟨hS.2.1 α' h', memG (assoc_mem hq.2)⟩⟩
            fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
        · refine hL.step_zero ht (XMach.act_seek_norule hsc hc) trivial
            (XMach.ans_of_fail hL (T := ⟨todo, .seek a₀ α₀ p c⟩) rfl
            (fun x => x) ?_)
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
          exact hL.step_zero ht (XMach.act_seek_next hsc hns)
            ⟨hS.1, hS.2.1, hS.2.2.1, p :: vs, .step tr hlG
              (Trail.fresh hG.symm hG.irrefl hG.deg hS.2.2.1 tr hlG hqp)⟩
            fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
        | none =>
          refine hL.step_zero ht (XMach.act_seek_stop hsc hns) trivial
            (XMach.ans_of_fail hL (T := ⟨todo, .seek a₀ α₀ p c⟩) rfl
            (fun x => x) ?_)
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
            exact ans_of_agent ht (.inr rfl) r.hb hnb (fun x => x) (fun x => x) _
          · obtain ⟨v₂, x₂, w₂⟩ := r.conn
            have ev : v₂ = v := hG.end_unique r.end_left w₂.link_first w'.link_first
            subst ev
            obtain ⟨q, hq, hqp⟩ := Walk.extend hG.wiring w' w₂ hEc r.end_right
            refine ans_of_link ht hq (fun hm => ?_) (fun x => x) _
            exact nextSeg_ne_none hm hqp hns
    | ready a₀ b₀ α₀ β₀ =>
      by_cases ha : assoc a₀ M.mem.agents = some α₀
      · exact hL.step_zero ht (XMach.act_ready ha) hS
          fun a b α β R _ hA => .inl (hA.carry rfl rfl fun x => x)
      · refine hL.step_zero ht (XMach.act_ready_neg ha) trivial
          (XMach.ans_of_fail hL (T := ⟨todo, .ready a₀ b₀ α₀ β₀⟩) rfl
            (fun x => x) ?_)
        intro a b α β R r htg
        have ea : a = a₀ := (Option.some.inj htg).symm
        subst ea
        have eα : α = α₀ := (hS.2 α r.ha).1
        subst eα
        exact ans_of_agent ht (.inl rfl) r.ha (fun hm => ha (assocG hm)) (fun x => x)
          (fun x => x) _
    | half a₀ b₀ α₀ β₀ =>
      cases hh : (if assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ then xs.rule α₀ β₀
          else none) with
      | some R => exact hL.step_claim ht (XMach.act_half hh) trivial
      | none =>
        refine hL.step_zero ht (XMach.act_half_none hh) trivial
          (XMach.ans_of_fail hL (T := ⟨todo, .half a₀ b₀ α₀ β₀⟩) rfl
            (fun x => x) ?_)
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
        exact ans_of_agent ht (.inr rfl) r.hb hnb (fun x => r.ne x.1.symm) (fun x => x) _
    | write as ls =>
      cases as with
      | cons e as =>
        obtain ⟨i, γ⟩ := e
        exact hL.step_zero ht rfl trivial fun a b α β R _ _ => .inl (.inl trivial)
      | nil =>
        cases ls with
        | cons e ls =>
          obtain ⟨p, q⟩ := e
          exact hL.step_zero ht rfl trivial fun a b α β R _ _ => .inl (.inl trivial)
        | nil =>
          refine hL.step_zero ht rfl trivial ?_
          intro a b α β R r _
          by_cases hm : (a, α) ∈ M.mem.agents
          · exact .inl (.inr (.inl hm))
          · exact ans_of_agent ht (.inl rfl) r.ha hm (fun x => x)
              (fun x => List.not_mem_nil x) _

/-- The invariant holds along every run. -/
theorem XMach.exec_live : ∀ (σ : List Nat) {M : XMach S}, M.Live xs → (M.exec xs σ).1.Live xs
  | [], _, h => h
  | t :: σ, _, h => XMach.exec_live σ (XMach.step_live h t)

omit [DecidableEq S] in
theorem XMach.init_live {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt) :
    (XMach.init X nt).Live xs := by
  have e : (XMach.init X nt).toMach = Mach.init X.toNet := XMach.init_toMach X nt
  have eg : (XMach.init X nt).toMach.goal = X.toNet := by
    rw [e]
    exact congrArg CState.goal (Mach.init_quiet X.toNet).abs
  refine ⟨by rw [e]; exact Mach.init_inv hX, ?_, ?_⟩
  · intro a b α β R r
    rw [eg] at r
    exact ⟨0, _, XMach.init_thread X hnt, .inr (.inl (List.mem_append_left _ r.ha))⟩
  · intro u U hu
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hu)
    trivial

/-- Every thread is idle and has an empty list. -/
def XMach.resting (M : XMach S) : Bool := M.ths.all fun T => T.todo.isEmpty && T.st.isIdle

omit [DecidableEq S] in
/-- **The threads do not all rest while there is work.**  When every thread
is idle with an empty list, the memory holds no active pair with a rule. -/
theorem XMach.Live.rest {M : XMach S} (hL : M.Live xs) (hr : M.resting = true) :
    M.toMach.Quiet ∧ Normal (Step xs.sys) M.mem.toNet := by
  have hall : ∀ T, T ∈ M.ths → T.todo = [] ∧ T.st = .idle := by
    intro T hT
    have h : (T.todo.isEmpty && T.st.isIdle) = true := List.all_eq_true.1 hr T hT
    obtain ⟨todo, st⟩ := T
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
    show threadOf M.ths u = .idle
    unfold threadOf
    split
    · rename_i T hT
      exact (hall T (List.mem_of_getElem? hT)).2
    · rfl
  refine ⟨hq, ?_⟩
  have eg : M.toMach.goal = M.mem.toNet := congrArg CState.goal hq.abs
  rintro N' ⟨a, b, α, β, R, r, -⟩
  rw [← eg] at r
  obtain ⟨t, T, ht, hA⟩ := hL.cov a b α β R r
  obtain ⟨h₁, h₂⟩ := hall T (List.mem_of_getElem? ht)
  rcases hA with hw | hm | hm | htg | htg
  · rw [h₂] at hw
    exact hw
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
theorem XMach.exec_rest {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : List Nat)
    (hr : ((XMach.init X nt).exec xs σ).1.resting = true) :
    ((XMach.init X nt).exec xs σ).2 = n ∧ ((XMach.init X nt).exec xs σ).1.mem.toNet = N' := by
  obtain ⟨hq, hnorm⟩ := (XMach.exec_live σ (XMach.init_live hX hnt)).rest hr
  obtain ⟨-, hu⟩ := (XMach.exec_mrun xs X nt σ).final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨e₂.symm, e₁.symm⟩

/-- The same against the list reducer: a run that ends with every thread at
rest has made as many claims as the list reducer takes steps, and holds its
result once the history is forgotten. -/
theorem XMach.exec_rest_agrees {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) {nt : Nat} (hnt : 0 < nt) (σ : List Nat)
    (hr : ((XMach.init X nt).exec xs σ).1.resting = true) :
    ((XMach.init X nt).exec xs σ).2 = (X.run xs f).2 ∧
      ((XMach.init X nt).exec xs σ).1.mem.toNet.compact xs.sys.ar = (X.run xs f).1.toNet := by
  obtain ⟨sts, -⟩ := XNet.run_steps hX f
  have hn := (XNet.run_normal hX f stop).1
  have sts' : Steps (CStep xs.sys) (X.run xs f).2 (X.toNet.compact xs.sys.ar)
      (X.run xs f).1.toNet := by
    rw [hX.2]
    exact sts
  obtain ⟨N', hs, e⟩ := Steps.lift hX.1 sts'
  have hN' : Normal (Step xs.sys) N' := by
    refine (normal_compact (Steps.wf hX.1 hs)).2 ?_
    rw [← e]
    exact hn
  obtain ⟨h₁, h₂⟩ := XMach.exec_rest hX.1 hnt hs hN' σ hr
  refine ⟨h₁, ?_⟩
  rw [h₂]
  exact e.symm

/-- The segments of the goal, as a list: those in memory and those that the
threads have left to write. -/
def XMach.links (M : XMach S) : List (Port × Port) :=
  M.mem.wires ++ M.ths.flatMap fun T =>
    match T.st with
    | .write _ ls => ls
    | _ => []

omit [DecidableEq S] in
theorem XMach.mem_links {M : XMach S} {p q : Port} (h : M.toMach.goal.link p q) :
    (p, q) ∈ M.links := by
  rcases XMach.goal_link h with hm | ⟨u, U, hu, hU⟩
  · exact List.mem_append_left _ hm
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨U, List.mem_of_getElem? hu, ?_⟩)
    obtain ⟨todo, st⟩ := U
    cases st with
    | write as ls => exact hU
    | idle => exact False.elim hU
    | look a α => exact False.elim hU
    | seek a α p c => exact False.elim hU
    | ready a b α β => exact False.elim hU
    | half a b α β => exact False.elim hU

omit [DecidableEq S] in
/-- **A search is bounded**, under every schedule.  The ports that a thread
has visited while following a wire are linked one to the next and pairwise
distinct, so there are at most as many of them as the goal has segments,
plus one: a thread cannot follow a wire for ever. -/
theorem XMach.Live.seek_bound {M : XMach S} (hL : M.Live xs) {t : Nat} {T : XThread S}
    (ht : M.ths[t]? = some T) {a : Id} {α : S} {p c : Port} (hst : T.st = .seek a α p c) :
    ∃ vs, Trail M.toMach.goal.link (a, 0) (c :: p :: vs) ∧
      (c :: p :: vs).length ≤ M.links.length + 1 := by
  have hS := hL.sane t T ht
  rw [hst] at hS
  obtain ⟨vs, tr⟩ := hS.2.2.2
  exact ⟨vs, tr, tr.length_le M.links fun h => XMach.mem_links h⟩

end Live

/-! ### Under a fair schedule the run comes to rest

The last piece: a number that decreases with every action that is neither a
claim nor the action of a thread at rest.  It adds up, over the threads,
what each still has to do before it is idle with a shorter list: the agents
left in its list, and within an attempt the steps left, a search being
counted by the ports it can still visit.  Claims are at most as many as the
steps of the sequential reduction.  So in a run in which every thread keeps
being scheduled, from some action on every thread is at rest, and then the
memory holds the normal form. -/

section Fair

open Classical in
/-- The largest number up to `B` that satisfies `P`, or `0`. -/
noncomputable def supBelow (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | B + 1 => if P (B + 1) then B + 1 else supBelow P B

theorem supBelow_le (P : Nat → Prop) : ∀ B, supBelow P B ≤ B
  | 0 => Nat.le_refl _
  | B + 1 => by
    unfold supBelow
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (supBelow_le P B)

theorem le_supBelow {P : Nat → Prop} : ∀ {B n : Nat}, P n → n ≤ B → n ≤ supBelow P B
  | 0, n, _, h => h
  | B + 1, n, hP, h => by
    unfold supBelow
    split
    · exact h
    · rename_i hn
      have hne : n ≠ B + 1 := fun e => hn (e ▸ hP)
      exact le_supBelow hP (by omega)

theorem supBelow_spec (P : Nat → Prop) : ∀ B, supBelow P B = 0 ∨ P (supBelow P B)
  | 0 => .inl rfl
  | B + 1 => by
    unfold supBelow
    split
    · rename_i h
      exact .inr h
    · exact supBelow_spec P B

/-- A sum over the threads. -/
def total (f : XThread S → Nat) : List (XThread S) → Nat
  | [] => 0
  | T :: ths => f T + total f ths

theorem total_set (f : XThread S → Nat) : ∀ (ths : List (XThread S)) (t : Nat)
    (T T' : XThread S), ths[t]? = some T → total f (ths.set t T') + f T = total f ths + f T'
  | [], _, _, _, h => by cases h
  | U :: ths, 0, T, T', h => by
    rw [List.getElem?_cons_zero] at h
    rw [Option.some.inj h]
    show f T' + total f ths + f T = f T + total f ths + f T'
    omega
  | U :: ths, t + 1, T, T', h => by
    rw [List.getElem?_cons_succ] at h
    have ih := total_set f ths t T T' h
    show f U + total f (ths.set t T') + f T = f U + total f ths + f T'
    omega

theorem total_le {f g : XThread S → Nat} (h : ∀ U, f U ≤ g U) :
    ∀ ths : List (XThread S), total f ths ≤ total g ths
  | [] => Nat.le_refl _
  | U :: ths => Nat.add_le_add (h U) (total_le h ths)

/-- If one thread's share goes down and no other's goes up, the sum goes
down. -/
theorem total_set_lt {f f' : XThread S → Nat} (h : ∀ U, f' U ≤ f U) :
    ∀ (ths : List (XThread S)) (t : Nat) {T T₁ : XThread S}, ths[t]? = some T →
      f' T₁ < f T → total f' (ths.set t T₁) < total f ths
  | [], _, _, _, ht, _ => by cases ht
  | U :: ths, 0, T, T₁, ht, hlt => by
    rw [List.getElem?_cons_zero] at ht
    rw [← Option.some.inj ht] at hlt
    have := total_le h ths
    show f' T₁ + total f' ths < f U + total f ths
    omega
  | U :: ths, t + 1, T, T₁, ht, hlt => by
    rw [List.getElem?_cons_succ] at ht
    have ih := total_set_lt h ths t ht hlt
    have := h U
    show f' U + total f' (ths.set t T₁) < f U + total f ths
    omega

theorem length_filter_succ_le {A : Type} {p : A → Bool} : ∀ {l : List A} {x : A}, x ∈ l →
    p x = false → (l.filter p).length + 1 ≤ l.length
  | [], _, hx, _ => absurd hx List.not_mem_nil
  | y :: l, x, hx, hp => by
    have hle := List.length_filter_le p l
    cases hpy : p y with
    | false =>
      rw [List.filter_cons_of_neg (by rw [hpy]; exact Bool.false_ne_true)]
      show (l.filter p).length + 1 ≤ l.length + 1
      omega
    | true =>
      have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with e | h
        · rw [e, hpy] at hp
          cases hp
        · exact h
      have ih := length_filter_succ_le hx' hp
      rw [List.filter_cons_of_pos hpy]
      show (l.filter p).length + 1 + 1 ≤ l.length + 1
      omega

theorem XNet.takeAgent_length {X : XNet S} {a : Id} {α : S} (h : (a, α) ∈ X.agents) :
    (X.takeAgent a).agents.length + 1 ≤ X.agents.length :=
  length_filter_succ_le h (decide_eq_false fun hne => hne rfl)

/-- The segments a thread has left to write. -/
def XThread.pendLen (T : XThread S) : Nat :=
  match T.st with
  | .write _ ls => ls.length
  | _ => 0

/-- The agents a thread has left to write or may give back. -/
def XThread.owes (T : XThread S) : Nat :=
  match T.st with
  | .write as _ => as.length
  | .half _ _ _ _ => 1
  | _ => 0

/-- The number of segments of the goal. -/
def XMach.segs (M : XMach S) : Nat := M.mem.wires.length + total XThread.pendLen M.ths

/-- A bound on the number of agents in memory until the next claim. -/
def XMach.heads (M : XMach S) : Nat := M.mem.agents.length + total XThread.owes M.ths

theorem XMach.links_length (M : XMach S) : M.links.length = M.segs := by
  have key : ∀ (f : XThread S → List (Port × Port)), (∀ T, (f T).length = T.pendLen) →
      ∀ ths : List (XThread S), (ths.flatMap f).length = total XThread.pendLen ths := by
    intro f hf ths
    induction ths with
    | nil => rfl
    | cons T ths ih =>
      rw [List.flatMap_cons, List.length_append, ih, hf]
      rfl
  show (M.mem.wires ++ _).length = M.mem.wires.length + total XThread.pendLen M.ths
  rw [List.length_append, key]
  intro T
  obtain ⟨todo, st⟩ := T
  cases st <;> rfl

/-- The lengths of the trails from the principal port of `a` whose last
step goes from `p` to `c`. -/
def TrailLen (G : Net S) (a : Id) (p c : Port) (n : Nat) : Prop :=
  ∃ vs, Trail G.link (a, 0) (c :: p :: vs) ∧ vs.length + 2 = n

/-- What a thread still has to do, at most, before it is idle with a
shorter list or makes a claim: `K` is the number of segments of the goal and
`A` bounds the number of agents in memory. -/
noncomputable def pot (G : Net S) (K A : Nat) (T : XThread S) : Nat :=
  match T.st with
  | .idle => T.todo.length * (K + 6)
  | .look _ _ => T.todo.length * (K + 6) + (K + 5)
  | .seek a _ p c =>
    T.todo.length * (K + 6) + (K + 1 - supBelow (TrailLen G a p c) (K + 1)) + 3
  | .ready _ _ _ _ => T.todo.length * (K + 6) + 2
  | .half _ _ _ _ => T.todo.length * (K + 6) + 1
  | .write as ls => as.length + ls.length + 1 + A * (K + 6)

theorem pot_mono (G : Net S) (K : Nat) {A' A : Nat} (h : A' ≤ A) (U : XThread S) :
    pot G K A' U ≤ pot G K A U := by
  obtain ⟨todo, st⟩ := U
  cases st with
  | write as ls => exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
  | idle => exact Nat.le_refl _
  | look a α => exact Nat.le_refl _
  | seek a α p c => exact Nat.le_refl _
  | ready a b α β => exact Nat.le_refl _
  | half a b α β => exact Nat.le_refl _

theorem supBelow_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) (B : Nat) :
    supBelow P B ≤ supBelow Q B := by
  rcases supBelow_spec P B with e | hP
  · rw [e]
    exact Nat.zero_le _
  · exact le_supBelow (h _ hP) (supBelow_le P B)

/-- What the threads still have to do before the next claim. -/
noncomputable def XMach.energy (M : XMach S) : Nat :=
  total (pot M.toMach.goal M.segs M.heads) M.ths

variable [DecidableEq S] {xs : XSys S}

theorem XMach.Live.goal_same {M : XMach S} (hL : M.Live xs) {t : Nat} {T T₁ : XThread S}
    {X₁ : XNet S} (ht : M.ths[t]? = some T) (hact : XMach.act xs M.mem T = (X₁, T₁, 0)) :
    (XMach.toMach ⟨X₁, M.ths.set t T₁⟩).goal = M.toMach.goal := by
  have es := XMach.step_eq ht hact
  have h := XMach.step_sim xs M t
  rw [es] at h
  rcases h with ⟨e₁, -⟩ | hs
  · have e₁' : XMach.toMach ⟨X₁, M.ths.set t T₁⟩ = M.toMach := e₁
    rw [e₁']
  · exact (MStep.sim hL.inv hs).2.goal_zero rfl

/-- An action that makes no claim brings the energy down, if it keeps the
counts of segments and agents and brings the thread's own share down. -/
theorem XMach.Live.progress {M : XMach S} (hL : M.Live xs) {t : Nat} {T T₁ : XThread S}
    {X₁ : XNet S} (ht : M.ths[t]? = some T) (hact : XMach.act xs M.mem T = (X₁, T₁, 0))
    (hK : X₁.wires.length + T₁.pendLen = M.mem.wires.length + T.pendLen)
    (hA : X₁.agents.length + T₁.owes ≤ M.mem.agents.length + T.owes)
    (hφ : ∀ A', A' ≤ M.heads →
      pot M.toMach.goal M.segs A' T₁ < pot M.toMach.goal M.segs M.heads T) :
    (M.step xs t).2 = 0 ∧ (M.step xs t).1.energy < M.energy ∧
      (M.step xs t).1.segs = M.segs ∧ (M.step xs t).1.heads ≤ M.heads := by
  have hg := hL.goal_same ht hact
  rw [XMach.step_eq ht hact]
  have hsegs : XMach.segs ⟨X₁, M.ths.set t T₁⟩ = M.segs := by
    have h := total_set XThread.pendLen M.ths t T T₁ ht
    show X₁.wires.length + total XThread.pendLen (M.ths.set t T₁) =
      M.mem.wires.length + total XThread.pendLen M.ths
    omega
  have hheads : XMach.heads ⟨X₁, M.ths.set t T₁⟩ ≤ M.heads := by
    have h := total_set XThread.owes M.ths t T T₁ ht
    show X₁.agents.length + total XThread.owes (M.ths.set t T₁) ≤
      M.mem.agents.length + total XThread.owes M.ths
    omega
  refine ⟨rfl, ?_, hsegs, hheads⟩
  show total (pot (XMach.toMach ⟨X₁, M.ths.set t T₁⟩).goal (XMach.segs ⟨X₁, M.ths.set t T₁⟩)
    (XMach.heads ⟨X₁, M.ths.set t T₁⟩)) (M.ths.set t T₁) <
      total (pot M.toMach.goal M.segs M.heads) M.ths
  rw [hg, hsegs]
  exact total_set_lt (fun U => pot_mono _ _ hheads U) M.ths t ht (hφ _ hheads)

/-- **Every action is a rest, a claim, or brings the energy down.**  A claim
is the second compare-and-swap of a thread, which then has the right-hand
side of the rule to write; any other action that is not a rest keeps the
counts of segments and of agents. -/
theorem XMach.step_progress {M : XMach S} (hL : M.Live xs) (t : Nat) :
    (M.step xs t = (M, 0) ∧ ∀ T, M.ths[t]? = some T → T = ⟨[], .idle⟩) ∨
      ((M.step xs t).2 = 1 ∧ ∃ (todo : List (Id × S)) (a b : Id) (α β : S) (R : XRhs S),
        xs.rule α β = some R ∧ M.ths[t]? = some ⟨todo, .half a b α β⟩ ∧
        (b, β) ∈ M.mem.agents ∧
        (M.step xs t).1 = ⟨M.mem.takeAgent b, M.ths.set t
          ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩⟩) ∨
      ((M.step xs t).2 = 0 ∧ (M.step xs t).1.energy < M.energy ∧
        (M.step xs t).1.segs = M.segs ∧ (M.step xs t).1.heads ≤ M.heads) := by
  cases ht : M.ths[t]? with
  | none =>
    refine .inl ⟨?_, fun T h => by cases h⟩
    unfold XMach.step
    rw [ht]
  | some T =>
    have hG := hL.inv.wf
    have hS := hL.sane t T ht
    obtain ⟨todo, s⟩ := T
    cases s with
    | idle =>
      cases todo with
      | nil =>
        refine .inl ⟨?_, fun T h => (Option.some.inj h).symm⟩
        rw [XMach.step_eq ht (rfl : XMach.act xs M.mem ⟨[], .idle⟩ = (M.mem, ⟨[], .idle⟩, 0)),
          set_self M.ths t _ ht]
      | cons e rest =>
        by_cases he : assoc e.1 M.mem.agents = some e.2
        · refine .inr (.inr (hL.progress ht (XMach.act_idle_pos he) rfl (Nat.le_refl _)
            fun A' _ => ?_))
          show rest.length * (M.segs + 6) + (M.segs + 5) < (rest.length + 1) * (M.segs + 6)
          rw [Nat.add_mul, Nat.one_mul]
          omega
        · refine .inr (.inr (hL.progress ht (XMach.act_idle_neg he) rfl (Nat.le_refl _)
            fun A' _ => ?_))
          show rest.length * (M.segs + 6) < (rest.length + 1) * (M.segs + 6)
          rw [Nat.add_mul, Nat.one_mul]
          omega
    | look a₀ α₀ =>
      cases hv : assoc (a₀, 0) M.mem.wires with
      | some q =>
        refine .inr (.inr (hL.progress ht (XMach.act_look hv) rfl (Nat.le_refl _)
          fun A' _ => ?_))
        have hl : M.toMach.goal.link (a₀, 0) q := .inl (assoc_mem hv)
        have hf : q ∉ [((a₀, 0) : Port)] := by
          intro h
          rw [List.mem_singleton.1 h] at hl
          exact hG.irrefl hl
        have tr : Trail M.toMach.goal.link (a₀, 0) [q, (a₀, 0)] := .step .start hl hf
        have hb := tr.length_le M.links fun h => XMach.mem_links h
        rw [XMach.links_length] at hb
        have hb' : 2 ≤ M.segs + 1 := hb
        have hsup : 2 ≤ supBelow (TrailLen M.toMach.goal a₀ (a₀, 0) q) (M.segs + 1) :=
          le_supBelow ⟨[], tr, rfl⟩ hb'
        show todo.length * (M.segs + 6) +
            (M.segs + 1 - supBelow (TrailLen M.toMach.goal a₀ (a₀, 0) q) (M.segs + 1)) + 3 <
          todo.length * (M.segs + 6) + (M.segs + 5)
        omega
      | none =>
        refine .inr (.inr (hL.progress ht (XMach.act_look_none hv) rfl (Nat.le_refl _)
          fun A' _ => ?_))
        show todo.length * (M.segs + 6) < todo.length * (M.segs + 6) + (M.segs + 5)
        omega
    | seek a₀ α₀ p c =>
      obtain ⟨-, -, hd1, vs₀, tr₀⟩ := hS
      have hb₀ := tr₀.length_le M.links fun h => XMach.mem_links h
      rw [XMach.links_length] at hb₀
      have hb₀' : vs₀.length + 2 ≤ M.segs + 1 := hb₀
      have hsup₀ : vs₀.length + 2 ≤ supBelow (TrailLen M.toMach.goal a₀ p c) (M.segs + 1) :=
        le_supBelow ⟨vs₀, tr₀, rfl⟩ hb₀'
      have hle := supBelow_le (TrailLen M.toMach.goal a₀ p c) (M.segs + 1)
      cases hsc : (if c.2 = 0 then assoc c.1 M.mem.agents else none) with
      | some β' =>
        by_cases hc : a₀ ≠ c.1 ∧ (xs.rule α₀ β').isSome
        · refine .inr (.inr (hL.progress ht (XMach.act_seek_found hsc hc) rfl (Nat.le_refl _)
            fun A' _ => ?_))
          show todo.length * (M.segs + 6) + 2 < todo.length * (M.segs + 6) +
            (M.segs + 1 - supBelow (TrailLen M.toMach.goal a₀ p c) (M.segs + 1)) + 3
          omega
        · refine .inr (.inr (hL.progress ht (XMach.act_seek_norule hsc hc) rfl (Nat.le_refl _)
            fun A' _ => ?_))
          show todo.length * (M.segs + 6) < todo.length * (M.segs + 6) +
            (M.segs + 1 - supBelow (TrailLen M.toMach.goal a₀ p c) (M.segs + 1)) + 3
          omega
      | none =>
        cases hns : nextSeg M.mem.wires c p with
        | some q =>
          refine .inr (.inr (hL.progress ht (XMach.act_seek_next hsc hns) rfl (Nat.le_refl _)
            fun A' _ => ?_))
          obtain ⟨hl, hqp⟩ := nextSeg_spec hns
          have hlG : M.toMach.goal.link c q := .inl hl
          rcases supBelow_spec (TrailLen M.toMach.goal a₀ p c) (M.segs + 1) with
            h0 | ⟨vs, tr, hlen⟩
          · omega
          · have tr' : Trail M.toMach.goal.link (a₀, 0) (q :: c :: p :: vs) :=
              .step tr hlG (Trail.fresh hG.symm hG.irrefl hG.deg hd1 tr hlG hqp)
            have hb := tr'.length_le M.links fun h => XMach.mem_links h
            rw [XMach.links_length] at hb
            have hb' : (p :: vs).length + 2 ≤ M.segs + 1 := hb
            have hsup : (p :: vs).length + 2 ≤
                supBelow (TrailLen M.toMach.goal a₀ c q) (M.segs + 1) :=
              le_supBelow ⟨p :: vs, tr', rfl⟩ hb'
            have e1 : (p :: vs).length = vs.length + 1 := rfl
            show todo.length * (M.segs + 6) +
                (M.segs + 1 - supBelow (TrailLen M.toMach.goal a₀ c q) (M.segs + 1)) + 3 <
              todo.length * (M.segs + 6) +
                (M.segs + 1 - supBelow (TrailLen M.toMach.goal a₀ p c) (M.segs + 1)) + 3
            omega
        | none =>
          refine .inr (.inr (hL.progress ht (XMach.act_seek_stop hsc hns) rfl (Nat.le_refl _)
            fun A' _ => ?_))
          show todo.length * (M.segs + 6) < todo.length * (M.segs + 6) +
            (M.segs + 1 - supBelow (TrailLen M.toMach.goal a₀ p c) (M.segs + 1)) + 3
          omega
    | ready a₀ b₀ α₀ β₀ =>
      by_cases ha : assoc a₀ M.mem.agents = some α₀
      · refine .inr (.inr (hL.progress ht (XMach.act_ready ha) rfl
          (XNet.takeAgent_length (assoc_mem ha)) fun A' _ => ?_))
        show todo.length * (M.segs + 6) + 1 < todo.length * (M.segs + 6) + 2
        omega
      · refine .inr (.inr (hL.progress ht (XMach.act_ready_neg ha) rfl (Nat.le_refl _)
          fun A' _ => ?_))
        show todo.length * (M.segs + 6) < todo.length * (M.segs + 6) + 2
        omega
    | half a₀ b₀ α₀ β₀ =>
      cases hh : (if assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ then xs.rule α₀ β₀
          else none) with
      | some R =>
        have hc : assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ ∧ xs.rule α₀ β₀ = some R := by
          split at hh
          · rename_i h
            exact ⟨h.1, h.2, hh⟩
          · cases hh
        refine .inr (.inl ⟨?_, todo, a₀, b₀, α₀, β₀, R, hc.2.2, rfl, assoc_mem hc.1, ?_⟩)
        · rw [XMach.step_eq ht (XMach.act_half hh)]
        · rw [XMach.step_eq ht (XMach.act_half hh)]
      | none =>
        refine .inr (.inr (hL.progress ht (XMach.act_half_none hh) rfl (Nat.le_refl _)
          fun A' _ => ?_))
        show todo.length * (M.segs + 6) < todo.length * (M.segs + 6) + 1
        omega
    | write as ls =>
      cases as with
      | cons e as =>
        obtain ⟨i, γ⟩ := e
        refine .inr (.inr (hL.progress ht rfl rfl ?_ fun A' hA' => ?_))
        · show M.mem.agents.length + 1 + as.length ≤ M.mem.agents.length + (as.length + 1)
          omega
        · have hm := Nat.mul_le_mul_right (M.segs + 6) hA'
          show as.length + ls.length + 1 + A' * (M.segs + 6) <
            as.length + 1 + ls.length + 1 + M.heads * (M.segs + 6)
          omega
      | nil =>
        cases ls with
        | cons e ls =>
          obtain ⟨p, q⟩ := e
          refine .inr (.inr (hL.progress ht rfl ?_ (Nat.le_refl _) fun A' hA' => ?_))
          · show M.mem.wires.length + 1 + ls.length = M.mem.wires.length + (ls.length + 1)
            omega
          · have hm := Nat.mul_le_mul_right (M.segs + 6) hA'
            show 0 + ls.length + 1 + A' * (M.segs + 6) <
              0 + (ls.length + 1) + 1 + M.heads * (M.segs + 6)
            omega
        | nil =>
          refine .inr (.inr (hL.progress ht rfl rfl (Nat.le_refl _) fun A' _ => ?_))
          have h1 : M.mem.agents.length ≤ M.heads := Nat.le_add_right _ _
          have hm := Nat.mul_le_mul_right (M.segs + 6) h1
          show M.mem.agents.length * (M.segs + 6) < 0 + 0 + 1 + M.heads * (M.segs + 6)
          omega

theorem XMach.step_length (xs : XSys S) (M : XMach S) (t : Nat) :
    (M.step xs t).1.ths.length = M.ths.length := by
  unfold XMach.step
  split
  · exact List.length_set
  · rfl

/-- The run under an unending schedule: the state and the number of claims
after `i` actions. -/
def XMach.trace (xs : XSys S) (σ : Nat → Nat) (M : XMach S) : Nat → XMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((XMach.trace xs σ M i).1.step xs (σ i)).1,
      (XMach.trace xs σ M i).2 + ((XMach.trace xs σ M i).1.step xs (σ i)).2)

/-- The run is an execution of the machine. -/
theorem XMach.trace_run (xs : XSys S) (σ : Nat → Nat) (M : XMach S) :
    ∀ i, MRun xs.sys (M.trace xs σ i).2 M.toMach (M.trace xs σ i).1.toMach
  | 0 => .refl _
  | i + 1 => by
    have ih := XMach.trace_run xs σ M i
    show MRun xs.sys ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2) M.toMach
      ((M.trace xs σ i).1.step xs (σ i)).1.toMach
    rcases XMach.step_sim xs (M.trace xs σ i).1 (σ i) with ⟨e₁, e₂⟩ | hs
    · rw [e₂, e₁, Nat.add_zero]
      exact ih
    · exact ih.trans (.step hs (.refl _))

theorem XMach.trace_live (σ : Nat → Nat) {M : XMach S} (hL : M.Live xs) :
    ∀ i, (M.trace xs σ i).1.Live xs
  | 0 => hL
  | i + 1 => XMach.step_live (XMach.trace_live σ hL i) (σ i)

theorem XMach.trace_length (xs : XSys S) (σ : Nat → Nat) (M : XMach S) :
    ∀ i, (M.trace xs σ i).1.ths.length = M.ths.length
  | 0 => rfl
  | i + 1 => (XMach.step_length xs _ _).trans (XMach.trace_length xs σ M i)

/-- **Under a fair schedule the run comes to rest with the normal form.**
Take a well-formed net that has a normal form, reached in `n` steps, at
least one thread, and any unending schedule in which every thread keeps
being scheduled; the actions of the threads may overlap in any way.  From
some action on every thread is idle with an empty list, `n` claims have
been made, and the memory holds the normal form. -/
theorem XMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init X nt).trace xs σ i).1.resting = true ∧
      ((XMach.init X nt).trace xs σ i).2 = n ∧
      ((XMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  have live := XMach.trace_live (xs := xs) σ (XMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((XMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((XMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := XMach.trace_run xs σ (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((XMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  have len : ∀ i, ((XMach.init X nt).trace xs σ i).1.ths.length = nt := by
    intro i
    rw [XMach.trace_length]
    show ((List.range nt).map _).length = nt
    rw [List.length_map, List.length_range]
  obtain ⟨i₀, hi₀⟩ := lex_settles
    (fun i => n - ((XMach.init X nt).trace xs σ i).2)
    (fun i => ((XMach.init X nt).trace xs σ i).1.energy)
    (fun i => ((XMach.init X nt).trace xs σ i).1.step xs (σ i) =
        (((XMach.init X nt).trace xs σ i).1, 0) ∧
      ∀ T, ((XMach.init X nt).trace xs σ i).1.ths[σ i]? = some T → T = ⟨[], .idle⟩) (by
      intro i
      have hb := bound (i + 1)
      have hc : ((XMach.init X nt).trace xs σ (i + 1)).2 =
          ((XMach.init X nt).trace xs σ i).2 +
            (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2 := rfl
      have hm : ((XMach.init X nt).trace xs σ (i + 1)).1 =
          (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1 := rfl
      rcases XMach.step_progress (live i) (σ i) with ⟨e, hT⟩ | ⟨h1, -⟩ | ⟨h0, hlt, -, -⟩
      · refine .inl ⟨⟨e, hT⟩, ?_, ?_⟩
        · show n - ((XMach.init X nt).trace xs σ (i + 1)).2 =
            n - ((XMach.init X nt).trace xs σ i).2
          rw [hc, e]
          rfl
        · show ((XMach.init X nt).trace xs σ (i + 1)).1.energy =
            ((XMach.init X nt).trace xs σ i).1.energy
          rw [hm, e]
      · refine .inr (.inl ?_)
        show n - ((XMach.init X nt).trace xs σ (i + 1)).2 <
          n - ((XMach.init X nt).trace xs σ i).2
        omega
      · refine .inr (.inr ⟨?_, ?_⟩)
        · show n - ((XMach.init X nt).trace xs σ (i + 1)).2 =
            n - ((XMach.init X nt).trace xs σ i).2
          omega
        · show ((XMach.init X nt).trace xs σ (i + 1)).1.energy <
            ((XMach.init X nt).trace xs σ i).1.energy
          rw [hm]
          exact hlt)
  have stay : ∀ i, i₀ ≤ i → (XMach.init X nt).trace xs σ (i + 1) =
      (XMach.init X nt).trace xs σ i := by
    intro i hi
    obtain ⟨e, -⟩ := hi₀ i hi
    show ((((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1,
      ((XMach.init X nt).trace xs σ i).2 +
        (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2) = _
    rw [e]
    rfl
  have same : ∀ d, (XMach.init X nt).trace xs σ (i₀ + d) = (XMach.init X nt).trace xs σ i₀ := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => exact (stay (i₀ + d) (Nat.le_add_right _ _)).trans ih
  have hrest : ((XMach.init X nt).trace xs σ i₀).1.resting = true := by
    refine List.all_eq_true.2 fun T hT => ?_
    obtain ⟨u, hu⟩ := List.getElem?_of_mem hT
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hu
    rw [len i₀] at hlt
    obtain ⟨j, hj, hju⟩ := hfair u hlt i₀
    obtain ⟨d, rfl⟩ : ∃ d, j = i₀ + d := ⟨j - i₀, by omega⟩
    obtain ⟨-, hT'⟩ := hi₀ (i₀ + d) hj
    rw [same d, hju] at hT'
    rw [hT' T hu]
    rfl
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, i = i₀ + d := ⟨i - i₀, by omega⟩
  rw [same d]
  obtain ⟨hq, hnorm⟩ := (live i₀).rest hrest
  obtain ⟨-, hu⟩ := (run i₀).final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨hrest, e₂.symm, e₁.symm⟩

end Fair

/-! ### How long a fair run can take

A thread makes one pass over its first list of agents, and one more after
each claim it makes.  A pass follows the wire from the principal port of
each agent, and the wires from different principal ports share no segment,
even as other threads lengthen them.  So a pass costs at most seven actions
for each agent and one for each segment.  The threads are counted one at a
time: what a thread has to do before its next claim is not raised by the
others, and all the threads together make as many claims as there are
steps.  So the number of actions before every thread is at rest is bounded
by the window times the bound of one thread alone, in terms of the net, of
the number of steps to its normal form and of the size of the rules. -/

section Bound

theorem dedupFst_length_le {A B : Type} [DecidableEq A] :
    ∀ l : List (A × B), (dedupFst l).length ≤ l.length
  | [] => Nat.le_refl _
  | e :: l => by
    have ih := dedupFst_length_le l
    unfold dedupFst
    split
    · exact Nat.le_succ_of_le ih
    · exact Nat.succ_le_succ ih

theorem XRhs.newAgents_length (R : XRhs S) (a b : Id) :
    (R.newAgents a b).length ≤ R.slots.length :=
  Nat.le_trans (dedupFst_length_le _) (List.length_filterMap_le _ _)

theorem XRhs.newLinks_length (R : XRhs S) (ar : S → Nat) (a b : Id) (α β : S) :
    (R.newLinks ar a b α β).length ≤ (ifcPorts ar α β ++ R.newPorts ar).length :=
  List.length_filterMap_le _ _

/-- No rule of the system writes more than `C` agents or `D` segments. -/
def XSys.Bounded (xs : XSys S) (C D : Nat) : Prop :=
  ∀ α β R, xs.rule α β = some R →
    R.slots.length ≤ C ∧ (ifcPorts xs.sys.ar α β ++ R.newPorts xs.sys.ar).length ≤ D

theorem total_le_mul {f : XThread S → Nat} {P : Nat} :
    ∀ {ths : List (XThread S)}, (∀ T, T ∈ ths → f T ≤ P) → total f ths ≤ ths.length * P
  | [], _ => Nat.zero_le _
  | U :: ths, h => by
    have h₁ := h U List.mem_cons_self
    have ih := total_le_mul (ths := ths) fun T hT => h T (List.mem_cons_of_mem _ hT)
    show f U + total f ths ≤ (ths.length + 1) * P
    rw [Nat.add_mul, Nat.one_mul]
    omega

section TrailSteps

variable {V : Type} {L : V → V → Prop}

/-- The steps of a trail, each as the pair of the point it leaves and the
point it reaches. -/
def trailSteps : List V → List (V × V)
  | y :: x :: vs => (x, y) :: trailSteps (x :: vs)
  | _ => []

theorem trailSteps_length : ∀ vs : List V, vs.length ≤ (trailSteps vs).length + 1
  | [] => Nat.zero_le _
  | [_] => Nat.le_refl _
  | y :: x :: vs => by
    have ih := trailSteps_length (x :: vs)
    show (x :: vs).length + 1 ≤ (trailSteps (x :: vs)).length + 1 + 1
    omega

theorem mem_trailSteps_snd : ∀ {vs : List V} {x y : V}, (x, y) ∈ trailSteps vs → y ∈ vs
  | [], _, _, h => absurd h List.not_mem_nil
  | [_], _, _, h => absurd h List.not_mem_nil
  | y₀ :: x₀ :: vs, x, y, h => by
    have h' : (x, y) ∈ (x₀, y₀) :: trailSteps (x₀ :: vs) := h
    rcases List.mem_cons.1 h' with e | h''
    · have e2 : y = y₀ := congrArg Prod.snd e
      rw [e2]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_trailSteps_snd h'')

theorem trailSteps_nodup : ∀ {vs : List V}, vs.Nodup → (trailSteps vs).Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_nil
  | y :: x :: vs, h => by
    obtain ⟨hy, h'⟩ := List.nodup_cons.1 h
    show ((x, y) :: trailSteps (x :: vs)).Nodup
    exact List.nodup_cons.2 ⟨fun hm => hy (mem_trailSteps_snd hm), trailSteps_nodup h'⟩

/-- Every step of a trail is the last step of a trail from the same point. -/
theorem Trail.of_step {u : V} {vs : List V} (t : Trail L u vs) :
    ∀ {x y : V}, (x, y) ∈ trailSteps vs → ∃ vs', Trail L u (y :: x :: vs') := by
  induction t with
  | start =>
    intro x y h
    exact absurd h List.not_mem_nil
  | @step c q vs₀ t hl hf ih =>
    intro x y h
    have h' : (x, y) ∈ (c, q) :: trailSteps (c :: vs₀) := h
    rcases List.mem_cons.1 h' with e | h''
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨vs₀, .step t hl hf⟩
    · exact ih h''

/-- **A step lies on the trail from one end only**: two trails that end with
the same step, from points that lie on one segment each, start from the same
point. -/
theorem Trail.same_start (hs : ∀ {p q}, L p q → L q p)
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z) {u u' : V}
    (hu : ∀ q q', L u q → L u q' → q = q') (hu' : ∀ q q', L u' q → L u' q' → q = q') :
    ∀ (vs vs' : List V) (x y : V), Trail L u (y :: x :: vs) → Trail L u' (y :: x :: vs') →
      u = u' := by
  intro vs
  induction vs with
  | nil =>
    intro vs' x y t t'
    cases t with
    | step t₁ hl hf =>
      cases t₁ with
      | start =>
        cases t' with
        | step t₁' hl' hf' =>
          cases t₁' with
          | start => rfl
          | step t₂' hl₂' hf₂' =>
            have e := hu _ _ hl (hs hl₂')
            rw [e] at hf'
            exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hf'
  | cons w vs ih =>
    intro vs' x y t t'
    cases t with
    | step t₁ hl hf =>
      cases t' with
      | step t₁' hl' hf' =>
        cases t₁ with
        | step t₂ hl₂ hf₂ =>
          cases t₁' with
          | start =>
            have e := hu' _ _ hl' (hs hl₂)
            rw [e] at hf
            exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hf
          | step t₂' hl₂' hf₂' =>
            rcases hd hl (hs hl₂) (hs hl₂') with e | e | e
            · rw [e] at hf
              exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hf
            · rw [e] at hf'
              exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hf'
            · subst e
              exact ih _ _ _ (.step t₂ hl₂ hf₂) (.step t₂' hl₂' hf₂')

/-- A sum over a list. -/
def tally (f : V → Nat) : List V → Nat
  | [] => 0
  | u :: us => f u + tally f us

/-- **Trails from different ends share no step.**  Take different points
that lie on one segment each, and a trail from each.  Together the trails
have no more steps than there are segments, so no more points than that
plus one for each. -/
theorem trails_total [DecidableEq V] (hs : ∀ {p q}, L p q → L q p)
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z) (W : List (V × V))
    (hW : ∀ {p q}, L p q → (p, q) ∈ W) (f : V → Nat) (us : List V) (hn : us.Nodup)
    (hu : ∀ u, u ∈ us → ∀ q q', L u q → L u q' → q = q')
    (hf : ∀ u, u ∈ us → f u = 0 ∨ ∃ vs, Trail L u vs ∧ vs.length = f u) :
    tally f us ≤ W.length + us.length := by
  have key : ∀ (us : List V), us.Nodup →
      (∀ u, u ∈ us → ∀ q q', L u q → L u q' → q = q') →
      (∀ u, u ∈ us → f u = 0 ∨ ∃ vs, Trail L u vs ∧ vs.length = f u) →
      ∃ P : List (V × V), P.Nodup ∧
        (∀ x y, (x, y) ∈ P → ∃ u, u ∈ us ∧ ∃ vs, Trail L u (y :: x :: vs)) ∧
        tally f us ≤ P.length + us.length := by
    intro us
    induction us with
    | nil =>
      intro _ _ _
      exact ⟨[], List.nodup_nil, fun x y h => absurd h List.not_mem_nil, Nat.le_refl _⟩
    | cons u us ih =>
      intro hn hu hf
      obtain ⟨hu0, hn'⟩ := List.nodup_cons.1 hn
      obtain ⟨P, hP, hPm, hle⟩ := ih hn' (fun v hv => hu v (List.mem_cons_of_mem _ hv))
        (fun v hv => hf v (List.mem_cons_of_mem _ hv))
      rcases hf u List.mem_cons_self with h0 | ⟨vs, tr, hlen⟩
      · refine ⟨P, hP, fun x y h => ?_, ?_⟩
        · obtain ⟨v, hv, w⟩ := hPm x y h
          exact ⟨v, List.mem_cons_of_mem _ hv, w⟩
        · show f u + tally f us ≤ P.length + (us.length + 1)
          omega
      · refine ⟨trailSteps vs ++ P, ?_, fun x y h => ?_, ?_⟩
        · refine List.nodup_append.2 ⟨trailSteps_nodup tr.nodup, hP, fun a ha b hb e => ?_⟩
          obtain ⟨x, y⟩ := a
          rw [← e] at hb
          obtain ⟨vs', t'⟩ := tr.of_step ha
          obtain ⟨v, hv, vs'', t''⟩ := hPm x y hb
          have euv : u = v := Trail.same_start hs hd (hu u List.mem_cons_self)
            (hu v (List.mem_cons_of_mem _ hv)) vs' vs'' x y t' t''
          rw [← euv] at hv
          exact hu0 hv
        · rcases List.mem_append.1 h with h₁ | h₂
          · obtain ⟨vs', t'⟩ := tr.of_step h₁
            exact ⟨u, List.mem_cons_self, vs', t'⟩
          · obtain ⟨v, hv, w⟩ := hPm x y h₂
            exact ⟨v, List.mem_cons_of_mem _ hv, w⟩
        · have h1 := trailSteps_length vs
          show f u + tally f us ≤ (trailSteps vs ++ P).length + (us.length + 1)
          rw [List.length_append]
          omega
  obtain ⟨P, hP, hPm, hle⟩ := key us hn hu hf
  have h := nodup_length_le P W hP fun e he => by
    obtain ⟨x, y⟩ := e
    obtain ⟨v, -, vs, t⟩ := hPm x y he
    cases t with
    | step _ hl _ => exact hW hl
  omega

end TrailSteps

/-- A reduction step only adds segments. -/
theorem Step.link_mono {sys : System S} {N N' : Net S} (h : Step sys N N') {p q : Port}
    (hl : N.link p q) : N'.link p q := by
  obtain ⟨a, b, α, β, R, -, rfl⟩ := h
  exact .inl hl

/-- A reduction step adds no segment at the principal port of a name in
use. -/
theorem Step.link_principal {sys : System S} {N N' : Net S} (hN : N.WF sys.ar)
    (h : Step sys N N') {a : Id} (hU : N.Used a) {q : Port} (hl : N'.link (a, 0) q) :
    N.link (a, 0) q := by
  obtain ⟨c, d, γ, δ, R, r, rfl⟩ := h
  rcases hl with h' | ⟨x, y, -, e, -⟩
  · exact h'
  · cases x with
    | ifc s k =>
      have e2 : (0 : Nat) = k + 1 := congrArg Prod.snd e
      omega
    | new o j k =>
      have e1 : a = child c d o j := congrArg Prod.fst e
      exact absurd (e1 ▸ hU) ((r.site hN).not_used_child o j)

/-- Along a reduction segments are only added, and none at the principal
port of a name in use. -/
theorem Steps.links {sys : System S} {n : Nat} {N N' : Net S} (hN : N.WF sys.ar)
    (h : Steps (Step sys) n N N') :
    (∀ {p q}, N.link p q → N'.link p q) ∧
      ∀ {a q}, N.Used a → N'.link (a, 0) q → N.link (a, 0) q := by
  induction h with
  | refl N => exact ⟨fun h => h, fun _ h => h⟩
  | head st _ ih =>
    obtain ⟨m, pr⟩ := ih (st.wf hN)
    exact ⟨fun h => m (st.link_mono h),
      fun hU h => st.link_principal hN hU (pr (st.used hN hU) h)⟩

/-- A net with a list of its segments, at most `K` of them, in which a
point lies on two segments at most and no segment joins a point to
itself. -/
structure Net.Sized (H : Net S) (K : Nat) : Prop where
  symm : ∀ {p q}, H.link p q → H.link q p
  irrefl : ∀ {p}, ¬ H.link p p
  deg : ∀ {p x y z}, H.link p x → H.link p y → H.link p z → x = y ∨ x = z ∨ y = z
  fin : ∃ W : List (Port × Port), W.length ≤ K ∧ ∀ {p q}, H.link p q → (p, q) ∈ W

/-- The net `H` lies ahead of the goal of `M`: it has the segments of the
goal, and no other at the principal port of a name in use. -/
structure XMach.Ahead (M : XMach S) (H : Net S) : Prop where
  link : ∀ {p q}, M.toMach.goal.link p q → H.link p q
  principal : ∀ {a q}, M.toMach.goal.Used a → H.link (a, 0) q → M.toMach.goal.link (a, 0) q

/-- The number of points of the longest trail of `H` from `u`, up to
`K + 1`. -/
noncomputable def Net.far (H : Net S) (K : Nat) (u : Port) : Nat :=
  supBelow (fun n => ∃ vs, Trail H.link u vs ∧ vs.length = n) (K + 1)

/-- What a pass over a list of agents costs at most: for each agent, the
trail of `H` from its principal port and six more actions. -/
noncomputable def Net.scan (H : Net S) (K : Nat) : List (Id × S) → Nat
  | [] => 0
  | e :: l => H.far K (e.1, 0) + 6 + Net.scan H K l

theorem Net.scan_append (H : Net S) (K : Nat) : ∀ l₁ l₂ : List (Id × S),
    H.scan K (l₁ ++ l₂) = H.scan K l₁ + H.scan K l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show H.far K (e.1, 0) + 6 + H.scan K (l₁ ++ l₂) =
      H.far K (e.1, 0) + 6 + H.scan K l₁ + H.scan K l₂
    rw [Net.scan_append H K l₁ l₂]
    omega

theorem Net.trailLen_le_far (H : Net S) (K : Nat) (a : Id) (p c : Port) :
    supBelow (TrailLen H a p c) (K + 1) ≤ H.far K (a, 0) :=
  supBelow_mono (fun _ ⟨vs, t, e⟩ => ⟨c :: p :: vs, t, e⟩) (K + 1)

/-- **A pass costs seven actions for each agent and one for each segment**,
at most: the trails from the principal ports of different agents share no
segment. -/
theorem Net.scan_le {H : Net S} {K : Nat} (hH : H.Sized K) (l : List (Id × S))
    (hn : (l.map Prod.fst).Nodup)
    (hu : ∀ e, e ∈ l → ∀ q q', H.link (e.1, 0) q → H.link (e.1, 0) q' → q = q') :
    H.scan K l ≤ 7 * l.length + K := by
  obtain ⟨W, hWK, hW⟩ := hH.fin
  have hports : ∀ (l : List (Id × S)), (l.map Prod.fst).Nodup →
      (l.map fun e => ((e.1, 0) : Port)).Nodup := by
    intro l
    induction l with
    | nil => exact fun _ => List.nodup_nil
    | cons e l ih =>
      intro h
      have h1 : (e.1 :: l.map Prod.fst).Nodup := h
      obtain ⟨he, h'⟩ := List.nodup_cons.1 h1
      show (((e.1, 0) : Port) :: l.map fun e => ((e.1, 0) : Port)).Nodup
      refine List.nodup_cons.2 ⟨fun hm => ?_, ih h'⟩
      obtain ⟨e', he', ee⟩ := List.mem_map.1 hm
      exact he (List.mem_map.2 ⟨e', he', (Prod.mk.inj ee).1⟩)
  have hsum : ∀ (l : List (Id × S)),
      H.scan K l = tally (H.far K) (l.map fun e => ((e.1, 0) : Port)) + 6 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih =>
      show H.far K (e.1, 0) + 6 + H.scan K l =
        H.far K (e.1, 0) + tally (H.far K) (l.map fun e => ((e.1, 0) : Port)) +
          6 * (l.length + 1)
      rw [ih]
      omega
  have ht := trails_total hH.symm hH.deg W hW (H.far K) (l.map fun e => ((e.1, 0) : Port))
    (hports l hn)
    (fun u hu' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu'
      exact hu e he)
    (fun u _ => supBelow_spec _ _)
  rw [List.length_map] at ht
  rw [hsum l]
  omega

/-- What a thread still has to do, at most, before it is idle with a
shorter list or makes a claim, measured in a net `H` that lies ahead of the
goal: `K` bounds the segments of `H`, and `A` the agents in memory.  A
thread about to take a fresh list of agents is charged a whole pass. -/
noncomputable def potIn (H : Net S) (K A : Nat) (T : XThread S) : Nat :=
  match T.st with
  | .idle => H.scan K T.todo
  | .look a _ => H.scan K T.todo + H.far K (a, 0) + 5
  | .seek a _ p c =>
    H.scan K T.todo + (H.far K (a, 0) - supBelow (TrailLen H a p c) (K + 1)) + 3
  | .ready _ _ _ _ => H.scan K T.todo + 2
  | .half _ _ _ _ => H.scan K T.todo + 1
  | .write as ls => as.length + ls.length + 1 + (7 * A + K)

/-- A bound on the actions of one pass of a thread over the agents, in a
run from the net `X` whose normal form is `n` steps away, when no rule
writes more than `C` agents or `D` segments: seven for each agent there can
be (a claim takes two out and writes at most `C`), and one for each
segment. -/
def XNet.passBound (X : XNet S) (n C D : Nat) : Nat :=
  7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)

/-- Before the program starts there is nothing to write. -/
theorem XMach.init_sizes (X : XNet S) (nt : Nat) :
    (XMach.init X nt).segs = X.wires.length ∧ (XMach.init X nt).heads = X.agents.length := by
  have hall : ∀ T, T ∈ (XMach.init X nt).ths →
      ∃ t, T = ⟨X.agents.drop t ++ X.agents.take t, .idle⟩ := by
    intro T hT
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
    exact ⟨t, rfl⟩
  have hp : total XThread.pendLen (XMach.init X nt).ths ≤ (XMach.init X nt).ths.length * 0 :=
    total_le_mul fun T hT => by
      obtain ⟨t, rfl⟩ := hall T hT
      exact Nat.le_refl _
  have ho : total XThread.owes (XMach.init X nt).ths ≤ (XMach.init X nt).ths.length * 0 :=
    total_le_mul fun T hT => by
      obtain ⟨t, rfl⟩ := hall T hT
      exact Nat.le_refl _
  constructor
  · show X.wires.length + total XThread.pendLen (XMach.init X nt).ths = X.wires.length
    omega
  · show X.agents.length + total XThread.owes (XMach.init X nt).ths = X.agents.length
    omega

/-- A quantity that goes down at every action that is not still settles
within a known number of actions, if a window of `F` still actions means
rest and rest lasts. -/
theorem window_settles (Ψ : Nat → Nat) (still rest : Nat → Prop) (F : Nat)
    (hstep : ∀ i, (still i ∧ Ψ (i + 1) = Ψ i) ∨ Ψ (i + 1) < Ψ i)
    (hwin : ∀ i, (∀ j, i ≤ j → j < i + F → still j) → rest i)
    (hrest : ∀ i, rest i → rest (i + 1)) :
    ∀ i, F * (Ψ 0 + 1) ≤ i → rest i := by
  have mono : ∀ i d, Ψ (i + d) ≤ Ψ i := by
    intro i d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      show Ψ (i + d + 1) ≤ Ψ i
      rcases hstep (i + d) with ⟨-, e⟩ | h
      · omega
      · omega
  have pers : ∀ i d, rest i → rest (i + d) := by
    intro i d h
    induction d with
    | zero => exact h
    | succ d ih => exact hrest _ ih
  have key : ∀ m, ∃ i, i ≤ F * m ∧ (rest i ∨ Ψ i + m ≤ Ψ 0) := by
    intro m
    induction m with
    | zero => exact ⟨0, Nat.zero_le _, .inr (Nat.le_refl _)⟩
    | succ m ih =>
      obtain ⟨i, hi, h⟩ := ih
      have hF : F * (m + 1) = F * m + F := by rw [Nat.mul_add, Nat.mul_one]
      rcases h with h | h
      · exact ⟨i, by omega, .inl h⟩
      · rcases Classical.em (∀ j, i ≤ j → j < i + F → still j) with hall | hall
        · exact ⟨i, by omega, .inl (hwin i hall)⟩
        · have hex : ∃ j, i ≤ j ∧ j < i + F ∧ ¬ still j :=
            Classical.byContradiction fun hne => hall fun j h₁ h₂ =>
              Classical.byContradiction fun hs => hne ⟨j, h₁, h₂, hs⟩
          obtain ⟨j, h₁, h₂, hs⟩ := hex
          have hlt : Ψ (j + 1) < Ψ j := by
            rcases hstep j with ⟨s, -⟩ | h'
            · exact absurd s hs
            · exact h'
          obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
          have m₁ := mono i d
          have m₂ := mono (i + d + 1) (F - d - 1)
          have e : i + d + 1 + (F - d - 1) = i + F := by omega
          rw [e] at m₂
          exact ⟨i + F, by omega, .inr (by omega)⟩
  intro i hi
  obtain ⟨i₁, h₁, h⟩ := key (Ψ 0 + 1)
  rcases h with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, i = i₁ + d := ⟨i - i₁, by omega⟩
    exact pers i₁ d h
  · omega

variable [DecidableEq S] {xs : XSys S}

/-- An action adds at most `D` segments to the goal and, since a claim
takes the two agents of its pair out of the memory, at most `C - 2` agents
to it, and only when it is a claim. -/
theorem XMach.step_sizes {M : XMach S} (hL : M.Live xs) {C D : Nat} (hb : xs.Bounded C D)
    (t : Nat) :
    (M.step xs t).1.segs ≤ M.segs + D * (M.step xs t).2 ∧
      (M.step xs t).1.heads ≤ M.heads + (C - 2) * (M.step xs t).2 := by
  rcases XMach.step_progress hL t with ⟨e, -⟩ | ⟨h1, todo, a, b, α, β, R, hR, ht, hbm, e⟩ |
    ⟨h0, -, hs, hh⟩
  · rw [e]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · obtain ⟨hC, hD⟩ := hb α β R hR
    have ha := Nat.le_trans (R.newAgents_length a b) hC
    have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
    have tp : total XThread.pendLen (M.ths.set t
          ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩) + 0 =
        total XThread.pendLen M.ths + (R.newLinks xs.sys.ar a b α β).length :=
      total_set XThread.pendLen M.ths t _ _ ht
    have to : total XThread.owes (M.ths.set t
          ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩) + 1 =
        total XThread.owes M.ths + (R.newAgents a b).length :=
      total_set XThread.owes M.ths t _ _ ht
    have hk := XNet.takeAgent_length hbm
    rw [h1, e, Nat.mul_one, Nat.mul_one]
    constructor
    · show M.mem.wires.length + total XThread.pendLen (M.ths.set t
          ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩) ≤
        M.mem.wires.length + total XThread.pendLen M.ths + D
      omega
    · show (M.mem.takeAgent b).agents.length + total XThread.owes (M.ths.set t
          ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩) ≤
        M.mem.agents.length + total XThread.owes M.ths + (C - 2)
      omega
  · rw [h0, hs]
    exact ⟨Nat.le_add_right _ _, Nat.le_trans hh (Nat.le_add_right _ _)⟩

/-- Along a sequence of actions, every claim adds at most `D` segments to
the goal and `C - 2` agents to the memory. -/
theorem XMach.seq_sizes (tr : Nat → XMach S × Nat) (σ : Nat → Nat) {W A₀ C D : Nat}
    (hsucc : ∀ i, tr (i + 1) =
      (((tr i).1.step xs (σ i)).1, (tr i).2 + ((tr i).1.step xs (σ i)).2))
    (live : ∀ i, (tr i).1.Live xs) (hb : xs.Bounded C D)
    (h₀ : (tr 0).1.segs ≤ W + D * (tr 0).2 ∧ (tr 0).1.heads ≤ A₀ + (C - 2) * (tr 0).2) :
    ∀ i, (tr i).1.segs ≤ W + D * (tr i).2 ∧ (tr i).1.heads ≤ A₀ + (C - 2) * (tr i).2
  | 0 => h₀
  | i + 1 => by
    obtain ⟨h₁, h₂⟩ := XMach.seq_sizes tr σ hsucc live hb h₀ i
    obtain ⟨s₁, s₂⟩ := XMach.step_sizes (live i) hb (σ i)
    rw [hsucc i]
    constructor
    · show ((tr i).1.step xs (σ i)).1.segs ≤
        W + D * ((tr i).2 + ((tr i).1.step xs (σ i)).2)
      rw [Nat.mul_add]
      omega
    · show ((tr i).1.step xs (σ i)).1.heads ≤
        A₀ + (C - 2) * ((tr i).2 + ((tr i).1.step xs (σ i)).2)
      rw [Nat.mul_add]
      omega

/-- At rest, every action leaves everything as it is. -/
theorem XMach.resting_step {M : XMach S} (hr : M.resting = true) (t : Nat) :
    M.step xs t = (M, 0) := by
  cases ht : M.ths[t]? with
  | none =>
    unfold XMach.step
    rw [ht]
  | some T =>
    have h : (T.todo.isEmpty && T.st.isIdle) = true :=
      List.all_eq_true.1 hr T (List.mem_of_getElem? ht)
    obtain ⟨todo, st⟩ := T
    cases todo with
    | cons e rest => cases h
    | nil =>
      cases st with
      | idle =>
        rw [XMach.step_eq ht (rfl : XMach.act xs M.mem ⟨[], .idle⟩ = (M.mem, ⟨[], .idle⟩, 0)),
          set_self M.ths t _ ht]
      | look a α => cases h
      | seek a α p c => cases h
      | ready a b α β => cases h
      | half a b α β => cases h
      | write as ls => cases h

/-- What an action does to the agents in memory: nothing, or it takes one
out, or it gives back the one its thread holds, or it writes the next one
its thread has left to write. -/
theorem XMach.act_agents (xs : XSys S) (X : XNet S) (T : XThread S) :
    (XMach.act xs X T).1.agents = X.agents ∨
      (∃ a, (XMach.act xs X T).1 = X.takeAgent a) ∨
      (∃ a b α β, T.st = .half a b α β ∧ (XMach.act xs X T).1 = X.putAgent a α) ∨
      ∃ i γ as ls, T.st = .write ((i, γ) :: as) ls ∧
        (XMach.act xs X T).1 = X.putAgent i γ := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact .inl rfl
    | cons e rest =>
      unfold XMach.act
      dsimp only
      split
      · exact .inl rfl
      · exact .inl rfl
  | look a α =>
    unfold XMach.act
    dsimp only
    split
    · exact .inl rfl
    · exact .inl rfl
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    split
    · split
      · exact .inl rfl
      · exact .inl rfl
    · split
      · exact .inl rfl
      · exact .inl rfl
  | ready a b α β =>
    unfold XMach.act
    dsimp only
    split
    · exact .inr (.inl ⟨a, rfl⟩)
    · exact .inl rfl
  | half a b α β =>
    unfold XMach.act
    dsimp only
    split
    · exact .inr (.inl ⟨b, rfl⟩)
    · exact .inr (.inr (.inl ⟨a, b, α, β, rfl, rfl⟩))
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact .inr (.inr (.inr ⟨i, γ, as, ls, rfl, rfl⟩))
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact .inl rfl
      | nil => exact .inl rfl

/-- **No agent is in memory twice**, if none was at the start: a thread
gives back only the agent it holds, and writes only agents that are not
there yet. -/
theorem XMach.step_nodup {M : XMach S} (hL : M.Live xs)
    (h : (M.mem.agents.map Prod.fst).Nodup) (t : Nat) :
    ((M.step xs t).1.mem.agents.map Prod.fst).Nodup := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold XMach.step
      rw [ht]
    rw [e]
    exact h
  | some T =>
    have e : (M.step xs t).1.mem = (XMach.act xs M.mem T).1 := by
      unfold XMach.step
      rw [ht]
    rw [e]
    have hok := hL.ok ht
    have fresh : ∀ {i : Id} {γ : S}, (∀ δ, ¬ M.mem.toNet.agent i δ) →
        ((M.mem.putAgent i γ).agents.map Prod.fst).Nodup := by
      intro i γ hi
      show (i :: M.mem.agents.map Prod.fst).Nodup
      refine List.nodup_cons.2 ⟨fun hm => ?_, h⟩
      obtain ⟨e', he', ee⟩ := List.mem_map.1 hm
      have hm' : (i, e'.2) ∈ M.mem.agents := by
        rw [← ee]
        exact he'
      exact hi e'.2 hm'
    rcases XMach.act_agents xs M.mem T with e₁ | ⟨a, e₁⟩ | ⟨a, b, α, β, es, e₁⟩ |
      ⟨i, γ, as, ls, es, e₁⟩
    · rw [e₁]
      exact h
    · rw [e₁]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) h
    · rw [e₁]
      rw [es] at hok
      exact fresh hok.2
    · rw [e₁]
      refine fresh fun δ hδ => ?_
      have hp : (threadOf M.ths t).pendA i γ := by
        rw [threadOf_eq ht, es]
        exact List.mem_cons_self
      exact hL.inv.pend_fresh δ hp (.inl hδ)

/-- An action of one thread leaves the others as they were. -/
theorem XMach.step_other (M : XMach S) {s t : Nat} (h : s ≠ t) :
    (M.step xs s).1.ths[t]? = M.ths[t]? := by
  unfold XMach.step
  split
  · exact List.getElem?_set_ne h
  · rfl

/-- A thread at rest stays at rest, whoever acts. -/
theorem XMach.step_rest (M : XMach S) (s : Nat) {t : Nat}
    (h : M.ths[t]? = some ⟨[], .idle⟩) : (M.step xs s).1.ths[t]? = some ⟨[], .idle⟩ := by
  by_cases e : s = t
  · subst e
    rw [XMach.step_eq h (rfl : XMach.act xs M.mem ⟨[], .idle⟩ = (M.mem, ⟨[], .idle⟩, 0)),
      set_self M.ths s _ h]
    exact h
  · rw [XMach.step_other M e]
    exact h

/-- An action of a thread puts the thread where its action leaves it, and
counts the claim the action makes. -/
theorem XMach.step_self {M : XMach S} {t : Nat} {T : XThread S} (ht : M.ths[t]? = some T) :
    (M.step xs t).1.ths[t]? = some (XMach.act xs M.mem T).2.1 ∧
      (M.step xs t).2 = (XMach.act xs M.mem T).2.2 := by
  rw [XMach.step_eq ht (rfl : XMach.act xs M.mem T =
    ((XMach.act xs M.mem T).1, (XMach.act xs M.mem T).2.1, (XMach.act xs M.mem T).2.2))]
  exact ⟨List.getElem?_set_self (List.getElem?_eq_some_iff.1 ht).1, rfl⟩

/-- **Every action of a thread is a rest, a claim, or brings its share
down**, measured in a net that lies ahead of the goal.  A claim raises the
share by at most the writes of one rule and one pass over the agents. -/
theorem XMach.act_pot {M : XMach S} (hL : M.Live xs)
    (hnd : (M.mem.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D)
    {H : Net S} {K A : Nat} (hH : H.Sized K) (hM : M.Ahead H) (hA : M.heads ≤ A) {t : Nat}
    {T : XThread S} (ht : M.ths[t]? = some T) :
    (XMach.act xs M.mem T = (M.mem, T, 0) ∧ T = ⟨[], .idle⟩) ∨
      ((XMach.act xs M.mem T).2.2 = 1 ∧
        potIn H K A (XMach.act xs M.mem T).2.1 ≤ potIn H K A T + (C + D + 7 * A + K)) ∨
      ((XMach.act xs M.mem T).2.2 = 0 ∧
        potIn H K A (XMach.act xs M.mem T).2.1 < potIn H K A T) := by
  obtain ⟨W, hWK, hW⟩ := hH.fin
  have hlen : ∀ {u : Port} {vs : List Port}, Trail H.link u vs → vs.length ≤ K + 1 := by
    intro u vs tr
    have h := tr.length_le W hW
    omega
  have hG := hL.inv.wf
  have hS := hL.sane t T ht
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil =>
      exact .inl ⟨rfl, rfl⟩
    | cons e rest =>
      by_cases he : assoc e.1 M.mem.agents = some e.2
      · rw [XMach.act_idle_pos he]
        refine .inr (.inr ⟨rfl, ?_⟩)
        show H.scan K rest + H.far K (e.1, 0) + 5 < H.far K (e.1, 0) + 6 + H.scan K rest
        omega
      · rw [XMach.act_idle_neg he]
        refine .inr (.inr ⟨rfl, ?_⟩)
        show H.scan K rest < H.far K (e.1, 0) + 6 + H.scan K rest
        omega
  | look a₀ α₀ =>
    cases hv : assoc (a₀, 0) M.mem.wires with
    | some q =>
      rw [XMach.act_look hv]
      refine .inr (.inr ⟨rfl, ?_⟩)
      show H.scan K todo +
          (H.far K (a₀, 0) - supBelow (TrailLen H a₀ (a₀, 0) q) (K + 1)) + 3 <
        H.scan K todo + H.far K (a₀, 0) + 5
      omega
    | none =>
      rw [XMach.act_look_none hv]
      refine .inr (.inr ⟨rfl, ?_⟩)
      show H.scan K todo < H.scan K todo + H.far K (a₀, 0) + 5
      omega
  | seek a₀ α₀ p c =>
    obtain ⟨hU, -, hd1, vs₀, tr₀⟩ := hS
    have hu : ∀ q q', H.link (a₀, 0) q → H.link (a₀, 0) q' → q = q' :=
      fun q q' h h' => hd1 q q' (hM.principal hU h) (hM.principal hU h')
    have trH₀ : Trail H.link (a₀, 0) (c :: p :: vs₀) := tr₀.mono hM.link
    have hsup₀ : vs₀.length + 2 ≤ supBelow (TrailLen H a₀ p c) (K + 1) :=
      le_supBelow ⟨vs₀, trH₀, rfl⟩ (hlen trH₀)
    have hle := H.trailLen_le_far K a₀ p c
    cases hsc : (if c.2 = 0 then assoc c.1 M.mem.agents else none) with
    | some β' =>
      by_cases hc : a₀ ≠ c.1 ∧ (xs.rule α₀ β').isSome
      · rw [XMach.act_seek_found hsc hc]
        refine .inr (.inr ⟨rfl, ?_⟩)
        show H.scan K todo + 2 < H.scan K todo +
          (H.far K (a₀, 0) - supBelow (TrailLen H a₀ p c) (K + 1)) + 3
        omega
      · rw [XMach.act_seek_norule hsc hc]
        refine .inr (.inr ⟨rfl, ?_⟩)
        show H.scan K todo < H.scan K todo +
          (H.far K (a₀, 0) - supBelow (TrailLen H a₀ p c) (K + 1)) + 3
        omega
    | none =>
      cases hns : nextSeg M.mem.wires c p with
      | some q =>
        rw [XMach.act_seek_next hsc hns]
        refine .inr (.inr ⟨rfl, ?_⟩)
        obtain ⟨hl, hqp⟩ := nextSeg_spec hns
        have hlH : H.link c q := hM.link (.inl hl)
        rcases supBelow_spec (TrailLen H a₀ p c) (K + 1) with h0 | ⟨vs, tr, hvs⟩
        · omega
        · have tr' : Trail H.link (a₀, 0) (q :: c :: p :: vs) :=
            .step tr hlH (Trail.fresh hH.symm hH.irrefl hH.deg hu tr hlH hqp)
          have hb' : (p :: vs).length + 2 ≤ K + 1 := hlen tr'
          have hsup : (p :: vs).length + 2 ≤ supBelow (TrailLen H a₀ c q) (K + 1) :=
            le_supBelow ⟨p :: vs, tr', rfl⟩ hb'
          have hle' := H.trailLen_le_far K a₀ c q
          have e1 : (p :: vs).length = vs.length + 1 := rfl
          show H.scan K todo +
              (H.far K (a₀, 0) - supBelow (TrailLen H a₀ c q) (K + 1)) + 3 <
            H.scan K todo +
              (H.far K (a₀, 0) - supBelow (TrailLen H a₀ p c) (K + 1)) + 3
          omega
      | none =>
        rw [XMach.act_seek_stop hsc hns]
        refine .inr (.inr ⟨rfl, ?_⟩)
        show H.scan K todo < H.scan K todo +
          (H.far K (a₀, 0) - supBelow (TrailLen H a₀ p c) (K + 1)) + 3
        omega
  | ready a₀ b₀ α₀ β₀ =>
    by_cases ha : assoc a₀ M.mem.agents = some α₀
    · rw [XMach.act_ready ha]
      refine .inr (.inr ⟨rfl, ?_⟩)
      show H.scan K todo + 1 < H.scan K todo + 2
      omega
    · rw [XMach.act_ready_neg ha]
      refine .inr (.inr ⟨rfl, ?_⟩)
      show H.scan K todo < H.scan K todo + 2
      omega
  | half a₀ b₀ α₀ β₀ =>
    cases hh : (if assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ then xs.rule α₀ β₀
        else none) with
    | some R =>
      have hc : xs.rule α₀ β₀ = some R := by
        split at hh
        · exact hh
        · cases hh
      obtain ⟨hC, hD⟩ := hb α₀ β₀ R hc
      have ha := Nat.le_trans (R.newAgents_length a₀ b₀) hC
      have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a₀ b₀ α₀ β₀) hD
      rw [XMach.act_half hh]
      refine .inr (.inl ⟨rfl, ?_⟩)
      show (R.newAgents a₀ b₀).length + (R.newLinks xs.sys.ar a₀ b₀ α₀ β₀).length + 1 +
          (7 * A + K) ≤ H.scan K todo + 1 + (C + D + 7 * A + K)
      omega
    | none =>
      rw [XMach.act_half_none hh]
      refine .inr (.inr ⟨rfl, ?_⟩)
      show H.scan K todo < H.scan K todo + 1
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      refine .inr (.inr ⟨rfl, ?_⟩)
      show as.length + ls.length + 1 + (7 * A + K) <
        as.length + 1 + ls.length + 1 + (7 * A + K)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        refine .inr (.inr ⟨rfl, ?_⟩)
        show 0 + ls.length + 1 + (7 * A + K) < 0 + (ls.length + 1) + 1 + (7 * A + K)
        omega
      | nil =>
        refine .inr (.inr ⟨rfl, ?_⟩)
        have memG : ∀ {i : Id} {γ : S}, (i, γ) ∈ M.mem.agents → M.toMach.goal.agent i γ :=
          fun h => .inl (.inl h)
        have hs := Net.scan_le hH M.mem.agents hnd fun e he q q' h h' =>
          hG.end_unique (.inr ⟨e.2, memG (i := e.1) (γ := e.2) he, Nat.zero_le _⟩)
            (hM.principal (.inl ⟨e.2, memG (i := e.1) (γ := e.2) he⟩) h)
            (hM.principal (.inl ⟨e.2, memG (i := e.1) (γ := e.2) he⟩) h')
        have h1 : M.mem.agents.length ≤ M.heads := Nat.le_add_right _ _
        show H.scan K M.mem.agents < 0 + 0 + 1 + (7 * A + K)
        omega

/-- The share of thread `t`: what it still has to do before it is idle with
a shorter list or makes a claim.  No other thread can raise it. -/
noncomputable def XMach.potAt (M : XMach S) (H : Net S) (K A t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => potIn H K A T
  | none => 0

omit [DecidableEq S] in
theorem XMach.potAt_eq {M : XMach S} {t : Nat} {T : XThread S} (ht : M.ths[t]? = some T)
    (H : Net S) (K A : Nat) : M.potAt H K A t = potIn H K A T := by
  unfold XMach.potAt
  rw [ht]

/-- **One action and the share of one thread**, measured in a net that lies
ahead of the goal.  Either another thread acted, or the thread is at rest,
and its share is what it was; or the thread made a claim, which raises its
share by at most the writes of one rule and one pass over the agents; or
its share went down. -/
theorem XMach.step_pot {M : XMach S} (hL : M.Live xs)
    (hnd : (M.mem.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D)
    {H : Net S} {K A : Nat} (hH : H.Sized K) (hM : M.Ahead H) (hA : M.heads ≤ A) {t : Nat}
    (ht : t < M.ths.length) (s : Nat) :
    ((s ≠ t ∨ M.ths[t]? = some ⟨[], .idle⟩) ∧
        (M.step xs s).1.potAt H K A t = M.potAt H K A t) ∨
      ((M.step xs s).2 = 1 ∧
        (M.step xs s).1.potAt H K A t ≤ M.potAt H K A t + (C + D + 7 * A + K)) ∨
      ((M.step xs s).2 = 0 ∧ (M.step xs s).1.potAt H K A t < M.potAt H K A t) := by
  obtain ⟨T, hT⟩ : ∃ T, M.ths[t]? = some T := ⟨_, List.getElem?_eq_getElem ht⟩
  by_cases hs : s = t
  · subst hs
    obtain ⟨e₁, e₂⟩ := XMach.step_self (xs := xs) hT
    rw [e₂, XMach.potAt_eq e₁, XMach.potAt_eq hT]
    rcases XMach.act_pot hL hnd hb hH hM hA hT with ⟨e, rfl⟩ | h | h
    · rw [e]
      exact .inl ⟨.inr hT, rfl⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · refine .inl ⟨.inl hs, ?_⟩
    unfold XMach.potAt
    rw [XMach.step_other M hs]

/-- The normal form of a net has at most the segments of the net and `D`
more for every step: one thread alone writes it. -/
theorem XNet.normal_sized {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') : N'.Sized (X.wires.length + D * n) := by
  have hN' := Steps.wf hX hs
  refine ⟨hN'.symm, hN'.irrefl, hN'.deg, ?_⟩
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xs) hX (Nat.succ_pos 0) hs hn (fun _ => 0)
    (fun u hu i => ⟨i, Nat.le_refl _, by show 0 = u; omega⟩)
  obtain ⟨-, hc, hmem⟩ := h i₀ (Nat.le_refl _)
  have live := XMach.trace_live (xs := xs) (fun _ => 0) (XMach.init_live hX (Nat.succ_pos 0))
  obtain ⟨is, ih⟩ := XMach.init_sizes X 1
  have sizes := XMach.seq_sizes (xs := xs) ((XMach.init X 1).trace xs fun _ => 0) (fun _ => 0)
    (fun _ => rfl) live hb (W := X.wires.length) (A₀ := X.agents.length)
    ⟨Nat.le_trans (Nat.le_of_eq is) (Nat.le_add_right _ _),
      Nat.le_trans (Nat.le_of_eq ih) (Nat.le_add_right _ _)⟩
  have h₁ := (sizes i₀).1
  rw [hc] at h₁
  refine ⟨((XMach.init X 1).trace xs (fun _ => 0) i₀).1.links, ?_, fun {p q} hl => ?_⟩
  · rw [XMach.links_length]
    exact h₁
  · refine XMach.mem_links (.inl ?_)
    rw [← hmem] at hl
    exact hl

omit [DecidableEq S] in
/-- The normal form lies ahead of the goal of every state of a run. -/
theorem XMach.ahead_of_run {M : XMach S} (hinv : M.toMach.Inv xs.sys) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {k : Nat} (hr : MRun xs.sys k (Mach.init X.toNet) M.toMach)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') : M.Ahead N' := by
  obtain ⟨-, rest⟩ := reduction_bounded hX hs hn (hr.sequential hX)
  obtain ⟨m, pr⟩ := Steps.links hinv.wf rest
  exact ⟨m, pr⟩

/-- A sequence of actions with at most `n` claims and at most `A` agents,
measured in a net with at most `K` segments that lies ahead of every goal,
in which every thread is scheduled in every window of `F` actions, is at
rest after `F * (B + 1)` actions, if `B` bounds a measure at the start for
each thread: its share, plus one pass and the writes of one rule for every
claim still to come.  The measure of a thread goes down at each of its
actions, and at each claim of another thread; no action raises it.  So the
number of threads does not enter. -/
theorem XMach.settles_within (tr : Nat → XMach S × Nat) (σ : Nat → Nat)
    {n nt F K A C D B : Nat} {H : Net S}
    (hsucc : ∀ i, tr (i + 1) =
      (((tr i).1.step xs (σ i)).1, (tr i).2 + ((tr i).1.step xs (σ i)).2))
    (live : ∀ i, (tr i).1.Live xs) (bound : ∀ i, (tr i).2 ≤ n)
    (len : ∀ i, (tr i).1.ths.length = nt) (hb : xs.Bounded C D)
    (hnd : ∀ i, ((tr i).1.mem.agents.map Prod.fst).Nodup) (hH : H.Sized K)
    (hM : ∀ i, (tr i).1.Ahead H) (hA : ∀ i, (tr i).1.heads ≤ A)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u)
    (h0 : ∀ t, t < nt →
      (tr 0).1.potAt H K A t + (n - (tr 0).2) * (C + D + 7 * A + K + 1) ≤ B) :
    ∀ i, F * (B + 1) ≤ i → (tr i).1.resting = true := by
  have each : ∀ t, t < nt → ∀ i, F * (B + 1) ≤ i →
      (tr i).1.ths[t]? = some ⟨[], .idle⟩ := by
    intro t ht i hi
    have hi' : F * ((tr 0).1.potAt H K A t + (n - (tr 0).2) * (C + D + 7 * A + K + 1) + 1) ≤
        i := Nat.le_trans (Nat.mul_le_mul_left F (Nat.succ_le_succ (h0 t ht))) hi
    refine window_settles
      (fun i => (tr i).1.potAt H K A t + (n - (tr i).2) * (C + D + 7 * A + K + 1))
      (fun i => σ i ≠ t ∨ (tr i).1.ths[t]? = some ⟨[], .idle⟩)
      (fun i => (tr i).1.ths[t]? = some ⟨[], .idle⟩) F ?_ ?_ ?_ i hi'
    · intro i
      have hb1 : (tr i).2 + ((tr i).1.step xs (σ i)).2 ≤ n := by
        have h := bound (i + 1)
        rw [hsucc i] at h
        exact h
      have hlt : t < (tr i).1.ths.length := by
        rw [len i]
        exact ht
      show (_ ∧ (tr (i + 1)).1.potAt H K A t +
            (n - (tr (i + 1)).2) * (C + D + 7 * A + K + 1) =
          (tr i).1.potAt H K A t + (n - (tr i).2) * (C + D + 7 * A + K + 1)) ∨
        (tr (i + 1)).1.potAt H K A t + (n - (tr (i + 1)).2) * (C + D + 7 * A + K + 1) <
          (tr i).1.potAt H K A t + (n - (tr i).2) * (C + D + 7 * A + K + 1)
      rw [hsucc i]
      show (_ ∧ ((tr i).1.step xs (σ i)).1.potAt H K A t +
            (n - ((tr i).2 + ((tr i).1.step xs (σ i)).2)) * (C + D + 7 * A + K + 1) =
          (tr i).1.potAt H K A t + (n - (tr i).2) * (C + D + 7 * A + K + 1)) ∨
        ((tr i).1.step xs (σ i)).1.potAt H K A t +
            (n - ((tr i).2 + ((tr i).1.step xs (σ i)).2)) * (C + D + 7 * A + K + 1) <
          (tr i).1.potAt H K A t + (n - (tr i).2) * (C + D + 7 * A + K + 1)
      rcases XMach.step_pot (live i) (hnd i) hb hH (hM i) (hA i) hlt (σ i) with
        ⟨hst, he⟩ | ⟨h1, hce⟩ | ⟨hz, hlt'⟩
      · rw [he]
        rcases Nat.eq_zero_or_pos ((tr i).1.step xs (σ i)).2 with hz | hp
        · refine .inl ⟨hst, ?_⟩
          rw [hz]
          rfl
        · refine .inr ?_
          have e1 : (n - ((tr i).2 + ((tr i).1.step xs (σ i)).2)) + 1 ≤ n - (tr i).2 := by
            omega
          have h2 := Nat.mul_le_mul_right (C + D + 7 * A + K + 1) e1
          rw [Nat.add_mul, Nat.one_mul] at h2
          omega
      · refine .inr ?_
        have e1 : n - (tr i).2 = (n - ((tr i).2 + ((tr i).1.step xs (σ i)).2)) + 1 := by omega
        rw [e1, Nat.add_mul, Nat.one_mul]
        omega
      · refine .inr ?_
        rw [hz]
        exact Nat.add_lt_add_right hlt' _
    · intro i hall
      have same : ∀ d, d ≤ F → (tr (i + d)).1.ths[t]? = (tr i).1.ths[t]? := by
        intro d
        induction d with
        | zero => exact fun _ => rfl
        | succ d ih =>
          intro hd
          have ih' := ih (by omega)
          show (tr (i + d + 1)).1.ths[t]? = (tr i).1.ths[t]?
          rw [hsucc (i + d)]
          show ((tr (i + d)).1.step xs (σ (i + d))).1.ths[t]? = (tr i).1.ths[t]?
          rcases hall (i + d) (by omega) (by omega) with hne | hr
          · rw [XMach.step_other _ hne]
            exact ih'
          · rw [XMach.step_rest _ _ hr, ← ih', hr]
      obtain ⟨j, hj₁, hj₂, hju⟩ := hfair t ht i
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
      rcases hall (i + d) hj₁ hj₂ with hne | hr
      · exact absurd hju hne
      · show (tr i).1.ths[t]? = some ⟨[], .idle⟩
        rw [← same d (by omega)]
        exact hr
    · intro i h
      show (tr (i + 1)).1.ths[t]? = some ⟨[], .idle⟩
      rw [hsucc i]
      exact XMach.step_rest _ _ h
  intro i hi
  refine List.all_eq_true.2 fun T hT => ?_
  obtain ⟨u, hu⟩ := List.getElem?_of_mem hT
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hu
  rw [len i] at hlt
  have h := each u hlt i hi
  rw [hu] at h
  rw [Option.some.inj h]
  rfl

/-- **A bound on the length of a fair run.**  Take a well-formed net in
which no agent is listed twice, with a normal form `n` steps away, rules
that write at most `C` agents and `D` segments, `nt` threads, at least one,
and a schedule in which every thread is scheduled in every window of `F`
actions.  Every thread is at rest, `n` claims have been made and the memory
holds the normal form after `F` times

    (n + 1) * X.passBound n C D + n * (C + D + 1) + 1

actions: for each thread one pass over the agents, one more for each claim
whoever makes it, and the writes of each claim.  The threads are not added
up: the bound does not grow with their number, except that the window
cannot be shorter than it. -/
theorem XMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((n + 1) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((XMach.init X nt).trace xs σ i).1.resting = true ∧
      ((XMach.init X nt).trace xs σ i).2 = n ∧
      ((XMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  have live := XMach.trace_live (xs := xs) σ (XMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((XMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((XMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := XMach.trace_run xs σ (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((XMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  have len : ∀ i, ((XMach.init X nt).trace xs σ i).1.ths.length = nt := by
    intro i
    rw [XMach.trace_length]
    show ((List.range nt).map _).length = nt
    rw [List.length_map, List.length_range]
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
  intro i hi
  have hrest : ((XMach.init X nt).trace xs σ i).1.resting = true := by
    refine XMach.settles_within (xs := xs) ((XMach.init X nt).trace xs σ) σ (fun _ => rfl)
      live bound len hb nd hH ahead hA hfair
      (B := (n + 1) * X.passBound n C D + n * (C + D + 1)) (fun t ht => ?_) i hi
    obtain ⟨-, pr⟩ := Steps.links hX hs
    have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
    have hscan : N'.scan (X.wires.length + D * n) X.agents ≤
        7 * X.agents.length + (X.wires.length + D * n) :=
      Net.scan_le hH X.agents hnd fun e he q q' h h' =>
        hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
          (pr (.inl ⟨e.2, hag e he⟩) h')
    have hp : 7 * X.agents.length + (X.wires.length + D * n) ≤ X.passBound n C D := by
      show _ ≤ 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)
      omega
    have e1 : C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1 =
        X.passBound n C D + (C + D + 1) := by
      show _ = 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + (C + D + 1)
      omega
    have ep : (XMach.init X nt).potAt N' (X.wires.length + D * n)
        (X.agents.length + (C - 2) * n) t =
        N'.scan (X.wires.length + D * n) X.agents := by
      rw [XMach.potAt_eq (XMach.init_thread X ht)]
      show N'.scan (X.wires.length + D * n) (X.agents.drop t ++ X.agents.take t) = _
      have e : N'.scan (X.wires.length + D * n) X.agents =
          N'.scan (X.wires.length + D * n) (X.agents.take t) +
            N'.scan (X.wires.length + D * n) (X.agents.drop t) := by
        rw [← Net.scan_append, List.take_append_drop]
      rw [Net.scan_append, e]
      exact Nat.add_comm _ _
    show (XMach.init X nt).potAt N' (X.wires.length + D * n) (X.agents.length + (C - 2) * n) t +
        (n - 0) * (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) ≤
      (n + 1) * X.passBound n C D + n * (C + D + 1)
    rw [ep, Nat.sub_zero, e1, Nat.mul_add n (X.passBound n C D) (C + D + 1),
      Nat.add_mul n 1 (X.passBound n C D), Nat.one_mul]
    omega
  obtain ⟨hq, hnorm⟩ := (live i).rest hrest
  obtain ⟨-, hu⟩ := (run i).final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨hrest, e₂.symm, e₁.symm⟩

/-- **A bound for one thread alone**: it is at rest with the normal form
after `(n + 1) * X.passBound n C D + n * (C + D + 1) + 1` actions. -/
theorem XMach.solo_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D) {n : Nat}
    {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') :
    ∀ i, (n + 1) * X.passBound n C D + n * (C + D + 1) + 1 ≤ i →
      ((XMach.init X 1).trace xs (fun _ => 0) i).1.resting = true ∧
      ((XMach.init X 1).trace xs (fun _ => 0) i).2 = n ∧
      ((XMach.init X 1).trace xs (fun _ => 0) i).1.mem.toNet = N' := by
  intro i hi
  refine XMach.fair_bound hX hnd (Nat.succ_pos 0) hb hs hn (fun _ => 0) (F := 1)
    (fun u hu j => ⟨j, Nat.le_refl _, Nat.lt_succ_self _, ?_⟩) i ?_
  · show 0 = u
    omega
  · rw [Nat.one_mul]
    exact hi

/-- Distinct threads scheduled in one window take as many actions of it. -/
theorem window_distinct (σ : Nat → Nat) : ∀ (F : Nat) (us : List Nat) (i : Nat), us.Nodup →
    (∀ u, u ∈ us → ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) → us.length ≤ F
  | 0, us, i, _, h => by
    cases us with
    | nil => exact Nat.le_refl _
    | cons u us =>
      obtain ⟨j, h₁, h₂, -⟩ := h u List.mem_cons_self
      omega
  | F + 1, us, i, hnd, h => by
    have ih := window_distinct σ F (us.erase (σ i)) (i + 1) (hnd.erase _) fun u hu => by
      obtain ⟨hne, hu'⟩ := hnd.mem_erase_iff.1 hu
      obtain ⟨j, h₁, h₂, h₃⟩ := h u hu'
      have hj : j ≠ i := fun e => hne (by rw [← h₃, e])
      exact ⟨j, by omega, by omega, h₃⟩
    have hl := List.length_erase (a := σ i) (l := us)
    split at hl <;> omega

/-- **A window in which every one of `nt` threads is scheduled has at least
`nt` actions.**  This is the only way the number of threads enters the
bound of `XMach.fair_bound`. -/
theorem fair_window_le {σ : Nat → Nat} {nt F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) : nt ≤ F := by
  have h := window_distinct σ F (List.range nt) 0 List.nodup_range fun u hu =>
    hfair u (List.mem_range.1 hu) 0
  rw [List.length_range] at h
  exact h

/-- Threads scheduled in turn are each scheduled in every window of as many
actions as there are threads. -/
theorem roundRobin_fair {nt : Nat} :
    ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + nt ∧ j % nt = u := by
  intro u hu i
  have hnt : 0 < nt := by omega
  have hd := Nat.div_add_mod i nt
  have hr := Nat.mod_lt i hnt
  rcases Nat.lt_or_ge u (i % nt) with h | h
  · refine ⟨nt * (i / nt + 1) + u, ?_, ?_, ?_⟩
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
  · refine ⟨nt * (i / nt) + u, by omega, by omega, ?_⟩
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hu]

/-- **A bound for threads scheduled in turn**, one action each: `nt` threads
are at rest with the normal form after `nt` times the bound of one thread
alone. -/
theorem XMach.roundRobin_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') :
    ∀ i, nt * ((n + 1) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((XMach.init X nt).trace xs (· % nt) i).1.resting = true ∧
      ((XMach.init X nt).trace xs (· % nt) i).2 = n ∧
      ((XMach.init X nt).trace xs (· % nt) i).1.mem.toNet = N' :=
  XMach.fair_bound hX hnd hnt hb hs hn (· % nt) roundRobin_fair

end Bound

end INet
