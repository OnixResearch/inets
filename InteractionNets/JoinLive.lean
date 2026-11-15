import InteractionNets.JoinWalk
import InteractionNets.WorkLive

/-! # The program that walks the joined wires does not rest early

The argument of `WMach.Live` carries over with one change: a thread that
writes a rule that joins interface ports no longer answers for every
active pair, only for those whose wire runs through one of its joined
segments (`JEnds`).  A claim makes no other new pair without a new agent
in it (`Redex.of_fire_join`), and a walk that stops early has met a
segment not yet written, an agent held by another thread, or a loop,
which carries no pair (`Walk.cycle_false`). -/

namespace INet

section Wires

variable {V : Type} {L : V → V → Prop} {T : V → Prop}

/-- **A walk that starts like another follows it**: if a walk to a
terminal starts with the first segment of a walk to a point that is not a
terminal, it runs along the second, and goes on from its last segment. -/
theorem Walk.follow (hW : Wiring L T) {u v x' z : V} (C : Walk L T u v x' z) :
    ∀ {x y : V}, Walk L T u v x y → T y → ¬ T z → Walk L T x' z x y := by
  induction C with
  | single _ => exact fun W _ _ => W
  | cons h hv hw C' ih =>
    intro x y W hy hz
    cases W with
    | single _ => exact absurd hy hv
    | cons _ _ hw₂ W' =>
      rcases hW.deg (hW.symm h) W'.link_first C'.link_first with e | e | e
      · exact absurd e.symm hw₂
      · exact absurd e.symm hw
      · subst e
        exact ih W' hy hz

/-- **A wire that closes on itself has no end**: no walk that starts with
the first segment of a closed walk reaches a terminal. -/
theorem Walk.cycle_false (hW : Wiring L T) {u v x y : V} (W : Walk L T u v x y) (hy : T y) :
    ∀ {c z : V}, Walk L T u v c z → z = u → c ≠ v → ¬ T u → False := by
  induction W with
  | single h =>
    intro c z C hz hc hu
    cases C with
    | single _ => exact hc hz.symm
    | cons _ hv _ _ => exact hv hy
  | cons h hv hw W' ih =>
    intro c z C hz hc hu
    cases C with
    | single _ => exact hc hz.symm
    | cons _ _ hw' C' =>
      rcases hW.deg (hW.symm h) W'.link_first C'.link_first with e | e | e
      · exact hw e.symm
      · exact hw' e.symm
      · subst e hz
        exact ih hy (C'.snoc hu h (Ne.symm hc)) rfl (Ne.symm hw) hv

/-- In a wiring where a point lies on two segments at most, every point of
a trail but its start and the last one reached has all its neighbours on
the trail. -/
theorem Trail.closed' (hs : ∀ {p q}, L p q → L q p)
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z) {u : V} :
    ∀ {ws : List V}, Trail L u ws → ∀ c vs, ws = c :: vs →
      ∀ x, x ∈ vs → x ≠ u → ∀ y, L x y → y ∈ ws := by
  intro ws t
  induction t with
  | start =>
    intro c vs e x hx
    obtain ⟨-, rfl⟩ := List.cons.inj e
    exact absurd hx List.not_mem_nil
  | @step c₀ q₀ vs₀ t hl hf ih =>
    intro c vs e x hx hxu y hy
    obtain ⟨-, rfl⟩ := List.cons.inj e
    rcases List.mem_cons.1 hx with rfl | hx
    · cases t with
      | start => exact absurd rfl hxu
      | step _ hl' _ =>
        rename_i p vs'
        rcases hd (hs hl') hl hy with e | e | e
        · exact absurd (e ▸ List.mem_cons_of_mem _ List.mem_cons_self) hf
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (e ▸ List.mem_cons_self))
        · exact List.mem_cons.2 (.inl e.symm)
    · exact List.mem_cons_of_mem _ (ih c₀ vs₀ rfl x hx hxu y hy)

/-- **The next point is new, or the start**: following a segment that does
not go back to the point one came from leads off the trail or back to its
start. -/
theorem Trail.fresh' (hs : ∀ {p q}, L p q → L q p) (hi : ∀ {p}, ¬ L p p)
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z) {u c p q : V}
    {vs : List V} (t : Trail L u (c :: p :: vs)) (hl : L c q) (hq : q ≠ p) :
    q ∉ c :: p :: vs ∨ q = u := by
  by_cases hqu : q = u
  · exact .inr hqu
  refine .inl fun hm => ?_
  cases t with
  | step t' _ hf =>
    rcases List.mem_cons.1 hm with e | hm
    · rw [e] at hl
      exact hi hl
    · rcases List.mem_cons.1 hm with e | hm
      · exact hq e
      · exact hf (Trail.closed' hs hd t' p vs rfl q hm hqu c (hs hl))

end Wires

variable {S : Type} {sys : System S}

/-- The wire through the segment from `p` to `q` has the principal port of
`a` at the end beyond `p` and that of `b` at the end beyond `q`. -/
def JEnds (ar : S → Nat) (G : Net S) (p q : Port) (a b : Id) : Prop :=
  (∃ x, Walk G.link (G.End ar) q p x (a, 0)) ∧ ∃ y, Walk G.link (G.End ar) p q y (b, 0)

/-- **Firing keeps a wire between two ends that are not on the fired
agents.** -/
theorem JEnds.fire {ar : S → Nat} {G : Net S} {c d : Id} {γ δ : S} {R : Rhs S}
    (site : Site ar G c d γ δ) {p q : Port} {a b : Id} (h : JEnds ar G p q a b) :
    JEnds ar (G.fire c d R) p q a b := by
  obtain ⟨⟨x, w₁⟩, ⟨y, w₂⟩⟩ := h
  exact ⟨⟨x, site.walk_fire w₁⟩, ⟨y, site.walk_fire w₂⟩⟩

/-- A walk after a firing that starts with an old segment either is a walk
before the firing, or runs along old segments to an auxiliary port of a
fired agent and goes on by a segment of the rule that joins it to another,
or ends at a port of a new agent. -/
theorem walk_split {G : Net S} {c d : Id} {γ δ : S} {R : Rhs S}
    (site : Site sys.ar G c d γ δ) (hRwf : R.WF sys.ar γ δ) :
    ∀ {u v x y : Port}, Walk (G.fire c d R).link ((G.fire c d R).End sys.ar) u v x y →
      G.link u v → (∀ o j, y.1 ≠ child c d o j) →
      Walk G.link (G.End sys.ar) u v x y ∨
      ∃ x₀ s₁ s₂, Walk G.link (G.End sys.ar) u v x₀ s₁ ∧ Site.NewLink c d R s₁ s₂ ∧
        (∃ s k s' k', s₁ = emb c d (.ifc s k) ∧ s₂ = emb c d (.ifc s' k')) := by
  have hG := site.wf
  intro u v x y w
  induction w with
  | single h => exact fun hl _ => .inl (.single hl)
  | cons h hv hw w' ih =>
    rename_i u v w₂ x y
    intro hl hy
    by_cases hE : G.End sys.ar v
    · -- `v` is an end of `G` and not of the new net: a port of a fired agent
      have hnext := w'.link_first
      rcases hnext with ho | ⟨x', y', hxy, ev, ew⟩
      · exact absurd (hG.end_unique hE ho (hG.symm hl)) hw
      · cases x' with
        | new o j k =>
          have hu : G.Used v.1 := .inr (.inl ⟨v.2, u, hG.symm hl⟩)
          rw [ev] at hu
          exact absurd hu (site.not_used_child o j)
        | ifc s k =>
          cases y' with
          | new o j k' =>
            -- the next point is a port of a new agent, an end: the walk stops there
            have hEn : (G.fire c d R).End sys.ar w₂ := by
              obtain ⟨γ', hlab, hk'⟩ :=
                (hRwf.valid (hRwf.symm hxy) : R.Valid sys.ar γ δ (.new o j k'))
              rw [ew]
              exact .inr ⟨γ', .inr ⟨o, j, rfl, hlab⟩, hk'⟩
            cases w' with
            | single _ => exact absurd (congrArg Prod.fst ew) (hy o j)
            | cons _ hv' _ _ => exact absurd hEn hv'
          | ifc s' k' =>
            exact .inr ⟨u, v, w₂, .single hl, ⟨_, _, hxy, ev, ew⟩, s, k, s', k', ev, ew⟩
    · have hl' : G.link v w₂ := by
        rcases w'.link_first with ho | hn
        · exact ho
        · exact absurd (site.end_of_newLink hRwf hn (hG.symm hl)) hE
      rcases ih hl' hy with h₁ | ⟨x₀, s₁, s₂, P, hn, hs⟩
      · exact .inl (.cons hl hE hw h₁)
      · exact .inr ⟨x₀, s₁, s₂, .cons hl hE hw P, hn, hs⟩

/-- **After a firing, an active pair was already one, has a new agent in
it, or its wire runs through a segment of the rule that joins two
interface ports.** -/
theorem Redex.of_fire_join {G : Net S} {c d a b : Id} {γ δ α β : S} {R R' : Rhs S}
    (hG : G.WF sys.ar) (r : Redex sys G c d γ δ R)
    (r' : Redex sys (G.fire c d R) a b α β R') :
    Redex sys G a b α β R' ∨ (∃ o j, a = child c d o j) ∨ (∃ o j, b = child c d o j) ∨
      ∃ s k s' k', R.link (.ifc s k) (.ifc s' k') ∧
        JEnds sys.ar (G.fire c d R) (emb c d (.ifc s k)) (emb c d (.ifc s' k')) a b := by
  have site : Site sys.ar G c d γ δ := ⟨hG, r.ha, r.hb, r.ne, r.conn⟩
  have hRwf := sys.rule_wf r.rule
  have hG' := site.fire_wf hRwf
  by_cases ha : ∃ o j, a = child c d o j
  · exact .inr (.inl ha)
  by_cases hb : ∃ o j, b = child c d o j
  · exact .inr (.inr (.inl hb))
  have oldAgent : ∀ {i : Id} {ε : S}, (G.fire c d R).agent i ε → ¬ (∃ o j, i = child c d o j) →
      G.agent i ε ∧ i ≠ c ∧ i ≠ d := by
    intro i ε h hi
    rcases h with h | ⟨o, j, e, -⟩
    · exact h
    · exact absurd ⟨o, j, e⟩ hi
  obtain ⟨hga, hac, had⟩ := oldAgent r'.ha ha
  obtain ⟨hgb, -, -⟩ := oldAgent r'.hb hb
  obtain ⟨v, x, w⟩ := r'.conn
  have hfirst : G.link (a, 0) v := by
    rcases w.link_first with h | ⟨x', y', -, e, -⟩
    · exact h
    · cases x' with
      | ifc s k =>
        have e2 : (0 : Nat) = k + 1 := congrArg Prod.snd e
        omega
      | new o j k => exact absurd ⟨o, j, congrArg Prod.fst e⟩ ha
  rcases walk_split site hRwf w hfirst (fun o j e => hb ⟨o, j, e⟩) with w₀ | hsplit
  · exact .inl ⟨hga, hgb, r'.ne, ⟨v, x, w₀⟩, r'.rule⟩
  obtain ⟨x₀, s₁, s₂, P, ⟨x', y', hxy, e₁, e₂⟩, s, k, s', k', rfl, rfl⟩ := hsplit
  obtain rfl := site.emb_inj e₁
  obtain rfl := site.emb_inj e₂
  refine .inr (.inr (.inr ⟨s, k, s', k', hxy, ?_, ?_⟩))
  · -- back from the second auxiliary port, along the old segments, to `a`
    have hk' : k' < sys.ar (sel γ δ s') := hRwf.valid (hRwf.symm hxy)
    have hE₂ : G.End sys.ar (emb c d (.ifc s' k')) :=
      .inr ⟨_, site.agent_sel s', Nat.succ_le_of_lt hk'⟩
    have hx₀ : x₀ ≠ emb c d (.ifc s' k') := by
      rcases P.penult with e | hn
      · rw [e]
        intro e'
        have e2 : (0 : Nat) = k' + 1 := congrArg Prod.snd e'
        omega
      · exact fun e => hn (e ▸ hE₂)
    exact ⟨v, .cons (.inr ⟨_, _, hRwf.symm hxy, rfl, rfl⟩) (site.not_end_fire_sel s _) hx₀
      (site.walk_fire (P.rev hG.symm))⟩
  · -- on along the wire, past the joined segment, to `b`
    have hk' : k' < sys.ar (sel γ δ s') := hRwf.valid (hRwf.symm hxy)
    have hE₂ : G.End sys.ar (emb c d (.ifc s' k')) :=
      .inr ⟨_, site.agent_sel s', Nat.succ_le_of_lt hk'⟩
    have hx₀ : emb c d (.ifc s' k') ≠ x₀ := by
      rcases P.penult with e | hn
      · rw [e]
        intro e'
        have e2 : k' + 1 = 0 := congrArg Prod.snd e'
        omega
      · exact fun e => hn (e ▸ hE₂)
    have C := (site.walk_fire (R := R) P).snoc (site.not_end_fire_sel s _)
      (.inr ⟨_, _, hxy, rfl, rfl⟩) hx₀
    exact ⟨x, Walk.follow hG'.wiring C w r'.end_right (site.not_end_fire_sel s' _)⟩

/-- Swap the two sides of a joined segment. -/
theorem JEnds.swap {ar : S → Nat} {G : Net S} {p q : Port} {a b : Id} (h : JEnds ar G p q a b) :
    JEnds ar G q p b a :=
  ⟨h.2, h.1⟩

/-- **A reader on the wire of a pair**: a walk from the principal port of
`a` that has come to a point `c` that is not an end, with a segment on to
`q`, makes the wire of the pair run through that segment. -/
theorem JEnds.reader {ar : S → Nat} {G : Net S} (hG : G.WF ar) {a b : Id} {v p c q : Port}
    (W : Walk G.link (G.End ar) (a, 0) v p c) (hc : G.Conn ar (a, 0) (b, 0))
    (hEa : G.End ar (a, 0)) (hEb : G.End ar (b, 0)) (hEc : ¬ G.End ar c) (hl : G.link c q)
    (hq : q ≠ p) : JEnds ar G c q a b := by
  refine ⟨⟨v, .cons (hG.symm hl) hEc (Ne.symm hq) (W.rev hG.symm)⟩, ?_⟩
  obtain ⟨v₂, x₂, w₂⟩ := hc
  obtain rfl := hG.end_unique hEa W.link_first w₂.link_first
  have F := Walk.follow hG.wiring W w₂ hEb hEc
  cases F with
  | single _ => exact absurd hEb hEc
  | cons h _ hn F' =>
    rcases hG.deg (hG.symm h) F'.link_first hl with e | e | e
    · exact absurd e.symm hn
    · exact absurd e.symm hq
    · exact ⟨x₂, e ▸ F'⟩

/-- **A side of a walk on the wire of a pair**: a walk that starts with the
joined segment from `u` to `v` and has come to a point `cur` that is not an
end, with a segment on to `q`, makes the wire run through that segment. -/
theorem JEnds.cursor {ar : S → Nat} {G : Net S} (hG : G.WF ar) {a b : Id} {u v prev cur q : Port}
    (C : Walk G.link (G.End ar) u v prev cur) (J : JEnds ar G v u a b)
    (hEa : G.End ar (a, 0)) (hEb : G.End ar (b, 0)) (hEu : ¬ G.End ar u)
    (hEc : ¬ G.End ar cur) (hl : G.link cur q) (hq : q ≠ prev) : JEnds ar G cur q b a := by
  obtain ⟨⟨x, wa⟩, ⟨y, wb⟩⟩ := J
  refine ⟨?_, ?_⟩
  · cases wb with
    | single _ => exact absurd hEb hEu
    | cons h hu hz W'' =>
      exact ⟨y, .cons (hG.symm hl) hEc (Ne.symm hq) ((C.rev hG.symm).append hEu W'' hz)⟩
  · have F := Walk.follow hG.wiring C wa hEa hEc
    cases F with
    | single _ => exact absurd hEa hEc
    | cons h _ hn F' =>
      rcases hG.deg (hG.symm h) F'.link_first hl with e | e | e
      · exact absurd e.symm hn
      · exact absurd e.symm hq
      · exact ⟨x, e ▸ F'⟩

section JLive

variable [DecidableEq S] {xs : XSys S}

/-- The thread answers for the pair of `a` and `b`: one of the two is in its
list or is the agent it attempts, or the wire of the pair runs through a
joined segment that it has still to walk or is walking. -/
def JThread.Answers (ar : S → Nat) (G : Net S) (T : JThread S) (a b : Id) (α β : S) : Prop :=
  (a, α) ∈ T.todo ∨ (b, β) ∈ T.todo ∨ T.st.target = some a ∨ T.st.target = some b ∨
    (∃ pq, pq ∈ T.joins ∧ (JEnds ar G pq.1 pq.2 a b ∨ JEnds ar G pq.2 pq.1 a b)) ∨
    ∃ w, T.walk = some w ∧ (JEnds ar G w.s₁ w.s₂ a b ∨ JEnds ar G w.s₂ w.s₁ a b)

/-- What one side of a walk has read, starting with the segment from `u` to
`v`: the walk so far, a trail of the points met, and, at a principal port,
the agent found there. -/
def JCur.Ok (ar : S → Nat) (G : Net S) (u v : Port) : JCur S → Prop
  | .go prev cur => Walk G.link (G.End ar) u v prev cur ∧ cur ≠ u ∧ (cur = v → prev = u) ∧
      ∃ vs, Trail G.link u (cur :: prev :: vs) ∧ v ∈ cur :: prev :: vs
  | .prin i γ => (∃ x, Walk G.link (G.End ar) u v x (i, 0)) ∧ G.Used i ∧
      (∀ γ', G.agent i γ' → γ' = γ) ∧ ∀ q q', G.link (i, 0) q → G.link (i, 0) q' → q = q'
  | .stop => False

/-- A walk under way: the joined segment is a segment of the goal between
two points that are not ends, each side is as it should be, and the walk
has not yet found anything. -/
def JWalk.Ok (ar : S → Nat) (G : Net S) (w : JWalk S) : Prop :=
  G.link w.s₁ w.s₂ ∧ ¬ G.End ar w.s₁ ∧ ¬ G.End ar w.s₂ ∧ JCur.Ok ar G w.s₂ w.s₁ w.c₁ ∧
    JCur.Ok ar G w.s₁ w.s₂ w.c₂ ∧ w.found = none

/-- After an action of thread `t`, which leaves it as `T₁`, someone answers
for the pair. -/
def JNewAns (ar : S → Nat) (G : Net S) (ths : List (JThread S)) (t : Nat) (T₁ : JThread S)
    (a b : Id) (α β : S) : Prop :=
  T₁.Answers ar G a b α β ∨
    ∃ (u : Nat) (U : JThread S), u ≠ t ∧ ths[u]? = some U ∧ U.Answers ar G a b α β

/-- The invariant. -/
structure JMach.Live (xs : XSys S) (M : JMach S) : Prop where
  inv : M.toMach.Inv xs.sys
  /-- Every active pair of the goal with a rule is answered for. -/
  cov : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
    ∃ (t : Nat) (T : JThread S), M.ths[t]? = some T ∧ T.Answers xs.sys.ar M.toMach.goal a b α β
  /-- What the threads have read is still true. -/
  sane : ∀ (t : Nat) (T : JThread S), M.ths[t]? = some T → T.st.Sane M.toMach.goal
  /-- A writer has the agents it is writing in its list. -/
  kids : ∀ (t : Nat) (T : JThread S), M.ths[t]? = some T → ∀ i γ, T.st.pendA i γ →
    (i, γ) ∈ T.todo
  /-- A segment that a writer has still to write ends at a port of an agent
  it has still to write, or is a joined segment it has still to walk. -/
  own : ∀ (t : Nat) (T : JThread S), M.ths[t]? = some T → ∀ p q, T.st.pendL p q →
    (∃ i γ k, T.st.pendA i γ ∧ k ≤ xs.sys.ar γ ∧ (p = (i, k) ∨ q = (i, k))) ∨
      (p, q) ∈ T.joins ∨ (q, p) ∈ T.joins
  /-- Only a writer has joined segments to walk, or a walk under way. -/
  quiet : ∀ (t : Nat) (T : JThread S), M.ths[t]? = some T → ¬ T.st.writing →
    T.joins = [] ∧ T.walk = none
  /-- A walk is under way only once everything is written. -/
  wst : ∀ (t : Nat) (T : JThread S) (w : JWalk S), M.ths[t]? = some T → T.walk = some w →
    T.st = .write [] []
  /-- A thread whose rule joins nothing has nothing to walk. -/
  nojoin : ∀ (t : Nat) (T : JThread S), M.ths[t]? = some T → T.again = false →
    T.joins = [] ∧ T.walk = none
  /-- A joined segment still to walk is a segment of the goal between two
  points that are not ends. -/
  jok : ∀ (t : Nat) (T : JThread S), M.ths[t]? = some T → ∀ pq, pq ∈ T.joins →
    M.toMach.goal.link pq.1 pq.2 ∧ ¬ M.toMach.goal.End xs.sys.ar pq.1 ∧
      ¬ M.toMach.goal.End xs.sys.ar pq.2
  /-- A walk under way is as it should be. -/
  wok : ∀ (t : Nat) (T : JThread S) (w : JWalk S), M.ths[t]? = some T → T.walk = some w →
    JWalk.Ok xs.sys.ar M.toMach.goal w

omit [DecidableEq S] in
theorem JMach.get_toW {M : JMach S} {u : Nat} {U' : WThread S}
    (h : M.toW.ths[u]? = some U') : ∃ U, M.ths[u]? = some U ∧ U.toW = U' := by
  have h' : (M.ths.map JThread.toW)[u]? = some U' := h
  rw [List.getElem?_map] at h'
  cases hu : M.ths[u]? with
  | none =>
    rw [hu] at h'
    cases h'
  | some U =>
    rw [hu] at h'
    exact ⟨U, rfl, Option.some.inj h'⟩

omit [DecidableEq S] in
theorem JMach.toW_get {M : JMach S} {u : Nat} {U : JThread S} (h : M.ths[u]? = some U) :
    M.toW.ths[u]? = some U.toW := by
  show (M.ths.map JThread.toW)[u]? = _
  rw [List.getElem?_map, h]
  rfl

omit [DecidableEq S] in
theorem JMach.Live.ok {M : JMach S} (hL : M.Live xs) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) : T.st.Ok M.mem.toNet := by
  have h : (threadOf ((M.ths.map JThread.toW).map WThread.toX) t).Ok M.mem.toNet := hL.inv.ok t
  rw [threadOf_mapJ_eq ht] at h
  exact h

omit [DecidableEq S] in
theorem JMach.Live.lift {M : JMach S} (hL : M.Live xs) {u v x y : Port}
    (w : Walk M.mem.toNet.link (fun _ => False) u v x y) :
    Walk M.toMach.goal.link (M.toMach.goal.End xs.sys.ar) u v x y :=
  w.mono_term (fun hl => .inl hl) (fun hl => .inl hl) hL.inv.wf.symm (fun hT => hT)
    hL.inv.wf.end_unique

omit [DecidableEq S] in
/-- An agent of the goal is in memory, or held by a thread, or still to be
written by one. -/
theorem JMach.goal_agent {M : JMach S} {i : Id} {γ : S} (h : M.toMach.goal.agent i γ) :
    (i, γ) ∈ M.mem.agents ∨
      (∃ (u : Nat) (U : JThread S), M.ths[u]? = some U ∧ U.st.held i γ) ∨
      ∃ (u : Nat) (U : JThread S), M.ths[u]? = some U ∧ U.st.pendA i γ := by
  rcases WMach.goal_agent (M := M.toW) h with hm | ⟨u, U', hu, hU⟩ | ⟨u, U', hu, hU⟩
  · exact .inl hm
  · obtain ⟨U, hu', rfl⟩ := JMach.get_toW hu
    exact .inr (.inl ⟨u, U, hu', hU⟩)
  · obtain ⟨U, hu', rfl⟩ := JMach.get_toW hu
    exact .inr (.inr ⟨u, U, hu', hU⟩)

omit [DecidableEq S] in
theorem JMach.goal_link {M : JMach S} {p q : Port} (h : M.toMach.goal.link p q) :
    (p, q) ∈ M.mem.wires ∨
      ∃ (u : Nat) (U : JThread S), M.ths[u]? = some U ∧ U.st.pendL p q := by
  rcases WMach.goal_link (M := M.toW) h with hm | ⟨u, U', hu, hU⟩
  · exact .inl hm
  · obtain ⟨U, hu', rfl⟩ := JMach.get_toW hu
    exact .inr ⟨u, U, hu', hU⟩

omit [DecidableEq S] in
/-- An agent of the pair that is not in memory is held by another thread,
which attempts it, or is still to be written by another thread, which has
it in its list. -/
theorem JMach.Live.ans_of_agent {M : JMach S} (hL : M.Live xs) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) {a b : Id} {α β : S} {i : Id} {γ : S}
    (hi : (i = a ∧ γ = α) ∨ (i = b ∧ γ = β))
    (hg : M.toMach.goal.agent i γ) (hnm : (i, γ) ∉ M.mem.agents) (hT : ¬ T.st.held i γ)
    (hTp : ¬ T.st.pendA i γ) (T₁ : JThread S) :
    JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β := by
  rcases JMach.goal_agent hg with hm | ⟨u, U, hu, hU⟩ | ⟨u, U, hu, hU⟩
  · exact absurd hm hnm
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hT (Option.some.inj hu ▸ hU)
    refine .inr ⟨u, U, hne, hu, ?_⟩
    rcases hi with ⟨e, -⟩ | ⟨e, -⟩
    · exact .inr (.inr (.inl (e ▸ TState.held_target hU)))
    · exact .inr (.inr (.inr (.inl (e ▸ TState.held_target hU))))
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hTp (Option.some.inj hu ▸ hU)
    have hk := hL.kids u U hu i γ hU
    refine .inr ⟨u, U, hne, hu, ?_⟩
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl hk
    · exact .inr (.inl hk)

omit [DecidableEq S] in
/-- A segment of the goal that is not in memory is still to be written by
another thread.  The segment ends at a port of an agent the thread is
writing, which is an end of the goal, or it is a joined segment of the
thread: when the wire of the pair runs through it, the thread answers for
the pair. -/
theorem JMach.Live.ans_of_link {M : JMach S} (hL : M.Live xs) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) {a b : Id} {α β : S} {R : Rhs S}
    (r : Redex xs.sys M.toMach.goal a b α β R) {p q : Port} (hg : M.toMach.goal.link p q)
    (hnm : (p, q) ∉ M.mem.wires) (hTp : ¬ T.st.pendL p q)
    (hon : ∀ z, (z = p ∨ z = q) → M.toMach.goal.End xs.sys.ar z → z = (a, 0) ∨ z = (b, 0))
    (hJ : JEnds xs.sys.ar M.toMach.goal p q a b ∨ JEnds xs.sys.ar M.toMach.goal p q b a)
    (T₁ : JThread S) : JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β := by
  have hG := hL.inv.wf
  rcases JMach.goal_link hg with hm | ⟨u, U, hu, hU⟩
  · exact absurd hm hnm
  · have hne : u ≠ t := by
      intro e
      rw [e, ht] at hu
      exact hTp (Option.some.inj hu ▸ hU)
    refine .inr ⟨u, U, hne, hu, ?_⟩
    rcases hL.own u U hu p q hU with ⟨i, γ, k, hpa, hk, hz⟩ | hj | hj
    · have hgi : M.toMach.goal.agent i γ := by
        refine .inr ⟨u, ?_⟩
        show (threadOf ((M.ths.map JThread.toW).map WThread.toX) u).pendA i γ
        rw [threadOf_mapJ_eq hu]
        exact hpa
      have hE : M.toMach.goal.End xs.sys.ar (i, k) := .inr ⟨γ, hgi, hk⟩
      have hm := hL.kids u U hu i γ hpa
      rcases hon (i, k) (hz.imp (fun e => e.symm) (fun e => e.symm)) hE with e | e
      · obtain ⟨rfl, -⟩ := Prod.mk.inj e
        rw [hG.agent_fun hgi r.ha] at hm
        exact .inl hm
      · obtain ⟨rfl, -⟩ := Prod.mk.inj e
        rw [hG.agent_fun hgi r.hb] at hm
        exact .inr (.inl hm)
    · refine .inr (.inr (.inr (.inr (.inl ⟨(p, q), hj, ?_⟩))))
      rcases hJ with h | h
      · exact .inl h
      · exact .inr h.swap
    · refine .inr (.inr (.inr (.inr (.inl ⟨(q, p), hj, ?_⟩))))
      rcases hJ with h | h
      · exact .inr h
      · exact .inl h.swap

theorem JMach.step_eq {M : JMach S} {t : Nat} {T T₁ : JThread S} {X₁ : XNet S} {c : Nat}
    (ht : M.ths[t]? = some T) (hact : JMach.act xs M.mem T = (X₁, T₁, c)) :
    M.step xs t = (⟨X₁, M.ths.set t T₁⟩, c) := by
  unfold JMach.step
  rw [ht]
  dsimp only
  rw [hact]

/-- An action that makes no claim keeps the invariant, if the thread is
still answered for and its own parts of the invariant still hold. -/
theorem JMach.Live.step_zero {M : JMach S} (hL : M.Live xs) {t : Nat} {T T₁ : JThread S}
    {X₁ : XNet S} (ht : M.ths[t]? = some T) (hact : JMach.act xs M.mem T = (X₁, T₁, 0))
    (hsane : T₁.st.Sane M.toMach.goal)
    (hkids : ∀ i γ, T₁.st.pendA i γ → (i, γ) ∈ T₁.todo)
    (hown : ∀ p q, T₁.st.pendL p q →
      (∃ i γ k, T₁.st.pendA i γ ∧ k ≤ xs.sys.ar γ ∧ (p = (i, k) ∨ q = (i, k))) ∨
        (p, q) ∈ T₁.joins ∨ (q, p) ∈ T₁.joins)
    (hquiet : ¬ T₁.st.writing → T₁.joins = [] ∧ T₁.walk = none)
    (hwst : ∀ w, T₁.walk = some w → T₁.st = .write [] [])
    (hnojoin : T₁.again = false → T₁.joins = [] ∧ T₁.walk = none)
    (hjok : ∀ pq, pq ∈ T₁.joins → M.toMach.goal.link pq.1 pq.2 ∧
      ¬ M.toMach.goal.End xs.sys.ar pq.1 ∧ ¬ M.toMach.goal.End xs.sys.ar pq.2)
    (hwok : ∀ w, T₁.walk = some w → JWalk.Ok xs.sys.ar M.toMach.goal w)
    (hans : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
      T.Answers xs.sys.ar M.toMach.goal a b α β →
      JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β) : (M.step xs t).1.Live xs := by
  have es := JMach.step_eq ht hact
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
  have hbase : (JMach.toMach ⟨X₁, M.ths.set t T₁⟩).Inv xs.sys ∧
      (JMach.toMach ⟨X₁, M.ths.set t T₁⟩).goal = M.toMach.goal := by
    have h := JMach.step_sim xs M t
    rw [es] at h
    rcases h with ⟨e₁, -⟩ | hs
    · have e₁' : JMach.toMach ⟨X₁, M.ths.set t T₁⟩ = M.toMach := e₁
      rw [e₁']
      exact ⟨hL.inv, rfl⟩
    · obtain ⟨hi, hr⟩ := MStep.sim hL.inv hs
      exact ⟨hi, hr.goal_zero rfl⟩
  obtain ⟨hinv, hg⟩ := hbase
  have get : ∀ {u : Nat} {U : JThread S}, (M.ths.set t T₁)[u]? = some U →
      (u = t ∧ U = T₁) ∨ (u ≠ t ∧ M.ths[u]? = some U) := by
    intro u U hu
    by_cases hut : u = t
    · rw [hut, List.getElem?_set_self hlt] at hu
      exact .inl ⟨hut, (Option.some.inj hu).symm⟩
    · rw [List.getElem?_set_ne (Ne.symm hut)] at hu
      exact .inr ⟨hut, hu⟩
  rw [es]
  show JMach.Live xs ⟨X₁, M.ths.set t T₁⟩
  refine ⟨hinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b α β R r
    rw [hg] at r ⊢
    show ∃ (u : Nat) (U : JThread S), (M.ths.set t T₁)[u]? = some U ∧
      U.Answers xs.sys.ar M.toMach.goal a b α β
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
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hquiet
    · exact hL.quiet u U hu'
  · intro u U w hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hwst w
    · exact hL.wst u U w hu'
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hnojoin
    · exact hL.nojoin u U hu'
  · intro u U hu
    rw [hg]
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hjok
    · exact hL.jok u U hu'
  · intro u U w hu
    rw [hg]
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact hwok w
    · exact hL.wok u U w hu'

/-- Away from writing and claiming, the program acts as `XMach`, and keeps
the rest of the thread. -/
theorem JMach.act_lift {X X₁ : XNet S} {todo : List (Id × S)} {st : TState S} {again : Bool}
    {js : List (Port × Port)} {wk : Option (JWalk S)} {T₁ : XThread S}
    (hst : ∀ as ls, st ≠ .write as ls) (h : XMach.act xs X ⟨todo, st⟩ = (X₁, T₁, 0)) :
    JMach.act xs X ⟨todo, st, again, js, wk⟩ = (X₁, ⟨T₁.todo, T₁.st, again, js, wk⟩, 0) := by
  have hw := WMach.act_lift (again := again) hst h
  cases st with
  | idle =>
    show (_, _, _) = _
    rw [show WThread.mk todo .idle again = JThread.toW ⟨todo, .idle, again, js, wk⟩ from rfl] at hw
    rw [hw]
  | look a α =>
    show (_, _, _) = _
    rw [show WThread.mk todo (.look a α) again =
      JThread.toW ⟨todo, .look a α, again, js, wk⟩ from rfl] at hw
    rw [hw]
  | seek a α p c =>
    show (_, _, _) = _
    rw [show WThread.mk todo (.seek a α p c) again =
      JThread.toW ⟨todo, .seek a α p c, again, js, wk⟩ from rfl] at hw
    rw [hw]
  | ready a b α β =>
    show (_, _, _) = _
    rw [show WThread.mk todo (.ready a b α β) again =
      JThread.toW ⟨todo, .ready a b α β, again, js, wk⟩ from rfl] at hw
    rw [hw]
  | half a b α β =>
    unfold WMach.act at hw
    unfold JMach.act
    dsimp only at hw ⊢
    cases hh : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      rw [hh] at hw
      have e := congrArg (fun x => x.2.2) hw
      dsimp only at e
      exact absurd e (by decide)
    | none =>
      rw [hh] at hw
      have e₁ := congrArg Prod.fst hw
      have e₂ := congrArg (fun x => x.2.1.todo) hw
      have e₃ := congrArg (fun x => x.2.1.st) hw
      dsimp only at e₁ e₂ e₃ ⊢
      rw [e₁, e₂, e₃]
  | write as ls => exact absurd rfl (hst as ls)

omit [DecidableEq S] in
/-- What a thread answers for through its joined segments and its walk
stays answered for after a firing by another thread. -/
theorem JThread.Answers.fire {ar : S → Nat} {G : Net S} {c d : Id} {γ δ : S} {R : Rhs S}
    (site : Site ar G c d γ δ) {T : JThread S} {a b : Id} {α β : S}
    (h : T.Answers ar G a b α β) : T.Answers ar (G.fire c d R) a b α β := by
  rcases h with h | h | h | h | ⟨pq, hm, h | h⟩ | ⟨w, hw, h | h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨pq, hm, .inl (h.fire site)⟩))))
  · exact .inr (.inr (.inr (.inr (.inl ⟨pq, hm, .inr (h.fire site)⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨w, hw, .inl (h.fire site)⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨w, hw, .inr (h.fire site)⟩))))

omit [DecidableEq S] in
/-- A point that is not an end and lies on a segment is still not an end
after a firing. -/
theorem not_end_fire {ar : S → Nat} {G : Net S} {c d : Id} {γ δ : S} {R : Rhs S}
    (site : Site ar G c d γ δ) {p q : Port} (hl : G.link p q) (hE : ¬ G.End ar p) :
    ¬ (G.fire c d R).End ar p :=
  fun h => hE (site.end_of_fire_link h hl)

omit [DecidableEq S] in
/-- What one side of a walk has read stays true after a firing. -/
theorem JCur.Ok.fire {ar : S → Nat} {G : Net S} {c d : Id} {γ δ : S} {R : Rhs S}
    (site : Site ar G c d γ δ) {u v : Port} {cur : JCur S} (h : JCur.Ok ar G u v cur) :
    JCur.Ok ar (G.fire c d R) u v cur := by
  cases cur with
  | go prev c' =>
    obtain ⟨w, hne, hv, vs, tr, hm⟩ := h
    exact ⟨site.walk_fire w, hne, hv, vs, tr.mono fun hl => .inl hl, hm⟩
  | prin i γ' =>
    obtain ⟨⟨x, w⟩, hU, hf, hu⟩ := h
    have old : ∀ q, (G.fire c d R).link (i, 0) q → G.link (i, 0) q := by
      intro q h'
      rcases h' with h' | ⟨x, y, -, e, -⟩
      · exact h'
      · cases x with
        | ifc s k =>
          have e2 : (0 : Nat) = k + 1 := congrArg Prod.snd e
          omega
        | new o j k =>
          have e1 : i = child c d o j := congrArg Prod.fst e
          exact absurd (e1 ▸ hU) (site.not_used_child o j)
    refine ⟨⟨x, site.walk_fire w⟩, Net.used_fire site.wf hU c d R, fun γ'' h' => ?_,
      fun q q' h h' => hu q q' (old q h) (old q' h')⟩
    rcases h' with ⟨h', -, -⟩ | ⟨o, j, e, -⟩
    · exact hf γ'' h'
    · exact absurd (e ▸ hU) (site.not_used_child o j)
  | stop => exact h

omit [DecidableEq S] in
/-- A walk under way stays as it should be after a firing. -/
theorem JWalk.Ok.fire {ar : S → Nat} {G : Net S} {c d : Id} {γ δ : S} {R : Rhs S}
    (site : Site ar G c d γ δ) {w : JWalk S} (h : JWalk.Ok ar G w) :
    JWalk.Ok ar (G.fire c d R) w :=
  ⟨.inl h.1, not_end_fire site h.1 h.2.1, not_end_fire site (site.wf.symm h.1) h.2.2.1,
    h.2.2.2.1.fire site, h.2.2.2.2.1.fire site, h.2.2.2.2.2⟩

omit [DecidableEq S] in
/-- A joined segment of a rule joins two interface ports that the rule
wires together. -/
theorem XRhs.mem_joinPairs {R : XRhs S} {ar : S → Nat} {a b : Id} {α β : S} {p q : Port}
    (h : (p, q) ∈ R.joinPairs ar a b α β) :
    ∃ s k s' k', R.wire (.ifc s k) = some (.ifc s' k') ∧ (LPort.ifc s k) ∈ ifcPorts ar α β ∧
      p = emb a b (.ifc s k) ∧ q = emb a b (.ifc s' k') := by
  unfold XRhs.joinPairs at h
  obtain ⟨x, hx, hf⟩ := List.mem_filterMap.1 h
  obtain ⟨s, k, rfl, -⟩ := mem_ifcPorts.1 hx
  cases hw : R.wire (.ifc s k) with
  | none =>
    rw [hw] at hf
    cases hf
  | some y =>
    rw [hw] at hf
    dsimp only at hf
    cases y with
    | new o j k' => cases hf
    | ifc s' k' =>
      split at hf
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
        exact ⟨s, k, s', k', hw, hx, rfl, rfl⟩
      · cases hf

omit [DecidableEq S] in
/-- A rule with a joined segment joins. -/
theorem XRhs.joins_of_mem {R : XRhs S} {ar : S → Nat} {a b : Id} {α β : S} {pq : Port × Port}
    (h : pq ∈ R.joinPairs ar a b α β) : R.joins ar α β = true := by
  obtain ⟨s, k, s', k', hw, hx, -, -⟩ := XRhs.mem_joinPairs (p := pq.1) (q := pq.2) h
  unfold XRhs.joins
  rw [List.any_eq_true]
  exact ⟨_, hx, by rw [hw]; rfl⟩

omit [DecidableEq S] in
/-- Every segment of a rule that joins two interface ports is a joined
segment, one way or the other. -/
theorem XRhs.joinPairs_of_wire {R : XRhs S} {ar : S → Nat} {a b : Id} {α β : S}
    (hwf : R.toRhs.WF ar α β) {s k s' k' : _}
    (hw : R.wire (.ifc s k) = some (.ifc s' k')) :
    (emb a b (.ifc s k), emb a b (.ifc s' k')) ∈ R.joinPairs ar a b α β ∨
      (emb a b (.ifc s' k'), emb a b (.ifc s k)) ∈ R.joinPairs ar a b α β := by
  have hw' : R.wire (.ifc s' k') = some (.ifc s k) := hwf.symm hw
  have hv : k < ar (sel α β s) := hwf.valid hw
  have hv' : k' < ar (sel α β s') := hwf.valid hw'
  have hne : LPort.ifc s k ≠ LPort.ifc s' k' := fun e => hwf.irrefl (e ▸ hw : R.wire _ = _)
  have hr : (LPort.ifc s k).rank ≠ (LPort.ifc s' k').rank := by
    intro e
    apply hne
    simp only [LPort.rank] at e
    cases s <;> cases s' <;> simp at e ⊢ <;> omega
  unfold XRhs.joinPairs
  rcases Nat.lt_or_gt_of_ne hr with h | h
  · refine .inl (List.mem_filterMap.2 ⟨_, mem_ifcPorts.2 ⟨s, k, rfl, hv⟩, ?_⟩)
    rw [hw]
    simp [LPort.isNew, h]
  · refine .inr (List.mem_filterMap.2 ⟨_, mem_ifcPorts.2 ⟨s', k', rfl, hv'⟩, ?_⟩)
    rw [hw']
    simp [LPort.isNew, h]

theorem JMach.act_half_some {X : XNet S} {T : JThread S} {a b : Id} {α β : S} {R : XRhs S}
    (hs : T.st = .half a b α β)
    (h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    JMach.act xs X T = (X.takeAgent b, ⟨R.newAgents a b ++ T.todo,
      .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β),
      R.joins xs.sys.ar α β, R.joinPairs xs.sys.ar a b α β, none⟩, 1) := by
  obtain ⟨todo, st, again, js, wk⟩ := T
  dsimp only at hs
  subst hs
  unfold JMach.act
  dsimp only
  rw [h]

/-- **A claim keeps the invariant.**  A new active pair has a new agent in
it, which is in the thread's list, or its wire runs through a segment that
the thread has joined and will walk. -/
theorem JMach.Live.step_claim {M : JMach S} (hL : M.Live xs) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) {a₀ b₀ : Id} {α₀ β₀ : S} {R : XRhs S}
    (hs : T.st = .half a₀ b₀ α₀ β₀)
    (hh : (if assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ then xs.rule α₀ β₀ else none) = some R) :
    (M.step xs t).1.Live xs := by
  have hact := JMach.act_half_some (xs := xs) (X := M.mem) hs hh
  have es := JMach.step_eq ht hact
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
    exact threadOf_mapJ_eq ht
  obtain ⟨rg, eg⟩ := hL.inv.cas₂_goal e (assoc_mem hc.1) hc.2 hsys hw
  let T₁ : JThread S := ⟨R.newAgents a₀ b₀ ++ T.todo,
    .write (R.newAgents a₀ b₀) (R.newLinks xs.sys.ar a₀ b₀ α₀ β₀),
    R.joins xs.sys.ar α₀ β₀, R.joinPairs xs.sys.ar a₀ b₀ α₀ β₀, none⟩
  have hm1 : ((M.ths.set t T₁).map JThread.toW).map WThread.toX =
      ((M.ths.map JThread.toW).map WThread.toX).set t T₁.toW.toX := by
    rw [List.map_set, List.map_set]
  have hmx : ((M.ths.map JThread.toW).map WThread.toX)[t]? = some T.toW.toX := by
    rw [List.getElem?_map, List.getElem?_map, ht]
    rfl
  have eM : JMach.toMach ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩ =
      ⟨M.toMach.mem.take b₀, upd M.toMach.th t
        (.write (R.newAgents a₀ b₀) (R.newLinks xs.sys.ar a₀ b₀ α₀ β₀))⟩ := by
    show Mach.mk (M.mem.takeAgent b₀).toNet
      (threadOf (((M.ths.set t T₁).map JThread.toW).map WThread.toX)) = _
    rw [hm1, threadOf_set hmx, XNet.takeAgent_toNet]
    rfl
  have eg' : (JMach.toMach ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩).goal =
      M.toMach.goal.fire a₀ b₀ R.toRhs := by
    rw [eM]
    exact eg
  have hinv : (JMach.toMach ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩).Inv xs.sys := by
    have h := JMach.step_sim xs M t
    rw [es] at h
    rcases h with ⟨-, e₂⟩ | hs'
    · cases e₂
    · exact (MStep.sim hL.inv hs').1
  have get : ∀ {u : Nat} {U : JThread S}, (M.ths.set t T₁)[u]? = some U →
      (u = t ∧ U = T₁) ∨ (u ≠ t ∧ M.ths[u]? = some U) := by
    intro u U hu
    by_cases hut : u = t
    · rw [hut, List.getElem?_set_self hlt] at hu
      exact .inl ⟨hut, (Option.some.inj hu).symm⟩
    · rw [List.getElem?_set_ne (Ne.symm hut)] at hu
      exact .inr ⟨hut, hu⟩
  have site : Site xs.sys.ar M.toMach.goal a₀ b₀ α₀ β₀ := ⟨hG, rg.ha, rg.hb, rg.ne, rg.conn⟩
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
  have notWriting : ¬ T.st.writing := by
    rw [hs]
    exact fun x => x
  obtain ⟨hTj, hTw⟩ := hL.quiet t T ht notWriting
  rw [es]
  show JMach.Live xs ⟨M.mem.takeAgent b₀, M.ths.set t T₁⟩
  refine ⟨hinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b α β R' r'
    rw [eg'] at r' ⊢
    show ∃ (u : Nat) (U : JThread S), (M.ths.set t T₁)[u]? = some U ∧ U.Answers _ _ a b α β
    rcases Redex.of_fire_join hG rg r' with r | hka | hkb | ⟨s, k, s', k', hl, hJ⟩
    · obtain ⟨u, U, hu, hA⟩ := hL.cov a b α β R' r
      by_cases hut : u = t
      · rw [hut, ht] at hu
        obtain rfl := Option.some.inj hu
        refine ⟨t, T₁, List.getElem?_set_self hlt, ?_⟩
        rcases hA with hm | hm | htg | htg | ⟨pq, hm, -⟩ | ⟨w, hw', -⟩
        · exact .inl (List.mem_append_right _ hm)
        · exact .inr (.inl (List.mem_append_right _ hm))
        · rw [hs] at htg
          obtain rfl : a₀ = a := Option.some.inj htg
          exact absurd r'.ha gone
        · rw [hs] at htg
          obtain rfl : a₀ = b := Option.some.inj htg
          exact absurd r'.hb gone
        · rw [hTj] at hm
          exact absurd hm List.not_mem_nil
        · rw [hTw] at hw'
          cases hw'
      · exact ⟨u, U, by rw [List.getElem?_set_ne (Ne.symm hut)]; exact hu, hA.fire site⟩
    · exact ⟨t, T₁, List.getElem?_set_self hlt, .inl (List.mem_append_left _ (newKid r'.ha hka))⟩
    · exact ⟨t, T₁, List.getElem?_set_self hlt,
        .inr (.inl (List.mem_append_left _ (newKid r'.hb hkb)))⟩
    · refine ⟨t, T₁, List.getElem?_set_self hlt, .inr (.inr (.inr (.inr (.inl ?_))))⟩
      rcases XRhs.joinPairs_of_wire (a := a₀) (b := b₀) hRwf hl with hm | hm
      · exact ⟨_, hm, .inl hJ⟩
      · exact ⟨_, hm, .inr hJ⟩
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
    · intro p q hp
      obtain ⟨x, y, hxy, rfl, rfl⟩ := hw.link.1 hp
      cases x with
      | new o j k =>
        obtain ⟨γ, hl, hk⟩ := (hRwf.valid hxy : R.toRhs.Valid xs.sys.ar α₀ β₀ (.new o j k))
        exact .inl ⟨child a₀ b₀ o j, γ, k, hw.agent.2 ⟨o, j, rfl, hl⟩, hk, .inl rfl⟩
      | ifc s k =>
        cases y with
        | new o j k' =>
          obtain ⟨γ, hl, hk⟩ :=
            (hRwf.valid (hRwf.symm hxy) : R.toRhs.Valid xs.sys.ar α₀ β₀ (.new o j k'))
          exact .inl ⟨child a₀ b₀ o j, γ, k', hw.agent.2 ⟨o, j, rfl, hl⟩, hk, .inr rfl⟩
        | ifc s' k' => exact .inr (XRhs.joinPairs_of_wire hRwf hxy)
    · exact hL.own u U hu'
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact fun h => absurd trivial h
    · exact hL.quiet u U hu'
  · intro u U w hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact fun h => by cases h
    · exact hL.wst u U w hu'
  · intro u U hu
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · intro hj
      refine ⟨?_, rfl⟩
      show R.joinPairs xs.sys.ar a₀ b₀ α₀ β₀ = []
      cases hjp : R.joinPairs xs.sys.ar a₀ b₀ α₀ β₀ with
      | nil => rfl
      | cons pq rest =>
        have h1 := XRhs.joins_of_mem (pq := pq) (by rw [hjp]; exact List.mem_cons_self)
        have h2 : R.joins xs.sys.ar α₀ β₀ = false := hj
        rw [h1] at h2
        cases h2
    · exact hL.nojoin u U hu'
  · intro u U hu
    rw [eg']
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · intro pq hpq
      obtain ⟨s, k, s', k', hwr, -, e₁, e₂⟩ :=
        XRhs.mem_joinPairs (p := pq.1) (q := pq.2) hpq
      rw [e₁, e₂]
      exact ⟨.inr ⟨_, _, hwr, rfl, rfl⟩, site.not_end_fire_sel s _, site.not_end_fire_sel s' _⟩
    · intro pq hpq
      obtain ⟨h1, h2, h3⟩ := hL.jok u U hu' pq hpq
      exact ⟨.inl h1, not_end_fire site h1 h2, not_end_fire site (hG.symm h1) h3⟩
  · intro u U w hu
    rw [eg']
    rcases get hu with ⟨-, rfl⟩ | ⟨-, hu'⟩
    · exact fun h => by cases h
    · exact fun hw' => (hL.wok u U w hu' hw').fire site

omit [DecidableEq S] in
theorem JThread.Answers.carry {ar : S → Nat} {G : Net S} {T T₁ : JThread S} {a b : Id} {α β : S}
    (h : T.Answers ar G a b α β) (hT₁ : T₁.todo = T.todo) (htg : T₁.st.target = T.st.target)
    (hj : T₁.joins = T.joins) (hw : T₁.walk = T.walk) : T₁.Answers ar G a b α β := by
  rcases h with h | h | h | h | ⟨pq, hm, h⟩ | ⟨w, hw', h⟩
  · exact .inl (by rw [hT₁]; exact h)
  · exact .inr (.inl (by rw [hT₁]; exact h))
  · exact .inr (.inr (.inl (htg.trans h)))
  · exact .inr (.inr (.inr (.inl (htg.trans h))))
  · exact .inr (.inr (.inr (.inr (.inl ⟨pq, by rw [hj]; exact hm, h⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨w, by rw [hw]; exact hw', h⟩))))

omit [DecidableEq S] in
theorem JThread.Answers.symm {ar : S → Nat} {G : Net S} {T : JThread S} {a b : Id} {α β : S}
    (h : T.Answers ar G a b α β) : T.Answers ar G b a β α := by
  rcases h with h | h | h | h | ⟨pq, hm, h | h⟩ | ⟨w, hw, h | h⟩
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inr (.inl ⟨pq, hm, .inr h.swap⟩))))
  · exact .inr (.inr (.inr (.inr (.inl ⟨pq, hm, .inl h.swap⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨w, hw, .inr h.swap⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨w, hw, .inl h.swap⟩))))

omit [DecidableEq S] in
theorem JNewAns.symm {ar : S → Nat} {G : Net S} {ths : List (JThread S)} {t : Nat}
    {T₁ : JThread S} {a b : Id} {α β : S} (h : JNewAns ar G ths t T₁ a b α β) :
    JNewAns ar G ths t T₁ b a β α := by
  rcases h with h | ⟨u, U, hne, hu, hA⟩
  · exact .inl h.symm
  · exact .inr ⟨u, U, hne, hu, hA.symm⟩

omit [DecidableEq S] in
/-- When an attempt fails, the pairs the thread answered for through its
list are still answered for by it; only the agent it was attempting needs
another answer. -/
theorem JMach.Live.ans_of_fail {M : JMach S} (hL : M.Live xs) {t : Nat} {T T₁ : JThread S}
    (hT₁ : T₁.todo = T.todo) (hj : T₁.joins = T.joins) (hw : T₁.walk = T.walk)
    (h : ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R → T.st.target = some a →
      JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β) :
    ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
      T.Answers xs.sys.ar M.toMach.goal a b α β →
      JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β := by
  intro a b α β R r hA
  rcases hA with hm | hm | htg | htg | hJ | hJ
  · exact .inl (.inl (by rw [hT₁]; exact hm))
  · exact .inl (.inr (.inl (by rw [hT₁]; exact hm)))
  · exact h a b α β R r htg
  · obtain ⟨R', r', -⟩ := r.flip hL.inv.wf
    exact (h b a β α R' r' htg).symm
  · exact .inl (.inr (.inr (.inr (.inr (.inl (by rw [hj]; exact hJ))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (by rw [hw]; exact hJ))))))

omit [DecidableEq S] in
theorem JWalk.advance_cases [DecidableEq S] (w : JWalk S) (X : XNet S) :
    (w.advance X).s₁ = w.s₁ ∧ (w.advance X).s₂ = w.s₂ ∧
      ((w.advance X).c₁ = w.c₁ ∨ (w.advance X).c₁ = w.c₁.next X w.s₂) ∧
      ((w.advance X).c₂ = w.c₂ ∨ (w.advance X).c₂ = w.c₂.next X w.s₁) := by
  unfold JWalk.advance
  split
  · exact ⟨rfl, rfl, .inr rfl, .inl rfl⟩
  · exact ⟨rfl, rfl, .inl rfl, .inr rfl⟩

omit [DecidableEq S] in
/-- **One step of a side keeps what it has read**, unless it stops. -/
theorem JMach.Live.cur_next {M : JMach S} (hL : M.Live xs) {u v : Port} {c : JCur S}
    (hc : JCur.Ok xs.sys.ar M.toMach.goal u v c)
    (hne : JCur.next M.mem u c ≠ .stop) :
    JCur.Ok xs.sys.ar M.toMach.goal u v (JCur.next M.mem u c) := by
  have hG := hL.inv.wf
  cases c with
  | prin i γ => exact hc
  | stop => exact False.elim hc
  | go prev cur =>
    obtain ⟨C, hcu, hcv, vs, tr, hvm⟩ := hc
    unfold JCur.next at hne ⊢
    dsimp only at hne ⊢
    cases hns : nextSeg M.mem.wires cur prev with
    | some n =>
      rw [hns] at hne
      dsimp only at hne ⊢
      by_cases hnu : n = u
      · rw [ite_pos' hnu] at hne
        exact absurd rfl hne
      · rw [ite_neg' hnu]
        obtain ⟨hl, hnp⟩ := nextSeg_spec hns
        have hlG : M.toMach.goal.link cur n := .inl hl
        have hEc : ¬ M.toMach.goal.End xs.sys.ar cur :=
          fun hE => hnp (hG.end_unique hE hlG (hG.symm C.link_last))
        have hfr : n ∉ cur :: prev :: vs := by
          rcases Trail.fresh' hG.symm hG.irrefl hG.deg tr hlG hnp with h | h
          · exact h
          · exact absurd h hnu
        refine ⟨C.snoc hEc hlG hnp, hnu, fun e => absurd (e ▸ hvm) hfr, prev :: vs,
          .step tr hlG hfr, List.mem_cons_of_mem _ hvm⟩
    | none =>
      rw [hns] at hne
      dsimp only at hne ⊢
      by_cases h0 : cur.2 = 0
      · rw [ite_pos' h0] at hne ⊢
        cases hag : assoc cur.1 M.mem.agents with
        | none =>
          rw [hag] at hne
          exact absurd rfl hne
        | some γ =>
          dsimp only
          have hgi : M.toMach.goal.agent cur.1 γ := .inl (.inl (assoc_mem hag))
          have ec : cur = (cur.1, 0) := Prod.ext rfl h0
          have hE : M.toMach.goal.End xs.sys.ar (cur.1, 0) := .inr ⟨γ, hgi, Nat.zero_le _⟩
          refine ⟨⟨prev, ec ▸ C⟩, .inl ⟨γ, hgi⟩, fun γ' h' => hG.agent_fun h' hgi,
            fun q q' h h' => hG.end_unique hE h h'⟩
      · rw [ite_neg' h0] at hne
        exact absurd rfl hne

omit [DecidableEq S] in
/-- **A side that stops leaves the pair to someone else**: a side of a walk
on the wire of a pair that stops has met a loop, which no pair has, or an
agent of the pair that is not in memory, or a segment not yet written. -/
theorem JMach.Live.cur_stop {M : JMach S} (hL : M.Live xs) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) (hTs : T.st = .write [] []) {u v : Port} {c : JCur S}
    (hc : JCur.Ok xs.sys.ar M.toMach.goal u v c) (hu : ¬ M.toMach.goal.End xs.sys.ar u)
    (hstop : JCur.next M.mem u c = .stop) {a b : Id} {α β : S} {R : Rhs S}
    (r : Redex xs.sys M.toMach.goal a b α β R) (J : JEnds xs.sys.ar M.toMach.goal v u a b)
    (T₁ : JThread S) : JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β := by
  have hG := hL.inv.wf
  have memG : ∀ {i : Id} {γ : S}, (i, γ) ∈ M.mem.agents → M.toMach.goal.agent i γ :=
    fun h => .inl (.inl h)
  have assocG : ∀ {i : Id} {γ : S}, (i, γ) ∈ M.mem.agents → assoc i M.mem.agents = some γ :=
    fun h => assoc_eq_of_unique h fun γ' h' => hG.agent_fun (memG h') (memG h)
  cases c with
  | prin i γ =>
    unfold JCur.next at hstop
    cases hstop
  | stop => exact False.elim hc
  | go prev cur =>
    obtain ⟨C, hcu, hcv, vs, tr, hvm⟩ := hc
    obtain ⟨⟨x, wa⟩, hJ2⟩ := J
    unfold JCur.next at hstop
    dsimp only at hstop
    cases hns : nextSeg M.mem.wires cur prev with
    | some n =>
      rw [hns] at hstop
      dsimp only at hstop
      by_cases hnu : n = u
      · -- the wire is a loop, and the pair has no wire through it
        exfalso
        obtain ⟨hl, hnp⟩ := nextSeg_spec hns
        have hlG : M.toMach.goal.link cur n := .inl hl
        have hEc : ¬ M.toMach.goal.End xs.sys.ar cur :=
          fun hE => hnp (hG.end_unique hE hlG (hG.symm C.link_last))
        subst hnu
        have hcv' : cur ≠ v := fun e => hnp (hcv e).symm
        exact Walk.cycle_false hG.wiring wa r.end_left (C.snoc hEc hlG hnp) rfl hcv' hu
      · rw [ite_neg' hnu] at hstop
        cases hstop
    | none =>
      rw [hns] at hstop
      dsimp only at hstop
      have hst : ¬ T.st.held a α ∧ ¬ T.st.pendA a α := by
        rw [hTs]
        exact ⟨fun h => h, fun h => List.not_mem_nil h⟩
      by_cases hEc : M.toMach.goal.End xs.sys.ar cur
      · have ec : cur = (a, 0) := Walk.det hG.wiring C wa hEc r.end_left
        subst ec
        have hnm : (a, α) ∉ M.mem.agents := by
          intro hm
          rw [ite_pos' rfl, assocG hm] at hstop
          cases hstop
        exact hL.ans_of_agent ht (.inl ⟨rfl, rfl⟩) r.ha hnm hst.1 hst.2 _
      · obtain ⟨q, hq, hqp, hqy⟩ := Walk.extend' hG.wiring C wa hEc r.end_left
        refine hL.ans_of_link ht r hq (fun hm => nextSeg_ne_none hm hqp hns) ?_ ?_
          (.inr (JEnds.cursor hG C ⟨⟨x, wa⟩, hJ2⟩ r.end_left r.end_right hu hEc hq hqp)) _
        · rw [hTs]
          exact fun h => List.not_mem_nil h
        · intro z hz hE
          rcases hz with ez | ez
          · rw [ez] at hE
            exact absurd hE hEc
          · rw [ez] at hE ⊢
            exact .inl (hqy hE)

omit [DecidableEq S] in
theorem JWalk.found_none {w : JWalk S} (h : w.found = none) : w.c₁ ≠ .stop ∧ w.c₂ ≠ .stop := by
  unfold JWalk.found at h
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [e] at h
    cases h
  · rw [e] at h
    cases hc : w.c₁ <;> rw [hc] at h <;> cases h

omit [DecidableEq S] in
theorem JWalk.found_some_none {w : JWalk S} (h : w.found = some none) :
    w.c₁ = .stop ∨ w.c₂ = .stop := by
  unfold JWalk.found at h
  cases hc : w.c₁ with
  | stop => exact .inl rfl
  | go p c =>
    rw [hc] at h
    cases hd : w.c₂ <;> rw [hd] at h <;> first | exact .inr rfl | cases h
  | prin i γ =>
    rw [hc] at h
    cases hd : w.c₂ <;> rw [hd] at h <;> first | exact .inr rfl | cases h

omit [DecidableEq S] in
theorem JWalk.found_some_some {w : JWalk S} {e : Id × S} (h : w.found = some (some e)) :
    ∃ i γ j δ, w.c₁ = .prin i γ ∧ w.c₂ = .prin j δ ∧ e = (i, γ) := by
  unfold JWalk.found at h
  cases hc : w.c₁ with
  | stop =>
    rw [hc] at h
    cases h
  | go p c =>
    rw [hc] at h
    cases hd : w.c₂ <;> rw [hd] at h <;> cases h
  | prin i γ =>
    rw [hc] at h
    cases hd : w.c₂ with
    | prin j δ =>
      rw [hd] at h
      exact ⟨i, γ, j, δ, rfl, rfl, (Option.some.inj (Option.some.inj h)).symm⟩
    | go p c =>
      rw [hd] at h
      cases h
    | stop =>
      rw [hd] at h
      cases h

/-- **A step of a walk that finds nothing keeps it as it should be.** -/
theorem JMach.Live.advance_ok {M : JMach S} (hL : M.Live xs) {w : JWalk S}
    (hw : JWalk.Ok xs.sys.ar M.toMach.goal w) (hf : (w.advance M.mem).found = none) :
    JWalk.Ok xs.sys.ar M.toMach.goal (w.advance M.mem) := by
  obtain ⟨e₁, e₂, h₁, h₂⟩ := JWalk.advance_cases w M.mem
  obtain ⟨n₁, n₂⟩ := JWalk.found_none hf
  obtain ⟨hl, hE₁, hE₂, hc₁, hc₂, -⟩ := hw
  refine ⟨e₁ ▸ e₂ ▸ hl, e₁ ▸ hE₁, e₂ ▸ hE₂, ?_, ?_, hf⟩
  · rw [e₁, e₂]
    rcases h₁ with h | h
    · rw [h]
      exact hc₁
    · rw [h] at n₁ ⊢
      exact hL.cur_next hc₁ n₁
  · rw [e₁, e₂]
    rcases h₂ with h | h
    · rw [h]
      exact hc₂
    · rw [h] at n₂ ⊢
      exact hL.cur_next hc₂ n₂

/-- **A step of a walk that stops leaves its pairs to others.** -/
theorem JMach.Live.advance_stop {M : JMach S} (hL : M.Live xs) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) (hTs : T.st = .write [] []) {w : JWalk S}
    (hw : JWalk.Ok xs.sys.ar M.toMach.goal w) (hf : (w.advance M.mem).found = some none)
    {a b : Id} {α β : S} {R : Rhs S} (r : Redex xs.sys M.toMach.goal a b α β R)
    (hJ : JEnds xs.sys.ar M.toMach.goal w.s₁ w.s₂ a b ∨
      JEnds xs.sys.ar M.toMach.goal w.s₂ w.s₁ a b)
    (T₁ : JThread S) : JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β := by
  obtain ⟨-, -, h₁, h₂⟩ := JWalk.advance_cases w M.mem
  obtain ⟨-, hE₁, hE₂, hc₁, hc₂, -⟩ := hw
  obtain ⟨R', r', -⟩ := r.flip hL.inv.wf
  rcases JWalk.found_some_none hf with hs | hs
  · have hn : JCur.next M.mem w.s₂ w.c₁ = .stop := by
      rcases h₁ with h | h
      · rw [h] at hs
        rw [hs] at hc₁
        exact False.elim hc₁
      · rw [← h]
        exact hs
    rcases hJ with J | J
    · exact hL.cur_stop ht hTs hc₁ hE₂ hn r J T₁
    · exact (hL.cur_stop ht hTs hc₁ hE₂ hn r' J.swap T₁).symm
  · have hn : JCur.next M.mem w.s₁ w.c₂ = .stop := by
      rcases h₂ with h | h
      · rw [h] at hs
        rw [hs] at hc₂
        exact False.elim hc₂
      · rw [← h]
        exact hs
    rcases hJ with J | J
    · exact (hL.cur_stop ht hTs hc₂ hE₁ hn r' J.swap T₁).symm
    · exact hL.cur_stop ht hTs hc₂ hE₁ hn r J T₁

omit [DecidableEq S] in
/-- A walk that reaches a principal port whose agent may since have gone
reaches the end of every walk to an end that starts the same way. -/
theorem prin_end {ar : S → Nat} {G : Net S} (hG : G.WF ar) {u v x x' y : Port} {i : Id}
    (W : Walk G.link (G.End ar) u v x (i, 0))
    (hu : ∀ q q', G.link (i, 0) q → G.link (i, 0) q' → q = q')
    (W' : Walk G.link (G.End ar) u v x' y) (hy : G.End ar y) : (i, 0) = y := by
  by_cases hE : G.End ar (i, 0)
  · exact W.det hG.wiring W' hE hy
  · have F := Walk.follow hG.wiring W W' hy hE
    cases F with
    | single _ => exact absurd hy hE
    | cons h _ hn F' => exact absurd (hu _ _ F'.link_first (hG.symm h)) hn

/-- **A step of a walk that finds both ends puts an agent of the pair in
front of the list.** -/
theorem JMach.Live.advance_found {M : JMach S} (hL : M.Live xs) {w : JWalk S}
    (hw : JWalk.Ok xs.sys.ar M.toMach.goal w) {e : Id × S}
    (hf : (w.advance M.mem).found = some (some e)) {a b : Id} {α β : S} {R : Rhs S}
    (r : Redex xs.sys M.toMach.goal a b α β R)
    (hJ : JEnds xs.sys.ar M.toMach.goal w.s₁ w.s₂ a b ∨
      JEnds xs.sys.ar M.toMach.goal w.s₂ w.s₁ a b) :
    e = (a, α) ∨ e = (b, β) := by
  have hG := hL.inv.wf
  obtain ⟨e₁, e₂, h₁, h₂⟩ := JWalk.advance_cases w M.mem
  obtain ⟨-, -, -, hc₁, hc₂, -⟩ := hw
  obtain ⟨i, γ, j, δ, p₁, p₂, rfl⟩ := JWalk.found_some_some hf
  have k₁ : JCur.Ok xs.sys.ar M.toMach.goal w.s₂ w.s₁ (.prin i γ) := by
    rw [← p₁]
    rcases h₁ with h | h
    · rw [h]
      exact hc₁
    · rw [h]
      exact hL.cur_next hc₁ (by rw [← h, p₁]; exact fun h => by cases h)
  obtain ⟨⟨x, W⟩, -, hf₁, hu₁⟩ := k₁
  rcases hJ with ⟨⟨x', Wa⟩, -⟩ | ⟨-, ⟨y', Wb⟩⟩
  · have ea := prin_end hG W hu₁ Wa r.end_left
    obtain rfl : i = a := congrArg Prod.fst ea
    exact .inl (by rw [hf₁ α r.ha])
  · have eb := prin_end hG W hu₁ Wb r.end_right
    obtain rfl : i = b := congrArg Prod.fst eb
    exact .inr (by rw [hf₁ β r.hb])

/-- **Every action keeps the invariant.** -/
theorem JMach.step_live {M : JMach S} (hL : M.Live xs) (t : Nat) :
    (M.step xs t).1.Live xs := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold JMach.step
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
    obtain ⟨todo, s, again, js, wk⟩ := T
    have noA : ∀ {st : TState S}, ¬ st.writing → ∀ i γ, ¬ st.pendA i γ :=
      fun hn i γ h => hn (TState.pendA_writing h)
    have noL : ∀ {st : TState S}, ¬ st.writing → ∀ p q, ¬ st.pendL p q :=
      fun hn p q h => hn (TState.pendL_writing h)
    -- away from writing: nothing joined, no walk, and the answers are the
    -- ones of `WMach`
    have zero : ∀ {X₁ : XNet S} {T₁ : XThread S}, (∀ as ls, s ≠ .write as ls) →
        XMach.act xs M.mem ⟨todo, s⟩ = (X₁, T₁, 0) → T₁.st.Sane M.toMach.goal →
        ¬ T₁.st.writing →
        (∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
          JThread.Answers xs.sys.ar M.toMach.goal ⟨todo, s, again, js, wk⟩ a b α β →
          JNewAns xs.sys.ar M.toMach.goal M.ths t ⟨T₁.todo, T₁.st, again, js, wk⟩ a b α β) →
        (M.step xs t).1.Live xs := by
      intro X₁ T₁ hst hact hsane hnw hans
      have hsw : ¬ s.writing := by
        intro hw
        cases s with
        | write as ls => exact hst as ls rfl
        | _ => exact hw
      obtain ⟨hj, hwk⟩ := hL.quiet t _ ht hsw
      change js = [] at hj
      change wk = none at hwk
      refine hL.step_zero ht (JMach.act_lift hst hact) hsane
        (fun i γ h => absurd h (noA hnw i γ)) (fun p q h => absurd h (noL hnw p q))
        (fun _ => ⟨hj, hwk⟩) (fun w h => by change wk = some w at h; rw [hwk] at h; cases h)
        (fun _ => ⟨hj, hwk⟩)
        (fun pq h => by change pq ∈ js at h; rw [hj] at h; exact absurd h List.not_mem_nil)
        (fun w h => by change wk = some w at h; rw [hwk] at h; cases h) hans
    have plain : ¬ s.writing → ∀ {a b : Id} {α β : S},
        JThread.Answers xs.sys.ar M.toMach.goal ⟨todo, s, again, js, wk⟩ a b α β →
        (a, α) ∈ todo ∨ (b, β) ∈ todo ∨ s.target = some a ∨ s.target = some b := by
      intro hsw a b α β hA
      obtain ⟨hj, hwk⟩ := hL.quiet t _ ht hsw
      change js = [] at hj
      change wk = none at hwk
      rcases hA with h | h | h | h | ⟨pq, hm, -⟩ | ⟨w, hw', -⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
      · change pq ∈ js at hm
        rw [hj] at hm
        exact absurd hm List.not_mem_nil
      · change wk = some w at hw'
        rw [hwk] at hw'
        cases hw'
    cases s with
    | idle =>
      cases todo with
      | nil =>
        refine zero (fun _ _ h => by cases h) rfl trivial (fun x => x)
          fun a b α β R _ hA => .inl hA
      | cons e rest =>
        by_cases he : assoc e.1 M.mem.agents = some e.2
        · refine zero (fun _ _ h => by cases h) (XMach.act_idle_pos he)
            ⟨.inl ⟨e.2, memG (assoc_mem he)⟩,
              fun α' h' => hG.agent_fun h' (memG (assoc_mem he)),
              fun q q' h h' => hG.end_unique
                (.inr ⟨e.2, memG (assoc_mem he), Nat.zero_le _⟩) h h'⟩ (fun x => x) ?_
          intro a b α β R _ hA
          rcases plain (fun x => x) hA with hm | hm | htg | htg
          · rcases List.mem_cons.1 hm with heq | hm
            · exact .inl (.inr (.inr (.inl
                (congrArg (fun x : Id × S => some x.1) heq).symm)))
            · exact .inl (.inl hm)
          · rcases List.mem_cons.1 hm with heq | hm
            · exact .inl (.inr (.inr (.inr (.inl
                (congrArg (fun x : Id × S => some x.1) heq).symm))))
            · exact .inl (.inr (.inl hm))
          · cases htg
          · cases htg
        · refine zero (fun _ _ h => by cases h) (XMach.act_idle_neg he) trivial (fun x => x) ?_
          intro a b α β R r hA
          rcases plain (fun x => x) hA with hm | hm | htg | htg
          · rcases List.mem_cons.1 hm with heq | hm
            · have hnm : (a, α) ∉ M.mem.agents := fun h => he (by rw [← heq]; exact assocG h)
              exact hL.ans_of_agent ht (.inl ⟨rfl, rfl⟩) r.ha hnm (fun x => x) (fun x => x) _
            · exact .inl (.inl hm)
          · rcases List.mem_cons.1 hm with heq | hm
            · have hnm : (b, β) ∉ M.mem.agents := fun h => he (by rw [← heq]; exact assocG h)
              exact hL.ans_of_agent ht (.inr ⟨rfl, rfl⟩) r.hb hnm (fun x => x) (fun x => x) _
            · exact .inl (.inr (.inl hm))
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
        exact zero (fun _ _ h => by cases h) (XMach.act_look hv)
          ⟨hS.1, hS.2.1, hS.2.2, [], .step .start hl hf⟩ (fun x => x)
          fun a b α β R _ hA => .inl (hA.carry rfl rfl rfl rfl)
      | none =>
        refine zero (fun _ _ h => by cases h) (XMach.act_look_none hv) trivial (fun x => x)
          (hL.ans_of_fail (T := ⟨todo, .look a₀ α₀, again, js, wk⟩) rfl rfl rfl ?_)
        intro a b α β R r htg
        have ea : a = a₀ := (Option.some.inj htg).symm
        subst ea
        obtain ⟨q, hq⟩ := hG.end_wired r.end_left
        obtain ⟨v₂, x₂, w₂⟩ := r.conn
        have ev : q = v₂ := hG.end_unique r.end_left hq w₂.link_first
        subst ev
        refine hL.ans_of_link ht r hq (fun hm => ?_) (fun x => x) ?_
          (.inl ⟨⟨q, .single (hG.symm hq)⟩, ⟨x₂, w₂⟩⟩) _
        · obtain ⟨q', e'⟩ := assoc_of_mem hm
          rw [hv] at e'
          cases e'
        · intro z hz hE
          rcases hz with ez | ez
          · exact .inl ez
          · rw [ez] at hE ⊢
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
        · exact zero (fun _ _ h => by cases h) (XMach.act_seek_found hsc hc)
            ⟨hS.1, fun α' h' => ⟨hS.2.1 α' h', memG (assoc_mem hq.2)⟩⟩ (fun x => x)
            fun a b α β R _ hA => .inl (hA.carry rfl rfl rfl rfl)
        · refine zero (fun _ _ h => by cases h) (XMach.act_seek_norule hsc hc) trivial
            (fun x => x)
            (hL.ans_of_fail (T := ⟨todo, .seek a₀ α₀ p c, again, js, wk⟩) rfl rfl rfl ?_)
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
          exact zero (fun _ _ h => by cases h) (XMach.act_seek_next hsc hns)
            ⟨hS.1, hS.2.1, hS.2.2.1, p :: vs, .step tr hlG
              (Trail.fresh hG.symm hG.irrefl hG.deg hS.2.2.1 tr hlG hqp)⟩ (fun x => x)
            fun a b α β R _ hA => .inl (hA.carry rfl rfl rfl rfl)
        | none =>
          refine zero (fun _ _ h => by cases h) (XMach.act_seek_stop hsc hns) trivial
            (fun x => x)
            (hL.ans_of_fail (T := ⟨todo, .seek a₀ α₀ p c, again, js, wk⟩) rfl rfl rfl ?_)
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
            refine hL.ans_of_link ht r hq (fun hm => nextSeg_ne_none hm hqp hns) (fun x => x) ?_
              (.inl (JEnds.reader hG w' ⟨v₂, x₂, w₂⟩ r.end_left r.end_right hEc hq hqp)) _
            intro z hz hE
            rcases hz with ez | ez
            · rw [ez] at hE
              exact absurd hE hEc
            · rw [ez] at hE ⊢
              exact .inr (hqy hE)
    | ready a₀ b₀ α₀ β₀ =>
      by_cases ha : assoc a₀ M.mem.agents = some α₀
      · exact zero (fun _ _ h => by cases h) (XMach.act_ready ha) hS (fun x => x)
          fun a b α β R _ hA => .inl (hA.carry rfl rfl rfl rfl)
      · refine zero (fun _ _ h => by cases h) (XMach.act_ready_neg ha) trivial (fun x => x)
          (hL.ans_of_fail (T := ⟨todo, .ready a₀ b₀ α₀ β₀, again, js, wk⟩) rfl rfl rfl ?_)
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
        refine zero (fun _ _ h => by cases h) (XMach.act_half_none hh) trivial (fun x => x)
          (hL.ans_of_fail (T := ⟨todo, .half a₀ b₀ α₀ β₀, again, js, wk⟩) rfl rfl rfl ?_)
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
      have hnj := hL.nojoin t _ ht
      have hjk := hL.jok t _ ht
      have hwo := fun w => hL.wok t _ w ht
      have hkd := hL.kids t _ ht
      have hown0 := hL.own t _ ht
      have hst : ∀ {T₁ : JThread S}, T₁.todo = todo → T₁.st.target = none → T₁.joins = js →
          T₁.walk = wk → ∀ a b α β R, Redex xs.sys M.toMach.goal a b α β R →
          JThread.Answers xs.sys.ar M.toMach.goal ⟨todo, .write as ls, again, js, wk⟩ a b α β →
          JNewAns xs.sys.ar M.toMach.goal M.ths t T₁ a b α β :=
        fun h₁ h₂ h₃ h₄ a b α β R _ hA => .inl (hA.carry h₁ h₂ h₃ h₄)
      have nowalk : ∀ {as' ls'}, (as' ≠ [] ∨ ls' ≠ []) → as = as' → ls = ls' → wk = none := by
        intro as' ls' hn ea el
        cases hw : wk with
        | none => rfl
        | some w =>
          have e := hL.wst t _ w ht hw
          change TState.write as ls = .write [] [] at e
          obtain ⟨e₁, e₂⟩ := TState.write.inj e
          subst ea el
          rcases hn with hn | hn
          · exact absurd e₁ hn
          · exact absurd e₂ hn
      cases as with
      | cons e as =>
        cases ls with
        | cons l ls =>
          obtain ⟨p, q⟩ := l
          have hw := nowalk (as' := e :: as) (ls' := (p, q) :: ls)
            (.inl (List.cons_ne_nil _ _)) rfl rfl
          refine hL.step_zero ht rfl trivial (fun i γ h => hkd i γ h) ?_
            (fun h => absurd trivial h)
            (fun w h => by change wk = some w at h; rw [hw] at h; cases h)
            hnj hjk hwo
            (hst rfl rfl rfl rfl)
          intro p' q' hp
          exact hown0 p' q' (List.mem_cons_of_mem _ hp)
        | nil =>
          obtain ⟨i, γ⟩ := e
          have hw := nowalk (as' := (i, γ) :: as) (ls' := [])
            (.inl (List.cons_ne_nil _ _)) rfl rfl
          exact hL.step_zero ht rfl trivial
            (fun i' γ' h => hkd i' γ' (List.mem_cons_of_mem _ h))
            (fun p q h => absurd h List.not_mem_nil) (fun h => absurd trivial h)
            (fun w h => by change wk = some w at h; rw [hw] at h; cases h)
            hnj hjk hwo
            (hst rfl rfl rfl rfl)
      | nil =>
        cases ls with
        | cons l ls =>
          obtain ⟨p, q⟩ := l
          have hw := nowalk (as' := []) (ls' := (p, q) :: ls) (.inr (List.cons_ne_nil _ _))
            rfl rfl
          refine hL.step_zero ht rfl trivial (fun i γ h => absurd h List.not_mem_nil) ?_
            (fun h => absurd trivial h)
            (fun w h => by change wk = some w at h; rw [hw] at h; cases h)
            hnj hjk hwo
            (hst rfl rfl rfl rfl)
          intro p' q' hp
          exact hown0 p' q' (List.mem_cons_of_mem _ hp)
        | nil =>
          cases again with
          | false =>
            obtain ⟨hj, hw⟩ := hnj rfl
            change js = [] at hj
            change wk = none at hw
            subst hj hw
            exact hL.step_zero ht rfl trivial (fun i γ h => False.elim h)
              (fun p q h => False.elim h) (fun _ => ⟨rfl, rfl⟩) (fun w h => by cases h)
              (fun _ => ⟨rfl, rfl⟩) (fun pq h => absurd h List.not_mem_nil) (fun w h => by cases h)
              (hst rfl rfl rfl rfl)
          | true =>
            cases wk with
            | none =>
              cases js with
              | nil =>
                exact hL.step_zero ht rfl trivial (fun i γ h => False.elim h)
                  (fun p q h => False.elim h) (fun _ => ⟨rfl, rfl⟩) (fun w h => by cases h)
                  (fun _ => ⟨rfl, rfl⟩) (fun pq h => absurd h List.not_mem_nil)
                  (fun w h => by cases h) (hst rfl rfl rfl rfl)
              | cons pq js =>
                obtain ⟨p, q⟩ := pq
                obtain ⟨hl, hE₁, hE₂⟩ := hjk (p, q) List.mem_cons_self
                have hpq : p ≠ q := fun e => hG.irrefl (e ▸ hl)
                refine hL.step_zero ht rfl trivial (fun i γ h => absurd h List.not_mem_nil)
                  (fun p q h => absurd h List.not_mem_nil) (fun h => absurd trivial h)
                  (fun w _ => rfl)
                  (fun h => by cases h)
                  (fun pq' h => hjk pq' (List.mem_cons_of_mem _ h)) ?_ ?_
                · intro w hw
                  obtain rfl := Option.some.inj hw
                  refine ⟨hl, hE₁, hE₂, ?_, ?_, rfl⟩
                  · refine ⟨.single (hG.symm hl), hpq, fun _ => rfl, [], ?_, List.mem_cons_self⟩
                    exact .step .start (hG.symm hl) (fun h => hpq (List.mem_singleton.1 h))
                  · refine ⟨.single hl, Ne.symm hpq, fun _ => rfl, [], ?_, List.mem_cons_self⟩
                    exact .step .start hl (fun h => hpq (List.mem_singleton.1 h).symm)
                · intro a b α β R _ hA
                  rcases hA with h | h | h | h | ⟨pq', hm, hJ⟩ | ⟨w, hw', -⟩
                  · exact .inl (.inl h)
                  · exact .inl (.inr (.inl h))
                  · exact .inl (.inr (.inr (.inl h)))
                  · exact .inl (.inr (.inr (.inr (.inl h))))
                  · rcases List.mem_cons.1 hm with rfl | hm
                    · exact .inl (.inr (.inr (.inr (.inr (.inr ⟨_, rfl, hJ⟩)))))
                    · exact .inl (.inr (.inr (.inr (.inr (.inl ⟨pq', hm, hJ⟩)))))
                  · cases hw'
            | some w =>
              have hwk := hwo w rfl
              obtain ⟨e₁, e₂, -, -⟩ := JWalk.advance_cases w M.mem
              cases hf : (w.advance M.mem).found with
              | none =>
                have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, js, some w⟩ =
                    (M.mem, ⟨todo, .write [] [], true, js, some (w.advance M.mem)⟩, 0) := by
                  unfold JMach.act
                  dsimp only
                  rw [hf]
                  rfl
                refine hL.step_zero ht hact trivial (fun i γ h => absurd h List.not_mem_nil)
                  (fun p q h => absurd h List.not_mem_nil) (fun h => absurd trivial h)
                  (fun w _ => rfl)
                  (fun h => by cases h) hjk ?_ ?_
                · intro w' hw'
                  obtain rfl := Option.some.inj hw'
                  exact hL.advance_ok hwk hf
                · intro a b α β R _ hA
                  rcases hA with h | h | h | h | h | ⟨w', hw', hJ⟩
                  · exact .inl (.inl h)
                  · exact .inl (.inr (.inl h))
                  · exact .inl (.inr (.inr (.inl h)))
                  · exact .inl (.inr (.inr (.inr (.inl h))))
                  · exact .inl (.inr (.inr (.inr (.inr (.inl h)))))
                  · obtain rfl := Option.some.inj hw'
                    refine .inl (.inr (.inr (.inr (.inr (.inr ⟨_, rfl, ?_⟩)))))
                    rw [e₁, e₂]
                    exact hJ
              | some o =>
                cases o with
                | none =>
                  have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, js, some w⟩ =
                      (M.mem, ⟨todo, .write [] [], true, js, none⟩, 0) := by
                    unfold JMach.act
                    dsimp only
                    rw [hf]
                    rfl
                  refine hL.step_zero ht hact trivial (fun i γ h => absurd h List.not_mem_nil)
                    (fun p q h => absurd h List.not_mem_nil) (fun h => absurd trivial h)
                    (fun w h => by cases h) (fun h => by cases h) hjk
                    (fun w h => by cases h) ?_
                  intro a b α β R r hA
                  rcases hA with h | h | h | h | h | ⟨w', hw', hJ⟩
                  · exact .inl (.inl h)
                  · exact .inl (.inr (.inl h))
                  · exact .inl (.inr (.inr (.inl h)))
                  · exact .inl (.inr (.inr (.inr (.inl h))))
                  · exact .inl (.inr (.inr (.inr (.inr (.inl h)))))
                  · obtain rfl := Option.some.inj hw'
                    exact hL.advance_stop ht rfl hwk hf r hJ _
                | some e =>
                  have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, js, some w⟩ =
                      (M.mem, ⟨e :: todo, .write [] [], true, js, none⟩, 0) := by
                    unfold JMach.act
                    dsimp only
                    rw [hf]
                    rfl
                  refine hL.step_zero ht hact trivial (fun i γ h => absurd h List.not_mem_nil)
                    (fun p q h => absurd h List.not_mem_nil) (fun h => absurd trivial h)
                    (fun w h => by cases h) (fun h => by cases h) hjk
                    (fun w h => by cases h) ?_
                  intro a b α β R r hA
                  rcases hA with h | h | h | h | h | ⟨w', hw', hJ⟩
                  · exact .inl (.inl (List.mem_cons_of_mem _ h))
                  · exact .inl (.inr (.inl (List.mem_cons_of_mem _ h)))
                  · exact .inl (.inr (.inr (.inl h)))
                  · exact .inl (.inr (.inr (.inr (.inl h))))
                  · exact .inl (.inr (.inr (.inr (.inr (.inl h)))))
                  · obtain rfl := Option.some.inj hw'
                    rcases hL.advance_found hwk hf r hJ with he | he
                    · exact .inl (.inl (he ▸ List.mem_cons_self))
                    · exact .inl (.inr (.inl (he ▸ List.mem_cons_self)))

/-- The invariant holds along every run. -/
theorem JMach.exec_live : ∀ (σ : List Nat) {M : JMach S}, M.Live xs → (M.exec xs σ).1.Live xs
  | [], _, h => h
  | t :: σ, _, h => JMach.exec_live σ (JMach.step_live h t)

omit [DecidableEq S] in
theorem JMach.init_thread (X : XNet S) {nt u : Nat} (hu : u < nt) :
    (JMach.init X nt).ths[u]? =
      some ⟨X.agents.drop u ++ X.agents.take u, .idle, false, [], none⟩ := by
  show ((List.range nt).map fun t =>
    (⟨X.agents.drop t ++ X.agents.take t, .idle, false, [], none⟩ : JThread S))[u]? = _
  rw [List.getElem?_map, List.getElem?_range hu]
  rfl

omit [DecidableEq S] in
theorem JMach.init_live {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt) :
    (JMach.init X nt).Live xs := by
  have e : (JMach.init X nt).toMach = Mach.init X.toNet := JMach.init_toMach X nt
  have eg : (JMach.init X nt).toMach.goal = X.toNet := by
    rw [e]
    exact congrArg CState.goal (Mach.init_quiet X.toNet).abs
  have init : ∀ {u : Nat} {U : JThread S}, (JMach.init X nt).ths[u]? = some U →
      U.st = .idle ∧ U.joins = [] ∧ U.walk = none ∧ U.again = false := by
    intro u U hu
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hu)
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨by rw [e]; exact Mach.init_inv hX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b α β R r
    rw [eg] at r
    exact ⟨0, _, JMach.init_thread X hnt, .inl (List.mem_append_left _ r.ha)⟩
  · intro u U hu
    rw [(init hu).1]
    trivial
  · intro u U hu i γ h
    rw [(init hu).1] at h
    exact False.elim h
  · intro u U hu p q h
    rw [(init hu).1] at h
    exact False.elim h
  · intro u U hu _
    exact ⟨(init hu).2.1, (init hu).2.2.1⟩
  · intro u U w hu h
    rw [(init hu).2.2.1] at h
    cases h
  · intro u U hu _
    exact ⟨(init hu).2.1, (init hu).2.2.1⟩
  · intro u U hu pq h
    rw [(init hu).2.1] at h
    exact absurd h List.not_mem_nil
  · intro u U w hu h
    rw [(init hu).2.2.1] at h
    cases h

omit [DecidableEq S] in
/-- **The threads do not all rest while there is work.**  When every thread
is idle with an empty list, the memory holds no active pair with a rule. -/
theorem JMach.Live.rest {M : JMach S} (hL : M.Live xs) (hr : M.resting = true) :
    M.toMach.Quiet ∧ Normal (Step xs.sys) M.mem.toNet := by
  have hall : ∀ T, T ∈ M.ths → T.todo = [] ∧ T.st = .idle := by
    intro T hT
    have h : (T.todo.isEmpty && T.st.isIdle) = true := List.all_eq_true.1 hr T hT
    obtain ⟨todo, st, again, js, wk⟩ := T
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
    show threadOf ((M.ths.map JThread.toW).map WThread.toX) u = .idle
    unfold threadOf
    split
    · rename_i T hT
      rw [List.map_map] at hT
      obtain ⟨U, hU, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hT)
      exact (hall U hU).2
    · rfl
  refine ⟨hq, ?_⟩
  have eg : M.toMach.goal = M.mem.toNet := congrArg CState.goal hq.abs
  rintro N' ⟨a, b, α, β, R, r, -⟩
  rw [← eg] at r
  obtain ⟨t, T, ht, hA⟩ := hL.cov a b α β R r
  obtain ⟨h₁, h₂⟩ := hall T (List.mem_of_getElem? ht)
  obtain ⟨hj, hw⟩ := hL.quiet t T ht (by rw [h₂]; exact fun x => x)
  rcases hA with hm | hm | htg | htg | ⟨pq, hm, -⟩ | ⟨w, hw', -⟩
  · rw [h₁] at hm
    exact absurd hm List.not_mem_nil
  · rw [h₁] at hm
    exact absurd hm List.not_mem_nil
  · rw [h₂] at htg
    cases htg
  · rw [h₂] at htg
    cases htg
  · rw [hj] at hm
    exact absurd hm List.not_mem_nil
  · rw [hw] at hw'
    cases hw'

/-- **A run that ends with every thread at rest has computed the normal
form**, whatever the schedule and the number of threads: the memory holds
the normal form, and the claims are as many as the steps of the sequential
reduction. -/
theorem JMach.exec_rest {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : List Nat)
    (hr : ((JMach.init X nt).exec xs σ).1.resting = true) :
    ((JMach.init X nt).exec xs σ).2 = n ∧ ((JMach.init X nt).exec xs σ).1.mem.toNet = N' := by
  obtain ⟨hq, hnorm⟩ := (JMach.exec_live σ (JMach.init_live hX hnt)).rest hr
  obtain ⟨-, hu⟩ := (JMach.exec_mrun xs X nt σ).final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨e₂.symm, e₁.symm⟩

end JLive

end INet
