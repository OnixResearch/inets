import InteractionNets.Arith.ListsAtRest

/-! # Any nets side by side

The side-by-side results of the modules before this one are proved from
the run of one thread on each net.  Here they are proved from the
reduction of nets alone, and for any nets that have normal forms.

The first part is about any interaction system whose rules give every
new agent to one of the two agents that meet (`System.Sided`).  A net
made of nets under different tags (`Net.Made`) takes a step whenever one
of its parts does, and is then made of the same parts with that one
replaced (`Net.Made.step`); it is normal when all its parts are
(`Net.Made.normal`).  So if the parts with the tags of a list have normal
forms, the whole reduces, in as many steps as the parts together, to a
normal form made of the normal forms (`Net.Made.reduce`), and the thread
machine, with any number of threads and any schedule, comes to rest on
exactly that net (`XMach.made_rest`, `XMach.made_fair`).

The second part is the addition system: any well-formed compact nets side
by side (`Arith.besides_rest`, `Arith.besides_fair`), and what that says
about numerals (`Arith.besides_rest_num`).
-/

namespace INet

open Arith (tagPort tagPort_inj tagPort_snoc snoc_inj)

section Made

variable {S : Type}

/-- **A net made of nets under tags.**  `U.Made P`: the net `U` is the
nets `P c` side by side, the names of `P c` with the tag `c` at the end,
and nothing else. -/
structure Net.Made (U : Net S) (P : Nat → Net S) : Prop where
  agent : ∀ {i γ}, U.agent i γ → ∃ c i', i = i' ++ [c] ∧ (P c).agent i' γ
  link : ∀ {p q}, U.link p q →
    ∃ c p' q', p = tagPort c p' ∧ q = tagPort c q' ∧ (P c).link p' q'
  free : ∀ {p}, U.free p → ∃ c p', p = tagPort c p' ∧ (P c).free p'
  agent' : ∀ {c i γ}, (P c).agent i γ → U.agent (i ++ [c]) γ
  link' : ∀ {c p q}, (P c).link p q → U.link (tagPort c p) (tagPort c q)
  free' : ∀ {c p}, (P c).free p → U.free (tagPort c p)

variable {U : Net S} {P : Nat → Net S}

/-- The agents with the tag `c` are the agents of the part `c`. -/
theorem Net.Made.agent_iff (h : U.Made P) {c : Nat} {i : Id} {γ : S} :
    U.agent (i ++ [c]) γ ↔ (P c).agent i γ := by
  constructor
  · intro hu
    obtain ⟨d, i', e, hi⟩ := h.agent hu
    obtain ⟨e1, e2⟩ := snoc_inj e
    rw [e1, e2]
    exact hi
  · exact fun hi => h.agent' hi

/-- A segment that starts in a part is a segment of that part. -/
theorem Net.Made.link_from (h : U.Made P) {c : Nat} {p q' : Port}
    (hl : U.link (tagPort c p) q') : ∃ q, q' = tagPort c q ∧ (P c).link p q := by
  obtain ⟨d, p', q, e1, e2, hq⟩ := h.link hl
  obtain ⟨e3, e4⟩ := tagPort_snoc e1
  rw [e3, e4]
  exact ⟨q, e2, hq⟩

/-- The segments with the tag `c` are the segments of the part `c`. -/
theorem Net.Made.link_iff (h : U.Made P) {c : Nat} {p q : Port} :
    U.link (tagPort c p) (tagPort c q) ↔ (P c).link p q := by
  constructor
  · intro hu
    obtain ⟨q₀, e, hq⟩ := h.link_from hu
    rw [tagPort_inj e]
    exact hq
  · exact fun hl => h.link' hl

/-- The free ports with the tag `c` are the free ports of the part `c`. -/
theorem Net.Made.free_iff (h : U.Made P) {c : Nat} {p : Port} :
    U.free (tagPort c p) ↔ (P c).free p := by
  constructor
  · intro hu
    obtain ⟨d, p', e, hp⟩ := h.free hu
    obtain ⟨e1, e2⟩ := tagPort_snoc e
    rw [e1, e2]
    exact hp
  · exact fun hp => h.free' hp

theorem Net.Made.end_iff (h : U.Made P) (ar : S → Nat) {c : Nat} {p : Port} :
    U.End ar (tagPort c p) ↔ (P c).End ar p := by
  show (U.free (tagPort c p) ∨ ∃ γ, U.agent (p.1 ++ [c]) γ ∧ p.2 ≤ ar γ) ↔
    ((P c).free p ∨ ∃ γ, (P c).agent p.1 γ ∧ p.2 ≤ ar γ)
  exact or_congr h.free_iff (exists_congr fun γ => and_congr h.agent_iff Iff.rfl)

/-- A wire of a part is a wire of the whole. -/
theorem Net.Made.walk (h : U.Made P) (ar : S → Nat) {c : Nat} {u v x y : Port}
    (w : Walk (P c).link ((P c).End ar) u v x y) :
    Walk U.link (U.End ar) (tagPort c u) (tagPort c v) (tagPort c x) (tagPort c y) := by
  induction w with
  | single hl => exact .single (h.link' hl)
  | cons hl hT hne _ ih =>
    exact .cons (h.link' hl) (fun he => hT ((h.end_iff ar).1 he))
      (fun e => hne (tagPort_inj e)) ih

/-- A wire of the whole that starts in a part is a wire of that part. -/
theorem Net.Made.walk_back (h : U.Made P) (ar : S → Nat) {c : Nat} {u' v' x' y' : Port}
    (w : Walk U.link (U.End ar) u' v' x' y') : ∀ u, u' = tagPort c u →
      ∃ v x y, v' = tagPort c v ∧ x' = tagPort c x ∧ y' = tagPort c y ∧
        Walk (P c).link ((P c).End ar) u v x y := by
  induction w with
  | single hl =>
    intro u eu
    rw [eu] at hl
    obtain ⟨v, ev, hv⟩ := h.link_from hl
    exact ⟨v, u, v, ev, eu, ev, .single hv⟩
  | cons hl hT hne _ ih =>
    intro u eu
    rw [eu] at hl
    obtain ⟨v, ev, hv⟩ := h.link_from hl
    obtain ⟨w₀, x, y, ew, ex, ey, wk⟩ := ih v ev
    refine ⟨v, x, y, ev, ex, ey, .cons hv (fun he => hT ?_) (fun e => hne ?_) wk⟩
    · rw [ev]
      exact (h.end_iff ar).2 he
    · rw [ew, e, eu]

/-- Two ends joined by a wire in a part are joined by a wire in the
whole. -/
theorem Net.Made.paired (h : U.Made P) (ar : S → Nat) {c : Nat} {p q : Port}
    (hp : (P c).Paired ar p q) : U.Paired ar (tagPort c p) (tagPort c q) := by
  obtain ⟨e1, e2, v, x, w⟩ := hp
  exact ⟨(h.end_iff ar).2 e1, (h.end_iff ar).2 e2, tagPort c v, tagPort c x, h.walk ar w⟩

theorem Net.Made.congr (h : U.Made P) {P' : Nat → Net S} (e : ∀ c, P c = P' c) :
    U.Made P' := by
  have e' : P = P' := funext e
  rw [← e']
  exact h

/-- The parts with the part of tag `c` replaced by `Q`. -/
def setPart (P : Nat → Net S) (c : Nat) (Q : Net S) : Nat → Net S :=
  fun d => if d = c then Q else P d

theorem setPart_same (P : Nat → Net S) (c : Nat) (Q : Net S) : setPart P c Q c = Q := by
  show (if c = c then Q else P c) = Q
  exact ite_pos' rfl

theorem setPart_ne (P : Nat → Net S) (Q : Net S) {c d : Nat} (h : d ≠ c) :
    setPart P c Q d = P d := by
  show (if d = c then Q else P d) = P d
  exact ite_neg' h

/-! ### Names under a tag -/

/-- An agent that belongs to one side is named after the agent of that
side, so a tag at the end of both names is a tag at the end of its
name. -/
theorem child_tag (a b : Id) (c : Nat) (s : Bool) (j : Nat) :
    child (a ++ [c]) (b ++ [c]) (some s) j = child a b (some s) j ++ [c] := by
  cases s <;> rfl

theorem emb_tag (a b : Id) (c : Nat) : ∀ x : LPort, (∀ j k, x ≠ .new none j k) →
    emb (a ++ [c]) (b ++ [c]) x = tagPort c (emb a b x)
  | .ifc s k, _ => by cases s <;> rfl
  | .new (some s) j k, _ => by cases s <;> rfl
  | .new none j k, h => absurd rfl (h j k)

/-- **Rules whose new agents all have a side.**  No rule makes an agent
that belongs to neither of the two agents that meet.  Such an agent is
named after one of the two, chosen by comparing their names, and a tag at
the end of both names can change the outcome of the comparison; an agent
with a side is named after the agent of its side whatever the names. -/
def System.Sided (sys : System S) : Prop :=
  ∀ (α β : S) (R : Rhs S), sys.rule α β = some R → ∀ j, R.lab none j = none

/-- In such a system the wires of a rule touch no agent without a side. -/
theorem System.Sided.port {sys : System S} (hs : sys.Sided) {α β : S} {R : Rhs S}
    (hR : sys.rule α β = some R) {x y : LPort} (hl : R.link x y) :
    ∀ j k, x ≠ .new none j k := by
  intro j k e
  have hv := (sys.rule_wf hR).valid hl
  rw [e] at hv
  obtain ⟨γ, hγ, -⟩ := hv
  rw [hs α β R hR j] at hγ
  cases hγ

/-! ### One step in a part -/

/-- **Firing in a part is firing in the whole.**  The whole with the pair
of the part `c` fired is made of the same parts, with the part `c`
fired. -/
theorem Net.Made.fire {sys : System S} (hs : sys.Sided) (h : U.Made P) {c : Nat} {a b : Id}
    {α β : S} {R : Rhs S} (hR : sys.rule α β = some R) :
    (U.fire (a ++ [c]) (b ++ [c]) R).Made (setPart P c ((P c).fire a b R)) where
  agent := fun {i γ} hu => by
    rcases hu with ⟨hi, h1, h2⟩ | ⟨o, j, rfl, hl⟩
    · obtain ⟨d, i', rfl, hi'⟩ := h.agent hi
      refine ⟨d, i', rfl, ?_⟩
      by_cases hd : d = c
      · subst hd
        rw [setPart_same]
        exact .inl ⟨hi', fun e => h1 (by rw [e]), fun e => h2 (by rw [e])⟩
      · rw [setPart_ne _ _ hd]
        exact hi'
    · cases o with
      | none =>
        rw [hs α β R hR j] at hl
        cases hl
      | some s =>
        refine ⟨c, child a b (some s) j, child_tag a b c s j, ?_⟩
        rw [setPart_same]
        exact .inr ⟨some s, j, rfl, hl⟩
  link := fun {p q} hu => by
    rcases hu with hl | ⟨x, y, hxy, rfl, rfl⟩
    · obtain ⟨d, p', q', rfl, rfl, hl'⟩ := h.link hl
      refine ⟨d, p', q', rfl, rfl, ?_⟩
      by_cases hd : d = c
      · subst hd
        rw [setPart_same]
        exact .inl hl'
      · rw [setPart_ne _ _ hd]
        exact hl'
    · have hx := hs.port hR hxy
      have hy := hs.port hR ((sys.rule_wf hR).symm hxy)
      refine ⟨c, emb a b x, emb a b y, emb_tag a b c x hx, emb_tag a b c y hy, ?_⟩
      rw [setPart_same]
      exact .inr ⟨x, y, hxy, rfl, rfl⟩
  free := fun {p} hu => by
    obtain ⟨d, p', rfl, hp⟩ := h.free hu
    refine ⟨d, p', rfl, ?_⟩
    by_cases hd : d = c
    · subst hd
      rw [setPart_same]
      exact hp
    · rw [setPart_ne _ _ hd]
      exact hp
  agent' := fun {d i γ} hq => by
    by_cases hd : d = c
    · subst hd
      rw [setPart_same] at hq
      rcases hq with ⟨hi, h1, h2⟩ | ⟨o, j, rfl, hl⟩
      · exact .inl ⟨h.agent' hi, fun e => h1 (List.append_cancel_right e),
          fun e => h2 (List.append_cancel_right e)⟩
      · cases o with
        | none =>
          rw [hs α β R hR j] at hl
          cases hl
        | some s => exact .inr ⟨some s, j, (child_tag a b _ s j).symm, hl⟩
    · rw [setPart_ne _ _ hd] at hq
      exact .inl ⟨h.agent' hq, fun e => hd (snoc_inj e).2, fun e => hd (snoc_inj e).2⟩
  link' := fun {d p q} hq => by
    by_cases hd : d = c
    · subst hd
      rw [setPart_same] at hq
      rcases hq with hl | ⟨x, y, hxy, rfl, rfl⟩
      · exact .inl (h.link' hl)
      · have hx := hs.port hR hxy
        have hy := hs.port hR ((sys.rule_wf hR).symm hxy)
        exact .inr ⟨x, y, hxy, (emb_tag a b _ x hx).symm, (emb_tag a b _ y hy).symm⟩
    · rw [setPart_ne _ _ hd] at hq
      exact .inl (h.link' hq)
  free' := fun {d p} hq => by
    by_cases hd : d = c
    · subst hd
      rw [setPart_same] at hq
      exact h.free' hq
    · rw [setPart_ne _ _ hd] at hq
      exact h.free' hq

/-- **A step of a part is a step of the whole.** -/
theorem Net.Made.step {sys : System S} (hs : sys.Sided) (h : U.Made P) {c : Nat} {Q : Net S}
    (st : Step sys (P c) Q) : ∃ U', Step sys U U' ∧ U'.Made (setPart P c Q) := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := st
  obtain ⟨v, x, w⟩ := r.conn
  exact ⟨U.fire (a ++ [c]) (b ++ [c]) R,
    ⟨a ++ [c], b ++ [c], α, β, R,
      ⟨h.agent' r.ha, h.agent' r.hb, fun e => r.ne (List.append_cancel_right e),
        ⟨tagPort c v, tagPort c x, h.walk sys.ar w⟩, r.rule⟩, rfl⟩,
    h.fire hs r.rule⟩

theorem Net.Made.steps_aux {sys : System S} (hs : sys.Sided) {c n : Nat} {A Q : Net S}
    (st : Steps (Step sys) n A Q) : ∀ {P : Nat → Net S} {U : Net S}, U.Made P → P c = A →
      ∃ U', Steps (Step sys) n U U' ∧ U'.Made (setPart P c Q) := by
  induction st with
  | refl A =>
    intro P U h e
    refine ⟨U, .refl _, h.congr fun d => ?_⟩
    by_cases hd : d = c
    · rw [hd, setPart_same, e]
    · rw [setPart_ne _ _ hd]
  | head s _ ih =>
    intro P U h e
    rw [← e] at s
    obtain ⟨U₁, s₁, h₁⟩ := h.step hs s
    obtain ⟨U', s', h'⟩ := ih h₁ (setPart_same _ _ _)
    refine ⟨U', .head s₁ s', h'.congr fun d => ?_⟩
    by_cases hd : d = c
    · rw [hd, setPart_same, setPart_same]
    · rw [setPart_ne _ _ hd, setPart_ne _ _ hd, setPart_ne _ _ hd]

/-- **A reduction of a part is a reduction of the whole**, step for
step. -/
theorem Net.Made.steps {sys : System S} (hs : sys.Sided) (h : U.Made P) {c n : Nat}
    {Q : Net S} (st : Steps (Step sys) n (P c) Q) :
    ∃ U', Steps (Step sys) n U U' ∧ U'.Made (setPart P c Q) :=
  Net.Made.steps_aux hs st h rfl

/-! ### All the parts -/

/-- The parts with those of the tags `T` replaced by the nets `nf`. -/
def partsAt (P nf : Nat → Net S) (T : List Nat) : Nat → Net S :=
  fun c => if c ∈ T then nf c else P c

theorem partsAt_mem (P nf : Nat → Net S) {T : List Nat} {c : Nat} (h : c ∈ T) :
    partsAt P nf T c = nf c := by
  show (if c ∈ T then nf c else P c) = nf c
  exact ite_pos' h

theorem partsAt_not_mem (P nf : Nat → Net S) {T : List Nat} {c : Nat} (h : ¬ c ∈ T) :
    partsAt P nf T c = P c := by
  show (if c ∈ T then nf c else P c) = P c
  exact ite_neg' h

/-- The steps of the reductions of the parts with the tags `T`. -/
def stepsOf (cl : Nat → Nat) : List Nat → Nat
  | [] => 0
  | c :: T => cl c + stepsOf cl T

/-- **The parts reduce one after the other.** -/
theorem Net.Made.steps_all {sys : System S} (hs : sys.Sided) (cl : Nat → Nat)
    (nf : Nat → Net S) : ∀ (T : List Nat) {P : Nat → Net S} {U : Net S}, T.Nodup → U.Made P →
      (∀ c, c ∈ T → Steps (Step sys) (cl c) (P c) (nf c)) →
      ∃ U', Steps (Step sys) (stepsOf cl T) U U' ∧ U'.Made (partsAt P nf T)
  | [], P, U, _, h, _ =>
    ⟨U, .refl _, h.congr fun c => (partsAt_not_mem P nf List.not_mem_nil).symm⟩
  | c :: T, P, U, hT, h, hst => by
    obtain ⟨hc, hT'⟩ := List.nodup_cons.1 hT
    obtain ⟨U₁, s₁, h₁⟩ := h.steps hs (hst c List.mem_cons_self)
    obtain ⟨U', s', h'⟩ := Net.Made.steps_all hs cl nf T hT' h₁ (fun d hd => by
      have hne : d ≠ c := fun e => hc (by
        rw [← e]
        exact hd)
      rw [setPart_ne _ _ hne]
      exact hst d (List.mem_cons_of_mem _ hd))
    refine ⟨U', s₁.trans s', h'.congr fun d => ?_⟩
    by_cases hdT : d ∈ T
    · rw [partsAt_mem _ _ hdT, partsAt_mem _ _ (List.mem_cons_of_mem _ hdT)]
    · rw [partsAt_not_mem _ _ hdT]
      by_cases hdc : d = c
      · rw [hdc, setPart_same, partsAt_mem _ _ List.mem_cons_self]
      · have hn : ¬ d ∈ c :: T := fun hm => (List.mem_cons.1 hm).elim hdc hdT
        rw [setPart_ne _ _ hdc, partsAt_not_mem _ _ hn]

/-- **A net made of normal nets is normal.**  An active pair of the whole
is an active pair of one part: its two agents carry tags, and the wire
between them stays in one part. -/
theorem Net.Made.normal {sys : System S} (h : U.Made P)
    (hn : ∀ c, Normal (Step sys) (P c)) : Normal (Step sys) U := by
  rintro U' ⟨a', b', α, β, R, r, -⟩
  obtain ⟨c, a, rfl, ha⟩ := h.agent r.ha
  obtain ⟨d, b, rfl, hb⟩ := h.agent r.hb
  obtain ⟨v', x', w⟩ := r.conn
  obtain ⟨v, x, y, -, -, ey, wk⟩ := h.walk_back sys.ar (c := c) w (a, 0) rfl
  obtain ⟨yi, yk⟩ := y
  have ey' : ((b ++ [d], 0) : Port) = (yi ++ [c], yk) := ey
  injection ey' with e1 e2
  obtain ⟨e3, e4⟩ := snoc_inj e1
  subst e2
  subst e3
  subst e4
  exact hn _ _ ⟨_, _, α, β, R, ⟨ha, hb, fun e => r.ne (by rw [e]), ⟨v, x, wk⟩, r.rule⟩, rfl⟩

/-- **What a net made of nets with normal forms reduces to.**  Let the
rules give every new agent a side.  If the parts with the tags `T` reduce
to normal forms, and the other parts are normal, then the whole reduces,
in as many steps as those parts together, to a normal form, and that
normal form is made of the normal forms. -/
theorem Net.Made.reduce {sys : System S} (hs : sys.Sided) (h : U.Made P) {T : List Nat}
    (hT : T.Nodup) (cl : Nat → Nat) (nf : Nat → Net S)
    (hst : ∀ c, c ∈ T → Steps (Step sys) (cl c) (P c) (nf c))
    (hnf : ∀ c, c ∈ T → Normal (Step sys) (nf c))
    (hrest : ∀ c, ¬ c ∈ T → Normal (Step sys) (P c)) :
    ∃ U', Steps (Step sys) (stepsOf cl T) U U' ∧ Normal (Step sys) U' ∧
      U'.Made (partsAt P nf T) := by
  obtain ⟨U', s, h'⟩ := Net.Made.steps_all hs cl nf T hT h hst
  refine ⟨U', s, h'.normal fun c => ?_, h'⟩
  by_cases hc : c ∈ T
  · rw [partsAt_mem _ _ hc]
    exact hnf c hc
  · rw [partsAt_not_mem _ _ hc]
    exact hrest c hc

end Made

/-! ### The thread machine on such a net -/

section Machine

variable {S : Type} [DecidableEq S]

/-- **Nets side by side come out right, whatever the threads do.**  Let
the rules give every new agent a side, and let the memory hold a
well-formed net made of nets under tags, those with the tags `T` having
normal forms and the others being normal.  Then, with any number of
threads and any schedule, a run that ends at rest has made as many claims
as the reductions of the parts have steps, and the memory is made of the
normal forms. -/
theorem XMach.made_rest (xs : XSys S) (hs : xs.sys.Sided) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {P : Nat → Net S} (h : X.toNet.Made P) {T : List Nat}
    (hT : T.Nodup) (cl : Nat → Nat) (nf : Nat → Net S)
    (hst : ∀ c, c ∈ T → Steps (Step xs.sys) (cl c) (P c) (nf c))
    (hnf : ∀ c, c ∈ T → Normal (Step xs.sys) (nf c))
    (hrest : ∀ c, ¬ c ∈ T → Normal (Step xs.sys) (P c))
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init X nt).trace xs σ i).1.resting = true) :
    ((XMach.init X nt).trace xs σ i).2 = stepsOf cl T ∧
      ((XMach.init X nt).trace xs σ i).1.mem.toNet.Made (partsAt P nf T) := by
  obtain ⟨U', s, hn', h'⟩ := h.reduce hs hT cl nf hst hnf hrest
  have L := XMach.trace_live σ (XMach.init_live (xs := xs) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xs σ (XMach.init X nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e, ek⟩ := (hu s).2 hn'
  have e' : U' = ((XMach.init X nt).trace xs σ i).1.mem.toNet := e
  rw [← e']
  exact ⟨ek.symm, h'⟩

/-- **Nets side by side under a fair schedule.**  In the same situation,
with any number of threads and any unending schedule in which every
thread keeps being scheduled, from some action on every thread is at
rest, the claims are the steps of the reductions of the parts, and the
memory is made of the normal forms. -/
theorem XMach.made_fair (xs : XSys S) (hs : xs.sys.Sided) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {P : Nat → Net S} (h : X.toNet.Made P) {T : List Nat}
    (hT : T.Nodup) (cl : Nat → Nat) (nf : Nat → Net S)
    (hst : ∀ c, c ∈ T → Steps (Step xs.sys) (cl c) (P c) (nf c))
    (hnf : ∀ c, c ∈ T → Normal (Step xs.sys) (nf c))
    (hrest : ∀ c, ¬ c ∈ T → Normal (Step xs.sys) (P c))
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init X nt).trace xs σ i).1.resting = true ∧
      ((XMach.init X nt).trace xs σ i).2 = stepsOf cl T ∧
      ((XMach.init X nt).trace xs σ i).1.mem.toNet.Made (partsAt P nf T) := by
  obtain ⟨U', s, hn', h'⟩ := h.reduce hs hT cl nf hst hnf hrest
  obtain ⟨i₀, hh⟩ := XMach.fair_complete (xs := xs) hX hnt s hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, hc, e⟩ := hh i hi
  rw [e]
  exact ⟨hr, hc, h'⟩

end Machine

/-! ### The addition system -/

namespace Arith

/-- The rules of addition give every new agent a side. -/
theorem system_sided : system.Sided := by
  intro α β R hR j
  cases α <;> cases β
  case add.zero =>
    have e : system.rule add zero = some addZero.toX.toRhs := rfl
    rw [e] at hR
    injection hR with hR
    rw [← hR]
    rfl
  case zero.add =>
    have e : system.rule zero add = some addZero.swap.toX.toRhs := rfl
    rw [e] at hR
    injection hR with hR
    rw [← hR]
    rfl
  case add.succ =>
    have e : system.rule add succ = some addSucc.toX.toRhs := rfl
    rw [e] at hR
    injection hR with hR
    rw [← hR]
    rfl
  case succ.add =>
    have e : system.rule succ add = some addSucc.swap.toX.toRhs := rfl
    rw [e] at hR
    injection hR with hR
    rw [← hR]
    rfl
  all_goals
    exact absurd hR (by
      intro h
      cases h)

/-- Nets side by side are made of them. -/
theorem made_besides {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup) :
    (besides L).toNet.Made (partOf L) :=
  have hp := parts_besides hnd
  ⟨hp.agent, hp.link, hp.free, hp.agent', hp.link', hp.free'⟩

theorem partOf_none : ∀ {L : List (Nat × XNet Arith)} {c : Nat},
    ¬ c ∈ L.map Prod.fst → partOf L c = noNet
  | [], _, _ => rfl
  | e :: L, c, h => by
    show (if c = e.1 then e.2.toNet else partOf L c) = noNet
    have hne : c ≠ e.1 := fun hc => h (by
      rw [hc]
      exact List.mem_cons_self)
    rw [ite_neg' hne]
    exact partOf_none fun hm => h (List.mem_cons_of_mem _ hm)

theorem noNet_normal : Normal (Step system) noNet := by
  rintro N' ⟨a, b, α, β, R, r, -⟩
  exact r.ha

/-- The normal forms `nf`, under the tags of `L`. -/
def normalParts (L : List (Nat × XNet Arith)) (nf : Nat → Net Arith) : Nat → Net Arith :=
  partsAt (fun _ => noNet) nf (L.map Prod.fst)

/-- **Any nets side by side reduce as each does alone.**  Let nets be put
side by side under different tags, and let the net with the tag `c`
reduce in `cl c` steps to the normal form `nf c`.  Then the whole
reduces, in as many steps as the nets together, to a normal form, and
that normal form is made of the normal forms, each under its tag. -/
theorem besides_reduce {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup)
    (cl : Nat → Nat) (nf : Nat → Net Arith)
    (hst : ∀ e, e ∈ L → Steps (Step system) (cl e.1) e.2.toNet (nf e.1))
    (hnf : ∀ e, e ∈ L → Normal (Step system) (nf e.1)) :
    ∃ Z : Net Arith, Steps (Step system) (stepsOf cl (L.map Prod.fst)) (besides L).toNet Z ∧
      Normal (Step system) Z ∧ Z.Made (normalParts L nf) := by
  have hpart : ∀ c, c ∈ L.map Prod.fst → ∃ e, e ∈ L ∧ e.1 = c ∧ partOf L c = e.2.toNet := by
    intro c hc
    obtain ⟨e, he, ec⟩ := List.mem_map.1 hc
    refine ⟨e, he, ec, ?_⟩
    rw [← ec]
    exact partOf_mem hnd (show (e.1, e.2) ∈ L from he)
  obtain ⟨Z, s, hn, hm⟩ := (made_besides hnd).reduce system_sided hnd cl nf
    (fun c hc => by
      obtain ⟨e, he, ec, ep⟩ := hpart c hc
      rw [ep, ← ec]
      exact hst e he)
    (fun c hc => by
      obtain ⟨e, he, ec, -⟩ := hpart c hc
      rw [← ec]
      exact hnf e he)
    (fun c hc => by
      rw [partOf_none hc]
      exact noNet_normal)
  refine ⟨Z, s, hn, hm.congr fun c => ?_⟩
  by_cases hc : c ∈ L.map Prod.fst
  · show partsAt (partOf L) nf (L.map Prod.fst) c = partsAt (fun _ => noNet) nf (L.map Prod.fst) c
    rw [partsAt_mem _ _ hc, partsAt_mem _ _ hc]
  · show partsAt (partOf L) nf (L.map Prod.fst) c = partsAt (fun _ => noNet) nf (L.map Prod.fst) c
    rw [partsAt_not_mem _ _ hc, partsAt_not_mem _ _ hc, partOf_none hc]

/-- **Any nets side by side come out right, whatever the threads do.**
Let well-formed compact nets be put side by side under different tags,
and let the net with the tag `c` reduce in `cl c` steps to the normal
form `nf c`.  Then, with any number of threads and any schedule, a run
that ends at rest has made as many claims as the reductions have steps,
and the memory is made of the normal forms, each under its tag. -/
theorem besides_rest {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup)
    (hOk : ∀ e, e ∈ L → e.2.Ok ar) (cl : Nat → Nat) (nf : Nat → Net Arith)
    (hst : ∀ e, e ∈ L → Steps (Step system) (cl e.1) e.2.toNet (nf e.1))
    (hnf : ∀ e, e ∈ L → Normal (Step system) (nf e.1))
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (besides L) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (besides L) nt).trace xsys σ i).2 = stepsOf cl (L.map Prod.fst) ∧
      ((XMach.init (besides L) nt).trace xsys σ i).1.mem.toNet.Made (normalParts L nf) := by
  obtain ⟨Z, s, hn', hm⟩ := besides_reduce hnd cl nf hst hnf
  have hX := besides_wf hnd hOk
  have L' := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L'.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (besides L) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e, ek⟩ := (hu s).2 hn'
  have e' : Z = ((XMach.init (besides L) nt).trace xsys σ i).1.mem.toNet := e
  rw [← e']
  exact ⟨ek.symm, hm⟩

/-- **Any nets side by side under a fair schedule.**  In the same
situation, with any number of threads and any unending schedule in which
every thread keeps being scheduled, from some action on every thread is
at rest, the claims are the steps of the reductions, and the memory is
made of the normal forms. -/
theorem besides_fair {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup)
    (hOk : ∀ e, e ∈ L → e.2.Ok ar) (cl : Nat → Nat) (nf : Nat → Net Arith)
    (hst : ∀ e, e ∈ L → Steps (Step system) (cl e.1) e.2.toNet (nf e.1))
    (hnf : ∀ e, e ∈ L → Normal (Step system) (nf e.1))
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (besides L) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (besides L) nt).trace xsys σ i).2 = stepsOf cl (L.map Prod.fst) ∧
      ((XMach.init (besides L) nt).trace xsys σ i).1.mem.toNet.Made (normalParts L nf) := by
  obtain ⟨Z, s, hn', hm⟩ := besides_reduce hnd cl nf hst hnf
  obtain ⟨i₀, hh⟩ := XMach.fair_complete (xs := xsys) (besides_wf hnd hOk) hnt s hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, hc, e⟩ := hh i hi
  rw [e]
  exact ⟨hr, hc, hm⟩

/-! ### Numerals -/

/-- A numeral of a part is a numeral of the whole. -/
theorem made_num {U : Net Arith} {P : Nat → Net Arith} (h : U.Made P) {c : Nat} :
    ∀ {k : Nat} {i : Id}, Num (P c) i k → Num U (i ++ [c]) k
  | 0, _, hz => h.agent' hz
  | _ + 1, _, ⟨hs, i', hp, hn⟩ => ⟨h.agent' hs, i' ++ [c], h.paired ar hp, made_num h hn⟩

theorem made_isNum {U : Net Arith} {P : Nat → Net Arith} (h : U.Made P) {c : Nat} {p : Port}
    {k : Nat} (hn : IsNum (P c) p k) : IsNum U (tagPort c p) k := by
  obtain ⟨i, hp, hk⟩ := hn
  exact ⟨i ++ [c], h.paired ar hp, made_num h hk⟩

/-- **The numerals of the normal forms are in the memory at rest.**  In
the situation of `besides_rest`, if the normal form of one of the nets
has the numeral `k` on the port `p`, the memory has the numeral `k` on
that port under the tag of the net. -/
theorem besides_rest_num {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup)
    (hOk : ∀ e, e ∈ L → e.2.Ok ar) (cl : Nat → Nat) (nf : Nat → Net Arith)
    (hst : ∀ e, e ∈ L → Steps (Step system) (cl e.1) e.2.toNet (nf e.1))
    (hnf : ∀ e, e ∈ L → Normal (Step system) (nf e.1))
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (besides L) nt).trace xsys σ i).1.resting = true)
    {e : Nat × XNet Arith} (he : e ∈ L) {p : Port} {k : Nat} (hk : IsNum (nf e.1) p k) :
    IsNum ((XMach.init (besides L) nt).trace xsys σ i).1.mem.toNet (tagPort e.1 p) k := by
  obtain ⟨-, hm⟩ := besides_rest hnd hOk cl nf hst hnf hnt σ hr
  refine made_isNum hm (c := e.1) ?_
  have hc : e.1 ∈ L.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) he
  show IsNum (partsAt (fun _ => noNet) nf (L.map Prod.fst) e.1) p k
  rw [partsAt_mem _ _ hc]
  exact hk

/-- An addition and a numeral side by side, with any number of threads and
any schedule: a run that ends at rest has made the three claims of
`2 + 3`, the memory has `5` on the free port of the addition, and the
numeral is as it was. -/
example {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (besides [(0, sum 2 3), (1, two)]) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (besides [(0, sum 2 3), (1, two)]) nt).trace xsys σ i).2 = 3 ∧
      IsNum ((XMach.init (besides [(0, sum 2 3), (1, two)]) nt).trace xsys σ i).1.mem.toNet
        ([0, 0], 0) 5 ∧
      ∀ j γ, ((XMach.init (besides [(0, sum 2 3), (1, two)]) nt).trace xsys σ i).1.mem.toNet.agent
        (j ++ [1]) γ ↔ two.toNet.agent j γ := by
  obtain ⟨N', hs, hn, hnum⟩ := add_correct (good_sum 2 3).config
  have hnd : (([(0, sum 2 3), (1, two)] : List (Nat × XNet Arith)).map Prod.fst).Nodup := by
    decide
  have htwo : Normal (Step system) two.toNet := normal_of_no_add fun j h => by
    have h' : (j, Arith.add) ∈
        [(([3] : Id), Arith.succ), ([4], Arith.zero), ([0, 0], Arith.succ)] := h
    simp at h'
  have hOk : ∀ e, e ∈ [(0, sum 2 3), (1, two)] → e.2.Ok ar := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact sum_ok 2 3
    · rcases List.mem_cons.1 he with rfl | he
      · exact (by decide : two.Ok ar)
      · exact absurd he List.not_mem_nil
  have hst : ∀ e, e ∈ [(0, sum 2 3), (1, two)] →
      Steps (Step system) ((fun c : Nat => if c = 0 then 3 else 0) e.1) e.2.toNet
        ((fun c : Nat => if c = 0 then N' else two.toNet) e.1) := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hs
    · rcases List.mem_cons.1 he with rfl | he
      · exact .refl _
      · exact absurd he List.not_mem_nil
  have hnf : ∀ e, e ∈ [(0, sum 2 3), (1, two)] →
      Normal (Step system) ((fun c : Nat => if c = 0 then N' else two.toNet) e.1) := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hn
    · rcases List.mem_cons.1 he with rfl | he
      · exact htwo
      · exact absurd he List.not_mem_nil
  obtain ⟨hc, hm⟩ := besides_rest hnd hOk (fun c : Nat => if c = 0 then 3 else 0)
    (fun c : Nat => if c = 0 then N' else two.toNet) hst hnf hnt σ hr
  have h5 := besides_rest_num hnd hOk (fun c : Nat => if c = 0 then 3 else 0)
    (fun c : Nat => if c = 0 then N' else two.toNet) hst hnf hnt σ hr (e := (0, sum 2 3))
    List.mem_cons_self (p := ([0], 0)) (k := 5) hnum
  have e1 : normalParts [(0, sum 2 3), (1, two)]
      (fun c : Nat => if c = 0 then N' else two.toNet) 1 = two.toNet :=
    partsAt_mem _ _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨hc, h5, fun j γ => ?_⟩
  have h1 := hm.agent_iff (c := 1) (i := j) (γ := γ)
  rw [e1] at h1
  exact h1

end Arith

end INet
