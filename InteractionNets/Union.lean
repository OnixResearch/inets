import InteractionNets.Plug
import InteractionNets.Fair

/-! # Nets side by side, names apart

Two nets are put side by side with their names as they are
(`Net.union`).  This asks that their names are apart: no name of one, and
no name made from it by putting numbers in front, as the names of new
agents are made, is a name of the other or made from one
(`Net.Apart`).  Then a step of one net is a step of the union, and the
names stay apart (`Step.union_left`); the union is well formed when the
two nets are (`Net.WF.union`) and normal when they are
(`Net.Apart.normal`).  So the union reduces to the union of the normal
forms, in as many steps as the two nets together (`Net.Apart.reduce`),
and the thread machine at rest holds exactly that net
(`XMach.union_rest`, `XMach.union_fair`).

This is for any interaction system.  With `Net.plug` it says that a net
reduces inside a larger net as it does alone.
-/

namespace INet

variable {S : Type}

/-- **Two nets side by side**, with their names as they are. -/
def Net.union (A B : Net S) : Net S where
  agent i γ := A.agent i γ ∨ B.agent i γ
  link p q := A.link p q ∨ B.link p q
  free p := A.free p ∨ B.free p

/-- **Names apart.**  No name in use in `A`, with any numbers in front,
is a name in use in `B` with any numbers in front. -/
def Net.Apart (A B : Net S) : Prop :=
  ∀ (l l' : List Nat) (i j : Id), A.Used i → B.Used j → l ++ i ≠ l' ++ j

theorem Net.used_agent {N : Net S} {i : Id} {γ : S} (h : N.agent i γ) : N.Used i :=
  .inl ⟨γ, h⟩

theorem Net.used_free {N : Net S} {p : Port} (h : N.free p) : N.Used p.1 :=
  .inr (.inr ⟨p.2, h⟩)

variable {A A' B B' : Net S}

theorem Net.union_comm (A B : Net S) : A.union B = B.union A :=
  Net.ext' (fun _ _ => Or.comm) (fun _ _ => Or.comm) (fun _ => Or.comm)

theorem Net.Apart.symm (h : A.Apart B) : B.Apart A :=
  fun l l' i j hi hj e => h l' l j i hj hi e.symm

/-- No name is in use in both nets. -/
theorem Net.Apart.used (h : A.Apart B) {i : Id} (hA : A.Used i) (hB : B.Used i) : False :=
  h [] [] i i hA hB rfl

/-- Nets whose names end in different tags have their names apart. -/
theorem Net.Apart.of_tags {c c' : Nat} (hc : c ≠ c')
    (hA : ∀ i, A.Used i → ∃ i', i = i' ++ [c]) (hB : ∀ j, B.Used j → ∃ j', j = j' ++ [c']) :
    A.Apart B := by
  intro l l' i j hi hj e
  obtain ⟨i', rfl⟩ := hA i hi
  obtain ⟨j', rfl⟩ := hB j hj
  rw [← List.append_assoc, ← List.append_assoc] at e
  have e' := (List.append_inj' e rfl).2
  injection e' with e''
  exact hc e''

theorem Net.used_union {i : Id} (h : (A.union B).Used i) : A.Used i ∨ B.Used i := by
  rcases h with ⟨γ, h | h⟩ | ⟨k, q, h | h⟩ | ⟨k, h | h⟩
  · exact .inl (.inl ⟨γ, h⟩)
  · exact .inr (.inl ⟨γ, h⟩)
  · exact .inl (.inr (.inl ⟨k, q, h⟩))
  · exact .inr (.inr (.inl ⟨k, q, h⟩))
  · exact .inl (.inr (.inr ⟨k, h⟩))
  · exact .inr (.inr (.inr ⟨k, h⟩))

/-! ### Ends and wires -/

theorem Net.end_union_left {ar : S → Nat} {p : Port} (he : A.End ar p) :
    (A.union B).End ar p := by
  rcases he with hf | ⟨γ, hγ, hk⟩
  · exact .inl (.inl hf)
  · exact .inr ⟨γ, .inl hγ, hk⟩

theorem Net.end_union_swap {ar : S → Nat} {p : Port} (he : (A.union B).End ar p) :
    (B.union A).End ar p := by
  rw [Net.union_comm]
  exact he

theorem Net.end_union_right {ar : S → Nat} {p : Port} (he : B.End ar p) :
    (A.union B).End ar p :=
  Net.end_union_swap (Net.end_union_left he)

theorem Net.end_union_cases {ar : S → Nat} {p : Port} (he : (A.union B).End ar p) :
    A.End ar p ∨ B.End ar p := by
  rcases he with (hf | hf) | ⟨γ, hγ | hγ, hk⟩
  · exact .inl (.inl hf)
  · exact .inr (.inl hf)
  · exact .inl (.inr ⟨γ, hγ, hk⟩)
  · exact .inr (.inr ⟨γ, hγ, hk⟩)

/-- An end of the union at a name of `A` is an end of `A`. -/
theorem Net.Apart.end_left (h : A.Apart B) {ar : S → Nat} {p : Port} (hp : A.Used p.1)
    (he : (A.union B).End ar p) : A.End ar p := by
  rcases he with (hf | hf) | ⟨γ, hγ | hγ, hk⟩
  · exact .inl hf
  · exact (h.used hp (Net.used_free hf)).elim
  · exact .inr ⟨γ, hγ, hk⟩
  · exact (h.used hp (Net.used_agent hγ)).elim

/-- A segment of the union at a name of `A` is a segment of `A`. -/
theorem Net.Apart.link_left (h : A.Apart B) {p q : Port} (hp : A.Used p.1)
    (hl : (A.union B).link p q) : A.link p q := by
  rcases hl with hl | hl
  · exact hl
  · exact (h.used hp (Net.used_link hl)).elim

/-- A wire of `A` is a wire of the union. -/
theorem Net.Apart.walk_left (h : A.Apart B) (hs : ∀ {p q}, A.link p q → A.link q p)
    {ar : S → Nat} {u v x y : Port} (w : Walk A.link (A.End ar) u v x y) :
    Walk (A.union B).link ((A.union B).End ar) u v x y :=
  w.mono (fun hl => .inl hl)
    (fun hl hq hq' => hq (h.end_left (Net.used_link (hs hl)) hq'))

theorem Net.Apart.walk_right (h : A.Apart B) (hs : ∀ {p q}, B.link p q → B.link q p)
    {ar : S → Nat} {u v x y : Port} (w : Walk B.link (B.End ar) u v x y) :
    Walk (A.union B).link ((A.union B).End ar) u v x y := by
  rw [Net.union_comm]
  exact h.symm.walk_left hs w

/-- A wire of the union that starts at a name of `A` is a wire of `A`. -/
theorem Net.Apart.walk_back (h : A.Apart B) (hs : ∀ {p q}, A.link p q → A.link q p)
    {ar : S → Nat} {u v x y : Port}
    (w : Walk (A.union B).link ((A.union B).End ar) u v x y) :
    A.Used u.1 → Walk A.link (A.End ar) u v x y := by
  induction w with
  | single hl =>
    intro hu
    exact .single (h.link_left hu hl)
  | cons hl hT hne _ ih =>
    intro hu
    have hl' := h.link_left hu hl
    exact .cons hl' (fun he => hT (Net.end_union_left he)) hne (ih (Net.used_link (hs hl')))

/-! ### Steps -/

theorem Net.fire_union (h : A.Apart B) {a b : Id} {α β : S} (ha : A.agent a α)
    (hb : A.agent b β) (R : Rhs S) : (A.union B).fire a b R = (A.fire a b R).union B := by
  apply Net.ext'
  · intro i γ
    show (((A.agent i γ ∨ B.agent i γ) ∧ i ≠ a ∧ i ≠ b) ∨
        ∃ o j, i = child a b o j ∧ R.lab o j = some γ) ↔
      (((A.agent i γ ∧ i ≠ a ∧ i ≠ b) ∨ ∃ o j, i = child a b o j ∧ R.lab o j = some γ) ∨
        B.agent i γ)
    constructor
    · rintro (⟨hA | hB, h1, h2⟩ | hc)
      · exact .inl (.inl ⟨hA, h1, h2⟩)
      · exact .inr hB
      · exact .inl (.inr hc)
    · rintro ((⟨hA, h1, h2⟩ | hc) | hB)
      · exact .inl ⟨.inl hA, h1, h2⟩
      · exact .inr hc
      · refine .inl ⟨.inr hB, fun e => ?_, fun e => ?_⟩
        · rw [e] at hB
          exact h.used (Net.used_agent ha) (Net.used_agent hB)
        · rw [e] at hB
          exact h.used (Net.used_agent hb) (Net.used_agent hB)
  · intro p q
    show ((A.link p q ∨ B.link p q) ∨ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y) ↔
      ((A.link p q ∨ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y) ∨ B.link p q)
    exact or_right_comm
  · intro p
    exact Iff.rfl

/-- A name in use after a firing is a name in use before, or made from
one by putting a number in front. -/
theorem Net.used_of_fire {N : Net S} {a b : Id} {α β : S} (ha : N.agent a α) (hb : N.agent b β)
    {R : Rhs S} {i : Id} (hu : (N.fire a b R).Used i) : ∃ l i₀, i = l ++ i₀ ∧ N.Used i₀ := by
  have hpar : ∀ o, N.Used (par a b o) := fun o => by
    rcases par_eq a b o with e | e
    · rw [e]
      exact Net.used_agent ha
    · rw [e]
      exact Net.used_agent hb
  rcases hu with ⟨γ, ⟨hγ, -, -⟩ | ⟨o, j, e, -⟩⟩ | ⟨k, q, hl | ⟨x, y, -, e, -⟩⟩ | ⟨k, hf⟩
  · exact ⟨[], i, rfl, Net.used_agent hγ⟩
  · exact ⟨[slot o j], par a b o, e, hpar o⟩
  · exact ⟨[], i, rfl, Net.used_link hl⟩
  · cases x with
    | ifc s k' =>
      have e1 : i = sel a b s := congrArg Prod.fst e
      refine ⟨[], i, rfl, ?_⟩
      rw [e1]
      cases s
      · exact Net.used_agent ha
      · exact Net.used_agent hb
    | new o j k' =>
      have e1 : i = child a b o j := congrArg Prod.fst e
      exact ⟨[slot o j], par a b o, e1, hpar o⟩
  · exact ⟨[], i, rfl, .inr (.inr ⟨k, hf⟩)⟩

/-- Names stay apart when a pair fires. -/
theorem Net.Apart.fire (h : A.Apart B) {a b : Id} {α β : S} (ha : A.agent a α)
    (hb : A.agent b β) (R : Rhs S) : (A.fire a b R).Apart B := by
  intro l l' i j hi hj e
  obtain ⟨l₀, i₀, rfl, h₀⟩ := Net.used_of_fire ha hb hi
  exact h (l ++ l₀) l' i₀ j h₀ hj (by
    rw [List.append_assoc]
    exact e)

/-- **A step of a net is a step of the net beside another**, and the
names stay apart. -/
theorem Step.union_left {sys : System S} (hA : A.WF sys.ar) (h : A.Apart B)
    (st : Step sys A A') : Step sys (A.union B) (A'.union B) ∧ A'.Apart B := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := st
  obtain ⟨v, x, w⟩ := r.conn
  exact ⟨⟨a, b, α, β, R, ⟨.inl r.ha, .inl r.hb, r.ne, ⟨v, x, h.walk_left hA.symm w⟩, r.rule⟩,
    (Net.fire_union h r.ha r.hb R).symm⟩, h.fire r.ha r.hb R⟩

/-- **A reduction of a net is a reduction of the net beside another**,
step for step. -/
theorem Steps.union_left {sys : System S} {n : Nat} (hA : A.WF sys.ar) (h : A.Apart B)
    (st : Steps (Step sys) n A A') :
    Steps (Step sys) n (A.union B) (A'.union B) ∧ A'.Apart B := by
  induction st with
  | refl => exact ⟨.refl _, h⟩
  | head s _ ih =>
    obtain ⟨s', h'⟩ := s.union_left hA h
    obtain ⟨ss, h''⟩ := ih (s.wf hA) h'
    exact ⟨.head s' ss, h''⟩

theorem Steps.union_right {sys : System S} {n : Nat} (hB : B.WF sys.ar) (h : A.Apart B)
    (st : Steps (Step sys) n B B') :
    Steps (Step sys) n (A.union B) (A.union B') ∧ A.Apart B' := by
  obtain ⟨s, h'⟩ := Steps.union_left hB h.symm st
  rw [Net.union_comm A B, Net.union_comm A B']
  exact ⟨s, h'.symm⟩

/-- **A net reduces inside a larger net as it does alone.**  Put a
well-formed net beside any other net with names apart, and join any
ports of the two by new segments: every reduction of the net is a
reduction of the whole, step for step. -/
theorem Steps.context {sys : System S} {n : Nat} (hA : A.WF sys.ar) (h : A.Apart B)
    (J : Port → Port → Prop) (st : Steps (Step sys) n A A') :
    Steps (Step sys) n ((A.union B).plug J) ((A'.union B).plug J) :=
  (Steps.union_left hA h st).1.plug J

/-- **Normal nets side by side are a normal net.**  The wire of an active
pair of the union starts at a name of one net and stays in it. -/
theorem Net.Apart.normal {sys : System S} (hA : A.WF sys.ar) (hB : B.WF sys.ar)
    (h : A.Apart B) (nA : Normal (Step sys) A) (nB : Normal (Step sys) B) :
    Normal (Step sys) (A.union B) := by
  rintro U' ⟨a, b, α, β, R, r, -⟩
  obtain ⟨v, x, w⟩ := r.conn
  rcases r.ha with ha | ha
  · have w' := h.walk_back hA.symm w (Net.used_agent ha)
    have hb : A.agent b β := by
      rcases r.hb with hb | hb
      · exact hb
      · exact (h.used (Net.used_link (hA.symm w'.link_last)) (Net.used_agent hb)).elim
    exact nA _ ⟨a, b, α, β, R, ⟨ha, hb, r.ne, ⟨v, x, w'⟩, r.rule⟩, rfl⟩
  · rw [Net.union_comm] at w
    have w' := h.symm.walk_back hB.symm w (Net.used_agent ha)
    have hb : B.agent b β := by
      rcases r.hb with hb | hb
      · exact (h.used (Net.used_agent hb) (Net.used_link (hB.symm w'.link_last))).elim
      · exact hb
    exact nB _ ⟨a, b, α, β, R, ⟨ha, hb, r.ne, ⟨v, x, w'⟩, r.rule⟩, rfl⟩

/-- **Well-formed nets side by side, names apart, are a well-formed
net.** -/
theorem Net.WF.union {ar : S → Nat} (hA : A.WF ar) (hB : B.WF ar) (h : A.Apart B) :
    (A.union B).WF ar where
  agent_fun := fun {i α β} h1 h2 => by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hA.agent_fun h1 h2
    · exact (h.used (Net.used_agent h1) (Net.used_agent h2)).elim
    · exact (h.used (Net.used_agent h2) (Net.used_agent h1)).elim
    · exact hB.agent_fun h1 h2
  symm := fun {p q} hl => by
    rcases hl with hl | hl
    · exact .inl (hA.symm hl)
    · exact .inr (hB.symm hl)
  irrefl := fun {p} hl => by
    rcases hl with hl | hl
    · exact hA.irrefl hl
    · exact hB.irrefl hl
  end_unique := fun {p q r} hp h1 h2 => by
    rcases h1 with l1 | l1
    · have u := Net.used_link l1
      exact hA.end_unique (h.end_left u hp) l1 (h.link_left u h2)
    · have u := Net.used_link l1
      exact hB.end_unique (h.symm.end_left u (Net.end_union_swap hp)) l1
        (h.symm.link_left u (Or.symm h2))
  end_conn := fun {p} hp => by
    rcases Net.end_union_cases hp with he | he
    · obtain ⟨q, hq, hne, v, x, w⟩ := hA.end_conn he
      exact ⟨q, Net.end_union_left hq, hne, v, x, h.walk_left hA.symm w⟩
    · obtain ⟨q, hq, hne, v, x, w⟩ := hB.end_conn he
      exact ⟨q, Net.end_union_right hq, hne, v, x, h.walk_right hB.symm w⟩
  deg := fun {p x y z} h1 h2 h3 => by
    rcases h1 with l1 | l1
    · have u := Net.used_link l1
      exact hA.deg l1 (h.link_left u h2) (h.link_left u h3)
    · have u := Net.used_link l1
      exact hB.deg l1 (h.symm.link_left u (Or.symm h2)) (h.symm.link_left u (Or.symm h3))
  free_agent := fun {i k α} hf ha => by
    rcases hf with hf | hf <;> rcases ha with ha | ha
    · exact hA.free_agent hf ha
    · exact h.used (Net.used_free hf) (Net.used_agent ha)
    · exact h.used (Net.used_agent ha) (Net.used_free hf)
    · exact hB.free_agent hf ha
  fresh := fun {a α} l ha hu => by
    rcases ha with ha | ha <;> rcases Net.used_union hu with hu' | hu'
    · exact hA.fresh l ha hu'
    · exact (h l [] a (l ++ a) (Net.used_agent ha) hu' rfl).elim
    · exact (h [] l (l ++ a) a hu' (Net.used_agent ha) rfl).elim
    · exact hB.fresh l ha hu'

/-- **What two nets side by side reduce to.**  If the nets are well
formed, have their names apart and reduce to normal forms, the union
reduces, in as many steps as the two together, to the union of the
normal forms, and that is a normal form. -/
theorem Net.Apart.reduce {sys : System S} (hA : A.WF sys.ar) (hB : B.WF sys.ar)
    (h : A.Apart B) {n m : Nat} (sA : Steps (Step sys) n A A') (nA : Normal (Step sys) A')
    (sB : Steps (Step sys) m B B') (nB : Normal (Step sys) B') :
    Steps (Step sys) (n + m) (A.union B) (A'.union B') ∧ Normal (Step sys) (A'.union B') := by
  obtain ⟨s1, h1⟩ := Steps.union_left hA h sA
  obtain ⟨s2, h2⟩ := Steps.union_right hB h1 sB
  exact ⟨s1.trans s2, h2.normal (Steps.wf hA sA) (Steps.wf hB sB) nA nB⟩

/-! ### In memory -/

/-- Two memories side by side: the cells of the first, then those of the
second. -/
def XNet.union (X Y : XNet S) : XNet S :=
  ⟨X.agents ++ Y.agents, X.free ++ Y.free, X.wires ++ Y.wires⟩

theorem XNet.union_toNet (X Y : XNet S) : (X.union Y).toNet = X.toNet.union Y.toNet :=
  Net.ext' (fun _ _ => List.mem_append) (fun _ _ => List.mem_append) (fun _ => List.mem_append)

section Machine

variable [DecidableEq S]

/-- **Two nets side by side come out right, whatever the threads do, in
any system.**  Let two memories hold well-formed nets with their names
apart, each with a normal form.  Then, with any number of threads and any
schedule, a run on the two side by side that ends at rest has made as
many claims as the two reductions have steps, and the memory holds the
two normal forms side by side. -/
theorem XMach.union_rest (xs : XSys S) {X Y : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hY : Y.toNet.WF xs.sys.ar) (h : X.toNet.Apart Y.toNet) {n m : Nat}
    (sA : Steps (Step xs.sys) n X.toNet A') (nA : Normal (Step xs.sys) A')
    (sB : Steps (Step xs.sys) m Y.toNet B') (nB : Normal (Step xs.sys) B')
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (X.union Y) nt).trace xs σ i).1.resting = true) :
    ((XMach.init (X.union Y) nt).trace xs σ i).2 = n + m ∧
      ((XMach.init (X.union Y) nt).trace xs σ i).1.mem.toNet = A'.union B' := by
  obtain ⟨s, hn'⟩ := h.reduce hX hY sA nA sB nB
  have hU : (X.union Y).toNet.WF xs.sys.ar := by
    rw [XNet.union_toNet]
    exact hX.union hY h
  rw [← XNet.union_toNet] at s
  have L := XMach.trace_live σ (XMach.init_live (xs := xs) hU hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xs σ (XMach.init (X.union Y) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hU r q hn
  obtain ⟨e, ek⟩ := (hu s).2 hn'
  exact ⟨ek.symm, e.symm⟩

/-- **Two nets side by side under a fair schedule, in any system.**  In
the same situation, with any number of threads and any unending schedule
in which every thread keeps being scheduled, from some action on every
thread is at rest, the claims are the steps of the two reductions, and
the memory holds the two normal forms side by side. -/
theorem XMach.union_fair (xs : XSys S) {X Y : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hY : Y.toNet.WF xs.sys.ar) (h : X.toNet.Apart Y.toNet) {n m : Nat}
    (sA : Steps (Step xs.sys) n X.toNet A') (nA : Normal (Step xs.sys) A')
    (sB : Steps (Step xs.sys) m Y.toNet B') (nB : Normal (Step xs.sys) B')
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (X.union Y) nt).trace xs σ i).1.resting = true ∧
      ((XMach.init (X.union Y) nt).trace xs σ i).2 = n + m ∧
      ((XMach.init (X.union Y) nt).trace xs σ i).1.mem.toNet = A'.union B' := by
  obtain ⟨s, hn'⟩ := h.reduce hX hY sA nA sB nB
  have hU : (X.union Y).toNet.WF xs.sys.ar := by
    rw [XNet.union_toNet]
    exact hX.union hY h
  rw [← XNet.union_toNet] at s
  exact XMach.fair_complete (xs := xs) hU hnt s hn' σ hfair

/-! ### Tags, in any system -/

omit [DecidableEq S] in
/-- Putting a tag at the end of every name is a renaming of a well-formed
net. -/
theorem Renaming.tag {ar : S → Nat} {N : Net S} (hN : N.WF ar) (c : Nat) :
    Renaming (fun i => i ++ [c]) N where
  inj := fun _ _ e => List.append_cancel_right e
  fresh := by
    intro a α i l ha hu e
    have e0 : i ++ [c] = l ++ (a ++ [c]) := e
    rw [← List.append_assoc] at e0
    have ei : i = l ++ a := List.append_cancel_right e0
    rw [ei] at hu
    exact hN.fresh l ha hu

/-- A memory with a tag at the end of every name. -/
def XNet.tag (c : Nat) (X : XNet S) : XNet S :=
  ⟨X.agents.map fun e => (e.1 ++ [c], e.2), X.free.map fun p => (p.1 ++ [c], p.2),
    X.wires.map fun e => ((e.1.1 ++ [c], e.1.2), (e.2.1 ++ [c], e.2.2))⟩

omit [DecidableEq S] in
theorem XNet.tag_toNet (c : Nat) (X : XNet S) :
    (X.tag c).toNet = X.toNet.map (fun i => i ++ [c]) := by
  apply Net.ext'
  · intro i γ
    show (i, γ) ∈ X.agents.map (fun e => (e.1 ++ [c], e.2)) ↔
      ∃ i', i = i' ++ [c] ∧ (i', γ) ∈ X.agents
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨i', γ'⟩, h, e⟩
      injection e with e1 e2
      have e2' : γ' = γ := e2
      rw [e2'] at h
      exact ⟨i', e1.symm, h⟩
    · rintro ⟨i', rfl, h⟩
      exact ⟨(i', γ), h, rfl⟩
  · intro p q
    show (p, q) ∈ X.wires.map (fun e => ((e.1.1 ++ [c], e.1.2), (e.2.1 ++ [c], e.2.2))) ↔
      ∃ p' q', p = mapPort (fun i => i ++ [c]) p' ∧ q = mapPort (fun i => i ++ [c]) q' ∧
        (p', q') ∈ X.wires
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨p', q'⟩, h, e⟩
      injection e with e1 e2
      exact ⟨p', q', e1.symm, e2.symm, h⟩
    · rintro ⟨p', q', rfl, rfl, h⟩
      exact ⟨(p', q'), h, rfl⟩
  · intro p
    show p ∈ X.free.map (fun p => (p.1 ++ [c], p.2)) ↔
      ∃ p', p = mapPort (fun i => i ++ [c]) p' ∧ p' ∈ X.free
    rw [List.mem_map]
    constructor
    · rintro ⟨p', h, e⟩
      exact ⟨p', e.symm, h⟩
    · rintro ⟨p', rfl, h⟩
      exact ⟨p', h, rfl⟩

/-- **Two nets side by side under tags come out right, whatever the
threads do, in any system.**  Let two memories hold well-formed nets,
each with a normal form, and let them be put side by side with different
tags at the end of their names.  Then, with any number of threads and any
schedule, a run that ends at rest has made as many claims as the two
reductions have steps, and the memory holds the two normal forms side by
side, each renamed: the names of the start carry the tag, and the names
of the agents made on the way are whatever the renaming says. -/
theorem XMach.tagged_rest (xs : XSys S) {X Y : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hY : Y.toNet.WF xs.sys.ar) {c c' : Nat} (hc : c ≠ c') {n m : Nat}
    (sA : Steps (Step xs.sys) n X.toNet A') (nA : Normal (Step xs.sys) A')
    (sB : Steps (Step xs.sys) m Y.toNet B') (nB : Normal (Step xs.sys) B')
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init ((X.tag c).union (Y.tag c')) nt).trace xs σ i).1.resting = true) :
    ∃ g g', Renaming g A' ∧ Renaming g' B' ∧
      (∀ j, X.toNet.Used j → g j = j ++ [c]) ∧ (∀ j, Y.toNet.Used j → g' j = j ++ [c']) ∧
      ((XMach.init ((X.tag c).union (Y.tag c')) nt).trace xs σ i).2 = n + m ∧
      ((XMach.init ((X.tag c).union (Y.tag c')) nt).trace xs σ i).1.mem.toNet =
        (A'.map g).union (B'.map g') := by
  have rX := Renaming.tag hX c
  have rY := Renaming.tag hY c'
  obtain ⟨g, hg, eg, sg⟩ := Steps.map hX rX sA
  obtain ⟨g', hg', eg', sg'⟩ := Steps.map hY rY sB
  have ng := (hg.normal (Steps.wf hX sA)).1 nA
  have ng' := (hg'.normal (Steps.wf hY sB)).1 nB
  have wX : (X.tag c).toNet.WF xs.sys.ar := by
    rw [XNet.tag_toNet]
    exact rX.wf_map hX
  have wY : (Y.tag c').toNet.WF xs.sys.ar := by
    rw [XNet.tag_toNet]
    exact rY.wf_map hY
  have ap : (X.tag c).toNet.Apart (Y.tag c').toNet := by
    rw [XNet.tag_toNet, XNet.tag_toNet]
    refine Net.Apart.of_tags hc (fun j hj => ?_) (fun j hj => ?_)
    · obtain ⟨j', e, -⟩ := Net.used_map hj
      exact ⟨j', e⟩
    · obtain ⟨j', e, -⟩ := Net.used_map hj
      exact ⟨j', e⟩
  rw [← XNet.tag_toNet] at sg sg'
  obtain ⟨h1, h2⟩ := XMach.union_rest xs wX wY ap sg ng sg' ng' hnt σ hr
  exact ⟨g, g', hg, hg', eg, eg', h1, h2⟩

end Machine

end INet
