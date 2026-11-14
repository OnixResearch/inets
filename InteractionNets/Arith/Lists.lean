import InteractionNets.Arith.AtRest

/-! ### Any number of additions side by side -/

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

namespace Arith

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

variable {j m n : Nat}

local macro "ports_differ" : tactic =>
  `(tactic| first | (intro e; simp at e; done) | (intro e; simp at e; omega))

local macro "under_wires" : tactic =>
  `(tactic| repeat (first | rw [wires_takeAgent] | rw [wires_putAgent] |
      rw [assoc_wires_putLink (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))] | rw [nextSeg_putLink (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))]))

local macro "under_agents" : tactic =>
  `(tactic| repeat (first | rw [agents_putLink] | rw [assoc_takeAgent_ne (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))] |
      rw [assoc_putAgent_ne (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))]))

/-- The lists that `f` gives for the nets of `L`, one after the other. -/
def flatG {α : Type} (f : Nat × XNet Arith → List α) : List (Nat × XNet Arith) → List α
  | [] => []
  | e :: L => f e ++ flatG f L

theorem mem_flatG {α : Type} {f : Nat × XNet Arith → List α} {x : α} :
    ∀ {L : List (Nat × XNet Arith)}, x ∈ flatG f L ↔ ∃ e, e ∈ L ∧ x ∈ f e
  | [] => ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | e :: L => by
    show x ∈ f e ++ flatG f L ↔ _
    rw [List.mem_append, mem_flatG (L := L)]
    constructor
    · rintro (h | ⟨e', he', h⟩)
      · exact ⟨e, List.mem_cons_self, h⟩
      · exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · rintro ⟨e', he', h⟩
      rcases List.mem_cons.1 he' with rfl | he''
      · exact .inl h
      · exact .inr ⟨e', he'', h⟩

theorem flatG_append {α : Type} (f : Nat × XNet Arith → List α) :
    ∀ (L₁ L₂ : List (Nat × XNet Arith)), flatG f (L₁ ++ L₂) = flatG f L₁ ++ flatG f L₂
  | [], _ => rfl
  | e :: L₁, L₂ => by
    show f e ++ flatG f (L₁ ++ L₂) = f e ++ flatG f L₁ ++ flatG f L₂
    rw [flatG_append f L₁ L₂, List.append_assoc]

/-- The agents of nets side by side, each net under its tag. -/
def flatA (L : List (Nat × XNet Arith)) : List (Id × Arith) :=
  flatG (fun e => e.2.agents.map (tagA e.1)) L

/-- Their segments. -/
def flatW (L : List (Nat × XNet Arith)) : List (Port × Port) :=
  flatG (fun e => e.2.wires.map (tagL e.1)) L

/-- Their free ports. -/
def flatF (L : List (Nat × XNet Arith)) : List Port :=
  flatG (fun e => e.2.free.map (tagPort e.1)) L

/-- **Any number of nets side by side**, each with its tag put at the end
of every name: the cells of the first, then those of the second, and so
on, and no segment between two of them. -/
def besides (L : List (Nat × XNet Arith)) : XNet Arith := ⟨flatA L, flatF L, flatW L⟩

theorem filter_flatA_none {c : Nat} : ∀ {L : List (Nat × XNet Arith)},
    (∀ e, e ∈ L → e.1 ≠ c) → (flatA L).filter (fun x => tagged c x.1) = []
  | [], _ => rfl
  | e :: L, h => by
    show (e.2.agents.map (tagA e.1) ++ flatA L).filter (fun x => tagged c x.1) = []
    rw [List.filter_append, filter_tag_none (h e List.mem_cons_self),
      filter_flatA_none (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    rfl

/-- The cells with the tag of one of the nets are the cells of that net. -/
theorem filter_flatA {c : Nat} {X : XNet Arith} : ∀ {L : List (Nat × XNet Arith)},
    (L.map Prod.fst).Nodup → (c, X) ∈ L →
      (flatA L).filter (fun x => tagged c x.1) = X.agents.map (tagA c)
  | [], _, h => by cases h
  | e :: L, hnd, h => by
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
    show (e.2.agents.map (tagA e.1) ++ flatA L).filter (fun x => tagged c x.1) = _
    rw [List.filter_append]
    rcases List.mem_cons.1 h with he | h'
    · have e1 : e.1 = c := (congrArg Prod.fst he).symm
      have e2 : e.2 = X := (congrArg Prod.snd he).symm
      have hno : ∀ e', e' ∈ L → e'.1 ≠ c := fun e' he' hc => hn (by
        rw [e1, ← hc]
        exact List.mem_map_of_mem (f := Prod.fst) he')
      rw [e1, e2, filter_tag_self, filter_flatA_none hno, List.append_nil]
    · have hne : e.1 ≠ c := fun hc => hn (by
        rw [hc]
        exact List.mem_map_of_mem (f := Prod.fst) h')
      rw [filter_tag_none hne, filter_flatA hnd' h', List.nil_append]

theorem filter_flatW_none {c : Nat} : ∀ {L : List (Nat × XNet Arith)},
    (∀ e, e ∈ L → e.1 ≠ c) → (flatW L).filter (fun x => tagged c x.1.1) = []
  | [], _ => rfl
  | e :: L, h => by
    show (e.2.wires.map (tagL e.1) ++ flatW L).filter (fun x => tagged c x.1.1) = []
    rw [List.filter_append, filterW_tag_none (h e List.mem_cons_self),
      filter_flatW_none (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    rfl

theorem filter_flatW {c : Nat} {X : XNet Arith} : ∀ {L : List (Nat × XNet Arith)},
    (L.map Prod.fst).Nodup → (c, X) ∈ L →
      (flatW L).filter (fun x => tagged c x.1.1) = X.wires.map (tagL c)
  | [], _, h => by cases h
  | e :: L, hnd, h => by
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
    show (e.2.wires.map (tagL e.1) ++ flatW L).filter (fun x => tagged c x.1.1) = _
    rw [List.filter_append]
    rcases List.mem_cons.1 h with he | h'
    · have e1 : e.1 = c := (congrArg Prod.fst he).symm
      have e2 : e.2 = X := (congrArg Prod.snd he).symm
      have hno : ∀ e', e' ∈ L → e'.1 ≠ c := fun e' he' hc => hn (by
        rw [e1, ← hc]
        exact List.mem_map_of_mem (f := Prod.fst) he')
      rw [e1, e2, filterW_tag_self, filter_flatW_none hno, List.append_nil]
    · have hne : e.1 ≠ c := fun hc => hn (by
        rw [hc]
        exact List.mem_map_of_mem (f := Prod.fst) h')
      rw [filterW_tag_none hne, filter_flatW hnd' h', List.nil_append]

/-- With tags all different, a tag names one net. -/
theorem tag_unique {c : Nat} {X Y : XNet Arith} : ∀ {L : List (Nat × XNet Arith)},
    (L.map Prod.fst).Nodup → (c, X) ∈ L → (c, Y) ∈ L → X = Y
  | [], _, h, _ => by cases h
  | e :: L, hnd, hX, hY => by
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
    rcases List.mem_cons.1 hX with h1 | h1
    · rcases List.mem_cons.1 hY with h2 | h2
      · exact (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm
      · refine absurd ?_ hn
        have e1 : e.1 = c := (congrArg Prod.fst h1).symm
        rw [e1]
        exact List.mem_map_of_mem (f := Prod.fst) h2
    · rcases List.mem_cons.1 hY with h2 | h2
      · refine absurd ?_ hn
        have e1 : e.1 = c := (congrArg Prod.fst h2).symm
        rw [e1]
        exact List.mem_map_of_mem (f := Prod.fst) h1
      · exact tag_unique hnd' h1 h2

/-- A free port with the tag of one of the nets is a free port of it. -/
theorem mem_flatF_tag {c : Nat} {X : XNet Arith} {L : List (Nat × XNet Arith)}
    (hnd : (L.map Prod.fst).Nodup) (hX : (c, X) ∈ L) (q : Port) :
    tagPort c q ∈ flatF L ↔ q ∈ X.free := by
  constructor
  · intro h
    obtain ⟨e, he, hx⟩ := mem_flatG.1 h
    obtain ⟨q', hq', ee⟩ := List.mem_map.1 hx
    obtain ⟨e1, e2⟩ := tagPort_snoc ee
    have he' : (c, e.2) ∈ L := by
      rw [← e2]
      exact he
    rw [tag_unique hnd hX he', ← e1]
    exact hq'
  · intro h
    exact mem_flatG.2 ⟨(c, X), hX, List.mem_map_of_mem h⟩

/-- The part with a given tag: the net of that tag, or nothing. -/
def partOf : List (Nat × XNet Arith) → Nat → Net Arith
  | [], _ => noNet
  | e :: L, c => if c = e.1 then e.2.toNet else partOf L c

theorem partOf_matching : ∀ {L : List (Nat × XNet Arith)}, (∀ e, e ∈ L → e.2.Ok ar) →
    ∀ c, (partOf L c).Matching ar
  | [], _, _ => noNet_matching
  | e :: L, h, c => by
    show (if c = e.1 then e.2.toNet else partOf L c).Matching ar
    by_cases hc : c = e.1
    · rw [ite_pos' hc]
      exact XNet.ok_iff_matching.1 (h e List.mem_cons_self)
    · rw [ite_neg' hc]
      exact partOf_matching (fun e' he' => h e' (List.mem_cons_of_mem _ he')) c

theorem partOf_mem {c : Nat} {X : XNet Arith} : ∀ {L : List (Nat × XNet Arith)},
    (L.map Prod.fst).Nodup → (c, X) ∈ L → partOf L c = X.toNet
  | [], _, h => by cases h
  | e :: L, hnd, h => by
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
    show (if c = e.1 then e.2.toNet else partOf L c) = X.toNet
    rcases List.mem_cons.1 h with he | h'
    · have e1 : c = e.1 := congrArg Prod.fst he
      have e2 : X = e.2 := congrArg Prod.snd he
      rw [ite_pos' e1, e2]
    · have hne : c ≠ e.1 := fun hc => hn (by
        rw [← hc]
        exact List.mem_map_of_mem (f := Prod.fst) h')
      rw [ite_neg' hne]
      exact partOf_mem hnd' h'

theorem partOf_cases {Q : Net Arith → Prop} {c : Nat} : ∀ {L : List (Nat × XNet Arith)},
    Q (partOf L c) → ¬ Q noNet → ∃ X, (c, X) ∈ L ∧ Q X.toNet
  | [], h, hn => absurd h hn
  | e :: L, h, hn => by
    have h' : Q (if c = e.1 then e.2.toNet else partOf L c) := h
    by_cases hc : c = e.1
    · rw [ite_pos' hc] at h'
      exact ⟨e.2, by
        rw [hc]
        exact List.mem_cons_self, h'⟩
    · rw [ite_neg' hc] at h'
      obtain ⟨X, hX, hQ⟩ := partOf_cases h' hn
      exact ⟨X, List.mem_cons_of_mem _ hX, hQ⟩

/-- Nets side by side under different tags are made of them as parts. -/
theorem parts_besides {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup) :
    Parts (besides L).toNet (partOf L) where
  agent := fun {i γ} h => by
    obtain ⟨e, he, hx⟩ := mem_flatG.1 (show (i, γ) ∈ flatA L from h)
    obtain ⟨⟨j, δ⟩, hj, ee⟩ := List.mem_map.1 hx
    have e' : ((j ++ [e.1], δ) : Id × Arith) = (i, γ) := ee
    injection e' with e1 e2
    subst e1
    subst e2
    refine ⟨e.1, j, rfl, ?_⟩
    rw [partOf_mem hnd (show (e.1, e.2) ∈ L from he)]
    exact hj
  link := fun {p q} h => by
    obtain ⟨e, he, hx⟩ := mem_flatG.1 (show (p, q) ∈ flatW L from h)
    obtain ⟨⟨p', q'⟩, hj, ee⟩ := List.mem_map.1 hx
    have e' : ((tagPort e.1 p', tagPort e.1 q') : Port × Port) = (p, q) := ee
    injection e' with e1 e2
    refine ⟨e.1, p', q', e1.symm, e2.symm, ?_⟩
    rw [partOf_mem hnd (show (e.1, e.2) ∈ L from he)]
    exact hj
  free := fun {p} h => by
    obtain ⟨e, he, hx⟩ := mem_flatG.1 (show p ∈ flatF L from h)
    obtain ⟨p', hj, ee⟩ := List.mem_map.1 hx
    refine ⟨e.1, p', ee.symm, ?_⟩
    rw [partOf_mem hnd (show (e.1, e.2) ∈ L from he)]
    exact hj
  agent' := fun {c i γ} h => by
    obtain ⟨X, hX, hQ⟩ := partOf_cases (Q := fun N => N.agent i γ) h (fun x => x)
    exact mem_flatG.2 ⟨(c, X), hX, List.mem_map.2 ⟨(i, γ), hQ, rfl⟩⟩
  link' := fun {c p q} h => by
    obtain ⟨X, hX, hQ⟩ := partOf_cases (Q := fun N => N.link p q) h (fun x => x)
    exact mem_flatG.2 ⟨(c, X), hX, List.mem_map.2 ⟨(p, q), hQ, rfl⟩⟩
  free' := fun {c p} h => by
    obtain ⟨X, hX, hQ⟩ := partOf_cases (Q := fun N => N.free p) h (fun x => x)
    exact mem_flatG.2 ⟨(c, X), hX, List.mem_map.2 ⟨p, hQ, rfl⟩⟩

/-- **Well-formed compact nets side by side under different tags are a
well-formed net.** -/
theorem besides_wf {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup)
    (hOk : ∀ e, e ∈ L → e.2.Ok ar) : (besides L).toNet.WF ar :=
  ((parts_besides hnd).matching (partOf_matching hOk)).wf

theorem flatA_append (L₁ L₂ : List (Nat × XNet Arith)) :
    flatA (L₁ ++ L₂) = flatA L₁ ++ flatA L₂ := flatG_append _ L₁ L₂

theorem flatA_single (c : Nat) (X : XNet Arith) : flatA [(c, X)] = X.agents.map (tagA c) :=
  List.append_nil _

/-- **A memory that holds nets side by side**: its agents are the cells
of the nets of `L`, in the order of `L`, each net under its tag; the
segments with the tag of a net are the segments of that net; and the
tags are all different. -/
structure Holds (L : List (Nat × XNet Arith)) (M : XNet Arith) : Prop where
  agents : M.agents = flatA L
  wires : ∀ e, e ∈ L → M.wires.filter (fun w => tagged e.1 w.1.1) = e.2.wires.map (tagL e.1)
  tags : (L.map Prod.fst).Nodup

theorem holds_besides {L : List (Nat × XNet Arith)} (hnd : (L.map Prod.fst).Nodup) :
    Holds L (besides L) :=
  ⟨rfl, fun e he => filter_flatW hnd (show (e.1, e.2) ∈ L from he), hnd⟩

/-- Each of the nets is seen in the memory. -/
theorem Holds.looks {L : List (Nat × XNet Arith)} {M : XNet Arith} (h : Holds L M)
    {e : Nat × XNet Arith} (he : e ∈ L) : Looks e.1 e.2 M :=
  ⟨by
    rw [h.agents]
    exact filter_flatA h.tags (show (e.1, e.2) ∈ L from he), h.wires e he⟩

/-- **One thread on the first of the nets of a memory.**  Its run on the
net alone is its run in the memory, claim for claim; the memory it leaves
is one the start reduces to; and with the cells of that net listed last
it holds the other nets and what the run leaves of this one. -/
theorem Holds.run {c : Nat} {X X' : XNet Arith} {L : List (Nat × XNet Arith)} {M : XNet Arith}
    {cl k : Nat} (h : Holds ((c, X) :: L) M) (hM : M.toNet.WF ar)
    (w : Works xsys X ⟨X.agents, .idle⟩ X' ⟨[], .idle⟩ cl k) :
    ∃ M', Steps (Step system) cl M.toNet M'.toNet ∧ Holds (L ++ [(c, X')]) M' ∧
      M'.free = M.free := by
  obtain ⟨hn, hnd⟩ := List.nodup_cons.1 h.tags
  have hne : ∀ e, e ∈ L → c ≠ e.1 := fun e he hc => hn (by
    show c ∈ L.map Prod.fst
    rw [hc]
    exact List.mem_map_of_mem (f := Prod.fst) he)
  have hIn : Inside c (flatA L) X M :=
    ⟨h.looks (e := (c, X)) List.mem_cons_self, h.agents, fun x hx => by
      obtain ⟨e, he, hxe⟩ := mem_flatG.1 hx
      exact mem_tag_other (fun hc => hne e he hc.symm) hxe⟩
  obtain ⟨M1, r1, W1, hIn1, mv1, hr1⟩ := Inside.works w (flatA L) hIn
  have er1 : r1 = flatA L := by
    rcases hr1 with e | e <;> exact e
  subst er1
  have W1' : Works xsys M ⟨M.agents, .idle⟩ M1 ⟨flatA L, .idle⟩ cl k := by
    rw [h.agents]
    exact W1
  have s1 := works_steps hM W1'
  -- the cells of the net moved to the end of the list
  have eN : (⟨flatA (L ++ [(c, X')]), M1.free, M1.wires⟩ : XNet Arith).toNet = M1.toNet := by
    apply Net.ext'
    · intro i γ
      show (i, γ) ∈ flatA (L ++ [(c, X')]) ↔ (i, γ) ∈ M1.agents
      rw [hIn1.agents, flatA_append, flatA_single, List.mem_append, List.mem_append]
      exact Or.comm
    · exact fun _ _ => Iff.rfl
    · exact fun _ => Iff.rfl
  have fM : M1.free = M.free := works_free W1'
  refine ⟨⟨flatA (L ++ [(c, X')]), M1.free, M1.wires⟩, ?_, ⟨rfl, fun e he => ?_, ?_⟩, fM⟩
  · rw [eN]
    exact s1
  · rcases List.mem_append.1 he with h1 | h1
    · exact (mv1.other e.1 e.2 (hne e h1)
        (h.looks (List.mem_cons_of_mem _ h1))).wires
    · rw [List.mem_singleton.1 h1]
      exact hIn1.looks.wires
  · rw [List.map_append]
    refine List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb e => ?_⟩
    rw [List.mem_singleton.1 hb] at e
    exact hn (e ▸ ha)

/-- A net with the run of one thread on it: its tag, the net, the memory
the run leaves, and the number of its claims. -/
structure Part where
  tag : Nat
  net : XNet Arith
  left : XNet Arith
  claims : Nat

/-- One thread alone brings the net to rest at what is left. -/
def Part.Runs (p : Part) : Prop :=
  ∃ k, Works xsys p.net ⟨p.net.agents, .idle⟩ p.left ⟨[], .idle⟩ p.claims k

/-- A new pass over what is left only reads. -/
def Part.Reads (p : Part) : Prop :=
  ∃ k, Stays xsys p.left ⟨p.left.agents, .idle⟩ ⟨[], .idle⟩ k

/-- The nets of a list of parts, with their tags. -/
def partNets (P : List Part) : List (Nat × XNet Arith) := P.map fun p => (p.tag, p.net)

/-- What the runs leave, with the tags. -/
def partLefts (P : List Part) : List (Nat × XNet Arith) := P.map fun p => (p.tag, p.left)

/-- The claims of all the runs. -/
def claimsOf : List Part → Nat
  | [] => 0
  | p :: P => p.claims + claimsOf P

/-- **One thread on each net in turn.**  From a memory that holds the
nets of the parts `P` and then the nets `D`, the start reduces, in as
many steps as the runs on the parts have claims, to a memory that holds
the nets `D` and then what the runs leave. -/
theorem phases : ∀ (P : List Part) (D : List (Nat × XNet Arith)) (M : XNet Arith),
    (∀ p, p ∈ P → p.Runs) → Holds (partNets P ++ D) M → M.toNet.WF ar →
      ∃ M', Steps (Step system) (claimsOf P) M.toNet M'.toNet ∧
        Holds (D ++ partLefts P) M' ∧ M'.free = M.free
  | [], D, M, _, h, _ => by
    refine ⟨M, .refl _, ?_, rfl⟩
    show Holds (D ++ []) M
    rw [List.append_nil]
    exact h
  | p :: P, D, M, hR, h, hM => by
    obtain ⟨k, w⟩ := hR p List.mem_cons_self
    have h' : Holds ((p.tag, p.net) :: (partNets P ++ D)) M := h
    obtain ⟨M1, s1, h1, f1⟩ := h'.run hM w
    rw [List.append_assoc] at h1
    obtain ⟨M2, s2, h2, f2⟩ := phases P (D ++ [(p.tag, p.left)]) M1
      (fun q hq => hR q (List.mem_cons_of_mem _ hq)) h1 (Steps.wf hM s1)
    rw [List.append_assoc] at h2
    exact ⟨M2, s1.trans s2, h2, f2.trans f1⟩

/-- **A pass over nets that are all at rest only reads.** -/
theorem pass_all {M : XNet Arith} : ∀ (F : List (Nat × XNet Arith)) (r : List (Id × Arith)),
    (∀ e, e ∈ F → Looks e.1 e.2 M ∧
      ∃ k, Stays xsys e.2 ⟨e.2.agents, .idle⟩ ⟨[], .idle⟩ k) →
    ∃ K, Stays xsys M ⟨flatA F ++ r, .idle⟩ ⟨r, .idle⟩ K
  | [], r, _ => ⟨0, .refl _⟩
  | e :: F, r, h => by
    obtain ⟨hl, k, p⟩ := h e List.mem_cons_self
    obtain ⟨k1, -, -, sY, -⟩ :=
      hl.pass p rfl trivial e.2.agents [] (flatA F ++ r) (List.append_nil _).symm
    obtain ⟨K, sK⟩ := pass_all F r (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    refine ⟨k1 + K, ?_⟩
    have s := sY.trans sK
    rw [← List.append_assoc] at s
    exact s

/-- **Any number of nets side by side reduce as each does alone.**  Let
one thread alone bring each net to rest, and let a new pass over what it
leaves only read.  Then the nets side by side, under different tags,
reduce, in as many steps as the runs have claims, to a normal form that
holds under each tag what the run on that net leaves. -/
theorem besides_normal (P : List Part) (hT : ((partNets P).map Prod.fst).Nodup)
    (hY : (besides (partNets P)).toNet.WF ar)
    (hR : ∀ p, p ∈ P → p.Runs) (hS : ∀ p, p ∈ P → p.Reads) :
    ∃ Z : XNet Arith,
      Steps (Step system) (claimsOf P) (besides (partNets P)).toNet Z.toNet ∧
        Normal (Step system) Z.toNet ∧ ∀ p, p ∈ P → Within p.tag p.left Z := by
  have h0 : Holds (partNets P ++ []) (besides (partNets P)) := by
    rw [List.append_nil]
    exact holds_besides hT
  obtain ⟨M, s, h, f⟩ := phases P [] _ hR h0 hY
  have h' : Holds (partLefts P) M := h
  -- the last pass
  obtain ⟨K, sK⟩ := pass_all (M := M) (partLefts P) [] (fun e he => by
    obtain ⟨p, hp, ep⟩ := List.mem_map.1 he
    refine ⟨h'.looks he, ?_⟩
    rw [← ep]
    exact hS p hp)
  have W : Works xsys M ⟨M.agents, .idle⟩ M ⟨[], .idle⟩ 0 K := by
    have q := sK.works
    rw [List.append_nil, ← h'.agents] at q
    exact q
  have n := works_normal (Steps.wf hY s) W
  refine ⟨M, s, n, fun p hp => ?_⟩
  obtain ⟨k, w⟩ := hR p hp
  have hm : (p.tag, p.left) ∈ partLefts P := List.mem_map.2 ⟨p, hp, rfl⟩
  have hmn : (p.tag, p.net) ∈ partNets P := List.mem_map.2 ⟨p, hp, rfl⟩
  refine (h'.looks hm).within rfl (fun _ => Iff.rfl) (fun q => ?_)
  rw [f, works_free w]
  exact mem_flatF_tag hT hmn q

/-- A list of additions with their places as tags, from the tag `t` on. -/
def sumsFrom : Nat → List (Nat × Nat) → List (Nat × XNet Arith)
  | _, [] => []
  | t, e :: l => (t, sum e.1 e.2) :: sumsFrom (t + 1) l

/-- **Any number of additions side by side**: for the `i`-th pair
`(m, n)` of the list, the net for `m + n` with its names tagged `i`. -/
def sums (l : List (Nat × Nat)) : XNet Arith := besides (sumsFrom 0 l)

/-- The interactions of a list of additions: `m + 1` for each. -/
def claimsSum : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => e.1 + 1 + claimsSum l

theorem sumsFrom_tags : ∀ (l : List (Nat × Nat)) (t : Nat),
    (∀ c, c ∈ (sumsFrom t l).map Prod.fst → t ≤ c) ∧ ((sumsFrom t l).map Prod.fst).Nodup
  | [], _ => ⟨fun _ hc => absurd hc List.not_mem_nil, List.nodup_nil⟩
  | e :: l, t => by
    obtain ⟨h1, h2⟩ := sumsFrom_tags l (t + 1)
    refine ⟨fun c hc => ?_, List.nodup_cons.2 ⟨fun hm => ?_, h2⟩⟩
    · rcases List.mem_cons.1 hc with rfl | hc'
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (h1 c hc')
    · exact Nat.not_succ_le_self t (h1 t hm)

theorem sumsFrom_ok : ∀ (l : List (Nat × Nat)) (t : Nat), ∀ e, e ∈ sumsFrom t l → e.2.Ok ar
  | [], _, _, he => absurd he List.not_mem_nil
  | x :: l, t, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact sum_ok x.1 x.2
    · exact sumsFrom_ok l (t + 1) e he'

/-- Any number of additions side by side are a well-formed net. -/
theorem sums_wf (l : List (Nat × Nat)) : (sums l).toNet.WF ar :=
  besides_wf (sumsFrom_tags l 0).2 (sumsFrom_ok l 0)

/-- The run of one thread on each addition of a list. -/
theorem sum_parts : ∀ (l : List (Nat × Nat)) (t : Nat), ∃ P : List Part,
    partNets P = sumsFrom t l ∧ claimsOf P = claimsSum l ∧
      (∀ p, p ∈ P → p.Runs ∧ p.Reads) ∧
      ∀ i m n, l[i]? = some (m, n) → ∃ p, p ∈ P ∧ p.tag = t + i ∧ p.net = sum m n
  | [], _ => ⟨[], rfl, rfl, fun _ hp => absurd hp List.not_mem_nil, fun i m n h => by
      rw [List.getElem?_nil] at h
      cases h⟩
  | (m₀, n₀) :: l, t => by
    obtain ⟨Xf, k, kp, w, st⟩ := sum_solo_pass m₀ n₀
    obtain ⟨P, e1, e2, hR, hI⟩ := sum_parts l (t + 1)
    refine ⟨⟨t, sum m₀ n₀, Xf, m₀ + 1⟩ :: P, ?_, ?_, ?_, ?_⟩
    · show (t, sum m₀ n₀) :: partNets P = (t, sum m₀ n₀) :: sumsFrom (t + 1) l
      rw [e1]
    · show m₀ + 1 + claimsOf P = m₀ + 1 + claimsSum l
      rw [e2]
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact ⟨Exists.intro k w, Exists.intro kp st⟩
      · exact hR p hp'
    · intro i m n h
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at h
        have e : (m₀, n₀) = (m, n) := Option.some.inj h
        injection e with em en
        subst em
        subst en
        exact ⟨_, List.mem_cons_self, rfl, rfl⟩
      | succ i =>
        rw [List.getElem?_cons_succ] at h
        obtain ⟨p, hp, ht, hn⟩ := hI i m n h
        exact ⟨p, List.mem_cons_of_mem _ hp, by
          rw [ht]
          omega, hn⟩

/-- **Any number of additions side by side, as a net.**  The net reduces,
in `m + 1` steps for each addition `m + n`, to a normal form that has
the numeral `m + n` of the `i`-th addition on its `i`-th free port. -/
theorem sums_normal (l : List (Nat × Nat)) : ∃ N' : Net Arith,
    Steps (Step system) (claimsSum l) (sums l).toNet N' ∧ Normal (Step system) N' ∧
      ∀ i m n, l[i]? = some (m, n) → IsNum N' ([0, i], 0) (m + n) := by
  obtain ⟨P, e1, e2, hR, hI⟩ := sum_parts l 0
  have hT : ((partNets P).map Prod.fst).Nodup := by
    rw [e1]
    exact (sumsFrom_tags l 0).2
  have hY : (besides (partNets P)).toNet.WF ar := by
    rw [e1]
    exact sums_wf l
  obtain ⟨Z, s, hn, hW⟩ := besides_normal P hT hY (fun p hp => (hR p hp).1)
    (fun p hp => (hR p hp).2)
  rw [e1, e2] at s
  refine ⟨Z.toNet, s, hn, fun i m n h => ?_⟩
  obtain ⟨p, hp, ht, hnet⟩ := hI i m n h
  obtain ⟨k, w⟩ := (hR p hp).1
  rw [hnet] at w
  have num := (hW p hp).isNum (works_rest_num w)
  rw [ht, Nat.zero_add] at num
  exact num

/-- **Any number of additions side by side come out right, whatever the
threads do.**  With any number of threads and any schedule, a run that
ends at rest has made `m + 1` claims for each addition `m + n`, and the
memory has the numeral `m + n` of the `j`-th addition on the `j`-th free
port. -/
theorem sums_rest (l : List (Nat × Nat)) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sums l) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (sums l) nt).trace xsys σ i).2 = claimsSum l ∧
      ∀ j m n, l[j]? = some (m, n) →
        IsNum ((XMach.init (sums l) nt).trace xsys σ i).1.mem.toNet ([0, j], 0) (m + n) := by
  obtain ⟨N', hs, hn', hA⟩ := sums_normal l
  have hX := sums_wf l
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (sums l) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (sums l) nt).trace xsys σ i).1.mem.toNet := e
  rw [← e']
  exact ⟨ek.symm, hA⟩

/-- **Any number of additions side by side under a fair schedule.**  With
any number of threads and any unending schedule in which every thread
keeps being scheduled, from some action on every thread is at rest, the
claims are `m + 1` for each addition, and the memory has every sum on
its free port. -/
theorem sums_fair (l : List (Nat × Nat)) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (sums l) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (sums l) nt).trace xsys σ i).2 = claimsSum l ∧
      ∀ j m n, l[j]? = some (m, n) →
        IsNum ((XMach.init (sums l) nt).trace xsys σ i).1.mem.toNet ([0, j], 0) (m + n) := by
  obtain ⟨N', hs, hn', hA⟩ := sums_normal l
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) (sums_wf l) hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, hc, e⟩ := h i hi
  rw [e]
  exact ⟨hr, hc, hA⟩

/-- `0 + 7`, `3 + 0` and `2 + 2` side by side, with any number of threads
and any schedule: a run that ends at rest has made eight claims, and the
memory has `7`, `3` and `4` on the three free ports. -/
example {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).2 = 8 ∧
      IsNum ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.mem.toNet
        ([0, 0], 0) 7 ∧
      IsNum ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.mem.toNet
        ([0, 1], 0) 3 ∧
      IsNum ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.mem.toNet
        ([0, 2], 0) 4 := by
  obtain ⟨hc, h⟩ := sums_rest [(0, 7), (3, 0), (2, 2)] hnt σ hr
  exact ⟨hc, h 0 0 7 rfl, h 1 3 0 rfl, h 2 2 2 rfl⟩

end Arith

end INet
