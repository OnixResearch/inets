import InteractionNets.Confluence

/-! # Wiring free ports together

A net is plugged into another, or into itself, by new segments between
free ports: the ports stop being free and become points of longer wires
(`Net.plug`).  Reduction does not see the difference: a step of the net
is a step of the plugged net (`Step.plug`), for any system and any new
segments.  The plugged net is well formed when the new segments are a
finite matching of free ports (`Net.WF.plug`), and two wires that ended
at ports now joined are one wire (`Net.Conn.plug`).
-/

namespace INet

variable {S : Type}

/-- **Wiring free ports together.**  `U.plug J`: the net `U` with the
segments `J` added; a port that one of them touches is no longer free. -/
def Net.plug (U : Net S) (J : Port → Port → Prop) : Net S where
  agent := U.agent
  link p q := U.link p q ∨ J p q
  free p := U.free p ∧ ¬ ∃ q, J p q

variable {U V : Net S} {J : Port → Port → Prop}

/-- An end of the plugged net is an end of the net. -/
theorem Net.plug_end {ar : S → Nat} {p : Port} (h : (U.plug J).End ar p) : U.End ar p := by
  rcases h with h | h
  · obtain ⟨h1, -⟩ := h
    exact .inl h1
  · exact .inr h

/-- An end that no new segment touches is an end of the plugged net. -/
theorem Net.end_plug {ar : S → Nat} {p : Port} (h : U.End ar p) (hp : ¬ ∃ q, J p q) :
    (U.plug J).End ar p := by
  rcases h with h | h
  · exact .inl ⟨h, hp⟩
  · exact .inr h

theorem Net.fire_plug (U : Net S) (J : Port → Port → Prop) (a b : Id) (R : Rhs S) :
    (U.plug J).fire a b R = (U.fire a b R).plug J := by
  apply Net.ext'
  · intro i γ
    exact Iff.rfl
  · intro p q
    show ((U.link p q ∨ J p q) ∨ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y) ↔
      ((U.link p q ∨ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y) ∨ J p q)
    exact or_right_comm
  · intro p
    exact Iff.rfl

/-- **A step of a net is a step of the net with free ports wired
together.**  The active pair is still one: its wire runs through no end
of the net, and the plugged net has no new ends.  Firing it changes the
agents and adds the same segments. -/
theorem Step.plug {sys : System S} (J : Port → Port → Prop) (h : Step sys U V) :
    Step sys (U.plug J) (V.plug J) := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  obtain ⟨v, x, w⟩ := r.conn
  exact ⟨a, b, α, β, R, ⟨r.ha, r.hb, r.ne,
    ⟨v, x, w.mono (fun h => .inl h) (fun _ hq hq' => hq (Net.plug_end hq'))⟩, r.rule⟩,
    (Net.fire_plug U J a b R).symm⟩

/-- **A reduction of a net is a reduction of the net with free ports
wired together**, step for step. -/
theorem Steps.plug {sys : System S} (J : Port → Port → Prop) {n : Nat}
    (h : Steps (Step sys) n U V) : Steps (Step sys) n (U.plug J) (V.plug J) := by
  induction h with
  | refl => exact .refl _
  | head h _ ih => exact .head (h.plug J) ih

/-- When the new segments touch free ports only, the ends of the plugged
net are the ends that no new segment touches. -/
theorem Net.plug_end_iff {ar : S → Nat} (hU : U.WF ar) (hfree : ∀ p q, J p q → U.free p)
    (p : Port) : (U.plug J).End ar p ↔ U.End ar p ∧ ¬ ∃ q, J p q := by
  constructor
  · intro h
    refine ⟨Net.plug_end h, ?_⟩
    rcases h with ⟨-, h2⟩ | ⟨γ, hγ, -⟩
    · exact h2
    · rintro ⟨q, hq⟩
      exact hU.free_agent (i := p.1) (k := p.2) (hfree _ _ hq) hγ
  · rintro ⟨h, hp⟩
    exact Net.end_plug h hp

/-- No new segment touches a port of an agent. -/
theorem Net.WF.unplugged {ar : S → Nat} (hU : U.WF ar) (hfree : ∀ p q, J p q → U.free p)
    {i : Id} {γ : S} (hi : U.agent i γ) (k : Nat) : ¬ ∃ r, J (i, k) r := by
  rintro ⟨r, hr⟩
  exact hU.free_agent (hfree _ _ hr) hi

/-- **A well-formed net with free ports wired together is well formed**,
when the new segments are finitely many, join free ports, and no port is
on two of them. -/
theorem Net.WF.plug {ar : S → Nat} (hU : U.WF ar)
    (hs : ∀ {p q}, J p q → J q p) (hi : ∀ {p}, ¬ J p p)
    (hf : ∀ {p q r}, J p q → J p r → q = r) (hfree : ∀ p q, J p q → U.free p)
    (l : List Port) (hl : ∀ {p q}, J p q → p ∈ l) : (U.plug J).WF ar := by
  have hT : ∀ {p q}, J p q → U.End ar p := fun h => .inl (hfree _ _ h)
  have hE := Net.plug_end_iff hU (J := J) hfree
  have W : Wiring (U.plug J).link ((U.plug J).End ar) :=
    (hU.wiring.add (M := J) hs hf hT).congr (fun _ _ => Iff.rfl) (fun p => (hE p).symm)
  have D : Wired (U.plug J).link ((U.plug J).End ar) :=
    ((hU.wired.joint.add_matching hU.wiring hU.wiring l (M := J) hs hi hf hT hl).left).congr
      (fun _ _ => Iff.rfl) (fun p => (hE p).symm)
  refine ⟨fun h h' => hU.agent_fun h h', W.symm, ?_, W.term, fun ht => D _ ht, W.deg, ?_, ?_⟩
  · intro p h
    rcases h with h | h
    · exact hU.irrefl h
    · exact hi h
  · intro i k α h
    obtain ⟨h1, -⟩ := h
    exact hU.free_agent h1
  · intro a α l' ha hu
    refine hU.fresh l' ha ?_
    rcases hu with hu | ⟨k, q, hu | hu⟩ | ⟨k, hu⟩
    · exact .inl hu
    · exact .inr (.inl ⟨k, q, hu⟩)
    · exact .inr (.inr ⟨k, hfree _ _ hu⟩)
    · obtain ⟨h1, -⟩ := hu
      exact .inr (.inr ⟨k, h1⟩)

/-- Ends joined by a wire, neither on a new segment, are joined by that
wire in the plugged net. -/
theorem Net.Paired.plug {ar : S → Nat} {p q : Port} (h : U.Paired ar p q)
    (hp : ¬ ∃ r, J p r) (hq : ¬ ∃ r, J q r) : (U.plug J).Paired ar p q := by
  obtain ⟨e1, e2, v, x, w⟩ := h
  exact ⟨Net.end_plug e1 hp, Net.end_plug e2 hq, v, x,
    w.mono (fun h => .inl h) (fun _ hq hq' => hq (Net.plug_end hq'))⟩

/-- **Two wires that end at ports joined by a new segment are one
wire.** -/
theorem Net.Conn.plug {ar : S → Nat} (hU : U.WF ar) (hfree : ∀ p q, J p q → U.free p)
    {x p q y : Port} (hpq : J p q) (hqp : J q p) (hx : x ≠ q)
    (c₁ : U.Conn ar x p) (c₂ : U.Conn ar q y) : (U.plug J).Conn ar x y := by
  obtain ⟨z, u, w⟩ := c₁
  obtain ⟨z₂, u₂, w₂⟩ := c₂
  have hE := Net.plug_end_iff hU (J := J) hfree
  exact Walk.splice hU.wiring (.inl (hfree _ _ hpq)) (.inl (hfree _ _ hqp)) (fun h => .inl h)
    (fun h => Net.plug_end h) (fun h => ((hE p).1 h).2 ⟨q, hpq⟩)
    (fun h => ((hE q).1 h).2 ⟨p, hqp⟩) (.inr hpq) hx w w₂

/-! ### One new segment -/

/-- The two directions of one segment between `x` and `y`. -/
def joinRel (x y : Port) : Port → Port → Prop :=
  fun p q => (p = x ∧ q = y) ∨ (p = y ∧ q = x)

theorem joinRel_left (x y : Port) : joinRel x y x y := .inl ⟨rfl, rfl⟩

theorem joinRel_right (x y : Port) : joinRel x y y x := .inr ⟨rfl, rfl⟩

/-- A port is on the segment only if it is one of its two ends. -/
theorem joinRel_ne {x y p : Port} (h1 : p ≠ x) (h2 : p ≠ y) : ¬ ∃ r, joinRel x y p r := by
  rintro ⟨r, ⟨e, -⟩ | ⟨e, -⟩⟩
  · exact h1 e
  · exact h2 e

/-- **A well-formed net with two of its free ports wired together is well
formed.** -/
theorem Net.WF.plug_two {ar : S → Nat} (hU : U.WF ar) {x y : Port} (hx : U.free x)
    (hy : U.free y) (hxy : x ≠ y) : (U.plug (joinRel x y)).WF ar := by
  refine hU.plug ?_ ?_ ?_ ?_ [x, y] ?_
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .inr ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · rintro p (⟨e1, e2⟩ | ⟨e1, e2⟩)
    · exact hxy (e1.symm.trans e2)
    · exact hxy (e2.symm.trans e1)
  · rintro p q r (⟨e1, e2⟩ | ⟨e1, e2⟩) (⟨e3, e4⟩ | ⟨e3, e4⟩)
    · exact e2.trans e4.symm
    · exact absurd (e1.symm.trans e3) hxy
    · exact absurd (e3.symm.trans e1) hxy
    · exact e2.trans e4.symm
  · rintro p q (⟨e, -⟩ | ⟨e, -⟩)
    · rw [e]
      exact hx
    · rw [e]
      exact hy
  · rintro p q (⟨e, -⟩ | ⟨e, -⟩)
    · rw [e]
      exact List.mem_cons_self
    · rw [e]
      exact List.mem_cons_of_mem _ List.mem_cons_self

end INet
