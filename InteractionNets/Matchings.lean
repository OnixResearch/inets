import InteractionNets.Symmetry

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### Nets without history, as matchings

The valid inputs of the reducer are exactly the nets whose segments form a
perfect matching of their ends.  Matchings can be built by hand: inserting
an agent on a segment of a matching gives a matching. -/

/-- The segments of the net form a perfect matching of its ends. -/
structure Net.Matching (ar : S → Nat) (N : Net S) : Prop where
  agent_fun : ∀ {i α β}, N.agent i α → N.agent i β → α = β
  symm : ∀ {p q}, N.link p q → N.link q p
  irrefl : ∀ {p}, ¬ N.link p p
  functional : ∀ {p q q'}, N.link p q → N.link p q' → q = q'
  ends : ∀ {p q}, N.link p q → N.End ar p
  wired : ∀ {p}, N.End ar p → ∃ q, N.link p q
  free_agent : ∀ {i k α}, N.free (i, k) → ¬ N.agent i α
  fresh : ∀ {a α} (l : List Nat), N.agent a α → N.Used (l ++ a) → l = []

namespace Net.Matching

variable {ar : S → Nat} {N : Net S}

/-- In a matching, the wires are the segments. -/
theorem paired_iff (h : N.Matching ar) {p q : Port} : N.Paired ar p q ↔ N.link p q := by
  constructor
  · rintro ⟨-, -, v, x, w⟩
    cases w with
    | single hl => exact hl
    | cons hl hv _ _ => exact absurd (h.ends (h.symm hl)) hv
  · intro hl
    exact ⟨h.ends hl, h.ends (h.symm hl), q, p, .single hl⟩

theorem wf (h : N.Matching ar) : N.WF ar where
  agent_fun := h.agent_fun
  symm := h.symm
  irrefl := h.irrefl
  end_unique := fun _ h₁ h₂ => h.functional h₁ h₂
  end_conn := by
    intro p hp
    obtain ⟨q, hl⟩ := h.wired hp
    refine ⟨q, h.ends (h.symm hl), ?_, q, p, .single hl⟩
    rintro rfl
    exact h.irrefl hl
  deg := fun h₁ h₂ _ => .inl (h.functional h₁ h₂)
  free_agent := h.free_agent
  fresh := h.fresh

theorem compact (h : N.Matching ar) : N.compact ar = N :=
  Net.ext' (fun _ _ => Iff.rfl) (fun _ _ => h.paired_iff) (fun _ => Iff.rfl)

end Net.Matching

/-- A well-formed net without history is a matching. -/
theorem Net.WF.matching {ar : S → Nat} {N : Net S} (hN : N.WF ar) (hc : N.compact ar = N) :
    N.Matching ar := by
  have hl : ∀ {p q : Port}, N.link p q → N.Paired ar p q := by
    intro p q h
    have e : (N.compact ar).link p q := by
      rw [hc]
      exact h
    exact e
  exact ⟨hN.agent_fun, hN.symm, hN.irrefl, fun h₁ h₂ => hN.end_unique (hl h₁).1 h₁ h₂,
    fun h => (hl h).1, hN.end_wired, hN.free_agent, hN.fresh⟩

/-- **The valid inputs of the reducer are the matchings.** -/
theorem XNet.ok_iff_matching {ar : S → Nat} {X : XNet S} : X.Ok ar ↔ X.toNet.Matching ar :=
  ⟨fun h => h.1.matching h.2, fun h => ⟨h.wf, h.compact⟩⟩

/-- Put a new agent `u`, with symbol `γ` and one auxiliary port, on the
segment between `p` and `q`.  Its principal port faces `p`. -/
def Net.insert1 (N : Net S) (u : Id) (γ : S) (p q : Port) : Net S where
  agent i α := N.agent i α ∨ (i = u ∧ α = γ)
  link x y := (N.link x y ∧ x ≠ p ∧ x ≠ q) ∨ (x = p ∧ y = (u, 0)) ∨ (x = (u, 0) ∧ y = p) ∨
    (x = (u, 1) ∧ y = q) ∨ (x = q ∧ y = (u, 1))
  free := N.free

theorem Net.used_insert1 {N : Net S} {u : Id} {γ : S} {p q : Port} (hpq : N.link p q)
    (hs : ∀ {x y}, N.link x y → N.link y x) {i : Id} (h : (N.insert1 u γ p q).Used i) :
    N.Used i ∨ i = u := by
  rcases h with ⟨α, hα | ⟨e, -⟩⟩ | ⟨k, y, ⟨hl, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩⟩ | ⟨k, hf⟩
  · exact .inl (.inl ⟨α, hα⟩)
  · exact .inr e
  · exact .inl (Net.used_link hl)
  · have e' : i = p.1 := congrArg Prod.fst e
    exact .inl (e' ▸ Net.used_link hpq)
  · exact .inr (congrArg Prod.fst e)
  · exact .inr (congrArg Prod.fst e)
  · have e' : i = q.1 := congrArg Prod.fst e
    exact .inl (e' ▸ Net.used_link (hs hpq))
  · exact .inl (.inr (.inr ⟨k, hf⟩))

/-- **Inserting an agent on a segment of a matching gives a matching**, as
long as the name of the new agent is fresh. -/
theorem Net.Matching.insert1 {ar : S → Nat} {N : Net S} (h : N.Matching ar) {u : Id} {γ : S}
    {p q : Port} (hγ : ar γ = 1) (hpq : N.link p q) (hu : ∀ l, ¬ N.Used (l ++ u))
    (hu' : ∀ l a α, N.agent a α → u ≠ l ++ a) : (N.insert1 u γ p q).Matching ar := by
  have hu0 : ¬ N.Used u := hu []
  have hold : ∀ {x y : Port}, N.link x y → ∀ k, x ≠ (u, k) := by
    intro x y hl k e
    have hx := Net.used_link hl
    rw [e] at hx
    exact hu0 hx
  have hpu : ∀ k, p ≠ (u, k) := hold hpq
  have hqu : ∀ k, q ≠ (u, k) := hold (h.symm hpq)
  have hne : p ≠ q := by
    rintro rfl
    exact h.irrefl hpq
  have hend : ∀ {x : Port}, N.End ar x → (N.insert1 u γ p q).End ar x := by
    rintro x (hf | ⟨α, hα, hk⟩)
    · exact .inl hf
    · exact .inr ⟨α, .inl hα, hk⟩
  have hE0 : (N.insert1 u γ p q).End ar (u, 0) := .inr ⟨γ, .inr ⟨rfl, rfl⟩, Nat.zero_le _⟩
  have hE1 : (N.insert1 u γ p q).End ar (u, 1) := by
    refine .inr ⟨γ, .inr ⟨rfl, rfl⟩, ?_⟩
    show 1 ≤ ar γ
    omega
  have hwired : ∀ {x : Port}, N.End ar x → ∃ y, (N.insert1 u γ p q).link x y := by
    intro x hx
    obtain ⟨y, hl⟩ := h.wired hx
    by_cases hxp : x = p
    · exact ⟨(u, 0), .inr (.inl ⟨hxp, rfl⟩)⟩
    by_cases hxq : x = q
    · exact ⟨(u, 1), .inr (.inr (.inr (.inr ⟨hxq, rfl⟩)))⟩
    exact ⟨y, .inl ⟨hl, hxp, hxq⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i α β (h₁ | ⟨e₁, e₁'⟩) (h₂ | ⟨e₂, e₂'⟩)
    · exact h.agent_fun h₁ h₂
    · exact absurd (.inl ⟨α, e₂ ▸ h₁⟩) hu0
    · exact absurd (.inl ⟨β, e₁ ▸ h₂⟩) hu0
    · rw [e₁', e₂']
  · rintro x y (⟨hl, hxp, hxq⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩)
    · refine .inl ⟨h.symm hl, fun e => ?_, fun e => ?_⟩
      · exact hxq (h.functional (h.symm (e ▸ hl)) hpq)
      · exact hxp (h.functional (h.symm (e ▸ hl)) (h.symm hpq))
    · exact .inr (.inr (.inl ⟨e₂, e₁⟩))
    · exact .inr (.inl ⟨e₂, e₁⟩)
    · exact .inr (.inr (.inr (.inr ⟨e₂, e₁⟩)))
    · exact .inr (.inr (.inr (.inl ⟨e₂, e₁⟩)))
  · rintro x (⟨hl, -, -⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩)
    · exact h.irrefl hl
    · exact hpu 0 (e₁.symm.trans e₂)
    · exact hpu 0 (e₂.symm.trans e₁)
    · exact hqu 1 (e₂.symm.trans e₁)
    · exact hqu 1 (e₁.symm.trans e₂)
  · rintro x y y' h₁ h₂
    rcases h₁ with ⟨l₁, a₁, b₁⟩ | ⟨e₁, f₁⟩ | ⟨e₁, f₁⟩ | ⟨e₁, f₁⟩ | ⟨e₁, f₁⟩ <;>
      rcases h₂ with ⟨l₂, a₂, b₂⟩ | ⟨e₂, f₂⟩ | ⟨e₂, f₂⟩ | ⟨e₂, f₂⟩ | ⟨e₂, f₂⟩ <;>
      first
        | exact h.functional l₁ l₂
        | exact f₁.trans f₂.symm
        | exact absurd e₂ a₁
        | exact absurd e₂ b₁
        | exact absurd e₁ a₂
        | exact absurd e₁ b₂
        | exact absurd e₂ (hold l₁ _)
        | exact absurd e₁ (hold l₂ _)
        | exact absurd (e₁.symm.trans e₂) hne
        | exact absurd (e₂.symm.trans e₁) hne
        | exact absurd (e₁.symm.trans e₂) (hpu _)
        | exact absurd (e₂.symm.trans e₁) (hpu _)
        | exact absurd (e₁.symm.trans e₂) (hqu _)
        | exact absurd (e₂.symm.trans e₁) (hqu _)
        | exact absurd (e₁.symm.trans e₂) (port_ne_snd (by decide))
        | exact absurd (e₂.symm.trans e₁) (port_ne_snd (by decide))
  · rintro x y (⟨hl, -, -⟩ | ⟨e₁, -⟩ | ⟨e₁, -⟩ | ⟨e₁, -⟩ | ⟨e₁, -⟩)
    · exact hend (h.ends hl)
    · rw [e₁]
      exact hend (h.ends hpq)
    · rw [e₁]
      exact hE0
    · rw [e₁]
      exact hE1
    · rw [e₁]
      exact hend (h.ends (h.symm hpq))
  · rintro ⟨i, k⟩ (hf | ⟨α, hα | ⟨e₁, e₂⟩, hk⟩)
    · exact hwired (.inl hf)
    · exact hwired (.inr ⟨α, hα, hk⟩)
    · have e₁' : i = u := e₁
      have hk' : k ≤ ar α := hk
      rw [e₂, hγ] at hk'
      rw [e₁']
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk' with rfl | rfl
      · exact ⟨p, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨q, .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))⟩
  · rintro i k α hf (hα | ⟨e, -⟩)
    · exact h.free_agent hf hα
    · exact hu0 (.inr (.inr ⟨k, e ▸ hf⟩))
  · rintro a α l (hα | ⟨e, -⟩) hused
    · rcases Net.used_insert1 hpq h.symm hused with hN | e'
      · exact h.fresh l hα hN
      · exact absurd e'.symm (hu' l a α hα)
    · rw [e] at hused
      rcases Net.used_insert1 hpq h.symm hused with hN | e'
      · exact absurd hN (hu l)
      · exact List.append_left_eq_self.1 e'

/-- The same insertion, on the data of a net. -/
def XNet.insert1 (X : XNet S) (u : Id) (γ : S) (p q : Port) : XNet S :=
  ⟨(u, γ) :: X.agents, X.free,
    (p, (u, 0)) :: ((u, 0), p) :: ((u, 1), q) :: (q, (u, 1)) ::
      X.wires.filter fun e => decide (e.1 ≠ p ∧ e.1 ≠ q)⟩

theorem XNet.insert1_toNet (X : XNet S) (u : Id) (γ : S) (p q : Port) :
    (X.insert1 u γ p q).toNet = X.toNet.insert1 u γ p q := by
  apply Net.ext'
  · intro i α
    show (i, α) ∈ (u, γ) :: X.agents ↔ (i, α) ∈ X.agents ∨ (i = u ∧ α = γ)
    rw [List.mem_cons]
    constructor
    · rintro (e | h)
      · exact .inr ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
      · exact .inl h
    · rintro (h | ⟨e₁, e₂⟩)
      · exact .inr h
      · exact .inl (by rw [e₁, e₂])
  · intro x y
    show (x, y) ∈ (p, (u, 0)) :: ((u, 0), p) :: ((u, 1), q) :: (q, (u, 1)) ::
        X.wires.filter (fun e => decide (e.1 ≠ p ∧ e.1 ≠ q)) ↔
      ((x, y) ∈ X.wires ∧ x ≠ p ∧ x ≠ q) ∨ (x = p ∧ y = (u, 0)) ∨ (x = (u, 0) ∧ y = p) ∨
        (x = (u, 1) ∧ y = q) ∨ (x = q ∧ y = (u, 1))
    rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_filter]
    constructor
    · rintro (e | e | e | e | ⟨hm, hd⟩)
      · exact .inr (.inl ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩)
      · exact .inr (.inr (.inl ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩))
      · exact .inr (.inr (.inr (.inl ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩)))
      · exact .inr (.inr (.inr (.inr ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩)))
      · exact .inl ⟨hm, of_decide_eq_true hd⟩
    · rintro (⟨hm, hd⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩)
      · exact .inr (.inr (.inr (.inr ⟨hm, decide_eq_true hd⟩)))
      · exact .inl (by rw [e₁, e₂])
      · exact .inr (.inl (by rw [e₁, e₂]))
      · exact .inr (.inr (.inl (by rw [e₁, e₂])))
      · exact .inr (.inr (.inr (.inl (by rw [e₁, e₂]))))
  · intro x
    exact Iff.rfl

/-! ### Firing is local

In a net without history, what a firing does to the wires is decided by the
neighbourhood of the active pair: its two agents and the segments at their
ports. -/

/-- The neighbourhood of two agents: the two agents, the segments at their
ports, and, as free ports, the other extremities of those segments. -/
def Net.nbhd (N : Net S) (a b : Id) (α β : S) : Net S where
  agent i γ := (i = a ∧ γ = α) ∨ (i = b ∧ γ = β)
  link p q := N.link p q ∧ (p.1 = a ∨ p.1 = b ∨ q.1 = a ∨ q.1 = b)
  free p := p.1 ≠ a ∧ p.1 ≠ b ∧ ∃ A : Port, (A.1 = a ∨ A.1 = b) ∧ N.link A p

namespace Site

variable {ar : S → Nat} {a b : Id} {α β : S} {R : Rhs S}

/-- The neighbourhood of an active pair of a matching is a matching. -/
theorem nbhd_matching (h : Site ar N a b α β) (hm : N.Matching ar) :
    (N.nbhd a b α β).Matching ar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i γ δ (⟨e₁, e₁'⟩ | ⟨e₁, e₁'⟩) (⟨e₂, e₂'⟩ | ⟨e₂, e₂'⟩)
    · rw [e₁', e₂']
    · exact absurd (e₁.symm.trans e₂) h.ne
    · exact absurd (e₂.symm.trans e₁) h.ne
    · rw [e₁', e₂']
  · rintro p q ⟨hl, ho⟩
    refine ⟨hm.symm hl, ?_⟩
    rcases ho with ho | ho | ho | ho
    · exact .inr (.inr (.inl ho))
    · exact .inr (.inr (.inr ho))
    · exact .inl ho
    · exact .inr (.inl ho)
  · rintro p ⟨hl, -⟩
    exact hm.irrefl hl
  · rintro p q q' ⟨hl, -⟩ ⟨hl', -⟩
    exact hm.functional hl hl'
  · rintro p q ⟨hl, ho⟩
    have hE := hm.ends hl
    by_cases hpa : p.1 = a
    · rcases hE with hf | ⟨γ, hg, hk⟩
      · exact absurd (hpa ▸ h.ha) (hm.free_agent hf)
      · rw [hpa] at hg
        rw [hm.agent_fun hg h.ha] at hk
        exact .inr ⟨α, .inl ⟨hpa, rfl⟩, hk⟩
    by_cases hpb : p.1 = b
    · rcases hE with hf | ⟨γ, hg, hk⟩
      · exact absurd (hpb ▸ h.hb) (hm.free_agent hf)
      · rw [hpb] at hg
        rw [hm.agent_fun hg h.hb] at hk
        exact .inr ⟨β, .inr ⟨hpb, rfl⟩, hk⟩
    · refine .inl ⟨hpa, hpb, q, ?_, hm.symm hl⟩
      rcases ho with ho | ho | ho | ho
      · exact absurd ho hpa
      · exact absurd ho hpb
      · exact .inl ho
      · exact .inr ho
  · rintro p (⟨-, -, A, hA, hl⟩ | ⟨γ, ⟨e, rfl⟩ | ⟨e, rfl⟩, hk⟩)
    · exact ⟨A, hm.symm hl, .inr (.inr hA)⟩
    · obtain ⟨q, hl⟩ := hm.wired (p := p) (.inr ⟨γ, e ▸ h.ha, hk⟩)
      exact ⟨q, hl, .inl e⟩
    · obtain ⟨q, hl⟩ := hm.wired (p := p) (.inr ⟨γ, e ▸ h.hb, hk⟩)
      exact ⟨q, hl, .inr (.inl e)⟩
  · rintro i k γ ⟨ha, hb, -⟩ (⟨e, -⟩ | ⟨e, -⟩)
    · exact ha e
    · exact hb e
  · intro c γ l hc hu
    have hc' : ∃ δ, N.agent c δ := by
      rcases hc with ⟨e, -⟩ | ⟨e, -⟩
      · exact ⟨α, e ▸ h.ha⟩
      · exact ⟨β, e ▸ h.hb⟩
    obtain ⟨δ, hδ⟩ := hc'
    refine hm.fresh l hδ ?_
    rcases hu with ⟨ε, ⟨e, -⟩ | ⟨e, -⟩⟩ | ⟨k, q, hl, -⟩ | ⟨k, -, -, A, -, hl⟩
    · exact .inl ⟨α, e ▸ h.ha⟩
    · exact .inl ⟨β, e ▸ h.hb⟩
    · exact .inr (.inl ⟨k, q, hl⟩)
    · exact .inr (.inl ⟨k, A, hm.symm hl⟩)

/-- The pair is an active pair of its neighbourhood. -/
theorem nbhd_site (h : Site ar N a b α β) (hm : N.Matching ar) :
    Site ar (N.nbhd a b α β) a b α β :=
  ⟨(h.nbhd_matching hm).wf, .inl ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩, h.ne,
    _, _, .single ⟨hm.paired_iff.1 h.paired_principal, .inl rfl⟩⟩

/-- The ends after a firing are those of the fired neighbourhood, and the
ends that are away from the pair. -/
theorem end_fire_local (h : Site ar N a b α β) (hm : N.Matching ar) {p : Port}
    (hp : (N.fire a b R).End ar p) :
    ((N.nbhd a b α β).fire a b R).End ar p ∨
      (N.End ar p ∧ p.1 ≠ a ∧ p.1 ≠ b ∧ ∀ r, N.link p r → r.1 ≠ a ∧ r.1 ≠ b) := by
  have key : N.End ar p → p.1 ≠ a → p.1 ≠ b →
      ((N.nbhd a b α β).fire a b R).End ar p ∨
        (N.End ar p ∧ p.1 ≠ a ∧ p.1 ≠ b ∧ ∀ r, N.link p r → r.1 ≠ a ∧ r.1 ≠ b) := by
    intro hE hpa hpb
    by_cases hfar : ∃ r : Port, N.link p r ∧ (r.1 = a ∨ r.1 = b)
    · obtain ⟨r, hl, hr⟩ := hfar
      exact .inl (.inl ⟨hpa, hpb, r, hr, hm.symm hl⟩)
    · refine .inr ⟨hE, hpa, hpb, fun r hl => ⟨fun e => hfar ⟨r, hl, .inl e⟩,
        fun e => hfar ⟨r, hl, .inr e⟩⟩⟩
  rcases hp with hf | ⟨γ, ⟨hg, hpa, hpb⟩ | ⟨o, j, e, hl⟩, hk⟩
  · exact key (.inl hf) (fun e => hm.free_agent hf (e ▸ h.ha))
      (fun e => hm.free_agent hf (e ▸ h.hb))
  · exact key (.inr ⟨γ, hg, hk⟩) hpa hpb
  · exact .inl (.inr ⟨γ, .inr ⟨o, j, e, hl⟩, hk⟩)

/-- **Firing is local.**  After a firing in a net without history, two ends
are paired exactly when they are paired after the same firing in the
neighbourhood of the pair, or were joined before by a segment away from the
pair. -/
theorem fire_local (h : Site ar N a b α β) (hm : N.Matching ar) (hR : R.WF ar α β)
    {p q : Port} :
    (N.fire a b R).Paired ar p q ↔
      ((N.nbhd a b α β).fire a b R).Paired ar p q ∨
        (N.link p q ∧ p.1 ≠ a ∧ p.1 ≠ b ∧ q.1 ≠ a ∧ q.1 ≠ b) := by
  have h₀ := h.nbhd_site hm
  -- ends of the fired neighbourhood are ends of the fired net
  have hend : ∀ {x : Port}, ((N.nbhd a b α β).fire a b R).End ar x → (N.fire a b R).End ar x := by
    rintro x (⟨hxa, hxb, A, -, hl⟩ | ⟨γ, ⟨⟨e, -⟩ | ⟨e, -⟩, na, nb⟩ | ⟨o, j, e, hl⟩, hk⟩)
    · exact (hm.ends (hm.symm hl)).fire hxa hxb
    · exact absurd e na
    · exact absurd e nb
    · exact .inr ⟨γ, .inr ⟨o, j, e, hl⟩, hk⟩
  -- a junction of the fired neighbourhood is a junction of the fired net
  have hjun : ∀ {x y : Port}, ((N.nbhd a b α β).fire a b R).link x y →
      ¬ ((N.nbhd a b α β).fire a b R).End ar y → ¬ (N.fire a b R).End ar y := by
    intro x y hl hn hE
    rcases h.end_fire_local hm hE with hE₀ | ⟨hEy, hya, hyb, hfar⟩
    · exact hn hE₀
    · rcases hl with ⟨hl, ho⟩ | ⟨z, w, -, -, rfl⟩
      · have := hfar x (hm.symm hl)
        rcases ho with ho | ho | ho | ho
        · exact this.1 ho
        · exact this.2 ho
        · exact hya ho
        · exact hyb ho
      · cases w with
        | ifc s k =>
          cases s
          · exact hya rfl
          · exact hyb rfl
        | new o j k => exact h.not_used_child o j hEy.used
  have hsub : ∀ {x y : Port}, ((N.nbhd a b α β).fire a b R).Paired ar x y →
      (N.fire a b R).Paired ar x y := by
    have hL : ∀ {x y : Port}, ((N.nbhd a b α β).fire a b R).link x y →
        (N.fire a b R).link x y := by
      rintro x y (hl | hl)
      · exact .inl hl.1
      · exact .inr hl
    rintro x y ⟨hx, hy, v, z, w⟩
    exact ⟨hend hx, hend hy, v, z,
      Walk.mono (L' := (N.fire a b R).link) (T' := (N.fire a b R).End ar) hL hjun w⟩
  constructor
  · intro hpq
    rcases h.end_fire_local hm hpq.1 with hE₀ | ⟨hEp, hpa, hpb, hfar⟩
    · obtain ⟨q₀, hq₀, -, c⟩ := (h₀.fire_wf hR).end_conn hE₀
      have hp₀ : ((N.nbhd a b α β).fire a b R).Paired ar p q₀ := ⟨hE₀, hq₀, c⟩
      rw [hpq.det (h.fire_wf hR) (hsub hp₀)]
      exact .inl hp₀
    · obtain ⟨r, hl⟩ := hm.wired hEp
      obtain ⟨hra, hrb⟩ := hfar r hl
      have hpr := h.paired_fire (R := R) (hm.paired_iff.2 hl) hpa hpb hra hrb
      rw [hpq.det (h.fire_wf hR) hpr]
      exact .inr ⟨hl, hpa, hpb, hra, hrb⟩
  · rintro (hp₀ | ⟨hl, hpa, hpb, hqa, hqb⟩)
    · exact hsub hp₀
    · exact h.paired_fire (hm.paired_iff.2 hl) hpa hpb hqa hqb

end Site

/-! ### Counting the loops, executably

The loops closed by a firing are found by exploring the segments from each
auxiliary port of the pair, and the result of each exploration is checked.
A list of points that every segment stays inside, reached from the port, is
the port's component: if it holds no end the port is dead, if it holds one
the port is live, and if the list is not closed the count is not reported.
The next section shows that, on valid inputs, the exploration always
finishes and the count is always reported. -/

/-- One round of exploration: add the points joined to a point already
found. -/
def grow (links : List (Port × Port)) (K : List Port) : List Port :=
  K ++ links.filterMap fun e => if e.1 ∈ K ∧ e.2 ∉ K then some e.2 else none

/-- `n` rounds of exploration. -/
def explore (links : List (Port × Port)) : Nat → List Port → List Port
  | 0, K => K
  | n + 1, K => explore links n (grow links K)

/-- No segment leaves the list. -/
def closedIn (links : List (Port × Port)) (K : List Port) : Bool :=
  links.all fun e => decide (e.1 ∈ K → e.2 ∈ K)

section Explore

variable {M : Net S} {links : List (Port × Port)} {e : Port}

theorem grow_reach (hl : ∀ {p q}, (p, q) ∈ links → M.link p q) {K : List Port}
    (hK : ∀ x ∈ K, M.Reach e x) : ∀ x ∈ grow links K, M.Reach e x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hK x hx
  · obtain ⟨⟨p, q⟩, hm, hs⟩ := List.mem_filterMap.1 hx
    dsimp only at hs
    split at hs
    · rename_i hc
      have e' : q = x := Option.some.inj hs
      rw [← e']
      exact .tail (hK p hc.1) (hl hm)
    · cases hs

theorem explore_reach (hl : ∀ {p q}, (p, q) ∈ links → M.link p q) :
    ∀ (n : Nat) {K : List Port}, (∀ x ∈ K, M.Reach e x) → ∀ x ∈ explore links n K, M.Reach e x
  | 0, _, hK => hK
  | n + 1, _, hK => explore_reach hl n (grow_reach hl hK)

theorem mem_explore {x : Port} : ∀ (n : Nat) {K : List Port}, x ∈ K → x ∈ explore links n K
  | 0, _, h => h
  | n + 1, _, h => mem_explore n (List.mem_append_left _ h)

theorem closedIn_reach (hl : ∀ {p q}, M.link p q → (p, q) ∈ links) {K : List Port}
    (hc : closedIn links K = true) (he : e ∈ K) {x : Port} (hr : M.Reach e x) : x ∈ K := by
  induction hr with
  | refl => exact he
  | tail _ hlk ih => exact of_decide_eq_true (List.all_eq_true.1 hc _ (hl hlk)) ih

end Explore

/-- Explore from `e` and check the result: `some (true, K)` when `e` is dead
and `K` is its component, `some (false, K)` when `e` reaches an end, `none`
when the exploration did not finish. -/
def deadStatus (links : List (Port × Port)) (ends : List Port) (fuel : Nat) (e : Port) :
    Option (Bool × List Port) :=
  if (explore links fuel [e]).any (fun x => decide (x ∈ ends)) then
    some (false, explore links fuel [e])
  else if closedIn links (explore links fuel [e]) then some (true, explore links fuel [e])
  else none

section Status

variable {M : Net S} {ar : S → Nat} {links : List (Port × Port)} {ends : List Port}
  {fuel : Nat} {e : Port} {K : List Port}

theorem deadStatus_live (hl : ∀ p q, (p, q) ∈ links ↔ M.link p q)
    (hends : ∀ p, p ∈ ends ↔ M.End ar p)
    (h : deadStatus links ends fuel e = some (false, K)) : ¬ M.Dead ar e := by
  unfold deadStatus at h
  split at h
  · rename_i hany
    obtain ⟨x, hx, hxe⟩ := List.any_eq_true.1 hany
    intro hd
    refine hd.2 x (explore_reach (fun h => (hl _ _).1 h) fuel (K := [e]) ?_ x hx)
      ((hends x).1 (of_decide_eq_true hxe))
    intro y hy
    rw [List.mem_singleton.1 hy]
    exact .refl
  · split at h
    · cases h
    · cases h

theorem deadStatus_dead (hl : ∀ p q, (p, q) ∈ links ↔ M.link p q)
    (hends : ∀ p, p ∈ ends ↔ M.End ar p) (he : ∃ q, M.link e q)
    (h : deadStatus links ends fuel e = some (true, K)) :
    M.Dead ar e ∧ ∀ x, x ∈ K ↔ M.Reach e x := by
  unfold deadStatus at h
  split at h
  · cases h
  · rename_i hany
    split at h
    · rename_i hc
      have eK : explore links fuel [e] = K := (Prod.mk.inj (Option.some.inj h)).2
      subst eK
      have hin : e ∈ explore links fuel [e] := mem_explore fuel (List.mem_singleton.2 rfl)
      have hmem : ∀ x, x ∈ explore links fuel [e] ↔ M.Reach e x := by
        intro x
        refine ⟨fun hx => explore_reach (fun h => (hl _ _).1 h) fuel (K := [e]) ?_ x hx,
          fun hr => closedIn_reach (fun h => (hl _ _).2 h) hc hin hr⟩
        intro y hy
        rw [List.mem_singleton.1 hy]
        exact .refl
      refine ⟨⟨he, fun q hr hE => ?_⟩, hmem⟩
      exact hany (List.any_eq_true.2 ⟨q, (hmem q).2 hr, decide_eq_true ((hends q).2 hE)⟩)
    · cases h

end Status

/-- One point in each dead component that meets the list, or `none` if an
exploration did not finish. -/
def loopReps (links : List (Port × Port)) (ends : List Port) (fuel : Nat) :
    List Port → Option (List Port)
  | [] => some []
  | e :: es =>
    match loopReps links ends fuel es with
    | none => none
    | some rs =>
      match deadStatus links ends fuel e with
      | none => none
      | some (true, K) => some (if rs.all (fun r => decide (r ∉ K)) then e :: rs else rs)
      | some (false, _) => some rs

theorem loopReps_spec {M : Net S} {ar : S → Nat} {links : List (Port × Port)} {ends : List Port}
    {fuel : Nat} (hs : ∀ {p q}, M.link p q → M.link q p)
    (hl : ∀ p q, (p, q) ∈ links ↔ M.link p q) (hends : ∀ p, p ∈ ends ↔ M.End ar p) :
    ∀ {l rs : List Port}, (∀ e ∈ l, ∃ q, M.link e q) → loopReps links ends fuel l = some rs →
      (∀ r ∈ rs, r ∈ l ∧ M.Dead ar r) ∧ rs.Pairwise (fun p q => ¬ M.Reach p q) ∧
        ∀ e ∈ l, M.Dead ar e → ∃ r ∈ rs, M.Reach r e
  | [], rs, _, h => by
    have e : [] = rs := Option.some.inj h
    subst e
    exact ⟨fun r hr => absurd hr List.not_mem_nil, .nil, fun e he => absurd he List.not_mem_nil⟩
  | e :: es, rs, hlk, h => by
    unfold loopReps at h
    cases h₁ : loopReps links ends fuel es with
    | none =>
      rw [h₁] at h
      cases h
    | some rs₀ =>
      rw [h₁] at h
      obtain ⟨hmem, hpw, hcov⟩ := loopReps_spec hs hl hends
        (fun e' he' => hlk e' (List.mem_cons_of_mem _ he')) h₁
      have hmem' : ∀ r ∈ rs₀, r ∈ e :: es ∧ M.Dead ar r :=
        fun r hr => ⟨List.mem_cons_of_mem _ (hmem r hr).1, (hmem r hr).2⟩
      cases h₂ : deadStatus links ends fuel e with
      | none =>
        rw [h₂] at h
        cases h
      | some t =>
        obtain ⟨d, K⟩ := t
        rw [h₂] at h
        cases d with
        | false =>
          have hlive := deadStatus_live hl hends h₂
          have e' : rs₀ = rs := Option.some.inj h
          subst e'
          refine ⟨hmem', hpw, fun x hx hd => ?_⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact absurd hd hlive
          · exact hcov x hx hd
        | true =>
          obtain ⟨hdead, hK⟩ := deadStatus_dead hl hends (hlk e (List.mem_cons.2 (.inl rfl))) h₂
          have e' : (if rs₀.all (fun r => decide (r ∉ K)) then e :: rs₀ else rs₀) = rs :=
            Option.some.inj h
          split at e'
          · rename_i hall
            subst e'
            refine ⟨fun r hr => ?_, List.pairwise_cons.2 ⟨fun r hr hreach => ?_, hpw⟩,
              fun x hx hd => ?_⟩
            · rcases List.mem_cons.1 hr with rfl | hr
              · exact ⟨List.mem_cons.2 (.inl rfl), hdead⟩
              · exact hmem' r hr
            · exact of_decide_eq_true (List.all_eq_true.1 hall r hr) ((hK r).2 hreach)
            · rcases List.mem_cons.1 hx with rfl | hx
              · exact ⟨x, List.mem_cons.2 (.inl rfl), .refl⟩
              · obtain ⟨r, hr, hrx⟩ := hcov x hx hd
                exact ⟨r, List.mem_cons_of_mem _ hr, hrx⟩
          · rename_i hall
            subst e'
            refine ⟨hmem', hpw, fun x hx hd => ?_⟩
            rcases List.mem_cons.1 hx with rfl | hx
            · have hex : ∃ r ∈ rs₀, r ∈ K := Classical.byContradiction fun hne =>
                hall (List.all_eq_true.2 fun r hr => decide_eq_true fun hrK => hne ⟨r, hr, hrK⟩)
              obtain ⟨r, hr, hrK⟩ := hex
              exact ⟨r, hr, ((hK r).1 hrK).symm hs⟩
            · exact hcov x hx hd

/-- The number of loops that the firing of `a ⋈ b` closes in the net `Z`, or
`none` if an exploration did not finish. -/
def XNet.loopsAt (ar : S → Nat) (Z : XNet S) (a b : Id) (α β : S) (R : XRhs S) : Option Nat :=
  (loopReps (Z.wires ++ R.wiresFrom a b (ifcPorts ar α β ++ R.newPorts ar) fun _ => true)
    ((Z.fire ar a b α β R).ends ar) (ar α + ar β + 3) (auxPorts ar a b α β)).map List.length

/-- **The count is right whenever it is reported.** -/
theorem XNet.loopsAt_spec {xs : XSys S} {Z : XNet S} (hZ : Z.Ok xs.sys.ar) {a b : Id} {α β : S}
    {R : XRhs S} (r : Redex xs.sys Z.toNet a b α β R.toRhs) (hR : xs.rule α β = some R)
    {ℓ : Nat} (h : Z.loopsAt xs.sys.ar a b α β R = some ℓ) :
    AuxCount xs.sys.ar (Z.toNet.fire a b R.toRhs) a b α β ℓ := by
  have site := r.site hZ.1
  have hRwf := xs.sys.rule_wf r.rule
  have hN' := site.fire_wf hRwf
  obtain ⟨rs, hr, hlen⟩ := Option.map_eq_some_iff.1 h
  have hl : ∀ p q, (p, q) ∈ Z.wires ++
      R.wiresFrom a b (ifcPorts xs.sys.ar α β ++ R.newPorts xs.sys.ar) (fun _ => true) ↔
      (Z.toNet.fire a b R.toRhs).link p q := by
    intro p q
    rw [List.mem_append, XRhs.mem_wiresFrom]
    constructor
    · rintro (hm | ⟨x, -, y, hw, -, rfl, rfl⟩)
      · exact .inl hm
      · exact .inr ⟨x, y, hw, rfl, rfl⟩
    · rintro (hm | ⟨x, y, hxy, rfl, rfl⟩)
      · exact .inl hm
      · refine .inr ⟨x, ?_, y, hxy, rfl, rfl, rfl⟩
        have hv := hRwf.valid hxy
        cases x with
        | ifc s k => exact List.mem_append_left _ (mem_ifcPorts.2 ⟨s, k, rfl, hv⟩)
        | new o j k =>
          obtain ⟨γ, hγ, hk⟩ := hv
          exact List.mem_append_right _
            (XRhs.mem_newPorts.2 ⟨o, j, k, γ, rfl, xs.slots_spec hR hγ, hγ, hk⟩)
  have hends : ∀ p, p ∈ (Z.fire xs.sys.ar a b α β R).ends xs.sys.ar ↔
      (Z.toNet.fire a b R.toRhs).End xs.sys.ar p := by
    intro p
    rw [XNet.mem_ends, XNet.fire_toNet hZ r hR]
    exact Net.end_congr (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) p
  have hlk : ∀ e ∈ auxPorts xs.sys.ar a b α β, ∃ q, (Z.toNet.fire a b R.toRhs).link e q := by
    intro e he
    obtain ⟨s, k, hk, rfl⟩ := mem_auxPorts.1 he
    obtain ⟨y, hy⟩ := hRwf.total (x := .ifc s k) hk
    exact ⟨emb a b y, .inr ⟨_, _, hy, rfl, rfl⟩⟩
  obtain ⟨h₁, h₂, h₃⟩ := loopReps_spec hN'.symm hl hends hlk hr
  exact ⟨rs, hlen, h₁, h₂, h₃⟩

/-- Run the list reducer for at most `n` steps, counting the loops it closes.
Returns the net reached, the number of steps and the number of loops, or
`none` if a count could not be established. -/
def XNet.runLoops (xs : XSys S) : Nat → XNet S → Option (XNet S × Nat × Nat)
  | 0, X => some (X, 0, 0)
  | n + 1, X =>
    match X.findRedex xs with
    | none => some (X, 0, 0)
    | some r =>
      match X.loopsAt xs.sys.ar r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 with
      | none => none
      | some ℓ =>
        (XNet.runLoops xs n (X.fire xs.sys.ar r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)).map
          fun t => (t.1, t.2.1 + 1, ℓ + t.2.2)

/-- The run with counts is the run, and it follows a reduction of any net
with history whose compact form is the input: the two end on the same compact
net, and the net with history has gained one dead component per step and one
per loop counted. -/
theorem XNet.runLoops_spec {xs : XSys S} :
    ∀ {n : Nat} {X Y : XNet S} {k L : Nat} {N : Net S} {n₀ : Nat},
      X.Ok xs.sys.ar → N.WF xs.sys.ar → N.compact xs.sys.ar = X.toNet →
      N.DeadCount xs.sys.ar n₀ → X.runLoops xs n = some (Y, k, L) →
      X.run xs n = (Y, k) ∧ ∃ N', Steps (Step xs.sys) k N N' ∧
        N'.compact xs.sys.ar = Y.toNet ∧ N'.DeadCount xs.sys.ar (n₀ + k + L)
  | 0, X, Y, k, L, N, n₀, _, _, hc, hd, h => by
    have e : (X, 0, 0) = (Y, k, L) := Option.some.inj h
    obtain ⟨rfl, e'⟩ := Prod.mk.inj e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
    exact ⟨rfl, N, .refl _, hc, hd⟩
  | n + 1, X, Y, k, L, N, n₀, hX, hN, hc, hd, h => by
    unfold XNet.runLoops at h
    cases hf : X.findRedex xs with
    | none =>
      rw [hf] at h
      have e : (X, 0, 0) = (Y, k, L) := Option.some.inj h
      obtain ⟨rfl, e'⟩ := Prod.mk.inj e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
      have hstep : X.step xs = none := by
        unfold XNet.step
        rw [hf]
        rfl
      refine ⟨?_, N, .refl _, hc, hd⟩
      unfold XNet.run
      rw [hstep]
    | some t =>
      obtain ⟨a, b, α, β, R⟩ := t
      rw [hf] at h
      dsimp only at h
      cases hℓ : X.loopsAt xs.sys.ar a b α β R with
      | none =>
        rw [hℓ] at h
        cases h
      | some ℓ =>
        rw [hℓ] at h
        cases hrec : XNet.runLoops xs n (X.fire xs.sys.ar a b α β R) with
        | none =>
          rw [hrec] at h
          cases h
        | some t' =>
          obtain ⟨Y', k', L'⟩ := t'
          rw [hrec] at h
          have e : (Y', k' + 1, ℓ + L') = (Y, k, L) := Option.some.inj h
          obtain ⟨rfl, e'⟩ := Prod.mk.inj e
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
          obtain ⟨⟨a₀, α₀⟩, hm, he⟩ := List.exists_of_findSome?_eq_some hf
          obtain ⟨r, hR⟩ := XNet.redexAt_sound he hm
          have hstep : X.step xs = some (X.fire xs.sys.ar a b α β R) := by
            unfold XNet.step
            rw [hf]
            rfl
          obtain ⟨-, hX'⟩ := XNet.step_sound hX hstep
          -- the same step, on the net with history
          have rC : Redex xs.sys (N.compact xs.sys.ar) a b α β R.toRhs := by
            rw [hc]
            exact r
          have rN : Redex xs.sys N a b α β R.toRhs := (Net.compact_obs xs.sys.ar N).symm.redex rC
          have site := rN.site hN
          have hRwf := xs.sys.rule_wf rN.rule
          have hc₁ : (N.fire a b R.toRhs).compact xs.sys.ar = (X.fire xs.sys.ar a b α β R).toNet := by
            rw [site.compact_fire hRwf, hc, XNet.fire_toNet hX r hR]
          have hA : AuxCount xs.sys.ar ((N.compact xs.sys.ar).fire a b R.toRhs) a b α β ℓ := by
            rw [hc]
            exact XNet.loopsAt_spec hX r hR hℓ
          have hd₁ := site.deadCount_of_auxCount hRwf hd (site.auxCount_of_compact hRwf hA)
          obtain ⟨hrun, N', sts, hc', hd'⟩ :=
            XNet.runLoops_spec hX' (site.fire_wf hRwf) hc₁ hd₁ hrec
          refine ⟨?_, N', .head ⟨a, b, α, β, _, rN, rfl⟩ sts, hc', ?_⟩
          · unfold XNet.run
            rw [hstep]
            dsimp only
            rw [hrun]
          · have e : n₀ + (k' + 1) + (ℓ + L') = n₀ + 1 + ℓ + k' + L' := by omega
            rw [e]
            exact hd'

/-- **The reducer counts the loops.**  When the run with counts returns, it
has returned the result of the run, and the number of loops closed by a
reduction of the input, in that many steps, that ends on a net whose compact
form is that result. -/
theorem XNet.runLoops_loops {xs : XSys S} {X Y : XNet S} {n k L : Nat} (hX : X.Ok xs.sys.ar)
    (h : X.runLoops xs n = some (Y, k, L)) :
    X.run xs n = (Y, k) ∧ ∃ N', Steps (Step xs.sys) k X.toNet N' ∧
      N'.compact xs.sys.ar = Y.toNet ∧ Loops xs.sys.ar X.toNet k N' L := by
  obtain ⟨h₁, N', sts, hc, hd⟩ :=
    XNet.runLoops_spec hX hX.1 hX.2 (Net.WF.deadCount_compact hX.2) h
  exact ⟨h₁, N', sts, hc, 0, Net.WF.deadCount_compact hX.2, hd⟩

/-- **The count is the count of every reduction.**  When the run with counts
has stopped on a normal form, every reduction of the input to a normal form
has that many steps and closes that many loops. -/
theorem XNet.runLoops_unique {xs : XSys S} {X Y : XNet S} {n k L : Nat} (hX : X.Ok xs.sys.ar)
    (h : X.runLoops xs n = some (Y, k, L)) (hstop : Y.step xs = none) {m L' : Nat}
    {N₂ : Net S} (h₂ : Steps (Step xs.sys) m X.toNet N₂) (hn₂ : Normal (Step xs.sys) N₂)
    (l₂ : Loops xs.sys.ar X.toNet m N₂ L') : m = k ∧ L' = L := by
  obtain ⟨hrun, N', sts, hc, hl⟩ := XNet.runLoops_loops hX h
  have hY : Y.Ok xs.sys.ar := by
    have := (XNet.run_steps hX n).2
    rw [hrun] at this
    exact this
  have hnY := XNet.step_complete hY hstop
  rw [← hc] at hnY
  have hn' : Normal (Step xs.sys) N' := (normal_compact (Steps.wf hX.1 sts)).2 hnY
  exact ⟨(normal_form_unique hX.1 h₂ sts hn₂ hn').2, loops_unique hX.1 h₂ sts hn₂ hn' l₂ hl⟩

/-! ### The count is always reported -/

section FilterLength

variable {α : Type u} {p q : α → Bool}

theorem length_filter_le_of_imp (hpq : ∀ x, q x = true → p x = true) :
    ∀ l : List α, (l.filter q).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | x :: l => by
    have ih := length_filter_le_of_imp hpq l
    by_cases hq : q x = true
    · rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos (hpq x hq)]
      exact Nat.succ_le_succ ih
    · rw [List.filter_cons_of_neg hq]
      by_cases hp : p x = true
      · rw [List.filter_cons_of_pos hp]
        exact Nat.le_succ_of_le ih
      · rw [List.filter_cons_of_neg hp]
        exact ih

theorem length_filter_lt_of_imp (hpq : ∀ x, q x = true → p x = true) :
    ∀ (l : List α) (y : α), y ∈ l → p y = true → ¬ q y = true →
      (l.filter q).length < (l.filter p).length
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | x :: l, y, hy, hp, hq => by
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [List.filter_cons_of_neg hq, List.filter_cons_of_pos hp]
      exact Nat.lt_succ_of_le (length_filter_le_of_imp hpq l)
    · have ih := length_filter_lt_of_imp hpq l y hy hp hq
      by_cases hqx : q x = true
      · rw [List.filter_cons_of_pos hqx, List.filter_cons_of_pos (hpq x hqx)]
        exact Nat.succ_lt_succ ih
      · rw [List.filter_cons_of_neg hqx]
        by_cases hpx : p x = true
        · rw [List.filter_cons_of_pos hpx]
          exact Nat.lt_succ_of_lt ih
        · rw [List.filter_cons_of_neg hpx]
          exact ih

end FilterLength

section ExploreDone

variable {M : Net S} {ar : S → Nat} {links : List (Port × Port)} {ends : List Port} {e : Port}

theorem grow_closed {K : List Port} (hc : closedIn links K = true) : grow links K = K := by
  have h : (links.filterMap fun e => if e.1 ∈ K ∧ e.2 ∉ K then some e.2 else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    have := of_decide_eq_true (List.all_eq_true.1 hc x hx)
    by_cases h₁ : x.1 ∈ K
    · simp [h₁, this h₁]
    · simp [h₁]
  unfold grow
  rw [h, List.append_nil]

theorem explore_closed {K : List Port} (hc : closedIn links K = true) :
    ∀ n : Nat, explore links n K = K
  | 0 => rfl
  | n + 1 => by
    show explore links n (grow links K) = K
    rw [grow_closed hc]
    exact explore_closed hc n

/-- **The exploration finishes**: if the points that can be reached without
passing an end all lie in a list, then after more rounds than that list has
elements an end has been found, or no segment leaves what has been found. -/
theorem explore_done (B : List Port) (hl : ∀ p q, (p, q) ∈ links ↔ M.link p q)
    (hends : ∀ p, p ∈ ends ↔ M.End ar p)
    (hB : ∀ x, M.Reach e x → ¬ M.End ar x → x ∈ B) :
    ∀ (fuel : Nat) (K : List Port), (∀ x ∈ K, M.Reach e x) →
      (B.filter fun x => decide (x ∉ K)).length < fuel →
      (explore links fuel K).any (fun x => decide (x ∈ ends)) = true ∨
        closedIn links (explore links fuel K) = true
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, K, hK, hμ => by
    by_cases hc : closedIn links K = true
    · refine .inr ?_
      rw [explore_closed hc]
      exact hc
    · have hK₁ := grow_reach (M := M) (e := e) (fun h => (hl _ _).1 h) hK
      by_cases hend : ∃ x ∈ grow links K, M.End ar x
      · obtain ⟨x, hx, hE⟩ := hend
        exact .inl (List.any_eq_true.2 ⟨x, mem_explore n hx, decide_eq_true ((hends x).2 hE)⟩)
      · -- a point outside `K` is found, and it is in `B`
        have hex : ∃ e₀ ∈ links, e₀.1 ∈ K ∧ e₀.2 ∉ K := Classical.byContradiction fun hne =>
          hc (List.all_eq_true.2 fun e₀ he₀ => decide_eq_true fun h₁ =>
            Classical.byContradiction fun h₂ => hne ⟨e₀, he₀, h₁, h₂⟩)
        obtain ⟨e₀, he₀, h₁, h₂⟩ := hex
        have hy : e₀.2 ∈ grow links K :=
          List.mem_append_right _ (List.mem_filterMap.2 ⟨e₀, he₀, by simp [h₁, h₂]⟩)
        have hyB : e₀.2 ∈ B := hB _ (hK₁ _ hy) (fun hE => hend ⟨_, hy, hE⟩)
        have hlt : (B.filter fun x => decide (x ∉ grow links K)).length <
            (B.filter fun x => decide (x ∉ K)).length :=
          length_filter_lt_of_imp (p := fun x => decide (x ∉ K))
            (q := fun x => decide (x ∉ grow links K))
            (fun x hx => decide_eq_true fun hxK =>
              (of_decide_eq_true hx : x ∉ grow links K) (List.mem_append_left _ hxK))
            B e₀.2 hyB (decide_eq_true h₂)
            (fun h => (of_decide_eq_true h : e₀.2 ∉ grow links K) hy)
        exact explore_done B hl hends hB n (grow links K) hK₁ (by omega)

theorem deadStatus_isSome (B : List Port) (hl : ∀ p q, (p, q) ∈ links ↔ M.link p q)
    (hends : ∀ p, p ∈ ends ↔ M.End ar p) (hB : ∀ x, M.Reach e x → ¬ M.End ar x → x ∈ B)
    {fuel : Nat} (hf : B.length < fuel) : (deadStatus links ends fuel e).isSome = true := by
  have hdone := explore_done B hl hends hB fuel [e]
    (fun x hx => by rw [List.mem_singleton.1 hx]; exact .refl)
    (Nat.lt_of_le_of_lt (List.length_filter_le _ _) hf)
  unfold deadStatus
  split
  · rfl
  · rename_i hany
    split
    · rfl
    · rename_i hc
      exact absurd hdone (fun h => h.elim hany hc)

theorem loopReps_isSome {fuel : Nat} :
    ∀ l : List Port, (∀ e ∈ l, (deadStatus links ends fuel e).isSome = true) →
      (loopReps links ends fuel l).isSome = true
  | [], _ => rfl
  | e :: es, h => by
    have ih := loopReps_isSome es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have he := h e (List.mem_cons.2 (.inl rfl))
    unfold loopReps
    cases h₁ : loopReps links ends fuel es with
    | none =>
      rw [h₁] at ih
      cases ih
    | some rs =>
      cases h₂ : deadStatus links ends fuel e with
      | none =>
        rw [h₂] at he
        cases he
      | some t =>
        obtain ⟨d, K⟩ := t
        cases d <;> rfl

end ExploreDone

/-- **The count is always reported** for an active pair of a valid net. -/
theorem XNet.loopsAt_isSome {xs : XSys S} {Z : XNet S} (hZ : Z.Ok xs.sys.ar) {a b : Id}
    {α β : S} {R : XRhs S} (r : Redex xs.sys Z.toNet a b α β R.toRhs)
    (hR : xs.rule α β = some R) : ∃ ℓ, Z.loopsAt xs.sys.ar a b α β R = some ℓ := by
  have site := r.site hZ.1
  have hm := XNet.ok_iff_matching.1 hZ
  have hRwf := xs.sys.rule_wf r.rule
  have hN' := site.fire_wf hRwf
  have hl : ∀ p q, (p, q) ∈ Z.wires ++
      R.wiresFrom a b (ifcPorts xs.sys.ar α β ++ R.newPorts xs.sys.ar) (fun _ => true) ↔
      (Z.toNet.fire a b R.toRhs).link p q := by
    intro p q
    rw [List.mem_append, XRhs.mem_wiresFrom]
    constructor
    · rintro (hm | ⟨x, -, y, hw, -, rfl, rfl⟩)
      · exact .inl hm
      · exact .inr ⟨x, y, hw, rfl, rfl⟩
    · rintro (hm | ⟨x, y, hxy, rfl, rfl⟩)
      · exact .inl hm
      · refine .inr ⟨x, ?_, y, hxy, rfl, rfl, rfl⟩
        have hv := hRwf.valid hxy
        cases x with
        | ifc s k => exact List.mem_append_left _ (mem_ifcPorts.2 ⟨s, k, rfl, hv⟩)
        | new o j k =>
          obtain ⟨γ, hγ, hk⟩ := hv
          exact List.mem_append_right _
            (XRhs.mem_newPorts.2 ⟨o, j, k, γ, rfl, xs.slots_spec hR hγ, hγ, hk⟩)
  have hends : ∀ p, p ∈ (Z.fire xs.sys.ar a b α β R).ends xs.sys.ar ↔
      (Z.toNet.fire a b R.toRhs).End xs.sys.ar p := by
    intro p
    rw [XNet.mem_ends, XNet.fire_toNet hZ r hR]
    exact Net.end_congr (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) p
  -- the points that are not ends are ports of the pair
  have hB : ∀ e ∈ auxPorts xs.sys.ar a b α β, ∀ x, (Z.toNet.fire a b R.toRhs).Reach e x →
      ¬ (Z.toNet.fire a b R.toRhs).End xs.sys.ar x →
      x ∈ (a, 0) :: (b, 0) :: auxPorts xs.sys.ar a b α β := by
    intro e he x hr hx
    have hold : ∀ {y : Port}, Z.toNet.link x y →
        x ∈ (a, 0) :: (b, 0) :: auxPorts xs.sys.ar a b α β := by
      intro y hlxy
      have hE := hm.ends hlxy
      have hab : x.1 = a ∨ x.1 = b := by
        by_cases ha : x.1 = a
        · exact .inl ha
        by_cases hb : x.1 = b
        · exact .inr hb
        exact absurd (hE.fire ha hb) hx
      obtain ⟨i, k⟩ := x
      rcases hab with e' | e'
      · have e'' : i = a := e'
        subst e''
        rcases hE with hf | ⟨γ, hg, hk⟩
        · exact absurd site.ha (hm.free_agent hf)
        · rw [hm.agent_fun hg site.ha] at hk
          cases k with
          | zero => exact List.mem_cons.2 (.inl rfl)
          | succ k =>
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (mem_auxPorts.2 ⟨false, k, hk, rfl⟩))
      · have e'' : i = b := e'
        subst e''
        rcases hE with hf | ⟨γ, hg, hk⟩
        · exact absurd site.hb (hm.free_agent hf)
        · rw [hm.agent_fun hg site.hb] at hk
          cases k with
          | zero => exact List.mem_cons_of_mem _ (List.mem_cons.2 (.inl rfl))
          | succ k =>
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (mem_auxPorts.2 ⟨true, k, hk, rfl⟩))
    rcases hr.last with rfl | ⟨y, hly⟩
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)
    · rcases hN'.symm hly with hlo | ⟨z, w, hzw, e', -⟩
      · exact hold hlo
      · cases z with
        | ifc s k =>
          rw [e']
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (mem_auxPorts.2 ⟨s, k, hRwf.valid hzw, rfl⟩))
        | new o j k =>
          obtain ⟨γ, hγ, hk⟩ := hRwf.valid hzw
          exact absurd (e' ▸ .inr ⟨γ, .inr ⟨o, j, rfl, hγ⟩, hk⟩) hx
  have hlen : ((a, 0) :: (b, 0) :: auxPorts xs.sys.ar a b α β).length <
      xs.sys.ar α + xs.sys.ar β + 3 := by
    simp [auxPorts]
  have hall : ∀ e ∈ auxPorts xs.sys.ar a b α β,
      (deadStatus (Z.wires ++
        R.wiresFrom a b (ifcPorts xs.sys.ar α β ++ R.newPorts xs.sys.ar) (fun _ => true))
        ((Z.fire xs.sys.ar a b α β R).ends xs.sys.ar) (xs.sys.ar α + xs.sys.ar β + 3) e).isSome =
        true :=
    fun e he => deadStatus_isSome _ hl hends (hB e he) hlen
  have hsome := loopReps_isSome (auxPorts xs.sys.ar a b α β) hall
  unfold XNet.loopsAt
  cases hr : loopReps (Z.wires ++
      R.wiresFrom a b (ifcPorts xs.sys.ar α β ++ R.newPorts xs.sys.ar) (fun _ => true))
      ((Z.fire xs.sys.ar a b α β R).ends xs.sys.ar) (xs.sys.ar α + xs.sys.ar β + 3)
      (auxPorts xs.sys.ar a b α β) with
  | none =>
    rw [hr] at hsome
    cases hsome
  | some rs => exact ⟨rs.length, rfl⟩

/-- **The list reducer always reports a count**: on a valid input the run
with counts returns the result of the run and a number of loops. -/
theorem XNet.runLoops_isSome {xs : XSys S} : ∀ (n : Nat) {X : XNet S}, X.Ok xs.sys.ar →
    ∃ L, X.runLoops xs n = some ((X.run xs n).1, (X.run xs n).2, L)
  | 0, _, _ => ⟨0, rfl⟩
  | n + 1, X, hX => by
    unfold XNet.runLoops XNet.run
    cases hf : X.findRedex xs with
    | none =>
      have hstep : X.step xs = none := by
        unfold XNet.step
        rw [hf]
        rfl
      rw [hstep]
      exact ⟨0, rfl⟩
    | some t =>
      obtain ⟨a, b, α, β, R⟩ := t
      obtain ⟨⟨a₀, α₀⟩, hm, he⟩ := List.exists_of_findSome?_eq_some hf
      obtain ⟨r, hR⟩ := XNet.redexAt_sound he hm
      have hstep : X.step xs = some (X.fire xs.sys.ar a b α β R) := by
        unfold XNet.step
        rw [hf]
        rfl
      obtain ⟨-, hX'⟩ := XNet.step_sound hX hstep
      obtain ⟨ℓ, hℓ⟩ := XNet.loopsAt_isSome hX r hR
      obtain ⟨L', hL'⟩ := XNet.runLoops_isSome n hX'
      rw [hstep]
      dsimp only
      rw [hℓ, hL']
      exact ⟨ℓ + L', rfl⟩

end INet
