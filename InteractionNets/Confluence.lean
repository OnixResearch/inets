import InteractionNets.Nets

namespace INet

universe u v

variable {S : Type}

/-! ## Reduction -/

/-- An active pair: two distinct live agents whose principal ports are joined
by a wire, together with the rule that applies to them. -/
structure Redex (sys : System S) (N : Net S) (a b : Id) (α β : S) (R : Rhs S) : Prop where
  ha : N.agent a α
  hb : N.agent b β
  ne : a ≠ b
  conn : N.Conn sys.ar (a, 0) (b, 0)
  rule : sys.rule α β = some R

/-- One step of reduction: fire an active pair. -/
def Step (sys : System S) (N N' : Net S) : Prop :=
  ∃ a b α β R, Redex sys N a b α β R ∧ N' = N.fire a b R

namespace Redex

variable {sys : System S} {N : Net S} {a b c d : Id} {α β γ δ : S} {R R' : Rhs S}

theorem site (r : Redex sys N a b α β R) (hN : N.WF sys.ar) : Site sys.ar N a b α β :=
  ⟨hN, r.ha, r.hb, r.ne, r.conn⟩

theorem end_left (r : Redex sys N a b α β R) : N.End sys.ar (a, 0) :=
  .inr ⟨α, r.ha, Nat.zero_le _⟩

theorem end_right (r : Redex sys N a b α β R) : N.End sys.ar (b, 0) :=
  .inr ⟨β, r.hb, Nat.zero_le _⟩

/-- The same active pair, seen from the other side. -/
theorem flip (r : Redex sys N a b α β R) (hN : N.WF sys.ar) :
    ∃ R', Redex sys N b a β α R' ∧ N.fire a b R = N.fire b a R' := by
  obtain ⟨R', hR', hm⟩ := sys.rule_symm r.rule
  exact ⟨R', ⟨r.hb, r.ha, r.ne.symm, r.conn.symm hN, hR'⟩, fire_mirror N a b hm⟩

/-- An agent belongs to at most one active pair. -/
theorem partner_unique (r : Redex sys N a b α β R) (r' : Redex sys N a d γ δ R')
    (hN : N.WF sys.ar) : b = d :=
  (Prod.mk.inj (Net.Conn.det hN r.end_left r.end_right r'.end_right r.conn r'.conn)).1

/-- An active pair determines the net obtained by firing it. -/
theorem fire_eq (r : Redex sys N a b α β R) (r' : Redex sys N a b γ δ R')
    (hN : N.WF sys.ar) : N.fire a b R = N.fire a b R' := by
  obtain rfl := hN.agent_fun r.ha r'.ha
  obtain rfl := hN.agent_fun r.hb r'.hb
  obtain rfl := Option.some.inj (r.rule.symm.trans r'.rule)
  rfl

/-- An active pair survives the firing of a disjoint one. -/
theorem fire (r : Redex sys N a b α β R) (r' : Redex sys N c d γ δ R') (hN : N.WF sys.ar)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    Redex sys (N.fire a b R) c d γ δ R' where
  ha := .inl ⟨r'.ha, hca, hcb⟩
  hb := .inl ⟨r'.hb, hda, hdb⟩
  ne := r'.ne
  conn := by
    obtain ⟨v, x, w⟩ := r'.conn
    exact ⟨v, x, (r.site hN).walk_fire w⟩
  rule := r'.rule

/-- Two active pairs are equal, or mirror images, or disjoint; in the last
case they can be fired in either order with the same result. -/
theorem diamond (r : Redex sys N a b α β R) (r' : Redex sys N c d γ δ R') (hN : N.WF sys.ar) :
    N.fire a b R = N.fire c d R' ∨
      ∃ N', Step sys (N.fire a b R) N' ∧ Step sys (N.fire c d R') N' := by
  by_cases hac : a = c
  · subst hac
    obtain rfl := r.partner_unique r' hN
    exact .inl (r.fire_eq r' hN)
  by_cases had : a = d
  · subst had
    obtain ⟨R'', r'', e⟩ := r'.flip hN
    obtain rfl := r.partner_unique r'' hN
    exact .inl ((r.fire_eq r'' hN).trans e.symm)
  by_cases hbc : b = c
  · subst hbc
    obtain ⟨R'', r'', -⟩ := r.flip hN
    exact absurd (r''.partner_unique r' hN) had
  by_cases hbd : b = d
  · subst hbd
    obtain ⟨R₁, r₁, -⟩ := r.flip hN
    obtain ⟨R₂, r₂, -⟩ := r'.flip hN
    exact absurd (r₁.partner_unique r₂ hN) hac
  · refine .inr ⟨(N.fire a b R).fire c d R', ⟨c, d, γ, δ, R', ?_, rfl⟩, ⟨a, b, α, β, R, ?_, ?_⟩⟩
    · exact r.fire r' hN (Ne.symm hac) (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd)
    · exact r'.fire r hN hac had hbc hbd
    · have s := r.site hN
      have s' := r'.site hN
      exact fire_comm N R R'
        (fun t j => ⟨fun e => s.not_used_child t j (e ▸ .inl ⟨_, r'.ha⟩),
          fun e => s.not_used_child t j (e ▸ .inl ⟨_, r'.hb⟩)⟩)
        (fun t j => ⟨fun e => s'.not_used_child t j (e ▸ .inl ⟨_, r.ha⟩),
          fun e => s'.not_used_child t j (e ▸ .inl ⟨_, r.hb⟩)⟩)

end Redex

/-! ## The main theorems -/

variable {sys : System S} {N N₁ N₂ : Net S}

/-- Reduction preserves well-formedness. -/
theorem Step.wf (hN : N.WF sys.ar) (h : Step sys N N₁) : N₁.WF sys.ar := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  exact (r.site hN).fire_wf (sys.rule_wf r.rule)

/-- Reduction preserves the interface. -/
theorem Step.free (h : Step sys N N₁) : N₁.free = N.free := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  rfl

/-- **Strong confluence** (Lafont): two different one-step reducts of a net
have a common one-step reduct. -/
theorem Step.diamond (hN : N.WF sys.ar) (h₁ : Step sys N N₁) (h₂ : Step sys N N₂) :
    N₁ = N₂ ∨ ∃ N', Step sys N₁ N' ∧ Step sys N₂ N' := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h₁
  obtain ⟨c, d, γ, δ, R', r', rfl⟩ := h₂
  exact r.diamond r' hN

theorem strongConfluent (sys : System S) :
    StrongConfluent (fun N : Net S => N.WF sys.ar) (Step sys) :=
  ⟨Step.wf, Step.diamond⟩

/-- **Confluence**: two reductions of a net can be completed to a common
reduct, by paths of equal total length. -/
theorem confluence {n m : Nat} (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) n N N₁) (h₂ : Steps (Step sys) m N N₂) :
    ∃ N' k l, Steps (Step sys) k N₁ N' ∧ Steps (Step sys) l N₂ N' ∧ n + k = m + l :=
  (strongConfluent sys).confluence hN h₁ h₂

/-- **Uniqueness of normal forms**: a net has at most one normal form, and
all reductions reaching it have the same length. -/
theorem normal_form_unique {n m : Nat} (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) n N N₁) (h₂ : Steps (Step sys) m N N₂)
    (hn₁ : Normal (Step sys) N₁) (hn₂ : Normal (Step sys) N₂) : N₁ = N₂ ∧ n = m :=
  (strongConfluent sys).normal_unique hN h₁ h₂ hn₁ hn₂

/-- If a net reaches a normal form in `n` steps, then no reduction of it is
longer than `n` steps, and every reduction extends to that normal form. -/
theorem reduction_bounded {n m : Nat} (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) n N N₁) (hn₁ : Normal (Step sys) N₁)
    (h₂ : Steps (Step sys) m N N₂) : m ≤ n ∧ Steps (Step sys) (n - m) N₂ N₁ :=
  (strongConfluent sys).bounded hN h₁ hn₁ h₂

/-- Well-formedness and the interface are preserved along reductions. -/
theorem Steps.wf {n : Nat} (hN : N.WF sys.ar) (h : Steps (Step sys) n N N₁) : N₁.WF sys.ar :=
  (strongConfluent sys).inv_steps hN h

theorem Steps.free {n : Nat} (h : Steps (Step sys) n N N₁) : N₁.free = N.free := by
  induction h with
  | refl => rfl
  | head h₁ _ ih => exact ih.trans h₁.free

/-! ## Firing several active pairs at once

Active pairs that share no agent can be fired simultaneously.  The result
is the net obtained by firing them one after the other, in any order, and
it is reached by a reduction with one step per pair. -/

/-- Fire all the pairs of a list simultaneously: delete their agents, add
all their new agents and all their new segments. -/
def Net.fireAll (N : Net S) (rs : List (Id × Id × Rhs S)) : Net S where
  agent i γ := (N.agent i γ ∧ ∀ r ∈ rs, i ≠ r.1 ∧ i ≠ r.2.1) ∨
    ∃ r ∈ rs, ∃ o j, i = child r.1 r.2.1 o j ∧ r.2.2.lab o j = some γ
  link p q := N.link p q ∨
    ∃ r ∈ rs, ∃ x y, r.2.2.link x y ∧ p = emb r.1 r.2.1 x ∧ q = emb r.1 r.2.1 y
  free := N.free

/-- Fire the pairs of a list one after the other. -/
def Net.fireSeq (N : Net S) : List (Id × Id × Rhs S) → Net S
  | [] => N
  | r :: rs => (N.fire r.1 r.2.1 r.2.2).fireSeq rs

/-- Simultaneous firing only depends on which pairs are fired. -/
theorem Net.fireAll_congr (N : Net S) {rs rs' : List (Id × Id × Rhs S)}
    (h : ∀ r, r ∈ rs ↔ r ∈ rs') : N.fireAll rs = N.fireAll rs' := by
  have agent : ∀ {rs rs' : List (Id × Id × Rhs S)}, (∀ r, r ∈ rs ↔ r ∈ rs') → ∀ i γ,
      (N.fireAll rs).agent i γ → (N.fireAll rs').agent i γ := by
    rintro rs rs' h i γ (⟨hg, hall⟩ | ⟨r, hr, rest⟩)
    · exact .inl ⟨hg, fun r hr => hall r ((h r).2 hr)⟩
    · exact .inr ⟨r, (h r).1 hr, rest⟩
  have link : ∀ {rs rs' : List (Id × Id × Rhs S)}, (∀ r, r ∈ rs ↔ r ∈ rs') → ∀ p q,
      (N.fireAll rs).link p q → (N.fireAll rs').link p q := by
    rintro rs rs' h p q (hl | ⟨r, hr, rest⟩)
    · exact .inl hl
    · exact .inr ⟨r, (h r).1 hr, rest⟩
  exact Net.ext' (fun i γ => ⟨agent h i γ, agent (fun r => (h r).symm) i γ⟩)
    (fun p q => ⟨link h p q, link (fun r => (h r).symm) p q⟩) (fun _ => Iff.rfl)

/-- Active pairs that can be fired together: each is an active pair of the
net, and no two of them share an agent. -/
structure Indep (sys : System S) (N : Net S) (rs : List (Id × Id × Rhs S)) : Prop where
  redex : ∀ r ∈ rs, ∃ α β, Redex sys N r.1 r.2.1 α β r.2.2
  disjoint : rs.Pairwise fun r r' =>
    r.1 ≠ r'.1 ∧ r.1 ≠ r'.2.1 ∧ r.2.1 ≠ r'.1 ∧ r.2.1 ≠ r'.2.1

namespace Indep

variable {rs rs' : List (Id × Id × Rhs S)} {r : Id × Id × Rhs S}

/-- After the first pair fires, the others are still independent active
pairs. -/
theorem tail (h : Indep sys N (r :: rs)) (hN : N.WF sys.ar) :
    Indep sys (N.fire r.1 r.2.1 r.2.2) rs := by
  obtain ⟨α, β, rx⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
  obtain ⟨hd, ht⟩ := List.pairwise_cons.1 h.disjoint
  refine ⟨fun r' hr' => ?_, ht⟩
  obtain ⟨γ, δ, rx'⟩ := h.redex r' (List.mem_cons.2 (.inr hr'))
  obtain ⟨d₁, d₂, d₃, d₄⟩ := hd r' hr'
  exact ⟨γ, δ, rx.fire rx' hN (Ne.symm d₁) (Ne.symm d₃) (Ne.symm d₂) (Ne.symm d₄)⟩

theorem step (h : Indep sys N (r :: rs)) : Step sys N (N.fire r.1 r.2.1 r.2.2) := by
  obtain ⟨α, β, rx⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
  exact ⟨_, _, α, β, _, rx, rfl⟩

/-- Firing independent pairs one after the other is a reduction with one
step per pair. -/
theorem steps (hN : N.WF sys.ar) (h : Indep sys N rs) :
    Steps (Step sys) rs.length N (N.fireSeq rs) := by
  induction rs generalizing N with
  | nil => exact .refl N
  | cons r rs ih => exact .head h.step (ih (Step.wf hN h.step) (h.tail hN))

/-- Firing independent pairs one after the other is firing them
simultaneously. -/
theorem fireSeq_eq (hN : N.WF sys.ar) (h : Indep sys N rs) : N.fireSeq rs = N.fireAll rs := by
  induction rs generalizing N with
  | nil =>
    refine Net.ext' (fun i γ => ⟨fun hg => .inl ⟨hg, fun r hr => absurd hr List.not_mem_nil⟩, ?_⟩)
      (fun p q => ⟨.inl, ?_⟩) (fun _ => Iff.rfl)
    · rintro (⟨hg, -⟩ | ⟨r, hr, -⟩)
      · exact hg
      · exact absurd hr List.not_mem_nil
    · rintro (hl | ⟨r, hr, -⟩)
      · exact hl
      · exact absurd hr List.not_mem_nil
  | cons r rs ih =>
    show (N.fire r.1 r.2.1 r.2.2).fireSeq rs = _
    rw [ih (Step.wf hN h.step) (h.tail hN)]
    obtain ⟨α, β, rx⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
    have site := rx.site hN
    -- the new agents of `r` are not agents of the other pairs
    have fresh : ∀ r' ∈ rs, ∀ o j,
        child r.1 r.2.1 o j ≠ r'.1 ∧ child r.1 r.2.1 o j ≠ r'.2.1 := by
      intro r' hr' o j
      obtain ⟨γ, δ, rx'⟩ := h.redex r' (List.mem_cons.2 (.inr hr'))
      exact ⟨fun e => site.not_used_child o j (e ▸ .inl ⟨_, rx'.ha⟩),
        fun e => site.not_used_child o j (e ▸ .inl ⟨_, rx'.hb⟩)⟩
    apply Net.ext'
    · intro i γ
      constructor
      · rintro (⟨⟨hg, ha, hb⟩ | ⟨o, j, rfl, hl⟩, hall⟩ | ⟨r', hr', rest⟩)
        · refine .inl ⟨hg, fun r'' hr'' => ?_⟩
          rcases List.mem_cons.1 hr'' with rfl | hr''
          · exact ⟨ha, hb⟩
          · exact hall r'' hr''
        · exact .inr ⟨r, List.mem_cons.2 (.inl rfl), o, j, rfl, hl⟩
        · exact .inr ⟨r', List.mem_cons.2 (.inr hr'), rest⟩
      · rintro (⟨hg, hall⟩ | ⟨r'', hr'', o, j, rfl, hl⟩)
        · have hr := hall r (List.mem_cons.2 (.inl rfl))
          exact .inl ⟨.inl ⟨hg, hr.1, hr.2⟩, fun r' hr' => hall r' (List.mem_cons.2 (.inr hr'))⟩
        · rcases List.mem_cons.1 hr'' with rfl | hr''
          · exact .inl ⟨.inr ⟨o, j, rfl, hl⟩, fun r' hr' => fresh r' hr' o j⟩
          · exact .inr ⟨r'', hr'', o, j, rfl, hl⟩
    · intro p q
      constructor
      · rintro ((hl | hl) | ⟨r', hr', rest⟩)
        · exact .inl hl
        · exact .inr ⟨r, List.mem_cons.2 (.inl rfl), hl⟩
        · exact .inr ⟨r', List.mem_cons.2 (.inr hr'), rest⟩
      · rintro (hl | ⟨r'', hr'', rest⟩)
        · exact .inl (.inl hl)
        · rcases List.mem_cons.1 hr'' with rfl | hr''
          · exact .inl (.inr rest)
          · exact .inr ⟨r'', hr'', rest⟩
    · exact fun _ => Iff.rfl

/-- **Simultaneous firing is a reduction**: firing `k` independent active
pairs at once is reached by `k` steps. -/
theorem fireAll_steps (hN : N.WF sys.ar) (h : Indep sys N rs) :
    Steps (Step sys) rs.length N (N.fireAll rs) := by
  rw [← h.fireSeq_eq hN]
  exact h.steps hN

/-- **The order does not matter**: two lists of independent active pairs
with the same members give the same net when fired one pair at a time. -/
theorem fireSeq_perm (hN : N.WF sys.ar) (h : Indep sys N rs) (h' : Indep sys N rs')
    (hm : ∀ r, r ∈ rs ↔ r ∈ rs') : N.fireSeq rs = N.fireSeq rs' := by
  rw [h.fireSeq_eq hN, h'.fireSeq_eq hN, N.fireAll_congr hm]

end Indep

/-! ## Wire history is unobservable

Two well-formed nets with the same live agents, the same free ports and the
same pairing of ends by wires take the same steps, one for one, and stay
equivalent.  How wires are cut into segments, and what inert segments are
left behind, has no influence on reduction. -/

namespace Net.ObsEq

variable {M N' M' : Net S}

/-- An active pair of a net is an active pair of every equivalent net. -/
theorem redex {a b : Id} {α β : S} {R : Rhs S} (ho : N.ObsEq sys.ar M)
    (r : Redex sys N a b α β R) : Redex sys M a b α β R where
  ha := (ho.agent a α).1 r.ha
  hb := (ho.agent b β).1 r.hb
  ne := r.ne
  conn := ((ho.paired _ _).1 ⟨r.end_left, r.end_right, r.conn⟩).2.2
  rule := r.rule

/-- **Bisimulation**: a step of a net is matched by exactly one step of any
equivalent net, and the results are equivalent. -/
theorem step (ho : N.ObsEq sys.ar M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h : Step sys N N') : ∃ M', Step sys M M' ∧ N'.ObsEq sys.ar M' := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  have r' := ho.redex r
  exact ⟨M.fire a b R, ⟨a, b, α, β, R, r', rfl⟩,
    (r.site hN).obsEq_fire (r'.site hM) ho (sys.rule_wf r.rule)⟩

/-- A reduction is matched by a reduction of the same length. -/
theorem steps {n : Nat} (ho : N.ObsEq sys.ar M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h : Steps (Step sys) n N N') : ∃ M', Steps (Step sys) n M M' ∧ N'.ObsEq sys.ar M' := by
  induction h generalizing M with
  | refl N => exact ⟨M, .refl M, ho⟩
  | head h₁ _ ih =>
    obtain ⟨M₁, s₁, ho₁⟩ := ho.step hN hM h₁
    obtain ⟨M', s', ho'⟩ := ih ho₁ (Step.wf hN h₁) (Step.wf hM s₁)
    exact ⟨M', .head s₁ s', ho'⟩

/-- Equivalent nets are normal together. -/
theorem normal (ho : N.ObsEq sys.ar M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h : Normal (Step sys) N) : Normal (Step sys) M := by
  intro M' s
  obtain ⟨N', s', -⟩ := ho.symm.step hM hN s
  exact h N' s'

/-- Normal forms of equivalent nets are equivalent, and are reached in the
same number of steps. -/
theorem normal_form {n m : Nat} (ho : N.ObsEq sys.ar M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h₁ : Steps (Step sys) n N N') (h₂ : Steps (Step sys) m M M')
    (hn₁ : Normal (Step sys) N') (hn₂ : Normal (Step sys) M') :
    N'.ObsEq sys.ar M' ∧ n = m := by
  obtain ⟨M₁, s₁, ho₁⟩ := ho.steps hN hM h₁
  have hn := ho₁.normal (Steps.wf hN h₁) (Steps.wf hM s₁) hn₁
  obtain ⟨rfl, rfl⟩ := normal_form_unique hM s₁ h₂ hn hn₂
  exact ⟨ho₁, rfl⟩

/-- If a net reaches a normal form in `n` steps, no reduction of an
equivalent net is longer than `n` steps, and every such reduction extends to
an equivalent normal form. -/
theorem bounded {n m : Nat} (ho : N.ObsEq sys.ar M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h₁ : Steps (Step sys) n N N') (hn₁ : Normal (Step sys) N')
    (h₂ : Steps (Step sys) m M M') :
    m ≤ n ∧ ∃ M₁, Steps (Step sys) (n - m) M' M₁ ∧ N'.ObsEq sys.ar M₁ := by
  obtain ⟨M₁, s₁, ho₁⟩ := ho.steps hN hM h₁
  have hn := ho₁.normal (Steps.wf hN h₁) (Steps.wf hM s₁) hn₁
  obtain ⟨hle, s⟩ := reduction_bounded hM s₁ hn h₂
  exact ⟨hle, M₁, s, ho₁⟩

/-- Confluence up to observation: reductions of two equivalent nets can be
completed to equivalent nets, by paths of equal total length. -/
theorem confluence {n m : Nat} (ho : N.ObsEq sys.ar M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h₁ : Steps (Step sys) n N N') (h₂ : Steps (Step sys) m M M') :
    ∃ N'' M'' k l, Steps (Step sys) k N' N'' ∧ Steps (Step sys) l M' M'' ∧
      N''.ObsEq sys.ar M'' ∧ n + k = m + l := by
  obtain ⟨M₁, s₁, ho₁⟩ := ho.steps hN hM h₁
  obtain ⟨M'', k, l, sk, sl, e⟩ := INet.confluence hM s₁ h₂
  obtain ⟨N'', sk', ho''⟩ := ho₁.symm.steps (Steps.wf hM s₁) (Steps.wf hN h₁) sk
  exact ⟨N'', M'', k, l, sk', sl, ho''.symm, e⟩

end Net.ObsEq

/-! ## Compaction

The compact form of a net keeps its agents and free ports and replaces every
wire by a single segment between its two ends.  Segments that touch no end
disappear.  It is a specification, not an algorithm. -/

/-- The net without wire history. -/
def Net.compact (ar : S → Nat) (N : Net S) : Net S where
  agent := N.agent
  link := N.Paired ar
  free := N.free

/-- In a compact net the wires are the segments. -/
theorem Net.compact_paired {ar : S → Nat} {N : Net S} {p q : Port} :
    (N.compact ar).Paired ar p q ↔ N.Paired ar p q := by
  constructor
  · rintro ⟨hp, hq, v, x, w⟩
    cases w with
    | single hl => exact hl
    | cons hl hv _ _ => exact absurd hl.2.1 hv
  · intro h
    exact ⟨h.1, h.2.1, q, p, .single h⟩

/-- A net and its compact form are observationally equivalent. -/
theorem Net.compact_obs (ar : S → Nat) (N : Net S) : N.ObsEq ar (N.compact ar) :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Net.compact_paired.symm⟩

/-- Compacting twice is compacting once. -/
theorem Net.compact_idem (ar : S → Nat) (N : Net S) :
    (N.compact ar).compact ar = N.compact ar :=
  Net.ext' (fun _ _ => Iff.rfl) (fun _ _ => Net.compact_paired) (fun _ => Iff.rfl)

/-- Two nets are observationally equivalent exactly when they have the same
compact form. -/
theorem Net.obsEq_iff_compact_eq {ar : S → Nat} {N M : Net S} :
    N.ObsEq ar M ↔ N.compact ar = M.compact ar := by
  constructor
  · intro h
    exact Net.ext' h.agent h.paired h.free
  · intro e
    have ha : ∀ i γ, (N.compact ar).agent i γ ↔ (M.compact ar).agent i γ :=
      fun i γ => by rw [e]
    have hf : ∀ p, (N.compact ar).free p ↔ (M.compact ar).free p := fun p => by rw [e]
    have hl : ∀ p q, (N.compact ar).link p q ↔ (M.compact ar).link p q :=
      fun p q => by rw [e]
    exact ⟨ha, hf, hl⟩

/-- The compact form of a well-formed net is well formed. -/
theorem Net.WF.compact {ar : S → Nat} {N : Net S} (hN : N.WF ar) : (N.compact ar).WF ar where
  agent_fun := hN.agent_fun
  symm := fun h => ⟨h.2.1, h.1, h.2.2.symm hN⟩
  irrefl := by
    rintro p ⟨hp, -, c⟩
    obtain ⟨q, hq, hne, c'⟩ := hN.end_conn hp
    exact hne (Net.Conn.det hN hp hq hp c' c)
  end_unique := fun _ h h' => Net.Conn.det hN h.1 h.2.1 h'.2.1 h.2.2 h'.2.2
  end_conn := by
    intro p hp
    obtain ⟨q, hq, hne, c⟩ := hN.end_conn hp
    exact ⟨q, hq, hne, q, p, .single ⟨hp, hq, c⟩⟩
  deg := fun h h' _ => .inl (Net.Conn.det hN h.1 h.2.1 h'.2.1 h.2.2 h'.2.2)
  free_agent := hN.free_agent
  fresh := by
    intro a α l ha hu
    refine hN.fresh l ha ?_
    rcases hu with hu | ⟨k, q, hp, -, -⟩ | hu
    · exact .inl hu
    · rcases hp with hf | ⟨γ, hg, -⟩
      · exact .inr (.inr ⟨k, hf⟩)
      · exact .inl ⟨γ, hg⟩
    · exact .inr (.inr hu)

theorem Site.compact {ar : S → Nat} {N : Net S} {a b : Id} {α β : S}
    (h : Site ar N a b α β) : Site ar (N.compact ar) a b α β :=
  ⟨h.wf.compact, h.ha, h.hb, h.ne,
    (Net.compact_paired.2
      ⟨.inr ⟨α, h.ha, Nat.zero_le _⟩, .inr ⟨β, h.hb, Nat.zero_le _⟩, h.conn⟩).2.2⟩

/-- **Compaction commutes with firing**: firing a pair and compacting gives
the same net as compacting first, firing the same pair, and compacting. -/
theorem Site.compact_fire {ar : S → Nat} {N : Net S} {a b : Id} {α β : S} {R : Rhs S}
    (h : Site ar N a b α β) (hR : R.WF ar α β) :
    (N.fire a b R).compact ar = ((N.compact ar).fire a b R).compact ar :=
  Net.obsEq_iff_compact_eq.1 (h.obsEq_fire h.compact (Net.compact_obs ar N) hR)

theorem Net.fireAll_nil (N : Net S) : N.fireAll [] = N := by
  refine Net.ext' (fun i γ => ⟨?_, fun hg => .inl ⟨hg, fun r hr => absurd hr List.not_mem_nil⟩⟩)
    (fun p q => ⟨?_, .inl⟩) (fun _ => Iff.rfl)
  · rintro (⟨hg, -⟩ | ⟨r, hr, -⟩)
    · exact hg
    · exact absurd hr List.not_mem_nil
  · rintro (hl | ⟨r, hr, -⟩)
    · exact hl
    · exact absurd hr List.not_mem_nil

/-- Independent active pairs of a net are independent active pairs of every
equivalent net. -/
theorem Indep.obsEq {M : Net S} {rs : List (Id × Id × Rhs S)} (h : Indep sys N rs)
    (ho : N.ObsEq sys.ar M) : Indep sys M rs :=
  ⟨fun r hr => by
    obtain ⟨α, β, rx⟩ := h.redex r hr
    exact ⟨α, β, ho.redex rx⟩, h.disjoint⟩

/-- Firing the same independent pairs in two equivalent nets gives equivalent
nets. -/
theorem Indep.obsEq_fireSeq {M : Net S} {rs : List (Id × Id × Rhs S)} (h : Indep sys N rs)
    (ho : N.ObsEq sys.ar M) (hN : N.WF sys.ar) (hM : M.WF sys.ar) :
    (N.fireSeq rs).ObsEq sys.ar (M.fireSeq rs) := by
  induction rs generalizing N M with
  | nil => exact ho
  | cons r rs ih =>
    obtain ⟨α, β, rx⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
    have rx' := ho.redex rx
    have h' := h.obsEq ho
    exact ih (h.tail hN)
      ((rx.site hN).obsEq_fire (rx'.site hM) ho (sys.rule_wf rx.rule))
      (Step.wf hN h.step) (Step.wf hM h'.step)

/-- **Compaction commutes with simultaneous firing.** -/
theorem Indep.compact_fireAll {rs : List (Id × Id × Rhs S)} (h : Indep sys N rs)
    (hN : N.WF sys.ar) :
    (N.fireAll rs).compact sys.ar = ((N.compact sys.ar).fireAll rs).compact sys.ar := by
  have ho := Net.compact_obs sys.ar N
  have h' := h.obsEq ho
  rw [← h.fireSeq_eq hN, ← h'.fireSeq_eq hN.compact]
  exact Net.obsEq_iff_compact_eq.1 (h.obsEq_fireSeq ho hN hN.compact)

/-- Reduction of nets without history: fire an active pair, then compact. -/
def CStep (sys : System S) (C C' : Net S) : Prop :=
  ∃ N', Step sys C N' ∧ C' = N'.compact sys.ar

section Compact

variable {C C₁ C₂ C' N' : Net S}

theorem CStep.wf (hC : C.WF sys.ar) (h : CStep sys C C') : C'.WF sys.ar := by
  obtain ⟨N', s, rfl⟩ := h
  exact (Step.wf hC s).compact

/-- The result of a compact step is compact. -/
theorem CStep.compact (h : CStep sys C C') : C'.compact sys.ar = C' := by
  obtain ⟨N', s, rfl⟩ := h
  exact Net.compact_idem sys.ar N'

/-- A step of a net is a compact step of its compact form ... -/
theorem Step.cstep (hN : N.WF sys.ar) (h : Step sys N N') :
    CStep sys (N.compact sys.ar) (N'.compact sys.ar) := by
  obtain ⟨M', s, ho⟩ := (Net.compact_obs sys.ar N).step hN hN.compact h
  exact ⟨M', s, Net.obsEq_iff_compact_eq.1 ho⟩

/-- ... and every compact step of the compact form arises in this way. -/
theorem CStep.lift (hN : N.WF sys.ar) (h : CStep sys (N.compact sys.ar) C') :
    ∃ N', Step sys N N' ∧ C' = N'.compact sys.ar := by
  obtain ⟨M', s, rfl⟩ := h
  obtain ⟨N', s', ho⟩ := (Net.compact_obs sys.ar N).symm.step hN.compact hN s
  exact ⟨N', s', Net.obsEq_iff_compact_eq.1 ho⟩

/-- Reductions and their lengths are preserved by compaction. -/
theorem Steps.cstep {n : Nat} (hN : N.WF sys.ar) (h : Steps (Step sys) n N N') :
    Steps (CStep sys) n (N.compact sys.ar) (N'.compact sys.ar) := by
  induction h with
  | refl N => exact .refl _
  | head h₁ _ ih => exact .head (Step.cstep hN h₁) (ih (Step.wf hN h₁))

/-- A net is normal exactly when its compact form is. -/
theorem normal_compact (hN : N.WF sys.ar) :
    Normal (Step sys) N ↔ Normal (CStep sys) (N.compact sys.ar) := by
  constructor
  · intro hn C' hc
    obtain ⟨N', s, -⟩ := CStep.lift hN hc
    exact hn N' s
  · intro hn N' s
    exact hn _ (Step.cstep hN s)

/-- A reduction of the compact form of a net is the compact image of a
reduction of the net. -/
theorem Steps.lift {n : Nat} {C' : Net S} (hN : N.WF sys.ar)
    (h : Steps (CStep sys) n (N.compact sys.ar) C') :
    ∃ N', Steps (Step sys) n N N' ∧ C' = N'.compact sys.ar := by
  generalize hC : N.compact sys.ar = C at h
  induction h generalizing N with
  | refl C => exact ⟨N, .refl _, hC.symm⟩
  | head h₁ _ ih =>
    subst hC
    obtain ⟨N₁, s₁, rfl⟩ := CStep.lift hN h₁
    obtain ⟨N', sts, e⟩ := ih (Step.wf hN s₁) rfl
    exact ⟨N', .head s₁ sts, e⟩

/-- **Strong confluence without history**. -/
theorem CStep.diamond (hC : C.WF sys.ar) (h₁ : CStep sys C C₁) (h₂ : CStep sys C C₂) :
    C₁ = C₂ ∨ ∃ C', CStep sys C₁ C' ∧ CStep sys C₂ C' := by
  obtain ⟨N₁, s₁, rfl⟩ := h₁
  obtain ⟨N₂, s₂, rfl⟩ := h₂
  rcases Step.diamond hC s₁ s₂ with rfl | ⟨N', t₁, t₂⟩
  · exact .inl rfl
  · exact .inr ⟨N'.compact sys.ar, Step.cstep (Step.wf hC s₁) t₁, Step.cstep (Step.wf hC s₂) t₂⟩

theorem cstrongConfluent (sys : System S) :
    StrongConfluent (fun C : Net S => C.WF sys.ar) (CStep sys) :=
  ⟨CStep.wf, CStep.diamond⟩

/-- Confluence of reduction without history. -/
theorem cconfluence {n m : Nat} (hC : C.WF sys.ar)
    (h₁ : Steps (CStep sys) n C C₁) (h₂ : Steps (CStep sys) m C C₂) :
    ∃ C' k l, Steps (CStep sys) k C₁ C' ∧ Steps (CStep sys) l C₂ C' ∧ n + k = m + l :=
  (cstrongConfluent sys).confluence hC h₁ h₂

/-- Normal forms of reduction without history are unique, and all reductions
reaching them have the same length. -/
theorem cnormal_form_unique {n m : Nat} (hC : C.WF sys.ar)
    (h₁ : Steps (CStep sys) n C C₁) (h₂ : Steps (CStep sys) m C C₂)
    (hn₁ : Normal (CStep sys) C₁) (hn₂ : Normal (CStep sys) C₂) : C₁ = C₂ ∧ n = m :=
  (cstrongConfluent sys).normal_unique hC h₁ h₂ hn₁ hn₂

end Compact

end INet
