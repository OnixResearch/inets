import InteractionNets.Fair
import InteractionNets.Addition

/-! # A system inside another

A map of symbols `ι` puts the system `sys₁` inside `sys₂` when it keeps
the arities and the rules: the rule of `sys₂` for two symbols that come
from `sys₁` is the rule of `sys₁`, relabelled (`System.Embeds`).  The
system `sys₂` may have any other symbols, and any rules for them.

A net of `sys₁` with its symbols relabelled (`Net.relabel`) is then a net
of `sys₂` that reduces in the same way: step for step
(`Step.relabel`, `Steps.relabel`), and it is normal when the net is
(`Net.relabel_normal`).  So whatever a net of `sys₁` reduces to, the
thread machine of `sys₂`, with any number of threads and any schedule,
reaches the same on the relabelled memory, with the same claims
(`XMach.relabel_rest`, `XMach.relabel_fair`).  Numerals are kept
(`Addition.IsNum.relabel`).
-/

namespace INet

variable {S₁ S₂ : Type}

/-- A right-hand side with its symbols relabelled. -/
def Rhs.relabel (ι : S₁ → S₂) (R : Rhs S₁) : Rhs S₂ where
  lab o j := (R.lab o j).map ι
  link := R.link

/-- **A net with its symbols relabelled.** -/
def Net.relabel (ι : S₁ → S₂) (N : Net S₁) : Net S₂ where
  agent i γ₂ := ∃ γ, γ₂ = ι γ ∧ N.agent i γ
  link := N.link
  free := N.free

/-- **A system inside another**: the map of symbols keeps the arities,
and the rule of the larger system for two symbols of the smaller is the
rule of the smaller, relabelled. -/
structure System.Embeds (ι : S₁ → S₂) (sys₁ : System S₁) (sys₂ : System S₂) : Prop where
  ar : ∀ α, sys₂.ar (ι α) = sys₁.ar α
  rule : ∀ α β, sys₂.rule (ι α) (ι β) = (sys₁.rule α β).map (Rhs.relabel ι)

theorem Rhs.relabel_id (R : Rhs S₁) : R.relabel id = R := by
  cases R with
  | mk lab link =>
    show Rhs.mk (fun o j => (lab o j).map id) link = Rhs.mk lab link
    congr 1
    funext o j
    cases lab o j <;> rfl

/-- Every system is inside itself. -/
theorem System.Embeds.refl (sys : System S₁) : sys.Embeds id sys where
  ar := fun _ => rfl
  rule := fun α β => by
    show sys.rule α β = (sys.rule α β).map (Rhs.relabel id)
    cases sys.rule α β with
    | none => rfl
    | some R =>
      show some R = some (R.relabel id)
      rw [Rhs.relabel_id]

variable {ι : S₁ → S₂} {sys₁ : System S₁} {sys₂ : System S₂} {N N' : Net S₁}

theorem Net.relabel_agent {i : Id} {γ : S₁} (h : N.agent i γ) : (N.relabel ι).agent i (ι γ) :=
  ⟨γ, rfl, h⟩

/-- The relabelled net has the same ends. -/
theorem Net.relabel_end (h : sys₁.Embeds ι sys₂) (p : Port) :
    (N.relabel ι).End sys₂.ar p ↔ N.End sys₁.ar p := by
  constructor
  · rintro (hf | ⟨γ₂, ⟨γ, e, hγ⟩, hk⟩)
    · exact .inl hf
    · rw [e, h.ar] at hk
      exact .inr ⟨γ, hγ, hk⟩
  · rintro (hf | ⟨γ, hγ, hk⟩)
    · exact .inl hf
    · exact .inr ⟨ι γ, ⟨γ, rfl, hγ⟩, by
        rw [h.ar]
        exact hk⟩

/-- The relabelled net has the same wires. -/
theorem Net.relabel_walk (h : sys₁.Embeds ι sys₂) {u v x y : Port} :
    Walk (N.relabel ι).link ((N.relabel ι).End sys₂.ar) u v x y ↔
      Walk N.link (N.End sys₁.ar) u v x y :=
  ⟨fun w => w.mono (fun hl => hl) (fun _ hq hq' => hq ((Net.relabel_end h _).2 hq')),
    fun w => w.mono (fun hl => hl) (fun _ hq hq' => hq ((Net.relabel_end h _).1 hq'))⟩

theorem Net.relabel_conn (h : sys₁.Embeds ι sys₂) {p q : Port} :
    (N.relabel ι).Conn sys₂.ar p q ↔ N.Conn sys₁.ar p q :=
  ⟨fun ⟨v, x, w⟩ => ⟨v, x, (Net.relabel_walk h).1 w⟩,
    fun ⟨v, x, w⟩ => ⟨v, x, (Net.relabel_walk h).2 w⟩⟩

theorem Net.Paired.relabel (h : sys₁.Embeds ι sys₂) {p q : Port} (hp : N.Paired sys₁.ar p q) :
    (N.relabel ι).Paired sys₂.ar p q :=
  ⟨(Net.relabel_end h p).2 hp.1, (Net.relabel_end h q).2 hp.2.1, (Net.relabel_conn h).2 hp.2.2⟩

/-- Firing and relabelling can be done in either order. -/
theorem Net.fire_relabel (ι : S₁ → S₂) (N : Net S₁) (a b : Id) (R : Rhs S₁) :
    (N.relabel ι).fire a b (R.relabel ι) = (N.fire a b R).relabel ι := by
  apply Net.ext'
  · intro i γ₂
    show (((∃ γ, γ₂ = ι γ ∧ N.agent i γ) ∧ i ≠ a ∧ i ≠ b) ∨
        ∃ o j, i = child a b o j ∧ (R.lab o j).map ι = some γ₂) ↔
      ∃ γ, γ₂ = ι γ ∧ ((N.agent i γ ∧ i ≠ a ∧ i ≠ b) ∨
        ∃ o j, i = child a b o j ∧ R.lab o j = some γ)
    constructor
    · rintro (⟨⟨γ, e, hγ⟩, h1, h2⟩ | ⟨o, j, e, hl⟩)
      · exact ⟨γ, e, .inl ⟨hγ, h1, h2⟩⟩
      · cases hR : R.lab o j with
        | none =>
          rw [hR] at hl
          cases hl
        | some γ =>
          rw [hR] at hl
          exact ⟨γ, (Option.some.inj hl).symm, .inr ⟨o, j, e, hR⟩⟩
    · rintro ⟨γ, e, ⟨hγ, h1, h2⟩ | ⟨o, j, e', hl⟩⟩
      · exact .inl ⟨⟨γ, e, hγ⟩, h1, h2⟩
      · refine .inr ⟨o, j, e', ?_⟩
        rw [hl, e]
        rfl
  · intro p q
    exact Iff.rfl
  · intro p
    exact Iff.rfl

/-- An active pair of the net is an active pair of the relabelled net. -/
theorem Redex.relabel (h : sys₁.Embeds ι sys₂) {a b : Id} {α β : S₁} {R : Rhs S₁}
    (r : Redex sys₁ N a b α β R) :
    Redex sys₂ (N.relabel ι) a b (ι α) (ι β) (R.relabel ι) :=
  ⟨Net.relabel_agent r.ha, Net.relabel_agent r.hb, r.ne, (Net.relabel_conn h).2 r.conn, by
    rw [h.rule, r.rule]
    rfl⟩

/-- **A step of a net is a step of the relabelled net**, in the larger
system. -/
theorem Step.relabel (h : sys₁.Embeds ι sys₂) (st : Step sys₁ N N') :
    Step sys₂ (N.relabel ι) (N'.relabel ι) := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := st
  exact ⟨a, b, ι α, ι β, R.relabel ι, r.relabel h, (Net.fire_relabel ι N a b R).symm⟩

/-- **A reduction of a net is a reduction of the relabelled net**, step
for step. -/
theorem Steps.relabel (h : sys₁.Embeds ι sys₂) {n : Nat} (st : Steps (Step sys₁) n N N') :
    Steps (Step sys₂) n (N.relabel ι) (N'.relabel ι) := by
  induction st with
  | refl => exact .refl _
  | head s _ ih => exact .head (s.relabel h) ih

/-- A step of the relabelled net comes from a step of the net: the two
agents of the pair carry symbols of the smaller system, so the rule is
one of its rules. -/
theorem Step.of_relabel (h : sys₁.Embeds ι sys₂) {M : Net S₂}
    (st : Step sys₂ (N.relabel ι) M) : ∃ N', Step sys₁ N N' ∧ M = N'.relabel ι := by
  obtain ⟨a, b, α₂, β₂, R₂, r, rfl⟩ := st
  obtain ⟨α, eα, ha⟩ := r.ha
  obtain ⟨β, eβ, hb⟩ := r.hb
  have hr := r.rule
  rw [eα, eβ, h.rule] at hr
  cases hR : sys₁.rule α β with
  | none =>
    rw [hR] at hr
    cases hr
  | some R =>
    rw [hR] at hr
    have eR : R.relabel ι = R₂ := Option.some.inj hr
    refine ⟨N.fire a b R, ⟨a, b, α, β, R, ⟨ha, hb, r.ne, (Net.relabel_conn h).1 r.conn, hR⟩, rfl⟩,
      ?_⟩
    rw [← eR]
    exact Net.fire_relabel ι N a b R

/-- **A normal net, relabelled, is normal** in the larger system. -/
theorem Net.relabel_normal (h : sys₁.Embeds ι sys₂) (hn : Normal (Step sys₁) N) :
    Normal (Step sys₂) (N.relabel ι) := by
  intro M st
  obtain ⟨N', s, -⟩ := Step.of_relabel h st
  exact hn N' s

theorem Net.used_relabel {i : Id} (hu : (N.relabel ι).Used i) : N.Used i := by
  rcases hu with ⟨γ₂, γ, -, hγ⟩ | hl | hf
  · exact .inl ⟨γ, hγ⟩
  · exact .inr (.inl hl)
  · exact .inr (.inr hf)

/-- **A well-formed net, relabelled, is well formed** for the larger
system. -/
theorem Net.WF.relabel (h : sys₁.Embeds ι sys₂) (hN : N.WF sys₁.ar) :
    (N.relabel ι).WF sys₂.ar where
  agent_fun := fun {i α β} h1 h2 => by
    obtain ⟨γ, e, hγ⟩ := h1
    obtain ⟨γ', e', hγ'⟩ := h2
    rw [e, e', hN.agent_fun hγ hγ']
  symm := fun hl => hN.symm hl
  irrefl := fun hl => hN.irrefl hl
  end_unique := fun hp h1 h2 => hN.end_unique ((Net.relabel_end h _).1 hp) h1 h2
  end_conn := fun {p} hp => by
    obtain ⟨q, hq, hne, c⟩ := hN.end_conn ((Net.relabel_end h p).1 hp)
    exact ⟨q, (Net.relabel_end h q).2 hq, hne, (Net.relabel_conn h).2 c⟩
  deg := fun h1 h2 h3 => hN.deg h1 h2 h3
  free_agent := fun {i k α} hf ha => by
    obtain ⟨γ, -, hγ⟩ := ha
    exact hN.free_agent hf hγ
  fresh := fun {a α} l ha hu => by
    obtain ⟨γ, -, hγ⟩ := ha
    exact hN.fresh l hγ (Net.used_relabel hu)

/-! ### Numerals -/

namespace Addition

variable {zero succ : S₁}

/-- A numeral of the net is a numeral of the relabelled net. -/
theorem Num.relabel (h : sys₁.Embeds ι sys₂) : ∀ {k : Nat} {i : Id},
    Num sys₁.ar zero succ N i k → Num sys₂.ar (ι zero) (ι succ) (N.relabel ι) i k
  | 0, _, hz => Net.relabel_agent hz
  | _ + 1, _, ⟨hs, i', hp, hn⟩ =>
    ⟨Net.relabel_agent hs, i', hp.relabel h, Num.relabel h hn⟩

theorem IsNum.relabel (h : sys₁.Embeds ι sys₂) {p : Port} {k : Nat}
    (hn : IsNum sys₁.ar zero succ N p k) :
    IsNum sys₂.ar (ι zero) (ι succ) (N.relabel ι) p k := by
  obtain ⟨i, hp, hk⟩ := hn
  exact ⟨i, hp.relabel h, Num.relabel h hk⟩

end Addition

/-! ### Rules given as data -/

theorem assoc_map_snd {A B C : Type} [DecidableEq A] (f : B → C) (k : A) :
    ∀ l : List (A × B), (assoc k l).map f = assoc k (l.map fun e => (e.1, f e.2))
  | [] => rfl
  | (k', v) :: l => by
    show (if k' = k then some v else assoc k l).map f =
      (if k' = k then some (f v) else assoc k (l.map fun e => (e.1, f e.2)))
    by_cases h : k' = k
    · rw [ite_pos' h, ite_pos' h]
      rfl
    · rw [ite_neg' h, ite_neg' h]
      exact assoc_map_snd f k l

/-- The data of a right-hand side with its symbols relabelled. -/
def RuleData.relabel (ι : S₁ → S₂) (D : RuleData S₁) : RuleData S₂ :=
  ⟨D.agents.map fun e => (e.1, ι e.2), D.wires⟩

/-- Relabelling the data relabels the right-hand side. -/
theorem RuleData.toRhs_relabel (ι : S₁ → S₂) (D : RuleData S₁) :
    D.toX.toRhs.relabel ι = (D.relabel ι).toX.toRhs := by
  show Rhs.mk (fun o j => (assoc (o, j) D.agents).map ι)
      (fun x y => assoc x D.wires = some y) =
    Rhs.mk (fun o j => assoc (o, j) (D.agents.map fun e => (e.1, ι e.2)))
      (fun x y => assoc x D.wires = some y)
  congr 1
  funext o j
  exact assoc_map_snd ι (o, j) D.agents

/-! ### In memory -/

/-- A memory with its symbols relabelled. -/
def XNet.relabel (ι : S₁ → S₂) (X : XNet S₁) : XNet S₂ :=
  ⟨X.agents.map fun e => (e.1, ι e.2), X.free, X.wires⟩

theorem XNet.relabel_toNet (ι : S₁ → S₂) (X : XNet S₁) :
    (X.relabel ι).toNet = X.toNet.relabel ι := by
  apply Net.ext'
  · intro i γ₂
    show (i, γ₂) ∈ X.agents.map (fun e => (e.1, ι e.2)) ↔ ∃ γ, γ₂ = ι γ ∧ (i, γ) ∈ X.agents
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨i', γ⟩, hm, e⟩
      injection e with e1 e2
      have e1' : i' = i := e1
      rw [e1'] at hm
      exact ⟨γ, e2.symm, hm⟩
    · rintro ⟨γ, e, hm⟩
      exact ⟨(i, γ), hm, by rw [e]⟩
  · intro p q
    exact Iff.rfl
  · intro p
    exact Iff.rfl

section Machine

variable [DecidableEq S₂]

/-- **What a net reduces to, the larger system's machine reaches on the
relabelled memory.**  Let `sys₁` be inside the system of `xs₂`, and let a
memory hold a well-formed net of `sys₁` that reduces in `n` steps to a
normal form.  Then, with any number of threads and any schedule, a run of
the program of `xs₂` on the relabelled memory that ends at rest has made
`n` claims, and the memory holds the normal form, relabelled. -/
theorem XMach.relabel_rest (xs₂ : XSys S₂) (h : sys₁.Embeds ι xs₂.sys) {X : XNet S₁}
    (hX : X.toNet.WF sys₁.ar) {n : Nat} (s : Steps (Step sys₁) n X.toNet N')
    (nN : Normal (Step sys₁) N') {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.resting = true) :
    ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).2 = n ∧
      ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.mem.toNet = N'.relabel ι := by
  have hU : (X.relabel ι).toNet.WF xs₂.sys.ar := by
    rw [XNet.relabel_toNet]
    exact hX.relabel h
  have s' := s.relabel h
  rw [← XNet.relabel_toNet] at s'
  have hn' := Net.relabel_normal h nN
  have L := XMach.trace_live σ (XMach.init_live (xs := xs₂) hU hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xs₂ σ (XMach.init (X.relabel ι) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hU r q hn
  obtain ⟨e, ek⟩ := (hu s').2 hn'
  exact ⟨ek.symm, e.symm⟩

/-- **The same under a fair schedule.**  With any number of threads and
any unending schedule in which every thread keeps being scheduled, from
some action on every thread is at rest, the claims are `n`, and the
memory holds the normal form, relabelled. -/
theorem XMach.relabel_fair (xs₂ : XSys S₂) (h : sys₁.Embeds ι xs₂.sys) {X : XNet S₁}
    (hX : X.toNet.WF sys₁.ar) {n : Nat} (s : Steps (Step sys₁) n X.toNet N')
    (nN : Normal (Step sys₁) N') {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.resting = true ∧
      ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).2 = n ∧
      ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.mem.toNet = N'.relabel ι := by
  have hU : (X.relabel ι).toNet.WF xs₂.sys.ar := by
    rw [XNet.relabel_toNet]
    exact hX.relabel h
  have s' := s.relabel h
  rw [← XNet.relabel_toNet] at s'
  exact XMach.fair_complete (xs := xs₂) hU hnt s' (Net.relabel_normal h nN) σ hfair

end Machine

end INet
