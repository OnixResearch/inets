import InteractionNets.Loops

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## An executable reducer

Finite nets without history, executable rules, and a step function that
finds an active pair and fires it, rewiring as it goes.  The step function
is proved to implement `CStep`, and to stop only on normal forms. -/

/-- Executable version of `LPort.IsNew`. -/
def LPort.isNew : LPort → Bool
  | .ifc _ _ => false
  | .new _ _ _ => true

theorem LPort.isNew_iff {x : LPort} : x.isNew = true ↔ x.IsNew := by
  cases x <;> simp [LPort.isNew, LPort.IsNew]

/-- An executable right-hand side: the symbols of the new agents, the
partner of every port, and the list of the slots that hold a new agent. -/
structure XRhs (S : Type) where
  lab : Option Bool → Nat → Option S
  wire : LPort → Option LPort
  slots : List (Option Bool × Nat)

/-- The right-hand side it stands for. -/
def XRhs.toRhs (R : XRhs S) : Rhs S := Rhs.ofWire R.lab R.wire

/-- An executable presentation of an interaction system. -/
structure XSys (S : Type) where
  sys : System S
  rule : S → S → Option (XRhs S)
  rule_spec : ∀ α β, sys.rule α β = (rule α β).map XRhs.toRhs
  slots_spec : ∀ {α β R o j γ}, rule α β = some R → R.lab o j = some γ → (o, j) ∈ R.slots

/-- The mirror image of an executable right-hand side. -/
def XRhs.swap (R : XRhs S) : XRhs S where
  lab o j := R.lab (flipOwner o) j
  wire x := (R.wire x.swap).map LPort.swap
  slots := R.slots.map fun s => (flipOwner s.1, s.2)

theorem XRhs.toRhs_swap (R : XRhs S) : R.swap.toRhs = R.toRhs.swap := by
  have e : ∀ x y : LPort,
      ((R.wire x.swap).map LPort.swap = some y) = (R.wire x.swap = some y.swap) := by
    intro x y
    apply propext
    cases R.wire x.swap with
    | none => simp
    | some z =>
      constructor
      · intro h
        obtain rfl := Option.some.inj h
        simp
      · intro h
        obtain rfl := Option.some.inj h
        simp
  exact congrArg (Rhs.mk (fun o j => R.lab (flipOwner o) j))
    (funext fun x => funext fun y => e x y)

theorem XRhs.swap_slots {R : XRhs S}
    (h : ∀ {o j γ}, R.lab o j = some γ → (o, j) ∈ R.slots) {o : Option Bool} {j : Nat} {γ : S}
    (hl : R.swap.lab o j = some γ) : (o, j) ∈ R.swap.slots :=
  List.mem_map.2 ⟨(flipOwner o, j), h hl, by simp⟩

/-- A finite net without history: its agents, its free ports, and for every
end the end at the other extremity of its wire. -/
structure XNet (S : Type) where
  agents : List (Id × S)
  free : List Port
  wires : List (Port × Port)
  deriving DecidableEq, Repr

/-- The net it stands for. -/
def XNet.toNet (X : XNet S) : Net S where
  agent i γ := (i, γ) ∈ X.agents
  link p q := (p, q) ∈ X.wires
  free p := p ∈ X.free

/-- The invariant of the reducer: the net is well formed and compact. -/
def XNet.Ok (ar : S → Nat) (X : XNet S) : Prop :=
  X.toNet.WF ar ∧ X.toNet.compact ar = X.toNet

/-- The active pair whose first agent is `a`, if there is one. -/
def XNet.redexAt (xs : XSys S) (X : XNet S) (a : Id) (α : S) :
    Option (Id × Id × S × S × XRhs S) :=
  match assoc (a, 0) X.wires with
  | none => none
  | some (b, k) =>
    if k = 0 ∧ a ≠ b then
      match assoc b X.agents with
      | none => none
      | some β =>
        match xs.rule α β with
        | none => none
        | some R => some (a, b, α, β, R)
    else none

/-- Search the agents for an active pair. -/
def XNet.findRedex (xs : XSys S) (X : XNet S) : Option (Id × Id × S × S × XRhs S) :=
  X.agents.findSome? fun e => X.redexAt xs e.1 e.2

/-- The auxiliary ports of the two fired agents, as ports of the right-hand
side. -/
def ifcPorts (ar : S → Nat) (α β : S) : List LPort :=
  (List.range (ar α)).map (.ifc false) ++ (List.range (ar β)).map (.ifc true)

/-- The ports of the new agents. -/
def XRhs.newPorts (ar : S → Nat) (R : XRhs S) : List LPort :=
  R.slots.flatMap fun s =>
    match R.lab s.1 s.2 with
    | some γ => (List.range (ar γ + 1)).map (.new s.1 s.2)
    | none => []

/-- The wires of the right-hand side that leave a port in `xs` and arrive at
a port satisfying `c`, as pairs of ports of the net. -/
def XRhs.wiresFrom (R : XRhs S) (a b : Id) (xs : List LPort) (c : LPort → Bool) :
    List (Port × Port) :=
  xs.filterMap fun x =>
    match R.wire x with
    | some y => if c y then some (emb a b x, emb a b y) else none
    | none => none

/-- The table of wires after `a` and `b` fire: drop the principal wire, join
the auxiliary ports that the right-hand side wires together, and move the
wires that stop at an auxiliary port on to the new agent wired to it. -/
def fireTable (ar : S → Nat) (W : List (Port × Port)) (a b : Id) (α β : S) (R : XRhs S) :
    List (Port × Port) :=
  let ifcs := ifcPorts ar α β
  let et := R.wiresFrom a b ifcs LPort.isNew
  let W₂ := spliceAll (retireTable W (a, 0) (b, 0)) (R.wiresFrom a b ifcs fun y => !y.isNew)
  W₂.map (fun w => ((assoc w.1 et).getD w.1, (assoc w.2 et).getD w.2)) ++
    R.wiresFrom a b (R.newPorts ar) LPort.isNew

/-- Fire the active pair `a ⋈ b`. -/
def XNet.fire (ar : S → Nat) (X : XNet S) (a b : Id) (α β : S) (R : XRhs S) : XNet S where
  agents := X.agents.filter (fun e => decide (e.1 ≠ a ∧ e.1 ≠ b)) ++
    R.slots.filterMap fun s => (R.lab s.1 s.2).map fun γ => (child a b s.1 s.2, γ)
  free := X.free
  wires := fireTable ar X.wires a b α β R

/-- One step of the reducer; `none` when there is no active pair. -/
def XNet.step (xs : XSys S) (X : XNet S) : Option (XNet S) :=
  (X.findRedex xs).map fun r => X.fire xs.sys.ar r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2

/-- Run the reducer for at most `n` steps.  Returns the net reached and the
number of steps taken. -/
def XNet.run (xs : XSys S) : Nat → XNet S → XNet S × Nat
  | 0, X => (X, 0)
  | n + 1, X =>
    match X.step xs with
    | none => (X, 0)
    | some X' => ((XNet.run xs n X').1, (XNet.run xs n X').2 + 1)

/-! ### The reducer implements `CStep` -/

theorem mem_ifcPorts {ar : S → Nat} {α β : S} {x : LPort} :
    x ∈ ifcPorts ar α β ↔ ∃ s k, x = .ifc s k ∧ k < ar (sel α β s) := by
  unfold ifcPorts
  rw [List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨false, k, rfl, List.mem_range.1 hk⟩
    · exact ⟨true, k, rfl, List.mem_range.1 hk⟩
  · rintro ⟨s, k, rfl, hk⟩
    cases s
    · exact .inl ⟨k, List.mem_range.2 hk, rfl⟩
    · exact .inr ⟨k, List.mem_range.2 hk, rfl⟩

theorem XRhs.mem_newPorts {ar : S → Nat} {R : XRhs S} {x : LPort} :
    x ∈ R.newPorts ar ↔
      ∃ o j k γ, x = .new o j k ∧ (o, j) ∈ R.slots ∧ R.lab o j = some γ ∧ k ≤ ar γ := by
  unfold XRhs.newPorts
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨o, j⟩, hs, hx⟩
    dsimp only at hx
    cases hl : R.lab o j with
    | none =>
      rw [hl] at hx
      cases hx
    | some γ =>
      rw [hl] at hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact ⟨o, j, k, γ, rfl, hs, hl, Nat.le_of_lt_succ (List.mem_range.1 hk)⟩
  · rintro ⟨o, j, k, γ, rfl, hs, hl, hk⟩
    refine ⟨(o, j), hs, ?_⟩
    dsimp only
    rw [hl]
    exact List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩

theorem XRhs.mem_wiresFrom {R : XRhs S} {a b : Id} {xs : List LPort} {c : LPort → Bool}
    {p q : Port} :
    (p, q) ∈ R.wiresFrom a b xs c ↔
      ∃ x, x ∈ xs ∧ ∃ y, R.wire x = some y ∧ c y = true ∧ p = emb a b x ∧ q = emb a b y := by
  unfold XRhs.wiresFrom
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, he⟩
    cases hw : R.wire x with
    | none =>
      rw [hw] at he
      cases he
    | some y =>
      rw [hw] at he
      dsimp only at he
      split at he
      · rename_i hc
        cases he
        exact ⟨x, hx, y, hw, hc, rfl, rfl⟩
      · cases he
  · rintro ⟨x, hx, y, hw, hc, rfl, rfl⟩
    exact ⟨x, hx, by simp [hw, hc]⟩

/-- The table computed by `fireTable` is the table of the fired net. -/
theorem Site.exact_fire {ar : S → Nat} {N : Net S} {a b : Id} {α β : S}
    (h : Site ar N a b α β) {R : XRhs S} (hR : R.toRhs.WF ar α β)
    (hslots : ∀ {o j γ}, R.lab o j = some γ → (o, j) ∈ R.slots)
    {W : List (Port × Port)} (hW : Exact W N.link (N.End ar)) :
    Exact (fireTable ar W a b α β R) (N.fire a b R.toRhs).link
      ((N.fire a b R.toRhs).End ar) := by
  have hlink : ∀ {x y : LPort}, R.toRhs.link x y ↔ R.wire x = some y := Iff.rfl
  -- the three lists of wires of the right-hand side
  have hps : ∀ {p q : Port},
      (p, q) ∈ R.wiresFrom a b (ifcPorts ar α β) (fun y => !y.isNew) ↔
        IfcLink a b R.toRhs p q := by
    intro p q
    rw [XRhs.mem_wiresFrom]
    constructor
    · rintro ⟨x, hx, y, hw, hc, rfl, rfl⟩
      obtain ⟨s, k, rfl, -⟩ := mem_ifcPorts.1 hx
      cases y with
      | ifc s' k' => exact ⟨s, k, s', k', hlink.2 hw, rfl, rfl⟩
      | new o j k' => simp [LPort.isNew] at hc
    · rintro ⟨s, k, s', k', hl, rfl, rfl⟩
      exact ⟨.ifc s k, mem_ifcPorts.2 ⟨s, k, rfl, hR.valid hl⟩, .ifc s' k', hlink.1 hl,
        by simp [LPort.isNew], rfl, rfl⟩
  have het : ∀ {p f : Port},
      (p, f) ∈ R.wiresFrom a b (ifcPorts ar α β) LPort.isNew ↔
        ∃ s k y, R.toRhs.link (.ifc s k) y ∧ y.IsNew ∧
          p = emb a b (.ifc s k) ∧ f = emb a b y := by
    intro p f
    rw [XRhs.mem_wiresFrom]
    constructor
    · rintro ⟨x, hx, y, hw, hc, rfl, rfl⟩
      obtain ⟨s, k, rfl, -⟩ := mem_ifcPorts.1 hx
      exact ⟨s, k, y, hlink.2 hw, LPort.isNew_iff.1 hc, rfl, rfl⟩
    · rintro ⟨s, k, y, hl, hn, rfl, rfl⟩
      exact ⟨.ifc s k, mem_ifcPorts.2 ⟨s, k, rfl, hR.valid hl⟩, y, hlink.1 hl,
        LPort.isNew_iff.2 hn, rfl, rfl⟩
  have hfp : ∀ {f g : Port},
      (f, g) ∈ R.wiresFrom a b (R.newPorts ar) LPort.isNew ↔
        NewEnd ar a b R.toRhs f ∧ NewEnd ar a b R.toRhs g ∧ AgentLink a b R.toRhs f g := by
    intro f g
    rw [XRhs.mem_wiresFrom]
    constructor
    · rintro ⟨x, hx, y, hw, hc, rfl, rfl⟩
      obtain ⟨o, j, k, γ, rfl, -, hl, hk⟩ := XRhs.mem_newPorts.1 hx
      have hy := LPort.isNew_iff.1 hc
      exact ⟨⟨o, j, k, γ, rfl, hl, hk⟩,
        Site.newEnd_of_valid hR (hR.symm (hlink.2 hw)) hy,
        _, y, hlink.2 hw, .inr hy, rfl, rfl⟩
    · rintro ⟨⟨o, j, k, γ, rfl, hl, hk⟩, ⟨o', j', k', γ', rfl, -, -⟩, x, y, hxy, -, e₁, e₂⟩
      obtain rfl := h.emb_inj e₁
      obtain rfl := h.emb_inj e₂
      exact ⟨.new o j k, XRhs.mem_newPorts.2 ⟨o, j, k, γ, rfl, hslots hl, hl, hk⟩,
        .new o' j' k', hlink.1 hxy, rfl, rfl, rfl⟩
  have W₀ := h.wf.wiring
  -- retire the two principal ports
  have E₁ : Exact (retireTable W (a, 0) (b, 0)) N.link (Pending ar N a b) :=
    hW.retire W₀ (.inr ⟨α, h.ha, Nat.zero_le _⟩) (.inr ⟨β, h.hb, Nat.zero_le _⟩) h.conn
  have W₁ : Wiring N.link (Pending ar N a b) := ⟨W₀.symm, W₀.deg, fun hp => W₀.term hp.1⟩
  -- join the auxiliary ports wired together by the right-hand side
  have E₂ := Exact.spliceAll (M := IfcLink a b R.toRhs)
    (fun hl => Site.ifcLink_symm hR hl)
    (fun hl => h.newLink_irrefl hR (Site.newLink_iff.2 (.inl hl)))
    (fun hl hl' =>
      h.newLink_unique hR (Site.newLink_iff.2 (.inl hl)) (Site.newLink_iff.2 (.inl hl')))
    (R.wiresFrom a b (ifcPorts ar α β) (fun y => !y.isNew))
    (fun e he => hps.1 he) W₁ E₁
    (fun hl => .inl ⟨h.ifcLink_pending hR hl, h.ifcLink_pending hR (Site.ifcLink_symm hR hl)⟩)
  have E₂' : Exact
      (spliceAll (retireTable W (a, 0) (b, 0))
        (R.wiresFrom a b (ifcPorts ar α β) (fun y => !y.isNew)))
      (fun p q => N.link p q ∨ IfcLink a b R.toRhs p q)
      (fun p => Pending ar N a b p ∧ ¬ ∃ q, IfcLink a b R.toRhs p q) := by
    refine E₂.congr (fun p q => or_congr Iff.rfl ?_) (fun p => and_congr Iff.rfl ?_)
    · constructor
      · rintro (hm | hm)
        · exact hps.1 hm
        · exact Site.ifcLink_symm hR (hps.1 hm)
      · exact fun hl => .inl (hps.2 hl)
    · constructor
      · rintro hall ⟨q, hl⟩
        exact (hall (p, q) (hps.2 hl)).1 rfl
      · rintro hn ⟨u, v⟩ he
        constructor
        · rintro rfl
          exact hn ⟨v, hps.1 he⟩
        · rintro rfl
          exact hn ⟨u, Site.ifcLink_symm hR (hps.1 he)⟩
  -- move the wires that stop at an auxiliary port on to the new agents
  have etfun : ∀ {p f f' : Port},
      (p, f) ∈ R.wiresFrom a b (ifcPorts ar α β) LPort.isNew →
      (p, f') ∈ R.wiresFrom a b (ifcPorts ar α β) LPort.isNew → f = f' := by
    intro p f f' hm hm'
    obtain ⟨s, k, y, hl, -, rfl, rfl⟩ := het.1 hm
    obtain ⟨s', k', y', hl', -, e, rfl⟩ := het.1 hm'
    cases h.emb_inj e
    rw [hR.unique hl hl']
  have E₃ := E₂'.attach (K := AgentLink a b R.toRhs) (F := NewEnd ar a b R.toRhs)
    (fun hl => hl.elim (fun x => .inl (h.wf.symm x)) (fun x => .inr (Site.ifcLink_symm hR x)))
    (fun hl => Site.agentLink_symm hR hl)
    (fun hl => h.newLink_irrefl hR (Site.newLink_iff.2 (.inr hl)))
    (fun hl hl' =>
      h.newLink_unique hR (Site.newLink_iff.2 (.inr hl)) (Site.newLink_iff.2 (.inr hl')))
    (fun hl => Site.agentLink_newEnd hR hl)
    (fun hl => h.agentLink_left hR hl)
    (fun hp => Site.newEnd_agentLink hR hp)
    (fun hp => h.newEnd_not_link hp)
    (fun hp => h.newEnd_not_pending hp)
    (fun p => (assoc p (R.wiresFrom a b (ifcPorts ar α β) LPort.isNew)).getD p)
    (by
      rintro p f hT ⟨x, y, hxy, hn, rfl, rfl⟩
      cases x with
      | new o j k => exact absurd hT.1.1 (h.not_end_child o j k)
      | ifc s k =>
        have hy : y.IsNew := hn.elim (fun e => e.elim) id
        have hm := het.2 ⟨s, k, y, hxy, hy, rfl, rfl⟩
        obtain ⟨f', hf'⟩ := assoc_of_mem hm
        show (assoc _ _).getD _ = _
        rw [hf', etfun (assoc_mem hf') hm]
        rfl)
    (by
      intro p _ hn
      show (assoc _ _).getD _ = _
      cases hf : assoc p (R.wiresFrom a b (ifcPorts ar α β) LPort.isNew) with
      | none => rfl
      | some f =>
        obtain ⟨s, k, y, hl, hy, rfl, rfl⟩ := het.1 (assoc_mem hf)
        exact absurd ⟨_, _, y, hl, .inr hy, rfl, rfl⟩ hn)
    (R.wiresFrom a b (R.newPorts ar) LPort.isNew) hfp
  have key : ∀ (p q : Port),
      ((N.link p q ∨ IfcLink a b R.toRhs p q) ∨ AgentLink a b R.toRhs p q) ↔
        (N.fire a b R.toRhs).link p q := by
    intro p q
    constructor
    · rintro ((hl | hl) | hl)
      · exact .inl hl
      · exact .inr (Site.newLink_iff.2 (.inl hl))
      · exact .inr (Site.newLink_iff.2 (.inr hl))
    · rintro (hl | hl)
      · exact .inl (.inl hl)
      · exact (Site.newLink_iff.1 hl).elim (fun x => .inl (.inr x)) (fun x => .inr x)
  exact E₃.congr key (h.end_fire_iff hR)

namespace XNet

variable {xs : XSys S} {X X' : XNet S} {ar : S → Nat}

/-- In a net satisfying the invariant, the table of wires is the pairing of
ends. -/
theorem Ok.link_iff (h : X.Ok ar) {p q : Port} :
    (p, q) ∈ X.wires ↔ X.toNet.Paired ar p q := by
  have e : (X.toNet.compact ar).link p q = X.toNet.link p q := by rw [h.2]
  exact (Iff.of_eq e).symm

theorem Ok.exact (h : X.Ok ar) : Exact X.wires X.toNet.link (X.toNet.End ar) where
  sound := fun {p q} hm => by
    obtain ⟨hp, hq, c⟩ := h.link_iff.1 hm
    refine ⟨hp, hq, ?_, c⟩
    rintro rfl
    exact h.1.irrefl hm
  total := fun hp => by
    obtain ⟨q, hq, -, c⟩ := h.1.end_conn hp
    exact ⟨q, h.link_iff.2 ⟨hp, hq, c⟩⟩

/-- Firing in the reducer is firing followed by compaction. -/
theorem fire_toNet (hX : X.Ok xs.sys.ar) {a b : Id} {α β : S} {R : XRhs S}
    (r : Redex xs.sys X.toNet a b α β R.toRhs) (hR : xs.rule α β = some R) :
    (X.fire xs.sys.ar a b α β R).toNet = (X.toNet.fire a b R.toRhs).compact xs.sys.ar := by
  have site := r.site hX.1
  have hwf := xs.sys.rule_wf r.rule
  apply Net.ext'
  · intro i γ
    show (i, γ) ∈ (X.fire xs.sys.ar a b α β R).agents ↔ _
    unfold XNet.fire
    dsimp only
    rw [List.mem_append, List.mem_filter, List.mem_filterMap]
    constructor
    · rintro (⟨hm, hk⟩ | ⟨⟨o, j⟩, -, he⟩)
      · exact .inl ⟨hm, of_decide_eq_true hk⟩
      · dsimp only at he
        cases hl : R.lab o j with
        | none =>
          rw [hl] at he
          cases he
        | some γ' =>
          rw [hl] at he
          cases he
          exact .inr ⟨o, j, rfl, hl⟩
    · rintro (⟨hm, hk⟩ | ⟨o, j, rfl, hl⟩)
      · exact .inl ⟨hm, decide_eq_true hk⟩
      · exact .inr ⟨(o, j), xs.slots_spec hR hl, by
          show (R.lab o j).map _ = _
          rw [show R.lab o j = some γ from hl]
          rfl⟩
  · intro p q
    exact (site.exact_fire hwf (fun hl => xs.slots_spec hR hl) hX.exact).mem_iff
      (site.fire_wf hwf).wiring
  · intro p
    exact Iff.rfl

theorem redexAt_sound {a₀ a b : Id} {α₀ α β : S} {R : XRhs S}
    (he : X.redexAt xs a₀ α₀ = some (a, b, α, β, R)) (ha : (a₀, α₀) ∈ X.agents) :
    Redex xs.sys X.toNet a b α β R.toRhs ∧ xs.rule α β = some R := by
  unfold XNet.redexAt at he
  split at he
  · cases he
  · rename_i b' k hw
    split at he
    · rename_i hk
      obtain ⟨rfl, hab⟩ := hk
      split at he
      · cases he
      · rename_i β' hβ
        split at he
        · cases he
        · rename_i R' hR
          cases he
          exact ⟨⟨ha, assoc_mem hβ, hab, ⟨_, _, .single (assoc_mem hw)⟩,
            by rw [xs.rule_spec, hR]; rfl⟩, hR⟩
    · cases he

theorem redexAt_complete (hX : X.Ok xs.sys.ar) {a b : Id} {α β : S} {R : Rhs S}
    (r : Redex xs.sys X.toNet a b α β R) : X.redexAt xs a α ≠ none := by
  have hw : assoc (a, 0) X.wires = some (b, 0) :=
    hX.exact.assoc_eq hX.1.wiring (hX.link_iff.2 ⟨r.end_left, r.end_right, r.conn⟩)
  obtain ⟨β', hβ'⟩ := assoc_of_mem (show (b, β) ∈ X.agents from r.hb)
  obtain rfl : β' = β := hX.1.agent_fun (assoc_mem hβ') r.hb
  have hr := r.rule
  rw [xs.rule_spec] at hr
  cases hx : xs.rule α β' with
  | none =>
    rw [hx] at hr
    cases hr
  | some XR =>
    unfold XNet.redexAt
    simp [hw, hβ', hx, r.ne]

/-- **Soundness**: a step of the reducer is a compact step, and it preserves
the invariant. -/
theorem step_sound (hX : X.Ok xs.sys.ar) (h : X.step xs = some X') :
    CStep xs.sys X.toNet X'.toNet ∧ X'.Ok xs.sys.ar := by
  unfold XNet.step at h
  cases hf : X.findRedex xs with
  | none =>
    rw [hf] at h
    cases h
  | some t =>
    rw [hf] at h
    obtain ⟨a, b, α, β, R⟩ := t
    cases h
    obtain ⟨⟨a₀, α₀⟩, hm, he⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨r, hR⟩ := redexAt_sound he hm
    have e := fire_toNet hX r hR
    have st : Step xs.sys X.toNet (X.toNet.fire a b R.toRhs) := ⟨a, b, α, β, R.toRhs, r, rfl⟩
    refine ⟨⟨_, st, e⟩, ?_, ?_⟩
    · show (X.fire xs.sys.ar a b α β R).toNet.WF xs.sys.ar
      rw [e]
      exact (Step.wf hX.1 st).compact
    · show (X.fire xs.sys.ar a b α β R).toNet.compact xs.sys.ar = _
      rw [e]
      exact Net.compact_idem _ _

/-- **Completeness**: the reducer stops only on normal forms. -/
theorem step_complete (hX : X.Ok xs.sys.ar) (h : X.step xs = none) :
    Normal (CStep xs.sys) X.toNet := by
  rintro C' ⟨N', ⟨a, b, α, β, R, r, -⟩, -⟩
  unfold XNet.step at h
  cases hf : X.findRedex xs with
  | some t =>
    rw [hf] at h
    cases h
  | none =>
    exact redexAt_complete hX r
      (List.findSome?_eq_none_iff.1 hf (a, α) (show (a, α) ∈ X.agents from r.ha))

/-- Running the reducer performs that many compact steps and preserves the
invariant. -/
theorem run_steps (hX : X.Ok xs.sys.ar) (n : Nat) :
    Steps (CStep xs.sys) (X.run xs n).2 X.toNet (X.run xs n).1.toNet ∧
      (X.run xs n).1.Ok xs.sys.ar := by
  induction n generalizing X with
  | zero => exact ⟨.refl _, hX⟩
  | succ n ih =>
    unfold XNet.run
    split
    · exact ⟨.refl _, hX⟩
    · rename_i X' hs
      obtain ⟨st, hX'⟩ := step_sound hX hs
      obtain ⟨sts, hok⟩ := ih hX'
      exact ⟨.head st sts, hok⟩

/-- **Correctness of the reducer**: if it stops, the net it returns is the
normal form of the input, the number of steps it took is the length of every
reduction to normal form, and no reduction is longer. -/
theorem run_normal (hX : X.Ok xs.sys.ar) (n : Nat) (h : (X.run xs n).1.step xs = none) :
    Normal (CStep xs.sys) (X.run xs n).1.toNet ∧
      ∀ {m : Nat} {C : Net S}, Steps (CStep xs.sys) m X.toNet C →
        m ≤ (X.run xs n).2 ∧
          (Normal (CStep xs.sys) C → C = (X.run xs n).1.toNet ∧ m = (X.run xs n).2) := by
  obtain ⟨sts, hok⟩ := run_steps hX n
  have hn := step_complete hok h
  refine ⟨hn, fun {m C} hC => ⟨((cstrongConfluent xs.sys).bounded hX.1 sts hn hC).1, fun hnC => ?_⟩⟩
  obtain ⟨e₁, e₂⟩ := cnormal_form_unique hX.1 hC sts hnC hn
  exact ⟨e₁, e₂⟩

/-- The reducer stops before its fuel runs out, or it uses all of it. -/
theorem run_stop_or_full (xs : XSys S) (X : XNet S) (n : Nat) :
    (X.run xs n).1.step xs = none ∨ (X.run xs n).2 = n := by
  induction n generalizing X with
  | zero => exact .inr rfl
  | succ n ih =>
    unfold XNet.run
    split
    · rename_i hs
      exact .inl hs
    · rename_i X' hs
      rcases ih X' with h | h
      · exact .inl h
      · exact .inr (congrArg (· + 1) h)

/-- On a normal form the reducer has nothing to do. -/
theorem step_none_of_normal (hX : X.Ok xs.sys.ar) (h : Normal (CStep xs.sys) X.toNet) :
    X.step xs = none := by
  cases hs : X.step xs with
  | none => rfl
  | some X' => exact absurd (step_sound hX hs).1 (h _)

/-- **Completeness of the reducer**: if the input has a normal form `C`,
reached in `k` steps by some reduction, and the fuel is at least `k`, then
the reducer stops after exactly `k` steps on a net that stands for `C`. -/
theorem run_complete (hX : X.Ok xs.sys.ar) {k n : Nat} {C : Net S}
    (hC : Steps (CStep xs.sys) k X.toNet C) (hn : Normal (CStep xs.sys) C) (hk : k ≤ n) :
    (X.run xs n).1.step xs = none ∧ (X.run xs n).2 = k ∧ (X.run xs n).1.toNet = C := by
  obtain ⟨sts, hY⟩ := run_steps hX n
  obtain ⟨hle, rest⟩ := (cstrongConfluent xs.sys).bounded hX.1 hC hn sts
  have stop : (X.run xs n).1.step xs = none := by
    rcases run_stop_or_full xs X n with h | h
    · exact h
    · have e : k - (X.run xs n).2 = 0 := by omega
      rw [e] at rest
      cases rest
      exact step_none_of_normal hY hn
  obtain ⟨-, hb⟩ := run_normal hX n stop
  obtain ⟨e₁, e₂⟩ := (hb hC).2 hn
  exact ⟨stop, e₂.symm, e₁.symm⟩

end XNet

/-! ### Firing all active pairs at once

A second reducer, which fires every active pair of the net in one round.
It is proved to compute the compaction of the simultaneous firing, and to
agree with the reducer that fires one pair at a time. -/

/-- An active pair as the reducer finds it: the two agents, their symbols,
and the rule. -/
abbrev XRedex (S : Type) := Id × Id × S × S × XRhs S

/-- The same pair, for the net the data stands for. -/
abbrev XRedex.abs (r : XRedex S) : Id × Id × Rhs S := (r.1, r.2.1, r.2.2.2.2.toRhs)

/-- Fire a list of active pairs. -/
def XNet.fireList (ar : S → Nat) (X : XNet S) : List (XRedex S) → XNet S
  | [] => X
  | r :: rs => (X.fire ar r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2).fireList ar rs

/-- A list of active pairs of a finite net, no two of which share an agent. -/
structure XNet.Indep (xs : XSys S) (X : XNet S) (rs : List (XRedex S)) : Prop where
  redex : ∀ r ∈ rs, Redex xs.sys X.toNet r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.toRhs ∧
    xs.rule r.2.2.1 r.2.2.2.1 = some r.2.2.2.2
  disjoint : rs.Pairwise fun r r' =>
    r.1 ≠ r'.1 ∧ r.1 ≠ r'.2.1 ∧ r.2.1 ≠ r'.1 ∧ r.2.1 ≠ r'.2.1

theorem XNet.Indep.abs {xs : XSys S} {X : XNet S} {rs : List (XRedex S)} (h : X.Indep xs rs) :
    INet.Indep xs.sys X.toNet (rs.map XRedex.abs) := by
  refine ⟨fun r' hr' => ?_, List.pairwise_map.2 h.disjoint⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
  exact ⟨_, _, (h.redex r hr).1⟩

/-- Firing a list of independent pairs in the reducer computes the
compaction of their simultaneous firing, and preserves the invariant. -/
theorem XNet.fireList_toNet {xs : XSys S} {X : XNet S} {rs : List (XRedex S)}
    (hX : X.Ok xs.sys.ar) (h : X.Indep xs rs) :
    (X.fireList xs.sys.ar rs).toNet =
        (X.toNet.fireAll (rs.map XRedex.abs)).compact xs.sys.ar ∧
      (X.fireList xs.sys.ar rs).Ok xs.sys.ar := by
  induction rs generalizing X with
  | nil =>
    refine ⟨?_, hX⟩
    show X.toNet = (X.toNet.fireAll []).compact xs.sys.ar
    rw [Net.fireAll_nil, hX.2]
  | cons r rs ih =>
    obtain ⟨rx, hR⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
    obtain ⟨hd, ht⟩ := List.pairwise_cons.1 h.disjoint
    have e := XNet.fire_toNet hX rx hR
    have st : Step xs.sys X.toNet (X.toNet.fire r.1 r.2.1 r.2.2.2.2.toRhs) :=
      ⟨_, _, _, _, _, rx, rfl⟩
    have hwf := Step.wf hX.1 st
    have hX₁ : (X.fire xs.sys.ar r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2).Ok xs.sys.ar := by
      unfold XNet.Ok
      rw [e]
      exact ⟨hwf.compact, Net.compact_idem _ _⟩
    have h₁ : (X.fire xs.sys.ar r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2).Indep xs rs := by
      refine ⟨fun r' hr' => ?_, ht⟩
      obtain ⟨rx', hR'⟩ := h.redex r' (List.mem_cons.2 (.inr hr'))
      obtain ⟨d₁, d₂, d₃, d₄⟩ := hd r' hr'
      have rf := rx.fire rx' hX.1 (Ne.symm d₁) (Ne.symm d₃) (Ne.symm d₂) (Ne.symm d₄)
      refine ⟨?_, hR'⟩
      rw [e]
      exact (Net.compact_obs xs.sys.ar _).redex rf
    obtain ⟨e', hok⟩ := ih hX₁ h₁
    refine ⟨?_, hok⟩
    show ((X.fire xs.sys.ar r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2).fireList xs.sys.ar rs).toNet = _
    rw [e', e]
    have habs := h.abs
    have hI : INet.Indep xs.sys (X.toNet.fire r.1 r.2.1 r.2.2.2.2.toRhs) (rs.map XRedex.abs) :=
      habs.tail hX.1
    rw [← hI.compact_fireAll hwf, ← hI.fireSeq_eq hwf]
    exact congrArg (Net.compact xs.sys.ar) (habs.fireSeq_eq hX.1)

/-- All the active pairs found by scanning the agents.  Each pair shows up
once from each of its two agents. -/
def XNet.redexes (xs : XSys S) (X : XNet S) : List (XRedex S) :=
  X.agents.filterMap fun e => X.redexAt xs e.1 e.2

/-- Keep the pairs that share no agent with a pair already kept. -/
def selectIndep : List (XRedex S) → List (XRedex S) → List (XRedex S)
  | acc, [] => acc
  | acc, r :: rs =>
    if acc.all (fun r' =>
        decide (r.1 ≠ r'.1 ∧ r.1 ≠ r'.2.1 ∧ r.2.1 ≠ r'.1 ∧ r.2.1 ≠ r'.2.1)) then
      selectIndep (r :: acc) rs
    else selectIndep acc rs

theorem selectIndep_spec {P : XRedex S → Prop} (rs : List (XRedex S)) :
    ∀ acc : List (XRedex S), (∀ r ∈ acc, P r) → (∀ r ∈ rs, P r) →
      acc.Pairwise (fun r r' => r.1 ≠ r'.1 ∧ r.1 ≠ r'.2.1 ∧ r.2.1 ≠ r'.1 ∧ r.2.1 ≠ r'.2.1) →
      (∀ r ∈ selectIndep acc rs, P r) ∧
        (selectIndep acc rs).Pairwise
          (fun r r' => r.1 ≠ r'.1 ∧ r.1 ≠ r'.2.1 ∧ r.2.1 ≠ r'.1 ∧ r.2.1 ≠ r'.2.1) := by
  induction rs with
  | nil => exact fun acc hacc _ hp => ⟨hacc, hp⟩
  | cons r rs ih =>
    intro acc hacc hrs hp
    have hr := hrs r (List.mem_cons.2 (.inl rfl))
    have hrs' : ∀ r' ∈ rs, P r' := fun r' h => hrs r' (List.mem_cons.2 (.inr h))
    unfold selectIndep
    split
    · rename_i hall
      refine ih (r :: acc) (fun r' h => ?_) hrs'
        (List.pairwise_cons.2
          ⟨fun r' h => of_decide_eq_true (List.all_eq_true.1 hall r' h), hp⟩)
      rcases List.mem_cons.1 h with e | h
      · exact e ▸ hr
      · exact hacc r' h
    · exact ih acc hacc hrs' hp

theorem mem_selectIndep (rs : List (XRedex S)) :
    ∀ (acc : List (XRedex S)) (r : XRedex S), r ∈ acc → r ∈ selectIndep acc rs := by
  induction rs with
  | nil => exact fun acc r h => h
  | cons r' rs ih =>
    intro acc r h
    unfold selectIndep
    split
    · exact ih _ r (List.mem_cons.2 (.inr h))
    · exact ih _ r h

/-- The pairs selected from a scan of the agents can be fired together. -/
theorem XNet.redexes_indep (xs : XSys S) (X : XNet S) :
    X.Indep xs (selectIndep [] (X.redexes xs)) := by
  have hP : ∀ r ∈ X.redexes xs,
      Redex xs.sys X.toNet r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.toRhs ∧
        xs.rule r.2.2.1 r.2.2.2.1 = some r.2.2.2.2 := by
    rintro ⟨a, b, α, β, R⟩ hr
    obtain ⟨⟨a₀, α₀⟩, hm, he⟩ := List.mem_filterMap.1 hr
    exact XNet.redexAt_sound he hm
  have h := selectIndep_spec (X.redexes xs) [] (fun r hr => absurd hr List.not_mem_nil) hP
    List.Pairwise.nil
  exact ⟨h.1, h.2⟩

/-- Fire every active pair of the net at once.  Returns the net reached and
the number of pairs fired. -/
def XNet.parStep (xs : XSys S) (X : XNet S) : XNet S × Nat :=
  (X.fireList xs.sys.ar (selectIndep [] (X.redexes xs)),
    (selectIndep [] (X.redexes xs)).length)

/-- A round of the parallel reducer is a reduction with one step per pair
fired, and it preserves the invariant. -/
theorem XNet.parStep_spec {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) :
    Steps (CStep xs.sys) (X.parStep xs).2 X.toNet (X.parStep xs).1.toNet ∧
      (X.parStep xs).1.Ok xs.sys.ar := by
  have hI := XNet.redexes_indep xs X
  obtain ⟨e, hok⟩ := XNet.fireList_toNet hX hI
  refine ⟨?_, hok⟩
  have sts := Steps.cstep hX.1 (hI.abs.fireAll_steps hX.1)
  rw [hX.2, List.length_map] at sts
  show Steps (CStep xs.sys) (selectIndep [] (X.redexes xs)).length X.toNet
    (X.fireList xs.sys.ar (selectIndep [] (X.redexes xs))).toNet
  rw [e]
  exact sts

theorem filterMap_nil_iff_findSome {α : Type u} {β : Type v} (f : α → Option β) (l : List α) :
    l.filterMap f = [] ↔ l.findSome? f = none := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : f a with
    | none => simp [h, ih]
    | some b => simp [h]

/-- A round fires nothing exactly when the net has no active pair. -/
theorem XNet.parStep_zero_iff {xs : XSys S} {X : XNet S} :
    (X.parStep xs).2 = 0 ↔ X.step xs = none := by
  have key : selectIndep [] (X.redexes xs) = [] → X.redexes xs = [] := by
    intro h
    cases hr : X.redexes xs with
    | nil => rfl
    | cons r rs =>
      rw [hr] at h
      have hm : r ∈ selectIndep [] (r :: rs) :=
        mem_selectIndep rs [r] r (List.mem_cons.2 (.inl rfl))
      rw [h] at hm
      exact absurd hm List.not_mem_nil
  constructor
  · intro h
    have h₂ : X.redexes xs = [] := key (List.eq_nil_of_length_eq_zero h)
    have h₃ : X.findRedex xs = none := (filterMap_nil_iff_findSome _ _).1 h₂
    unfold XNet.step
    rw [h₃]
    rfl
  · intro h
    have h₃ : X.findRedex xs = none := by
      unfold XNet.step at h
      cases hf : X.findRedex xs with
      | none => rfl
      | some t =>
        rw [hf] at h
        cases h
    have h₂ : X.redexes xs = [] := (filterMap_nil_iff_findSome _ _).2 h₃
    show (selectIndep [] (X.redexes xs)).length = 0
    rw [h₂]
    rfl

theorem XNet.redexAt_fst {xs : XSys S} {X : XNet S} {a : Id} {α : S} {t : XRedex S}
    (h : X.redexAt xs a α = some t) : t.1 = a := by
  unfold XNet.redexAt at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          rfl
    · cases h

/-- Every pair of the scan is selected, or shares an agent with a selected
pair. -/
theorem selectIndep_covers (rs : List (XRedex S)) :
    ∀ (acc : List (XRedex S)) (r : XRedex S), r ∈ rs →
      ∃ r' ∈ selectIndep acc rs,
        r' = r ∨ ¬ (r.1 ≠ r'.1 ∧ r.1 ≠ r'.2.1 ∧ r.2.1 ≠ r'.1 ∧ r.2.1 ≠ r'.2.1) := by
  induction rs with
  | nil => exact fun acc r h => absurd h List.not_mem_nil
  | cons r₀ rs ih =>
    intro acc r h
    unfold selectIndep
    split
    · rcases List.mem_cons.1 h with e | h
      · exact ⟨r₀, mem_selectIndep rs _ r₀ (List.mem_cons.2 (.inl rfl)), .inl e.symm⟩
      · exact ih _ r h
    · rename_i hall
      rcases List.mem_cons.1 h with e | h
      · obtain ⟨r', hr', hn⟩ := List.all_eq_false.1 (Bool.eq_false_iff.2 hall)
        refine ⟨r', mem_selectIndep rs acc r' hr', .inr ?_⟩
        rw [e]
        exact fun hd => hn (decide_eq_true hd)
      · exact ih _ r h

/-- **A round fires every active pair**: an agent that was in an active pair
is no longer there after the round. -/
theorem XNet.parStep_fires_all {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {a b : Id}
    {α β : S} {R : Rhs S} (r : Redex xs.sys X.toNet a b α β R) (γ : S) :
    ¬ (X.parStep xs).1.toNet.agent a γ := by
  have hI := XNet.redexes_indep xs X
  obtain ⟨e, -⟩ := XNet.fireList_toNet hX hI
  cases ht : X.redexAt xs a α with
  | none => exact absurd ht (XNet.redexAt_complete hX r)
  | some t =>
    have hmem : t ∈ X.redexes xs := List.mem_filterMap.2 ⟨(a, α), r.ha, ht⟩
    have hfst := XNet.redexAt_fst ht
    obtain ⟨a', b', α', β', R'⟩ := t
    have hfst' : a' = a := hfst
    subst hfst'
    obtain ⟨rt, -⟩ := XNet.redexAt_sound ht r.ha
    obtain ⟨⟨c, d, γ', δ', R''⟩, hr', hc⟩ := selectIndep_covers (X.redexes xs) [] _ hmem
    obtain ⟨rx', -⟩ := hI.redex _ hr'
    -- `a'` is one of the two agents of a selected pair
    have ha : a' = c ∨ a' = d := by
      rcases hc with e' | hc
      · exact .inl (congrArg (·.1) e').symm
      · by_cases h₁ : a' = c
        · exact .inl h₁
        by_cases h₂ : a' = d
        · exact .inr h₂
        by_cases h₃ : b' = c
        · subst h₃
          obtain ⟨R₂, rt', -⟩ := rt.flip hX.1
          exact .inr (rt'.partner_unique rx' hX.1)
        by_cases h₄ : b' = d
        · subst h₄
          obtain ⟨R₂, rt', -⟩ := rt.flip hX.1
          obtain ⟨R₃, rx'', -⟩ := rx'.flip hX.1
          exact .inl (rt'.partner_unique rx'' hX.1)
        exact absurd ⟨h₁, h₂, h₃, h₄⟩ hc
    intro hag
    have hag' : (X.fireList xs.sys.ar (selectIndep [] (X.redexes xs))).toNet.agent a' γ := hag
    rw [e] at hag'
    rcases hag' with ⟨-, hall⟩ | ⟨r'', hr'', o, j, e', -⟩
    · have h' := hall _ (List.mem_map.2 ⟨_, hr', rfl⟩)
      exact ha.elim h'.1 h'.2
    · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr''
      obtain ⟨rx₀, -⟩ := hI.redex r₀ hr₀
      exact (rx₀.site hX.1).not_used_child o j (e' ▸ .inl ⟨_, r.ha⟩)

/-- Repeat `parStep` for at most `n` rounds.  Returns the net reached and
the total number of pairs fired. -/
def XNet.parRun (xs : XSys S) : Nat → XNet S → XNet S × Nat
  | 0, X => (X, 0)
  | n + 1, X =>
    if (X.parStep xs).2 = 0 then (X, 0)
    else ((XNet.parRun xs n (X.parStep xs).1).1,
      (X.parStep xs).2 + (XNet.parRun xs n (X.parStep xs).1).2)

theorem XNet.parRun_steps {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) (n : Nat) :
    Steps (CStep xs.sys) (X.parRun xs n).2 X.toNet (X.parRun xs n).1.toNet ∧
      (X.parRun xs n).1.Ok xs.sys.ar := by
  induction n generalizing X with
  | zero => exact ⟨.refl _, hX⟩
  | succ n ih =>
    unfold XNet.parRun
    split
    · exact ⟨.refl _, hX⟩
    · obtain ⟨st, hX'⟩ := XNet.parStep_spec hX
      obtain ⟨sts, hok⟩ := ih hX'
      exact ⟨st.trans sts, hok⟩

/-- **The two reducers agree**: when both have stopped, firing all active
pairs at once and firing one pair at a time have reached the same net, in the
same number of steps. -/
theorem XNet.parRun_eq_run {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {n n' : Nat}
    (h : (X.run xs n).1.step xs = none) (h' : (X.parRun xs n').1.step xs = none) :
    (X.parRun xs n').1.toNet = (X.run xs n).1.toNet ∧ (X.parRun xs n').2 = (X.run xs n).2 := by
  obtain ⟨-, hb⟩ := XNet.run_normal hX n h
  obtain ⟨sts', hok'⟩ := XNet.parRun_steps hX n'
  exact (hb sts').2 (XNet.step_complete hok' h')

/-- The parallel reducer stops before its rounds run out, or it has fired at
least one pair in every round. -/
theorem XNet.parRun_stop_or_full (xs : XSys S) (X : XNet S) (n : Nat) :
    (X.parRun xs n).1.step xs = none ∨ n ≤ (X.parRun xs n).2 := by
  induction n generalizing X with
  | zero => exact .inr (Nat.le_refl 0)
  | succ n ih =>
    unfold XNet.parRun
    split
    · rename_i h0
      exact .inl (XNet.parStep_zero_iff.1 h0)
    · rename_i h0
      rcases ih (X.parStep xs).1 with h | h
      · exact .inl h
      · refine .inr ?_
        show n + 1 ≤ (X.parStep xs).2 + (XNet.parRun xs n (X.parStep xs).1).2
        omega

/-- **Completeness of the parallel reducer**: if the input has a normal form
`C`, reached in `k` steps by some reduction, then `k` rounds are enough: the
parallel reducer stops on a net that stands for `C`, having fired exactly
`k` pairs. -/
theorem XNet.parRun_complete {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {k n : Nat}
    {C : Net S} (hC : Steps (CStep xs.sys) k X.toNet C) (hn : Normal (CStep xs.sys) C)
    (hk : k ≤ n) :
    (X.parRun xs n).1.step xs = none ∧ (X.parRun xs n).2 = k ∧
      (X.parRun xs n).1.toNet = C := by
  obtain ⟨sts, hY⟩ := XNet.parRun_steps hX n
  obtain ⟨hle, rest⟩ := (cstrongConfluent xs.sys).bounded hX.1 hC hn sts
  have stop : (X.parRun xs n).1.step xs = none := by
    rcases XNet.parRun_stop_or_full xs X n with h | h
    · exact h
    · have e : k - (X.parRun xs n).2 = 0 := by omega
      rw [e] at rest
      cases rest
      exact XNet.step_none_of_normal hY hn
  obtain ⟨e₁, e₂⟩ := cnormal_form_unique hX.1 hC sts hn (XNet.step_complete hY stop)
  exact ⟨stop, e₂.symm, e₁.symm⟩

/-! ### The reducer and the names of agents -/

/-- Rename the agents of a finite net. -/
def XNet.map (f : Id → Id) (X : XNet S) : XNet S where
  agents := X.agents.map fun e => (f e.1, e.2)
  free := X.free.map (mapPort f)
  wires := X.wires.map fun e => (mapPort f e.1, mapPort f e.2)

theorem XNet.map_toNet (f : Id → Id) (X : XNet S) : (X.map f).toNet = X.toNet.map f := by
  apply Net.ext'
  · intro i γ
    show (i, γ) ∈ X.agents.map (fun e => (f e.1, e.2)) ↔ ∃ i', i = f i' ∧ (i', γ) ∈ X.agents
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨i', γ'⟩, h, e⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨i', rfl, h⟩
    · rintro ⟨i', rfl, h⟩
      exact ⟨(i', γ), h, rfl⟩
  · intro p q
    show (p, q) ∈ X.wires.map (fun e => (mapPort f e.1, mapPort f e.2)) ↔
      ∃ p' q', p = mapPort f p' ∧ q = mapPort f q' ∧ (p', q') ∈ X.wires
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨p', q'⟩, h, e⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨p', q', rfl, rfl, h⟩
    · rintro ⟨p', q', rfl, rfl, h⟩
      exact ⟨(p', q'), h, rfl⟩
  · intro p
    show p ∈ X.free.map (mapPort f) ↔ ∃ p', p = mapPort f p' ∧ p' ∈ X.free
    rw [List.mem_map]
    constructor
    · rintro ⟨p', h, rfl⟩
      exact ⟨p', rfl, h⟩
    · rintro ⟨p', rfl, h⟩
      exact ⟨p', h, rfl⟩

theorem XNet.run_le (xs : XSys S) (X : XNet S) (n : Nat) : (X.run xs n).2 ≤ n := by
  induction n generalizing X with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    unfold XNet.run
    split
    · exact Nat.zero_le _
    · rename_i X' hs
      exact Nat.succ_le_succ (ih X')

/-- A renamed input of the reducer is a valid input. -/
theorem XNet.Ok.map {ar : S → Nat} {f : Id → Id} {X : XNet S} (hX : X.Ok ar)
    (hf : Renaming f X.toNet) :
    (X.map f).Ok ar := by
  show (X.map f).toNet.WF ar ∧ (X.map f).toNet.compact ar = (X.map f).toNet
  rw [XNet.map_toNet]
  exact ⟨hf.wf_map hX.1, by rw [hf.compact_map hX.1, hX.2]⟩

/-- **The reducer does not depend on the names of the agents.**  If it
stops on an input, it stops on every renamed input after the same number of
steps, and the net it returns is a renaming of the net it returned, by a
renaming that agrees with the given one on the interface. -/
theorem XNet.run_map {xs : XSys S} {X : XNet S} {f : Id → Id} (hX : X.Ok xs.sys.ar)
    (hf : Renaming f X.toNet) {n : Nat} (h : (X.run xs n).1.step xs = none) :
    ((X.map f).run xs n).1.step xs = none ∧ ((X.map f).run xs n).2 = (X.run xs n).2 ∧
      ∃ g, Renaming g (X.run xs n).1.toNet ∧ (∀ p ∈ X.free, g p.1 = f p.1) ∧
        ((X.map f).run xs n).1.toNet = (X.run xs n).1.toNet.map g := by
  obtain ⟨sts, hXn⟩ := XNet.run_steps hX n
  have hn := XNet.step_complete hXn h
  obtain ⟨g, hg, e, sts'⟩ := Steps.cmap hX.1 hf sts
  have hn' : Normal (CStep xs.sys) ((X.run xs n).1.toNet.map g) := by
    intro D s
    obtain ⟨C', s'⟩ := CStep.of_map hXn.1 hg s
    exact hn C' s'
  rw [← XNet.map_toNet f X] at sts'
  obtain ⟨stop, e₁, e₂⟩ := XNet.run_complete (hX.map hf) sts' hn' (XNet.run_le xs X n)
  exact ⟨stop, e₁, g, hg, fun p hp => e p hp, e₂⟩

/-! ### Reductions of executable systems as concurrent executions -/

/-- The rules of an executable system are finite. -/
theorem XSys.fin (xs : XSys S) {α β : S} {R : Rhs S} (h : xs.sys.rule α β = some R) :
    R.Fin := by
  have hwf := xs.sys.rule_wf h
  rw [xs.rule_spec] at h
  cases hx : xs.rule α β with
  | none =>
    rw [hx] at h
    cases h
  | some R₀ =>
    rw [hx] at h
    obtain rfl := Option.some.inj h
    refine ⟨R₀.slots,
      ((List.range (xs.sys.ar α)).map (LPort.ifc false) ++
        (List.range (xs.sys.ar β)).map (LPort.ifc true) ++
        R₀.newPorts xs.sys.ar).filterMap fun x => (R₀.wire x).map fun y => (x, y),
      fun o j γ hl => xs.slots_spec hx hl, ?_⟩
    intro x y hxy
    have hv := hwf.valid hxy
    have hw : R₀.wire x = some y := hxy
    refine List.mem_filterMap.2 ⟨x, ?_, by simp [hw]⟩
    cases x with
    | ifc s k =>
      cases s
      · exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨k, List.mem_range.2 hv, rfl⟩))
      · exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.2 ⟨k, List.mem_range.2 hv, rfl⟩))
    | new o j k =>
      obtain ⟨γ, hγ, hk⟩ := hv
      exact List.mem_append_right _
        (XRhs.mem_newPorts.2 ⟨o, j, k, γ, rfl, xs.slots_spec hx hγ, hγ, hk⟩)

/-- Every reduction of an executable system is a concurrent execution. -/
theorem XSys.steps_run (xs : XSys S) {n : Nat} {N N' : Net S} (hN : N.WF xs.sys.ar)
    (h : Steps (Step xs.sys) n N N') : Run xs.sys n ⟨N, N⟩ ⟨N', N'⟩ :=
  Steps.run (fun h => xs.fin h) hN h

/-- The machine can perform every reduction of an executable system. -/
theorem XSys.steps_mrun (xs : XSys S) {n : Nat} {N N' : Net S}
    (h : Steps (Step xs.sys) n N N') : MRun xs.sys n (Mach.init N) (Mach.init N') :=
  Steps.mrun (fun h => xs.fin h) h

/-- From every state that the machine can get into on an executable system,
the normal form is within reach. -/
theorem XSys.mrun_complete (xs : XSys S) {n k : Nat} {N N' : Net S} {M : Mach S}
    (hN : N.WF xs.sys.ar) (hs : Steps (Step xs.sys) n N N') (hn : Normal (Step xs.sys) N')
    (hr : MRun xs.sys k (Mach.init N) M) :
    ∃ M', MRun xs.sys (n - k) M M' ∧ M'.Quiet ∧ M'.mem = N' :=
  MRun.complete (fun h => xs.fin h) hN hs hn hr

/-- A net reached from the input of the list reducer in as many compact
steps as the reducer took is the net that the reducer returned. -/
theorem XNet.run_agree {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) (n : Nat)
    (stop : (X.run xs n).1.step xs = none) {C : Net S}
    (hC : Steps (CStep xs.sys) (X.run xs n).2 X.toNet C) : C = (X.run xs n).1.toNet := by
  obtain ⟨sts, -⟩ := XNet.run_steps hX n
  have hn := (XNet.run_normal hX n stop).1
  obtain ⟨-, rest⟩ := (cstrongConfluent xs.sys).bounded hX.1 sts hn hC
  rw [Nat.sub_self] at rest
  cases rest
  rfl

end INet
