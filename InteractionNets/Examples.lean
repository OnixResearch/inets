import InteractionNets.RoundByRound

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### Systems as data

A right-hand side given as two finite tables, and a system given as a
finite table of right-hand sides.  An executable check establishes
everything `System` and `XSys` ask for, so a system defined this way needs
no proof beyond evaluating the check. -/

/-- A right-hand side as data: the new agents with their symbols, and for
every port the port at the other end of its wire. -/
structure RuleData (S : Type) where
  agents : List ((Option Bool × Nat) × S)
  wires : List (LPort × LPort)

/-- Build a right-hand side from a list of wires, each given once. -/
def RuleData.ofWires (agents : List ((Option Bool × Nat) × S)) (ws : List (LPort × LPort)) :
    RuleData S :=
  ⟨agents, ws ++ ws.map fun e => (e.2, e.1)⟩

/-- The executable right-hand side it stands for. -/
def RuleData.toX (D : RuleData S) : XRhs S where
  lab o j := assoc (o, j) D.agents
  wire x := assoc x D.wires
  slots := D.agents.map (·.1)

/-- The mirror image. -/
def RuleData.swap (D : RuleData S) : RuleData S where
  agents := D.agents.map fun e => ((flipOwner e.1.1, e.1.2), e.2)
  wires := D.wires.map fun e => (e.1.swap, e.2.swap)

/-- The ports of a right-hand side for `α ⋈ β`. -/
def RuleData.ports (ar : S → Nat) (α β : S) (D : RuleData S) : List LPort :=
  ifcPorts ar α β ++
    D.agents.flatMap fun e => (List.range (ar e.2 + 1)).map (.new e.1.1 e.1.2)

theorem RuleData.mem_ports {ar : S → Nat} {α β : S} {D : RuleData S} {x : LPort} :
    x ∈ D.ports ar α β ↔
      (∃ s k, x = .ifc s k ∧ k < ar (sel α β s)) ∨
        ∃ o j k γ, x = .new o j k ∧ ((o, j), γ) ∈ D.agents ∧ k ≤ ar γ := by
  unfold RuleData.ports
  rw [List.mem_append, mem_ifcPorts, List.mem_flatMap]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨⟨⟨o, j⟩, γ⟩, he, hx⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact ⟨o, j, k, γ, rfl, he, Nat.le_of_lt_succ (List.mem_range.1 hk)⟩
  · rintro ⟨o, j, k, γ, rfl, he, hk⟩
    exact ⟨((o, j), γ), he, List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩⟩

/-- The executable check that a right-hand side is one for `α ⋈ β`. -/
def RuleData.checkWF [DecidableEq S] (ar : S → Nat) (α β : S) (D : RuleData S) : Bool :=
  D.agents.all (fun e => decide (assoc e.1 D.agents = some e.2)) &&
  D.wires.all (fun e => decide (assoc e.1 D.wires = some e.2)) &&
  D.wires.all (fun e => decide ((e.2, e.1) ∈ D.wires)) &&
  D.wires.all (fun e => decide (e.1 ≠ e.2)) &&
  D.wires.all (fun e => decide (e.1 ∈ D.ports ar α β)) &&
  (D.ports ar α β).all (fun x => (assoc x D.wires).isSome)

/-- No entry of the two tables is shadowed by an earlier entry with the
same key. -/
def RuleData.Clean (D : RuleData S) : Prop :=
  (∀ e ∈ D.agents, assoc e.1 D.agents = some e.2) ∧ ∀ e ∈ D.wires, assoc e.1 D.wires = some e.2

theorem RuleData.mem_ports_iff_valid {ar : S → Nat} {α β : S} {D : RuleData S}
    (h₁ : ∀ e ∈ D.agents, assoc e.1 D.agents = some e.2) (x : LPort) :
    x ∈ D.ports ar α β ↔ (Rhs.ofWire D.toX.lab D.toX.wire).Valid ar α β x := by
  rw [RuleData.mem_ports]
  cases x with
  | ifc s k =>
    constructor
    · rintro (⟨s', k', e, hk⟩ | ⟨o, j, k', γ, e, -, -⟩)
      · cases e
        exact hk
      · cases e
    · exact fun hk => .inl ⟨s, k, rfl, hk⟩
  | new o j k =>
    constructor
    · rintro (⟨s', k', e, -⟩ | ⟨o', j', k', γ, e, he, hk⟩)
      · cases e
      · cases e
        exact ⟨γ, h₁ _ he, hk⟩
    · rintro ⟨γ, hl, hk⟩
      exact .inr ⟨o, j, k, γ, rfl, assoc_mem hl, hk⟩

theorem RuleData.checkWF_sound [DecidableEq S] {ar : S → Nat} {α β : S} {D : RuleData S}
    (h : D.checkWF ar α β = true) : D.Clean ∧ D.toX.toRhs.WF ar α β := by
  simp only [RuleData.checkWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := h
  refine ⟨⟨h₁, h₂⟩, ?_⟩
  show (Rhs.ofWire D.toX.lab D.toX.wire).WF ar α β
  apply Rhs.ofWire_wf
  · intro x y hw
    exact h₂ (y, x) (h₃ (x, y) (assoc_mem hw))
  · intro x hw
    exact h₄ (x, x) (assoc_mem hw) rfl
  · intro x
    rw [← RuleData.mem_ports_iff_valid h₁]
    constructor
    · intro hs
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
      exact h₅ (x, y) (assoc_mem hy)
    · exact fun hx => h₆ x hx

/-- The check accepts every clean table that is a right-hand side. -/
theorem RuleData.checkWF_complete [DecidableEq S] {ar : S → Nat} {α β : S} {D : RuleData S}
    (hc : D.Clean) (h : D.toX.toRhs.WF ar α β) : D.checkWF ar α β = true := by
  have hw : (Rhs.ofWire D.toX.lab D.toX.wire).WF ar α β := h
  have link : ∀ {x y : LPort}, (x, y) ∈ D.wires →
      (Rhs.ofWire D.toX.lab D.toX.wire).link x y := fun he => hc.2 _ he
  simp only [RuleData.checkWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hc.1, hc.2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rintro ⟨x, y⟩ he
    exact assoc_mem (hw.symm (link he))
  · rintro ⟨x, y⟩ he hxy
    have hxy' : x = y := hxy
    subst hxy'
    exact hw.irrefl (link he)
  · rintro ⟨x, y⟩ he
    exact (RuleData.mem_ports_iff_valid hc.1 x).2 (hw.valid (link he))
  · intro x hx
    obtain ⟨y, hy⟩ := hw.total ((RuleData.mem_ports_iff_valid hc.1 x).1 hx)
    exact Option.isSome_iff_exists.2 ⟨y, hy⟩

/-- The executable check that `D'` is the mirror image of `D`. -/
def RuleData.checkMirror [DecidableEq S] (D D' : RuleData S) : Bool :=
  D'.agents.all (fun e => decide (assoc (flipOwner e.1.1, e.1.2) D.agents = some e.2)) &&
  D.agents.all (fun e => decide (assoc (flipOwner e.1.1, e.1.2) D'.agents = some e.2)) &&
  D'.wires.all (fun e => decide (assoc e.1.swap D.wires = some e.2.swap)) &&
  D.wires.all (fun e => decide (assoc e.1.swap D'.wires = some e.2.swap))

theorem RuleData.checkMirror_sound [DecidableEq S] {D D' : RuleData S}
    (h : D.checkMirror D' = true) : D.toX.toRhs.Mirror D'.toX.toRhs := by
  simp only [RuleData.checkMirror, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  constructor
  · intro o j
    show assoc (o, j) D'.agents = assoc (flipOwner o, j) D.agents
    cases h' : assoc (o, j) D'.agents with
    | some γ => exact (h₁ _ (assoc_mem h')).symm
    | none =>
      cases hd : assoc (flipOwner o, j) D.agents with
      | none => rfl
      | some γ =>
        have e : assoc (flipOwner (flipOwner o), j) D'.agents = some γ := h₂ _ (assoc_mem hd)
        rw [flipOwner_flipOwner, h'] at e
        cases e
  · intro x y
    show assoc x D'.wires = some y ↔ assoc x.swap D.wires = some y.swap
    constructor
    · exact fun hw => h₃ _ (assoc_mem hw)
    · intro hw
      have e : assoc x.swap.swap D'.wires = some y.swap.swap := h₄ _ (assoc_mem hw)
      simpa using e

/-- The check accepts the mirror image of a clean table whenever it is
clean. -/
theorem RuleData.checkMirror_complete [DecidableEq S] {D D' : RuleData S}
    (hc : D.Clean) (hc' : D'.Clean) (h : D.toX.toRhs.Mirror D'.toX.toRhs) :
    D.checkMirror D' = true := by
  have hl : ∀ o j, assoc (o, j) D'.agents = assoc (flipOwner o, j) D.agents := h.1
  have hw : ∀ x y, assoc x D'.wires = some y ↔ assoc x.swap D.wires = some y.swap := h.2
  simp only [RuleData.checkMirror, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro ⟨⟨o, j⟩, γ⟩ he
    exact (hl o j).symm.trans (hc'.1 _ he)
  · rintro ⟨⟨o, j⟩, γ⟩ he
    have e := hl (flipOwner o) j
    rw [flipOwner_flipOwner] at e
    exact e.trans (hc.1 _ he)
  · rintro ⟨x, y⟩ he
    exact (hw x y).1 (hc'.2 _ he)
  · rintro ⟨x, y⟩ he
    have e : assoc x.swap.swap D.wires = some y.swap.swap := by
      simpa using hc.2 _ he
    exact (hw x.swap y.swap).2 e

/-- An interaction system as data: the arities, and a table of right-hand
sides indexed by ordered pairs of symbols. -/
structure SysData (S : Type) where
  ar : S → Nat
  rules : List ((S × S) × RuleData S)

/-- The right-hand side for `α ⋈ β`, if there is one. -/
def SysData.rule [DecidableEq S] (D : SysData S) (α β : S) : Option (RuleData S) :=
  assoc (α, β) D.rules

/-- The executable check of a system: every right-hand side is one for its
pair of symbols, and the table holds its mirror image for the reversed
pair. -/
def SysData.check [DecidableEq S] (D : SysData S) : Bool :=
  D.rules.all fun e =>
    e.2.checkWF D.ar e.1.1 e.1.2 &&
      match assoc (e.1.2, e.1.1) D.rules with
      | some R' => e.2.checkMirror R'
      | none => false

theorem SysData.check_entry [DecidableEq S] {D : SysData S} (h : D.check = true) {α β : S}
    {R : RuleData S} (hr : D.rule α β = some R) :
    R.checkWF D.ar α β = true ∧ ∃ R', D.rule β α = some R' ∧ R.checkMirror R' = true := by
  have hm : ((α, β), R) ∈ D.rules := assoc_mem hr
  have ha := List.all_eq_true.1 h _ hm
  dsimp only at ha
  rw [Bool.and_eq_true] at ha
  obtain ⟨h₁, h₂⟩ := ha
  refine ⟨h₁, ?_⟩
  cases hr' : assoc (β, α) D.rules with
  | none =>
    rw [hr'] at h₂
    cases h₂
  | some R' =>
    rw [hr'] at h₂
    exact ⟨R', hr', h₂⟩

/-- The interaction system described by checked data. -/
def SysData.toSystem [DecidableEq S] (D : SysData S) (h : D.check = true) : System S where
  ar := D.ar
  rule α β := (D.rule α β).map fun R => R.toX.toRhs
  rule_wf := by
    intro α β R hr
    cases hd : D.rule α β with
    | none =>
      rw [hd] at hr
      cases hr
    | some R₀ =>
      rw [hd] at hr
      obtain rfl := Option.some.inj hr
      exact (RuleData.checkWF_sound (D.check_entry h hd).1).2
  rule_symm := by
    intro α β R hr
    cases hd : D.rule α β with
    | none =>
      rw [hd] at hr
      cases hr
    | some R₀ =>
      rw [hd] at hr
      obtain rfl := Option.some.inj hr
      obtain ⟨R', hr', hm⟩ := (D.check_entry h hd).2
      exact ⟨R'.toX.toRhs, by rw [hr']; rfl, RuleData.checkMirror_sound hm⟩

/-- The executable system described by checked data.  The only proof it
takes is the evaluation of the check. -/
def SysData.toXSys [DecidableEq S] (D : SysData S) (h : D.check = true) : XSys S where
  sys := D.toSystem h
  rule α β := (D.rule α β).map RuleData.toX
  rule_spec := by
    intro α β
    show (D.rule α β).map _ = ((D.rule α β).map _).map _
    cases D.rule α β <;> rfl
  slots_spec := by
    intro α β R o j γ hR hl
    cases hd : D.rule α β with
    | none =>
      rw [hd] at hR
      cases hR
    | some R₀ =>
      rw [hd] at hR
      obtain rfl := Option.some.inj hR
      exact List.mem_map.2 ⟨((o, j), γ), assoc_mem hl, rfl⟩

/-- **What the check of a system accepts**: exactly the tables in which
every right-hand side is clean, is a right-hand side for its pair of
symbols, and has its mirror image listed for the reversed pair. -/
theorem SysData.check_iff [DecidableEq S] {D : SysData S} :
    D.check = true ↔
      ∀ e ∈ D.rules, e.2.Clean ∧ e.2.toX.toRhs.WF D.ar e.1.1 e.1.2 ∧
        ∃ R', D.rule e.1.2 e.1.1 = some R' ∧ e.2.toX.toRhs.Mirror R'.toX.toRhs := by
  constructor
  · rintro h ⟨⟨α, β⟩, R⟩ he
    have ha := List.all_eq_true.1 h _ he
    dsimp only at ha
    rw [Bool.and_eq_true] at ha
    obtain ⟨h₁, h₂⟩ := ha
    obtain ⟨hc, hwf⟩ := RuleData.checkWF_sound h₁
    refine ⟨hc, hwf, ?_⟩
    cases hr' : assoc (β, α) D.rules with
    | none =>
      rw [hr'] at h₂
      cases h₂
    | some R' =>
      rw [hr'] at h₂
      exact ⟨R', hr', RuleData.checkMirror_sound h₂⟩
  · intro h
    unfold SysData.check
    rw [List.all_eq_true]
    rintro ⟨⟨α, β⟩, R⟩ he
    obtain ⟨hc, hwf, R', hr, hm⟩ := h _ he
    have hc' : R'.Clean := (h _ (assoc_mem hr)).1
    have hr' : assoc (β, α) D.rules = some R' := hr
    dsimp only
    rw [Bool.and_eq_true, hr']
    exact ⟨RuleData.checkWF_complete hc hwf, RuleData.checkMirror_complete hc hc' hm⟩

/-- Build a finite net from a list of wires, each given once. -/
def XNet.ofWires (agents : List (Id × S)) (free : List Port) (ws : List (Port × Port)) :
    XNet S :=
  ⟨agents, free, ws ++ ws.map fun e => (e.2, e.1)⟩

/-! ## Example: Lafont's interaction combinators -/

/-- The three interaction combinators. -/
inductive Comb
  | γ | δ | ε
  deriving DecidableEq, Repr

namespace Comb

/-- `γ` and `δ` are binary, `ε` is nullary. -/
def ar : Comb → Nat
  | γ => 2
  | δ => 2
  | ε => 0

@[simp] theorem ar_γ : ar γ = 2 := rfl
@[simp] theorem ar_δ : ar δ = 2 := rfl
@[simp] theorem ar_ε : ar ε = 0 := rfl

/-- Annihilation of two binary agents.  In terms of port numbers the
auxiliary ports are wired straight for `δ ⋈ δ` (first to first) and with a
twist for `γ ⋈ γ` (first to second). -/
def annWire (twist : Bool) : LPort → Option LPort
  | .ifc s k => if k < 2 then some (.ifc (!s) (if twist then 1 - k else k)) else none
  | .new _ _ _ => none

/-- Erasure of a binary agent by `ε`: one `ε` on each auxiliary port. -/
def eraLab : Option Bool → Nat → Option Comb
  | some false, j => if j < 2 then some ε else none
  | _, _ => none

def eraWire : LPort → Option LPort
  | .ifc false k => if k < 2 then some (.new (some false) k 0) else none
  | .new (some false) j 0 => if j < 2 then some (.ifc false j) else none
  | _ => none

/-- Commutation `γ ⋈ δ`: two `δ` on the auxiliary ports of `γ`, two `γ` on
those of `δ`, fully cross-wired. -/
def comLab : Option Bool → Nat → Option Comb
  | some s, j => if j < 2 then some (if s then γ else δ) else none
  | none, _ => none

def comWire : LPort → Option LPort
  | .ifc s k => if k < 2 then some (.new (some s) k 0) else none
  | .new (some s) j 0 => if j < 2 then some (.ifc s j) else none
  | .new (some s) j (k + 1) =>
      if j < 2 ∧ k < 2 then some (.new (some (!s)) k (j + 1)) else none
  | .new none _ _ => none

/-- A right-hand side without agents. -/
def noLab : Option Bool → Nat → Option Comb := fun _ _ => none

/-- Annihilation of two binary agents. -/
def rAnn (twist : Bool) : Rhs Comb := Rhs.ofWire noLab (annWire twist)
/-- `ε ⋈ ε`: the empty net. -/
def rEps : Rhs Comb := Rhs.ofWire noLab (fun _ => none)
/-- Erasure of a binary agent (on the left) by `ε` (on the right). -/
def rEra : Rhs Comb := Rhs.ofWire eraLab eraWire
/-- Commutation of `γ` (on the left) with `δ` (on the right). -/
def rCom : Rhs Comb := Rhs.ofWire comLab comWire

theorem rAnn_wf (twist : Bool) {α : Comb} (hα : ar α = 2) : (rAnn twist).WF ar α α := by
  apply Rhs.ofWire_wf
  · intro x y h
    cases x with
    | ifc s k =>
      simp only [annWire] at h
      split at h
      · cases h
        cases twist <;> simp [annWire] <;> omega
      · cases h
    | new s j k => cases h
  · intro x h
    cases x with
    | ifc s k =>
      simp only [annWire] at h
      split at h
      · cases s <;> simp at h
      · cases h
    | new s j k => cases h
  · intro x
    cases x with
    | ifc s k => cases s <;> simp [annWire, Rhs.Valid, hα]
    | new s j k => simp [annWire, Rhs.Valid, Rhs.ofWire, noLab]

theorem rAnn_mirror (twist : Bool) : (rAnn twist).Mirror (rAnn twist) := by
  apply Rhs.ofWire_mirror (fun _ _ => rfl)
  intro x
  cases x with
  | ifc s k => simp only [annWire, LPort.swap]; split <;> simp [LPort.swap]
  | new s j k => rfl

theorem rEps_wf : rEps.WF ar ε ε := by
  apply Rhs.ofWire_wf
  · intro x y h; cases h
  · intro x h; cases h
  · intro x
    cases x with
    | ifc s k => cases s <;> simp [Rhs.Valid]
    | new s j k => simp [Rhs.Valid, Rhs.ofWire, noLab]

theorem rEps_mirror : rEps.Mirror rEps :=
  Rhs.ofWire_mirror (fun _ _ => rfl) (fun _ => rfl)

theorem rEra_wf {α : Comb} (hα : ar α = 2) : rEra.WF ar α ε := by
  apply Rhs.ofWire_wf
  · intro x y h
    unfold eraWire at h
    split at h
    · split at h
      · cases h; simp [eraWire, *]
      · cases h
    · split at h
      · cases h; simp [eraWire, *]
      · cases h
    · cases h
  · intro x h
    unfold eraWire at h
    split at h
    · split at h <;> cases h
    · split at h <;> cases h
    · cases h
  · intro x
    rcases x with ⟨_ | _, k⟩ | ⟨_ | ⟨_ | _⟩, j, _ | k⟩ <;>
      simp [eraWire, Rhs.Valid, Rhs.ofWire, eraLab, hα]

theorem rCom_wf : rCom.WF ar γ δ := by
  apply Rhs.ofWire_wf
  · intro x y h
    rcases x with ⟨s, k⟩ | ⟨_ | s, j, _ | k⟩ <;> simp only [comWire] at h <;>
      first
        | cases h
        | (split at h <;> cases h <;> simp [comWire, *])
  · intro x h
    rcases x with ⟨s, k⟩ | ⟨_ | s, j, _ | k⟩ <;> simp only [comWire] at h <;>
      first
        | cases h
        | (split at h <;> first | cases h | (cases s <;> simp at h))
  · intro x
    rcases x with ⟨_ | _, k⟩ | ⟨_ | ⟨_ | _⟩, j, _ | k⟩ <;>
      simp [comWire, Rhs.Valid, Rhs.ofWire, comLab]
    all_goals
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨_, ⟨h₁, rfl⟩, by simp; omega⟩
      · rintro ⟨_, ⟨h₁, rfl⟩, h₂⟩
        simp at h₂
        exact ⟨h₁, by omega⟩

/-- The interaction rules of the combinators: annihilation (`γ ⋈ γ`,
`δ ⋈ δ`, `ε ⋈ ε`), commutation (`γ ⋈ δ`) and erasure (`γ ⋈ ε`, `δ ⋈ ε`),
each given in both orientations. -/
def rule : Comb → Comb → Option (Rhs Comb)
  | γ, γ => some (rAnn true)
  | δ, δ => some (rAnn false)
  | ε, ε => some rEps
  | γ, δ => some rCom
  | δ, γ => some rCom.swap
  | γ, ε => some rEra
  | ε, γ => some rEra.swap
  | δ, ε => some rEra
  | ε, δ => some rEra.swap

/-- The interaction combinators form an interaction system. -/
def system : System Comb where
  ar := ar
  rule := rule
  rule_wf := by
    intro α β R h
    cases α <;> cases β <;> obtain rfl := Option.some.inj h
    · exact rAnn_wf true rfl
    · exact rCom_wf
    · exact rEra_wf rfl
    · exact rCom_wf.swap
    · exact rAnn_wf false rfl
    · exact rEra_wf rfl
    · exact (rEra_wf rfl).swap
    · exact (rEra_wf rfl).swap
    · exact rEps_wf
  rule_symm := by
    intro α β R h
    cases α <;> cases β <;> obtain rfl := Option.some.inj h
    · exact ⟨_, rfl, rAnn_mirror true⟩
    · exact ⟨_, rfl, Rhs.mirror_swap _⟩
    · exact ⟨_, rfl, Rhs.mirror_swap _⟩
    · exact ⟨_, rfl, Rhs.swap_mirror _⟩
    · exact ⟨_, rfl, rAnn_mirror false⟩
    · exact ⟨_, rfl, Rhs.mirror_swap _⟩
    · exact ⟨_, rfl, Rhs.swap_mirror _⟩
    · exact ⟨_, rfl, Rhs.swap_mirror _⟩
    · exact ⟨_, rfl, rEps_mirror⟩

/-- Reduction of interaction-combinator nets is strongly confluent. -/
theorem diamond {N N₁ N₂ : Net Comb} (hN : N.WF ar)
    (h₁ : Step system N N₁) (h₂ : Step system N N₂) :
    N₁ = N₂ ∨ ∃ N', Step system N₁ N' ∧ Step system N₂ N' :=
  Step.diamond hN h₁ h₂

/-- Reduction of interaction-combinator nets is confluent. -/
theorem confluence {N N₁ N₂ : Net Comb} {n m : Nat} (hN : N.WF ar)
    (h₁ : Steps (Step system) n N N₁) (h₂ : Steps (Step system) m N N₂) :
    ∃ N' k l, Steps (Step system) k N₁ N' ∧ Steps (Step system) l N₂ N' ∧ n + k = m + l :=
  INet.confluence hN h₁ h₂

/-! ### A concrete reduction

Two `γ` agents `[0]` and `[1]` facing each other, their auxiliary ports wired
to four free ports `f₂ … f₅` (the ports `([2], 0) … ([5], 0)`):

```
   f₂   f₃         f₄   f₅
     \ /             \ /
     γ[0] ───────── γ[1]
```
-/

/-- The wiring of the example net. -/
def ggWire : Port → Option Port
  | ([0], 0) => some ([1], 0)
  | ([1], 0) => some ([0], 0)
  | ([0], 1) => some ([2], 0)
  | ([2], 0) => some ([0], 1)
  | ([0], 2) => some ([3], 0)
  | ([3], 0) => some ([0], 2)
  | ([1], 1) => some ([4], 0)
  | ([4], 0) => some ([1], 1)
  | ([1], 2) => some ([5], 0)
  | ([5], 0) => some ([1], 2)
  | _ => none

/-- The example net. -/
def gg : Net Comb where
  agent i c := (i = [0] ∨ i = [1]) ∧ c = γ
  link p q := ggWire p = some q
  free p := p = ([2], 0) ∨ p = ([3], 0) ∨ p = ([4], 0) ∨ p = ([5], 0)

theorem gg_used {i : Id} (h : gg.Used i) : ∃ n, i = [n] := by
  rcases h with ⟨c, hi | hi, -⟩ | ⟨k, q, h⟩ | ⟨k, h | h | h | h⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · change ggWire (i, k) = some q at h
    unfold ggWire at h
    split at h <;> first | (rename_i e; exact ⟨_, (Prod.mk.inj e).1⟩) | cases h
  all_goals exact ⟨_, (Prod.mk.inj h).1⟩

theorem gg_wf : gg.WF ar where
  agent_fun := by
    rintro i α β ⟨-, rfl⟩ ⟨-, rfl⟩
    rfl
  symm := by
    intro p q h
    change ggWire p = some q at h
    change ggWire q = some p
    unfold ggWire at h
    split at h <;> cases h <;> rfl
  irrefl := by
    intro p h
    change ggWire p = some p at h
    unfold ggWire at h
    split at h <;> simp at h
  end_unique := fun {p q r} _ h h' =>
    Option.some.inj ((show ggWire p = some q from h).symm.trans h')
  end_conn := by
    have key : ∀ p q : Port, ggWire p = some q → gg.End ar q → q ≠ p →
        ∃ q, gg.End ar q ∧ q ≠ p ∧ gg.Conn ar p q :=
      fun p q hw hq hne => ⟨q, hq, hne, q, p, .single hw⟩
    have agentEnd : ∀ (i : Id) (k : Nat), i = [0] ∨ i = [1] → k ≤ 2 → gg.End ar (i, k) :=
      fun i k hi hk => .inr ⟨γ, ⟨hi, rfl⟩, hk⟩
    rintro ⟨i, k⟩ (h | ⟨c, ⟨hi, rfl⟩, hk⟩)
    · rcases h with h | h | h | h <;> cases h
      · exact key _ ([0], 1) rfl (agentEnd _ _ (.inl rfl) (by decide)) (by decide)
      · exact key _ ([0], 2) rfl (agentEnd _ _ (.inl rfl) (by decide)) (by decide)
      · exact key _ ([1], 1) rfl (agentEnd _ _ (.inr rfl) (by decide)) (by decide)
      · exact key _ ([1], 2) rfl (agentEnd _ _ (.inr rfl) (by decide)) (by decide)
    · dsimp only at hi hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by simp at hk; omega
      rcases hi with rfl | rfl <;> rcases hk' with rfl | rfl | rfl
      · exact key _ ([1], 0) rfl (agentEnd _ _ (.inr rfl) (by decide)) (by decide)
      · exact key _ ([2], 0) rfl (.inl (.inl rfl)) (by decide)
      · exact key _ ([3], 0) rfl (.inl (.inr (.inl rfl))) (by decide)
      · exact key _ ([0], 0) rfl (agentEnd _ _ (.inl rfl) (by decide)) (by decide)
      · exact key _ ([4], 0) rfl (.inl (.inr (.inr (.inl rfl)))) (by decide)
      · exact key _ ([5], 0) rfl (.inl (.inr (.inr (.inr rfl)))) (by decide)
  deg := fun {p x y z} h h' _ =>
    .inl (Option.some.inj ((show ggWire p = some x from h).symm.trans h'))
  free_agent := by
    rintro i k c (h | h | h | h) ⟨hi | hi, -⟩ <;> cases h <;> simp at hi
  fresh := by
    rintro a c l ⟨ha | ha, -⟩ hu <;> subst ha <;> obtain ⟨n, hn⟩ := gg_used hu <;>
      cases l with
      | nil => rfl
      | cons x l' => simp at hn

/-- The result of firing the active pair of `gg`. -/
def ggOut : Net Comb := gg.fire [0] [1] (rAnn true)

theorem gg_redex : Redex system gg [0] [1] γ γ (rAnn true) where
  ha := ⟨.inl rfl, rfl⟩
  hb := ⟨.inr rfl, rfl⟩
  ne := by decide
  conn := ⟨([1], 0), ([0], 0), .single rfl⟩
  rule := rfl

/-- `gg` reduces to `ggOut` in one step. -/
theorem gg_step : Step system gg ggOut :=
  ⟨[0], [1], γ, γ, rAnn true, gg_redex, rfl⟩

/-- No agent is left ... -/
theorem ggOut_no_agent (i : Id) (c : Comb) : ¬ ggOut.agent i c := by
  rintro (⟨⟨h | h, -⟩, h₀, h₁⟩ | ⟨s, j, -, hl⟩)
  · exact h₀ h
  · exact h₁ h
  · cases hl

/-- ... so the result is a normal form ... -/
theorem ggOut_normal : Normal (Step system) ggOut := by
  rintro N' ⟨a, b, α, β, R, r, -⟩
  exact ggOut_no_agent _ _ r.ha

/-- ... in which the free ports are wired together with a twist: `f₂ — f₅`
and `f₃ — f₄`.  Each wire runs through two former auxiliary ports. -/
theorem ggOut_conn :
    ggOut.Conn ar ([2], 0) ([5], 0) ∧ ggOut.Conn ar ([3], 0) ([4], 0) := by
  have site := gg_redex.site gg_wf
  have j₀ : ∀ k, ¬ ggOut.End ar ([0], k) := site.not_end_fire_sel false
  have j₁ : ∀ k, ¬ ggOut.End ar ([1], k) := site.not_end_fire_sel true
  refine ⟨⟨([0], 1), ([1], 2), ?_⟩, ⟨([0], 2), ([1], 1), ?_⟩⟩
  · refine .cons (.inl rfl) (j₀ 1) (w := ([1], 2)) (by decide) ?_
    refine .cons (.inr ⟨.ifc false 0, .ifc true 1, rfl, rfl, rfl⟩) (j₁ 2) (w := ([5], 0)) (by decide) ?_
    exact .single (.inl rfl)
  · refine .cons (.inl rfl) (j₀ 2) (w := ([1], 1)) (by decide) ?_
    refine .cons (.inr ⟨.ifc false 1, .ifc true 0, rfl, rfl, rfl⟩) (j₁ 1) (w := ([4], 0)) (by decide) ?_
    exact .single (.inl rfl)

/-- The compact form of the result consists of exactly those two wires: the
inert segment left by the two principal ports is gone, and each wire is one
segment. -/
theorem ggOut_compact (p q : Port) :
    (ggOut.compact ar).link p q ↔
      (p = ([2], 0) ∧ q = ([5], 0)) ∨ (p = ([5], 0) ∧ q = ([2], 0)) ∨
      (p = ([3], 0) ∧ q = ([4], 0)) ∨ (p = ([4], 0) ∧ q = ([3], 0)) := by
  have hW : ggOut.WF ar := Step.wf gg_wf gg_step
  have free : ∀ p, ggOut.End ar p → gg.free p := by
    rintro p (hf | ⟨c, hc, -⟩)
    · exact hf
    · exact absurd hc (ggOut_no_agent _ _)
  have e₂ : ggOut.End ar ([2], 0) := .inl (.inl rfl)
  have e₃ : ggOut.End ar ([3], 0) := .inl (.inr (.inl rfl))
  have e₄ : ggOut.End ar ([4], 0) := .inl (.inr (.inr (.inl rfl)))
  have e₅ : ggOut.End ar ([5], 0) := .inl (.inr (.inr (.inr rfl)))
  obtain ⟨c₂₅, c₃₄⟩ := ggOut_conn
  constructor
  · rintro ⟨hp, hq, c⟩
    rcases free p hp with rfl | rfl | rfl | rfl
    · exact .inl ⟨rfl, Net.Conn.det hW hp hq e₅ c c₂₅⟩
    · exact .inr (.inr (.inl ⟨rfl, Net.Conn.det hW hp hq e₄ c c₃₄⟩))
    · exact .inr (.inr (.inr ⟨rfl, Net.Conn.det hW hp hq e₃ c (c₃₄.symm hW)⟩))
    · exact .inr (.inl ⟨rfl, Net.Conn.det hW hp hq e₂ c (c₂₅.symm hW)⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨e₂, e₅, c₂₅⟩
    · exact ⟨e₅, e₂, c₂₅.symm hW⟩
    · exact ⟨e₃, e₄, c₃₄⟩
    · exact ⟨e₄, e₃, c₃₄.symm hW⟩

/-! ### The combinators, executably -/

def xAnn (twist : Bool) : XRhs Comb := ⟨noLab, annWire twist, []⟩
def xEps : XRhs Comb := ⟨noLab, fun _ => none, []⟩
def xEra : XRhs Comb := ⟨eraLab, eraWire, [(some false, 0), (some false, 1)]⟩
def xCom : XRhs Comb :=
  ⟨comLab, comWire, [(some false, 0), (some false, 1), (some true, 0), (some true, 1)]⟩

theorem xEra_slots {o : Option Bool} {j : Nat} {c : Comb} (hl : xEra.lab o j = some c) :
    (o, j) ∈ xEra.slots := by
  rcases o with _ | ⟨_ | _⟩ <;> rcases j with _ | _ | j <;> simp [xEra, eraLab] at hl ⊢
  exact absurd hl.1 (by omega)

theorem xCom_slots {o : Option Bool} {j : Nat} {c : Comb} (hl : xCom.lab o j = some c) :
    (o, j) ∈ xCom.slots := by
  rcases o with _ | ⟨_ | _⟩ <;> rcases j with _ | _ | j <;> simp [xCom, comLab] at hl ⊢
  all_goals exact absurd hl.1 (by omega)

/-- The rules of `Comb.rule`, executably. -/
def xrule : Comb → Comb → Option (XRhs Comb)
  | γ, γ => some (xAnn true)
  | δ, δ => some (xAnn false)
  | ε, ε => some xEps
  | γ, δ => some xCom
  | δ, γ => some xCom.swap
  | γ, ε => some xEra
  | ε, γ => some xEra.swap
  | δ, ε => some xEra
  | ε, δ => some xEra.swap

/-- An executable presentation of the interaction combinators. -/
def xsystem : XSys Comb where
  sys := system
  rule := xrule
  rule_spec := by
    intro α β
    cases α <;> cases β <;>
      first
        | rfl
        | exact congrArg some (XRhs.toRhs_swap xCom).symm
        | exact congrArg some (XRhs.toRhs_swap xEra).symm
  slots_spec := by
    intro α β R o j c hR hl
    cases α <;> cases β <;> obtain rfl := Option.some.inj hR
    · cases hl
    · exact xCom_slots hl
    · exact xEra_slots hl
    · exact XRhs.swap_slots xCom_slots hl
    · cases hl
    · exact xEra_slots hl
    · exact XRhs.swap_slots xEra_slots hl
    · exact XRhs.swap_slots xEra_slots hl
    · cases hl

/-- The net `gg` as data. -/
def xgg : XNet Comb where
  agents := [([0], γ), ([1], γ)]
  free := [([2], 0), ([3], 0), ([4], 0), ([5], 0)]
  wires := [(([0], 0), ([1], 0)), (([1], 0), ([0], 0)), (([0], 1), ([2], 0)),
    (([2], 0), ([0], 1)), (([0], 2), ([3], 0)), (([3], 0), ([0], 2)), (([1], 1), ([4], 0)),
    (([4], 0), ([1], 1)), (([1], 2), ([5], 0)), (([5], 0), ([1], 2))]

/-- Running the reducer on it: one step, after which it stops, leaving no
agent and the two wires `f₂ — f₅` and `f₃ — f₄`. -/
theorem xgg_run :
    xgg.run xsystem 10 =
      (⟨[], [([2], 0), ([3], 0), ([4], 0), ([5], 0)],
          [(([2], 0), ([5], 0)), (([3], 0), ([4], 0)), (([4], 0), ([3], 0)),
            (([5], 0), ([2], 0))]⟩, 1) := by
  decide

theorem xgg_link {p q : Port} : (p, q) ∈ xgg.wires ↔ ggWire p = some q := by
  constructor
  · intro h
    have all : ∀ e ∈ xgg.wires, ggWire e.1 = some e.2 := by decide
    exact all (p, q) h
  · intro h
    unfold ggWire at h
    split at h <;> first | (cases h; decide) | cases h

/-- The data `xgg` stands for the net `gg` ... -/
theorem xgg_toNet : xgg.toNet = gg := by
  apply Net.ext'
  · intro i c
    show (i, c) ∈ [([0], γ), ([1], γ)] ↔ (i = [0] ∨ i = [1]) ∧ c = γ
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    constructor
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨.inl h, rfl⟩
      · exact ⟨.inr h, rfl⟩
    · rintro ⟨h | h, rfl⟩
      · exact .inl ⟨h, rfl⟩
      · exact .inr ⟨h, rfl⟩
  · exact fun p q => xgg_link
  · intro p
    show p ∈ [([2], 0), ([3], 0), ([4], 0), ([5], 0)] ↔ _
    simp [gg]

theorem gg_wire_end {p q : Port} (h : ggWire p = some q) : gg.End ar p := by
  unfold ggWire at h
  split at h <;>
    first
      | exact .inr ⟨γ, ⟨.inl rfl, rfl⟩, by decide⟩
      | exact .inr ⟨γ, ⟨.inr rfl, rfl⟩, by decide⟩
      | exact .inl (.inl rfl)
      | exact .inl (.inr (.inl rfl))
      | exact .inl (.inr (.inr (.inl rfl)))
      | exact .inl (.inr (.inr (.inr rfl)))
      | cases h

/-- ... which is compact ... -/
theorem gg_compact : gg.compact ar = gg := by
  refine Net.ext' (fun _ _ => Iff.rfl) (fun p q => ⟨?_, ?_⟩) (fun _ => Iff.rfl)
  · rintro ⟨hp, hq, c⟩
    obtain ⟨q', hl⟩ := gg_wf.end_wired hp
    have hl' : ggWire p = some q' := hl
    obtain rfl := Net.Conn.det gg_wf hp hq (gg_wire_end (gg_wf.symm hl)) c ⟨q', p, .single hl⟩
    exact hl'
  · intro h
    have h' : ggWire p = some q := h
    exact ⟨gg_wire_end h', gg_wire_end (gg_wf.symm h), q, p, .single h⟩

/-- ... so the reducer's invariant holds for `xgg` ... -/
theorem xgg_ok : xgg.Ok ar := by
  unfold XNet.Ok
  rw [xgg_toNet]
  exact ⟨gg_wf, gg_compact⟩

/-- ... and what the reducer returned is the normal form of `gg` for
reduction without history: every reduction of `gg` has at most one step,
and every reduction to a normal form ends there. -/
theorem xgg_normal_form :
    Normal (CStep system) (xgg.run xsystem 10).1.toNet ∧
      ∀ {m : Nat} {C : Net Comb}, Steps (CStep system) m gg C →
        m ≤ 1 ∧ (Normal (CStep system) C → C = (xgg.run xsystem 10).1.toNet ∧ m = 1) := by
  have h := XNet.run_normal (xs := xsystem) xgg_ok 10 (by decide)
  have e : (xgg.run xsystem 10).2 = 1 := by rw [xgg_run]
  rw [xgg_toNet, e] at h
  exact h

/-- The same net with a `δ` in place of the second `γ`. -/
def xgd : XNet Comb := { xgg with agents := [([0], γ), ([1], δ)] }

/-- What a commutation should leave: two `δ` named after the `γ`, two `γ`
named after the `δ`, each on one of the four free wires, and fully
cross-wired. -/
def xgdOut : XNet Comb :=
  ⟨[([0, 0], δ), ([2, 0], δ), ([0, 1], γ), ([2, 1], γ)],
    [([2], 0), ([3], 0), ([4], 0), ([5], 0)],
    [(([0, 0], 0), ([2], 0)), (([2], 0), ([0, 0], 0)), (([2, 0], 0), ([3], 0)),
      (([3], 0), ([2, 0], 0)), (([0, 1], 0), ([4], 0)), (([4], 0), ([0, 1], 0)),
      (([2, 1], 0), ([5], 0)), (([5], 0), ([2, 1], 0)), (([0, 0], 1), ([0, 1], 1)),
      (([0, 0], 2), ([2, 1], 1)), (([2, 0], 1), ([0, 1], 2)), (([2, 0], 2), ([2, 1], 2)),
      (([0, 1], 1), ([0, 0], 1)), (([0, 1], 2), ([2, 0], 1)), (([2, 1], 1), ([0, 0], 2)),
      (([2, 1], 2), ([2, 0], 2))]⟩

/-- `normalize` validates `xgd`, runs it, and returns `xgdOut` after one
step.  Proved by evaluating `normalize` inside the kernel. -/
theorem xgd_normalize : xgd.normalize xsystem 10 = some (xgdOut, 1) := by
  decide

/-- Hence `xgdOut` is the normal form of `xgd`.  Nothing about `xgd` is
proved by hand. -/
theorem xgd_normal_form :
    Steps (CStep system) 1 xgd.toNet xgdOut.toNet ∧ Normal (CStep system) xgdOut.toNet ∧
      ∀ {m : Nat} {C : Net Comb}, Steps (CStep system) m xgd.toNet C →
        m ≤ 1 ∧ (Normal (CStep system) C → C = xgdOut.toNet ∧ m = 1) := by
  obtain ⟨-, -, h₁, h₂, h₃⟩ := XNet.normalize_spec xgd_normalize
  exact ⟨h₁, h₂, h₃⟩

/-- The invariant of `xgg`, proved by hand above, also follows by
evaluation. -/
example : xgg.Ok ar := by
  decide

/-- Two copies of `gg` side by side: two active pairs. -/
def xgg2 : XNet Comb :=
  XNet.ofWires [([0], γ), ([1], γ), ([6], γ), ([7], γ)]
    [([2], 0), ([3], 0), ([4], 0), ([5], 0), ([8], 0), ([9], 0), ([10], 0), ([11], 0)]
    [(([0], 0), ([1], 0)), (([0], 1), ([2], 0)), (([0], 2), ([3], 0)), (([1], 1), ([4], 0)),
      (([1], 2), ([5], 0)), (([6], 0), ([7], 0)), (([6], 1), ([8], 0)), (([6], 2), ([9], 0)),
      (([7], 1), ([10], 0)), (([7], 2), ([11], 0))]

/-- The parallel reducer fires both pairs in one round and is then done. -/
example :
    xgg2.Ok ar ∧ (xgg2.parStep xsystem).2 = 2 ∧
      (xgg2.parStep xsystem).1.step xsystem = none := by
  decide

/-- Exchange the numbers `0` and `1`. -/
def sw (n : Nat) : Nat := if n = 0 then 1 else if n = 1 then 0 else n

/-- The commutation example with its two agents renamed into each other
still normalizes in one step ... -/
example : ((xgd.map (List.map sw)).normalize xsystem 10).map (·.2) = some 1 := by
  decide

/-- ... but not to the relabelled result: the new agents are named after
the slots of the rule, which the relabelling does not respect. -/
example : (xgd.map (List.map sw)).normalize xsystem 10 ≠ some (xgdOut.map (List.map sw), 1) := by
  decide

theorem sw_inj {m n : Nat} (h : sw m = sw n) : m = n := by
  unfold sw at h
  repeat' split at h
  all_goals omega

/-- The net returned for the renamed input is a renaming of `xgdOut` all the
same. -/
theorem xgd_map_run :
    ∃ g, Renaming g xgdOut.toNet ∧
      ((xgd.map (List.map sw)).run xsystem 10).1.toNet = xgdOut.toNet.map g := by
  have hX : xgd.Ok ar := by decide
  have hr : (xgd.run xsystem 10).1 = xgdOut := by decide
  have hs : (xgd.run xsystem 10).1.step xsystem = none := by decide
  obtain ⟨-, -, g, hg, -, e⟩ := XNet.run_map hX (Renaming.relabel hX.1 sw_inj) hs
  rw [hr] at hg e
  exact ⟨g, hg, e⟩

/-- Two `γ` agents wired to each other on all three ports. -/
def xloop : XNet Comb :=
  XNet.ofWires [([0], γ), ([1], γ)] []
    [(([0], 0), ([1], 0)), (([0], 1), ([1], 2)), (([0], 2), ([1], 1))]

/-- The reducer annihilates them and returns the empty net ... -/
theorem xloop_normalize : xloop.normalize xsystem 10 = some (⟨[], [], []⟩, 1) := by
  decide

/-- ... although the firing closes wires onto themselves.  Each of them is a
single segment, doubled by the firing, so the segments of the net after the
firing show no cycle.  The count of dead components records the loops all
the same: there are more dead components than the one wire between the two
principal ports. -/
theorem xloop_loop :
    ∃ ℓ, 0 < ℓ ∧ (xloop.toNet.fire [0] [1] (rAnn true)).DeadCount ar (1 + ℓ) := by
  have hX : xloop.Ok ar := by decide
  have site : Site ar xloop.toNet [0] [1] γ γ :=
    ⟨hX.1, show ([0], γ) ∈ xloop.agents by decide, show ([1], γ) ∈ xloop.agents by decide,
      by decide, (hX.link_iff.1 (show (([0], 0), ([1], 0)) ∈ xloop.wires by decide)).2.2⟩
  exact site.loop_counted (system.rule_wf (show system.rule γ γ = some (rAnn true) from rfl))
    (s := false) (s' := true) (k := 0) (k' := 1) rfl
    (hX.link_iff.1 (show (([0], 1), ([1], 2)) ∈ xloop.wires by decide))
    (Net.WF.deadCount_compact hX.2)

/-- A number that the segments of `xloop`, before and after the firing,
never change: it tells the three wires apart. -/
def loopColour (p : Port) : Nat :=
  if p.1 = [0] then p.2 else if p.2 = 0 then 0 else 3 - p.2

/-- The count is exact: after the firing there are three dead components,
the wire between the principal ports and two loops. -/
theorem xloop_dead : (xloop.toNet.fire [0] [1] (rAnn true)).DeadCount ar 3 := by
  have hnoend : ∀ q, ¬ (xloop.toNet.fire [0] [1] (rAnn true)).End ar q := by
    rintro q (hf | ⟨c, ⟨hg, na, nb⟩ | ⟨o, j, -, hl⟩, -⟩)
    · exact absurd hf List.not_mem_nil
    · have hg' : (q.1, c) ∈ [(([0] : Id), γ), ([1], γ)] := hg
      rcases List.mem_cons.1 hg' with e | hg'
      · exact na (Prod.mk.inj e).1
      · rcases List.mem_cons.1 hg' with e | hg'
        · exact nb (Prod.mk.inj e).1
        · exact absurd hg' List.not_mem_nil
    · cases hl
  have hnew : ∀ {x y : LPort}, (rAnn true).link x y →
      ∃ s k, k < 2 ∧ x = .ifc s k ∧ y = .ifc (!s) (1 - k) := by
    intro x y hxy
    have hxy' : annWire true x = some y := hxy
    cases x with
    | ifc s k =>
      simp only [annWire] at hxy'
      split at hxy'
      · rename_i hk
        exact ⟨s, k, hk, rfl, (Option.some.inj hxy').symm⟩
      · cases hxy'
    | new o j k => cases hxy'
  have hcol : ∀ {p q : Port}, (xloop.toNet.fire [0] [1] (rAnn true)).link p q →
      loopColour p = loopColour q := by
    rintro p q (hl | ⟨x, y, hxy, rfl, rfl⟩)
    · have hall : ∀ e ∈ xloop.wires, loopColour e.1 = loopColour e.2 := by decide
      exact hall (p, q) hl
    · obtain ⟨s, k, hk, rfl, rfl⟩ := hnew hxy
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> cases s <;> rfl
  have hreach : ∀ {p q : Port}, (xloop.toNet.fire [0] [1] (rAnn true)).Reach p q →
      loopColour p = loopColour q := by
    intro p q h
    induction h with
    | refl => rfl
    | tail _ hl ih => exact ih.trans (hcol hl)
  have hrep : ∀ {p q : Port}, (xloop.toNet.fire [0] [1] (rAnn true)).link p q →
      ∃ r ∈ ([([0], 0), ([0], 1), ([0], 2)] : List Port), r = p ∨ (r, p) ∈ xloop.wires := by
    rintro p q (hl | ⟨x, y, hxy, rfl, rfl⟩)
    · have hall : ∀ e ∈ xloop.wires, ∃ r ∈ ([([0], 0), ([0], 1), ([0], 2)] : List Port),
          r = e.1 ∨ (r, e.1) ∈ xloop.wires := by decide
      exact hall (p, q) hl
    · obtain ⟨s, k, hk, rfl, rfl⟩ := hnew hxy
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> cases s <;> decide
  refine ⟨[([0], 0), ([0], 1), ([0], 2)], rfl, ?_, ?_, ?_⟩
  · intro p hp
    have hall : ∀ p ∈ ([([0], 0), ([0], 1), ([0], 2)] : List Port), ∃ e ∈ xloop.wires, e.1 = p := by
      decide
    obtain ⟨e, he, rfl⟩ := hall p hp
    exact ⟨⟨e.2, .inl he⟩, fun q _ => hnoend q⟩
  · have hne : ∀ p ∈ ([([0], 0), ([0], 1), ([0], 2)] : List Port),
        ∀ q ∈ ([([0], 0), ([0], 1), ([0], 2)] : List Port), loopColour p = loopColour q → p = q := by
      decide
    have hnd : ([([0], 0), ([0], 1), ([0], 2)] : List Port).Pairwise (· ≠ ·) := by decide
    exact hnd.imp_of_mem fun hp hq hpq hr => hpq (hne _ hp _ hq (hreach hr))
  · intro p hd
    obtain ⟨q, hl⟩ := hd.1
    obtain ⟨r, hr, h | h⟩ := hrep hl
    · exact ⟨r, hr, h ▸ .refl⟩
    · exact ⟨r, hr, .single (.inl h)⟩

/-- So the firing of `xloop` closes exactly two loops, which the reducer's
result, the empty net, does not show. -/
theorem xloop_loops : Loops ar xloop.toNet 1 (xloop.toNet.fire [0] [1] (rAnn true)) 2 :=
  ⟨0, Net.WF.deadCount_compact (show xloop.Ok ar by decide).2, xloop_dead⟩

/-- The reducer reports the two loops that the annihilation of `xloop`
closes, along with the empty net. -/
theorem xloop_runLoops : xloop.runLoops xsystem 10 = some (⟨[], [], []⟩, 1, 2) := by
  decide

/-- No loop is closed in the other examples. -/
example : (xgg.runLoops xsystem 10).map (·.2) = some (1, 0) ∧
    (xgd.runLoops xsystem 10).map (·.2) = some (1, 0) := by
  decide

/-! ### The combinators, as data

The same six rules written as tables.  The system is built by evaluating
the check, with no proof about the rules. -/

def dAnn (twist : Bool) : RuleData Comb :=
  RuleData.ofWires []
    [(.ifc false 0, .ifc true (if twist then 1 else 0)),
      (.ifc false 1, .ifc true (if twist then 0 else 1))]

def dEra : RuleData Comb :=
  RuleData.ofWires [((some false, 0), ε), ((some false, 1), ε)]
    [(.ifc false 0, .new (some false) 0 0), (.ifc false 1, .new (some false) 1 0)]

def dCom : RuleData Comb :=
  RuleData.ofWires
    [((some false, 0), δ), ((some false, 1), δ), ((some true, 0), γ), ((some true, 1), γ)]
    [(.ifc false 0, .new (some false) 0 0), (.ifc false 1, .new (some false) 1 0),
      (.ifc true 0, .new (some true) 0 0), (.ifc true 1, .new (some true) 1 0),
      (.new (some false) 0 1, .new (some true) 0 1), (.new (some false) 0 2, .new (some true) 1 1),
      (.new (some false) 1 1, .new (some true) 0 2), (.new (some false) 1 2, .new (some true) 1 2)]

def data : SysData Comb :=
  ⟨ar, [((γ, γ), dAnn true), ((δ, δ), dAnn false), ((ε, ε), ⟨[], []⟩),
    ((γ, δ), dCom), ((δ, γ), dCom.swap), ((γ, ε), dEra), ((ε, γ), dEra.swap),
    ((δ, ε), dEra), ((ε, δ), dEra.swap)]⟩

/-- The combinators as an executable system, by evaluation of the check. -/
def dsystem : XSys Comb := data.toXSys (by decide)

/-- It reduces the two example nets exactly as the hand-proved system does. -/
example : xgg.normalize dsystem 10 = xgg.normalize xsystem 10 := by
  decide

example : xgd.normalize dsystem 10 = xgd.normalize xsystem 10 := by
  decide

/-- The check rejects a net with a port left unwired ... -/
example : ¬ ({ xgg with free := ([6], 0) :: xgg.free } : XNet Comb).Ok ar := by
  decide

/-- ... and a net that uses a name reserved for a descendant of a live
agent: here `[9, 0]`, which extends the name `[0]` of the first `γ`. -/
example :
    ¬ ({ xgg with
          free := xgg.free ++ [([8], 0), ([9, 0], 0)]
          wires := xgg.wires ++ [(([8], 0), ([9, 0], 0)), (([9, 0], 0), ([8], 0))] } :
        XNet Comb).Ok ar := by
  decide

/-- **Two threads on two active pairs**, taking turns for sixty actions:
every thread ends idle, the two claims are made (one by each thread), and
the memory, with its history forgotten, is the net that the list reducer
returns. -/
theorem xgg2_exec :
    Normal (Step xsystem.sys)
        ((XMach.init xgg2 2).exec xsystem ((List.range 60).map (· % 2))).1.mem.toNet ∧
      ((XMach.init xgg2 2).exec xsystem ((List.range 60).map (· % 2))).1.mem.toNet.compact
          xsystem.sys.ar = (xgg2.run xsystem 10).1.toNet :=
  XMach.exec_agrees (f := 10) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

/-- In that run each thread makes one of the two claims. -/
example : (XMach.init xgg2 2).claimers xsystem ((List.range 60).map (· % 2)) = [1, 0] := by
  decide +kernel

/-- The same run without counting the claims: every thread is at rest, and
that is enough. -/
example :
    ((XMach.init xgg2 2).exec xsystem ((List.range 60).map (· % 2))).2 =
        (xgg2.run xsystem 10).2 ∧
      ((XMach.init xgg2 2).exec xsystem ((List.range 60).map (· % 2))).1.mem.toNet.compact
          xsystem.sys.ar = (xgg2.run xsystem 10).1.toNet :=
  XMach.exec_rest_agrees (f := 10) (by decide) (by decide) (by decide) _ (by decide +kernel)

/-- The same with another schedule: each thread runs four actions at a
time. -/
example :
    ((XMach.init xgg2 2).exec xsystem ((List.range 80).map fun i => i / 4 % 2)).1.mem.toNet.compact
        xsystem.sys.ar = (xgg2.run xsystem 10).1.toNet :=
  (XMach.exec_agrees (f := 10) (by decide) (by decide) (by decide +kernel) (by decide +kernel)).2

end Comb

/-! ## Example: a same-symbol rule that creates a single agent

`A` has no auxiliary port and `B` has one.  The rule `A ⋈ A` creates a single
`B` whose principal port is wired to its own auxiliary port.  This right-hand
side is its own mirror image, but its only agent cannot belong to either
side: it is owned by neither. -/

inductive Solo
  | A | B
  deriving DecidableEq

namespace Solo

def ar : Solo → Nat
  | A => 0
  | B => 1

/-- One new agent `B`, owned by neither side. -/
def lab : Option Bool → Nat → Option Solo
  | none, 0 => some B
  | _, _ => none

/-- Its principal port is wired to its auxiliary port. -/
def wire : LPort → Option LPort
  | .new none 0 0 => some (.new none 0 1)
  | .new none 0 1 => some (.new none 0 0)
  | _ => none

def rAA : Rhs Solo := Rhs.ofWire lab wire

theorem rAA_wf : rAA.WF ar A A := by
  apply Rhs.ofWire_wf
  · intro x y h
    unfold wire at h
    split at h <;> cases h <;> rfl
  · intro x h
    unfold wire at h
    split at h <;> simp at h
  · intro x
    rcases x with ⟨s, k⟩ | ⟨_ | s, j, k⟩
    · cases s <;> simp [wire, Rhs.Valid, ar]
    · rcases j with _ | j
      · rcases k with _ | _ | k <;> simp [wire, Rhs.Valid, Rhs.ofWire, lab, ar]
      · simp [wire, Rhs.Valid, Rhs.ofWire, lab]
    · simp [wire, Rhs.Valid, Rhs.ofWire, lab]

theorem rAA_mirror : rAA.Mirror rAA := by
  apply Rhs.ofWire_mirror
  · intro o j
    cases o with
    | none => rfl
    | some s => simp [lab]
  · intro x
    rcases x with ⟨s, k⟩ | ⟨_ | s, j, k⟩
    · simp [wire, LPort.swap]
    · rcases j with _ | j
      · rcases k with _ | _ | k <;> simp [wire, LPort.swap]
      · simp [wire, LPort.swap]
    · simp [wire, LPort.swap]

def rule : Solo → Solo → Option (Rhs Solo)
  | A, A => some rAA
  | _, _ => none

/-- An interaction system whose only rule is `A ⋈ A`. -/
def system : System Solo where
  ar := ar
  rule := rule
  rule_wf := by
    intro α β R h
    cases α <;> cases β <;>
      first
        | (obtain rfl := Option.some.inj h; exact rAA_wf)
        | cases h
  rule_symm := by
    intro α β R h
    cases α <;> cases β <;>
      first
        | (obtain rfl := Option.some.inj h; exact ⟨_, rfl, rAA_mirror⟩)
        | cases h

/-- Two `A` agents facing each other. -/
def aaWire : Port → Option Port
  | ([0], 0) => some ([1], 0)
  | ([1], 0) => some ([0], 0)
  | _ => none

def aa : Net Solo where
  agent i c := (i = [0] ∨ i = [1]) ∧ c = A
  link p q := aaWire p = some q
  free _ := False

theorem aa_used {i : Id} (h : aa.Used i) : ∃ n, i = [n] := by
  rcases h with ⟨c, hi | hi, -⟩ | ⟨k, q, h⟩ | ⟨k, h⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · change aaWire (i, k) = some q at h
    unfold aaWire at h
    split at h <;> first | (rename_i e; exact ⟨_, (Prod.mk.inj e).1⟩) | cases h
  · exact h.elim

theorem aa_wf : aa.WF ar where
  agent_fun := by
    rintro i α β ⟨-, rfl⟩ ⟨-, rfl⟩
    rfl
  symm := by
    intro p q h
    change aaWire p = some q at h
    change aaWire q = some p
    unfold aaWire at h
    split at h <;> cases h <;> rfl
  irrefl := by
    intro p h
    change aaWire p = some p at h
    unfold aaWire at h
    split at h <;> simp at h
  end_unique := fun {p q r} _ h h' =>
    Option.some.inj ((show aaWire p = some q from h).symm.trans h')
  end_conn := by
    rintro ⟨i, k⟩ (h | ⟨c, ⟨hi, rfl⟩, hk⟩)
    · exact h.elim
    · dsimp only at hi hk
      obtain rfl : k = 0 := Nat.le_zero.1 hk
      rcases hi with rfl | rfl
      · exact ⟨([1], 0), .inr ⟨A, ⟨.inr rfl, rfl⟩, Nat.zero_le _⟩, by decide, _, _, .single rfl⟩
      · exact ⟨([0], 0), .inr ⟨A, ⟨.inl rfl, rfl⟩, Nat.zero_le _⟩, by decide, _, _, .single rfl⟩
  deg := fun {p x y z} h h' _ =>
    .inl (Option.some.inj ((show aaWire p = some x from h).symm.trans h'))
  free_agent := fun h => h.elim
  fresh := by
    rintro a c l ⟨ha | ha, -⟩ hu <;> subst ha <;> obtain ⟨n, hn⟩ := aa_used hu <;>
      cases l with
      | nil => rfl
      | cons x l' => simp at hn

theorem aa_redex : Redex system aa [0] [1] A A rAA where
  ha := ⟨.inl rfl, rfl⟩
  hb := ⟨.inr rfl, rfl⟩
  ne := by decide
  conn := ⟨([1], 0), ([0], 0), .single rfl⟩
  rule := rfl

/-- The pair fires ... -/
theorem aa_step : Step system aa (aa.fire [0] [1] rAA) :=
  ⟨[0], [1], A, A, rAA, aa_redex, rfl⟩

/-- ... with the same result whichever agent is taken first ... -/
theorem aa_fire_symm : aa.fire [0] [1] rAA = aa.fire [1] [0] rAA :=
  fire_mirror aa [0] [1] rAA_mirror

/-- ... and leaves exactly one agent, a `B`. -/
theorem aa_fire_agent (i : Id) (c : Solo) :
    (aa.fire [0] [1] rAA).agent i c ↔ i = [1, 0] ∧ c = B := by
  constructor
  · rintro (⟨⟨h | h, -⟩, h₀, h₁⟩ | ⟨o, j, rfl, hl⟩)
    · exact absurd h h₀
    · exact absurd h h₁
    · change lab o j = some c at hl
      unfold lab at hl
      split at hl
      · exact ⟨rfl, (Option.some.inj hl).symm⟩
      · cases hl
  · rintro ⟨rfl, rfl⟩
    exact .inr ⟨none, 0, rfl, rfl⟩

/-! ### The same, executably -/

def xAA : XRhs Solo := ⟨lab, wire, [(none, 0)]⟩

theorem xAA_slots {o : Option Bool} {j : Nat} {c : Solo} (hl : xAA.lab o j = some c) :
    (o, j) ∈ xAA.slots := by
  rcases o with _ | s <;> rcases j with _ | j <;> simp [xAA, lab] at hl ⊢

def xrule : Solo → Solo → Option (XRhs Solo)
  | A, A => some xAA
  | _, _ => none

/-- An executable presentation of `Solo.system`. -/
def xsystem : XSys Solo where
  sys := system
  rule := xrule
  rule_spec := by
    intro α β
    cases α <;> cases β <;> rfl
  slots_spec := by
    intro α β R o j c hR hl
    cases α <;> cases β <;>
      first
        | (obtain rfl := Option.some.inj hR; exact xAA_slots hl)
        | cases hR

/-- The net `aa` as data, and what the reducer should leave. -/
def xaa : XNet Solo :=
  ⟨[([0], A), ([1], A)], [], [(([0], 0), ([1], 0)), (([1], 0), ([0], 0))]⟩

def xaaOut : XNet Solo :=
  ⟨[([1, 0], B)], [], [(([1, 0], 0), ([1, 0], 1)), (([1, 0], 1), ([1, 0], 0))]⟩

/-- `normalize` validates `xaa` and returns the single `B` wired to itself. -/
theorem xaa_normalize : xaa.normalize xsystem 10 = some (xaaOut, 1) := by
  decide

end Solo

end INet
