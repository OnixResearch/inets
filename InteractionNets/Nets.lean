import InteractionNets.Wires

namespace INet

universe u v

/-! ## Nets -/

/-- Agent identifiers. -/
abbrev Id := List Nat

/-- A port: an agent identifier and a port index (`0` is the principal port). -/
abbrev Port := Id × Nat

/-- Select one of two things by a side (`false` = left, `true` = right). -/
def sel {X : Type u} (x y : X) : Bool → X
  | false => x
  | true => y

@[simp] theorem sel_false {X : Type u} (x y : X) : sel x y false = x := rfl
@[simp] theorem sel_true {X : Type u} (x y : X) : sel x y true = y := rfl

theorem sel_not {X : Type u} (x y : X) (s : Bool) : sel x y (!s) = sel y x s := by
  cases s <;> rfl

/-- A total order on identifiers (lexicographic).  It is used for one thing
only: choosing one of two identifiers in a way that does not depend on the
order in which they are given. -/
def idLe : Id → Id → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && idLe xs ys)

theorem idLe_total (a b : Id) : idLe a b = true ∨ idLe b a = true := by
  induction a generalizing b with
  | nil => exact .inl (by simp [idLe])
  | cons x xs ih =>
    cases b with
    | nil => exact .inr (by simp [idLe])
    | cons y ys =>
      simp only [idLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rcases Nat.lt_trichotomy x y with h | h | h
      · exact .inl (.inl h)
      · rcases ih ys with h' | h'
        · exact .inl (.inr ⟨h, h'⟩)
        · exact .inr (.inr ⟨h.symm, h'⟩)
      · exact .inr (.inl h)

theorem idLe_antisymm {a b : Id} (h₁ : idLe a b = true) (h₂ : idLe b a = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp [idLe] at h₂
  | cons x xs ih =>
    cases b with
    | nil => simp [idLe] at h₁
    | cons y ys =>
      simp only [idLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        at h₁ h₂
      rcases h₁ with h₁ | ⟨rfl, h₁⟩
      · rcases h₂ with h₂ | ⟨h₂, -⟩ <;> omega
      · rcases h₂ with h₂ | ⟨-, h₂⟩
        · omega
        · rw [ih h₁ h₂]

/-- One of two identifiers, the same whichever way round they are given. -/
def pick (a b : Id) : Id := if idLe a b then a else b

theorem pick_eq (a b : Id) : pick a b = a ∨ pick a b = b := by
  unfold pick
  split
  · exact .inl rfl
  · exact .inr rfl

theorem pick_comm (a b : Id) : pick a b = pick b a := by
  unfold pick
  split <;> split
  · rename_i h₁ h₂
    exact idLe_antisymm h₁ h₂
  · rfl
  · rfl
  · rename_i h₁ h₂
    exact absurd (idLe_total a b) (by simp [h₁, h₂])

/-- Exchange the two sides in the owner of a new agent (see `LPort`). -/
def flipOwner (o : Option Bool) : Option Bool := o.map (!·)

@[simp] theorem flipOwner_none : flipOwner none = none := rfl
@[simp] theorem flipOwner_some (s : Bool) : flipOwner (some s) = some (!s) := rfl
@[simp] theorem flipOwner_flipOwner (o : Option Bool) : flipOwner (flipOwner o) = o := by
  cases o <;> simp

/-- The agent after which a new agent is named: the fired agent of its own
side, or, for a new agent owned by neither side, one of the two fired agents
chosen independently of their order. -/
def par (a b : Id) : Option Bool → Id
  | some s => sel a b s
  | none => pick a b

/-- Position of a new agent among those named after the same fired agent. -/
def slot : Option Bool → Nat → Nat
  | some _, j => 2 * j
  | none, j => 2 * j + 1

/-- Identifier of the `j`-th new agent with owner `o` when `a` and `b` fire. -/
def child (a b : Id) (o : Option Bool) (j : Nat) : Id := slot o j :: par a b o

theorem par_eq (a b : Id) (o : Option Bool) : par a b o = a ∨ par a b o = b := by
  cases o with
  | none => exact pick_eq a b
  | some s =>
    cases s
    · exact .inl rfl
    · exact .inr rfl

theorem child_swap (a b : Id) (o : Option Bool) (j : Nat) :
    child b a (flipOwner o) j = child a b o j := by
  cases o with
  | none => simp [child, slot, par, pick_comm b a]
  | some s => simp [child, slot, par, sel_not]

variable {S : Type}

/-- A net over the set of symbols `S`. -/
structure Net (S : Type) where
  /-- `agent i α`: agent `i` is live and carries symbol `α`. -/
  agent : Id → S → Prop
  /-- Wire segments. -/
  link : Port → Port → Prop
  /-- The interface: free ports. -/
  free : Port → Prop

theorem Net.ext' {N M : Net S} (h₁ : ∀ i γ, N.agent i γ ↔ M.agent i γ)
    (h₂ : ∀ p q, N.link p q ↔ M.link p q) (h₃ : ∀ p, N.free p ↔ M.free p) : N = M := by
  cases N; cases M
  simp only [Net.mk.injEq]
  exact ⟨funext fun i => funext fun γ => propext (h₁ i γ),
    funext fun p => funext fun q => propext (h₂ p q), funext fun p => propext (h₃ p)⟩

/-- An *end* is a real port of the net: a free port, or a port of a live agent
whose index is within the arity of its symbol. -/
def Net.End (ar : S → Nat) (N : Net S) (p : Port) : Prop :=
  N.free p ∨ ∃ γ, N.agent p.1 γ ∧ p.2 ≤ ar γ

/-- Identifiers occurring in the net. -/
def Net.Used (N : Net S) (i : Id) : Prop :=
  (∃ γ, N.agent i γ) ∨ (∃ k q, N.link (i, k) q) ∨ ∃ k, N.free (i, k)

/-- Two ports are the extremities of a wire: they are joined by a chain of
segments running through junctions only. -/
def Net.Conn (ar : S → Nat) (N : Net S) (p q : Port) : Prop :=
  INet.Conn N.link (N.End ar) p q

/-- Well-formed nets. -/
structure Net.WF (ar : S → Nat) (N : Net S) : Prop where
  /-- An agent has one symbol. -/
  agent_fun : ∀ {i α β}, N.agent i α → N.agent i β → α = β
  symm : ∀ {p q}, N.link p q → N.link q p
  irrefl : ∀ {p}, ¬ N.link p p
  /-- Every end is attached to at most one segment. -/
  end_unique : ∀ {p q r}, N.End ar p → N.link p q → N.link p r → q = r
  /-- The wire leaving an end reaches another end. -/
  end_conn : ∀ {p}, N.End ar p → ∃ q, N.End ar q ∧ q ≠ p ∧ N.Conn ar p q
  /-- Every point is attached to at most two segments. -/
  deg : ∀ {p x y z}, N.link p x → N.link p y → N.link p z → x = y ∨ x = z ∨ y = z
  /-- Free ports are not ports of live agents. -/
  free_agent : ∀ {i k α}, N.free (i, k) → ¬ N.agent i α
  /-- Names reserved for the descendants of a live agent are not in use. -/
  fresh : ∀ {a α} (l : List Nat), N.agent a α → N.Used (l ++ a) → l = []

theorem Net.WF.wiring {ar : S → Nat} {N : Net S} (hN : N.WF ar) :
    Wiring N.link (N.End ar) :=
  ⟨hN.symm, hN.deg, hN.end_unique⟩

theorem Net.WF.wired {ar : S → Nat} {N : Net S} (hN : N.WF ar) :
    Wired N.link (N.End ar) :=
  fun _ ht => hN.end_conn ht

/-- Every end is attached to a segment. -/
theorem Net.WF.end_wired {ar : S → Nat} {N : Net S} (hN : N.WF ar) {p : Port}
    (hp : N.End ar p) : ∃ q, N.link p q := by
  obtain ⟨q, -, -, v, x, w⟩ := hN.end_conn hp
  exact ⟨v, w.link_first⟩

theorem Net.Conn.symm {ar : S → Nat} {N : Net S} (hN : N.WF ar) {p q : Port}
    (h : N.Conn ar p q) : N.Conn ar q p :=
  INet.Conn.symm hN.wiring h

/-- A wire leaving an end has exactly one other extremity. -/
theorem Net.Conn.det {ar : S → Nat} {N : Net S} (hN : N.WF ar) {p q q' : Port}
    (hp : N.End ar p) (hq : N.End ar q) (hq' : N.End ar q')
    (h : N.Conn ar p q) (h' : N.Conn ar p q') : q = q' :=
  INet.Conn.det hN.wiring hp hq hq' h h'

/-- `p` and `q` are the two ends of a wire of the net. -/
def Net.Paired (ar : S → Nat) (N : Net S) (p q : Port) : Prop :=
  N.End ar p ∧ N.End ar q ∧ N.Conn ar p q

/-- Being an end only depends on the agents and on the free ports. -/
theorem Net.end_congr {ar : S → Nat} {N M : Net S}
    (ha : ∀ i γ, N.agent i γ ↔ M.agent i γ) (hf : ∀ p, N.free p ↔ M.free p) (p : Port) :
    N.End ar p ↔ M.End ar p :=
  or_congr (hf p) (exists_congr fun γ => and_congr (ha p.1 γ) Iff.rfl)

/-- Observational equivalence: the same live agents with the same names and
symbols, the same free ports, and the same pairing of ends by wires.  How a
wire is cut into segments, and segments that touch no end, are not observed. -/
structure Net.ObsEq (ar : S → Nat) (N M : Net S) : Prop where
  agent : ∀ i γ, N.agent i γ ↔ M.agent i γ
  free : ∀ p, N.free p ↔ M.free p
  paired : ∀ p q, N.Paired ar p q ↔ M.Paired ar p q

namespace Net.ObsEq

variable {ar : S → Nat} {N M P : Net S}

theorem refl (N : Net S) : N.ObsEq ar N :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem symm (h : N.ObsEq ar M) : M.ObsEq ar N :=
  ⟨fun i γ => (h.agent i γ).symm, fun p => (h.free p).symm, fun p q => (h.paired p q).symm⟩

theorem trans (h : N.ObsEq ar M) (h' : M.ObsEq ar P) : N.ObsEq ar P :=
  ⟨fun i γ => (h.agent i γ).trans (h'.agent i γ), fun p => (h.free p).trans (h'.free p),
    fun p q => (h.paired p q).trans (h'.paired p q)⟩

theorem end_iff (h : N.ObsEq ar M) (p : Port) : N.End ar p ↔ M.End ar p :=
  Net.end_congr h.agent h.free p

theorem end_eq (h : N.ObsEq ar M) : N.End ar = M.End ar :=
  funext fun p => propext (h.end_iff p)

end Net.ObsEq

/-! ## Interaction rules -/

/-- Ports of the right-hand side of a rule.  Side `false` is the first agent
of the active pair, side `true` the second.  Every new agent has an *owner*:
`some s` if it belongs to side `s`, `none` if it belongs to neither side.
Exchanging the two sides exchanges the agents of side `false` with those of
side `true` and leaves the agents owned by neither side where they are. -/
inductive LPort
  /-- The `k`-th auxiliary port of the agent on side `s`. -/
  | ifc (s : Bool) (k : Nat)
  /-- Port `k` of the `j`-th new agent with owner `o`. -/
  | new (o : Option Bool) (j k : Nat)
  deriving DecidableEq

/-- Exchange the two sides. -/
def LPort.swap : LPort → LPort
  | .ifc s k => .ifc (!s) k
  | .new o j k => .new (flipOwner o) j k

/-- The port belongs to a new agent rather than to the interface. -/
def LPort.IsNew : LPort → Prop
  | .ifc _ _ => False
  | .new _ _ _ => True

@[simp] theorem LPort.swap_swap (x : LPort) : x.swap.swap = x := by
  cases x <;> simp [LPort.swap]

/-- The right-hand side of an interaction rule. -/
structure Rhs (S : Type) where
  /-- Symbol of the `j`-th new agent with owner `o`, if there is one. -/
  lab : Option Bool → Nat → Option S
  /-- Wires of the right-hand side. -/
  link : LPort → LPort → Prop

/-- The ports that exist in the right-hand side of a rule for `α ⋈ β`. -/
def Rhs.Valid (ar : S → Nat) (R : Rhs S) (α β : S) : LPort → Prop
  | .ifc s k => k < ar (sel α β s)
  | .new o j k => ∃ γ, R.lab o j = some γ ∧ k ≤ ar γ

/-- A right-hand side for `α ⋈ β` is a net whose interface is made of the
auxiliary ports of `α` and `β`: every port is attached to exactly one wire. -/
structure Rhs.WF (ar : S → Nat) (R : Rhs S) (α β : S) : Prop where
  symm : ∀ {x y}, R.link x y → R.link y x
  irrefl : ∀ {x}, ¬ R.link x x
  valid : ∀ {x y}, R.link x y → R.Valid ar α β x
  unique : ∀ {x y z}, R.link x y → R.link x z → y = z
  total : ∀ {x}, R.Valid ar α β x → ∃ y, R.link x y

/-- `R'` is `R` with the two sides exchanged. -/
def Rhs.Mirror (R R' : Rhs S) : Prop :=
  (∀ o j, R'.lab o j = R.lab (flipOwner o) j) ∧ ∀ x y, R'.link x y ↔ R.link x.swap y.swap

/-- The mirror image of a right-hand side. -/
def Rhs.swap (R : Rhs S) : Rhs S where
  lab o j := R.lab (flipOwner o) j
  link x y := R.link x.swap y.swap

theorem Rhs.mirror_swap (R : Rhs S) : R.Mirror R.swap :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

theorem Rhs.swap_mirror (R : Rhs S) : R.swap.Mirror R :=
  ⟨fun o j => by simp [Rhs.swap], fun x y => by simp [Rhs.swap]⟩

theorem Rhs.valid_swap {ar : S → Nat} {R : Rhs S} {α β : S} {x : LPort} :
    R.swap.Valid ar β α x ↔ R.Valid ar α β x.swap := by
  cases x with
  | ifc s k => simp [Rhs.Valid, LPort.swap, sel_not]
  | new o j k => simp [Rhs.Valid, LPort.swap, Rhs.swap]

theorem Rhs.WF.swap {ar : S → Nat} {R : Rhs S} {α β : S} (h : R.WF ar α β) :
    R.swap.WF ar β α where
  symm := fun hl => h.symm hl
  irrefl := fun hl => h.irrefl hl
  valid := fun hl => Rhs.valid_swap.2 (h.valid hl)
  unique := fun hl hl' => by
    have := congrArg LPort.swap (h.unique hl hl')
    simpa using this
  total := fun hv => by
    obtain ⟨y, hy⟩ := h.total (Rhs.valid_swap.1 hv)
    exact ⟨y.swap, by simpa [Rhs.swap] using hy⟩

/-- An interaction system: symbols with arities, and at most one rule for
each pair of symbols, given consistently in both orientations. -/
structure System (S : Type) where
  ar : S → Nat
  rule : S → S → Option (Rhs S)
  rule_wf : ∀ {α β R}, rule α β = some R → R.WF ar α β
  rule_symm : ∀ {α β R}, rule α β = some R → ∃ R', rule β α = some R' ∧ R.Mirror R'

/-! ## Firing an active pair -/

/-- Where a port of the right-hand side lands when agents `a` and `b` fire. -/
def emb (a b : Id) : LPort → Port
  | .ifc s k => (sel a b s, k + 1)
  | .new o j k => (child a b o j, k)

theorem emb_swap (a b : Id) (x : LPort) : emb b a x.swap = emb a b x := by
  cases x <;> simp [emb, LPort.swap, sel_not, child_swap]

/-- Replace the agents `a` and `b` by the right-hand side `R`. -/
def Net.fire (N : Net S) (a b : Id) (R : Rhs S) : Net S where
  agent i γ := (N.agent i γ ∧ i ≠ a ∧ i ≠ b) ∨ ∃ o j, i = child a b o j ∧ R.lab o j = some γ
  link p q := N.link p q ∨ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y
  free := N.free

/-- Firing does not depend on the orientation of the pair. -/
theorem fire_mirror (N : Net S) (a b : Id) {R R' : Rhs S} (hm : R.Mirror R') :
    N.fire a b R = N.fire b a R' := by
  apply Net.ext'
  · intro i γ
    constructor
    · rintro (⟨hg, ha, hb⟩ | ⟨s, j, rfl, hl⟩)
      · exact .inl ⟨hg, hb, ha⟩
      · exact .inr ⟨flipOwner s, j, (child_swap a b s j).symm,
          by rw [hm.1, flipOwner_flipOwner]; exact hl⟩
    · rintro (⟨hg, hb, ha⟩ | ⟨s, j, rfl, hl⟩)
      · exact .inl ⟨hg, ha, hb⟩
      · exact .inr ⟨flipOwner s, j, (child_swap b a s j).symm, by rw [← hm.1]; exact hl⟩
  · intro p q
    constructor
    · rintro (hl | ⟨x, y, hxy, rfl, rfl⟩)
      · exact .inl hl
      · exact .inr ⟨x.swap, y.swap, (hm.2 _ _).2 (by simpa using hxy),
          (emb_swap a b x).symm ▸ rfl, (emb_swap a b y).symm ▸ rfl⟩
    · rintro (hl | ⟨x, y, hxy, rfl, rfl⟩)
      · exact .inl hl
      · exact .inr ⟨x.swap, y.swap, (hm.2 _ _).1 hxy,
          (emb_swap b a x).symm ▸ rfl, (emb_swap b a y).symm ▸ rfl⟩
  · intro p
    exact Iff.rfl

/-- Firing two pairs commutes as soon as neither creates an agent that the
other deletes. -/
theorem fire_comm (N : Net S) {a b c d : Id} (R R' : Rhs S)
    (h₁ : ∀ o j, child a b o j ≠ c ∧ child a b o j ≠ d)
    (h₂ : ∀ o j, child c d o j ≠ a ∧ child c d o j ≠ b) :
    (N.fire a b R).fire c d R' = (N.fire c d R').fire a b R := by
  have key : ∀ {a b c d : Id} {R R' : Rhs S},
      (∀ o j, child c d o j ≠ a ∧ child c d o j ≠ b) → ∀ i γ,
      ((N.fire a b R).fire c d R').agent i γ → ((N.fire c d R').fire a b R).agent i γ := by
    intro a b c d R R' h i γ
    rintro (⟨⟨hg, ha, hb⟩ | ⟨s, j, rfl, hl⟩, hc, hd⟩ | ⟨s, j, rfl, hl⟩)
    · exact .inl ⟨.inl ⟨hg, hc, hd⟩, ha, hb⟩
    · exact .inr ⟨s, j, rfl, hl⟩
    · exact .inl ⟨.inr ⟨s, j, rfl, hl⟩, (h s j).1, (h s j).2⟩
  apply Net.ext'
  · exact fun i γ => ⟨key h₂ i γ, key h₁ i γ⟩
  · exact fun p q => or_right_comm
  · exact fun p => Iff.rfl

/-- The data of a firing site: two distinct live agents of a well-formed net. -/
structure Site (ar : S → Nat) (N : Net S) (a b : Id) (α β : S) : Prop where
  wf : N.WF ar
  ha : N.agent a α
  hb : N.agent b β
  ne : a ≠ b
  conn : N.Conn ar (a, 0) (b, 0)

namespace Site

variable {ar : S → Nat} {N : Net S} {a b : Id} {α β : S}

theorem agent_sel (h : Site ar N a b α β) (s : Bool) : N.agent (sel a b s) (sel α β s) := by
  cases s
  · exact h.ha
  · exact h.hb

theorem used_sel (h : Site ar N a b α β) (s : Bool) : N.Used (sel a b s) :=
  .inl ⟨_, h.agent_sel s⟩

theorem par_live (h : Site ar N a b α β) (o : Option Bool) : ∃ γ, N.agent (par a b o) γ := by
  rcases par_eq a b o with e | e
  · rw [e]; exact ⟨α, h.ha⟩
  · rw [e]; exact ⟨β, h.hb⟩

theorem used_par (h : Site ar N a b α β) (o : Option Bool) : N.Used (par a b o) :=
  .inl (h.par_live o)

theorem not_used_desc (h : Site ar N a b α β) (o : Option Bool) (n : Nat) (l : List Nat) :
    ¬ N.Used (l ++ n :: par a b o) := by
  intro hu
  obtain ⟨γ, hg⟩ := h.par_live o
  have e : l ++ n :: par a b o = (l ++ [n]) ++ par a b o := by simp
  rw [e] at hu
  have := h.wf.fresh _ hg hu
  simp at this

/-- The names of the new agents are not in use. -/
theorem not_used_child (h : Site ar N a b α β) (o : Option Bool) (j : Nat) :
    ¬ N.Used (child a b o j) :=
  h.not_used_desc o (slot o j) []

theorem sel_inj (h : Site ar N a b α β) {s s' : Bool} (e : sel a b s = sel a b s') : s = s' := by
  cases s <;> cases s' <;> first | rfl | exact absurd e h.ne | exact absurd e.symm h.ne

theorem sel_ne_child (h : Site ar N a b α β) {s : Bool} {o : Option Bool} {j : Nat} :
    sel a b s ≠ child a b o j :=
  fun e => h.not_used_child o j (e ▸ h.used_sel s)

/-- Distinct new agents get distinct names. -/
theorem child_inj (h : Site ar N a b α β) {o o' : Option Bool} {j j' : Nat}
    (e : child a b o j = child a b o' j') : o = o' ∧ j = j' := by
  have e' : slot o j :: par a b o = slot o' j' :: par a b o' := e
  obtain ⟨e₁, e₂⟩ := List.cons.inj e'
  cases o with
  | none =>
    cases o' with
    | none => exact ⟨rfl, by simp only [slot] at e₁; omega⟩
    | some s' => simp only [slot] at e₁; omega
  | some s =>
    cases o' with
    | none => simp only [slot] at e₁; omega
    | some s' =>
      obtain rfl := h.sel_inj e₂
      exact ⟨rfl, by simp only [slot] at e₁; omega⟩

theorem emb_inj (h : Site ar N a b α β) {x y : LPort} (e : emb a b x = emb a b y) : x = y := by
  cases x with
  | ifc s k =>
    cases y with
    | ifc s' k' =>
      simp only [emb, Prod.mk.injEq, Nat.add_right_cancel_iff] at e
      obtain ⟨e₁, rfl⟩ := e
      rw [h.sel_inj e₁]
    | new o' j k' =>
      simp only [emb, Prod.mk.injEq] at e
      exact absurd e.1 h.sel_ne_child
  | new o j k =>
    cases y with
    | ifc s' k' =>
      simp only [emb, Prod.mk.injEq] at e
      exact absurd e.1.symm h.sel_ne_child
    | new o' j' k' =>
      simp only [emb, Prod.mk.injEq] at e
      obtain ⟨e₁, rfl⟩ := e
      obtain ⟨rfl, rfl⟩ := h.child_inj e₁
      rfl

variable {R : Rhs S}

/-- Firing only brings into use the names of the new agents. -/
theorem used_fire (h : Site ar N a b α β) {i : Id} (hu : (N.fire a b R).Used i) :
    N.Used i ∨ ∃ o j, i = child a b o j := by
  rcases hu with ⟨γ, ⟨hg, -, -⟩ | ⟨s, j, rfl, -⟩⟩ | ⟨k, q, hl | ⟨x, y, -, e, -⟩⟩ | ⟨k, hf⟩
  · exact .inl (.inl ⟨γ, hg⟩)
  · exact .inr ⟨s, j, rfl⟩
  · exact .inl (.inr (.inl ⟨k, q, hl⟩))
  · cases x with
    | ifc s k' =>
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact .inl (h.used_sel s)
    | new s j k' => exact .inr ⟨s, j, (Prod.mk.inj e).1⟩
  · exact .inl (.inr (.inr ⟨k, hf⟩))

/-- An end of the new net that carries an old segment was already an end. -/
theorem end_of_fire_link (h : Site ar N a b α β) {p q : Port}
    (hE : (N.fire a b R).End ar p) (hl : N.link p q) : N.End ar p := by
  rcases hE with hf | ⟨γ, ⟨hg, -, -⟩ | ⟨s, j, e, -⟩, hk⟩
  · exact .inl hf
  · exact .inr ⟨γ, hg, hk⟩
  · exact absurd (.inr (.inl ⟨p.2, q, hl⟩)) (e ▸ h.not_used_child s j)

/-- The ports of the two fired agents are no longer ends. -/
theorem not_end_fire_sel (h : Site ar N a b α β) (s : Bool) (k : Nat) :
    ¬ (N.fire a b R).End ar (sel a b s, k) := by
  rintro (hf | ⟨γ, ⟨-, na, nb⟩ | ⟨s', j, e, -⟩, -⟩)
  · exact h.wf.free_agent hf (h.agent_sel s)
  · cases s
    · exact na rfl
    · exact nb rfl
  · exact h.sel_ne_child e

/-- The segments added by the firing. -/
def NewLink (a b : Id) (R : Rhs S) (p q : Port) : Prop :=
  ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y

theorem newLink_unique (h : Site ar N a b α β) (hR : R.WF ar α β) {p q r : Port}
    (hq : NewLink a b R p q) (hr : NewLink a b R p r) : q = r := by
  obtain ⟨x, y, hxy, rfl, rfl⟩ := hq
  obtain ⟨x', y', hxy', e, rfl⟩ := hr
  obtain rfl := h.emb_inj e
  rw [hR.unique hxy hxy']

/-- A new segment is attached to an old one only at an auxiliary port of a
fired agent. -/
theorem end_of_newLink (h : Site ar N a b α β) (hR : R.WF ar α β) {p q r : Port}
    (hq : NewLink a b R p q) (hr : N.link p r) : N.End ar p := by
  obtain ⟨x, y, hxy, rfl, rfl⟩ := hq
  have hv := hR.valid hxy
  cases x with
  | ifc s k => exact .inr ⟨_, h.agent_sel s, Nat.succ_le_of_lt hv⟩
  | new s j k => exact absurd (.inr (.inl ⟨k, r, hr⟩)) (h.not_used_child s j)

theorem newLink_old_unique (h : Site ar N a b α β) (hR : R.WF ar α β) {p q r r' : Port}
    (hq : NewLink a b R p q) (hr : N.link p r) (hr' : N.link p r') : r = r' :=
  h.wf.end_unique (h.end_of_newLink hR hq hr) hr hr'

/-- No end of the new net carries both an old and a new segment. -/
theorem end_fire_newLink (h : Site ar N a b α β) {p q r : Port}
    (hE : (N.fire a b R).End ar p) (hq : NewLink a b R p q) (hr : N.link p r) : False := by
  obtain ⟨x, y, -, rfl, rfl⟩ := hq
  cases x with
  | ifc s k => exact h.not_end_fire_sel s _ hE
  | new s j k => exact h.not_used_child s j (.inr (.inl ⟨k, r, hr⟩))

theorem newLink_irrefl (h : Site ar N a b α β) (hR : R.WF ar α β) {p : Port} :
    ¬ NewLink a b R p p := by
  rintro ⟨x, y, hxy, e₁, e₂⟩
  obtain rfl := h.emb_inj (e₁.symm.trans e₂)
  exact hR.irrefl hxy

/-! ### Wires after a firing

Firing is decomposed into three operations on wires: retire the two principal
ports, which are joined by a wire; add the new segments that join two
auxiliary ports of the fired agents, of which there are finitely many; attach
the ports of the new agents. -/

/-- The ends of `N` other than the two principal ports being consumed. -/
def Pending (ar : S → Nat) (N : Net S) (a b : Id) (p : Port) : Prop :=
  N.End ar p ∧ p ≠ (a, 0) ∧ p ≠ (b, 0)

/-- New segments between two auxiliary ports of the fired agents. -/
def IfcLink (a b : Id) (R : Rhs S) (p q : Port) : Prop :=
  ∃ s k s' k', R.link (.ifc s k) (.ifc s' k') ∧
    p = emb a b (.ifc s k) ∧ q = emb a b (.ifc s' k')

/-- New segments with an extremity on a new agent. -/
def AgentLink (a b : Id) (R : Rhs S) (p q : Port) : Prop :=
  ∃ x y, R.link x y ∧ (x.IsNew ∨ y.IsNew) ∧ p = emb a b x ∧ q = emb a b y

/-- The ports of the new agents. -/
def NewEnd (ar : S → Nat) (a b : Id) (R : Rhs S) (p : Port) : Prop :=
  ∃ s j k γ, p = emb a b (.new s j k) ∧ R.lab s j = some γ ∧ k ≤ ar γ

/-- The auxiliary ports of the fired agents, as a list. -/
def auxPorts (ar : S → Nat) (a b : Id) (α β : S) : List Port :=
  (List.range (ar α)).map (fun k => (a, k + 1)) ++ (List.range (ar β)).map (fun k => (b, k + 1))

theorem newLink_iff {p q : Port} :
    NewLink a b R p q ↔ IfcLink a b R p q ∨ AgentLink a b R p q := by
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    cases x with
    | ifc s k =>
      cases y with
      | ifc s' k' => exact .inl ⟨s, k, s', k', hxy, rfl, rfl⟩
      | new s' j k' => exact .inr ⟨_, _, hxy, .inr trivial, rfl, rfl⟩
    | new s j k => exact .inr ⟨_, _, hxy, .inl trivial, rfl, rfl⟩
  · rintro (⟨s, k, s', k', hxy, rfl, rfl⟩ | ⟨x, y, hxy, -, rfl, rfl⟩)
    · exact ⟨_, _, hxy, rfl, rfl⟩
    · exact ⟨_, _, hxy, rfl, rfl⟩

theorem aux_end (h : Site ar N a b α β) {s : Bool} {k : Nat} (hk : k < ar (sel α β s)) :
    N.End ar (sel a b s, k + 1) :=
  .inr ⟨_, h.agent_sel s, Nat.succ_le_of_lt hk⟩

theorem not_end_child (h : Site ar N a b α β) (s : Option Bool) (j k : Nat) :
    ¬ N.End ar (child a b s j, k) := by
  rintro (hf | ⟨γ, hg, -⟩)
  · exact h.not_used_child s j (.inr (.inr ⟨k, hf⟩))
  · exact h.not_used_child s j (.inl ⟨γ, hg⟩)

theorem agent_cases (h : Site ar N a b α β) {i : Id} {γ : S} (hg : N.agent i γ) :
    (∃ s, i = sel a b s ∧ γ = sel α β s) ∨ (i ≠ a ∧ i ≠ b) := by
  by_cases ha : i = a
  · subst ha
    exact .inl ⟨false, rfl, h.wf.agent_fun hg h.ha⟩
  by_cases hb : i = b
  · subst hb
    exact .inl ⟨true, rfl, h.wf.agent_fun hg h.hb⟩
  exact .inr ⟨ha, hb⟩

theorem ifcLink_symm (hR : R.WF ar α β) {p q : Port} (hl : IfcLink a b R p q) :
    IfcLink a b R q p := by
  obtain ⟨s, k, s', k', hxy, rfl, rfl⟩ := hl
  exact ⟨s', k', s, k, hR.symm hxy, rfl, rfl⟩

theorem ifcLink_pending (h : Site ar N a b α β) (hR : R.WF ar α β) {p q : Port}
    (hl : IfcLink a b R p q) : Pending ar N a b p := by
  obtain ⟨s, k, s', k', hxy, rfl, rfl⟩ := hl
  refine ⟨h.aux_end (hR.valid hxy), ?_, ?_⟩ <;>
    exact fun e => Nat.succ_ne_zero k (Prod.mk.inj e).2

theorem ifcLink_mem (hR : R.WF ar α β) {p q : Port} (hl : IfcLink a b R p q) :
    p ∈ auxPorts ar a b α β := by
  obtain ⟨s, k, s', k', hxy, rfl, rfl⟩ := hl
  have hk := hR.valid hxy
  cases s
  · exact List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)

theorem agentLink_symm (hR : R.WF ar α β) {p q : Port} (hl : AgentLink a b R p q) :
    AgentLink a b R q p := by
  obtain ⟨x, y, hxy, hn, rfl, rfl⟩ := hl
  exact ⟨y, x, hR.symm hxy, hn.symm, rfl, rfl⟩

theorem newEnd_of_valid (hR : R.WF ar α β) {x y : LPort} (hxy : R.link x y) (hx : x.IsNew) :
    NewEnd ar a b R (emb a b x) := by
  cases x with
  | ifc s k => exact hx.elim
  | new s j k =>
    obtain ⟨γ, hl, hk⟩ := hR.valid hxy
    exact ⟨s, j, k, γ, rfl, hl, hk⟩

theorem agentLink_newEnd (hR : R.WF ar α β) {p q : Port} (hl : AgentLink a b R p q) :
    NewEnd ar a b R p ∨ NewEnd ar a b R q := by
  obtain ⟨x, y, hxy, hn | hn, rfl, rfl⟩ := hl
  · exact .inl (newEnd_of_valid hR hxy hn)
  · exact .inr (newEnd_of_valid hR (hR.symm hxy) hn)

theorem agentLink_left (h : Site ar N a b α β) (hR : R.WF ar α β) {p q : Port}
    (hl : AgentLink a b R p q) :
    NewEnd ar a b R p ∨ (Pending ar N a b p ∧ ¬ ∃ q, IfcLink a b R p q) := by
  obtain ⟨x, y, hxy, hn, rfl, rfl⟩ := hl
  cases x with
  | new s j k => exact .inl (newEnd_of_valid hR hxy trivial)
  | ifc s k =>
    refine .inr ⟨⟨h.aux_end (hR.valid hxy), ?_, ?_⟩, ?_⟩
    · exact fun e => Nat.succ_ne_zero k (Prod.mk.inj e).2
    · exact fun e => Nat.succ_ne_zero k (Prod.mk.inj e).2
    · rintro ⟨q, s₁, k₁, s₂, k₂, hxy', e, -⟩
      cases h.emb_inj e
      obtain rfl := hR.unique hxy hxy'
      exact hn.elim id id

theorem newEnd_agentLink (hR : R.WF ar α β) {p : Port} (hp : NewEnd ar a b R p) :
    ∃ q, AgentLink a b R p q := by
  obtain ⟨s, j, k, γ, rfl, hl, hk⟩ := hp
  obtain ⟨y, hy⟩ := hR.total (x := .new s j k) ⟨γ, hl, hk⟩
  exact ⟨emb a b y, _, y, hy, .inl trivial, rfl, rfl⟩

theorem newEnd_not_link (h : Site ar N a b α β) {p q : Port} (hp : NewEnd ar a b R p) :
    ¬ (N.link p q ∨ IfcLink a b R p q) := by
  obtain ⟨s, j, k, γ, rfl, -, -⟩ := hp
  rintro (hl | ⟨s₁, k₁, s₂, k₂, -, e, -⟩)
  · exact h.not_used_child s j (.inr (.inl ⟨k, q, hl⟩))
  · cases h.emb_inj e

theorem newEnd_not_pending (h : Site ar N a b α β) {p : Port} (hp : NewEnd ar a b R p) :
    ¬ (Pending ar N a b p ∧ ¬ ∃ q, IfcLink a b R p q) := by
  obtain ⟨s, j, k, γ, rfl, -, -⟩ := hp
  exact fun hT => h.not_end_child s j k hT.1.1

/-- The ends of the new net are the pending ends that received no new
segment, together with the ports of the new agents. -/
theorem end_fire_iff (h : Site ar N a b α β) (hR : R.WF ar α β) (p : Port) :
    (((Pending ar N a b p ∧ ¬ ∃ q, IfcLink a b R p q) ∧ ¬ ∃ q, AgentLink a b R p q) ∨
        NewEnd ar a b R p) ↔ (N.fire a b R).End ar p := by
  constructor
  · rintro (⟨⟨⟨hE, hpa, hpb⟩, hnI⟩, hnA⟩ | ⟨s, j, k, γ, rfl, hl, hk⟩)
    · have hnew : ∀ q, ¬ NewLink a b R p q := fun q hq =>
        (newLink_iff.1 hq).elim (fun h' => hnI ⟨q, h'⟩) (fun h' => hnA ⟨q, h'⟩)
      rcases hE with hf | ⟨γ, hg, hk⟩
      · exact .inl hf
      · obtain ⟨i, k⟩ := p
        rcases h.agent_cases hg with ⟨s, rfl, rfl⟩ | ⟨hia, hib⟩
        · exfalso
          cases k with
          | zero =>
            cases s
            · exact hpa rfl
            · exact hpb rfl
          | succ k =>
            obtain ⟨y, hy⟩ := hR.total (x := .ifc s k) (Nat.lt_of_succ_le hk)
            exact hnew _ ⟨_, y, hy, rfl, rfl⟩
        · exact .inr ⟨γ, .inl ⟨hg, hia, hib⟩, hk⟩
    · exact .inr ⟨γ, .inr ⟨s, j, rfl, hl⟩, hk⟩
  · intro hp
    have hsel : ∀ s k, p ≠ (sel a b s, k) := by
      rintro s k rfl
      exact h.not_end_fire_sel s k hp
    have old : N.End ar p →
        (Pending ar N a b p ∧ ¬ ∃ q, IfcLink a b R p q) ∧ ¬ ∃ q, AgentLink a b R p q := by
      intro hE
      refine ⟨⟨⟨hE, hsel false 0, hsel true 0⟩, ?_⟩, ?_⟩
      · rintro ⟨q, s, k, s', k', -, e, -⟩
        exact hsel s (k + 1) e
      · rintro ⟨q, x, y, -, -, e, -⟩
        cases x with
        | ifc s k => exact hsel s (k + 1) e
        | new s j k =>
          subst e
          exact h.not_end_child s j k hE
    rcases hp with hf | ⟨γ, ⟨hg, -, -⟩ | ⟨s, j, e, hl⟩, hk⟩
    · exact .inl (old (.inl hf))
    · exact .inl (old (.inr ⟨γ, hg, hk⟩))
    · exact .inr ⟨s, j, p.2, γ, Prod.ext e rfl, hl, hk⟩

/-- Firing the same pair in two nets with the same agents, free ports and
pairing of ends joins every end of the two results to the same end. -/
theorem joint_fire {M : Net S} (h : Site ar N a b α β) (h' : Site ar M a b α β)
    (ho : N.ObsEq ar M) (hR : R.WF ar α β) :
    JointWired (N.fire a b R).link (M.fire a b R).link ((N.fire a b R).End ar) := by
  have hE : M.End ar = N.End ar := ho.end_eq.symm
  have W₁ := h.wf.wiring
  have W₂ : Wiring M.link (N.End ar) := hE ▸ h'.wf.wiring
  have J₀ : JointWired N.link M.link (N.End ar) := by
    intro t ht
    obtain ⟨t', ht', hne, c⟩ := h.wf.end_conn ht
    have c' : M.Conn ar t t' := ((ho.paired t t').1 ⟨ht, ht', c⟩).2.2
    refine ⟨t', ht', hne, c, ?_⟩
    rw [← hE]
    exact c'
  -- retire the two principal ports
  have J₁ : JointWired N.link M.link (Pending ar N a b) :=
    J₀.retire W₁ (.inr ⟨α, h.ha, Nat.zero_le _⟩) (.inr ⟨β, h.hb, Nat.zero_le _⟩) h.conn
  have W₁' : Wiring N.link (Pending ar N a b) := ⟨W₁.symm, W₁.deg, fun hp => W₁.term hp.1⟩
  have W₂' : Wiring M.link (Pending ar N a b) := ⟨W₂.symm, W₂.deg, fun hp => W₂.term hp.1⟩
  -- add the segments between auxiliary ports
  have J₂ := J₁.add_matching W₁' W₂' (auxPorts ar a b α β) (M := IfcLink a b R)
    (fun hl => ifcLink_symm hR hl)
    (fun hl => h.newLink_irrefl hR (newLink_iff.2 (.inl hl)))
    (fun hl hl' => h.newLink_unique hR (newLink_iff.2 (.inl hl)) (newLink_iff.2 (.inl hl')))
    (fun hl => h.ifcLink_pending hR hl)
    (fun hl => ifcLink_mem hR hl)
  -- attach the new agents
  have J₃ := J₂.attach (K := AgentLink a b R) (F := NewEnd ar a b R)
    (fun hl => hl.elim (fun x => .inl (h.wf.symm x)) (fun x => .inr (ifcLink_symm hR x)))
    (fun hl => hl.elim (fun x => .inl (h'.wf.symm x)) (fun x => .inr (ifcLink_symm hR x)))
    (fun hl => agentLink_symm hR hl)
    (fun hl => h.newLink_irrefl hR (newLink_iff.2 (.inr hl)))
    (fun hl hl' => h.newLink_unique hR (newLink_iff.2 (.inr hl)) (newLink_iff.2 (.inr hl')))
    (fun hl => agentLink_newEnd hR hl)
    (fun hl => h.agentLink_left hR hl)
    (fun hp => newEnd_agentLink hR hp)
    (fun hp => h.newEnd_not_link hp)
    (fun hp => h'.newEnd_not_link hp)
    (fun hp => h.newEnd_not_pending hp)
  have key : ∀ (X : Net S) (p q : Port),
      ((X.link p q ∨ IfcLink a b R p q) ∨ AgentLink a b R p q) ↔ (X.fire a b R).link p q := by
    intro X p q
    constructor
    · rintro ((hl | hl) | hl)
      · exact .inl hl
      · exact .inr (newLink_iff.2 (.inl hl))
      · exact .inr (newLink_iff.2 (.inr hl))
    · rintro (hl | hl)
      · exact .inl (.inl hl)
      · exact (newLink_iff.1 hl).elim (fun x => .inl (.inr x)) (fun x => .inr x)
  exact J₃.congr (key N) (key M) (h.end_fire_iff hR)

/-- After a firing, the wire leaving any end still reaches another end. -/
theorem wired_fire (h : Site ar N a b α β) (hR : R.WF ar α β) :
    Wired (N.fire a b R).link ((N.fire a b R).End ar) :=
  (h.joint_fire h (Net.ObsEq.refl N) hR).left

/-- **Subject reduction**: firing a rule at a site of a well-formed net yields
a well-formed net. -/
theorem fire_wf (h : Site ar N a b α β) (hR : R.WF ar α β) : (N.fire a b R).WF ar where
  agent_fun := by
    rintro i γ γ' (⟨h₁, -, -⟩ | ⟨s, j, rfl, h₁⟩) (⟨h₂, -, -⟩ | ⟨s', j', e, h₂⟩)
    · exact h.wf.agent_fun h₁ h₂
    · exact absurd (.inl ⟨_, h₁⟩) (e ▸ h.not_used_child s' j')
    · exact absurd (.inl ⟨_, h₂⟩) (h.not_used_child s j)
    · obtain ⟨rfl, rfl⟩ := h.child_inj e
      exact Option.some.inj (h₁.symm.trans h₂)
  symm := by
    rintro p q (hl | ⟨x, y, hxy, rfl, rfl⟩)
    · exact .inl (h.wf.symm hl)
    · exact .inr ⟨y, x, hR.symm hxy, rfl, rfl⟩
  irrefl := by
    rintro p (hl | ⟨x, y, hxy, e₁, e₂⟩)
    · exact h.wf.irrefl hl
    · obtain rfl := h.emb_inj (e₁.symm.trans e₂)
      exact hR.irrefl hxy
  end_unique := by
    rintro p q r hE (hq | hq) (hr | hr)
    · exact h.wf.end_unique (h.end_of_fire_link hE hq) hq hr
    · exact (h.end_fire_newLink hE hr hq).elim
    · exact (h.end_fire_newLink hE hq hr).elim
    · exact h.newLink_unique hR hq hr
  end_conn := fun hp => h.wired_fire hR _ hp
  deg := by
    rintro p x y z (hx | hx) (hy | hy) (hz | hz)
    · exact h.wf.deg hx hy hz
    · exact .inl (h.newLink_old_unique hR hz hx hy)
    · exact .inr (.inl (h.newLink_old_unique hR hy hx hz))
    · exact .inr (.inr (h.newLink_unique hR hy hz))
    · exact .inr (.inr (h.newLink_old_unique hR hx hy hz))
    · exact .inr (.inl (h.newLink_unique hR hx hz))
    · exact .inl (h.newLink_unique hR hx hy)
    · exact .inl (h.newLink_unique hR hx hy)
  free_agent := by
    rintro i k γ hf (⟨hg, -, -⟩ | ⟨s, j, rfl, -⟩)
    · exact h.wf.free_agent hf hg
    · exact h.not_used_child s j (.inr (.inr ⟨k, hf⟩))
  fresh := by
    rintro c γ l hc hu
    rcases h.used_fire hu with hu | ⟨s', j', e⟩
    · rcases hc with ⟨hg, -, -⟩ | ⟨s, j, rfl, -⟩
      · exact h.wf.fresh l hg hu
      · exact (h.not_used_desc s (slot s j) l hu).elim
    · cases l with
      | nil => rfl
      | cons x l' =>
        exfalso
        have e : l' ++ c = par a b s' := (List.cons.inj e).2
        rcases hc with ⟨hg, hca, hcb⟩ | ⟨s, j, rfl, -⟩
        · have hl' := h.wf.fresh l' hg (e ▸ h.used_par s')
          subst hl'
          rcases par_eq a b s' with e' | e'
          · exact hca (e.trans e')
          · exact hcb (e.trans e')
        · exact h.not_used_desc s (slot s j) l' (e ▸ h.used_par s')

/-- Wires that exist before a firing still exist after it. -/
theorem walk_fire (h : Site ar N a b α β) {u v x y : Port}
    (w : Walk N.link (N.End ar) u v x y) :
    Walk (N.fire a b R).link ((N.fire a b R).End ar) u v x y :=
  w.mono (fun hl => .inl hl) (fun hl hv hE => hv (h.end_of_fire_link hE (h.wf.symm hl)))

/-- Firing the same pair in two observationally equivalent nets gives
observationally equivalent nets. -/
theorem obsEq_fire {M : Net S} (h : Site ar N a b α β) (h' : Site ar M a b α β)
    (ho : N.ObsEq ar M) (hR : R.WF ar α β) : (N.fire a b R).ObsEq ar (M.fire a b R) := by
  have ha : ∀ i γ, (N.fire a b R).agent i γ ↔ (M.fire a b R).agent i γ :=
    fun i γ => or_congr (and_congr (ho.agent i γ) Iff.rfl) Iff.rfl
  have hE : ∀ p, (N.fire a b R).End ar p ↔ (M.fire a b R).End ar p :=
    Net.end_congr ha ho.free
  have hE' : (M.fire a b R).End ar = (N.fire a b R).End ar :=
    funext fun p => propext (hE p).symm
  have J := h.joint_fire h' ho hR
  have W₁ := (h.fire_wf hR).wiring
  have W₂ : Wiring (M.fire a b R).link ((N.fire a b R).End ar) :=
    hE' ▸ (h'.fire_wf hR).wiring
  refine ⟨ha, ho.free, fun p q => ⟨?_, ?_⟩⟩
  · rintro ⟨hp, hq, c⟩
    refine ⟨(hE p).1 hp, (hE q).1 hq, ?_⟩
    have c' := (J.conn_iff W₁ W₂ hp hq).1 c
    rw [← hE'] at c'
    exact c'
  · rintro ⟨hp, hq, c⟩
    have hp' := (hE p).2 hp
    have hq' := (hE q).2 hq
    refine ⟨hp', hq', (J.conn_iff W₁ W₂ hp' hq').2 ?_⟩
    rw [← hE']
    exact c

end Site

theorem port_ne_snd {i i' : Id} {k k' : Nat} (h : k ≠ k') : ((i, k) : Port) ≠ (i', k') :=
  fun e => h (congrArg Prod.snd e)

/-! ### Pairing of ends after a firing -/

theorem Net.Paired.symm {ar : S → Nat} {N : Net S} (hN : N.WF ar) {p q : Port}
    (h : N.Paired ar p q) : N.Paired ar q p :=
  ⟨h.2.1, h.1, h.2.2.symm hN⟩

/-- An end is paired with one end only. -/
theorem Net.Paired.det {ar : S → Nat} {N : Net S} (hN : N.WF ar) {p q q' : Port}
    (h : N.Paired ar p q) (h' : N.Paired ar p q') : q = q' :=
  Net.Conn.det hN h.1 h.2.1 h'.2.1 h.2.2 h'.2.2

theorem Net.Paired.det_left {ar : S → Nat} {N : Net S} (hN : N.WF ar) {p p' q : Port}
    (h : N.Paired ar p q) (h' : N.Paired ar p' q) : p = p' :=
  (h.symm hN).det hN (h'.symm hN)

/-- An end that is not on a fired agent is still an end. -/
theorem Net.End.fire {ar : S → Nat} {N : Net S} {a b : Id} {R : Rhs S} {p : Port}
    (hp : N.End ar p) (ha : p.1 ≠ a) (hb : p.1 ≠ b) : (N.fire a b R).End ar p := by
  rcases hp with hf | ⟨γ, hg, hk⟩
  · exact .inl hf
  · exact .inr ⟨γ, .inl ⟨hg, ha, hb⟩, hk⟩

namespace Site

variable {ar : S → Nat} {N : Net S} {a b : Id} {α β : S} {R : Rhs S}

/-- A wire between two ends that are not on the fired agents is still
there. -/
theorem paired_fire (h : Site ar N a b α β) {p q : Port} (hpq : N.Paired ar p q)
    (hpa : p.1 ≠ a) (hpb : p.1 ≠ b) (hqa : q.1 ≠ a) (hqb : q.1 ≠ b) :
    (N.fire a b R).Paired ar p q := by
  obtain ⟨hp, hq, v, x, w⟩ := hpq
  exact ⟨hp.fire hpa hpb, hq.fire hqa hqb, v, x, h.walk_fire w⟩

/-- A wire of the right-hand side between a new agent and the interface
extends the wire that arrived at that auxiliary port. -/
theorem paired_fire_ifc_new (h : Site ar N a b α β) (hR : R.WF ar α β) {s : Bool} {k : Nat}
    {o : Option Bool} {j k' : Nat} (hl : R.link (.ifc s k) (.new o j k')) {p : Port}
    (hp : N.Paired ar p (sel a b s, k + 1)) (hpa : p.1 ≠ a) (hpb : p.1 ≠ b) :
    (N.fire a b R).Paired ar p (child a b o j, k') := by
  obtain ⟨hpE, -, v, x, w⟩ := hp
  have w' := h.walk_fire (R := R) w
  have hA : ¬ (N.fire a b R).End ar (sel a b s, k + 1) := h.not_end_fire_sel s _
  have hnew : (N.fire a b R).link (sel a b s, k + 1) (child a b o j, k') :=
    .inr ⟨_, _, hl, rfl, rfl⟩
  have hx : (child a b o j, k') ≠ x := by
    rintro rfl
    exact h.not_used_child o j (.inr (.inl ⟨k', _, w.link_last⟩))
  have hE : (N.fire a b R).End ar (child a b o j, k') := by
    obtain ⟨γ, hγ, hk⟩ := hR.valid (hR.symm hl)
    exact .inr ⟨γ, .inr ⟨o, j, rfl, hγ⟩, hk⟩
  exact ⟨hpE.fire hpa hpb, hE, v, _, w'.snoc hA hnew hx⟩

/-- A wire of the right-hand side between two interface ports joins the two
wires that arrived there. -/
theorem paired_fire_ifc_ifc (h : Site ar N a b α β) {s s' : Bool} {k k' : Nat}
    (hl : R.link (.ifc s k) (.ifc s' k')) {p q : Port}
    (hp : N.Paired ar p (sel a b s, k + 1)) (hq : N.Paired ar q (sel a b s', k' + 1))
    (hpa : p.1 ≠ a) (hpb : p.1 ≠ b) (hqa : q.1 ≠ a) (hqb : q.1 ≠ b) :
    (N.fire a b R).Paired ar p q := by
  obtain ⟨hpE, hAE, v, x, w⟩ := hp
  obtain ⟨hqE, hBE, c⟩ := hq
  obtain ⟨z, y, w₂⟩ := c.symm h.wf
  have w' := h.walk_fire (R := R) w
  have w₂' := h.walk_fire (R := R) w₂
  have hA : ¬ (N.fire a b R).End ar (sel a b s, k + 1) := h.not_end_fire_sel s _
  have hB : ¬ (N.fire a b R).End ar (sel a b s', k' + 1) := h.not_end_fire_sel s' _
  have hnew : (N.fire a b R).link (sel a b s, k + 1) (sel a b s', k' + 1) :=
    .inr ⟨_, _, hl, rfl, rfl⟩
  have hx : (sel a b s', k' + 1) ≠ x := by
    rintro rfl
    rcases w.penult with e | hT
    · have e' : sel a b s' = p.1 := congrArg Prod.fst e
      cases s'
      · exact hpa e'.symm
      · exact hpb e'.symm
    · exact hT hBE
  have hz : z ≠ (sel a b s, k + 1) := by
    rintro rfl
    cases w₂ with
    | single _ =>
      cases s
      · exact hqa rfl
      · exact hqb rfl
    | cons _ hv _ _ => exact hv hAE
  exact ⟨hpE.fire hpa hpb, hqE.fire hqa hqb, v, y, (w'.snoc hA hnew hx).append hB w₂' hz⟩

/-- A wire of the right-hand side between two new agents is a wire of the
net. -/
theorem paired_fire_new_new (hR : R.WF ar α β) {o o' : Option Bool} {j k j' k' : Nat}
    (hl : R.link (.new o j k) (.new o' j' k')) :
    (N.fire a b R).Paired ar (child a b o j, k) (child a b o' j', k') := by
  obtain ⟨γ, hγ, hk⟩ := hR.valid hl
  obtain ⟨γ', hγ', hk'⟩ := hR.valid (hR.symm hl)
  exact ⟨.inr ⟨γ, .inr ⟨o, j, rfl, hγ⟩, hk⟩, .inr ⟨γ', .inr ⟨o', j', rfl, hγ'⟩, hk'⟩, _, _,
    .single (.inr ⟨_, _, hl, rfl, rfl⟩)⟩

end Site

end INet
