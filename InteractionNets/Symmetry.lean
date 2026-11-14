import InteractionNets.Time

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### Checking the invariant

The invariant `XNet.Ok` is decidable: `XNet.check` evaluates to `true`
exactly on the nets that satisfy it. -/

/-- The ends of a finite net: its free ports and the ports of its agents. -/
def XNet.ends (ar : S → Nat) (X : XNet S) : List Port :=
  X.free ++ X.agents.flatMap fun e => (List.range (ar e.2 + 1)).map fun k => (e.1, k)

theorem XNet.mem_ends {ar : S → Nat} {X : XNet S} {p : Port} :
    p ∈ X.ends ar ↔ X.toNet.End ar p := by
  unfold XNet.ends
  rw [List.mem_append, List.mem_flatMap]
  constructor
  · rintro (hf | ⟨⟨i, γ⟩, he, hp⟩)
    · exact .inl hf
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
      exact .inr ⟨γ, he, Nat.le_of_lt_succ (List.mem_range.1 hk)⟩
  · rintro (hf | ⟨γ, hg, hk⟩)
    · exact .inl hf
    · exact .inr ⟨(p.1, γ), hg,
        List.mem_map.2 ⟨p.2, List.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩⟩

/-- The identifiers in use in a finite net. -/
def XNet.ids (X : XNet S) : List Id := X.agents.map (·.1) ++ X.free.map (·.1)

/-- `a` is a suffix of `u`. -/
def endsWith (u a : Id) : Bool := decide (u.drop (u.length - a.length) = a)

theorem drop_length_append (l a : Id) : (l ++ a).drop l.length = a := by
  simp

theorem endsWith_append (l a : Id) : endsWith (l ++ a) a = true := by
  have e : (l ++ a).length - a.length = l.length := by
    rw [List.length_append]
    omega
  unfold endsWith
  rw [e, drop_length_append]
  exact decide_eq_true rfl

theorem append_of_endsWith {u a : Id} (h : endsWith u a = true) : ∃ l, u = l ++ a := by
  have h' : u.drop (u.length - a.length) = a := of_decide_eq_true h
  have e := List.take_append_drop (u.length - a.length) u
  rw [h'] at e
  exact ⟨_, e.symm⟩

/-- The executable check of the invariant. -/
def XNet.check [DecidableEq S] (ar : S → Nat) (X : XNet S) : Bool :=
  -- an agent has one symbol
  X.agents.all (fun e => decide (assoc e.1 X.agents = some e.2)) &&
  -- a port has one partner, which has it as its partner, and is another port
  X.wires.all (fun e => decide (assoc e.1 X.wires = some e.2)) &&
  X.wires.all (fun e => decide ((e.2, e.1) ∈ X.wires)) &&
  X.wires.all (fun e => decide (e.1 ≠ e.2)) &&
  -- the wires run between ends, and every end is on a wire
  X.wires.all (fun e => decide (e.1 ∈ X.ends ar)) &&
  (X.ends ar).all (fun p => (assoc p X.wires).isSome) &&
  -- free ports are not ports of agents
  X.free.all (fun p => (assoc p.1 X.agents).isNone) &&
  -- no identifier in use extends the identifier of an agent
  X.agents.all (fun e => X.ids.all fun u => decide (endsWith u e.1 = true → u = e.1))

/-- What the check establishes. -/
structure XNet.Checked (ar : S → Nat) (X : XNet S) : Prop where
  agents : ∀ e ∈ X.agents, assoc e.1 X.agents = some e.2
  wires : ∀ e ∈ X.wires, assoc e.1 X.wires = some e.2
  symm : ∀ e ∈ X.wires, (e.2, e.1) ∈ X.wires
  irrefl : ∀ e ∈ X.wires, e.1 ≠ e.2
  ends : ∀ e ∈ X.wires, e.1 ∈ X.ends ar
  wired : ∀ p ∈ X.ends ar, (assoc p X.wires).isSome = true
  free : ∀ p ∈ X.free, (assoc p.1 X.agents).isNone = true
  fresh : ∀ e ∈ X.agents, ∀ u ∈ X.ids, endsWith u e.1 = true → u = e.1

theorem XNet.check_iff [DecidableEq S] {ar : S → Nat} {X : XNet S} :
    X.check ar = true ↔ X.Checked ar := by
  simp only [XNet.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    exact ⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩

/-- A net that passes the check satisfies the invariant. -/
theorem XNet.Checked.ok {ar : S → Nat} {X : XNet S} (h : X.Checked ar) : X.Ok ar := by
  have hfun : ∀ {p q q' : Port}, (p, q) ∈ X.wires → (p, q') ∈ X.wires → q = q' :=
    fun h₁ h₂ => Option.some.inj ((h.wires _ h₁).symm.trans (h.wires _ h₂))
  have hend : ∀ {p q : Port}, (p, q) ∈ X.wires → X.toNet.End ar p ∧ X.toNet.End ar q :=
    fun hm => ⟨XNet.mem_ends.1 (h.ends _ hm), XNet.mem_ends.1 (h.ends _ (h.symm _ hm))⟩
  have hused : ∀ {i : Id}, X.toNet.Used i → i ∈ X.ids := by
    rintro i (⟨γ, hg⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩)
    · exact List.mem_append.2 (.inl (List.mem_map.2 ⟨(i, γ), hg, rfl⟩))
    · rcases (hend hl).1 with hf | ⟨γ, hg, -⟩
      · exact List.mem_append.2 (.inr (List.mem_map.2 ⟨(i, k), hf, rfl⟩))
      · exact List.mem_append.2 (.inl (List.mem_map.2 ⟨(i, γ), hg, rfl⟩))
    · exact List.mem_append.2 (.inr (List.mem_map.2 ⟨(i, k), hf, rfl⟩))
  have wf : X.toNet.WF ar :=
    { agent_fun := fun h₁ h₂ => Option.some.inj ((h.agents _ h₁).symm.trans (h.agents _ h₂))
      symm := fun hl => h.symm _ hl
      irrefl := fun hl => h.irrefl _ hl rfl
      end_unique := fun _ h₁ h₂ => hfun h₁ h₂
      end_conn := fun {p} hp => by
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (h.wired p (XNet.mem_ends.2 hp))
        have hm := assoc_mem hq
        exact ⟨q, (hend hm).2, fun e => h.irrefl _ hm e.symm, q, p, .single hm⟩
      deg := fun h₁ h₂ _ => .inl (hfun h₁ h₂)
      free_agent := fun {i k α} hf hg => by
        have hn : (assoc i X.agents).isNone = true := h.free (i, k) hf
        obtain ⟨γ', e⟩ := assoc_of_mem hg
        rw [e] at hn
        cases hn
      fresh := fun {a α} l ha hu => by
        have e : l ++ a = a := h.fresh (a, α) ha _ (hused hu) (endsWith_append l a)
        have hlen := congrArg List.length e
        rw [List.length_append] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega) }
  refine ⟨wf, Net.ext' (fun _ _ => Iff.rfl) (fun p q => ⟨?_, ?_⟩) (fun _ => Iff.rfl)⟩
  · rintro ⟨hp, hq, c⟩
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 (h.wired p (XNet.mem_ends.2 hp))
    have hm := assoc_mem hq'
    obtain rfl := Net.Conn.det wf hp hq (hend hm).2 c ⟨q', p, .single hm⟩
    exact hm
  · intro hm
    exact ⟨(hend hm).1, (hend hm).2, q, p, .single hm⟩

/-- A net that satisfies the invariant passes the check. -/
theorem XNet.Ok.checked {ar : S → Nat} {X : XNet S} (h : X.Ok ar) : X.Checked ar where
  agents := by
    rintro ⟨i, γ⟩ he
    obtain ⟨γ', e⟩ := assoc_of_mem he
    exact e.trans (congrArg some (h.1.agent_fun (assoc_mem e) he))
  wires := by
    rintro ⟨p, q⟩ he
    exact h.exact.assoc_eq h.1.wiring he
  symm := fun _ he => h.1.symm he
  irrefl := by
    rintro ⟨p, q⟩ he hpq
    have hpq' : p = q := hpq
    subst hpq'
    exact h.1.irrefl he
  ends := fun _ he => XNet.mem_ends.2 (h.link_iff.1 he).1
  wired := by
    intro p hp
    obtain ⟨q, hq, -, c⟩ := h.1.end_conn (XNet.mem_ends.1 hp)
    obtain ⟨q', e⟩ := assoc_of_mem (h.link_iff.2 ⟨XNet.mem_ends.1 hp, hq, c⟩)
    rw [e]
    rfl
  free := by
    rintro ⟨i, k⟩ hp
    show (assoc i X.agents).isNone = true
    cases e : assoc i X.agents with
    | none => rfl
    | some γ => exact absurd (assoc_mem e) (h.1.free_agent hp)
  fresh := by
    rintro ⟨a, α⟩ he u hu hs
    obtain ⟨l, rfl⟩ := append_of_endsWith hs
    have hused : X.toNet.Used (l ++ a) := by
      rcases List.mem_append.1 hu with hu | hu
      · obtain ⟨⟨i, γ⟩, hm, e⟩ := List.mem_map.1 hu
        have e' : i = l ++ a := e
        subst e'
        exact .inl ⟨γ, hm⟩
      · obtain ⟨⟨i, k⟩, hm, e⟩ := List.mem_map.1 hu
        have e' : i = l ++ a := e
        subst e'
        exact .inr (.inr ⟨k, hm⟩)
    show l ++ a = a
    rw [h.1.fresh l he hused]
    rfl

/-- **The check decides the invariant.** -/
theorem XNet.check_iff_ok [DecidableEq S] {ar : S → Nat} {X : XNet S} :
    X.check ar = true ↔ X.Ok ar :=
  ⟨fun h => (XNet.check_iff.1 h).ok, fun h => XNet.check_iff.2 h.checked⟩

instance [DecidableEq S] (ar : S → Nat) (X : XNet S) : Decidable (X.Ok ar) :=
  decidable_of_iff _ XNet.check_iff_ok

/-- Validate the input, run the reducer for at most `fuel` steps, and return
the net reached and the number of steps taken if the reducer has stopped. -/
def XNet.normalize [DecidableEq S] (xs : XSys S) (fuel : Nat) (X : XNet S) :
    Option (XNet S × Nat) :=
  if X.check xs.sys.ar then
    if ((X.run xs fuel).1.step xs).isNone then some (X.run xs fuel) else none
  else none

/-- **Specification of `normalize`**: whatever it returns is the normal form
of its input, reached in the number of steps it reports; that number is the
length of every reduction to normal form, and no reduction is longer.  There
is nothing left for the caller to prove. -/
theorem XNet.normalize_spec [DecidableEq S] {xs : XSys S} {X Y : XNet S} {n k : Nat}
    (h : X.normalize xs n = some (Y, k)) :
    X.Ok xs.sys.ar ∧ Y.Ok xs.sys.ar ∧ Steps (CStep xs.sys) k X.toNet Y.toNet ∧
      Normal (CStep xs.sys) Y.toNet ∧
      ∀ {m : Nat} {C : Net S}, Steps (CStep xs.sys) m X.toNet C →
        m ≤ k ∧ (Normal (CStep xs.sys) C → C = Y.toNet ∧ m = k) := by
  unfold XNet.normalize at h
  split at h
  · rename_i hc
    have hX := XNet.check_iff_ok.1 hc
    split at h
    · rename_i hs
      have e : X.run xs n = (Y, k) := Option.some.inj h
      have hstop : (X.run xs n).1.step xs = none := Option.isNone_iff_eq_none.1 hs
      obtain ⟨sts, hY⟩ := XNet.run_steps hX n
      obtain ⟨hn, hb⟩ := XNet.run_normal hX n hstop
      rw [e] at sts hY hn hb
      exact ⟨hX, hY, sts, hn, hb⟩
    · cases h
  · cases h

/-- **Completeness of `normalize`**: if the input satisfies the invariant
and has a normal form `C` reached in `k` steps, then with fuel at least `k`
it returns a net that stands for `C`, together with `k`. -/
theorem XNet.normalize_complete [DecidableEq S] {xs : XSys S} {X : XNet S}
    (hX : X.Ok xs.sys.ar) {k n : Nat} {C : Net S}
    (hC : Steps (CStep xs.sys) k X.toNet C) (hn : Normal (CStep xs.sys) C) (hk : k ≤ n) :
    ∃ Y, X.normalize xs n = some (Y, k) ∧ Y.toNet = C := by
  obtain ⟨stop, e₁, e₂⟩ := XNet.run_complete hX hC hn hk
  refine ⟨(X.run xs n).1, ?_, e₂⟩
  have hc : X.check xs.sys.ar = true := XNet.check_iff_ok.2 hX
  have hs : ((X.run xs n).1.step xs).isNone = true := by
    rw [stop]
    rfl
  simp only [XNet.normalize, hc, hs, ↓reduceIte]
  exact congrArg some (Prod.ext rfl e₁)

/-! ### Lafont's symmetry condition

A `System` asks that the rule of two equal symbols be its own mirror image,
where the mirror image exchanges the agents owned by the two sides.  Lafont
asks less, on the face of it: that some symmetry of the right-hand side
exchange the two sides of the interface.  The two are the same up to the
numbering of the agents.  A symmetry moves every agent that is connected to
the interface, and moves it back, because it moves every port of the
interface; so those agents come in pairs, one for each side, and the others
can be left where they are. -/

section Lafont

/-- Exchange the two sides of the interface, and move the new agents owned
by neither side as `σ` says. -/
def LPort.flipBy (σ : Nat → Nat) : LPort → LPort
  | .ifc s k => .ifc (!s) k
  | .new none j k => .new none (σ j) k
  | .new (some b) j k => .new (some b) j k

/-- **Lafont's symmetry condition**, for a right-hand side of `α ⋈ α` given
without owners: its new agents are numbered, all of them owned by neither
side, and exchanging the two sides of the interface while moving the agents
as `σ` says keeps the symbols and the wires. -/
structure Rhs.Lafont (R : Rhs S) (σ : Nat → Nat) : Prop where
  unowned : ∀ b j, R.lab (some b) j = none
  lab : ∀ j, R.lab none (σ j) = R.lab none j
  link : ∀ {x y}, R.link x y → R.link (x.flipBy σ) (y.flipBy σ)

/-- The new agents that are connected to the interface. -/
inductive Rhs.Reach (R : Rhs S) : Nat → Prop
  | base {s : Bool} {k j k' : Nat} : R.link (.ifc s k) (.new none j k') → Rhs.Reach R j
  | step {i k j k' : Nat} :
      Rhs.Reach R i → R.link (.new none i k) (.new none j k') → Rhs.Reach R j

/-- **An agent connected to the interface is exchanged with a different
agent**, and exchanged back: the symmetry is an involution without fixed
agents there, because it moves every port of the interface. -/
theorem Rhs.Lafont.reach {ar : S → Nat} {α : S} {R : Rhs S} {σ : Nat → Nat}
    (hσ : R.Lafont σ) (hR : R.WF ar α α) {j : Nat} (h : R.Reach j) :
    σ (σ j) = j ∧ σ j ≠ j ∧ R.Reach (σ j) := by
  induction h with
  | @base s k j k' hl =>
    have h₁ : R.link (.ifc (!s) k) (.new none (σ j) k') := hσ.link hl
    have h₂ : R.link (.ifc (!!s) k) (.new none (σ (σ j)) k') := hσ.link h₁
    rw [Bool.not_not] at h₂
    refine ⟨((LPort.new.inj (hR.unique hl h₂)).2.1).symm, fun e => ?_, .base h₁⟩
    rw [e] at h₁
    have e' := (LPort.ifc.inj (hR.unique (hR.symm hl) (hR.symm h₁))).1
    exact absurd e' (by cases s <;> decide)
  | @step i k j k' _ hl ih =>
    obtain ⟨e₁, n₁, r₁⟩ := ih
    have h₁ : R.link (.new none (σ i) k) (.new none (σ j) k') := hσ.link hl
    have h₂ : R.link (.new none (σ (σ i)) k) (.new none (σ (σ j)) k') := hσ.link h₁
    rw [e₁] at h₂
    refine ⟨((LPort.new.inj (hR.unique hl h₂)).2.1).symm, fun e => ?_, .step r₁ h₁⟩
    rw [e] at h₁
    exact n₁ ((LPort.new.inj (hR.unique (hR.symm hl) (hR.symm h₁))).2.1).symm

/-- Renumber the new agents of a right-hand side. -/
def LPort.renum (e : Option Bool → Nat → Option Bool × Nat) : LPort → LPort
  | .ifc s k => .ifc s k
  | .new o j k => .new (e o j).1 (e o j).2 k

/-- `R'` is `R` with its new agents renumbered by `e`: different agents get
different numbers, every agent of `R'` is one of `R` with the same symbol,
and the wires are the same. -/
structure Rhs.Renum (e : Option Bool → Nat → Option Bool × Nat) (R R' : Rhs S) : Prop where
  inj : ∀ {o j o' j' γ γ'}, R.lab o j = some γ → R.lab o' j' = some γ' → e o j = e o' j' →
    o = o' ∧ j = j'
  lab : ∀ {o j γ}, R.lab o j = some γ → R'.lab (e o j).1 (e o j).2 = some γ
  onto : ∀ {o' j' γ}, R'.lab o' j' = some γ → ∃ o j, e o j = (o', j') ∧ R.lab o j = some γ
  link : ∀ x y, R'.link x y ↔ ∃ p q, x = p.renum e ∧ y = q.renum e ∧ R.link p q

open Classical in
/-- Owners for the agents of a symmetric right-hand side: of two agents that
the symmetry exchanges, the one with the smaller number goes to the first
side and the other to the second, under the same number; an agent that is
not connected to the interface is owned by neither side. -/
noncomputable def Rhs.own (R : Rhs S) (σ : Nat → Nat) : Option Bool → Nat → Option Bool × Nat
  | none, j =>
    if R.Reach j then (if j < σ j then (some false, j) else (some true, σ j)) else (none, j)
  | some b, j => (some b, j)

open Classical in
theorem Rhs.own_far {R : Rhs S} {σ : Nat → Nat} {j : Nat} (h : ¬ R.Reach j) :
    R.own σ none j = (none, j) := ite_neg' h

open Classical in
theorem Rhs.own_lt {R : Rhs S} {σ : Nat → Nat} {j : Nat} (h : R.Reach j) (l : j < σ j) :
    R.own σ none j = (some false, j) := (ite_pos' h).trans (ite_pos' l)

open Classical in
theorem Rhs.own_ge {R : Rhs S} {σ : Nat → Nat} {j : Nat} (h : R.Reach j) (l : ¬ j < σ j) :
    R.own σ none j = (some true, σ j) := (ite_pos' h).trans (ite_neg' l)

open Classical in
/-- The right-hand side with those owners. -/
noncomputable def Rhs.owned (R : Rhs S) (σ : Nat → Nat) : Rhs S where
  lab
    | none, j => if R.Reach j then none else R.lab none j
    | some _, j => if R.Reach j ∧ j < σ j then R.lab none j else none
  link x y := ∃ p q, x = p.renum (R.own σ) ∧ y = q.renum (R.own σ) ∧ R.link p q

open Classical in
theorem Rhs.owned_lab_far {R : Rhs S} {σ : Nat → Nat} {j : Nat} (h : ¬ R.Reach j) :
    (R.owned σ).lab none j = R.lab none j := ite_neg' h

open Classical in
theorem Rhs.owned_lab_near {R : Rhs S} {σ : Nat → Nat} {j : Nat} (h : R.Reach j) :
    (R.owned σ).lab none j = none := ite_pos' h

open Classical in
theorem Rhs.owned_lab_some {R : Rhs S} {σ : Nat → Nat} {j : Nat} (b : Bool)
    (h : R.Reach j ∧ j < σ j) : (R.owned σ).lab (some b) j = R.lab none j := ite_pos' h

open Classical in
theorem Rhs.owned_lab_some_neg {R : Rhs S} {σ : Nat → Nat} {j : Nat} (b : Bool)
    (h : ¬ (R.Reach j ∧ j < σ j)) : (R.owned σ).lab (some b) j = none := ite_neg' h

open Classical in
/-- The symmetry on the agents connected to the interface, and nothing
elsewhere. -/
noncomputable def Rhs.turn (R : Rhs S) (σ : Nat → Nat) : LPort → LPort
  | .ifc s k => .ifc (!s) k
  | .new none j k => if R.Reach j then .new none (σ j) k else .new none j k
  | .new (some b) j k => .new (some b) j k

open Classical in
theorem Rhs.turn_near {R : Rhs S} {σ : Nat → Nat} {j : Nat} (k : Nat) (h : R.Reach j) :
    R.turn σ (.new none j k) = .new none (σ j) k := ite_pos' h

open Classical in
theorem Rhs.turn_far {R : Rhs S} {σ : Nat → Nat} {j : Nat} (k : Nat) (h : ¬ R.Reach j) :
    R.turn σ (.new none j k) = .new none j k := ite_neg' h

namespace Rhs.Lafont

variable {ar : S → Nat} {α : S} {R : Rhs S} {σ : Nat → Nat}

theorem valid_new (hσ : R.Lafont σ) {o : Option Bool} {j k : Nat}
    (h : R.Valid ar α α (.new o j k)) : o = none := by
  obtain ⟨γ, hl, -⟩ := h
  cases o with
  | none => rfl
  | some b =>
    rw [hσ.unowned] at hl
    cases hl

theorem own_inj (hσ : R.Lafont σ) (hR : R.WF ar α α) {j j' : Nat}
    (e : R.own σ none j = R.own σ none j') : j = j' := by
  by_cases h : R.Reach j
  · obtain ⟨s₁, -, -⟩ := hσ.reach hR h
    by_cases h' : R.Reach j'
    · obtain ⟨s₂, -, -⟩ := hσ.reach hR h'
      by_cases l : j < σ j
      · by_cases l' : j' < σ j'
        · rw [Rhs.own_lt h l, Rhs.own_lt h' l'] at e
          exact (Prod.mk.inj e).2
        · rw [Rhs.own_lt h l, Rhs.own_ge h' l'] at e
          cases (Prod.mk.inj e).1
      · by_cases l' : j' < σ j'
        · rw [Rhs.own_ge h l, Rhs.own_lt h' l'] at e
          cases (Prod.mk.inj e).1
        · rw [Rhs.own_ge h l, Rhs.own_ge h' l'] at e
          exact s₁.symm.trans ((congrArg σ (Prod.mk.inj e).2).trans s₂)
    · rw [Rhs.own_far h'] at e
      by_cases l : j < σ j
      · rw [Rhs.own_lt h l] at e
        cases (Prod.mk.inj e).1
      · rw [Rhs.own_ge h l] at e
        cases (Prod.mk.inj e).1
  · rw [Rhs.own_far h] at e
    by_cases h' : R.Reach j'
    · by_cases l' : j' < σ j'
      · rw [Rhs.own_lt h' l'] at e
        cases (Prod.mk.inj e).1
      · rw [Rhs.own_ge h' l'] at e
        cases (Prod.mk.inj e).1
    · rw [Rhs.own_far h'] at e
      exact (Prod.mk.inj e).2

theorem own_lab (hσ : R.Lafont σ) (hR : R.WF ar α α) {j : Nat} {γ : S}
    (hl : R.lab none j = some γ) :
    (R.owned σ).lab (R.own σ none j).1 (R.own σ none j).2 = some γ := by
  by_cases h : R.Reach j
  · obtain ⟨s₁, n₁, r₁⟩ := hσ.reach hR h
    by_cases l : j < σ j
    · rw [Rhs.own_lt h l]
      show (R.owned σ).lab (some false) j = some γ
      rw [Rhs.owned_lab_some false ⟨h, l⟩]
      exact hl
    · rw [Rhs.own_ge h l]
      show (R.owned σ).lab (some true) (σ j) = some γ
      rw [Rhs.owned_lab_some true ⟨r₁, by rw [s₁]; omega⟩, hσ.lab]
      exact hl
  · rw [Rhs.own_far h]
    show (R.owned σ).lab none j = some γ
    rw [Rhs.owned_lab_far h]
    exact hl

theorem own_onto (hσ : R.Lafont σ) (hR : R.WF ar α α) {o' : Option Bool} {j' : Nat} {γ : S}
    (hl : (R.owned σ).lab o' j' = some γ) :
    ∃ j, R.own σ none j = (o', j') ∧ R.lab none j = some γ := by
  cases o' with
  | none =>
    by_cases h : R.Reach j'
    · rw [Rhs.owned_lab_near h] at hl
      cases hl
    · rw [Rhs.owned_lab_far h] at hl
      exact ⟨j', Rhs.own_far h, hl⟩
  | some b =>
    by_cases h : R.Reach j' ∧ j' < σ j'
    · rw [Rhs.owned_lab_some b h] at hl
      obtain ⟨s₁, -, r₁⟩ := hσ.reach hR h.1
      cases b with
      | false => exact ⟨j', Rhs.own_lt h.1 h.2, hl⟩
      | true =>
        refine ⟨σ j', ?_, by rw [hσ.lab]; exact hl⟩
        rw [Rhs.own_ge r₁ (by rw [s₁]; omega), s₁]
    · rw [Rhs.owned_lab_some_neg b h] at hl
      cases hl

theorem renum_inj (hσ : R.Lafont σ) (hR : R.WF ar α α) {p q : LPort}
    (hp : R.Valid ar α α p) (hq : R.Valid ar α α q)
    (e : p.renum (R.own σ) = q.renum (R.own σ)) : p = q := by
  cases p with
  | ifc s k =>
    cases q with
    | ifc s' k' => exact e
    | new o' j' k' =>
      have e' : LPort.ifc s k = LPort.new (R.own σ o' j').1 (R.own σ o' j').2 k' := e
      cases e'
  | new o j k =>
    cases q with
    | ifc s' k' =>
      have e' : LPort.new (R.own σ o j).1 (R.own σ o j).2 k = LPort.ifc s' k' := e
      cases e'
    | new o' j' k' =>
      have ho := hσ.valid_new hp
      have ho' := hσ.valid_new hq
      subst ho
      subst ho'
      have e' : LPort.new (R.own σ none j).1 (R.own σ none j).2 k =
          LPort.new (R.own σ none j').1 (R.own σ none j').2 k' := e
      obtain ⟨e₁, e₂, e₃⟩ := LPort.new.inj e'
      rw [hσ.own_inj hR (Prod.ext e₁ e₂), e₃]

theorem valid_renum (hσ : R.Lafont σ) (hR : R.WF ar α α) {p : LPort}
    (hp : R.Valid ar α α p) : (R.owned σ).Valid ar α α (p.renum (R.own σ)) := by
  cases p with
  | ifc s k => exact hp
  | new o j k =>
    have ho := hσ.valid_new hp
    subst ho
    obtain ⟨γ, hl, hk⟩ := hp
    exact ⟨γ, hσ.own_lab hR hl, hk⟩

theorem valid_of_owned (hσ : R.Lafont σ) (hR : R.WF ar α α) {x : LPort}
    (hx : (R.owned σ).Valid ar α α x) : ∃ p, x = p.renum (R.own σ) ∧ R.Valid ar α α p := by
  cases x with
  | ifc s k => exact ⟨.ifc s k, rfl, hx⟩
  | new o' j' k =>
    obtain ⟨γ, hl, hk⟩ := hx
    obtain ⟨j, e, hl'⟩ := hσ.own_onto hR hl
    refine ⟨.new none j k, ?_, γ, hl', hk⟩
    show LPort.new o' j' k = LPort.new (R.own σ none j).1 (R.own σ none j).2 k
    rw [e]

/-- The right-hand side with owners is a right-hand side. -/
theorem owned_wf (hσ : R.Lafont σ) (hR : R.WF ar α α) : (R.owned σ).WF ar α α where
  symm := by
    rintro x y ⟨p, q, rfl, rfl, h⟩
    exact ⟨q, p, rfl, rfl, hR.symm h⟩
  irrefl := by
    rintro x ⟨p, q, e₁, e₂, h⟩
    have e := hσ.renum_inj hR (hR.valid h) (hR.valid (hR.symm h)) (e₁.symm.trans e₂)
    rw [e] at h
    exact hR.irrefl h
  valid := by
    rintro x y ⟨p, q, rfl, rfl, h⟩
    exact hσ.valid_renum hR (hR.valid h)
  unique := by
    rintro x y z ⟨p, q, e₁, rfl, h⟩ ⟨p', q', e₁', rfl, h'⟩
    have e := hσ.renum_inj hR (hR.valid h) (hR.valid h') (e₁.symm.trans e₁')
    rw [e] at h
    rw [hR.unique h h']
  total := by
    intro x hx
    obtain ⟨p, rfl, hp⟩ := hσ.valid_of_owned hR hx
    obtain ⟨q, h⟩ := hR.total hp
    exact ⟨q.renum _, p, q, rfl, rfl, h⟩

theorem turn_link (hσ : R.Lafont σ) (hR : R.WF ar α α) {p q : LPort} (h : R.link p q) :
    R.link (R.turn σ p) (R.turn σ q) := by
  have vp := hR.valid h
  have vq := hR.valid (hR.symm h)
  cases p with
  | ifc s k =>
    cases q with
    | ifc s' k' => exact hσ.link h
    | new o j k' =>
      have ho := hσ.valid_new vq
      subst ho
      rw [Rhs.turn_near k' (.base h)]
      exact hσ.link h
  | new o i k =>
    have ho := hσ.valid_new vp
    subst ho
    cases q with
    | ifc s' k' =>
      rw [Rhs.turn_near k (.base (hR.symm h))]
      exact hσ.link h
    | new o' j k' =>
      have ho' := hσ.valid_new vq
      subst ho'
      by_cases r : R.Reach i
      · rw [Rhs.turn_near k r, Rhs.turn_near k' (.step r h)]
        exact hσ.link h
      · have r' : ¬ R.Reach j := fun rj => r (.step rj (hR.symm h))
        rw [Rhs.turn_far k r, Rhs.turn_far k' r']
        exact h

theorem turn_renum (hσ : R.Lafont σ) (hR : R.WF ar α α) {p : LPort}
    (hp : R.Valid ar α α p) :
    (R.turn σ p).renum (R.own σ) = (p.renum (R.own σ)).swap := by
  cases p with
  | ifc s k => rfl
  | new o j k =>
    have ho := hσ.valid_new hp
    subst ho
    by_cases r : R.Reach j
    · obtain ⟨s₁, n₁, r₁⟩ := hσ.reach hR r
      rw [Rhs.turn_near k r]
      show LPort.new (R.own σ none (σ j)).1 (R.own σ none (σ j)).2 k =
        (LPort.new (R.own σ none j).1 (R.own σ none j).2 k).swap
      by_cases l : j < σ j
      · rw [Rhs.own_lt r l, Rhs.own_ge r₁ (by rw [s₁]; omega), s₁]
        rfl
      · rw [Rhs.own_ge r l, Rhs.own_lt r₁ (by rw [s₁]; omega)]
        rfl
    · rw [Rhs.turn_far k r]
      show LPort.new (R.own σ none j).1 (R.own σ none j).2 k =
        (LPort.new (R.own σ none j).1 (R.own σ none j).2 k).swap
      rw [Rhs.own_far r]
      rfl

/-- It is its own mirror image. -/
theorem owned_mirror (hσ : R.Lafont σ) (hR : R.WF ar α α) :
    (R.owned σ).Mirror (R.owned σ) := by
  have fwd : ∀ x y, (R.owned σ).link x y → (R.owned σ).link x.swap y.swap := by
    rintro x y ⟨p, q, rfl, rfl, h⟩
    exact ⟨R.turn σ p, R.turn σ q, (hσ.turn_renum hR (hR.valid h)).symm,
      (hσ.turn_renum hR (hR.valid (hR.symm h))).symm, hσ.turn_link hR h⟩
  refine ⟨fun o j => ?_, fun x y => ⟨fwd x y, fun h => ?_⟩⟩
  · cases o with
    | none => rfl
    | some b => rfl
  · have h' := fwd _ _ h
    rw [LPort.swap_swap, LPort.swap_swap] at h'
    exact h'

/-- It is the right-hand side given, with its agents renumbered. -/
theorem renum (hσ : R.Lafont σ) (hR : R.WF ar α α) : Rhs.Renum (R.own σ) R (R.owned σ) where
  inj := by
    intro o j o' j' γ γ' hl hl' e
    cases o with
    | some b =>
      rw [hσ.unowned] at hl
      cases hl
    | none =>
      cases o' with
      | some b =>
        rw [hσ.unowned] at hl'
        cases hl'
      | none => exact ⟨rfl, hσ.own_inj hR e⟩
  lab := by
    intro o j γ hl
    cases o with
    | some b =>
      rw [hσ.unowned] at hl
      cases hl
    | none => exact hσ.own_lab hR hl
  onto := by
    intro o' j' γ hl
    obtain ⟨j, e, hl'⟩ := hσ.own_onto hR hl
    exact ⟨none, j, e, hl'⟩
  link := fun _ _ => Iff.rfl

/-- **Lafont's symmetry condition can always be presented with owners.**
A right-hand side of `α ⋈ α` that is symmetric in Lafont's sense is, up to
the numbering of its agents, a right-hand side that is its own mirror
image, which is what a `System` asks of the rule of two equal symbols.  The
agents connected to the interface are owned by one side or the other, and
the others by neither. -/
theorem presented (hσ : R.Lafont σ) (hR : R.WF ar α α) :
    ∃ (e : Option Bool → Nat → Option Bool × Nat) (R' : Rhs S),
      Rhs.Renum e R R' ∧ R'.WF ar α α ∧ R'.Mirror R' ∧
      (∀ j, R.Reach j → (e none j).1 ≠ none) ∧ ∀ j, ¬ R.Reach j → e none j = (none, j) := by
  refine ⟨R.own σ, R.owned σ, hσ.renum hR, hσ.owned_wf hR, hσ.owned_mirror hR,
    fun j r => ?_, fun j r => Rhs.own_far r⟩
  by_cases l : j < σ j
  · rw [Rhs.own_lt r l]
    exact fun e => by cases e
  · rw [Rhs.own_ge r l]
    exact fun e => by cases e

end Rhs.Lafont

end Lafont

/-! ### The numbering of the agents of a rule does not matter

Firing with a renumbered right-hand side gives the same net with the new
agents renamed.  So two systems whose rules are renumberings of each other
simulate each other, up to copies of nets, and reach normal forms that are
copies of each other in the same number of steps. -/

section RenumRule

/-- Rename the agents created when `a` and `b` fire as a renumbering `e` of
the right-hand side says; other names stay as they are. -/
def renumId (a b : Id) (e : Option Bool → Nat → Option Bool × Nat) : Id → Id
  | [] => []
  | n :: t =>
    if t = a ∨ t = b then
      if n % 2 = 0 then
        child a b (e (some (decide (t = b))) (n / 2)).1 (e (some (decide (t = b))) (n / 2)).2
      else child a b (e none (n / 2)).1 (e none (n / 2)).2
    else n :: t

theorem renumId_child {a b : Id} (hne : a ≠ b) (e : Option Bool → Nat → Option Bool × Nat)
    (o : Option Bool) (j : Nat) :
    renumId a b e (child a b o j) = child a b (e o j).1 (e o j).2 := by
  have h : par a b o = a ∨ par a b o = b := par_eq a b o
  show (if par a b o = a ∨ par a b o = b then
      if slot o j % 2 = 0 then
        child a b (e (some (decide (par a b o = b))) (slot o j / 2)).1
          (e (some (decide (par a b o = b))) (slot o j / 2)).2
      else child a b (e none (slot o j / 2)).1 (e none (slot o j / 2)).2
    else slot o j :: par a b o) = _
  rw [ite_pos' h]
  cases o with
  | none =>
    have h1 : ¬ slot none j % 2 = 0 := by
      show ¬ (2 * j + 1) % 2 = 0
      omega
    have h2 : slot none j / 2 = j := by
      show (2 * j + 1) / 2 = j
      omega
    rw [ite_neg' h1, h2]
  | some s =>
    have h1 : slot (some s) j % 2 = 0 := by
      show (2 * j) % 2 = 0
      omega
    have h2 : slot (some s) j / 2 = j := by
      show (2 * j) / 2 = j
      omega
    have h3 : decide (par a b (some s) = b) = s := by
      cases s
      · exact decide_eq_false hne
      · exact decide_eq_true rfl
    rw [ite_pos' h1, h2, h3]

namespace Site

variable {ar : S → Nat} {N : Net S} {a b : Id} {α β : S}

/-- A name in use before the firing stays as it is. -/
theorem renumId_used (h : Site ar N a b α β) (e : Option Bool → Nat → Option Bool × Nat)
    {i : Id} (hu : N.Used i) : renumId a b e i = i := by
  cases i with
  | nil => rfl
  | cons n t =>
    have ht : ¬ (t = a ∨ t = b) := by
      rintro (e₁ | e₁)
      · rw [e₁] at hu
        exact absurd (h.wf.fresh [n] h.ha hu) (List.cons_ne_nil _ _)
      · rw [e₁] at hu
        exact absurd (h.wf.fresh [n] h.hb hu) (List.cons_ne_nil _ _)
    show (if t = a ∨ t = b then _ else n :: t) = n :: t
    rw [ite_neg' ht]

/-- Firing a well-formed right-hand side only brings into use the names of
its agents. -/
theorem used_fire_lab (h : Site ar N a b α β) {R : Rhs S} (hR : R.WF ar α β) {i : Id}
    (hu : (N.fire a b R).Used i) :
    N.Used i ∨ ∃ o j γ, i = child a b o j ∧ R.lab o j = some γ := by
  rcases hu with ⟨γ, ⟨hg, -, -⟩ | ⟨s, j, rfl, hl⟩⟩ | ⟨k, q, hl | ⟨x, y, hxy, e, -⟩⟩ | ⟨k, hf⟩
  · exact .inl (.inl ⟨γ, hg⟩)
  · exact .inr ⟨s, j, γ, rfl, hl⟩
  · exact .inl (.inr (.inl ⟨k, q, hl⟩))
  · cases x with
    | ifc s k' =>
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact .inl (h.used_sel s)
    | new s j k' =>
      obtain ⟨γ, hl, -⟩ := hR.valid hxy
      exact .inr ⟨s, j, γ, (Prod.mk.inj e).1, hl⟩
  · exact .inl (.inr (.inr ⟨k, hf⟩))

theorem emb_renum (h : Site ar N a b α β) (e : Option Bool → Nat → Option Bool × Nat)
    (x : LPort) : mapPort (renumId a b e) (emb a b x) = emb a b (x.renum e) := by
  cases x with
  | ifc s k =>
    show (renumId a b e (sel a b s), k + 1) = (sel a b s, k + 1)
    rw [h.renumId_used e (h.used_sel s)]
  | new o j k =>
    show (renumId a b e (child a b o j), k) = (child a b (e o j).1 (e o j).2, k)
    rw [renumId_child h.ne]

/-- **Firing with a renumbered right-hand side** gives the same net, with
the new agents renamed. -/
theorem fire_renum (h : Site ar N a b α β) {R R' : Rhs S}
    {e : Option Bool → Nat → Option Bool × Nat} (hr : Rhs.Renum e R R') :
    (N.fire a b R).map (renumId a b e) = N.fire a b R' := by
  have hg : ∀ {i}, N.Used i → renumId a b e i = i := fun hu => h.renumId_used e hu
  have hp : ∀ {p : Port}, N.Used p.1 → mapPort (renumId a b e) p = p := fun hu => by
    show (renumId a b e _, _) = _
    rw [hg hu]
  apply Net.ext'
  · intro i γ
    constructor
    · rintro ⟨i', rfl, ⟨hag, na, nb⟩ | ⟨o, j, rfl, hl⟩⟩
      · rw [hg (.inl ⟨γ, hag⟩)]
        exact .inl ⟨hag, na, nb⟩
      · rw [renumId_child h.ne]
        exact .inr ⟨_, _, rfl, hr.lab hl⟩
    · rintro (⟨hag, na, nb⟩ | ⟨o', j', rfl, hl⟩)
      · exact ⟨i, (hg (.inl ⟨γ, hag⟩)).symm, .inl ⟨hag, na, nb⟩⟩
      · obtain ⟨o, j, eo, hl'⟩ := hr.onto hl
        have ec := renumId_child h.ne e o j
        rw [eo] at ec
        exact ⟨child a b o j, ec.symm, .inr ⟨o, j, rfl, hl'⟩⟩
  · intro p q
    constructor
    · rintro ⟨p', q', rfl, rfl, hl | ⟨x, y, hxy, rfl, rfl⟩⟩
      · rw [hp (Net.used_link hl), hp (Net.used_link (h.wf.symm hl))]
        exact .inl hl
      · rw [h.emb_renum, h.emb_renum]
        exact .inr ⟨_, _, (hr.link _ _).2 ⟨x, y, rfl, rfl, hxy⟩, rfl, rfl⟩
    · rintro (hl | ⟨x', y', hxy, rfl, rfl⟩)
      · exact ⟨p, q, (hp (Net.used_link hl)).symm,
          (hp (Net.used_link (h.wf.symm hl))).symm, .inl hl⟩
      · obtain ⟨x, y, rfl, rfl, hl⟩ := (hr.link _ _).1 hxy
        exact ⟨emb a b x, emb a b y, (h.emb_renum e x).symm, (h.emb_renum e y).symm,
          .inr ⟨x, y, hl, rfl, rfl⟩⟩
  · intro p
    constructor
    · rintro ⟨p', rfl, hf⟩
      rw [hp (.inr (.inr ⟨p'.2, hf⟩))]
      exact hf
    · intro hf
      exact ⟨p, (hp (.inr (.inr ⟨p.2, hf⟩))).symm, hf⟩

/-- That renaming is a renaming of the net after the firing. -/
theorem renaming_renum (h : Site ar N a b α β) {R R' : Rhs S}
    {e : Option Bool → Nat → Option Bool × Nat} (hR : R.WF ar α β)
    (hr : Rhs.Renum e R R') : Renaming (renumId a b e) (N.fire a b R) := by
  have hg : ∀ {i}, N.Used i → renumId a b e i = i := fun hu => h.renumId_used e hu
  have hc := renumId_child h.ne e
  constructor
  · intro i j hi hj eq
    rcases h.used_fire_lab hR hi with hi | ⟨o, n, γ, rfl, hl⟩ <;>
      rcases h.used_fire_lab hR hj with hj | ⟨o', n', γ', rfl, hl'⟩
    · rw [hg hi, hg hj] at eq
      exact eq
    · rw [hg hi, hc] at eq
      exact absurd hi (by rw [eq]; exact h.not_used_child _ _)
    · rw [hc, hg hj] at eq
      exact absurd hj (by rw [← eq]; exact h.not_used_child _ _)
    · rw [hc, hc] at eq
      obtain ⟨e₁, e₂⟩ := h.child_inj eq
      obtain ⟨rfl, rfl⟩ := hr.inj hl hl' (Prod.ext e₁ e₂)
      rfl
  · intro c γ i l hcg hi eq
    rcases hcg with ⟨hag, na, nb⟩ | ⟨o, n, rfl, hlab⟩ <;>
      rcases h.used_fire_lab hR hi with hi | ⟨o', n', γ', rfl, hl'⟩
    · rw [hg hi, hg (.inl ⟨_, hag⟩)] at eq
      exact h.wf.fresh l hag (by rw [← eq]; exact hi)
    · rw [hc, hg (.inl ⟨_, hag⟩)] at eq
      cases l with
      | nil => rfl
      | cons m l' =>
        have e' : slot (e o' n').1 (e o' n').2 :: par a b (e o' n').1 = m :: (l' ++ c) := eq
        have e₂ := (List.cons.inj e').2
        have hl0 := h.wf.fresh l' hag (by rw [← e₂]; exact h.used_par _)
        rw [hl0] at e₂
        rcases par_eq a b (e o' n').1 with e₃ | e₃
        · exact absurd (e₂.symm.trans e₃) na
        · exact absurd (e₂.symm.trans e₃) nb
    · rw [hg hi, hc] at eq
      exact absurd hi (by rw [eq]; exact h.not_used_desc _ _ _)
    · rw [hc, hc] at eq
      cases l with
      | nil => rfl
      | cons m l' =>
        have e' : slot (e o' n').1 (e o' n').2 :: par a b (e o' n').1 =
            m :: (l' ++ child a b (e o n).1 (e o n).2) := eq
        have e₂ := (List.cons.inj e').2
        exact absurd (h.used_par (e o' n').1) (by rw [e₂]; exact h.not_used_desc _ _ _)

end Site

/-- `sys'` is `sys` with the new agents of its rules renumbered. -/
structure System.Renum (sys sys' : System S) : Prop where
  ar : sys'.ar = sys.ar
  rule : ∀ α β, (sys.rule α β = none ∧ sys'.rule α β = none) ∨
    ∃ R R' e, sys.rule α β = some R ∧ sys'.rule α β = some R' ∧ Rhs.Renum e R R'

variable {sys sys' : System S}

/-- A step of the system is a step of the renumbered one from the same net,
to a copy of the same result. -/
theorem Step.renum (hr : sys.Renum sys') {N N' : Net S} (hN : N.WF sys.ar)
    (h : Step sys N N') : ∃ g N'', Step sys' N N'' ∧ N'.Iso sys.ar g N'' := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  rcases hr.rule α β with ⟨hn, -⟩ | ⟨R₀, R', e, h₀, h', hren⟩
  · rw [r.rule] at hn
    cases hn
  · rw [r.rule] at h₀
    obtain rfl := Option.some.inj h₀
    have hs := r.site hN
    refine ⟨renumId a b e, N.fire a b R', ⟨a, b, α, β, R', ⟨r.ha, r.hb, r.ne, ?_, h'⟩, rfl⟩,
      hs.renaming_renum (sys.rule_wf r.rule) hren, ?_⟩
    · rw [hr.ar]
      exact r.conn
    · rw [hs.fire_renum hren]
      exact Net.ObsEq.refl _

/-- And a step of the renumbered system is a step of the system. -/
theorem Step.renum_inv (hr : sys.Renum sys') {N N'' : Net S} (hN : N.WF sys.ar)
    (h : Step sys' N N'') : ∃ g N', Step sys N N' ∧ N'.Iso sys.ar g N'' := by
  obtain ⟨a, b, α, β, R', r, rfl⟩ := h
  rcases hr.rule α β with ⟨-, hn⟩ | ⟨R, R₀, e, h₀, h', hren⟩
  · rw [r.rule] at hn
    cases hn
  · rw [r.rule] at h'
    obtain rfl := Option.some.inj h'
    have r₀ : Redex sys N a b α β R := ⟨r.ha, r.hb, r.ne, by rw [← hr.ar]; exact r.conn, h₀⟩
    have hs := r₀.site hN
    exact ⟨renumId a b e, N.fire a b R, ⟨a, b, α, β, R, r₀, rfl⟩,
      hs.renaming_renum (sys.rule_wf h₀) hren, by
        rw [hs.fire_renum hren]
        exact Net.ObsEq.refl _⟩

/-- **A renumbered system simulates the system, up to names.**  If `M` is a
copy of the net `C`, a step of `C` without history is matched by a step of
`M` in the renumbered system, and the results are copies. -/
theorem CStep.renum (hr : sys.Renum sys') {C C' M : Net S} {f : Id → Id}
    (hi : C.Iso sys.ar f M) (hC : C.WF sys.ar) (hM : M.WF sys.ar) (h : CStep sys C C') :
    ∃ g M', Step sys' M M' ∧ C'.Iso sys.ar g M' := by
  obtain ⟨N', s, rfl⟩ := h
  obtain ⟨g₁, M₁, -, s₁, hi₁⟩ := hi.step hC hM s
  obtain ⟨g₂, M', s₂, hi₂⟩ := Step.renum hr hM s₁
  exact ⟨g₂ ∘ g₁, M', s₂, hi₁.trans hi₂ (Step.wf hC s) (Step.wf hM s₁)⟩

/-- **And the system simulates the renumbered one.** -/
theorem CStep.renum_inv (hr : sys.Renum sys') {C M M' : Net S} {f : Id → Id}
    (hi : C.Iso sys.ar f M) (hC : C.WF sys.ar) (hM : M.WF sys.ar) (h : Step sys' M M') :
    ∃ g C', CStep sys C C' ∧ C'.Iso sys.ar g M' := by
  obtain ⟨g₂, M₁, s₁, hi₂⟩ := Step.renum_inv hr hM h
  obtain ⟨g₁, N', -, s, hi₁⟩ := hi.step_inv hC hM s₁
  exact ⟨g₂ ∘ g₁, N'.compact sys.ar, ⟨N', s, rfl⟩,
    hi₁.trans hi₂ (Step.wf hC s) (Step.wf hM s₁)⟩

/-- The same for reductions of any length. -/
theorem System.Renum.steps (hr : sys.Renum sys') {n : Nat} {C C' : Net S}
    (h : Steps (CStep sys) n C C') : ∀ {M : Net S} {f : Id → Id}, C.Iso sys.ar f M →
      C.WF sys.ar → M.WF sys.ar →
      ∃ g M', Steps (Step sys') n M M' ∧ C'.Iso sys.ar g M' ∧ C'.WF sys.ar ∧ M'.WF sys.ar := by
  induction h with
  | refl C => exact fun hi hC hM => ⟨_, _, .refl _, hi, hC, hM⟩
  | head s _ ih =>
    intro M f hi hC hM
    obtain ⟨g, M₁, s₁, hi₁⟩ := CStep.renum hr hi hC hM s
    have hM₁ : M₁.WF sys.ar := by
      have h' : M.WF sys'.ar := by
        rw [hr.ar]
        exact hM
      have h₁ := Step.wf h' s₁
      rw [hr.ar] at h₁
      exact h₁
    obtain ⟨g', M', ss, hi', hC', hM'⟩ := ih hi₁ (CStep.wf hC s) hM₁
    exact ⟨g', M', .head s₁ ss, hi', hC', hM'⟩

/-- **Renumbering the agents of the rules changes nothing but names.**  If
a net without history reduces to a normal form in `n` steps, a copy of it
reduces in the renumbered system to a normal form in `n` steps, and the two
normal forms are copies of each other. -/
theorem System.Renum.normal_form (hr : sys.Renum sys') {n : Nat} {C C' M : Net S}
    {f : Id → Id} (hi : C.Iso sys.ar f M) (hC : C.WF sys.ar) (hM : M.WF sys.ar)
    (hs : Steps (CStep sys) n C C') (hn : Normal (CStep sys) C') :
    ∃ g M', Steps (Step sys') n M M' ∧ Normal (Step sys') M' ∧ C'.Iso sys.ar g M' := by
  obtain ⟨g, M', ss, hi', hC', hM'⟩ := hr.steps hs hi hC hM
  refine ⟨g, M', ss, fun M'' s => ?_, hi'⟩
  obtain ⟨g', C'', s', -⟩ := CStep.renum_inv hr hi' hC' hM' s
  exact hn C'' s'

/-- In particular for one net under the two systems. -/
theorem System.Renum.same (hr : sys.Renum sys') {n : Nat} {N C' : Net S} (hN : N.WF sys.ar)
    (hs : Steps (CStep sys) n (N.compact sys.ar) C') (hn : Normal (CStep sys) C') :
    ∃ g M', Steps (Step sys') n N M' ∧ Normal (Step sys') M' ∧ C'.Iso sys.ar g M' :=
  hr.normal_form ((Net.compact_obs sys.ar N).symm.iso hN.compact) hN.compact hN hs hn

end RenumRule

/-! ### All presentations of the same rules reduce alike

Renumbering is reflexive, symmetric and transitive.  So two presentations
of one right-hand side are renumberings of each other, and two systems that
present the same right-hand sides reduce alike, up to names. -/

section RenumEquiv

/-- A right-hand side is a renumbering of itself. -/
theorem Rhs.Renum.refl (R : Rhs S) : Rhs.Renum (fun o j => (o, j)) R R where
  inj := fun _ _ eq => ⟨(Prod.mk.inj eq).1, (Prod.mk.inj eq).2⟩
  lab := fun hl => hl
  onto := fun hl => ⟨_, _, rfl, hl⟩
  link := by
    intro x y
    have hc : ∀ p : LPort, p.renum (fun o j => (o, j)) = p := by
      intro p
      cases p <;> rfl
    constructor
    · intro h
      exact ⟨x, y, (hc x).symm, (hc y).symm, h⟩
    · rintro ⟨p, q, rfl, rfl, hl⟩
      rw [hc, hc]
      exact hl

/-- A renumbering of a renumbering is a renumbering. -/
theorem Rhs.Renum.trans {e e' : Option Bool → Nat → Option Bool × Nat} {R R' R'' : Rhs S}
    (h₁ : Rhs.Renum e R R') (h₂ : Rhs.Renum e' R' R'') :
    Rhs.Renum (fun o j => e' (e o j).1 (e o j).2) R R'' where
  inj := by
    intro o j o₁ j₁ γ γ₁ hl hl₁ eq
    obtain ⟨e₁, e₂⟩ := h₂.inj (h₁.lab hl) (h₁.lab hl₁) eq
    exact h₁.inj hl hl₁ (Prod.ext e₁ e₂)
  lab := fun hl => h₂.lab (h₁.lab hl)
  onto := by
    intro o'' j'' γ hl
    obtain ⟨o', j', e₂, hl'⟩ := h₂.onto hl
    obtain ⟨o, j, e₁, hl₀⟩ := h₁.onto hl'
    refine ⟨o, j, ?_, hl₀⟩
    show e' (e o j).1 (e o j).2 = (o'', j'')
    rw [e₁]
    exact e₂
  link := by
    intro x y
    have hc : ∀ p : LPort,
        (p.renum e).renum e' = p.renum (fun o j => e' (e o j).1 (e o j).2) := by
      intro p
      cases p <;> rfl
    constructor
    · intro h
      obtain ⟨p', q', rfl, rfl, hl'⟩ := (h₂.link _ _).1 h
      obtain ⟨p, q, rfl, rfl, hl⟩ := (h₁.link _ _).1 hl'
      exact ⟨p, q, hc p, hc q, hl⟩
    · rintro ⟨p, q, rfl, rfl, hl⟩
      rw [← hc, ← hc]
      exact (h₂.link _ _).2 ⟨_, _, rfl, rfl, (h₁.link _ _).2 ⟨p, q, rfl, rfl, hl⟩⟩

/-- The numbering back: the agent of `R` that `e` sends to a given number,
if there is one. -/
noncomputable def Rhs.unrenum (e : Option Bool → Nat → Option Bool × Nat) (R : Rhs S)
    (o' : Option Bool) (j' : Nat) : Option Bool × Nat :=
  @dite _ (∃ p : Option Bool × Nat, e p.1 p.2 = (o', j') ∧ ∃ γ, R.lab p.1 p.2 = some γ)
    (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => (o', j'))

theorem Rhs.Renum.unrenum_apply {e : Option Bool → Nat → Option Bool × Nat} {R R' : Rhs S}
    (h : Rhs.Renum e R R') {o : Option Bool} {j : Nat} {γ : S} (hl : R.lab o j = some γ) :
    R.unrenum e (e o j).1 (e o j).2 = (o, j) := by
  unfold Rhs.unrenum
  split
  · rename_i h'
    obtain ⟨he, γ', hl'⟩ := Classical.choose_spec h'
    obtain ⟨e₁, e₂⟩ := h.inj hl' hl he
    exact Prod.ext e₁ e₂
  · rename_i h'
    exact absurd ⟨(o, j), rfl, γ, hl⟩ h'

theorem Rhs.Renum.apply_unrenum {e : Option Bool → Nat → Option Bool × Nat} {R R' : Rhs S}
    (h : Rhs.Renum e R R') {o' : Option Bool} {j' : Nat} {γ : S} (hl : R'.lab o' j' = some γ) :
    e (R.unrenum e o' j').1 (R.unrenum e o' j').2 = (o', j') ∧
      R.lab (R.unrenum e o' j').1 (R.unrenum e o' j').2 = some γ := by
  obtain ⟨o, j, eo, hl'⟩ := h.onto hl
  obtain ⟨rfl, rfl⟩ : o' = (e o j).1 ∧ j' = (e o j).2 := by
    rw [eo]
    exact ⟨rfl, rfl⟩
  rw [h.unrenum_apply hl']
  exact ⟨rfl, hl'⟩

/-- **Renumbering can be undone**: the right-hand side given is a
renumbering of its renumbering. -/
theorem Rhs.Renum.symm {ar : S → Nat} {α β : S} {e : Option Bool → Nat → Option Bool × Nat}
    {R R' : Rhs S} (h : Rhs.Renum e R R') (hR : R.WF ar α β) :
    Rhs.Renum (R.unrenum e) R' R where
  inj := by
    intro o₁ j₁ o₂ j₂ γ₁ γ₂ hl₁ hl₂ eq
    have a₁ := (h.apply_unrenum hl₁).1
    have a₂ := (h.apply_unrenum hl₂).1
    rw [eq] at a₁
    obtain ⟨e₁, e₂⟩ := Prod.mk.inj (a₁.symm.trans a₂)
    exact ⟨e₁, e₂⟩
  lab := fun hl => (h.apply_unrenum hl).2
  onto := fun hl => ⟨_, _, h.unrenum_apply hl, h.lab hl⟩
  link := by
    intro x y
    have hc : ∀ {p : LPort}, R.Valid ar α β p → (p.renum e).renum (R.unrenum e) = p := by
      intro p hp
      cases p with
      | ifc s k => rfl
      | new o j k =>
        obtain ⟨γ, hl, -⟩ := hp
        show LPort.new (R.unrenum e (e o j).1 (e o j).2).1 (R.unrenum e (e o j).1 (e o j).2).2 k =
          LPort.new o j k
        rw [h.unrenum_apply hl]
    constructor
    · intro hxy
      exact ⟨x.renum e, y.renum e, (hc (hR.valid hxy)).symm, (hc (hR.valid (hR.symm hxy))).symm,
        (h.link _ _).2 ⟨x, y, rfl, rfl, hxy⟩⟩
    · rintro ⟨p', q', rfl, rfl, hl'⟩
      obtain ⟨p, q, rfl, rfl, hl⟩ := (h.link _ _).1 hl'
      rw [hc (hR.valid hl), hc (hR.valid (hR.symm hl))]
      exact hl

/-- **Two presentations of one right-hand side are renumberings of each
other.** -/
theorem Rhs.Renum.common {ar : S → Nat} {α β : S}
    {e₁ e₂ : Option Bool → Nat → Option Bool × Nat} {R R₁ R₂ : Rhs S}
    (h₁ : Rhs.Renum e₁ R R₁) (h₂ : Rhs.Renum e₂ R R₂) (hR : R.WF ar α β) :
    ∃ e, Rhs.Renum e R₁ R₂ :=
  ⟨_, (h₁.symm hR).trans h₂⟩

/-- **A symmetric right-hand side has one presentation, up to numbering**:
whatever symmetry is used to give it owners, the result is a renumbering of
any other presentation. -/
theorem Rhs.Lafont.presented_unique {ar : S → Nat} {α : S} {R R₂ : Rhs S} {σ : Nat → Nat}
    (hσ : R.Lafont σ) (hR : R.WF ar α α) {e₂ : Option Bool → Nat → Option Bool × Nat}
    (h₂ : Rhs.Renum e₂ R R₂) : ∃ e, Rhs.Renum e (R.owned σ) R₂ :=
  (hσ.renum hR).common h₂ hR

variable {sys sys' sys'' : System S}

theorem System.Renum.refl (sys : System S) : sys.Renum sys :=
  ⟨rfl, fun α β => by
    cases h : sys.rule α β with
    | none => exact .inl ⟨rfl, rfl⟩
    | some R => exact .inr ⟨R, R, _, rfl, rfl, Rhs.Renum.refl R⟩⟩

theorem System.Renum.symm (hr : sys.Renum sys') : sys'.Renum sys :=
  ⟨hr.ar.symm, fun α β => by
    rcases hr.rule α β with ⟨a, b⟩ | ⟨R, R', e, a, b, r⟩
    · exact .inl ⟨b, a⟩
    · exact .inr ⟨R', R, _, b, a, r.symm (sys.rule_wf a)⟩⟩

theorem System.Renum.trans (h₁ : sys.Renum sys') (h₂ : sys'.Renum sys'') : sys.Renum sys'' :=
  ⟨h₂.ar.trans h₁.ar, fun α β => by
    rcases h₁.rule α β with ⟨a, b⟩ | ⟨R, R', e, a, b, r⟩ <;>
      rcases h₂.rule α β with ⟨c, d⟩ | ⟨R₁, R'', e', c, d, r'⟩
    · exact .inl ⟨a, d⟩
    · rw [b] at c
      cases c
    · rw [b] at c
      cases c
    · rw [b] at c
      obtain rfl := Option.some.inj c
      exact .inr ⟨R, R'', _, a, d, r.trans r'⟩⟩

/-- **Two systems that present the same right-hand sides** are renumberings
of each other: it is enough that, for each pair of symbols with a rule, the
two rules are renumberings of one right-hand side, given without owners
say. -/
theorem System.Renum.of_common {sys₁ sys₂ : System S} (har : sys₂.ar = sys₁.ar)
    (h : ∀ α β, (sys₁.rule α β = none ∧ sys₂.rule α β = none) ∨
      ∃ R R₁ R₂ e₁ e₂, R.WF sys₁.ar α β ∧ sys₁.rule α β = some R₁ ∧
        sys₂.rule α β = some R₂ ∧ Rhs.Renum e₁ R R₁ ∧ Rhs.Renum e₂ R R₂) :
    sys₁.Renum sys₂ :=
  ⟨har, fun α β => by
    rcases h α β with hn | ⟨R, R₁, R₂, e₁, e₂, hR, h₁, h₂, r₁, r₂⟩
    · exact .inl hn
    · obtain ⟨e, he⟩ := r₁.common r₂ hR
      exact .inr ⟨R₁, R₂, e, h₁, h₂, he⟩⟩

/-- **All presentations of the same rules reduce alike.**  If two systems
present the same right-hand sides, a net that reduces to a normal form in
`n` steps in the first, without history, reduces to a normal form in `n`
steps in the second, and the two normal forms are copies of each other. -/
theorem System.common_normal_form {sys₁ sys₂ : System S} (har : sys₂.ar = sys₁.ar)
    (h : ∀ α β, (sys₁.rule α β = none ∧ sys₂.rule α β = none) ∨
      ∃ R R₁ R₂ e₁ e₂, R.WF sys₁.ar α β ∧ sys₁.rule α β = some R₁ ∧
        sys₂.rule α β = some R₂ ∧ Rhs.Renum e₁ R R₁ ∧ Rhs.Renum e₂ R R₂)
    {n : Nat} {N C' : Net S} (hN : N.WF sys₁.ar)
    (hs : Steps (CStep sys₁) n (N.compact sys₁.ar) C') (hn : Normal (CStep sys₁) C') :
    ∃ g M', Steps (Step sys₂) n N M' ∧ Normal (Step sys₂) M' ∧ C'.Iso sys₁.ar g M' :=
  (System.Renum.of_common har h).same hN hs hn

end RenumEquiv

/-! ### History that a copy cannot give back

A segment between names that are not in use can be added to a well-formed
net without changing what is observed.  A copy of a net may carry such
history on names that the net reserves, and then the net is not a copy of
it: being a copy is symmetric only once the history is discarded. -/

section Junk

/-- A net with one more segment, between two ports. -/
def Net.junk (N : Net S) (p₀ q₀ : Port) : Net S where
  agent := N.agent
  link p q := N.link p q ∨ (p = p₀ ∧ q = q₀) ∨ (p = q₀ ∧ q = p₀)
  free := N.free

/-- Wires of the net are wires of the net with the segment. -/
theorem Net.conn_junk {ar : S → Nat} {N : Net S} (p₀ q₀ : Port) {p q : Port}
    (h : N.Conn ar p q) : (N.junk p₀ q₀).Conn ar p q := by
  obtain ⟨v, x, w⟩ := h
  exact ⟨v, x, w.image id (fun h => .inl h) (fun _ h => h) (fun _ _ h => h)⟩

/-- **History may be added.**  A segment between two names that are not in
use, and are not reserved for the descendants of an agent, leaves the net
well formed. -/
theorem Net.WF.junk {ar : S → Nat} {N : Net S} {p₀ q₀ : Port} (hN : N.WF ar) (hne : p₀ ≠ q₀)
    (hp : ¬ N.Used p₀.1) (hq : ¬ N.Used q₀.1)
    (hfp : ∀ {a α} (l : List Nat), N.agent a α → p₀.1 ≠ l ++ a)
    (hfq : ∀ {a α} (l : List Nat), N.agent a α → q₀.1 ≠ l ++ a) : (N.junk p₀ q₀).WF ar := by
  have np : ∀ {q : Port}, ¬ N.link p₀ q := fun h => hp (Net.used_link h)
  have nq : ∀ {q : Port}, ¬ N.link q₀ q := fun h => hq (Net.used_link h)
  have at_p : ∀ {x : Port}, (N.junk p₀ q₀).link p₀ x → x = q₀ := by
    intro x h
    rcases h with h | ⟨-, e⟩ | ⟨e, -⟩
    · exact absurd h np
    · exact e
    · exact absurd e hne
  have at_q : ∀ {x : Port}, (N.junk p₀ q₀).link q₀ x → x = p₀ := by
    intro x h
    rcases h with h | ⟨e, -⟩ | ⟨-, e⟩
    · exact absurd h nq
    · exact absurd e.symm hne
    · exact e
  have old : ∀ {p q : Port}, (N.junk p₀ q₀).link p q → p ≠ p₀ → p ≠ q₀ → N.link p q := by
    intro p q h h₁ h₂
    rcases h with h | ⟨e, -⟩ | ⟨e, -⟩
    · exact h
    · exact absurd e h₁
    · exact absurd e h₂
  have endne : ∀ {p : Port}, N.End ar p → p ≠ p₀ ∧ p ≠ q₀ := fun hE =>
    ⟨fun e => hp (e ▸ hE.used), fun e => hq (e ▸ hE.used)⟩
  refine ⟨hN.agent_fun, ?_, ?_, ?_, ?_, ?_, hN.free_agent, ?_⟩
  · intro p q h
    rcases h with h | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact .inl (hN.symm h)
    · exact .inr (.inr ⟨e₂, e₁⟩)
    · exact .inr (.inl ⟨e₂, e₁⟩)
  · intro p h
    rcases h with h | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact hN.irrefl h
    · exact hne (e₁.symm.trans e₂)
    · exact hne (e₂.symm.trans e₁)
  · intro p q r hE h₁ h₂
    obtain ⟨n₁, n₂⟩ := endne hE
    exact hN.end_unique hE (old h₁ n₁ n₂) (old h₂ n₁ n₂)
  · intro p hE
    obtain ⟨q, hq', hne', hc⟩ := hN.end_conn hE
    exact ⟨q, hq', hne', Net.conn_junk p₀ q₀ hc⟩
  · intro p x y z h₁ h₂ h₃
    by_cases e₁ : p = p₀
    · rw [e₁] at h₁ h₂
      exact .inl ((at_p h₁).trans (at_p h₂).symm)
    · by_cases e₂ : p = q₀
      · rw [e₂] at h₁ h₂
        exact .inl ((at_q h₁).trans (at_q h₂).symm)
      · exact hN.deg (old h₁ e₁ e₂) (old h₂ e₁ e₂) (old h₃ e₁ e₂)
  · intro a α l hg hu
    rcases hu with ⟨γ, h⟩ | ⟨k, q, h | ⟨e, -⟩ | ⟨e, -⟩⟩ | ⟨k, h⟩
    · exact hN.fresh l hg (.inl ⟨γ, h⟩)
    · exact hN.fresh l hg (.inr (.inl ⟨k, q, h⟩))
    · exact absurd (congrArg Prod.fst e).symm (hfp l hg)
    · exact absurd (congrArg Prod.fst e).symm (hfq l hg)
    · exact hN.fresh l hg (.inr (.inr ⟨k, h⟩))

/-- And nothing that is observed changes. -/
theorem Net.junk_obs {ar : S → Nat} {N : Net S} {p₀ q₀ : Port} (hN : N.WF ar)
    (hW : (N.junk p₀ q₀).WF ar) : N.ObsEq ar (N.junk p₀ q₀) := by
  refine ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun p q =>
    ⟨fun h => ⟨h.1, h.2.1, Net.conn_junk p₀ q₀ h.2.2⟩, fun h => ?_⟩⟩
  obtain ⟨q', hq', -, hc⟩ := hN.end_conn h.1
  have e := Net.Conn.det hW h.1 hq' h.2.1 (Net.conn_junk p₀ q₀ hc) h.2.2
  rw [← e]
  exact ⟨h.1, hq', hc⟩

theorem singleton_ne_append {x y : Nat} (h : x ≠ y) : ∀ l : List Nat, [x] ≠ l ++ [y]
  | [], e => h (List.cons.inj e).1
  | z :: l, e => by
    have t : ([] : List Nat) = l ++ [y] := (List.cons.inj e).2
    have hl : (0 : Nat) = l.length + 1 := by
      have h' := congrArg List.length t
      rw [List.length_append] at h'
      exact h'
    omega

/-- One agent whose principal port is wired to its auxiliary port. -/
def loopNet : XNet Unit := ⟨[([], ())], [], [(([], 0), ([], 1)), (([], 1), ([], 0))]⟩

/-- **Being a copy is not symmetric as it stands.**  The agent of `loopNet`
has the empty name, so every name is reserved for its descendants.  A copy
that names the agent `[7]` may carry a segment of history on other names,
and no renaming can bring those names back. -/
theorem Net.Iso.not_symm : ∃ (ar : Unit → Nat) (N M : Net Unit) (f : Id → Id),
    N.WF ar ∧ M.WF ar ∧ N.Iso ar f M ∧ ¬ ∃ g, M.Iso ar g N := by
  have hOk : loopNet.Ok (fun _ => 1) := by decide
  have hN := hOk.1
  have hused : ∀ i, loopNet.toNet.Used i → i = [] := by
    intro i hu
    rcases hu with ⟨γ, h⟩ | ⟨k, q, h⟩ | ⟨k, h⟩
    · exact (Prod.mk.inj (List.mem_singleton.1 h)).1
    · rcases List.mem_cons.1 h with e | h'
      · exact (Prod.mk.inj (Prod.mk.inj e).1).1
      · exact (Prod.mk.inj (Prod.mk.inj (List.mem_singleton.1 h')).1).1
    · exact absurd h List.not_mem_nil
  have hf : Renaming (fun _ => [7]) loopNet.toNet := by
    constructor
    · intro i j hi hj _
      rw [hused i hi, hused j hj]
    · intro a α i l _ _ e
      have e' : ([7] : List Nat) = l ++ [7] := e
      have hl := congrArg List.length e'
      rw [List.length_append] at hl
      have h1 : ([7] : List Nat).length = 1 := rfl
      exact List.eq_nil_of_length_eq_zero (by omega)
  have hmapUsed : ∀ j, (loopNet.toNet.map fun _ => [7]).Used j → j = [7] := by
    intro j h
    obtain ⟨i, e, -⟩ := Net.used_map h
    exact e
  have hmapAgent : ∀ a α, (loopNet.toNet.map fun _ => [7]).agent a α → a = [7] := by
    rintro a α ⟨i, e, -⟩
    exact e
  have hWmap := hf.wf_map hN
  have hM : ((loopNet.toNet.map fun _ => [7]).junk ([5], 0) ([6], 0)).WF (fun _ => 1) :=
    hWmap.junk (by decide) (fun h => absurd (hmapUsed _ h) (by decide))
      (fun h => absurd (hmapUsed _ h) (by decide))
      (fun l hg e => by
        rw [hmapAgent _ _ hg] at e
        exact singleton_ne_append (by decide) l e)
      (fun l hg e => by
        rw [hmapAgent _ _ hg] at e
        exact singleton_ne_append (by decide) l e)
  refine ⟨fun _ => 1, loopNet.toNet, _, fun _ => [7], hN, hM, ⟨hf, Net.junk_obs hWmap hM⟩, ?_⟩
  rintro ⟨g, hg⟩
  have hag : ((loopNet.toNet.map fun _ => [7]).junk ([5], 0) ([6], 0)).agent [7] () :=
    ⟨[], rfl, List.mem_singleton.2 rfl⟩
  have h7 : g [7] = [] := by
    obtain ⟨i', e, hi'⟩ := (hg.obs.agent [] ()).2 (List.mem_singleton.2 rfl)
    rw [hmapAgent i' () hi'] at e
    exact e.symm
  have hu5 : ((loopNet.toNet.map fun _ => [7]).junk ([5], 0) ([6], 0)).Used [5] :=
    .inr (.inl ⟨0, ([6], 0), .inr (.inl ⟨rfl, rfl⟩)⟩)
  have hu7 : ((loopNet.toNet.map fun _ => [7]).junk ([5], 0) ([6], 0)).Used [7] :=
    .inl ⟨(), hag⟩
  have e5 : g [5] = [] := hg.ren.fresh (g [5]) hag hu5 (by rw [h7, List.append_nil])
  exact absurd (hg.ren.inj hu5 hu7 (e5.trans h7.symm)) (by decide)

end Junk

end INet
