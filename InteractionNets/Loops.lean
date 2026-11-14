import InteractionNets.Concurrent

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## Closed loops

A firing can close a wire onto itself.  Such a loop has no end, so it is not
observable and compaction discards it; and since segments form a set, a loop
made of two copies of the same segment is not even recorded as a cycle.
What is recorded, in every case, is a *dead component*: a connected piece of
the wiring that reaches no end.  Each firing leaves behind exactly one dead
component that is not a loop, the wire between the two principal ports.  So
the loops closed by a reduction can be counted: they are the dead components
gained, minus one per step. -/

section ClosedLoops


/-- Joined by a chain of segments. -/
inductive Net.Reach (N : Net S) (p : Port) : Port → Prop
  | refl : Net.Reach N p p
  | tail {q r : Port} : Net.Reach N p q → N.link q r → Net.Reach N p r

namespace Net.Reach

variable {M : Net S} {p q r : Port}

theorem single (h : N.link p q) : N.Reach p q := .tail .refl h

theorem trans (h₁ : N.Reach p q) (h₂ : N.Reach q r) : N.Reach p r := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hl ih => exact .tail ih hl

theorem symm (hs : ∀ {p q}, N.link p q → N.link q p) (h : N.Reach p q) : N.Reach q p := by
  induction h with
  | refl => exact .refl
  | tail _ hl ih => exact (single (hs hl)).trans ih

theorem mono (hL : ∀ {p q}, N.link p q → M.link p q) (h : N.Reach p q) : M.Reach p q := by
  induction h with
  | refl => exact .refl
  | tail _ hl ih => exact .tail ih (hL hl)

/-- The last point of a chain is its first point, or lies on a segment. -/
theorem last (h : N.Reach p q) : q = p ∨ ∃ r, N.link r q := by
  cases h with
  | refl => exact .inl rfl
  | tail _ hl => exact .inr ⟨_, hl⟩

end Net.Reach

theorem Walk.reach {T : Port → Prop} {u v x y : Port} (w : Walk N.link T u v x y) :
    N.Reach u y := by
  induction w with
  | single h => exact .single h
  | cons h _ _ _ ih => exact (Net.Reach.single h).trans ih

/-- A walk without its last segment. -/
theorem Walk.init {V : Type u} {L : V → V → Prop} {T : V → Prop} {u v x y : V}
    (w : Walk L T u v x y) : x = u ∨ ∃ x', Walk L T u v x' x := by
  induction w with
  | single _ => exact .inl rfl
  | cons h hv hw _ ih =>
    rcases ih with e | ⟨x', w'⟩
    · subst e
      exact .inr ⟨_, Walk.single h⟩
    · exact .inr ⟨x', .cons h hv hw w'⟩

/-- A point of a dead component: it lies on a segment, and no chain of
segments leads from it to an end. -/
def Net.Dead (ar : S → Nat) (N : Net S) (p : Port) : Prop :=
  (∃ q, N.link p q) ∧ ∀ q, N.Reach p q → ¬ N.End ar q

theorem Net.Dead.reach {ar : S → Nat} {p q : Port} (hs : ∀ {p q}, N.link p q → N.link q p)
    (h : N.Dead ar p) (hr : N.Reach p q) : N.Dead ar q := by
  refine ⟨?_, fun q' hr' => h.2 q' (hr.trans hr')⟩
  rcases hr.last with rfl | ⟨r, hl⟩
  · exact h.1
  · exact ⟨r, hs hl⟩

/-- `q` lies on the wire that leaves `p`. -/
def Net.OnWire (ar : S → Nat) (N : Net S) (p q : Port) : Prop :=
  q = p ∨ ∃ v x, Walk N.link (N.End ar) p v x q

theorem Net.OnWire.reach {ar : S → Nat} {p q : Port} (h : N.OnWire ar p q) : N.Reach p q := by
  rcases h with rfl | ⟨v, x, w⟩
  · exact .refl
  · exact w.reach

/-- **The component of an end is its wire.** -/
theorem Net.WF.onWire_of_reach {ar : S → Nat} (hN : N.WF ar) {p q : Port}
    (h : N.Reach p q) : N.OnWire ar p q := by
  induction h with
  | refl => exact .inl rfl
  | @tail q r _ hl ih =>
    rcases ih with rfl | ⟨v, x, w⟩
    · exact .inr ⟨r, _, .single hl⟩
    · by_cases hrx : r = x
      · rcases w.init with e | ⟨x', w'⟩
        · exact .inl (hrx.trans e)
        · exact .inr ⟨v, x', hrx ▸ w'⟩
      · by_cases hq : N.End ar q
        · exact absurd (hN.end_unique hq hl (hN.symm w.link_last)) hrx
        · exact .inr ⟨v, q, w.snoc hq hl hrx⟩

/-- The only ends on the wire that leaves an end are its two extremities. -/
theorem Net.OnWire.end_cases {ar : S → Nat} {p q : Port} (h : N.OnWire ar p q)
    (hp : N.End ar p) (hq : N.End ar q) : q = p ∨ N.Paired ar p q := by
  rcases h with rfl | ⟨v, x, w⟩
  · exact .inl rfl
  · exact .inr ⟨hp, hq, v, x, w⟩

namespace Site

variable {ar : S → Nat} {a b : Id} {α β : S} {R : Rhs S} {p q : Port}

/-- A valid auxiliary port of a fired agent was an end. -/
theorem end_aux (h : Site ar N a b α β) {s : Bool} {k : Nat} (hk : k < ar (sel α β s)) :
    N.End ar (sel a b s, k + 1) :=
  .inr ⟨_, h.agent_sel s, Nat.succ_le_of_lt hk⟩

theorem paired_principal (h : Site ar N a b α β) : N.Paired ar (a, 0) (b, 0) :=
  ⟨.inr ⟨α, h.ha, Nat.zero_le _⟩, .inr ⟨β, h.hb, Nat.zero_le _⟩, h.conn⟩

/-- No new segment leaves a dead component: its chains are the old ones. -/
theorem reach_fire_of_dead (h : Site ar N a b α β) (hR : R.WF ar α β) (hd : N.Dead ar p)
    (hr : (N.fire a b R).Reach p q) : N.Reach p q := by
  induction hr with
  | refl => exact .refl
  | @tail q r _ hl ih =>
    rcases hl with hl | ⟨x, y, hxy, rfl, rfl⟩
    · exact .tail ih hl
    · exfalso
      cases x with
      | ifc s k => exact hd.2 _ ih (h.end_aux (hR.valid hxy))
      | new o j k =>
        rcases ih.last with e | ⟨r', hl'⟩
        · obtain ⟨q', hq'⟩ := hd.1
          rw [← e] at hq'
          exact h.not_used_child o j (.inr (.inl ⟨k, q', hq'⟩))
        · exact h.not_used_child o j (.inr (.inl ⟨k, r', h.wf.symm hl'⟩))

/-- **Dead components are permanent.** -/
theorem dead_fire (h : Site ar N a b α β) (hR : R.WF ar α β) (hd : N.Dead ar p) :
    (N.fire a b R).Dead ar p := by
  obtain ⟨q₀, hl₀⟩ := hd.1
  refine ⟨⟨q₀, .inl hl₀⟩, fun q hr hE => ?_⟩
  have hr' := h.reach_fire_of_dead hR hd hr
  have hlq : ∃ r, N.link q r := by
    rcases hr'.last with rfl | ⟨r, hl⟩
    · exact ⟨q₀, hl₀⟩
    · exact ⟨r, h.wf.symm hl⟩
  obtain ⟨r, hl⟩ := hlq
  exact hd.2 q hr' (h.end_of_fire_link hE hl)

/-- A dead component is not joined to anything that was an end. -/
theorem not_reach_fire_end (h : Site ar N a b α β) (hR : R.WF ar α β) (hd : N.Dead ar p)
    (hq : N.End ar q) : ¬ (N.fire a b R).Reach p q :=
  fun hr => hd.2 q (h.reach_fire_of_dead hR hd hr) hq

/-- No new segment touches the wire between the two principal ports. -/
theorem reach_fire_principal (h : Site ar N a b α β) (hR : R.WF ar α β)
    (hr : (N.fire a b R).Reach (a, 0) q) : N.Reach (a, 0) q := by
  induction hr with
  | refl => exact .refl
  | @tail q r _ hl ih =>
    rcases hl with hl | ⟨x, y, hxy, rfl, rfl⟩
    · exact .tail ih hl
    · exfalso
      cases x with
      | ifc s k =>
        have hE := h.end_aux (hR.valid hxy)
        rcases (h.wf.onWire_of_reach ih).end_cases h.paired_principal.1 hE with e | hp
        · exact absurd (congrArg Prod.snd e) (Nat.succ_ne_zero k)
        · exact absurd (congrArg Prod.snd (hp.det h.wf h.paired_principal)) (Nat.succ_ne_zero k)
      | new o j k =>
        rcases ih.last with e | ⟨r', hl'⟩
        · exact h.sel_ne_child (s := false) (congrArg Prod.fst e).symm
        · exact h.not_used_child o j (.inr (.inl ⟨k, r', h.wf.symm hl'⟩))

/-- **The wire between the two principal ports dies.** -/
theorem dead_fire_principal (h : Site ar N a b α β) (hR : R.WF ar α β) :
    (N.fire a b R).Dead ar (a, 0) := by
  obtain ⟨q₀, hl₀⟩ := h.wf.end_wired h.paired_principal.1
  refine ⟨⟨q₀, .inl hl₀⟩, fun q hr hE => ?_⟩
  rcases h.wf.onWire_of_reach (h.reach_fire_principal hR hr) with rfl | ⟨v, x, w⟩
  · exact h.not_end_fire_sel false 0 hE
  · have hE' := h.end_of_fire_link hE (h.wf.symm w.link_last)
    have e := Net.Paired.det h.wf ⟨h.paired_principal.1, hE', v, x, w⟩ h.paired_principal
    rw [e] at hE
    exact h.not_end_fire_sel true 0 hE

/-- That wire is not joined to an auxiliary port. -/
theorem not_reach_principal_aux (h : Site ar N a b α β) (hR : R.WF ar α β) {s : Bool} {k : Nat}
    (hk : k < ar (sel α β s)) : ¬ (N.fire a b R).Reach (a, 0) (sel a b s, k + 1) := by
  intro hr
  rcases (h.wf.onWire_of_reach (h.reach_fire_principal hR hr)).end_cases h.paired_principal.1
    (h.end_aux hk) with e | hp
  · exact absurd (congrArg Prod.snd e) (Nat.succ_ne_zero k)
  · exact absurd (congrArg Prod.snd (hp.det h.wf h.paired_principal)) (Nat.succ_ne_zero k)

/-- **What dies in a firing**: a point that is dead after the firing was
dead before, or lies on the wire between the two principal ports, or is
joined to an auxiliary port of a fired agent, that is, lies on a loop that
the firing has closed. -/
theorem dead_fire_cases (h : Site ar N a b α β) (hR : R.WF ar α β)
    (hd' : (N.fire a b R).Dead ar p) :
    N.Dead ar p ∨ (N.fire a b R).Reach p (a, 0) ∨
      ∃ s k, k < ar (sel α β s) ∧ (N.fire a b R).Reach p (sel a b s, k + 1) := by
  have hN' := h.fire_wf hR
  by_cases hd : N.Dead ar p
  · exact .inl hd
  have hlp : ∃ q, N.link p q := by
    obtain ⟨q₀, hl₀⟩ := hd'.1
    rcases hl₀ with hl | ⟨x, y, hxy, rfl, -⟩
    · exact ⟨q₀, hl⟩
    · cases x with
      | ifc s k => exact h.wf.end_wired (h.end_aux (hR.valid hxy))
      | new o j k =>
        obtain ⟨γ, hγ, hk⟩ := hR.valid hxy
        exact absurd (.inr ⟨γ, .inr ⟨o, j, rfl, hγ⟩, hk⟩) (hd'.2 _ .refl)
  have hex : ∃ q, N.Reach p q ∧ N.End ar q :=
    Classical.byContradiction fun hne => hd ⟨hlp, fun q hr hE => hne ⟨q, hr, hE⟩⟩
  obtain ⟨⟨i, k⟩, hr, hE⟩ := hex
  have hr' : (N.fire a b R).Reach p (i, k) := hr.mono (fun hl => Or.inl hl)
  have hab : i = a ∨ i = b := by
    by_cases ha : i = a
    · exact .inl ha
    by_cases hb : i = b
    · exact .inr hb
    exact absurd (hE.fire ha hb) (hd'.2 _ hr')
  rcases hab with e | e
  · rw [e] at hr' hE
    rcases hE with hf | ⟨γ, hg, hk⟩
    · exact absurd h.ha (h.wf.free_agent hf)
    · have hγ := h.wf.agent_fun hg h.ha
      rw [hγ] at hk
      cases k with
      | zero => exact .inr (.inl hr')
      | succ k => exact .inr (.inr ⟨false, k, hk, hr'⟩)
  · rw [e] at hr' hE
    rcases hE with hf | ⟨γ, hg, hk⟩
    · exact absurd h.hb (h.wf.free_agent hf)
    · have hγ := h.wf.agent_fun hg h.hb
      rw [hγ] at hk
      cases k with
      | zero =>
        have hba : (N.fire a b R).Reach (b, 0) (a, 0) :=
          (h.conn.choose_spec.choose_spec.reach.mono (fun hl => Or.inl hl)).symm hN'.symm
        exact .inr (.inl (hr'.trans hba))
      | succ k => exact .inr (.inr ⟨true, k, hk, hr'⟩)

end Site

section Reps

variable {α : Type u}

/-- Among the elements of a list that satisfy `D`, pick one in each class of
the relation `E`. -/
theorem exists_reps (E : α → α → Prop) (D : α → Prop) (hrefl : ∀ x, E x x)
    (hs : ∀ {x y}, E x y → E y x) (l : List α) :
    ∃ rs : List α, rs.length ≤ l.length ∧ (∀ r ∈ rs, r ∈ l ∧ D r) ∧
      rs.Pairwise (fun x y => ¬ E x y) ∧ ∀ e ∈ l, D e → ∃ r ∈ rs, E r e := by
  induction l with
  | nil =>
    exact ⟨[], Nat.le_refl _, fun r hr => absurd hr List.not_mem_nil, .nil,
      fun e he => absurd he List.not_mem_nil⟩
  | cons e es ih =>
    obtain ⟨rs, hlen, hmem, hpw, hcov⟩ := ih
    by_cases hc : D e ∧ ∀ r ∈ rs, ¬ E r e
    · refine ⟨e :: rs, Nat.succ_le_succ hlen, ?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨List.mem_cons.2 (.inl rfl), hc.1⟩
        · exact ⟨List.mem_cons_of_mem _ (hmem r hr).1, (hmem r hr).2⟩
      · exact List.pairwise_cons.2 ⟨fun r hr h => hc.2 r hr (hs h), hpw⟩
      · intro e' he' hd
        rcases List.mem_cons.1 he' with rfl | he'
        · exact ⟨e', List.mem_cons.2 (.inl rfl), hrefl e'⟩
        · obtain ⟨r, hr, h⟩ := hcov e' he' hd
          exact ⟨r, List.mem_cons_of_mem _ hr, h⟩
    · refine ⟨rs, Nat.le_succ_of_le hlen,
        fun r hr => ⟨List.mem_cons_of_mem _ (hmem r hr).1, (hmem r hr).2⟩, hpw, ?_⟩
      intro e' he' hd
      rcases List.mem_cons.1 he' with rfl | he'
      · exact Classical.byContradiction fun hne => hc ⟨hd, fun r hr h => hne ⟨r, hr, h⟩⟩
      · exact hcov e' he' hd

/-- A list of pairwise inequivalent elements, each equivalent to an element
of a second list, is not longer than the second list. -/
theorem length_le_of_reps (E : α → α → Prop) (hs : ∀ {x y}, E x y → E y x)
    (ht : ∀ {x y z}, E x y → E y z → E x z) :
    ∀ (l l' : List α), l.Pairwise (fun x y => ¬ E x y) → (∀ x ∈ l, ∃ y ∈ l', E y x) →
      l.length ≤ l'.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l', hp, hc => by
    obtain ⟨hx, hp'⟩ := List.pairwise_cons.1 hp
    obtain ⟨y, hy, hyx⟩ := hc x (List.mem_cons.2 (.inl rfl))
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hy
    have ih := length_le_of_reps E hs ht xs (s ++ t) hp' (by
      intro x' hx'
      obtain ⟨y', hy', hy'x⟩ := hc x' (List.mem_cons_of_mem _ hx')
      rcases List.mem_append.1 hy' with h | h
      · exact ⟨y', List.mem_append_left _ h, hy'x⟩
      · rcases List.mem_cons.1 h with rfl | h
        · exact absurd (ht (hs hyx) hy'x) (hx x' hx')
        · exact ⟨y', List.mem_append_right _ h, hy'x⟩)
    simp only [List.length_cons, List.length_append] at ih ⊢
    omega

end Reps

/-- The net has exactly `n` dead components: the list picks one point in
each. -/
def Net.DeadCount (ar : S → Nat) (N : Net S) (n : Nat) : Prop :=
  ∃ reps : List Port, reps.length = n ∧ (∀ p ∈ reps, N.Dead ar p) ∧
    reps.Pairwise (fun p q => ¬ N.Reach p q) ∧ ∀ p, N.Dead ar p → ∃ r ∈ reps, N.Reach r p

/-- The number of dead components is well defined. -/
theorem Net.DeadCount.unique {ar : S → Nat} {n m : Nat} (hN : N.WF ar)
    (h₁ : N.DeadCount ar n) (h₂ : N.DeadCount ar m) : n = m := by
  obtain ⟨l₁, rfl, d₁, p₁, c₁⟩ := h₁
  obtain ⟨l₂, rfl, d₂, p₂, c₂⟩ := h₂
  have hs : ∀ {x y : Port}, N.Reach x y → N.Reach y x := fun h => h.symm hN.symm
  have ht : ∀ {x y z : Port}, N.Reach x y → N.Reach y z → N.Reach x z := fun h h' => h.trans h'
  exact Nat.le_antisymm
    (length_le_of_reps N.Reach hs ht l₁ l₂ p₁ fun x hx => c₂ x (d₁ x hx))
    (length_le_of_reps N.Reach hs ht l₂ l₁ p₂ fun x hx => c₁ x (d₂ x hx))

/-- A net without history has no dead component. -/
theorem Net.WF.deadCount_compact {ar : S → Nat} (hc : N.compact ar = N) :
    N.DeadCount ar 0 := by
  refine ⟨[], rfl, fun p hp => absurd hp List.not_mem_nil, .nil, fun p hd => ?_⟩
  obtain ⟨q, hl⟩ := hd.1
  have hp : (N.compact ar).link p q := by
    rw [hc]
    exact hl
  exact absurd hp.1 (hd.2 p .refl)

/-- The auxiliary ports of two agents. -/
def auxPorts (ar : S → Nat) (a b : Id) (α β : S) : List Port :=
  (List.range (ar α)).map (fun k => (a, k + 1)) ++ (List.range (ar β)).map (fun k => (b, k + 1))

theorem mem_auxPorts {ar : S → Nat} {a b : Id} {α β : S} {e : Port} :
    e ∈ auxPorts ar a b α β ↔ ∃ s k, k < ar (sel α β s) ∧ e = (sel a b s, k + 1) := by
  unfold auxPorts
  rw [List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨false, k, List.mem_range.1 hk, rfl⟩
    · exact ⟨true, k, List.mem_range.1 hk, rfl⟩
  · rintro ⟨s, k, hk, rfl⟩
    cases s
    · exact .inl ⟨k, List.mem_range.2 hk, rfl⟩
    · exact .inr ⟨k, List.mem_range.2 hk, rfl⟩

namespace Site

variable {ar : S → Nat} {a b : Id} {α β : S} {R : Rhs S} {p q : Port}

/-- **Counting what a firing kills.**  If the net has `n` dead components,
the net after the firing has `n + 1 + ℓ`: the old ones, the wire between the
two principal ports, and `ℓ` loops closed by the firing.  There are no more
loops than auxiliary ports, and there is none exactly when no auxiliary port
of the two agents has died. -/
theorem deadCount_fire (h : Site ar N a b α β) (hR : R.WF ar α β) {n : Nat}
    (hc : N.DeadCount ar n) :
    ∃ ℓ, (N.fire a b R).DeadCount ar (n + 1 + ℓ) ∧ ℓ ≤ ar α + ar β ∧
      (ℓ = 0 ↔ ∀ s k, k < ar (sel α β s) → ¬ (N.fire a b R).Dead ar (sel a b s, k + 1)) := by
  have hN' := h.fire_wf hR
  have hsymm : ∀ {x y : Port}, (N.fire a b R).Reach x y → (N.fire a b R).Reach y x :=
    fun hxy => hxy.symm hN'.symm
  obtain ⟨reps, rfl, hdead, hpw, hcov⟩ := hc
  obtain ⟨rs, hlen, hmem, hpw', hcov'⟩ := exists_reps (N.fire a b R).Reach
    ((N.fire a b R).Dead ar) (fun _ => .refl) hsymm (auxPorts ar a b α β)
  have haux : ∀ r ∈ rs, ∃ s k, k < ar (sel α β s) ∧ r = (sel a b s, k + 1) :=
    fun r hr => mem_auxPorts.1 (hmem r hr).1
  refine ⟨rs.length, ⟨reps ++ (a, 0) :: rs, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h.dead_fire hR (hdead p hp)
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact h.dead_fire_principal hR
      · exact (hmem p hp).2
  · refine List.pairwise_append.2 ⟨hpw.imp_of_mem ?_, List.pairwise_cons.2 ⟨?_, hpw'⟩, ?_⟩
    · intro p q hp _ hn hr
      exact hn (h.reach_fire_of_dead hR (hdead p hp) hr)
    · intro r hr
      obtain ⟨s, k, hk, rfl⟩ := haux r hr
      exact h.not_reach_principal_aux hR hk
    · intro p hp q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h.not_reach_fire_end hR (hdead p hp) h.paired_principal.1
      · obtain ⟨s, k, hk, rfl⟩ := haux q hq
        exact h.not_reach_fire_end hR (hdead p hp) (h.end_aux hk)
  · intro p hd'
    rcases h.dead_fire_cases hR hd' with hd | hr | ⟨s, k, hk, hr⟩
    · obtain ⟨r, hr, hrp⟩ := hcov p hd
      exact ⟨r, List.mem_append_left _ hr, hrp.mono (fun hl => Or.inl hl)⟩
    · exact ⟨(a, 0), List.mem_append_right _ (List.mem_cons.2 (.inl rfl)), hsymm hr⟩
    · have hde := hd'.reach hN'.symm hr
      obtain ⟨r, hr', hre⟩ := hcov' _ (mem_auxPorts.2 ⟨s, k, hk, rfl⟩) hde
      exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hre.trans (hsymm hr)⟩
  · have e : (auxPorts ar a b α β).length = ar α + ar β := by simp [auxPorts]
    omega
  · constructor
    · intro h0 s k hk hd
      obtain ⟨r, hr, -⟩ := hcov' _ (mem_auxPorts.2 ⟨s, k, hk, rfl⟩) hd
      rw [List.eq_nil_of_length_eq_zero h0] at hr
      exact absurd hr List.not_mem_nil
    · intro hall
      cases rs with
      | nil => rfl
      | cons r rs' =>
        obtain ⟨s, k, hk, e⟩ := haux r (List.mem_cons.2 (.inl rfl))
        exact absurd (e ▸ (hmem r (List.mem_cons.2 (.inl rfl))).2) (hall s k hk)

/-- **A wire closed onto itself is dead.**  If the rule joins two interface
ports whose auxiliary ports are the two ends of one wire, the firing turns
that wire into a dead component.  This holds also when the wire is a single
segment, in which case the new segment is that very segment and the set of
segments shows no cycle. -/
theorem dead_of_loop (h : Site ar N a b α β) (hR : R.WF ar α β) {s s' : Bool} {k k' : Nat}
    (hl : R.link (.ifc s k) (.ifc s' k'))
    (hp : N.Paired ar (sel a b s, k + 1) (sel a b s', k' + 1)) :
    (N.fire a b R).Dead ar (sel a b s, k + 1) := by
  have key : ∀ q, (N.fire a b R).Reach (sel a b s, k + 1) q →
      N.OnWire ar (sel a b s, k + 1) q := by
    intro q hr
    induction hr with
    | refl => exact .inl rfl
    | @tail q r _ hl' ih =>
      rcases hl' with hl' | ⟨x, y, hxy, rfl, rfl⟩
      · exact h.wf.onWire_of_reach (.tail ih.reach hl')
      · cases x with
        | ifc s₁ k₁ =>
          have hE := h.end_aux (hR.valid hxy)
          rcases ih.end_cases hp.1 hE with e | hp'
          · have ex : LPort.ifc s₁ k₁ = LPort.ifc s k := h.emb_inj e
            rw [ex] at hxy
            rw [hR.unique hxy hl]
            exact .inr hp.2.2
          · have e := hp'.det h.wf hp
            have ex : LPort.ifc s₁ k₁ = LPort.ifc s' k' := h.emb_inj e
            rw [ex] at hxy
            rw [hR.unique hxy (hR.symm hl)]
            exact .inl rfl
        | new o j k₁ =>
          exfalso
          rcases ih with e | ⟨v, x, w⟩
          · exact h.sel_ne_child (congrArg Prod.fst e).symm
          · exact h.not_used_child o j (.inr (.inl ⟨k₁, x, h.wf.symm w.link_last⟩))
  refine ⟨⟨_, .inr ⟨_, _, hl, rfl, rfl⟩⟩, fun q hr hE => ?_⟩
  rcases key q hr with rfl | ⟨v, x, w⟩
  · exact h.not_end_fire_sel s _ hE
  · have hE' := h.end_of_fire_link hE (h.wf.symm w.link_last)
    have e := Net.Paired.det h.wf ⟨hp.1, hE', v, x, w⟩ hp
    rw [e] at hE
    exact h.not_end_fire_sel s' _ hE

/-- Such a firing is counted as closing at least one loop. -/
theorem loop_counted (h : Site ar N a b α β) (hR : R.WF ar α β) {s s' : Bool} {k k' : Nat}
    (hl : R.link (.ifc s k) (.ifc s' k'))
    (hp : N.Paired ar (sel a b s, k + 1) (sel a b s', k' + 1)) {n : Nat}
    (hc : N.DeadCount ar n) : ∃ ℓ, 0 < ℓ ∧ (N.fire a b R).DeadCount ar (n + 1 + ℓ) := by
  obtain ⟨ℓ, hℓ, -, h0⟩ := h.deadCount_fire hR hc
  exact ⟨ℓ, Nat.pos_of_ne_zero fun e => h0.1 e s k (hR.valid hl) (h.dead_of_loop hR hl hp), hℓ⟩

end Site

/-- A step adds one dead component, plus one for each loop it closes. -/
theorem Step.deadCount {n : Nat} {N' : Net S} (hN : N.WF sys.ar) (h : Step sys N N')
    (hc : N.DeadCount sys.ar n) : ∃ ℓ, N'.DeadCount sys.ar (n + 1 + ℓ) := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  obtain ⟨ℓ, hℓ, -⟩ := (r.site hN).deadCount_fire (sys.rule_wf r.rule) hc
  exact ⟨ℓ, hℓ⟩

theorem Steps.deadCount {k n : Nat} {N' : Net S} (hN : N.WF sys.ar)
    (h : Steps (Step sys) k N N') (hc : N.DeadCount sys.ar n) :
    ∃ L, N'.DeadCount sys.ar (n + k + L) := by
  induction h generalizing n with
  | refl N => exact ⟨0, hc⟩
  | head h₁ _ ih =>
    obtain ⟨ℓ, hℓ⟩ := Step.deadCount hN h₁ hc
    obtain ⟨L, hL⟩ := ih (Step.wf hN h₁) hℓ
    refine ⟨ℓ + L, ?_⟩
    have e : ∀ k', n + (k' + 1) + (ℓ + L) = n + 1 + ℓ + k' + L := by
      intro k'
      omega
    rw [e]
    exact hL

/-- **The loops closed by a reduction.**  A reduction of `k` steps from `N`
to `N'` has closed `L` loops when `N'` has `k + L` more dead components than
`N`: one per step for the wire between the principal ports of the fired
pair, and one per loop. -/
def Loops (ar : S → Nat) (N : Net S) (k : Nat) (N' : Net S) (L : Nat) : Prop :=
  ∃ n, N.DeadCount ar n ∧ N'.DeadCount ar (n + k + L)

theorem Loops.unique {ar : S → Nat} {k L L' : Nat} {N' : Net S} (hN : N.WF ar)
    (hN' : N'.WF ar) (h : Loops ar N k N' L) (h' : Loops ar N k N' L') : L = L' := by
  obtain ⟨n, c, c'⟩ := h
  obtain ⟨m, d, d'⟩ := h'
  have e := c.unique hN d
  have e' := c'.unique hN' d'
  omega

/-- Every reduction of a net with finitely many dead components closes a
definite number of loops. -/
theorem Steps.loops {k n : Nat} {N' : Net S} (hN : N.WF sys.ar)
    (h : Steps (Step sys) k N N') (hc : N.DeadCount sys.ar n) :
    ∃ L, Loops sys.ar N k N' L := by
  obtain ⟨L, hL⟩ := Steps.deadCount hN h hc
  exact ⟨L, n, hc, hL⟩

/-- **The number of loops does not depend on the order of reduction**: all
reductions of a net to its normal form close the same number of loops. -/
theorem loops_unique {k m L₁ L₂ : Nat} (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) k N N₁) (h₂ : Steps (Step sys) m N N₂)
    (hn₁ : Normal (Step sys) N₁) (hn₂ : Normal (Step sys) N₂)
    (l₁ : Loops sys.ar N k N₁ L₁) (l₂ : Loops sys.ar N m N₂ L₂) : L₁ = L₂ := by
  obtain ⟨rfl, rfl⟩ := normal_form_unique hN h₁ h₂ hn₁ hn₂
  exact l₁.unique hN (Steps.wf hN h₁) l₂

/-! ### The loops closed by a firing, with and without history -/

/-- The firing of `a ⋈ b` that led to the net `N` has closed `ℓ` loops:
the list picks one auxiliary port of the two agents in each dead component
that contains one. -/
def AuxCount (ar : S → Nat) (N : Net S) (a b : Id) (α β : S) (ℓ : Nat) : Prop :=
  ∃ rs : List Port, rs.length = ℓ ∧ (∀ r ∈ rs, r ∈ auxPorts ar a b α β ∧ N.Dead ar r) ∧
    rs.Pairwise (fun p q => ¬ N.Reach p q) ∧
    ∀ e ∈ auxPorts ar a b α β, N.Dead ar e → ∃ r ∈ rs, N.Reach r e

/-- An end of the fired net was an end, or is a port of a new agent. -/
theorem Net.end_fire_old_or_child {ar : S → Nat} {a b : Id} {R : Rhs S} {q : Port}
    (hE : (N.fire a b R).End ar q) : N.End ar q ∨ ∃ o j k, q = (child a b o j, k) := by
  rcases hE with hf | ⟨γ, ⟨hg, -, -⟩ | ⟨o, j, e, -⟩, hk⟩
  · exact .inl (.inl hf)
  · exact .inl (.inr ⟨γ, hg, hk⟩)
  · exact .inr ⟨o, j, q.2, Prod.ext e rfl⟩

/-- A chain of segments of the fired net without history is a chain of
segments of the fired net. -/
theorem Net.reach_fire_of_compact {ar : S → Nat} {a b : Id} {R : Rhs S} {p q : Port}
    (hr : ((N.compact ar).fire a b R).Reach p q) : (N.fire a b R).Reach p q := by
  induction hr with
  | refl => exact .refl
  | tail _ hl ih =>
    rcases hl with hl | hl
    · obtain ⟨-, -, v, z, w⟩ := hl
      exact ih.trans (w.reach.mono (fun hl => Or.inl hl))
    · exact .tail ih (.inr hl)

namespace Site

variable {ar : S → Nat} {a b : Id} {α β : S} {R : Rhs S}

/-- If the firing has closed `ℓ` loops, the net has `1 + ℓ` more dead
components. -/
theorem deadCount_of_auxCount (h : Site ar N a b α β) (hR : R.WF ar α β) {n ℓ : Nat}
    (hc : N.DeadCount ar n) (ha : AuxCount ar (N.fire a b R) a b α β ℓ) :
    (N.fire a b R).DeadCount ar (n + 1 + ℓ) := by
  have hN' := h.fire_wf hR
  have hsymm : ∀ {x y : Port}, (N.fire a b R).Reach x y → (N.fire a b R).Reach y x :=
    fun hxy => hxy.symm hN'.symm
  obtain ⟨reps, rfl, hdead, hpw, hcov⟩ := hc
  obtain ⟨rs, rfl, hmem, hpw', hcov'⟩ := ha
  have haux : ∀ r ∈ rs, ∃ s k, k < ar (sel α β s) ∧ r = (sel a b s, k + 1) :=
    fun r hr => mem_auxPorts.1 (hmem r hr).1
  refine ⟨reps ++ (a, 0) :: rs, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h.dead_fire hR (hdead p hp)
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact h.dead_fire_principal hR
      · exact (hmem p hp).2
  · refine List.pairwise_append.2 ⟨hpw.imp_of_mem ?_, List.pairwise_cons.2 ⟨?_, hpw'⟩, ?_⟩
    · intro p q hp _ hn hr
      exact hn (h.reach_fire_of_dead hR (hdead p hp) hr)
    · intro r hr
      obtain ⟨s, k, hk, rfl⟩ := haux r hr
      exact h.not_reach_principal_aux hR hk
    · intro p hp q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h.not_reach_fire_end hR (hdead p hp) h.paired_principal.1
      · obtain ⟨s, k, hk, rfl⟩ := haux q hq
        exact h.not_reach_fire_end hR (hdead p hp) (h.end_aux hk)
  · intro p hd'
    rcases h.dead_fire_cases hR hd' with hd | hr | ⟨s, k, hk, hr⟩
    · obtain ⟨r, hr, hrp⟩ := hcov p hd
      exact ⟨r, List.mem_append_left _ hr, hrp.mono (fun hl => Or.inl hl)⟩
    · exact ⟨(a, 0), List.mem_append_right _ (List.mem_cons.2 (.inl rfl)), hsymm hr⟩
    · have hde := hd'.reach hN'.symm hr
      obtain ⟨r, hr', hre⟩ := hcov' _ (mem_auxPorts.2 ⟨s, k, hk, rfl⟩) hde
      exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hre.trans (hsymm hr)⟩

/-- A chain of segments of the fired net, from an end of the net, stays on
the wires of the ends that the fired net without history reaches. -/
theorem reach_compact_anchor (h : Site ar N a b α β) (hR : R.WF ar α β) {e x : Port}
    (he : N.End ar e) (hr : (N.fire a b R).Reach e x) :
    ∃ p, ((N.compact ar).fire a b R).Reach e p ∧
      ((∃ o j k, x = (child a b o j, k) ∧ p = x) ∨ (N.End ar p ∧ N.OnWire ar p x)) := by
  induction hr with
  | refl => exact ⟨e, .refl, .inr ⟨he, .inl rfl⟩⟩
  | @tail x x' _ hl ih =>
    obtain ⟨p, hp, hx⟩ := ih
    rcases hl with hl | ⟨z, z', hzz, rfl, rfl⟩
    · rcases hx with ⟨o, j, k, rfl, -⟩ | ⟨hpE, hw⟩
      · exact absurd (.inr (.inl ⟨k, _, hl⟩)) (h.not_used_child o j)
      · exact ⟨p, hp, .inr ⟨hpE, h.wf.onWire_of_reach (.tail hw.reach hl)⟩⟩
    · have hx' : ((N.compact ar).fire a b R).Reach e (emb a b z) := by
        rcases hx with ⟨o, j, k, -, e'⟩ | ⟨hpE, hw⟩
        · rw [← e']
          exact hp
        · cases z with
          | ifc s k =>
            rcases hw.end_cases hpE (h.end_aux (hR.valid hzz)) with e' | hpair
            · rw [e']
              exact hp
            · exact .tail hp (.inl hpair)
          | new o j k =>
            rcases hw with e' | ⟨v, y, w⟩
            · rw [e']
              exact hp
            · exact absurd (.inr (.inl ⟨k, y, h.wf.symm w.link_last⟩)) (h.not_used_child o j)
      refine ⟨emb a b z', .tail hx' (.inr ⟨z, z', hzz, rfl, rfl⟩), ?_⟩
      cases z' with
      | ifc s k => exact .inr ⟨h.end_aux (hR.valid (hR.symm hzz)), .inl rfl⟩
      | new o j k => exact .inl ⟨o, j, k, rfl, rfl⟩

/-- Between an end of the net and an end of the fired net, a chain of
segments of the fired net gives one of the fired net without history. -/
theorem reach_compact_of_fire (h : Site ar N a b α β) (hR : R.WF ar α β) {e q : Port}
    (he : N.End ar e) (hq : N.End ar q ∨ ∃ o j k, q = (child a b o j, k))
    (hr : (N.fire a b R).Reach e q) : ((N.compact ar).fire a b R).Reach e q := by
  obtain ⟨p, hp, hx⟩ := h.reach_compact_anchor hR he hr
  rcases hx with ⟨o, j, k, -, e'⟩ | ⟨hpE, hw⟩
  · rw [← e']
    exact hp
  · rcases hw with e' | ⟨v, y, w⟩
    · rw [e']
      exact hp
    · rcases hq with hqE | ⟨o, j, k, rfl⟩
      · exact .tail hp (.inl ⟨hpE, hqE, v, y, w⟩)
      · exact absurd (.inr (.inl ⟨k, y, h.wf.symm w.link_last⟩)) (h.not_used_child o j)

/-- **History does not change the loops.**  The loops closed by a firing in
a net are those closed by the same firing in the net without history. -/
theorem auxCount_of_compact (h : Site ar N a b α β) (hR : R.WF ar α β) {ℓ : Nat}
    (hc : AuxCount ar ((N.compact ar).fire a b R) a b α β ℓ) :
    AuxCount ar (N.fire a b R) a b α β ℓ := by
  obtain ⟨rs, hlen, hmem, hpw, hcov⟩ := hc
  have hendc : ∀ q : Port, ((N.compact ar).fire a b R).End ar q ↔ (N.fire a b R).End ar q :=
    fun q => Net.end_congr (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) q
  have haux : ∀ {r : Port}, r ∈ auxPorts ar a b α β → N.End ar r := by
    intro r hr
    obtain ⟨s, k, hk, rfl⟩ := mem_auxPorts.1 hr
    exact h.end_aux hk
  have hlink : ∀ {r : Port}, r ∈ auxPorts ar a b α β →
      ∃ q, ((N.compact ar).fire a b R).link r q := by
    intro r hr
    obtain ⟨s, k, hk, rfl⟩ := mem_auxPorts.1 hr
    obtain ⟨y, hy⟩ := hR.total (x := .ifc s k) hk
    exact ⟨emb a b y, .inr ⟨_, _, hy, rfl, rfl⟩⟩
  refine ⟨rs, hlen, fun r hr => ⟨(hmem r hr).1, ?_⟩, hpw.imp_of_mem ?_, fun e he hd => ?_⟩
  · obtain ⟨s, k, hk, e⟩ := mem_auxPorts.1 (hmem r hr).1
    obtain ⟨y, hy⟩ := hR.total (x := .ifc s k) hk
    refine ⟨⟨emb a b y, .inr ⟨.ifc s k, y, hy, e, rfl⟩⟩, fun q' hr' hE => ?_⟩
    exact (hmem r hr).2.2 q' (h.reach_compact_of_fire hR (haux (hmem r hr).1)
      (Net.end_fire_old_or_child hE) hr') ((hendc q').2 hE)
  · intro p q hp hq hn hreach
    exact hn (h.reach_compact_of_fire hR (haux (hmem p hp).1) (.inl (haux (hmem q hq).1)) hreach)
  · have hd' : ((N.compact ar).fire a b R).Dead ar e :=
      ⟨hlink he, fun q hr hE => hd.2 q (Net.reach_fire_of_compact hr) ((hendc q).1 hE)⟩
    obtain ⟨r, hr, hre⟩ := hcov e he hd'
    exact ⟨r, hr, Net.reach_fire_of_compact hre⟩

end Site

end ClosedLoops

/-! ## Right-hand sides given by a partner function -/

theorem LPort.swap_inj {x y : LPort} : x.swap = y.swap ↔ x = y :=
  ⟨fun h => by simpa using congrArg LPort.swap h, fun h => h ▸ rfl⟩

/-- The right-hand side in which port `x` is wired to `wire x`. -/
def Rhs.ofWire (lab : Option Bool → Nat → Option S) (wire : LPort → Option LPort) : Rhs S where
  lab := lab
  link x y := wire x = some y

theorem Rhs.ofWire_wf {ar : S → Nat} {lab : Option Bool → Nat → Option S}
    {wire : LPort → Option LPort} {α β : S}
    (hs : ∀ x y, wire x = some y → wire y = some x)
    (hi : ∀ x, wire x ≠ some x)
    (hv : ∀ x, (wire x).isSome ↔ (Rhs.ofWire lab wire).Valid ar α β x) :
    (Rhs.ofWire lab wire).WF ar α β where
  symm := fun h => hs _ _ h
  irrefl := fun h => hi _ h
  valid := fun {x y} h => (hv x).1 (by simp [show wire x = some y from h])
  unique := fun {x y z} h h' => Option.some.inj ((show wire x = some y from h).symm.trans h')
  total := fun {x} h => Option.isSome_iff_exists.1 ((hv x).2 h)

theorem Rhs.ofWire_mirror {lab : Option Bool → Nat → Option S} {wire : LPort → Option LPort}
    (hl : ∀ o j, lab o j = lab (flipOwner o) j)
    (hw : ∀ x, wire x.swap = (wire x).map LPort.swap) :
    (Rhs.ofWire lab wire).Mirror (Rhs.ofWire lab wire) := by
  refine ⟨hl, fun x y => ?_⟩
  show wire x = some y ↔ wire x.swap = some y.swap
  rw [hw]
  cases wire x with
  | none => simp
  | some z => simp [LPort.swap_inj]

end INet
