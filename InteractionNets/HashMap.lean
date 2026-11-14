import InteractionNets.Matchings

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## A reducer on hash maps

The reducer of the previous sections keeps its net in lists: every lookup is
a scan, and every step rebuilds the table of wires.  The reducer of this
section keeps agents and wires in hash maps and the active pairs in a work
list.  A step takes an active pair from the work list, reads its
neighbourhood out of the maps, fires it there with the verified list
reducer, and writes the result back; this is correct because firing is
local.  The work done in a step depends on the rule, not on the size of the
net. -/

section HashLemmas

variable {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K]

theorem hget_insert (m : Std.HashMap K V) (k a : K) (v : V) :
    (m.insert k v)[a]? = if k = a then some v else m[a]? := by
  rw [Std.HashMap.getElem?_insert]
  simp

theorem hget_erase (m : Std.HashMap K V) (k a : K) :
    (m.erase k)[a]? = if k = a then none else m[a]? := by
  rw [Std.HashMap.getElem?_erase]
  simp

/-- Erasing the keys of a list. -/
theorem hget_foldl_erase (l : List (K × V)) : ∀ (m : Std.HashMap K V) (p : K) (q : V),
    (l.foldl (fun m e => m.erase e.1) m)[p]? = some q ↔ m[p]? = some q ∧ ∀ e ∈ l, e.1 ≠ p := by
  induction l with
  | nil =>
    intro m p q
    exact ⟨fun h => ⟨h, fun e he => absurd he List.not_mem_nil⟩, fun h => h.1⟩
  | cons e l ih =>
    intro m p q
    rw [List.foldl_cons, ih, hget_erase]
    constructor
    · rintro ⟨h, hl⟩
      split at h
      · cases h
      · rename_i he
        refine ⟨h, fun e' he' => ?_⟩
        rcases List.mem_cons.1 he' with eq | he'
        · rw [eq]
          exact he
        · exact hl e' he'
    · rintro ⟨h, hl⟩
      have he : e.1 ≠ p := hl e (List.mem_cons.2 (.inl rfl))
      refine ⟨?_, fun e' he' => hl e' (List.mem_cons_of_mem _ he')⟩
      simp only [he, ↓reduceIte]
      exact h

/-- Inserting the entries of a list in which no key has two values. -/
theorem hget_foldl_insert (l : List (K × V))
    (hf : ∀ {k : K} {v v' : V}, (k, v) ∈ l → (k, v') ∈ l → v = v') :
    ∀ (m : Std.HashMap K V) (p : K) (q : V),
      (l.foldl (fun m e => m.insert e.1 e.2) m)[p]? = some q ↔
        (p, q) ∈ l ∨ (m[p]? = some q ∧ ∀ q', (p, q') ∉ l) := by
  induction l with
  | nil =>
    intro m p q
    exact ⟨fun h => .inr ⟨h, fun q' hq' => absurd hq' List.not_mem_nil⟩,
      fun h => h.elim (fun h => absurd h List.not_mem_nil) (fun h => h.1)⟩
  | cons e l ih =>
    intro m p q
    have hf' : ∀ {k : K} {v v' : V}, (k, v) ∈ l → (k, v') ∈ l → v = v' :=
      fun h h' => hf (List.mem_cons_of_mem _ h) (List.mem_cons_of_mem _ h')
    rw [List.foldl_cons, ih hf', hget_insert]
    by_cases he : e.1 = p
    · have hi : (if e.1 = p then some e.2 else m[p]?) = some e.2 := by simp [he]
      rw [hi]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inl (List.mem_cons.2 (.inl (Prod.ext he.symm (Option.some.inj h).symm)))
      · rintro (h | ⟨-, h⟩)
        · rcases List.mem_cons.1 h with eq | h
          · by_cases hex : ∃ q', (p, q') ∈ l
            · obtain ⟨q', hq'⟩ := hex
              have e' : q' = q := hf (List.mem_cons_of_mem _ hq') (List.mem_cons.2 (.inl eq))
              exact .inl (e' ▸ hq')
            · exact .inr ⟨congrArg some (congrArg Prod.snd eq).symm, fun q' hq' => hex ⟨q', hq'⟩⟩
          · exact .inl h
        · have hmem : (p, e.2) ∈ e :: l := List.mem_cons.2 (.inl (Prod.ext he.symm rfl))
          exact absurd hmem (h e.2)
    · have hi : (if e.1 = p then some e.2 else m[p]?) = m[p]? := by simp [he]
      rw [hi]
      constructor
      · rintro (h | ⟨h, hn⟩)
        · exact .inl (List.mem_cons_of_mem _ h)
        · refine .inr ⟨h, fun q' hq' => ?_⟩
          rcases List.mem_cons.1 hq' with eq | hq'
          · exact he (congrArg Prod.fst eq).symm
          · exact hn q' hq'
      · rintro (h | ⟨h, hn⟩)
        · rcases List.mem_cons.1 h with eq | h
          · exact absurd (congrArg Prod.fst eq).symm he
          · exact .inl h
        · exact .inr ⟨h, fun q' hq' => hn q' (List.mem_cons_of_mem _ hq')⟩

end HashLemmas

/-- A net without history, in hash maps, with a work list of pairs of agents
that may be active. -/
structure HNet (S : Type) where
  agents : Std.HashMap Id S
  wires : Std.HashMap Port Port
  free : List Port
  work : List (Id × Id)

/-- The net that the maps stand for. -/
def HNet.toNet (H : HNet S) : Net S where
  agent i γ := H.agents[i]? = some γ
  link p q := H.wires[p]? = some q
  free p := p ∈ H.free

/-- The ports of an agent. -/
def portsOf (ar : S → Nat) (a : Id) (α : S) : List Port :=
  (List.range (ar α + 1)).map fun k => (a, k)

theorem mem_portsOf {ar : S → Nat} {a : Id} {α : S} {p : Port} :
    p ∈ portsOf ar a α ↔ p.1 = a ∧ p.2 ≤ ar α := by
  unfold portsOf
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨rfl, Nat.le_of_lt_succ (List.mem_range.1 hk)⟩
  · rintro ⟨e, hk⟩
    exact ⟨p.2, List.mem_range.2 (Nat.lt_succ_of_le hk), Prod.ext e.symm rfl⟩

/-- The wires at the ports of two agents, read out of the map. -/
def HNet.nearWires (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) : List (Port × Port) :=
  (portsOf ar a α ++ portsOf ar b β).filterMap fun A => (H.wires[A]?).map fun q => (A, q)

theorem HNet.mem_nearWires {ar : S → Nat} {H : HNet S} {a b : Id} {α β : S} {p q : Port} :
    (p, q) ∈ H.nearWires ar a b α β ↔
      ((p.1 = a ∧ p.2 ≤ ar α) ∨ (p.1 = b ∧ p.2 ≤ ar β)) ∧ H.wires[p]? = some q := by
  unfold HNet.nearWires
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨A, hA, he⟩
    cases hw : H.wires[A]? with
    | none =>
      rw [hw] at he
      cases he
    | some q' =>
      rw [hw] at he
      have e' : (A, q') = (p, q) := Option.some.inj he
      rw [List.mem_append, mem_portsOf, mem_portsOf] at hA
      rw [← (Prod.mk.inj e').1, ← (Prod.mk.inj e').2]
      exact ⟨hA, hw⟩
  · rintro ⟨hA, hw⟩
    refine ⟨p, ?_, by rw [hw]; rfl⟩
    rw [List.mem_append, mem_portsOf, mem_portsOf]
    exact hA

/-- The neighbourhood of two agents, as a list net. -/
def HNet.nbhd (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) : XNet S :=
  ⟨[(a, α), (b, β)],
    (H.nearWires ar a b α β).filterMap fun e => if e.2.1 = a ∨ e.2.1 = b then none else some e.2,
    H.nearWires ar a b α β ++ (H.nearWires ar a b α β).map fun e => (e.2, e.1)⟩

/-- It stands for the neighbourhood of the two agents in the net. -/
theorem HNet.nbhd_toNet {ar : S → Nat} {H : HNet S} {a b : Id} {α β : S}
    (hm : H.toNet.Matching ar) (ha : H.toNet.agent a α) (hb : H.toNet.agent b β) :
    (H.nbhd ar a b α β).toNet = H.toNet.nbhd a b α β := by
  have ka : ∀ {p q : Port}, H.toNet.link p q → p.1 = a → p.2 ≤ ar α := by
    intro p q hl e
    rcases hm.ends hl with hf | ⟨γ, hg, hk⟩
    · exact absurd (e ▸ ha) (hm.free_agent hf)
    · rw [e] at hg
      rw [hm.agent_fun hg ha] at hk
      exact hk
  have kb : ∀ {p q : Port}, H.toNet.link p q → p.1 = b → p.2 ≤ ar β := by
    intro p q hl e
    rcases hm.ends hl with hf | ⟨γ, hg, hk⟩
    · exact absurd (e ▸ hb) (hm.free_agent hf)
    · rw [e] at hg
      rw [hm.agent_fun hg hb] at hk
      exact hk
  apply Net.ext'
  · intro i γ
    show (i, γ) ∈ [(a, α), (b, β)] ↔ (i = a ∧ γ = α) ∨ (i = b ∧ γ = β)
    constructor
    · intro h
      rcases List.mem_cons.1 h with e | h
      · exact .inl ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
      · rcases List.mem_cons.1 h with e | h
        · exact .inr ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
        · exact absurd h List.not_mem_nil
    · rintro (⟨e₁, e₂⟩ | ⟨e₁, e₂⟩)
      · rw [e₁, e₂]
        exact List.mem_cons.2 (.inl rfl)
      · rw [e₁, e₂]
        exact List.mem_cons_of_mem _ (List.mem_cons.2 (.inl rfl))
  · intro p q
    show (p, q) ∈ H.nearWires ar a b α β ++ (H.nearWires ar a b α β).map (fun e => (e.2, e.1)) ↔
      H.toNet.link p q ∧ (p.1 = a ∨ p.1 = b ∨ q.1 = a ∨ q.1 = b)
    rw [List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨e, he, eq⟩)
      · obtain ⟨hA, hw⟩ := HNet.mem_nearWires.1 h
        exact ⟨hw, hA.elim (fun h => .inl h.1) (fun h => .inr (.inl h.1))⟩
      · have he' : (q, p) ∈ H.nearWires ar a b α β := by
          have e' : e = (q, p) := Prod.ext (Prod.mk.inj eq).2 (Prod.mk.inj eq).1
          rw [← e']
          exact he
        obtain ⟨hA, hw⟩ := HNet.mem_nearWires.1 he'
        exact ⟨hm.symm hw, hA.elim (fun h => .inr (.inr (.inl h.1))) (fun h => .inr (.inr (.inr h.1)))⟩
    · rintro ⟨hl, ho⟩
      rcases ho with e | e | e | e
      · exact .inl (HNet.mem_nearWires.2 ⟨.inl ⟨e, ka hl e⟩, hl⟩)
      · exact .inl (HNet.mem_nearWires.2 ⟨.inr ⟨e, kb hl e⟩, hl⟩)
      · exact .inr ⟨(q, p), HNet.mem_nearWires.2 ⟨.inl ⟨e, ka (hm.symm hl) e⟩, hm.symm hl⟩, rfl⟩
      · exact .inr ⟨(q, p), HNet.mem_nearWires.2 ⟨.inr ⟨e, kb (hm.symm hl) e⟩, hm.symm hl⟩, rfl⟩
  · intro p
    show p ∈ (H.nearWires ar a b α β).filterMap
        (fun e => if e.2.1 = a ∨ e.2.1 = b then none else some e.2) ↔
      p.1 ≠ a ∧ p.1 ≠ b ∧ ∃ A : Port, (A.1 = a ∨ A.1 = b) ∧ H.toNet.link A p
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨⟨A, q⟩, he, hs⟩
      dsimp only at hs
      split at hs
      · cases hs
      · rename_i hn
        have e' : q = p := Option.some.inj hs
        rw [e'] at hn he
        obtain ⟨hA, hw⟩ := HNet.mem_nearWires.1 he
        exact ⟨fun e => hn (.inl e), fun e => hn (.inr e), A,
          hA.elim (fun h => .inl h.1) (fun h => .inr h.1), hw⟩
    · rintro ⟨hpa, hpb, A, hA, hl⟩
      refine ⟨(A, p), HNet.mem_nearWires.2 ⟨?_, hl⟩, by simp [hpa, hpb]⟩
      rcases hA with e | e
      · exact .inl ⟨e, ka hl e⟩
      · exact .inr ⟨e, kb hl e⟩

/-- The pairs of agents whose principal ports are joined by a wire of the
list. -/
def principalPairs (ws : List (Port × Port)) : List (Id × Id) :=
  ws.filterMap fun e => if e.1.2 = 0 ∧ e.2.2 = 0 then some (e.1.1, e.2.1) else none

theorem mem_principalPairs {ws : List (Port × Port)} {c d : Id} (h : ((c, 0), (d, 0)) ∈ ws) :
    (c, d) ∈ principalPairs ws :=
  List.mem_filterMap.2 ⟨_, h, by simp⟩

/-- Fire the active pair `a ⋈ b`: read its neighbourhood, fire it there
with the list reducer, erase the old wires of the neighbourhood, write the
new ones, and put on the work list the pairs of principal ports that the new
wires join. -/
def HNet.fire (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) (R : XRhs S)
    (rest : List (Id × Id)) : HNet S where
  agents := ((H.nbhd ar a b α β).fire ar a b α β R).agents.foldl
    (fun m e => m.insert e.1 e.2) ((H.agents.erase a).erase b)
  wires := ((H.nbhd ar a b α β).fire ar a b α β R).wires.foldl
    (fun m e => m.insert e.1 e.2) ((H.nbhd ar a b α β).wires.foldl (fun m e => m.erase e.1) H.wires)
  free := H.free
  work := principalPairs ((H.nbhd ar a b α β).fire ar a b α β R).wires ++ rest

/-- **The hash-map firing is the firing**, followed by compaction; and the
wires of the fired neighbourhood that join two principal ports are on the new
work list. -/
theorem HNet.fire_toNet {xs : XSys S} {H : HNet S} (hm : H.toNet.Matching xs.sys.ar) {a b : Id}
    {α β : S} {R : XRhs S} (r : Redex xs.sys H.toNet a b α β R.toRhs)
    (hR : xs.rule α β = some R) (rest : List (Id × Id)) :
    (H.fire xs.sys.ar a b α β R rest).toNet = (H.toNet.fire a b R.toRhs).compact xs.sys.ar ∧
      ∀ c d, ((H.toNet.nbhd a b α β).fire a b R.toRhs).Paired xs.sys.ar (c, 0) (d, 0) →
        (c, d) ∈ (H.fire xs.sys.ar a b α β R rest).work := by
  have site := r.site hm.wf
  have hRwf := xs.sys.rule_wf r.rule
  have site₀ := site.nbhd_site hm
  have e₀ := HNet.nbhd_toNet hm r.ha r.hb
  have hX₀ : (H.nbhd xs.sys.ar a b α β).Ok xs.sys.ar := by
    rw [XNet.ok_iff_matching, e₀]
    exact site.nbhd_matching hm
  have r₀ : Redex xs.sys (H.nbhd xs.sys.ar a b α β).toNet a b α β R.toRhs := by
    rw [e₀]
    exact ⟨site₀.ha, site₀.hb, site₀.ne, site₀.conn, r.rule⟩
  have e₁ := XNet.fire_toNet hX₀ r₀ hR
  rw [e₀] at e₁
  have hm₁ : ((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).toNet.Matching xs.sys.ar := by
    rw [e₁]
    exact (site₀.fire_wf hRwf).compact.matching (Net.compact_idem _ _)
  have hw₁ : ∀ p q, (p, q) ∈ ((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).wires ↔
      ((H.toNet.nbhd a b α β).fire a b R.toRhs).Paired xs.sys.ar p q := by
    intro p q
    have h : ((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).toNet.link p q ↔
        (((H.toNet.nbhd a b α β).fire a b R.toRhs).compact xs.sys.ar).link p q := by rw [e₁]
    exact h
  have ha₁ : ∀ i γ, (i, γ) ∈ ((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).agents ↔
      ∃ o j, i = child a b o j ∧ R.toRhs.lab o j = some γ := by
    intro i γ
    have h : ((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).toNet.agent i γ ↔
        (((H.toNet.nbhd a b α β).fire a b R.toRhs).compact xs.sys.ar).agent i γ := by rw [e₁]
    refine h.trans ⟨?_, fun hc => .inr hc⟩
    rintro (⟨⟨e, -⟩ | ⟨e, -⟩, na, nb⟩ | hc)
    · exact absurd e na
    · exact absurd e nb
    · exact hc
  have hw₀ : ∀ x y, (x, y) ∈ (H.nbhd xs.sys.ar a b α β).wires ↔
      (H.toNet.nbhd a b α β).link x y := by
    intro x y
    have h : (H.nbhd xs.sys.ar a b α β).toNet.link x y ↔ (H.toNet.nbhd a b α β).link x y := by
      rw [e₀]
    exact h
  refine ⟨?_, fun c d hp => List.mem_append_left _ (mem_principalPairs ((hw₁ _ _).2 hp))⟩
  apply Net.ext'
  · intro i γ
    show (((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).agents.foldl
        (fun m e => m.insert e.1 e.2) ((H.agents.erase a).erase b))[i]? = some γ ↔ _
    refine (hget_foldl_insert _ (fun h h' => hm₁.agent_fun h h') _ i γ).trans ?_
    rw [hget_erase, hget_erase]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact .inr ((ha₁ i γ).1 h)
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i hb ha
            exact .inl ⟨h, fun e => ha e.symm, fun e => hb e.symm⟩
    · rintro (⟨hg, hia, hib⟩ | hc)
      · refine .inr ⟨?_, fun γ' hmem => ?_⟩
        · have hi : (if b = i then none else if a = i then none else H.agents[i]?) =
              H.agents[i]? := by simp [Ne.symm hia, Ne.symm hib]
          rw [hi]
          exact hg
        · obtain ⟨o, j, e, -⟩ := (ha₁ i γ').1 hmem
          exact site.not_used_child o j (.inl ⟨γ, e ▸ hg⟩)
      · exact .inl ((ha₁ i γ).2 hc)
  · intro p q
    show (((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).wires.foldl
        (fun m e => m.insert e.1 e.2)
        ((H.nbhd xs.sys.ar a b α β).wires.foldl (fun m e => m.erase e.1) H.wires))[p]? = some q ↔
      (H.toNet.fire a b R.toRhs).Paired xs.sys.ar p q
    refine (hget_foldl_insert _ (fun h h' => hm₁.functional h h') _ p q).trans ?_
    rw [hget_foldl_erase, site.fire_local hm hRwf]
    constructor
    · rintro (h | ⟨⟨hl, hne⟩, -⟩)
      · exact .inl ((hw₁ p q).1 h)
      · have hno : ¬ (p.1 = a ∨ p.1 = b ∨ q.1 = a ∨ q.1 = b) :=
          fun ho => hne (p, q) ((hw₀ p q).2 ⟨hl, ho⟩) rfl
        exact .inr ⟨hl, fun e => hno (.inl e), fun e => hno (.inr (.inl e)),
          fun e => hno (.inr (.inr (.inl e))), fun e => hno (.inr (.inr (.inr e)))⟩
    · rintro (hp₀ | ⟨hl, hpa, hpb, hqa, hqb⟩)
      · exact .inl ((hw₁ p q).2 hp₀)
      · by_cases hx : (p, q) ∈ ((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).wires
        · exact .inl hx
        · refine .inr ⟨⟨hl, fun e he heq => ?_⟩, fun q' hq' => hx ?_⟩
          · obtain ⟨hl', ho⟩ := (hw₀ e.1 e.2).1 he
            rw [heq] at hl' ho
            rw [hm.functional hl' hl] at ho
            rcases ho with ho | ho | ho | ho
            · exact hpa ho
            · exact hpb ho
            · exact hqa ho
            · exact hqb ho
          · have h₁ : (H.toNet.fire a b R.toRhs).Paired xs.sys.ar p q' :=
              (site.fire_local hm hRwf).2 (.inl ((hw₁ p q').1 hq'))
            have h₂ : (H.toNet.fire a b R.toRhs).Paired xs.sys.ar p q :=
              (site.fire_local hm hRwf).2 (.inr ⟨hl, hpa, hpb, hqa, hqb⟩)
            rw [← h₁.det (site.fire_wf hRwf) h₂]
            exact hq'
  · intro p
    exact Iff.rfl

/-- The invariant of the hash-map reducer: the maps stand for a net without
history, and every active pair is on the work list. -/
structure HNet.Inv (xs : XSys S) (H : HNet S) : Prop where
  matching : H.toNet.Matching xs.sys.ar
  cover : ∀ {c d : Id} {γ δ : S} {R : Rhs S}, Redex xs.sys H.toNet c d γ δ R →
    (c, d) ∈ H.work ∨ (d, c) ∈ H.work

/-- Is `c ⋈ d` an active pair?  Four lookups. -/
def HNet.redexOf (xs : XSys S) (H : HNet S) (c d : Id) : Option (S × S × XRhs S) :=
  match H.agents[c]? with
  | none => none
  | some γ =>
    match H.agents[d]? with
    | none => none
    | some δ =>
      if H.wires[(c, 0)]? = some (d, 0) then (xs.rule γ δ).map fun R => (γ, δ, R) else none

theorem HNet.redexOf_sound {xs : XSys S} {H : HNet S} (hm : H.toNet.Matching xs.sys.ar)
    {c d : Id} {γ δ : S} {R : XRhs S} (h : H.redexOf xs c d = some (γ, δ, R)) :
    Redex xs.sys H.toNet c d γ δ R.toRhs ∧ xs.rule γ δ = some R := by
  unfold HNet.redexOf at h
  cases hc : H.agents[c]? with
  | none =>
    rw [hc] at h
    cases h
  | some γ' =>
    cases hd : H.agents[d]? with
    | none =>
      rw [hc, hd] at h
      cases h
    | some δ' =>
      rw [hc, hd] at h
      dsimp only at h
      split at h
      · rename_i hw
        cases hr : xs.rule γ' δ' with
        | none =>
          rw [hr] at h
          cases h
        | some R' =>
          rw [hr] at h
          have e : (γ', δ', R') = (γ, δ, R) := Option.some.inj h
          have e₁ : γ' = γ := (Prod.mk.inj e).1
          have e₂ : δ' = δ := (Prod.mk.inj (Prod.mk.inj e).2).1
          have e₃ : R' = R := (Prod.mk.inj (Prod.mk.inj e).2).2
          rw [e₁] at hc hr
          rw [e₂] at hd hr
          rw [e₃] at hr
          refine ⟨⟨hc, hd, ?_, ⟨_, _, .single hw⟩, ?_⟩, hr⟩
          · rintro rfl
            exact hm.irrefl hw
          · rw [xs.rule_spec, hr]
            rfl
      · cases h

theorem HNet.redexOf_complete {xs : XSys S} {H : HNet S} (hm : H.toNet.Matching xs.sys.ar)
    {c d : Id} {γ δ : S} {R : Rhs S} (r : Redex xs.sys H.toNet c d γ δ R) :
    H.redexOf xs c d ≠ none := by
  have hc : H.agents[c]? = some γ := r.ha
  have hd : H.agents[d]? = some δ := r.hb
  have hw : H.wires[(c, 0)]? = some (d, 0) :=
    hm.paired_iff.1 ⟨r.end_left, r.end_right, r.conn⟩
  have hr := r.rule
  rw [xs.rule_spec] at hr
  cases hx : xs.rule γ δ with
  | none =>
    rw [hx] at hr
    cases hr
  | some R' => simp [HNet.redexOf, hc, hd, hw, hx]

/-- The first pair of the work list that is active, and the rest of the
list. -/
def HNet.next (xs : XSys S) (H : HNet S) :
    List (Id × Id) → Option ((Id × Id × S × S × XRhs S) × List (Id × Id))
  | [] => none
  | (c, d) :: w =>
    match H.redexOf xs c d with
    | some t => some ((c, d, t), w)
    | none => HNet.next xs H w

theorem HNet.next_some {xs : XSys S} {H : HNet S} :
    ∀ {w : List (Id × Id)} {t : Id × Id × S × S × XRhs S} {rest : List (Id × Id)},
      H.next xs w = some (t, rest) →
        H.redexOf xs t.1 t.2.1 = some t.2.2 ∧
          ∀ e ∈ w, e ∈ rest ∨ e = (t.1, t.2.1) ∨ H.redexOf xs e.1 e.2 = none
  | [], _, _, h => by cases h
  | (c, d) :: w, t, rest, h => by
    unfold HNet.next at h
    cases hr : H.redexOf xs c d with
    | some t' =>
      rw [hr] at h
      have e : ((c, d, t'), w) = (t, rest) := Option.some.inj h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      refine ⟨hr, fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact .inr (.inl rfl)
      · exact .inl he
    | none =>
      rw [hr] at h
      obtain ⟨h₁, h₂⟩ := HNet.next_some (w := w) h
      refine ⟨h₁, fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact .inr (.inr hr)
      · exact h₂ e he

theorem HNet.next_none {xs : XSys S} {H : HNet S} :
    ∀ {w : List (Id × Id)}, H.next xs w = none → ∀ e ∈ w, H.redexOf xs e.1 e.2 = none
  | [], _, e, he => absurd he List.not_mem_nil
  | (c, d) :: w, h, e, he => by
    unfold HNet.next at h
    cases hr : H.redexOf xs c d with
    | some t' =>
      rw [hr] at h
      cases h
    | none =>
      rw [hr] at h
      rcases List.mem_cons.1 he with rfl | he
      · exact hr
      · exact HNet.next_none (w := w) h e he

/-- One step: take the first active pair of the work list and fire it;
`none` when the work list holds no active pair. -/
def HNet.step (xs : XSys S) (H : HNet S) : Option (HNet S) :=
  (H.next xs H.work).map fun r =>
    H.fire xs.sys.ar r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2.1 r.1.2.2.2.2 r.2

/-- **A step of the hash-map reducer is a step of reduction without
history**, and preserves the invariant. -/
theorem HNet.step_sound {xs : XSys S} {H H' : HNet S} (hi : H.Inv xs) (h : H.step xs = some H') :
    CStep xs.sys H.toNet H'.toNet ∧ H'.Inv xs := by
  unfold HNet.step at h
  cases hn : H.next xs H.work with
  | none =>
    rw [hn] at h
    cases h
  | some r =>
    obtain ⟨⟨a, b, α, β, R⟩, rest⟩ := r
    rw [hn] at h
    have eH : H.fire xs.sys.ar a b α β R rest = H' := Option.some.inj h
    rw [← eH]
    obtain ⟨hro, hwork⟩ := HNet.next_some hn
    obtain ⟨red, hR⟩ := HNet.redexOf_sound hi.matching hro
    obtain ⟨e, hpush⟩ := HNet.fire_toNet hi.matching red hR rest
    have site := red.site hi.matching.wf
    have hRwf := xs.sys.rule_wf red.rule
    refine ⟨⟨_, ⟨a, b, α, β, _, red, rfl⟩, e⟩, ?_, ?_⟩
    · rw [e]
      exact (site.fire_wf hRwf).compact.matching (Net.compact_idem _ _)
    · intro c d γ δ R₂ r₂
      rw [e] at r₂
      have hp : (H.toNet.fire a b R.toRhs).Paired xs.sys.ar (c, 0) (d, 0) :=
        Net.compact_paired.1 ⟨r₂.end_left, r₂.end_right, r₂.conn⟩
      rcases (site.fire_local hi.matching hRwf).1 hp with hp₀ | ⟨hl, hca, -, hda, -⟩
      · exact .inl (hpush c d hp₀)
      · have hc : H.toNet.agent c γ := by
          rcases r₂.ha with ⟨hg, -, -⟩ | ⟨o, j, e', -⟩
          · exact hg
          · exact absurd (.inr (.inl ⟨0, _, e' ▸ hl⟩)) (site.not_used_child o j)
        have hd : H.toNet.agent d δ := by
          rcases r₂.hb with ⟨hg, -, -⟩ | ⟨o, j, e', -⟩
          · exact hg
          · exact absurd (.inr (.inl ⟨0, _, e' ▸ hi.matching.symm hl⟩)) (site.not_used_child o j)
        have rold : Redex xs.sys H.toNet c d γ δ R₂ :=
          ⟨hc, hd, r₂.ne, ⟨_, _, .single hl⟩, r₂.rule⟩
        have key : ∀ {x y : Id} {γ' δ' : S} {R' : Rhs S}, Redex xs.sys H.toNet x y γ' δ' R' →
            x ≠ a → (x, y) ∈ H.work → (x, y) ∈ (H.fire xs.sys.ar a b α β R rest).work := by
          intro x y γ' δ' R' rx hxa hmem
          rcases hwork _ hmem with hrest | heq | hnone
          · exact List.mem_append_right _ hrest
          · exact absurd (Prod.mk.inj heq).1 hxa
          · exact absurd hnone (HNet.redexOf_complete hi.matching rx)
        rcases hi.cover rold with hmem | hmem
        · exact .inl (key rold hca hmem)
        · obtain ⟨R₃, rflip, -⟩ := rold.flip hi.matching.wf
          exact .inr (key rflip hda hmem)

/-- **The hash-map reducer stops only on normal forms.** -/
theorem HNet.step_complete {xs : XSys S} {H : HNet S} (hi : H.Inv xs) (h : H.step xs = none) :
    Normal (CStep xs.sys) H.toNet := by
  rintro C' ⟨N', ⟨c, d, γ, δ, R, r, -⟩, -⟩
  unfold HNet.step at h
  cases hn : H.next xs H.work with
  | some t =>
    rw [hn] at h
    cases h
  | none =>
    have hall := HNet.next_none hn
    rcases hi.cover r with hm | hm
    · exact HNet.redexOf_complete hi.matching r (hall _ hm)
    · obtain ⟨R', r', -⟩ := r.flip hi.matching.wf
      exact HNet.redexOf_complete hi.matching r' (hall _ hm)

/-- Run the hash-map reducer for at most `n` steps.  Returns the state
reached and the number of steps taken. -/
def HNet.run (xs : XSys S) : Nat → HNet S → HNet S × Nat
  | 0, H => (H, 0)
  | n + 1, H =>
    match H.step xs with
    | none => (H, 0)
    | some H' => ((HNet.run xs n H').1, (HNet.run xs n H').2 + 1)

theorem HNet.run_steps {xs : XSys S} {H : HNet S} (hi : H.Inv xs) (n : Nat) :
    Steps (CStep xs.sys) (H.run xs n).2 H.toNet (H.run xs n).1.toNet ∧ (H.run xs n).1.Inv xs := by
  induction n generalizing H with
  | zero => exact ⟨.refl _, hi⟩
  | succ n ih =>
    unfold HNet.run
    split
    · exact ⟨.refl _, hi⟩
    · rename_i H' hs
      obtain ⟨st, hi'⟩ := HNet.step_sound hi hs
      obtain ⟨sts, hok⟩ := ih hi'
      exact ⟨.head st sts, hok⟩

/-- **Correctness of the hash-map reducer**: if it stops, the net it has
reached is the normal form of the input, the number of steps it took is the
length of every reduction to normal form, and no reduction is longer. -/
theorem HNet.run_normal {xs : XSys S} {H : HNet S} (hi : H.Inv xs) (n : Nat)
    (h : (H.run xs n).1.step xs = none) :
    Normal (CStep xs.sys) (H.run xs n).1.toNet ∧
      ∀ {m : Nat} {C : Net S}, Steps (CStep xs.sys) m H.toNet C →
        m ≤ (H.run xs n).2 ∧
          (Normal (CStep xs.sys) C → C = (H.run xs n).1.toNet ∧ m = (H.run xs n).2) := by
  obtain ⟨sts, hok⟩ := HNet.run_steps hi n
  have hn := HNet.step_complete hok h
  have hwf := hi.matching.wf
  refine ⟨hn, fun {m C} hC => ⟨((cstrongConfluent xs.sys).bounded hwf sts hn hC).1, fun hnC => ?_⟩⟩
  exact cnormal_form_unique hwf hC sts hnC hn

theorem HNet.run_stop_or_full (xs : XSys S) (H : HNet S) (n : Nat) :
    (H.run xs n).1.step xs = none ∨ (H.run xs n).2 = n := by
  induction n generalizing H with
  | zero => exact .inr rfl
  | succ n ih =>
    unfold HNet.run
    split
    · rename_i hs
      exact .inl hs
    · rename_i H' hs
      rcases ih H' with h | h
      · exact .inl h
      · exact .inr (congrArg (· + 1) h)

/-- **Completeness of the hash-map reducer**: if the input has a normal
form, reached in `k` steps by some reduction, and the fuel is at least `k`,
the reducer stops after exactly `k` steps on that normal form. -/
theorem HNet.run_complete {xs : XSys S} {H : HNet S} (hi : H.Inv xs) {k n : Nat} {C : Net S}
    (hC : Steps (CStep xs.sys) k H.toNet C) (hn : Normal (CStep xs.sys) C) (hk : k ≤ n) :
    (H.run xs n).1.step xs = none ∧ (H.run xs n).2 = k ∧ (H.run xs n).1.toNet = C := by
  obtain ⟨sts, hY⟩ := HNet.run_steps hi n
  obtain ⟨hle, rest⟩ := (cstrongConfluent xs.sys).bounded hi.matching.wf hC hn sts
  have stop : (H.run xs n).1.step xs = none := by
    rcases HNet.run_stop_or_full xs H n with h | h
    · exact h
    · have e : k - (H.run xs n).2 = 0 := by omega
      rw [e] at rest
      cases rest
      cases hs : (H.run xs n).1.step xs with
      | none => rfl
      | some H' => exact absurd (HNet.step_sound hY hs).1 (hn _)
  obtain ⟨-, hb⟩ := HNet.run_normal hi n stop
  obtain ⟨e₁, e₂⟩ := (hb hC).2 hn
  exact ⟨stop, e₂.symm, e₁.symm⟩

/-- Load a list net into hash maps.  Every wire between two principal ports
goes on the work list. -/
def HNet.ofXNet (X : XNet S) : HNet S where
  agents := X.agents.foldl (fun m e => m.insert e.1 e.2) ∅
  wires := X.wires.foldl (fun m e => m.insert e.1 e.2) ∅
  free := X.free
  work := principalPairs X.wires

theorem HNet.ofXNet_toNet {ar : S → Nat} {X : XNet S} (hX : X.Ok ar) :
    (HNet.ofXNet X).toNet = X.toNet := by
  have hm := XNet.ok_iff_matching.1 hX
  apply Net.ext'
  · intro i γ
    show (X.agents.foldl (fun m e => m.insert e.1 e.2) (∅ : Std.HashMap Id S))[i]? = some γ ↔
      (i, γ) ∈ X.agents
    rw [hget_foldl_insert _ (fun h h' => hm.agent_fun h h')]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · rw [Std.HashMap.getElem?_empty] at h
        cases h
    · exact fun h => .inl h
  · intro p q
    show (X.wires.foldl (fun m e => m.insert e.1 e.2) (∅ : Std.HashMap Port Port))[p]? = some q ↔
      (p, q) ∈ X.wires
    rw [hget_foldl_insert _ (fun h h' => hm.functional h h')]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · rw [Std.HashMap.getElem?_empty] at h
        cases h
    · exact fun h => .inl h
  · exact fun p => Iff.rfl

/-- A valid input of the list reducer, loaded into hash maps, satisfies the
invariant. -/
theorem HNet.ofXNet_inv {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) :
    (HNet.ofXNet X).Inv xs := by
  have e := HNet.ofXNet_toNet hX
  refine ⟨?_, ?_⟩
  · rw [e]
    exact XNet.ok_iff_matching.1 hX
  · intro c d γ δ R r
    rw [e] at r
    exact .inl (mem_principalPairs (hX.link_iff.2 ⟨r.end_left, r.end_right, r.conn⟩))

/-- **The two reducers agree**: on a valid input, when both have stopped,
the hash-map reducer and the list reducer have reached the same net in the
same number of steps. -/
theorem HNet.run_eq_run {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {n n' : Nat}
    (h : (X.run xs n).1.step xs = none) (h' : ((HNet.ofXNet X).run xs n').1.step xs = none) :
    ((HNet.ofXNet X).run xs n').1.toNet = (X.run xs n).1.toNet ∧
      ((HNet.ofXNet X).run xs n').2 = (X.run xs n).2 := by
  obtain ⟨-, hb⟩ := XNet.run_normal hX n h
  obtain ⟨sts', hi'⟩ := HNet.run_steps (HNet.ofXNet_inv hX) n'
  rw [HNet.ofXNet_toNet hX] at sts'
  exact (hb sts').2 (HNet.step_complete hi' h')

/-- The hash-map reducer stops whenever the list reducer does, given the same
fuel. -/
theorem HNet.run_of_run {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {n : Nat}
    (h : (X.run xs n).1.step xs = none) :
    ((HNet.ofXNet X).run xs n).1.step xs = none ∧
      ((HNet.ofXNet X).run xs n).2 = (X.run xs n).2 ∧
      ((HNet.ofXNet X).run xs n).1.toNet = (X.run xs n).1.toNet := by
  obtain ⟨sts, hY⟩ := XNet.run_steps hX n
  have hn := XNet.step_complete hY h
  rw [← HNet.ofXNet_toNet hX] at sts
  exact HNet.run_complete (HNet.ofXNet_inv hX) sts hn (XNet.run_le xs X n)

/-! ### Counting the loops in the neighbourhood -/

section NbhdLoops

variable {ar : S → Nat} {a b : Id} {α β : S} {R : Rhs S}

theorem Net.link_fire_of_nbhd {x y : Port} (hl : ((N.nbhd a b α β).fire a b R).link x y) :
    (N.fire a b R).link x y :=
  hl.elim (fun h => .inl h.1) (fun h => .inr h)

theorem Net.Matching.end_fire_of_nbhd (hm : N.Matching ar) {x : Port}
    (hE : ((N.nbhd a b α β).fire a b R).End ar x) : (N.fire a b R).End ar x := by
  rcases hE with ⟨hxa, hxb, A, -, hl⟩ | ⟨γ, ⟨⟨e, -⟩ | ⟨e, -⟩, na, nb⟩ | ⟨o, j, e, hl⟩, hk⟩
  · exact (hm.ends (hm.symm hl)).fire hxa hxb
  · exact absurd e na
  · exact absurd e nb
  · exact .inr ⟨γ, .inr ⟨o, j, e, hl⟩, hk⟩

/-- A point that the fired neighbourhood reaches from a port of the pair,
and that is not one of its ends, is a port of the pair. -/
theorem Net.on_of_reach_nbhd (hR : R.WF ar α β) {e x : Port} (he : e.1 = a ∨ e.1 = b)
    (hr : ((N.nbhd a b α β).fire a b R).Reach e x)
    (hx : ¬ ((N.nbhd a b α β).fire a b R).End ar x) : x.1 = a ∨ x.1 = b := by
  rcases hr.last with rfl | ⟨r, hl⟩
  · exact he
  · rcases hl with ⟨hl, ho⟩ | ⟨z, z', hzz, -, rfl⟩
    · by_cases hxa : x.1 = a
      · exact .inl hxa
      by_cases hxb : x.1 = b
      · exact .inr hxb
      · refine absurd (.inl ⟨hxa, hxb, r, ?_, hl⟩) hx
        rcases ho with ho | ho | ho | ho
        · exact .inl ho
        · exact .inr ho
        · exact absurd ho hxa
        · exact absurd ho hxb
    · cases z' with
      | ifc s k =>
        cases s
        · exact .inl rfl
        · exact .inr rfl
      | new o j k =>
        obtain ⟨γ, hγ, hk⟩ := hR.valid (hR.symm hzz)
        exact absurd (.inr ⟨γ, .inr ⟨o, j, rfl, hγ⟩, hk⟩) hx

/-- A chain of segments of the fired net, from a port of the pair, stays in
the fired neighbourhood until it meets one of its ends. -/
theorem Net.reach_nbhd_of_fire (hR : R.WF ar α β) {e x : Port} (he : e.1 = a ∨ e.1 = b)
    (hr : (N.fire a b R).Reach e x) :
    ((N.nbhd a b α β).fire a b R).Reach e x ∨
      ∃ q, ((N.nbhd a b α β).fire a b R).End ar q ∧ ((N.nbhd a b α β).fire a b R).Reach e q := by
  induction hr with
  | refl => exact .inl .refl
  | @tail x x' _ hl ih =>
    rcases ih with ih | ih
    · by_cases hE : ((N.nbhd a b α β).fire a b R).End ar x
      · exact .inr ⟨x, hE, ih⟩
      · have hon := Net.on_of_reach_nbhd hR he ih hE
        rcases hl with hl | hl
        · exact .inl (.tail ih (.inl ⟨hl, hon.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))⟩))
        · exact .inl (.tail ih (.inr hl))
    · exact .inr ih

namespace Site

theorem dead_fire_of_nbhd (h : Site ar N a b α β) (hm : N.Matching ar) (hR : R.WF ar α β)
    {s : Bool} {k : Nat} (hk : k < ar (sel α β s))
    (hd : ((N.nbhd a b α β).fire a b R).Dead ar (sel a b s, k + 1)) :
    (N.fire a b R).Dead ar (sel a b s, k + 1) := by
  obtain ⟨y, hy⟩ := hR.total (x := .ifc s k) hk
  have he : ((sel a b s, k + 1) : Port).1 = a ∨ ((sel a b s, k + 1) : Port).1 = b := by
    cases s
    · exact .inl rfl
    · exact .inr rfl
  refine ⟨⟨emb a b y, .inr ⟨_, _, hy, rfl, rfl⟩⟩, fun q hr hE => ?_⟩
  rcases Net.reach_nbhd_of_fire hR he hr with hr₀ | ⟨q', hq', hr'⟩
  · rcases h.end_fire_local hm hE with hE₀ | ⟨-, hqa, hqb, -⟩
    · exact hd.2 q hr₀ hE₀
    · exact (Net.on_of_reach_nbhd hR he hr₀ (hd.2 q hr₀)).elim hqa hqb
  · exact hd.2 q' hr' hq'

theorem dead_nbhd_of_fire (hm : N.Matching ar) (hR : R.WF ar α β) {s : Bool} {k : Nat}
    (hk : k < ar (sel α β s)) (hd : (N.fire a b R).Dead ar (sel a b s, k + 1)) :
    ((N.nbhd a b α β).fire a b R).Dead ar (sel a b s, k + 1) := by
  obtain ⟨y, hy⟩ := hR.total (x := .ifc s k) hk
  exact ⟨⟨emb a b y, .inr ⟨_, _, hy, rfl, rfl⟩⟩,
    fun q hr hE => hd.2 q (hr.mono Net.link_fire_of_nbhd) (hm.end_fire_of_nbhd hE)⟩

/-- **The loops are closed in the neighbourhood.**  In a net without
history, the loops closed by a firing are those closed by the same firing in
the neighbourhood of the pair. -/
theorem auxCount_of_nbhd (h : Site ar N a b α β) (hm : N.Matching ar) (hR : R.WF ar α β)
    {ℓ : Nat} (hc : AuxCount ar ((N.nbhd a b α β).fire a b R) a b α β ℓ) :
    AuxCount ar (N.fire a b R) a b α β ℓ := by
  obtain ⟨rs, hlen, hmem, hpw, hcov⟩ := hc
  have hon : ∀ {r : Port}, r ∈ auxPorts ar a b α β → r.1 = a ∨ r.1 = b := by
    intro r hr
    obtain ⟨s, k, -, rfl⟩ := mem_auxPorts.1 hr
    cases s
    · exact .inl rfl
    · exact .inr rfl
  refine ⟨rs, hlen, fun r hr => ⟨(hmem r hr).1, ?_⟩, hpw.imp_of_mem ?_, fun e he hd => ?_⟩
  · have hd := (hmem r hr).2
    obtain ⟨s, k, hk, rfl⟩ := mem_auxPorts.1 (hmem r hr).1
    exact h.dead_fire_of_nbhd hm hR hk hd
  · intro p q hp _ hn hreach
    rcases Net.reach_nbhd_of_fire hR (hon (hmem p hp).1) hreach with h₀ | ⟨q', hq', hr'⟩
    · exact hn h₀
    · exact (hmem p hp).2.2 q' hr' hq'
  · obtain ⟨s, k, hk, rfl⟩ := mem_auxPorts.1 he
    obtain ⟨r, hr, hre⟩ := hcov _ he (dead_nbhd_of_fire hm hR hk hd)
    exact ⟨r, hr, hre.mono Net.link_fire_of_nbhd⟩

end Site

end NbhdLoops

/-- Run the hash-map reducer for at most `n` steps, counting the loops it
closes.  The count of a step is taken in the neighbourhood of the pair. -/
def HNet.runLoops (xs : XSys S) : Nat → HNet S → Option (HNet S × Nat × Nat)
  | 0, H => some (H, 0, 0)
  | n + 1, H =>
    match H.next xs H.work with
    | none => some (H, 0, 0)
    | some r =>
      match (H.nbhd xs.sys.ar r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2.1).loopsAt xs.sys.ar r.1.1
          r.1.2.1 r.1.2.2.1 r.1.2.2.2.1 r.1.2.2.2.2 with
      | none => none
      | some ℓ =>
        (HNet.runLoops xs n
          (H.fire xs.sys.ar r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2.1 r.1.2.2.2.2 r.2)).map
          fun t => (t.1, t.2.1 + 1, ℓ + t.2.2)

theorem HNet.runLoops_spec {xs : XSys S} :
    ∀ {n : Nat} {H H' : HNet S} {k L : Nat} {N : Net S} {n₀ : Nat},
      H.Inv xs → N.WF xs.sys.ar → N.compact xs.sys.ar = H.toNet →
      N.DeadCount xs.sys.ar n₀ → H.runLoops xs n = some (H', k, L) →
      H.run xs n = (H', k) ∧ ∃ N', Steps (Step xs.sys) k N N' ∧
        N'.compact xs.sys.ar = H'.toNet ∧ N'.DeadCount xs.sys.ar (n₀ + k + L)
  | 0, H, H', k, L, N, n₀, _, _, hc, hd, h => by
    have e : (H, 0, 0) = (H', k, L) := Option.some.inj h
    obtain ⟨rfl, e'⟩ := Prod.mk.inj e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
    exact ⟨rfl, N, .refl _, hc, hd⟩
  | n + 1, H, H', k, L, N, n₀, hi, hN, hc, hd, h => by
    unfold HNet.runLoops at h
    cases hn : H.next xs H.work with
    | none =>
      rw [hn] at h
      have e : (H, 0, 0) = (H', k, L) := Option.some.inj h
      obtain ⟨rfl, e'⟩ := Prod.mk.inj e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
      have hstep : H.step xs = none := by
        unfold HNet.step
        rw [hn]
        rfl
      refine ⟨?_, N, .refl _, hc, hd⟩
      unfold HNet.run
      rw [hstep]
    | some t =>
      obtain ⟨⟨a, b, α, β, R⟩, rest⟩ := t
      rw [hn] at h
      dsimp only at h
      cases hℓ : (H.nbhd xs.sys.ar a b α β).loopsAt xs.sys.ar a b α β R with
      | none =>
        rw [hℓ] at h
        cases h
      | some ℓ =>
        rw [hℓ] at h
        cases hrec : HNet.runLoops xs n (H.fire xs.sys.ar a b α β R rest) with
        | none =>
          rw [hrec] at h
          cases h
        | some t' =>
          obtain ⟨Y', k', L'⟩ := t'
          rw [hrec] at h
          have e : (Y', k' + 1, ℓ + L') = (H', k, L) := Option.some.inj h
          obtain ⟨rfl, e'⟩ := Prod.mk.inj e
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
          obtain ⟨hro, -⟩ := HNet.next_some hn
          obtain ⟨red, hR⟩ := HNet.redexOf_sound hi.matching hro
          have hstep : H.step xs = some (H.fire xs.sys.ar a b α β R rest) := by
            unfold HNet.step
            rw [hn]
            rfl
          obtain ⟨-, hi'⟩ := HNet.step_sound hi hstep
          obtain ⟨efire, -⟩ := HNet.fire_toNet hi.matching red hR rest
          have hm := hi.matching
          have siteH := red.site hm.wf
          have hRwf := xs.sys.rule_wf red.rule
          -- the count, taken in the neighbourhood
          have e₀ := HNet.nbhd_toNet hm red.ha red.hb
          have hX₀ : (H.nbhd xs.sys.ar a b α β).Ok xs.sys.ar := by
            rw [XNet.ok_iff_matching, e₀]
            exact siteH.nbhd_matching hm
          have site₀ := siteH.nbhd_site hm
          have r₀ : Redex xs.sys (H.nbhd xs.sys.ar a b α β).toNet a b α β R.toRhs := by
            rw [e₀]
            exact ⟨site₀.ha, site₀.hb, site₀.ne, site₀.conn, red.rule⟩
          have hA₀ := XNet.loopsAt_spec hX₀ r₀ hR hℓ
          rw [e₀] at hA₀
          have hA₁ := siteH.auxCount_of_nbhd hm hRwf hA₀
          -- the same step, on the net with history
          have rC : Redex xs.sys (N.compact xs.sys.ar) a b α β R.toRhs := by
            rw [hc]
            exact red
          have rN : Redex xs.sys N a b α β R.toRhs := (Net.compact_obs xs.sys.ar N).symm.redex rC
          have site := rN.site hN
          have hc₁ : (N.fire a b R.toRhs).compact xs.sys.ar =
              (H.fire xs.sys.ar a b α β R rest).toNet := by
            rw [site.compact_fire hRwf, hc, efire]
          have hA : AuxCount xs.sys.ar ((N.compact xs.sys.ar).fire a b R.toRhs) a b α β ℓ := by
            rw [hc]
            exact hA₁
          have hd₁ := site.deadCount_of_auxCount hRwf hd (site.auxCount_of_compact hRwf hA)
          obtain ⟨hrun, N', sts, hc', hd'⟩ :=
            HNet.runLoops_spec hi' (site.fire_wf hRwf) hc₁ hd₁ hrec
          refine ⟨?_, N', .head ⟨a, b, α, β, _, rN, rfl⟩ sts, hc', ?_⟩
          · unfold HNet.run
            rw [hstep]
            dsimp only
            rw [hrun]
          · have e : n₀ + (k' + 1) + (ℓ + L') = n₀ + 1 + ℓ + k' + L' := by omega
            rw [e]
            exact hd'

/-- **The hash-map reducer counts the loops.** -/
theorem HNet.runLoops_loops {xs : XSys S} {X : XNet S} {H' : HNet S} {n k L : Nat}
    (hX : X.Ok xs.sys.ar) (h : (HNet.ofXNet X).runLoops xs n = some (H', k, L)) :
    (HNet.ofXNet X).run xs n = (H', k) ∧ ∃ N', Steps (Step xs.sys) k X.toNet N' ∧
      N'.compact xs.sys.ar = H'.toNet ∧ Loops xs.sys.ar X.toNet k N' L := by
  obtain ⟨h₁, N', sts, hc, hd⟩ := HNet.runLoops_spec (HNet.ofXNet_inv hX) hX.1
    (hX.2.trans (HNet.ofXNet_toNet hX).symm) (Net.WF.deadCount_compact hX.2) h
  exact ⟨h₁, N', sts, hc, 0, Net.WF.deadCount_compact hX.2, hd⟩

/-- When the hash-map reducer has stopped, its count is the number of loops
of every reduction of the input to a normal form.  In particular it is the
count of the list reducer. -/
theorem HNet.runLoops_unique {xs : XSys S} {X : XNet S} {H' : HNet S} {n k L : Nat}
    (hX : X.Ok xs.sys.ar) (h : (HNet.ofXNet X).runLoops xs n = some (H', k, L))
    (hstop : H'.step xs = none) {m L' : Nat} {N₂ : Net S}
    (h₂ : Steps (Step xs.sys) m X.toNet N₂) (hn₂ : Normal (Step xs.sys) N₂)
    (l₂ : Loops xs.sys.ar X.toNet m N₂ L') : m = k ∧ L' = L := by
  obtain ⟨hrun, N', sts, hc, hl⟩ := HNet.runLoops_loops hX h
  have hi' : H'.Inv xs := by
    have := (HNet.run_steps (HNet.ofXNet_inv hX) n).2
    rw [hrun] at this
    exact this
  have hnY := HNet.step_complete hi' hstop
  rw [← hc] at hnY
  have hn' : Normal (Step xs.sys) N' := (normal_compact (Steps.wf hX.1 sts)).2 hnY
  exact ⟨(normal_form_unique hX.1 h₂ sts hn₂ hn').2, loops_unique hX.1 h₂ sts hn₂ hn' l₂ hl⟩

/-- **The hash-map reducer always reports a count.** -/
theorem HNet.runLoops_isSome {xs : XSys S} : ∀ (n : Nat) {H : HNet S}, H.Inv xs →
    ∃ L, H.runLoops xs n = some ((H.run xs n).1, (H.run xs n).2, L)
  | 0, _, _ => ⟨0, rfl⟩
  | n + 1, H, hi => by
    unfold HNet.runLoops HNet.run
    cases hn : H.next xs H.work with
    | none =>
      have hstep : H.step xs = none := by
        unfold HNet.step
        rw [hn]
        rfl
      rw [hstep]
      exact ⟨0, rfl⟩
    | some t =>
      obtain ⟨⟨a, b, α, β, R⟩, rest⟩ := t
      obtain ⟨hro, -⟩ := HNet.next_some hn
      obtain ⟨red, hR⟩ := HNet.redexOf_sound hi.matching hro
      have hstep : H.step xs = some (H.fire xs.sys.ar a b α β R rest) := by
        unfold HNet.step
        rw [hn]
        rfl
      obtain ⟨-, hi'⟩ := HNet.step_sound hi hstep
      have hm := hi.matching
      have siteH := red.site hm.wf
      have e₀ := HNet.nbhd_toNet hm red.ha red.hb
      have hX₀ : (H.nbhd xs.sys.ar a b α β).Ok xs.sys.ar := by
        rw [XNet.ok_iff_matching, e₀]
        exact siteH.nbhd_matching hm
      have site₀ := siteH.nbhd_site hm
      have r₀ : Redex xs.sys (H.nbhd xs.sys.ar a b α β).toNet a b α β R.toRhs := by
        rw [e₀]
        exact ⟨site₀.ha, site₀.hb, site₀.ne, site₀.conn, red.rule⟩
      obtain ⟨ℓ, hℓ⟩ := XNet.loopsAt_isSome hX₀ r₀ hR
      obtain ⟨L', hL'⟩ := HNet.runLoops_isSome n hi'
      rw [hstep]
      dsimp only
      rw [hℓ, hL']
      exact ⟨ℓ + L', rfl⟩

/-! ### The cost of the hash-map reducer

The reducer is written once more, with every operation on a hash map
counted.  The counted reducer computes what the reducer computes, a firing
costs a number of operations that depends on the rule alone, and a run costs
three operations for each pair on the initial work list plus a bounded number
for each step. -/

/-- A value, and the number of hash-map operations spent to compute it. -/
structure Counted (α : Type) where
  val : α
  cost : Nat

section CountedOps

variable {K V : Type} [BEq K] [Hashable K]

/-- Insert the entries of a list: one operation each. -/
def insertAllC (m : Std.HashMap K V) : List (K × V) → Counted (Std.HashMap K V)
  | [] => ⟨m, 0⟩
  | e :: l => ⟨(insertAllC (m.insert e.1 e.2) l).val, (insertAllC (m.insert e.1 e.2) l).cost + 1⟩

theorem insertAllC_val : ∀ (l : List (K × V)) (m : Std.HashMap K V),
    (insertAllC m l).val = l.foldl (fun m e => m.insert e.1 e.2) m
  | [], _ => rfl
  | e :: l, m => insertAllC_val l (m.insert e.1 e.2)

theorem insertAllC_cost : ∀ (l : List (K × V)) (m : Std.HashMap K V),
    (insertAllC m l).cost = l.length
  | [], _ => rfl
  | e :: l, m => congrArg (· + 1) (insertAllC_cost l (m.insert e.1 e.2))

/-- Erase the keys of a list: one operation each. -/
def eraseAllC (m : Std.HashMap K V) : List (K × V) → Counted (Std.HashMap K V)
  | [] => ⟨m, 0⟩
  | e :: l => ⟨(eraseAllC (m.erase e.1) l).val, (eraseAllC (m.erase e.1) l).cost + 1⟩

theorem eraseAllC_val : ∀ (l : List (K × V)) (m : Std.HashMap K V),
    (eraseAllC m l).val = l.foldl (fun m e => m.erase e.1) m
  | [], _ => rfl
  | e :: l, m => eraseAllC_val l (m.erase e.1)

theorem eraseAllC_cost : ∀ (l : List (K × V)) (m : Std.HashMap K V),
    (eraseAllC m l).cost = l.length
  | [], _ => rfl
  | e :: l, m => congrArg (· + 1) (eraseAllC_cost l (m.erase e.1))

/-- Look up the keys of a list: one operation each. -/
def lookupAllC (m : Std.HashMap K V) : List K → Counted (List (K × V))
  | [] => ⟨[], 0⟩
  | k :: l =>
    ⟨(match m[k]? with
      | some v => (k, v) :: (lookupAllC m l).val
      | none => (lookupAllC m l).val), (lookupAllC m l).cost + 1⟩

theorem lookupAllC_val (m : Std.HashMap K V) : ∀ l : List K,
    (lookupAllC m l).val = l.filterMap fun k => (m[k]?).map fun v => (k, v)
  | [] => rfl
  | k :: l => by
    have ih := lookupAllC_val m l
    cases h : m[k]? with
    | none => simp [lookupAllC, h, ih]
    | some v => simp [lookupAllC, h, ih]

theorem lookupAllC_cost (m : Std.HashMap K V) : ∀ l : List K, (lookupAllC m l).cost = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (lookupAllC_cost m l)

end CountedOps

/-- Read the wires at the ports of two agents: one lookup per port. -/
def HNet.nearWiresC (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) :
    Counted (List (Port × Port)) :=
  lookupAllC H.wires (portsOf ar a α ++ portsOf ar b β)

theorem HNet.nearWiresC_val (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) :
    (H.nearWiresC ar a b α β).val = H.nearWires ar a b α β :=
  lookupAllC_val _ _

theorem HNet.nearWiresC_cost (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) :
    (H.nearWiresC ar a b α β).cost = ar α + ar β + 2 := by
  unfold HNet.nearWiresC
  rw [lookupAllC_cost]
  simp [portsOf]
  omega

/-- The neighbourhood, built from the wires read at the ports of the pair. -/
def nbhdOf (a b : Id) (α β : S) (near : List (Port × Port)) : XNet S :=
  ⟨[(a, α), (b, β)],
    near.filterMap fun e => if e.2.1 = a ∨ e.2.1 = b then none else some e.2,
    near ++ near.map fun e => (e.2, e.1)⟩

/-- The firing, counted: one lookup per port of the pair, two erases for
the agents, one insert per new agent, one erase per old wire entry of the
neighbourhood and one insert per new one. -/
def HNet.fireC (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) (R : XRhs S)
    (rest : List (Id × Id)) : Counted (HNet S) :=
  let near := H.nearWiresC ar a b α β
  let X₀ := nbhdOf a b α β near.val
  let X₁ := X₀.fire ar a b α β R
  let ag := insertAllC ((H.agents.erase a).erase b) X₁.agents
  let er := eraseAllC H.wires X₀.wires
  let wi := insertAllC er.val X₁.wires
  ⟨⟨ag.val, wi.val, H.free, principalPairs X₁.wires ++ rest⟩,
    near.cost + 2 + ag.cost + er.cost + wi.cost⟩

theorem HNet.fireC_val (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) (R : XRhs S)
    (rest : List (Id × Id)) : (H.fireC ar a b α β R rest).val = H.fire ar a b α β R rest := by
  unfold HNet.fireC HNet.fire
  simp only [HNet.nearWiresC_val, insertAllC_val, eraseAllC_val]
  rfl

theorem HNet.fireC_cost (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) (R : XRhs S)
    (rest : List (Id × Id)) :
    (H.fireC ar a b α β R rest).cost = ar α + ar β + 2 + 2 +
      ((H.nbhd ar a b α β).fire ar a b α β R).agents.length +
      (H.nbhd ar a b α β).wires.length +
      ((H.nbhd ar a b α β).fire ar a b α β R).wires.length := by
  unfold HNet.fireC
  simp only [HNet.nearWiresC_val, HNet.nearWiresC_cost, insertAllC_cost, eraseAllC_cost]
  rfl

/-! #### What a firing costs -/

theorem spliceAll_length_le {V : Type u} [DecidableEq V] :
    ∀ (ps W : List (V × V)), (spliceAll W ps).length ≤ W.length
  | [], _ => Nat.le_refl _
  | (x, y) :: ps, W =>
    Nat.le_trans (spliceAll_length_le ps (spliceTable W x y)) (List.length_filterMap_le _ _)

/-- Firing adds at most one wire entry per port of a new agent. -/
theorem fireTable_length_le (ar : S → Nat) (W : List (Port × Port)) (a b : Id) (α β : S)
    (R : XRhs S) : (fireTable ar W a b α β R).length ≤ W.length + (R.newPorts ar).length := by
  have h₁ := spliceAll_length_le (R.wiresFrom a b (ifcPorts ar α β) fun y => !y.isNew)
    (retireTable W (a, 0) (b, 0))
  have h₂ : (retireTable W (a, 0) (b, 0)).length ≤ W.length := List.length_filter_le _ _
  have h₃ : (R.wiresFrom a b (R.newPorts ar) LPort.isNew).length ≤ (R.newPorts ar).length :=
    List.length_filterMap_le _ _
  unfold fireTable
  simp only [List.length_append, List.length_map]
  omega

theorem XNet.fire_agents_length_le (ar : S → Nat) (X : XNet S) (a b : Id) (α β : S)
    (R : XRhs S) : (X.fire ar a b α β R).agents.length ≤ X.agents.length + R.slots.length := by
  show (X.agents.filter _ ++ R.slots.filterMap _).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (List.length_filter_le _ _) (List.length_filterMap_le _ _)

theorem HNet.nearWires_length_le (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) :
    (H.nearWires ar a b α β).length ≤ ar α + ar β + 2 := by
  unfold HNet.nearWires
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  simp [portsOf]
  omega

theorem HNet.nbhd_wires_length (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) :
    (H.nbhd ar a b α β).wires.length = 2 * (H.nearWires ar a b α β).length := by
  show (H.nearWires ar a b α β ++ (H.nearWires ar a b α β).map _).length = _
  rw [List.length_append, List.length_map]
  omega

theorem principalPairs_length_le (ws : List (Port × Port)) :
    (principalPairs ws).length ≤ ws.length :=
  List.length_filterMap_le _ _

/-- A bound, in terms of the rule alone, on the hash-map operations of one
firing, plus three for each pair that the firing puts on the work list. -/
def stepBound (ar : S → Nat) (α β : S) (R : XRhs S) : Nat :=
  11 * (ar α + ar β + 2) + R.slots.length + 4 * (R.newPorts ar).length + 4

/-- **A firing costs a number of operations that depends on the rule
alone**, not on the net. -/
theorem HNet.fireC_bound (ar : S → Nat) (H : HNet S) (a b : Id) (α β : S) (R : XRhs S)
    (rest : List (Id × Id)) :
    (H.fireC ar a b α β R rest).cost +
        3 * (principalPairs ((H.nbhd ar a b α β).fire ar a b α β R).wires).length ≤
      stepBound ar α β R := by
  rw [HNet.fireC_cost]
  have h₁ := HNet.nearWires_length_le ar H a b α β
  have h₂ := HNet.nbhd_wires_length ar H a b α β
  have h₃ := XNet.fire_agents_length_le ar (H.nbhd ar a b α β) a b α β R
  have h₄ : ((H.nbhd ar a b α β).fire ar a b α β R).wires.length ≤
      (H.nbhd ar a b α β).wires.length + (R.newPorts ar).length :=
    fireTable_length_le ar _ a b α β R
  have h₅ := principalPairs_length_le ((H.nbhd ar a b α β).fire ar a b α β R).wires
  have h₆ : (H.nbhd ar a b α β).agents.length = 2 := rfl
  unfold stepBound
  omega

theorem HNet.redexOf_rule {xs : XSys S} {H : HNet S} {c d : Id} {γ δ : S} {R : XRhs S}
    (h : H.redexOf xs c d = some (γ, δ, R)) : xs.rule γ δ = some R := by
  unfold HNet.redexOf at h
  cases hc : H.agents[c]? with
  | none =>
    rw [hc] at h
    cases h
  | some γ' =>
    cases hd : H.agents[d]? with
    | none =>
      rw [hc, hd] at h
      cases h
    | some δ' =>
      rw [hc, hd] at h
      dsimp only at h
      split at h
      · cases hr : xs.rule γ' δ' with
        | none =>
          rw [hr] at h
          cases h
        | some R' =>
          rw [hr] at h
          have e : (γ', δ', R') = (γ, δ, R) := Option.some.inj h
          rw [← (Prod.mk.inj e).1, ← (Prod.mk.inj (Prod.mk.inj e).2).1,
            ← (Prod.mk.inj (Prod.mk.inj e).2).2]
          exact hr
      · cases h

/-! #### The counted reducer -/

/-- Find the first active pair of the work list: at most three lookups for
each pair examined. -/
def HNet.nextC (xs : XSys S) (H : HNet S) :
    List (Id × Id) → Counted (Option ((Id × Id × S × S × XRhs S) × List (Id × Id)))
  | [] => ⟨none, 0⟩
  | (c, d) :: w =>
    match H.redexOf xs c d with
    | some t => ⟨some ((c, d, t), w), 3⟩
    | none => ⟨(HNet.nextC xs H w).val, (HNet.nextC xs H w).cost + 3⟩

theorem HNet.nextC_val {xs : XSys S} {H : HNet S} :
    ∀ w : List (Id × Id), (H.nextC xs w).val = H.next xs w
  | [] => rfl
  | (c, d) :: w => by
    unfold HNet.nextC HNet.next
    cases H.redexOf xs c d with
    | some t => rfl
    | none => exact HNet.nextC_val w

theorem HNet.nextC_cost_none {xs : XSys S} {H : HNet S} :
    ∀ {w : List (Id × Id)}, H.next xs w = none → (H.nextC xs w).cost = 3 * w.length
  | [], _ => rfl
  | (c, d) :: w, h => by
    unfold HNet.next at h
    unfold HNet.nextC
    cases hr : H.redexOf xs c d with
    | some t =>
      rw [hr] at h
      cases h
    | none =>
      rw [hr] at h
      have ih := HNet.nextC_cost_none (w := w) h
      show (H.nextC xs w).cost + 3 = 3 * (w.length + 1)
      omega

theorem HNet.nextC_cost_some {xs : XSys S} {H : HNet S} :
    ∀ {w : List (Id × Id)} {t : Id × Id × S × S × XRhs S} {rest : List (Id × Id)},
      H.next xs w = some (t, rest) → (H.nextC xs w).cost + 3 * rest.length = 3 * w.length
  | [], _, _, h => by cases h
  | (c, d) :: w, t, rest, h => by
    unfold HNet.next at h
    unfold HNet.nextC
    cases hr : H.redexOf xs c d with
    | some t' =>
      rw [hr] at h
      have e : ((c, d, t'), w) = (t, rest) := Option.some.inj h
      rw [← (Prod.mk.inj e).2]
      show 3 + 3 * w.length = 3 * (w.length + 1)
      omega
    | none =>
      rw [hr] at h
      have ih := HNet.nextC_cost_some (w := w) h
      show (H.nextC xs w).cost + 3 + 3 * rest.length = 3 * (w.length + 1)
      omega

/-- One step, counted. -/
def HNet.stepC (xs : XSys S) (H : HNet S) : Counted (Option (HNet S)) :=
  match (H.nextC xs H.work).val with
  | none => ⟨none, (H.nextC xs H.work).cost⟩
  | some r =>
    ⟨some (H.fireC xs.sys.ar r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2.1 r.1.2.2.2.2 r.2).val,
      (H.nextC xs H.work).cost +
        (H.fireC xs.sys.ar r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2.1 r.1.2.2.2.2 r.2).cost⟩

theorem HNet.stepC_val (xs : XSys S) (H : HNet S) : (H.stepC xs).val = H.step xs := by
  unfold HNet.stepC HNet.step
  rw [HNet.nextC_val]
  cases H.next xs H.work with
  | none => rfl
  | some r => exact congrArg some (HNet.fireC_val _ _ _ _ _ _ _ _)

theorem HNet.stepC_cost_none {xs : XSys S} {H : HNet S} (h : H.step xs = none) :
    (H.stepC xs).cost = 3 * H.work.length := by
  unfold HNet.step at h
  unfold HNet.stepC
  rw [HNet.nextC_val]
  cases hn : H.next xs H.work with
  | none => exact HNet.nextC_cost_none hn
  | some r =>
    rw [hn] at h
    cases h

/-- A step costs three operations for each pair it takes off the work list,
and a number of operations bounded by the rule. -/
theorem HNet.stepC_cost_some {xs : XSys S} {H H' : HNet S} (h : H.step xs = some H') :
    ∃ α β R, xs.rule α β = some R ∧
      (H.stepC xs).cost + 3 * H'.work.length ≤ 3 * H.work.length + stepBound xs.sys.ar α β R := by
  unfold HNet.step at h
  cases hn : H.next xs H.work with
  | none =>
    rw [hn] at h
    cases h
  | some r =>
    obtain ⟨⟨a, b, α, β, R⟩, rest⟩ := r
    rw [hn] at h
    have eH : H.fire xs.sys.ar a b α β R rest = H' := Option.some.inj h
    subst eH
    refine ⟨α, β, R, HNet.redexOf_rule (HNet.next_some hn).1, ?_⟩
    have hc := HNet.nextC_cost_some hn
    have hf := HNet.fireC_bound xs.sys.ar H a b α β R rest
    have hs : (H.stepC xs).cost =
        (H.nextC xs H.work).cost + (H.fireC xs.sys.ar a b α β R rest).cost := by
      unfold HNet.stepC
      rw [HNet.nextC_val, hn]
    rw [hs]
    show _ + 3 * (principalPairs ((H.nbhd xs.sys.ar a b α β).fire xs.sys.ar a b α β R).wires ++
      rest).length ≤ _
    rw [List.length_append]
    omega

/-- The run, counted. -/
def HNet.runC (xs : XSys S) : Nat → HNet S → Counted (HNet S × Nat)
  | 0, H => ⟨(H, 0), 0⟩
  | n + 1, H =>
    match (H.stepC xs).val with
    | none => ⟨(H, 0), (H.stepC xs).cost⟩
    | some H' =>
      ⟨((HNet.runC xs n H').val.1, (HNet.runC xs n H').val.2 + 1),
        (H.stepC xs).cost + (HNet.runC xs n H').cost⟩

/-- **The counted reducer is the reducer.** -/
theorem HNet.runC_val (xs : XSys S) : ∀ (n : Nat) (H : HNet S), (H.runC xs n).val = H.run xs n
  | 0, _ => rfl
  | n + 1, H => by
    unfold HNet.runC HNet.run
    rw [HNet.stepC_val]
    cases H.step xs with
    | none => rfl
    | some H' =>
      show ((HNet.runC xs n H').val.1, (HNet.runC xs n H').val.2 + 1) = _
      rw [HNet.runC_val xs n H']

/-- **A run costs three operations for each pair on the initial work list,
and a bounded number for each step.**  `C` bounds `stepBound` over the rules
of the system. -/
theorem HNet.runC_cost {xs : XSys S} {C : Nat}
    (hC : ∀ α β R, xs.rule α β = some R → stepBound xs.sys.ar α β R ≤ C) :
    ∀ (n : Nat) (H : HNet S), (H.runC xs n).cost ≤ 3 * H.work.length + C * (H.run xs n).2
  | 0, _ => Nat.zero_le _
  | n + 1, H => by
    unfold HNet.runC HNet.run
    rw [HNet.stepC_val]
    cases hs : H.step xs with
    | none =>
      show (H.stepC xs).cost ≤ 3 * H.work.length + C * 0
      rw [HNet.stepC_cost_none hs]
      omega
    | some H' =>
      obtain ⟨α, β, R, hR, hc⟩ := HNet.stepC_cost_some hs
      have ih := HNet.runC_cost hC n H'
      have hb := hC α β R hR
      show (H.stepC xs).cost + (HNet.runC xs n H').cost ≤
        3 * H.work.length + C * ((HNet.run xs n H').2 + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- The same, for a net loaded from lists. -/
theorem HNet.runC_cost_ofXNet {xs : XSys S} {C : Nat}
    (hC : ∀ α β R, xs.rule α β = some R → stepBound xs.sys.ar α β R ≤ C) (X : XNet S)
    (n : Nat) :
    ((HNet.ofXNet X).runC xs n).cost ≤ 3 * X.wires.length + C * ((HNet.ofXNet X).run xs n).2 := by
  have h₁ := HNet.runC_cost hC n (HNet.ofXNet X)
  have h₂ : (HNet.ofXNet X).work.length ≤ X.wires.length := principalPairs_length_le X.wires
  omega

end INet
