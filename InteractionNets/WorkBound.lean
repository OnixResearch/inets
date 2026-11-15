import InteractionNets.WorkLive

namespace INet

variable {S : Type}

/-! # How many actions the program that rechecks only what a rule touched takes

The measure of `XMach.settles_within` charges every claim a whole pass over
the agents, for the fresh list its thread takes.  Here a thread takes a
fresh list only after a rule that joins interface ports; after any other
claim it puts the agents the rule wrote in front of its list, and checking
them costs the trails of their principal ports.  That is not bounded claim
by claim, but it is over the run: the agents born along a run have
different names, so their trails share no segment (`Net.scan_le`).  So the
measure of a thread carries a reserve, one pass over all the agents that
can be born, from which each claim pays for its children. -/

section WBound

variable [DecidableEq S] {xs : XSys S}

/-- The segments the machine has written and has still to write. -/
def WMach.segs (M : WMach S) : Nat := M.toX.segs

/-- A bound on the agents in memory until the next claim. -/
def WMach.heads (M : WMach S) : Nat := M.toX.heads

/-- An action adds at most `D` segments and `C - 2` agents to what is
written and still to write, and only when it is a claim. -/
theorem WMach.act_sizes {C D : Nat} (hb : xs.Bounded C D) (X : XNet S) (T : WThread S) :
    (WMach.act xs X T).1.wires.length + (WMach.act xs X T).2.1.toX.pendLen ≤
        X.wires.length + T.toX.pendLen + D * (WMach.act xs X T).2.2 ∧
      (WMach.act xs X T).1.agents.length + (WMach.act xs X T).2.1.toX.owes ≤
        X.agents.length + T.toX.owes + (C - 2) * (WMach.act xs X T).2.2 := by
  obtain ⟨todo, s, again⟩ := T
  -- an action that changes neither memory nor what is owed
  have still : ∀ {T₁ : WThread S}, WMach.act xs X ⟨todo, s, again⟩ = (X, T₁, 0) →
      T₁.toX.pendLen = (⟨todo, s, again⟩ : WThread S).toX.pendLen →
      T₁.toX.owes = (⟨todo, s, again⟩ : WThread S).toX.owes →
      (WMach.act xs X ⟨todo, s, again⟩).1.wires.length +
          (WMach.act xs X ⟨todo, s, again⟩).2.1.toX.pendLen ≤
        X.wires.length + (⟨todo, s, again⟩ : WThread S).toX.pendLen +
          D * (WMach.act xs X ⟨todo, s, again⟩).2.2 ∧
      (WMach.act xs X ⟨todo, s, again⟩).1.agents.length +
          (WMach.act xs X ⟨todo, s, again⟩).2.1.toX.owes ≤
        X.agents.length + (⟨todo, s, again⟩ : WThread S).toX.owes +
          (C - 2) * (WMach.act xs X ⟨todo, s, again⟩).2.2 := by
    intro T₁ e h₁ h₂
    rw [e]
    dsimp only
    rw [h₁, h₂]
    omega
  cases s with
  | idle =>
    cases todo with
    | nil => exact still (WMach.act_lift (fun _ _ h => by cases h) rfl) rfl rfl
    | cons e rest =>
      by_cases he : assoc e.1 X.agents = some e.2
      · exact still (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_idle_pos he)) rfl rfl
      · exact still (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_idle_neg he)) rfl rfl
  | look a α =>
    cases hv : assoc (a, 0) X.wires with
    | some q => exact still (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_look hv)) rfl rfl
    | none =>
      exact still (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_look_none hv)) rfl rfl
  | seek a α p c =>
    cases hsc : (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some β' =>
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β').isSome
      · exact still (WMach.act_lift (fun _ _ h => by cases h)
          (XMach.act_seek_found hsc hc)) rfl rfl
      · exact still (WMach.act_lift (fun _ _ h => by cases h)
          (XMach.act_seek_norule hsc hc)) rfl rfl
    | none =>
      cases hns : nextSeg X.wires c p with
      | some q => exact still (WMach.act_lift (fun _ _ h => by cases h)
          (XMach.act_seek_next hsc hns)) rfl rfl
      | none => exact still (WMach.act_lift (fun _ _ h => by cases h)
          (XMach.act_seek_stop hsc hns)) rfl rfl
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [WMach.act_lift (fun _ _ h => by cases h) (XMach.act_ready (todo := todo) (b := b)
        (β := β) ha)]
      have hk := XNet.takeAgent_length (assoc_mem ha)
      show (X.takeAgent a).wires.length + 0 ≤ X.wires.length + 0 + D * 0 ∧
        (X.takeAgent a).agents.length + 1 ≤ X.agents.length + 0 + (C - 2) * 0
      exact ⟨Nat.le_refl _, by omega⟩
    · exact still (WMach.act_lift (fun _ _ h => by cases h) (XMach.act_ready_neg ha)) rfl rfl
  | half a b α β =>
    cases hh : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      rw [WMach.act_half_some (T := ⟨todo, .half a b α β, again⟩) rfl hh]
      have hc : assoc b X.agents = some β ∧ a ≠ b := by
        split at hh
        · rename_i hc
          exact hc
        · cases hh
      have hR : xs.rule α β = some R := by
        rw [ite_pos' hc] at hh
        exact hh
      obtain ⟨hC, hD⟩ := hb α β R hR
      have ha := Nat.le_trans (R.newAgents_length a b) hC
      have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
      have hk := XNet.takeAgent_length (assoc_mem hc.1)
      show (X.takeAgent b).wires.length + (R.newLinks xs.sys.ar a b α β).length ≤
          X.wires.length + 0 + D * 1 ∧
        (X.takeAgent b).agents.length + (R.newAgents a b).length ≤
          X.agents.length + 1 + (C - 2) * 1
      have : (X.takeAgent b).wires.length = X.wires.length := rfl
      omega
    | none =>
      rw [WMach.act_lift (fun _ _ h => by cases h) (XMach.act_half_none (todo := todo) hh)]
      show (X.putAgent a α).wires.length + 0 ≤ X.wires.length + 0 + D * 0 ∧
        (X.putAgent a α).agents.length + 0 ≤ X.agents.length + 1 + (C - 2) * 0
      exact ⟨Nat.le_refl _, by show X.agents.length + 1 + 0 ≤ _; omega⟩
  | write as ls =>
    cases ls with
    | cons e ls =>
      obtain ⟨p, q⟩ := e
      show (X.putLink p q).wires.length + ls.length ≤ X.wires.length + (ls.length + 1) + D * 0 ∧
        (X.putLink p q).agents.length + as.length ≤ X.agents.length + as.length + (C - 2) * 0
      exact ⟨by show X.wires.length + 1 + ls.length ≤ _; omega, Nat.le_refl _⟩
    | nil =>
      cases as with
      | cons e as =>
        obtain ⟨i, γ⟩ := e
        show (X.putAgent i γ).wires.length + 0 ≤ X.wires.length + 0 + D * 0 ∧
          (X.putAgent i γ).agents.length + as.length ≤
            X.agents.length + (as.length + 1) + (C - 2) * 0
        exact ⟨Nat.le_refl _, by show X.agents.length + 1 + as.length ≤ _; omega⟩
      | nil =>
        unfold WMach.act
        dsimp only
        split
        · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- The states after each number of actions under the schedule `σ`, with the
claims so far. -/
def WMach.trace (xs : XSys S) (σ : Nat → Nat) (M : WMach S) : Nat → WMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((WMach.trace xs σ M i).1.step xs (σ i)).1,
      (WMach.trace xs σ M i).2 + ((WMach.trace xs σ M i).1.step xs (σ i)).2)

theorem WMach.trace_run (xs : XSys S) (σ : Nat → Nat) (M : WMach S) :
    ∀ i, MRun xs.sys (M.trace xs σ i).2 M.toMach (M.trace xs σ i).1.toMach
  | 0 => .refl _
  | i + 1 => by
    have ih := WMach.trace_run xs σ M i
    show MRun xs.sys ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2) M.toMach
      ((M.trace xs σ i).1.step xs (σ i)).1.toMach
    rcases WMach.step_sim xs (M.trace xs σ i).1 (σ i) with ⟨e₁, e₂⟩ | hs
    · rw [e₂, e₁, Nat.add_zero]
      exact ih
    · exact ih.trans (.step hs (.refl _))

theorem WMach.trace_live (σ : Nat → Nat) {M : WMach S} (hL : M.Live xs) :
    ∀ i, (M.trace xs σ i).1.Live xs
  | 0 => hL
  | i + 1 => WMach.step_live (WMach.trace_live σ hL i) (σ i)

theorem WMach.step_length (xs : XSys S) (M : WMach S) (t : Nat) :
    (M.step xs t).1.ths.length = M.ths.length := by
  unfold WMach.step
  split
  · exact List.length_set
  · rfl

theorem WMach.trace_length (xs : XSys S) (σ : Nat → Nat) (M : WMach S) :
    ∀ i, (M.trace xs σ i).1.ths.length = M.ths.length
  | 0 => rfl
  | i + 1 => (WMach.step_length xs _ _).trans (WMach.trace_length xs σ M i)

omit [DecidableEq S] in
theorem total_map_set (f : XThread S → Nat) (ths : List (WThread S)) (t : Nat)
    (T T₁ : WThread S) (ht : ths[t]? = some T) :
    total f ((ths.set t T₁).map WThread.toX) + f T.toX =
      total f (ths.map WThread.toX) + f T₁.toX := by
  rw [List.map_set]
  refine total_set f _ t _ _ ?_
  rw [List.getElem?_map, ht]
  rfl

/-- An action adds at most `D` segments and `C - 2` agents, and only when it
is a claim. -/
theorem WMach.step_sizes {C D : Nat} (hb : xs.Bounded C D) (M : WMach S) (t : Nat) :
    (M.step xs t).1.segs ≤ M.segs + D * (M.step xs t).2 ∧
      (M.step xs t).1.heads ≤ M.heads + (C - 2) * (M.step xs t).2 := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold WMach.step
      rw [ht]
    rw [e]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | some T =>
    have e := WMach.step_eq (xs := xs) ht (rfl : WMach.act xs M.mem T =
      ((WMach.act xs M.mem T).1, (WMach.act xs M.mem T).2.1, (WMach.act xs M.mem T).2.2))
    rw [e]
    obtain ⟨h₁, h₂⟩ := WMach.act_sizes hb M.mem T
    have tp := total_map_set XThread.pendLen M.ths t T (WMach.act xs M.mem T).2.1 ht
    have to := total_map_set XThread.owes M.ths t T (WMach.act xs M.mem T).2.1 ht
    constructor
    · show (WMach.act xs M.mem T).1.wires.length +
          total XThread.pendLen ((M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX) ≤
        M.mem.wires.length + total XThread.pendLen (M.ths.map WThread.toX) +
          D * (WMach.act xs M.mem T).2.2
      omega
    · show (WMach.act xs M.mem T).1.agents.length +
          total XThread.owes ((M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX) ≤
        M.mem.agents.length + total XThread.owes (M.ths.map WThread.toX) +
          (C - 2) * (WMach.act xs M.mem T).2.2
      omega

/-- Along a run, every claim adds at most `D` segments and `C - 2` agents. -/
theorem WMach.trace_sizes (σ : Nat → Nat) (M : WMach S) {C D : Nat} (hb : xs.Bounded C D) :
    ∀ i, (M.trace xs σ i).1.segs ≤ M.segs + D * (M.trace xs σ i).2 ∧
      (M.trace xs σ i).1.heads ≤ M.heads + (C - 2) * (M.trace xs σ i).2
  | 0 => ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | i + 1 => by
    obtain ⟨h₁, h₂⟩ := WMach.trace_sizes σ M hb i
    obtain ⟨s₁, s₂⟩ := WMach.step_sizes hb (M.trace xs σ i).1 (σ i)
    show ((M.trace xs σ i).1.step xs (σ i)).1.segs ≤
        M.segs + D * ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2) ∧
      ((M.trace xs σ i).1.step xs (σ i)).1.heads ≤
        M.heads + (C - 2) * ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2)
    rw [Nat.mul_add, Nat.mul_add]
    omega

omit [DecidableEq S] in
theorem WMach.init_heads (X : XNet S) (nt : Nat) :
    (WMach.init X nt).heads = X.agents.length := by
  have h := (XMach.init_sizes X nt).2
  have e : (WMach.init X nt).toX = XMach.init X nt := by
    show WMach.toX ⟨X, _⟩ = ⟨X, _⟩
    unfold WMach.toX
    rw [List.map_map]
    rfl
  unfold WMach.heads
  rw [e]
  exact h

/-- What an action does to the agents in memory. -/
theorem WMach.act_agents (X : XNet S) (T : WThread S) :
    (WMach.act xs X T).1.agents = X.agents ∨
      (∃ a, (WMach.act xs X T).1 = X.takeAgent a) ∨
      (∃ a b α β, T.st = .half a b α β ∧ (WMach.act xs X T).1 = X.putAgent a α) ∨
      ∃ i γ as, T.st = .write ((i, γ) :: as) [] ∧ (WMach.act xs X T).1 = X.putAgent i γ := by
  obtain ⟨todo, s, again⟩ := T
  by_cases hw : ∀ as ls, s ≠ .write as ls
  · rcases WMach.act_agree xs X ⟨todo, s, again⟩ hw with e | ⟨a, b, α, β, R, -, -, e, -⟩
    · rw [e]
      dsimp only
      rcases XMach.act_agents xs X ⟨todo, s⟩ with h | h | ⟨a, b, α, β, hs, h⟩ |
        ⟨i, γ, as, ls, hs, -⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl ⟨a, b, α, β, hs, h⟩))
      · exact absurd hs (hw _ _)
    · rw [e]
      exact .inr (.inl ⟨b, rfl⟩)
  · obtain ⟨as, ls, rfl⟩ : ∃ as ls, s = .write as ls :=
      Classical.byContradiction fun hn => hw fun as ls e => hn ⟨as, ls, e⟩
    cases ls with
    | cons e ls => exact .inl rfl
    | nil =>
      cases as with
      | cons e as =>
        obtain ⟨i, γ⟩ := e
        exact .inr (.inr (.inr ⟨i, γ, as, rfl, rfl⟩))
      | nil =>
        left
        unfold WMach.act
        dsimp only
        split <;> rfl

/-- No agent is in memory twice, if none was at the start. -/
theorem WMach.step_nodup {M : WMach S} (hL : M.Live xs)
    (h : (M.mem.agents.map Prod.fst).Nodup) (t : Nat) :
    ((M.step xs t).1.mem.agents.map Prod.fst).Nodup := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold WMach.step
      rw [ht]
    rw [e]
    exact h
  | some T =>
    have e : (M.step xs t).1.mem = (WMach.act xs M.mem T).1 := by
      unfold WMach.step
      rw [ht]
    rw [e]
    have hok := hL.ok ht
    have fresh : ∀ {i : Id} {γ : S}, (∀ δ, ¬ M.mem.toNet.agent i δ) →
        ((M.mem.putAgent i γ).agents.map Prod.fst).Nodup := by
      intro i γ hi
      show (i :: M.mem.agents.map Prod.fst).Nodup
      refine List.nodup_cons.2 ⟨fun hm => ?_, h⟩
      obtain ⟨e', he', ee⟩ := List.mem_map.1 hm
      have hm' : (i, e'.2) ∈ M.mem.agents := by
        rw [← ee]
        exact he'
      exact hi e'.2 hm'
    rcases WMach.act_agents M.mem T with e₁ | ⟨a, e₁⟩ | ⟨a, b, α, β, es, e₁⟩ |
      ⟨i, γ, as, es, e₁⟩
    · rw [e₁]
      exact h
    · rw [e₁]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) h
    · rw [e₁]
      rw [es] at hok
      exact fresh hok.2
    · rw [e₁]
      refine fresh fun δ hδ => ?_
      have hp : (M.toMach.th t).pendA i γ := by
        show (threadOf (M.ths.map WThread.toX) t).pendA i γ
        rw [threadOf_map_eq ht, es]
        exact List.mem_cons_self
      exact hL.inv.pend_fresh δ hp (.inl hδ)

/-- What a thread still has to do before it is idle with a shorter list or
makes a claim.  A thread about to take a fresh list is charged a pass. -/
noncomputable def potW (H : Net S) (K A : Nat) (T : WThread S) : Nat :=
  match T.st with
  | .write as ls => H.scan K T.todo + (as.length + ls.length + 1) +
      (if T.again then 7 * A + K else 0)
  | _ => potIn H K A T.toX

omit [DecidableEq S] in
theorem potW_of_not_write {H : Net S} {K A : Nat} {T : WThread S}
    (h : ∀ as ls, T.st ≠ .write as ls) : potW H K A T = potIn H K A T.toX := by
  obtain ⟨todo, s, again⟩ := T
  cases s with
  | write as ls => exact absurd rfl (h as ls)
  | _ => rfl

/-- An action of `XMach` claims, or leaves its thread writing, only from a
claim or from writing. -/
theorem XMach.act_claim_or_write (X : XNet S) (T : XThread S)
    (h : (XMach.act xs X T).2.2 ≠ 0 ∨ ∃ as ls, (XMach.act xs X T).2.1.st = .write as ls) :
    (∃ as ls, T.st = .write as ls) ∨
      ∃ a b α β R, T.st = .half a b α β ∧
        (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | write as ls => exact .inl ⟨as, ls, rfl⟩
  | half a b α β =>
    cases hh : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R => exact .inr ⟨a, b, α, β, R, rfl, hh⟩
    | none =>
      rw [XMach.act_half_none hh] at h
      rcases h with h | ⟨as, ls, h⟩
      · exact absurd rfl h
      · cases h
  | idle =>
    exfalso
    cases todo with
    | nil => rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
    | cons e rest =>
      by_cases he : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos he] at h
        rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
      · rw [XMach.act_idle_neg he] at h
        rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
  | look a α =>
    exfalso
    cases hv : assoc (a, 0) X.wires with
    | some q =>
      rw [XMach.act_look hv] at h
      rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
    | none =>
      rw [XMach.act_look_none hv] at h
      rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
  | seek a α p c =>
    exfalso
    cases hsc : (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some β' =>
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β').isSome
      · rw [XMach.act_seek_found hsc hc] at h
        rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
      · rw [XMach.act_seek_norule hsc hc] at h
        rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
    | none =>
      cases hns : nextSeg X.wires c p with
      | some q =>
        rw [XMach.act_seek_next hsc hns] at h
        rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
      | none =>
        rw [XMach.act_seek_stop hsc hns] at h
        rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
  | ready a b α β =>
    exfalso
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready ha] at h
      rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h
    · rw [XMach.act_ready_neg ha] at h
      rcases h with h | ⟨as, ls, h⟩ <;> first | exact absurd rfl h | cases h

/-- The agents a claim writes, if the action is a claim. -/
def WMach.actKids (xs : XSys S) (X : XNet S) (T : WThread S) : List (Id × S) :=
  match T.st with
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R => R.newAgents a b
    | none => []
  | _ => []

/-- Whether the action is a claim of a rule that joins interface ports. -/
def WMach.actJoins (xs : XSys S) (X : XNet S) (T : WThread S) : Bool :=
  match T.st with
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R => R.joins xs.sys.ar α β
    | none => false
  | _ => false

/-- **Every action of a thread is a rest, a claim, or brings its share
down.**  A claim raises the share by the writes of one rule, the trails of
the agents it writes, and a pass if its rule joins interface ports. -/
theorem WMach.act_pot {M : WMach S} (hG : M.toMach.goal.WF xs.sys.ar)
    (hnd : (M.mem.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D)
    {H : Net S} {K A : Nat} (hH : H.Sized K) (hM : M.toX.Ahead H) (hA : M.heads ≤ A)
    {T : WThread S} (hS : T.st.Sane M.toMach.goal) :
    (WMach.act xs M.mem T = (M.mem, T, 0) ∧ T.todo = [] ∧ T.st = .idle) ∨
      ((WMach.act xs M.mem T).2.2 = 1 ∧
        potW H K A (WMach.act xs M.mem T).2.1 ≤ potW H K A T + (C + D) +
          H.scan K (WMach.actKids xs M.mem T) +
          (if WMach.actJoins xs M.mem T then 7 * A + K else 0)) ∨
      ((WMach.act xs M.mem T).2.2 = 0 ∧
        potW H K A (WMach.act xs M.mem T).2.1 < potW H K A T) := by
  obtain ⟨todo, s, again⟩ := T
  by_cases hw : ∀ as ls, s ≠ .write as ls
  · by_cases hcl : ∃ a b α β R, s = .half a b α β ∧
        (if assoc b M.mem.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R
    · obtain ⟨a, b, α, β, R, rfl, hh⟩ := hcl
      refine .inr (.inl ⟨?_, ?_⟩)
      · rw [WMach.act_half_some (T := ⟨todo, .half a b α β, again⟩) rfl hh]
      · have hc : assoc b M.mem.agents = some β ∧ a ≠ b := by
          split at hh
          · rename_i hc
            exact hc
          · cases hh
        have hR : xs.rule α β = some R := by
          rw [ite_pos' hc] at hh
          exact hh
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        rw [WMach.act_half_some (T := ⟨todo, .half a b α β, again⟩) rfl hh]
        have ek : WMach.actKids xs M.mem ⟨todo, .half a b α β, again⟩ = R.newAgents a b := by
          unfold WMach.actKids
          dsimp only
          rw [hh]
        have ej : WMach.actJoins xs M.mem ⟨todo, .half a b α β, again⟩ =
            R.joins xs.sys.ar α β := by
          unfold WMach.actJoins
          dsimp only
          rw [hh]
        rw [ek, ej]
        show H.scan K (R.newAgents a b ++ todo) + ((R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length + 1) +
            (if R.joins xs.sys.ar α β then 7 * A + K else 0) ≤
          (H.scan K todo + 1) + (C + D) + H.scan K (R.newAgents a b) +
            (if R.joins xs.sys.ar α β then 7 * A + K else 0)
        rw [Net.scan_append]
        omega
    · have hnot : ¬ ((∃ as ls, s = .write as ls) ∨ ∃ a b α β R, s = .half a b α β ∧
          (if assoc b M.mem.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R) := by
        rintro (⟨as, ls, e⟩ | h)
        · exact hw as ls e
        · exact hcl h
      have hc0 : (XMach.act xs M.mem ⟨todo, s⟩).2.2 ≠ 1 := fun h =>
        hnot (XMach.act_claim_or_write M.mem ⟨todo, s⟩ (.inl (by omega)))
      have hw0 : ∀ as ls, (XMach.act xs M.mem ⟨todo, s⟩).2.1.st ≠ .write as ls :=
        fun as ls h => hnot (XMach.act_claim_or_write M.mem ⟨todo, s⟩ (.inr ⟨as, ls, h⟩))
      have e : WMach.act xs M.mem ⟨todo, s, again⟩ = ((XMach.act xs M.mem ⟨todo, s⟩).1,
          ⟨(XMach.act xs M.mem ⟨todo, s⟩).2.1.todo, (XMach.act xs M.mem ⟨todo, s⟩).2.1.st,
            again⟩, (XMach.act xs M.mem ⟨todo, s⟩).2.2) := by
        rcases WMach.act_agree xs M.mem ⟨todo, s, again⟩ hw with e | ⟨a, b, α, β, R, hs, hh, -⟩
        · exact e
        · exact absurd ⟨a, b, α, β, R, hs, hh⟩ hcl
      have hp : potW H K A ⟨(XMach.act xs M.mem ⟨todo, s⟩).2.1.todo,
          (XMach.act xs M.mem ⟨todo, s⟩).2.1.st, again⟩ =
          potIn H K A (XMach.act xs M.mem ⟨todo, s⟩).2.1 := potW_of_not_write hw0
      have hp0 : potW H K A ⟨todo, s, again⟩ = potIn H K A ⟨todo, s⟩ := potW_of_not_write hw
      rw [e]
      dsimp only
      rw [hp, hp0]
      rcases XMach.act_pot_of (M := M.toX) hG hnd hb hH hM hA (T := ⟨todo, s⟩) hS with
        ⟨e₁, e₂⟩ | ⟨h1, -⟩ | ⟨h0, hlt⟩
      · refine .inl ⟨?_, ?_, ?_⟩
        · have e₁' : XMach.act xs M.mem ⟨todo, s⟩ = (M.mem, ⟨todo, s⟩, 0) := e₁
          rw [e₁']
        · exact congrArg XThread.todo e₂
        · exact congrArg XThread.st e₂
      · exact absurd h1 hc0
      · exact .inr (.inr ⟨h0, hlt⟩)
  · obtain ⟨as, ls, rfl⟩ : ∃ as ls, s = .write as ls :=
      Classical.byContradiction fun hn => hw fun as ls e => hn ⟨as, ls, e⟩
    refine .inr (.inr ⟨?_, ?_⟩)
    · cases ls with
      | cons e ls => rfl
      | nil =>
        cases as with
        | cons e as => rfl
        | nil =>
          unfold WMach.act
          dsimp only
          split <;> rfl
    · cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show H.scan K todo + (as.length + ls.length + 1) + (if again then 7 * A + K else 0) <
          H.scan K todo + (as.length + (ls.length + 1) + 1) + (if again then 7 * A + K else 0)
        omega
      | nil =>
        cases as with
        | cons e as =>
          obtain ⟨i, γ⟩ := e
          show H.scan K todo + (as.length + 0 + 1) + (if again then 7 * A + K else 0) <
            H.scan K todo + ((as.length + 1) + 0 + 1) + (if again then 7 * A + K else 0)
          omega
        | nil =>
          cases hag : again with
          | true =>
            have hact : WMach.act xs M.mem ⟨todo, .write [] [], true⟩ =
                (M.mem, ⟨M.mem.agents, .idle, false⟩, 0) := rfl
            rw [hact]
            have memG : ∀ {i : Id} {γ : S}, (i, γ) ∈ M.mem.agents →
                M.toMach.goal.agent i γ := fun h => .inl (.inl h)
            have hs := Net.scan_le hH M.mem.agents hnd fun e he q q' h h' =>
              hG.end_unique (.inr ⟨e.2, memG (i := e.1) (γ := e.2) he, Nat.zero_le _⟩)
                (hM.principal (.inl ⟨e.2, memG (i := e.1) (γ := e.2) he⟩) h)
                (hM.principal (.inl ⟨e.2, memG (i := e.1) (γ := e.2) he⟩) h')
            have h1 : M.mem.agents.length ≤ M.heads := Nat.le_add_right _ _
            show H.scan K M.mem.agents < H.scan K todo + (0 + 0 + 1) + (7 * A + K)
            omega
          | false =>
            have hact : WMach.act xs M.mem ⟨todo, .write [] [], false⟩ =
                (M.mem, ⟨todo, .idle, false⟩, 0) := rfl
            rw [hact]
            show H.scan K todo < H.scan K todo + (0 + 0 + 1) + (if false then 7 * A + K else 0)
            omega

/-- The agents written by the action of thread `t`, if it is a claim. -/
def WMach.stepKids (xs : XSys S) (M : WMach S) (t : Nat) : List (Id × S) :=
  match M.ths[t]? with
  | some T => WMach.actKids xs M.mem T
  | none => []

/-- `1` if the action of thread `t` claims by a rule that joins interface
ports. -/
def WMach.stepJoins (xs : XSys S) (M : WMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => if WMach.actJoins xs M.mem T then 1 else 0
  | none => 0

/-- An action that is not a claim writes no agents and joins nothing. -/
theorem WMach.act_zero_kids {X : XNet S} {T : WThread S} (h : (WMach.act xs X T).2.2 = 0) :
    WMach.actKids xs X T = [] ∧ WMach.actJoins xs X T = false := by
  obtain ⟨todo, s, again⟩ := T
  cases s with
  | half a b α β =>
    cases hh : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      rw [WMach.act_half_some (T := ⟨todo, .half a b α β, again⟩) rfl hh] at h
      cases h
    | none =>
      unfold WMach.actKids WMach.actJoins
      dsimp only
      rw [hh]
      exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

/-- An action is a claim only from `half` when the claim succeeds. -/
theorem WMach.act_count (X : XNet S) (T : WThread S) :
    (WMach.act xs X T).2.2 = 0 ∨ ∃ a b α β R, T.st = .half a b α β ∧
      (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R := by
  obtain ⟨todo, s, again⟩ := T
  by_cases hw : ∀ as ls, s ≠ .write as ls
  · rcases WMach.act_agree xs X ⟨todo, s, again⟩ hw with e | ⟨a, b, α, β, R, hs, hh, -⟩
    · rw [e]
      dsimp only
      by_cases h : (XMach.act xs X ⟨todo, s⟩).2.2 = 0
      · exact .inl h
      · rcases XMach.act_claim_or_write X ⟨todo, s⟩ (.inl h) with ⟨as, ls, e⟩ | h
        · exact absurd e (hw as ls)
        · exact .inr h
    · exact .inr ⟨a, b, α, β, R, hs, hh⟩
  · obtain ⟨as, ls, rfl⟩ : ∃ as ls, s = .write as ls :=
      Classical.byContradiction fun hn => hw fun as ls e => hn ⟨as, ls, e⟩
    refine .inl ?_
    cases ls with
    | cons e ls => rfl
    | nil =>
      cases as with
      | cons e as => rfl
      | nil =>
        unfold WMach.act
        dsimp only
        split <;> rfl

/-- **What an action does to the goal**: nothing, or it fires the pair its
thread claims, and the agents it writes are the children of that firing. -/
theorem WMach.step_goal {M : WMach S} (hL : M.Live xs) (t : Nat) :
    ((M.step xs t).2 = 0 ∧ (M.step xs t).1.toMach.goal = M.toMach.goal ∧
        WMach.stepKids xs M t = [] ∧ WMach.stepJoins xs M t = 0) ∨
      ∃ (a b : Id) (α β : S) (R : XRhs S), xs.rule α β = some R ∧ (M.step xs t).2 = 1 ∧
        Redex xs.sys M.toMach.goal a b α β R.toRhs ∧
        (M.step xs t).1.toMach.goal = M.toMach.goal.fire a b R.toRhs ∧
        Writes a b R.toRhs (R.newAgents a b) (R.newLinks xs.sys.ar a b α β) ∧
        WMach.stepKids xs M t = R.newAgents a b ∧
        WMach.stepJoins xs M t = if R.joins xs.sys.ar α β then 1 else 0 := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold WMach.step
      rw [ht]
    refine .inl ⟨by rw [e], by rw [e], ?_, ?_⟩
    · unfold WMach.stepKids
      rw [ht]
    · unfold WMach.stepJoins
      rw [ht]
  | some T =>
    have es := WMach.step_eq (xs := xs) ht (rfl : WMach.act xs M.mem T =
      ((WMach.act xs M.mem T).1, (WMach.act xs M.mem T).2.1, (WMach.act xs M.mem T).2.2))
    rcases WMach.act_count M.mem T with h0 | ⟨a₀, b₀, α₀, β₀, R, hs, hh⟩
    · obtain ⟨k0, j0⟩ := WMach.act_zero_kids h0
      have hc : (M.step xs t).2 = 0 := by
        rw [es]
        exact h0
      refine .inl ⟨hc, ?_, ?_, ?_⟩
      · have h := WMach.step_sim xs M t
        rcases h with ⟨e₁, -⟩ | hs'
        · rw [e₁]
        · rw [hc] at hs'
          exact (MStep.sim hL.inv hs').2.goal_zero rfl
      · unfold WMach.stepKids
        rw [ht]
        exact k0
      · unfold WMach.stepJoins
        rw [ht]
        dsimp only
        rw [j0]
        rfl
    · have hact := WMach.act_half_some (xs := xs) (X := M.mem) hs hh
      have hc : assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ := by
        split at hh
        · rename_i hc
          exact hc
        · cases hh
      have hR : xs.rule α₀ β₀ = some R := by
        rw [ite_pos' hc] at hh
        exact hh
      obtain ⟨hsys, hw⟩ := xs.writes hc.2 hR
      have e : M.toMach.th t = .half a₀ b₀ α₀ β₀ := by
        rw [← hs]
        exact threadOf_map_eq ht
      obtain ⟨rg, eg⟩ := hL.inv.cas₂_goal e (assoc_mem hc.1) hc.2 hsys hw
      have es' := WMach.step_eq ht hact
      have hmx : (M.ths.map WThread.toX)[t]? = some T.toX := by
        rw [List.getElem?_map, ht]
        rfl
      refine .inr ⟨a₀, b₀, α₀, β₀, R, hR, by rw [es'], rg, ?_, hw, ?_, ?_⟩
      · rw [es']
        show Mach.goal ⟨(M.mem.takeAgent b₀).toNet, threadOf ((M.ths.set t _).map WThread.toX)⟩ = _
        rw [List.map_set, threadOf_set hmx, XNet.takeAgent_toNet]
        exact eg
      · unfold WMach.stepKids WMach.actKids
        rw [ht]
        dsimp only
        rw [hs]
        dsimp only
        rw [hh]
      · unfold WMach.stepJoins WMach.actJoins
        rw [ht]
        dsimp only
        rw [hs]
        dsimp only
        simp only [hh]

/-- The agents written so far along a run, by the claims that wrote them. -/
def WMach.born (xs : XSys S) (σ : Nat → Nat) (M : WMach S) : Nat → List (Id × S)
  | 0 => []
  | i + 1 => WMach.born xs σ M i ++ WMach.stepKids xs (M.trace xs σ i).1 (σ i)

/-- The claims so far along a run of rules that join interface ports. -/
def WMach.joined (xs : XSys S) (σ : Nat → Nat) (M : WMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => WMach.joined xs σ M i + WMach.stepJoins xs (M.trace xs σ i).1 (σ i)

/-- **The agents written along a run have different names**, all in use in
the goal, and each has one segment at its principal port in a net ahead of
every goal of the run; a claim writes at most `C` of them. -/
theorem WMach.born_inv {X : XNet S} {nt : Nat} {σ : Nat → Nat} {C D : Nat}
    (hb : xs.Bounded C D) {H : Net S}
    (live : ∀ i, ((WMach.init X nt).trace xs σ i).1.Live xs)
    (ahead : ∀ i, ((WMach.init X nt).trace xs σ i).1.toX.Ahead H) :
    ∀ i, ((WMach.born xs σ (WMach.init X nt) i).map Prod.fst).Nodup ∧
      (∀ e, e ∈ WMach.born xs σ (WMach.init X nt) i →
        ((WMach.init X nt).trace xs σ i).1.toMach.goal.Used e.1) ∧
      (∀ e, e ∈ WMach.born xs σ (WMach.init X nt) i → ∀ q q',
        H.link (e.1, 0) q → H.link (e.1, 0) q' → q = q') ∧
      (WMach.born xs σ (WMach.init X nt) i).length ≤ C * ((WMach.init X nt).trace xs σ i).2
  | 0 => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  | i + 1 => by
    obtain ⟨hnd, hu, hl, hlen⟩ := WMach.born_inv hb live ahead i
    have hsucc : ((WMach.init X nt).trace xs σ (i + 1)) =
        ((((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1,
          ((WMach.init X nt).trace xs σ i).2 +
            (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).2) := rfl
    have hbs : WMach.born xs σ (WMach.init X nt) (i + 1) = WMach.born xs σ (WMach.init X nt) i ++
        WMach.stepKids xs ((WMach.init X nt).trace xs σ i).1 (σ i) := rfl
    have hG' := (live (i + 1)).inv.wf
    have hA' := ahead (i + 1)
    rw [hsucc] at hG' hA'
    rw [hbs, hsucc]
    rcases WMach.step_goal (live i) (σ i) with ⟨h0, eg, ek, -⟩ |
      ⟨a, b, α, β, R, hR, h1, rg, eg, hw, ek, -⟩
    · rw [ek, List.append_nil, h0, Nat.add_zero]
      refine ⟨hnd, fun e he => ?_, hl, hlen⟩
      show (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toMach.goal.Used e.1
      rw [eg]
      exact hu e he
    · have hG := (live i).inv.wf
      have site := rg.site hG
      rw [ek, h1]
      have kid : ∀ e, e ∈ R.newAgents a b →
          (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toMach.goal.agent e.1 e.2 ∧
            ∃ o j, e.1 = child a b o j := by
        intro e he
        obtain ⟨o, j, ei, hlab⟩ := hw.agent.1 he
        refine ⟨?_, o, j, ei⟩
        rw [eg]
        exact .inr ⟨o, j, ei, hlab⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.map_append]
        refine List.nodup_append.2 ⟨hnd, hw.nodup, ?_⟩
        intro x hx y hy hxy
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 hy
        obtain ⟨-, o, j, ej⟩ := kid e' he'
        exact site.not_used_child o j (by rw [← ej, ← hxy]; exact hu e he)
      · intro e he
        rcases List.mem_append.1 he with he | he
        · rw [eg]
          exact site.used_fire_mono R.toRhs (hu e he)
        · exact .inl ⟨e.2, (kid e he).1⟩
      · intro e he q q' h h'
        rcases List.mem_append.1 he with he | he
        · exact hl e he q q' h h'
        · have hag := (kid e he).1
          have hU : (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toMach.goal.Used e.1 :=
            .inl ⟨e.2, hag⟩
          exact hG'.end_unique (.inr ⟨e.2, hag, Nat.zero_le _⟩) (hA'.principal hU h)
            (hA'.principal hU h')
      · rw [List.length_append]
        have hk : (R.newAgents a b).length ≤ C := by
          obtain ⟨hC, -⟩ := hb α β R hR
          exact Nat.le_trans (R.newAgents_length a b) hC
        rw [Nat.mul_add, Nat.mul_one]
        omega

theorem WMach.step_other (M : WMach S) {s t : Nat} (h : s ≠ t) :
    (M.step xs s).1.ths[t]? = M.ths[t]? := by
  unfold WMach.step
  split
  · exact List.getElem?_set_ne h
  · rfl

theorem WMach.rest_act (X : XNet S) (g : Bool) :
    WMach.act xs X ⟨[], .idle, g⟩ = (X, ⟨[], .idle, g⟩, 0) := rfl

/-- A thread at rest stays at rest, whoever acts. -/
theorem WMach.step_rest (M : WMach S) (s : Nat) {t : Nat} {g : Bool}
    (h : M.ths[t]? = some ⟨[], .idle, g⟩) : (M.step xs s).1.ths[t]? = some ⟨[], .idle, g⟩ := by
  by_cases e : s = t
  · subst e
    rw [WMach.step_eq h (WMach.rest_act M.mem g), set_self M.ths s _ h]
    exact h
  · rw [WMach.step_other M e]
    exact h

/-- The share of thread `t`. -/
noncomputable def WMach.potAt (M : WMach S) (H : Net S) (K A t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => potW H K A T
  | none => 0

omit [DecidableEq S] in
theorem WMach.potAt_eq {M : WMach S} {t : Nat} {T : WThread S} (ht : M.ths[t]? = some T)
    (H : Net S) (K A : Nat) : M.potAt H K A t = potW H K A T := by
  unfold WMach.potAt
  rw [ht]

/-- The thread is idle with nothing left to try. -/
def WMach.AtRest (M : WMach S) (t : Nat) : Prop := ∃ g, M.ths[t]? = some ⟨[], .idle, g⟩

/-- **A bound on the length of a fair run of the program that rechecks only
what a rule touched.**  Take a well-formed net with no name twice, whose
normal form is `n` steps away, a system whose rules write at most `C`
agents and `D` segments, and a schedule in which every thread acts in every
window of `F` actions.  If at most `m` of the claims along the run are of
rules that join interface ports, the run is at rest with the normal form
after `F * (B + 1)` actions, where `B` is one pass over the agents at the
start, the writes of each claim, a pass for each claim that joins, and one
pass over all the agents the claims can write. -/
theorem WMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F m : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u)
    (hm : ∀ i, WMach.joined xs σ (WMach.init X nt) i ≤ m) :
    ∀ i, F * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
          m * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)) +
          (7 * (C * n) + (X.wires.length + D * n)) + 1) ≤ i →
      ((WMach.init X nt).trace xs σ i).1.resting = true ∧
      ((WMach.init X nt).trace xs σ i).2 = n ∧
      ((WMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  -- the run and what holds along it
  have live := WMach.trace_live (xs := xs) σ (WMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((WMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((WMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := WMach.trace_run xs σ (WMach.init X nt) i
    rw [WMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((WMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  have len : ∀ i, ((WMach.init X nt).trace xs σ i).1.ths.length = nt := by
    intro i
    rw [WMach.trace_length]
    show ((List.range nt).map _).length = nt
    rw [List.length_map, List.length_range]
  have hA : ∀ i, ((WMach.init X nt).trace xs σ i).1.heads ≤ X.agents.length + (C - 2) * n := by
    intro i
    have h := (WMach.trace_sizes σ (WMach.init X nt) hb i).2
    rw [WMach.init_heads] at h
    exact Nat.le_trans h (Nat.add_le_add_left (Nat.mul_le_mul_left (C - 2) (bound i)) _)
  have nd : ∀ i, (((WMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact WMach.step_nodup (live i) ih (σ i)
  have hH := XNet.normal_sized hX hb hs hn
  have ahead : ∀ i, ((WMach.init X nt).trace xs σ i).1.toX.Ahead N' :=
    fun i => XMach.ahead_of_run (M := ((WMach.init X nt).trace xs σ i).1.toX) (live i).inv hX
      (run i) hs hn
  have born := WMach.born_inv hb live ahead
  -- names for the quantities
  generalize hK : X.wires.length + D * n = K at hH
  generalize hAA : X.agents.length + (C - 2) * n = A at hA
  have hR : ∀ i, N'.scan K (WMach.born xs σ (WMach.init X nt) i) ≤ 7 * (C * n) + K := by
    intro i
    obtain ⟨h₁, -, h₃, h₄⟩ := born i
    have := Net.scan_le hH _ h₁ h₃
    have h5 : C * ((WMach.init X nt).trace xs σ i).2 ≤ C * n :=
      Nat.mul_le_mul_left C (bound i)
    omega
  let Ψ : Nat → Nat → Nat := fun t i =>
    ((WMach.init X nt).trace xs σ i).1.potAt N' K A t +
      (n - ((WMach.init X nt).trace xs σ i).2) * (C + D + 1) +
      (m - WMach.joined xs σ (WMach.init X nt) i) * (7 * A + K) +
      (7 * (C * n) + K - N'.scan K (WMach.born xs σ (WMach.init X nt) i))
  have each : ∀ t, t < nt → ∀ i,
      F * ((7 * X.agents.length + K) + n * (C + D + 1) + m * (7 * A + K) +
        (7 * (C * n) + K) + 1) ≤ i → ((WMach.init X nt).trace xs σ i).1.AtRest t := by
    intro t ht
    have h0 : Ψ t 0 ≤ (7 * X.agents.length + K) + n * (C + D + 1) + m * (7 * A + K) +
        (7 * (C * n) + K) := by
      have hT := WMach.init_thread X ht
      have ep : ((WMach.init X nt).trace xs σ 0).1.potAt N' K A t = N'.scan K X.agents := by
        show (WMach.init X nt).potAt N' K A t = _
        rw [WMach.potAt_eq hT]
        show N'.scan K (X.agents.drop t ++ X.agents.take t) = _
        have e : N'.scan K X.agents = N'.scan K (X.agents.take t) +
            N'.scan K (X.agents.drop t) := by
          rw [← Net.scan_append, List.take_append_drop]
        rw [Net.scan_append, e]
        exact Nat.add_comm _ _
      obtain ⟨-, pr⟩ := Steps.links hX hs
      have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
      have hscan : N'.scan K X.agents ≤ 7 * X.agents.length + K :=
        Net.scan_le hH X.agents hnd fun e he q q' h h' =>
          hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
            (pr (.inl ⟨e.2, hag e he⟩) h')
      show ((WMach.init X nt).trace xs σ 0).1.potAt N' K A t + (n - 0) * (C + D + 1) +
        (m - 0) * (7 * A + K) +
        (7 * (C * n) + K - N'.scan K []) ≤ _
      rw [ep, Nat.sub_zero, Nat.sub_zero]
      have : N'.scan K ([] : List (Id × S)) = 0 := rfl
      omega
    intro i hi
    refine window_settles (Ψ t) (fun i => σ i ≠ t ∨ ((WMach.init X nt).trace xs σ i).1.AtRest t)
      (fun i => ((WMach.init X nt).trace xs σ i).1.AtRest t) F ?_ ?_ ?_ i
      (Nat.le_trans (Nat.mul_le_mul_left F (Nat.succ_le_succ h0)) hi)
    · intro i
      have hsucc : ((WMach.init X nt).trace xs σ (i + 1)) =
          ((((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1,
          ((WMach.init X nt).trace xs σ i).2 +
            (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).2) := rfl
      have hbs : WMach.born xs σ (WMach.init X nt) (i + 1) =
          WMach.born xs σ (WMach.init X nt) i ++
            WMach.stepKids xs ((WMach.init X nt).trace xs σ i).1 (σ i) := rfl
      have hjs : WMach.joined xs σ (WMach.init X nt) (i + 1) =
          WMach.joined xs σ (WMach.init X nt) i +
            WMach.stepJoins xs ((WMach.init X nt).trace xs σ i).1 (σ i) := rfl
      have hb1 := bound (i + 1)
      have hm1 := hm (i + 1)
      have hR1 := hR (i + 1)
      rw [hsucc] at hb1
      rw [hjs] at hm1
      rw [hbs] at hR1
      dsimp only at hb1
      rw [Net.scan_append] at hR1
      show (_ ∧ Ψ t (i + 1) = Ψ t i) ∨ Ψ t (i + 1) < Ψ t i
      simp only [Ψ]
      rw [hbs, hjs, Net.scan_append, hsucc]
      dsimp only
      have hlt : t < ((WMach.init X nt).trace xs σ i).1.ths.length := by
        rw [len i]
        exact ht
      obtain ⟨T, hT⟩ : ∃ T, ((WMach.init X nt).trace xs σ i).1.ths[t]? = some T :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      by_cases hst : σ i = t
      · rw [hst] at hb1 hm1 hR1 ⊢
        have es := WMach.step_eq (xs := xs) hT
          (rfl : WMach.act xs ((WMach.init X nt).trace xs σ i).1.mem T =
          ((WMach.act xs ((WMach.init X nt).trace xs σ i).1.mem T).1,
            (WMach.act xs ((WMach.init X nt).trace xs σ i).1.mem T).2.1,
            (WMach.act xs ((WMach.init X nt).trace xs σ i).1.mem T).2.2))
        have hk : WMach.stepKids xs ((WMach.init X nt).trace xs σ i).1 t =
            WMach.actKids xs ((WMach.init X nt).trace xs σ i).1.mem T := by
          unfold WMach.stepKids
          rw [hT]
        have hj : WMach.stepJoins xs ((WMach.init X nt).trace xs σ i).1 t =
            if WMach.actJoins xs ((WMach.init X nt).trace xs σ i).1.mem T then 1 else 0 := by
          unfold WMach.stepJoins
          rw [hT]
        have hp1 : (((WMach.init X nt).trace xs σ i).1.step xs t).1.potAt N' K A t =
            potW N' K A (WMach.act xs ((WMach.init X nt).trace xs σ i).1.mem T).2.1 := by
          rw [es]
          exact WMach.potAt_eq (List.getElem?_set_self hlt) N' K A
        have hc2 : (((WMach.init X nt).trace xs σ i).1.step xs t).2 =
            (WMach.act xs ((WMach.init X nt).trace xs σ i).1.mem T).2.2 :=
          congrArg Prod.snd es
        rw [hk, hj, hp1, hc2, WMach.potAt_eq hT]
        rw [hc2] at hb1
        rw [hj] at hm1
        rw [hk] at hR1
        rcases WMach.act_pot (live i).inv.wf (nd i) hb hH (ahead i) (hA i)
            ((live i).sane t T hT) with ⟨e, hto, hsto⟩ | ⟨h1, hle⟩ | ⟨h0', hlt'⟩
        · obtain ⟨todo, st, g⟩ := T
          dsimp only at hto hsto
          subst hto hsto
          refine .inl ⟨.inr ⟨g, hT⟩, ?_⟩
          rw [e]
          have k0 := WMach.act_zero_kids (xs := xs) (X := ((WMach.init X nt).trace xs σ i).1.mem)
            (T := ⟨[], .idle, g⟩) rfl
          rw [k0.1, k0.2]
          rfl
        · refine .inr ?_
          rw [h1]
          rw [h1] at hb1
          cases hJ : WMach.actJoins xs ((WMach.init X nt).trace xs σ i).1.mem T with
          | true =>
            rw [hJ] at hle hm1
            simp only [ite_true] at hle hm1 ⊢
            have e1 : n - ((WMach.init X nt).trace xs σ i).2 =
                (n - (((WMach.init X nt).trace xs σ i).2 + 1)) + 1 := by omega
            have e2 : m - WMach.joined xs σ (WMach.init X nt) i =
                (m - (WMach.joined xs σ (WMach.init X nt) i + 1)) + 1 := by omega
            rw [e1, e2, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
            omega
          | false =>
            rw [hJ] at hle hm1
            simp only [Bool.false_eq_true, ite_false] at hle hm1 ⊢
            have e1 : n - ((WMach.init X nt).trace xs σ i).2 =
                (n - (((WMach.init X nt).trace xs σ i).2 + 1)) + 1 := by omega
            rw [e1, Nat.add_mul, Nat.one_mul]
            simp only [Nat.add_zero] at hle ⊢
            omega
        · refine .inr ?_
          obtain ⟨k0, j0⟩ := WMach.act_zero_kids h0'
          rw [h0', k0, j0]
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          have : N'.scan K ([] : List (Id × S)) = 0 := rfl
          omega
      · have hpo : (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1.potAt N' K A t =
            ((WMach.init X nt).trace xs σ i).1.potAt N' K A t := by
          unfold WMach.potAt
          rw [WMach.step_other _ hst]
        rw [hpo]
        rcases WMach.step_goal (live i) (σ i) with ⟨h0', -, k0, j0⟩ |
            ⟨a, b, α, β, R, -, h1, -⟩
        · refine .inl ⟨.inl hst, ?_⟩
          rw [h0', k0, j0]
          simp only [Nat.add_zero]
          have : N'.scan K ([] : List (Id × S)) = 0 := rfl
          omega
        · refine .inr ?_
          rw [h1] at hb1 ⊢
          have e1 : n - ((WMach.init X nt).trace xs σ i).2 =
              (n - (((WMach.init X nt).trace xs σ i).2 + 1)) + 1 := by omega
          rw [e1, Nat.add_mul, Nat.one_mul]
          have hj2 : m - (WMach.joined xs σ (WMach.init X nt) i +
              WMach.stepJoins xs ((WMach.init X nt).trace xs σ i).1 (σ i)) ≤
                m - WMach.joined xs σ (WMach.init X nt) i :=
            by omega
          have hj3 := Nat.mul_le_mul_right (7 * A + K) hj2
          omega
    · intro i hall
      have same : ∀ d, d ≤ F → ((WMach.init X nt).trace xs σ (i + d)).1.ths[t]? =
          ((WMach.init X nt).trace xs σ i).1.ths[t]? := by
        intro d
        induction d with
        | zero => exact fun _ => rfl
        | succ d ih =>
          intro hd
          have ih' := ih (by omega)
          show (((WMach.init X nt).trace xs σ (i + d)).1.step xs (σ (i + d))).1.ths[t]? =
            ((WMach.init X nt).trace xs σ i).1.ths[t]?
          rcases hall (i + d) (by omega) (by omega) with hne | ⟨g, hr⟩
          · rw [WMach.step_other _ hne]
            exact ih'
          · rw [WMach.step_rest _ _ hr, ← ih', hr]
      obtain ⟨j, hj₁, hj₂, hju⟩ := hfair t ht i
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
      rcases hall (i + d) hj₁ hj₂ with hne | ⟨g, hr⟩
      · exact absurd hju hne
      · exact ⟨g, by rw [← same d (by omega)]; exact hr⟩
    · intro i ⟨g, h⟩
      exact ⟨g, WMach.step_rest _ _ h⟩
  intro i hi
  have hrest : ((WMach.init X nt).trace xs σ i).1.resting = true := by
    refine List.all_eq_true.2 fun T hT => ?_
    obtain ⟨u, hu⟩ := List.getElem?_of_mem hT
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hu
    rw [len i] at hlt
    obtain ⟨g, h⟩ := each u hlt i hi
    rw [hu] at h
    rw [Option.some.inj h]
    rfl
  obtain ⟨hq, hnorm⟩ := (live i).rest hrest
  obtain ⟨-, hu⟩ := (run i).final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨hrest, e₂.symm, e₁.symm⟩

/-- No rule of the system wires two of its interface ports together. -/
def XSys.NoJoins (xs : XSys S) : Prop :=
  ∀ α β R, xs.rule α β = some R → R.joins xs.sys.ar α β = false

/-- In a system none of whose rules joins interface ports, no claim does. -/
theorem WMach.joined_zero (hj : xs.NoJoins) (σ : Nat → Nat) (M : WMach S) :
    ∀ i, WMach.joined xs σ M i = 0
  | 0 => rfl
  | i + 1 => by
    show WMach.joined xs σ M i + WMach.stepJoins xs (M.trace xs σ i).1 (σ i) = 0
    rw [WMach.joined_zero hj σ M i, Nat.zero_add]
    unfold WMach.stepJoins
    split
    · rename_i T _
      rcases WMach.act_count (xs := xs) (M.trace xs σ i).1.mem T with h0 | ⟨a, b, α, β, R, hs, hh⟩
      · rw [(WMach.act_zero_kids h0).2]
        rfl
      · have hc : assoc b (M.trace xs σ i).1.mem.agents = some β ∧ a ≠ b := by
          split at hh
          · rename_i hc
            exact hc
          · cases hh
        have hR : xs.rule α β = some R := by
          rw [ite_pos' hc] at hh
          exact hh
        have ej : WMach.actJoins xs (M.trace xs σ i).1.mem T = R.joins xs.sys.ar α β := by
          unfold WMach.actJoins
          rw [hs]
          dsimp only
          rw [hh]
        rw [ej, hj α β R hR]
        rfl
    · rfl

/-- Claims that join interface ports are claims. -/
theorem WMach.joined_le (σ : Nat → Nat) (M : WMach S) :
    ∀ i, WMach.joined xs σ M i ≤ (M.trace xs σ i).2
  | 0 => Nat.le_refl _
  | i + 1 => by
    show WMach.joined xs σ M i + WMach.stepJoins xs (M.trace xs σ i).1 (σ i) ≤
      (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2
    have ih := WMach.joined_le σ M i
    have h : WMach.stepJoins xs (M.trace xs σ i).1 (σ i) ≤
        ((M.trace xs σ i).1.step xs (σ i)).2 := by
      unfold WMach.stepJoins
      split
      · rename_i T ht
        rcases WMach.act_count (xs := xs) (M.trace xs σ i).1.mem T with h0 | ⟨a, b, α, β, R, hs, hh⟩
        · rw [(WMach.act_zero_kids h0).2]
          exact Nat.zero_le _
        · have e := WMach.step_eq (xs := xs) ht (WMach.act_half_some hs hh)
          rw [e]
          have h1 : (if WMach.actJoins xs (M.trace xs σ i).1.mem T then 1 else 0) ≤ 1 := by
            split <;> omega
          exact h1
      · exact Nat.zero_le _
    omega

/-- **A bound linear in the steps, for systems whose rules join no
interface ports**: a fair run is at rest with the normal form after
`F * (B + 1)` actions, where `B` is two passes over the start and the writes
of each claim with seven actions for each agent it writes.  No trail
length enters: the agents written along the run have different names, so
their trails share no segment. -/
theorem WMach.fair_bound_nojoin {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) (hj : xs.NoJoins) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    {F : Nat} (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * (7 * X.agents.length + 2 * (X.wires.length + D * n) +
          n * (8 * C + D + 1) + 1) ≤ i →
      ((WMach.init X nt).trace xs σ i).1.resting = true ∧
      ((WMach.init X nt).trace xs σ i).2 = n ∧
      ((WMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  intro i hi
  refine WMach.fair_bound hX hnd hnt hb hs hn σ (m := 0) hfair
    (fun i => Nat.le_of_eq (WMach.joined_zero hj σ _ i)) i (Nat.le_trans ?_ hi)
  apply Nat.mul_le_mul_left
  have h1 : n * (8 * C + D + 1) = 8 * (C * n) + D * n + n := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_comm n C,
      Nat.mul_comm n D]
  have h2 : n * (C + D + 1) = C * n + D * n + n := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm n C, Nat.mul_comm n D]
  rw [Nat.zero_mul, h1, h2]
  omega

/-- **Never worse in shape than the program that always rescans**: at most
every claim joins, so the run is at rest with the normal form after `F`
times one pass, the writes of each claim, a pass for each claim, and one
pass over all the agents the claims can write. -/
theorem WMach.fair_bound_all {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
          n * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)) +
          (7 * (C * n) + (X.wires.length + D * n)) + 1) ≤ i →
      ((WMach.init X nt).trace xs σ i).1.resting = true ∧
      ((WMach.init X nt).trace xs σ i).2 = n ∧
      ((WMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  have run : ∀ i, MRun xs.sys ((WMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((WMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := WMach.trace_run xs σ (WMach.init X nt) i
    rw [WMach.init_toMach] at h
    exact h
  exact WMach.fair_bound hX hnd hnt hb hs hn σ hfair
    fun i => Nat.le_trans (WMach.joined_le σ _ i) ((run i).claims_le hX hs hn)

end WBound

end INet
