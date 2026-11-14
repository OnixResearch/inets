import InteractionNets.Names

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### The size of the numbers

The counts take a number as one unit.  The numbered program gives numbers
that grow with the run, so here they are bounded: the counter, every cell
of every name, and the stamps stay below bounds fixed before the run.  The
count is then that of a machine whose words have a size known in
advance. -/

section NumberSizes

variable [DecidableEq S] {xs : XSys S}

/-- **No rule needs more than `Sp` numbers for its new agents.** -/
def XSys.SpanLe (xs : XSys S) (Sp : Nat) : Prop :=
  ∀ α β R, xs.rule α β = some R → R.span ≤ Sp

/-- An action moves the counter forward, by `Sp` at most, and only when it
claims. -/
theorem YMach.act_cnt (xs : XSys S) {Sp : Nat} (hsp : xs.SpanLe Sp) (X : XNet S) (cnt : Nat)
    (T : XThread S) :
    cnt ≤ (YMach.act xs X cnt T).2.2.2 ∧
      (YMach.act xs X cnt T).2.2.2 ≤ cnt + Sp * (YMach.act xs X cnt T).2.2.1 := by
  rcases XMach.act_zero_or_claim xs X T with h0 | ⟨a, b, α, β, R, hst, hR⟩
  · rw [YMach.act_zero cnt h0]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨todo, st⟩ := T
    have hst' : st = .half a b α β := hst
    subst hst'
    have hc : assoc b X.agents = some β ∧ a ≠ b := by
      by_cases c : assoc b X.agents = some β ∧ a ≠ b
      · exact c
      · rw [ite_neg' c] at hR
        cases hR
    have hr : xs.rule α β = some R := by
      rw [ite_pos' hc] at hR
      exact hR
    have hspan := hsp α β R hr
    rw [YMach.act_claim cnt hR]
    show cnt ≤ cnt + R.span ∧ cnt + R.span ≤ cnt + Sp * 1
    omega

theorem YMach.step_eq {Y : YMach S} {t : Nat} {T : XThread S} (hT : Y.ths[t]? = some T) :
    Y.step xs t =
      (⟨(YMach.act xs Y.mem Y.cnt T).1, Y.ths.set t (YMach.act xs Y.mem Y.cnt T).2.1,
        (YMach.act xs Y.mem Y.cnt T).2.2.2⟩, (YMach.act xs Y.mem Y.cnt T).2.2.1) := by
  unfold YMach.step
  rw [hT] <;> rfl

theorem YMach.step_none {Y : YMach S} {t : Nat} (hT : Y.ths[t]? = none) :
    Y.step xs t = (Y, 0) := by
  unfold YMach.step
  rw [hT]

theorem YMach.step_cnt (xs : XSys S) {Sp : Nat} (hsp : xs.SpanLe Sp) (Y : YMach S) (t : Nat) :
    Y.cnt ≤ (Y.step xs t).1.cnt ∧ (Y.step xs t).1.cnt ≤ Y.cnt + Sp * (Y.step xs t).2 := by
  cases hT : Y.ths[t]? with
  | none =>
    rw [YMach.step_none hT]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | some T =>
    rw [YMach.step_eq hT]
    exact YMach.act_cnt xs hsp Y.mem Y.cnt T

/-- **The counter moves by `Sp` at most for each claim.** -/
theorem YMach.trace_cnt {Sp : Nat} (hsp : xs.SpanLe Sp) (σ : Nat → Nat) (Y : YMach S) :
    ∀ i, Y.cnt ≤ (Y.trace xs σ i).1.cnt ∧
      (Y.trace xs σ i).1.cnt ≤ Y.cnt + Sp * (Y.trace xs σ i).2
  | 0 => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | i + 1 => by
    obtain ⟨a, b⟩ := YMach.trace_cnt hsp σ Y i
    obtain ⟨c, d⟩ := YMach.step_cnt xs hsp (Y.trace xs σ i).1 (σ i)
    show Y.cnt ≤ ((Y.trace xs σ i).1.step xs (σ i)).1.cnt ∧
      ((Y.trace xs σ i).1.step xs (σ i)).1.cnt ≤
        Y.cnt + Sp * ((Y.trace xs σ i).2 + ((Y.trace xs σ i).1.step xs (σ i)).2)
    rw [Nat.mul_add]
    omega

/-- **The counter stays below a bound fixed before the run.**  From a net
that reaches its normal form in `n` steps, whatever the schedule, it never
passes the number it started from by more than `Sp * n`. -/
theorem YMach.cnt_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {Sp : Nat} (hsp : xs.SpanLe Sp)
    {nt : Nat} (hnt : 0 < nt) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    ((YMach.init X nt).trace xs σ i).1.cnt ≤ X.top + Sp * n := by
  have run : MRun xs.sys ((XMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((XMach.init X nt).trace xs σ i).1.toMach := by
    have h := XMach.trace_run xs σ (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ((XMach.init X nt).trace xs σ i).2 ≤ n := run.claims_le hX hs hn
  obtain ⟨g, -, hc⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
  have h := (YMach.trace_cnt hsp σ (YMach.init X nt) i).2
  rw [hc] at h
  have hm := Nat.mul_le_mul_left Sp bound
  have h' : ((YMach.init X nt).trace xs σ i).1.cnt ≤
      X.top + Sp * ((XMach.init X nt).trace xs σ i).2 := h
  omega

/-- **What holds of the names and of the numbers an action gives holds of
every name after it.** -/
theorem YMach.step_all (xs : XSys S) {Q : Id → Prop} {Y : YMach S} (h : Y.toX.All Q) (t : Nat)
    (hQ : ∀ k, Y.cnt ≤ k → k < (Y.step xs t).1.cnt → Q [k]) : (Y.step xs t).1.toX.All Q := by
  cases hT : Y.ths[t]? with
  | none =>
    rw [YMach.step_none hT]
    exact h
  | some T =>
    have hTm : T ∈ Y.ths := List.mem_of_getElem? hT
    rcases XMach.act_zero_or_claim xs Y.mem T with h0 | ⟨a, b, α, β, R, hst, hR⟩
    · obtain ⟨b1, b2⟩ := XMach.act_all xs h.1 (h.2 T hTm)
      rw [YMach.step_eq hT, YMach.act_zero Y.cnt h0]
      refine ⟨b1, fun T' hT' => ?_⟩
      have hT'' : T' ∈ Y.ths.set t (XMach.act xs Y.mem T).2.1 := hT'
      rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
      · exact h.2 T' hm
      · exact b2 h0
    · obtain ⟨todo, st⟩ := T
      have hst' : st = .half a b α β := hst
      subst hst'
      have hc : assoc b Y.mem.agents = some β ∧ a ≠ b := by
        by_cases c : assoc b Y.mem.agents = some β ∧ a ≠ b
        · exact c
        · rw [ite_neg' c] at hR
          cases hR
      have hr : xs.rule α β = some R := by
        rw [ite_pos' hc] at hR
        exact hR
      have hT0 : (∀ e ∈ todo, Q e.1) ∧ ∀ i, (TState.half a b α β).Mentions i → Q i :=
        h.2 _ hTm
      have hQa : Q a := hT0.2 a (.inl rfl)
      have hQb : Q b := hT0.2 b (.inr rfl)
      rw [YMach.step_eq hT, YMach.act_claim Y.cnt hR] at hQ
      rw [YMach.step_eq hT, YMach.act_claim Y.cnt hR]
      have hQn : ∀ o j, (o, j) ∈ R.slots → Q (numName Y.cnt o j) := by
        intro o j hsl
        have hlt := R.lt_span hsl
        exact hQ _ (Nat.le_add_right _ _)
          (by show Y.cnt + (3 * j + ocode o) < Y.cnt + R.span; omega)
      refine ⟨h.1.take b, fun T' hT' => ?_⟩
      have hT'' : T' ∈ Y.ths.set t ⟨todo, .write (R.numAgents Y.cnt)
          (R.numLinks xs.sys.ar a b Y.cnt α β)⟩ := hT'
      rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
      · exact h.2 T' hm
      · refine ⟨hT0.1, fun i hi => ?_⟩
        have hi' : (∃ e ∈ R.numAgents Y.cnt, e.1 = i) ∨
            ∃ e ∈ R.numLinks xs.sys.ar a b Y.cnt α β, e.1.1 = i ∨ e.2.1 = i := hi
        rcases hi' with ⟨e, he, e'⟩ | ⟨e, he, e'⟩
        · obtain ⟨o, j, hsl, en⟩ := R.numAgents_name Y.cnt he
          rw [← e', en]
          exact hQn o j hsl
        · obtain ⟨n1, n2⟩ := xs.numLinks_name hr a b Y.cnt he
          rcases e' with e' | e'
          · rw [← e']
            rcases n1 with n | n | ⟨o, j, hsl, en⟩
            · rw [n]
              exact hQa
            · rw [n]
              exact hQb
            · rw [en]
              exact hQn o j hsl
          · rw [← e']
            rcases n2 with n | n | ⟨o, j, hsl, en⟩
            · rw [n]
              exact hQa
            · rw [n]
              exact hQb
            · rw [en]
              exact hQn o j hsl

omit [DecidableEq S] in
/-- Every cell of every name of a memory is below its top. -/
theorem XNet.cell_lt_top {X : XNet S} {j : Id} (hj : j ∈ X.names) {k : Nat} (hk : k ∈ j) :
    k < X.top :=
  le_foldr_max _ _ (List.mem_map.2 ⟨k, List.mem_flatten.2 ⟨j, hj, hk⟩, rfl⟩)

/-- **Every number in a name stays below a bound fixed before the run.**
At every moment of every run of the numbered program, every cell of every
name of an agent, on a segment, or in the list or the hand of a thread is
below `X.top + Sp * n`. -/
theorem YMach.cells_lt {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {Sp : Nat}
    (hsp : xs.SpanLe Sp) {nt : Nat} (hnt : 0 < nt) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, ((YMach.init X nt).trace xs σ i).1.toX.All (fun j => ∀ k ∈ j, k < X.top + Sp * n)
  | 0 => by
    have hA : ∀ e ∈ X.agents, ∀ k ∈ e.1, k < X.top + Sp * n := fun e he k hk =>
      Nat.lt_of_lt_of_le
        (XNet.cell_lt_top (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map.2 ⟨e, he, rfl⟩)))) hk)
        (Nat.le_add_right _ _)
    refine ⟨⟨hA, fun e he => ⟨fun k hk => ?_, fun k hk => ?_⟩⟩, fun T hT => ?_⟩
    · exact Nat.lt_of_lt_of_le
        (XNet.cell_lt_top (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩)))) hk)
        (Nat.le_add_right _ _)
    · exact Nat.lt_of_lt_of_le
        (XNet.cell_lt_top (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩))) hk)
        (Nat.le_add_right _ _)
    · have hT' : T ∈ (List.range nt).map fun t =>
          (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S) := hT
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hT'
      refine ⟨fun e he => ?_, fun i hi => absurd hi id⟩
      have he' : e ∈ X.agents.drop u ++ X.agents.take u := he
      rcases List.mem_append.1 he' with h | h
      · exact hA e (List.mem_of_mem_drop h)
      · exact hA e (List.mem_of_mem_take h)
  | i + 1 => by
    have ih := YMach.cells_lt hX hsp hnt hs hn σ i
    have hc := YMach.cnt_le hX hsp hnt hs hn σ (i + 1)
    refine YMach.step_all xs ih (σ i) (fun k _ hk k' hk' => ?_)
    have e : k' = k := List.mem_singleton.1 hk'
    rw [e]
    exact Nat.lt_of_lt_of_le hk hc

end NumberSizes

section NumberSizesOrdered

variable [DecidableEq S] {xs : XSys S}

omit [DecidableEq S] in
theorem OMem.take_stamp (O : OMem S) (a : Id) : (O.take a).stamp = O.stamp := by
  unfold OMem.take
  split <;> rfl

/-- **An action gives one stamp at most, and none when the thread
rests.** -/
theorem OMach.act_stamp (xs : XSys S) (O : OMem S) (T : TThread S) :
    O.stamp ≤ (OMach.act xs O T).1.stamp ∧
      (OMach.act xs O T).1.stamp ≤ O.stamp + T.toX.busy := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold OMach.act
    dsimp only
    repeat' split
    all_goals exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | look a α =>
    unfold OMach.act
    dsimp only
    repeat' split
    all_goals exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | seek a α p c =>
    unfold OMach.act
    dsimp only
    repeat' split
    all_goals exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | ready a b α β =>
    unfold OMach.act
    dsimp only
    split
    · show O.stamp ≤ (O.take a).stamp ∧ (O.take a).stamp ≤ O.stamp + 1
      rw [OMem.take_stamp]
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
    · exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | half a b α β =>
    unfold OMach.act
    dsimp only
    split
    · show O.stamp ≤ (O.take b).stamp ∧ (O.take b).stamp ≤ O.stamp + 1
      rw [OMem.take_stamp]
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
      | nil => exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

/-- A key of the list a thread is left with was a key of its list, or is
the stamp of an agent of the memory. -/
theorem OMach.act_todo (xs : XSys S) (O : OMem S) (T : TThread S) (s : Nat) (v : Id × S)
    (h : (OMach.act xs O T).2.1.todo[s]? = some v) :
    T.todo[s]? = some v ∨ O.cells[s]? = some v := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    unfold OMach.act at h
    dsimp only at h
    split at h
    · exact .inl h
    · split at h
      · split at h
        · have h' : (todo.erase _)[s]? = some v := h
          rw [tget_erase] at h'
          split at h'
          · cases h'
          · exact .inl h'
        · have h' : (todo.erase _)[s]? = some v := h
          rw [tget_erase] at h'
          split at h'
          · cases h'
          · exact .inl h'
      · exact .inl h
  | look a α =>
    unfold OMach.act at h
    dsimp only at h
    split at h <;> exact .inl h
  | seek a α p c =>
    unfold OMach.act at h
    dsimp only at h
    repeat' split at h
    all_goals exact .inl h
  | ready a b α β =>
    unfold OMach.act at h
    dsimp only at h
    split at h <;> exact .inl h
  | half a b α β =>
    unfold OMach.act at h
    dsimp only at h
    split at h <;> exact .inl h
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact .inl h
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact .inl h
      | nil => exact .inr h

theorem ZMach.act_todo (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S) :
    (ZMach.act xs O cnt T).2.1.todo = (OMach.act xs O T).2.1.todo := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | half a b α β =>
    cases h : (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | none => rw [ZMach.act_half_none cnt h, OMach.act_half_none h]
    | some R => rw [ZMach.act_half cnt h, OMach.act_half h]
  | idle => rfl
  | look a α => rfl
  | seek a α p c => rfl
  | ready a b α β => rfl
  | write as ls => rfl

omit [DecidableEq S] in
theorem OMem.ofX_stamp (X : XNet S) : (OMem.ofX X).stamp = X.agents.length := by
  have hp : ∀ (l : List (Id × S)) (O : OMem S),
      (l.foldr (fun e O => O.put e.1 e.2) O).stamp = O.stamp + l.length := by
    intro l O
    induction l with
    | nil => rfl
    | cons e l ih =>
      show (l.foldr (fun e O => O.put e.1 e.2) O).stamp + 1 = O.stamp + (l.length + 1)
      rw [ih]
      rfl
  have hl : ∀ (l : List (Port × Port)) (O : OMem S),
      (l.foldr (fun e O => O.link e.1 e.2) O).stamp = O.stamp := by
    intro l O
    induction l with
    | nil => rfl
    | cons e l ih => exact ih
  show (X.wires.foldr (fun e O => O.link e.1 e.2)
    (X.agents.foldr (fun e O => O.put e.1 e.2) (OMem.empty X.free))).stamp = _
  rw [hl, hp]
  exact Nat.zero_add _

/-- **The stamps in use are below the next stamp**, in the memory and in
the list of every thread. -/
def ZMach.Stamped (Z : ZMach S) : Prop :=
  Z.mem.Sized ∧ ∀ T ∈ Z.ths, ∀ (s : Nat) v, T.todo[s]? = some v → s < Z.mem.stamp

theorem ZMach.step_stamped (xs : XSys S) {Z : ZMach S} (h : Z.Stamped) (t : Nat) :
    (Z.step xs t).1.Stamped := by
  cases hT : Z.ths[t]? with
  | none =>
    have e : Z.step xs t = (Z, 0) := by
      unfold ZMach.step
      rw [hT]
    rw [e]
    exact h
  | some T =>
    have e : Z.step xs t =
        (⟨(ZMach.act xs Z.mem Z.cnt T).1, Z.ths.set t (ZMach.act xs Z.mem Z.cnt T).2.1,
          (ZMach.act xs Z.mem Z.cnt T).2.2.2⟩, (ZMach.act xs Z.mem Z.cnt T).2.2.1) := by
      unfold ZMach.step
      rw [hT] <;> rfl
    have hTm : T ∈ Z.ths := List.mem_of_getElem? hT
    have hmono := (OMach.act_stamp xs Z.mem T).1
    rw [e]
    refine ⟨?_, fun T' hT' s v hs => ?_⟩
    · show (ZMach.act xs Z.mem Z.cnt T).1.Sized
      rw [ZMach.act_mem]
      exact OMach.act_sized xs h.1 T
    · show s < (ZMach.act xs Z.mem Z.cnt T).1.stamp
      rw [ZMach.act_mem]
      have hT'' : T' ∈ Z.ths.set t (ZMach.act xs Z.mem Z.cnt T).2.1 := hT'
      rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
      · exact Nat.lt_of_lt_of_le (h.2 T' hm s v hs) hmono
      · rw [ZMach.act_todo] at hs
        rcases OMach.act_todo xs Z.mem T s v hs with h' | h'
        · exact Nat.lt_of_lt_of_le (h.2 T hTm s v h') hmono
        · exact Nat.lt_of_lt_of_le (h.1.lt s v h') hmono

omit [DecidableEq S] in
theorem ZMach.init_stamped (X : XNet S) (n : Nat) : (ZMach.init X n).Stamped := by
  refine ⟨OMem.ofX_sized X, fun T hT s v hs => ?_⟩
  have hT' : T ∈ (List.range n).map fun t =>
      (⟨treeOf (X.agents.drop t ++ X.agents.take t), .idle⟩ : TThread S) := hT
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hT'
  have hlt := (treeOf_spec (X.agents.drop u ++ X.agents.take u)).1 s v hs
  show s < (OMem.ofX X).stamp
  rw [OMem.ofX_stamp]
  have e : (X.agents.drop u ++ X.agents.take u).length = X.agents.length := by
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  omega

theorem ZMach.trace_stamped (xs : XSys S) (σ : Nat → Nat) {Z : ZMach S} (h : Z.Stamped) :
    ∀ i, (Z.trace xs σ i).1.Stamped
  | 0 => h
  | i + 1 => ZMach.step_stamped xs (ZMach.trace_stamped xs σ h i) (σ i)

/-- One action moves the next stamp by one at most, and only when the
thread is not at rest. -/
theorem ZMach.step_stamp (xs : XSys S) (Z : ZMach S) {g : Id → Id} {M : XMach S}
    (hM : M = Z.toY.toX.map g) (t : Nat) :
    (Z.step xs t).1.mem.stamp ≤ Z.mem.stamp + M.stepTally XThread.busy t := by
  subst hM
  have hm : (Z.toY.toX.map g).ths[t]? = (Z.ths[t]?).map fun T => T.toX.map g := by
    show ((Z.ths.map TThread.toX).map (XThread.map g))[t]? = _
    rw [List.getElem?_map, List.getElem?_map]
    cases Z.ths[t]? <;> rfl
  unfold ZMach.step XMach.stepTally
  rw [hm]
  cases hT : Z.ths[t]? with
  | none => exact Nat.le_refl _
  | some T =>
    show (ZMach.act xs Z.mem Z.cnt T).1.stamp ≤ Z.mem.stamp + (T.toX.map g).busy
    rw [ZMach.act_mem, XThread.busy_map]
    exact (OMach.act_stamp xs Z.mem T).2

/-- **The next stamp is at most the agents of the net and the work
done.** -/
theorem ZMach.stamp_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, ((ZMach.init X nt).trace xs σ i).1.mem.stamp ≤
      X.agents.length + (XMach.init X nt).work xs σ i
  | 0 => by
    show (OMem.ofX X).stamp ≤ X.agents.length + 0
    rw [OMem.ofX_stamp]
    exact Nat.le_refl _
  | i + 1 => by
    have ih := ZMach.stamp_le_work hX hnd hnt σ i
    obtain ⟨a, -, -⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨g, hr, -⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
    have hM : ((XMach.init X nt).trace xs σ i).1 =
        ((ZMach.init X nt).trace xs σ i).1.toY.toX.map g := by
      rw [a]
      exact hr.eq
    have hstep := ZMach.step_stamp xs ((ZMach.init X nt).trace xs σ i).1 hM (σ i)
    show (((ZMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.stamp ≤
      X.agents.length + ((XMach.init X nt).work xs σ i +
        ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i))
    omega

/-- **The stamps stay below a bound fixed before the run**: the agents of
the net and the bound on the actions that are not rests. -/
theorem ZMach.stamp_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    ((ZMach.init X nt).trace xs σ i).1.mem.stamp ≤
      X.agents.length + ((nt + n) * X.passBound n C D + n * (C + D + 1)) := by
  have h₁ := ZMach.stamp_le_work (xs := xs) hX hnd hnt σ i
  have h₂ := XMach.work_le hX hnd hnt hb hs hn σ i
  omega

/-- The counter of the numbered program on ordered maps alone stays below
the bound fixed before the run. -/
theorem ZMach.cnt_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {Sp : Nat} (hsp : xs.SpanLe Sp) {nt : Nat}
    (hnt : 0 < nt) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    ((ZMach.init X nt).trace xs σ i).1.cnt ≤ X.top + Sp * n := by
  obtain ⟨a, -, -⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
  have e : ((ZMach.init X nt).trace xs σ i).1.cnt = ((YMach.init X nt).trace xs σ i).1.cnt :=
    congrArg YMach.cnt a
  rw [e]
  exact YMach.cnt_le hX hsp hnt hs hn σ i

/-- **Every number the numbered program holds fits in a word fixed before
the run.**  If `2 ^ W` is above `X.top + Sp * n` and above the agents of
the net and the bound on the actions that are not rests, then at every
moment of every run the counter, every cell of every name in the state,
and every stamp in the memory or in the list of a thread is below
`2 ^ W`. -/
theorem ZMach.numbers_lt {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {Sp : Nat} (hsp : xs.SpanLe Sp) {nt : Nat}
    (hnt : 0 < nt) {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (i : Nat) {W : Nat} (hW : X.top + Sp * n < 2 ^ W)
    (hW' : X.agents.length + ((nt + n) * X.passBound n C D + n * (C + D + 1)) < 2 ^ W) :
    ((ZMach.init X nt).trace xs σ i).1.cnt < 2 ^ W ∧
      (∀ j, ((ZMach.init X nt).trace xs σ i).1.toY.toX.Mentions j → ∀ k ∈ j, k < 2 ^ W) ∧
      (∀ (s : Nat) v, ((ZMach.init X nt).trace xs σ i).1.mem.cells[s]? = some v → s < 2 ^ W) ∧
      ∀ T ∈ ((ZMach.init X nt).trace xs σ i).1.ths, ∀ (s : Nat) v,
        T.todo[s]? = some v → s < 2 ^ W := by
  obtain ⟨a, -, -⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
  have hc := ZMach.cnt_le (xs := xs) hX hnd hsp hnt hs hn σ i
  have hcells := YMach.cells_lt (xs := xs) hX hsp hnt hs hn σ i
  rw [← a] at hcells
  have hst := ZMach.stamp_le (xs := xs) hX hnd hnt hb hs hn σ i
  have hsd := ZMach.trace_stamped xs σ (ZMach.init_stamped X nt) i
  refine ⟨Nat.lt_of_le_of_lt hc hW, fun j hj k hk => ?_, fun s v hs' => ?_,
    fun T hT s v hs' => ?_⟩
  · exact Nat.lt_trans (hcells.of_mentions hj k hk) hW
  · exact Nat.lt_of_lt_of_le (hsd.1.lt s v hs') (Nat.le_of_lt (Nat.lt_of_le_of_lt hst hW'))
  · exact Nat.lt_of_lt_of_le (hsd.2 T hT s v hs') (Nat.le_of_lt (Nat.lt_of_le_of_lt hst hW'))

end NumberSizesOrdered

/-! ### Counting in bits

The counts take a number as one unit.  Here the numbers are charged by
their size: a comparison of two numbers costs the bits of the shorter, and
a number made costs its bits.  The operations on the maps are the same
functions as before, with this charge for the weight of a comparison, so
they return what the library returns.  An operation then costs at most its
count times the bits of its key.  The time of the numbered program in bits
is defined, and the kernel computes it on the two runs. -/

section BitScale

open Std.DTreeMap.Internal

variable {α : Type} {β : α → Type}

/-- **A lookup charged `w'` costs at most `c` times the lookup charged
`w`**, when each comparison with the key costs at most `c` times as
much. -/
theorem implGetF_scale {δ : Type} [Ord α] {w w' : α → α → Nat} {c : Nat} (hc : 1 ≤ c)
    (t : Impl α (fun _ => δ)) (k : α) (h : ∀ k', w' k k' ≤ c * w k k') :
    (implGetF w' t k).2 ≤ c * (implGetF w t k).2 := by
  induction t with
  | leaf =>
    show 1 ≤ c * 1
    omega
  | inner sz k' v' l r ihl ihr =>
    have hk := h k'
    rw [implGetF, implGetF]
    cases compare k k' with
    | lt =>
      show (implGetF w' l k).2 + (1 + w' k k') ≤ c * ((implGetF w l k).2 + (1 + w k k'))
      rw [Nat.mul_add, Nat.mul_add]
      omega
    | gt =>
      show (implGetF w' r k).2 + (1 + w' k k') ≤ c * ((implGetF w r k).2 + (1 + w k k'))
      rw [Nat.mul_add, Nat.mul_add]
      omega
    | eq =>
      show 1 + w' k k' ≤ c * (1 + w k k')
      rw [Nat.mul_add]
      omega

theorem implInsertF_scale [Ord α] {w w' : α → α → Nat} {c : Nat} (hc : 1 ≤ c) (k : α)
    (v : β k) (t : Impl α β) (h : ∀ k', w' k k' ≤ c * w k k') :
    (implInsertF w' k v t).2 ≤ c * (implInsertF w k v t).2 := by
  induction t with
  | leaf =>
    show 2 ≤ c * 2
    omega
  | inner sz k' v' l r ihl ihr =>
    have hk := h k'
    rw [implInsertF, implInsertF]
    cases compare k k' with
    | lt =>
      have e : (implInsertF w' k v l).1 = (implInsertF w k v l).1 := by
        rw [implInsertF_fst, implInsertF_fst]
      have hB := Nat.le_mul_of_pos_left (balanceLF k' v' (implInsertF w k v l).1 r).2 hc
      show (implInsertF w' k v l).2 +
          (1 + w' k k' + (balanceLF k' v' (implInsertF w' k v l).1 r).2) ≤
        c * ((implInsertF w k v l).2 +
          (1 + w k k' + (balanceLF k' v' (implInsertF w k v l).1 r).2))
      rw [e, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      omega
    | gt =>
      have e : (implInsertF w' k v r).1 = (implInsertF w k v r).1 := by
        rw [implInsertF_fst, implInsertF_fst]
      have hB := Nat.le_mul_of_pos_left (balanceRF k' v' l (implInsertF w k v r).1).2 hc
      show (implInsertF w' k v r).2 +
          (1 + w' k k' + (balanceRF k' v' l (implInsertF w' k v r).1).2) ≤
        c * ((implInsertF w k v r).2 +
          (1 + w k k' + (balanceRF k' v' l (implInsertF w k v r).1).2))
      rw [e, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      omega
    | eq =>
      show 1 + w' k k' + 1 ≤ c * (1 + w k k' + 1)
      rw [Nat.mul_add, Nat.mul_add]
      omega

theorem implEraseF_scale [Ord α] {w w' : α → α → Nat} {c : Nat} (hc : 1 ≤ c) (k : α)
    (t : Impl α β) (h : ∀ k', w' k k' ≤ c * w k k') :
    (implEraseF w' k t).2 ≤ c * (implEraseF w k t).2 := by
  induction t with
  | leaf =>
    show 1 ≤ c * 1
    omega
  | inner sz k' v' l r ihl ihr =>
    have hk := h k'
    rw [implEraseF, implEraseF]
    cases compare k k' with
    | lt =>
      have e : (implEraseF w' k l).1 = (implEraseF w k l).1 := by
        rw [implEraseF_fst, implEraseF_fst]
      have hB := Nat.le_mul_of_pos_left (balanceRF k' v' (implEraseF w k l).1 r).2 hc
      show (implEraseF w' k l).2 +
          (1 + w' k k' + (balanceRF k' v' (implEraseF w' k l).1 r).2) ≤
        c * ((implEraseF w k l).2 +
          (1 + w k k' + (balanceRF k' v' (implEraseF w k l).1 r).2))
      rw [e, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      omega
    | gt =>
      have e : (implEraseF w' k r).1 = (implEraseF w k r).1 := by
        rw [implEraseF_fst, implEraseF_fst]
      have hB := Nat.le_mul_of_pos_left (balanceLF k' v' l (implEraseF w k r).1).2 hc
      show (implEraseF w' k r).2 +
          (1 + w' k k' + (balanceLF k' v' l (implEraseF w' k r).1).2) ≤
        c * ((implEraseF w k r).2 +
          (1 + w k k' + (balanceLF k' v' l (implEraseF w k r).1).2))
      rw [e, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      omega
    | eq =>
      have hG := Nat.le_mul_of_pos_left (implGlueF l r).2 hc
      show (implGlueF l r).2 + (1 + w' k k') ≤ c * ((implGlueF l r).2 + (1 + w k k'))
      rw [Nat.mul_add, Nat.mul_add]
      omega

end BitScale

section Bits

open Std.DTreeMap.Internal

variable {V : Type}

/-- **The bits read to compare two numbers**: those of the shorter. -/
def cellBits (x y : Nat) : Nat := min (lg x) (lg y)

theorem cellBits_le (x y : Nat) : cellBits x y ≤ lg x := Nat.min_le_left _ _

theorem cellBits_pos (x y : Nat) : 1 ≤ cellBits x y := Nat.le_min.2 ⟨lg_pos x, lg_pos y⟩

/-- **The bits read to compare two names**: as `cmpC`, but each pair of
cells compared is charged its bits. -/
def cmpB : List Nat → List Nat → Nat
  | [], [] => 1
  | [], _ :: _ => 1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => cellBits x y
    | .eq => cmpB xs ys + cellBits x y
    | .gt => cellBits x y

/-- **The size of a name in bits.** -/
def nameBits : List Nat → Nat
  | [] => 1
  | x :: xs => lg x + nameBits xs

theorem nameBits_pos : ∀ a : List Nat, 1 ≤ nameBits a
  | [] => Nat.le_refl _
  | x :: _ => Nat.le_trans (lg_pos x) (Nat.le_add_right _ _)

/-- A comparison reads no more bits than the first name has. -/
theorem cmpB_le : ∀ a b : List Nat, cmpB a b ≤ nameBits a
  | [], [] => Nat.le_refl _
  | [], _ :: _ => Nat.le_refl _
  | x :: xs, [] => nameBits_pos (x :: xs)
  | x :: xs, y :: ys => by
    have ih := cmpB_le xs ys
    have hx := cellBits_le x y
    have hp := nameBits_pos xs
    rw [cmpB]
    show _ ≤ lg x + nameBits xs
    cases compare x y with
    | lt =>
      show cellBits x y ≤ _
      omega
    | eq =>
      show cmpB xs ys + cellBits x y ≤ _
      omega
    | gt =>
      show cellBits x y ≤ _
      omega

/-- **A name of at most `L` cells below `2 ^ W` has at most
`L * (W + 1) + 1` bits.** -/
theorem nameBits_le {W : Nat} : ∀ (a : List Nat) {L : Nat}, a.length ≤ L →
    (∀ k ∈ a, k < 2 ^ W) → nameBits a ≤ L * (W + 1) + 1
  | [], _, _, _ => Nat.le_add_left _ _
  | x :: xs, L, hl, hc => by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by
      have : xs.length + 1 ≤ L := hl
      omega⟩
    have ih := nameBits_le xs (L := L') (Nat.le_of_succ_le_succ hl)
      (fun k hk => hc k (List.mem_cons_of_mem _ hk))
    have hx := lg_le (hc x List.mem_cons_self)
    show lg x + nameBits xs ≤ (L' + 1) * (W + 1) + 1
    rw [Nat.succ_mul]
    omega

theorem one_le_cmpC : ∀ a b : List Nat, 1 ≤ (cmpC a b).2
  | [], [] => Nat.le_refl _
  | [], _ :: _ => Nat.le_refl _
  | _ :: _, [] => Nat.le_refl _
  | x :: xs, y :: ys => by
    rw [cmpC]
    cases compare x y with
    | lt => exact Nat.le_refl _
    | eq => exact Nat.le_add_left _ _
    | gt => exact Nat.le_refl _

/-- What a comparison of two numbers reads, in bits. -/
def natB : Nat → Nat → Nat := cellBits

/-- What a comparison of two names reads, in bits. -/
def nameB (a b : List Nat) : Nat := cmpB a b

theorem natB_le (k k' : Nat) : natB k k' ≤ lg k * natW k k' := by
  have h := cellBits_le k k'
  show cellBits k k' ≤ lg k * 1
  omega

theorem nameB_le (k k' : List Nat) : nameB k k' ≤ nameBits k * nameW k k' :=
  Nat.le_trans (cmpB_le k k') (Nat.le_mul_of_pos_right _ (one_le_cmpC k k'))

/-- The lookup in a map keyed by numbers, in bits. -/
def tgetB (t : Std.TreeMap Nat V) (k : Nat) : Option V × Nat := implGetF natB t.inner.inner k

/-- The insertion in a map keyed by numbers, in bits. -/
def tinsertB (t : Std.TreeMap Nat V) (k : Nat) (v : V) : Impl Nat (fun _ => V) × Nat :=
  implInsertF natB k v t.inner.inner

/-- The erasure in a map keyed by numbers, in bits. -/
def teraseB (t : Std.TreeMap Nat V) (k : Nat) : Impl Nat (fun _ => V) × Nat :=
  implEraseF natB k t.inner.inner

/-- The lookup of a name, in bits. -/
def ngetB (t : Std.TreeMap (List Nat) V) (k : List Nat) : Option V × Nat :=
  implGetF nameB t.inner.inner k

/-- The insertion at a name, in bits. -/
def ninsertB (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    Impl (List Nat) (fun _ => V) × Nat :=
  implInsertF nameB k v t.inner.inner

/-- The erasure at a name, in bits. -/
def neraseB (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    Impl (List Nat) (fun _ => V) × Nat :=
  implEraseF nameB k t.inner.inner

/-- **The operations counted in bits are those of the library.** -/
theorem tgetB_fst (t : Std.TreeMap Nat V) (k : Nat) : (tgetB t k).1 = t[k]? :=
  implGetF_fst natB t.inner.inner k

theorem tinsertB_fst (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (tinsertB t k v).1 = (t.insert k v).inner.inner := by
  show (implInsertF natB k v t.inner.inner).1 =
    (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl
  rw [implInsertF_fst, Impl.insert_eq_insert!]

theorem teraseB_fst (t : Std.TreeMap Nat V) (k : Nat) :
    (teraseB t k).1 = (t.erase k).inner.inner := by
  show (implEraseF natB k t.inner.inner).1 =
    (Impl.erase k t.inner.inner t.inner.wf.balanced).impl
  rw [implEraseF_fst, Impl.erase_eq_erase!]

theorem ngetB_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) : (ngetB t k).1 = t[k]? :=
  implGetF_fst nameB t.inner.inner k

theorem ninsertB_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    (ninsertB t k v).1 = (t.insert k v).inner.inner := by
  show (implInsertF nameB k v t.inner.inner).1 =
    (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl
  rw [implInsertF_fst, Impl.insert_eq_insert!]

theorem neraseB_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (neraseB t k).1 = (t.erase k).inner.inner := by
  show (implEraseF nameB k t.inner.inner).1 =
    (Impl.erase k t.inner.inner t.inner.wf.balanced).impl
  rw [implEraseF_fst, Impl.erase_eq_erase!]

/-- **In bits, an operation on a map keyed by numbers costs at most its
count times the bits of its key.** -/
theorem tgetB_le (t : Std.TreeMap Nat V) (k : Nat) : (tgetB t k).2 ≤ lg k * (tgetF t k).2 :=
  implGetF_scale (lg_pos k) t.inner.inner k (natB_le k)

theorem tinsertB_le (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (tinsertB t k v).2 ≤ lg k * (tinsertF t k v).2 :=
  implInsertF_scale (β := fun _ => V) (lg_pos k) k v t.inner.inner (natB_le k)

theorem teraseB_le (t : Std.TreeMap Nat V) (k : Nat) :
    (teraseB t k).2 ≤ lg k * (teraseF t k).2 :=
  implEraseF_scale (lg_pos k) k t.inner.inner (natB_le k)

/-- **In bits, an operation on a map keyed by names costs at most its
count times the bits of its key.** -/
theorem ngetB_le (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (ngetB t k).2 ≤ nameBits k * (ngetF t k).2 :=
  implGetF_scale (nameBits_pos k) t.inner.inner k (nameB_le k)

theorem ninsertB_le (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    (ninsertB t k v).2 ≤ nameBits k * (ninsertF t k v).2 :=
  implInsertF_scale (β := fun _ => V) (nameBits_pos k) k v t.inner.inner (nameB_le k)

theorem neraseB_le (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (neraseB t k).2 ≤ nameBits k * (neraseF t k).2 :=
  implEraseF_scale (nameBits_pos k) k t.inner.inner (nameB_le k)

end Bits

section BitCost

variable [DecidableEq S] {xs : XSys S}

/-- The bits read to compare two ports: the index, then the name. -/
def portB (p q : Port) : Nat := nameB (portKey p) (portKey q)

theorem portB_le (p q : Port) : portB p q ≤ nameBits (portKey p) := cmpB_le _ _

/-- Looking a name up, in bits. -/
def OMem.symB (O : OMem S) (i : Id) : Nat := (ngetB O.live i).2

/-- Looking the neighbours of a port up, in bits. -/
def OMem.nbB (O : OMem S) (p : Port) : Nat := (ngetB O.nbrs (portKey p)).2

/-- Taking an agent out, in bits. -/
def OMem.takeB (O : OMem S) (a : Id) : Nat :=
  match O.live[a]? with
  | some v => (teraseB O.cells v.1).2 + (neraseB O.live a).2
  | none => 0

/-- Writing an agent, in bits: the two insertions, and the bits of the
stamp that is moved forward. -/
def OMem.putB (O : OMem S) (i : Id) (γ : S) : Nat :=
  (tinsertB O.cells O.stamp (i, γ)).2 + (ninsertB O.live i (O.stamp, γ)).2 + lg O.stamp

/-- Writing a segment, in bits: the lookup, the comparison with the
latest neighbour, the insertion. -/
def OMem.linkB (O : OMem S) (p q : Port) : Nat :=
  O.nbB p + (match (O.nb p).head? with
    | some h => portB q h
    | none => 0) + (ninsertB O.nbrs (portKey p) (pushNb q (O.nb p))).2

omit [DecidableEq S] in
/-- **In bits, a lookup of a name costs at most its count times the bits
of the name.** -/
theorem OMem.symB_le (O : OMem S) (i : Id) : O.symB i ≤ nameBits i * O.symF i :=
  ngetB_le O.live i

omit [DecidableEq S] in
theorem OMem.nbB_le (O : OMem S) (p : Port) : O.nbB p ≤ nameBits (portKey p) * O.nbF p :=
  ngetB_le O.nbrs (portKey p)

omit [DecidableEq S] in
/-- In bits, taking an agent out costs at most its count times the bits
of its name or of its stamp. -/
theorem OMem.takeB_le (O : OMem S) (a : Id) {K : Nat} (ha : nameBits a ≤ K)
    (hs : ∀ v, O.live[a]? = some v → lg v.1 ≤ K) : O.takeB a ≤ K * O.takeF a := by
  unfold OMem.takeB OMem.takeF
  cases hl : O.live[a]? with
  | none => exact Nat.zero_le _
  | some v =>
    have h₁ := teraseB_le O.cells v.1
    have h₂ := neraseB_le O.live a
    have h₃ := Nat.mul_le_mul_right (teraseF O.cells v.1).2 (hs v hl)
    have h₄ := Nat.mul_le_mul_right (neraseF O.live a).2 ha
    show (teraseB O.cells v.1).2 + (neraseB O.live a).2 ≤
      K * ((teraseF O.cells v.1).2 + (neraseF O.live a).2)
    rw [Nat.mul_add]
    omega

omit [DecidableEq S] in
/-- In bits, writing an agent costs at most its count and one, times the
bits of its name or of the stamp. -/
theorem OMem.putB_le (O : OMem S) (i : Id) (γ : S) {K : Nat} (hi : nameBits i ≤ K)
    (hs : lg O.stamp ≤ K) : O.putB i γ ≤ K * (O.putF i γ + 1) := by
  have h₁ := tinsertB_le O.cells O.stamp (i, γ)
  have h₂ := ninsertB_le O.live i (O.stamp, γ)
  have h₃ := Nat.mul_le_mul_right (tinsertF O.cells O.stamp (i, γ)).2 hs
  have h₄ := Nat.mul_le_mul_right (ninsertF O.live i (O.stamp, γ)).2 hi
  show (tinsertB O.cells O.stamp (i, γ)).2 + (ninsertB O.live i (O.stamp, γ)).2 + lg O.stamp ≤
    K * ((tinsertF O.cells O.stamp (i, γ)).2 + (ninsertF O.live i (O.stamp, γ)).2 + 1)
  rw [Nat.mul_add, Nat.mul_add]
  omega

omit [DecidableEq S] in
/-- In bits, writing a segment costs at most its count and one, times the
bits of its two ports. -/
theorem OMem.linkB_le (O : OMem S) (p q : Port) {K : Nat} (hp : nameBits (portKey p) ≤ K)
    (hq : nameBits (portKey q) ≤ K) : O.linkB p q ≤ K * (O.linkF p q + 1) := by
  have h₁ := O.nbB_le p
  have h₂ := ninsertB_le O.nbrs (portKey p) (pushNb q (O.nb p))
  have h₃ := Nat.mul_le_mul_right (O.nbF p) hp
  have h₄ := Nat.mul_le_mul_right (ninsertF O.nbrs (portKey p) (pushNb q (O.nb p))).2 hp
  have h₅ : (match (O.nb p).head? with
      | some h => portB q h
      | none => 0) ≤ K := by
    cases (O.nb p).head? with
    | none => exact Nat.zero_le _
    | some h => exact Nat.le_trans (portB_le q h) hq
  show O.nbB p + (match (O.nb p).head? with
      | some h => portB q h
      | none => 0) + (ninsertB O.nbrs (portKey p) (pushNb q (O.nb p))).2 ≤
    K * (O.nbF p + (ninsertF O.nbrs (portKey p) (pushNb q (O.nb p))).2 + 1)
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- The bits that the search for a neighbour other than `p` reads. -/
def findBits (p : Port) : List Port → Nat
  | [] => 0
  | q :: l => if q ≠ p then portB q p else findBits p l + portB q p

/-- **What an action of the numbered program costs in bits.**  As
`ZMach.fcost`, but every comparison of two numbers is charged the bits of
the shorter, in the operations on the maps and in the tests of the action
itself, and so is each number that an action makes: the stamp of an agent
written, the counter and the numbers of a claim.  A call and a node built
still count one. -/
def ZMach.bcost (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match (tmaxC T.todo).1 with
    | none => 0
    | some s =>
      match T.todo[s]? with
      | some e =>
        1 + ((tmaxC T.todo).2 + (tgetB T.todo s).2 + (teraseB T.todo s).2) + O.symB e.1
      | none => 1 + ((tmaxC T.todo).2 + (tgetB T.todo s).2)
  | .look a _ => 2 + O.nbB (a, 0)
  | .seek a _ p c =>
    if c.2 = 0 then
      1 + O.symB c.1 +
        if (O.sym c.1).isSome then nameB a c.1 else O.nbB c + findBits p (O.nb c)
    else 1 + O.nbB c + findBits p (O.nb c)
  | .ready a _ α _ => 1 + O.symB a + if O.sym a = some α then O.takeB a else 0
  | .half a b α β =>
    1 + O.symB b + if O.sym b = some β then
        nameB a b + if a ≠ b then
            match xs.rule α β with
            | some R =>
              O.takeB b + lg (cnt + R.span) *
                (1 + (R.numAgents cnt).length +
                  2 * (R.numLinks xs.sys.ar a b cnt α β).length)
            | none => O.putB a α
          else O.putB a α
      else O.putB a α
  | .write ((i, γ) :: _) _ => 1 + O.putB i γ
  | .write [] ((p, q) :: _) => 4 + O.linkB p q
  | .write [] [] => 1

/-- What the action of thread `t` costs in bits. -/
def ZMach.stepBcost (xs : XSys S) (M : ZMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => ZMach.bcost xs M.mem M.cnt T
  | none => 0

/-- **The running time of the numbered program in bits.** -/
def ZMach.btime (xs : XSys S) (σ : Nat → Nat) (M : ZMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => ZMach.btime xs σ M i + (M.trace xs σ i).1.stepBcost xs (σ i)

theorem ZMach.stepBcost_rest (xs : XSys S) {M : ZMach S} (h : M.toO.resting = true)
    (t : Nat) : M.stepBcost xs t = 0 := by
  unfold ZMach.stepBcost
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := OMach.rest_thread (M := M.toO) h hT
    show ZMach.bcost xs M.mem M.cnt ⟨todo, .idle⟩ = 0
    unfold ZMach.bcost
    dsimp only
    rw [hmax]

/-- Once the numbered program is at rest its time in bits stays what it
is. -/
theorem ZMach.btime_rest (σ : Nat → Nat) {M : ZMach S} {B : Nat}
    (h : (M.trace xs σ B).1.toO.resting = true) :
    ∀ d, M.btime xs σ (B + d) = M.btime xs σ B
  | 0 => rfl
  | d + 1 => by
    have z : (M.trace xs σ (B + d)).1.stepBcost xs (σ (B + d)) = 0 := by
      rw [ZMach.trace_rest σ h d]
      exact ZMach.stepBcost_rest xs h _
    show M.btime xs σ (B + d) + (M.trace xs σ (B + d)).1.stepBcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact ZMach.btime_rest σ h d

end BitCost

/-! ### A bound in bits for every schedule

The time in bits is bounded for a whole run.  Every key that an action
looks up has a number of bits fixed before the run: the stamps and the
counter are bounded, the names are numbers of one cell or names of the
net, and the indices of the ports, which are cells of the keys of the map
of the neighbours, do not grow.  An action then costs in bits at most its
count times the bits of a key, three times over, and the bound on the
count gives a bound on the bits. -/

/-- The index of the port of an agent that a port of a rule becomes. -/
def LPort.idx : LPort → Nat
  | .ifc _ k => k + 1
  | .new _ _ k => k

section PortIndices

variable [DecidableEq S] {xs : XSys S}

/-- **No port of a rule has an index above `P`.** -/
def XSys.PortsLe (xs : XSys S) (P : Nat) : Prop :=
  ∀ α β R, xs.rule α β = some R →
    ∀ x ∈ ifcPorts xs.sys.ar α β ++ R.newPorts xs.sys.ar,
      x.idx ≤ P ∧ ∀ y, R.wire x = some y → y.idx ≤ P

/-- No segment of the memory has a port of index above `P`. -/
def XNet.PortsLe (X : XNet S) (P : Nat) : Prop := ∀ e ∈ X.wires, e.1.2 ≤ P ∧ e.2.2 ≤ P

/-- No port that a thread has in hand has an index above `P`. -/
def TState.PortsLe : TState S → Nat → Prop
  | .seek _ _ p c, P => p.2 ≤ P ∧ c.2 ≤ P
  | .write _ ls, P => ∀ e ∈ ls, e.1.2 ≤ P ∧ e.2.2 ≤ P
  | _, _ => True

/-- **An action that does not claim makes no index of a port**: the ports
it comes to hold are ports of segments of the memory, and the segments it
writes are those it held. -/
theorem XMach.act_ports (xs : XSys S) {X : XNet S} {T : XThread S} {P : Nat}
    (hX : X.PortsLe P) (hT : T.st.PortsLe P) :
    (XMach.act xs X T).1.PortsLe P ∧
      ((XMach.act xs X T).2.2 = 0 → (XMach.act xs X T).2.1.st.PortsLe P) := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨hX, fun _ => trivial⟩
    | cons e rest =>
      cases hact : XMach.act xs X ⟨e :: rest, .idle⟩ with
      | mk X' r =>
        obtain ⟨T', k⟩ := r
        unfold XMach.act at hact
        dsimp only at hact
        split at hact
        · cases hact
          exact ⟨hX, fun _ => trivial⟩
        · cases hact
          exact ⟨hX, fun _ => trivial⟩
  | look a α =>
    cases hact : XMach.act xs X ⟨todo, .look a α⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · rename_i q hq
        cases hact
        have hq' := (hX _ (assoc_mem hq)).2
        exact ⟨hX, fun _ => ⟨Nat.zero_le _, hq'⟩⟩
      · cases hact
        exact ⟨hX, fun _ => trivial⟩
  | seek a α p c =>
    have hc : c.2 ≤ P := hT.2
    cases hact : XMach.act xs X ⟨todo, .seek a α p c⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · split at hact
        · cases hact
          exact ⟨hX, fun _ => trivial⟩
        · cases hact
          exact ⟨hX, fun _ => trivial⟩
      · split at hact
        · rename_i q hq
          cases hact
          have hq' := (hX _ (nextSeg_spec hq).1).2
          exact ⟨hX, fun _ => ⟨hc, hq'⟩⟩
        · cases hact
          exact ⟨hX, fun _ => trivial⟩
  | ready a b α β =>
    cases hact : XMach.act xs X ⟨todo, .ready a b α β⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · cases hact
        exact ⟨hX, fun _ => trivial⟩
      · cases hact
        exact ⟨hX, fun _ => trivial⟩
  | half a b α β =>
    cases h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | none =>
      rw [XMach.act_half_none h]
      exact ⟨hX, fun _ => trivial⟩
    | some R =>
      rw [XMach.act_half h]
      exact ⟨hX, fun h0 => absurd h0 (Nat.succ_ne_zero 0)⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨hX, fun _ => hT⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        refine ⟨fun e he => ?_, fun _ x hx => hT x (List.mem_cons_of_mem _ hx)⟩
        have he' : e ∈ (p, q) :: X.wires := he
        rcases List.mem_cons.1 he' with rfl | h
        · exact hT (p, q) List.mem_cons_self
        · exact hX e h
      | nil => exact ⟨hX, fun _ => trivial⟩

theorem embN_idx (a b : Id) (cnt : Nat) (x : LPort) : (embN a b cnt x).2 = x.idx := by
  cases x <;> rfl

omit [DecidableEq S] in
/-- The segments that a numbered claim lists have the indices of the
rule. -/
theorem XSys.numLinks_ports (xs : XSys S) {P : Nat} (hp : xs.PortsLe P) {α β : S}
    {R : XRhs S} (hr : xs.rule α β = some R) (a b : Id) (cnt : Nat) :
    ∀ e ∈ R.numLinks xs.sys.ar a b cnt α β, e.1.2 ≤ P ∧ e.2.2 ≤ P := by
  intro e he
  have he' : e ∈ (ifcPorts xs.sys.ar α β ++ R.newPorts xs.sys.ar).filterMap _ := he
  obtain ⟨x, hx, hex⟩ := List.mem_filterMap.1 he'
  have h := hp α β R hr x hx
  cases hw : R.wire x with
  | none =>
    rw [hw] at hex
    cases hex
  | some y =>
    rw [hw] at hex
    have e' : e = (embN a b cnt x, embN a b cnt y) := (Option.some.inj hex).symm
    rw [e']
    show (embN a b cnt x).2 ≤ P ∧ (embN a b cnt y).2 ≤ P
    rw [embN_idx, embN_idx]
    exact ⟨h.1, h.2 y hw⟩

/-- No port in the state of the numbered program has an index above
`P`. -/
def YMach.PortsLe (Y : YMach S) (P : Nat) : Prop :=
  Y.mem.PortsLe P ∧ ∀ T ∈ Y.ths, T.st.PortsLe P

theorem YMach.step_ports (xs : XSys S) {P : Nat} (hp : xs.PortsLe P) {Y : YMach S}
    (h : Y.PortsLe P) (t : Nat) : (Y.step xs t).1.PortsLe P := by
  cases hT : Y.ths[t]? with
  | none =>
    rw [YMach.step_none hT]
    exact h
  | some T =>
    have hTm : T ∈ Y.ths := List.mem_of_getElem? hT
    rcases XMach.act_zero_or_claim xs Y.mem T with h0 | ⟨a, b, α, β, R, hst, hR⟩
    · obtain ⟨b1, b2⟩ := XMach.act_ports xs h.1 (h.2 T hTm)
      rw [YMach.step_eq hT, YMach.act_zero Y.cnt h0]
      refine ⟨b1, fun T' hT' => ?_⟩
      have hT'' : T' ∈ Y.ths.set t (XMach.act xs Y.mem T).2.1 := hT'
      rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
      · exact h.2 T' hm
      · exact b2 h0
    · obtain ⟨todo, st⟩ := T
      have hst' : st = .half a b α β := hst
      subst hst'
      have hc : assoc b Y.mem.agents = some β ∧ a ≠ b := by
        by_cases c : assoc b Y.mem.agents = some β ∧ a ≠ b
        · exact c
        · rw [ite_neg' c] at hR
          cases hR
      have hr : xs.rule α β = some R := by
        rw [ite_pos' hc] at hR
        exact hR
      rw [YMach.step_eq hT, YMach.act_claim Y.cnt hR]
      refine ⟨h.1, fun T' hT' => ?_⟩
      have hT'' : T' ∈ Y.ths.set t ⟨todo, .write (R.numAgents Y.cnt)
          (R.numLinks xs.sys.ar a b Y.cnt α β)⟩ := hT'
      rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
      · exact h.2 T' hm
      · exact xs.numLinks_ports hp hr a b Y.cnt

/-- **The indices of the ports do not grow.**  If no segment of the net
and no port of a rule has an index above `P`, then at every moment of
every run of the numbered program no port in the memory or in the hand of
a thread has one. -/
theorem YMach.ports_le {P : Nat} (hp : xs.PortsLe P) {X : XNet S} (hX : X.PortsLe P)
    (nt : Nat) (σ : Nat → Nat) : ∀ i, ((YMach.init X nt).trace xs σ i).1.PortsLe P
  | 0 => by
    refine ⟨hX, fun T hT => ?_⟩
    have hT' : T ∈ (List.range nt).map fun t =>
        (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S) := hT
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hT'
    trivial
  | i + 1 => YMach.step_ports xs hp (YMach.ports_le hp hX nt σ i) (σ i)

end PortIndices

theorem mem_pushNb {q q' : Port} {l : List Port} (h : q' ∈ pushNb q l) : q' = q ∨ q' ∈ l := by
  unfold pushNb at h
  split at h
  · exact .inr h
  · exact List.mem_cons.1 h

/-- A neighbour of a port is the other end of one of its segments. -/
theorem mem_nbOf : ∀ (ws : List (Port × Port)) {c q : Port}, q ∈ nbOf ws c → (c, q) ∈ ws
  | [], _, _, h => absurd h List.not_mem_nil
  | e :: ws, c, q, h => by
    have h' : q ∈ (if e.1 = c then pushNb e.2 (nbOf ws c) else nbOf ws c) := h
    by_cases hc : e.1 = c
    · rw [ite_pos' hc] at h'
      rcases mem_pushNb h' with e' | h''
      · have ee : e = (c, q) := by
          obtain ⟨e1, e2⟩ := e
          have h1 : e1 = c := hc
          have h2 : q = e2 := e'
          rw [h1, h2]
        rw [ee]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_nbOf ws h'')
    · rw [ite_neg' hc] at h'
      exact List.mem_cons_of_mem _ (mem_nbOf ws h')

theorem findBits_le (p : Port) {K : Nat} : ∀ l : List Port, (∀ q ∈ l, portB q p ≤ K) →
    findBits p l ≤ K * findCells p l
  | [], _ => Nat.zero_le _
  | q :: l, h => by
    have ih := findBits_le p l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hq := h q List.mem_cons_self
    show (if q ≠ p then portB q p else findBits p l + portB q p) ≤
      K * (if q ≠ p then 1 else findCells p l + 1)
    by_cases c : q ≠ p
    · rw [ite_pos' c, ite_pos' c]
      omega
    · rw [ite_neg' c, ite_neg' c, Nat.mul_add]
      omega

section BitBound

variable [DecidableEq S] {xs : XSys S}

/-- **In bits, an action costs at most three times its count times the
bits of a key.**  `K` bounds the bits of every number and of every key
that the action can use: the stamps, the counter after a claim, the names
in the hand and the list of the thread, and the ports with their index. -/
theorem ZMach.bcost_le (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S)
    {K Kn P Sp : Nat} (hsp : xs.SpanLe Sp) (hcnt : lg (cnt + Sp) ≤ K) (hst : lg O.stamp ≤ K)
    (hlive : ∀ (a : Id) (v : Nat × S), O.live[a]? = some v → lg v.1 ≤ K)
    (htodo : ∀ (s : Nat) v, T.todo[s]? = some v → lg s ≤ K)
    (hnames : T.toX.All (fun i => nameBits i ≤ Kn)) (hports : T.st.PortsLe P)
    (hnb : ∀ c q, q ∈ O.nb c → nameBits (portKey q) ≤ K) (hK : lg P + Kn ≤ K) :
    ZMach.bcost xs O cnt T ≤ 3 * (K * ZMach.fcost xs O cnt T) := by
  have hP1 := lg_pos P
  have hK1 : 1 ≤ K := by omega
  have hname : ∀ i, nameBits i ≤ Kn → nameBits i ≤ K := fun i h => by omega
  have hport : ∀ p : Port, p.2 ≤ P → nameBits p.1 ≤ Kn → nameBits (portKey p) ≤ K := by
    intro p h1 h2
    have h3 := lg_mono h1
    show lg p.2 + nameBits p.1 ≤ K
    omega
  obtain ⟨todo, st⟩ := T
  obtain ⟨hTd, hTs⟩ := hnames
  cases st with
  | idle =>
    show ZMach.bcost xs O cnt ⟨todo, .idle⟩ ≤ 3 * (K * OMach.fcost xs O ⟨todo, .idle⟩)
    unfold ZMach.bcost OMach.fcost
    dsimp only
    cases hmax : (tmaxC todo).1 with
    | none => exact Nat.zero_le _
    | some s =>
      have hs' : todo.maxKey? = some s := by
        rw [← tmaxC_fst]
        exact hmax
      obtain ⟨⟨v, hv⟩, -⟩ := tmax_some todo hs'
      have hlg : lg s ≤ K := htodo s v hv
      have g₁ := tgetB_le todo s
      have g₂ := teraseB_le todo s
      have g₁' := Nat.mul_le_mul_right (tgetF todo s).2 hlg
      have g₂' := Nat.mul_le_mul_right (teraseF todo s).2 hlg
      have hm := Nat.le_mul_of_pos_left (tmaxC todo).2 hK1
      dsimp only
      cases he : todo[s]? with
      | none =>
        show 1 + ((tmaxC todo).2 + (tgetB todo s).2) ≤
          3 * (K * (1 + ((tmaxC todo).2 + (tgetF todo s).2)))
        simp only [Nat.mul_add]
        omega
      | some e =>
        have hen : nameBits e.1 ≤ K := hname _ (hTd e ((mem_treeList todo e).2 ⟨s, he⟩))
        have g₃ := O.symB_le e.1
        have g₃' := Nat.mul_le_mul_right (O.symF e.1) hen
        show 1 + ((tmaxC todo).2 + (tgetB todo s).2 + (teraseB todo s).2) + O.symB e.1 ≤
          3 * (K * (1 + ((tmaxC todo).2 + (tgetF todo s).2 + (teraseF todo s).2) +
            O.symF e.1))
        simp only [Nat.mul_add]
        omega
  | look a α =>
    have ha : nameBits a ≤ Kn := hTs a rfl
    have hp := hport (a, 0) (Nat.zero_le _) ha
    have g := O.nbB_le (a, 0)
    have g' := Nat.mul_le_mul_right (O.nbF (a, 0)) hp
    show 2 + O.nbB (a, 0) ≤ 3 * (K * (2 + O.nbF (a, 0)))
    simp only [Nat.mul_add]
    omega
  | seek a α p c =>
    have ha : nameBits a ≤ Kn := hTs a (.inl rfl)
    have hcn : nameBits c.1 ≤ Kn := hTs c.1 (.inr (.inr rfl))
    have hpc : nameBits (portKey c) ≤ K := hport c hports.2 hcn
    have g₁ := O.symB_le c.1
    have g₁' := Nat.mul_le_mul_right (O.symF c.1) (hname _ hcn)
    have g₂ := O.nbB_le c
    have g₂' := Nat.mul_le_mul_right (O.nbF c) hpc
    have g₃ := findBits_le p (K := K) (O.nb c)
      (fun q hq => Nat.le_trans (portB_le q p) (hnb c q hq))
    have g₄ : nameB a c.1 ≤ K := Nat.le_trans (cmpB_le a c.1) (hname _ ha)
    show ZMach.bcost xs O cnt ⟨todo, .seek a α p c⟩ ≤
      3 * (K * OMach.fcost xs O ⟨todo, .seek a α p c⟩)
    unfold ZMach.bcost OMach.fcost
    dsimp only
    by_cases h0 : c.2 = 0
    · rw [ite_pos' h0, ite_pos' h0]
      by_cases hs : (O.sym c.1).isSome = true
      · rw [ite_pos' hs, ite_pos' hs]
        simp only [Nat.mul_add]
        omega
      · rw [ite_neg' hs, ite_neg' hs]
        simp only [Nat.mul_add]
        omega
    · rw [ite_neg' h0, ite_neg' h0]
      simp only [Nat.mul_add]
      omega
  | ready a b α β =>
    have ha : nameBits a ≤ Kn := hTs a (.inl rfl)
    have g₁ := O.symB_le a
    have g₁' := Nat.mul_le_mul_right (O.symF a) (hname _ ha)
    have g₂ := O.takeB_le a (hname _ ha) (hlive a)
    show ZMach.bcost xs O cnt ⟨todo, .ready a b α β⟩ ≤
      3 * (K * OMach.fcost xs O ⟨todo, .ready a b α β⟩)
    unfold ZMach.bcost OMach.fcost
    dsimp only
    by_cases hs : O.sym a = some α
    · rw [ite_pos' hs, ite_pos' hs]
      simp only [Nat.mul_add]
      omega
    · rw [ite_neg' hs, ite_neg' hs]
      simp only [Nat.mul_add]
      omega
  | half a b α β =>
    have ha : nameBits a ≤ Kn := hTs a (.inl rfl)
    have hb : nameBits b ≤ Kn := hTs b (.inr rfl)
    have g₁ := O.symB_le b
    have g₁' := Nat.mul_le_mul_right (O.symF b) (hname _ hb)
    have g₂ := O.takeB_le b (hname _ hb) (hlive b)
    have g₃ := O.putB_le a α (hname _ ha) hst
    have g₄ : nameB a b ≤ K := Nat.le_trans (cmpB_le a b) (hname _ ha)
    unfold ZMach.bcost ZMach.fcost
    dsimp only
    by_cases h1 : O.sym b = some β
    · rw [ite_pos' h1]
      by_cases h2 : a ≠ b
      · rw [ite_pos' h2, ite_pos' (⟨h1, h2⟩ : O.sym b = some β ∧ a ≠ b)]
        cases hr : xs.rule α β with
        | none =>
          show 1 + O.symB b + (nameB a b + O.putB a α) ≤
            3 * (K * (1 + O.symF b + O.putF a α))
          simp only [Nat.mul_add] at g₃ ⊢
          omega
        | some R =>
          have hspan := hsp α β R hr
          have hl : lg (cnt + R.span) ≤ K := Nat.le_trans (lg_mono (by omega)) hcnt
          have g₅ := Nat.mul_le_mul_right
            (1 + (R.numAgents cnt).length + 2 * (R.numLinks xs.sys.ar a b cnt α β).length) hl
          have e : K * (1 + (R.numAgents cnt).length +
              2 * (R.numLinks xs.sys.ar a b cnt α β).length) =
              K * 1 + K * (R.numAgents cnt).length +
                2 * (K * (R.numLinks xs.sys.ar a b cnt α β).length) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm]
          have key : ∀ CB, CB ≤ K * (1 + (R.numAgents cnt).length +
                2 * (R.numLinks xs.sys.ar a b cnt α β).length) →
              1 + O.symB b + (nameB a b + (O.takeB b + CB)) ≤
                3 * (K * (1 + O.symF b + (O.takeF b + 1 + (R.numAgents cnt).length +
                  (R.numLinks xs.sys.ar a b cnt α β).length))) := by
            intro CB hCB
            rw [e] at hCB
            simp only [Nat.mul_add]
            omega
          exact key _ g₅
      · rw [ite_neg' h2, ite_neg' (fun h : O.sym b = some β ∧ a ≠ b => h2 h.2)]
        simp only [Nat.mul_add] at g₃ ⊢
        omega
    · rw [ite_neg' h1, ite_neg' (fun h : O.sym b = some β ∧ a ≠ b => h1 h.1)]
      simp only [Nat.mul_add] at g₃ ⊢
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have hi : nameBits i ≤ Kn := hTs i (.inl ⟨(i, γ), List.mem_cons_self, rfl⟩)
      have g := O.putB_le i γ (hname _ hi) hst
      show 1 + O.putB i γ ≤ 3 * (K * (1 + O.putF i γ))
      simp only [Nat.mul_add] at g ⊢
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have hpq := hports (p, q) List.mem_cons_self
        have hpn : nameBits p.1 ≤ Kn :=
          hTs p.1 (.inr ⟨(p, q), List.mem_cons_self, .inl rfl⟩)
        have hqn : nameBits q.1 ≤ Kn :=
          hTs q.1 (.inr ⟨(p, q), List.mem_cons_self, .inr rfl⟩)
        have g := O.linkB_le p q (hport p hpq.1 hpn) (hport q hpq.2 hqn)
        show 4 + O.linkB p q ≤ 3 * (K * (4 + O.linkF p q))
        simp only [Nat.mul_add] at g ⊢
        omega
      | nil =>
        show 1 ≤ 3 * (K * 1)
        omega

end BitBound

section BitRun

variable [DecidableEq S] {xs : XSys S}

/-- **Every name of the numbered program has a number of bits fixed before
the run.**  With `2 ^ W` above the bound on the counter, a name has at
most `max L 1` cells of `W + 1` bits each, and one. -/
theorem YMach.name_bits {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {Sp : Nat}
    (hsp : xs.SpanLe Sp) {nt : Nat} (hnt : 0 < nt) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {L W : Nat}
    (hL : X.NamesLe L) (hW : X.top + Sp * n < 2 ^ W) (σ : Nat → Nat) :
    ∀ i, ((YMach.init X nt).trace xs σ i).1.toX.All
      (fun j => nameBits j ≤ max L 1 * (W + 1) + 1)
  | 0 => by
    have hin : ∀ j ∈ X.names, j.length ≤ L → nameBits j ≤ max L 1 * (W + 1) + 1 :=
      fun j hj hl => nameBits_le j (Nat.le_trans hl (Nat.le_max_left _ _))
        (fun k hk => Nat.lt_trans
          (Nat.lt_of_lt_of_le (XNet.cell_lt_top hj hk) (Nat.le_add_right _ _)) hW)
    have hA : ∀ e ∈ X.agents, nameBits e.1 ≤ max L 1 * (W + 1) + 1 := fun e he =>
      hin _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.2 ⟨e, he, rfl⟩)))) (hL.1 e he)
    refine ⟨⟨hA, fun e he => ⟨?_, ?_⟩⟩, fun T hT => ?_⟩
    · exact hin _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩)))) (hL.2 e he).1
    · exact hin _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩))) (hL.2 e he).2
    · have hT' : T ∈ (List.range nt).map fun t =>
          (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S) := hT
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hT'
      refine ⟨fun e he => ?_, fun i hi => absurd hi id⟩
      have he' : e ∈ X.agents.drop u ++ X.agents.take u := he
      rcases List.mem_append.1 he' with h | h
      · exact hA e (List.mem_of_mem_drop h)
      · exact hA e (List.mem_of_mem_take h)
  | i + 1 => by
    have ih := YMach.name_bits hX hsp hnt hs hn hL hW σ i
    have hc := YMach.cnt_le hX hsp hnt hs hn σ (i + 1)
    refine YMach.step_all xs ih (σ i) (fun k _ hk => ?_)
    have hk' : k < 2 ^ W := Nat.lt_trans (Nat.lt_of_lt_of_le hk hc) hW
    have h1 := lg_le hk'
    have h2 : 1 * (W + 1) ≤ max L 1 * (W + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_max_right _ _)
    show lg k + 1 ≤ max L 1 * (W + 1) + 1
    omega

/-- **In bits, the action of a thread costs at most three times its count
times the bits of a key**, on a state whose numbers, names and ports are
bounded. -/
theorem ZMach.stepBcost_le (xs : XSys S) {Z : ZMach S} {H : TMem S} (hA : Z.mem.Agree H)
    (hk : H.Ok) (hsd : Z.Stamped) {K Kn P Sp : Nat} (hsp : xs.SpanLe Sp)
    (hcnt : lg (Z.cnt + Sp) ≤ K) (hst : lg Z.mem.stamp ≤ K)
    (hnames : Z.toY.toX.All (fun i => nameBits i ≤ Kn)) (hports : Z.toY.PortsLe P)
    (hK : lg P + Kn ≤ K) (t : Nat) :
    Z.stepBcost xs t ≤ 3 * (K * Z.stepFcost xs t) := by
  unfold ZMach.stepBcost ZMach.stepFcost
  cases hT : Z.ths[t]? with
  | none => exact Nat.zero_le _
  | some T =>
    have hTm : T ∈ Z.ths := List.mem_of_getElem? hT
    have hlive : ∀ (a : Id) (v : Nat × S), Z.mem.live[a]? = some v → lg v.1 ≤ K := by
      intro a v hv
      rw [hA.live a] at hv
      obtain ⟨s, γ⟩ := v
      have h1 := hk.lt s (a, γ) (hk.fwd a s γ hv)
      rw [← hA.stamp] at h1
      exact Nat.le_trans (lg_mono (Nat.le_of_lt h1)) hst
    have htodo : ∀ (s : Nat) v, T.todo[s]? = some v → lg s ≤ K := fun s v hv =>
      Nat.le_trans (lg_mono (Nat.le_of_lt (hsd.2 T hTm s v hv))) hst
    have hTn : T.toX.All (fun i => nameBits i ≤ Kn) :=
      hnames.2 T.toX (List.mem_map.2 ⟨T, hTm, rfl⟩)
    have hTp : T.st.PortsLe P := hports.2 T.toX (List.mem_map.2 ⟨T, hTm, rfl⟩)
    have hnb : ∀ c q, q ∈ Z.mem.nb c → nameBits (portKey q) ≤ K := by
      intro c q hq
      rw [hA.nb c, hk.nbrs c, ← hA.wires] at hq
      have hw := mem_nbOf _ hq
      have h1 : q.2 ≤ P := (hports.1 (c, q) hw).2
      have h2 : nameBits q.1 ≤ Kn := (hnames.1.2 (c, q) hw).2
      have h3 := lg_mono h1
      show lg q.2 + nameBits q.1 ≤ K
      omega
    exact ZMach.bcost_le xs Z.mem Z.cnt T hsp hcnt hst hlive htodo hTn hTp hnb hK

/-- **The time in bits is at most the count times the bits of a key, three
times over**, at every moment of every run.  `2 ^ W` is above the bound on
the counter one claim further and above the bound on the stamps; `P`
bounds the indices of the ports of the net and of the rules. -/
theorem ZMach.btime_le_ftime {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {Sp : Nat} (hsp : xs.SpanLe Sp) {P : Nat}
    (hp : xs.PortsLe P) (hXp : X.PortsLe P) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {L : Nat} (hL : X.NamesLe L) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    {W : Nat} (hW : X.top + Sp * (n + 1) < 2 ^ W)
    (hW' : X.agents.length + ((nt + n) * X.passBound n C D + n * (C + D + 1)) < 2 ^ W) :
    ∀ i, (ZMach.init X nt).btime xs σ i ≤
      3 * ((lg P + (max L 1 * (W + 1) + 1)) * (ZMach.init X nt).ftime xs σ i)
  | 0 => Nat.zero_le _
  | i + 1 => by
    have ih := ZMach.btime_le_ftime hX hnd hsp hp hXp hnt hb hL hs hn σ hW hW' i
    obtain ⟨a, -, H, hA, hk⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
    have hsd := ZMach.trace_stamped xs σ (ZMach.init_stamped X nt) i
    have hc := ZMach.cnt_le (xs := xs) hX hnd hsp hnt hs hn σ i
    have hstamp := ZMach.stamp_le (xs := xs) hX hnd hnt hb hs hn σ i
    have esp : Sp * (n + 1) = Sp * n + Sp := Nat.mul_succ Sp n
    have hW0 : X.top + Sp * n < 2 ^ W := by omega
    have hnames := YMach.name_bits (xs := xs) hX hsp hnt hs hn hL hW0 σ i
    rw [← a] at hnames
    have hports := YMach.ports_le hp hXp nt σ i
    rw [← a] at hports
    have h3 : 1 * (W + 1) ≤ max L 1 * (W + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_max_right _ _)
    have h4 := lg_pos P
    have hcnt : lg (((ZMach.init X nt).trace xs σ i).1.cnt + Sp) ≤
        lg P + (max L 1 * (W + 1) + 1) := by
      have h1 : ((ZMach.init X nt).trace xs σ i).1.cnt + Sp < 2 ^ W := by omega
      have h2 := lg_le h1
      omega
    have hst : lg ((ZMach.init X nt).trace xs σ i).1.mem.stamp ≤
        lg P + (max L 1 * (W + 1) + 1) := by
      have h2 := lg_le (Nat.lt_of_le_of_lt hstamp hW')
      omega
    have hstep := ZMach.stepBcost_le xs hA hk hsd hsp hcnt hst hnames hports
      (Nat.le_refl _) (σ i)
    show (ZMach.init X nt).btime xs σ i +
        ((ZMach.init X nt).trace xs σ i).1.stepBcost xs (σ i) ≤
      3 * ((lg P + (max L 1 * (W + 1) + 1)) * ((ZMach.init X nt).ftime xs σ i +
        ((ZMach.init X nt).trace xs σ i).1.stepFcost xs (σ i)))
    rw [Nat.mul_add]
    omega

/-- **A bound on the running time of the numbered program in bits,
whatever the schedule.**  The bound on the count, times three times the
bits of a key: `lg P` for the index of a port and `W + 1` for each of the
`max L 1` cells of a name. -/
theorem ZMach.btime_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {Sp : Nat} (hsp : xs.SpanLe Sp) {P : Nat}
    (hp : xs.PortsLe P) (hXp : X.PortsLe P) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {L : Nat} (hL : X.NamesLe L) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    {W : Nat} (hW : X.top + Sp * (n + 1) < 2 ^ W)
    (hW' : X.agents.length + ((nt + n) * X.passBound n C D + n * (C + D + 1)) < 2 ^ W)
    (i : Nat) :
    (ZMach.init X nt).btime xs σ i ≤
      3 * ((lg P + (max L 1 * (W + 1) + 1)) *
        (((nt + n) * X.passBound n C D + n * (C + D + 1)) *
          (C + D + 5 + 4 * ((max L 1 + 6) *
            (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))))) := by
  have h₁ := ZMach.btime_le_ftime (xs := xs) hX hnd hsp hp hXp hnt hb hL hs hn σ hW hW' i
  have h₂ := ZMach.ftime_bound (xs := xs) hX hnd hnt hb hL hs hn σ i
  exact Nat.le_trans h₁ (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ h₂))

end BitRun

theorem foldr_max_le : ∀ (l : List Nat) (b : Nat), (∀ x ∈ l, x ≤ b) → l.foldr max 0 ≤ b
  | [], _, _ => Nat.zero_le _
  | y :: l, b, h => by
    show max y (l.foldr max 0) ≤ b
    exact Nat.max_le.2 ⟨h y List.mem_cons_self,
      foldr_max_le l b (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

end INet
