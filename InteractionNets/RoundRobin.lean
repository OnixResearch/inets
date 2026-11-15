import InteractionNets.ReadBack
import InteractionNets.Time

/-! # How many actions are enough, threads taking turns

Threads that take turns (the schedule `j ↦ j % nt`) come to rest
(`XMach.fair_complete`), and the theorem said nothing about when.  Here
the point is bounded: a run on a well-formed net, in which no agent is
listed twice, with a normal form `n` steps away and rules that write at
most `C` agents and `D` segments, is at rest after

    nt * ((nt + n) * X.passBound n C D + n * (C + D + 1) + 1)

actions (`XMach.roundRobin_rest`).

The count is that of `XMach.time_bound`, read differently.  There, a
measure goes down at every action that is not free, and a free action
changes nothing and costs nothing (`XMach.step_work`).  An action costs
nothing only for a thread at rest (`XThread.rest_of_cost`).  In a round
of `nt` actions in which the threads take turns and every action is free,
the state does not change and every thread rests, so the program is at
rest; and there are no more rounds with an action that is not free than
the measure at the start.
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- **An action that costs nothing is that of a thread at rest.** -/
theorem XThread.rest_of_cost {X : XNet S} {T : XThread S} (h : XMach.cost xs X T = 0) :
    (T.todo.isEmpty && T.st.isIdle) = true := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => rfl
    | cons e l =>
      unfold XMach.cost at h
      simp only at h
      omega
  | look a α =>
    unfold XMach.cost at h
    simp only at h
    omega
  | seek a α p c =>
    unfold XMach.cost at h
    simp only at h
    split at h <;> omega
  | ready a b α β =>
    unfold XMach.cost at h
    simp only at h
    omega
  | half a b α β =>
    unfold XMach.cost at h
    simp only at h
    omega
  | write l m =>
    cases l <;> cases m <;> (unfold XMach.cost at h; simp only at h; omega)

/-- A measure that never goes up, and goes down at every step that is not
free: from `a` on, `d` steps later it is no higher. -/
theorem measure_mono {Φ : Nat → Nat} (h : ∀ i, Φ (i + 1) ≤ Φ i) (a : Nat) :
    ∀ d, Φ (a + d) ≤ Φ a
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (h (a + d)) (measure_mono h a d)

/-- **Some round of `nt` steps among the first `P + 1` is free**, when a
measure that never goes up and starts at most at `P` goes down at every
step that is not free. -/
theorem free_round {Φ : Nat → Nat} {free : Nat → Prop} {nt P : Nat}
    (h : ∀ i, free i ∨ Φ (i + 1) < Φ i) (hm : ∀ i, Φ (i + 1) ≤ Φ i) (h0 : Φ 0 ≤ P) :
    ∃ k, k ≤ P ∧ ∀ u, u < nt → free (k * nt + u) := by
  apply Classical.byContradiction
  intro hno
  have hdrop : ∀ k, k ≤ P + 1 → Φ (k * nt) + k ≤ Φ 0 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hk' : ¬ ∀ u, u < nt → free (k * nt + u) := fun hall => hno ⟨k, by omega, hall⟩
      obtain ⟨u, hu, hnf⟩ : ∃ u, u < nt ∧ ¬ free (k * nt + u) := by
        apply Classical.byContradiction
        intro hc
        exact hk' fun u hu => Classical.byContradiction fun hf => hc ⟨u, hu, hf⟩
      have hlt := (h (k * nt + u)).resolve_left hnf
      have m1 := measure_mono hm (k * nt) u
      have m2 := measure_mono hm (k * nt + u + 1) (nt - u - 1)
      have e : k * nt + u + 1 + (nt - u - 1) = (k + 1) * nt := by
        rw [Nat.succ_mul]
        omega
      rw [e] at m2
      omega
  have := hdrop (P + 1) (Nat.le_refl _)
  omega

/-- **Threads that take turns are at rest after a bounded number of
actions.** -/
theorem XMach.roundRobin_rest {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') :
    ∀ i, nt * ((nt + n) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((XMach.init X nt).trace xs (fun j => j % nt) i).1.resting = true := by
  -- what `XMach.time_bound` knows about the run
  have live := XMach.trace_live (xs := xs) (fun j => j % nt) (XMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((XMach.init X nt).trace xs (fun j => j % nt) i).2
      (Mach.init X.toNet) ((XMach.init X nt).trace xs (fun j => j % nt) i).1.toMach := by
    intro i
    have h := XMach.trace_run xs (fun j => j % nt) (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((XMach.init X nt).trace xs (fun j => j % nt) i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  let K := X.wires.length + D * n
  let A := X.agents.length + C * n
  obtain ⟨is, ih⟩ := XMach.init_sizes X nt
  have sizes := XMach.seq_sizes (xs := xs) ((XMach.init X nt).trace xs (fun j => j % nt))
    (fun j => j % nt) (fun _ => rfl) live hb (W := X.wires.length) (A₀ := X.agents.length)
    ⟨Nat.le_trans (Nat.le_of_eq is) (Nat.le_add_right _ _),
      Nat.le_trans (Nat.le_of_eq ih) (Nat.le_add_right _ _)⟩
  have hA : ∀ i, ((XMach.init X nt).trace xs (fun j => j % nt) i).1.heads ≤ A :=
    fun i => Nat.le_trans (sizes i).2
      (Nat.add_le_add_left (Nat.mul_le_mul_left C (bound i)) _)
  have nd : ∀ i, (((XMach.init X nt).trace xs (fun j => j % nt) i).1.mem.agents.map
      Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact XMach.step_nodup (live i) ih (i % nt)
  have hH : N'.Sized K := XNet.normal_sized hX hb hs hn
  have ahead : ∀ i, ((XMach.init X nt).trace xs (fun j => j % nt) i).1.Ahead N' :=
    fun i => XMach.ahead_of_run (live i).inv hX (run i) hs hn
  -- the measure
  let Kc := C + D + 7 * A + K + 1
  let Φ : Nat → Nat := fun i =>
    ((XMach.init X nt).trace xs (fun j => j % nt) i).1.energyIn N' K A +
      (n - ((XMach.init X nt).trace xs (fun j => j % nt) i).2) * Kc
  let free : Nat → Prop := fun i =>
    (XMach.init X nt).trace xs (fun j => j % nt) (i + 1) =
        (XMach.init X nt).trace xs (fun j => j % nt) i ∧
      ((XMach.init X nt).trace xs (fun j => j % nt) i).1.stepCost xs (i % nt) = 0
  have dich : ∀ i, free i ∨ Φ (i + 1) < Φ i := by
    intro i
    have hb1 : ((XMach.init X nt).trace xs (fun j => j % nt) i).2 +
        (((XMach.init X nt).trace xs (fun j => j % nt) i).1.step xs (i % nt)).2 ≤ n :=
      bound (i + 1)
    have htr : (XMach.init X nt).trace xs (fun j => j % nt) (i + 1) =
        ((((XMach.init X nt).trace xs (fun j => j % nt) i).1.step xs (i % nt)).1,
          ((XMach.init X nt).trace xs (fun j => j % nt) i).2 +
            (((XMach.init X nt).trace xs (fun j => j % nt) i).1.step xs (i % nt)).2) := rfl
    rcases XMach.step_work (live i) (nd i) hb hH (ahead i) (hA i) (i % nt) with
      ⟨e, hz⟩ | ⟨h1, hce⟩ | ⟨h0, hlt⟩
    · refine .inl ⟨?_, hz⟩
      rw [htr, e, Nat.add_zero]
    · refine .inr ?_
      show (((XMach.init X nt).trace xs (fun j => j % nt) (i + 1)).1.energyIn N' K A +
          (n - ((XMach.init X nt).trace xs (fun j => j % nt) (i + 1)).2) * Kc) <
        ((XMach.init X nt).trace xs (fun j => j % nt) i).1.energyIn N' K A +
          (n - ((XMach.init X nt).trace xs (fun j => j % nt) i).2) * Kc
      rw [htr]
      dsimp only
      have e1 : n - ((XMach.init X nt).trace xs (fun j => j % nt) i).2 =
          (n - (((XMach.init X nt).trace xs (fun j => j % nt) i).2 +
            (((XMach.init X nt).trace xs (fun j => j % nt) i).1.step xs (i % nt)).2)) + 1 := by
        omega
      rw [e1, Nat.add_mul, Nat.one_mul]
      have : C + D + 7 * A + K < Kc := by
        show C + D + 7 * A + K < C + D + 7 * A + K + 1
        omega
      omega
    · refine .inr ?_
      show (((XMach.init X nt).trace xs (fun j => j % nt) (i + 1)).1.energyIn N' K A +
          (n - ((XMach.init X nt).trace xs (fun j => j % nt) (i + 1)).2) * Kc) <
        ((XMach.init X nt).trace xs (fun j => j % nt) i).1.energyIn N' K A +
          (n - ((XMach.init X nt).trace xs (fun j => j % nt) i).2) * Kc
      rw [htr]
      dsimp only
      rw [h0, Nat.add_zero]
      exact Nat.add_lt_add_right hlt _
  have mono : ∀ i, Φ (i + 1) ≤ Φ i := by
    intro i
    rcases dich i with ⟨e, -⟩ | hlt
    · show (((XMach.init X nt).trace xs (fun j => j % nt) (i + 1)).1.energyIn N' K A +
          (n - ((XMach.init X nt).trace xs (fun j => j % nt) (i + 1)).2) * Kc) ≤ _
      rw [e]
      exact Nat.le_refl _
    · exact Nat.le_of_lt hlt
  -- the measure at the start
  have h0 : Φ 0 ≤ (nt + n) * X.passBound n C D + n * (C + D + 1) := by
    have e0 := XMach.init_energyIn X nt N' K A
    obtain ⟨-, pr⟩ := Steps.links hX hs
    have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
    have hscan : N'.scan K X.agents ≤ 7 * X.agents.length + K :=
      Net.scan_le hH X.agents hnd fun e he q q' h h' =>
        hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
          (pr (.inl ⟨e.2, hag e he⟩) h')
    have hsc : nt * N'.scan K X.agents ≤ nt * X.passBound n C D :=
      Nat.mul_le_mul_left nt (Nat.le_trans hscan (by
        show 7 * X.agents.length + (X.wires.length + D * n) ≤
          7 * (X.agents.length + C * n) + (X.wires.length + D * n)
        omega))
    have e1 : Kc = X.passBound n C D + (C + D + 1) := by
      show C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1 =
        7 * (X.agents.length + C * n) + (X.wires.length + D * n) + (C + D + 1)
      omega
    show (XMach.init X nt).energyIn N' K A + (n - 0) * Kc ≤ _
    rw [Nat.sub_zero, e1, Nat.mul_add n (X.passBound n C D) (C + D + 1),
      Nat.add_mul nt n (X.passBound n C D)]
    omega
  -- a free round, and rest from then on
  obtain ⟨k, hk, hfree⟩ := free_round dich mono h0
  have same : ∀ u, u ≤ nt → (XMach.init X nt).trace xs (fun j => j % nt) (k * nt + u) =
      (XMach.init X nt).trace xs (fun j => j % nt) (k * nt) := by
    intro u
    induction u with
    | zero => intro _; rfl
    | succ u ih =>
      intro hu
      rw [← Nat.add_assoc, (hfree u (by omega)).1, ih (by omega)]
  have hlen : ((XMach.init X nt).trace xs (fun j => j % nt) (k * nt)).1.ths.length = nt := by
    rw [XMach.trace_length]
    show ((List.range nt).map _).length = nt
    rw [List.length_map, List.length_range]
  have rest : ((XMach.init X nt).trace xs (fun j => j % nt) (k * nt)).1.resting = true := by
    apply List.all_eq_true.2
    intro T hT
    obtain ⟨u, hu, hTu⟩ := List.getElem_of_mem hT
    rw [hlen] at hu
    have hc := (hfree u hu).2
    rw [same u (Nat.le_of_lt hu)] at hc
    have em : (k * nt + u) % nt = u := by
      rw [Nat.mul_comm, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hu
    rw [em] at hc
    unfold XMach.stepCost at hc
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hu), hTu] at hc
    exact XThread.rest_of_cost hc
  intro i hi
  have hki : k * nt ≤ i := by
    have := Nat.mul_le_mul_right nt hk
    rw [Nat.mul_comm nt] at hi
    have h2 : ((nt + n) * X.passBound n C D + n * (C + D + 1)) * nt + nt ≤ i := by
      rw [Nat.add_mul, Nat.one_mul] at hi
      exact hi
    omega
  obtain ⟨d, rfl⟩ : ∃ d, i = k * nt + d := ⟨i - k * nt, by omega⟩
  exact XMach.resting_trace _ rest d

/-! ### Enough fuel to read -/

/-- The segments that `followTo` goes along. -/
def XNet.trail (X : XNet S) : Nat → Port → Port → List (Port × Port)
  | 0, _, _ => []
  | fuel + 1, p, c =>
    match (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some _ => [(p, c)]
    | none =>
      match nextSeg X.wires c p with
      | some q => (p, c) :: XNet.trail X fuel c q
      | none => [(p, c)]

omit [DecidableEq S] in
/-- The trail is made of segments. -/
theorem XNet.trail_sub (X : XNet S) : ∀ (f : Nat) (p c : Port), (p, c) ∈ X.wires →
    ∀ x, x ∈ X.trail f p c → x ∈ X.wires
  | 0, _, _, _, _, h => absurd h List.not_mem_nil
  | f + 1, p, c, hpc, x, h => by
    unfold XNet.trail at h
    split at h
    · rw [List.mem_singleton.1 h]
      exact hpc
    · split at h
      · rename_i q hq
        rcases List.mem_cons.1 h with e | h'
        · rw [e]
          exact hpc
        · exact XNet.trail_sub X f c q (nextSeg_spec hq).1 x h'
      · rw [List.mem_singleton.1 h]
        exact hpc

omit [DecidableEq S] in
/-- Fuel for the length of the trail is enough. -/
theorem XNet.followTo_trail (X : XNet S) : ∀ {f : Nat} {p c : Port} {i : Id},
    X.followTo f p c = some i → X.followTo (X.trail f p c).length p c = some i
  | 0, _, _, _, h => by cases h
  | f + 1, p, c, i, h => by
    unfold XNet.followTo at h
    unfold XNet.trail
    split
    · rename_i γ hc
      rw [hc] at h
      show X.followTo 1 p c = some i
      unfold XNet.followTo
      rw [hc]
      exact h
    · rename_i hc
      rw [hc] at h
      dsimp only at h
      split
      · rename_i q hq
        rw [hq] at h
        have ih := XNet.followTo_trail X h
        show X.followTo ((X.trail f c q).length + 1) p c = some i
        unfold XNet.followTo
        rw [hc]
        dsimp only
        rw [hq]
        exact ih
      · rename_i hq
        rw [hq] at h
        cases h

omit [DecidableEq S] in
/-- No less fuel than the length of the trail is enough. -/
theorem XNet.trail_le (X : XNet S) : ∀ {f g : Nat} {p c : Port} {i i' : Id},
    X.followTo f p c = some i → X.followTo g p c = some i' → (X.trail f p c).length ≤ g
  | 0, _, _, _, _, _, h, _ => by cases h
  | f + 1, g, p, c, i, i', h, hg => by
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := by
      cases g with
      | zero => cases hg
      | succ g' => exact ⟨g', rfl⟩
    unfold XNet.followTo at h hg
    unfold XNet.trail
    split
    · show 1 ≤ g' + 1
      omega
    · rename_i hc
      rw [hc] at h hg
      dsimp only at h hg
      split
      · rename_i q hq
        rw [hq] at h hg
        show (X.trail f c q).length + 1 ≤ g' + 1
        have := XNet.trail_le X h hg
        omega
      · show 1 ≤ g' + 1
        omega

omit [DecidableEq S] in
/-- From every segment of the trail, fuel for the length of the trail is
enough. -/
theorem XNet.trail_reach (X : XNet S) : ∀ {f : Nat} {p c : Port} {i : Id},
    X.followTo f p c = some i → ∀ x, x ∈ X.trail f p c →
      ∃ g, g ≤ (X.trail f p c).length ∧ X.followTo g x.1 x.2 = some i
  | 0, _, _, _, h, _, _ => by cases h
  | f + 1, p, c, i, h, x, hx => by
    have ht := XNet.followTo_trail X h
    unfold XNet.followTo at h
    unfold XNet.trail at hx ⊢
    split at hx
    · rename_i γ hc
      rw [List.mem_singleton.1 hx]
      refine ⟨1, Nat.le_refl _, ?_⟩
      unfold XNet.followTo
      rw [hc]
      rw [hc] at h
      exact h
    · rename_i hc
      rw [hc] at h
      dsimp only at h
      split at hx
      · rename_i q hq
        rw [hq] at h
        rcases List.mem_cons.1 hx with e | hx'
        · rw [e]
          refine ⟨(X.trail f c q).length + 1, Nat.le_refl _, ?_⟩
          unfold XNet.trail at ht
          rw [hc] at ht
          dsimp only at ht
          rw [hq] at ht
          exact ht
        · obtain ⟨g, hg, hfo⟩ := XNet.trail_reach X h x hx'
          exact ⟨g, Nat.le_trans hg (Nat.le_succ _), hfo⟩
      · rename_i hq
        rw [hq] at h
        cases h

omit [DecidableEq S] in
/-- **The trail goes along no segment twice.** -/
theorem XNet.trail_nodup (X : XNet S) : ∀ {f : Nat} {p c : Port} {i : Id},
    X.followTo f p c = some i → (X.trail f p c).Nodup
  | 0, _, _, _, h => by cases h
  | f + 1, p, c, i, h => by
    have h₀ := h
    unfold XNet.followTo at h
    unfold XNet.trail
    split
    · exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
    · rename_i hc
      rw [hc] at h
      dsimp only at h
      split
      · rename_i q hq
        rw [hq] at h
        refine List.nodup_cons.2 ⟨fun hm => ?_, XNet.trail_nodup X h⟩
        obtain ⟨g, hg, hfo⟩ := XNet.trail_reach X h (p, c) hm
        have hle := XNet.trail_le X h₀ hfo
        unfold XNet.trail at hle
        rw [hc] at hle
        dsimp only at hle
        rw [hq] at hle
        simp only [List.length_cons] at hle
        omega
      · exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩

omit [DecidableEq S] in
/-- **Fuel for the segments of the memory is enough to follow a wire.** -/
theorem XNet.followTo_wires {X : XNet S} {f : Nat} {p c : Port} {i : Id}
    (hpc : (p, c) ∈ X.wires) (h : X.followTo f p c = some i) :
    X.followTo X.wires.length p c = some i :=
  XNet.followTo_mono (XNet.followTo_trail X h)
    (nodup_length_le _ _ (XNet.trail_nodup X h) (XNet.trail_sub X f p c hpc))

variable {ar : S → Nat} {zero succ : S}

/-- **Fuel for the segments of the memory and for the numeral is enough to
read it.** -/
theorem XNet.readNum_bounded (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF ar) :
    ∀ (k : Nat) (p : Port), Addition.IsNum ar zero succ X.toNet p k →
      X.readNum zero succ X.wires.length (k + 1) p = some k
  | 0, p, ⟨i, ⟨hp, _, v, x, wk⟩, hn⟩ => by
    have hv : assoc p X.wires = some v :=
      assoc_eq_of_unique wk.link_first fun q' hq' => hX.end_unique hp hq' wk.link_first
    have hz : (i, zero) ∈ X.agents := hn
    obtain ⟨f₁, hf₁⟩ := XNet.followTo_complete hX wk hz
    have hf₁' := XNet.followTo_wires (assoc_mem hv) hf₁
    have ha : assoc i X.agents = some zero :=
      assoc_eq_of_unique hz fun α' h' => hX.agent_fun h' hz
    unfold XNet.readNum
    rw [hv]
    dsimp only
    rw [hf₁']
    dsimp only
    rw [ha]
    dsimp only
    rw [ite_pos' rfl]
  | k + 1, p, ⟨i, ⟨hp, _, v, x, wk⟩, hs, j, hpj, hnj⟩ => by
    have hv : assoc p X.wires = some v :=
      assoc_eq_of_unique wk.link_first fun q' hq' => hX.end_unique hp hq' wk.link_first
    have hs' : (i, succ) ∈ X.agents := hs
    obtain ⟨f₁, hf₁⟩ := XNet.followTo_complete hX wk hs'
    have hf₁' := XNet.followTo_wires (assoc_mem hv) hf₁
    have ha : assoc i X.agents = some succ :=
      assoc_eq_of_unique hs' fun α' h' => hX.agent_fun h' hs'
    have h₂ := XNet.readNum_bounded hzs hX k (i, 1) ⟨j, hpj, hnj⟩
    unfold XNet.readNum
    rw [hv]
    dsimp only
    rw [hf₁']
    dsimp only
    rw [ha]
    dsimp only
    rw [ite_neg' (Ne.symm hzs), ite_pos' rfl, h₂]
    rfl

/-- The memory of the run never has more segments than the net and the
right-hand sides of the claims. -/
theorem XMach.trace_wires_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (i : Nat) : ((XMach.init X nt).trace xs σ i).1.mem.wires.length ≤ X.wires.length + D * n := by
  have live := XMach.trace_live (xs := xs) σ (XMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((XMach.init X nt).trace xs σ i).2
      (Mach.init X.toNet) ((XMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := XMach.trace_run xs σ (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((XMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  obtain ⟨is, ih⟩ := XMach.init_sizes X nt
  have sizes := XMach.seq_sizes (xs := xs) ((XMach.init X nt).trace xs σ) σ (fun _ => rfl) live
    hb (W := X.wires.length) (A₀ := X.agents.length)
    ⟨Nat.le_trans (Nat.le_of_eq is) (Nat.le_add_right _ _),
      Nat.le_trans (Nat.le_of_eq ih) (Nat.le_add_right _ _)⟩
  have h1 : ((XMach.init X nt).trace xs σ i).1.mem.wires.length ≤
      ((XMach.init X nt).trace xs σ i).1.segs := Nat.le_add_right _ _
  have h2 := Nat.le_trans (sizes i).1 (Nat.add_le_add_left (Nat.mul_le_mul_left D (bound i)) _)
  omega

/-- **How many actions are enough to run and read.**  Let the net reduce
to a normal form with the numeral `v₀` on the port `p`.  Threads that take
turns, run for at least the bound of `XMach.roundRobin_rest`, the
segments the memory can hold and the length of the numeral, return
`v₀`. -/
theorem XNet.runRead_bound (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') {p : Port} {v₀ : Nat}
    (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) (s : Nat)
    (h₁ : nt * ((nt + n) * X.passBound n C D + n * (C + D + 1) + 1) ≤ s)
    (h₂ : X.wires.length + D * n ≤ s) (h₃ : v₀ + 1 ≤ s) :
    XNet.runRead xs zero succ X p nt s = some v₀ := by
  have hr := XMach.roundRobin_rest hX hnd hnt hb hs hn s h₁
  have L := XMach.trace_live (fun j => j % nt) (XMach.init_live (xs := xs) hX hnt) s
  obtain ⟨q, hq⟩ := L.rest hr
  have r := XMach.trace_run xs (fun j => j % nt) (XMach.init X nt) s
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hq
  obtain ⟨e', -⟩ := (hu hs).2 hn
  have e'' : N' = ((XMach.init X nt).trace xs (fun j => j % nt) s).1.mem.toNet := e'
  have hW : ((XMach.init X nt).trace xs (fun j => j % nt) s).1.mem.toNet.WF xs.sys.ar := by
    rw [← e'']
    exact Steps.wf hX hs
  have hnum' : Addition.IsNum xs.sys.ar zero succ
      ((XMach.init X nt).trace xs (fun j => j % nt) s).1.mem.toNet p v₀ := by
    rw [← e'']
    exact hnum
  have hread := XNet.readNum_bounded hzs hW v₀ p hnum'
  have hwl := XMach.trace_wires_le hX hnt hb hs hn (fun j => j % nt) s
  unfold XNet.runRead
  rw [ite_pos' hr]
  exact XNet.readNum_mono (by omega) hread h₃

end INet
