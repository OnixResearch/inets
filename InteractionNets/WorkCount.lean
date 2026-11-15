import InteractionNets.WorkBound
import InteractionNets.Weighted

/-! # How many claims join interface ports is fixed by the start

`WMach.fair_bound` charges a pass for each claim of a rule that joins
interface ports, and takes how many there are along the run as a
hypothesis.  The goals along a run of the program form a reduction, each
claim a firing of the pair it claims, so the claims that join are firings
of weight `1` (`Rhs.weight`).  No reduction weighs more than one to the
normal form, and all those weigh the same (`wsteps_bounded`).  So any run
that comes to rest, with any schedule and any number of threads, tells how
many claims join on every run (`WMach.joined_le_rest`), and a run of one
thread can be evaluated.  `WMach.fair_bound_ref` then bounds every fair run
by the numbers read off one evaluated run. -/

namespace INet

variable {S : Type}

section WCount

variable [DecidableEq S] {xs : XSys S}

omit [DecidableEq S] in
/-- The test of the program for joining agrees with `Rhs.Joins`. -/
theorem XRhs.weight_toRhs {R : XRhs S} {ar : S → Nat} {α β : S}
    (hwf : R.toRhs.WF ar α β) : R.toRhs.weight = if R.joins ar α β then 1 else 0 := by
  have e : R.toRhs.Joins ↔ R.joins ar α β = true := by
    constructor
    · rintro ⟨x, y, hl, hx, hy⟩
      cases x with
      | new o j k => exact absurd trivial hx
      | ifc s k =>
        cases y with
        | new o j k' => exact absurd trivial hy
        | ifc s' k' =>
          have hv : k < ar (sel α β s) := hwf.valid hl
          have hmem : LPort.ifc s k ∈ ifcPorts ar α β := mem_ifcPorts.2 ⟨s, k, rfl, hv⟩
          have hw : R.wire (.ifc s k) = some (.ifc s' k') := hl
          unfold XRhs.joins
          rw [List.any_eq_true]
          exact ⟨_, hmem, by rw [hw]; rfl⟩
    · intro h
      unfold XRhs.joins at h
      obtain ⟨x, hx, hy⟩ := List.any_eq_true.1 h
      obtain ⟨s, k, rfl, -⟩ := mem_ifcPorts.1 hx
      cases hw : R.wire (.ifc s k) with
      | none =>
        rw [hw] at hy
        cases hy
      | some y =>
        rw [hw] at hy
        refine ⟨.ifc s k, y, hw, fun h => h, ?_⟩
        cases y with
        | ifc s' k' => exact fun h => h
        | new o j k' => cases hy
  unfold Rhs.weight
  by_cases hj : R.joins ar α β = true
  · simp [hj, e.2 hj]
  · simp [hj, show ¬ R.toRhs.Joins from fun h' => hj (e.1 h')]

theorem WSteps.tail {A : Type} {r : Nat → A → A → Prop} {n w v : Nat} {a b c : A}
    (s : WSteps r n w a b) (h : r v b c) : WSteps r (n + 1) (w + v) a c := by
  induction s generalizing c with
  | refl a =>
    have := WSteps.head h (.refl c)
    rw [Nat.add_zero] at this
    rw [Nat.zero_add, Nat.zero_add]
    exact this
  | head st _ ih =>
    have h' := WSteps.head st (ih h)
    rw [← Nat.add_assoc] at h'
    exact h'

/-- **The goals along a run form a reduction**, as many steps as claims,
weighing as many as the claims that join interface ports. -/
theorem WMach.trace_wsteps {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) : ∀ i, WSteps (WStep xs.sys) ((WMach.init X nt).trace xs σ i).2
      (WMach.joined xs σ (WMach.init X nt) i) X.toNet
      ((WMach.init X nt).trace xs σ i).1.toMach.goal
  | 0 => by
    have e : (WMach.init X nt).toMach.goal = X.toNet := by
      rw [WMach.init_toMach]
      exact congrArg CState.goal (Mach.init_quiet X.toNet).abs
    show WSteps (WStep xs.sys) 0 0 X.toNet (WMach.init X nt).toMach.goal
    rw [e]
    exact .refl _
  | i + 1 => by
    have ih := WMach.trace_wsteps hX hnt σ i
    have live := WMach.trace_live (xs := xs) σ (WMach.init_live hX hnt) i
    show WSteps (WStep xs.sys)
      (((WMach.init X nt).trace xs σ i).2 + (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).2)
      (WMach.joined xs σ (WMach.init X nt) i +
        WMach.stepJoins xs ((WMach.init X nt).trace xs σ i).1 (σ i)) X.toNet
      (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toMach.goal
    rcases WMach.step_goal live (σ i) with ⟨h0, eg, -, j0⟩ |
      ⟨a, b, α, β, R, hR, h1, rg, eg, -, -, ej⟩
    · rw [h0, j0, eg, Nat.add_zero, Nat.add_zero]
      exact ih
    · rw [h1, ej, eg]
      refine ih.tail ⟨a, b, α, β, R.toRhs, rg, rfl, ?_⟩
      exact (XRhs.weight_toRhs (xs.sys.rule_wf rg.rule)).symm

/-- **A run that comes to rest tells how many claims join on every run**:
no run, with any schedule and any number of threads, makes more claims of
rules that join interface ports. -/
theorem WMach.joined_le_rest {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt nt' : Nat}
    (hnt : 0 < nt) (hnt' : 0 < nt') {σ' : Nat → Nat} {j : Nat}
    (hr : ((WMach.init X nt').trace xs σ' j).1.resting = true) (σ : Nat → Nat) (i : Nat) :
    WMach.joined xs σ (WMach.init X nt) i ≤ WMach.joined xs σ' (WMach.init X nt') j := by
  have live := WMach.trace_live (xs := xs) σ' (WMach.init_live hX hnt') j
  obtain ⟨hq, hnorm⟩ := live.rest hr
  have eg : ((WMach.init X nt').trace xs σ' j).1.toMach.goal =
      ((WMach.init X nt').trace xs σ' j).1.mem.toNet := congrArg CState.goal hq.abs
  have s := WMach.trace_wsteps hX hnt' σ' j
  rw [eg] at s
  exact wsteps_bounded hX s hnorm (WMach.trace_wsteps hX hnt σ i)

/-- A run that comes to rest has reached the normal form in as many steps
as it made claims. -/
theorem WMach.rest_steps {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {σ : Nat → Nat} {j : Nat} (hr : ((WMach.init X nt).trace xs σ j).1.resting = true) :
    Steps (Step xs.sys) ((WMach.init X nt).trace xs σ j).2 X.toNet
        ((WMach.init X nt).trace xs σ j).1.mem.toNet ∧
      Normal (Step xs.sys) ((WMach.init X nt).trace xs σ j).1.mem.toNet := by
  have live := WMach.trace_live (xs := xs) σ (WMach.init_live hX hnt) j
  obtain ⟨hq, hnorm⟩ := live.rest hr
  have run := WMach.trace_run xs σ (WMach.init X nt) j
  rw [WMach.init_toMach] at run
  exact ⟨(run.final hX hq hnorm).1, hnorm⟩

/-- **A bound on every fair run from one evaluated run.**  Run the program
once, with any schedule, until it rests; read off the claims `n` and the
claims `m` of rules that join interface ports.  Then every fair run, with
any number of threads and window `F`, is at rest with the same normal form
after `F * (B + 1)` actions, with `B` as in `WMach.fair_bound`. -/
theorem WMach.fair_bound_ref {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D)
    {nt' : Nat} (hnt' : 0 < nt') {σ' : Nat → Nat} {j : Nat}
    (hr : ((WMach.init X nt').trace xs σ' j).1.resting = true)
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((7 * X.agents.length + (X.wires.length +
            D * ((WMach.init X nt').trace xs σ' j).2)) +
          ((WMach.init X nt').trace xs σ' j).2 * (C + D + 1) +
          WMach.joined xs σ' (WMach.init X nt') j *
            (7 * (X.agents.length + (C - 2) * ((WMach.init X nt').trace xs σ' j).2) +
              (X.wires.length + D * ((WMach.init X nt').trace xs σ' j).2)) +
          (7 * (C * ((WMach.init X nt').trace xs σ' j).2) +
            (X.wires.length + D * ((WMach.init X nt').trace xs σ' j).2)) + 1) ≤ i →
      ((WMach.init X nt).trace xs σ i).1.resting = true ∧
      ((WMach.init X nt).trace xs σ i).2 = ((WMach.init X nt').trace xs σ' j).2 ∧
      ((WMach.init X nt).trace xs σ i).1.mem.toNet =
        ((WMach.init X nt').trace xs σ' j).1.mem.toNet := by
  obtain ⟨hs, hn⟩ := WMach.rest_steps hX hnt' hr
  exact WMach.fair_bound hX hnd hnt hb hs hn σ hfair
    fun i => WMach.joined_le_rest hX hnt hnt' hr σ i

/-! ### Counting the joining claims by a census of agents

In some systems a symbol counts the joining claims to come: each rule
takes as many agents of it out as it writes back, except a rule that joins
interface ports, which takes one more.  For unary addition, `add` is such
a symbol: `0 + y` removes its adder, `S x + y` replaces it.  Then the
agents of that symbol in the goal, plus the joining claims so far, never
change, and the joining claims are at most the agents of that symbol at
the start. -/

/-- How many agents of symbol `κ` a thread holds or has still to write. -/
def TState.kc (κ : S) : TState S → Nat
  | .half _ _ α _ => if α = κ then 1 else 0
  | .write as _ => as.countP fun e => decide (e.2 = κ)
  | _ => 0

/-- The agents of symbol `κ` in the goal: in memory, held, or still to be
written. -/
def WMach.census (κ : S) (M : WMach S) : Nat :=
  M.mem.agents.countP (fun e => decide (e.2 = κ)) +
    total (fun T => T.st.kc κ) (M.ths.map WThread.toX)

omit [DecidableEq S] in
theorem countP_takeAgent [DecidableEq S] {L : List (Id × S)} {a : Id} {α κ : S}
    (hm : (a, α) ∈ L) (hnd : (L.map Prod.fst).Nodup) :
    (L.filter fun e => decide (e.1 ≠ a)).countP (fun e => decide (e.2 = κ)) +
      (if α = κ then 1 else 0) = L.countP fun e => decide (e.2 = κ) := by
  induction L with
  | nil => exact absurd hm List.not_mem_nil
  | cons e L ih =>
    obtain ⟨hnin, hnd'⟩ := List.nodup_cons.1 hnd
    rcases List.mem_cons.1 hm with rfl | hm'
    · have hL : L.filter (fun e => decide (e.1 ≠ a)) = L := by
        refine List.filter_eq_self.2 fun x hx => ?_
        simp only [decide_eq_true_eq]
        intro ex
        exact hnin (List.mem_map.2 ⟨x, hx, ex⟩)
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ite_false, hL, List.countP_cons]
      by_cases h : α = κ <;> simp [h]
    · have hea : e.1 ≠ a := by
        intro ex
        exact hnin (List.mem_map.2 ⟨(a, α), hm', ex.symm ▸ rfl⟩)
      have ih' := ih hm' hnd'
      simp only [List.filter_cons, ne_eq, hea, not_false_eq_true, decide_true, ite_true,
        List.countP_cons] at ih' ⊢
      omega

/-- An action changes the agents of `κ` in the goal only by a claim of a
rule that joins interface ports, which takes one out, if every rule takes
out as many agents of `κ` as it writes, but for one when it joins. -/
theorem WMach.act_census {κ : S}
    (hk : ∀ α β R a b, a ≠ b → xs.rule α β = some R →
      (R.newAgents a b).countP (fun e => decide (e.2 = κ)) +
        (if R.joins xs.sys.ar α β then 1 else 0) =
        (if α = κ then 1 else 0) + (if β = κ then 1 else 0))
    {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (T : WThread S) :
    (WMach.act xs X T).1.agents.countP (fun e => decide (e.2 = κ)) +
        (WMach.act xs X T).2.1.st.kc κ + (if WMach.actJoins xs X T then 1 else 0) =
      X.agents.countP (fun e => decide (e.2 = κ)) + T.st.kc κ := by
  obtain ⟨todo, s, again⟩ := T
  have still : ∀ {T₁ : WThread S}, WMach.act xs X ⟨todo, s, again⟩ = (X, T₁, 0) →
      T₁.st.kc κ = s.kc κ → WMach.actJoins xs X ⟨todo, s, again⟩ = false →
      (WMach.act xs X ⟨todo, s, again⟩).1.agents.countP (fun e => decide (e.2 = κ)) +
          (WMach.act xs X ⟨todo, s, again⟩).2.1.st.kc κ +
          (if WMach.actJoins xs X ⟨todo, s, again⟩ then 1 else 0) =
        X.agents.countP (fun e => decide (e.2 = κ)) + s.kc κ := by
    intro T₁ e h₁ h₂
    rw [e, h₂]
    dsimp only
    rw [h₁]
    rfl
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
      have h := countP_takeAgent (κ := κ) (assoc_mem ha) hnd
      show (X.takeAgent a).agents.countP _ + (if α = κ then 1 else 0) + 0 = _ + 0
      exact h
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
      have ej : WMach.actJoins xs X ⟨todo, .half a b α β, again⟩ = R.joins xs.sys.ar α β := by
        unfold WMach.actJoins
        dsimp only
        rw [hh]
      rw [ej]
      have h1 := countP_takeAgent (κ := κ) (assoc_mem hc.1) hnd
      have h2 := hk α β R a b hc.2 hR
      show (X.takeAgent b).agents.countP _ + (R.newAgents a b).countP _ +
          (if R.joins xs.sys.ar α β then 1 else 0) = _ + (if α = κ then 1 else 0)
      have : (X.takeAgent b).agents = X.agents.filter fun e => decide (e.1 ≠ b) := rfl
      rw [this]
      omega
    | none =>
      rw [WMach.act_lift (fun _ _ h => by cases h) (XMach.act_half_none (todo := todo) hh)]
      have ej : WMach.actJoins xs X ⟨todo, .half a b α β, again⟩ = false := by
        unfold WMach.actJoins
        dsimp only
        rw [hh]
      rw [ej]
      show (X.putAgent a α).agents.countP _ + 0 + 0 = _ + (if α = κ then 1 else 0)
      show ((a, α) :: X.agents).countP _ + 0 + 0 = _
      rw [List.countP_cons]
      by_cases h : α = κ <;> simp [h]
  | write as ls =>
    cases ls with
    | cons e ls =>
      obtain ⟨p, q⟩ := e
      rfl
    | nil =>
      cases as with
      | cons e as =>
        obtain ⟨i, γ⟩ := e
        show ((i, γ) :: X.agents).countP _ + as.countP _ + 0 =
          _ + ((i, γ) :: as).countP _
        rw [List.countP_cons, List.countP_cons]
        omega
      | nil =>
        have ej : WMach.actJoins xs X ⟨todo, .write [] [], again⟩ = false := rfl
        rw [ej]
        unfold WMach.act
        dsimp only
        split <;> rfl

/-- **The census plus the joining claims never changes** along a run. -/
theorem WMach.trace_census {κ : S}
    (hk : ∀ α β R a b, a ≠ b → xs.rule α β = some R →
      (R.newAgents a b).countP (fun e => decide (e.2 = κ)) +
        (if R.joins xs.sys.ar α β then 1 else 0) =
        (if α = κ then 1 else 0) + (if β = κ then 1 else 0))
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup)
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, WMach.joined xs σ (WMach.init X nt) i +
        ((WMach.init X nt).trace xs σ i).1.census κ =
      X.agents.countP fun e => decide (e.2 = κ)
  | 0 => by
    show 0 + (X.agents.countP _ + total (fun T => T.st.kc κ)
      (((List.range nt).map fun t =>
        (⟨X.agents.drop t ++ X.agents.take t, .idle, false⟩ : WThread S)).map WThread.toX)) = _
    have h0 : total (fun T : XThread S => T.st.kc κ)
        (((List.range nt).map fun t =>
          (⟨X.agents.drop t ++ X.agents.take t, .idle, false⟩ : WThread S)).map
            WThread.toX) = 0 := by
      rw [List.map_map]
      generalize (List.range nt) = L
      induction L with
      | nil => rfl
      | cons x L ih =>
        show 0 + total _ _ = 0
        rw [Nat.zero_add]
        exact ih
    rw [h0]
    omega
  | i + 1 => by
    have ih := WMach.trace_census hk hX hnd hnt σ i
    have live := WMach.trace_live (xs := xs) σ (WMach.init_live hX hnt) i
    have nd : (((WMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
      clear ih live
      induction i with
      | zero => exact hnd
      | succ i ih' =>
        exact WMach.step_nodup (WMach.trace_live σ (WMach.init_live hX hnt) i) ih' (σ i)
    show WMach.joined xs σ (WMach.init X nt) i +
        WMach.stepJoins xs ((WMach.init X nt).trace xs σ i).1 (σ i) +
        (((WMach.init X nt).trace xs σ i).1.step xs (σ i)).1.census κ = _
    rw [← ih]
    generalize ((WMach.init X nt).trace xs σ i).1 = M at nd ⊢
    unfold WMach.stepJoins
    cases ht : M.ths[σ i]? with
    | none =>
      have e : M.step xs (σ i) = (M, 0) := by
        unfold WMach.step
        rw [ht]
      rw [e]
      dsimp only
      omega
    | some T =>
      dsimp only
      have es := WMach.step_eq (xs := xs) ht (rfl : WMach.act xs M.mem T =
        ((WMach.act xs M.mem T).1, (WMach.act xs M.mem T).2.1, (WMach.act xs M.mem T).2.2))
      rw [es]
      have ha := WMach.act_census hk nd T
      have hto := total_map_set (fun T : XThread S => T.st.kc κ) M.ths (σ i) T
        (WMach.act xs M.mem T).2.1 ht
      show (WMach.joined xs σ (WMach.init X nt) i +
          (if WMach.actJoins xs M.mem T then 1 else 0)) +
          ((WMach.act xs M.mem T).1.agents.countP (fun e => decide (e.2 = κ)) +
            total (fun T => T.st.kc κ)
              ((M.ths.set (σ i) (WMach.act xs M.mem T).2.1).map WThread.toX)) =
        WMach.joined xs σ (WMach.init X nt) i +
          (M.mem.agents.countP (fun e => decide (e.2 = κ)) +
            total (fun T => T.st.kc κ) (M.ths.map WThread.toX))
      have e1 : (T.toX).st = T.st := rfl
      have e2 : ((WMach.act xs M.mem T).2.1.toX).st = (WMach.act xs M.mem T).2.1.st := rfl
      simp only [e1, e2] at hto
      omega

/-- **The joining claims are at most the agents of `κ` at the start**, on
every run, if every rule takes out as many agents of `κ` as it writes, but
for one when it joins interface ports. -/
theorem WMach.joined_le_census {κ : S}
    (hk : ∀ α β R a b, a ≠ b → xs.rule α β = some R →
      (R.newAgents a b).countP (fun e => decide (e.2 = κ)) +
        (if R.joins xs.sys.ar α β then 1 else 0) =
        (if α = κ then 1 else 0) + (if β = κ then 1 else 0))
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup)
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    WMach.joined xs σ (WMach.init X nt) i ≤ X.agents.countP fun e => decide (e.2 = κ) := by
  have := WMach.trace_census hk hX hnd hnt σ i
  omega

end WCount

end INet
