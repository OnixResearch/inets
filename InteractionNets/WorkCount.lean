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

end WCount

end INet
