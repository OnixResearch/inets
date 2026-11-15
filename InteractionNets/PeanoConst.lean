import InteractionNets.PeanoGExpr

/-! # Any constant on a zero

The theorems on recursion take what the agent does on a zero as a
hypothesis (`Peano.Zero1`, `Peano.Zero2`), and three rules were proved to
meet it: those of the multiplier, the power and the factorial, which put
`0` or `1` on the result.  Here any rule that puts a numeral `k` on the
result is proved to meet it, for one argument (`Peano.zero1_const`) and,
erasing the second argument, for two (`Peano.zero2_const`).

The rule is any rule data that passes checks which are bounded by `k`
and evaluated for a given rule (`Peano.ConstRule`, `Peano.EraRule`): the
new agents `0, …, k - 1` are successors, each on the next, the new agent
`k` is a zero, the result is on the new agent `0`, and there are no other
new agents but the eraser.  The three rules are cases
(`Peano.zero1_facZero'`, `Peano.zero2_mulZero'`, `Peano.zero2_powZero'`).

The test is a new agent whose rule on a zero puts down `0`, which no
other agent of one argument does: the triangular numbers `tri`
(`Peano.tri_computes`), proved by the theorems on recursion and on
constants alone, and on the machine by the theorems for operators
(`Peano.tri_rest`, `Peano.tri_fair`).
-/

namespace INet

namespace Peano

open Addition (gone gone2)

/-- **A rule that puts the numeral `k` on the result**: the new agents
`0, …, k - 1` are successors, each with its argument on the next, the new
agent `k` is a zero, and the interface port `res` is wired to the new
agent `0`.  Every field is evaluated for a given rule. -/
structure ConstRule (R : RuleData Peano) (res k : Nat) : Prop where
  succs : ∀ j, j < k → assoc ((some false : Option Bool), j) R.agents = some succ
  last : assoc ((some false : Option Bool), k) R.agents = some zero
  links : ∀ j, j < k →
    assoc (LPort.new (some false) j 1) R.wires = some (LPort.new (some false) (j + 1) 0)
  out : assoc (LPort.ifc false res) R.wires = some (LPort.new (some false) 0 0)

/-- **The rule also erases the second argument**: the new agent
`(some true, 0)` is an eraser, on the interface port `0`. -/
structure EraRule (R : RuleData Peano) : Prop where
  era : assoc ((some true : Option Bool), 0) R.agents = some era
  link : assoc (LPort.ifc false 0) R.wires = some (LPort.new (some true) 0 0)

/-- The names of the numeral the rule makes. -/
def constIds (a z : Id) (k : Nat) : List Id := (List.range' 0 (k + 1)).map (child a z (some false))

/-- **After the firing, the new agents of the rule are the numeral `k`**,
from the agent `k - d` on. -/
theorem const_chain {op : Peano} {R : RuleData Peano} {res k : Nat} (C : ConstRule R res k)
    (hR : R.toX.toRhs.WF ar op zero) {N : Net Peano} {a z : Id} (hA : Addition.Adder ar op N a z zero) :
    ∀ d, d ≤ k → NumList (N.fire a z R.toX.toRhs) (child a z (some false) (k - d))
      ((List.range' (k - d) (d + 1)).map (child a z (some false)))
  | 0, _ => by
    rw [Nat.sub_zero]
    exact .last (.inr ⟨some false, k, rfl, C.last⟩)
  | d + 1, hd => by
    have hj : k - (d + 1) < k := by omega
    have e : k - (d + 1) + 1 = k - d := by omega
    have hl := const_chain C hR hA d (by omega)
    have hp : (N.fire a z R.toX.toRhs).Paired ar (child a z (some false) (k - (d + 1)), 1)
        (child a z (some false) (k - d), 0) := by
      have h := Site.paired_fire_new_new (a := a) (b := z) (N := N) hR
        (show R.toX.toRhs.link (.new (some false) (k - (d + 1)) 1)
          (.new (some false) (k - (d + 1) + 1) 0) from C.links _ hj)
      rw [e] at h
      exact h
    rw [List.range'_succ, List.map_cons, e]
    exact .next (.inr ⟨some false, k - (d + 1), rfl, C.succs _ hj⟩) hp hl

theorem constIds_numList {op : Peano} {R : RuleData Peano} {res k : Nat} (C : ConstRule R res k)
    (hR : R.toX.toRhs.WF ar op zero) {N : Net Peano} {a z : Id}
    (hA : Addition.Adder ar op N a z zero) :
    NumList (N.fire a z R.toX.toRhs) (child a z (some false) 0) (constIds a z k) := by
  have h := const_chain C hR hA k (Nat.le_refl k)
  rw [Nat.sub_self] at h
  exact h

theorem constIds_length (a z : Id) (k : Nat) : (constIds a z k).length = k + 1 := by
  rw [constIds, List.length_map, List.length_range']

theorem mem_constIds {a z i : Id} {k : Nat} (h : i ∈ constIds a z k) :
    ∃ j, j ≤ k ∧ i = child a z (some false) j := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  obtain ⟨t, ht, e⟩ := List.mem_range'.1 hj
  exact ⟨j, by omega, rfl⟩

/-- **Any rule that puts the numeral `k` on the result** of an agent of
one argument, and makes nothing else, meets the hypothesis on a zero. -/
theorem zero1_const {op : Peano} {R : RuleData Peano} {k : Nat}
    (hr : system.rule op zero = some R.toX.toRhs) (h0 : zero ≠ op) (C : ConstRule R 0 k)
    (hall : ∀ e ∈ R.agents, e.1.1 = some false ∧ e.1.2 ≤ k) : Zero1 op k 1 := by
  intro N a z r hN ha hps hz hpx hr'
  have hA : Addition.Adder ar op N a z zero := ⟨hN, ha, hz, h0, hps⟩
  have hR : R.toX.toRhs.WF ar op zero := system.rule_wf hr
  have red : Redex system N a z op zero R.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, hr⟩
  have st : Step system N (N.fire a z R.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  refine ⟨_, .single st, ⟨child a z (some false) 0, constIds a z k,
    hA.site.paired_fire_ifc_new hR
      (show R.toX.toRhs.link (.ifc false 0) (.new (some false) 0 0) from C.out)
      (hpx.symm hN) hr'.1 hr'.2,
    constIds_numList C hR hA, constIds_length a z k, ?_⟩, (hA.site.keeps _).mono ?_, ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := mem_constIds hi
    exact hA.site.not_used_child _ _
  · rintro i (e1 | e1)
    · exact .inl e1
    · exact .inr (.inl (by
        rw [e1]
        exact List.mem_cons_self))
  · rintro i γ (⟨hi, h1, -⟩ | ⟨o, j, -, hlab⟩)
    · exact .inr (.inr ⟨hi, h1⟩)
    · have hlab' : assoc (o, j) R.agents = some γ := hlab
      obtain ⟨ho, hj⟩ := hall _ (assoc_mem hlab')
      simp only at ho hj
      subst ho
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · rw [C.succs j hlt] at hlab'
        exact .inr (.inl (Option.some.inj hlab').symm)
      · subst heq
        rw [C.last] at hlab'
        exact .inl (Option.some.inj hlab').symm

/-- **Any rule that puts the numeral `k` on the result** of an agent of
two arguments, erases the second argument and makes nothing else, meets
the hypothesis on a zero. -/
theorem zero2_const {op : Peano} {R : RuleData Peano} {k : Nat}
    (hr : system.rule op zero = some R.toX.toRhs) (h0 : zero ≠ op) (h1 : succ ≠ op)
    (C : ConstRule R 1 k) (E : EraRule R)
    (hall : ∀ e ∈ R.agents, (e.1.1 = some false ∧ e.1.2 ≤ k) ∨ e.1 = (some true, 0)) :
    Zero2 op (fun _ => k) (fun n => n + 1 + 1) := by
  intro N p s h₂ l₂ r n hN hp hps hz hpt hl₂ hpx hr' hlen₂
  obtain ⟨hrp, hrs, hrl₂⟩ := hr'
  have hru : N.Used r.1 := Net.End.used hpx.2.1
  have hA : Addition.Adder ar op N p s zero := ⟨hN, hp, hz, h0, hps⟩
  have hta : h₂ ≠ p := by
    rcases hl₂.label h₂ hl₂.head_mem with hx' | hx'
    · exact ne_of_agent hN hx' hp h0
    · exact ne_of_agent hN hx' hp h1
  have hts : h₂ ≠ s := hA.not_s hpt (port_ne_snd (by decide))
  have hav : ∀ j, j ∈ l₂ → ¬ (j = p ∨ j = s) := by
    intro j hj hc
    rcases hc with e1 | e1
    · rw [e1] at hj
      rcases hl₂.label p hj with hx' | hx'
      · exact h0 (hN.agent_fun hx' hp)
      · exact h1 (hN.agent_fun hx' hp)
    · rw [e1] at hj
      exact Addition.NumList.not_mem hN hps hl₂ hpt (port_ne_snd (by decide)) hj
  -- the firing
  have hR : R.toX.toRhs.WF ar op zero := system.rule_wf hr
  have red : Redex system N p s op zero R.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, hr⟩
  have st : Step system N (N.fire p s R.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN₁ := Step.wf hN st
  have k₁ : N.Keeps ar (fun i => i = p ∨ i = s) (N.fire p s R.toX.toRhs) := hA.site.keeps _
  have hused : ∀ i, N.Used i → (N.fire p s R.toX.toRhs).Used i :=
    fun i hu => Net.used_fire hN hu _ _ _
  have hE : ¬ N.Used (child p s (some true) 0) := hA.site.not_used_child _ _
  have aE : (N.fire p s R.toX.toRhs).agent (child p s (some true) 0) era :=
    .inr ⟨some true, 0, rfl, E.era⟩
  have pxU : (N.fire p s R.toX.toRhs).Paired ar r (child p s (some false) 0, 0) :=
    hA.site.paired_fire_ifc_new hR
      (show R.toX.toRhs.link (.ifc false 1) (.new (some false) 0 0) from C.out)
      (hpx.symm hN) hrp hrs
  have pEt : (N.fire p s R.toX.toRhs).Paired ar (child p s (some true) 0, 0) (h₂, 0) :=
    (hA.site.paired_fire_ifc_new hR
      (show R.toX.toRhs.link (.ifc false 0) (.new (some true) 0 0) from E.link)
      (hpt.symm hN) hta hts).symm hN₁
  have hnl := constIds_numList C hR hA
  -- the erasure
  have hl₂₁ := hl₂.keeps k₁ hav
  obtain ⟨N₂, sts, k₂, hag₂⟩ := erase l₂ hN₁ aE pEt hl₂₁
  rw [hlen₂] at sts
  have ngc : ∀ i, i ∈ constIds p s k → ¬ gone (N.fire p s R.toX.toRhs) (child p s (some true) 0)
      l₂ i := by
    intro i hi
    have hu : ¬ N.Used i := by
      obtain ⟨j, -, rfl⟩ := mem_constIds hi
      exact hA.site.not_used_child _ _
    refine not_gone ?_ (fun hm => hu (numList_used hl₂ hm)) ?_
    · rcases hnl.label i hi with h | h
      · exact ne_of_agent hN₁ h aE (by decide)
      · exact ne_of_agent hN₁ h aE (by decide)
    · rcases hnl.label i hi with h | h
      · exact .inl ⟨_, h⟩
      · exact .inl ⟨_, h⟩
  have ngr : ¬ gone (N.fire p s R.toX.toRhs) (child p s (some true) 0) l₂ r.1 :=
    not_gone (fun e' => hE (e' ▸ hru)) hrl₂ (hused _ hru)
  refine ⟨N₂, .head st sts, ⟨child p s (some false) 0, constIds p s k,
    k₂.paired pxU ngr (ngc _ hnl.head_mem), hnl.keeps k₂ ngc, constIds_length p s k, ?_⟩,
    (k₁.trans k₂).mono ?_, ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := mem_constIds hi
    exact hA.site.not_used_child _ _
  · rintro i ((e1 | e1) | e1 | hm' | hu)
    · exact .inl e1
    · exact .inr (.inl (by
        rw [e1]
        exact List.mem_cons_self))
    · exact .inr (.inr (.inr (by
        rw [e1]
        exact hE)))
    · exact .inr (.inr (.inl hm'))
    · exact .inr (.inr (.inr fun hu' => hu (hused i hu')))
  · intro i γ hi
    obtain ⟨hi₁, hne, -⟩ := hag₂ i γ hi
    rcases hi₁ with ⟨hi₀, hia, -⟩ | ⟨o, j, e, hlab⟩
    · exact .inr (.inr ⟨hi₀, hia⟩)
    · have hlab' : assoc (o, j) R.agents = some γ := hlab
      rcases hall _ (assoc_mem hlab') with ⟨ho, hj⟩ | heq
      · simp only at ho hj
        subst ho
        rcases Nat.lt_or_eq_of_le hj with hlt | heq
        · rw [C.succs j hlt] at hlab'
          exact .inr (.inl (Option.some.inj hlab').symm)
        · subst heq
          rw [C.last] at hlab'
          exact .inl (Option.some.inj hlab').symm
      · simp only at heq
        injection heq with ho hj
        subst ho hj
        exact absurd e hne

/-! ### The three rules, again -/

/-- The rule of the factorial on a zero, as a case. -/
theorem zero1_facZero' {op : Peano} (hr : system.rule op zero = some facZero.toX.toRhs)
    (h0 : zero ≠ op) : Zero1 op 1 1 :=
  zero1_const hr h0 ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- The rule of the multiplier on a zero, as a case. -/
theorem zero2_mulZero' {op : Peano} (hr : system.rule op zero = some mulZero.toX.toRhs)
    (h0 : zero ≠ op) (h1 : succ ≠ op) : Zero2 op (fun _ => 0) (fun n => n + 1 + 1) :=
  zero2_const hr h0 h1 ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide)

/-- The rule of the power on a zero, as a case. -/
theorem zero2_powZero' {op : Peano} (hr : system.rule op zero = some powZero.toX.toRhs)
    (h0 : zero ≠ op) (h1 : succ ≠ op) : Zero2 op (fun _ => 1) (fun n => n + 1 + 1) :=
  zero2_const hr h0 h1 ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide)

/-! ### A new agent with a new constant: the triangular numbers

The agent `tri` was added to the system with two rules: on a zero a new
zero on the result (`Peano.triZero`), a rule no other agent has, and on a
successor `t (S x) = t x + S x` (`Peano.triSucc`).  Its theorem is the
theorem on recursion on the predecessor, with `Peano.zero1_const` for
the zero and the adder as combiner. -/

/-- The triangular numbers. -/
def triN : Nat → Nat
  | 0 => 0
  | n + 1 => triN n + (n + 1)

/-- In closed form: `2 t n = n (n + 1)`. -/
theorem two_mul_triN : ∀ n, 2 * triN n = n * (n + 1)
  | 0 => rfl
  | n + 1 => by
    have ih := two_mul_triN n
    have e₁ : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (n + 1) := Nat.mul_succ _ _
    have e₂ : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := Nat.succ_mul _ _
    show 2 * (triN n + (n + 1)) = (n + 1) * (n + 1 + 1)
    rw [Nat.mul_add, ih]
    omega

/-- Its number of interactions: on a zero, one; on a successor, one, the
copy of the rest, the rest, and the addition. -/
def triCost : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1 + 1 + triCost n + (triN n + 1)

/-- The rule written for it on a successor is the template. -/
theorem triSucc_eq : triSucc = primSucc tri add := rfl

theorem prim_tri (n : Nat) : prim 0 (fun m n => m + n) n = triN n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show prim _ _ n + (n + 1) = triN n + (n + 1)
    rw [ih]

theorem primCost_tri (n : Nat) :
    primCost 1 (fun m _ => m + 1) 0 (fun m n => m + n) n = triCost n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show n + 1 + 1 + primCost _ _ _ _ n + (prim _ _ n + 1) = triCost (n + 1)
    rw [ih, prim_tri]
    rfl

/-- **The triangular numbers are computed**, in any net, in `triCost n`
steps: the theorem on recursion on the predecessor, with the theorem on
constants for the zero and the adder as combiner. -/
theorem tri_computes : Computes1 tri triN triCost :=
  (prim_computes (show system.rule tri succ = some (primSucc tri add).toX.toRhs from rfl)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (zero1_const (show system.rule tri zero = some triZero.toX.toRhs from rfl) (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide))
    add_combines).congr prim_tri primCost_tri

/-- The triangular numbers as an operator. -/
def triOp : Op1 := Op1.ofComputes tri_computes rfl (by decide) (by decide)

/-- **The triangular numbers on the machine**: with any number of threads
and any schedule, a run on the net for `t n` that is at rest has made
exactly `triCost n` interactions and holds `t n`. -/
theorem tri_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (unaryNet tri n) nt).trace xsys σ i).2 = triCost n ∧
      IsNum ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (triN n) :=
  triOp.rest n hnt σ hr

/-- **The triangular numbers under any fair schedule.** -/
theorem tri_fair (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (unaryNet tri n) nt).trace xsys σ i).2 = triCost n ∧
      IsNum ((XMach.init (unaryNet tri n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (triN n) :=
  triOp.fair n hnt σ hfair

/-- The reducer on the net for `t 4` stops after `triCost 4` steps on ten
successors and a zero: `t 4 = 10`. -/
example : ((unaryNet tri 4).normalize xsys 200).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) =
    some (triCost 4, 10, 1, 11) := by
  decide +kernel

/-- `t (2 + 1) * 3!`, an expression with all of them: `6 * 6 = 36`. -/
example : (GExpr.app2 mulOp (.app1 triOp (.app2 addOp (.lit 2) (.lit 1)))
    (.app1 facOp (.lit 3))).eval = 36 := by
  decide

end Peano

end INet
