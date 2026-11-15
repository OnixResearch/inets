import InteractionNets.PeanoCopy

/-! # The multiplier multiplies

In the system `Peano`, a multiplier whose arguments are the numerals `m`
and `n` and whose result is a free port reduces to the numeral `m * n`,
for all `m` and `n` (`Peano.mul_correct`).

The run has two parts.

In the first, the multiplier walks down its first argument.  On each
successor it leaves an adder behind, copies its second argument, and
gives one copy to the adder and keeps the other
(`Peano.MState.succ_round`); on the zero it puts a zero on its result and
erases its second argument (`Peano.MState.zero_round`).  The adders left
behind wait in a stack: each has a copy of `n` as its first argument, and
its second argument is the result of the next one (`Peano.Stack`).

In the second, the adders run, from the last one made to the first
(`Peano.SState.pop`), each adding `n` to what is below it.

The count of steps is exact: `(m + 1) * (n + 2)` for the first part and
`m * (n + 1)` for the second.

Scope.  The net has no other agents than the multiplier and its two
arguments.  The theorem is about reduction of nets; the machine is not
involved here.
-/

namespace INet

namespace Peano

open Addition (gone)

theorem rule_mul_zero : system.rule mul zero = some mulZero.toX.toRhs := rfl
theorem rule_mul_succ : system.rule mul succ = some mulSucc.toX.toRhs := rfl

/-- The rule for a multiplier on a zero makes two agents. -/
theorem mulZero_lab {o : Option Bool} {j : Nat} {γ : Peano}
    (h : mulZero.toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) mulZero.agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), zero), ((some true, 0), era)] :=
    assoc_mem h'
  rcases List.mem_cons.1 hm with e | hm'
  · injection e with e1 _
    injection e1 with e3 e4
    exact .inl ⟨e3, e4⟩
  · rcases List.mem_cons.1 hm' with e | hm''
    · injection e with e1 _
      injection e1 with e3 e4
      exact .inr ⟨e3, e4⟩
    · exact absurd hm'' List.not_mem_nil

/-- The rule for a multiplier on a successor makes three agents. -/
theorem mulSucc_lab {o : Option Bool} {j : Nat} {γ : Peano}
    (h : mulSucc.toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some false ∧ j = 1) ∨ (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) mulSucc.agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), dup), ((some false, 1), add),
      ((some true, 0), mul)] := assoc_mem h'
  rcases List.mem_cons.1 hm with e | hm'
  · injection e with e1 _
    injection e1 with e3 e4
    exact .inl ⟨e3, e4⟩
  · rcases List.mem_cons.1 hm' with e | hm''
    · injection e with e1 _
      injection e1 with e3 e4
      exact .inr (.inl ⟨e3, e4⟩)
    · rcases List.mem_cons.1 hm'' with e | hm'''
      · injection e with e1 _
        injection e1 with e3 e4
        exact .inr (.inr ⟨e3, e4⟩)
      · exact absurd hm''' List.not_mem_nil

/-! ### Small facts about names -/

theorem ne_of_agent {N : Net Peano} (hN : N.WF ar) {i j : Id} {α β : Peano}
    (hi : N.agent i α) (hj : N.agent j β) (h : α ≠ β) : i ≠ j := by
  rintro rfl
  exact h (hN.agent_fun hi hj)

theorem not_gone {N : Net Peano} {d i : Id} {l : List Id} (h1 : i ≠ d) (h2 : ¬ i ∈ l)
    (h3 : N.Used i) : ¬ gone N d l i := by
  rintro (e | hm | hu)
  · exact h1 e
  · exact h2 hm
  · exact hu h3

/-- A net whose agents are zeros and successors is normal. -/
theorem normal_of_numerals {N : Net Peano} (h : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ) :
    Normal (Step system) N := by
  rintro N' ⟨a, b, α, β, R, red, -⟩
  have hr := red.rule
  have hnone : ∀ α β : Peano, (α = zero ∨ α = succ) → (β = zero ∨ β = succ) →
      system.rule α β = none := by
    rintro α β (rfl | rfl) (rfl | rfl) <;> rfl
  rw [hnone α β (h a α red.ha) (h b β red.hb)] at hr
  cases hr

/-! ### The two firings of the multiplier -/

/-- **The multiplier meets a successor.**  The firing makes a copier `D`
on the second argument, an adder `A` whose first argument is the first
copy and whose result is the old result, and a multiplier `M` on the rest
of the first argument, whose second argument is the second copy and whose
result is the second argument of the adder. -/
theorem mulSucc_step {N : Net Peano} {a s h' t : Id} {x : Port}
    (hA : Addition.Adder ar mul N a s succ) (hpi : N.Paired ar (s, 1) (h', 0))
    (hpt : N.Paired ar (a, 1) (t, 0)) (hpx : N.Paired ar (a, 2) x)
    (hh' : h' ≠ a ∧ h' ≠ s) (ht : t ≠ a ∧ t ≠ s) (hx : x.1 ≠ a ∧ x.1 ≠ s) :
    ∃ (N₁ : Net Peano) (D A M : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = a ∨ i = s) N₁ ∧
      ¬ N.Used D ∧ ¬ N.Used A ∧ ¬ N.Used M ∧
      N₁.agent D dup ∧ N₁.agent A add ∧ N₁.agent M mul ∧
      N₁.Paired ar (D, 0) (t, 0) ∧ N₁.Paired ar (D, 1) (A, 0) ∧ N₁.Paired ar (D, 2) (M, 1) ∧
      N₁.Paired ar (M, 0) (h', 0) ∧ N₁.Paired ar (M, 2) (A, 1) ∧ N₁.Paired ar (A, 2) x ∧
      (∀ i, N.Used i → N₁.Used i) ∧
      ∀ i γ, N₁.agent i γ → (N.agent i γ ∧ i ≠ a ∧ i ≠ s) ∨ i = D ∨ i = A ∨ i = M := by
  have hN := hA.wf
  have hR : mulSucc.toX.toRhs.WF ar mul succ := system.rule_wf rule_mul_succ
  have red : Redex system N a s mul succ mulSucc.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, rule_mul_succ⟩
  have st : Step system N (N.fire a s mulSucc.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN₁ := Step.wf hN st
  refine ⟨_, child a s (some false) 0, child a s (some false) 1, child a s (some true) 0, st,
    hA.site.keeps _, hA.site.not_used_child _ _, hA.site.not_used_child _ _,
    hA.site.not_used_child _ _, .inr ⟨some false, 0, rfl, rfl⟩, .inr ⟨some false, 1, rfl, rfl⟩,
    .inr ⟨some true, 0, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hu => Net.used_fire hN hu _ _ _, ?_⟩
  · exact (hA.site.paired_fire_ifc_new hR
      (show mulSucc.toX.toRhs.link (.ifc false 0) (.new (some false) 0 0) from rfl)
      (hpt.symm hN) ht.1 ht.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show mulSucc.toX.toRhs.link (.new (some false) 0 1) (.new (some false) 1 0) from rfl)
  · exact Site.paired_fire_new_new hR
      (show mulSucc.toX.toRhs.link (.new (some false) 0 2) (.new (some true) 0 1) from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show mulSucc.toX.toRhs.link (.ifc true 0) (.new (some true) 0 0) from rfl)
      (hpi.symm hN) hh'.1 hh'.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show mulSucc.toX.toRhs.link (.new (some true) 0 2) (.new (some false) 1 1) from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show mulSucc.toX.toRhs.link (.ifc false 1) (.new (some false) 1 2) from rfl)
      (hpx.symm hN) hx.1 hx.2).symm hN₁
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases mulSucc_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr e))

/-- **The multiplier meets a zero.**  The firing puts a zero `Z` on the
result and an eraser `E` on the second argument. -/
theorem mulZero_step {N : Net Peano} {a z t : Id} {x : Port}
    (hA : Addition.Adder ar mul N a z zero)
    (hpt : N.Paired ar (a, 1) (t, 0)) (hpx : N.Paired ar (a, 2) x)
    (ht : t ≠ a ∧ t ≠ z) (hx : x.1 ≠ a ∧ x.1 ≠ z) :
    ∃ (N₁ : Net Peano) (Z E : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = a ∨ i = z) N₁ ∧ ¬ N.Used Z ∧ ¬ N.Used E ∧
      N₁.agent Z zero ∧ N₁.agent E era ∧
      N₁.Paired ar x (Z, 0) ∧ N₁.Paired ar (E, 0) (t, 0) ∧
      (∀ i, N.Used i → N₁.Used i) ∧
      ∀ i γ, N₁.agent i γ → (N.agent i γ ∧ i ≠ a ∧ i ≠ z) ∨ i = Z ∨ i = E := by
  have hN := hA.wf
  have hR : mulZero.toX.toRhs.WF ar mul zero := system.rule_wf rule_mul_zero
  have red : Redex system N a z mul zero mulZero.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, rule_mul_zero⟩
  have st : Step system N (N.fire a z mulZero.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN₁ := Step.wf hN st
  refine ⟨_, child a z (some false) 0, child a z (some true) 0, st, hA.site.keeps _,
    hA.site.not_used_child _ _, hA.site.not_used_child _ _, .inr ⟨some false, 0, rfl, rfl⟩,
    .inr ⟨some true, 0, rfl, rfl⟩, ?_, ?_, fun i hu => Net.used_fire hN hu _ _ _, ?_⟩
  · exact hA.site.paired_fire_ifc_new hR
      (show mulZero.toX.toRhs.link (.ifc false 1) (.new (some false) 0 0) from rfl)
      (hpx.symm hN) hx.1 hx.2
  · exact (hA.site.paired_fire_ifc_new hR
      (show mulZero.toX.toRhs.link (.ifc false 0) (.new (some true) 0 0) from rfl)
      (hpt.symm hN) ht.1 ht.2).symm hN₁
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases mulZero_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr e)

/-! ### The stack of waiting adders -/

/-- **The adders that wait for the product.**  The port `x` is where the
multiplier delivers.  With no adder waiting it is the result port `r`.
Otherwise it is the second argument of the adder `A`, whose first
argument is the numeral `n` and whose result is the port of the rest of
the stack. -/
def Stack (N : Net Peano) (n : Nat) : Port → List Id → Port → Prop
  | x, [], r => x = r
  | x, A :: As, r => x = (A, 1) ∧ N.agent A add ∧ IsNum N (A, 0) n ∧
      ∃ x', N.Paired ar (A, 2) x' ∧ Stack N n x' As r

variable {N N' : Net Peano} {n : Nat} {r : Port}

theorem Stack.agent : ∀ {As : List Id} {x : Port}, Stack N n x As r →
    ∀ A, A ∈ As → N.agent A add
  | [], _, _, _, hA => absurd hA List.not_mem_nil
  | B :: _, _, ⟨_, hB, _, _, _, hs⟩, A, hA => by
    rcases List.mem_cons.1 hA with e | hA'
    · rw [e]
      exact hB
    · exact Stack.agent hs A hA'

/-- The port of a stack is the result port or the second argument of one
of its adders. -/
theorem Stack.port : ∀ {As : List Id} {x : Port}, Stack N n x As r →
    x = r ∨ ∃ A, A ∈ As ∧ x = (A, 1)
  | [], _, h => .inl h
  | A :: _, _, ⟨e, _⟩ => .inr ⟨A, List.mem_cons_self, e⟩

/-- The port of a stack is on a name in use. -/
theorem Stack.port_used {As : List Id} {x : Port} (hr : N.free r) (hs : Stack N n x As r) :
    N.Used x.1 := by
  rcases hs.port with e | ⟨B, hB, e⟩
  · rw [e]
    exact .inr (.inr ⟨r.2, hr⟩)
  · rw [e]
    exact .inl ⟨add, hs.agent B hB⟩

/-- The port of a stack is not on an agent that is not an adder. -/
theorem Stack.port_ne {As : List Id} {x : Port} (hN : N.WF ar) (hr : N.free r)
    (hs : Stack N n x As r) {i : Id} {γ : Peano} (hi : N.agent i γ) (hγ : γ ≠ add) :
    x.1 ≠ i := by
  intro e
  rcases hs.port with e' | ⟨B, hB, e'⟩
  · rw [e'] at e
    rw [← e] at hi
    exact hN.free_agent (i := r.1) (k := r.2) hr hi
  · rw [e'] at e
    have e'' : B = i := e
    rw [← e''] at hi
    exact hγ (hN.agent_fun hi (hs.agent B hB))

/-- **A stack away from a closed set is kept.** -/
theorem Stack.keeps {C : Id → Prop} (k : N.Keeps ar C N') (hC : Addition.Closed ar C N)
    (hr : ¬ C r.1) : ∀ {As : List Id} {x : Port}, Stack N n x As r →
      (∀ A, A ∈ As → ¬ C A) → Stack N' n x As r
  | [], _, h, _ => h
  | A :: _, _, ⟨e, hA, hn, x', hp, hs⟩, hAs => by
    have hA' : ¬ C A := hAs A List.mem_cons_self
    have hx' : ¬ C x'.1 := by
      rcases hs.port with e' | ⟨B, hB, e'⟩
      · rw [e']
        exact hr
      · rw [e']
        exact hAs B (List.mem_cons_of_mem _ hB)
    exact ⟨e, k.agent hA hA', Addition.IsNum.keeps k hC hn hA', x', k.paired hp hA' hx',
      Stack.keeps k hC hr hs fun B hB => hAs B (List.mem_cons_of_mem _ hB)⟩

/-! ### The two parts of the run -/

/-- **The multiplier at work.**  The multiplier `a` has the numerals `m`
and `n` as arguments, and delivers to the stack of the adders `As`, which
ends on the free port `r`.  The net has nothing else. -/
structure MState (N : Net Peano) (a : Id) (m n : Nat) (As : List Id) (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a mul
  fst : IsNum N (a, 0) m
  snd : IsNum N (a, 1) n
  out : ∃ x, N.Paired ar (a, 2) x ∧ Stack N n x As r
  free : N.free r
  nodup : As.Nodup
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = a ∨ i ∈ As

/-- **The adders at work.**  The numeral `v` is delivered to the stack of
the adders `As`, which ends on the free port `r`.  The net has nothing
else. -/
structure SState (N : Net Peano) (v n : Nat) (As : List Id) (r : Port) : Prop where
  wf : N.WF ar
  val : ∃ x, IsNum N x v ∧ Stack N n x As r
  free : N.free r
  nodup : As.Nodup
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i ∈ As

/-- The agents of a numeral are in use. -/
theorem numList_used {h : Id} {l : List Id} (hl : NumList N h l) {j : Id} (hj : j ∈ l) :
    N.Used j :=
  (hl.label j hj).elim (fun h => .inl ⟨_, h⟩) fun h => .inl ⟨_, h⟩

/-- **A round of the multiplier on a successor**: one firing and a copy,
`n + 2` steps, after which there is one more adder waiting. -/
theorem MState.succ_round {a : Id} {m : Nat} {As : List Id}
    (c : MState N a (m + 1) n As r) :
    ∃ N' a' A, Steps (Step system) (n + 2) N N' ∧ MState N' a' m n (A :: As) r := by
  have hN := c.wf
  have ha := c.ha
  obtain ⟨s, hps, hs, h', hpi, hnh'⟩ := c.fst
  obtain ⟨t, hpt, hnt⟩ := c.snd
  obtain ⟨x, hpx, hst⟩ := c.out
  have hA : Addition.Adder ar mul N a s succ := ⟨hN, ha, hs, by decide, hps⟩
  have hh'a : h' ≠ a := by
    rcases Addition.Num.label hnh' with hx' | hx'
    · exact hA.ne_add hx' (by decide)
    · exact hA.ne_add hx' (by decide)
  have hh's : h' ≠ s := hA.not_s hpi (port_ne_snd (by decide))
  have hta : t ≠ a := by
    rcases Addition.Num.label hnt with hx' | hx'
    · exact hA.ne_add hx' (by decide)
    · exact hA.ne_add hx' (by decide)
  have hts : t ≠ s := hA.not_s hpt (port_ne_snd (by decide))
  have hxa : x.1 ≠ a := hst.port_ne hN c.free ha (by decide)
  have hxs : x.1 ≠ s := hst.port_ne hN c.free hs (by decide)
  obtain ⟨N₁, D, A, M, st, k₁, hD, hA', hM, aD, aA, aM, pDt, pDA, pDM, pMh, pMA, pAx, hused,
    hag₁⟩ := mulSucc_step hA hpi hpt hpx ⟨hh'a, hh's⟩ ⟨hta, hts⟩ ⟨hxa, hxs⟩
  have hN₁ := Step.wf hN st
  -- the second argument, in the net after the firing
  obtain ⟨l, hl, el⟩ := Addition.Num.list hnt
  have hav : ∀ j, j ∈ l → ¬ (j = a ∨ j = s) := by
    intro j hj hc
    rcases hc with e1 | e1
    · rw [e1] at hj
      rcases hl.label a hj with hx' | hx'
      · exact absurd (hN.agent_fun hx' ha) (by decide)
      · exact absurd (hN.agent_fun hx' ha) (by decide)
    · rw [e1] at hj
      exact Addition.NumList.not_mem hN hps hl hpt (port_ne_snd (by decide)) hj
  have hl₁ : NumList N₁ t l := hl.keeps k₁ hav
  -- the rest of the first argument, in the net after the firing
  obtain ⟨lh, hlh, elh⟩ := Addition.Num.list hnh'
  have havh : ∀ j, j ∈ lh → ¬ (j = a ∨ j = s) := by
    intro j hj hc
    rcases hc with e1 | e1
    · rw [e1] at hj
      rcases hlh.label a hj with hx' | hx'
      · exact absurd (hN.agent_fun hx' ha) (by decide)
      · exact absurd (hN.agent_fun hx' ha) (by decide)
    · rw [e1] at hj
      exact Addition.NumList.not_mem hN hps hlh hpi (port_ne_snd (by decide)) hj
  obtain ⟨m', em', hm'⟩ := (hlh.keeps k₁ havh).num
  have emm : m' = m := by omega
  rw [emm] at hm'
  -- the copy
  have hAl : ¬ A ∈ l := fun hm => hA' (numList_used hl hm)
  have hMl : ¬ M ∈ l := fun hm => hM (numList_used hl hm)
  obtain ⟨N₂, sts, i₁, i₂, k₂, hag₂⟩ := copy hN₁ aD pDt hl₁ el pDA pDM
    ⟨ne_of_agent hN₁ aA aD (by decide), hAl⟩ ⟨ne_of_agent hN₁ aM aD (by decide), hMl⟩
  have hC₂ : Addition.Closed ar (gone N₁ D l) N₁ := Addition.gone_closed hN₁ pDt hl₁
  have ngA : ¬ gone N₁ D l A := not_gone (ne_of_agent hN₁ aA aD (by decide)) hAl (.inl ⟨_, aA⟩)
  have ngM : ¬ gone N₁ D l M := not_gone (ne_of_agent hN₁ aM aD (by decide)) hMl (.inl ⟨_, aM⟩)
  -- what was there before and is not in the second argument is not used up
  have ngold : ∀ i, N.Used i → ¬ i ∈ l → ¬ gone N₁ D l i := fun i hu hl' =>
    not_gone (fun e => hD (e ▸ hu)) hl' (hused i hu)
  have hxl : ¬ x.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hst.port_ne hN c.free h (by decide) rfl)
      fun h => hst.port_ne hN c.free h (by decide) rfl
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  have hAsl : ∀ B, B ∈ As → ¬ B ∈ l := fun B hB hm =>
    (hl.label _ hm).elim (fun h => absurd (hN.agent_fun h (hst.agent B hB)) (by decide))
      fun h => absurd (hN.agent_fun h (hst.agent B hB)) (by decide)
  have hst₁ : Stack N₁ n x As r :=
    hst.keeps k₁ hA.closed
      (fun hc => hc.elim (fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ ha))
        fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ hs))
      fun B hB hc => hc.elim (ne_of_agent hN (hst.agent B hB) ha (by decide))
        (ne_of_agent hN (hst.agent B hB) hs (by decide))
  have hst₂ : Stack N₂ n x As r :=
    hst₁.keeps k₂ hC₂ (ngold _ (.inr (.inr ⟨r.2, c.free⟩)) hrl)
      fun B hB => ngold B (.inl ⟨_, hst.agent B hB⟩) (hAsl B hB)
  have ngx : ¬ gone N₁ D l x.1 := ngold _ (hst.port_used c.free) hxl
  refine ⟨N₂, M, A, .head st sts, Steps.wf hN₁ sts, k₂.agent aM ngM,
    Addition.IsNum.keeps k₂ hC₂ ⟨h', pMh, hm'⟩ ngM, i₂,
    ⟨(A, 1), k₂.paired pMA ngM ngA, rfl, k₂.agent aA ngA, i₁, x, k₂.paired pAx ngA ngx, hst₂⟩,
    ?_, List.nodup_cons.2 ⟨fun hm => hA' (.inl ⟨_, hst.agent A hm⟩), c.nodup⟩, ?_⟩
  · rw [sts.free, st.free]
    exact c.free
  · intro i γ hi
    rcases hag₂ i γ hi with hz | hsu | ⟨hi₁, hne⟩
    · exact .inl hz
    · exact .inr (.inl hsu)
    · rcases hag₁ i γ hi₁ with ⟨hi₀, hia, -⟩ | e | e | e
      · rcases c.only i γ hi₀ with hz | hsu | e | hm
        · exact .inl hz
        · exact .inr (.inl hsu)
        · exact absurd e hia
        · exact .inr (.inr (.inr (List.mem_cons_of_mem _ hm)))
      · exact absurd e hne
      · exact .inr (.inr (.inr (by
          rw [e]
          exact List.mem_cons_self)))
      · exact .inr (.inr (.inl e))

/-- **The round of the multiplier on the zero**: one firing and an
erasure, `n + 2` steps, after which the stack is given a zero. -/
theorem MState.zero_round {a : Id} {As : List Id} (c : MState N a 0 n As r) :
    ∃ N', Steps (Step system) (n + 2) N N' ∧ SState N' 0 n As r := by
  have hN := c.wf
  have ha := c.ha
  obtain ⟨z, hpz, hz⟩ := c.fst
  have hz' : N.agent z zero := hz
  obtain ⟨t, hpt, hnt⟩ := c.snd
  obtain ⟨x, hpx, hst⟩ := c.out
  have hA : Addition.Adder ar mul N a z zero := ⟨hN, ha, hz', by decide, hpz⟩
  have hta : t ≠ a := by
    rcases Addition.Num.label hnt with hx' | hx'
    · exact hA.ne_add hx' (by decide)
    · exact hA.ne_add hx' (by decide)
  have htz : t ≠ z := hA.not_s hpt (port_ne_snd (by decide))
  have hxa : x.1 ≠ a := hst.port_ne hN c.free ha (by decide)
  have hxz : x.1 ≠ z := hst.port_ne hN c.free hz' (by decide)
  obtain ⟨N₁, Z, E, st, k₁, hZ, hE, aZ, aE, pxZ, pEt, hused, hag₁⟩ :=
    mulZero_step hA hpt hpx ⟨hta, htz⟩ ⟨hxa, hxz⟩
  have hN₁ := Step.wf hN st
  obtain ⟨l, hl, el⟩ := Addition.Num.list hnt
  have hav : ∀ j, j ∈ l → ¬ (j = a ∨ j = z) := by
    intro j hj hc
    rcases hc with e1 | e1
    · rw [e1] at hj
      rcases hl.label a hj with hx' | hx'
      · exact absurd (hN.agent_fun hx' ha) (by decide)
      · exact absurd (hN.agent_fun hx' ha) (by decide)
    · rw [e1] at hj
      exact Addition.NumList.not_mem hN hpz hl hpt (port_ne_snd (by decide)) hj
  have hl₁ : NumList N₁ t l := hl.keeps k₁ hav
  obtain ⟨N₂, sts, k₂, hag₂⟩ := erase l hN₁ aE pEt hl₁
  rw [el] at sts
  have hC₂ : Addition.Closed ar (gone N₁ E l) N₁ := Addition.gone_closed hN₁ pEt hl₁
  have ngZ : ¬ gone N₁ E l Z :=
    not_gone (ne_of_agent hN₁ aZ aE (by decide)) (fun hm => hZ (numList_used hl hm))
      (.inl ⟨_, aZ⟩)
  have ngold : ∀ i, N.Used i → ¬ i ∈ l → ¬ gone N₁ E l i := fun i hu hl' =>
    not_gone (fun e => hE (e ▸ hu)) hl' (hused i hu)
  have hxl : ¬ x.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hst.port_ne hN c.free h (by decide) rfl)
      fun h => hst.port_ne hN c.free h (by decide) rfl
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  have hAsl : ∀ B, B ∈ As → ¬ B ∈ l := fun B hB hm =>
    (hl.label _ hm).elim (fun h => absurd (hN.agent_fun h (hst.agent B hB)) (by decide))
      fun h => absurd (hN.agent_fun h (hst.agent B hB)) (by decide)
  have hst₁ : Stack N₁ n x As r :=
    hst.keeps k₁ hA.closed
      (fun hc => hc.elim (fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ ha))
        fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ hz'))
      fun B hB hc => hc.elim (ne_of_agent hN (hst.agent B hB) ha (by decide))
        (ne_of_agent hN (hst.agent B hB) hz' (by decide))
  have hst₂ : Stack N₂ n x As r :=
    hst₁.keeps k₂ hC₂ (ngold _ (.inr (.inr ⟨r.2, c.free⟩)) hrl)
      fun B hB => ngold B (.inl ⟨_, hst.agent B hB⟩) (hAsl B hB)
  have ngx : ¬ gone N₁ E l x.1 := ngold _ (hst.port_used c.free) hxl
  refine ⟨N₂, .head st sts, Steps.wf hN₁ sts,
    ⟨x, ⟨Z, k₂.paired pxZ ngx ngZ, k₂.agent aZ ngZ⟩, hst₂⟩, ?_, c.nodup, ?_⟩
  · rw [sts.free, st.free]
    exact c.free
  · intro i γ hi
    obtain ⟨hi₁, hne, -⟩ := hag₂ i γ hi
    rcases hag₁ i γ hi₁ with ⟨hi₀, hia, -⟩ | e | e
    · rcases c.only i γ hi₀ with hz | hsu | e | hm
      · exact .inl hz
      · exact .inr (.inl hsu)
      · exact absurd e hia
      · exact .inr (.inr hm)
    · rw [e] at hi₁
      exact .inl (hN₁.agent_fun hi₁ aZ)
    · exact absurd e hne

/-- **The first adder of the stack runs**: `n + 1` steps, after which the
rest of the stack is given `n` more. -/
theorem SState.pop {v : Nat} {A : Id} {As : List Id} (c : SState N v n (A :: As) r) :
    ∃ N', Steps (Step system) (n + 1) N N' ∧ SState N' (n + v) n As r := by
  have hN := c.wf
  obtain ⟨x, hv, e, hA, ⟨h, hph, hnh⟩, x', hpx', hst'⟩ := c.val
  subst e
  have hAAs : ¬ A ∈ As := (List.nodup_cons.1 c.nodup).1
  obtain ⟨l, hl, el⟩ := Addition.Num.list hnh
  have hx'A : x'.1 ≠ A := by
    intro e
    rcases hst'.port with e' | ⟨B, hB, e'⟩
    · rw [e'] at e
      exact hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ hA)
    · rw [e'] at e
      have e'' : B = A := e
      exact hAAs (e'' ▸ hB)
  have hx'l : ¬ x'.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hst'.port_ne hN c.free h (by decide) rfl)
      fun h => hst'.port_ne hN c.free h (by decide) rfl
  have cA : Addition.Adding ar zero succ add N A 0 h l v x' :=
    ⟨hN, hA, hph, hl, hv, ⟨x', hpx', rfl⟩, ⟨hst'.port_used c.free, hx'A, hx'l⟩⟩
  obtain ⟨N', sts, inum, kp, hag⟩ := Addition.Adding.run rules l cA el
  rw [el] at sts
  rw [Nat.zero_add] at inum
  have hC : Addition.Closed ar (gone N A l) N := Addition.gone_closed hN hph hl
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  have hst₁ : Stack N' n x' As r :=
    hst'.keeps kp hC
      (not_gone (fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ hA)) hrl
        (.inr (.inr ⟨r.2, c.free⟩)))
      fun B hB => not_gone (fun e => hAAs (e ▸ hB))
        (fun hm => (hl.label _ hm).elim
          (fun h => absurd (hN.agent_fun h (hst'.agent B hB)) (by decide))
          fun h => absurd (hN.agent_fun h (hst'.agent B hB)) (by decide))
        (.inl ⟨_, hst'.agent B hB⟩)
  refine ⟨N', sts, Steps.wf hN sts, ⟨x', inum, hst₁⟩, ?_, (List.nodup_cons.1 c.nodup).2, ?_⟩
  · rw [sts.free]
    exact c.free
  · intro i γ hi
    rcases hag i γ hi with hsu | ⟨hi₀, hne⟩
    · exact .inr (.inl hsu)
    · rcases c.only i γ hi₀ with hz | hsu | hm
      · exact .inl hz
      · exact .inr (.inl hsu)
      · rcases List.mem_cons.1 hm with e | hm'
        · exact absurd e hne
        · exact .inr (.inr hm')

/-- **The first part**: the multiplier walks down its first argument, in
`(m + 1) * (n + 2)` steps, and leaves `m` adders waiting on a zero. -/
theorem MState.run : ∀ (m : Nat) {N : Net Peano} {a : Id} {n : Nat} {As : List Id} {r : Port},
    MState N a m n As r →
    ∃ N' As', Steps (Step system) ((m + 1) * (n + 2)) N N' ∧ SState N' 0 n As' r ∧
      As'.length = As.length + m
  | 0, _, _, n, As, _, c => by
    obtain ⟨N', sts, s⟩ := c.zero_round
    have e : (0 + 1) * (n + 2) = n + 2 := by omega
    rw [e]
    exact ⟨N', As, sts, s, rfl⟩
  | m + 1, _, _, n, As, _, c => by
    obtain ⟨N₁, a', A, sts₁, c₁⟩ := c.succ_round
    obtain ⟨N', As', sts₂, s, e'⟩ := MState.run m c₁
    have e : (m + 1 + 1) * (n + 2) = (n + 2) + (m + 1) * (n + 2) := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    exact ⟨N', As', sts₁.trans sts₂, s, by
      rw [e', List.length_cons]
      omega⟩

/-- **The second part**: the waiting adders run, in `n + 1` steps each. -/
theorem SState.run : ∀ (As : List Id) {N : Net Peano} {v n : Nat} {r : Port},
    SState N v n As r →
    ∃ N', Steps (Step system) (As.length * (n + 1)) N N' ∧ SState N' (As.length * n + v) n [] r
  | [], N, v, n, _, c => by
    have e₁ : ([] : List Id).length * (n + 1) = 0 := Nat.zero_mul _
    have e₂ : ([] : List Id).length * n + v = v := by
      rw [List.length_nil, Nat.zero_mul, Nat.zero_add]
    rw [e₁, e₂]
    exact ⟨N, .refl _, c⟩
  | A :: As, _, v, n, _, c => by
    obtain ⟨N₁, sts₁, c₁⟩ := c.pop
    obtain ⟨N', sts₂, c₂⟩ := SState.run As c₁
    have e₁ : (A :: As).length * (n + 1) = (n + 1) + As.length * (n + 1) := by
      rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    have e₂ : (A :: As).length * n + v = As.length * n + (n + v) := by
      rw [List.length_cons, Nat.succ_mul, Nat.add_assoc]
    rw [e₁, e₂]
    exact ⟨N', sts₁.trans sts₂, c₂⟩

/-! ### Multiplication is correct -/

/-- **The situation of a multiplication.**  The multiplier `a` has the
numerals `m` and `n` as arguments and the free port `r` as result, and
the net has no other agents than the multiplier and the successors and
zeros. -/
structure Product (N : Net Peano) (a : Id) (m n : Nat) (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a mul
  fst : IsNum N (a, 0) m
  snd : IsNum N (a, 1) n
  out : N.Paired ar (a, 2) r
  free : N.free r
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = a

/-- The number of interactions of `m * n`. -/
def prodCost (m n : Nat) : Nat := (m + 1) * (n + 2) + m * (n + 1)

/-- **The run of a multiplication**: in `prodCost m n` steps the net
becomes one that has the numeral `m * n` on the result port and whose
agents are successors and zeros. -/
theorem mul_steps {a : Id} {m : Nat} (c : Product N a m n r) :
    ∃ N', Steps (Step system) (prodCost m n) N N' ∧ IsNum N' r (m * n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ := by
  have c₀ : MState N a m n [] r :=
    ⟨c.wf, c.ha, c.fst, c.snd, ⟨r, c.out, rfl⟩, c.free, List.nodup_nil, fun i γ hi =>
      (c.only i γ hi).elim .inl fun h => h.elim (fun h => .inr (.inl h))
        fun h => .inr (.inr (.inl h))⟩
  obtain ⟨N₁, As, sts₁, c₁, eAs⟩ := c₀.run m
  obtain ⟨N', sts₂, c₂⟩ := c₁.run As
  have eAs' : As.length = m := by rw [eAs, List.length_nil, Nat.zero_add]
  rw [eAs'] at sts₂ c₂
  obtain ⟨x, hx, e⟩ := c₂.val
  have e' : x = r := e
  rw [e', Nat.add_zero] at hx
  refine ⟨N', sts₁.trans sts₂, hx, fun i γ hi => ?_⟩
  rcases c₂.only i γ hi with h | h | h
  · exact .inl h
  · exact .inr h
  · exact absurd h List.not_mem_nil

/-- **Multiplication is correct, for all inputs.**  A net whose multiplier
has the numerals `m` and `n` as arguments and the free port `r` as result
reduces, in `(m + 1) * (n + 2) + m * (n + 1)` steps, to a normal form in
which `r` carries the numeral `m * n`. -/
theorem mul_correct {a : Id} {m : Nat} (c : Product N a m n r) :
    ∃ N', Steps (Step system) ((m + 1) * (n + 2) + m * (n + 1)) N N' ∧
      Normal (Step system) N' ∧ IsNum N' r (m * n) := by
  obtain ⟨N', sts, hnum, hag⟩ := mul_steps c
  exact ⟨N', sts, normal_of_numerals hag, hnum⟩

/-- **The situation of an addition.**  The adder `a` has the numerals `m`
and `n` as arguments and the free port `r` as result, and the net has no
other agents than the adder and the successors and zeros. -/
structure Sum (N : Net Peano) (a : Id) (m n : Nat) (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a add
  fst : IsNum N (a, 0) m
  snd : IsNum N (a, 1) n
  out : N.Paired ar (a, 2) r
  free : N.free r
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = a

/-- **The run of an addition**, in this system: in `m + 1` steps the net
becomes one that has the numeral `m + n` on the result port and whose
agents are successors and zeros. -/
theorem add_steps' {a : Id} {m : Nat} (c : Sum N a m n r) :
    ∃ N', Steps (Step system) (m + 1) N N' ∧ IsNum N' r (m + n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ := by
  have hN := c.wf
  obtain ⟨h, hph, hnh⟩ := c.fst
  obtain ⟨l, hl, el⟩ := Addition.Num.list hnh
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  have cA : Addition.Adding ar zero succ add N a 0 h l n r :=
    ⟨hN, c.ha, hph, hl, c.snd, ⟨r, c.out, rfl⟩, ⟨.inr (.inr ⟨r.2, c.free⟩),
      fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ c.ha), hrl⟩⟩
  obtain ⟨N', sts, inum, -, hag⟩ := Addition.Adding.run rules l cA el
  rw [el] at sts
  rw [Nat.zero_add] at inum
  refine ⟨N', sts, inum, fun i γ hi => ?_⟩
  rcases hag i γ hi with hsu | ⟨hi₀, hne⟩
  · exact .inr hsu
  · rcases c.only i γ hi₀ with hz | hsu | e
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e hne

end Peano

end INet
