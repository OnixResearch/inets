import InteractionNets.PeanoCopy

/-! # The multiplier multiplies

In the system `Peano`, a multiplier whose arguments are the numerals `m`
and `n` reduces to the numeral `m * n`, for all `m` and `n`.

The main theorem is about a multiplier in any net
(`Peano.Multiplying.run`): the net may have any other agents, and the
result may be wired to any port.  The proof is by recursion on the first
argument.  On a zero, the multiplier puts a zero on its result and erases
its second argument.  On a successor, it leaves an adder and a new
multiplier behind and copies its second argument, one copy for each; the
new multiplier computes the product of the rest, on the second argument
of the adder; the adder then adds its copy.  The theorem says what the
run leaves alone (`Net.Keeps`), and that the result is made of new
agents, which is what lets it be used inside itself and inside other
runs.

For a net that has nothing else, with the result on a free port
(`Peano.Product`), the result is a normal form (`Peano.mul_correct`).

The count of steps is exact: `(m + 1) * (n + 2) + m * (n + 1)`.

The theorems are about reduction of nets; the machine is not involved
here.
-/

namespace INet

namespace Peano

open Addition (gone gone2)

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

/-! ### The multiplier, with anything else around -/

/-- The number of interactions of `m * n`. -/
def prodCost (m n : Nat) : Nat := (m + 1) * (n + 2) + m * (n + 1)

/-- The agents of a numeral are in use. -/
theorem numList_used {N : Net Peano} {h : Id} {l : List Id} (hl : NumList N h l) {j : Id}
    (hj : j ∈ l) : N.Used j :=
  (hl.label j hj).elim (fun h => .inl ⟨_, h⟩) fun h => .inl ⟨_, h⟩

theorem not_gone2 {N : Net Peano} {a i : Id} {l₁ l₂ : List Id} (h1 : i ≠ a) (h2 : ¬ i ∈ l₁)
    (h3 : ¬ i ∈ l₂) (h4 : N.Used i) : ¬ gone2 N a l₁ l₂ i := by
  rintro (e | hm | hm | hu)
  · exact h1 e
  · exact h2 hm
  · exact h3 hm
  · exact hu h4

/-- **The situation of a multiplication, with anything else in the net.**
The multiplier `a` faces the head `h₁` of its first argument, a numeral
with the agents `l₁`; its second argument is a numeral with the head `h₂`
and the agents `l₂`; its result is wired to the port `r`, which is not on
the multiplier or on an agent of the two numerals.  The port `r` need not
be free. -/
structure Multiplying (N : Net Peano) (a : Id) (h₁ : Id) (l₁ : List Id) (h₂ : Id)
    (l₂ : List Id) (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a mul
  fst : N.Paired ar (a, 0) (h₁, 0)
  num₁ : NumList N h₁ l₁
  snd : N.Paired ar (a, 1) (h₂, 0)
  num₂ : NumList N h₂ l₂
  out : N.Paired ar (a, 2) r
  hr : r.1 ≠ a ∧ ¬ r.1 ∈ l₁ ∧ ¬ r.1 ∈ l₂

variable {N N' : Net Peano} {n : Nat} {r : Port}

/-- **The multiplier multiplies, with anything else around.**  With the
numerals `m` and `n` as arguments, the net reduces in `prodCost m n`
steps to a net in which the port `r` carries the numeral `m * n`, made of
agents whose names were not in use.  Everything away from the multiplier
and its two arguments is kept, and the agents of the net are zeros,
successors, or agents of the start other than the multiplier.

On a zero, the multiplier puts a zero on its result and erases its second
argument.  On a successor it copies its second argument; the product of
the rest of the first argument and one copy is computed first, and the
other copy is then added to it. -/
theorem Multiplying.run : ∀ (l₁ : List Id) {N : Net Peano} {a h₁ h₂ : Id} {l₂ : List Id}
    {r : Port} {m n : Nat}, Multiplying N a h₁ l₁ h₂ l₂ r → l₁.length = m + 1 →
    l₂.length = n + 1 →
    ∃ N', Steps (Step system) (prodCost m n) N N' ∧
      IsNumQ N' (fun i => ¬ N.Used i) r (m * n) ∧ N.Keeps ar (gone2 N a l₁ l₂) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)
  | [], _, _, _, _, _, _, _, _, c, _, _ => by cases c.num₁
  | s :: l', N, a, _, h₂, l₂, r, m, n, c, hlen, hlen₂ => by
    have hN := c.wf
    have ha := c.ha
    have hps := c.fst
    have hpt := c.snd
    have hpx := c.out
    have hl₂ := c.num₂
    obtain ⟨hra, hrl₁, hrl₂⟩ := c.hr
    have hru : N.Used r.1 := Net.End.used hpx.2.1
    have hrs : r.1 ≠ s := fun e => hrl₁ (by
      rw [e]
      exact List.mem_cons_self)
    have hta : h₂ ≠ a := by
      rcases hl₂.label h₂ hl₂.head_mem with hx' | hx'
      · exact ne_of_agent hN hx' ha (by decide)
      · exact ne_of_agent hN hx' ha (by decide)
    -- the second argument is away from the multiplier and the head of the first
    have hav : ∀ t, N.Paired ar (a, 0) (t, 0) → ∀ j, j ∈ l₂ → ¬ (j = a ∨ j = t) := by
      intro t hpt' j hj hc
      rcases hc with e1 | e1
      · rw [e1] at hj
        rcases hl₂.label a hj with hx' | hx'
        · exact absurd (hN.agent_fun hx' ha) (by decide)
        · exact absurd (hN.agent_fun hx' ha) (by decide)
      · rw [e1] at hj
        exact Addition.NumList.not_mem hN hpt' hl₂ hpt (port_ne_snd (by decide)) hj
    have hnum := c.num₁
    cases hnum with
    | last hz =>
      have hm : m = 0 := Nat.succ.inj hlen.symm
      have hA : Addition.Adder ar mul N a s zero := ⟨hN, ha, hz, by decide, hps⟩
      have hts : h₂ ≠ s := hA.not_s hpt (port_ne_snd (by decide))
      obtain ⟨N₁, Z, E, st, k₁, hZ, hE, aZ, aE, pxZ, pEt, hused, hag₁⟩ :=
        mulZero_step hA hpt hpx ⟨hta, hts⟩ ⟨hra, hrs⟩
      have hN₁ := Step.wf hN st
      have hl₂₁ : NumList N₁ h₂ l₂ := hl₂.keeps k₁ (hav s hps)
      obtain ⟨N₂, sts, k₂, hag₂⟩ := erase l₂ hN₁ aE pEt hl₂₁
      rw [hlen₂] at sts
      have ngZ : ¬ gone N₁ E l₂ Z :=
        not_gone (ne_of_agent hN₁ aZ aE (by decide)) (fun hm => hZ (numList_used hl₂ hm))
          (.inl ⟨_, aZ⟩)
      have ngr : ¬ gone N₁ E l₂ r.1 := not_gone (fun e => hE (e ▸ hru)) hrl₂ (hused _ hru)
      have e : prodCost m n = n + 1 + 1 := by
        rw [hm]
        unfold prodCost
        omega
      refine ⟨N₂, ?_, ⟨Z, [Z], k₂.paired pxZ ngr ngZ, .last (k₂.agent aZ ngZ), ?_, ?_⟩,
        (k₁.trans k₂).mono ?_, ?_⟩
      · rw [e]
        exact .head st sts
      · rw [hm, Nat.zero_mul]
        rfl
      · intro i hi
        rw [List.mem_singleton.1 hi]
        exact hZ
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
        rcases hag₁ i γ hi₁ with ⟨hi₀, hia, -⟩ | e1 | e1
        · exact .inr (.inr ⟨hi₀, hia⟩)
        · rw [e1] at hi₁
          exact .inl (hN₁.agent_fun hi₁ aZ)
        · exact absurd e1 hne
    | @next _ h' _ hs hpi hl' =>
      obtain ⟨k, ek, -⟩ := hl'.num
      have hm : m = k + 1 := by
        have e : l'.length + 1 = m + 1 := hlen
        omega
      have hA : Addition.Adder ar mul N a s succ := ⟨hN, ha, hs, by decide, hps⟩
      have hh'a : h' ≠ a := by
        rcases hl'.label h' hl'.head_mem with hx' | hx'
        · exact hA.ne_add hx' (by decide)
        · exact hA.ne_add hx' (by decide)
      have hh's : h' ≠ s := hA.not_s hpi (port_ne_snd (by decide))
      have hts : h₂ ≠ s := hA.not_s hpt (port_ne_snd (by decide))
      obtain ⟨N₁, D, A, M, st, k₁, hD, hA', hM, aD, aA, aM, pDt, pDA, pDM, pMh, pMA, pAx,
        hused, hag₁⟩ := mulSucc_step hA hpi hpt hpx ⟨hh'a, hh's⟩ ⟨hta, hts⟩ ⟨hra, hrs⟩
      have hN₁ := Step.wf hN st
      have hl₂₁ : NumList N₁ h₂ l₂ := hl₂.keeps k₁ (hav s hps)
      have havh : ∀ j, j ∈ l' → ¬ (j = a ∨ j = s) := by
        intro j hj hc
        rcases hc with e1 | e1
        · rw [e1] at hj
          rcases hl'.label a hj with hx' | hx'
          · exact absurd (hN.agent_fun hx' ha) (by decide)
          · exact absurd (hN.agent_fun hx' ha) (by decide)
        · rw [e1] at hj
          exact Addition.NumList.not_mem hN hps hl' hpi (port_ne_snd (by decide)) hj
      have hl'₁ : NumList N₁ h' l' := hl'.keeps k₁ havh
      -- the copy
      have hAl : ¬ A ∈ l₂ := fun hm => hA' (numList_used hl₂ hm)
      have hMl : ¬ M ∈ l₂ := fun hm => hM (numList_used hl₂ hm)
      obtain ⟨N₂, sts₂, ⟨cA, lA, pA, hlA, elA, fA⟩, ⟨cM, lM, pM, hlM, elM, fM⟩, k₂, hag₂⟩ :=
        copy_fresh hN₁ aD pDt hl₂₁ hlen₂ pDA pDM
          ⟨ne_of_agent hN₁ aA aD (by decide), hAl⟩ ⟨ne_of_agent hN₁ aM aD (by decide), hMl⟩
      have hN₂ := Steps.wf hN₁ sts₂
      have U₂ : ∀ i, N.Used i → N₂.Used i := fun i hu => Steps.used hN₁ sts₂ (hused i hu)
      have hC₂ : Addition.Closed ar (gone N₁ D l₂) N₁ := Addition.gone_closed hN₁ pDt hl₂₁
      have ngA : ¬ gone N₁ D l₂ A :=
        not_gone (ne_of_agent hN₁ aA aD (by decide)) hAl (.inl ⟨_, aA⟩)
      have ngM : ¬ gone N₁ D l₂ M :=
        not_gone (ne_of_agent hN₁ aM aD (by decide)) hMl (.inl ⟨_, aM⟩)
      have ngr : ¬ gone N₁ D l₂ r.1 := not_gone (fun e => hD (e ▸ hru)) hrl₂ (hused _ hru)
      -- what the copy keeps: the rest of the first argument, the adder and the multiplier
      have havl' : ∀ j, j ∈ l' → ¬ gone N₁ D l₂ j := hl'₁.avoid hC₂ pMh ngM
      have hl'₂ : NumList N₂ h' l' := hl'₁.keeps k₂ havl'
      have pMh₂ : N₂.Paired ar (M, 0) (h', 0) := k₂.paired pMh ngM (havl' h' hl'₁.head_mem)
      have aM₂ : N₂.agent M mul := k₂.agent aM ngM
      have aA₂ : N₂.agent A add := k₂.agent aA ngA
      have pMA₂ : N₂.Paired ar (M, 2) (A, 1) := k₂.paired pMA ngM ngA
      have pAx₂ : N₂.Paired ar (A, 2) r := k₂.paired pAx ngA ngr
      -- the product of the rest, with its result on the second argument of the adder
      have hAl' : ¬ A ∈ l' := fun hm => hA' (numList_used hl' hm)
      have hAlM : ¬ A ∈ lM := fun hm =>
        (hlM.label _ hm).elim (fun h => absurd (hN₂.agent_fun h aA₂) (by decide))
          fun h => absurd (hN₂.agent_fun h aA₂) (by decide)
      have hAM : A ≠ M := ne_of_agent hN₂ aA₂ aM₂ (by decide)
      have cM' : Multiplying N₂ M h' l' cM lM (A, 1) :=
        ⟨hN₂, aM₂, pMh₂, hl'₂, pM, hlM, pMA₂, hAM, hAl', hAlM⟩
      obtain ⟨N₃, sts₃, ⟨cv, lv, pv, hlv, elv, fv⟩, k₃, hag₃⟩ := Multiplying.run l' cM' ek elM
      have hN₃ := Steps.wf hN₂ sts₃
      have U₃ : ∀ i, N.Used i → N₃.Used i := fun i hu => Steps.used hN₂ sts₃ (U₂ i hu)
      have hC₃ : Addition.Closed ar (gone2 N₂ M l' lM) N₂ :=
        Addition.gone2_closed hN₂ pMh₂ hl'₂ pM hlM
      -- what it keeps: the adder, its first argument and the result port
      have ng3A : ¬ gone2 N₂ M l' lM A := not_gone2 hAM hAl' hAlM (.inl ⟨_, aA₂⟩)
      have havlA : ∀ j, j ∈ lA → ¬ gone2 N₂ M l' lM j := hlA.avoid hC₃ pA ng3A
      have hlA₃ : NumList N₃ cA lA := hlA.keeps k₃ havlA
      have pA₃ : N₃.Paired ar (A, 0) (cA, 0) := k₃.paired pA ng3A (havlA cA hlA.head_mem)
      have aA₃ : N₃.agent A add := k₃.agent aA₂ ng3A
      have hru₁ : N₁.Used r.1 := hused _ hru
      have ng3r : ¬ gone2 N₂ M l' lM r.1 :=
        not_gone2 (fun e => hM (e ▸ hru)) (fun hm => hrl₁ (List.mem_cons_of_mem _ hm))
          (fun hm => fM _ hm hru₁) (U₂ _ hru)
      have pAx₃ : N₃.Paired ar (A, 2) r := k₃.paired pAx₂ ng3A ng3r
      -- the adder adds the other copy
      have cAdd : Addition.Adding ar zero succ add N₃ (fun i => ¬ N.Used i) A 0 cA lA (k * n)
          r :=
        ⟨hN₃, aA₃, pA₃, hlA₃, ⟨cv, lv, pv, hlv, elv, fun i hi hu => fv i hi (U₂ i hu)⟩,
          ⟨r, pAx₃, rfl⟩, ⟨U₃ _ hru, fun e => hA' (e ▸ hru), fun hm => fA _ hm hru₁⟩,
          fun i hu hu' => hu (U₃ i hu')⟩
      obtain ⟨N₄, sts₄, hres, k₄, hag₄⟩ := Addition.Adding.run rules lA cAdd elA
      rw [elA] at sts₄
      rw [Nat.zero_add] at hres
      have e₁ : (k + 1 + 1) * (n + 2) = (k + 1) * (n + 2) + (n + 2) := Nat.succ_mul _ _
      have e₂ : (k + 1) * (n + 1) = k * (n + 1) + (n + 1) := Nat.succ_mul _ _
      have e : prodCost m n = n + 1 + 1 + prodCost k n + (n + 1) := by
        rw [hm]
        unfold prodCost
        omega
      have ev : m * n = n + k * n := by
        rw [hm, Nat.succ_mul, Nat.add_comm]
      refine ⟨N₄, ?_, ?_, (((k₁.trans k₂).trans k₃).trans k₄).mono ?_, ?_⟩
      · rw [e]
        exact ((Steps.head st sts₂).trans sts₃).trans sts₄
      · rw [ev]
        exact hres
      · rintro i ((((e1 | e1) | (e1 | hm' | hu)) | (e1 | hm' | hm' | hu)) | (e1 | hm' | hu))
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
        · exact .inr (.inr (.inr (by
            rw [e1]
            exact hD)))
        · exact .inr (.inr (.inl hm'))
        · exact .inr (.inr (.inr fun hu' => hu (hused i hu')))
        · exact .inr (.inr (.inr (by
            rw [e1]
            exact hM)))
        · exact .inr (.inl (List.mem_cons_of_mem _ hm'))
        · exact .inr (.inr (.inr fun hu' => fM i hm' (hused i hu')))
        · exact .inr (.inr (.inr fun hu' => hu (U₂ i hu')))
        · exact .inr (.inr (.inr (by
            rw [e1]
            exact hA')))
        · exact .inr (.inr (.inr fun hu' => fA i hm' (hused i hu')))
        · exact .inr (.inr (.inr fun hu' => hu (U₃ i hu')))
      · intro i γ hi
        rcases hag₄ i γ hi with hsu | ⟨hi₃, hneA⟩
        · exact .inr (.inl hsu)
        · rcases hag₃ i γ hi₃ with hz | hsu | ⟨hi₂, hneM⟩
          · exact .inl hz
          · exact .inr (.inl hsu)
          · rcases hag₂ i γ hi₂ with hz | hsu | ⟨hi₁, hneD⟩
            · exact .inl hz
            · exact .inr (.inl hsu)
            · rcases hag₁ i γ hi₁ with ⟨hi₀, hia, -⟩ | e1 | e1 | e1
              · exact .inr (.inr ⟨hi₀, hia⟩)
              · exact absurd e1 hneD
              · exact absurd e1 hneA
              · exact absurd e1 hneM

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

/-- **The run of a multiplication**: in `prodCost m n` steps the net
becomes one that has the numeral `m * n` on the result port and whose
agents are successors and zeros. -/
theorem mul_steps {a : Id} {m : Nat} (c : Product N a m n r) :
    ∃ N', Steps (Step system) (prodCost m n) N N' ∧ IsNum N' r (m * n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ := by
  have hN := c.wf
  obtain ⟨h₁, hp₁, hn₁⟩ := c.fst
  obtain ⟨l₁, hl₁, e₁⟩ := Addition.Num.list hn₁
  obtain ⟨h₂, hp₂, hn₂⟩ := c.snd
  obtain ⟨l₂, hl₂, e₂⟩ := Addition.Num.list hn₂
  have hrl : ∀ (h : Id) (l : List Id), NumList N h l → ¬ r.1 ∈ l := fun h l hl hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  have cM : Multiplying N a h₁ l₁ h₂ l₂ r :=
    ⟨hN, c.ha, hp₁, hl₁, hp₂, hl₂, c.out,
      fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ c.ha), hrl _ _ hl₁, hrl _ _ hl₂⟩
  obtain ⟨N', sts, hres, -, hag⟩ := Multiplying.run l₁ cM e₁ e₂
  refine ⟨N', sts, hres.isNum, fun i γ hi => ?_⟩
  rcases hag i γ hi with hz | hsu | ⟨hi₀, hne⟩
  · exact .inl hz
  · exact .inr hsu
  · rcases c.only i γ hi₀ with hz | hsu | e
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e hne

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
  have cA : Addition.Adding ar zero succ add N (fun _ => True) a 0 h l n r :=
    ⟨hN, c.ha, hph, hl, Addition.IsNum.isNumQ c.snd, ⟨r, c.out, rfl⟩, ⟨.inr (.inr ⟨r.2, c.free⟩),
      fun e => hN.free_agent (i := r.1) (k := r.2) c.free (e ▸ c.ha), hrl⟩, fun _ _ => trivial⟩
  obtain ⟨N', sts, inum, -, hag⟩ := Addition.Adding.run rules l cA el
  rw [el] at sts
  rw [Nat.zero_add] at inum
  refine ⟨N', sts, inum.isNum, fun i γ hi => ?_⟩
  rcases hag i γ hi with hsu | ⟨hi₀, hne⟩
  · exact .inr hsu
  · rcases c.only i γ hi₀ with hz | hsu | e
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e hne

end Peano

end INet
