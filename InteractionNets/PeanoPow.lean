import InteractionNets.PeanoProd

/-! # Powers

In the system `Peano`, the agent `pow` with the numerals `e` and `b` as
exponent and base reduces to the numeral `b ^ e`, for all `e` and `b`.

As for the multiplier, the main theorem is about the agent in any net
(`Peano.Powering.run`).  The proof is by recursion on the exponent.  On a
zero, the agent puts the numeral `1` on its result and erases its base.
On a successor, it leaves a multiplier and a new `pow` behind and copies
its base, one copy for each; the new `pow` computes the power for the
rest of the exponent, on the second argument of the multiplier, by the
theorem itself; the multiplier then multiplies, by
`Peano.Multiplying.run`.  That theorem is used here in a net that has
other agents, with its result wired where this one needs it, and the
statement that its result is made of new agents is what lets this run
say what it leaves alone.

For a net that has nothing else, with the result on a free port
(`Peano.Power`), the result is a normal form (`Peano.pow_correct`), and
the theorems about the machine apply to the nets `Peano.power e b`: with
any number of threads and any schedule, a run at rest has made exactly
`powCost e b` interactions and holds the numeral `b ^ e`
(`Peano.power_rest`), and a fair run comes to rest (`Peano.power_fair`).
-/

namespace INet

namespace Peano

open Addition (gone gone2)

theorem rule_pow_zero : system.rule pow zero = some powZero.toX.toRhs := rfl
theorem rule_pow_succ : system.rule pow succ = some powSucc.toX.toRhs := rfl

/-- The rule for a power on a zero makes three agents. -/
theorem powZero_lab {o : Option Bool} {j : Nat} {γ : Peano}
    (h : powZero.toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some false ∧ j = 1) ∨ (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) powZero.agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), succ), ((some false, 1), zero),
      ((some true, 0), era)] := assoc_mem h'
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

/-- The rule for a power on a successor makes three agents. -/
theorem powSucc_lab {o : Option Bool} {j : Nat} {γ : Peano}
    (h : powSucc.toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some false ∧ j = 1) ∨ (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) powSucc.agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), dup), ((some false, 1), mul),
      ((some true, 0), pow)] := assoc_mem h'
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

/-! ### The two firings -/

/-- **The power meets a zero.**  The firing puts a successor `U` on the
result, a zero `Z` under it, and an eraser `E` on the base. -/
theorem powZero_step {N : Net Peano} {p z t : Id} {x : Port}
    (hA : Addition.Adder ar pow N p z zero)
    (hpt : N.Paired ar (p, 1) (t, 0)) (hpx : N.Paired ar (p, 2) x)
    (ht : t ≠ p ∧ t ≠ z) (hx : x.1 ≠ p ∧ x.1 ≠ z) :
    ∃ (N₁ : Net Peano) (U Z E : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = p ∨ i = z) N₁ ∧ ¬ N.Used U ∧ ¬ N.Used Z ∧ ¬ N.Used E ∧
      N₁.agent U succ ∧ N₁.agent Z zero ∧ N₁.agent E era ∧
      N₁.Paired ar x (U, 0) ∧ N₁.Paired ar (U, 1) (Z, 0) ∧ N₁.Paired ar (E, 0) (t, 0) ∧
      (∀ i, N.Used i → N₁.Used i) ∧
      ∀ i γ, N₁.agent i γ → (N.agent i γ ∧ i ≠ p ∧ i ≠ z) ∨ i = U ∨ i = Z ∨ i = E := by
  have hN := hA.wf
  have hR : powZero.toX.toRhs.WF ar pow zero := system.rule_wf rule_pow_zero
  have red : Redex system N p z pow zero powZero.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, rule_pow_zero⟩
  have st : Step system N (N.fire p z powZero.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN₁ := Step.wf hN st
  refine ⟨_, child p z (some false) 0, child p z (some false) 1, child p z (some true) 0, st,
    hA.site.keeps _, hA.site.not_used_child _ _, hA.site.not_used_child _ _,
    hA.site.not_used_child _ _, .inr ⟨some false, 0, rfl, rfl⟩, .inr ⟨some false, 1, rfl, rfl⟩,
    .inr ⟨some true, 0, rfl, rfl⟩, ?_, ?_, ?_, fun i hu => Net.used_fire hN hu _ _ _, ?_⟩
  · exact hA.site.paired_fire_ifc_new hR
      (show powZero.toX.toRhs.link (.ifc false 1) (.new (some false) 0 0) from rfl)
      (hpx.symm hN) hx.1 hx.2
  · exact Site.paired_fire_new_new hR
      (show powZero.toX.toRhs.link (.new (some false) 0 1) (.new (some false) 1 0) from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show powZero.toX.toRhs.link (.ifc false 0) (.new (some true) 0 0) from rfl)
      (hpt.symm hN) ht.1 ht.2).symm hN₁
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases powZero_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr e))

/-- **The power meets a successor.**  The firing makes a copier `D` on
the base, a multiplier `M` whose first argument is the first copy and
whose result is the old result, and a power `P` on the rest of the
exponent, whose base is the second copy and whose result is the second
argument of the multiplier. -/
theorem powSucc_step {N : Net Peano} {p s h' t : Id} {x : Port}
    (hA : Addition.Adder ar pow N p s succ) (hpi : N.Paired ar (s, 1) (h', 0))
    (hpt : N.Paired ar (p, 1) (t, 0)) (hpx : N.Paired ar (p, 2) x)
    (hh' : h' ≠ p ∧ h' ≠ s) (ht : t ≠ p ∧ t ≠ s) (hx : x.1 ≠ p ∧ x.1 ≠ s) :
    ∃ (N₁ : Net Peano) (D M P : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = p ∨ i = s) N₁ ∧
      ¬ N.Used D ∧ ¬ N.Used M ∧ ¬ N.Used P ∧
      N₁.agent D dup ∧ N₁.agent M mul ∧ N₁.agent P pow ∧
      N₁.Paired ar (D, 0) (t, 0) ∧ N₁.Paired ar (D, 1) (M, 0) ∧ N₁.Paired ar (D, 2) (P, 1) ∧
      N₁.Paired ar (P, 0) (h', 0) ∧ N₁.Paired ar (P, 2) (M, 1) ∧ N₁.Paired ar (M, 2) x ∧
      (∀ i, N.Used i → N₁.Used i) ∧
      ∀ i γ, N₁.agent i γ → (N.agent i γ ∧ i ≠ p ∧ i ≠ s) ∨ i = D ∨ i = M ∨ i = P := by
  have hN := hA.wf
  have hR : powSucc.toX.toRhs.WF ar pow succ := system.rule_wf rule_pow_succ
  have red : Redex system N p s pow succ powSucc.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, rule_pow_succ⟩
  have st : Step system N (N.fire p s powSucc.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN₁ := Step.wf hN st
  refine ⟨_, child p s (some false) 0, child p s (some false) 1, child p s (some true) 0, st,
    hA.site.keeps _, hA.site.not_used_child _ _, hA.site.not_used_child _ _,
    hA.site.not_used_child _ _, .inr ⟨some false, 0, rfl, rfl⟩, .inr ⟨some false, 1, rfl, rfl⟩,
    .inr ⟨some true, 0, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hu => Net.used_fire hN hu _ _ _, ?_⟩
  · exact (hA.site.paired_fire_ifc_new hR
      (show powSucc.toX.toRhs.link (.ifc false 0) (.new (some false) 0 0) from rfl)
      (hpt.symm hN) ht.1 ht.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show powSucc.toX.toRhs.link (.new (some false) 0 1) (.new (some false) 1 0) from rfl)
  · exact Site.paired_fire_new_new hR
      (show powSucc.toX.toRhs.link (.new (some false) 0 2) (.new (some true) 0 1) from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show powSucc.toX.toRhs.link (.ifc true 0) (.new (some true) 0 0) from rfl)
      (hpi.symm hN) hh'.1 hh'.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show powSucc.toX.toRhs.link (.new (some true) 0 2) (.new (some false) 1 1) from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show powSucc.toX.toRhs.link (.ifc false 1) (.new (some false) 1 2) from rfl)
      (hpx.symm hN) hx.1 hx.2).symm hN₁
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases powSucc_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr e))

/-! ### The power, with anything else around -/

/-- The number of interactions of `b ^ e`: on the zero, one and the
erasure of the base; on a successor, one, the copy of the base, the power
for the rest and the multiplication. -/
def powCost : Nat → Nat → Nat
  | 0, b => b + 1 + 1
  | e + 1, b => b + 1 + 1 + powCost e b + prodCost b (b ^ e)

/-- **The situation of a power, with anything else in the net.**  The
agent `p` faces the head `h₁` of its exponent, a numeral with the agents
`l₁`; its base is a numeral with the head `h₂` and the agents `l₂`; its
result is wired to the port `r`, which is not on the agent or on an agent
of the two numerals. -/
structure Powering (N : Net Peano) (p : Id) (h₁ : Id) (l₁ : List Id) (h₂ : Id)
    (l₂ : List Id) (r : Port) : Prop where
  wf : N.WF ar
  hp : N.agent p pow
  fst : N.Paired ar (p, 0) (h₁, 0)
  num₁ : NumList N h₁ l₁
  snd : N.Paired ar (p, 1) (h₂, 0)
  num₂ : NumList N h₂ l₂
  out : N.Paired ar (p, 2) r
  hr : r.1 ≠ p ∧ ¬ r.1 ∈ l₁ ∧ ¬ r.1 ∈ l₂

/-- **Powers, with anything else around.**  With the numerals `e` and `b`
as exponent and base, the net reduces in `powCost e b` steps to a net in
which the port `r` carries the numeral `b ^ e`, made of agents whose
names were not in use.  Everything away from the agent and its two
arguments is kept, and the agents of the net are zeros, successors, or
agents of the start other than the agent. -/
theorem Powering.run : ∀ (l₁ : List Id) {N : Net Peano} {p h₁ h₂ : Id} {l₂ : List Id}
    {r : Port} {e b : Nat}, Powering N p h₁ l₁ h₂ l₂ r → l₁.length = e + 1 →
    l₂.length = b + 1 →
    ∃ N', Steps (Step system) (powCost e b) N N' ∧
      IsNumQ N' (fun i => ¬ N.Used i) r (b ^ e) ∧ N.Keeps ar (gone2 N p l₁ l₂) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ p)
  | [], _, _, _, _, _, _, _, _, c, _, _ => by cases c.num₁
  | s :: l', N, p, _, h₂, l₂, r, e, b, c, hlen, hlen₂ => by
    have hN := c.wf
    have hp := c.hp
    have hps := c.fst
    have hpt := c.snd
    have hpx := c.out
    have hl₂ := c.num₂
    obtain ⟨hrp, hrl₁, hrl₂⟩ := c.hr
    have hru : N.Used r.1 := Net.End.used hpx.2.1
    have hrs : r.1 ≠ s := fun e' => hrl₁ (by
      rw [e']
      exact List.mem_cons_self)
    have hta : h₂ ≠ p := by
      rcases hl₂.label h₂ hl₂.head_mem with hx' | hx'
      · exact ne_of_agent hN hx' hp (by decide)
      · exact ne_of_agent hN hx' hp (by decide)
    have hav : ∀ t, N.Paired ar (p, 0) (t, 0) → ∀ j, j ∈ l₂ → ¬ (j = p ∨ j = t) := by
      intro t hpt' j hj hc
      rcases hc with e1 | e1
      · rw [e1] at hj
        rcases hl₂.label p hj with hx' | hx'
        · exact absurd (hN.agent_fun hx' hp) (by decide)
        · exact absurd (hN.agent_fun hx' hp) (by decide)
      · rw [e1] at hj
        exact Addition.NumList.not_mem hN hpt' hl₂ hpt (port_ne_snd (by decide)) hj
    have hnum := c.num₁
    cases hnum with
    | last hz =>
      have he : e = 0 := Nat.succ.inj hlen.symm
      have hA : Addition.Adder ar pow N p s zero := ⟨hN, hp, hz, by decide, hps⟩
      have hts : h₂ ≠ s := hA.not_s hpt (port_ne_snd (by decide))
      obtain ⟨N₁, U, Z, E, st, k₁, hU, hZ, hE, aU, aZ, aE, pxU, pUZ, pEt, hused, hag₁⟩ :=
        powZero_step hA hpt hpx ⟨hta, hts⟩ ⟨hrp, hrs⟩
      have hN₁ := Step.wf hN st
      have hl₂₁ : NumList N₁ h₂ l₂ := hl₂.keeps k₁ (hav s hps)
      obtain ⟨N₂, sts, k₂, hag₂⟩ := erase l₂ hN₁ aE pEt hl₂₁
      rw [hlen₂] at sts
      have ngU : ¬ gone N₁ E l₂ U :=
        not_gone (ne_of_agent hN₁ aU aE (by decide)) (fun hm => hU (numList_used hl₂ hm))
          (.inl ⟨_, aU⟩)
      have ngZ : ¬ gone N₁ E l₂ Z :=
        not_gone (ne_of_agent hN₁ aZ aE (by decide)) (fun hm => hZ (numList_used hl₂ hm))
          (.inl ⟨_, aZ⟩)
      have ngr : ¬ gone N₁ E l₂ r.1 := not_gone (fun e' => hE (e' ▸ hru)) hrl₂ (hused _ hru)
      refine ⟨N₂, ?_, ⟨U, [U, Z], k₂.paired pxU ngr ngU,
        .next (k₂.agent aU ngU) (k₂.paired pUZ ngU ngZ) (.last (k₂.agent aZ ngZ)), ?_, ?_⟩,
        (k₁.trans k₂).mono ?_, ?_⟩
      · rw [he]
        exact .head st sts
      · rw [he, Nat.pow_zero]
        rfl
      · intro i hi
        rcases List.mem_cons.1 hi with e1 | hi'
        · rw [e1]
          exact hU
        · rw [List.mem_singleton.1 hi']
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
        rcases hag₁ i γ hi₁ with ⟨hi₀, hia, -⟩ | e1 | e1 | e1
        · exact .inr (.inr ⟨hi₀, hia⟩)
        · rw [e1] at hi₁
          exact .inr (.inl (hN₁.agent_fun hi₁ aU))
        · rw [e1] at hi₁
          exact .inl (hN₁.agent_fun hi₁ aZ)
        · exact absurd e1 hne
    | @next _ h' _ hs hpi hl' =>
      obtain ⟨k, ek, -⟩ := hl'.num
      have he : e = k + 1 := by
        have e' : l'.length + 1 = e + 1 := hlen
        omega
      have hA : Addition.Adder ar pow N p s succ := ⟨hN, hp, hs, by decide, hps⟩
      have hh'p : h' ≠ p := by
        rcases hl'.label h' hl'.head_mem with hx' | hx'
        · exact hA.ne_add hx' (by decide)
        · exact hA.ne_add hx' (by decide)
      have hh's : h' ≠ s := hA.not_s hpi (port_ne_snd (by decide))
      have hts : h₂ ≠ s := hA.not_s hpt (port_ne_snd (by decide))
      obtain ⟨N₁, D, M, P, st, k₁, hD, hM, hP, aD, aM, aP, pDt, pDM, pDP, pPh, pPM, pMx,
        hused, hag₁⟩ := powSucc_step hA hpi hpt hpx ⟨hh'p, hh's⟩ ⟨hta, hts⟩ ⟨hrp, hrs⟩
      have hN₁ := Step.wf hN st
      have hl₂₁ : NumList N₁ h₂ l₂ := hl₂.keeps k₁ (hav s hps)
      have havh : ∀ j, j ∈ l' → ¬ (j = p ∨ j = s) := by
        intro j hj hc
        rcases hc with e1 | e1
        · rw [e1] at hj
          rcases hl'.label p hj with hx' | hx'
          · exact absurd (hN.agent_fun hx' hp) (by decide)
          · exact absurd (hN.agent_fun hx' hp) (by decide)
        · rw [e1] at hj
          exact Addition.NumList.not_mem hN hps hl' hpi (port_ne_snd (by decide)) hj
      have hl'₁ : NumList N₁ h' l' := hl'.keeps k₁ havh
      have hru₁ : N₁.Used r.1 := hused _ hru
      -- the copy
      have hMl : ¬ M ∈ l₂ := fun hm => hM (numList_used hl₂ hm)
      have hPl : ¬ P ∈ l₂ := fun hm => hP (numList_used hl₂ hm)
      obtain ⟨N₂, sts₂, ⟨cM, lM, pM, hlM, elM, fM⟩, ⟨cP, lP, pP, hlP, elP, fP⟩, k₂, hag₂⟩ :=
        copy_fresh hN₁ aD pDt hl₂₁ hlen₂ pDM pDP
          ⟨ne_of_agent hN₁ aM aD (by decide), hMl⟩ ⟨ne_of_agent hN₁ aP aD (by decide), hPl⟩
      have hN₂ := Steps.wf hN₁ sts₂
      have U₂ : ∀ i, N.Used i → N₂.Used i := fun i hu => Steps.used hN₁ sts₂ (hused i hu)
      have hC₂ : Addition.Closed ar (gone N₁ D l₂) N₁ := Addition.gone_closed hN₁ pDt hl₂₁
      have ngM : ¬ gone N₁ D l₂ M :=
        not_gone (ne_of_agent hN₁ aM aD (by decide)) hMl (.inl ⟨_, aM⟩)
      have ngP : ¬ gone N₁ D l₂ P :=
        not_gone (ne_of_agent hN₁ aP aD (by decide)) hPl (.inl ⟨_, aP⟩)
      have ngr : ¬ gone N₁ D l₂ r.1 := not_gone (fun e' => hD (e' ▸ hru)) hrl₂ hru₁
      -- what the copy keeps
      have havl' : ∀ j, j ∈ l' → ¬ gone N₁ D l₂ j := hl'₁.avoid hC₂ pPh ngP
      have hl'₂ : NumList N₂ h' l' := hl'₁.keeps k₂ havl'
      have pPh₂ : N₂.Paired ar (P, 0) (h', 0) := k₂.paired pPh ngP (havl' h' hl'₁.head_mem)
      have aP₂ : N₂.agent P pow := k₂.agent aP ngP
      have aM₂ : N₂.agent M mul := k₂.agent aM ngM
      have pPM₂ : N₂.Paired ar (P, 2) (M, 1) := k₂.paired pPM ngP ngM
      have pMx₂ : N₂.Paired ar (M, 2) r := k₂.paired pMx ngM ngr
      -- the power for the rest, with its result on the second argument of the multiplier
      have hMl' : ¬ M ∈ l' := fun hm => hM (numList_used hl' hm)
      have hMlP : ¬ M ∈ lP := fun hm =>
        (hlP.label _ hm).elim (fun h => absurd (hN₂.agent_fun h aM₂) (by decide))
          fun h => absurd (hN₂.agent_fun h aM₂) (by decide)
      have hMP : M ≠ P := ne_of_agent hN₂ aM₂ aP₂ (by decide)
      have cP' : Powering N₂ P h' l' cP lP (M, 1) :=
        ⟨hN₂, aP₂, pPh₂, hl'₂, pP, hlP, pPM₂, hMP, hMl', hMlP⟩
      obtain ⟨N₃, sts₃, ⟨cv, lv, pv, hlv, elv, fv⟩, k₃, hag₃⟩ := Powering.run l' cP' ek elP
      have hN₃ := Steps.wf hN₂ sts₃
      have U₃ : ∀ i, N.Used i → N₃.Used i := fun i hu => Steps.used hN₂ sts₃ (U₂ i hu)
      have hC₃ : Addition.Closed ar (gone2 N₂ P l' lP) N₂ :=
        Addition.gone2_closed hN₂ pPh₂ hl'₂ pP hlP
      -- what it keeps: the multiplier, its first argument and the result port
      have ng3M : ¬ gone2 N₂ P l' lP M := not_gone2 hMP hMl' hMlP (.inl ⟨_, aM₂⟩)
      have havlM : ∀ j, j ∈ lM → ¬ gone2 N₂ P l' lP j := hlM.avoid hC₃ pM ng3M
      have hlM₃ : NumList N₃ cM lM := hlM.keeps k₃ havlM
      have pM₃ : N₃.Paired ar (M, 0) (cM, 0) := k₃.paired pM ng3M (havlM cM hlM.head_mem)
      have aM₃ : N₃.agent M mul := k₃.agent aM₂ ng3M
      have ng3r : ¬ gone2 N₂ P l' lP r.1 :=
        not_gone2 (fun e' => hP (e' ▸ hru)) (fun hm => hrl₁ (List.mem_cons_of_mem _ hm))
          (fun hm => fP _ hm hru₁) (U₂ _ hru)
      have pMx₃ : N₃.Paired ar (M, 2) r := k₃.paired pMx₂ ng3M ng3r
      -- the multiplier multiplies
      have cMul : Multiplying N₃ M cM lM cv lv r :=
        ⟨hN₃, aM₃, pM₃, hlM₃, pv, hlv, pMx₃, fun e' => hM (e' ▸ hru), fun hm => fM _ hm hru₁,
          fun hm => fv _ hm (U₂ _ hru)⟩
      obtain ⟨N₄, sts₄, ⟨cw, lw, pw, hlw, elw, fw⟩, k₄, hag₄⟩ := Multiplying.run lM cMul elM elv
      have ev : b ^ e = b * b ^ k := by
        rw [he, Nat.pow_succ, Nat.mul_comm]
      refine ⟨N₄, ?_, ⟨cw, lw, pw, hlw, ?_, fun i hi hu => fw i hi (U₃ i hu)⟩,
        (((k₁.trans k₂).trans k₃).trans k₄).mono ?_, ?_⟩
      · rw [he]
        exact ((Steps.head st sts₂).trans sts₃).trans sts₄
      · rw [ev]
        exact elw
      · rintro i ((((e1 | e1) | (e1 | hm' | hu)) | (e1 | hm' | hm' | hu)) |
          (e1 | hm' | hm' | hu))
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
            exact hP)))
        · exact .inr (.inl (List.mem_cons_of_mem _ hm'))
        · exact .inr (.inr (.inr fun hu' => fP i hm' (hused i hu')))
        · exact .inr (.inr (.inr fun hu' => hu (U₂ i hu')))
        · exact .inr (.inr (.inr (by
            rw [e1]
            exact hM)))
        · exact .inr (.inr (.inr fun hu' => fM i hm' (hused i hu')))
        · exact .inr (.inr (.inr fun hu' => fv i hm' (U₂ i hu')))
        · exact .inr (.inr (.inr fun hu' => hu (U₃ i hu')))
      · intro i γ hi
        rcases hag₄ i γ hi with hz | hsu | ⟨hi₃, hneM⟩
        · exact .inl hz
        · exact .inr (.inl hsu)
        · rcases hag₃ i γ hi₃ with hz | hsu | ⟨hi₂, hneP⟩
          · exact .inl hz
          · exact .inr (.inl hsu)
          · rcases hag₂ i γ hi₂ with hz | hsu | ⟨hi₁, hneD⟩
            · exact .inl hz
            · exact .inr (.inl hsu)
            · rcases hag₁ i γ hi₁ with ⟨hi₀, hia, -⟩ | e1 | e1 | e1
              · exact .inr (.inr ⟨hi₀, hia⟩)
              · exact absurd e1 hneD
              · exact absurd e1 hneM
              · exact absurd e1 hneP

/-! ### Powers are correct -/

variable {N : Net Peano} {r : Port}

/-- **The situation of a power.**  The agent `p` has the numerals `e` and
`b` as exponent and base and the free port `r` as result, and the net has
no other agents than it and the successors and zeros. -/
structure Power (N : Net Peano) (p : Id) (e b : Nat) (r : Port) : Prop where
  wf : N.WF ar
  hp : N.agent p pow
  fst : IsNum N (p, 0) e
  snd : IsNum N (p, 1) b
  out : N.Paired ar (p, 2) r
  free : N.free r
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = p

/-- **The run of a power**: in `powCost e b` steps the net becomes one
that has the numeral `b ^ e` on the result port and whose agents are
successors and zeros. -/
theorem pow_steps {p : Id} {e b : Nat} (c : Power N p e b r) :
    ∃ N', Steps (Step system) (powCost e b) N N' ∧ IsNum N' r (b ^ e) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ := by
  have hN := c.wf
  obtain ⟨h₁, hp₁, hn₁⟩ := c.fst
  obtain ⟨l₁, hl₁, e₁⟩ := Addition.Num.list hn₁
  obtain ⟨h₂, hp₂, hn₂⟩ := c.snd
  obtain ⟨l₂, hl₂, e₂⟩ := Addition.Num.list hn₂
  have hrl : ∀ (h : Id) (l : List Id), NumList N h l → ¬ r.1 ∈ l := fun h l hl hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  have cP : Powering N p h₁ l₁ h₂ l₂ r :=
    ⟨hN, c.hp, hp₁, hl₁, hp₂, hl₂, c.out,
      fun e' => hN.free_agent (i := r.1) (k := r.2) c.free (e' ▸ c.hp), hrl _ _ hl₁,
      hrl _ _ hl₂⟩
  obtain ⟨N', sts, hres, -, hag⟩ := Powering.run l₁ cP e₁ e₂
  refine ⟨N', sts, hres.isNum, fun i γ hi => ?_⟩
  rcases hag i γ hi with hz | hsu | ⟨hi₀, hne⟩
  · exact .inl hz
  · exact .inr hsu
  · rcases c.only i γ hi₀ with hz | hsu | e'
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e' hne

/-- **Powers are correct, for all inputs.**  A net whose agent `pow` has
the numerals `e` and `b` as exponent and base and the free port `r` as
result reduces, in `powCost e b` steps, to a normal form in which `r`
carries the numeral `b ^ e`. -/
theorem pow_correct {p : Id} {e b : Nat} (c : Power N p e b r) :
    ∃ N', Steps (Step system) (powCost e b) N N' ∧ Normal (Step system) N' ∧
      IsNum N' r (b ^ e) := by
  obtain ⟨N', sts, hnum, hag⟩ := pow_steps c
  exact ⟨N', sts, normal_of_numerals hag, hnum⟩

/-! ### The nets for `b ^ e`, and the machine on them -/

/-- The net for `0 ^ 0`, with the result on the free port `([0], 0)`. -/
def powerBase : XNet Peano :=
  XNet.ofWires [([1], pow), ([2], zero), ([3], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

/-- The net for `b ^ 0`. -/
def powerSnd : Nat → XNet Peano
  | 0 => powerBase
  | b + 1 => (powerSnd b).pushOn succ ([1], 1) [b + 4]

/-- The net for `b ^ e`, with the result on the free port `([0], 0)`: `e`
successors are put on the exponent of the agent of `0 ^ 0`, and `b` on
its base. -/
def power : Nat → Nat → XNet Peano
  | 0, b => powerSnd b
  | e + 1, b => (power e b).pushOn succ ([1], 0) [e + b + 4]

/-- The situation of a power, on a valid input whose identifiers are
numbered below `c`. -/
structure GoodPower (X : XNet Peano) (e b c : Nat) : Prop where
  ok : X.Ok ar
  config : Power X.toNet [1] e b ([0], 0)
  below : X.Below c

/-- One more successor on the exponent. -/
theorem GoodPower.push_fst {X : XNet Peano} {e b c : Nat} (g : GoodPower X e b c) :
    GoodPower (X.pushOn succ ([1], 0) [c]) (e + 1) b (c + 1) := by
  have cf := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := cf.fst
  obtain ⟨t, hpt, hnt⟩ := cf.snd
  have hm' : (X.toNet.insert1 [c] succ ([1], 0) (h, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hph) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ X.toNet i k →
      Addition.Num ar zero succ (X.toNet.insert1 [c] succ ([1], 0) (h, 0)) i k :=
    Addition.Num.insert1 hm' hm (fun _ _ => port_ne_snd (by decide))
      (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, g.below.pushOn hX hph succ⟩
  · rw [XNet.pushOn_eq hX hph, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [XNet.pushOn_eq hX hph, XNet.insert1_toNet]
    refine ⟨hm'.wf, .inl cf.hp, ?_, ?_, ?_, cf.free, ?_⟩
    · exact ⟨[c], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, h,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnh⟩
    · exact ⟨t, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hpt, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩), hnum hnt⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 cf.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)
    · rintro i γ (hi | ⟨-, e'⟩)
      · exact cf.only i γ hi
      · exact .inr (.inl e')

/-- One more successor on the base. -/
theorem GoodPower.push_snd {X : XNet Peano} {e b c : Nat} (g : GoodPower X e b c) :
    GoodPower (X.pushOn succ ([1], 1) [c]) e (b + 1) (c + 1) := by
  have cf := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := cf.fst
  obtain ⟨t, hpt, hnt⟩ := cf.snd
  have hsucc : ∀ i, X.toNet.agent i succ → i ≠ [1] := by
    rintro i hi rfl
    exact absurd (cf.wf.agent_fun hi cf.hp) (by decide)
  have ht1 : t ≠ [1] := by
    rintro rfl
    rcases Addition.Num.label hnt with hl | hl
    · exact absurd (cf.wf.agent_fun hl cf.hp) (by decide)
    · exact absurd (cf.wf.agent_fun hl cf.hp) (by decide)
  have hm' : (X.toNet.insert1 [c] succ ([1], 1) (t, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hpt) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ X.toNet i k →
      Addition.Num ar zero succ (X.toNet.insert1 [c] succ ([1], 1) (t, 0)) i k :=
    Addition.Num.insert1 hm' hm (fun i hi e' => hsucc i hi (congrArg Prod.fst e'))
      (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, g.below.pushOn hX hpt succ⟩
  · rw [XNet.pushOn_eq hX hpt, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [XNet.pushOn_eq hX hpt, XNet.insert1_toNet]
    refine ⟨hm'.wf, .inl cf.hp, ?_, ?_, ?_, cf.free, ?_⟩
    · exact ⟨h, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hph, port_ne_snd (by decide),
        fun e' => ht1 (congrArg Prod.fst e').symm⟩), hnum hnh⟩
    · exact ⟨[c], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, t,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnt⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 cf.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)
    · rintro i γ (hi | ⟨-, e'⟩)
      · exact cf.only i γ hi
      · exact .inr (.inl e')

theorem good_powerBase : GoodPower powerBase 0 0 4 := by
  have hX : powerBase.Ok ar := by decide
  refine ⟨hX, ⟨hX.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show ([1], pow) ∈ powerBase.agents
    decide
  · exact ⟨[2], hX.link_iff.1 (by decide), show ([2], zero) ∈ powerBase.agents by decide⟩
  · exact ⟨[3], hX.link_iff.1 (by decide), show ([3], zero) ∈ powerBase.agents by decide⟩
  · exact hX.link_iff.1 (by decide)
  · show ([0], 0) ∈ powerBase.free
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), pow), ([2], zero), ([3], zero)] := hi
    rcases List.mem_cons.1 hi' with e | hi''
    · exact .inr (.inr (Prod.mk.inj e).1)
    · rcases List.mem_cons.1 hi'' with e | hi'''
      · exact .inl (Prod.mk.inj e).2
      · rcases List.mem_cons.1 hi''' with e | h4
        · exact .inl (Prod.mk.inj e).2
        · exact absurd h4 List.not_mem_nil
  · intro i hi
    have hall : ∀ i ∈ powerBase.usedIds, ∃ j, j < 4 ∧ i = [j] := by decide
    exact hall i (XNet.mem_usedIds hi)

theorem good_powerSnd : ∀ b, GoodPower (powerSnd b) 0 b (b + 4)
  | 0 => good_powerBase
  | b + 1 => (good_powerSnd b).push_snd

/-- **The nets for `b ^ e` are powers**, for all `e` and `b`. -/
theorem good_power : ∀ e b, GoodPower (power e b) e b (e + b + 4)
  | 0, b => by
    rw [Nat.zero_add]
    exact good_powerSnd b
  | e + 1, b => by
    have h : e + 1 + b + 4 = e + b + 4 + 1 := by omega
    rw [h]
    exact (good_power e b).push_fst

/-- The nets for `b ^ e` are valid inputs of the reducer, for all `e` and
`b`. -/
theorem power_ok (e b : Nat) : (power e b).Ok ar := (good_power e b).ok

/-- **Powers come out right, whatever the threads do**: with any number
of threads and any schedule, a run of the machine on the net for `b ^ e`
that is at rest has made exactly `powCost e b` interactions, and its
memory has the numeral `b ^ e` on the free port. -/
theorem power_rest (e b : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (power e b) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (power e b) nt).trace xsys σ i).2 = powCost e b ∧
      IsNum ((XMach.init (power e b) nt).trace xsys σ i).1.mem.toNet ([0], 0) (b ^ e) := by
  have g := good_power e b
  obtain ⟨N', hs, hn', hnum⟩ := pow_correct g.config
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (power e b) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (power e b) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **Powers under any fair schedule**: with any number of threads, as
long as every thread keeps being scheduled, the run comes to rest after
`powCost e b` interactions with the numeral `b ^ e` in memory. -/
theorem power_fair (e b : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (power e b) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (power e b) nt).trace xsys σ i).2 = powCost e b ∧
      IsNum ((XMach.init (power e b) nt).trace xsys σ i).1.mem.toNet ([0], 0) (b ^ e) := by
  have g := good_power e b
  obtain ⟨N', hs, hn', hnum⟩ := pow_correct g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- The count for `2 ^ 3`. -/
example : powCost 3 2 = 75 := by decide

/-- The reducer on the net for `2 ^ 3` stops after 75 steps on a net whose
agents are eight successors and a zero. -/
example : ((power 3 2).normalize xsys 200).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) = some (75, 8, 1, 9) := by
  decide +kernel

end Peano

end INet
