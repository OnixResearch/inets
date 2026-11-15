import InteractionNets.PeanoPow

/-! # What it is to compute, and factorials

The theorems for the multiplier and for powers have the same shape.  It
is stated here once.  `Peano.Computes2 op f c`: in any net, an agent with
the symbol `op` whose two arguments are the numerals `m` and `n`, with
its result wired to any port not on it or on its arguments, reduces in
`c m n` steps to a net in which that port carries the numeral `f m n`,
made of new agents; everything away from the agent and its arguments is
kept, and the agents of the net are zeros, successors, or agents of the
start other than the agent.  `Peano.Computes1` is the same for one
argument.  The multiplier and the power are two cases
(`Peano.mul_computes`, `Peano.pow_computes`).

The factorial is the test: an agent `fac` with the rules `0! = 1` and
`(S x)! = x! * S x`.  It computes the factorial in this sense
(`Peano.fac_computes`).  The proof is by recursion on the argument and
uses the multiplier only through `Peano.mul_computes`, on a first
argument that is the result of the factorial of the rest and a second
argument that is a new successor on a copy.

For a net that has nothing else (`Peano.Factorial`) the result is a
normal form (`Peano.fac_correct`), and on the machine a run on the net
`Peano.facNet n` that is at rest has made exactly `facCost n`
interactions and holds the numeral `n!` (`Peano.fac_rest`,
`Peano.fac_fair`).
-/

namespace INet

namespace Peano

open Addition (gone gone2)

/-! ### The shape of the theorems -/

/-- **An agent that computes a function of two numerals, in any net.** -/
def Computes2 (op : Peano) (f c : Nat → Nat → Nat) : Prop :=
  ∀ (l₁ : List Id) {N : Net Peano} {a h₁ h₂ : Id} {l₂ : List Id} {r : Port} {m n : Nat},
    N.WF ar → N.agent a op → N.Paired ar (a, 0) (h₁, 0) → NumList N h₁ l₁ →
    N.Paired ar (a, 1) (h₂, 0) → NumList N h₂ l₂ → N.Paired ar (a, 2) r →
    r.1 ≠ a ∧ ¬ r.1 ∈ l₁ ∧ ¬ r.1 ∈ l₂ → l₁.length = m + 1 → l₂.length = n + 1 →
    ∃ N', Steps (Step system) (c m n) N N' ∧
      IsNumQ N' (fun i => ¬ N.Used i) r (f m n) ∧ N.Keeps ar (gone2 N a l₁ l₂) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)

/-- **An agent that computes a function of one numeral, in any net.** -/
def Computes1 (op : Peano) (f c : Nat → Nat) : Prop :=
  ∀ (l : List Id) {N : Net Peano} {a h : Id} {r : Port} {n : Nat},
    N.WF ar → N.agent a op → N.Paired ar (a, 0) (h, 0) → NumList N h l →
    N.Paired ar (a, 1) r → r.1 ≠ a ∧ ¬ r.1 ∈ l → l.length = n + 1 →
    ∃ N', Steps (Step system) (c n) N N' ∧
      IsNumQ N' (fun i => ¬ N.Used i) r (f n) ∧ N.Keeps ar (gone N a l) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)

/-- **The multiplier computes the product.** -/
theorem mul_computes : Computes2 mul (fun m n => m * n) prodCost :=
  fun l₁ _ _ _ _ _ _ _ _ hN ha h1 n1 h2 n2 ho hr e1 e2 =>
    Multiplying.run l₁ ⟨hN, ha, h1, n1, h2, n2, ho, hr⟩ e1 e2

/-- **The power computes the power**, of the base, its second argument,
to the exponent, its first. -/
theorem pow_computes : Computes2 pow (fun e b => b ^ e) powCost :=
  fun l₁ _ _ _ _ _ _ _ _ hN ha h1 n1 h2 n2 ho hr e1 e2 =>
    Powering.run l₁ ⟨hN, ha, h1, n1, h2, n2, ho, hr⟩ e1 e2

/-! ### The factorial -/

/-- The factorial of a number. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)

/-- The number of interactions of `n!`: on the zero, one; on a successor,
one, the copy of the rest, the factorial of the rest and the
multiplication. -/
def facCost : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1 + 1 + facCost n + prodCost (fact n) (n + 1)

theorem rule_fac_zero : system.rule fac zero = some facZero.toX.toRhs := rfl
theorem rule_fac_succ : system.rule fac succ = some facSucc.toX.toRhs := rfl

/-- The rule for a factorial on a zero makes two agents. -/
theorem facZero_lab {o : Option Bool} {j : Nat} {γ : Peano}
    (h : facZero.toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some false ∧ j = 1) := by
  have h' : assoc (o, j) facZero.agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), succ), ((some false, 1), zero)] :=
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

/-- The rule for a factorial on a successor makes four agents. -/
theorem facSucc_lab {o : Option Bool} {j : Nat} {γ : Peano}
    (h : facSucc.toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some false ∧ j = 1) ∨ (o = some false ∧ j = 2) ∨
      (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) facSucc.agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), dup), ((some false, 1), succ),
      ((some false, 2), mul), ((some true, 0), fac)] := assoc_mem h'
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
        exact .inr (.inr (.inl ⟨e3, e4⟩))
      · rcases List.mem_cons.1 hm''' with e | h4
        · injection e with e1 _
          injection e1 with e3 e4
          exact .inr (.inr (.inr ⟨e3, e4⟩))
        · exact absurd h4 List.not_mem_nil

/-- **The factorial meets a zero.**  The firing puts a successor `U` on
the result and a zero `Z` under it. -/
theorem facZero_step {N : Net Peano} {a z : Id} {x : Port}
    (hA : Addition.Adder ar fac N a z zero) (hpx : N.Paired ar (a, 1) x)
    (hx : x.1 ≠ a ∧ x.1 ≠ z) :
    ∃ (N₁ : Net Peano) (U Z : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = a ∨ i = z) N₁ ∧ ¬ N.Used U ∧ ¬ N.Used Z ∧
      N₁.agent U succ ∧ N₁.agent Z zero ∧
      N₁.Paired ar x (U, 0) ∧ N₁.Paired ar (U, 1) (Z, 0) ∧
      ∀ i γ, N₁.agent i γ → (N.agent i γ ∧ i ≠ a ∧ i ≠ z) ∨ i = U ∨ i = Z := by
  have hN := hA.wf
  have hR : facZero.toX.toRhs.WF ar fac zero := system.rule_wf rule_fac_zero
  have red : Redex system N a z fac zero facZero.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, rule_fac_zero⟩
  have st : Step system N (N.fire a z facZero.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  refine ⟨_, child a z (some false) 0, child a z (some false) 1, st, hA.site.keeps _,
    hA.site.not_used_child _ _, hA.site.not_used_child _ _, .inr ⟨some false, 0, rfl, rfl⟩,
    .inr ⟨some false, 1, rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact hA.site.paired_fire_ifc_new hR
      (show facZero.toX.toRhs.link (.ifc false 0) (.new (some false) 0 0) from rfl)
      (hpx.symm hN) hx.1 hx.2
  · exact Site.paired_fire_new_new hR
      (show facZero.toX.toRhs.link (.new (some false) 0 1) (.new (some false) 1 0) from rfl)
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases facZero_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr e)

/-- **The factorial meets a successor.**  The firing makes a copier `D`
on the rest of the argument, a successor `U` on the first copy, a
factorial `F` on the second copy, and a multiplier `M` whose first
argument is the result of `F`, whose second argument is `U`, and whose
result is the old result. -/
theorem facSucc_step {N : Net Peano} {a s h' : Id} {x : Port}
    (hA : Addition.Adder ar fac N a s succ) (hpi : N.Paired ar (s, 1) (h', 0))
    (hpx : N.Paired ar (a, 1) x) (hh' : h' ≠ a ∧ h' ≠ s) (hx : x.1 ≠ a ∧ x.1 ≠ s) :
    ∃ (N₁ : Net Peano) (D U M F : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = a ∨ i = s) N₁ ∧
      ¬ N.Used D ∧ ¬ N.Used U ∧ ¬ N.Used M ∧ ¬ N.Used F ∧
      N₁.agent D dup ∧ N₁.agent U succ ∧ N₁.agent M mul ∧ N₁.agent F fac ∧
      N₁.Paired ar (D, 0) (h', 0) ∧ N₁.Paired ar (D, 1) (U, 1) ∧ N₁.Paired ar (D, 2) (F, 0) ∧
      N₁.Paired ar (F, 1) (M, 0) ∧ N₁.Paired ar (U, 0) (M, 1) ∧ N₁.Paired ar (M, 2) x ∧
      (∀ i, N.Used i → N₁.Used i) ∧
      ∀ i γ, N₁.agent i γ →
        (N.agent i γ ∧ i ≠ a ∧ i ≠ s) ∨ i = D ∨ i = U ∨ i = M ∨ i = F := by
  have hN := hA.wf
  have hR : facSucc.toX.toRhs.WF ar fac succ := system.rule_wf rule_fac_succ
  have red : Redex system N a s fac succ facSucc.toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, rule_fac_succ⟩
  have st : Step system N (N.fire a s facSucc.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN₁ := Step.wf hN st
  refine ⟨_, child a s (some false) 0, child a s (some false) 1, child a s (some false) 2,
    child a s (some true) 0, st, hA.site.keeps _, hA.site.not_used_child _ _,
    hA.site.not_used_child _ _, hA.site.not_used_child _ _, hA.site.not_used_child _ _,
    .inr ⟨some false, 0, rfl, rfl⟩, .inr ⟨some false, 1, rfl, rfl⟩,
    .inr ⟨some false, 2, rfl, rfl⟩, .inr ⟨some true, 0, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hu => Net.used_fire hN hu _ _ _, ?_⟩
  · exact (hA.site.paired_fire_ifc_new hR
      (show facSucc.toX.toRhs.link (.ifc true 0) (.new (some false) 0 0) from rfl)
      (hpi.symm hN) hh'.1 hh'.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show facSucc.toX.toRhs.link (.new (some false) 0 1) (.new (some false) 1 1) from rfl)
  · exact Site.paired_fire_new_new hR
      (show facSucc.toX.toRhs.link (.new (some false) 0 2) (.new (some true) 0 0) from rfl)
  · exact Site.paired_fire_new_new hR
      (show facSucc.toX.toRhs.link (.new (some true) 0 1) (.new (some false) 2 0) from rfl)
  · exact Site.paired_fire_new_new hR
      (show facSucc.toX.toRhs.link (.new (some false) 1 0) (.new (some false) 2 1) from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show facSucc.toX.toRhs.link (.ifc false 0) (.new (some false) 2 2) from rfl)
      (hpx.symm hN) hx.1 hx.2).symm hN₁
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases facSucc_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr (.inl e)))
      · exact .inr (.inr (.inr (.inr e)))

/-- **The factorial computes the factorial.**  On a zero, the agent puts
the numeral `1` on its result.  On a successor it copies the rest of its
argument; the factorial of one copy is computed first, on the first
argument of the multiplier that was left behind; the multiplier then
multiplies it by the successor of the other copy. -/
theorem fac_computes : Computes1 fac fact facCost
  | [], _, _, _, _, _, _, _, _, hl, _, _, _ => by cases hl
  | s :: l', N, a, _, r, n, hN, ha, hps, hnum, hpx, hr, hlen => by
    obtain ⟨hra, hrl⟩ := hr
    have hru : N.Used r.1 := Net.End.used hpx.2.1
    have hrs : r.1 ≠ s := fun e' => hrl (by
      rw [e']
      exact List.mem_cons_self)
    cases hnum with
    | last hz =>
      have hn : n = 0 := Nat.succ.inj hlen.symm
      have hA : Addition.Adder ar fac N a s zero := ⟨hN, ha, hz, by decide, hps⟩
      obtain ⟨N₁, U, Z, st, k₁, hU, hZ, aU, aZ, pxU, pUZ, hag₁⟩ := facZero_step hA hpx ⟨hra, hrs⟩
      have hN₁ := Step.wf hN st
      refine ⟨N₁, ?_, ⟨U, [U, Z], pxU, .next aU pUZ (.last aZ), ?_, ?_⟩, k₁.mono ?_, ?_⟩
      · rw [hn]
        exact .single st
      · rw [hn]
        rfl
      · intro i hi
        rcases List.mem_cons.1 hi with e1 | hi'
        · rw [e1]
          exact hU
        · rw [List.mem_singleton.1 hi']
          exact hZ
      · rintro i (e1 | e1)
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
      · intro i γ hi
        rcases hag₁ i γ hi with ⟨hi₀, hia, -⟩ | e1 | e1
        · exact .inr (.inr ⟨hi₀, hia⟩)
        · rw [e1] at hi
          exact .inr (.inl (hN₁.agent_fun hi aU))
        · rw [e1] at hi
          exact .inl (hN₁.agent_fun hi aZ)
    | @next _ h' _ hs hpi hl' =>
      obtain ⟨k, ek, -⟩ := hl'.num
      have hn : n = k + 1 := by
        have e' : l'.length + 1 = n + 1 := hlen
        omega
      have hA : Addition.Adder ar fac N a s succ := ⟨hN, ha, hs, by decide, hps⟩
      have hh'a : h' ≠ a := by
        rcases hl'.label h' hl'.head_mem with hx' | hx'
        · exact hA.ne_add hx' (by decide)
        · exact hA.ne_add hx' (by decide)
      have hh's : h' ≠ s := hA.not_s hpi (port_ne_snd (by decide))
      obtain ⟨N₁, D, U, M, F, st, k₁, hD, hU, hM, hF, aD, aU, aM, aF, pDh, pDU, pDF, pFM, pUM,
        pMx, hused, hag₁⟩ := facSucc_step hA hpi hpx ⟨hh'a, hh's⟩ ⟨hra, hrs⟩
      have hN₁ := Step.wf hN st
      have hru₁ : N₁.Used r.1 := hused _ hru
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
      have hrl' : ¬ r.1 ∈ l' := fun hm => hrl (List.mem_cons_of_mem _ hm)
      -- the copy of the rest
      have hUl : ¬ U ∈ l' := fun hm => hU (numList_used hl' hm)
      have hMl : ¬ M ∈ l' := fun hm => hM (numList_used hl' hm)
      have hFl : ¬ F ∈ l' := fun hm => hF (numList_used hl' hm)
      obtain ⟨N₂, sts₂, ⟨cU, lU, pU, hlU, elU, fU⟩, ⟨cF, lF, pF, hlF, elF, fF⟩, k₂, hag₂⟩ :=
        copy_fresh hN₁ aD pDh hl'₁ ek pDU pDF
          ⟨ne_of_agent hN₁ aU aD (by decide), hUl⟩ ⟨ne_of_agent hN₁ aF aD (by decide), hFl⟩
      have hN₂ := Steps.wf hN₁ sts₂
      have U₂ : ∀ i, N.Used i → N₂.Used i := fun i hu => Steps.used hN₁ sts₂ (hused i hu)
      have ngU : ¬ gone N₁ D l' U :=
        not_gone (ne_of_agent hN₁ aU aD (by decide)) hUl (.inl ⟨_, aU⟩)
      have ngM : ¬ gone N₁ D l' M :=
        not_gone (ne_of_agent hN₁ aM aD (by decide)) hMl (.inl ⟨_, aM⟩)
      have ngF : ¬ gone N₁ D l' F :=
        not_gone (ne_of_agent hN₁ aF aD (by decide)) hFl (.inl ⟨_, aF⟩)
      have ngr : ¬ gone N₁ D l' r.1 := not_gone (fun e' => hD (e' ▸ hru)) hrl' hru₁
      have aU₂ : N₂.agent U succ := k₂.agent aU ngU
      have aM₂ : N₂.agent M mul := k₂.agent aM ngM
      have aF₂ : N₂.agent F fac := k₂.agent aF ngF
      have pFM₂ : N₂.Paired ar (F, 1) (M, 0) := k₂.paired pFM ngF ngM
      have pUM₂ : N₂.Paired ar (U, 0) (M, 1) := k₂.paired pUM ngU ngM
      have pMx₂ : N₂.Paired ar (M, 2) r := k₂.paired pMx ngM ngr
      -- the factorial of the rest, with its result on the first argument of the multiplier
      have hMF : M ≠ F := ne_of_agent hN₂ aM₂ aF₂ (by decide)
      have hMlF : ¬ M ∈ lF := fun hm => fF _ hm (.inl ⟨_, aM⟩)
      obtain ⟨N₃, sts₃, ⟨cv, lv, pv, hlv, elv, fv⟩, k₃, hag₃⟩ :=
        fac_computes lF hN₂ aF₂ pF hlF pFM₂ ⟨hMF, hMlF⟩ elF
      have hN₃ := Steps.wf hN₂ sts₃
      have U₃ : ∀ i, N.Used i → N₃.Used i := fun i hu => Steps.used hN₂ sts₃ (U₂ i hu)
      have hC₃ : Addition.Closed ar (gone N₂ F lF) N₂ := Addition.gone_closed hN₂ pF hlF
      -- what it keeps: the multiplier, the successor and the copy under it, the result port
      have ng3M : ¬ gone N₂ F lF M := not_gone hMF hMlF (.inl ⟨_, aM₂⟩)
      have ng3U : ¬ gone N₂ F lF U :=
        not_gone (ne_of_agent hN₂ aU₂ aF₂ (by decide)) (fun hm => fF _ hm (.inl ⟨_, aU⟩))
          (.inl ⟨_, aU₂⟩)
      have ng3r : ¬ gone N₂ F lF r.1 :=
        not_gone (fun e' => hF (e' ▸ hru)) (fun hm => fF _ hm hru₁) (U₂ _ hru)
      have havlU : ∀ j, j ∈ lU → ¬ gone N₂ F lF j := hlU.avoid hC₃ pU ng3U
      have hlU₃ : NumList N₃ cU lU := hlU.keeps k₃ havlU
      have pU₃ : N₃.Paired ar (U, 1) (cU, 0) := k₃.paired pU ng3U (havlU cU hlU.head_mem)
      have aU₃ : N₃.agent U succ := k₃.agent aU₂ ng3U
      have aM₃ : N₃.agent M mul := k₃.agent aM₂ ng3M
      have pUM₃ : N₃.Paired ar (U, 0) (M, 1) := k₃.paired pUM₂ ng3U ng3M
      have pMx₃ : N₃.Paired ar (M, 2) r := k₃.paired pMx₂ ng3M ng3r
      -- the multiplier multiplies
      have hrUl : ¬ r.1 ∈ U :: lU := fun hm =>
        (List.mem_cons.1 hm).elim (fun e' => hU (e' ▸ hru)) fun hm' => fU _ hm' hru₁
      obtain ⟨N₄, sts₄, ⟨cw, lw, pw, hlw, elw, fw⟩, k₄, hag₄⟩ :=
        mul_computes lv hN₃ aM₃ pv hlv (pUM₃.symm hN₃) (.next aU₃ pU₃ hlU₃) pMx₃
          ⟨fun e' => hM (e' ▸ hru), fun hm => fv _ hm (U₂ _ hru), hrUl⟩ elv
          (by rw [List.length_cons, elU])
      refine ⟨N₄, ?_, ⟨cw, lw, pw, hlw, ?_, fun i hi hu => fw i hi (U₃ i hu)⟩,
        (((k₁.trans k₂).trans k₃).trans k₄).mono ?_, ?_⟩
      · rw [hn]
        exact ((Steps.head st sts₂).trans sts₃).trans sts₄
      · rw [hn]
        exact elw
      · rintro i ((((e1 | e1) | (e1 | hm' | hu)) | (e1 | hm' | hu)) | (e1 | hm' | hm' | hu))
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
        · exact .inr (.inr (by
            rw [e1]
            exact hD))
        · exact .inr (.inl (List.mem_cons_of_mem _ hm'))
        · exact .inr (.inr fun hu' => hu (hused i hu'))
        · exact .inr (.inr (by
            rw [e1]
            exact hF))
        · exact .inr (.inr fun hu' => fF i hm' (hused i hu'))
        · exact .inr (.inr fun hu' => hu (U₂ i hu'))
        · exact .inr (.inr (by
            rw [e1]
            exact hM))
        · exact .inr (.inr fun hu' => fv i hm' (U₂ i hu'))
        · rcases List.mem_cons.1 hm' with e1 | hm''
          · exact .inr (.inr (by
              rw [e1]
              exact hU))
          · exact .inr (.inr fun hu' => fU i hm'' (hused i hu'))
        · exact .inr (.inr fun hu' => hu (U₃ i hu'))
      · intro i γ hi
        rcases hag₄ i γ hi with hz | hsu | ⟨hi₃, hneM⟩
        · exact .inl hz
        · exact .inr (.inl hsu)
        · rcases hag₃ i γ hi₃ with hz | hsu | ⟨hi₂, hneF⟩
          · exact .inl hz
          · exact .inr (.inl hsu)
          · rcases hag₂ i γ hi₂ with hz | hsu | ⟨hi₁, hneD⟩
            · exact .inl hz
            · exact .inr (.inl hsu)
            · rcases hag₁ i γ hi₁ with ⟨hi₀, hia, -⟩ | e1 | e1 | e1 | e1
              · exact .inr (.inr ⟨hi₀, hia⟩)
              · exact absurd e1 hneD
              · rw [e1] at hi₁
                exact .inr (.inl (hN₁.agent_fun hi₁ aU))
              · exact absurd e1 hneM
              · exact absurd e1 hneF

/-! ### Factorials are correct -/

variable {N : Net Peano} {r : Port}

/-- **The situation of a factorial.**  The agent `a` has the numeral `n`
as argument and the free port `r` as result, and the net has no other
agents than it and the successors and zeros. -/
structure Factorial (N : Net Peano) (a : Id) (n : Nat) (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a fac
  fst : IsNum N (a, 0) n
  out : N.Paired ar (a, 1) r
  free : N.free r
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = a

/-- **Factorials are correct, for all inputs.**  A net whose agent `fac`
has the numeral `n` as argument and the free port `r` as result reduces,
in `facCost n` steps, to a normal form in which `r` carries the numeral
`n!`. -/
theorem fac_correct {a : Id} {n : Nat} (c : Factorial N a n r) :
    ∃ N', Steps (Step system) (facCost n) N N' ∧ Normal (Step system) N' ∧
      IsNum N' r (fact n) := by
  have hN := c.wf
  obtain ⟨h, hp, hn⟩ := c.fst
  obtain ⟨l, hl, el⟩ := Addition.Num.list hn
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) c.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) c.free h
  obtain ⟨N', sts, hres, -, hag⟩ := fac_computes l hN c.ha hp hl c.out
    ⟨fun e' => hN.free_agent (i := r.1) (k := r.2) c.free (e' ▸ c.ha), hrl⟩ el
  refine ⟨N', sts, normal_of_numerals fun i γ hi => ?_, hres.isNum⟩
  rcases hag i γ hi with hz | hsu | ⟨hi₀, hne⟩
  · exact .inl hz
  · exact .inr hsu
  · rcases c.only i γ hi₀ with hz | hsu | e'
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e' hne

/-! ### The nets for `n!`, and the machine on them -/

/-- The net for `0!`, with the result on the free port `([0], 0)`. -/
def facBase : XNet Peano :=
  XNet.ofWires [([1], fac), ([2], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([0], 0))]

/-- The net for `n!`: `n` successors are put on the argument of the agent
of `0!`. -/
def facNet : Nat → XNet Peano
  | 0 => facBase
  | n + 1 => (facNet n).pushOn succ ([1], 0) [n + 3]

/-- The situation of a factorial, on a valid input whose identifiers are
numbered below `c`. -/
structure GoodFac (X : XNet Peano) (n c : Nat) : Prop where
  ok : X.Ok ar
  config : Factorial X.toNet [1] n ([0], 0)
  below : X.Below c

/-- One more successor on the argument. -/
theorem GoodFac.push {X : XNet Peano} {n c : Nat} (g : GoodFac X n c) :
    GoodFac (X.pushOn succ ([1], 0) [c]) (n + 1) (c + 1) := by
  have cf := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := cf.fst
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
    refine ⟨hm'.wf, .inl cf.ha, ?_, ?_, cf.free, ?_⟩
    · exact ⟨[c], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, h,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnh⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 cf.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)
    · rintro i γ (hi | ⟨-, e'⟩)
      · exact cf.only i γ hi
      · exact .inr (.inl e')

theorem good_facBase : GoodFac facBase 0 3 := by
  have hX : facBase.Ok ar := by decide
  refine ⟨hX, ⟨hX.1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show ([1], fac) ∈ facBase.agents
    decide
  · exact ⟨[2], hX.link_iff.1 (by decide), show ([2], zero) ∈ facBase.agents by decide⟩
  · exact hX.link_iff.1 (by decide)
  · show ([0], 0) ∈ facBase.free
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), fac), ([2], zero)] := hi
    rcases List.mem_cons.1 hi' with e | hi''
    · exact .inr (.inr (Prod.mk.inj e).1)
    · rcases List.mem_cons.1 hi'' with e | h3
      · exact .inl (Prod.mk.inj e).2
      · exact absurd h3 List.not_mem_nil
  · intro i hi
    have hall : ∀ i ∈ facBase.usedIds, ∃ j, j < 3 ∧ i = [j] := by decide
    exact hall i (XNet.mem_usedIds hi)

/-- **The nets for `n!` are factorials**, for all `n`. -/
theorem good_facNet : ∀ n, GoodFac (facNet n) n (n + 3)
  | 0 => good_facBase
  | n + 1 => (good_facNet n).push

/-- **Factorials come out right, whatever the threads do**: with any
number of threads and any schedule, a run of the machine on the net for
`n!` that is at rest has made exactly `facCost n` interactions, and its
memory has the numeral `n!` on the free port. -/
theorem fac_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (facNet n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (facNet n) nt).trace xsys σ i).2 = facCost n ∧
      IsNum ((XMach.init (facNet n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (fact n) := by
  have g := good_facNet n
  obtain ⟨N', hs, hn', hnum⟩ := fac_correct g.config
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (facNet n) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (facNet n) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **Factorials under any fair schedule**: with any number of threads,
as long as every thread keeps being scheduled, the run comes to rest
after `facCost n` interactions with the numeral `n!` in memory. -/
theorem fac_fair (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (facNet n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (facNet n) nt).trace xsys σ i).2 = facCost n ∧
      IsNum ((XMach.init (facNet n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (fact n) := by
  have g := good_facNet n
  obtain ⟨N', hs, hn', hnum⟩ := fac_correct g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- `3! = 6`, in 52 interactions. -/
example : fact 3 = 6 ∧ facCost 3 = 52 := by decide

/-- The reducer on the net for `3!` stops after 52 steps on a net whose
agents are six successors and a zero. -/
example : ((facNet 3).normalize xsys 200).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) = some (52, 6, 1, 7) := by
  decide +kernel

end Peano

end INet
