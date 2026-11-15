import InteractionNets.Core.Basic

/-! # Recursion, proved once

The agents that compute by recursion on a numeral follow one course: on
a zero the agent puts down a constant; on a successor it copies a
numeral, leaves a new agent of its own symbol on the rest, and a second
agent, the combiner, that takes the result of the new agent.  The course
is proved here once, for any two symbols, in two shapes.

* **On a parameter** (`Core.iterSucc`): `f (S x) y = g y (f x y)`.  The
  agent copies its second argument, the parameter; one copy goes to the
  combiner, the other to the new agent.  The multiplier (`g` the adder)
  and the power (`g` the multiplier) have this rule.
  `Core.iter_computes`.
* **On the predecessor** (`Core.primSucc`): `f (S x) = g (f x) (S x)`.
  The agent copies the rest of its argument; one copy goes to the new
  agent, a new successor is put on the other, and the combiner takes the
  two.  The factorial (`g` the multiplier) has this rule.
  `Core.prim_computes`.

The rule on a successor is given as a template in the two symbols, and
the theorem asks that the system has it.  What the agent does on a zero
is a hypothesis (`Core.Zero2`, `Core.Zero1`), met by any rule that puts
a numeral `k` on the result, and for two arguments erases the second
(`Core.zero1_const`, `Core.zero2_const`), given checks bounded by `k`
that are evaluated for the rule (`Core.ConstRule`, `Core.EraRule`).

The combiner is asked for less than `Core.Computes2`: its result may
reuse the agents of its second argument (`Core.Combines2`).  The adder
does that, and is a combiner (`Core.add_combines`); every agent that
computes is one (`Core.Computes2.combines`).

The theorems of the agents follow, stacked: the multiplier with the
adder as combiner (`Peano.mul_computes`), and the power and the
factorial with that multiplier (`Peano.pow_computes`,
`Peano.fac_computes`).
-/

namespace INet

namespace Core

open Addition (gone gone2)

variable {S : Type} {system : System S} {zero succ dup era : S} [K : Core system zero succ dup era]

local notation "ar" => system.ar
local notation "NumList" => Addition.NumList system.ar zero succ
local notation "IsNum" => Addition.IsNum system.ar zero succ
local notation "IsNumQ" => Addition.IsNumQ system.ar zero succ

/-! ### Combiners -/

/-- **An agent that combines two numerals**: as `Core.Computes2`, except
that the result is made of agents that satisfy any property `Q` that the
agents of the second argument and all names not in use satisfy.  The
result may thus reuse the agents of the second argument. -/
def Combines2 (system : System S) {zero succ dup era : S} [Core system zero succ dup era]
    (op : S) (f c : Nat → Nat → Nat) : Prop :=
  ∀ (l₁ : List Id) (Q : Id → Prop) {N : Net S} {a h₁ h₂ : Id} {l₂ : List Id} {r : Port}
    {m n : Nat},
    N.WF system.ar → N.agent a op → N.Paired system.ar (a, 0) (h₁, 0) → Addition.NumList system.ar
        zero succ N h₁ l₁ →
    N.Paired system.ar (a, 1) (h₂, 0) → Addition.NumList system.ar zero succ N h₂ l₂ → N.Paired
        system.ar (a, 2) r →
    r.1 ≠ a ∧ ¬ r.1 ∈ l₁ ∧ ¬ r.1 ∈ l₂ → l₁.length = m + 1 → l₂.length = n + 1 →
    (∀ i, i ∈ l₂ → Q i) → (∀ i, ¬ N.Used i → Q i) →
    ∃ N', Steps (Step system) (c m n) N N' ∧
      Addition.IsNumQ system.ar zero succ N' Q r (f m n) ∧ N.Keeps system.ar (gone2 N a l₁ l₂) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)

/-- **An agent that computes is a combiner.** -/
theorem Computes2.combines {op : S} {f c : Nat → Nat → Nat} (H : Computes2 system op f c) :
    Combines2 system op f c :=
  fun l₁ _ _ _ _ _ _ _ _ _ hN ha h1 n1 h2 n2 ho hr e1 e2 _ hQ => by
    obtain ⟨N', sts, ⟨h, l, p, hl, el, fl⟩, kp, hag⟩ := H l₁ hN ha h1 n1 h2 n2 ho hr e1 e2
    exact ⟨N', sts, ⟨h, l, p, hl, el, fun i hi => hQ i (fl i hi)⟩, kp, hag⟩

/-- **The adder is a combiner.**  Its result is made of new successors
and of the agents of its second argument. -/
theorem add_combines {add : S} (HA : Addition.Rules system zero succ add) :
    Combines2 system add (fun m n => m + n) (fun m _ => m + 1) :=
  fun l₁ Q _ _ _ h₂ l₂ r _ _ hN ha h1 n1 h2 n2 ho hr e1 e2 hl₂ hQ => by
    have c : Addition.Adding ar zero succ add _ Q _ 0 _ l₁ _ r :=
      ⟨hN, ha, h1, n1, ⟨h₂, l₂, h2, n2, e2, hl₂⟩, ⟨r, ho, rfl⟩,
        ⟨Net.End.used ho.2.1, hr.1, hr.2.1⟩, hQ⟩
    obtain ⟨N', sts, hres, kp, hag⟩ := Addition.Adding.run HA l₁ c e1
    rw [e1] at sts
    rw [Nat.zero_add] at hres
    refine ⟨N', sts, hres, kp.mono ?_, fun i γ hi => ?_⟩
    · rintro i (e | hm | hu)
      · exact .inl e
      · exact .inr (.inl hm)
      · exact .inr (.inr (.inr hu))
    · rcases hag i γ hi with hs | h
      · exact .inr (.inl hs)
      · exact .inr (.inr h)

/-- The same agent with the same result and cost, written differently. -/
theorem Computes2.congr {op : S} {f c f' c' : Nat → Nat → Nat} (H : Computes2 system op f c)
    (hf : ∀ m n, f m n = f' m n) (hc : ∀ m n, c m n = c' m n) : Computes2 system op f' c' := by
  have ef : f = f' := funext fun m => funext fun n => hf m n
  have ec : c = c' := funext fun m => funext fun n => hc m n
  rw [← ef, ← ec]
  exact H

/-- The same for one argument. -/
theorem Computes1.congr {op : S} {f c f' c' : Nat → Nat} (H : Computes1 system op f c)
    (hf : ∀ n, f n = f' n) (hc : ∀ n, c n = c' n) : Computes1 system op f' c' := by
  have ef : f = f' := funext hf
  have ec : c = c' := funext hc
  rw [← ef, ← ec]
  exact H

/-! ### The two rules on a successor, as templates -/

/-- **Recursion on a parameter**, `f (S x) y = g y (f x y)`: `y` is
copied; one copy is the first argument of a new `g`, the other the second
argument of a new `op` on `x`, whose result is the second argument of
`g`. -/
def iterSucc (dup op g : S) : RuleData S :=
  RuleData.ofWires [((some false, 0), dup), ((some false, 1), g), ((some true, 0), op)]
    [(.ifc false 0, .new (some false) 0 0),            -- `y` — the new `dup`
      (.new (some false) 0 1, .new (some false) 1 0),   -- first copy — first argument of `g`
      (.new (some false) 0 2, .new (some true) 0 1),    -- second copy — second argument of `op`
      (.ifc true 0, .new (some true) 0 0),              -- `x` — first argument of `op`
      (.new (some true) 0 2, .new (some false) 1 1),    -- result of `op` — second argument of `g`
      (.new (some false) 1 2, .ifc false 1)]            -- result of `g` — result

/-- **Recursion on the predecessor**, `f (S x) = g (f x) (S x)`: `x` is
copied; a new successor on one copy is the second argument of a new `g`,
whose first argument is the result of a new `op` on the other copy. -/
def primSucc (succ dup op g : S) : RuleData S :=
  RuleData.ofWires [((some false, 0), dup), ((some false, 1), succ), ((some false, 2), g),
      ((some true, 0), op)]
    [(.ifc true 0, .new (some false) 0 0),             -- `x` — the new `dup`
      (.new (some false) 0 1, .new (some false) 1 1),   -- first copy — under the new `succ`
      (.new (some false) 0 2, .new (some true) 0 0),    -- second copy — argument of `op`
      (.new (some true) 0 1, .new (some false) 2 0),    -- result of `op` — first argument of `g`
      (.new (some false) 1 0, .new (some false) 2 1),   -- the new `succ` — second argument of `g`
      (.new (some false) 2 2, .ifc false 0)]            -- result of `g` — result

/-- **The symbols are apart**: the agent and the combiner are neither
numerals nor copiers, and not the same. -/
structure Apart (zero succ dup op g : S) : Prop where
  op_zero : zero ≠ op
  op_succ : succ ≠ op
  op_dup : dup ≠ op
  g_zero : zero ≠ g
  g_succ : succ ≠ g
  g_dup : dup ≠ g
  g_op : g ≠ op

/-! ### The rule on a zero, as a hypothesis -/

/-- **An agent that computes a function of its second argument when its
first is zero**: `Core.Computes2` with the first argument `0`. -/
def Zero2 (system : System S) {zero succ dup era : S} [Core system zero succ dup era]
    (op : S) (h c₀ : Nat → Nat) : Prop :=
  ∀ {N : Net S} {a z h₂ : Id} {l₂ : List Id} {r : Port} {n : Nat},
    N.WF system.ar → N.agent a op → N.Paired system.ar (a, 0) (z, 0) → N.agent z zero →
    N.Paired system.ar (a, 1) (h₂, 0) → Addition.NumList system.ar zero succ N h₂ l₂ → N.Paired
        system.ar (a, 2) r →
    r.1 ≠ a ∧ r.1 ≠ z ∧ ¬ r.1 ∈ l₂ → l₂.length = n + 1 →
    ∃ N', Steps (Step system) (c₀ n) N N' ∧ Addition.IsNumQ system.ar zero succ N' (fun i => ¬
        N.Used i) r (h n) ∧
      N.Keeps system.ar (gone2 N a [z] l₂) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)

/-- **An agent that puts the numeral `k` on its result when its argument
is zero**: `Core.Computes1` with the argument `0`. -/
def Zero1 (system : System S) {zero succ dup era : S} [Core system zero succ dup era]
    (op : S) (k c₀ : Nat) : Prop :=
  ∀ {N : Net S} {a z : Id} {r : Port},
    N.WF system.ar → N.agent a op → N.Paired system.ar (a, 0) (z, 0) → N.agent z zero →
    N.Paired system.ar (a, 1) r → r.1 ≠ a ∧ r.1 ≠ z →
    ∃ N', Steps (Step system) c₀ N N' ∧ Addition.IsNumQ system.ar zero succ N' (fun i => ¬ N.Used i)
        r k ∧
      N.Keeps system.ar (gone N a [z]) N' ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ ∨ (N.agent i γ ∧ i ≠ a)

/-! ### Recursion on a parameter -/

/-- The function: `h` on zero, and `g y (f x y)` on `S x`. -/
def iter (h : Nat → Nat) (g : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, n => h n
  | m + 1, n => g n (iter h g m n)

/-- Its number of interactions: on a zero, `c₀`; on a successor, one, the
copy of the parameter, the rest, and the combiner. -/
def iterCost (c₀ : Nat → Nat) (cg : Nat → Nat → Nat) (h : Nat → Nat) (g : Nat → Nat → Nat) :
    Nat → Nat → Nat
  | 0, n => c₀ n
  | m + 1, n => n + 1 + 1 + iterCost c₀ cg h g m n + cg n (iter h g m n)

/-- The rule makes three agents. -/
theorem iterSucc_lab {op g : S} {o : Option Bool} {j : Nat} {γ : S}
    (h : (iterSucc dup op g).toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some false ∧ j = 1) ∨ (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) (iterSucc dup op g).agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), dup), ((some false, 1), g),
      ((some true, 0), op)] := assoc_mem h'
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

/-- **The agent meets a successor.**  The firing makes a copier `D` on
the parameter, a combiner `M` whose first argument is the first copy and
whose result is the old result, and an agent `P` on the rest, whose
second argument is the second copy and whose result is the second
argument of the combiner. -/
theorem iterSucc_step {op g : S} (hs : system.rule op succ = some (iterSucc dup op g).toX.toRhs)
    {N : Net S} {p s h' t : Id} {x : Port}
    (hA : Addition.Adder ar op N p s succ) (hpi : N.Paired ar (s, 1) (h', 0))
    (hpt : N.Paired ar (p, 1) (t, 0)) (hpx : N.Paired ar (p, 2) x)
    (hh' : h' ≠ p ∧ h' ≠ s) (ht : t ≠ p ∧ t ≠ s) (hx : x.1 ≠ p ∧ x.1 ≠ s) :
    ∃ (N₁ : Net S) (D M P : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = p ∨ i = s) N₁ ∧
      ¬ N.Used D ∧ ¬ N.Used M ∧ ¬ N.Used P ∧
      N₁.agent D dup ∧ N₁.agent M g ∧ N₁.agent P op ∧
      N₁.Paired ar (D, 0) (t, 0) ∧ N₁.Paired ar (D, 1) (M, 0) ∧ N₁.Paired ar (D, 2) (P, 1) ∧
      N₁.Paired ar (P, 0) (h', 0) ∧ N₁.Paired ar (P, 2) (M, 1) ∧ N₁.Paired ar (M, 2) x ∧
      (∀ i, N.Used i → N₁.Used i) ∧
      ∀ i γ, N₁.agent i γ → (N.agent i γ ∧ i ≠ p ∧ i ≠ s) ∨ i = D ∨ i = M ∨ i = P := by
  have hN := hA.wf
  have hR : (iterSucc dup op g).toX.toRhs.WF ar op succ := system.rule_wf hs
  have red : Redex system N p s op succ (iterSucc dup op g).toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, hs⟩
  have st : Step system N (N.fire p s (iterSucc dup op g).toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN₁ := Step.wf hN st
  refine ⟨_, child p s (some false) 0, child p s (some false) 1, child p s (some true) 0, st,
    hA.site.keeps _, hA.site.not_used_child _ _, hA.site.not_used_child _ _,
    hA.site.not_used_child _ _, .inr ⟨some false, 0, rfl, rfl⟩, .inr ⟨some false, 1, rfl, rfl⟩,
    .inr ⟨some true, 0, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hu => Net.used_fire hN hu _ _ _, ?_⟩
  · exact (hA.site.paired_fire_ifc_new hR
      (show (iterSucc dup op g).toX.toRhs.link (.ifc false 0) (.new (some false) 0 0) from rfl)
      (hpt.symm hN) ht.1 ht.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show (iterSucc dup op g).toX.toRhs.link (.new (some false) 0 1) (.new (some false) 1 0)
        from rfl)
  · exact Site.paired_fire_new_new hR
      (show (iterSucc dup op g).toX.toRhs.link (.new (some false) 0 2) (.new (some true) 0 1)
        from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show (iterSucc dup op g).toX.toRhs.link (.ifc true 0) (.new (some true) 0 0) from rfl)
      (hpi.symm hN) hh'.1 hh'.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show (iterSucc dup op g).toX.toRhs.link (.new (some true) 0 2) (.new (some false) 1 1)
        from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show (iterSucc dup op g).toX.toRhs.link (.ifc false 1) (.new (some false) 1 2) from rfl)
      (hpx.symm hN) hx.1 hx.2).symm hN₁
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases iterSucc_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr e))

/-- **Recursion on a parameter computes.**  If the system has the rule
`Core.iterSucc dup op g` for `op` on a successor, `op` computes `h` when its
first argument is zero, and `g` combines, then `op` computes the function
`Core.iter h fg`, in `Core.iterCost` steps.  On a successor the agent
copies its parameter; the agent left on the rest computes by this theorem,
on the second argument of the combiner; the combiner then combines. -/
theorem iter_computes {op g : S} {h c₀ : Nat → Nat} {fg cg : Nat → Nat → Nat}
    (hs : system.rule op succ = some (iterSucc dup op g).toX.toRhs) (hd : Apart zero succ dup op g)
    (hz : Zero2 system op h c₀) (hg : Combines2 system g fg cg) :
    Computes2 system op (iter h fg) (iterCost c₀ cg h fg)
  | [], _, _, _, _, _, _, _, _, _, _, _, hl, _, _, _, _, _, _ => by cases hl
  | s :: l', N, p, _, h₂, l₂, r, e, b, hN, hp, hps, hnum, hpt, hl₂, hpx, hr, hlen, hlen₂ => by
    obtain ⟨hrp, hrl₁, hrl₂⟩ := hr
    have hru : N.Used r.1 := Net.End.used hpx.2.1
    have hrs : r.1 ≠ s := fun e' => hrl₁ (by
      rw [e']
      exact List.mem_cons_self)
    have hta : h₂ ≠ p := by
      rcases hl₂.label h₂ hl₂.head_mem with hx' | hx'
      · exact ne_of_agent hN hx' hp hd.op_zero
      · exact ne_of_agent hN hx' hp hd.op_succ
    have hav : ∀ t, N.Paired ar (p, 0) (t, 0) → ∀ j, j ∈ l₂ → ¬ (j = p ∨ j = t) := by
      intro t hpt' j hj hc
      rcases hc with e1 | e1
      · rw [e1] at hj
        rcases hl₂.label p hj with hx' | hx'
        · exact hd.op_zero (hN.agent_fun hx' hp)
        · exact hd.op_succ (hN.agent_fun hx' hp)
      · rw [e1] at hj
        exact Addition.NumList.not_mem hN hpt' hl₂ hpt (port_ne_snd (by decide)) hj
    cases hnum with
    | last hz' =>
      have he : e = 0 := Nat.succ.inj hlen.symm
      subst he
      exact hz hN hp hps hz' hpt hl₂ hpx ⟨hrp, hrs, hrl₂⟩ hlen₂
    | @next _ h' _ hsu hpi hl' =>
      obtain ⟨k, ek, -⟩ := hl'.num
      have he : e = k + 1 := by
        have e' : l'.length + 1 = e + 1 := hlen
        omega
      have hA : Addition.Adder ar op N p s succ := ⟨hN, hp, hsu, hd.op_succ, hps⟩
      have hh'p : h' ≠ p := by
        rcases hl'.label h' hl'.head_mem with hx' | hx'
        · exact hA.ne_add hx' hd.op_zero
        · exact hA.ne_add hx' hd.op_succ
      have hh's : h' ≠ s := hA.not_s hpi (port_ne_snd (by decide))
      have hts : h₂ ≠ s := hA.not_s hpt (port_ne_snd (by decide))
      obtain ⟨N₁, D, M, P, st, k₁, hD, hM, hP, aD, aM, aP, pDt, pDM, pDP, pPh, pPM, pMx,
        hused, hag₁⟩ := iterSucc_step hs hA hpi hpt hpx ⟨hh'p, hh's⟩ ⟨hta, hts⟩ ⟨hrp, hrs⟩
      have hN₁ := Step.wf hN st
      have hl₂₁ : NumList N₁ h₂ l₂ := hl₂.keeps k₁ (hav s hps)
      have havh : ∀ j, j ∈ l' → ¬ (j = p ∨ j = s) := by
        intro j hj hc
        rcases hc with e1 | e1
        · rw [e1] at hj
          rcases hl'.label p hj with hx' | hx'
          · exact hd.op_zero (hN.agent_fun hx' hp)
          · exact hd.op_succ (hN.agent_fun hx' hp)
        · rw [e1] at hj
          exact Addition.NumList.not_mem hN hps hl' hpi (port_ne_snd (by decide)) hj
      have hl'₁ : NumList N₁ h' l' := hl'.keeps k₁ havh
      have hru₁ : N₁.Used r.1 := hused _ hru
      -- the copy
      have hMl : ¬ M ∈ l₂ := fun hm => hM (numList_used hl₂ hm)
      have hPl : ¬ P ∈ l₂ := fun hm => hP (numList_used hl₂ hm)
      obtain ⟨N₂, sts₂, ⟨cM, lM, pM, hlM, elM, fM⟩, ⟨cP, lP, pP, hlP, elP, fP⟩, k₂, hag₂⟩ :=
        Copies.copy_fresh K.toRules hN₁ aD pDt hl₂₁ hlen₂ pDM pDP
          ⟨ne_of_agent hN₁ aM aD hd.g_dup.symm, hMl⟩ ⟨ne_of_agent hN₁ aP aD hd.op_dup.symm, hPl⟩
      have hN₂ := Steps.wf hN₁ sts₂
      have U₂ : ∀ i, N.Used i → N₂.Used i := fun i hu => Steps.used hN₁ sts₂ (hused i hu)
      have hC₂ : Addition.Closed ar (gone N₁ D l₂) N₁ := Addition.gone_closed hN₁ pDt hl₂₁
      have ngM : ¬ gone N₁ D l₂ M :=
        not_gone (ne_of_agent hN₁ aM aD hd.g_dup.symm) hMl (.inl ⟨_, aM⟩)
      have ngP : ¬ gone N₁ D l₂ P :=
        not_gone (ne_of_agent hN₁ aP aD hd.op_dup.symm) hPl (.inl ⟨_, aP⟩)
      have ngr : ¬ gone N₁ D l₂ r.1 := not_gone (fun e' => hD (e' ▸ hru)) hrl₂ hru₁
      -- what the copy keeps
      have havl' : ∀ j, j ∈ l' → ¬ gone N₁ D l₂ j := hl'₁.avoid hC₂ pPh ngP
      have hl'₂ : NumList N₂ h' l' := hl'₁.keeps k₂ havl'
      have pPh₂ : N₂.Paired ar (P, 0) (h', 0) := k₂.paired pPh ngP (havl' h' hl'₁.head_mem)
      have aP₂ : N₂.agent P op := k₂.agent aP ngP
      have aM₂ : N₂.agent M g := k₂.agent aM ngM
      have pPM₂ : N₂.Paired ar (P, 2) (M, 1) := k₂.paired pPM ngP ngM
      have pMx₂ : N₂.Paired ar (M, 2) r := k₂.paired pMx ngM ngr
      -- the rest, with its result on the second argument of the combiner
      have hMl' : ¬ M ∈ l' := fun hm => hM (numList_used hl' hm)
      have hMlP : ¬ M ∈ lP := fun hm =>
        (hlP.label _ hm).elim (fun h => hd.g_zero (hN₂.agent_fun h aM₂))
          fun h => hd.g_succ (hN₂.agent_fun h aM₂)
      have hMP : M ≠ P := ne_of_agent hN₂ aM₂ aP₂ hd.g_op
      obtain ⟨N₃, sts₃, ⟨cv, lv, pv, hlv, elv, fv⟩, k₃, hag₃⟩ :=
        iter_computes hs hd hz hg l' hN₂ aP₂ pPh₂ hl'₂ pP hlP pPM₂ ⟨hMP, hMl', hMlP⟩ ek elP
      have hN₃ := Steps.wf hN₂ sts₃
      have U₃ : ∀ i, N.Used i → N₃.Used i := fun i hu => Steps.used hN₂ sts₃ (U₂ i hu)
      have hC₃ : Addition.Closed ar (gone2 N₂ P l' lP) N₂ :=
        Addition.gone2_closed hN₂ pPh₂ hl'₂ pP hlP
      -- what it keeps: the combiner, its first argument and the result port
      have ng3M : ¬ gone2 N₂ P l' lP M := not_gone2 hMP hMl' hMlP (.inl ⟨_, aM₂⟩)
      have havlM : ∀ j, j ∈ lM → ¬ gone2 N₂ P l' lP j := hlM.avoid hC₃ pM ng3M
      have hlM₃ : NumList N₃ cM lM := hlM.keeps k₃ havlM
      have pM₃ : N₃.Paired ar (M, 0) (cM, 0) := k₃.paired pM ng3M (havlM cM hlM.head_mem)
      have aM₃ : N₃.agent M g := k₃.agent aM₂ ng3M
      have ng3r : ¬ gone2 N₂ P l' lP r.1 :=
        not_gone2 (fun e' => hP (e' ▸ hru)) (fun hm => hrl₁ (List.mem_cons_of_mem _ hm))
          (fun hm => fP _ hm hru₁) (U₂ _ hru)
      have pMx₃ : N₃.Paired ar (M, 2) r := k₃.paired pMx₂ ng3M ng3r
      -- the combiner combines
      obtain ⟨N₄, sts₄, ⟨cw, lw, pw, hlw, elw, fw⟩, k₄, hag₄⟩ :=
        hg lM (fun i => ¬ N.Used i) hN₃ aM₃ pM₃ hlM₃ pv hlv pMx₃
          ⟨fun e' => hM (e' ▸ hru), fun hm => fM _ hm hru₁, fun hm => fv _ hm (U₂ _ hru)⟩
          elM elv (fun i hi hu => fv i hi (U₂ i hu)) (fun i hu hu' => hu (U₃ i hu'))
      subst he
      refine ⟨N₄, ((Steps.head st sts₂).trans sts₃).trans sts₄, ⟨cw, lw, pw, hlw, elw, fw⟩,
        (((k₁.trans k₂).trans k₃).trans k₄).mono ?_, ?_⟩
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

/-! ### Any constant on a zero -/

/-- **A rule that puts the numeral `k` on the result**: the new agents
`0, …, k - 1` are successors, each with its argument on the next, the new
agent `k` is a zero, and the interface port `res` is wired to the new
agent `0`.  Every field is evaluated for a given rule. -/
structure ConstRule (zero succ : S) (R : RuleData S) (res k : Nat) : Prop where
  succs : ∀ j, j < k → assoc ((some false : Option Bool), j) R.agents = some succ
  last : assoc ((some false : Option Bool), k) R.agents = some zero
  links : ∀ j, j < k →
    assoc (LPort.new (some false) j 1) R.wires = some (LPort.new (some false) (j + 1) 0)
  out : assoc (LPort.ifc false res) R.wires = some (LPort.new (some false) 0 0)

/-- **The rule also erases the second argument**: the new agent
`(some true, 0)` is an eraser, on the interface port `0`. -/
structure EraRule (era : S) (R : RuleData S) : Prop where
  era : assoc ((some true : Option Bool), 0) R.agents = some era
  link : assoc (LPort.ifc false 0) R.wires = some (LPort.new (some true) 0 0)

/-- The names of the numeral the rule makes. -/
def constIds (a z : Id) (k : Nat) : List Id := (List.range' 0 (k + 1)).map (child a z (some false))

/-- **After the firing, the new agents of the rule are the numeral `k`**,
from the agent `k - d` on. -/
theorem const_chain {op : S} {R : RuleData S} {res k : Nat} (C : ConstRule zero succ R res k)
    (hR : R.toX.toRhs.WF ar op zero) {N : Net S} {a z : Id} (hA : Addition.Adder ar op N a z zero) :
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

theorem constIds_numList {op : S} {R : RuleData S} {res k : Nat} (C : ConstRule zero succ R res k)
    (hR : R.toX.toRhs.WF ar op zero) {N : Net S} {a z : Id}
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
theorem zero1_const {op : S} {R : RuleData S} {k : Nat}
    (hr : system.rule op zero = some R.toX.toRhs) (h0 : zero ≠ op) (C : ConstRule zero succ R 0 k)
    (hall : ∀ e ∈ R.agents, e.1.1 = some false ∧ e.1.2 ≤ k) : Zero1 system op k 1 := by
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
theorem zero2_const {op : S} {R : RuleData S} {k : Nat}
    (hr : system.rule op zero = some R.toX.toRhs) (h0 : zero ≠ op) (h1 : succ ≠ op)
    (C : ConstRule zero succ R 1 k) (E : EraRule era R)
    (hall : ∀ e ∈ R.agents, (e.1.1 = some false ∧ e.1.2 ≤ k) ∨ e.1 = (some true, 0)) :
    Zero2 system op (fun _ => k) (fun n => n + 1 + 1) := by
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
  obtain ⟨N₂, sts, k₂, hag₂⟩ := Copies.erase K.toRules l₂ hN₁ aE pEt hl₂₁
  rw [hlen₂] at sts
  have ngc : ∀ i, i ∈ constIds p s k → ¬ gone (N.fire p s R.toX.toRhs) (child p s (some true) 0)
      l₂ i := by
    intro i hi
    have hu : ¬ N.Used i := by
      obtain ⟨j, -, rfl⟩ := mem_constIds hi
      exact hA.site.not_used_child _ _
    refine not_gone ?_ (fun hm => hu (numList_used hl₂ hm)) ?_
    · rcases hnl.label i hi with h | h
      · exact ne_of_agent hN₁ h aE K.zero_ne_era
      · exact ne_of_agent hN₁ h aE K.succ_ne_era
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

/-! ### Recursion on the predecessor -/

/-- The function: `k` on zero, and `g (f x) (S x)` on `S x`. -/
def prim (k : Nat) (g : Nat → Nat → Nat) : Nat → Nat
  | 0 => k
  | n + 1 => g (prim k g n) (n + 1)

/-- Its number of interactions: on a zero, `c₀`; on a successor, one, the
copy of the rest, the rest, and the combiner. -/
def primCost (c₀ : Nat) (cg : Nat → Nat → Nat) (k : Nat) (g : Nat → Nat → Nat) : Nat → Nat
  | 0 => c₀
  | n + 1 => n + 1 + 1 + primCost c₀ cg k g n + cg (prim k g n) (n + 1)

/-- The rule makes four agents. -/
theorem primSucc_lab {op g : S} {o : Option Bool} {j : Nat} {γ : S}
    (h : (primSucc succ dup op g).toX.toRhs.lab o j = some γ) :
    (o = some false ∧ j = 0) ∨ (o = some false ∧ j = 1) ∨ (o = some false ∧ j = 2) ∨
      (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) (primSucc succ dup op g).agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), dup), ((some false, 1), succ),
      ((some false, 2), g), ((some true, 0), op)] := assoc_mem h'
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

/-- **The agent meets a successor.**  The firing makes a copier `D` on
the rest of the argument, a successor `U` on the first copy, an agent `F`
on the second copy, and a combiner `M` whose first argument is the result
of `F`, whose second argument is `U`, and whose result is the old
result. -/
theorem primSucc_step {op g : S} (hs : system.rule op succ = some (primSucc succ dup op
    g).toX.toRhs)
    {N : Net S} {a s h' : Id} {x : Port}
    (hA : Addition.Adder ar op N a s succ) (hpi : N.Paired ar (s, 1) (h', 0))
    (hpx : N.Paired ar (a, 1) x) (hh' : h' ≠ a ∧ h' ≠ s) (hx : x.1 ≠ a ∧ x.1 ≠ s) :
    ∃ (N₁ : Net S) (D U M F : Id), Step system N N₁ ∧
      N.Keeps ar (fun i => i = a ∨ i = s) N₁ ∧
      ¬ N.Used D ∧ ¬ N.Used U ∧ ¬ N.Used M ∧ ¬ N.Used F ∧
      N₁.agent D dup ∧ N₁.agent U succ ∧ N₁.agent M g ∧ N₁.agent F op ∧
      N₁.Paired ar (D, 0) (h', 0) ∧ N₁.Paired ar (D, 1) (U, 1) ∧ N₁.Paired ar (D, 2) (F, 0) ∧
      N₁.Paired ar (F, 1) (M, 0) ∧ N₁.Paired ar (U, 0) (M, 1) ∧ N₁.Paired ar (M, 2) x ∧
      (∀ i, N.Used i → N₁.Used i) ∧
      ∀ i γ, N₁.agent i γ →
        (N.agent i γ ∧ i ≠ a ∧ i ≠ s) ∨ i = D ∨ i = U ∨ i = M ∨ i = F := by
  have hN := hA.wf
  have hR : (primSucc succ dup op g).toX.toRhs.WF ar op succ := system.rule_wf hs
  have red : Redex system N a s op succ (primSucc succ dup op g).toX.toRhs :=
    ⟨hA.ha, hA.hs, hA.site.ne, hA.pair.2.2, hs⟩
  have st : Step system N (N.fire a s (primSucc succ dup op g).toX.toRhs) := ⟨_, _, _, _, _, red,
      rfl⟩
  have hN₁ := Step.wf hN st
  refine ⟨_, child a s (some false) 0, child a s (some false) 1, child a s (some false) 2,
    child a s (some true) 0, st, hA.site.keeps _, hA.site.not_used_child _ _,
    hA.site.not_used_child _ _, hA.site.not_used_child _ _, hA.site.not_used_child _ _,
    .inr ⟨some false, 0, rfl, rfl⟩, .inr ⟨some false, 1, rfl, rfl⟩,
    .inr ⟨some false, 2, rfl, rfl⟩, .inr ⟨some true, 0, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hu => Net.used_fire hN hu _ _ _, ?_⟩
  · exact (hA.site.paired_fire_ifc_new hR
      (show (primSucc succ dup op g).toX.toRhs.link (.ifc true 0) (.new (some false) 0 0) from rfl)
      (hpi.symm hN) hh'.1 hh'.2).symm hN₁
  · exact Site.paired_fire_new_new hR
      (show (primSucc succ dup op g).toX.toRhs.link (.new (some false) 0 1) (.new (some false) 1 1)
        from rfl)
  · exact Site.paired_fire_new_new hR
      (show (primSucc succ dup op g).toX.toRhs.link (.new (some false) 0 2) (.new (some true) 0 0)
        from rfl)
  · exact Site.paired_fire_new_new hR
      (show (primSucc succ dup op g).toX.toRhs.link (.new (some true) 0 1) (.new (some false) 2 0)
        from rfl)
  · exact Site.paired_fire_new_new hR
      (show (primSucc succ dup op g).toX.toRhs.link (.new (some false) 1 0) (.new (some false) 2 1)
        from rfl)
  · exact (hA.site.paired_fire_ifc_new hR
      (show (primSucc succ dup op g).toX.toRhs.link (.ifc false 0) (.new (some false) 2 2) from rfl)
      (hpx.symm hN) hx.1 hx.2).symm hN₁
  · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, e, hlab⟩)
    · exact .inl ⟨hi, h1, h2⟩
    · rcases primSucc_lab hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl e)
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr (.inl e)))
      · exact .inr (.inr (.inr (.inr e)))

/-- **Recursion on the predecessor computes.**  If the system has the
rule `Core.primSucc succ dup op g` for `op` on a successor, `op` puts the numeral
`k` on its result when its argument is zero, and `g` combines, then `op`
computes the function `Core.prim k fg`, in `Core.primCost` steps.  On a
successor the agent copies the rest of its argument; the agent left on
one copy computes by this theorem, on the first argument of the combiner;
the combiner then combines it with the successor of the other copy. -/
theorem prim_computes {op g : S} {k c₀ : Nat} {fg cg : Nat → Nat → Nat}
    (hs : system.rule op succ = some (primSucc succ dup op g).toX.toRhs) (hd : Apart zero succ dup
        op g)
    (hz : Zero1 system op k c₀) (hg : Combines2 system g fg cg) :
    Computes1 system op (prim k fg) (primCost c₀ cg k fg)
  | [], _, _, _, _, _, _, _, _, hl, _, _, _ => by cases hl
  | s :: l', N, a, _, r, n, hN, ha, hps, hnum, hpx, hr, hlen => by
    obtain ⟨hra, hrl⟩ := hr
    have hru : N.Used r.1 := Net.End.used hpx.2.1
    have hrs : r.1 ≠ s := fun e' => hrl (by
      rw [e']
      exact List.mem_cons_self)
    cases hnum with
    | last hz' =>
      have hn : n = 0 := Nat.succ.inj hlen.symm
      subst hn
      exact hz hN ha hps hz' hpx ⟨hra, hrs⟩
    | @next _ h' _ hsu hpi hl' =>
      obtain ⟨k', ek, -⟩ := hl'.num
      have hn : n = k' + 1 := by
        have e' : l'.length + 1 = n + 1 := hlen
        omega
      have hA : Addition.Adder ar op N a s succ := ⟨hN, ha, hsu, hd.op_succ, hps⟩
      have hh'a : h' ≠ a := by
        rcases hl'.label h' hl'.head_mem with hx' | hx'
        · exact hA.ne_add hx' hd.op_zero
        · exact hA.ne_add hx' hd.op_succ
      have hh's : h' ≠ s := hA.not_s hpi (port_ne_snd (by decide))
      obtain ⟨N₁, D, U, M, F, st, k₁, hD, hU, hM, hF, aD, aU, aM, aF, pDh, pDU, pDF, pFM, pUM,
        pMx, hused, hag₁⟩ := primSucc_step hs hA hpi hpx ⟨hh'a, hh's⟩ ⟨hra, hrs⟩
      have hN₁ := Step.wf hN st
      have hru₁ : N₁.Used r.1 := hused _ hru
      have havh : ∀ j, j ∈ l' → ¬ (j = a ∨ j = s) := by
        intro j hj hc
        rcases hc with e1 | e1
        · rw [e1] at hj
          rcases hl'.label a hj with hx' | hx'
          · exact hd.op_zero (hN.agent_fun hx' ha)
          · exact hd.op_succ (hN.agent_fun hx' ha)
        · rw [e1] at hj
          exact Addition.NumList.not_mem hN hps hl' hpi (port_ne_snd (by decide)) hj
      have hl'₁ : NumList N₁ h' l' := hl'.keeps k₁ havh
      have hrl' : ¬ r.1 ∈ l' := fun hm => hrl (List.mem_cons_of_mem _ hm)
      -- the copy of the rest
      have hUl : ¬ U ∈ l' := fun hm => hU (numList_used hl' hm)
      have hMl : ¬ M ∈ l' := fun hm => hM (numList_used hl' hm)
      have hFl : ¬ F ∈ l' := fun hm => hF (numList_used hl' hm)
      obtain ⟨N₂, sts₂, ⟨cU, lU, pU, hlU, elU, fU⟩, ⟨cF, lF, pF, hlF, elF, fF⟩, k₂, hag₂⟩ :=
        Copies.copy_fresh K.toRules hN₁ aD pDh hl'₁ ek pDU pDF
          ⟨ne_of_agent hN₁ aU aD K.succ_ne_dup, hUl⟩
          ⟨ne_of_agent hN₁ aF aD hd.op_dup.symm, hFl⟩
      have hN₂ := Steps.wf hN₁ sts₂
      have U₂ : ∀ i, N.Used i → N₂.Used i := fun i hu => Steps.used hN₁ sts₂ (hused i hu)
      have ngU : ¬ gone N₁ D l' U :=
        not_gone (ne_of_agent hN₁ aU aD K.succ_ne_dup) hUl (.inl ⟨_, aU⟩)
      have ngM : ¬ gone N₁ D l' M :=
        not_gone (ne_of_agent hN₁ aM aD hd.g_dup.symm) hMl (.inl ⟨_, aM⟩)
      have ngF : ¬ gone N₁ D l' F :=
        not_gone (ne_of_agent hN₁ aF aD hd.op_dup.symm) hFl (.inl ⟨_, aF⟩)
      have ngr : ¬ gone N₁ D l' r.1 := not_gone (fun e' => hD (e' ▸ hru)) hrl' hru₁
      have aU₂ : N₂.agent U succ := k₂.agent aU ngU
      have aM₂ : N₂.agent M g := k₂.agent aM ngM
      have aF₂ : N₂.agent F op := k₂.agent aF ngF
      have pFM₂ : N₂.Paired ar (F, 1) (M, 0) := k₂.paired pFM ngF ngM
      have pUM₂ : N₂.Paired ar (U, 0) (M, 1) := k₂.paired pUM ngU ngM
      have pMx₂ : N₂.Paired ar (M, 2) r := k₂.paired pMx ngM ngr
      -- the rest, with its result on the first argument of the combiner
      have hMF : M ≠ F := ne_of_agent hN₂ aM₂ aF₂ hd.g_op
      have hMlF : ¬ M ∈ lF := fun hm => fF _ hm (.inl ⟨_, aM⟩)
      obtain ⟨N₃, sts₃, ⟨cv, lv, pv, hlv, elv, fv⟩, k₃, hag₃⟩ :=
        prim_computes hs hd hz hg lF hN₂ aF₂ pF hlF pFM₂ ⟨hMF, hMlF⟩ elF
      have hN₃ := Steps.wf hN₂ sts₃
      have U₃ : ∀ i, N.Used i → N₃.Used i := fun i hu => Steps.used hN₂ sts₃ (U₂ i hu)
      have hC₃ : Addition.Closed ar (gone N₂ F lF) N₂ := Addition.gone_closed hN₂ pF hlF
      -- what it keeps: the combiner, the successor and the copy under it, the result port
      have ng3M : ¬ gone N₂ F lF M := not_gone hMF hMlF (.inl ⟨_, aM₂⟩)
      have ng3U : ¬ gone N₂ F lF U :=
        not_gone (ne_of_agent hN₂ aU₂ aF₂ hd.op_succ) (fun hm => fF _ hm (.inl ⟨_, aU⟩))
          (.inl ⟨_, aU₂⟩)
      have ng3r : ¬ gone N₂ F lF r.1 :=
        not_gone (fun e' => hF (e' ▸ hru)) (fun hm => fF _ hm hru₁) (U₂ _ hru)
      have havlU : ∀ j, j ∈ lU → ¬ gone N₂ F lF j := hlU.avoid hC₃ pU ng3U
      have hlU₃ : NumList N₃ cU lU := hlU.keeps k₃ havlU
      have pU₃ : N₃.Paired ar (U, 1) (cU, 0) := k₃.paired pU ng3U (havlU cU hlU.head_mem)
      have aU₃ : N₃.agent U succ := k₃.agent aU₂ ng3U
      have aM₃ : N₃.agent M g := k₃.agent aM₂ ng3M
      have pUM₃ : N₃.Paired ar (U, 0) (M, 1) := k₃.paired pUM₂ ng3U ng3M
      have pMx₃ : N₃.Paired ar (M, 2) r := k₃.paired pMx₂ ng3M ng3r
      -- the combiner combines
      have hrUl : ¬ r.1 ∈ U :: lU := fun hm =>
        (List.mem_cons.1 hm).elim (fun e' => hU (e' ▸ hru)) fun hm' => fU _ hm' hru₁
      have hQU : ∀ i, i ∈ U :: lU → ¬ N.Used i := by
        intro i hi
        rcases List.mem_cons.1 hi with e1 | hm'
        · rw [e1]
          exact hU
        · exact fun hu => fU i hm' (hused i hu)
      obtain ⟨N₄, sts₄, ⟨cw, lw, pw, hlw, elw, fw⟩, k₄, hag₄⟩ :=
        hg lv (fun i => ¬ N.Used i) hN₃ aM₃ pv hlv (pUM₃.symm hN₃) (.next aU₃ pU₃ hlU₃) pMx₃
          ⟨fun e' => hM (e' ▸ hru), fun hm => fv _ hm (U₂ _ hru), hrUl⟩ elv
          (by rw [List.length_cons, elU]) hQU (fun i hu hu' => hu (U₃ i hu'))
      subst hn
      refine ⟨N₄, ((Steps.head st sts₂).trans sts₃).trans sts₄, ⟨cw, lw, pw, hlw, elw, fw⟩,
        (((k₁.trans k₂).trans k₃).trans k₄).mono ?_, ?_⟩
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

/-! ### The arithmetic of multiplication by recursion -/

theorem iter_mul (m n : Nat) : iter (fun _ => 0) (fun n v => n + v) m n = m * n := by
  induction m with
  | zero => exact (Nat.zero_mul n).symm
  | succ m ih =>
    show n + iter _ _ m n = (m + 1) * n
    rw [ih, Nat.succ_mul, Nat.add_comm]

theorem iterCost_mul (m n : Nat) :
    iterCost (fun n => n + 1 + 1) (fun m _ => m + 1) (fun _ => 0) (fun n v => n + v) m n =
      prodCost m n := by
  induction m with
  | zero =>
    show n + 1 + 1 = prodCost 0 n
    unfold prodCost
    omega
  | succ m ih =>
    show n + 1 + 1 + iterCost _ _ _ _ m n + (n + 1) = prodCost (m + 1) n
    rw [ih]
    have e₁ : (m + 1 + 1) * (n + 2) = (m + 1) * (n + 2) + (n + 2) := Nat.succ_mul _ _
    have e₂ : (m + 1) * (n + 1) = m * (n + 1) + (n + 1) := Nat.succ_mul _ _
    unfold prodCost
    omega

end Core

end INet
