import InteractionNets.Examples

/-! # Addition, in any system that contains it

The proof that the adder adds, for an arbitrary interaction system with
three symbols `zero`, `succ` and `add` and the two rules of unary
addition among its rules (`Addition.Rules`).  The system may have any
other symbols and rules.

Numerals (`Num`, `IsNum`), towers of successors (`Tower`) and the
situation that addition is about (`Config`) are defined from the arities
and the three symbols.  In that situation the adder runs for `m + 1`
steps, after which the result port carries the numeral `m + n` and the
net has no adder left (`Config.steps`).  When every rule of the system
involves an adder, a net without adders is normal, and what is reached is
the normal form (`add_correct`).

The system `Arith` is the case of exactly these three symbols and two
rules; its notions are these, at its symbols.
-/

namespace INet

namespace Addition

variable {S : Type}

/-- `0 + y = y`: the second argument is wired to the result. -/
def zeroData : RuleData S :=
  RuleData.ofWires [] [(.ifc false 0, .ifc false 1)]

/-- `S x + y = S (x + y)`: a new `succ` on the result, a new `add` on
`x`. -/
def succData (succ add : S) : RuleData S :=
  RuleData.ofWires [((some false, 0), succ), ((some true, 0), add)]
    [(.ifc false 1, .new (some false) 0 0),            -- result — principal of the new `succ`
      (.new (some false) 0 1, .new (some true) 0 2),    -- its argument — result of the new `add`
      (.new (some true) 0 0, .ifc true 0),              -- first argument of the new `add` — `x`
      (.new (some true) 0 1, .ifc false 0)]             -- its second argument — `y`

/-- **A system that contains addition**: three different symbols, and the
two rules of unary addition for `add` meeting `zero` and `add` meeting
`succ`. -/
structure Rules (sys : System S) (zero succ add : S) : Prop where
  zero_ne_add : zero ≠ add
  succ_ne_add : succ ≠ add
  zero_ne_succ : zero ≠ succ
  rule_zero : sys.rule add zero = some (zeroData (S := S)).toX.toRhs
  rule_succ : sys.rule add succ = some (succData succ add).toX.toRhs

/-- Agent `i` is the head of the numeral `k`. -/
def Num (ar : S → Nat) (zero succ : S) (N : Net S) : Id → Nat → Prop
  | i, 0 => N.agent i zero
  | i, k + 1 => N.agent i succ ∧ ∃ i', N.Paired ar (i, 1) (i', 0) ∧ Num ar zero succ N i' k

/-- The port `p` is wired to the numeral `k`. -/
def IsNum (ar : S → Nat) (zero succ : S) (N : Net S) (p : Port) (k : Nat) : Prop :=
  ∃ i, N.Paired ar p (i, 0) ∧ Num ar zero succ N i k

/-- Above the port `x` there are `j` successors, the last of which has its
principal port wired to `r`. -/
def Tower (ar : S → Nat) (succ : S) (N : Net S) : Port → Nat → Port → Prop
  | x, 0, r => x = r
  | x, j + 1, r =>
    ∃ u x', x = (u, 1) ∧ N.agent u succ ∧ N.Paired ar x' (u, 0) ∧ Tower ar succ N x' j r

variable {ar : S → Nat} {zero succ add : S} {N M : Net S} {a s u : Id} {p q r : Port} {σ : S}

theorem Num.label : ∀ {k : Nat} {i : Id}, Num ar zero succ N i k →
    N.agent i zero ∨ N.agent i succ
  | 0, _, h => .inl h
  | _ + 1, _, h => .inr h.1

/-- Numerals are observations. -/
theorem Num.obs (ho : N.ObsEq ar M) : ∀ {k : Nat} {i : Id},
    Num ar zero succ N i k → Num ar zero succ M i k
  | 0, _, h => (ho.agent _ _).1 h
  | _ + 1, _, ⟨hs, i', hp, hn⟩ =>
    ⟨(ho.agent _ _).1 hs, i', (ho.paired _ _).1 hp, Num.obs ho hn⟩

theorem IsNum.obs (ho : N.ObsEq ar M) {p : Port} {k : Nat} (h : IsNum ar zero succ N p k) :
    IsNum ar zero succ M p k := by
  obtain ⟨i, hp, hn⟩ := h
  exact ⟨i, (ho.paired _ _).1 hp, hn.obs ho⟩

/-- A numeral under a tower of `j` successors is a numeral `j` larger. -/
theorem Tower.num : ∀ {j : Nat} {x : Port} {n : Nat},
    Tower ar succ N x j r → IsNum ar zero succ N x n → IsNum ar zero succ N r (j + n)
  | 0, x, n, ht, h => by
    have e : x = r := ht
    subst e
    rw [Nat.zero_add]
    exact h
  | j + 1, x, n, ⟨u, x', e, hu, hp, ht⟩, h => by
    subst e
    obtain ⟨t, hpt, hnt⟩ := h
    have h' : IsNum ar zero succ N x' (n + 1) := ⟨u, hp, hu, t, hpt, hnt⟩
    have e : j + 1 + n = j + (n + 1) := by omega
    rw [e]
    exact Tower.num ht h'

/-- An adder `a` whose principal port faces the agent `s`, which is not an
adder. -/
structure Adder (ar : S → Nat) (add : S) (N : Net S) (a s : Id) (σ : S) : Prop where
  wf : N.WF ar
  ha : N.agent a add
  hs : N.agent s σ
  hσ : σ ≠ add
  pair : N.Paired ar (a, 0) (s, 0)

namespace Adder

theorem ne_add (h : Adder ar add N a s σ) {i : Id} {γ : S} (hi : N.agent i γ) (hγ : γ ≠ add) :
    i ≠ a := by
  rintro rfl
  exact hγ (h.wf.agent_fun hi h.ha)

theorem site (h : Adder ar add N a s σ) : Site ar N a s add σ :=
  ⟨h.wf, h.ha, h.hs, (h.ne_add h.hs h.hσ).symm, h.pair.2.2⟩

/-- Only the adder is wired to the principal port of `s`. -/
theorem not_s (h : Adder ar add N a s σ) {q : Port} {i : Id} (hq : N.Paired ar q (i, 0))
    (hne : q ≠ (a, 0)) : i ≠ s := by
  rintro rfl
  exact hne (hq.det_left h.wf h.pair)

/-- A numeral that does not start at `s` survives the firing. -/
theorem num_fire (h : Adder ar add N a s σ) (hza : zero ≠ add) (hsa : succ ≠ add)
    (R : Rhs S) : ∀ {k : Nat} {i : Id}, Num ar zero succ N i k → i ≠ s →
      Num ar zero succ (N.fire a s R) i k
  | 0, i, hz, hne => .inl ⟨hz, h.ne_add hz hza, hne⟩
  | k + 1, i, ⟨hsu, i', hp, hn⟩, hne => by
    have hia : i ≠ a := h.ne_add hsu hsa
    have hi's : i' ≠ s := h.not_s hp (port_ne_snd (by decide))
    have hi'a : i' ≠ a := by
      rcases hn.label with hl | hl
      · exact h.ne_add hl hza
      · exact h.ne_add hl hsa
    exact ⟨.inl ⟨hsu, hia, hne⟩, i', h.site.paired_fire hp hia hne hi'a hi's,
      num_fire h hza hsa R hn hi's⟩

/-- A tower that ends on a free port survives the firing. -/
theorem tower_fire (h : Adder ar add N a s σ) (hsa : succ ≠ add) (R : Rhs S) (hr : N.free r) :
    ∀ {j : Nat} {x : Port}, Tower ar succ N x j r →
      x.1 ≠ a ∧ x.1 ≠ s ∧ Tower ar succ (N.fire a s R) x j r
  | 0, x, ht => by
    have e : x = r := ht
    subst e
    exact ⟨fun e => h.wf.free_agent (i := x.1) (k := x.2) hr (e ▸ h.ha),
      fun e => h.wf.free_agent (i := x.1) (k := x.2) hr (e ▸ h.hs), rfl⟩
  | j + 1, x, ⟨u, x', e, hu, hp, ht⟩ => by
    subst e
    obtain ⟨hx'a, hx's, ht'⟩ := tower_fire h hsa R hr ht
    have hua : u ≠ a := h.ne_add hu hsa
    have hus : u ≠ s := h.not_s hp (fun e => hx'a (congrArg Prod.fst e))
    exact ⟨hua, hus, u, x', rfl, .inl ⟨hu, hua, hus⟩,
      h.site.paired_fire hp hx'a hx's hua hus, ht'⟩

end Adder

/-- The situation that addition is about: the only adder `a` of the net has
the numeral `m` as its first argument and the numeral `n` as its second, and
its result goes up a tower of `j` successors to the free port `r`. -/
structure Config (ar : S → Nat) (zero succ add : S) (N : Net S) (a : Id) (j m n : Nat)
    (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a add
  only : ∀ i, N.agent i add → i = a
  fst : IsNum ar zero succ N (a, 0) m
  snd : IsNum ar zero succ N (a, 1) n
  out : ∃ x, N.Paired ar (a, 2) x ∧ Tower ar succ N x j r
  free : N.free r

variable {sys : System S} {j m n : Nat}

/-- `0 + n = n`: the adder meets `zero`; one step later `r` carries the
numeral `j + n` and the net has no adder left. -/
theorem Config.zero_step (H : Rules sys zero succ add)
    (c : Config sys.ar zero succ add N a j 0 n r) :
    ∃ N', Step sys N N' ∧ IsNum sys.ar zero succ N' r (j + n) ∧ ∀ i, ¬ N'.agent i add := by
  obtain ⟨z, hpz, hz⟩ := c.fst
  have hz' : N.agent z zero := hz
  have h : Adder sys.ar add N a z zero := ⟨c.wf, c.ha, hz', H.zero_ne_add, hpz⟩
  have red : Redex sys N a z add zero (zeroData (S := S)).toX.toRhs :=
    ⟨c.ha, hz', h.site.ne, hpz.2.2, H.rule_zero⟩
  have st : Step sys N (N.fire a z (zeroData (S := S)).toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN' := Step.wf c.wf st
  obtain ⟨t, hpt, hnt⟩ := c.snd
  obtain ⟨x, hpx, htx⟩ := c.out
  have hta : t ≠ a := by
    rcases hnt.label with hl | hl
    · exact h.ne_add hl H.zero_ne_add
    · exact h.ne_add hl H.succ_ne_add
  have hts : t ≠ z := h.not_s hpt (port_ne_snd (by decide))
  obtain ⟨hxa, hxs, htx'⟩ :=
    h.tower_fire H.succ_ne_add (zeroData (S := S)).toX.toRhs c.free htx
  have hl : (zeroData (S := S)).toX.toRhs.link (.ifc false 0) (.ifc false 1) := rfl
  have hp : (N.fire a z (zeroData (S := S)).toX.toRhs).Paired sys.ar (t, 0) x :=
    h.site.paired_fire_ifc_ifc hl (hpt.symm c.wf) (hpx.symm c.wf) hta hts hxa hxs
  refine ⟨_, st, htx'.num ⟨t, hp.symm hN',
    h.num_fire H.zero_ne_add H.succ_ne_add _ hnt hts⟩, ?_⟩
  rintro i (⟨hi, hia, -⟩ | ⟨o, j', -, hlab⟩)
  · exact hia (c.only i hi)
  · cases hlab

/-- The only new adder of the rule for `succ` is the one of the second
side. -/
theorem succ_lab_add (hsa : succ ≠ add) {o : Option Bool} {j : Nat}
    (h : (succData succ add).toX.toRhs.lab o j = some add) : o = some true ∧ j = 0 := by
  have h' : assoc (o, j) (succData succ add).agents = some add := h
  have hm : ((o, j), add) ∈ [(((some false : Option Bool), 0), succ), ((some true, 0), add)] :=
    assoc_mem h'
  rcases List.mem_cons.1 hm with e | hm'
  · injection e with _ e2
    exact absurd e2.symm hsa
  · rcases List.mem_cons.1 hm' with e | hm''
    · injection e with e1 _
      injection e1 with e3 e4
      exact ⟨e3, e4⟩
    · exact absurd hm'' List.not_mem_nil

/-- `S m + n = S (m + n)`: the adder meets `succ`; one step later a new
adder faces `m`, under a tower one successor higher. -/
theorem Config.succ_step (H : Rules sys zero succ add)
    (c : Config sys.ar zero succ add N a j (m + 1) n r) :
    ∃ N' a', Step sys N N' ∧ Config sys.ar zero succ add N' a' (j + 1) m n r := by
  obtain ⟨s, hps, hsu, s', hps', hns'⟩ := c.fst
  have h : Adder sys.ar add N a s succ := ⟨c.wf, c.ha, hsu, H.succ_ne_add, hps⟩
  have hR : (succData succ add).toX.toRhs.WF sys.ar add succ := sys.rule_wf H.rule_succ
  have red : Redex sys N a s add succ (succData succ add).toX.toRhs :=
    ⟨c.ha, hsu, h.site.ne, hps.2.2, H.rule_succ⟩
  have st : Step sys N (N.fire a s (succData succ add).toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
  have hN' := Step.wf c.wf st
  obtain ⟨t, hpt, hnt⟩ := c.snd
  obtain ⟨x, hpx, htx⟩ := c.out
  have hta : t ≠ a := by
    rcases hnt.label with hl | hl
    · exact h.ne_add hl H.zero_ne_add
    · exact h.ne_add hl H.succ_ne_add
  have hts : t ≠ s := h.not_s hpt (port_ne_snd (by decide))
  have hs'a : s' ≠ a := by
    rcases hns'.label with hl | hl
    · exact h.ne_add hl H.zero_ne_add
    · exact h.ne_add hl H.succ_ne_add
  have hs's : s' ≠ s := h.not_s hps' (port_ne_snd (by decide))
  obtain ⟨hxa, hxs, htx'⟩ :=
    h.tower_fire H.succ_ne_add (succData succ add).toX.toRhs c.free htx
  -- the four wires of the right-hand side
  have p₁ : (N.fire a s (succData succ add).toX.toRhs).Paired sys.ar x
      (child a s (some false) 0, 0) :=
    h.site.paired_fire_ifc_new hR
      (show (succData succ add).toX.toRhs.link (.ifc false 1) (.new (some false) 0 0) from rfl)
      (hpx.symm c.wf) hxa hxs
  have p₂ : (N.fire a s (succData succ add).toX.toRhs).Paired sys.ar
      (child a s (some false) 0, 1) (child a s (some true) 0, 2) :=
    Site.paired_fire_new_new hR
      (show (succData succ add).toX.toRhs.link (.new (some false) 0 1) (.new (some true) 0 2)
        from rfl)
  have p₃ : (N.fire a s (succData succ add).toX.toRhs).Paired sys.ar (s', 0)
      (child a s (some true) 0, 0) :=
    h.site.paired_fire_ifc_new hR
      (show (succData succ add).toX.toRhs.link (.ifc true 0) (.new (some true) 0 0) from rfl)
      (hps'.symm c.wf) hs'a hs's
  have p₄ : (N.fire a s (succData succ add).toX.toRhs).Paired sys.ar (t, 0)
      (child a s (some true) 0, 1) :=
    h.site.paired_fire_ifc_new hR
      (show (succData succ add).toX.toRhs.link (.ifc false 0) (.new (some true) 0 1) from rfl)
      (hpt.symm c.wf) hta hts
  refine ⟨_, child a s (some true) 0, st, hN', .inr ⟨some true, 0, rfl, rfl⟩, ?_,
    ⟨s', p₃.symm hN', h.num_fire H.zero_ne_add H.succ_ne_add _ hns' hs's⟩,
    ⟨t, p₄.symm hN', h.num_fire H.zero_ne_add H.succ_ne_add _ hnt hts⟩,
    ⟨_, p₂.symm hN', child a s (some false) 0, x, rfl, .inr ⟨some false, 0, rfl, rfl⟩, p₁, htx'⟩,
    c.free⟩
  rintro i (⟨hi, hia, -⟩ | ⟨o, j', rfl, hlab⟩)
  · exact absurd (c.only i hi) hia
  · obtain ⟨rfl, rfl⟩ := succ_lab_add H.succ_ne_add hlab
    rfl

/-- **The adder adds, in any system that contains addition.**  The adder
runs for `m + 1` steps, after which `r` carries the numeral `j + m + n`
and the net has no adder left. -/
theorem Config.steps (H : Rules sys zero succ add) :
    ∀ {m : Nat} {N : Net S} {a : Id} {j : Nat}, Config sys.ar zero succ add N a j m n r →
      ∃ N', Steps (Step sys) (m + 1) N N' ∧ IsNum sys.ar zero succ N' r (j + m + n) ∧
        ∀ i, ¬ N'.agent i add
  | 0, N, a, j, c => by
    obtain ⟨N', st, hnum, hno⟩ := c.zero_step H
    exact ⟨N', .single st, hnum, hno⟩
  | m + 1, N, a, j, c => by
    obtain ⟨N₁, a', st, c'⟩ := c.succ_step H
    obtain ⟨N', sts, hnum, hno⟩ := Config.steps H c'
    refine ⟨N', .head st sts, ?_, hno⟩
    have e : j + (m + 1) + n = j + 1 + m + n := by omega
    rw [e]
    exact hnum

/-- When every rule involves an adder, a net without adders is normal. -/
theorem normal_of_no_add (honly : ∀ α β, α ≠ add → β ≠ add → sys.rule α β = none)
    (h : ∀ i, ¬ N.agent i add) : Normal (Step sys) N := by
  rintro N' ⟨a, b, α, β, R, red, -⟩
  have hα : α ≠ add := fun e => h a (e ▸ red.ha)
  have hβ : β ≠ add := fun e => h b (e ▸ red.hb)
  have hr := red.rule
  rw [honly α β hα hβ] at hr
  cases hr

/-- **Addition is correct, for all inputs**, in a system that contains
addition and in which every rule involves an adder: a net whose only
adder has the numerals `m` and `n` as arguments and the free port `r` as
result reduces in `m + 1` steps to a normal form in which `r` carries the
numeral `m + n`. -/
theorem add_correct (H : Rules sys zero succ add)
    (honly : ∀ α β, α ≠ add → β ≠ add → sys.rule α β = none)
    (c : Config sys.ar zero succ add N a 0 m n r) :
    ∃ N', Steps (Step sys) (m + 1) N N' ∧ Normal (Step sys) N' ∧
      IsNum sys.ar zero succ N' r (m + n) := by
  obtain ⟨N', sts, hnum, hno⟩ := Config.steps H c
  rw [Nat.zero_add] at hnum
  exact ⟨N', sts, normal_of_no_add honly hno, hnum⟩

end Addition

end INet
