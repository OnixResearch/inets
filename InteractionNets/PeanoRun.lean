import InteractionNets.PeanoRec

/-! # The machine, for any agent that computes

The factorial was proved on the machine by a proof of its own
(`Peano.fac_rest`, `Peano.fac_fair`), and that proof uses the factorial
only through `Peano.fac_computes`.  It is done here once, for any agent
of one argument that computes (`Peano.Computes1`).

`Peano.unaryNet op n` is the net with the agent `op` on the numeral `n`
and its result on the free port `([0], 0)`.  If `op` computes `f` in `c`
steps, then on the machine, with any number of threads and any schedule,
a run on that net that is at rest has made exactly `c n` interactions
and holds the numeral `f n` (`Peano.unary_rest`), and a fair run comes
to rest (`Peano.unary_fair`).

The factorial is a case (`Peano.fac_rest'`, `Peano.fac_fair'`), and so is
the lazy caterer, which had no theorem for the machine
(`Peano.cater_rest`, `Peano.cater_fair`).

The same for two arguments (`Peano.Computes2`, `Peano.binaryNet`,
`Peano.binary_rest`, `Peano.binary_fair`), with the multiplier and the
power as cases (`Peano.prod_rest'`, `Peano.power_rest'`,
`Peano.prod_fair'`, `Peano.power_fair'`).  The cases use the theorems
derived from recursion (`Peano.mul_computes'`, `Peano.pow_computes'`,
`Peano.fac_computes'`), so the chain from the rules to the machine goes
through the general theorems alone.
-/

namespace INet

namespace Peano

open Addition (gone gone2)

variable {N : Net Peano} {r : Port}

/-- **The situation of an agent of one argument.**  The agent `a` has the
symbol `op`, the numeral `n` as argument and the free port `r` as result,
and the net has no other agents than it and the successors and zeros. -/
structure Unary (op : Peano) (N : Net Peano) (a : Id) (n : Nat) (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a op
  fst : IsNum N (a, 0) n
  out : N.Paired ar (a, 1) r
  free : N.free r
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = a

/-- **An agent that computes is correct alone.**  A net in the situation
`Peano.Unary` reduces in `c n` steps to a normal form in which `r`
carries the numeral `f n`. -/
theorem unary_correct {op : Peano} {f c : Nat → Nat} (H : Computes1 op f c) {a : Id} {n : Nat}
    (u : Unary op N a n r) :
    ∃ N', Steps (Step system) (c n) N N' ∧ Normal (Step system) N' ∧ IsNum N' r (f n) := by
  have hN := u.wf
  obtain ⟨h, hp, hn⟩ := u.fst
  obtain ⟨l, hl, el⟩ := Addition.Num.list hn
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) u.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) u.free h
  obtain ⟨N', sts, hres, -, hag⟩ := H l hN u.ha hp hl u.out
    ⟨fun e' => hN.free_agent (i := r.1) (k := r.2) u.free (e' ▸ u.ha), hrl⟩ el
  refine ⟨N', sts, normal_of_numerals fun i γ hi => ?_, hres.isNum⟩
  rcases hag i γ hi with hz | hsu | ⟨hi₀, hne⟩
  · exact .inl hz
  · exact .inr hsu
  · rcases u.only i γ hi₀ with hz | hsu | e'
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e' hne

/-! ### The nets, and the machine on them -/

/-- The net for `op 0`, with the result on the free port `([0], 0)`. -/
def unaryBase (op : Peano) : XNet Peano :=
  XNet.ofWires [([1], op), ([2], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([0], 0))]

/-- The net for `op n`: `n` successors are put on the argument of the
agent of `op 0`. -/
def unaryNet (op : Peano) : Nat → XNet Peano
  | 0 => unaryBase op
  | n + 1 => (unaryNet op n).pushOn succ ([1], 0) [n + 3]

/-- The situation of an agent of one argument, on a valid input whose
identifiers are numbered below `c`. -/
structure GoodUnary (op : Peano) (X : XNet Peano) (n c : Nat) : Prop where
  ok : X.Ok ar
  config : Unary op X.toNet [1] n ([0], 0)
  below : X.Below c

/-- One more successor on the argument. -/
theorem GoodUnary.push {op : Peano} {X : XNet Peano} {n c : Nat} (g : GoodUnary op X n c) :
    GoodUnary op (X.pushOn succ ([1], 0) [c]) (n + 1) (c + 1) := by
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

/-- The net for `op 0` is valid for every agent of one argument; the
check is evaluated for each symbol. -/
theorem unaryBase_ok {op : Peano} (h : ar op = 1) (h1 : succ ≠ op) : (unaryBase op).Ok ar := by
  cases op
  all_goals first
    | exact absurd h (by decide)
    | exact absurd rfl h1
    | decide

theorem good_unaryBase {op : Peano} (h : ar op = 1) (h1 : succ ≠ op) :
    GoodUnary op (unaryBase op) 0 3 := by
  have hX := unaryBase_ok h h1
  -- the wires, the free port and the names do not depend on the symbol
  have ew : (unaryBase op).wires = (unaryBase fac).wires := rfl
  have ef : (unaryBase op).free = (unaryBase fac).free := rfl
  have eu : (unaryBase op).usedIds = (unaryBase fac).usedIds := rfl
  refine ⟨hX, ⟨hX.1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact List.mem_cons_self
  · exact ⟨[2], hX.link_iff.1 (by rw [ew]; decide),
      List.mem_cons_of_mem _ List.mem_cons_self⟩
  · exact hX.link_iff.1 (by rw [ew]; decide)
  · show ([0], 0) ∈ (unaryBase op).free
    rw [ef]
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), op), ([2], zero)] := hi
    rcases List.mem_cons.1 hi' with e | hi''
    · exact .inr (.inr (Prod.mk.inj e).1)
    · rcases List.mem_cons.1 hi'' with e | h3
      · exact .inl (Prod.mk.inj e).2
      · exact absurd h3 List.not_mem_nil
  · intro i hi
    have hall : ∀ i ∈ (unaryBase op).usedIds, ∃ j, j < 3 ∧ i = [j] := by
      rw [eu]
      decide
    exact hall i (XNet.mem_usedIds hi)

/-- **The nets for `op n` are in the situation**, for all `n`. -/
theorem good_unaryNet {op : Peano} (h : ar op = 1) (h1 : succ ≠ op) :
    ∀ n, GoodUnary op (unaryNet op n) n (n + 3)
  | 0 => good_unaryBase h h1
  | n + 1 => (good_unaryNet h h1 n).push

/-- **An agent that computes comes out right, whatever the threads do**:
with any number of threads and any schedule, a run of the machine on the
net for `op n` that is at rest has made exactly `c n` interactions, and
its memory has the numeral `f n` on the free port. -/
theorem unary_rest {op : Peano} {f c : Nat → Nat} (H : Computes1 op f c) (har : ar op = 1)
    (h1 : succ ≠ op) (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (unaryNet op n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (unaryNet op n) nt).trace xsys σ i).2 = c n ∧
      IsNum ((XMach.init (unaryNet op n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (f n) := by
  have g := good_unaryNet har h1 n
  obtain ⟨N', hs, hn', hnum⟩ := unary_correct H g.config
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (unaryNet op n) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (unaryNet op n) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **An agent that computes, under any fair schedule**: with any number
of threads, as long as every thread keeps being scheduled, the run comes
to rest after `c n` interactions with the numeral `f n` in memory. -/
theorem unary_fair {op : Peano} {f c : Nat → Nat} (H : Computes1 op f c) (har : ar op = 1)
    (h1 : succ ≠ op) (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (unaryNet op n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (unaryNet op n) nt).trace xsys σ i).2 = c n ∧
      IsNum ((XMach.init (unaryNet op n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (f n) := by
  have g := good_unaryNet har h1 n
  obtain ⟨N', hs, hn', hnum⟩ := unary_correct H g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-! ### The factorial and the lazy caterer -/

/-- The nets for factorials are the nets of this module. -/
theorem facNet_eq : ∀ n, facNet n = unaryNet fac n
  | 0 => rfl
  | n + 1 => by
    show (facNet n).pushOn succ ([1], 0) [n + 3] = (unaryNet fac n).pushOn succ ([1], 0) [n + 3]
    rw [facNet_eq n]

/-- **Factorials on the machine**, as a case. -/
theorem fac_rest' (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (facNet n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (facNet n) nt).trace xsys σ i).2 = facCost n ∧
      IsNum ((XMach.init (facNet n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (fact n) := by
  rw [facNet_eq] at hr ⊢
  exact unary_rest fac_computes' rfl (by decide) n hnt σ hr

/-- **Factorials under any fair schedule**, as a case. -/
theorem fac_fair' (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (facNet n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (facNet n) nt).trace xsys σ i).2 = facCost n ∧
      IsNum ((XMach.init (facNet n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (fact n) := by
  rw [facNet_eq]
  exact unary_fair fac_computes' rfl (by decide) n hnt σ hfair

/-- **The lazy caterer on the machine**: with any number of threads and
any schedule, a run on the net for `c n` that is at rest has made exactly
`caterCost n` interactions and holds the numeral `c n`. -/
theorem cater_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (unaryNet cater n) nt).trace xsys σ i).2 = caterCost n ∧
      IsNum ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (cate n) :=
  unary_rest cater_computes rfl (by decide) n hnt σ hr

/-- **The lazy caterer under any fair schedule**: the run comes to rest
after `caterCost n` interactions with the numeral `c n` in memory. -/
theorem cater_fair (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (unaryNet cater n) nt).trace xsys σ i).2 = caterCost n ∧
      IsNum ((XMach.init (unaryNet cater n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (cate n) :=
  unary_fair cater_computes rfl (by decide) n hnt σ hfair

/-! ### Agents of two arguments -/

/-- **The situation of an agent of two arguments.**  The agent `a` has
the symbol `op`, the numerals `m` and `n` as arguments and the free port
`r` as result, and the net has no other agents than it and the
successors and zeros. -/
structure Binary (op : Peano) (N : Net Peano) (a : Id) (m n : Nat) (r : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a op
  fst : IsNum N (a, 0) m
  snd : IsNum N (a, 1) n
  out : N.Paired ar (a, 2) r
  free : N.free r
  only : ∀ i γ, N.agent i γ → γ = zero ∨ γ = succ ∨ i = a

/-- **An agent of two arguments that computes is correct alone.** -/
theorem binary_correct {op : Peano} {f c : Nat → Nat → Nat} (H : Computes2 op f c) {a : Id}
    {m n : Nat} (u : Binary op N a m n r) :
    ∃ N', Steps (Step system) (c m n) N N' ∧ Normal (Step system) N' ∧ IsNum N' r (f m n) := by
  have hN := u.wf
  obtain ⟨h₁, hp₁, hn₁⟩ := u.fst
  obtain ⟨l₁, hl₁, e₁⟩ := Addition.Num.list hn₁
  obtain ⟨h₂, hp₂, hn₂⟩ := u.snd
  obtain ⟨l₂, hl₂, e₂⟩ := Addition.Num.list hn₂
  have hrl : ∀ (h : Id) (l : List Id), NumList N h l → ¬ r.1 ∈ l := fun h l hl hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) u.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) u.free h
  obtain ⟨N', sts, hres, -, hag⟩ := H l₁ hN u.ha hp₁ hl₁ hp₂ hl₂ u.out
    ⟨fun e' => hN.free_agent (i := r.1) (k := r.2) u.free (e' ▸ u.ha), hrl _ _ hl₁,
      hrl _ _ hl₂⟩ e₁ e₂
  refine ⟨N', sts, normal_of_numerals fun i γ hi => ?_, hres.isNum⟩
  rcases hag i γ hi with hz | hsu | ⟨hi₀, hne⟩
  · exact .inl hz
  · exact .inr hsu
  · rcases u.only i γ hi₀ with hz | hsu | e'
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e' hne

/-- The net for `op 0 0`, with the result on the free port `([0], 0)`. -/
def binaryBase (op : Peano) : XNet Peano :=
  XNet.ofWires [([1], op), ([2], zero), ([3], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

/-- The net for `op 0 n`. -/
def binarySnd (op : Peano) : Nat → XNet Peano
  | 0 => binaryBase op
  | n + 1 => (binarySnd op n).pushOn succ ([1], 1) [n + 4]

/-- The net for `op m n`: `m` successors on the first argument of the
agent of `op 0 0`, and `n` on the second. -/
def binaryNet (op : Peano) : Nat → Nat → XNet Peano
  | 0, n => binarySnd op n
  | m + 1, n => (binaryNet op m n).pushOn succ ([1], 0) [m + n + 4]

/-- The situation of an agent of two arguments, on a valid input whose
identifiers are numbered below `c`. -/
structure GoodBinary (op : Peano) (X : XNet Peano) (m n c : Nat) : Prop where
  ok : X.Ok ar
  config : Binary op X.toNet [1] m n ([0], 0)
  below : X.Below c

/-- One more successor on the first argument. -/
theorem GoodBinary.push_fst {op : Peano} {X : XNet Peano} {m n c : Nat}
    (g : GoodBinary op X m n c) :
    GoodBinary op (X.pushOn succ ([1], 0) [c]) (m + 1) n (c + 1) := by
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
    refine ⟨hm'.wf, .inl cf.ha, ?_, ?_, ?_, cf.free, ?_⟩
    · exact ⟨[c], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, h,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnh⟩
    · exact ⟨t, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hpt, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩), hnum hnt⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 cf.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)
    · rintro i γ (hi | ⟨-, e'⟩)
      · exact cf.only i γ hi
      · exact .inr (.inl e')

/-- One more successor on the second argument. -/
theorem GoodBinary.push_snd {op : Peano} (h0 : zero ≠ op) (h1 : succ ≠ op) {X : XNet Peano}
    {m n c : Nat} (g : GoodBinary op X m n c) :
    GoodBinary op (X.pushOn succ ([1], 1) [c]) m (n + 1) (c + 1) := by
  have cf := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := cf.fst
  obtain ⟨t, hpt, hnt⟩ := cf.snd
  have hsucc : ∀ i, X.toNet.agent i succ → i ≠ [1] := by
    rintro i hi rfl
    exact h1 (cf.wf.agent_fun hi cf.ha)
  have ht1 : t ≠ [1] := by
    rintro rfl
    rcases Addition.Num.label hnt with hl | hl
    · exact h0 (cf.wf.agent_fun hl cf.ha)
    · exact h1 (cf.wf.agent_fun hl cf.ha)
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
    refine ⟨hm'.wf, .inl cf.ha, ?_, ?_, ?_, cf.free, ?_⟩
    · exact ⟨h, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hph, port_ne_snd (by decide),
        fun e' => ht1 (congrArg Prod.fst e').symm⟩), hnum hnh⟩
    · exact ⟨[c], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, t,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnt⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 cf.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)
    · rintro i γ (hi | ⟨-, e'⟩)
      · exact cf.only i γ hi
      · exact .inr (.inl e')

/-- The net for `op 0 0` is valid for every agent of two arguments; the
check is evaluated for each symbol. -/
theorem binaryBase_ok {op : Peano} (h : ar op = 2) : (binaryBase op).Ok ar := by
  cases op
  all_goals first
    | exact absurd h (by decide)
    | decide

theorem good_binaryBase {op : Peano} (h : ar op = 2) : GoodBinary op (binaryBase op) 0 0 4 := by
  have hX := binaryBase_ok h
  -- the wires, the free port and the names do not depend on the symbol
  have ew : (binaryBase op).wires = (binaryBase mul).wires := rfl
  have ef : (binaryBase op).free = (binaryBase mul).free := rfl
  have eu : (binaryBase op).usedIds = (binaryBase mul).usedIds := rfl
  refine ⟨hX, ⟨hX.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact List.mem_cons_self
  · exact ⟨[2], hX.link_iff.1 (by rw [ew]; decide),
      List.mem_cons_of_mem _ List.mem_cons_self⟩
  · exact ⟨[3], hX.link_iff.1 (by rw [ew]; decide),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · exact hX.link_iff.1 (by rw [ew]; decide)
  · show ([0], 0) ∈ (binaryBase op).free
    rw [ef]
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), op), ([2], zero), ([3], zero)] := hi
    rcases List.mem_cons.1 hi' with e | hi''
    · exact .inr (.inr (Prod.mk.inj e).1)
    · rcases List.mem_cons.1 hi'' with e | hi'''
      · exact .inl (Prod.mk.inj e).2
      · rcases List.mem_cons.1 hi''' with e | h4
        · exact .inl (Prod.mk.inj e).2
        · exact absurd h4 List.not_mem_nil
  · intro i hi
    have hall : ∀ i ∈ (binaryBase op).usedIds, ∃ j, j < 4 ∧ i = [j] := by
      rw [eu]
      decide
    exact hall i (XNet.mem_usedIds hi)

theorem good_binarySnd {op : Peano} (h : ar op = 2) (h0 : zero ≠ op) (h1 : succ ≠ op) :
    ∀ n, GoodBinary op (binarySnd op n) 0 n (n + 4)
  | 0 => good_binaryBase h
  | n + 1 => (good_binarySnd h h0 h1 n).push_snd h0 h1

/-- **The nets for `op m n` are in the situation**, for all `m` and `n`. -/
theorem good_binaryNet {op : Peano} (h : ar op = 2) (h0 : zero ≠ op) (h1 : succ ≠ op) :
    ∀ m n, GoodBinary op (binaryNet op m n) m n (m + n + 4)
  | 0, n => by
    rw [Nat.zero_add]
    exact good_binarySnd h h0 h1 n
  | m + 1, n => by
    have e : m + 1 + n + 4 = m + n + 4 + 1 := by omega
    rw [e]
    exact (good_binaryNet h h0 h1 m n).push_fst

/-- **An agent of two arguments that computes comes out right, whatever
the threads do.** -/
theorem binary_rest {op : Peano} {f c : Nat → Nat → Nat} (H : Computes2 op f c)
    (har : ar op = 2) (h0 : zero ≠ op) (h1 : succ ≠ op) (m n : Nat) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (binaryNet op m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (binaryNet op m n) nt).trace xsys σ i).2 = c m n ∧
      IsNum ((XMach.init (binaryNet op m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (f m n) := by
  have g := good_binaryNet har h0 h1 m n
  obtain ⟨N', hs, hn', hnum⟩ := binary_correct H g.config
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (binaryNet op m n) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (binaryNet op m n) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **An agent of two arguments that computes, under any fair
schedule.** -/
theorem binary_fair {op : Peano} {f c : Nat → Nat → Nat} (H : Computes2 op f c)
    (har : ar op = 2) (h0 : zero ≠ op) (h1 : succ ≠ op) (m n : Nat) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (binaryNet op m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (binaryNet op m n) nt).trace xsys σ i).2 = c m n ∧
      IsNum ((XMach.init (binaryNet op m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (f m n) := by
  have g := good_binaryNet har h0 h1 m n
  obtain ⟨N', hs, hn', hnum⟩ := binary_correct H g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- The nets for products are the nets of this module. -/
theorem prod_eq : ∀ m n, prod m n = binaryNet mul m n
  | 0, 0 => rfl
  | 0, n + 1 => by
    show (prodSnd n).pushOn succ ([1], 1) [n + 4] =
      (binarySnd mul n).pushOn succ ([1], 1) [n + 4]
    rw [show prodSnd n = binarySnd mul n from prod_eq 0 n]
  | m + 1, n => by
    show (prod m n).pushOn succ ([1], 0) [m + n + 4] =
      (binaryNet mul m n).pushOn succ ([1], 0) [m + n + 4]
    rw [prod_eq m n]

/-- The nets for powers are the nets of this module. -/
theorem power_eq : ∀ e b, power e b = binaryNet pow e b
  | 0, 0 => rfl
  | 0, b + 1 => by
    show (powerSnd b).pushOn succ ([1], 1) [b + 4] =
      (binarySnd pow b).pushOn succ ([1], 1) [b + 4]
    rw [show powerSnd b = binarySnd pow b from power_eq 0 b]
  | e + 1, b => by
    show (power e b).pushOn succ ([1], 0) [e + b + 4] =
      (binaryNet pow e b).pushOn succ ([1], 0) [e + b + 4]
    rw [power_eq e b]

/-- **Multiplication on the machine**, as a case, through the multiplier
derived from the theorem on recursion. -/
theorem prod_rest' (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (prod m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (prod m n) nt).trace xsys σ i).2 = prodCost m n ∧
      IsNum ((XMach.init (prod m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m * n) := by
  rw [prod_eq] at hr ⊢
  exact binary_rest mul_computes' rfl (by decide) (by decide) m n hnt σ hr

/-- **Powers on the machine**, as a case. -/
theorem power_rest' (e b : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (power e b) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (power e b) nt).trace xsys σ i).2 = powCost e b ∧
      IsNum ((XMach.init (power e b) nt).trace xsys σ i).1.mem.toNet ([0], 0) (b ^ e) := by
  rw [power_eq] at hr ⊢
  exact binary_rest pow_computes' rfl (by decide) (by decide) e b hnt σ hr

/-- **Multiplication under any fair schedule**, as a case. -/
theorem prod_fair' (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (prod m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (prod m n) nt).trace xsys σ i).2 = prodCost m n ∧
      IsNum ((XMach.init (prod m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m * n) := by
  rw [prod_eq]
  exact binary_fair mul_computes' rfl (by decide) (by decide) m n hnt σ hfair

/-- **Powers under any fair schedule**, as a case. -/
theorem power_fair' (e b : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (power e b) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (power e b) nt).trace xsys σ i).2 = powCost e b ∧
      IsNum ((XMach.init (power e b) nt).trace xsys σ i).1.mem.toNet ([0], 0) (b ^ e) := by
  rw [power_eq]
  exact binary_fair pow_computes' rfl (by decide) (by decide) e b hnt σ hfair

end Peano

end INet
