import InteractionNets.PeanoMul

/-! # The nets for `m * n`, and the machine on them

The nets `Peano.prod m n` are built from the net for `0 * 0` by putting
successors on the two arguments of the multiplier.  They are valid inputs
of the reducer and of the machine, for all `m` and `n`
(`Peano.prod_ok`), and each is a multiplication in the sense of
`Peano.Product` (`Peano.good_prod`).

With `Peano.mul_correct` and the theorems about the machine, this gives
the result for the machine: with any number of threads and any schedule,
a run on `prod m n` that is at rest has made exactly
`(m + 1) * (n + 2) + m * (n + 1)` interactions and has the numeral
`m * n` on the free port (`Peano.prod_rest`); and under a fair schedule
the run does come to rest (`Peano.prod_fair`).
-/

namespace INet

section Building

variable {S : Type}

/-- Put an agent with the symbol `γ` on the wire that leaves the port
`p`. -/
def XNet.pushOn (X : XNet S) (γ : S) (p : Port) (u : Id) : XNet S :=
  match assoc p X.wires with
  | some q => X.insert1 u γ p q
  | none => X

/-- The identifiers in use are the one-element lists of the numbers below
`b`. -/
def XNet.Below (X : XNet S) (b : Nat) : Prop :=
  ∀ i, X.toNet.Used i → ∃ j, j < b ∧ i = [j]

theorem XNet.Below.fresh {X : XNet S} {b : Nat} (hb : X.Below b) (l : List Nat) :
    ¬ X.toNet.Used (l ++ [b]) := by
  intro hu
  obtain ⟨j, hj, e⟩ := hb _ hu
  have := (Arith.append_singleton e).2
  omega

theorem XNet.Below.fresh' {X : XNet S} {b : Nat} (hb : X.Below b) (l : List Nat) (i : Id)
    (α : S) (hi : X.toNet.agent i α) : [b] ≠ l ++ i := by
  intro e
  obtain ⟨j, hj, rfl⟩ := hb i (.inl ⟨α, hi⟩)
  have := (Arith.append_singleton e.symm).2
  omega

theorem XNet.pushOn_eq {ar : S → Nat} {X : XNet S} (hX : X.Ok ar) {p q : Port}
    (h : X.toNet.Paired ar p q) (γ : S) (u : Id) : X.pushOn γ p u = X.insert1 u γ p q := by
  have e : assoc p X.wires = some q := hX.exact.assoc_eq hX.1.wiring (hX.link_iff.2 h)
  unfold XNet.pushOn
  rw [e]

theorem XNet.Below.pushOn {ar : S → Nat} {X : XNet S} {b : Nat} (hb : X.Below b)
    (hX : X.Ok ar) {p q : Port} (h : X.toNet.Paired ar p q) (γ : S) :
    (X.pushOn γ p [b]).Below (b + 1) := by
  intro i hi
  rw [XNet.pushOn_eq hX h, XNet.insert1_toNet] at hi
  rcases Net.used_insert1 (hX.link_iff.2 h) hX.1.symm hi with hu | rfl
  · obtain ⟨j, hj, e⟩ := hb i hu
    exact ⟨j, by omega, e⟩
  · exact ⟨b, by omega, rfl⟩

/-- The identifiers of a finite net. -/
def XNet.usedIds (X : XNet S) : List Id :=
  X.agents.map (·.1) ++ X.wires.map (·.1.1) ++ X.free.map (·.1)

theorem XNet.mem_usedIds {X : XNet S} {i : Id} (h : X.toNet.Used i) : i ∈ X.usedIds := by
  unfold XNet.usedIds
  rcases h with ⟨γ, hγ⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨(i, γ), hγ, rfl⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨((i, k), q), hl, rfl⟩))
  · exact List.mem_append_right _ (List.mem_map.2 ⟨(i, k), hf, rfl⟩)

/-- A numeral is still there after a successor is put on a wire that
leaves none of its auxiliary ports. -/
theorem Addition.Num.insert1 {ar : S → Nat} {zero succ : S} {N : Net S} {u : Id} {p q : Port}
    (hm' : (N.insert1 u succ p q).Matching ar) (hm : N.Matching ar)
    (hp : ∀ i, N.agent i succ → (i, 1) ≠ p) (hq : ∀ i : Id, (i, 1) ≠ q) :
    ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ N i k →
      Addition.Num ar zero succ (N.insert1 u succ p q) i k
  | 0, _, hz => .inl hz
  | _ + 1, i, ⟨hs, i', hp', hn⟩ =>
    ⟨.inl hs, i', hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hp', hp i hs, hq i⟩),
      Addition.Num.insert1 hm' hm hp hq hn⟩

end Building

namespace Peano

/-- The net for `0 * 0`, with the result on the free port `([0], 0)`. -/
def prodBase : XNet Peano :=
  XNet.ofWires [([1], mul), ([2], zero), ([3], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

/-- The net for `0 * n`. -/
def prodSnd : Nat → XNet Peano
  | 0 => prodBase
  | n + 1 => (prodSnd n).pushOn succ ([1], 1) [n + 4]

/-- The net for `m * n`, with the result on the free port `([0], 0)`: `m`
successors are put on the first argument of the multiplier of `0 * 0`,
and `n` on the second. -/
def prod : Nat → Nat → XNet Peano
  | 0, n => prodSnd n
  | m + 1, n => (prod m n).pushOn succ ([1], 0) [m + n + 4]

/-- The situation of multiplication, on a valid input whose identifiers
are numbered below `b`. -/
structure GoodProd (X : XNet Peano) (m n b : Nat) : Prop where
  ok : X.Ok ar
  config : Product X.toNet [1] m n ([0], 0)
  below : X.Below b

/-- One more successor on the first argument. -/
theorem GoodProd.push_fst {X : XNet Peano} {m n b : Nat} (g : GoodProd X m n b) :
    GoodProd (X.pushOn succ ([1], 0) [b]) (m + 1) n (b + 1) := by
  have c := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := c.fst
  obtain ⟨t, hpt, hnt⟩ := c.snd
  have hm' : (X.toNet.insert1 [b] succ ([1], 0) (h, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hph) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ X.toNet i k →
      Addition.Num ar zero succ (X.toNet.insert1 [b] succ ([1], 0) (h, 0)) i k :=
    Addition.Num.insert1 hm' hm (fun _ _ => port_ne_snd (by decide))
      (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, g.below.pushOn hX hph succ⟩
  · rw [XNet.pushOn_eq hX hph, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [XNet.pushOn_eq hX hph, XNet.insert1_toNet]
    refine ⟨hm'.wf, .inl c.ha, ?_, ?_, ?_, c.free, ?_⟩
    · exact ⟨[b], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, h,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnh⟩
    · exact ⟨t, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hpt, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩), hnum hnt⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 c.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)
    · rintro i γ (hi | ⟨-, e⟩)
      · exact c.only i γ hi
      · exact .inr (.inl e)

/-- One more successor on the second argument. -/
theorem GoodProd.push_snd {X : XNet Peano} {m n b : Nat} (g : GoodProd X m n b) :
    GoodProd (X.pushOn succ ([1], 1) [b]) m (n + 1) (b + 1) := by
  have c := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := c.fst
  obtain ⟨t, hpt, hnt⟩ := c.snd
  have hsucc : ∀ i, X.toNet.agent i succ → i ≠ [1] := by
    rintro i hi rfl
    exact absurd (c.wf.agent_fun hi c.ha) (by decide)
  have ht1 : t ≠ [1] := by
    rintro rfl
    rcases Addition.Num.label hnt with hl | hl
    · exact absurd (c.wf.agent_fun hl c.ha) (by decide)
    · exact absurd (c.wf.agent_fun hl c.ha) (by decide)
  have hm' : (X.toNet.insert1 [b] succ ([1], 1) (t, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hpt) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ X.toNet i k →
      Addition.Num ar zero succ (X.toNet.insert1 [b] succ ([1], 1) (t, 0)) i k :=
    Addition.Num.insert1 hm' hm (fun i hi e => hsucc i hi (congrArg Prod.fst e))
      (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, g.below.pushOn hX hpt succ⟩
  · rw [XNet.pushOn_eq hX hpt, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [XNet.pushOn_eq hX hpt, XNet.insert1_toNet]
    refine ⟨hm'.wf, .inl c.ha, ?_, ?_, ?_, c.free, ?_⟩
    · exact ⟨h, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hph, port_ne_snd (by decide),
        fun e => ht1 (congrArg Prod.fst e).symm⟩), hnum hnh⟩
    · exact ⟨[b], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, t,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnt⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 c.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)
    · rintro i γ (hi | ⟨-, e⟩)
      · exact c.only i γ hi
      · exact .inr (.inl e)

theorem good_prodBase : GoodProd prodBase 0 0 4 := by
  have hX : prodBase.Ok ar := by decide
  refine ⟨hX, ⟨hX.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show ([1], mul) ∈ prodBase.agents
    decide
  · exact ⟨[2], hX.link_iff.1 (by decide), show ([2], zero) ∈ prodBase.agents by decide⟩
  · exact ⟨[3], hX.link_iff.1 (by decide), show ([3], zero) ∈ prodBase.agents by decide⟩
  · exact hX.link_iff.1 (by decide)
  · show ([0], 0) ∈ prodBase.free
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), mul), ([2], zero), ([3], zero)] := hi
    rcases List.mem_cons.1 hi' with e | hi''
    · exact .inr (.inr (Prod.mk.inj e).1)
    · rcases List.mem_cons.1 hi'' with e | hi'''
      · exact .inl (Prod.mk.inj e).2
      · rcases List.mem_cons.1 hi''' with e | h4
        · exact .inl (Prod.mk.inj e).2
        · exact absurd h4 List.not_mem_nil
  · intro i hi
    have hall : ∀ i ∈ prodBase.usedIds, ∃ j, j < 4 ∧ i = [j] := by decide
    exact hall i (XNet.mem_usedIds hi)

theorem good_prodSnd : ∀ n, GoodProd (prodSnd n) 0 n (n + 4)
  | 0 => good_prodBase
  | n + 1 => (good_prodSnd n).push_snd

/-- **The nets for `m * n` are multiplications**, for all `m` and `n`. -/
theorem good_prod : ∀ m n, GoodProd (prod m n) m n (m + n + 4)
  | 0, n => by
    rw [Nat.zero_add]
    exact good_prodSnd n
  | m + 1, n => by
    have e : m + 1 + n + 4 = m + n + 4 + 1 := by omega
    rw [e]
    exact (good_prod m n).push_fst

/-- The nets for `m * n` are valid inputs of the reducer, for all `m` and
`n`. -/
theorem prod_ok (m n : Nat) : (prod m n).Ok ar := (good_prod m n).ok

/-- The number of interactions of `m * n`. -/
def prodCost (m n : Nat) : Nat := (m + 1) * (n + 2) + m * (n + 1)

/-- **Multiplication comes out right, whatever the threads do**: with any
number of threads and any schedule, a run of the machine on the net for
`m * n` that is at rest has made exactly `prodCost m n` interactions, and
its memory has the numeral `m * n` on the free port. -/
theorem prod_rest (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (prod m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (prod m n) nt).trace xsys σ i).2 = prodCost m n ∧
      IsNum ((XMach.init (prod m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m * n) := by
  have g := good_prod m n
  obtain ⟨N', hs, hn', hnum⟩ := mul_correct g.config
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (prod m n) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 r q hn
  obtain ⟨e, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (prod m n) nt).trace xsys σ i).1.mem.toNet := e
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **Multiplication under any fair schedule**: with any number of
threads, as long as every thread keeps being scheduled, the run comes to
rest after `prodCost m n` interactions with the numeral `m * n` in
memory. -/
theorem prod_fair (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (prod m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (prod m n) nt).trace xsys σ i).2 = prodCost m n ∧
      IsNum ((XMach.init (prod m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m * n) := by
  have g := good_prod m n
  obtain ⟨N', hs, hn', hnum⟩ := mul_correct g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- The count for `2 * 3` is the 23 steps that the reducer takes. -/
example : prodCost 2 3 = 23 := by decide

/-- The reducer on the net for `2 * 3` stops after 23 steps on a net whose
agents are six successors and a zero. -/
example : ((prod 2 3).normalize xsys 100).map (fun r => (r.2, r.1.agents.map (·.2))) =
    some (23, [zero, succ, succ, succ, succ, succ, succ]) := by
  decide +kernel

end Peano

end INet
