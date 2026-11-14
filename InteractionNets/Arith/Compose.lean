import InteractionNets.Arith.AnyNets
import InteractionNets.Plug

/-! # One addition after another

Two nets wired together: the result of an addition is the first argument
of a second adder.  The first net reduces inside the whole as it does
alone (`Net.Made.steps`, `Steps.plug`); its sum is then, across the new
segment, the first argument of the second adder, and the whole is a net
that addition is about (`Config`), so `add_correct` finishes
(`add_add`).
-/

namespace INet

namespace Arith

/-- **An adder waiting for its first argument.**  The only adder `d` of
the net has its first argument on the free port `q`, the numeral `k` as
its second argument, and its result on the free port `r`. -/
structure OpenAdd (N : Net Arith) (d : Id) (k : Nat) (q r : Port) : Prop where
  ha : N.agent d add
  only : ∀ i, N.agent i add → i = d
  inp : N.Paired ar (d, 0) q
  inq : N.free q
  snd : IsNum N (d, 1) k
  out : N.Paired ar (d, 2) r
  free : N.free r
  ne : r ≠ q

/-- Numerals are kept when free ports are wired together. -/
theorem Num.plug {U : Net Arith} {J : Port → Port → Prop} (hU : U.WF ar)
    (hfree : ∀ p q, J p q → U.free p) :
    ∀ {k : Nat} {i : Id}, Num U i k → Num (U.plug J) i k
  | 0, _, hz => hz
  | _ + 1, _, ⟨hs, i', hp, hn⟩ =>
    ⟨hs, i', hp.plug (hU.unplugged hfree hs 1)
      (hn.label.elim (fun h => hU.unplugged hfree h 0) (fun h => hU.unplugged hfree h 0)),
      Num.plug hU hfree hn⟩

/-- A numeral on a port of an agent is kept too. -/
theorem IsNum.plug_agent {U : Net Arith} {J : Port → Port → Prop} (hU : U.WF ar)
    (hfree : ∀ p q, J p q → U.free p) {i₀ : Id} {γ : Arith} (h0 : U.agent i₀ γ) {j k : Nat}
    (h : IsNum U (i₀, j) k) : IsNum (U.plug J) (i₀, j) k := by
  obtain ⟨i, hp, hn⟩ := h
  exact ⟨i, hp.plug (hU.unplugged hfree h0 j)
    (hn.label.elim (fun h => hU.unplugged hfree h 0) (fun h => hU.unplugged hfree h 0)),
    Num.plug hU hfree hn⟩

/-- **One addition after another.**  Let a well-formed net be made of
nets under tags: under `cA` a net that addition is about, with the
numerals `m` and `n` and its result on the free port `p`; under `cB` an
adder waiting for its first argument on the free port `q`, with the
numeral `k` as second argument and its result on the free port `r`; and
no adder elsewhere.  Wire `p` to `q`.  Then the net reduces, in `m + 1`
steps for the first addition and `m + n + 1` for the second, to a normal
form that has the numeral `m + n + k` on `r`. -/
theorem add_add {U : Net Arith} {P : Nat → Net Arith} (hU : U.WF ar) (hm : U.Made P)
    {cA cB : Nat} (hc : cA ≠ cB) {a d : Id} {m n k : Nat} {p q r : Port}
    (cfg : Config (P cA) a 0 m n p) (hB : OpenAdd (P cB) d k q r)
    (hO : ∀ c, c ≠ cA → c ≠ cB → ∀ i, ¬ (P c).agent i add) :
    ∃ N', Steps (Step system) (m + 1 + (m + n + 1))
        (U.plug (joinRel (tagPort cA p) (tagPort cB q))) N' ∧
      Normal (Step system) N' ∧ IsNum N' (tagPort cB r) (m + n + k) := by
  -- the first addition, inside the whole
  obtain ⟨A', sA, numA, noA⟩ := cfg.steps
  rw [Nat.zero_add] at numA
  obtain ⟨U₁, s₁, hm₁⟩ := hm.steps system_sided sA
  have hU₁ : U₁.WF ar := Steps.wf hU s₁
  have eA : setPart P cA A' cA = A' := setPart_same _ _ _
  have eB : setPart P cA A' cB = P cB := setPart_ne _ _ (Ne.symm hc)
  -- the ports that are wired together, and the port of the result
  have fp : U₁.free (tagPort cA p) := hm₁.free' (c := cA) (p := p) (by
    rw [eA, Steps.free sA]
    exact cfg.free)
  have fq : U₁.free (tagPort cB q) := hm₁.free' (c := cB) (p := q) (by
    rw [eB]
    exact hB.inq)
  have fr : U₁.free (tagPort cB r) := hm₁.free' (c := cB) (p := r) (by
    rw [eB]
    exact hB.free)
  have hpq : tagPort cA p ≠ tagPort cB q := fun e => hc (tagPort_snoc e).2
  have hr1 : tagPort cB r ≠ tagPort cA p := fun e => hc (tagPort_snoc e).2.symm
  have hr2 : tagPort cB r ≠ tagPort cB q := fun e => hB.ne (tagPort_inj e)
  have hfree : ∀ u v : Port, joinRel (tagPort cA p) (tagPort cB q) u v → U₁.free u := by
    rintro u v (⟨e, -⟩ | ⟨e, -⟩)
    · rw [e]
      exact fp
    · rw [e]
      exact fq
  have hW : (U₁.plug (joinRel (tagPort cA p) (tagPort cB q))).WF ar :=
    hU₁.plug_two fp fq hpq
  -- the adder that is left
  have hd : U₁.agent (d ++ [cB]) add := hm₁.agent' (c := cB) (by
    rw [eB]
    exact hB.ha)
  -- its first argument is the sum, across the new segment
  obtain ⟨i, pi, ni⟩ := made_isNum hm₁ (c := cA) (p := p) (k := m + n) (by
    rw [eA]
    exact numA)
  have pin : U₁.Paired ar (tagPort cB (d, 0)) (tagPort cB q) :=
    hm₁.paired ar (c := cB) (by
      rw [eB]
      exact hB.inp)
  have c1 : (U₁.plug (joinRel (tagPort cA p) (tagPort cB q))).Conn ar (d ++ [cB], 0) (i, 0) :=
    Net.Conn.plug hU₁ hfree (joinRel_right _ _) (joinRel_left _ _)
      (fun e => hc (tagPort_snoc (c := cB) (p := (d, 0)) e).2.symm) pin.2.2 pi.2.2
  have cfg₁ : Config (U₁.plug (joinRel (tagPort cA p) (tagPort cB q))) (d ++ [cB]) 0 (m + n) k
      (tagPort cB r) :=
    { wf := hW
      ha := hd
      only := by
        intro x hx
        obtain ⟨c, x', rfl, hx'⟩ := hm₁.agent hx
        by_cases h1 : c = cA
        · rw [h1, eA] at hx'
          exact absurd hx' (noA x')
        · by_cases h2 : c = cB
          · rw [h2, eB] at hx'
            rw [h2, hB.only x' hx']
          · rw [setPart_ne _ _ h1] at hx'
            exact absurd hx' (hO c h1 h2 x')
      fst := ⟨i, ⟨.inr ⟨add, hd, Nat.zero_le _⟩,
        ni.label.elim (fun h => .inr ⟨zero, h, Nat.zero_le _⟩)
          (fun h => .inr ⟨succ, h, Nat.zero_le _⟩), c1⟩, Num.plug hU₁ hfree ni⟩
      snd := IsNum.plug_agent hU₁ hfree (i₀ := d ++ [cB]) (j := 1) hd
        (made_isNum hm₁ (c := cB) (p := (d, 1)) (by
          rw [eB]
          exact hB.snd))
      out := ⟨tagPort cB r, (hm₁.paired ar (c := cB) (p := (d, 2)) (by
          rw [eB]
          exact hB.out)).plug (hU₁.unplugged hfree hd 2) (joinRel_ne hr1 hr2), rfl⟩
      free := ⟨fr, joinRel_ne hr1 hr2⟩ }
  -- the second addition
  obtain ⟨N', s₂, hn, hnum⟩ := add_correct cfg₁
  exact ⟨N', (s₁.plug _).trans s₂, hn, hnum⟩

end Arith

/-! ### In memory -/

/-- **A memory with two of its free ports wired together**: a new
segment, written in both directions, and the two ports off the list of
free ports. -/
def XNet.plug2 {S : Type} (X : XNet S) (x y : Port) : XNet S :=
  ⟨X.agents, X.free.filter (fun p => decide (p ≠ x ∧ p ≠ y)), (x, y) :: (y, x) :: X.wires⟩

theorem XNet.plug2_toNet {S : Type} (X : XNet S) (x y : Port) :
    (X.plug2 x y).toNet = X.toNet.plug (joinRel x y) := by
  apply Net.ext'
  · intro i γ
    exact Iff.rfl
  · intro p q
    show (p, q) ∈ (x, y) :: (y, x) :: X.wires ↔
      ((p, q) ∈ X.wires ∨ ((p = x ∧ q = y) ∨ (p = y ∧ q = x)))
    rw [List.mem_cons, List.mem_cons]
    constructor
    · rintro (e | e | h)
      · injection e with e1 e2
        exact .inr (.inl ⟨e1, e2⟩)
      · injection e with e1 e2
        exact .inr (.inr ⟨e1, e2⟩)
      · exact .inl h
    · rintro (h | ⟨e1, e2⟩ | ⟨e1, e2⟩)
      · exact .inr (.inr h)
      · exact .inl (by rw [e1, e2])
      · exact .inr (.inl (by rw [e1, e2]))
  · intro p
    show p ∈ X.free.filter (fun p => decide (p ≠ x ∧ p ≠ y)) ↔
      (p ∈ X.free ∧ ¬ ∃ r, (p = x ∧ r = y) ∨ (p = y ∧ r = x))
    rw [List.mem_filter, decide_eq_true_iff]
    constructor
    · rintro ⟨h, h1, h2⟩
      refine ⟨h, ?_⟩
      rintro ⟨r, ⟨e, -⟩ | ⟨e, -⟩⟩
      · exact h1 e
      · exact h2 e
    · rintro ⟨h, hn⟩
      exact ⟨h, fun e => hn ⟨y, .inl ⟨e, rfl⟩⟩, fun e => hn ⟨x, .inr ⟨e, rfl⟩⟩⟩

namespace Arith

/-! ### The nets for an adder that waits -/

/-- An adder waiting for its first argument on the free port `([2], 0)`,
with `0` as its second argument and its result on the free port
`([0], 0)`. -/
def openBase : XNet Arith :=
  XNet.ofWires [([1], add), ([3], zero)] [([0], 0), ([2], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

/-- The same with `k` as second argument. -/
def openSnd : Nat → XNet Arith
  | 0 => openBase
  | k + 1 => push (openSnd k) ([1], 1) [k + 4]

/-- What the construction keeps: the net is a valid input of the reducer,
its adder `[1]` waits on `([2], 0)` with the numeral `k` as second
argument and the result on `([0], 0)`, and its names are below `b`. -/
structure GoodOpen (X : XNet Arith) (k b : Nat) : Prop where
  ok : X.Ok ar
  op : OpenAdd X.toNet [1] k ([2], 0) ([0], 0)
  below : Below X b

theorem good_openBase : GoodOpen openBase 0 4 := by
  have hX : openBase.Ok ar := by decide
  refine ⟨hX, ⟨?_, ?_, hX.link_iff.1 (by decide), ?_, ?_, hX.link_iff.1 (by decide), ?_, ?_⟩, ?_⟩
  · show ([1], add) ∈ openBase.agents
    decide
  · intro i hi
    have hi' : (i, add) ∈ [(([1] : Id), add), ([3], zero)] := hi
    simpa using hi'
  · show ([2], 0) ∈ openBase.free
    decide
  · exact ⟨[3], hX.link_iff.1 (by decide), show ([3], zero) ∈ openBase.agents by decide⟩
  · show ([0], 0) ∈ openBase.free
    decide
  · decide
  · intro i hi
    have hall : ∀ i ∈ usedIds openBase, ∃ j, j < 4 ∧ i = [j] := by decide
    exact hall i (mem_usedIds hi)

/-- One more successor on the second argument. -/
theorem GoodOpen.push {X : XNet Arith} {k b : Nat} (g : GoodOpen X k b) :
    GoodOpen (push X ([1], 1) [b]) (k + 1) (b + 1) := by
  have o := g.op
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨t, hpt, hnt⟩ := o.snd
  have hsucc : ∀ i, X.toNet.agent i succ → i ≠ [1] := by
    rintro i hi rfl
    exact absurd (hX.1.agent_fun hi o.ha) (by decide)
  have ht1 : t ≠ [1] := by
    rintro rfl
    rcases hnt.label with hl | hl
    · exact absurd (hX.1.agent_fun hl o.ha) (by decide)
    · exact absurd (hX.1.agent_fun hl o.ha) (by decide)
  have hm' : (X.toNet.insert1 [b] succ ([1], 1) (t, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hpt) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Num X.toNet i k →
      Num (X.toNet.insert1 [b] succ ([1], 1) (t, 0)) i k :=
    Num.insert1 hm' hm (fun i hi e => hsucc i hi (congrArg Prod.fst e))
      (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, g.below.push hX hpt⟩
  · rw [push_eq hX hpt, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [push_eq hX hpt, XNet.insert1_toNet]
    refine ⟨.inl o.ha, ?_, ?_, o.inq, ?_, ?_, o.free, o.ne⟩
    · rintro i (hi | ⟨-, e⟩)
      · exact o.only i hi
      · cases e
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 o.inp, port_ne_snd (by decide),
        fun e => ht1 (congrArg Prod.fst e).symm⟩)
    · exact ⟨[b], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, t,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnt⟩
    · exact hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 o.out, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩)

theorem good_openSnd : ∀ k, GoodOpen (openSnd k) k (k + 4)
  | 0 => good_openBase
  | k + 1 => (good_openSnd k).push

/-! ### `(m + n) + k` -/

/-- The two nets of `(m + n) + k`: the net for `m + n` under the tag `0`,
and under the tag `1` an adder that waits, with `k` as its second
argument. -/
def sum3Parts (m n k : Nat) : List (Nat × XNet Arith) := [(0, sum m n), (1, openSnd k)]

/-- **The net for `(m + n) + k`**: the two nets side by side, and the
free port of the first sum wired to the port on which the second adder
waits.  The result is on the free port `([0, 1], 0)`. -/
def sum3 (m n k : Nat) : XNet Arith :=
  (besides (sum3Parts m n k)).plug2 ([0, 0], 0) ([2, 1], 0)

theorem sum3Parts_tags (m n k : Nat) : ((sum3Parts m n k).map Prod.fst).Nodup := by
  show ([0, 1] : List Nat).Nodup
  decide

theorem sum3Parts_ok (m n k : Nat) : ∀ e, e ∈ sum3Parts m n k → e.2.Ok ar := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact sum_ok m n
  · rcases List.mem_cons.1 he with rfl | he
    · exact (good_openSnd k).ok
    · exact absurd he List.not_mem_nil

theorem sum3Parts_fst (m n k : Nat) : partOf (sum3Parts m n k) 0 = (sum m n).toNet :=
  partOf_mem (sum3Parts_tags m n k) List.mem_cons_self

theorem sum3Parts_snd (m n k : Nat) : partOf (sum3Parts m n k) 1 = (openSnd k).toNet :=
  partOf_mem (sum3Parts_tags m n k) (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The net for `(m + n) + k` is well formed. -/
theorem sum3_wf (m n k : Nat) : (sum3 m n k).toNet.WF ar := by
  have hm := made_besides (sum3Parts_tags m n k)
  have fp : (besides (sum3Parts m n k)).toNet.free ([0, 0], 0) :=
    hm.free' (c := 0) (p := ([0], 0)) (by
      rw [sum3Parts_fst]
      exact (good_sum m n).config.free)
  have fq : (besides (sum3Parts m n k)).toNet.free ([2, 1], 0) :=
    hm.free' (c := 1) (p := ([2], 0)) (by
      rw [sum3Parts_snd]
      exact (good_openSnd k).op.inq)
  rw [sum3, XNet.plug2_toNet]
  exact (besides_wf (sum3Parts_tags m n k) (sum3Parts_ok m n k)).plug_two fp fq (by decide)

/-- **`(m + n) + k`, as a net.**  The net reduces, in `m + 1` steps for
the first addition and `m + n + 1` for the second, to a normal form that
has the numeral `m + n + k` on its free port. -/
theorem sum3_normal (m n k : Nat) : ∃ N' : Net Arith,
    Steps (Step system) (m + 1 + (m + n + 1)) (sum3 m n k).toNet N' ∧
      Normal (Step system) N' ∧ IsNum N' ([0, 1], 0) (m + n + k) := by
  have hnd := sum3Parts_tags m n k
  have cfg : Config (partOf (sum3Parts m n k) 0) [1] 0 m n ([0], 0) := by
    rw [sum3Parts_fst]
    exact (good_sum m n).config
  have hB : OpenAdd (partOf (sum3Parts m n k) 1) [1] k ([2], 0) ([0], 0) := by
    rw [sum3Parts_snd]
    exact (good_openSnd k).op
  have hO : ∀ c, c ≠ 0 → c ≠ 1 → ∀ i, ¬ (partOf (sum3Parts m n k) c).agent i add := by
    intro c h0 h1 i h
    have hc : ¬ c ∈ (sum3Parts m n k).map Prod.fst := by
      intro hc
      have hc' : c ∈ [0, 1] := hc
      rcases List.mem_cons.1 hc' with e | hc''
      · exact h0 e
      · rcases List.mem_cons.1 hc'' with e | hc'''
        · exact h1 e
        · exact absurd hc''' List.not_mem_nil
    rw [partOf_none hc] at h
    exact h
  obtain ⟨N', s, hn, hnum⟩ := add_add (besides_wf hnd (sum3Parts_ok m n k)) (made_besides hnd)
    (cA := 0) (cB := 1) (by decide) cfg hB hO
  refine ⟨N', ?_, hn, hnum⟩
  rw [sum3, XNet.plug2_toNet]
  exact s

/-- **`(m + n) + k` comes out right, whatever the threads do.**  With any
number of threads and any schedule, a run that ends at rest has made
`m + 1` claims for the first addition and `m + n + 1` for the second, and
the memory has the numeral `m + n + k` on the free port. -/
theorem sum3_rest (m n k : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sum3 m n k) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (sum3 m n k) nt).trace xsys σ i).2 = m + 1 + (m + n + 1) ∧
      IsNum ((XMach.init (sum3 m n k) nt).trace xsys σ i).1.mem.toNet ([0, 1], 0)
        (m + n + k) := by
  obtain ⟨N', hs, hn', hA⟩ := sum3_normal m n k
  have hX := sum3_wf m n k
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (sum3 m n k) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (sum3 m n k) nt).trace xsys σ i).1.mem.toNet := e
  rw [← e']
  exact ⟨ek.symm, hA⟩

/-- **`(m + n) + k` under a fair schedule.**  With any number of threads
and any unending schedule in which every thread keeps being scheduled,
from some action on every thread is at rest, the claims are those of the
two additions, and the memory has the numeral `m + n + k` on the free
port. -/
theorem sum3_fair (m n k : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (sum3 m n k) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (sum3 m n k) nt).trace xsys σ i).2 = m + 1 + (m + n + 1) ∧
      IsNum ((XMach.init (sum3 m n k) nt).trace xsys σ i).1.mem.toNet ([0, 1], 0)
        (m + n + k) := by
  obtain ⟨N', hs, hn', hA⟩ := sum3_normal m n k
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) (sum3_wf m n k) hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, hc, e⟩ := h i hi
  rw [e]
  exact ⟨hr, hc, hA⟩

/-- `(2 + 3) + 4`, with any number of threads and any schedule: a run
that ends at rest has made nine claims, and the memory has `9` on the
free port. -/
example {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sum3 2 3 4) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (sum3 2 3 4) nt).trace xsys σ i).2 = 9 ∧
      IsNum ((XMach.init (sum3 2 3 4) nt).trace xsys σ i).1.mem.toNet ([0, 1], 0) 9 :=
  sum3_rest 2 3 4 hnt σ hr

end Arith

end INet
