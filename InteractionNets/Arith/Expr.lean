import InteractionNets.Arith.Compose

/-! # Every expression of additions

An adder whose two arguments are computed by other nets.  The two nets
reduce inside the whole as they do alone; their results are then, across
two new segments, the arguments of the adder, and `Config.steps`
finishes (`add_evals`).  What the whole computes is again a result on a
free port, so this can be repeated: for every expression built from
numerals and additions there is a net (`Expr.net`), and with any number
of threads and any schedule that net comes out right (`Expr.rest`,
`Expr.fair`).

The first part is about any system: a net made of well-formed nets under
tags is well formed (`Net.Made.wf`), without asking the parts to be
compact.
-/

namespace INet

open Arith (tagPort tagPort_inj tagPort_snoc snoc_inj)

section Made

variable {S : Type} {U : Net S} {P : Nat → Net S}

/-- An end of the whole is an end of a part. -/
theorem Net.Made.end_part (h : U.Made P) (ar : S → Nat) {p : Port} (hp : U.End ar p) :
    ∃ c p', p = tagPort c p' ∧ (P c).End ar p' := by
  rcases hp with hf | ⟨γ, hγ, hk⟩
  · obtain ⟨c, p', e, hp'⟩ := h.free hf
    exact ⟨c, p', e, .inl hp'⟩
  · obtain ⟨c, i', e, hi⟩ := h.agent hγ
    exact ⟨c, (i', p.2), Prod.ext e rfl, .inr ⟨γ, hi, hk⟩⟩

/-- **A net made of well-formed nets under tags is well formed.** -/
theorem Net.Made.wf (h : U.Made P) {ar : S → Nat} (hP : ∀ c, (P c).WF ar) : U.WF ar where
  agent_fun := fun {i α β} h1 h2 => by
    obtain ⟨c, i', e, hi⟩ := h.agent h1
    rw [e] at h2
    exact (hP c).agent_fun hi (h.agent_iff.1 h2)
  symm := fun {p q} hl => by
    obtain ⟨c, p', q', rfl, rfl, hl'⟩ := h.link hl
    exact h.link' ((hP c).symm hl')
  irrefl := fun {p} hl => by
    obtain ⟨c, p', q', e1, e2, hl'⟩ := h.link hl
    have e : p' = q' := tagPort_inj (e1.symm.trans e2)
    rw [e] at hl'
    exact (hP c).irrefl hl'
  end_unique := fun {p q r} hp h1 h2 => by
    obtain ⟨c, p', q', rfl, rfl, hl1⟩ := h.link h1
    obtain ⟨r', rfl, hl2⟩ := h.link_from h2
    rw [(hP c).end_unique ((h.end_iff ar).1 hp) hl1 hl2]
  end_conn := fun {p} hp => by
    obtain ⟨c, p', rfl, hp'⟩ := h.end_part ar hp
    obtain ⟨q', hq', hne, v, x, w⟩ := (hP c).end_conn hp'
    exact ⟨tagPort c q', (h.end_iff ar).2 hq', fun e => hne (tagPort_inj e), tagPort c v,
      tagPort c x, h.walk ar w⟩
  deg := fun {p x y z} h1 h2 h3 => by
    obtain ⟨c, p', x', rfl, rfl, l1⟩ := h.link h1
    obtain ⟨y', rfl, l2⟩ := h.link_from h2
    obtain ⟨z', rfl, l3⟩ := h.link_from h3
    rcases (hP c).deg l1 l2 l3 with e | e | e
    · exact .inl (by rw [e])
    · exact .inr (.inl (by rw [e]))
    · exact .inr (.inr (by rw [e]))
  free_agent := fun {i k α} hf ha => by
    obtain ⟨c, p', e, hp'⟩ := h.free hf
    obtain ⟨c', i', rfl, hi⟩ := h.agent ha
    obtain ⟨p1, p2⟩ := p'
    have e' : ((i' ++ [c'], k) : Port) = (p1 ++ [c], p2) := e
    injection e' with e1 e2
    obtain ⟨e3, e4⟩ := snoc_inj e1
    rw [e3, e4] at hi
    exact (hP c).free_agent hp' hi
  fresh := fun {a α} l ha hu => by
    obtain ⟨c, a', rfl, ha'⟩ := h.agent ha
    refine (hP c).fresh l ha' ?_
    have ea : l ++ (a' ++ [c]) = (l ++ a') ++ [c] := (List.append_assoc _ _ _).symm
    rw [ea] at hu
    rcases hu with ⟨γ, hγ⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
    · exact .inl ⟨γ, h.agent_iff.1 hγ⟩
    · obtain ⟨q', -, hl'⟩ := h.link_from (c := c) (p := (l ++ a', k)) hl
      exact .inr (.inl ⟨k, q', hl'⟩)
    · exact .inr (.inr ⟨k, (h.free_iff (c := c) (p := (l ++ a', k))).1 hf⟩)

end Made

namespace Arith

/-- Ports under different tags are different. -/
theorem tag_ne {c c' : Nat} (h : c ≠ c') (p q : Port) : tagPort c p ≠ tagPort c' q :=
  fun e => h (tagPort_snoc e).2

/-- **A net that computes a number.**  `Evals N s v p`: the port `p` is
free, and the net reduces in `s` steps to a net without adders that has
the numeral `v` on `p`. -/
def Evals (N : Net Arith) (s v : Nat) (p : Port) : Prop :=
  N.free p ∧ ∃ N', Steps (Step system) s N N' ∧ IsNum N' p v ∧ ∀ i, ¬ N'.agent i add

/-- **An adder waiting for both arguments**: the only adder `d` of the
net has its arguments on the free ports `q₁` and `q₂` and its result on
the free port `r`. -/
structure Open2 (N : Net Arith) (d : Id) (q₁ q₂ r : Port) : Prop where
  ha : N.agent d add
  only : ∀ i, N.agent i add → i = d
  fst : N.Paired ar (d, 0) q₁
  snd : N.Paired ar (d, 1) q₂
  out : N.Paired ar (d, 2) r
  free₁ : N.free q₁
  free₂ : N.free q₂
  free : N.free r
  ne₁ : q₁ ≠ q₂
  ne₂ : r ≠ q₁
  ne₃ : r ≠ q₂

/-- **An adder on two nets that compute.**  Let a well-formed net be made
of nets under tags: under `cA` a net that computes `v₁` on its free port
`p₁`, under `cB` one that computes `v₂` on `p₂`, under `cD` an adder
waiting for both arguments on `q₁` and `q₂`, with its result on `r`; and
no adder elsewhere.  Wire `p₁` to `q₁` and `p₂` to `q₂`.  The net is well
formed, and it computes `v₁ + v₂` on `r`, in the steps of the two nets
and `v₁ + 1` more. -/
theorem add_evals {U : Net Arith} {P : Nat → Net Arith} (hU : U.WF ar) (hm : U.Made P)
    {cA cB cD : Nat} (hAB : cA ≠ cB) (hAD : cA ≠ cD) (hBD : cB ≠ cD)
    {d : Id} {s₁ v₁ s₂ v₂ : Nat} {p₁ p₂ q₁ q₂ r : Port}
    (eA : Evals (P cA) s₁ v₁ p₁) (eB : Evals (P cB) s₂ v₂ p₂) (hD : Open2 (P cD) d q₁ q₂ r)
    (hO : ∀ c, c ≠ cA → c ≠ cB → c ≠ cD → ∀ i, ¬ (P c).agent i add) :
    ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
        (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar ∧
      Evals ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
          (joinRel (tagPort cB p₂) (tagPort cD q₂)))
        (s₁ + s₂ + (v₁ + 1)) (v₁ + v₂) (tagPort cD r) := by
  obtain ⟨fA, A', sA, numA, noA⟩ := eA
  obtain ⟨fB, B', sB, numB, noB⟩ := eB
  -- the ports that are wired, all different
  have n1 : tagPort cA p₁ ≠ tagPort cD q₁ := tag_ne hAD _ _
  have n2 : tagPort cB p₂ ≠ tagPort cD q₂ := tag_ne hBD _ _
  have nBA : tagPort cB p₂ ≠ tagPort cA p₁ := tag_ne (Ne.symm hAB) _ _
  have nBD : tagPort cB p₂ ≠ tagPort cD q₁ := tag_ne hBD _ _
  have nDA : tagPort cD q₂ ≠ tagPort cA p₁ := tag_ne (Ne.symm hAD) _ _
  have nDD : tagPort cD q₂ ≠ tagPort cD q₁ := fun e => hD.ne₁ (tagPort_inj e).symm
  have nrA : tagPort cD r ≠ tagPort cA p₁ := tag_ne (Ne.symm hAD) _ _
  have nr1 : tagPort cD r ≠ tagPort cD q₁ := fun e => hD.ne₂ (tagPort_inj e)
  have nrB : tagPort cD r ≠ tagPort cB p₂ := tag_ne (Ne.symm hBD) _ _
  have nr2 : tagPort cD r ≠ tagPort cD q₂ := fun e => hD.ne₃ (tagPort_inj e)
  -- the whole is well formed
  have hV0 : (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).WF ar :=
    hU.plug_two (hm.free' fA) (hm.free' hD.free₁) n1
  have hW0 : ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
      (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar :=
    hV0.plug_two ⟨hm.free' fB, joinRel_ne nBA nBD⟩ ⟨hm.free' hD.free₂, joinRel_ne nDA nDD⟩ n2
  have fr0 : ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
      (joinRel (tagPort cB p₂) (tagPort cD q₂))).free (tagPort cD r) :=
    ⟨⟨hm.free' hD.free, joinRel_ne nrA nr1⟩, joinRel_ne nrB nr2⟩
  refine ⟨hW0, fr0, ?_⟩
  -- the two nets reduce inside the whole
  obtain ⟨U₁, s₁', hm₁⟩ := hm.steps system_sided sA
  have eB1 : setPart P cA A' cB = P cB := setPart_ne _ _ (Ne.symm hAB)
  have sB' : Steps (Step system) s₂ (setPart P cA A' cB) B' := by
    rw [eB1]
    exact sB
  obtain ⟨U₂, s₂', hm₂⟩ := hm₁.steps system_sided sB'
  have S12 : Steps (Step system) (s₁ + s₂) U U₂ := s₁'.trans s₂'
  have e2A : setPart (setPart P cA A') cB B' cA = A' := by
    rw [setPart_ne _ _ hAB, setPart_same]
  have e2B : setPart (setPart P cA A') cB B' cB = B' := setPart_same _ _ _
  have e2D : setPart (setPart P cA A') cB B' cD = P cD := by
    rw [setPart_ne _ _ (Ne.symm hBD), setPart_ne _ _ (Ne.symm hAD)]
  have hU₂ : U₂.WF ar := Steps.wf hU S12
  have hW₁ : (U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).WF ar :=
    Steps.wf hV0 (S12.plug _)
  have hW₂ : ((U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
      (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar :=
    Steps.wf hW0 ((S12.plug _).plug _)
  -- free ports after the two reductions
  have fp₁ : U₂.free (tagPort cA p₁) := hm₂.free' (c := cA) (p := p₁) (by
    rw [e2A, Steps.free sA]
    exact fA)
  have fq₁ : U₂.free (tagPort cD q₁) := hm₂.free' (c := cD) (p := q₁) (by
    rw [e2D]
    exact hD.free₁)
  have fp₂ : U₂.free (tagPort cB p₂) := hm₂.free' (c := cB) (p := p₂) (by
    rw [e2B, Steps.free sB]
    exact fB)
  have fq₂ : U₂.free (tagPort cD q₂) := hm₂.free' (c := cD) (p := q₂) (by
    rw [e2D]
    exact hD.free₂)
  have fr : U₂.free (tagPort cD r) := hm₂.free' (c := cD) (p := r) (by
    rw [e2D]
    exact hD.free)
  have hfree₁ : ∀ u v : Port, joinRel (tagPort cA p₁) (tagPort cD q₁) u v → U₂.free u := by
    rintro u v (⟨e, -⟩ | ⟨e, -⟩)
    · rw [e]
      exact fp₁
    · rw [e]
      exact fq₁
  have hfree₂ : ∀ u v : Port, joinRel (tagPort cB p₂) (tagPort cD q₂) u v →
      (U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).free u := by
    rintro u v (⟨e, -⟩ | ⟨e, -⟩)
    · rw [e]
      exact ⟨fp₂, joinRel_ne nBA nBD⟩
    · rw [e]
      exact ⟨fq₂, joinRel_ne nDA nDD⟩
  -- the adder
  have hd : U₂.agent (d ++ [cD]) add := hm₂.agent' (c := cD) (by
    rw [e2D]
    exact hD.ha)
  -- its first argument, across the first segment
  obtain ⟨i₁, pi₁, ni₁⟩ := made_isNum hm₂ (c := cA) (p := p₁) (k := v₁) (by
    rw [e2A]
    exact numA)
  have pin₁ : U₂.Paired ar (tagPort cD (d, 0)) (tagPort cD q₁) :=
    hm₂.paired ar (c := cD) (by
      rw [e2D]
      exact hD.fst)
  have hi₁ : ∀ k, ¬ ∃ x, joinRel (tagPort cA p₁) (tagPort cD q₁) (i₁, k) x := fun k =>
    ni₁.label.elim (fun h => hU₂.unplugged hfree₁ h k) (fun h => hU₂.unplugged hfree₁ h k)
  have hi₁' : ∀ k, ¬ ∃ x, joinRel (tagPort cB p₂) (tagPort cD q₂) (i₁, k) x := fun k =>
    ni₁.label.elim (fun h => hW₁.unplugged hfree₂ h k) (fun h => hW₁.unplugged hfree₂ h k)
  have c1 : (U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).Conn ar (d ++ [cD], 0) (i₁, 0) :=
    Net.Conn.plug hU₂ hfree₁ (joinRel_right _ _) (joinRel_left _ _)
      (tag_ne (Ne.symm hAD) (d, 0) p₁) pin₁.2.2 pi₁.2.2
  have P1 : (U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).Paired ar (d ++ [cD], 0)
      (i₁, 0) :=
    ⟨.inr ⟨add, hd, Nat.zero_le _⟩,
      ni₁.label.elim (fun h => .inr ⟨zero, h, Nat.zero_le _⟩)
        (fun h => .inr ⟨succ, h, Nat.zero_le _⟩), c1⟩
  -- its second argument, across the second segment
  obtain ⟨i₂, pi₂, ni₂⟩ := made_isNum hm₂ (c := cB) (p := p₂) (k := v₂) (by
    rw [e2B]
    exact numB)
  have pin₂ : U₂.Paired ar (tagPort cD (d, 1)) (tagPort cD q₂) :=
    hm₂.paired ar (c := cD) (by
      rw [e2D]
      exact hD.snd)
  have hi₂ : ∀ k, ¬ ∃ x, joinRel (tagPort cA p₁) (tagPort cD q₁) (i₂, k) x := fun k =>
    ni₂.label.elim (fun h => hU₂.unplugged hfree₁ h k) (fun h => hU₂.unplugged hfree₁ h k)
  have pin₂' := pin₂.plug (J := joinRel (tagPort cA p₁) (tagPort cD q₁))
    (hU₂.unplugged hfree₁ hd 1) (joinRel_ne nDA nDD)
  have pi₂' := pi₂.plug (J := joinRel (tagPort cA p₁) (tagPort cD q₁))
    (joinRel_ne nBA nBD) (hi₂ 0)
  have c2 : ((U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
      (joinRel (tagPort cB p₂) (tagPort cD q₂))).Conn ar (d ++ [cD], 1) (i₂, 0) :=
    Net.Conn.plug hW₁ hfree₂ (joinRel_right _ _) (joinRel_left _ _)
      (tag_ne (Ne.symm hBD) (d, 1) p₂) pin₂'.2.2 pi₂'.2.2
  -- the result
  have pout : U₂.Paired ar (tagPort cD (d, 2)) (tagPort cD r) :=
    hm₂.paired ar (c := cD) (by
      rw [e2D]
      exact hD.out)
  have cfg : Config ((U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
      (joinRel (tagPort cB p₂) (tagPort cD q₂))) (d ++ [cD]) 0 v₁ v₂ (tagPort cD r) :=
    { wf := hW₂
      ha := hd
      only := by
        intro x hx
        obtain ⟨c, x', rfl, hx'⟩ := hm₂.agent hx
        by_cases h1 : c = cA
        · rw [h1, e2A] at hx'
          exact absurd hx' (noA x')
        · by_cases h2 : c = cB
          · rw [h2, e2B] at hx'
            exact absurd hx' (noB x')
          · by_cases h3 : c = cD
            · rw [h3, e2D] at hx'
              rw [h3, hD.only x' hx']
            · rw [setPart_ne _ _ h2, setPart_ne _ _ h1] at hx'
              exact absurd hx' (hO c h1 h2 h3 x')
      fst := ⟨i₁, P1.plug (hW₁.unplugged hfree₂ hd 0) (hi₁' 0),
        Num.plug hW₁ hfree₂ (Num.plug hU₂ hfree₁ ni₁)⟩
      snd := ⟨i₂, ⟨.inr ⟨add, hd, Nat.le_succ 1⟩,
          ni₂.label.elim (fun h => .inr ⟨zero, h, Nat.zero_le _⟩)
            (fun h => .inr ⟨succ, h, Nat.zero_le _⟩), c2⟩,
        Num.plug hW₁ hfree₂ (Num.plug hU₂ hfree₁ ni₂)⟩
      out := ⟨tagPort cD r,
        (pout.plug (J := joinRel (tagPort cA p₁) (tagPort cD q₁)) (hU₂.unplugged hfree₁ hd 2)
          (joinRel_ne nrA nr1)).plug (hW₁.unplugged hfree₂ hd 2) (joinRel_ne nrB nr2), rfl⟩
      free := ⟨⟨fr, joinRel_ne nrA nr1⟩, joinRel_ne nrB nr2⟩ }
  -- the addition
  obtain ⟨N', s₃, hnum, hno⟩ := cfg.steps
  rw [Nat.zero_add] at hnum
  exact ⟨N', ((S12.plug _).plug _).trans s₃, hnum, hno⟩

/-! ### The nets -/

/-- The numeral `0` on the free port `([0], 0)`. -/
def litBase : XNet Arith :=
  XNet.ofWires [([1], zero)] [([0], 0)] [(([0], 0), ([1], 0))]

/-- **The numeral `n` on the free port `([0], 0)`.** -/
def lit : Nat → XNet Arith
  | 0 => litBase
  | n + 1 => push (lit n) ([0], 0) [n + 2]

/-- What the construction keeps: the net is a valid input of the reducer,
it has the numeral `n` on its free port and no adder, and its names are
below `b`. -/
structure GoodLit (X : XNet Arith) (n b : Nat) : Prop where
  ok : X.Ok ar
  num : IsNum X.toNet ([0], 0) n
  free : X.toNet.free ([0], 0)
  none : ∀ i, ¬ X.toNet.agent i add
  below : Below X b

theorem good_litBase : GoodLit litBase 0 2 := by
  have hX : litBase.Ok ar := by decide
  refine ⟨hX, ⟨[1], hX.link_iff.1 (by decide), show ([1], zero) ∈ litBase.agents by decide⟩,
    ?_, ?_, ?_⟩
  · show ([0], 0) ∈ litBase.free
    decide
  · intro i hi
    have hi' : (i, add) ∈ [(([1] : Id), zero)] := hi
    simp at hi'
  · intro i hi
    have hall : ∀ i ∈ usedIds litBase, ∃ j, j < 2 ∧ i = [j] := by decide
    exact hall i (mem_usedIds hi)

/-- One more successor on the free port. -/
theorem GoodLit.push {X : XNet Arith} {n b : Nat} (g : GoodLit X n b) :
    GoodLit (push X ([0], 0) [b]) (n + 1) (b + 1) := by
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨t, hpt, hnt⟩ := g.num
  have hm' : (X.toNet.insert1 [b] succ ([0], 0) (t, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hpt) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Num X.toNet i k →
      Num (X.toNet.insert1 [b] succ ([0], 0) (t, 0)) i k :=
    Num.insert1 hm' hm (fun _ _ => port_ne_snd (by decide)) (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, ?_, ?_, g.below.push hX hpt⟩
  · rw [push_eq hX hpt, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [push_eq hX hpt, XNet.insert1_toNet]
    exact ⟨[b], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, t,
      hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnt⟩
  · rw [push_eq hX hpt, XNet.insert1_toNet]
    exact g.free
  · rw [push_eq hX hpt, XNet.insert1_toNet]
    rintro i (hi | ⟨-, e⟩)
    · exact g.none i hi
    · cases e

theorem good_lit : ∀ n, GoodLit (lit n) n (n + 2)
  | 0 => good_litBase
  | n + 1 => (good_lit n).push

/-- **An adder waiting for both arguments**, on the free ports `([2], 0)`
and `([3], 0)`, with its result on the free port `([0], 0)`. -/
def open2 : XNet Arith :=
  XNet.ofWires [([1], add)] [([0], 0), ([2], 0), ([3], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

theorem open2_ok : open2.Ok ar := by decide

theorem open2_spec : Open2 open2.toNet [1] ([2], 0) ([3], 0) ([0], 0) := by
  have hX := open2_ok
  refine ⟨?_, ?_, hX.link_iff.1 (by decide), hX.link_iff.1 (by decide),
    hX.link_iff.1 (by decide), ?_, ?_, ?_, by decide, by decide, by decide⟩
  · show ([1], add) ∈ open2.agents
    decide
  · intro i hi
    have hi' : (i, add) ∈ [(([1] : Id), add)] := hi
    simpa using hi'
  · show ([2], 0) ∈ open2.free
    decide
  · show ([3], 0) ∈ open2.free
    decide
  · show ([0], 0) ∈ open2.free
    decide

theorem partOf_wf : ∀ {L : List (Nat × XNet Arith)}, (∀ e, e ∈ L → e.2.toNet.WF ar) →
    ∀ c, (partOf L c).WF ar
  | [], _, _ => noNet_matching.wf
  | e :: L, h, c => by
    show (if c = e.1 then e.2.toNet else partOf L c).WF ar
    by_cases hc : c = e.1
    · rw [ite_pos' hc]
      exact h e List.mem_cons_self
    · rw [ite_neg' hc]
      exact partOf_wf (fun e' he' => h e' (List.mem_cons_of_mem _ he')) c

/-! ### Expressions -/

/-- **Expressions**: numerals and additions. -/
inductive Expr
  | lit (n : Nat)
  | add (e₁ e₂ : Expr)

/-- The value of an expression. -/
def Expr.eval : Expr → Nat
  | .lit n => n
  | .add e₁ e₂ => e₁.eval + e₂.eval

/-- The interactions of an expression: for each addition, one more than
the value of its first argument. -/
def Expr.cost : Expr → Nat
  | .lit _ => 0
  | .add e₁ e₂ => e₁.cost + e₂.cost + (e₁.eval + 1)

/-- The free port that carries the result. -/
def Expr.res : Expr → Port
  | .lit _ => ([0], 0)
  | .add _ _ => ([0, 2], 0)

/-- **The net of an expression.**  A numeral is its net.  An addition is
the nets of its two arguments and an adder that waits, side by side under
the tags `0`, `1` and `2`, with the result of each argument wired to a
port of the adder. -/
def Expr.net : Expr → XNet Arith
  | .lit n => Arith.lit n
  | .add e₁ e₂ =>
    ((besides [(0, e₁.net), (1, e₂.net), (2, open2)]).plug2 (tagPort 0 e₁.res)
      ([2, 2], 0)).plug2 (tagPort 1 e₂.res) ([3, 2], 0)

theorem Expr.net_add (e₁ e₂ : Expr) :
    (Expr.add e₁ e₂).net.toNet =
      (((besides [(0, e₁.net), (1, e₂.net), (2, open2)]).toNet.plug
        (joinRel (tagPort 0 e₁.res) (tagPort 2 ([2], 0)))).plug
        (joinRel (tagPort 1 e₂.res) (tagPort 2 ([3], 0)))) := by
  show (XNet.plug2 (XNet.plug2 _ _ _) _ _).toNet = _
  rw [XNet.plug2_toNet, XNet.plug2_toNet]
  rfl

/-- **The net of an expression is well formed and computes its value**,
in the interactions counted by `Expr.cost`. -/
theorem Expr.good : ∀ e : Expr, e.net.toNet.WF ar ∧ Evals e.net.toNet e.cost e.eval e.res
  | .lit n =>
    ⟨(good_lit n).ok.1, (good_lit n).free, (Arith.lit n).toNet, .refl _, (good_lit n).num,
      (good_lit n).none⟩
  | .add e₁ e₂ => by
    obtain ⟨w₁, ev₁⟩ := Expr.good e₁
    obtain ⟨w₂, ev₂⟩ := Expr.good e₂
    have hnd : (([(0, e₁.net), (1, e₂.net), (2, open2)] : List (Nat × XNet Arith)).map
        Prod.fst).Nodup := by
      show ([0, 1, 2] : List Nat).Nodup
      decide
    have hm := made_besides hnd
    have hP : ∀ c, (partOf [(0, e₁.net), (1, e₂.net), (2, open2)] c).WF ar := by
      refine partOf_wf fun e he => ?_
      rcases List.mem_cons.1 he with rfl | he
      · exact w₁
      · rcases List.mem_cons.1 he with rfl | he
        · exact w₂
        · rcases List.mem_cons.1 he with rfl | he
          · exact open2_ok.1
          · exact absurd he List.not_mem_nil
    have e0 : partOf [(0, e₁.net), (1, e₂.net), (2, open2)] 0 = e₁.net.toNet :=
      partOf_mem hnd List.mem_cons_self
    have e1 : partOf [(0, e₁.net), (1, e₂.net), (2, open2)] 1 = e₂.net.toNet :=
      partOf_mem hnd (List.mem_cons_of_mem _ List.mem_cons_self)
    have e2 : partOf [(0, e₁.net), (1, e₂.net), (2, open2)] 2 = open2.toNet :=
      partOf_mem hnd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have hO : ∀ c, c ≠ 0 → c ≠ 1 → c ≠ 2 → ∀ i,
        ¬ (partOf [(0, e₁.net), (1, e₂.net), (2, open2)] c).agent i Arith.add := by
      intro c h0 h1 h2 i h
      have hc : ¬ c ∈ ([(0, e₁.net), (1, e₂.net), (2, open2)] : List (Nat × XNet Arith)).map
          Prod.fst := by
        intro hc
        have hc' : c ∈ [0, 1, 2] := hc
        rcases List.mem_cons.1 hc' with e | hc'
        · exact h0 e
        · rcases List.mem_cons.1 hc' with e | hc'
          · exact h1 e
          · rcases List.mem_cons.1 hc' with e | hc'
            · exact h2 e
            · exact absurd hc' List.not_mem_nil
      rw [partOf_none hc] at h
      exact h
    rw [Expr.net_add]
    exact add_evals (hm.wf hP) hm (cA := 0) (cB := 1) (cD := 2) (by decide) (by decide)
      (by decide) (by rw [e0]; exact ev₁) (by rw [e1]; exact ev₂) (by rw [e2]; exact open2_spec)
      hO

/-- **Every expression comes out right, whatever the threads do.**  With
any number of threads and any schedule, a run on the net of an expression
that ends at rest has made the interactions counted by `Expr.cost`, and
the memory has the numeral of the value on the free port. -/
theorem Expr.rest (e : Expr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  have hn' := normal_of_no_add hno
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init e.net nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e', ek⟩ := (hu hs).2 hn'
  have e'' : N' = ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet := e'
  rw [← e'']
  exact ⟨ek.symm, hA⟩

/-- **Every expression under a fair schedule.**  With any number of
threads and any unending schedule in which every thread keeps being
scheduled, from some action on every thread is at rest, the claims are
the interactions of the expression, and the memory has the numeral of its
value on the free port. -/
theorem Expr.fair (e : Expr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) hX hnt hs (normal_of_no_add hno) σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, hc, e'⟩ := h i hi
  rw [e']
  exact ⟨hr, hc, hA⟩

/-- `(2 + 3) + (1 + 4)`, with any number of threads and any schedule: a
run that ends at rest has made eleven claims, and the memory has `10` on
the free port. -/
example {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).net
      nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).net
        nt).trace xsys σ i).2 = 11 ∧
      IsNum ((XMach.init (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).net
        nt).trace xsys σ i).1.mem.toNet ([0, 2], 0) 10 :=
  Expr.rest (.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))) hnt σ hr

end Arith

end INet
