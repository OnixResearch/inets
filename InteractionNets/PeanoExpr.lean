import InteractionNets.PeanoProd
import InteractionNets.Union
import InteractionNets.ReadBack

/-! # Every expression of additions and multiplications

Expressions built from numerals with `+` and `*` (`Peano.PExpr`).  Each
has a net (`PExpr.net`): the nets of the two arguments and an adder or a
multiplier that waits for them, side by side under tags, with the result
of each argument wired to a port of the operator.

The two argument nets reduce inside the whole as they do alone
(`Net.Made.steps`, the rules of `Peano` giving every new agent a side,
`Peano.system_sided`).  Their results are then, across the two new
segments, the arguments of the operator (`Peano.op_setup`), and the
theorem for the operator finishes: `Peano.add_steps'` for the adder,
`Peano.mul_steps` for the multiplier.  What the whole computes is again a
numeral on a free port, in a net of successors and zeros, so this
repeats (`PExpr.good`).

On the machine: with any number of threads and any schedule, a run on the
net of an expression that is at rest has made exactly `PExpr.cost`
interactions and holds the numeral of the value (`PExpr.rest`); under a
fair schedule the run comes to rest (`PExpr.fair`).

An expression can be run (`PExpr.run`): threads take turns on its net for
a number of actions and the numeral on the free port is read.  Whatever
is returned is the value of the expression (`PExpr.run_sound`), and with
enough actions the value is returned (`PExpr.run_complete`).
-/

namespace INet

open Arith (tagPort tagPort_inj tagPort_snoc snoc_inj tag_ne)

section Three

variable {S : Type}

/-- Three nets as the parts under the tags `0`, `1` and `2`. -/
def parts3 (A B D : Net S) : Nat → Net S
  | 0 => A
  | 1 => B
  | 2 => D
  | _ + 3 => Net.empty

theorem parts3_rest (A B D : Net S) (c : Nat) : parts3 A B D (c + 3) = Net.empty := rfl

/-- Three memories side by side, under the tags `0`, `1` and `2`. -/
def XNet.three (X₀ X₁ X₂ : XNet S) : XNet S :=
  (X₀.tag 0).union ((X₁.tag 1).union (X₂.tag 2))

theorem XNet.three_toNet (X₀ X₁ X₂ : XNet S) :
    (XNet.three X₀ X₁ X₂).toNet =
      (X₀.toNet.map (fun i => i ++ [0])).union
        ((X₁.toNet.map (fun i => i ++ [1])).union (X₂.toNet.map (fun i => i ++ [2]))) := by
  unfold XNet.three
  rw [XNet.union_toNet, XNet.union_toNet, XNet.tag_toNet, XNet.tag_toNet, XNet.tag_toNet]

/-- **Three memories side by side are made of the three nets.** -/
theorem XNet.three_made (X₀ X₁ X₂ : XNet S) :
    (XNet.three X₀ X₁ X₂).toNet.Made (parts3 X₀.toNet X₁.toNet X₂.toNet) := by
  rw [XNet.three_toNet]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i γ (⟨i', rfl, h⟩ | ⟨i', rfl, h⟩ | ⟨i', rfl, h⟩)
    · exact ⟨0, i', rfl, h⟩
    · exact ⟨1, i', rfl, h⟩
    · exact ⟨2, i', rfl, h⟩
  · rintro p q (⟨p', q', rfl, rfl, h⟩ | ⟨p', q', rfl, rfl, h⟩ | ⟨p', q', rfl, rfl, h⟩)
    · exact ⟨0, p', q', rfl, rfl, h⟩
    · exact ⟨1, p', q', rfl, rfl, h⟩
    · exact ⟨2, p', q', rfl, rfl, h⟩
  · rintro p (⟨p', rfl, h⟩ | ⟨p', rfl, h⟩ | ⟨p', rfl, h⟩)
    · exact ⟨0, p', rfl, h⟩
    · exact ⟨1, p', rfl, h⟩
    · exact ⟨2, p', rfl, h⟩
  · intro c i γ h
    match c, h with
    | 0, h => exact .inl ⟨i, rfl, h⟩
    | 1, h => exact .inr (.inl ⟨i, rfl, h⟩)
    | 2, h => exact .inr (.inr ⟨i, rfl, h⟩)
    | c + 3, h =>
      rw [parts3_rest] at h
      exact False.elim h
  · intro c p q h
    match c, h with
    | 0, h => exact .inl ⟨p, q, rfl, rfl, h⟩
    | 1, h => exact .inr (.inl ⟨p, q, rfl, rfl, h⟩)
    | 2, h => exact .inr (.inr ⟨p, q, rfl, rfl, h⟩)
    | c + 3, h =>
      rw [parts3_rest] at h
      exact False.elim h
  · intro c p h
    match c, h with
    | 0, h => exact .inl ⟨p, rfl, h⟩
    | 1, h => exact .inr (.inl ⟨p, rfl, h⟩)
    | 2, h => exact .inr (.inr ⟨p, rfl, h⟩)
    | c + 3, h =>
      rw [parts3_rest] at h
      exact False.elim h

theorem parts3_wf {ar : S → Nat} {A B D : Net S} (hA : A.WF ar) (hB : B.WF ar) (hD : D.WF ar) :
    ∀ c, (parts3 A B D c).WF ar
  | 0 => hA
  | 1 => hB
  | 2 => hD
  | _ + 3 => Net.empty_wf ar

/-- A numeral of a part is a numeral of the whole, under the tag. -/
theorem Addition.Num.made {ar : S → Nat} {zero succ : S} {U : Net S} {P : Nat → Net S}
    (h : U.Made P) {c : Nat} : ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ (P c) i k →
      Addition.Num ar zero succ U (i ++ [c]) k
  | 0, _, hz => h.agent' hz
  | _ + 1, _, ⟨hs, i', hp, hn⟩ =>
    ⟨h.agent' hs, i' ++ [c], h.paired ar hp, Addition.Num.made h hn⟩

theorem Addition.IsNum.made {ar : S → Nat} {zero succ : S} {U : Net S} {P : Nat → Net S}
    (h : U.Made P) {c : Nat} {p : Port} {k : Nat} (hn : Addition.IsNum ar zero succ (P c) p k) :
    Addition.IsNum ar zero succ U (tagPort c p) k := by
  obtain ⟨i, hp, hk⟩ := hn
  exact ⟨i ++ [c], h.paired ar hp, Addition.Num.made h hk⟩

/-- Numerals are kept when free ports are wired together. -/
theorem Addition.Num.plug {ar : S → Nat} {zero succ : S} {U : Net S}
    {J : Port → Port → Prop} (hU : U.WF ar) (hfree : ∀ p q, J p q → U.free p) :
    ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ U i k →
      Addition.Num ar zero succ (U.plug J) i k
  | 0, _, hz => hz
  | _ + 1, _, ⟨hs, i', hp, hn⟩ =>
    ⟨hs, i', hp.plug (hU.unplugged hfree hs 1)
      (hn.label.elim (fun h => hU.unplugged hfree h 0) (fun h => hU.unplugged hfree h 0)),
      Addition.Num.plug hU hfree hn⟩

end Three

namespace Peano

/-- **The rules of `Peano` give every new agent a side.** -/
theorem system_sided : system.Sided := by
  intro α β R hR j
  cases α <;> cases β <;> cases hR <;> rfl

/-- **A net that computes a number.**  `Evals N s v p`: the port `p` is
free, and the net reduces in `s` steps to a net of successors and zeros
that has the numeral `v` on `p`. -/
def Evals (N : Net Peano) (s v : Nat) (p : Port) : Prop :=
  N.free p ∧ ∃ N', Steps (Step system) s N N' ∧ IsNum N' p v ∧
    ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ

/-- **An operator waiting for both arguments**: the only agent `d` of the
net, with the symbol `op`, has its arguments on the free ports `q₁` and
`q₂` and its result on the free port `r`. -/
structure OpenOp (N : Net Peano) (op : Peano) (d : Id) (q₁ q₂ r : Port) : Prop where
  ha : N.agent d op
  only : ∀ i γ, N.agent i γ → i = d
  fst : N.Paired ar (d, 0) q₁
  snd : N.Paired ar (d, 1) q₂
  out : N.Paired ar (d, 2) r
  free₁ : N.free q₁
  free₂ : N.free q₂
  free : N.free r
  ne₁ : q₁ ≠ q₂
  ne₂ : r ≠ q₁
  ne₃ : r ≠ q₂

/-- **An operator on two nets that compute.**  Let a well-formed net be
made of nets under tags: under `cA` a net that computes `v₁` on its free
port `p₁`, under `cB` one that computes `v₂` on `p₂`, under `cD` an
operator waiting for both arguments on `q₁` and `q₂`, with its result on
`r`; and no agent elsewhere.  Wire `p₁` to `q₁` and `p₂` to `q₂`.  The
net is well formed, and in the steps of the two nets it becomes a net in
which the operator has the numerals `v₁` and `v₂` as arguments and the
free port `r` as result, with no other agents than successors and
zeros. -/
theorem op_setup {U : Net Peano} {P : Nat → Net Peano} (hU : U.WF ar) (hm : U.Made P)
    {cA cB cD : Nat} (hAB : cA ≠ cB) (hAD : cA ≠ cD) (hBD : cB ≠ cD)
    {op : Peano} {d : Id} {s₁ v₁ s₂ v₂ : Nat} {p₁ p₂ q₁ q₂ r : Port}
    (eA : Evals (P cA) s₁ v₁ p₁) (eB : Evals (P cB) s₂ v₂ p₂)
    (hD : OpenOp (P cD) op d q₁ q₂ r)
    (hO : ∀ c, c ≠ cA → c ≠ cB → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
        (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar ∧
      ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
        (joinRel (tagPort cB p₂) (tagPort cD q₂))).free (tagPort cD r) ∧
      ∃ W, Steps (Step system) (s₁ + s₂)
          ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
            (joinRel (tagPort cB p₂) (tagPort cD q₂))) W ∧
        W.WF ar ∧ W.agent (d ++ [cD]) op ∧ IsNum W (d ++ [cD], 0) v₁ ∧
        IsNum W (d ++ [cD], 1) v₂ ∧ W.Paired ar (d ++ [cD], 2) (tagPort cD r) ∧
        W.free (tagPort cD r) ∧
        ∀ i γ, W.agent i γ → γ = zero ∨ γ = succ ∨ i = d ++ [cD] := by
  obtain ⟨fA, A', sA, numA, onlyA⟩ := eA
  obtain ⟨fB, B', sB, numB, onlyB⟩ := eB
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
  -- the operator
  have hd : U₂.agent (d ++ [cD]) op := hm₂.agent' (c := cD) (by
    rw [e2D]
    exact hD.ha)
  -- its first argument, across the first segment
  obtain ⟨i₁, pi₁, ni₁⟩ := Addition.IsNum.made hm₂ (c := cA) (p := p₁) (k := v₁) (by
    rw [e2A]
    exact numA)
  have pin₁ : U₂.Paired ar (tagPort cD (d, 0)) (tagPort cD q₁) :=
    hm₂.paired ar (c := cD) (by
      rw [e2D]
      exact hD.fst)
  have hi₁' : ∀ k, ¬ ∃ x, joinRel (tagPort cB p₂) (tagPort cD q₂) (i₁, k) x := fun k =>
    (Addition.Num.label ni₁).elim (fun h => hW₁.unplugged hfree₂ h k)
      (fun h => hW₁.unplugged hfree₂ h k)
  have c1 : (U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).Conn ar (d ++ [cD], 0) (i₁, 0) :=
    Net.Conn.plug hU₂ hfree₁ (joinRel_right _ _) (joinRel_left _ _)
      (tag_ne (Ne.symm hAD) (d, 0) p₁) pin₁.2.2 pi₁.2.2
  have P1 : (U₂.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).Paired ar (d ++ [cD], 0)
      (i₁, 0) :=
    ⟨.inr ⟨op, hd, Nat.zero_le _⟩,
      (Addition.Num.label ni₁).elim (fun h => .inr ⟨zero, h, Nat.zero_le _⟩)
        (fun h => .inr ⟨succ, h, Nat.zero_le _⟩), c1⟩
  -- its second argument, across the second segment
  obtain ⟨i₂, pi₂, ni₂⟩ := Addition.IsNum.made hm₂ (c := cB) (p := p₂) (k := v₂) (by
    rw [e2B]
    exact numB)
  have pin₂ : U₂.Paired ar (tagPort cD (d, 1)) (tagPort cD q₂) :=
    hm₂.paired ar (c := cD) (by
      rw [e2D]
      exact hD.snd)
  have hi₂ : ∀ k, ¬ ∃ x, joinRel (tagPort cA p₁) (tagPort cD q₁) (i₂, k) x := fun k =>
    (Addition.Num.label ni₂).elim (fun h => hU₂.unplugged hfree₁ h k)
      (fun h => hU₂.unplugged hfree₁ h k)
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
  refine ⟨_, (S12.plug _).plug _, hW₂, hd, ?_, ?_, ?_, ⟨⟨fr, joinRel_ne nrA nr1⟩,
    joinRel_ne nrB nr2⟩, ?_⟩
  · exact ⟨i₁, P1.plug (hW₁.unplugged hfree₂ hd 0) (hi₁' 0),
      Addition.Num.plug hW₁ hfree₂ (Addition.Num.plug hU₂ hfree₁ ni₁)⟩
  · exact ⟨i₂, ⟨Net.end_plug pin₂'.1 (hW₁.unplugged hfree₂ hd 1),
        (Addition.Num.label ni₂).elim (fun h => .inr ⟨zero, h, Nat.zero_le _⟩)
          (fun h => .inr ⟨succ, h, Nat.zero_le _⟩), c2⟩,
      Addition.Num.plug hW₁ hfree₂ (Addition.Num.plug hU₂ hfree₁ ni₂)⟩
  · exact (pout.plug (J := joinRel (tagPort cA p₁) (tagPort cD q₁))
      (hU₂.unplugged hfree₁ hd 2) (joinRel_ne nrA nr1)).plug (hW₁.unplugged hfree₂ hd 2)
        (joinRel_ne nrB nr2)
  · intro x γ hx
    obtain ⟨c, x', rfl, hx'⟩ := hm₂.agent hx
    by_cases h1 : c = cA
    · rw [h1, e2A] at hx'
      exact (onlyA x' γ hx').elim .inl fun h => .inr (.inl h)
    · by_cases h2 : c = cB
      · rw [h2, e2B] at hx'
        exact (onlyB x' γ hx').elim .inl fun h => .inr (.inl h)
      · by_cases h3 : c = cD
        · rw [h3, e2D] at hx'
          rw [h3, hD.only x' γ hx']
          exact .inr (.inr rfl)
        · rw [setPart_ne _ _ h2, setPart_ne _ _ h1] at hx'
          exact absurd hx' (hO c h1 h2 h3 x' γ)

/-- **An adder on two nets that compute** computes the sum, in the steps
of the two nets and `v₁ + 1` more. -/
theorem add_evals {U : Net Peano} {P : Nat → Net Peano} (hU : U.WF ar) (hm : U.Made P)
    {cA cB cD : Nat} (hAB : cA ≠ cB) (hAD : cA ≠ cD) (hBD : cB ≠ cD)
    {d : Id} {s₁ v₁ s₂ v₂ : Nat} {p₁ p₂ q₁ q₂ r : Port}
    (eA : Evals (P cA) s₁ v₁ p₁) (eB : Evals (P cB) s₂ v₂ p₂)
    (hD : OpenOp (P cD) add d q₁ q₂ r)
    (hO : ∀ c, c ≠ cA → c ≠ cB → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
        (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar ∧
      Evals ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
          (joinRel (tagPort cB p₂) (tagPort cD q₂)))
        (s₁ + s₂ + (v₁ + 1)) (v₁ + v₂) (tagPort cD r) := by
  obtain ⟨hW0, fr0, W, sts, hW, hd, h1, h2, hout, hfr, honly⟩ :=
    op_setup hU hm hAB hAD hBD eA eB hD hO
  obtain ⟨N', sts', hnum, hag⟩ := add_steps' ⟨hW, hd, h1, h2, hout, hfr, honly⟩
  exact ⟨hW0, fr0, N', sts.trans sts', hnum, hag⟩

/-- **A multiplier on two nets that compute** computes the product, in
the steps of the two nets and `prodCost v₁ v₂` more. -/
theorem mul_evals {U : Net Peano} {P : Nat → Net Peano} (hU : U.WF ar) (hm : U.Made P)
    {cA cB cD : Nat} (hAB : cA ≠ cB) (hAD : cA ≠ cD) (hBD : cB ≠ cD)
    {d : Id} {s₁ v₁ s₂ v₂ : Nat} {p₁ p₂ q₁ q₂ r : Port}
    (eA : Evals (P cA) s₁ v₁ p₁) (eB : Evals (P cB) s₂ v₂ p₂)
    (hD : OpenOp (P cD) mul d q₁ q₂ r)
    (hO : ∀ c, c ≠ cA → c ≠ cB → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
        (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar ∧
      Evals ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
          (joinRel (tagPort cB p₂) (tagPort cD q₂)))
        (s₁ + s₂ + prodCost v₁ v₂) (v₁ * v₂) (tagPort cD r) := by
  obtain ⟨hW0, fr0, W, sts, hW, hd, h1, h2, hout, hfr, honly⟩ :=
    op_setup hU hm hAB hAD hBD eA eB hD hO
  obtain ⟨N', sts', hnum, hag⟩ := mul_steps ⟨hW, hd, h1, h2, hout, hfr, honly⟩
  exact ⟨hW0, fr0, N', sts.trans sts', hnum, hag⟩

/-! ### The nets -/

/-- The numeral `0` on the free port `([0], 0)`. -/
def litBase : XNet Peano :=
  XNet.ofWires [([1], zero)] [([0], 0)] [(([0], 0), ([1], 0))]

/-- **The numeral `n` on the free port `([0], 0)`.** -/
def lit : Nat → XNet Peano
  | 0 => litBase
  | n + 1 => (lit n).pushOn succ ([0], 0) [n + 2]

/-- What the construction keeps: the net is a valid input of the reducer,
it has the numeral `n` on its free port and only successors and zeros,
and its names are below `b`. -/
structure GoodLit (X : XNet Peano) (n b : Nat) : Prop where
  ok : X.Ok ar
  num : IsNum X.toNet ([0], 0) n
  free : X.toNet.free ([0], 0)
  only : ∀ i γ, X.toNet.agent i γ → γ = zero ∨ γ = succ
  below : X.Below b

theorem good_litBase : GoodLit litBase 0 2 := by
  have hX : litBase.Ok ar := by decide
  refine ⟨hX, ⟨[1], hX.link_iff.1 (by decide), show ([1], zero) ∈ litBase.agents by decide⟩,
    ?_, ?_, ?_⟩
  · show ([0], 0) ∈ litBase.free
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), zero)] := hi
    exact .inl (Prod.mk.inj (List.mem_singleton.1 hi')).2
  · intro i hi
    have hall : ∀ i ∈ litBase.usedIds, ∃ j, j < 2 ∧ i = [j] := by decide
    exact hall i (XNet.mem_usedIds hi)

/-- One more successor on the free port. -/
theorem GoodLit.push {X : XNet Peano} {n b : Nat} (g : GoodLit X n b) :
    GoodLit (X.pushOn succ ([0], 0) [b]) (n + 1) (b + 1) := by
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨t, hpt, hnt⟩ := g.num
  have hm' : (X.toNet.insert1 [b] succ ([0], 0) (t, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hpt) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ X.toNet i k →
      Addition.Num ar zero succ (X.toNet.insert1 [b] succ ([0], 0) (t, 0)) i k :=
    Addition.Num.insert1 hm' hm (fun _ _ => port_ne_snd (by decide))
      (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, ?_, ?_, g.below.pushOn hX hpt succ⟩
  · rw [XNet.pushOn_eq hX hpt, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [XNet.pushOn_eq hX hpt, XNet.insert1_toNet]
    exact ⟨[b], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, t,
      hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnt⟩
  · rw [XNet.pushOn_eq hX hpt, XNet.insert1_toNet]
    exact g.free
  · rw [XNet.pushOn_eq hX hpt, XNet.insert1_toNet]
    rintro i γ (hi | ⟨-, e⟩)
    · exact g.only i γ hi
    · exact .inr e

theorem good_lit : ∀ n, GoodLit (lit n) n (n + 2)
  | 0 => good_litBase
  | n + 1 => (good_lit n).push

/-- **An operator waiting for both arguments**, on the free ports
`([2], 0)` and `([3], 0)`, with its result on the free port `([0], 0)`. -/
def openOp (γ : Peano) : XNet Peano :=
  XNet.ofWires [([1], γ)] [([0], 0), ([2], 0), ([3], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

theorem openAdd_ok : (openOp add).Ok ar := by decide

theorem openMul_ok : (openOp mul).Ok ar := by decide

theorem openAdd_spec : OpenOp (openOp add).toNet add [1] ([2], 0) ([3], 0) ([0], 0) := by
  have hX := openAdd_ok
  refine ⟨?_, ?_, hX.link_iff.1 (by decide), hX.link_iff.1 (by decide),
    hX.link_iff.1 (by decide), ?_, ?_, ?_, by decide, by decide, by decide⟩
  · show ([1], add) ∈ (openOp add).agents
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), add)] := hi
    exact (Prod.mk.inj (List.mem_singleton.1 hi')).1
  · show ([2], 0) ∈ (openOp add).free
    decide
  · show ([3], 0) ∈ (openOp add).free
    decide
  · show ([0], 0) ∈ (openOp add).free
    decide

theorem openMul_spec : OpenOp (openOp mul).toNet mul [1] ([2], 0) ([3], 0) ([0], 0) := by
  have hX := openMul_ok
  refine ⟨?_, ?_, hX.link_iff.1 (by decide), hX.link_iff.1 (by decide),
    hX.link_iff.1 (by decide), ?_, ?_, ?_, by decide, by decide, by decide⟩
  · show ([1], mul) ∈ (openOp mul).agents
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), mul)] := hi
    exact (Prod.mk.inj (List.mem_singleton.1 hi')).1
  · show ([2], 0) ∈ (openOp mul).free
    decide
  · show ([3], 0) ∈ (openOp mul).free
    decide
  · show ([0], 0) ∈ (openOp mul).free
    decide

/-- The net of an operator on two nets: the two nets and the operator
that waits, side by side under the tags `0`, `1` and `2`, with the result
port of each net wired to a port of the operator. -/
def opNet (γ : Peano) (X₁ X₂ : XNet Peano) (p₁ p₂ : Port) : XNet Peano :=
  ((XNet.three X₁ X₂ (openOp γ)).plug2 (tagPort 0 p₁) ([2, 2], 0)).plug2 (tagPort 1 p₂)
    ([3, 2], 0)

theorem opNet_toNet (γ : Peano) (X₁ X₂ : XNet Peano) (p₁ p₂ : Port) :
    (opNet γ X₁ X₂ p₁ p₂).toNet =
      (((XNet.three X₁ X₂ (openOp γ)).toNet.plug
        (joinRel (tagPort 0 p₁) (tagPort 2 ([2], 0)))).plug
        (joinRel (tagPort 1 p₂) (tagPort 2 ([3], 0)))) := by
  show (XNet.plug2 (XNet.plug2 _ _ _) _ _).toNet = _
  rw [XNet.plug2_toNet, XNet.plug2_toNet]
  rfl

/-! ### Expressions -/

/-- **Expressions**: numerals, additions and multiplications. -/
inductive PExpr
  | lit (n : Nat)
  | add (e₁ e₂ : PExpr)
  | mul (e₁ e₂ : PExpr)

/-- The value of an expression. -/
def PExpr.eval : PExpr → Nat
  | .lit n => n
  | .add e₁ e₂ => e₁.eval + e₂.eval
  | .mul e₁ e₂ => e₁.eval * e₂.eval

/-- The interactions of an expression: for each addition, one more than
the value of its first argument; for each multiplication, `prodCost` of
the values of its two arguments. -/
def PExpr.cost : PExpr → Nat
  | .lit _ => 0
  | .add e₁ e₂ => e₁.cost + e₂.cost + (e₁.eval + 1)
  | .mul e₁ e₂ => e₁.cost + e₂.cost + prodCost e₁.eval e₂.eval

/-- The free port that carries the result. -/
def PExpr.res : PExpr → Port
  | .lit _ => ([0], 0)
  | .add _ _ => ([0, 2], 0)
  | .mul _ _ => ([0, 2], 0)

/-- **The net of an expression.**  A numeral is its net.  An addition or
a multiplication is the nets of its two arguments and an operator that
waits, side by side, with the result of each argument wired to a port of
the operator. -/
def PExpr.net : PExpr → XNet Peano
  | .lit n => Peano.lit n
  | .add e₁ e₂ => opNet Peano.add e₁.net e₂.net e₁.res e₂.res
  | .mul e₁ e₂ => opNet Peano.mul e₁.net e₂.net e₁.res e₂.res

theorem parts3_none {A B D : Net Peano} : ∀ c, c ≠ 0 → c ≠ 1 → c ≠ 2 → ∀ i γ,
    ¬ (parts3 A B D c).agent i γ
  | 0, h, _, _, _, _ => absurd rfl h
  | 1, _, h, _, _, _ => absurd rfl h
  | 2, _, _, h, _, _ => absurd rfl h
  | c + 3, _, _, _, _, _ => fun h => by
    rw [parts3_rest] at h
    exact h

/-- **The net of an expression is well formed and computes its value**,
in the interactions counted by `PExpr.cost`. -/
theorem PExpr.good : ∀ e : PExpr, e.net.toNet.WF ar ∧ Evals e.net.toNet e.cost e.eval e.res
  | .lit n =>
    ⟨(good_lit n).ok.1, (good_lit n).free, (Peano.lit n).toNet, .refl _, (good_lit n).num,
      (good_lit n).only⟩
  | .add e₁ e₂ => by
    obtain ⟨w₁, ev₁⟩ := PExpr.good e₁
    obtain ⟨w₂, ev₂⟩ := PExpr.good e₂
    have hm := XNet.three_made e₁.net e₂.net (openOp Peano.add)
    have hP := parts3_wf w₁ w₂ openAdd_ok.1
    show (opNet Peano.add e₁.net e₂.net e₁.res e₂.res).toNet.WF ar ∧
      Evals (opNet Peano.add e₁.net e₂.net e₁.res e₂.res).toNet
        (e₁.cost + e₂.cost + (e₁.eval + 1)) (e₁.eval + e₂.eval) (tagPort 2 ([0], 0))
    rw [opNet_toNet]
    exact add_evals (hm.wf hP) hm (cA := 0) (cB := 1) (cD := 2) (by decide) (by decide)
      (by decide) ev₁ ev₂ openAdd_spec parts3_none
  | .mul e₁ e₂ => by
    obtain ⟨w₁, ev₁⟩ := PExpr.good e₁
    obtain ⟨w₂, ev₂⟩ := PExpr.good e₂
    have hm := XNet.three_made e₁.net e₂.net (openOp Peano.mul)
    have hP := parts3_wf w₁ w₂ openMul_ok.1
    show (opNet Peano.mul e₁.net e₂.net e₁.res e₂.res).toNet.WF ar ∧
      Evals (opNet Peano.mul e₁.net e₂.net e₁.res e₂.res).toNet
        (e₁.cost + e₂.cost + prodCost e₁.eval e₂.eval) (e₁.eval * e₂.eval)
        (tagPort 2 ([0], 0))
    rw [opNet_toNet]
    exact mul_evals (hm.wf hP) hm (cA := 0) (cB := 1) (cD := 2) (by decide) (by decide)
      (by decide) ev₁ ev₂ openMul_spec parts3_none

/-- **Every expression comes out right, whatever the threads do.**  With
any number of threads and any schedule, a run on the net of an expression
that is at rest has made the interactions counted by `PExpr.cost`, and
the memory has the numeral of the value on the free port. -/
theorem PExpr.rest (e : PExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := PExpr.good e
  have hn' := normal_of_numerals hag
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
scheduled, from some action on every thread is at rest, the interactions
made are those counted by `PExpr.cost`, and the memory has the numeral of
the value on the free port. -/
theorem PExpr.fair (e : PExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := PExpr.good e
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) hX hnt hs (normal_of_numerals hag) σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hA

/-! ### Running an expression -/

/-- **Run an expression.**  `nt` threads take turns on the net of the
expression for `steps` actions; if they are then at rest, the numeral on
the free port is read. -/
def PExpr.run (e : PExpr) (nt steps : Nat) : Option Nat :=
  XNet.runRead xsys zero succ e.net e.res nt steps

/-- **Whatever the run returns is the value of the expression.** -/
theorem PExpr.run_sound (e : PExpr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.run nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := PExpr.good e
  exact XNet.runRead_sound (zero := zero) (succ := succ) xsys (by decide) (Nat.le_refl 1) hX hs (normal_of_numerals hag) hA
    hnt h

/-- **Given enough actions, the run returns the value of the
expression.** -/
theorem PExpr.run_complete (e : PExpr) {nt : Nat} (hnt : 0 < nt) :
    ∃ s₀, ∀ s, s₀ ≤ s → e.run nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := PExpr.good e
  exact XNet.runRead_complete (zero := zero) (succ := succ) xsys (by decide) hX hs (normal_of_numerals hag) hA hnt

/-- `(2 + 1) * (3 * 2)` has the value 18 and costs 81 interactions. -/
example : (PExpr.mul (.add (.lit 2) (.lit 1)) (.mul (.lit 3) (.lit 2))).eval = 18 ∧
    (PExpr.mul (.add (.lit 2) (.lit 1)) (.mul (.lit 3) (.lit 2))).cost = 81 := by
  decide

set_option maxRecDepth 100000 in
/-- `(2 * 2) + 1` on the machine, two threads taking turns: after 1000
actions both are at rest and they have made 23 interactions, the cost of
the expression. -/
example :
    ((XMach.init (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).net 2).trace xsys
      (fun j => j % 2) 1000).1.resting = true ∧
    ((XMach.init (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).net 2).trace xsys
      (fun j => j % 2) 1000).2 = 23 ∧
    (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).cost = 23 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `(2 * 2) + 1` run by two threads taking turns: after 1000 actions
they are at rest and the result read is `5`. -/
example : (PExpr.add (.mul (.lit 2) (.lit 2)) (.lit 1)).run 2 1000 = some 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `2 * (1 + 2)` run by three threads taking turns: after 1500 actions
they are at rest and the result read is `6`. -/
example : (PExpr.mul (.lit 2) (.add (.lit 1) (.lit 2))).run 3 1500 = some 6 := by
  decide +kernel

end Peano

end INet
