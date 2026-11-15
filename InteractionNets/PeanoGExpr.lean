import InteractionNets.PeanoRun
import InteractionNets.Union
import InteractionNets.ReadBack

/-! # Expressions over any operators that compute

An operator is data (`Peano.Op1`, `Peano.Op2`): a symbol, the function it
computes, its cost, and the proof that, alone with numerals as
arguments, it reduces in that many steps to the numeral of the value.
Any agent that computes (`Peano.Computes1`, `Peano.Computes2`) gives one
(`Core.Op1.ofComputes`, `Core.Op2.ofComputes`), and so does the adder
(`Peano.addOp`).

Expressions (`Peano.GExpr`) are numerals and operators of one or two
arguments applied to expressions.  Each has a net: the nets of the
arguments and an operator that waits for them, side by side under tags,
with the result of each argument wired to a port of the operator.  The
argument nets reduce inside the whole as they do alone
(`Net.Made.steps`, the rules of `Peano` giving every new agent a side,
`Peano.system_sided`); their results are then the arguments of the
operator (`Core.op_setup`, and `Core.op_setup1` for one argument), and
the operator finishes.  So every expression has a net that is well
formed and computes the value in exactly `GExpr.cost` interactions
(`GExpr.good`); on the machine, with any number of threads and any
schedule, a run at rest has made that many interactions and holds the
value (`GExpr.rest`), and a fair run comes to rest (`GExpr.fair`); the
expression can be run and its result read (`GExpr.run_sound`,
`GExpr.run_complete`).

The theorems for the machine on a single operator are also stated for
the operators (`Core.Op2.rest`, `Core.Op1.rest`), which brings in the
adder (`Peano.sum_rest`).
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

namespace Core

open Arith (tagPort tagPort_inj tagPort_snoc snoc_inj tag_ne)

variable {S : Type} [DecidableEq S] {xsys : XSys S} {zero succ dup era : S}
  [K : Core xsys.sys zero succ dup era]

include K

set_option linter.unusedSectionVars false

local notation "system" => xsys.sys
local notation "ar" => xsys.sys.ar
local notation "NumList" => Addition.NumList xsys.sys.ar zero succ
local notation "IsNum" => Addition.IsNum xsys.sys.ar zero succ
local notation "IsNumQ" => Addition.IsNumQ xsys.sys.ar zero succ



omit K in
/-- **A net that computes a number.**  `Evals N s v p`: the port `p` is
free, and the net reduces in `s` steps to a net of successors and zeros
that has the numeral `v` on `p`. -/
def Evals (xs : XSys S) {zero succ dup era : S} [Core xs.sys zero succ dup era]
    (N : Net S) (s v : Nat) (p : Port) : Prop :=
  N.free p ∧ ∃ N', Steps (Step xs.sys) s N N' ∧ Addition.IsNum xs.sys.ar zero succ N' p v ∧
    ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ

omit K in
/-- **An operator waiting for both arguments**: the only agent `d` of the
net, with the symbol `op`, has its arguments on the free ports `q₁` and
`q₂` and its result on the free port `r`. -/
structure OpenOp (xs : XSys S) {zero succ dup era : S} [Core xs.sys zero succ dup era]
    (N : Net S) (op : S) (d : Id) (q₁ q₂ r : Port) : Prop where
  ha : N.agent d op
  only : ∀ i γ, N.agent i γ → i = d
  fst : N.Paired xs.sys.ar (d, 0) q₁
  snd : N.Paired xs.sys.ar (d, 1) q₂
  out : N.Paired xs.sys.ar (d, 2) r
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
theorem op_setup {U : Net S} {P : Nat → Net S} (hU : U.WF ar) (hm : U.Made P)
    {cA cB cD : Nat} (hAB : cA ≠ cB) (hAD : cA ≠ cD) (hBD : cB ≠ cD)
    {op : S} {d : Id} {s₁ v₁ s₂ v₂ : Nat} {p₁ p₂ q₁ q₂ r : Port}
    (eA : Evals xsys (P cA) s₁ v₁ p₁) (eB : Evals xsys (P cB) s₂ v₂ p₂)
    (hD : OpenOp xsys (P cD) op d q₁ q₂ r)
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
  obtain ⟨U₁, s₁', hm₁⟩ := hm.steps K.sided sA
  have eB1 : setPart P cA A' cB = P cB := setPart_ne _ _ (Ne.symm hAB)
  have sB' : Steps (Step system) s₂ (setPart P cA A' cB) B' := by
    rw [eB1]
    exact sB
  obtain ⟨U₂, s₂', hm₂⟩ := hm₁.steps K.sided sB'
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

/-! ### The nets -/

omit K in
/-- The numeral `0` on the free port `([0], 0)`. -/
def litBase (zero : S) : XNet S :=
  XNet.ofWires [([1], zero)] [([0], 0)] [(([0], 0), ([1], 0))]

omit K in
/-- **The numeral `n` on the free port `([0], 0)`.** -/
def lit (zero succ : S) : Nat → XNet S
  | 0 => litBase zero
  | n + 1 => (lit zero succ n).pushOn succ ([0], 0) [n + 2]

omit K in
/-- What the construction keeps: the net is a valid input of the reducer,
it has the numeral `n` on its free port and only successors and zeros,
and its names are below `b`. -/
structure GoodLit (xs : XSys S) {zero succ dup era : S} [Core xs.sys zero succ dup era]
    (X : XNet S) (n b : Nat) : Prop where
  ok : X.Ok xs.sys.ar
  num : Addition.IsNum xs.sys.ar zero succ X.toNet ([0], 0) n
  free : X.toNet.free ([0], 0)
  only : ∀ i γ, X.toNet.agent i γ → γ = zero ∨ γ = succ
  below : X.Below b

/-- The numeral `0`, over the symbols of `Arith`. -/
def litT : XNet Arith :=
  XNet.ofWires [([1], .zero)] [([0], 0)] [(([0], 0), ([1], 0))]

theorem good_litBase : GoodLit xsys (litBase zero) 0 2 := by
  have hT : litT.Ok Arith.ar := by decide
  have e : litBase zero = litT.relabel (ofArithAt zero zero) := rfl
  have hX : (litBase zero).Ok ar := by
    rw [e]
    refine hT.relabel (ofArithAt zero zero) fun i γ hi => ?_
    have hi' : (i, γ) ∈ [(([1] : Id), Arith.zero)] := hi
    rw [(Prod.mk.inj (List.mem_singleton.1 hi')).2]
    exact K.ar_zero
  have ew : (litBase zero).wires = litT.wires := rfl
  have ef : (litBase zero).free = litT.free := rfl
  have eu : (litBase zero).usedIds = litT.usedIds := rfl
  refine ⟨hX, ⟨[1], hX.link_iff.1 (by rw [ew]; decide), List.mem_cons_self⟩, ?_, ?_, ?_⟩
  · show ([0], 0) ∈ (litBase zero).free
    rw [ef]
    decide
  · intro i γ hi
    have hi' : (i, γ) ∈ [(([1] : Id), zero)] := hi
    exact .inl (Prod.mk.inj (List.mem_singleton.1 hi')).2
  · intro i hi
    have hall : ∀ i ∈ (litBase zero).usedIds, ∃ j, j < 2 ∧ i = [j] := by
      rw [eu]
      decide
    exact hall i (XNet.mem_usedIds hi)

/-- One more successor on the free port. -/
theorem GoodLit.push {X : XNet S} {n b : Nat} (g : GoodLit xsys X n b) :
    GoodLit xsys (X.pushOn succ ([0], 0) [b]) (n + 1) (b + 1) := by
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨t, hpt, hnt⟩ := g.num
  have hm' : (X.toNet.insert1 [b] succ ([0], 0) (t, 0)).Matching ar :=
    hm.insert1 K.ar_succ (hm.paired_iff.1 hpt) g.below.fresh g.below.fresh'
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

theorem good_lit : ∀ n, GoodLit xsys (lit zero succ n) n (n + 2)
  | 0 => good_litBase
  | n + 1 => (good_lit n).push

omit K in
/-- **An operator waiting for both arguments**, on the free ports
`([2], 0)` and `([3], 0)`, with its result on the free port `([0], 0)`. -/
def openOp (γ : S) : XNet S :=
  XNet.ofWires [([1], γ)] [([0], 0), ([2], 0), ([3], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

omit K in
/-- The net of an operator on two nets: the two nets and the operator
that waits, side by side under the tags `0`, `1` and `2`, with the result
port of each net wired to a port of the operator. -/
def opNet (γ : S) (X₁ X₂ : XNet S) (p₁ p₂ : Port) : XNet S :=
  ((XNet.three X₁ X₂ (openOp γ)).plug2 (tagPort 0 p₁) ([2, 2], 0)).plug2 (tagPort 1 p₂)
    ([3, 2], 0)

omit K in
theorem opNet_toNet (γ : S) (X₁ X₂ : XNet S) (p₁ p₂ : Port) :
    (opNet γ X₁ X₂ p₁ p₂).toNet =
      (((XNet.three X₁ X₂ (openOp γ)).toNet.plug
        (joinRel (tagPort 0 p₁) (tagPort 2 ([2], 0)))).plug
        (joinRel (tagPort 1 p₂) (tagPort 2 ([3], 0)))) := by
  show (XNet.plug2 (XNet.plug2 _ _ _) _ _).toNet = _
  rw [XNet.plug2_toNet, XNet.plug2_toNet]
  rfl

omit K in
theorem parts3_none {A B D : Net S} : ∀ c, c ≠ 0 → c ≠ 1 → c ≠ 2 → ∀ i γ,
    ¬ (parts3 A B D c).agent i γ
  | 0, h, _, _, _, _ => absurd rfl h
  | 1, _, h, _, _, _ => absurd rfl h
  | 2, _, _, h, _, _ => absurd rfl h
  | c + 3, _, _, _, _, _ => fun h => by
    rw [parts3_rest] at h
    exact h


variable {N : Net S} {r : Port}

/-! ### Operators -/

omit K in
/-- **An operator of one argument**: a symbol, the function it computes
and its cost; alone with a numeral as argument, the agent reduces in the
cost to the numeral of the value, in a net of successors and zeros. -/
structure Op1 (xsys : XSys S) {zero succ dup era : S} [Core xsys.sys zero succ dup era] where
  sym : S
  f : Nat → Nat
  c : Nat → Nat
  ar_eq : xsys.sys.ar sym = 1
  ne0 : zero ≠ sym
  ne1 : succ ≠ sym
  steps : ∀ {N : Net S} {a : Id} {n : Nat} {r : Port}, Unary xsys.sys sym N a n r →
    ∃ N', Steps (Step xsys.sys) (c n) N N' ∧ Addition.IsNum xsys.sys.ar zero succ N' r (f n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ

omit K in
/-- **An operator of two arguments**, the same with two numerals. -/
structure Op2 (xsys : XSys S) {zero succ dup era : S} [Core xsys.sys zero succ dup era] where
  sym : S
  f : Nat → Nat → Nat
  c : Nat → Nat → Nat
  ar_eq : xsys.sys.ar sym = 2
  ne0 : zero ≠ sym
  ne1 : succ ≠ sym
  steps : ∀ {N : Net S} {a : Id} {m n : Nat} {r : Port}, Binary xsys.sys sym N a m n r →
    ∃ N', Steps (Step xsys.sys) (c m n) N N' ∧ Addition.IsNum xsys.sys.ar zero succ N' r (f m n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ

/-- What is left of an agent that computes: the numeral and the
numerals. -/
theorem unary_steps {op : S} {f c : Nat → Nat} (H : Computes1 system op f c) {a : Id} {n : Nat}
    (u : Unary system op N a n r) :
    ∃ N', Steps (Step system) (c n) N N' ∧ IsNum N' r (f n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ := by
  have hN := u.wf
  obtain ⟨h, hp, hn⟩ := u.fst
  obtain ⟨l, hl, el⟩ := Addition.Num.list hn
  have hrl : ¬ r.1 ∈ l := fun hm =>
    (hl.label _ hm).elim (fun h => hN.free_agent (i := r.1) (k := r.2) u.free h)
      fun h => hN.free_agent (i := r.1) (k := r.2) u.free h
  obtain ⟨N', sts, hres, -, hag⟩ := H l hN u.ha hp hl u.out
    ⟨fun e' => hN.free_agent (i := r.1) (k := r.2) u.free (e' ▸ u.ha), hrl⟩ el
  refine ⟨N', sts, hres.isNum, fun i γ hi => ?_⟩
  rcases hag i γ hi with hz | hsu | ⟨hi₀, hne⟩
  · exact .inl hz
  · exact .inr hsu
  · rcases u.only i γ hi₀ with hz | hsu | e'
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e' hne

/-- The same for two arguments. -/
theorem binary_steps {op : S} {f c : Nat → Nat → Nat} (H : Computes2 system op f c) {a : Id}
    {m n : Nat} (u : Binary system op N a m n r) :
    ∃ N', Steps (Step system) (c m n) N N' ∧ IsNum N' r (f m n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ := by
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
  refine ⟨N', sts, hres.isNum, fun i γ hi => ?_⟩
  rcases hag i γ hi with hz | hsu | ⟨hi₀, hne⟩
  · exact .inl hz
  · exact .inr hsu
  · rcases u.only i γ hi₀ with hz | hsu | e'
    · exact .inl hz
    · exact .inr hsu
    · exact absurd e' hne

/-- **An agent of one argument that computes is an operator.** -/
def Op1.ofComputes {op : S} {f c : Nat → Nat} (H : Computes1 system op f c) (h : ar op = 1)
    (h0 : zero ≠ op) (h1 : succ ≠ op) : Op1 xsys :=
  ⟨op, f, c, h, h0, h1, fun u => unary_steps H u⟩

/-- **An agent of two arguments that computes is an operator.** -/
def Op2.ofComputes {op : S} {f c : Nat → Nat → Nat} (H : Computes2 system op f c)
    (h : ar op = 2) (h0 : zero ≠ op) (h1 : succ ≠ op) : Op2 xsys :=
  ⟨op, f, c, h, h0, h1, fun u => binary_steps H u⟩

/-! ### An operator of one argument on a net that computes -/

omit K in
/-- **An operator of one argument waiting for it**: the only agent `d` of
the net, with the symbol `op`, has its argument on the free port `q₁` and
its result on the free port `r`. -/
structure OpenOp1 (xs : XSys S) {zero succ dup era : S} [Core xs.sys zero succ dup era]
    (N : Net S) (op : S) (d : Id) (q₁ r : Port) : Prop where
  ha : N.agent d op
  only : ∀ i γ, N.agent i γ → i = d
  fst : N.Paired xs.sys.ar (d, 0) q₁
  out : N.Paired xs.sys.ar (d, 1) r
  free₁ : N.free q₁
  free : N.free r
  ne : r ≠ q₁

/-- **An operator of one argument on a net that computes.**  Let a
well-formed net be made of nets under tags: under `cA` a net that
computes `v` on its free port `p₁`, under `cD` an operator waiting for
its argument on `q₁`, with its result on `r`; and no agent elsewhere.
Wire `p₁` to `q₁`.  The net is well formed, and in the steps of the net
it becomes a net in which the operator has the numeral `v` as argument
and the free port `r` as result, with no other agents than successors
and zeros. -/
theorem op_setup1 {U : Net S} {P : Nat → Net S} (hU : U.WF ar) (hm : U.Made P)
    {cA cD : Nat} (hAD : cA ≠ cD) {op : S} {d : Id} {s v : Nat} {p₁ q₁ r : Port}
    (eA : Evals xsys (P cA) s v p₁) (hD : OpenOp1 xsys (P cD) op d q₁ r)
    (hO : ∀ c, c ≠ cA → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).WF ar ∧
      (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).free (tagPort cD r) ∧
      ∃ W, Steps (Step system) s (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))) W ∧
        W.WF ar ∧ W.agent (d ++ [cD]) op ∧ IsNum W (d ++ [cD], 0) v ∧
        W.Paired ar (d ++ [cD], 1) (tagPort cD r) ∧ W.free (tagPort cD r) ∧
        ∀ i γ, W.agent i γ → γ = zero ∨ γ = succ ∨ i = d ++ [cD] := by
  obtain ⟨fA, A', sA, numA, onlyA⟩ := eA
  have n1 : tagPort cA p₁ ≠ tagPort cD q₁ := tag_ne hAD _ _
  have nrA : tagPort cD r ≠ tagPort cA p₁ := tag_ne (Ne.symm hAD) _ _
  have nr1 : tagPort cD r ≠ tagPort cD q₁ := fun e => hD.ne (tagPort_inj e)
  have hV0 : (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).WF ar :=
    hU.plug_two (hm.free' fA) (hm.free' hD.free₁) n1
  have fr0 : (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).free (tagPort cD r) :=
    ⟨hm.free' hD.free, joinRel_ne nrA nr1⟩
  refine ⟨hV0, fr0, ?_⟩
  -- the net reduces inside the whole
  obtain ⟨U₁, S1, hm₁⟩ := hm.steps K.sided sA
  have e1A : setPart P cA A' cA = A' := setPart_same _ _ _
  have e1D : setPart P cA A' cD = P cD := setPart_ne _ _ (Ne.symm hAD)
  have hU₁ : U₁.WF ar := Steps.wf hU S1
  have hW₁ : (U₁.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).WF ar :=
    Steps.wf hV0 (S1.plug _)
  have fp₁ : U₁.free (tagPort cA p₁) := hm₁.free' (c := cA) (p := p₁) (by
    rw [e1A, Steps.free sA]
    exact fA)
  have fq₁ : U₁.free (tagPort cD q₁) := hm₁.free' (c := cD) (p := q₁) (by
    rw [e1D]
    exact hD.free₁)
  have fr : U₁.free (tagPort cD r) := hm₁.free' (c := cD) (p := r) (by
    rw [e1D]
    exact hD.free)
  have hfree₁ : ∀ u v : Port, joinRel (tagPort cA p₁) (tagPort cD q₁) u v → U₁.free u := by
    rintro u v (⟨e, -⟩ | ⟨e, -⟩)
    · rw [e]
      exact fp₁
    · rw [e]
      exact fq₁
  have hd : U₁.agent (d ++ [cD]) op := hm₁.agent' (c := cD) (by
    rw [e1D]
    exact hD.ha)
  -- the argument, across the segment
  obtain ⟨i₁, pi₁, ni₁⟩ := Addition.IsNum.made hm₁ (c := cA) (p := p₁) (k := v) (by
    rw [e1A]
    exact numA)
  have pin₁ : U₁.Paired ar (tagPort cD (d, 0)) (tagPort cD q₁) :=
    hm₁.paired ar (c := cD) (by
      rw [e1D]
      exact hD.fst)
  have c1 : (U₁.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).Conn ar (d ++ [cD], 0) (i₁, 0) :=
    Net.Conn.plug hU₁ hfree₁ (joinRel_right _ _) (joinRel_left _ _)
      (tag_ne (Ne.symm hAD) (d, 0) p₁) pin₁.2.2 pi₁.2.2
  have P1 : (U₁.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).Paired ar (d ++ [cD], 0)
      (i₁, 0) :=
    ⟨.inr ⟨op, hd, Nat.zero_le _⟩,
      (Addition.Num.label ni₁).elim (fun h => .inr ⟨zero, h, Nat.zero_le _⟩)
        (fun h => .inr ⟨succ, h, Nat.zero_le _⟩), c1⟩
  -- the result
  have pout : U₁.Paired ar (tagPort cD (d, 1)) (tagPort cD r) :=
    hm₁.paired ar (c := cD) (by
      rw [e1D]
      exact hD.out)
  refine ⟨_, S1.plug _, hW₁, hd, ⟨i₁, P1, Addition.Num.plug hU₁ hfree₁ ni₁⟩,
    pout.plug (J := joinRel (tagPort cA p₁) (tagPort cD q₁)) (hU₁.unplugged hfree₁ hd 1)
      (joinRel_ne nrA nr1), ⟨fr, joinRel_ne nrA nr1⟩, ?_⟩
  intro x γ hx
  obtain ⟨c, x', rfl, hx'⟩ := hm₁.agent hx
  by_cases h1 : c = cA
  · rw [h1, e1A] at hx'
    exact (onlyA x' γ hx').elim .inl fun h => .inr (.inl h)
  · by_cases h3 : c = cD
    · rw [h3, e1D] at hx'
      rw [h3, hD.only x' γ hx']
      exact .inr (.inr rfl)
    · rw [setPart_ne _ _ h1] at hx'
      exact absurd hx' (hO c h1 h3 x' γ)

/-- **An operator of one argument on a net that computes** computes its
function, in the steps of the net and its cost more. -/
theorem op1_evals (o : Op1 xsys) {U : Net S} {P : Nat → Net S} (hU : U.WF ar)
    (hm : U.Made P) {cA cD : Nat} (hAD : cA ≠ cD) {d : Id} {s v : Nat} {p₁ q₁ r : Port}
    (eA : Evals xsys (P cA) s v p₁) (hD : OpenOp1 xsys (P cD) o.sym d q₁ r)
    (hO : ∀ c, c ≠ cA → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).WF ar ∧
      Evals xsys (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))) (s + o.c v) (o.f v)
        (tagPort cD r) := by
  obtain ⟨hW0, fr0, W, sts, hW, hd, h1, hout, hfr, honly⟩ := op_setup1 hU hm hAD eA hD hO
  obtain ⟨N', sts', hnum, hag⟩ := o.steps ⟨hW, hd, h1, hout, hfr, honly⟩
  exact ⟨hW0, fr0, N', sts.trans sts', hnum, hag⟩

/-- **An operator of two arguments on two nets that compute** computes
its function, in the steps of the two nets and its cost more. -/
theorem op2_evals (o : Op2 xsys) {U : Net S} {P : Nat → Net S} (hU : U.WF ar)
    (hm : U.Made P) {cA cB cD : Nat} (hAB : cA ≠ cB) (hAD : cA ≠ cD) (hBD : cB ≠ cD)
    {d : Id} {s₁ v₁ s₂ v₂ : Nat} {p₁ p₂ q₁ q₂ r : Port}
    (eA : Evals xsys (P cA) s₁ v₁ p₁) (eB : Evals xsys (P cB) s₂ v₂ p₂)
    (hD : OpenOp xsys (P cD) o.sym d q₁ q₂ r)
    (hO : ∀ c, c ≠ cA → c ≠ cB → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
        (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar ∧
      Evals xsys ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
          (joinRel (tagPort cB p₂) (tagPort cD q₂)))
        (s₁ + s₂ + o.c v₁ v₂) (o.f v₁ v₂) (tagPort cD r) := by
  obtain ⟨hW0, fr0, W, sts, hW, hd, h1, h2, hout, hfr, honly⟩ :=
    op_setup hU hm hAB hAD hBD eA eB hD hO
  obtain ⟨N', sts', hnum, hag⟩ := o.steps ⟨hW, hd, h1, h2, hout, hfr, honly⟩
  exact ⟨hW0, fr0, N', sts.trans sts', hnum, hag⟩

/-! ### The nets -/

omit K in
/-- The empty memory. -/
def emptyX : XNet S := XNet.ofWires [] [] []

/-- The empty memory, over the symbols of `Arith`. -/
def emptyT : XNet Arith := XNet.ofWires [] [] []

theorem emptyX_ok : (emptyX : XNet S).Ok ar := by
  have hT : emptyT.Ok Arith.ar := by decide
  have e : (emptyX : XNet S) = emptyT.relabel (ofArithAt zero zero) := rfl
  rw [e]
  exact hT.relabel (ofArithAt zero zero) fun i γ hi => absurd hi List.not_mem_nil

omit K in
theorem emptyX_none (i : Id) (γ : S) : ¬ emptyX.toNet.agent i γ :=
  fun h => List.not_mem_nil h

omit K in
/-- **An operator of one argument waiting for it**, on the free port
`([2], 0)`, with its result on the free port `([0], 0)`. -/
def openOp1 (γ : S) : XNet S :=
  XNet.ofWires [([1], γ)] [([0], 0), ([2], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([0], 0))]

/-- An operator of one argument that waits, over the symbols of
`Arith`. -/
def openOp1T : XNet Arith :=
  XNet.ofWires [([1], .succ)] [([0], 0), ([2], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([0], 0))]

theorem openOp1_ok {γ : S} (h : ar γ = 1) : (openOp1 γ).Ok ar := by
  have hT : openOp1T.Ok Arith.ar := by decide
  have e : openOp1 γ = openOp1T.relabel (ofArithAt zero γ) := rfl
  rw [e]
  refine hT.relabel (ofArithAt zero γ) fun i γ' hi => ?_
  have hi' : (i, γ') ∈ [(([1] : Id), Arith.succ)] := hi
  rw [(Prod.mk.inj (List.mem_singleton.1 hi')).2]
  exact h

theorem openOp1_spec {γ : S} (h : ar γ = 1) :
    OpenOp1 xsys (openOp1 γ).toNet γ [1] ([2], 0) ([0], 0) := by
  have hX := openOp1_ok h
  have ew : (openOp1 γ).wires = openOp1T.wires := rfl
  have ef : (openOp1 γ).free = openOp1T.free := rfl
  refine ⟨List.mem_cons_self, ?_, hX.link_iff.1 (by rw [ew]; decide),
    hX.link_iff.1 (by rw [ew]; decide), ?_, ?_, by decide⟩
  · intro i γ' hi
    have hi' : (i, γ') ∈ [(([1] : Id), γ)] := hi
    exact (Prod.mk.inj (List.mem_singleton.1 hi')).1
  · show ([2], 0) ∈ (openOp1 γ).free
    rw [ef]
    decide
  · show ([0], 0) ∈ (openOp1 γ).free
    rw [ef]
    decide

omit K in
/-- The net of an operator of one argument on a net: the net, the empty
memory and the operator that waits, side by side under the tags `0`, `1`
and `2`, with the result port of the net wired to the argument of the
operator. -/
def opNet1 (γ : S) (X : XNet S) (p : Port) : XNet S :=
  (XNet.three X emptyX (openOp1 γ)).plug2 (tagPort 0 p) ([2, 2], 0)

omit K in
theorem opNet1_toNet (γ : S) (X : XNet S) (p : Port) :
    (opNet1 γ X p).toNet =
      (XNet.three X emptyX (openOp1 γ)).toNet.plug
        (joinRel (tagPort 0 p) (tagPort 2 ([2], 0))) := by
  show (XNet.plug2 _ _ _).toNet = _
  rw [XNet.plug2_toNet]
  rfl

/-- An operator of two arguments that waits, over the symbols of
`Arith`. -/
def openOpT : XNet Arith :=
  XNet.ofWires [([1], .add)] [([0], 0), ([2], 0), ([3], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

theorem openOp_ok {γ : S} (h : ar γ = 2) : (openOp γ).Ok ar := by
  have hT : openOpT.Ok Arith.ar := by decide
  have e : openOp γ = openOpT.relabel (ofArithAt zero γ) := rfl
  rw [e]
  refine hT.relabel (ofArithAt zero γ) fun i γ' hi => ?_
  have hi' : (i, γ') ∈ [(([1] : Id), Arith.add)] := hi
  rw [(Prod.mk.inj (List.mem_singleton.1 hi')).2]
  exact h

theorem openOp_spec {γ : S} (h : ar γ = 2) :
    OpenOp xsys (openOp γ).toNet γ [1] ([2], 0) ([3], 0) ([0], 0) := by
  have hX := openOp_ok h
  have ew : (openOp γ).wires = openOpT.wires := rfl
  have ef : (openOp γ).free = openOpT.free := rfl
  refine ⟨List.mem_cons_self, ?_, hX.link_iff.1 (by rw [ew]; decide),
    hX.link_iff.1 (by rw [ew]; decide), hX.link_iff.1 (by rw [ew]; decide), ?_, ?_, ?_,
    by decide, by decide, by decide⟩
  · intro i γ' hi
    have hi' : (i, γ') ∈ [(([1] : Id), γ)] := hi
    exact (Prod.mk.inj (List.mem_singleton.1 hi')).1
  · show ([2], 0) ∈ (openOp γ).free
    rw [ef]
    decide
  · show ([3], 0) ∈ (openOp γ).free
    rw [ef]
    decide
  · show ([0], 0) ∈ (openOp γ).free
    rw [ef]
    decide

omit K in
theorem parts3_none1 {A D : Net S} : ∀ c, c ≠ 0 → c ≠ 2 → ∀ i γ,
    ¬ (parts3 A emptyX.toNet D c).agent i γ
  | 0, h, _, _, _ => absurd rfl h
  | 1, _, _, i, γ => emptyX_none i γ
  | 2, _, h, _, _ => absurd rfl h
  | c + 3, _, _, _, _ => fun h => by
    rw [parts3_rest] at h
    exact h

/-! ### Expressions -/

omit K in
/-- **Expressions over any operators**: numerals, and operators of one
or two arguments applied to expressions. -/
inductive GExpr (xsys : XSys S) {zero succ dup era : S} [Core xsys.sys zero succ dup era]
  | lit (n : Nat)
  | app1 (o : Op1 xsys) (e : GExpr xsys)
  | app2 (o : Op2 xsys) (e₁ e₂ : GExpr xsys)

/-- The value of an expression. -/
def GExpr.eval : GExpr xsys → Nat
  | .lit n => n
  | .app1 o e => o.f e.eval
  | .app2 o e₁ e₂ => o.f e₁.eval e₂.eval

/-- The interactions of an expression: for each operator, its cost on
the values of its arguments. -/
def GExpr.cost : GExpr xsys → Nat
  | .lit _ => 0
  | .app1 o e => e.cost + o.c e.eval
  | .app2 o e₁ e₂ => e₁.cost + e₂.cost + o.c e₁.eval e₂.eval

/-- The free port that carries the result. -/
def GExpr.res : GExpr xsys → Port
  | .lit _ => ([0], 0)
  | .app1 _ _ => ([0, 2], 0)
  | .app2 _ _ _ => ([0, 2], 0)

/-- **The net of an expression.**  A numeral is its net; an operator is
the nets of its arguments and the operator that waits, side by side,
with the result of each argument wired to a port of the operator. -/
def GExpr.net : GExpr xsys → XNet S
  | .lit n => Core.lit zero succ n
  | .app1 o e => opNet1 o.sym e.net e.res
  | .app2 o e₁ e₂ => opNet o.sym e₁.net e₂.net e₁.res e₂.res

/-- **The net of an expression is well formed and computes its value**,
in the interactions counted by `GExpr.cost`. -/
theorem GExpr.good : ∀ e : GExpr xsys, e.net.toNet.WF ar ∧ Evals xsys e.net.toNet e.cost e.eval e.res
  | .lit n =>
    ⟨(good_lit (xsys := xsys) n).ok.1, (good_lit (xsys := xsys) n).free,
      (Core.lit zero succ n).toNet, .refl _, (good_lit (xsys := xsys) n).num,
      (good_lit (xsys := xsys) n).only⟩
  | .app1 o e => by
    obtain ⟨w, ev⟩ := GExpr.good e
    have hm := XNet.three_made e.net emptyX (openOp1 o.sym)
    have hP := parts3_wf w emptyX_ok.1 (openOp1_ok o.ar_eq).1
    show (opNet1 o.sym e.net e.res).toNet.WF ar ∧
      Evals xsys (opNet1 o.sym e.net e.res).toNet (e.cost + o.c e.eval) (o.f e.eval)
        (tagPort 2 ([0], 0))
    rw [opNet1_toNet]
    exact op1_evals o (hm.wf hP) hm (cA := 0) (cD := 2) (by decide) ev (openOp1_spec o.ar_eq)
      parts3_none1
  | .app2 o e₁ e₂ => by
    obtain ⟨w₁, ev₁⟩ := GExpr.good e₁
    obtain ⟨w₂, ev₂⟩ := GExpr.good e₂
    have hm := XNet.three_made e₁.net e₂.net (openOp o.sym)
    have hP := parts3_wf w₁ w₂ (openOp_ok o.ar_eq).1
    show (opNet o.sym e₁.net e₂.net e₁.res e₂.res).toNet.WF ar ∧
      Evals xsys (opNet o.sym e₁.net e₂.net e₁.res e₂.res).toNet
        (e₁.cost + e₂.cost + o.c e₁.eval e₂.eval) (o.f e₁.eval e₂.eval) (tagPort 2 ([0], 0))
    rw [opNet_toNet]
    exact op2_evals o (hm.wf hP) hm (cA := 0) (cB := 1) (cD := 2) (by decide) (by decide)
      (by decide) ev₁ ev₂ (openOp_spec o.ar_eq) parts3_none

/-- **Every expression comes out right, whatever the threads do.**  With
any number of threads and any schedule, a run on the net of an expression
that is at rest has made the interactions counted by `GExpr.cost`, and
the memory has the numeral of the value on the free port. -/
theorem GExpr.rest (e : GExpr xsys) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  have hn' := (normal_of_numerals hag : Normal (Step xsys.sys) _)
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init e.net nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e', ek⟩ := (hu hs).2 hn'
  have e'' : N' = ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet := e'
  rw [← e'']
  exact ⟨ek.symm, hA⟩

/-- **Every expression under a fair schedule.** -/
theorem GExpr.fair (e : GExpr xsys) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) hX hnt hs ((normal_of_numerals hag : Normal (Step xsys.sys) _)) σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hA

/-- **Run an expression.** -/
def GExpr.run (e : GExpr xsys) (nt steps : Nat) : Option Nat :=
  XNet.runRead xsys zero succ e.net e.res nt steps

/-- **Whatever the run returns is the value of the expression.** -/
theorem GExpr.run_sound (e : GExpr xsys) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.run nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  exact XNet.runRead_sound (zero := zero) (succ := succ) xsys K.zero_ne_succ (Nat.le_of_eq K.ar_succ.symm) hX hs
    ((normal_of_numerals hag : Normal (Step xsys.sys) _)) hA hnt h

/-- **Given enough actions, the run returns the value of the
expression.** -/
theorem GExpr.run_complete (e : GExpr xsys) {nt : Nat} (hnt : 0 < nt) :
    ∃ s₀, ∀ s, s₀ ≤ s → e.run nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  exact XNet.runRead_complete (zero := zero) (succ := succ) xsys K.zero_ne_succ hX hs
    ((normal_of_numerals hag : Normal (Step xsys.sys) _)) hA hnt

/-! ### One operator on the machine -/

/-- **An operator of two arguments, alone on the machine**: on the net
`Peano.binaryNet zero succ o.sym m n`, with any number of threads and any
schedule, a run at rest has made exactly `o.c m n` interactions and
holds `o.f m n`. -/
theorem Op2.rest (o : Op2 xsys) (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (binaryNet zero succ o.sym m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (binaryNet zero succ o.sym m n) nt).trace xsys σ i).2 = o.c m n ∧
      IsNum ((XMach.init (binaryNet zero succ o.sym m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f m n) := by
  have g := good_binaryNet (xsys := xsys) o.ar_eq o.ne0 o.ne1 m n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  have hn' := (normal_of_numerals hag : Normal (Step xsys.sys) _)
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (binaryNet zero succ o.sym m n) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (binaryNet zero succ o.sym m n) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **An operator of two arguments, alone, under any fair schedule.** -/
theorem Op2.fair (o : Op2 xsys) (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (binaryNet zero succ o.sym m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (binaryNet zero succ o.sym m n) nt).trace xsys σ i).2 = o.c m n ∧
      IsNum ((XMach.init (binaryNet zero succ o.sym m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f m n) := by
  have g := good_binaryNet (xsys := xsys) o.ar_eq o.ne0 o.ne1 m n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs ((normal_of_numerals hag : Normal (Step xsys.sys) _))
    σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- **An operator of one argument, alone on the machine.** -/
theorem Op1.rest (o : Op1 xsys) (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (unaryNet zero succ o.sym n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (unaryNet zero succ o.sym n) nt).trace xsys σ i).2 = o.c n ∧
      IsNum ((XMach.init (unaryNet zero succ o.sym n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f n) := by
  have g := good_unaryNet (xsys := xsys) o.ar_eq o.ne1 n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  have hn' := (normal_of_numerals hag : Normal (Step xsys.sys) _)
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (unaryNet zero succ o.sym n) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (unaryNet zero succ o.sym n) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **An operator of one argument, alone, under any fair schedule.** -/
theorem Op1.fair (o : Op1 xsys) (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (unaryNet zero succ o.sym n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (unaryNet zero succ o.sym n) nt).trace xsys σ i).2 = o.c n ∧
      IsNum ((XMach.init (unaryNet zero succ o.sym n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f n) := by
  have g := good_unaryNet (xsys := xsys) o.ar_eq o.ne1 n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs ((normal_of_numerals hag : Normal (Step xsys.sys) _))
    σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum


end Core

namespace Peano

open Core

/-- **The rules of `Peano` give every new agent a side.** -/
theorem system_sided : system.Sided := by
  intro α β R hR j
  cases α <;> cases β <;> cases hR <;> rfl

/-- A net of `Peano` that computes a number. -/
abbrev Evals (N : Net Peano) (s v : Nat) (p : Port) : Prop := Core.Evals xsys N s v p

/-- Expressions over operators of `Peano`. -/
abbrev GExpr := Core.GExpr xsys

/-- Operators of `Peano`. -/
abbrev Op1 := Core.Op1 xsys
abbrev Op2 := Core.Op2 xsys

/-- A numeral of `Peano`. -/
abbrev lit (n : Nat) : XNet Peano := Core.lit zero succ n

/-- **The adder is an operator**, by its own theorem. -/
def addOp : Op2 :=
  ⟨add, fun m n => m + n, fun m _ => m + 1, rfl, by decide, by decide,
    fun u => add_steps' rules ⟨u.wf, u.ha, u.fst, u.snd, u.out, u.free, u.only⟩⟩

/-- The multiplier, through the theorem on recursion. -/
def mulOp : Op2 := Op2.ofComputes mul_computes rfl (by decide) (by decide)

/-- The power, through the theorem on recursion: the first argument is
the exponent. -/
def powOp : Op2 := Op2.ofComputes pow_computes rfl (by decide) (by decide)

/-- The factorial, through the theorem on recursion. -/
def facOp : Op1 := Op1.ofComputes fac_computes rfl (by decide) (by decide)

/-- **Addition on the machine**, as a case: a run on the net for `m + n`
that is at rest has made exactly `m + 1` interactions and holds
`m + n`. -/
theorem sum_rest (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (binaryNet add m n) nt).trace xsys σ i).2 = m + 1 ∧
      IsNum ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (m + n) :=
  addOp.rest m n hnt σ hr

/-- **Addition under any fair schedule**, as a case. -/
theorem sum_fair (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (binaryNet add m n) nt).trace xsys σ i).2 = m + 1 ∧
      IsNum ((XMach.init (binaryNet add m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (m + n) :=
  addOp.fair m n hnt σ hfair

end Peano

end INet
