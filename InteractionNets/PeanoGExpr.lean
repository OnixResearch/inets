import InteractionNets.PeanoRun
import InteractionNets.PeanoExpr

/-! # Expressions over any operators that compute

The expressions of `PeanoExpr` have three operators, `+`, `*` and `^`,
each with a lemma of its own.  Here an operator is data
(`Peano.Op1`, `Peano.Op2`): a symbol, the function it computes, its cost,
and the proof that, alone with numerals as arguments, it reduces in that
many steps to the numeral of the value.  Any agent that computes
(`Peano.Computes1`, `Peano.Computes2`) gives one (`Peano.Op1.ofComputes`,
`Peano.Op2.ofComputes`), and so does the adder (`Peano.addOp`).

Expressions (`Peano.GExpr`) are numerals and operators of one or two
arguments applied to expressions.  Every expression has a net, which is
well formed and computes the value in exactly `GExpr.cost` interactions
(`GExpr.good`); on the machine, with any number of threads and any
schedule, a run at rest has made that many interactions and holds the
value (`GExpr.rest`), and a fair run comes to rest (`GExpr.fair`); the
expression can be run and its result read (`GExpr.run_sound`,
`GExpr.run_complete`).

An operator of one argument waits on its argument as one of two
arguments does (`Peano.op_setup1`), with an empty net in the middle
place.  The expressions of `PeanoExpr` are a case, with the same nets,
values and costs (`Peano.PExpr.toG`).  The factorial and the lazy caterer
are operators (`Peano.facOp`, `Peano.caterOp`), so `3! + c 2` is an
expression.

The theorems for the machine on a single operator are also stated for
the operators (`Peano.Op2.rest`, `Peano.Op1.rest`), which brings in the
adder, whose result is not made of new agents only and which is not a
case of `Peano.binary_rest`.
-/

namespace INet

open Arith (tagPort tagPort_inj tagPort_snoc snoc_inj tag_ne)

namespace Peano

variable {N : Net Peano} {r : Port}

/-! ### Operators -/

/-- **An operator of one argument**: a symbol, the function it computes
and its cost; alone with a numeral as argument, the agent reduces in the
cost to the numeral of the value, in a net of successors and zeros. -/
structure Op1 where
  sym : Peano
  f : Nat → Nat
  c : Nat → Nat
  ar_eq : ar sym = 1
  ne0 : zero ≠ sym
  ne1 : succ ≠ sym
  steps : ∀ {N : Net Peano} {a : Id} {n : Nat} {r : Port}, Unary sym N a n r →
    ∃ N', Steps (Step system) (c n) N N' ∧ IsNum N' r (f n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ

/-- **An operator of two arguments**, the same with two numerals. -/
structure Op2 where
  sym : Peano
  f : Nat → Nat → Nat
  c : Nat → Nat → Nat
  ar_eq : ar sym = 2
  ne0 : zero ≠ sym
  ne1 : succ ≠ sym
  steps : ∀ {N : Net Peano} {a : Id} {m n : Nat} {r : Port}, Binary sym N a m n r →
    ∃ N', Steps (Step system) (c m n) N N' ∧ IsNum N' r (f m n) ∧
      ∀ i γ, N'.agent i γ → γ = zero ∨ γ = succ

/-- What is left of an agent that computes: the numeral and the
numerals. -/
theorem unary_steps {op : Peano} {f c : Nat → Nat} (H : Computes1 op f c) {a : Id} {n : Nat}
    (u : Unary op N a n r) :
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
theorem binary_steps {op : Peano} {f c : Nat → Nat → Nat} (H : Computes2 op f c) {a : Id}
    {m n : Nat} (u : Binary op N a m n r) :
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
def Op1.ofComputes {op : Peano} {f c : Nat → Nat} (H : Computes1 op f c) (h : ar op = 1)
    (h0 : zero ≠ op) (h1 : succ ≠ op) : Op1 :=
  ⟨op, f, c, h, h0, h1, fun u => unary_steps H u⟩

/-- **An agent of two arguments that computes is an operator.** -/
def Op2.ofComputes {op : Peano} {f c : Nat → Nat → Nat} (H : Computes2 op f c)
    (h : ar op = 2) (h0 : zero ≠ op) (h1 : succ ≠ op) : Op2 :=
  ⟨op, f, c, h, h0, h1, fun u => binary_steps H u⟩

/-- **The adder is an operator**, by its own theorem. -/
def addOp : Op2 :=
  ⟨add, fun m n => m + n, fun m _ => m + 1, rfl, by decide, by decide,
    fun u => add_steps' ⟨u.wf, u.ha, u.fst, u.snd, u.out, u.free, u.only⟩⟩

/-- The multiplier, through the theorem on recursion. -/
def mulOp : Op2 := Op2.ofComputes mul_computes' rfl (by decide) (by decide)

/-- The power, through the theorem on recursion: the first argument is
the exponent. -/
def powOp : Op2 := Op2.ofComputes pow_computes' rfl (by decide) (by decide)

/-- The factorial, through the theorem on recursion. -/
def facOp : Op1 := Op1.ofComputes fac_computes' rfl (by decide) (by decide)

/-- The lazy caterer, through the theorem on recursion. -/
def caterOp : Op1 := Op1.ofComputes cater_computes rfl (by decide) (by decide)

/-! ### An operator of one argument on a net that computes -/

/-- **An operator of one argument waiting for it**: the only agent `d` of
the net, with the symbol `op`, has its argument on the free port `q₁` and
its result on the free port `r`. -/
structure OpenOp1 (N : Net Peano) (op : Peano) (d : Id) (q₁ r : Port) : Prop where
  ha : N.agent d op
  only : ∀ i γ, N.agent i γ → i = d
  fst : N.Paired ar (d, 0) q₁
  out : N.Paired ar (d, 1) r
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
theorem op_setup1 {U : Net Peano} {P : Nat → Net Peano} (hU : U.WF ar) (hm : U.Made P)
    {cA cD : Nat} (hAD : cA ≠ cD) {op : Peano} {d : Id} {s v : Nat} {p₁ q₁ r : Port}
    (eA : Evals (P cA) s v p₁) (hD : OpenOp1 (P cD) op d q₁ r)
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
  obtain ⟨U₁, S1, hm₁⟩ := hm.steps system_sided sA
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
theorem op1_evals (o : Op1) {U : Net Peano} {P : Nat → Net Peano} (hU : U.WF ar)
    (hm : U.Made P) {cA cD : Nat} (hAD : cA ≠ cD) {d : Id} {s v : Nat} {p₁ q₁ r : Port}
    (eA : Evals (P cA) s v p₁) (hD : OpenOp1 (P cD) o.sym d q₁ r)
    (hO : ∀ c, c ≠ cA → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).WF ar ∧
      Evals (U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))) (s + o.c v) (o.f v)
        (tagPort cD r) := by
  obtain ⟨hW0, fr0, W, sts, hW, hd, h1, hout, hfr, honly⟩ := op_setup1 hU hm hAD eA hD hO
  obtain ⟨N', sts', hnum, hag⟩ := o.steps ⟨hW, hd, h1, hout, hfr, honly⟩
  exact ⟨hW0, fr0, N', sts.trans sts', hnum, hag⟩

/-- **An operator of two arguments on two nets that compute** computes
its function, in the steps of the two nets and its cost more. -/
theorem op2_evals (o : Op2) {U : Net Peano} {P : Nat → Net Peano} (hU : U.WF ar)
    (hm : U.Made P) {cA cB cD : Nat} (hAB : cA ≠ cB) (hAD : cA ≠ cD) (hBD : cB ≠ cD)
    {d : Id} {s₁ v₁ s₂ v₂ : Nat} {p₁ p₂ q₁ q₂ r : Port}
    (eA : Evals (P cA) s₁ v₁ p₁) (eB : Evals (P cB) s₂ v₂ p₂)
    (hD : OpenOp (P cD) o.sym d q₁ q₂ r)
    (hO : ∀ c, c ≠ cA → c ≠ cB → c ≠ cD → ∀ i γ, ¬ (P c).agent i γ) :
    ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
        (joinRel (tagPort cB p₂) (tagPort cD q₂))).WF ar ∧
      Evals ((U.plug (joinRel (tagPort cA p₁) (tagPort cD q₁))).plug
          (joinRel (tagPort cB p₂) (tagPort cD q₂)))
        (s₁ + s₂ + o.c v₁ v₂) (o.f v₁ v₂) (tagPort cD r) := by
  obtain ⟨hW0, fr0, W, sts, hW, hd, h1, h2, hout, hfr, honly⟩ :=
    op_setup hU hm hAB hAD hBD eA eB hD hO
  obtain ⟨N', sts', hnum, hag⟩ := o.steps ⟨hW, hd, h1, h2, hout, hfr, honly⟩
  exact ⟨hW0, fr0, N', sts.trans sts', hnum, hag⟩

/-! ### The nets -/

/-- The empty memory. -/
def emptyX : XNet Peano := XNet.ofWires [] [] []

theorem emptyX_ok : emptyX.Ok ar := by decide

theorem emptyX_none (i : Id) (γ : Peano) : ¬ emptyX.toNet.agent i γ :=
  fun h => List.not_mem_nil h

/-- **An operator of one argument waiting for it**, on the free port
`([2], 0)`, with its result on the free port `([0], 0)`. -/
def openOp1 (γ : Peano) : XNet Peano :=
  XNet.ofWires [([1], γ)] [([0], 0), ([2], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([0], 0))]

theorem openOp1_ok {γ : Peano} (h : ar γ = 1) : (openOp1 γ).Ok ar := by
  cases γ
  all_goals first
    | exact absurd h (by decide)
    | decide

theorem openOp1_spec {γ : Peano} (h : ar γ = 1) :
    OpenOp1 (openOp1 γ).toNet γ [1] ([2], 0) ([0], 0) := by
  have hX := openOp1_ok h
  have ew : (openOp1 γ).wires = (openOp1 fac).wires := rfl
  have ef : (openOp1 γ).free = (openOp1 fac).free := rfl
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

/-- The net of an operator of one argument on a net: the net, the empty
memory and the operator that waits, side by side under the tags `0`, `1`
and `2`, with the result port of the net wired to the argument of the
operator. -/
def opNet1 (γ : Peano) (X : XNet Peano) (p : Port) : XNet Peano :=
  (XNet.three X emptyX (openOp1 γ)).plug2 (tagPort 0 p) ([2, 2], 0)

theorem opNet1_toNet (γ : Peano) (X : XNet Peano) (p : Port) :
    (opNet1 γ X p).toNet =
      (XNet.three X emptyX (openOp1 γ)).toNet.plug
        (joinRel (tagPort 0 p) (tagPort 2 ([2], 0))) := by
  show (XNet.plug2 _ _ _).toNet = _
  rw [XNet.plug2_toNet]
  rfl

/-- An operator of two arguments that waits is valid for every symbol of
two arguments. -/
theorem openOp_ok {γ : Peano} (h : ar γ = 2) : (openOp γ).Ok ar := by
  cases γ
  all_goals first
    | exact absurd h (by decide)
    | decide

theorem openOp_spec {γ : Peano} (h : ar γ = 2) :
    OpenOp (openOp γ).toNet γ [1] ([2], 0) ([3], 0) ([0], 0) := by
  have hX := openOp_ok h
  have ew : (openOp γ).wires = (openOp mul).wires := rfl
  have ef : (openOp γ).free = (openOp mul).free := rfl
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

theorem parts3_none1 {A D : Net Peano} : ∀ c, c ≠ 0 → c ≠ 2 → ∀ i γ,
    ¬ (parts3 A emptyX.toNet D c).agent i γ
  | 0, h, _, _, _ => absurd rfl h
  | 1, _, _, i, γ => emptyX_none i γ
  | 2, _, h, _, _ => absurd rfl h
  | c + 3, _, _, _, _ => fun h => by
    rw [parts3_rest] at h
    exact h

/-! ### Expressions -/

/-- **Expressions over any operators**: numerals, and operators of one
or two arguments applied to expressions. -/
inductive GExpr
  | lit (n : Nat)
  | app1 (o : Op1) (e : GExpr)
  | app2 (o : Op2) (e₁ e₂ : GExpr)

/-- The value of an expression. -/
def GExpr.eval : GExpr → Nat
  | .lit n => n
  | .app1 o e => o.f e.eval
  | .app2 o e₁ e₂ => o.f e₁.eval e₂.eval

/-- The interactions of an expression: for each operator, its cost on
the values of its arguments. -/
def GExpr.cost : GExpr → Nat
  | .lit _ => 0
  | .app1 o e => e.cost + o.c e.eval
  | .app2 o e₁ e₂ => e₁.cost + e₂.cost + o.c e₁.eval e₂.eval

/-- The free port that carries the result. -/
def GExpr.res : GExpr → Port
  | .lit _ => ([0], 0)
  | .app1 _ _ => ([0, 2], 0)
  | .app2 _ _ _ => ([0, 2], 0)

/-- **The net of an expression.**  A numeral is its net; an operator is
the nets of its arguments and the operator that waits, side by side,
with the result of each argument wired to a port of the operator. -/
def GExpr.net : GExpr → XNet Peano
  | .lit n => Peano.lit n
  | .app1 o e => opNet1 o.sym e.net e.res
  | .app2 o e₁ e₂ => opNet o.sym e₁.net e₂.net e₁.res e₂.res

/-- **The net of an expression is well formed and computes its value**,
in the interactions counted by `GExpr.cost`. -/
theorem GExpr.good : ∀ e : GExpr, e.net.toNet.WF ar ∧ Evals e.net.toNet e.cost e.eval e.res
  | .lit n =>
    ⟨(good_lit n).ok.1, (good_lit n).free, (Peano.lit n).toNet, .refl _, (good_lit n).num,
      (good_lit n).only⟩
  | .app1 o e => by
    obtain ⟨w, ev⟩ := GExpr.good e
    have hm := XNet.three_made e.net emptyX (openOp1 o.sym)
    have hP := parts3_wf w emptyX_ok.1 (openOp1_ok o.ar_eq).1
    show (opNet1 o.sym e.net e.res).toNet.WF ar ∧
      Evals (opNet1 o.sym e.net e.res).toNet (e.cost + o.c e.eval) (o.f e.eval)
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
      Evals (opNet o.sym e₁.net e₂.net e₁.res e₂.res).toNet
        (e₁.cost + e₂.cost + o.c e₁.eval e₂.eval) (o.f e₁.eval e₂.eval) (tagPort 2 ([0], 0))
    rw [opNet_toNet]
    exact op2_evals o (hm.wf hP) hm (cA := 0) (cB := 1) (cD := 2) (by decide) (by decide)
      (by decide) ev₁ ev₂ (openOp_spec o.ar_eq) parts3_none

/-- **Every expression comes out right, whatever the threads do.**  With
any number of threads and any schedule, a run on the net of an expression
that is at rest has made the interactions counted by `GExpr.cost`, and
the memory has the numeral of the value on the free port. -/
theorem GExpr.rest (e : GExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
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

/-- **Every expression under a fair schedule.** -/
theorem GExpr.fair (e : GExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) hX hnt hs (normal_of_numerals hag) σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hA

/-- **Run an expression.** -/
def GExpr.run (e : GExpr) (nt steps : Nat) : Option Nat :=
  XNet.runRead xsys zero succ e.net e.res nt steps

/-- **Whatever the run returns is the value of the expression.** -/
theorem GExpr.run_sound (e : GExpr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.run nt steps = some v) : v = e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  exact XNet.runRead_sound (zero := zero) (succ := succ) xsys (by decide) (Nat.le_refl 1) hX hs
    (normal_of_numerals hag) hA hnt h

/-- **Given enough actions, the run returns the value of the
expression.** -/
theorem GExpr.run_complete (e : GExpr) {nt : Nat} (hnt : 0 < nt) :
    ∃ s₀, ∀ s, s₀ ≤ s → e.run nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  exact XNet.runRead_complete (zero := zero) (succ := succ) xsys (by decide) hX hs
    (normal_of_numerals hag) hA hnt

/-! ### The expressions of `PeanoExpr` are a case -/

/-- An expression of `+`, `*` and `^` as an expression over operators;
for a power the exponent is the first argument. -/
def PExpr.toG : PExpr → GExpr
  | .lit n => .lit n
  | .add e₁ e₂ => .app2 addOp e₁.toG e₂.toG
  | .mul e₁ e₂ => .app2 mulOp e₁.toG e₂.toG
  | .pow b e => .app2 powOp e.toG b.toG

theorem PExpr.toG_eval : ∀ e : PExpr, e.toG.eval = e.eval
  | .lit _ => rfl
  | .add e₁ e₂ => by
    show e₁.toG.eval + e₂.toG.eval = e₁.eval + e₂.eval
    rw [e₁.toG_eval, e₂.toG_eval]
  | .mul e₁ e₂ => by
    show e₁.toG.eval * e₂.toG.eval = e₁.eval * e₂.eval
    rw [e₁.toG_eval, e₂.toG_eval]
  | .pow b e => by
    show b.toG.eval ^ e.toG.eval = b.eval ^ e.eval
    rw [b.toG_eval, e.toG_eval]

theorem PExpr.toG_cost : ∀ e : PExpr, e.toG.cost = e.cost
  | .lit _ => rfl
  | .add e₁ e₂ => by
    show e₁.toG.cost + e₂.toG.cost + (e₁.toG.eval + 1) = e₁.cost + e₂.cost + (e₁.eval + 1)
    rw [e₁.toG_cost, e₂.toG_cost, e₁.toG_eval]
  | .mul e₁ e₂ => by
    show e₁.toG.cost + e₂.toG.cost + prodCost e₁.toG.eval e₂.toG.eval =
      e₁.cost + e₂.cost + prodCost e₁.eval e₂.eval
    rw [e₁.toG_cost, e₂.toG_cost, e₁.toG_eval, e₂.toG_eval]
  | .pow b e => by
    show e.toG.cost + b.toG.cost + powCost e.toG.eval b.toG.eval =
      e.cost + b.cost + powCost e.eval b.eval
    rw [e.toG_cost, b.toG_cost, e.toG_eval, b.toG_eval]

theorem PExpr.toG_res : ∀ e : PExpr, e.toG.res = e.res
  | .lit _ => rfl
  | .add _ _ => rfl
  | .mul _ _ => rfl
  | .pow _ _ => rfl

/-- **The same nets.** -/
theorem PExpr.toG_net : ∀ e : PExpr, e.toG.net = e.net
  | .lit _ => rfl
  | .add e₁ e₂ => by
    show opNet Peano.add e₁.toG.net e₂.toG.net e₁.toG.res e₂.toG.res =
      opNet Peano.add e₁.net e₂.net e₁.res e₂.res
    rw [e₁.toG_net, e₂.toG_net, e₁.toG_res, e₂.toG_res]
  | .mul e₁ e₂ => by
    show opNet Peano.mul e₁.toG.net e₂.toG.net e₁.toG.res e₂.toG.res =
      opNet Peano.mul e₁.net e₂.net e₁.res e₂.res
    rw [e₁.toG_net, e₂.toG_net, e₁.toG_res, e₂.toG_res]
  | .pow b e => by
    show opNet Peano.pow e.toG.net b.toG.net e.toG.res b.toG.res =
      opNet Peano.pow e.net b.net e.res b.res
    rw [e.toG_net, b.toG_net, e.toG_res, b.toG_res]

/-- **The expressions of `+`, `*` and `^` on the machine**, as a case. -/
theorem PExpr.rest' (e : PExpr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  rw [← e.toG_net] at hr ⊢
  rw [← e.toG_cost, ← e.toG_res, ← e.toG_eval]
  exact e.toG.rest hnt σ hr

/-! ### Examples -/

/-- `3! + c 2` has the value `10` and costs `70` interactions: `52` for
the factorial, `11` for the caterer and `7` for the addition. -/
example : (GExpr.app2 addOp (.app1 facOp (.lit 3)) (.app1 caterOp (.lit 2))).eval = 10 ∧
    (GExpr.app2 addOp (.app1 facOp (.lit 3)) (.app1 caterOp (.lit 2))).cost = 70 := by
  decide

set_option maxRecDepth 100000 in
/-- `c 2 + 2!` run by two threads taking turns: after 2500 actions they
are at rest and the result read is `6`. -/
example : (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).run 2 2500 =
    some 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same on the machine: after 2500 actions both threads are at rest
and they have made 41 interactions, the cost of the expression. -/
example :
    ((XMach.init (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).net 2).trace
      xsys (fun j => j % 2) 2500).1.resting = true ∧
    ((XMach.init (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).net 2).trace
      xsys (fun j => j % 2) 2500).2 = 41 ∧
    (GExpr.app2 addOp (.app1 caterOp (.lit 2)) (.app1 facOp (.lit 2))).cost = 41 := by
  decide +kernel

/-! ### One operator on the machine -/

/-- **An operator of two arguments, alone on the machine**: on the net
`Peano.binaryNet o.sym m n`, with any number of threads and any
schedule, a run at rest has made exactly `o.c m n` interactions and
holds `o.f m n`. -/
theorem Op2.rest (o : Op2) (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (binaryNet o.sym m n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (binaryNet o.sym m n) nt).trace xsys σ i).2 = o.c m n ∧
      IsNum ((XMach.init (binaryNet o.sym m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f m n) := by
  have g := good_binaryNet o.ar_eq o.ne0 o.ne1 m n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  have hn' := normal_of_numerals hag
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (binaryNet o.sym m n) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (binaryNet o.sym m n) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **An operator of two arguments, alone, under any fair schedule.** -/
theorem Op2.fair (o : Op2) (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (binaryNet o.sym m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (binaryNet o.sym m n) nt).trace xsys σ i).2 = o.c m n ∧
      IsNum ((XMach.init (binaryNet o.sym m n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f m n) := by
  have g := good_binaryNet o.ar_eq o.ne0 o.ne1 m n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs (normal_of_numerals hag)
    σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- **An operator of one argument, alone on the machine.** -/
theorem Op1.rest (o : Op1) (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (unaryNet o.sym n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (unaryNet o.sym n) nt).trace xsys σ i).2 = o.c n ∧
      IsNum ((XMach.init (unaryNet o.sym n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f n) := by
  have g := good_unaryNet o.ar_eq o.ne1 n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  have hn' := normal_of_numerals hag
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have rn := XMach.trace_run xsys σ (XMach.init (unaryNet o.sym n) nt) i
  rw [XMach.init_toMach] at rn
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 rn q hn
  obtain ⟨e₁, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (unaryNet o.sym n) nt).trace xsys σ i).1.mem.toNet := e₁
  refine ⟨ek.symm, ?_⟩
  rw [← e']
  exact hnum

/-- **An operator of one argument, alone, under any fair schedule.** -/
theorem Op1.fair (o : Op1) (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (unaryNet o.sym n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (unaryNet o.sym n) nt).trace xsys σ i).2 = o.c n ∧
      IsNum ((XMach.init (unaryNet o.sym n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (o.f n) := by
  have g := good_unaryNet o.ar_eq o.ne1 n
  obtain ⟨N', hs, hnum, hag⟩ := o.steps g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs (normal_of_numerals hag)
    σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

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
