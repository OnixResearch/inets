import InteractionNets.Arith.Expr

/-! # Running an expression and reading the result

The memories that the nets of expressions leave have wires of several
segments, which `readNat` does not follow.  `readNum` does: it goes along
the wire from a port as a thread does, to the principal port of an agent,
and reads the numeral there.  Whatever it returns is a numeral of the net
(`readNum_sound`), and a port carries at most one numeral
(`IsNum.unique`).

`Expr.run` lets a number of threads take turns on the net of an
expression for a number of actions and, if they are then at rest, reads
the result.  Whatever it returns is the value of the expression
(`Expr.run_sound`), and given enough actions it returns the value
(`Expr.run_complete`).
-/

namespace INet

/-- Once at rest, the program does not change. -/
theorem XMach.trace_rest_eq {S : Type} [DecidableEq S] {xs : XSys S} (σ : Nat → Nat)
    {M : XMach S} {i : Nat} (h : (M.trace xs σ i).1.resting = true) :
    ∀ d, (M.trace xs σ (i + d)).1 = (M.trace xs σ i).1
  | 0 => rfl
  | d + 1 => by
    have ih := XMach.trace_rest_eq σ h d
    have hr := XMach.resting_trace σ h d
    show ((M.trace xs σ (i + d)).1.step xs (σ (i + d))).1 = _
    rw [XMach.resting_step hr]
    exact ih

namespace Arith

/-! ### A port carries at most one numeral -/

theorem Num.unique {N : Net Arith} (hN : N.WF ar) :
    ∀ {k k' : Nat} {i : Id}, Num N i k → Num N i k' → k = k'
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, _, hz, ⟨hs, _⟩ => absurd (hN.agent_fun hz hs) (by decide)
  | _ + 1, 0, _, ⟨hs, _⟩, hz => absurd (hN.agent_fun hz hs) (by decide)
  | k + 1, k' + 1, _, ⟨_, j, hp, hn⟩, ⟨_, j', hp', hn'⟩ => by
    have e : ((j, 0) : Port) = (j', 0) := Net.Conn.det hN hp.1 hp.2.1 hp'.2.1 hp.2.2 hp'.2.2
    have ej : j = j' := congrArg Prod.fst e
    rw [← ej] at hn'
    rw [Num.unique hN hn hn']

/-- **A port carries at most one numeral.** -/
theorem IsNum.unique {N : Net Arith} (hN : N.WF ar) {p : Port} {k k' : Nat}
    (h : IsNum N p k) (h' : IsNum N p k') : k = k' := by
  obtain ⟨i, hp, hn⟩ := h
  obtain ⟨i', hp', hn'⟩ := h'
  have e : ((i, 0) : Port) = (i', 0) := Net.Conn.det hN hp.1 hp.2.1 hp'.2.1 hp.2.2 hp'.2.2
  have ei : i = i' := congrArg Prod.fst e
  rw [← ei] at hn'
  exact Num.unique hN hn hn'

/-! ### Reading a numeral along wires of several segments -/

/-- Go along the wire that came from `p` into `c`, as a thread does, to
the principal port of an agent. -/
def followTo (X : XNet Arith) : Nat → Port → Port → Option Id
  | 0, _, _ => none
  | fuel + 1, p, c =>
    match (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some _ => some c.1
    | none =>
      match nextSeg X.wires c p with
      | some q => followTo X fuel c q
      | none => none

/-- Where `followTo` stops is the other end of the wire, and an agent. -/
theorem followTo_sound {X : XNet Arith} (hX : X.toNet.WF ar) :
    ∀ (fuel : Nat) (p c : Port) (i : Id), (p, c) ∈ X.wires → followTo X fuel p c = some i →
      (∃ x, Walk X.toNet.link (X.toNet.End ar) p c x (i, 0)) ∧ ∃ γ, (i, γ) ∈ X.agents
  | 0, _, _, _, _, h => by cases h
  | fuel + 1, p, c, i, hl, h => by
    unfold followTo at h
    cases hc : (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some γ =>
      rw [hc] at h
      have ei : c.1 = i := Option.some.inj h
      have h0 : c.2 = 0 ∧ assoc c.1 X.agents = some γ := by
        split at hc
        · rename_i h0
          exact ⟨h0, hc⟩
        · cases hc
      have ec : c = (i, 0) := Prod.ext ei h0.1
      rw [ec] at hl
      rw [ec]
      refine ⟨⟨p, .single hl⟩, γ, ?_⟩
      rw [← ei]
      exact assoc_mem h0.2
    | none =>
      rw [hc] at h
      cases hq : nextSeg X.wires c p with
      | none =>
        rw [hq] at h
        cases h
      | some q =>
        rw [hq] at h
        obtain ⟨hcq, hne⟩ := nextSeg_spec hq
        obtain ⟨⟨x, w⟩, hγ⟩ := followTo_sound hX fuel c q i hcq h
        have hnE : ¬ X.toNet.End ar c := fun hE =>
          hne (hX.end_unique hE hcq (hX.symm hl))
        exact ⟨⟨x, .cons hl hnE hne w⟩, hγ⟩

/-- More fuel does not change where `followTo` stops. -/
theorem followTo_mono {X : XNet Arith} : ∀ {f f' : Nat} {p c : Port} {i : Id},
    followTo X f p c = some i → f ≤ f' → followTo X f' p c = some i
  | 0, _, _, _, _, h, _ => by cases h
  | f + 1, f', p, c, i, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    unfold followTo at h ⊢
    cases hc : (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some γ =>
      rw [hc] at h
      exact h
    | none =>
      rw [hc] at h
      cases hq : nextSeg X.wires c p with
      | none =>
        rw [hq] at h
        cases h
      | some q =>
        rw [hq] at h
        exact followTo_mono (f := f) (f' := g) h (by omega)

theorem followTo_complete_aux {X : XNet Arith} (hX : X.toNet.WF ar) {p c x y : Port}
    (w : Walk X.toNet.link (X.toNet.End ar) p c x y) :
    ∀ {i : Id} {γ : Arith}, y = (i, 0) → (i, γ) ∈ X.agents → ∃ f, followTo X f p c = some i := by
  induction w with
  | @single u v h =>
    intro i γ e hi
    obtain ⟨γ', hγ'⟩ := assoc_of_mem hi
    refine ⟨1, ?_⟩
    rw [e]
    unfold followTo
    have h1 : (if ((i, 0) : Port).2 = 0 then assoc ((i, 0) : Port).1 X.agents else none) =
        some γ' := by
      rw [ite_pos' rfl]
      exact hγ'
    rw [h1]
  | @cons u v w' x y h hT hne w ih =>
    intro i γ e hi
    obtain ⟨f, hf⟩ := ih e hi
    have h₁ : (if v.2 = 0 then assoc v.1 X.agents else none) = none := by
      split
      · rename_i hv
        cases ha : assoc v.1 X.agents with
        | none => rfl
        | some β =>
          exact absurd (.inr ⟨β, assoc_mem ha, by rw [hv]; exact Nat.zero_le _⟩) hT
      · rfl
    have h₂ : nextSeg X.wires v u = some w' := by
      refine nextSeg_some w.link_first hne fun q hq hqu => ?_
      rcases hX.deg (hX.symm h) w.link_first hq with e | e | e
      · exact absurd e.symm hne
      · exact absurd e.symm hqu
      · exact e.symm
    refine ⟨f + 1, ?_⟩
    unfold followTo
    rw [h₁, h₂]
    exact hf

/-- `followTo` reaches the agent at the other end of a wire, given enough
fuel. -/
theorem followTo_complete {X : XNet Arith} (hX : X.toNet.WF ar) {p c x : Port} {i : Id}
    (w : Walk X.toNet.link (X.toNet.End ar) p c x (i, 0)) {γ : Arith} (hi : (i, γ) ∈ X.agents) :
    ∃ f, followTo X f p c = some i :=
  followTo_complete_aux hX w rfl hi

/-- **Read the numeral on a port**, following wires of any number of
segments.  The first number bounds the segments of a wire, the second
the length of the numeral. -/
def readNum (X : XNet Arith) (w : Nat) : Nat → Port → Option Nat
  | 0, _ => none
  | fuel + 1, p =>
    match assoc p X.wires with
    | none => none
    | some c =>
      match followTo X w p c with
      | none => none
      | some i =>
        match assoc i X.agents with
        | some Arith.zero => some 0
        | some Arith.succ => (readNum X w fuel (i, 1)).map (· + 1)
        | _ => none

/-- **What `readNum` returns is a numeral of the net.** -/
theorem readNum_sound {X : XNet Arith} (hX : X.toNet.WF ar) (w : Nat) :
    ∀ (fuel : Nat) (p : Port) (k : Nat), X.toNet.End ar p → readNum X w fuel p = some k →
      IsNum X.toNet p k
  | 0, _, _, _, h => by cases h
  | fuel + 1, p, k, hp, h => by
    unfold readNum at h
    cases hc : assoc p X.wires with
    | none =>
      rw [hc] at h
      cases h
    | some c =>
      rw [hc] at h
      dsimp only at h
      cases hf : followTo X w p c with
      | none =>
        rw [hf] at h
        cases h
      | some i =>
        rw [hf] at h
        dsimp only at h
        obtain ⟨⟨x, wk⟩, -⟩ := followTo_sound hX _ p c i (assoc_mem hc) hf
        have hconn : X.toNet.Conn ar p (i, 0) := ⟨c, x, wk⟩
        cases ha : assoc i X.agents with
        | none =>
          rw [ha] at h
          cases h
        | some γ =>
          rw [ha] at h
          have hi : X.toNet.agent i γ := assoc_mem ha
          have hE : X.toNet.End ar (i, 0) := .inr ⟨γ, hi, Nat.zero_le _⟩
          cases γ with
          | zero =>
            have ek : 0 = k := Option.some.inj h
            rw [← ek]
            exact ⟨i, ⟨hp, hE, hconn⟩, hi⟩
          | succ =>
            cases hr : readNum X w fuel (i, 1) with
            | none =>
              rw [hr] at h
              cases h
            | some k' =>
              rw [hr] at h
              have ek : k' + 1 = k := Option.some.inj h
              rw [← ek]
              obtain ⟨j, hpj, hnj⟩ := readNum_sound hX w fuel (i, 1) k'
                (.inr ⟨succ, hi, Nat.le_refl 1⟩) hr
              exact ⟨i, ⟨hp, hE, hconn⟩, hi, j, hpj, hnj⟩
          | add => cases h

/-- More fuel does not change what `readNum` returns. -/
theorem readNum_mono {X : XNet Arith} {w w' : Nat} (hw : w ≤ w') :
    ∀ {f f' : Nat} {p : Port} {k : Nat},
      readNum X w f p = some k → f ≤ f' → readNum X w' f' p = some k
  | 0, _, _, _, h, _ => by cases h
  | f + 1, f', p, k, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    unfold readNum at h ⊢
    cases hc : assoc p X.wires with
    | none =>
      rw [hc] at h
      cases h
    | some c =>
      rw [hc] at h
      dsimp only at h ⊢
      cases hfo : followTo X w p c with
      | none =>
        rw [hfo] at h
        cases h
      | some i =>
        rw [hfo] at h
        rw [followTo_mono hfo hw]
        dsimp only at h ⊢
        cases ha : assoc i X.agents with
        | none =>
          rw [ha] at h
          cases h
        | some γ =>
          rw [ha] at h
          cases γ with
          | zero => exact h
          | succ =>
            cases hr : readNum X w f (i, 1) with
            | none =>
              rw [hr] at h
              cases h
            | some k' =>
              rw [hr] at h
              dsimp only at h ⊢
              rw [readNum_mono hw (f := f) (f' := g) hr (by omega)]
              exact h
          | add => cases h

/-- **`readNum` returns every numeral of the net**, given enough fuel. -/
theorem readNum_complete {X : XNet Arith} (hX : X.toNet.WF ar) :
    ∀ (k : Nat) (p : Port), IsNum X.toNet p k → ∃ w f, readNum X w f p = some k
  | 0, p, ⟨i, ⟨hp, _, v, x, wk⟩, hn⟩ => by
    have hv : assoc p X.wires = some v :=
      assoc_eq_of_unique wk.link_first fun q' hq' => hX.end_unique hp hq' wk.link_first
    have hz : (i, zero) ∈ X.agents := hn
    obtain ⟨f₁, hf₁⟩ := followTo_complete hX wk hz
    have ha : assoc i X.agents = some zero :=
      assoc_eq_of_unique hz fun α' h' => hX.agent_fun h' hz
    refine ⟨f₁, 1, ?_⟩
    unfold readNum
    rw [hv]
    dsimp only
    rw [hf₁]
    dsimp only
    rw [ha]
  | k + 1, p, ⟨i, ⟨hp, _, v, x, wk⟩, hs, j, hpj, hnj⟩ => by
    have hv : assoc p X.wires = some v :=
      assoc_eq_of_unique wk.link_first fun q' hq' => hX.end_unique hp hq' wk.link_first
    have hs' : (i, succ) ∈ X.agents := hs
    obtain ⟨f₁, hf₁⟩ := followTo_complete hX wk hs'
    have ha : assoc i X.agents = some succ :=
      assoc_eq_of_unique hs' fun α' h' => hX.agent_fun h' hs'
    obtain ⟨w₂, f₂, h₂⟩ := readNum_complete hX k (i, 1) ⟨j, hpj, hnj⟩
    refine ⟨max f₁ w₂, f₂ + 1, ?_⟩
    unfold readNum
    rw [hv]
    dsimp only
    rw [followTo_mono hf₁ (Nat.le_max_left _ _)]
    dsimp only
    rw [ha]
    dsimp only
    rw [readNum_mono (Nat.le_max_right _ _) h₂ (Nat.le_refl _)]
    rfl

/-! ### Running an expression -/

/-- At rest the memory holds a well-formed net. -/
theorem Expr.rest_wf (e : Expr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init e.net nt).trace xsys σ i).1.resting = true) :
    ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet.WF ar := by
  obtain ⟨hX, -, N', hs, -, hno⟩ := Expr.good e
  have hn' := normal_of_no_add hno
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init e.net nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e', -⟩ := (hu hs).2 hn'
  have e'' : N' = ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet := e'
  rw [← e'']
  exact Steps.wf hX hs

/-- **Run an expression.**  `nt` threads take turns on the net of the
expression for `steps` actions; if they are then at rest, the numeral on
the free port is read. -/
def Expr.run (e : Expr) (nt steps : Nat) : Option Nat :=
  if ((XMach.init e.net nt).trace xsys (fun j => j % nt) steps).1.resting = true then
    readNum ((XMach.init e.net nt).trace xsys (fun j => j % nt) steps).1.mem steps steps e.res
  else none

/-- **Whatever the run returns is the value of the expression.** -/
theorem Expr.run_sound (e : Expr) {nt steps v : Nat} (hnt : 0 < nt)
    (h : e.run nt steps = some v) : v = e.eval := by
  unfold Expr.run at h
  by_cases hr : ((XMach.init e.net nt).trace xsys (fun j => j % nt) steps).1.resting = true
  · rw [ite_pos' hr] at h
    have hW := Expr.rest_wf e hnt (fun j => j % nt) hr
    obtain ⟨-, hnum⟩ := Expr.rest e hnt (fun j => j % nt) hr
    have hE := hnum.choose_spec.1.1
    exact IsNum.unique hW (readNum_sound hW _ _ _ _ hE h) hnum
  · rw [ite_neg' hr] at h
    cases h

/-- **Given enough actions, the run returns the value of the
expression.**  Threads that take turns are scheduled fairly, so they come
to rest; from then on the memory does not change, and the numeral on the
free port is read. -/
theorem Expr.run_complete (e : Expr) {nt : Nat} (hnt : 0 < nt) :
    ∃ s₀, ∀ s, s₀ ≤ s → e.run nt s = some e.eval := by
  have hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j % nt = u := by
    intro u hu i
    refine ⟨u + i * nt, ?_, ?_⟩
    · have h1 := Nat.mul_le_mul_left i hnt
      rw [Nat.mul_one] at h1
      omega
    · rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hu
  obtain ⟨i₀, h⟩ := Expr.fair e hnt (fun j => j % nt) hfair
  obtain ⟨hr, -, hnum⟩ := h i₀ (Nat.le_refl _)
  have hW := Expr.rest_wf e hnt (fun j => j % nt) hr
  obtain ⟨w, f, hread⟩ := readNum_complete hW _ _ hnum
  refine ⟨i₀ + (w + f), fun s hs => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, s = i₀ + d := ⟨s - i₀, by omega⟩
  unfold Expr.run
  rw [ite_pos' (XMach.resting_trace _ hr d), XMach.trace_rest_eq _ hr d]
  exact readNum_mono (by omega) hread (by omega)

/-- `1 + 1` run by two threads taking turns: after 200 actions they are
at rest and the result read is `2`. -/
example : (Expr.add (.lit 1) (.lit 1)).run 2 200 = some 2 := by
  decide +kernel

/-- `(2 + 3) + (1 + 4)` run by three threads taking turns: after 700
actions they are at rest and the result read is `10`. -/
example : (Expr.add (.add (.lit 2) (.lit 3)) (.add (.lit 1) (.lit 4))).run 3 700 = some 10 := by
  decide +kernel

end Arith

end INet
