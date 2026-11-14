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
(`Expr.run_sound`).
-/

namespace INet

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

/-- **Read the numeral on a port**, following wires of any number of
segments.  The first number bounds the length of the numeral. -/
def readNum (X : XNet Arith) : Nat → Port → Option Nat
  | 0, _ => none
  | fuel + 1, p =>
    match assoc p X.wires with
    | none => none
    | some c =>
      match followTo X (X.wires.length + 1) p c with
      | none => none
      | some i =>
        match assoc i X.agents with
        | some Arith.zero => some 0
        | some Arith.succ => (readNum X fuel (i, 1)).map (· + 1)
        | _ => none

/-- **What `readNum` returns is a numeral of the net.** -/
theorem readNum_sound {X : XNet Arith} (hX : X.toNet.WF ar) :
    ∀ (fuel : Nat) (p : Port) (k : Nat), X.toNet.End ar p → readNum X fuel p = some k →
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
      cases hf : followTo X (X.wires.length + 1) p c with
      | none =>
        rw [hf] at h
        cases h
      | some i =>
        rw [hf] at h
        dsimp only at h
        obtain ⟨⟨x, w⟩, -⟩ := followTo_sound hX _ p c i (assoc_mem hc) hf
        have hconn : X.toNet.Conn ar p (i, 0) := ⟨c, x, w⟩
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
            cases hr : readNum X fuel (i, 1) with
            | none =>
              rw [hr] at h
              cases h
            | some k' =>
              rw [hr] at h
              have ek : k' + 1 = k := Option.some.inj h
              rw [← ek]
              obtain ⟨j, hpj, hnj⟩ := readNum_sound hX fuel (i, 1) k'
                (.inr ⟨succ, hi, Nat.le_refl 1⟩) hr
              exact ⟨i, ⟨hp, hE, hconn⟩, hi, j, hpj, hnj⟩
          | add => cases h

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
    readNum ((XMach.init e.net nt).trace xsys (fun j => j % nt) steps).1.mem
      (((XMach.init e.net nt).trace xsys (fun j => j % nt) steps).1.mem.agents.length + 1) e.res
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
    exact IsNum.unique hW (readNum_sound hW _ _ _ hE h) hnum
  · rw [ite_neg' hr] at h
    cases h

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
