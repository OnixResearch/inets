import InteractionNets.Time
import InteractionNets.Addition

/-! # Running a memory and reading a numeral back

For any system with a zero and a successor.

A memory at rest may have wires of several segments, the junctions left
by the firings.  `XNet.followTo` goes along a wire to the agent at its
other end, as a thread does, and `XNet.readNum` reads the numeral on a
port.  What it returns is a numeral of the net (`XNet.readNum_sound`),
and with enough fuel it returns every numeral of the net
(`XNet.readNum_complete`).  A port carries at most one numeral
(`Addition.IsNum.unique`).

`XNet.runRead` runs the machine, its threads taking turns, for a number
of actions, and reads the numeral on a port if the threads are at rest.
When the net reduces to a normal form with the numeral `v` on that port,
whatever it returns is `v` (`XNet.runRead_sound`), and with enough
actions it does return `v` (`XNet.runRead_complete`).
-/

namespace INet

/-- A machine at rest stays as it is. -/
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

section Unique

variable {S : Type} {ar : S → Nat} {zero succ : S}

/-- An agent is the head of at most one numeral. -/
theorem Addition.Num.unique (hzs : zero ≠ succ) {N : Net S} (hN : N.WF ar) :
    ∀ {k k' : Nat} {i : Id}, Addition.Num ar zero succ N i k →
      Addition.Num ar zero succ N i k' → k = k'
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, _, hz, ⟨hs, _⟩ => absurd (hN.agent_fun hz hs) hzs
  | _ + 1, 0, _, ⟨hs, _⟩, hz => absurd (hN.agent_fun hz hs) hzs
  | k + 1, k' + 1, _, ⟨_, j, hp, hn⟩, ⟨_, j', hp', hn'⟩ => by
    have e : ((j, 0) : Port) = (j', 0) := Net.Conn.det hN hp.1 hp.2.1 hp'.2.1 hp.2.2 hp'.2.2
    have ej : j = j' := congrArg Prod.fst e
    rw [← ej] at hn'
    rw [Addition.Num.unique hzs hN hn hn']

/-- **A port carries at most one numeral.** -/
theorem Addition.IsNum.unique (hzs : zero ≠ succ) {N : Net S} (hN : N.WF ar) {p : Port}
    {k k' : Nat} (h : Addition.IsNum ar zero succ N p k)
    (h' : Addition.IsNum ar zero succ N p k') : k = k' := by
  obtain ⟨i, hp, hn⟩ := h
  obtain ⟨i', hp', hn'⟩ := h'
  have e : ((i, 0) : Port) = (i', 0) := Net.Conn.det hN hp.1 hp.2.1 hp'.2.1 hp.2.2 hp'.2.2
  have ei : i = i' := congrArg Prod.fst e
  rw [← ei] at hn'
  exact Addition.Num.unique hzs hN hn hn'

end Unique

section Read

variable {S : Type} [DecidableEq S] {ar : S → Nat} {zero succ : S}

/-! ### Reading a numeral along wires of several segments -/

/-- Go along the wire that came from `p` into `c`, as a thread does, to
the principal port of an agent. -/
def XNet.followTo (X : XNet S) : Nat → Port → Port → Option Id
  | 0, _, _ => none
  | fuel + 1, p, c =>
    match (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some _ => some c.1
    | none =>
      match nextSeg X.wires c p with
      | some q => XNet.followTo X fuel c q
      | none => none

omit [DecidableEq S] in
/-- Where `followTo` stops is the other end of the wire, and an agent. -/
theorem XNet.followTo_sound {X : XNet S} (hX : X.toNet.WF ar) :
    ∀ (fuel : Nat) (p c : Port) (i : Id), (p, c) ∈ X.wires → X.followTo fuel p c = some i →
      (∃ x, Walk X.toNet.link (X.toNet.End ar) p c x (i, 0)) ∧ ∃ γ, (i, γ) ∈ X.agents
  | 0, _, _, _, _, h => by cases h
  | fuel + 1, p, c, i, hl, h => by
    unfold XNet.followTo at h
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
        obtain ⟨⟨x, w⟩, hγ⟩ := XNet.followTo_sound hX fuel c q i hcq h
        have hnE : ¬ X.toNet.End ar c := fun hE =>
          hne (hX.end_unique hE hcq (hX.symm hl))
        exact ⟨⟨x, .cons hl hnE hne w⟩, hγ⟩

omit [DecidableEq S] in
/-- More fuel does not change where `followTo` stops. -/
theorem XNet.followTo_mono {X : XNet S} : ∀ {f f' : Nat} {p c : Port} {i : Id},
    X.followTo f p c = some i → f ≤ f' → X.followTo f' p c = some i
  | 0, _, _, _, _, h, _ => by cases h
  | f + 1, f', p, c, i, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    unfold XNet.followTo at h ⊢
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
        exact XNet.followTo_mono (f := f) (f' := g) h (by omega)

omit [DecidableEq S] in
theorem XNet.followTo_complete_aux {X : XNet S} (hX : X.toNet.WF ar) {p c x y : Port}
    (w : Walk X.toNet.link (X.toNet.End ar) p c x y) :
    ∀ {i : Id} {γ : S}, y = (i, 0) → (i, γ) ∈ X.agents → ∃ f, X.followTo f p c = some i := by
  induction w with
  | @single u v h =>
    intro i γ e hi
    obtain ⟨γ', hγ'⟩ := assoc_of_mem hi
    refine ⟨1, ?_⟩
    rw [e]
    unfold XNet.followTo
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
    unfold XNet.followTo
    rw [h₁, h₂]
    exact hf

omit [DecidableEq S] in
/-- `followTo` reaches the agent at the other end of a wire, given enough
fuel. -/
theorem XNet.followTo_complete {X : XNet S} (hX : X.toNet.WF ar) {p c x : Port} {i : Id}
    (w : Walk X.toNet.link (X.toNet.End ar) p c x (i, 0)) {γ : S} (hi : (i, γ) ∈ X.agents) :
    ∃ f, X.followTo f p c = some i :=
  XNet.followTo_complete_aux hX w rfl hi

/-- **Read the numeral on a port**, following wires of any number of
segments.  The first number bounds the segments of a wire, the second
the length of the numeral. -/
def XNet.readNum (X : XNet S) (zero succ : S) (w : Nat) : Nat → Port → Option Nat
  | 0, _ => none
  | fuel + 1, p =>
    match assoc p X.wires with
    | none => none
    | some c =>
      match X.followTo w p c with
      | none => none
      | some i =>
        match assoc i X.agents with
        | none => none
        | some γ =>
          if γ = zero then some 0
          else if γ = succ then (XNet.readNum X zero succ w fuel (i, 1)).map (· + 1)
          else none

/-- **What `readNum` returns is a numeral of the net.** -/
theorem XNet.readNum_sound (hsucc : 1 ≤ ar succ) {X : XNet S} (hX : X.toNet.WF ar) (w : Nat) :
    ∀ (fuel : Nat) (p : Port) (k : Nat), X.toNet.End ar p →
      X.readNum zero succ w fuel p = some k → Addition.IsNum ar zero succ X.toNet p k
  | 0, _, _, _, h => by cases h
  | fuel + 1, p, k, hp, h => by
    unfold XNet.readNum at h
    cases hc : assoc p X.wires with
    | none =>
      rw [hc] at h
      cases h
    | some c =>
      rw [hc] at h
      dsimp only at h
      cases hf : X.followTo w p c with
      | none =>
        rw [hf] at h
        cases h
      | some i =>
        rw [hf] at h
        dsimp only at h
        obtain ⟨⟨x, wk⟩, -⟩ := XNet.followTo_sound hX _ p c i (assoc_mem hc) hf
        have hconn : X.toNet.Conn ar p (i, 0) := ⟨c, x, wk⟩
        cases ha : assoc i X.agents with
        | none =>
          rw [ha] at h
          cases h
        | some γ =>
          rw [ha] at h
          dsimp only at h
          have hi : X.toNet.agent i γ := assoc_mem ha
          have hE : X.toNet.End ar (i, 0) := .inr ⟨γ, hi, Nat.zero_le _⟩
          by_cases hz : γ = zero
          · rw [ite_pos' hz] at h
            have ek : 0 = k := Option.some.inj h
            rw [← ek]
            rw [hz] at hi
            exact ⟨i, ⟨hp, hE, hconn⟩, hi⟩
          · rw [ite_neg' hz] at h
            by_cases hs : γ = succ
            · rw [ite_pos' hs] at h
              rw [hs] at hi
              cases hr : X.readNum zero succ w fuel (i, 1) with
              | none =>
                rw [hr] at h
                cases h
              | some k' =>
                rw [hr] at h
                have ek : k' + 1 = k := Option.some.inj h
                rw [← ek]
                obtain ⟨j, hpj, hnj⟩ := XNet.readNum_sound hsucc hX w fuel (i, 1) k'
                  (.inr ⟨succ, hi, hsucc⟩) hr
                exact ⟨i, ⟨hp, hE, hconn⟩, hi, j, hpj, hnj⟩
            · rw [ite_neg' hs] at h
              cases h

/-- More fuel does not change what `readNum` returns. -/
theorem XNet.readNum_mono {X : XNet S} {w w' : Nat} (hw : w ≤ w') :
    ∀ {f f' : Nat} {p : Port} {k : Nat},
      X.readNum zero succ w f p = some k → f ≤ f' → X.readNum zero succ w' f' p = some k
  | 0, _, _, _, h, _ => by cases h
  | f + 1, f', p, k, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    unfold XNet.readNum at h ⊢
    cases hc : assoc p X.wires with
    | none =>
      rw [hc] at h
      cases h
    | some c =>
      rw [hc] at h
      dsimp only at h ⊢
      cases hfo : X.followTo w p c with
      | none =>
        rw [hfo] at h
        cases h
      | some i =>
        rw [hfo] at h
        rw [XNet.followTo_mono hfo hw]
        dsimp only at h ⊢
        cases ha : assoc i X.agents with
        | none =>
          rw [ha] at h
          cases h
        | some γ =>
          rw [ha] at h
          dsimp only at h ⊢
          by_cases hz : γ = zero
          · rw [ite_pos' hz] at h ⊢
            exact h
          · rw [ite_neg' hz] at h ⊢
            by_cases hs : γ = succ
            · rw [ite_pos' hs] at h ⊢
              cases hr : X.readNum zero succ w f (i, 1) with
              | none =>
                rw [hr] at h
                cases h
              | some k' =>
                rw [hr] at h
                rw [XNet.readNum_mono hw (f := f) (f' := g) hr (by omega)]
                exact h
            · rw [ite_neg' hs] at h
              cases h

/-- **`readNum` returns every numeral of the net**, given enough fuel. -/
theorem XNet.readNum_complete (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF ar) :
    ∀ (k : Nat) (p : Port), Addition.IsNum ar zero succ X.toNet p k →
      ∃ w f, X.readNum zero succ w f p = some k
  | 0, p, ⟨i, ⟨hp, _, v, x, wk⟩, hn⟩ => by
    have hv : assoc p X.wires = some v :=
      assoc_eq_of_unique wk.link_first fun q' hq' => hX.end_unique hp hq' wk.link_first
    have hz : (i, zero) ∈ X.agents := hn
    obtain ⟨f₁, hf₁⟩ := XNet.followTo_complete hX wk hz
    have ha : assoc i X.agents = some zero :=
      assoc_eq_of_unique hz fun α' h' => hX.agent_fun h' hz
    refine ⟨f₁, 1, ?_⟩
    unfold XNet.readNum
    rw [hv]
    dsimp only
    rw [hf₁]
    dsimp only
    rw [ha]
    dsimp only
    rw [ite_pos' rfl]
  | k + 1, p, ⟨i, ⟨hp, _, v, x, wk⟩, hs, j, hpj, hnj⟩ => by
    have hv : assoc p X.wires = some v :=
      assoc_eq_of_unique wk.link_first fun q' hq' => hX.end_unique hp hq' wk.link_first
    have hs' : (i, succ) ∈ X.agents := hs
    obtain ⟨f₁, hf₁⟩ := XNet.followTo_complete hX wk hs'
    have ha : assoc i X.agents = some succ :=
      assoc_eq_of_unique hs' fun α' h' => hX.agent_fun h' hs'
    obtain ⟨w₂, f₂, h₂⟩ := XNet.readNum_complete hzs hX k (i, 1) ⟨j, hpj, hnj⟩
    refine ⟨max f₁ w₂, f₂ + 1, ?_⟩
    unfold XNet.readNum
    rw [hv]
    dsimp only
    rw [XNet.followTo_mono hf₁ (Nat.le_max_left _ _)]
    dsimp only
    rw [ha]
    dsimp only
    rw [ite_neg' (Ne.symm hzs), ite_pos' rfl,
      XNet.readNum_mono (Nat.le_max_right _ _) h₂ (Nat.le_refl _)]
    rfl

/-! ### Running and reading -/

/-- **Run a memory and read a numeral.**  `nt` threads take turns on the
memory for `steps` actions; if they are then at rest, the numeral on the
port `p` is read. -/
def XNet.runRead (xs : XSys S) (zero succ : S) (X : XNet S) (p : Port) (nt steps : Nat) :
    Option Nat :=
  if ((XMach.init X nt).trace xs (fun j => j % nt) steps).1.resting = true then
    ((XMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.readNum zero succ steps steps p
  else none

/-- **Whatever the run returns is the numeral of the normal form.**  Let
the net of the memory reduce to a normal form that has the numeral `v₀`
on the port `p`.  If the run returns a number, it is `v₀`. -/
theorem XNet.runRead_sound (xs : XSys S) (hzs : zero ≠ succ) (hsucc : 1 ≤ xs.sys.ar succ)
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {p : Port}
    {v₀ : Nat} (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) {nt steps v : Nat}
    (hnt : 0 < nt) (h : XNet.runRead xs zero succ X p nt steps = some v) : v = v₀ := by
  unfold XNet.runRead at h
  by_cases hr : ((XMach.init X nt).trace xs (fun j => j % nt) steps).1.resting = true
  · rw [ite_pos' hr] at h
    have L := XMach.trace_live (fun j => j % nt) (XMach.init_live (xs := xs) hX hnt) steps
    obtain ⟨q, hq⟩ := L.rest hr
    have r := XMach.trace_run xs (fun j => j % nt) (XMach.init X nt) steps
    rw [XMach.init_toMach] at r
    obtain ⟨-, hu⟩ := MRun.final hX r q hq
    obtain ⟨e', -⟩ := (hu hs).2 hn
    have e'' : N' = ((XMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet := e'
    have hW : ((XMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet.WF xs.sys.ar := by
      rw [← e'']
      exact Steps.wf hX hs
    have hnum' : Addition.IsNum xs.sys.ar zero succ
        ((XMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet p v₀ := by
      rw [← e'']
      exact hnum
    obtain ⟨i, hpi, -⟩ := hnum'
    exact Addition.IsNum.unique hzs hW (XNet.readNum_sound hsucc hW _ _ _ _ hpi.1 h)
      (by
        rw [← e'']
        exact hnum)
  · rw [ite_neg' hr] at h
    cases h

/-- **Given enough actions, the run returns the numeral of the normal
form.**  Threads that take turns are scheduled fairly, so they come to
rest; from then on the memory does not change, and the numeral on the
port is read. -/
theorem XNet.runRead_complete (xs : XSys S) (hzs : zero ≠ succ) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {p : Port}
    {v₀ : Nat} (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) {nt : Nat} (hnt : 0 < nt) :
    ∃ s₀, ∀ s, s₀ ≤ s → XNet.runRead xs zero succ X p nt s = some v₀ := by
  have hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j % nt = u := by
    intro u hu i
    refine ⟨u + i * nt, ?_, ?_⟩
    · have h1 := Nat.mul_le_mul_left i hnt
      rw [Nat.mul_one] at h1
      omega
    · rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hu
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xs) hX hnt hs hn (fun j => j % nt) hfair
  obtain ⟨hr, -, hmem⟩ := h i₀ (Nat.le_refl _)
  have hW : ((XMach.init X nt).trace xs (fun j => j % nt) i₀).1.mem.toNet.WF xs.sys.ar := by
    rw [hmem]
    exact Steps.wf hX hs
  have hnum' : Addition.IsNum xs.sys.ar zero succ
      ((XMach.init X nt).trace xs (fun j => j % nt) i₀).1.mem.toNet p v₀ := by
    rw [hmem]
    exact hnum
  obtain ⟨w, f, hread⟩ := XNet.readNum_complete hzs hW _ _ hnum'
  refine ⟨i₀ + (w + f), fun s hs' => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, s = i₀ + d := ⟨s - i₀, by omega⟩
  unfold XNet.runRead
  rw [ite_pos' (XMach.resting_trace _ hr d), XMach.trace_rest_eq _ hr d]
  exact XNet.readNum_mono (by omega) hread (by omega)

end Read

end INet
