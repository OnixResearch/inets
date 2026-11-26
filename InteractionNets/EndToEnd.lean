import InteractionNets.ShortNames
import InteractionNets.Arith.JoinRun

/-! # From an expression to its value, on the indexed memory, in counted time

The pieces are proved apart: `JMach` at rest holds the normal form
(`JMach.rest_steps`), `IJMach` does what `JMach` does at a bounded cost a
step (`IJMach.init_sim`, `IJMach.time_bfSched`), and the short names of
`XNet.short` are a renaming (`XNet.short_steps`).  Here they are put
together in one program and one theorem.

`IJMach.runRead` runs the indexed program from a net under the busy-first
schedule within a fuel, and, if every thread is then at rest, reads the
numeral on a port from the maps of its memory (`IMem.readNum`, proved to
read what `XNet.readNum` reads on the lists, `IMem.readNum_eq`).  It
returns the numeral and the time of the run.  `IJMach.runRead_eq`: with
enough fuel it returns the numeral of the normal form, and a time within
`2 C + 3 D + 6` times the bound of `JMach.rests_bfSched`.

For an expression of additions (`Arith.Expr.shortRun_eq`): renamed short,
run by any number of threads and read at the renamed result port, the
program returns the value of the expression, at a time within the bound
of `Arith.Expr.itime_short`, with no hypothesis.  A numeral is carried
along a renaming (`Addition.IsNum.map`).

The reading is not in the time: it follows each wire of the numeral and
looks up each agent, as many operations as the numeral has cells times
the segments of a wire at most. -/

namespace INet

variable {S : Type} [DecidableEq S]

/-! ## Reading from the maps -/

/-- Go along a wire on the indexed memory, as `XNet.followTo` does. -/
def IMem.followTo (H : IMem S) : Nat → Port → Port → Option Id
  | 0, _, _ => none
  | fuel + 1, p, c =>
    match (if c.2 = 0 then H.sym c.1 else none) with
    | some _ => some c.1
    | none =>
      match (H.nb c).find? (fun q => decide (q ≠ p)) with
      | some q => IMem.followTo H fuel c q
      | none => none

theorem IMem.followTo_eq {H : IMem S} (h : H.Ok) :
    ∀ (fuel : Nat) (p c : Port), H.followTo fuel p c = H.toX.followTo fuel p c
  | 0, _, _ => rfl
  | fuel + 1, p, c => by
    unfold IMem.followTo XNet.followTo
    rw [h.sym c.1, h.next c p]
    cases (if c.2 = 0 then assoc c.1 H.toX.agents else none) with
    | some _ => rfl
    | none =>
      dsimp only
      cases nextSeg H.toX.wires c p with
      | none => rfl
      | some q => exact IMem.followTo_eq h fuel c q

/-- **Read the numeral on a port from the maps**, as `XNet.readNum` does
on the lists. -/
def IMem.readNum (H : IMem S) (zero succ : S) (w : Nat) : Nat → Port → Option Nat
  | 0, _ => none
  | fuel + 1, p =>
    match (H.nb p).head? with
    | none => none
    | some c =>
      match H.followTo w p c with
      | none => none
      | some i =>
        match H.sym i with
        | none => none
        | some γ =>
          if γ = zero then some 0
          else if γ = succ then (IMem.readNum H zero succ w fuel (i, 1)).map (· + 1)
          else none

theorem IMem.readNum_eq {H : IMem S} (h : H.Ok) (zero succ : S) (w : Nat) :
    ∀ (fuel : Nat) (p : Port), H.readNum zero succ w fuel p = H.toX.readNum zero succ w fuel p
  | 0, _ => rfl
  | fuel + 1, p => by
    unfold IMem.readNum XNet.readNum
    rw [h.first p]
    cases assoc p H.toX.wires with
    | none => rfl
    | some c =>
      dsimp only
      rw [IMem.followTo_eq h]
      cases H.toX.followTo w p c with
      | none => rfl
      | some i =>
        dsimp only
        rw [h.sym i]
        cases assoc i H.toX.agents with
        | none => rfl
        | some γ =>
          dsimp only
          rw [IMem.readNum_eq h zero succ w fuel (i, 1)]

/-! ## The run and the reading -/

/-- The busy-first run of the indexed program, returning the actions, the
time and the state where it stops. -/
def IJMach.bfLoopS (xs : XSys S) (nt : Nat) :
    Nat → Nat → Nat → IJMach S → Nat × Nat × IJMach S
  | 0, i, t, M => (i, t, M)
  | f + 1, i, t, M =>
    if M.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) then (i, t, M)
    else IJMach.bfLoopS xs nt f (i + 1) (t + M.stepCost xs (M.bfPick nt i))
      (M.step xs (M.bfPick nt i)).1

variable {xs : XSys S}

/-- The run stops after the actions of `JMach.bfRun`, with the time of the
indexed program over them and its state after them. -/
theorem IJMach.bfLoopS_eq {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (fuel : Nat) :
    IJMach.bfLoopS xs nt fuel 0 0 (IJMach.init X nt) = ((JMach.bfRun xs X nt fuel).1,
      (IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt)
        (JMach.bfRun xs X nt fuel).1,
      ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
        (JMach.bfRun xs X nt fuel).1).1) := by
  have key : ∀ f i, IJMach.bfLoopS xs nt f i
      ((IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt) i)
      ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt) i).1 =
      ((JMach.pLoop xs (fun M i => M.bfPick nt i) f i 0
          (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i)).1,
        (IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt)
          (JMach.pLoop xs (fun M i => M.bfPick nt i) f i 0
            (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i)).1,
        ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
          (JMach.pLoop xs (fun M i => M.bfPick nt i) f i 0
            (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i)).1).1) := by
    intro f
    induction f with
    | zero => intro i; rfl
    | succ f ih =>
      intro i
      obtain ⟨a, -, -⟩ := IJMach.init_sim hX hnd hnt (JMach.bfSched xs (JMach.init X nt) nt) i
      have es : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt) i).1 =
          JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i := by
        rw [JMach.bfSched_eq]
        exact JMach.pState_trace xs _ _ i
      have eP : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt) i).1.toJ =
          JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i := by
        rw [a, es]
      have er : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt) i).1.ths.all
          (fun T => T.todo.isEmpty && T.st.isIdle) =
          (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i).resting := by
        rw [← eP]
        rfl
      have ep : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt) i).1.bfPick
          nt i = JMach.bfSched xs (JMach.init X nt) nt i := by
        rw [IJMach.bfPick_eq, eP, JMach.bfSched_eq]
        rfl
      by_cases hr : (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i).resting = true
      · have hp : JMach.pLoop xs (fun M i => M.bfPick nt i) (f + 1) i 0
            (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i) = (i, 0) := by
          show (if _ then _ else _) = _
          rw [ite_pos' hr]
        rw [hp]
        show (if _ then _ else _) = _
        rw [er, ite_pos' hr]
      · have hp : JMach.pLoop xs (fun M i => M.bfPick nt i) (f + 1) i 0
            (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i) =
            JMach.pLoop xs (fun M i => M.bfPick nt i) f (i + 1)
              (0 + (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i).walkAct
                ((JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i).bfPick nt i))
              (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) (i + 1)) := by
          show (if _ then _ else _) = _
          rw [ite_neg' hr]
          rfl
        rw [hp, JMach.pLoop_fst xs _ f (i + 1) _ 0]
        show (if _ then _ else _) = _
        rw [er, ite_neg' hr, ep]
        exact ih (i + 1)
  exact key fuel 0

/-- **Run and read on the indexed memory**: the busy-first run from `X`
with `nt` threads within `s` actions and, if every thread is then at rest,
the numeral on the port `p` read from the maps, with the time of the run. -/
def IJMach.runRead (xs : XSys S) (zero succ : S) (X : XNet S) (p : Port) (nt s : Nat) :
    Option (Nat × Nat) :=
  match IJMach.bfLoopS xs nt s 0 0 (IJMach.init X nt) with
  | (_, t, M) =>
    if M.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) then
      (M.mem.readNum zero succ s s p).map fun v => (v, t)
    else none

/-- The bound of `JMach.rests_bfSched` on the actions at work, with `K` the
segments a memory can hold: `nt (7 |agents| + K) + n (C + D + 1 + 9 J) +
7 C n + K + J (4 K log₂ (K + 1) + 6 K)`, `K = wires + D n`. -/
def XNet.workBound (X : XNet S) (nt C D J n : Nat) : Nat :=
  nt * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
    7 * (C * n) + (X.wires.length + D * n) +
    J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
      6 * (X.wires.length + D * n))

/-- **The program returns the numeral of the normal form, in counted
time.**  On a well-formed net that lists no name twice and reaches a
normal form with the numeral `v₀` on `p` in `n` steps, given at least the
work bound and two actions, the segments of a memory and the numeral and
one, `IJMach.runRead` returns `v₀` and a time within `2 C + 3 D + 6` times
the work bound. -/
theorem IJMach.runRead_eq {zero succ : S} (hzs : zero ≠ succ) {J : Nat}
    (hJ : xs.JoinsAtMost J) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') {p : Port} {v₀ : Nat}
    (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) (s : Nat)
    (h₁ : X.workBound nt C D J n + 2 ≤ s) (h₂ : X.wires.length + D * n ≤ s)
    (h₃ : v₀ + 1 ≤ s) :
    ∃ t, IJMach.runRead xs zero succ X p nt s = some (v₀, t) ∧
      t ≤ (2 * C + 3 * D + 6) * X.workBound nt C D J n := by
  have hk : (JMach.bfRun xs X nt s).1 ≤ X.workBound nt C D J n + 1 :=
    JMach.bfRun_rests hJ hX hnd hnt hb hs hn s
  have spec := JMach.pRun_spec xs (fun M i => M.bfPick nt i) (JMach.init X nt) s
  rw [← JMach.bfSched_eq] at spec
  have hrest := spec.2.2.1 (by
    show (JMach.bfRun xs X nt s).1 < s
    omega)
  obtain ⟨hs', hn'⟩ := JMach.rest_steps hX hnt hrest
  have e : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.mem.toNet = N' :=
    (normal_form_unique hX hs' hs hn' hn).1
  obtain ⟨a, -, ok⟩ := IJMach.init_sim hX hnd hnt (JMach.bfSched xs (JMach.init X nt) nt)
    (JMach.bfRun xs X nt s).1
  have em := congrArg JMach.mem a
  have et := congrArg JMach.ths a
  refine ⟨(IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt)
    (JMach.bfRun xs X nt s).1, ?_, ?_⟩
  · unfold IJMach.runRead
    rw [IJMach.bfLoopS_eq hX hnd hnt s]
    dsimp only
    have hr : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
        (JMach.bfRun xs X nt s).1).1.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) = true := by
      have : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
          (JMach.bfRun xs X nt s).1).1.resting = true := hrest
      rw [← a] at this
      exact this
    rw [ite_pos' hr, IMem.readNum_eq ok]
    have hW : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
        (JMach.bfRun xs X nt s).1).1.mem.toNet.WF xs.sys.ar := by
      rw [e]
      exact Steps.wf hX hs
    have hnum' : Addition.IsNum xs.sys.ar zero succ
        ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
          (JMach.bfRun xs X nt s).1).1.mem.toNet p v₀ := by
      rw [e]
      exact hnum
    have hread := XNet.readNum_bounded hzs hW v₀ p hnum'
    have hwl := JMach.trace_wires_le hX hb hs hn nt (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1
    have hr' := XNet.readNum_mono (w' := s) (by omega) hread h₃
    have em' : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
        (JMach.bfRun xs X nt s).1).1.mem.toX = ((JMach.init X nt).trace xs
          (JMach.bfSched xs (JMach.init X nt) nt) (JMach.bfRun xs X nt s).1).1.mem := em
    rw [em', hr']
    rfl
  · exact IJMach.time_bfSched hJ hX hnd hnt hb hs hn _

/-! ## A numeral along a renaming -/

omit [DecidableEq S] in
theorem Net.Paired.map {ar : S → Nat} {N : Net S} {f : Id → Id} (hf : Renaming f N)
    (hN : N.WF ar) {p q : Port} (h : N.Paired ar p q) :
    (N.map f).Paired ar (mapPort f p) (mapPort f q) :=
  ⟨Net.end_map h.1, Net.end_map h.2.1, hf.conn_map hN.symm h.2.2⟩

omit [DecidableEq S] in
theorem Addition.Num.map {ar : S → Nat} {zero succ : S} {N : Net S} {f : Id → Id}
    (hf : Renaming f N) (hN : N.WF ar) :
    ∀ {k : Nat} {i : Id}, Addition.Num ar zero succ N i k →
      Addition.Num ar zero succ (N.map f) (f i) k
  | 0, i, h => ⟨i, rfl, h⟩
  | _ + 1, i, ⟨hs, i', hp, hn⟩ =>
    ⟨⟨i, rfl, hs⟩, f i', Net.Paired.map hf hN hp, Addition.Num.map hf hN hn⟩

omit [DecidableEq S] in
/-- **A numeral is carried along a renaming.** -/
theorem Addition.IsNum.map {ar : S → Nat} {zero succ : S} {N : Net S} {f : Id → Id}
    (hf : Renaming f N) (hN : N.WF ar) {p : Port} {k : Nat}
    (h : Addition.IsNum ar zero succ N p k) :
    Addition.IsNum ar zero succ (N.map f) (mapPort f p) k := by
  obtain ⟨i, hp, hn⟩ := h
  exact ⟨f i, Net.Paired.map hf hN hp, Addition.Num.map hf hN hn⟩

omit [DecidableEq S] in
theorem XNet.short_workBound (X : XNet S) (nt C D J n : Nat) :
    X.short.workBound nt C D J n = X.workBound nt C D J n := by
  unfold XNet.workBound
  rw [XNet.short_agents_length, XNet.short_wires_length]

/-- **From an expression of additions to its value, in counted time.**
Renamed short, run on the indexed memory by any number of threads under
the busy-first schedule, and read at the renamed result port, the program
returns the value of the expression, with a time within
`34 (nt (7 |agents| + K) + 20 c + 14 c + K + 4 K log₂ (K + 1) + 6 K)`,
`c` the steps of the expression and `K = wires + 8 c`, given that many
actions and two, `K` and the value and one.  No hypothesis. -/
theorem Arith.Expr.shortRun_eq (e : Arith.Expr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : e.net.workBound nt 2 8 1 e.cost + 2 ≤ s) (h₂ : e.net.wires.length + 8 * e.cost ≤ s)
    (h₃ : e.eval + 1 ≤ s) :
    ∃ t, IJMach.runRead Arith.xsys Arith.zero Arith.succ e.net.short
        (mapPort e.net.shortName e.res) nt s = some (e.eval, t) ∧
      t ≤ (2 * 2 + 3 * 8 + 6) * e.net.workBound nt 2 8 1 e.cost := by
  obtain ⟨hX, hfree, N', hs, hA, hno⟩ := Arith.Expr.good e
  have hn := Arith.normal_of_no_add hno
  obtain ⟨g, hg, eg, hs', hn'⟩ := XNet.short_steps hX hs hn
  have hW : N'.WF Arith.xsys.sys.ar := Steps.wf hX hs
  have hA' := Addition.IsNum.map hg hW hA
  have ep : mapPort g e.res = mapPort e.net.shortName e.res := by
    unfold mapPort
    rw [eg e.res.1 (.inr (.inr ⟨e.res.2, hfree⟩))]
  rw [ep] at hA'
  have k := IJMach.runRead_eq (xs := Arith.xsys) (zero := Arith.zero) (succ := Arith.succ)
    (by decide) Arith.xsys_joinsAtMost (XNet.short_wf hX)
    (XNet.short_nodup (Arith.Expr.net_nodup e))
    hnt Arith.xsys_bounded hs' hn' hA' s (by rw [XNet.short_workBound]; exact h₁)
    (by rw [XNet.short_wires_length]; exact h₂) h₃
  rw [XNet.short_workBound] at k
  exact k

end INet
