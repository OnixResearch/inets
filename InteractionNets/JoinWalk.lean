import InteractionNets.WorkList

namespace INet

variable {S : Type}

/-! # A program that walks the wires a rule joins

`WMach` takes a fresh list of all agents after a claim of a rule that joins
two interface ports, and on some nets that rescan makes it quadratic where
`XMach` is linear (`((5 + 0) + 0) + …`).  An active pair that such a claim
makes and that has no new agent in it is a pair of the two old agents at the
ends of a joined wire.  `JMach` keeps its list after every claim, as `WMach`
does after a claim of any other rule, and after writing a rule that joins it
walks each joined wire from the joined segment, both ways in turn, one
segment for each action.  It stops at the first end that is not the
principal port of an agent in memory: an auxiliary port, a free port, a
segment not yet written, an agent held by another thread, or the other end
of the joined segment, when the wire is a loop.  When both ends are
principal ports it puts the agent at the first end in front of its list.

A walk reads only the memory, and the thread stays in its last state of
writing while it walks, so the program is still an execution of the machine
`Mach` (`JMach.act_sim`, `JMach.exec_run`), and the evaluable test of
`XMach.exec_agrees` carries over (`JMach.exec_agrees`).

Walking one side of each joined wire to its end was tried before, and is
quadratic on `0 + (0 + (… + 5))`: memory keeps every segment ever written,
so the walks grow.  Walking both sides in turn stops at the shorter side
when that ends at an auxiliary port. -/

section JMachine

/-- Where one side of a walk is: going, having come to `cur` from `prev`;
at the principal port of an agent in memory; or stopped. -/
inductive JCur (S : Type) where
  | go (prev cur : Port)
  | prin (i : Id) (γ : S)
  | stop
  deriving DecidableEq, Repr

/-- A walk of a joined wire: the two ends of the joined segment, the two
sides, and whose turn it is (`true`: the first side). -/
structure JWalk (S : Type) where
  s₁ : Port
  s₂ : Port
  c₁ : JCur S
  c₂ : JCur S
  turn : Bool
  deriving DecidableEq, Repr

/-- A thread of the program: the agents it has yet to try, its state,
whether the rule it writes joins interface ports, the joined segments it
has still to walk, and the walk under way. -/
structure JThread (S : Type) where
  todo : List (Id × S)
  st : TState S
  again : Bool
  joins : List (Port × Port)
  walk : Option (JWalk S)

/-- The thread of `WMach` it agrees with. -/
def JThread.toW (T : JThread S) : WThread S := ⟨T.todo, T.st, T.again⟩

/-- The machine as data. -/
structure JMach (S : Type) where
  mem : XNet S
  ths : List (JThread S)

/-- The machine of `WMach` with the same memory and threads. -/
def JMach.toW (M : JMach S) : WMach S := ⟨M.mem, M.ths.map JThread.toW⟩

/-- The machine it stands for. -/
def JMach.toMach (M : JMach S) : Mach S := M.toW.toMach

/-- An order on interface ports, to walk each joined segment once. -/
def LPort.rank : LPort → Nat
  | .ifc s k => 2 * k + (if s then 1 else 0)
  | .new _ _ _ => 0

/-- The segments of a right-hand side that join two interface ports, each
once, as pairs of ports of the net. -/
def XRhs.joinPairs (R : XRhs S) (ar : S → Nat) (a b : Id) (α β : S) : List (Port × Port) :=
  (ifcPorts ar α β).filterMap fun x =>
    match R.wire x with
    | some y => if !y.isNew && x.rank < y.rank then some (emb a b x, emb a b y) else none
    | none => none

variable [DecidableEq S]

/-- One segment along one side of a walk.  `other` is the start of the
other side: coming to it, the wire is a loop. -/
def JCur.next (X : XNet S) (other : Port) : JCur S → JCur S
  | .go prev cur =>
    if cur = other then .stop
    else
      match nextSeg X.wires cur prev with
      | some n => .go cur n
      | none =>
        if cur.2 = 0 then
          match assoc cur.1 X.agents with
          | some γ => .prin cur.1 γ
          | none => .stop
        else .stop
  | c => c

/-- The side is still going. -/
def JCur.going : JCur S → Bool
  | .go _ _ => true
  | _ => false

/-- One step of a walk: the side whose turn it is moves, or the other if
the first is no longer going. -/
def JWalk.advance (X : XNet S) (w : JWalk S) : JWalk S :=
  if w.c₁.going && (w.turn || !w.c₂.going) then
    { w with c₁ := w.c₁.next X w.s₂, turn := false }
  else { w with c₂ := w.c₂.next X w.s₁, turn := true }

/-- What a walk finds: `none` while it goes on; `some none` when it stops
without a pair; `some (some e)` when both ends are principal ports, `e`
being the agent at the first. -/
def JWalk.found (w : JWalk S) : Option (Option (Id × S)) :=
  match w.c₁, w.c₂ with
  | .stop, _ => some none
  | _, .stop => some none
  | .prin i γ, .prin _ _ => some (some (i, γ))
  | _, _ => none

/-- One action of a thread on the memory `X`: the new memory, the new
thread, and `1` if the action completed a claim. -/
def JMach.act (xs : XSys S) (X : XNet S) (T : JThread S) : XNet S × JThread S × Nat :=
  match T.st with
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (X.takeAgent b, ⟨R.newAgents a b ++ T.todo,
        .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β),
        R.joins xs.sys.ar α β, R.joinPairs xs.sys.ar a b α β, none⟩, 1)
    | none => (X.putAgent a α, ⟨T.todo, .idle, T.again, T.joins, T.walk⟩, 0)
  | .write [] [] =>
    if T.again then
      match T.walk with
      | some w =>
        match (w.advance X).found with
        | none => (X, ⟨T.todo, T.st, true, T.joins, some (w.advance X)⟩, 0)
        | some none => (X, ⟨T.todo, T.st, true, T.joins, none⟩, 0)
        | some (some e) => (X, ⟨e :: T.todo, T.st, true, T.joins, none⟩, 0)
      | none =>
        match T.joins with
        | (p, q) :: js => (X, ⟨T.todo, T.st, true, js, some ⟨p, q, .go q p, .go p q, true⟩⟩, 0)
        | [] => (X, ⟨T.todo, .idle, false, [], none⟩, 0)
    else (X, ⟨T.todo, .idle, false, [], none⟩, 0)
  | _ =>
    ((WMach.act xs X T.toW).1,
      ⟨(WMach.act xs X T.toW).2.1.todo, (WMach.act xs X T.toW).2.1.st,
        (WMach.act xs X T.toW).2.1.again, T.joins, T.walk⟩,
      (WMach.act xs X T.toW).2.2)

/-- **An action of the program does to the memory and to the state of the
thread what an action of `WMach` does**, or changes neither. -/
theorem JMach.act_agree (xs : XSys S) (X : XNet S) (T : JThread S) :
    ((JMach.act xs X T).1 = (WMach.act xs X T.toW).1 ∧
      (JMach.act xs X T).2.1.st = (WMach.act xs X T.toW).2.1.st ∧
      (JMach.act xs X T).2.2 = (WMach.act xs X T.toW).2.2) ∨
    ((JMach.act xs X T).1 = X ∧ (JMach.act xs X T).2.1.st = T.st ∧
      (JMach.act xs X T).2.2 = 0) := by
  obtain ⟨todo, st, again, joins, walk⟩ := T
  cases st with
  | idle => exact .inl ⟨rfl, rfl, rfl⟩
  | look a α => exact .inl ⟨rfl, rfl, rfl⟩
  | seek a α p c => exact .inl ⟨rfl, rfl, rfl⟩
  | ready a b α β => exact .inl ⟨rfl, rfl, rfl⟩
  | half a b α β =>
    refine .inl ?_
    unfold JMach.act WMach.act
    dsimp only [JThread.toW]
    cases (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R => exact ⟨rfl, rfl, rfl⟩
    | none => exact ⟨rfl, rfl, rfl⟩
  | write as ls =>
    cases as with
    | cons e as =>
      cases ls with
      | cons e' ls => exact .inl ⟨rfl, rfl, rfl⟩
      | nil => exact .inl ⟨rfl, rfl, rfl⟩
    | nil =>
      cases ls with
      | cons e ls => exact .inl ⟨rfl, rfl, rfl⟩
      | nil =>
        cases again with
        | false => exact .inl ⟨rfl, rfl, rfl⟩
        | true =>
          cases walk with
          | some w =>
            refine .inr ?_
            unfold JMach.act
            dsimp only
            cases (w.advance X).found with
            | none => exact ⟨rfl, rfl, rfl⟩
            | some o =>
              cases o with
              | none => exact ⟨rfl, rfl, rfl⟩
              | some e => exact ⟨rfl, rfl, rfl⟩
          | none =>
            cases joins with
            | cons e js => exact .inr ⟨rfl, rfl, rfl⟩
            | nil => exact .inl ⟨rfl, rfl, rfl⟩

/-- **An action of the program is an action of the machine**, or changes
neither the memory nor the state of the thread. -/
theorem JMach.act_sim (xs : XSys S) (X : XNet S) (T : JThread S) (th : Nat → TState S)
    (t : Nat) (hs : th t = T.st) :
    ((JMach.act xs X T).1 = X ∧ (JMach.act xs X T).2.1.st = T.st ∧
        (JMach.act xs X T).2.2 = 0) ∨
      MStep xs.sys (JMach.act xs X T).2.2 ⟨X.toNet, th⟩
        ⟨(JMach.act xs X T).1.toNet, upd th t (JMach.act xs X T).2.1.st⟩ := by
  rcases JMach.act_agree xs X T with ⟨e₁, e₂, e₃⟩ | h
  · rw [e₁, e₂, e₃]
    exact WMach.act_sim xs X T.toW th t hs
  · exact .inl h

omit [DecidableEq S] in
theorem threadOf_mapJ_eq {ths : List (JThread S)} {t : Nat} {T : JThread S}
    (h : ths[t]? = some T) : threadOf ((ths.map JThread.toW).map WThread.toX) t = T.st := by
  have h' : (ths.map JThread.toW)[t]? = some T.toW := by
    rw [List.getElem?_map, h]
    rfl
  exact threadOf_map_eq h'

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def JMach.step (xs : XSys S) (M : JMach S) (t : Nat) : JMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(JMach.act xs M.mem T).1, M.ths.set t (JMach.act xs M.mem T).2.1⟩,
      (JMach.act xs M.mem T).2.2)
  | none => (M, 0)

theorem JMach.step_sim (xs : XSys S) (M : JMach S) (t : Nat) :
    ((M.step xs t).1.toMach = M.toMach ∧ (M.step xs t).2 = 0) ∨
      MStep xs.sys (M.step xs t).2 M.toMach (M.step xs t).1.toMach := by
  unfold JMach.step
  cases h : M.ths[t]? with
  | none => exact .inl ⟨rfl, rfl⟩
  | some T =>
    have hm : ((M.ths.map JThread.toW).map WThread.toX)[t]? = some T.toW.toX := by
      rw [List.getElem?_map, List.getElem?_map, h]
      rfl
    have hset : ((M.ths.set t (JMach.act xs M.mem T).2.1).map JThread.toW).map WThread.toX =
        ((M.ths.map JThread.toW).map WThread.toX).set t
          (JMach.act xs M.mem T).2.1.toW.toX := by
      rw [List.map_set, List.map_set]
    rcases JMach.act_sim xs M.mem T (threadOf ((M.ths.map JThread.toW).map WThread.toX)) t
        (threadOf_mapJ_eq h) with ⟨e₁, e₂, e₃⟩ | hs
    · refine .inl ⟨?_, e₃⟩
      show Mach.mk (JMach.act xs M.mem T).1.toNet
        (threadOf (((M.ths.set t (JMach.act xs M.mem T).2.1).map JThread.toW).map
          WThread.toX)) = ⟨M.mem.toNet, threadOf ((M.ths.map JThread.toW).map WThread.toX)⟩
      rw [hset, threadOf_set hm, e₁]
      show Mach.mk M.mem.toNet (upd _ t (JMach.act xs M.mem T).2.1.st) = _
      rw [e₂, ← threadOf_mapJ_eq h, upd_self]
    · refine .inr ?_
      show MStep xs.sys _ ⟨M.mem.toNet, threadOf ((M.ths.map JThread.toW).map WThread.toX)⟩
        ⟨(JMach.act xs M.mem T).1.toNet,
          threadOf (((M.ths.set t (JMach.act xs M.mem T).2.1).map JThread.toW).map
            WThread.toX)⟩
      rw [hset, threadOf_set hm]
      exact hs

/-- Run the threads in the order given by a schedule.  Returns the final
state and the number of claims. -/
def JMach.exec (xs : XSys S) : List Nat → JMach S → JMach S × Nat
  | [], M => (M, 0)
  | t :: ts, M =>
    ((JMach.exec xs ts (M.step xs t).1).1,
      (M.step xs t).2 + (JMach.exec xs ts (M.step xs t).1).2)

/-- **A run of the program is an execution of the machine**, whatever the
schedule. -/
theorem JMach.exec_run (xs : XSys S) : ∀ (ts : List Nat) (M : JMach S),
    MRun xs.sys (M.exec xs ts).2 M.toMach (M.exec xs ts).1.toMach
  | [], M => .refl _
  | t :: ts, M => by
    have ih := JMach.exec_run xs ts (M.step xs t).1
    show MRun xs.sys ((M.step xs t).2 + (JMach.exec xs ts (M.step xs t).1).2) M.toMach
      (JMach.exec xs ts (M.step xs t).1).1.toMach
    rcases JMach.step_sim xs M t with ⟨e₁, e₂⟩ | hs
    · rw [e₂, Nat.zero_add, ← e₁]
      exact ih
    · exact .step hs ih

/-- The program before it starts: `n` idle threads, as for `XMach`. -/
def JMach.init (X : XNet S) (n : Nat) : JMach S :=
  ⟨X, (List.range n).map fun t => ⟨X.agents.drop t ++ X.agents.take t, .idle, false, [], none⟩⟩

omit [DecidableEq S] in
theorem JMach.init_toW (X : XNet S) (n : Nat) : (JMach.init X n).toW = WMach.init X n := by
  show WMach.mk X (((List.range n).map _).map JThread.toW) = _
  rw [List.map_map]
  rfl

omit [DecidableEq S] in
theorem JMach.init_toMach (X : XNet S) (n : Nat) :
    (JMach.init X n).toMach = Mach.init X.toNet := by
  show (JMach.init X n).toW.toMach = _
  rw [JMach.init_toW]
  exact WMach.init_toMach X n

/-- Every thread is idle. -/
def JMach.quiet (M : JMach S) : Bool := M.ths.all fun T => T.st.isIdle

omit [DecidableEq S] in
theorem JMach.quiet_toMach {M : JMach S} (h : M.quiet = true) : M.toMach.Quiet := by
  have hx : M.toW.quiet = true := by
    show (M.ths.map JThread.toW).all _ = true
    rw [List.all_map]
    exact h
  exact WMach.quiet_toMach hx

/-- Nothing is left to do: every thread is idle, with nothing to try. -/
def JMach.resting (M : JMach S) : Bool :=
  M.ths.all fun T => T.todo.isEmpty && T.st.isIdle

/-- A run from a net, with `n` threads, is an execution of the machine from
that net. -/
theorem JMach.exec_mrun (xs : XSys S) (X : XNet S) (n : Nat) (σ : List Nat) :
    MRun xs.sys ((JMach.init X n).exec xs σ).2 (Mach.init X.toNet)
      ((JMach.init X n).exec xs σ).1.toMach := by
  have h := JMach.exec_run xs σ (JMach.init X n)
  rw [JMach.init_toMach] at h
  exact h

/-- **The program agrees with the list reducer.**  If a run ends with every
thread idle after as many claims as the list reducer took steps, then the
memory holds a normal form, and with its history forgotten it is the net
that the list reducer returned.  Both hypotheses can be evaluated. -/
theorem JMach.exec_agrees {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) {n : Nat} {σ : List Nat}
    (hq : ((JMach.init X n).exec xs σ).1.quiet = true)
    (hk : ((JMach.init X n).exec xs σ).2 = (X.run xs f).2) :
    Normal (Step xs.sys) ((JMach.init X n).exec xs σ).1.mem.toNet ∧
      ((JMach.init X n).exec xs σ).1.mem.toNet.compact xs.sys.ar = (X.run xs f).1.toNet := by
  have hr := JMach.exec_mrun xs X n σ
  have sts := hr.quiet hX.1 (JMach.quiet_toMach hq)
  have hwf := Steps.wf hX.1 sts
  have cs := Steps.cstep hX.1 sts
  rw [hX.2, hk] at cs
  have e := XNet.run_agree hX f stop cs
  refine ⟨(normal_compact hwf).2 ?_, e⟩
  rw [e]
  exact (XNet.run_normal hX f stop).1

/-- No run makes more claims than the list reducer takes steps. -/
theorem JMach.exec_le {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) (n : Nat) (σ : List Nat) :
    ((JMach.init X n).exec xs σ).2 ≤ (X.run xs f).2 := by
  have sts := (JMach.exec_mrun xs X n σ).sequential hX.1
  have cs := Steps.cstep hX.1 sts
  rw [hX.2] at cs
  exact ((XNet.run_normal hX f stop).2 cs).1

end JMachine

end INet
