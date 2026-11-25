import InteractionNets.Indexed
import InteractionNets.JoinBound
import InteractionNets.SchedRun
import InteractionNets.Arith.Bound

/-! # The program that walks joined wires, on the indexed memory

`JMach` keeps its memory in lists, so one of its actions reads lists: a
step of a walk searches the segments for the next one, a look at an agent
searches the agents.  Its bounds count actions, and an action is not a
constant.  `IJMach` is the same program on the indexed memory of `IMach`:
the agents in a hash map from names to symbols, and the neighbours of each
port in a hash map from ports.  It is proved to do, action by action, what
`JMach` does (`IJMach.act_sim`, `IJMach.trace_sim`, `IJMach.init_sim`), so
every theorem about the runs of `JMach` holds of it.

Unlike `IMach`, it never takes the list of agents afresh, so every action
costs a constant: at most `2 C + 3 D + 6`, and nothing for a thread at rest
(`IJMach.cost_le`).  The running time of a run is therefore at most that
constant times the actions of threads at work (`IJMach.time_le_worked`),
and the bounds on those carry over (`IJMach.time_cs`,
`IJMach.time_bfSched`; for the adders, every expression,
`Arith.Expr.itime_bfSched`).

What one unit is: one operation on a hash map, one cell of a list read or
built, as for `IMach.cost`.  A hash-map operation takes constant time only
in expectation, and hashing or comparing a name, which is a list of
numbers, takes time with its length; neither is counted here (`OMach` and
`ZMach` count them, for the program that rescans).  Names are long on
some nets: the net of a nested sum names its agents by their depth, so
on `((5 + 0) + 0) + …` with 1,024 additions the longest name has 1,025
cells at the start, and the time measured for a counted operation grows
with the size there, where on `joinChain` it does not (`MeasureJoin`).
So the bound is on counted operations; with names, each costs up to the
length of the longest name.  The rule is computed at the cost of the cells it produces and
of its interface ports.  Not counted: building the indexed memory and the
lists of the threads at the start, the turns of a thread at rest, and the
table of threads, and the choice of the next thread by a schedule.  The
log of the memory is never packed, so the memory
grows by one cell for each agent written.  The hash-map reducer
(`HNet.runC_cost`) is linear in the steps; this program, which follows
wires that keep the ports of the agents fired, is `O(n log n)` on the
families measured (`MeasureJoin`) and proved `O(n + K log K)`. -/

namespace INet

variable {S : Type} [DecidableEq S]

/-- One segment along one side of a walk, on the indexed memory: the same
as `JCur.next`, with the search for the next segment and the look at the
agent done in the maps. -/
def JCur.inext (H : IMem S) (other : Port) : JCur S → JCur S
  | .go prev cur =>
    match (H.nb cur).find? (fun q => decide (q ≠ prev)) with
    | some n => if n = other then .stop else .go cur n
    | none =>
      if cur.2 = 0 then
        match H.sym cur.1 with
        | some γ => .prin cur.1 γ
        | none => .stop
      else .stop
  | c => c

theorem JCur.inext_eq {H : IMem S} (h : H.Ok) (other : Port) (c : JCur S) :
    c.inext H other = c.next H.toX other := by
  cases c with
  | go prev cur =>
    unfold JCur.inext JCur.next
    dsimp only
    rw [h.next cur prev, h.sym cur.1]
    cases nextSeg H.toX.wires cur prev <;> cases assoc cur.1 H.toX.agents <;> rfl
  | prin i γ => rfl
  | stop => rfl

/-- One step of a walk on the indexed memory. -/
def JWalk.iadvance (H : IMem S) (w : JWalk S) : JWalk S :=
  if w.c₁.going && (w.turn || !w.c₂.going) then
    { w with c₁ := w.c₁.inext H w.s₂, turn := false }
  else { w with c₂ := w.c₂.inext H w.s₁, turn := true }

theorem JWalk.iadvance_eq {H : IMem S} (h : H.Ok) (w : JWalk S) :
    w.iadvance H = w.advance H.toX := by
  unfold JWalk.iadvance JWalk.advance
  rw [JCur.inext_eq h, JCur.inext_eq h]

/-- **One action of a thread on the indexed memory**: the action of `JMach`,
with every lookup in a list replaced by a lookup in a map. -/
def IJMach.act (xs : XSys S) (H : IMem S) (T : JThread S) : IMem S × JThread S × Nat :=
  match T.st with
  | .half a b α β =>
    match (if H.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (H.take b, ⟨R.newAgents a b ++ T.todo,
        .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β),
        R.joins xs.sys.ar α β, R.joinPairs xs.sys.ar a b α β, none⟩, 1)
    | none => (H.put a α, ⟨T.todo, .idle, T.again, T.joins, T.walk⟩, 0)
  | .write [] [] =>
    if T.again then
      match T.walk with
      | some w =>
        match (w.iadvance H).found with
        | none => (H, ⟨T.todo, T.st, true, T.joins, some (w.iadvance H)⟩, 0)
        | some none => (H, ⟨T.todo, T.st, true, T.joins, none⟩, 0)
        | some (some e) => (H, ⟨e :: T.todo, T.st, true, T.joins, none⟩, 0)
      | none =>
        match T.joins with
        | (p, q) :: js => (H, ⟨T.todo, T.st, true, js, some ⟨p, q, .go q p, .go p q, true⟩⟩, 0)
        | [] => (H, ⟨T.todo, .idle, false, [], none⟩, 0)
    else (H, ⟨T.todo, .idle, false, [], none⟩, 0)
  | .write as ((p, q) :: ls) => (H.link p q, ⟨T.todo, .write as ls, T.again, T.joins, T.walk⟩, 0)
  | .write ((i, γ) :: as) [] => (H.put i γ, ⟨T.todo, .write as [], T.again, T.joins, T.walk⟩, 0)
  | _ =>
    ((IMach.act xs H ⟨T.todo, T.st⟩).1,
      ⟨(IMach.act xs H ⟨T.todo, T.st⟩).2.1.todo, (IMach.act xs H ⟨T.todo, T.st⟩).2.1.st,
        T.again, T.joins, T.walk⟩,
      (IMach.act xs H ⟨T.todo, T.st⟩).2.2)

/-- **The indexed action is the action of `JMach`**: on a memory whose maps
say what its lists say, it does to the memory of lists it stands for what
`JMach` does, leaves the thread in the same state, claims as often, and
keeps the maps right.  The one condition is that `JMach` does not write an
agent that is in memory already, which it never does (`JMach.step_nodup`). -/
theorem IJMach.act_sim (xs : XSys S) {H : IMem S} (h : H.Ok) (T : JThread S)
    (hnd : ((JMach.act xs H.toX T).1.agents.map Prod.fst).Nodup) :
    (IJMach.act xs H T).1.toX = (JMach.act xs H.toX T).1 ∧
      (IJMach.act xs H T).2 = (JMach.act xs H.toX T).2 ∧ (IJMach.act xs H T).1.Ok := by
  obtain ⟨todo, st, again, joins, walk⟩ := T
  have other : ∀ st' : TState S,
      IJMach.act xs H ⟨todo, st', again, joins, walk⟩ =
        ((IMach.act xs H ⟨todo, st'⟩).1,
          ⟨(IMach.act xs H ⟨todo, st'⟩).2.1.todo, (IMach.act xs H ⟨todo, st'⟩).2.1.st,
            again, joins, walk⟩, (IMach.act xs H ⟨todo, st'⟩).2.2) →
      JMach.act xs H.toX ⟨todo, st', again, joins, walk⟩ =
        ((XMach.act xs H.toX ⟨todo, st'⟩).1,
          ⟨(XMach.act xs H.toX ⟨todo, st'⟩).2.1.todo, (XMach.act xs H.toX ⟨todo, st'⟩).2.1.st,
            again, joins, walk⟩, (XMach.act xs H.toX ⟨todo, st'⟩).2.2) →
      ((JMach.act xs H.toX ⟨todo, st', again, joins, walk⟩).1.agents.map Prod.fst).Nodup →
      (IJMach.act xs H ⟨todo, st', again, joins, walk⟩).1.toX =
          (JMach.act xs H.toX ⟨todo, st', again, joins, walk⟩).1 ∧
        (IJMach.act xs H ⟨todo, st', again, joins, walk⟩).2 =
          (JMach.act xs H.toX ⟨todo, st', again, joins, walk⟩).2 ∧
        (IJMach.act xs H ⟨todo, st', again, joins, walk⟩).1.Ok := by
    intro st' e₁ e₂ hn
    rw [e₂] at hn
    rw [e₁, e₂]
    obtain ⟨a, b, c⟩ := IMach.act_sim xs h ⟨todo, st'⟩ hn
    refine ⟨a, ?_, c⟩
    rw [b]
  cases st with
  | idle => exact other _ rfl rfl hnd
  | look a α => exact other _ rfl rfl hnd
  | seek a α p c => exact other _ rfl rfl hnd
  | ready a b α β => exact other _ rfl rfl hnd
  | half a b α β =>
    unfold JMach.act at hnd
    unfold WMach.act at hnd
    dsimp only [JThread.toW] at hnd
    unfold IJMach.act JMach.act WMach.act
    dsimp only [JThread.toW]
    rw [h.sym b]
    cases hR : (if assoc b H.toX.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R => exact ⟨H.toX_take b, rfl, h.take b⟩
    | none =>
      rw [hR] at hnd
      exact ⟨IMem.toX_put h (assoc_none_of_nodup_cons hnd) α, rfl, h.put a α⟩
  | write as ls =>
    cases ls with
    | cons e ls =>
      obtain ⟨p, q⟩ := e
      cases as with
      | nil => exact ⟨H.toX_link p q, rfl, h.link p q⟩
      | cons e' as => exact ⟨H.toX_link p q, rfl, h.link p q⟩
    | nil =>
      cases as with
      | cons e as =>
        obtain ⟨i, γ⟩ := e
        exact ⟨IMem.toX_put h (assoc_none_of_nodup_cons hnd) γ, rfl, h.put i γ⟩
      | nil =>
        cases again with
        | false => exact ⟨rfl, rfl, h⟩
        | true =>
          cases walk with
          | some w =>
            unfold IJMach.act JMach.act
            dsimp only
            rw [JWalk.iadvance_eq h]
            cases (w.advance H.toX).found with
            | none => exact ⟨rfl, rfl, h⟩
            | some o =>
              cases o with
              | none => exact ⟨rfl, rfl, h⟩
              | some e => exact ⟨rfl, rfl, h⟩
          | none =>
            cases joins with
            | cons e js =>
              obtain ⟨p, q⟩ := e
              exact ⟨rfl, rfl, h⟩
            | nil => exact ⟨rfl, rfl, h⟩

/-- The program on the indexed memory: the memory and the threads. -/
structure IJMach (S : Type) where
  mem : IMem S
  ths : List (JThread S)

/-- The program on lists that it stands for. -/
def IJMach.toJ (M : IJMach S) : JMach S := ⟨M.mem.toX, M.ths⟩

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def IJMach.step (xs : XSys S) (M : IJMach S) (t : Nat) : IJMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(IJMach.act xs M.mem T).1, M.ths.set t (IJMach.act xs M.mem T).2.1⟩,
      (IJMach.act xs M.mem T).2.2)
  | none => (M, 0)

/-- The run under an unending schedule: the state and the number of claims
after `i` actions. -/
def IJMach.trace (xs : XSys S) (σ : Nat → Nat) (M : IJMach S) : Nat → IJMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((IJMach.trace xs σ M i).1.step xs (σ i)).1,
      (IJMach.trace xs σ M i).2 + ((IJMach.trace xs σ M i).1.step xs (σ i)).2)

/-- The program before it starts: the indexed memory of the net, and the
threads of `JMach`. -/
def IJMach.init (X : XNet S) (n : Nat) : IJMach S := ⟨IMem.ofX X, (JMach.init X n).ths⟩

theorem IJMach.init_toJ {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (IJMach.init X n).toJ = JMach.init X n := by
  show (⟨(IMem.ofX X).toX, (JMach.init X n).ths⟩ : JMach S) = JMach.init X n
  rw [(IMem.ofX_toX hnd).2.1]
  rfl

/-- One action of the indexed program is one action of `JMach`. -/
theorem IJMach.step_sim (xs : XSys S) {M : IJMach S} (h : M.mem.Ok) (t : Nat)
    (hnd : ((M.toJ.step xs t).1.mem.agents.map Prod.fst).Nodup) :
    (M.step xs t).1.toJ = (M.toJ.step xs t).1 ∧ (M.step xs t).2 = (M.toJ.step xs t).2 ∧
      (M.step xs t).1.mem.Ok := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold IJMach.step
      rw [ht]
    have ht' : M.toJ.ths[t]? = none := ht
    have e₂ : M.toJ.step xs t = (M.toJ, 0) := by
      unfold JMach.step
      rw [ht']
    rw [e₁, e₂]
    exact ⟨rfl, rfl, h⟩
  | some T =>
    have ht' : M.toJ.ths[t]? = some T := ht
    have e₂ : M.toJ.step xs t = (⟨(JMach.act xs M.mem.toX T).1,
        M.ths.set t (JMach.act xs M.mem.toX T).2.1⟩, (JMach.act xs M.mem.toX T).2.2) := by
      unfold JMach.step
      rw [ht']
      rfl
    rw [e₂] at hnd
    obtain ⟨a, b, c⟩ := IJMach.act_sim xs h T hnd
    have e₁ : M.step xs t = (⟨(IJMach.act xs M.mem T).1,
        M.ths.set t (IJMach.act xs M.mem T).2.1⟩, (IJMach.act xs M.mem T).2.2) := by
      unfold IJMach.step
      rw [ht]
    rw [e₁, e₂]
    refine ⟨?_, ?_, c⟩
    · show (⟨(IJMach.act xs M.mem T).1.toX, M.ths.set t (IJMach.act xs M.mem T).2.1⟩ :
        JMach S) = ⟨(JMach.act xs M.mem.toX T).1, M.ths.set t (JMach.act xs M.mem.toX T).2.1⟩
      rw [a, b]
    · show (IJMach.act xs M.mem T).2.2 = (JMach.act xs M.mem.toX T).2.2
      rw [b]

variable {xs : XSys S}

/-- **The indexed program runs as `JMach` does.**  From a memory whose maps
say what its lists say and in which no agent is listed twice, under any
schedule, after any number of actions the indexed program stands for the
state of `JMach`, has claimed as often, and its maps are right. -/
theorem IJMach.trace_sim {M : IJMach S} (h : M.mem.Ok) (hL : M.toJ.Live xs)
    (hnd : (M.toJ.mem.agents.map Prod.fst).Nodup) (σ : Nat → Nat) :
    ∀ i, (M.trace xs σ i).1.toJ = (M.toJ.trace xs σ i).1 ∧
      (M.trace xs σ i).2 = (M.toJ.trace xs σ i).2 ∧ (M.trace xs σ i).1.mem.Ok := by
  have live := JMach.trace_live (xs := xs) σ hL
  have nd : ∀ i, ((M.toJ.trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact JMach.step_nodup (live i) ih (σ i)
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl, h⟩
  | succ i ih =>
    obtain ⟨a, b, c⟩ := ih
    have hn : (((M.trace xs σ i).1.toJ.step xs (σ i)).1.mem.agents.map Prod.fst).Nodup := by
      rw [a]
      exact nd (i + 1)
    obtain ⟨a', b', c'⟩ := IJMach.step_sim xs c (σ i) hn
    refine ⟨?_, ?_, c'⟩
    · show ((M.trace xs σ i).1.step xs (σ i)).1.toJ = ((M.toJ.trace xs σ i).1.step xs (σ i)).1
      rw [a', a]
    · show (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2 =
        (M.toJ.trace xs σ i).2 + ((M.toJ.trace xs σ i).1.step xs (σ i)).2
      rw [b', b, a]

/-- **The run from a net**: the indexed program stands for `JMach` at every
action, so every theorem about the runs of `JMach` holds of it. -/
theorem IJMach.init_sim {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((IJMach.init X nt).trace xs σ i).1.toJ = ((JMach.init X nt).trace xs σ i).1 ∧
      ((IJMach.init X nt).trace xs σ i).2 = ((JMach.init X nt).trace xs σ i).2 ∧
      ((IJMach.init X nt).trace xs σ i).1.mem.Ok := by
  have e := IJMach.init_toJ hnd nt
  have hL : (IJMach.init X nt).toJ.Live xs := by
    rw [e]
    exact JMach.init_live hX hnt
  have hn : ((IJMach.init X nt).toJ.mem.agents.map Prod.fst).Nodup := by
    rw [e]
    exact hnd
  have k := IJMach.trace_sim (IMem.ofX_toX hnd).1 hL hn σ i
  rw [e] at k
  exact k

/-! ## The running time -/

/-- What one step of a side of a walk costs on the indexed memory: one for
the lookup of the neighbours, the cells of the list it reads, and one more
for the lookup of an agent when no segment goes on. -/
def JCur.icost (H : IMem S) : JCur S → Nat
  | .go prev cur =>
    1 + findCells prev (H.nb cur) +
      (match (H.nb cur).find? (fun q => decide (q ≠ prev)) with
       | some _ => 0
       | none => if cur.2 = 0 then 1 else 0)
  | _ => 0

/-- What one step of a walk costs: that of the side that moves. -/
def JWalk.icost (H : IMem S) (w : JWalk S) : Nat :=
  if w.c₁.going && (w.turn || !w.c₂.going) then w.c₁.icost H else w.c₂.icost H

/-- **What an action costs on the indexed memory**: one for the action, one
for each operation on a map, one for each cell of a list of neighbours it
reads, and one for each cell it builds.  A claim builds the agents of the
rule twice (in the list of the thread and in the state) and its segments
once, and reads the interface ports of the pair twice (whether the rule
joins and which segments it joins).  Otherwise as `IMach.cost`.  A thread
at rest costs nothing. -/
def IJMach.cost (xs : XSys S) (H : IMem S) (T : JThread S) : Nat :=
  match T.st with
  | .half a b α β =>
    2 + if H.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 1 + 2 * (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length +
            2 * (ifcPorts xs.sys.ar α β).length
        | none => 2
      else 2
  | .write [] [] =>
    if T.again then
      match T.walk with
      | some w => 1 + w.icost H
      | none => 1
    else 1
  | .write _ (_ :: _) => 6
  | .write (_ :: _) [] => 3
  | _ => IMach.cost xs H ⟨T.todo, T.st⟩

omit [DecidableEq S] in
theorem JCur.icost_le {H : IMem S} (h : H.Ok) (c : JCur S) : c.icost H ≤ 4 := by
  cases c with
  | go prev cur =>
    have hf := findCells_nbOf H.wires cur prev
    rw [← h.nbrs cur] at hf
    show 1 + findCells prev (H.nb cur) +
      (match (H.nb cur).find? (fun q => decide (q ≠ prev)) with
       | some _ => 0
       | none => if cur.2 = 0 then 1 else 0) ≤ 4
    cases (H.nb cur).find? (fun q => decide (q ≠ prev)) with
    | some _ => show 1 + findCells prev (H.nb cur) + 0 ≤ 4; omega
    | none =>
      show 1 + findCells prev (H.nb cur) + (if cur.2 = 0 then 1 else 0) ≤ 4
      split <;> omega
  | prin i γ => exact Nat.zero_le _
  | stop => exact Nat.zero_le _

omit [DecidableEq S] in
theorem JWalk.icost_le {H : IMem S} (h : H.Ok) (w : JWalk S) : w.icost H ≤ 4 := by
  unfold JWalk.icost
  split
  · exact JCur.icost_le h _
  · exact JCur.icost_le h _

/-- **An action costs a constant**, `2 C + 3 D + 6`, whatever the size of the
memory, and nothing when the thread is at rest. -/
theorem IJMach.cost_le {C D : Nat} (hb : xs.Bounded C D) {H : IMem S} (h : H.Ok)
    (T : JThread S) :
    IJMach.cost xs H T ≤
      (2 * C + 3 * D + 6) * (if T.todo.isEmpty && T.st.isIdle then 0 else 1) := by
  obtain ⟨todo, st, again, joins, walk⟩ := T
  have one : ∀ k, k ≤ 2 * C + 3 * D + 6 →
      ∀ st' : TState S, st'.isIdle = false →
      k ≤ (2 * C + 3 * D + 6) * (if todo.isEmpty && st'.isIdle then 0 else 1) := by
    intro k hk st' hs
    rw [hs, Bool.and_false]
    simpa using hk
  have hX : ∀ st' : TState S, st'.isIdle = false →
      IMach.cost xs H ⟨todo, st'⟩ ≤ 2 * C + 3 * D + 6 →
      IJMach.cost xs H ⟨todo, st', again, joins, walk⟩ =
        IMach.cost xs H ⟨todo, st'⟩ →
      IJMach.cost xs H ⟨todo, st', again, joins, walk⟩ ≤
        (2 * C + 3 * D + 6) * (if todo.isEmpty && st'.isIdle then 0 else 1) := by
    intro st' hs hk e
    rw [e]
    exact one _ hk st' hs
  cases st with
  | idle =>
    cases todo with
    | nil => exact Nat.zero_le _
    | cons e rest =>
      show 2 ≤ (2 * C + 3 * D + 6) * 1
      omega
  | look a α =>
    refine hX _ rfl ?_ rfl
    show 3 ≤ _
    omega
  | seek a α p c =>
    refine hX _ rfl ?_ rfl
    have hf := findCells_nbOf H.wires c p
    rw [← h.nbrs c] at hf
    show (if c.2 = 0 then 2 + (if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c))
      else 2 + findCells p (H.nb c)) ≤ _
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    refine hX _ rfl ?_ rfl
    show 2 + (if H.sym a = some α then 1 else 0) ≤ _
    split <;> omega
  | half a b α β =>
    refine one _ ?_ _ rfl
    show 2 + (if H.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 1 + 2 * (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length +
            2 * (ifcPorts xs.sys.ar α β).length
        | none => 2
      else 2) ≤ _
    by_cases hc : H.sym b = some β ∧ a ≠ b
    · rw [ite_pos' hc]
      cases hR : xs.rule α β with
      | none => show 2 + 2 ≤ _; omega
      | some R =>
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        have hi : (ifcPorts xs.sys.ar α β).length ≤ D := by
          rw [List.length_append] at hD
          omega
        show 2 + (1 + 2 * (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length +
            2 * (ifcPorts xs.sys.ar α β).length) ≤ _
        omega
    · rw [ite_neg' hc]
      omega
  | write as ls =>
    refine one _ ?_ _ rfl
    cases as with
    | cons e as =>
      cases ls with
      | cons e' ls => show 6 ≤ _; omega
      | nil => show 3 ≤ _; omega
    | nil =>
      cases ls with
      | cons e' ls => show 6 ≤ _; omega
      | nil =>
        unfold IJMach.cost
        dsimp only
        split
        · split
          · have := JWalk.icost_le h ‹JWalk S›
            omega
          · omega
        · omega

/-- What the action of thread `t` costs. -/
def IJMach.stepCost (xs : XSys S) (M : IJMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => IJMach.cost xs M.mem T
  | none => 0

theorem IJMach.stepCost_le {C D : Nat} (hb : xs.Bounded C D) {M : IJMach S} (h : M.mem.Ok)
    (t : Nat) : M.stepCost xs t ≤ (2 * C + 3 * D + 6) * M.toJ.busyAct t := by
  unfold IJMach.stepCost JMach.busyAct
  show _ ≤ (2 * C + 3 * D + 6) * (match M.ths[t]? with
    | some T => if T.todo.isEmpty && T.st.isIdle then 0 else 1
    | none => 0)
  cases M.ths[t]? with
  | none => exact Nat.zero_le _
  | some T => exact IJMach.cost_le hb h T

/-- **The running time on the indexed memory** of the first `i` actions of
a run. -/
def IJMach.time (xs : XSys S) (σ : Nat → Nat) (M : IJMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => IJMach.time xs σ M i + (M.trace xs σ i).1.stepCost xs (σ i)

/-- **The time is the work, up to a constant.**  Under any schedule, the
first `i` actions of the indexed program from a well-formed net in which no
agent is listed twice take at most `2 C + 3 D + 6` for each action of a
thread at work in the same run of `JMach` (`JMach.worked`). -/
theorem IJMach.time_le_worked {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) (σ : Nat → Nat) :
    ∀ i, (IJMach.init X nt).time xs σ i ≤
      (2 * C + 3 * D + 6) * JMach.worked xs σ (JMach.init X nt) i
  | 0 => Nat.zero_le _
  | i + 1 => by
    have ih := IJMach.time_le_worked hX hnd hnt hb σ i
    obtain ⟨a, -, ok⟩ := IJMach.init_sim hX hnd hnt σ i
    have hc := IJMach.stepCost_le hb ok (σ i)
    rw [a] at hc
    show (IJMach.init X nt).time xs σ i +
        ((IJMach.init X nt).trace xs σ i).1.stepCost xs (σ i) ≤
      (2 * C + 3 * D + 6) * (JMach.worked xs σ (JMach.init X nt) i +
        JMach.busyAct ((JMach.init X nt).trace xs σ i).1 (σ i))
    rw [Nat.mul_add]
    omega

/-- With the bound of `JMach.worked_cs`: **under any schedule where a thread
in a claim keeps the turn, the time of the indexed program is at most
`2 C + 3 D + 6` times
`nt (7 |agents| + K) + n (C + D + 1 + 9 J) + 7 C n + K + J (4 K log₂(K+1) + 6 K)`**,
`K = wires + D n`, for rules that write at most `C` agents and `D` segments
and join at most `J`, on a net with a normal form `n` steps away: for a
fixed system and number of threads, `O(n + K log K)` operations on the maps
and cells, where on lists an action reads the memory. -/
theorem IJMach.time_cs {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hcs : ∀ i u U, ((JMach.init X nt).trace xs σ i).1.ths[u]? = some U → U.critical = true →
      σ i = u)
    (i : Nat) :
    (IJMach.init X nt).time xs σ i ≤ (2 * C + 3 * D + 6) *
      (nt * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n))) :=
  Nat.le_trans (IJMach.time_le_worked hX hnd hnt hb σ i)
    (Nat.mul_le_mul_left _ (JMach.worked_cs hJ hX hnd hnt hb hs hn σ hcs i))

/-- **The busy-first schedule** (`JMach.bfSched`): the same bound on the time
of the indexed program, with any number of threads. -/
theorem IJMach.time_bfSched {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (i : Nat) :
    (IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt) i ≤
      (2 * C + 3 * D + 6) *
      (nt * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n))) :=
  IJMach.time_cs hJ hX hnd hnt hb hs hn _ (JMach.bfSched_hcs xs (JMach.init_hcs X nt)) i

/-- **One thread**: the same bound with `nt = 1`, for the only schedule. -/
theorem IJMach.time_one {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (i : Nat) :
    (IJMach.init X 1).time xs (fun _ => 0) i ≤ (2 * C + 3 * D + 6) *
      (1 * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n))) :=
  IJMach.time_cs hJ hX hnd Nat.one_pos hb hs hn _ (fun i u U hU _ => by
    have hl := JMach.trace_length xs (fun _ => 0) (JMach.init X 1) i
    have hu : u < 1 := by
      have := (List.getElem?_eq_some_iff.1 hU).1
      rw [hl] at this
      simpa [JMach.init] using this
    omega) i

/-! ## The time told from the lists

Hashing is opaque to the kernel, so no run of `IJMach` is evaluated as it
stands.  Its cost is a function of the lists the maps stand for
(`IJMach.cost_shadow`), so its time is the time computed along the run of
`JMach` (`IJMach.time_shadow`), which the kernel evaluates. -/

/-- The cost of a step of a side of a walk, told from the lists. -/
def JCur.lcost (X : XNet S) : JCur S → Nat
  | .go prev cur =>
    1 + findCells prev (nbOf X.wires cur) +
      (match nextSeg X.wires cur prev with
       | some _ => 0
       | none => if cur.2 = 0 then 1 else 0)
  | _ => 0

/-- The cost of a step of a walk, told from the lists. -/
def JWalk.lcost (X : XNet S) (w : JWalk S) : Nat :=
  if w.c₁.going && (w.turn || !w.c₂.going) then w.c₁.lcost X else w.c₂.lcost X

/-- **What an action costs on the indexed memory, told from the lists.** -/
def JMach.icost (xs : XSys S) (X : XNet S) (T : JThread S) : Nat :=
  match T.st with
  | .half a b α β =>
    2 + if assoc b X.agents = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R => 1 + 2 * (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length +
            2 * (ifcPorts xs.sys.ar α β).length
        | none => 2
      else 2
  | .write [] [] =>
    if T.again then
      match T.walk with
      | some w => 1 + w.lcost X
      | none => 1
    else 1
  | .write _ (_ :: _) => 6
  | .write (_ :: _) [] => 3
  | _ => XMach.icost xs X 0 ⟨T.todo, T.st⟩

theorem JCur.icost_shadow {H : IMem S} (h : H.Ok) (c : JCur S) :
    c.icost H = c.lcost H.toX := by
  cases c with
  | go prev cur =>
    show 1 + findCells prev (H.nb cur) +
      (match (H.nb cur).find? (fun q => decide (q ≠ prev)) with
       | some _ => 0
       | none => if cur.2 = 0 then 1 else 0) = 1 + findCells prev (nbOf H.toX.wires cur) +
      (match nextSeg H.toX.wires cur prev with
       | some _ => 0
       | none => if cur.2 = 0 then 1 else 0)
    rw [h.next cur prev, h.nbrs cur]
    rfl
  | prin i γ => rfl
  | stop => rfl

/-- The cost told from the lists is the cost on the indexed memory. -/
theorem IJMach.cost_shadow (xs : XSys S) {H : IMem S} (h : H.Ok) (T : JThread S) :
    IJMach.cost xs H T = JMach.icost xs H.toX T := by
  obtain ⟨todo, st, again, joins, walk⟩ := T
  have other : ∀ st' : TState S,
      IJMach.cost xs H ⟨todo, st', again, joins, walk⟩ = IMach.cost xs H ⟨todo, st'⟩ →
      JMach.icost xs H.toX ⟨todo, st', again, joins, walk⟩ =
        XMach.icost xs H.toX 0 ⟨todo, st'⟩ →
      (∀ ℓ, XMach.icost xs H.toX ℓ ⟨todo, st'⟩ = XMach.icost xs H.toX 0 ⟨todo, st'⟩) →
      IJMach.cost xs H ⟨todo, st', again, joins, walk⟩ =
        JMach.icost xs H.toX ⟨todo, st', again, joins, walk⟩ := by
    intro st' e₁ e₂ e₃
    rw [e₁, e₂, IMach.cost_shadow xs h, e₃]
  cases st with
  | idle => exact other _ rfl rfl fun _ => rfl
  | look a α => exact other _ rfl rfl fun _ => rfl
  | seek a α p c => exact other _ rfl rfl fun _ => rfl
  | ready a b α β => exact other _ rfl rfl fun _ => rfl
  | half a b α β =>
    unfold IJMach.cost JMach.icost
    dsimp only
    rw [h.sym b]
  | write as ls =>
    cases ls with
    | cons e ls =>
      cases as with
      | nil => rfl
      | cons e' as => rfl
    | nil =>
      cases as with
      | cons e as => rfl
      | nil =>
        cases again with
        | false => rfl
        | true =>
          cases walk with
          | none => rfl
          | some w =>
            show 1 + w.icost H = 1 + w.lcost H.toX
            unfold JWalk.icost JWalk.lcost
            rw [JCur.icost_shadow h, JCur.icost_shadow h]

/-- The time along a run of `JMach`, with each action at the cost it has on
the indexed memory. -/
def JMach.itime (xs : XSys S) (σ : Nat → Nat) (M : JMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => JMach.itime xs σ M i +
      (match (M.trace xs σ i).1.ths[σ i]? with
       | some T => JMach.icost xs (M.trace xs σ i).1.mem T
       | none => 0)

/-- **The time of the indexed program is the time told from the lists**,
along the same run of `JMach`. -/
theorem IJMach.time_shadow {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (IJMach.init X nt).time xs σ i = JMach.itime xs σ (JMach.init X nt) i
  | 0 => rfl
  | i + 1 => by
    have ih := IJMach.time_shadow hX hnd hnt σ i
    obtain ⟨a, -, ok⟩ := IJMach.init_sim hX hnd hnt σ i
    show (IJMach.init X nt).time xs σ i +
        ((IJMach.init X nt).trace xs σ i).1.stepCost xs (σ i) =
      JMach.itime xs σ (JMach.init X nt) i +
      (match ((JMach.init X nt).trace xs σ i).1.ths[σ i]? with
       | some T => JMach.icost xs ((JMach.init X nt).trace xs σ i).1.mem T
       | none => 0)
    rw [ih, ← a]
    unfold IJMach.stepCost
    show _ + (match ((IJMach.init X nt).trace xs σ i).1.ths[σ i]? with
      | some T => IJMach.cost xs ((IJMach.init X nt).trace xs σ i).1.mem T
      | none => 0) = _ + (match ((IJMach.init X nt).trace xs σ i).1.ths[σ i]? with
       | some T => JMach.icost xs ((IJMach.init X nt).trace xs σ i).1.mem.toX T
       | none => 0)
    cases ((IJMach.init X nt).trace xs σ i).1.ths[σ i]? with
    | none => rfl
    | some T => exact congrArg (_ + ·) (IJMach.cost_shadow xs ok T)

/-- **Every expression of additions, on the indexed memory**, with any
number of threads under the busy-first schedule: the time is at most
`34 (nt (7 |agents| + K) + 20 c + 14 c + K + 4 K log₂(K+1) + 6 K)`
operations on the maps and cells, with `c` the steps of the expression to
its value and `K = wires + 8 c`.  No hypothesis: the net of an expression
is well formed, lists no agent twice, and reaches its value
(`Arith.Expr.good`). -/
theorem Arith.Expr.itime_bfSched (e : Arith.Expr) {nt : Nat} (hnt : 0 < nt) (i : Nat) :
    (IJMach.init e.net nt).time Arith.xsys (JMach.bfSched Arith.xsys (JMach.init e.net nt) nt) i ≤
      (2 * 2 + 3 * 8 + 6) *
      (nt * (7 * e.net.agents.length + (e.net.wires.length + 8 * e.cost)) +
        e.cost * (2 + 8 + 1 + 9 * 1) + 7 * (2 * e.cost) + (e.net.wires.length + 8 * e.cost) +
        1 * (4 * ((e.net.wires.length + 8 * e.cost) *
          Nat.log2 (e.net.wires.length + 8 * e.cost + 1)) +
          6 * (e.net.wires.length + 8 * e.cost))) := by
  obtain ⟨hX, -, N', hs, -, hno⟩ := Arith.Expr.good e
  exact IJMach.time_bfSched Arith.xsys_joinsAtMost hX (Arith.Expr.net_nodup e) hnt
    Arith.xsys_bounded hs (Arith.normal_of_no_add hno) i

/-- **Every expression of additions, in actions**: the busy-first run of
`JMach` with any number of threads is at rest within the bound of
`JMach.rests_bfSched` and one, whatever the fuel, with no hypothesis. -/
theorem Arith.Expr.bfRun_rests (e : Arith.Expr) {nt : Nat} (hnt : 0 < nt) (fuel : Nat) :
    (JMach.bfRun Arith.xsys e.net nt fuel).1 ≤
      nt * (7 * e.net.agents.length + (e.net.wires.length + 8 * e.cost)) +
        e.cost * (2 + 8 + 1 + 9 * 1) + 7 * (2 * e.cost) + (e.net.wires.length + 8 * e.cost) +
        1 * (4 * ((e.net.wires.length + 8 * e.cost) *
          Nat.log2 (e.net.wires.length + 8 * e.cost + 1)) +
          6 * (e.net.wires.length + 8 * e.cost)) + 1 := by
  obtain ⟨hX, -, N', hs, -, hno⟩ := Arith.Expr.good e
  exact Arith.bfRun_rests hX (Arith.Expr.net_nodup e) hnt hs (Arith.normal_of_no_add hno) fuel

/-! ## Several threads, run as a program

The busy-first schedule picks its thread from the threads alone, so the
indexed program can pick it without the lists the maps stand for.
`IJMach.bfRun` runs it and is proved to return the actions of the measuring
run `JMach.bfRun` and the time of the indexed program over them
(`IJMach.bfRun_eq`).  The pick reads the threads once at each action; that
is not counted in the time. -/

omit [DecidableEq S] in
/-- The busy-first pick reads the threads only. -/
theorem JMach.bfPick_ths {M M' : JMach S} (h : M.ths = M'.ths) (nt i : Nat) :
    M.bfPick nt i = M'.bfPick nt i := by
  obtain ⟨X, ths⟩ := M
  obtain ⟨X', ths'⟩ := M'
  cases h
  rfl

/-- The busy-first pick on the indexed program. -/
def IJMach.bfPick (M : IJMach S) (nt i : Nat) : Nat :=
  (⟨⟨[], [], []⟩, M.ths⟩ : JMach S).bfPick nt i

theorem IJMach.bfPick_eq (M : IJMach S) (nt i : Nat) : M.bfPick nt i = M.toJ.bfPick nt i :=
  JMach.bfPick_ths rfl nt i

/-- The busy-first run of the indexed program: from the state after `i`
actions and `t` of time, stop when every thread is at rest or the fuel is
out, and return the actions and the time. -/
def IJMach.bfLoop (xs : XSys S) (nt : Nat) : Nat → Nat → Nat → IJMach S → Nat × Nat
  | 0, i, t, _ => (i, t)
  | f + 1, i, t, M =>
    if M.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) then (i, t)
    else IJMach.bfLoop xs nt f (i + 1) (t + M.stepCost xs (M.bfPick nt i))
      (M.step xs (M.bfPick nt i)).1

/-- **The busy-first run of the indexed program, from a net with `nt`
threads**: the actions until rest and the time. -/
def IJMach.bfRun (xs : XSys S) (X : XNet S) (nt fuel : Nat) : Nat × Nat :=
  IJMach.bfLoop xs nt fuel 0 0 (IJMach.init X nt)

theorem JMach.pLoop_fst (xs : XSys S) (pk : JMach S → Nat → Nat) :
    ∀ f i w w' (M : JMach S), (JMach.pLoop xs pk f i w M).1 = (JMach.pLoop xs pk f i w' M).1
  | 0, _, _, _, _ => rfl
  | f + 1, i, w, w', M => by
    show (if M.resting then (i, w) else _).1 = (if M.resting then (i, w') else _).1
    split
    · rfl
    · exact JMach.pLoop_fst xs pk f (i + 1) _ _ _

/-- **The program run is the measuring run**: `IJMach.bfRun` stops after the
actions of `JMach.bfRun`, and returns the time of the indexed program over
them under the busy-first schedule. -/
theorem IJMach.bfRun_eq {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (fuel : Nat) :
    IJMach.bfRun xs X nt fuel = ((JMach.bfRun xs X nt fuel).1,
      (IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt)
        (JMach.bfRun xs X nt fuel).1) := by
  have key : ∀ f i, IJMach.bfLoop xs nt f i
      ((IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt) i)
      ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt) i).1 =
      ((JMach.pLoop xs (fun M i => M.bfPick nt i) f i 0
          (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i)).1,
        (IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt)
          (JMach.pLoop xs (fun M i => M.bfPick nt i) f i 0
            (JMach.pState xs (fun M i => M.bfPick nt i) (JMach.init X nt) i)).1) := by
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
  have k := key fuel 0
  exact k

end INet
