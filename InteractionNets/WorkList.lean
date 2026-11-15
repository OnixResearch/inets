import InteractionNets.Program

namespace INet

variable {S : Type}

/-! # A program that rechecks only what a rule touched

`XMach.act` takes a fresh copy of the whole list of agents after every
claim, so every rewrite step may read all of memory again.  Here a thread
keeps its list after a claim and puts the agents the rule wrote in front of
it.  Every new active pair then involves one of them, except when the rule
wires two of its interface ports together: then the two old agents whose
principal wires ran into the fired pair may come to face each other.  After
a claim of such a rule (one that *joins*) the thread takes a fresh copy of
the list of agents, as `XMach` does after every claim.

The program only reads memory where `XMach` does, so it is still an
execution of the machine `Mach` (`WMach.act_sim`, `WMach.exec_run`), and the
evaluable test of `XMach.exec_agrees` carries over (`WMach.exec_agrees`).

What it buys, measured by evaluation with one thread (actions until rest):

* a numeral of `k` successors listed first, then `k` pairs of an eraser and
  a zero: `XMach` takes 138, 423, 1443, 5283, 20163 actions for `k` = 5,
  10, 20, 40, 80 (about `3 * k ^ 2`), this program `10 * k + 3`;
* on the Peano expressions measured (sums, products, factorials, powers)
  the two are within 12% of each other, except `((5 + 0) + 0) + …`, where
  every claim joins and this program takes up to 1.7 times as many.

A version that walked the old side of each joined wire instead of
rescanning was quadratic on `0 + (0 + (… + 5))`: memory keeps every
segment ever written, so the walks grow. -/

section WMachine

/-- A thread of the program: the agents it has yet to try, its state, and
whether it must take a fresh list once it has written. -/
structure WThread (S : Type) where
  todo : List (Id × S)
  st : TState S
  again : Bool

/-- The thread of `XMach` it agrees with. -/
def WThread.toX (T : WThread S) : XThread S := ⟨T.todo, T.st⟩

/-- The machine as data. -/
structure WMach (S : Type) where
  mem : XNet S
  ths : List (WThread S)

/-- The machine it stands for. -/
def WMach.toMach (M : WMach S) : Mach S := ⟨M.mem.toNet, threadOf (M.ths.map WThread.toX)⟩

/-- The rule wires two of its interface ports together. -/
def XRhs.joins (R : XRhs S) (ar : S → Nat) (α β : S) : Bool :=
  (ifcPorts ar α β).any fun x =>
    match R.wire x with
    | some y => !y.isNew
    | none => false

variable [DecidableEq S]

/-- One action of a thread on the memory `X`: the new memory, the new
thread, and `1` if the action completed a claim. -/
def WMach.act (xs : XSys S) (X : XNet S) (T : WThread S) : XNet S × WThread S × Nat :=
  match T.st with
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (X.takeAgent b, ⟨R.newAgents a b ++ T.todo,
        .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β),
        T.again || R.joins xs.sys.ar α β⟩, 1)
    | none => (X.putAgent a α, ⟨T.todo, .idle, T.again⟩, 0)
  | .write [] [] =>
    if T.again then (X, ⟨X.agents, .idle, false⟩, 0) else (X, ⟨T.todo, .idle, false⟩, 0)
  | _ =>
    ((XMach.act xs X T.toX).1,
      ⟨(XMach.act xs X T.toX).2.1.todo, (XMach.act xs X T.toX).2.1.st, T.again⟩,
      (XMach.act xs X T.toX).2.2)

/-- An action of the program does to the memory and to the state of the
thread what an action of `XMach` does. -/
theorem WMach.act_agree (xs : XSys S) (X : XNet S) (T : WThread S) :
    (WMach.act xs X T).1 = (XMach.act xs X T.toX).1 ∧
      (WMach.act xs X T).2.1.st = (XMach.act xs X T.toX).2.1.st ∧
      (WMach.act xs X T).2.2 = (XMach.act xs X T.toX).2.2 := by
  obtain ⟨todo, st, again⟩ := T
  cases st with
  | idle => exact ⟨rfl, rfl, rfl⟩
  | look a α => exact ⟨rfl, rfl, rfl⟩
  | seek a α p c => exact ⟨rfl, rfl, rfl⟩
  | ready a b α β => exact ⟨rfl, rfl, rfl⟩
  | half a b α β =>
    unfold WMach.act XMach.act
    dsimp only [WThread.toX]
    cases (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) <;>
      exact ⟨rfl, rfl, rfl⟩
  | write as ls =>
    cases as with
    | cons e as => exact ⟨rfl, rfl, rfl⟩
    | nil =>
      cases ls with
      | cons e ls => exact ⟨rfl, rfl, rfl⟩
      | nil =>
        unfold WMach.act
        dsimp only
        split <;> exact ⟨rfl, rfl, rfl⟩

/-- **An action of the program is an action of the machine**, or changes
neither the memory nor the state of the thread. -/
theorem WMach.act_sim (xs : XSys S) (X : XNet S) (T : WThread S) (th : Nat → TState S)
    (t : Nat) (hs : th t = T.st) :
    ((WMach.act xs X T).1 = X ∧ (WMach.act xs X T).2.1.st = T.st ∧
        (WMach.act xs X T).2.2 = 0) ∨
      MStep xs.sys (WMach.act xs X T).2.2 ⟨X.toNet, th⟩
        ⟨(WMach.act xs X T).1.toNet, upd th t (WMach.act xs X T).2.1.st⟩ := by
  obtain ⟨e₁, e₂, e₃⟩ := WMach.act_agree xs X T
  rw [e₁, e₂, e₃]
  exact XMach.act_sim xs X T.toX th t hs

omit [DecidableEq S] in
theorem threadOf_map_eq {ths : List (WThread S)} {t : Nat} {T : WThread S}
    (h : ths[t]? = some T) : threadOf (ths.map WThread.toX) t = T.st := by
  have h' : (ths.map WThread.toX)[t]? = some T.toX := by
    rw [List.getElem?_map, h]
    rfl
  exact threadOf_eq h'

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def WMach.step (xs : XSys S) (M : WMach S) (t : Nat) : WMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(WMach.act xs M.mem T).1, M.ths.set t (WMach.act xs M.mem T).2.1⟩,
      (WMach.act xs M.mem T).2.2)
  | none => (M, 0)

theorem WMach.step_sim (xs : XSys S) (M : WMach S) (t : Nat) :
    ((M.step xs t).1.toMach = M.toMach ∧ (M.step xs t).2 = 0) ∨
      MStep xs.sys (M.step xs t).2 M.toMach (M.step xs t).1.toMach := by
  unfold WMach.step
  cases h : M.ths[t]? with
  | none => exact .inl ⟨rfl, rfl⟩
  | some T =>
    have hm : (M.ths.map WThread.toX)[t]? = some T.toX := by
      rw [List.getElem?_map, h]
      rfl
    have hset : (M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX =
        (M.ths.map WThread.toX).set t (WMach.act xs M.mem T).2.1.toX := by
      rw [List.map_set]
    rcases WMach.act_sim xs M.mem T (threadOf (M.ths.map WThread.toX)) t
        (threadOf_map_eq h) with ⟨e₁, e₂, e₃⟩ | hs
    · refine .inl ⟨?_, e₃⟩
      show Mach.mk (WMach.act xs M.mem T).1.toNet
        (threadOf ((M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX)) =
          ⟨M.mem.toNet, threadOf (M.ths.map WThread.toX)⟩
      rw [hset, threadOf_set hm, e₁]
      show Mach.mk M.mem.toNet (upd _ t (WMach.act xs M.mem T).2.1.st) = _
      rw [e₂, ← threadOf_map_eq h, upd_self]
    · refine .inr ?_
      show MStep xs.sys _ ⟨M.mem.toNet, threadOf (M.ths.map WThread.toX)⟩
        ⟨(WMach.act xs M.mem T).1.toNet,
          threadOf ((M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX)⟩
      rw [hset, threadOf_set hm]
      exact hs

/-- Run the threads in the order given by a schedule.  Returns the final
state and the number of claims. -/
def WMach.exec (xs : XSys S) : List Nat → WMach S → WMach S × Nat
  | [], M => (M, 0)
  | t :: ts, M =>
    ((WMach.exec xs ts (M.step xs t).1).1,
      (M.step xs t).2 + (WMach.exec xs ts (M.step xs t).1).2)

/-- **A run of the program is an execution of the machine**, whatever the
schedule. -/
theorem WMach.exec_run (xs : XSys S) : ∀ (ts : List Nat) (M : WMach S),
    MRun xs.sys (M.exec xs ts).2 M.toMach (M.exec xs ts).1.toMach
  | [], M => .refl _
  | t :: ts, M => by
    have ih := WMach.exec_run xs ts (M.step xs t).1
    show MRun xs.sys ((M.step xs t).2 + (WMach.exec xs ts (M.step xs t).1).2) M.toMach
      (WMach.exec xs ts (M.step xs t).1).1.toMach
    rcases WMach.step_sim xs M t with ⟨e₁, e₂⟩ | hs
    · rw [e₂, Nat.zero_add, ← e₁]
      exact ih
    · exact .step hs ih

/-- The program before it starts: `n` idle threads, as for `XMach`. -/
def WMach.init (X : XNet S) (n : Nat) : WMach S :=
  ⟨X, (List.range n).map fun t => ⟨X.agents.drop t ++ X.agents.take t, .idle, false⟩⟩

omit [DecidableEq S] in
theorem WMach.init_toMach (X : XNet S) (n : Nat) :
    (WMach.init X n).toMach = Mach.init X.toNet := by
  refine congrArg (Mach.mk X.toNet) (funext fun u => ?_)
  show threadOf (((List.range n).map fun t =>
    (⟨X.agents.drop t ++ X.agents.take t, .idle, false⟩ : WThread S)).map WThread.toX) u =
      .idle
  unfold threadOf
  split
  · rename_i T hT
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hT)
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT'
    rfl
  · rfl

/-- Every thread is idle. -/
def WMach.quiet (M : WMach S) : Bool := M.ths.all fun T => T.st.isIdle

omit [DecidableEq S] in
theorem WMach.quiet_toMach {M : WMach S} (h : M.quiet = true) : M.toMach.Quiet := by
  have hx : (⟨M.mem, M.ths.map WThread.toX⟩ : XMach S).quiet = true := by
    show (M.ths.map WThread.toX).all _ = true
    rw [List.all_map]
    exact h
  exact XMach.quiet_toMach hx

/-- Nothing is left to do: every thread is idle, with nothing to try. -/
def WMach.resting (M : WMach S) : Bool :=
  M.ths.all fun T => T.todo.isEmpty && T.st.isIdle

/-- A run from a net, with `n` threads, is an execution of the machine from
that net. -/
theorem WMach.exec_mrun (xs : XSys S) (X : XNet S) (n : Nat) (σ : List Nat) :
    MRun xs.sys ((WMach.init X n).exec xs σ).2 (Mach.init X.toNet)
      ((WMach.init X n).exec xs σ).1.toMach := by
  have h := WMach.exec_run xs σ (WMach.init X n)
  rw [WMach.init_toMach] at h
  exact h

/-- **The program agrees with the list reducer.**  If a run ends with every
thread idle after as many claims as the list reducer took steps, then the
memory holds a normal form, and with its history forgotten it is the net
that the list reducer returned.  Both hypotheses can be evaluated. -/
theorem WMach.exec_agrees {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) {n : Nat} {σ : List Nat}
    (hq : ((WMach.init X n).exec xs σ).1.quiet = true)
    (hk : ((WMach.init X n).exec xs σ).2 = (X.run xs f).2) :
    Normal (Step xs.sys) ((WMach.init X n).exec xs σ).1.mem.toNet ∧
      ((WMach.init X n).exec xs σ).1.mem.toNet.compact xs.sys.ar = (X.run xs f).1.toNet := by
  have hr := WMach.exec_mrun xs X n σ
  have sts := hr.quiet hX.1 (WMach.quiet_toMach hq)
  have hwf := Steps.wf hX.1 sts
  have cs := Steps.cstep hX.1 sts
  rw [hX.2, hk] at cs
  have e := XNet.run_agree hX f stop cs
  refine ⟨(normal_compact hwf).2 ?_, e⟩
  rw [e]
  exact (XNet.run_normal hX f stop).1

/-- No run makes more claims than the list reducer takes steps. -/
theorem WMach.exec_le {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) (n : Nat) (σ : List Nat) :
    ((WMach.init X n).exec xs σ).2 ≤ (X.run xs f).2 := by
  have sts := (WMach.exec_mrun xs X n σ).sequential hX.1
  have cs := Steps.cstep hX.1 sts
  rw [hX.2] at cs
  exact ((XNet.run_normal hX f stop).2 cs).1

end WMachine

end INet
