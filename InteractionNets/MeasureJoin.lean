import InteractionNets.JoinWalk
import InteractionNets.Arith.Expr
import InteractionNets.Peano.WorkList

/-! ## Measuring the three programs at sizes the kernel does not reach

Nothing here is proved, and nothing above depends on it.  These are the
functions that were compiled (with `lake`, into an executable whose `main`
is `INet.joinTable`) and run, to count the actions of `XMach`, `WMach` and
`JMach` until rest, threads taking turns.  The counts are of the programs
as defined; the kernel checks such counts only on small nets
(`Peano.inertThenJoins_bounds` and the examples of `Peano/JoinWalk.lean`).

One thread:

    net                      claims   JMach     WMach     XMach
    inertThenJoins 80            80    1,283    20,323    20,323
    inertThenJoins 160          160    2,563    79,043    79,043
    inertThenJoins 320          320    5,123   311,683
    ((5 + 0) + 0) + …, 80       480   11,514    22,974    10,002
    ((5 + 0) + 0) + …, 160      960   23,034    71,534    20,002
    ((5 + 0) + 0) + …, 320    1,920   46,074   245,454
    0 + (0 + (… + 5)), 80        80    2,170     1,138     1,138
    0 + (0 + (… + 5)), 160      160    4,330     2,258     2,258
    0 + (0 + (… + 5)), 320      320    8,650     4,498

`JMach` takes `16 * k + 3` actions on `inertThenJoins k` and about 144 for
each addition on `((5 + 0) + 0) + …`, where `WMach` grows as the square;
on `0 + (0 + (… + 5))` its walks cost about twice the rescans, and both
are linear.  `XMach` is linear on the sums nested either way: after each
claim the pair it needs next is at the head of its fresh list.

Several threads, `JMach`.  Turns go to the threads in order whether or
not they are at rest, and a turn of a thread at rest changes nothing; the
counts of actions until rest include those turns, so they jump with where
the threads happen to be when the work runs out.  The work, the actions of
threads that are not at rest, is linear (`jStats`):

    net                      threads  claims   actions    work    walk
    ((5 + 0) + 0) + …, 40          2     240     9,677   5,983     512
    ((5 + 0) + 0) + …, 80          2     480    11,579  11,574   1,032
    ((5 + 0) + 0) + …, 160         2     960    36,790  24,002   2,064
    ((5 + 0) + 0) + …, 320         2   1,920    82,870  48,050   4,144
    ((5 + 0) + 0) + …, 40          3     240    12,010   6,297     512
    ((5 + 0) + 0) + …, 320         3   1,920   106,139  50,148   4,144
    inertThenJoins 320             2     320     6,729   6,728   1,280
    0 + (0 + (… + 5)), 320         2     320    13,928  13,921   6,371

With one thread no turn is at rest, and the walks take 2,072 of the
23,034 actions on the sums with 160 additions (about two for each claim),
1,280 of 5,123 on `inertThenJoins 320` (four for each join) and 3,832 of
8,650 on `0 + (0 + (… + 5))` with 320 additions (twelve for each join).

`JMach` is not linear on every net.  On a chain of `n` adders, each facing
a zero, with the result of each wired to the second argument of the next
(`joinChain`), every claim joins two wires.  Listed in order, each walk
takes five actions.  Listed in the order of the reversed bits of their
positions, the walks join wires of equal length, both sides go to the end,
and the walks take 133, 773, 4,101, 20,485, 45,061 and 98,309 actions for
`n` = 16, 64, 256, 1,024, 2,048 and 4,096: almost exactly `2 * n * lg n`.
So the best bound to hope for on walks is of the order `n * lg n`.

With several threads it is not reached in general.  A schedule that gives
the turn to a thread that is not walking whenever there is one
(`jAdversary`), so that claims run ahead of walks and wires grow under the
walks, makes the walks cost about `n` for each thread, up to `n` threads:

    chain (order)        n   threads   walks, claims first   walks first
    bit-reversed        64        16                 1,320           773
    bit-reversed        64        64                 4,256           773
    bit-reversed       256        64                17,568         4,101
    bit-reversed       256       256                66,176         4,101
    bit-reversed     1,024       256               266,880        20,485
    in order         1,024        16                61,323
    in order         1,024        64               208,646
    in order         1,024       256               657,180

Under this one schedule, with as many threads as adders (64 and 256 here),
the walks cost of the order `n * n`; with a fixed number of threads they
grow about linearly with `n`, and giving the turn to walking threads first
keeps the cost of one thread.  So a bound on walks for several threads has
to grow with the number of threads: the proved bounds of one thread
(`JMach.walked_log`, `JMach.rests_log`) do not carry over, and
`JMach.fair_bound` remains the bound for several threads, for every
schedule.  When a thread in a claim keeps the turn (`jCritical`), the
walks cost exactly what they cost with one thread, with 1 to 256 threads
on chains of 64 to 1,024 adders (20,485 bit-reversed, 5,119 in order, for
1,024); `JMach.walked_cs` proves they cost no more than the bound of one
thread.

The schedules of the proofs are run by `JMach.bfRun` and `JMach.csRun`
(`SchedRun`), proved to stop at the first state at rest (or when the fuel
runs out) and to count the walks of `JMach.walked`.  On the runs below
`JMach.bfRun` returned exactly what `jBusyFirst` did (measured, not
proved), and the same at 64 and 256 adders.  `jCritical` gives turns
round from the last thread that acted, so it
is not `JMach.csSched`, whose turns go by the number of actions; on the
bit-reversed chain of 1,024 adders the two differ by under 10 percent:

    threads   jBusyFirst = bfRun   bound of bfRun   jCritical   csRun     bound of csRun
          1               29,701          786,553      29,701   29,701           786,553
          4               35,845          866,431      45,049   45,048         3,465,724
         16               60,421        1,185,943     106,165   98,016        18,975,088
         64              158,725        2,463,991     346,309  334,208       157,695,424

with 20,485 actions of walks in every run, against 722,036 by the bounds
of `JMach.bfRun_walked` and `JMach.csRun_walked`.  The bounds are those of
`JMach.bfRun_rests` and `JMach.csRun_rests` evaluated with `n = 1,024`
steps, 2,048 agents and 4,098 wires; that this chain is well formed and
reaches its normal form in 1,024 steps is not proved here (well formed
is checked for `b = 3` in `Arith.JoinChain`).  The bound of `JMach.csRun` has the factor
`nt` twice.

On the indexed memory (`IJMach`, `IndexedJoin`), run as programs with the
hash maps compiled, one thread on the bit-reversed chain rests after the
same actions as on lists, and its time in operations on the maps and cells
(`IJMach.time`) is about 3.5 for each action.  The milliseconds are of one
run on one machine, and the program on lists is `JMach` itself:

    adders   actions   time (IJMach.time)   ms indexed   ms on lists
        64     1,349                4,759            1            10
       256     6,405               22,553            4           132
     1,024    29,701              104,475           15         2,799
     2,048    63,493              223,260           39        11,605
     4,096   135,173              475,165           87              -

The walks alone read 6.0 `n^2 lg n` cells of the lists of segments (62.6
million for 1,024 adders), which the indexed memory replaces by at most
four operations a step.  The names of `joinChain` stay short.  On nested
sums they do not: the net of `((5 + 0) + 0) + …` (`Arith.lnest`) names its
agents by their depth, and there the time measured for one counted
operation grows with the size, from 386 ns for 64 additions to 14,801 ns
for 1,024, whose longest name has 1,035 cells; on `lit k + lit k + lit k`
names stay at seven cells and it stays near 180 ns.  With several threads
under the busy-first schedule, run by `IJMach.bfRun` (proved to stop after
the actions of `JMach.bfRun` and to return the time of `IJMach` over them,
`IJMach.bfRun_eq`):

    adders  threads   actions      time   ms
     1,024        1    29,701   104,475   16
     1,024        4    35,845   116,763   19
     1,024       16    60,421   165,915   58
     1,024       64   158,725   362,523  886
     4,096        1   135,173   475,165   91
     4,096       64   651,269 1,507,357 3,795

The time per action falls with more threads (turns of the scan are cheap),
but the milliseconds grow faster than the time, most likely from the pick
of the next thread, which reads the list of threads, with a lookup by
position for each, at every action, and is not counted (it was not timed
alone).

Where long names come from.  Measured, with one thread: on `joinChain` and
the chain of combinators every name has one cell throughout.  On nested
sums the names are long from the start, the depth of the expression
(1,025 cells for 1,024 additions), and grow by about ten in the run; with
the input renamed to one-cell names before the run, the time for a
counted operation stays near 200 ns up to 1,024 additions (287 ns, 191 ms
in all), against 13,747 ns (9.1 s) with the names of the input.  In Peano
multiplication the names start at two cells and grow with the run, to 258
for `256 * 3`, and the time for a counted operation rises only from 203 ns
to 296 ns between `128 * 3` and `1024 * 3`.  With `XNet.short`, the proved
renaming of the input to one-cell names (`ShortNames`), `((5 + 0) + 0) + …`
takes 15, 31, 69 and 142 ms for 128, 256, 512 and 1,024 additions, against
54, 325, 1,950 and 10,008 ms, at 180 to 214 ns a counted operation; the
renaming is done before the clock starts.  A measuring loop must not compute the lists the
maps stand for (`IMem.toX`) at each action: that is a pass over the log. -/

namespace INet

variable {S : Type} [DecidableEq S]

/-- Actions and claims of `JMach` until rest, threads taking turns. -/
def jCount (xs : XSys S) (nt : Nat) (M : JMach S) (fuel : Nat) : Nat × Nat := Id.run do
  let mut cur := M
  let mut c := 0
  for i in [0:fuel] do
    if cur.resting then return (i, c)
    let (M', d) := cur.step xs (i % nt)
    cur := M'
    c := c + d
  return (fuel, c)

/-- Actions of `WMach` until rest, threads taking turns. -/
def wCount (xs : XSys S) (nt : Nat) (M : WMach S) (fuel : Nat) : Nat := Id.run do
  let mut cur := M
  for i in [0:fuel] do
    if cur.resting then return i
    cur := (cur.step xs (i % nt)).1
  return fuel

/-- Actions of `XMach` until rest, threads taking turns. -/
def xCount (xs : XSys S) (nt : Nat) (M : XMach S) (fuel : Nat) : Nat := Id.run do
  let mut cur := M
  for i in [0:fuel] do
    if cur.resting then return i
    cur := (cur.step xs (i % nt)).1
  return fuel

/-- `((5 + 0) + 0) + …` with `k` additions. -/
def Arith.lnest : Nat → Arith.Expr
  | 0 => .lit 5
  | k + 1 => .add (Arith.lnest k) (.lit 0)

/-- `0 + (0 + (… + 5))` with `k` additions. -/
def Arith.rnest : Nat → Arith.Expr
  | 0 => .lit 5
  | k + 1 => .add (.lit 0) (Arith.rnest k)

/-- Actions until rest of `JMach`, threads taking turns, with the claims,
the turns of threads at rest, and the actions of walks (starting one or
stepping it). -/
def jStats (xs : XSys S) (nt : Nat) (M : JMach S) (fuel : Nat) : Nat × Nat × Nat × Nat :=
  Id.run do
  let mut cur := M
  let mut c := 0
  let mut idle := 0
  let mut walks := 0
  for i in [0:fuel] do
    if cur.resting then return (i, c, idle, walks)
    let t := i % nt
    match cur.ths[t]? with
    | some T =>
      if T.todo.isEmpty && T.st.isIdle then idle := idle + 1
      if T.walk.isSome then walks := walks + 1
      match T.st, T.walk, T.joins with
      | .write [] [], none, _ :: _ => if T.again then walks := walks + 1
      | _, _, _ => pure ()
    | none => pure ()
    let (M', d) := cur.step xs t
    cur := M'
    c := c + d
  return (fuel, c, idle, walks)

/-- One line of the table: claims and actions of the three programs. -/
def joinRow (xs : XSys S) (name : String) (X : XNet S) (nt : Nat) (doX : Bool) : IO Unit := do
  let fuel := 100000000
  let (j, c) := jCount xs nt (JMach.init X nt) fuel
  let w := wCount xs nt (WMach.init X nt) fuel
  let x := if doX then toString (xCount xs nt (XMach.init X nt) fuel) else "-"
  IO.println s!"{name} threads={nt} claims={c} JMach={j} WMach={w} XMach={x}"
  (← IO.getStdout).flush

/-- The runs of the table for one thread. -/
def joinTable : IO Unit := do
  for k in [80, 160, 320] do
    joinRow Peano.xsys s!"inertThenJoins {k}" (Peano.inertThenJoins k) 1 (k ≤ 160)
  for k in [80, 160, 320] do
    joinRow Arith.xsys s!"lnest {k}" (Arith.lnest k).net 1 (k ≤ 160)
    joinRow Arith.xsys s!"rnest {k}" (Arith.rnest k).net 1 (k ≤ 160)

/-- The reversal of the `b` lowest bits of `i`. -/
def bitRev (b i : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := i
  for _ in [0:b] do
    r := 2 * r + x % 2
    x := x / 2
  return r

/-- A chain of `2 ^ b` adders of `Arith`, each facing a zero: a free port,
the second argument of the first adder, its result wired to the second
argument of the next, and so on, the result of the last free.  The adders
are listed in the order `order`. -/
def joinChain (b : Nat) (order : Nat → Nat) : XNet Arith :=
  let n := 2 ^ b
  ⟨((List.range n).map order).flatMap fun i =>
      [([2 * i + 1], Arith.add), ([2 * i + 2], Arith.zero)],
    [([0], 0), ([0], 1)],
    ((List.range n).flatMap fun i =>
      [(([2 * i + 1], 0), ([2 * i + 2], 0)), (([2 * i + 2], 0), ([2 * i + 1], 0))]) ++
    ((List.range (n - 1)).flatMap fun i =>
      [(([2 * i + 1], 2), ([2 * (i + 1) + 1], 1)), (([2 * (i + 1) + 1], 1), ([2 * i + 1], 2))]) ++
    [(([0], 0), ([1], 1)), (([1], 1), ([0], 0)),
      (([2 * (n - 1) + 1], 2), ([0], 1)), (([0], 1), ([2 * (n - 1) + 1], 2))]⟩

/-- The actions until rest and the actions of walks of `JMach` when the
turn goes to a busy thread that is not walking whenever there is one
(`walkFirst = false`), or to one that is walking (`walkFirst = true`),
threads otherwise taking turns. -/
def jAdversary (xs : XSys S) (M : JMach S) (nt : Nat) (fuel : Nat) (walkFirst : Bool) :
    Nat × Nat := Id.run do
  let mut cur := M
  let mut w := 0
  let mut rr := 0
  for i in [0:fuel] do
    if cur.resting then return (i, w)
    let mut pick := rr % nt
    let mut found := false
    for k in [0:nt] do
      let t := (rr + k) % nt
      if !found then
        match cur.ths[t]? with
        | some T =>
          let walking := T.walk.isSome ||
            (match T.st with | .write [] [] => T.again | _ => false)
          let busy := !(T.todo.isEmpty && T.st.isIdle)
          if busy && (walking == walkFirst) then
            pick := t
            found := true
        | none => pure ()
    if !found then
      for k in [0:nt] do
        let t := (rr + k) % nt
        if !found then
          match cur.ths[t]? with
          | some T =>
            if !(T.todo.isEmpty && T.st.isIdle) then
              pick := t
              found := true
          | none => pure ()
    rr := pick + 1
    match cur.ths[pick]? with
    | some T =>
      if T.walk.isSome then w := w + 1
      match T.st, T.walk, T.joins with
      | .write [] [], none, _ :: _ => if T.again then w := w + 1
      | _, _, _ => pure ()
    | none => pure ()
    cur := (cur.step xs pick).1
  return (fuel, w)

/-- The actions until rest and the actions of walks of `JMach` when a
thread in a claim (`half`, writing or walking) keeps the turn, threads
otherwise taking turns: the schedules of `JMach.walked_cs`. -/
def jCritical (xs : XSys S) (M : JMach S) (nt : Nat) (fuel : Nat) : Nat × Nat := Id.run do
  let mut cur := M
  let mut w := 0
  let mut rr := 0
  for i in [0:fuel] do
    if cur.resting then return (i, w)
    let mut pick := rr % nt
    for k in [0:nt] do
      match cur.ths[k]? with
      | some T =>
        let crit := match T.st with
          | .half _ _ _ _ => true
          | .write _ _ => true
          | _ => false
        if crit then pick := k
      | none => pure ()
    match cur.ths[pick]? with
    | some T =>
      let crit := match T.st with
        | .half _ _ _ _ => true
        | .write _ _ => true
        | _ => false
      if !crit then rr := pick + 1
      if T.walk.isSome then w := w + 1
      match T.st, T.walk, T.joins with
      | .write [] [], none, _ :: _ => if T.again then w := w + 1
      | _, _, _ => pure ()
    | none => rr := pick + 1
    cur := (cur.step xs pick).1
  return (fuel, w)

/-- The actions until rest and the actions of walks of `JMach` when a
thread in a claim keeps the turn and otherwise the first thread at work
gets it: the schedule `JMach.bfSched` of `JMach.rests_bfSched`. -/
def jBusyFirst (xs : XSys S) (M : JMach S) (nt : Nat) (fuel : Nat) : Nat × Nat := Id.run do
  let mut cur := M
  let mut w := 0
  for i in [0:fuel] do
    if cur.resting then return (i, w)
    let mut pick := none
    for k in [0:nt] do
      match cur.ths[k]? with
      | some T =>
        let crit := match T.st with
          | .half _ _ _ _ => true
          | .write _ _ => true
          | _ => false
        if crit && pick.isNone then pick := some k
      | none => pure ()
    if pick.isNone then
      for k in [0:nt] do
        match cur.ths[k]? with
        | some T =>
          if !(T.todo.isEmpty && T.st.isIdle) && pick.isNone then pick := some k
        | none => pure ()
    let t := pick.getD 0
    match cur.ths[t]? with
    | some T =>
      if T.walk.isSome then w := w + 1
      match T.st, T.walk, T.joins with
      | .write [] [], none, _ :: _ => if T.again then w := w + 1
      | _, _, _ => pure ()
    | none => pure ()
    cur := (cur.step xs t).1
  return (fuel, w)

/-- The runs of `joinChain`, in order and with the bits of the positions
reversed: claims, actions and actions of walks of one thread. -/
def chainTable : IO Unit := do
  for b in [4, 6, 8, 10, 11, 12] do
    for (nm, ord) in [("in order", fun i => i), ("bit-reversed", bitRev b)] do
      let (a, c, _, w) := jStats Arith.xsys 1 (JMach.init (joinChain b ord) 1) 1000000000
      IO.println s!"{nm} n={2 ^ b} claims={c} actions={a} walk={w}"
      (← IO.getStdout).flush

end INet
