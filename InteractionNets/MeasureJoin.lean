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
So the best bound to hope for on walks is of the order `n * lg n`. -/

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

/-- The runs of `joinChain`, in order and with the bits of the positions
reversed: claims, actions and actions of walks of one thread. -/
def chainTable : IO Unit := do
  for b in [4, 6, 8, 10, 11, 12] do
    for (nm, ord) in [("in order", fun i => i), ("bit-reversed", bitRev b)] do
      let (a, c, _, w) := jStats Arith.xsys 1 (JMach.init (joinChain b ord) 1) 1000000000
      IO.println s!"{nm} n={2 ^ b} claims={c} actions={a} walk={w}"
      (← IO.getStdout).flush

end INet
