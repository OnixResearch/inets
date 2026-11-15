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

Two threads, `JMach`: `((5 + 0) + 0) + …` with 40, 80, 160, 320 and 640
additions takes 9,677, 11,579, 36,790, 82,870 and 162,430 actions
(`WMach` 37,393 and 129,813 for 80 and 160), and `inertThenJoins` 80,
160, 320 takes 1,689, 3,369 and 6,729.  From 160 additions on the count
about doubles with the size; between 80 and 160 it more than triples,
which turns on where the two threads are when the joins come.  With three
threads the sums take 12,010, 15,985, 48,059 and 106,139 for 40 to 320
additions. -/

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

end INet
