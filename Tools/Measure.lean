import InteractionNets.MeasureJoin
import InteractionNets.ShortNames
import InteractionNets.Peano.Expr
import InteractionNets.CombChain

/-! # The measurements of `MeasureJoin`, run again

`lake exe inets-measure <table>` prints the runs behind one of the tables
quoted in `MeasureJoin`.  Nothing here is proved.  Counts of actions and of
operations are of the programs as defined and come out the same on every
machine; milliseconds and nanoseconds are of one run on the machine at
hand.  The tables:

* `programs`: claims and actions of `JMach`, `WMach` and `XMach`, one thread;
* `threads`: `JMach` with two and three threads taking turns;
* `chain`: walks of one thread on `joinChain`, in order and bit-reversed;
* `adversary`: walks under `jAdversary`, claims first or walks first;
* `schedules`: `jBusyFirst`, `JMach.bfRun`, `jCritical` and `JMach.csRun`;
* `indexed`: one thread of `IJMach` against `JMach`, in time and cells read;
* `indexed-threads`: `IJMach.bfRun` with several threads;
* `names`: the longest names at the start, written and at the end;
* `name-time`: nanoseconds for a counted operation, with long names;
* `short`: `XNet.short` against the names of the input. -/

open INet

/-- Flush after each row, so that a long table shows as it goes. -/
def row (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def programs : IO Unit := joinTable

def threads : IO Unit := do
  let go {S : Type} [DecidableEq S] (xs : XSys S) (nm : String) (X : XNet S) (nt : Nat) :
      IO Unit := do
    let (a, c, idle, w) := jStats xs nt (JMach.init X nt) 1000000000
    row s!"{nm} threads={nt} claims={c} actions={a} work={a - idle} walk={w}"
  for k in [40, 80, 160, 320] do go Arith.xsys s!"lnest {k}" (Arith.lnest k).net 2
  for k in [40, 320] do go Arith.xsys s!"lnest {k}" (Arith.lnest k).net 3
  go Peano.xsys "inertThenJoins 320" (Peano.inertThenJoins 320) 2
  go Arith.xsys "rnest 320" (Arith.rnest 320).net 2

def chain : IO Unit := chainTable

def adversary : IO Unit := do
  for (b, nt) in [(6, 16), (6, 64), (8, 64), (8, 256), (10, 256)] do
    let X := joinChain b (bitRev b)
    let (_, w₁) := jAdversary Arith.xsys (JMach.init X nt) nt 1000000000 false
    let (_, w₂) := jAdversary Arith.xsys (JMach.init X nt) nt 1000000000 true
    row s!"bit-reversed n={2 ^ b} threads={nt} claims-first={w₁} walks-first={w₂}"
  for nt in [16, 64, 256] do
    let X := joinChain 10 id
    let (_, w₁) := jAdversary Arith.xsys (JMach.init X nt) nt 1000000000 false
    row s!"in order n=1024 threads={nt} claims-first={w₁}"

def schedules : IO Unit := do
  for b in [6, 8, 10] do
    for nt in [1, 4, 16, 64] do
      let X := joinChain b (bitRev b)
      let (a₁, w₁) := jBusyFirst Arith.xsys (JMach.init X nt) nt 1000000000
      let (b₁, v₁) := JMach.bfRun Arith.xsys X nt 1000000000
      let (a₂, w₂) := jCritical Arith.xsys (JMach.init X nt) nt 1000000000
      let (b₂, v₂) := JMach.csRun Arith.xsys X nt 1000000000
      row s!"n={2 ^ b} threads={nt} jBusyFirst=({a₁},{w₁}) bfRun=({b₁},{v₁}) \
        jCritical=({a₂},{w₂}) csRun=({b₂},{v₂})"

/-- The cells of the list of segments that one step of a side reads. -/
def sideCells {S : Type} [DecidableEq S] (X : XNet S) : JCur S → Nat
  | .go prev cur => nextSegCells X.wires cur prev
  | _ => 0

/-- The cells that one step of a walk reads on lists. -/
def walkCells {S : Type} [DecidableEq S] (X : XNet S) (w : JWalk S) : Nat :=
  if w.c₁.going && (w.turn || !w.c₂.going) then sideCells X w.c₁ else sideCells X w.c₂

/-- One thread of `JMach` to rest: actions, and the cells its walks read. -/
def listRun {S : Type} [DecidableEq S] (xs : XSys S) (X : XNet S) : Nat × Nat := Id.run do
  let mut cur := JMach.init X 1
  let mut a := 0
  let mut cells := 0
  for _ in [0:1000000000] do
    if cur.resting then break
    match cur.ths[0]? with
    | some T =>
      match T.st, T.walk with
      | .write [] [], some wk => if T.again then cells := cells + walkCells cur.mem wk
      | _, _ => pure ()
    | none => pure ()
    a := a + 1
    cur := (cur.step xs 0).1
  return (a, cells)

def indexed : IO Unit := do
  for b in [6, 7, 8, 9, 10, 11, 12] do
    let X := joinChain b (bitRev b)
    let t₀ ← IO.monoMsNow
    let (a, tm) := IJMach.bfRun Arith.xsys X 1 1000000000
    let t₁ ← IO.monoMsNow
    let lists ← if b ≤ 11 then do
        let (a', c) := listRun Arith.xsys X
        let t₂ ← IO.monoMsNow
        pure s!"lists: actions={a'} walk-cells={c} ms={t₂ - t₁}"
      else pure "lists: not run"
    row s!"n={2 ^ b} indexed: actions={a} time={tm} ms={t₁ - t₀}; {lists}"

def indexedThreads : IO Unit := do
  for b in [8, 10, 12] do
    for nt in [1, 4, 16, 64] do
      let t₀ ← IO.monoMsNow
      let (a, tm) := IJMach.bfRun Arith.xsys (joinChain b (bitRev b)) nt 1000000000
      let t₁ ← IO.monoMsNow
      row s!"n={2 ^ b} threads={nt} actions={a} time={tm} ms={t₁ - t₀}"

/-- One thread of `IJMach` to rest, with the longest names at the start,
among the agents written, and among the agents at the end. -/
def nameRun {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X : XNet S) :
    IO Unit := do
  let L₀ := X.agents.foldl (fun l e => max l e.1.length) 0
  let mut M := IJMach.init X 1
  let mut a := 0
  let mut L := L₀
  for _ in [0:1000000000] do
    if M.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) then break
    M := (M.step xs 0).1
    a := a + 1
    match M.mem.log.head? with
    | some e => L := max L e.2.1.length
    | none => pure ()
  let L₁ := (M.mem.log.filter M.mem.isLive).foldl (fun l e => max l e.2.1.length) 0
  row s!"{nm}: actions={a} longest at start={L₀} written={L} at end={L₁}"

def names : IO Unit := do
  for b in [6, 10] do
    nameRun s!"joinChain {2 ^ b}" Arith.xsys (joinChain b (bitRev b))
    nameRun s!"combChain {2 ^ b}" Comb.dsystem (INet.combChain b (bitRev b))
  for k in [64, 256] do
    nameRun s!"lnest {k}" Arith.xsys (Arith.lnest k).net
    nameRun s!"rnest {k}" Arith.xsys (Arith.rnest k).net
    nameRun s!"lit {k} + lit {k}" Arith.xsys (Arith.Expr.add (.lit k) (.lit k)).net
    nameRun s!"Peano {k} * 3" Peano.xsys (Peano.PExpr.mul (.lit k) (.lit 3)).net

/-- One thread of `IJMach` to rest: actions, time, and the clock. -/
def timeRun {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X : XNet S) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let (a, tm) := IJMach.bfRun xs X 1 1000000000
  let t₁ ← IO.monoMsNow
  row s!"{nm}: actions={a} time={tm} ms={t₁ - t₀} ns per operation={(t₁ - t₀) * 1000000 / tm}"

def nameTime : IO Unit := do
  for k in [64, 128, 256, 512, 1024] do
    timeRun s!"lnest {k}" Arith.xsys (Arith.lnest k).net
    timeRun s!"lit {k} + lit {k} + lit {k}" Arith.xsys
      (Arith.Expr.add (.add (.lit k) (.lit k)) (.lit k)).net
  for k in [128, 256, 512, 1024] do
    timeRun s!"Peano {k} * 3" Peano.xsys (Peano.PExpr.mul (.lit k) (.lit 3)).net

/-- The renaming to short names, timed on its own. -/
def shortTimed {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X : XNet S) :
    IO Unit := do
  let t₀ ← IO.monoMsNow
  let Y := X.short
  let size := Y.agents.length + Y.wires.length + Y.free.length
  let t₁ ← IO.monoMsNow
  row s!"{nm}: renamed {size} cells in {t₁ - t₀} ms"
  timeRun s!"{nm}, XNet.short" xs Y

def short : IO Unit := do
  for k in [128, 256, 512, 1024] do
    timeRun s!"lnest {k}" Arith.xsys (Arith.lnest k).net
    shortTimed s!"lnest {k}" Arith.xsys (Arith.lnest k).net
    shortTimed s!"rnest {k}" Arith.xsys (Arith.rnest k).net

def tables : List (String × IO Unit) :=
  [("programs", programs), ("threads", threads), ("chain", chain), ("adversary", adversary),
    ("schedules", schedules), ("indexed", indexed), ("indexed-threads", indexedThreads),
    ("names", names), ("name-time", nameTime), ("short", short)]

def main (args : List String) : IO UInt32 := do
  match args with
  | [t] =>
    match tables.lookup t with
    | some m => m; return 0
    | none => pure ()
  | _ => pure ()
  IO.println s!"usage: inets-measure <table>, one of {tables.map (·.1)}"
  return 1
