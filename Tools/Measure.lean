import InteractionNets.MeasureJoin
import InteractionNets.ShortNames
import InteractionNets.Peano.Expr
import InteractionNets.CombChain
import InteractionNets.EndToEnd
import InteractionNets.Arith.SideBySide
import InteractionNets.ParUnits

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
* `short`: `XNet.short` against the names of the input;
* `end-to-end`: `IJMach.runRead` on expressions, renamed short, against
  the value and the bound of `Arith.Expr.shortRun_eq`;
* `rounds`: the steps to the normal form against the rounds of
  `XNet.parStep`, which fires every active pair at once;
* `rounds-p`: rounds of `XNet.parRunP`, at most `p` pairs a round,
  against the bound `W / p + D` of `XNet.parRunP_bound`;
* `packed`: `XNet.packRun` from the short form, against `XNet.parRun`: the
  pairs and rounds, and the largest list of identifiers held, which bounds
  the numbers in the names (`XNet.packRun_short`);
* `reuse`: `XNet.reuseRun` from the short form, against `XNet.parRun`: the
  pairs and rounds, the free ports, the largest number in a name against
  the bound `XNet.reusePeak` of `XNet.reuseRun_short`;
* `units`: `XNet.reuseRunP`, at most `p` pairs a round and the allocator,
  from the short form: rounds against `W / p + D`
  (`XNet.reuseRunP_short`), the free ports, the largest number in a name
  against the longest list of identifiers held. -/

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
        let (a', _) := jCount Arith.xsys 1 (JMach.init X 1) 1000000000
        let t₂ ← IO.monoMsNow
        let (_, c) := listRun Arith.xsys X
        pure s!"lists: actions={a'} ms={t₂ - t₁} walk-cells={c}"
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

def endToEnd : IO Unit := do
  let go (nm : String) (e : Arith.Expr) (nt : Nat) : IO Unit := do
    let B := e.net.workBound nt 2 8 1 e.cost
    let s := B + 2 + e.net.wires.length + 8 * e.cost + e.eval + 1
    let X := e.net.short
    let p := mapPort e.net.shortName e.res
    let t₀ ← IO.monoMsNow
    let r := IJMach.runRead Arith.xsys Arith.zero Arith.succ X p nt s
    let t₁ ← IO.monoMsNow
    let shown := match r with
      | some (v, t) => s!"value={v} (expected {e.eval}) time={t} bound={34 * B}"
      | none => "none"
    row s!"{nm} threads={nt}: {shown} ms={t₁ - t₀}"
  for k in [64, 256, 1024] do
    for nt in [1, 4] do
      go s!"lnest {k}" (Arith.lnest k) nt
      go s!"rnest {k}" (Arith.rnest k) nt
      go s!"lit {k} + lit {k}" (Arith.Expr.add (.lit k) (.lit k)) nt

/-- The net with every wire one segment: for each end (a free port, or a
port of an agent within its arity), the end the wire from it reaches.  For
measuring only; the nets of expressions have wires of several segments,
and `XNet.parStep` reads a wire as one segment. -/
def compactX {S : Type} [DecidableEq S] (ar : S → Nat) (X : XNet S) : XNet S := Id.run do
  let mut adj : Std.HashMap Port (List Port) := {}
  for (p, q) in X.wires do adj := adj.insert p (q :: adj.getD p [])
  let mut syms : Std.HashMap Id S := {}
  for (i, γ) in X.agents do syms := syms.insert i γ
  let isEnd := fun (p : Port) =>
    X.free.contains p || (match syms[p.1]? with | some γ => p.2 ≤ ar γ | none => false)
  let ends := X.free ++ X.agents.flatMap fun (i, γ) => (List.range (ar γ + 1)).map (i, ·)
  let mut ws : List (Port × Port) := []
  for p in ends do
    match adj.getD p [] with
    | c :: _ =>
      let mut prev := p
      let mut cur := c
      let mut guard := 0
      while !isEnd cur && guard < 1000000 do
        guard := guard + 1
        match (adj.getD cur []).find? (· ≠ prev) with
        | some nx => prev := cur; cur := nx
        | none => guard := 1000000
      if isEnd cur then ws := (p, cur) :: ws
    | [] => pure ()
  return ⟨X.agents, X.free, ws.reverse⟩

/-- Rounds of `XNet.parStep` until no pair is active, and the pairs fired. -/
def roundRun {S : Type} [DecidableEq S] (xs : XSys S) (X : XNet S) : Nat × Nat := Id.run do
  let mut cur := X
  let mut r := 0
  let mut n := 0
  for _ in [0:1000000] do
    let (Y, k) := cur.parStep xs
    if k == 0 then break
    cur := Y
    r := r + 1
    n := n + k
  return (r, n)

/-- A balanced sum of `2 ^ d` ones. -/
def balanced : Nat → Arith.Expr
  | 0 => .lit 1
  | d + 1 => .add (balanced d) (balanced d)

/-- `k` additions `m + n` side by side, each tagged apart. -/
def sumsBeside (k m n : Nat) : XNet Arith :=
  (List.range k).foldl (fun X i => Arith.beside X (Arith.tagNet i (Arith.sum m n)))
    ⟨[], [], []⟩

def rounds : IO Unit := do
  let go {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X : XNet S) : IO Unit := do
    let (r, n) := roundRun xs X
    let seq := match X.normalize xs 100000 with | some (_, k) => toString k | none => "-"
    row s!"{nm}: ok={X.check xs.sys.ar} steps={seq} fired={n} rounds={r} \
      steps per round={if r = 0 then 0 else n / r}"
  let ar := Arith.xsys.sys.ar
  for k in [16, 64, 256] do
    go s!"lnest {k}" Arith.xsys (compactX ar (Arith.lnest k).net)
    go s!"rnest {k}" Arith.xsys (compactX ar (Arith.rnest k).net)
  for d in [4, 6, 8] do
    go s!"balanced sum of {2 ^ d} ones" Arith.xsys (compactX ar (balanced d).net)
  for m in [16, 64, 256] do
    go s!"sum {m} + {m}" Arith.xsys (Arith.sum m m)
  for k in [4, 16, 64] do
    go s!"{k} sums 32 + 32 side by side" Arith.xsys (sumsBeside k 32 32)
  for b in [4, 6, 8] do
    go s!"joinChain {2 ^ b} in order" Arith.xsys (joinChain b id)
    go s!"combChain {2 ^ b}" Comb.dsystem (INet.combChain b (bitRev b))
  for k in [8, 32] do
    let e : Peano.PExpr := .mul (.lit k) (.lit 3)
    go s!"Peano {k} * 3" Peano.xsys (compactX Peano.xsys.sys.ar e.net)

def roundsP : IO Unit := do
  let go {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X : XNet S) : IO Unit := do
    let (D, W) := roundRun xs X
    let mut line := s!"{nm}: W={W} D={D}"
    for p in [1, 2, 4, 16, 64] do
      let mut cur := X
      let mut r := 0
      let mut w := 0
      for _ in [0:W + 1] do
        let (Y, k) := cur.parStepP xs p
        if k == 0 then break
        cur := Y
        r := r + 1
        w := w + k
      line := line ++ s!" | p={p}: {r} (bound {W / p + D}){if w == W then "" else " ?"}"
    row line
  for k in [4, 16] do
    go s!"{k} sums 32 + 32 side by side" Arith.xsys (sumsBeside k 32 32)
  go "sum 32 + 32" Arith.xsys (Arith.sum 32 32)
  go "balanced sum of 64 ones" Arith.xsys (compactX Arith.xsys.sys.ar (balanced 6).net)
  go "joinChain 64" Arith.xsys (joinChain 6 id)

def packed : IO Unit := do
  let go {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X0 : XNet S) : IO Unit := do
    let mut X := X0.short
    let mut r := 0
    let mut n := 0
    let mut peak := X.allIds.length
    let mut wide := 0
    for _ in [0:1000000] do
      let (Y, k) := X.parStep xs
      if k == 0 then break
      X := Y.short
      r := r + 1
      n := n + k
      peak := max peak X.allIds.length
      wide := max wide (X.allIds.foldl (fun m i => max m i.length) 0)
    let (Z, m) := X0.parRun xs 1000000
    let same := X.short == Z.short && m == n
    row s!"{nm}: pairs={n} rounds={r} peak ids={peak} longest name={wide} \
      input ids={X0.allIds.length} same as parRun={same}"
  let ar := Arith.xsys.sys.ar
  for k in [64, 256] do
    go s!"lnest {k}" Arith.xsys (compactX ar (Arith.lnest k).net)
  go "balanced sum of 256 ones" Arith.xsys (compactX ar (balanced 8).net)
  go "64 sums 32 + 32 side by side" Arith.xsys (sumsBeside 64 32 32)
  go "Peano 32 * 3" Peano.xsys (compactX Peano.xsys.sys.ar (Peano.PExpr.mul (.lit 32) (.lit 3)).net)
  go "combChain 256" Comb.dsystem (INet.combChain 8 (bitRev 8))

def reuse : IO Unit := do
  let go {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X0 : XNet S) : IO Unit := do
    let mut X := X0.short
    let fr := X.free
    let mut r := 0
    let mut n := 0
    let mut top := 0
    let mut freeSame := true
    let mut peak := X.allIds.length
    for _ in [0:1000000] do
      let (Y, k) := X.parStep xs
      if k == 0 then break
      X := Y.map (X.reuseName Y)
      peak := max peak X.allIds.length
      r := r + 1
      n := n + k
      freeSame := freeSame && X.free == fr
      top := max top (X.allIds.foldl (fun m i => max m (i.headD 0)) 0)
    let (Z, m) := X0.parRun xs 1000000
    let same := X.short == Z.short && m == n
    row s!"{nm}: pairs={n} rounds={r} largest number={top} \
      bound={peak} free kept={freeSame} same as parRun={same}"
  let ar := Arith.xsys.sys.ar
  go "lnest 64" Arith.xsys (compactX ar (Arith.lnest 64).net)
  go "balanced sum of 32 ones" Arith.xsys (compactX ar (balanced 5).net)
  go "4 sums 32 + 32 side by side" Arith.xsys (sumsBeside 4 32 32)
  go "Peano 16 * 3" Peano.xsys (compactX Peano.xsys.sys.ar (Peano.PExpr.mul (.lit 16) (.lit 3)).net)
  go "combChain 64" Comb.dsystem (INet.combChain 6 (bitRev 6))

def units : IO Unit := do
  let go {S : Type} [DecidableEq S] (nm : String) (xs : XSys S) (X0 : XNet S) : IO Unit := do
    let (D, W) := roundRun xs X0
    let mut line := s!"{nm}: W={W} D={D}"
    for p in [1, 4, 16] do
      let mut X := X0.short
      let fr := X.free
      let mut r := 0
      let mut w := 0
      let mut peak := X.allIds.length
      let mut top := 0
      let mut freeSame := true
      for _ in [0:W + 1] do
        let (Y, k) := X.parStepP xs p
        if k == 0 then break
        X := Y.map (X.reuseName Y)
        peak := max peak X.allIds.length
        top := max top (X.allIds.foldl (fun m i => max m (i.headD 0)) 0)
        r := r + 1
        w := w + k
        freeSame := freeSame && X.free == fr
      let ok := w == W && freeSame && (X.step xs).isNone
      line := line ++ s!" | p={p}: {r} (bound {W / p + D}) largest {top} \
        (bound {peak}){if ok then "" else " ?"}"
    row line
  let ar := Arith.xsys.sys.ar
  go "balanced sum of 32 ones" Arith.xsys (compactX ar (balanced 5).net)
  go "4 sums 32 + 32 side by side" Arith.xsys (sumsBeside 4 32 32)
  go "Peano 8 * 3" Peano.xsys (compactX Peano.xsys.sys.ar (Peano.PExpr.mul (.lit 8) (.lit 3)).net)
  go "joinChain 64" Arith.xsys (joinChain 6 id)

def tables : List (String × IO Unit) :=
  [("programs", programs), ("threads", threads), ("chain", chain), ("adversary", adversary),
    ("schedules", schedules), ("indexed", indexed), ("indexed-threads", indexedThreads),
    ("names", names), ("name-time", nameTime), ("short", short),
    ("end-to-end", endToEnd), ("rounds", rounds), ("rounds-p", roundsP), ("packed", packed),
    ("reuse", reuse), ("units", units)]

def main (args : List String) : IO UInt32 := do
  match args with
  | [t] =>
    match tables.lookup t with
    | some m => m; return 0
    | none => pure ()
  | _ => pure ()
  IO.println s!"usage: inets-measure <table>, one of {tables.map (·.1)}"
  return 1
