import InteractionNets.Window

/-! ## Measuring the compiled program

No theorem of this development is about compiled code.  This section is the
program that was compiled and timed for the note on measurement in the
scope notes: it runs addition on ordered maps alone, on one thread, once
with everything counted and then, for the same number of actions, with
nothing counted and the clock running.  Nothing here is proved, and
nothing above depends on it. -/

namespace INet.Arith

/-- The actions to rest and the time with everything counted. -/
def runCount (X : XNet Arith) (fuel : Nat) : Nat × Nat := Id.run do
  let mut cur := OMach.init X 1
  let mut ct := 0
  for i in [0:fuel] do
    if cur.resting then return (i, ct)
    ct := ct + cur.stepFcost xsys 0
    cur := (cur.step xsys 0).1
  return (fuel, ct)

/-- The program alone: `steps` actions, nothing counted. -/
def runPlain (X : XNet Arith) (steps : Nat) : Nat := Id.run do
  let mut cur := OMach.init X 1
  for _ in [0:steps] do
    cur := (cur.step xsys 0).1
  return cur.mem.stamp

end INet.Arith

/-- For `k + k` with `k` from 24 to 768: the actions, the count, the time
of a run in nanoseconds, and the time for each unit counted in
picoseconds. -/
def main : IO Unit := do
  for k in [24, 48, 96, 192, 384, 768] do
    let X := INet.Arith.sum k k
    let (steps, cnt) := INet.Arith.runCount X 10000000
    let reps := if k ≤ 96 then 20 else 5
    let mut acc := 0
    let t0 ← IO.monoNanosNow
    for _ in [0:reps] do
      acc := acc + INet.Arith.runPlain X steps
    let t1 ← IO.monoNanosNow
    let ns := (t1 - t0) / reps
    IO.println s!"{k} actions={steps} count={cnt} ns={ns} ps/count={ns * 1000 / cnt} check={acc}"
