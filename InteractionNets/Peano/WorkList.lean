import InteractionNets.WorkList
import InteractionNets.Peano.Bound

/-! # Where rechecking only what a rule touched pays

A numeral of `k` successors, listed first, beside `k` pairs of an eraser
facing a zero.  Each pair is erased in one step, and nothing new is made.
`XMach` takes a fresh list of all agents after every claim and reads the
numeral again each time, so its actions grow as the square of `k`;
`WMach` keeps its list and reads everything once. -/

namespace INet
namespace Peano

/-- `k` pairs of an eraser facing a zero. -/
def eraPairs (k : Nat) : XNet Peano :=
  ⟨(List.range k).flatMap fun j => [([2 * j + 1, 9], era), ([2 * j + 2, 9], zero)], [],
    (List.range k).flatMap fun j =>
      [(([2 * j + 1, 9], 0), ([2 * j + 2, 9], 0)), (([2 * j + 2, 9], 0), ([2 * j + 1, 9], 0))]⟩

/-- The numeral `k` listed first, then `k` pairs of an eraser and a zero. -/
def inertThenPairs (k : Nat) : XNet Peano := ((lit k).tag 0).union (eraPairs k)

/-- Actions of one thread of `XMach` until it rests, within `fuel`. -/
def xActions : Nat → XMach Peano → Nat → Nat
  | 0, _, a => a
  | fuel + 1, M, a => if M.resting then a else xActions fuel (M.step xsys 0).1 (a + 1)

/-- Actions of one thread of `WMach` until it rests, within `fuel`. -/
def wActions : Nat → WMach Peano → Nat → Nat
  | 0, _, a => a
  | fuel + 1, M, a => if M.resting then a else wActions fuel (M.step xsys 0).1 (a + 1)

set_option maxRecDepth 100000

/-- With `k` = 10 the program that rescans takes 423 actions, and the one
that rechecks only what a rule touched 103. -/
example : xActions 10000 (XMach.init (inertThenPairs 10) 1) 0 = 423 := by
  decide +kernel
example : wActions 10000 (WMach.init (inertThenPairs 10) 1) 0 = 103 := by
  decide +kernel

/-- With `k` = 20: 1443 against 203. -/
example : xActions 10000 (XMach.init (inertThenPairs 20) 1) 0 = 1443 := by
  decide +kernel
example : wActions 10000 (WMach.init (inertThenPairs 20) 1) 0 = 203 := by
  decide +kernel

/-- With `k` = 40: 5283 against 403. -/
example : xActions 100000 (XMach.init (inertThenPairs 40) 1) 0 = 5283 := by
  decide +kernel
example : wActions 100000 (WMach.init (inertThenPairs 40) 1) 0 = 403 := by
  decide +kernel

end Peano
end INet
