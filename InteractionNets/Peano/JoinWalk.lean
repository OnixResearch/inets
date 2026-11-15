import InteractionNets.JoinWalk
import InteractionNets.Peano.WorkList

/-! # Where walking the joined wires pays

Beside a numeral listed first, `k` pairs of an adder facing a zero, `0 + y`
with `y` and the result free (`Peano.inertThenJoins`).  Every claim joins.
`XMach` and `WMach` take a fresh list after each and read the numeral again,
so their actions grow as the square of `k` (443, 1483, 5363 for `k` = 10,
20, 40).  `JMach` walks the joined wire instead: both sides end at free
ports after a segment or two, and it takes 163, 323 and 643 actions. -/

namespace INet
namespace Peano

/-- Actions of one thread of `JMach` until it rests, within `fuel`. -/
def jActions : Nat → JMach Peano → Nat → Nat
  | 0, _, a => a
  | fuel + 1, M, a => if M.resting then a else jActions fuel (M.step xsys 0).1 (a + 1)

set_option maxRecDepth 100000

example : jActions 10000 (JMach.init (inertThenJoins 10) 1) 0 = 163 := by
  decide +kernel
example : jActions 10000 (JMach.init (inertThenJoins 20) 1) 0 = 323 := by
  decide +kernel
example : jActions 100000 (JMach.init (inertThenJoins 40) 1) 0 = 643 := by
  decide +kernel

/-- Two threads taking turns on `inertThenJoins 10` for 300 actions end
idle after the 10 claims the list reducer takes, so the memory holds the
normal form that the list reducer returns (`JMach.exec_agrees`). -/
example :
    Normal (Step xsys.sys)
        ((JMach.init (inertThenJoins 10) 2).exec xsys ((List.range 300).map (· % 2))).1.mem.toNet ∧
      ((JMach.init (inertThenJoins 10) 2).exec xsys
          ((List.range 300).map (· % 2))).1.mem.toNet.compact xsys.sys.ar =
        ((inertThenJoins 10).run xsys 100).1.toNet :=
  JMach.exec_agrees (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- An adder facing a zero, with its two other ports wired to each other.
The rule joins them, and the joined wire is a loop: the walk comes back to
where it started, and stops. -/
def selfLoop : XNet Peano :=
  ⟨[([1], add), ([2], zero)], [],
    [(([1], 0), ([2], 0)), (([2], 0), ([1], 0)), (([1], 1), ([1], 2)), (([1], 2), ([1], 1))]⟩

example : selfLoop.Ok xsys.sys.ar := by
  decide +kernel

example : jActions 100 (JMach.init selfLoop 1) 0 = 11 := by
  decide +kernel

example :
    Normal (Step xsys.sys)
      ((JMach.init selfLoop 2).exec xsys ((List.range 40).map (· % 2))).1.mem.toNet :=
  (JMach.exec_agrees (f := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1

end Peano
end INet
