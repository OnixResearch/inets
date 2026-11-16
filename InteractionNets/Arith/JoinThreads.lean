import InteractionNets.MeasureJoin
import InteractionNets.SchedRun

/-! # Several threads: walks can cost the square

With one thread the walks of `JMach` cost `O(n log n)` on any net
(`JMach.walked_log`).  With several threads they need not: on the chain of
`n` adders in order (`joinChain`), with `n` threads and a schedule that
gives the turn to a thread that is not walking whenever there is one
(`jAdversary`), the claims run ahead of the walks, the wires grow under
them, and the walks take more than `n * n` actions.  Checked here in the
kernel for 16 adders: 296 actions of walks, against 79 with one thread
(for 32 adders, 1104 against 159, evaluated).  Measured up to 1,024 adders
in `MeasureJoin`.  When a thread that has claimed keeps the turn until it
has written and walked, the walks cost what they cost with one thread
(proved: `JMach.walked_cs`; checked here for the same net). -/

namespace INet

set_option maxRecDepth 100000

/-- Sixteen adders, sixteen threads, claims first: 296 actions of walks,
more than `16 * 16`. -/
example :
    jAdversary Arith.xsys (JMach.init (joinChain 4 id) 16) 16 100000 false = (999, 296) := by
  decide +kernel

/-- One thread on the same net: 79 actions of walks. -/
example : jStats Arith.xsys 1 (JMach.init (joinChain 4 id) 1) 100000 = (223, 16, 0, 79) := by
  decide +kernel

/-- The same net and threads, when a thread in a claim keeps the turn
(`jCritical`, the schedules of `JMach.walked_cs`): 79 actions of walks,
as with one thread. -/
example : jCritical Arith.xsys (JMach.init (joinChain 4 id) 16) 16 100000 = (1087, 79) := by
  decide +kernel

/-- The busy-first measuring run (`JMach.bfRun`, proved to follow the
schedule of `JMach.rests_bfSched`) on the same net and threads: at rest
after 703 actions, 79 of them walks. -/
example : JMach.bfRun Arith.xsys (joinChain 4 id) 16 100000 = (703, 79) := by
  decide +kernel

/-- The measuring run where turns go round (`JMach.csRun`, proved to follow
`JMach.csSched`): at rest after 1008 actions, 91 of them walks.  More walks
than one thread here, but within the bound of `JMach.csRun_walked`. -/
example : JMach.csRun Arith.xsys (joinChain 4 id) 16 100000 = (1008, 91) := by
  decide +kernel

end INet
