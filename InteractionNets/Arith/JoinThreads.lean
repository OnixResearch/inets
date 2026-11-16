import InteractionNets.MeasureJoin

/-! # Several threads: walks can cost the square

With one thread the walks of `JMach` cost `O(n log n)` on any net
(`JMach.walked_log`).  With several threads they need not: on the chain of
`n` adders in order (`joinChain`), with `n` threads and a schedule that
gives the turn to a thread that is not walking whenever there is one
(`jAdversary`), the claims run ahead of the walks, the wires grow under
them, and the walks take more than `n * n` actions.  Checked here in the
kernel for 16 adders: 296 actions of walks, against 79 with one thread
(for 32 adders, 1104 against 159, evaluated).  Measured up to 1,024 adders
in `MeasureJoin`. -/

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

end INet
