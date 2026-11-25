import InteractionNets.MeasureJoin
import InteractionNets.IndexedJoin

/-! # The program that walks joined wires, on the indexed memory: runs

`IJMach.time_shadow` makes the time of the indexed program a function the
kernel evaluates along the run of `JMach`.  One thread on the chain of
adders with the bits of the positions reversed (`joinChain`): 8 adders take
444 operations on the maps and cells, 16 take 981.  Measured as programs
in `MeasureJoin`, with the hash maps compiled, the time stays at about 3.5
operations an action up to 4,096 adders. -/

namespace INet

set_option maxRecDepth 100000

/-- Eight adders, one thread: 444 operations. -/
example :
    JMach.itime Arith.xsys (fun _ => 0) (JMach.init (joinChain 3 (bitRev 3)) 1) 200 = 444 := by
  decide +kernel

/-- Sixteen adders, one thread: 981 operations. -/
example :
    JMach.itime Arith.xsys (fun _ => 0) (JMach.init (joinChain 4 (bitRev 4)) 1) 400 = 981 := by
  decide +kernel

end INet
