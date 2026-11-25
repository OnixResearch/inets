import InteractionNets.MeasureJoin

/-! # A chain of joins

`joinChain b order` (in `MeasureJoin.lean`) is a chain of `2 ^ b` adders,
each facing a zero.  It is a well-formed net, and one thread of `JMach`
brings it to rest with every adder gone; the walks are counted here for
`b = 3`, in order and with the bits reversed, in the kernel. -/

namespace INet

set_option maxRecDepth 100000

theorem _root_.INet.Checks.Arith.JoinChain.c1
    : (joinChain 3 id).Ok Arith.xsys.sys.ar := by decide +kernel
theorem _root_.INet.Checks.Arith.JoinChain.c2
    : (joinChain 3 (bitRev 3)).Ok Arith.xsys.sys.ar := by decide +kernel

/-- In order, eight joins: 39 walk actions; bits reversed: 53. -/
theorem _root_.INet.Checks.Arith.JoinChain.c3
    : jStats Arith.xsys 1 (JMach.init (joinChain 3 id) 1) 10000 = (111, 8, 0, 39) := by
  decide +kernel
theorem _root_.INet.Checks.Arith.JoinChain.c4
    : jStats Arith.xsys 1 (JMach.init (joinChain 3 (bitRev 3)) 1) 10000 =
    (125, 8, 0, 53) := by
  decide +kernel

end INet
