import InteractionNets.MeasureJoin
import InteractionNets.IndexedJoin

/-! # The program that walks joined wires, on the indexed memory: runs

Hashing is opaque to the kernel, but `IJMach.time_shadow` makes the time of
the indexed program, on a well-formed net that lists no agent twice, the
function `JMach.itime` along the run of `JMach`, which the kernel
evaluates.  One thread on the chain of adders with the bits of the
positions reversed (`joinChain`): 8 adders take 444 operations on the maps
and cells, 16 take 981, both nets checked well formed and without a name
twice in the kernel.  Measured as programs in `MeasureJoin`, with the hash
maps compiled, the time stays at about 3.5 operations an action up to
4,096 adders. -/

namespace INet

set_option maxRecDepth 100000

theorem Arith.chain3_ok : (joinChain 3 (bitRev 3)).Ok Arith.xsys.sys.ar := by decide +kernel

theorem Arith.chain3_nodup : ((joinChain 3 (bitRev 3)).agents.map Prod.fst).Nodup := by
  decide +kernel

theorem Arith.chain4_ok : (joinChain 4 (bitRev 4)).Ok Arith.xsys.sys.ar := by decide +kernel

theorem Arith.chain4_nodup : ((joinChain 4 (bitRev 4)).agents.map Prod.fst).Nodup := by
  decide +kernel

/-- **Eight adders, one thread, on the indexed memory: 444 operations.** -/
theorem Arith.chain3_itime :
    (IJMach.init (joinChain 3 (bitRev 3)) 1).time Arith.xsys (fun _ => 0) 200 = 444 := by
  rw [IJMach.time_shadow Arith.chain3_ok.1 Arith.chain3_nodup Nat.one_pos]
  decide +kernel

/-- **Sixteen adders, one thread, on the indexed memory: 981 operations.** -/
theorem Arith.chain4_itime :
    (IJMach.init (joinChain 4 (bitRev 4)) 1).time Arith.xsys (fun _ => 0) 400 = 981 := by
  rw [IJMach.time_shadow Arith.chain4_ok.1 Arith.chain4_nodup Nat.one_pos]
  decide +kernel

end INet
