import InteractionNets.JoinPay
import InteractionNets.Arith.JoinChain
import InteractionNets.Peano
import InteractionNets.Extra
import InteractionNets.Window
import InteractionNets.LongRun
import InteractionNets.Examples

/-! # Which systems pay for their walks

`JMach.walked_log` (and the weaker `JMach.walked_bound`) bounds the walks
of one thread for a system whose rules join one segment at most
(`XSys.OneJoin`) and do nothing else when they join (`XSys.PureJoin`).
Both are checked here rule by rule for the systems of the development:
arithmetic, Peano arithmetic, the system of `Extra`, the chains of
`Window`, the system of `LongRun` and the one-symbol system of `Examples`
have both.  The interaction combinators do not have the first: two agents
of the same kind annihilate by joining two segments (the second holds of
them, but says nothing of such a rule).

The counter `JMach.walked` of the bound is checked against the count of
`jStats` on the chain of eight joins of `Arith.JoinChain`.
-/

namespace INet

theorem Arith.xsys_oneJoin : Arith.xsys.OneJoin := XSys.oneJoin_of fun α β R h => by
  cases α <;> cases β <;> cases h <;> decide

theorem Arith.xsys_pureJoin : Arith.xsys.PureJoin := XSys.pureJoin_of fun α β R h hj => by
  cases α <;> cases β <;> cases h <;> revert hj <;> decide

theorem Peano.xsys_oneJoin : Peano.xsys.OneJoin := XSys.oneJoin_of fun α β R h => by
  cases α <;> cases β <;> cases h <;> decide

theorem Peano.xsys_pureJoin : Peano.xsys.PureJoin := XSys.pureJoin_of fun α β R h hj => by
  cases α <;> cases β <;> cases h <;> revert hj <;> decide

theorem Extra.xsys_oneJoin : Extra.xsys.OneJoin := XSys.oneJoin_of fun α β R h => by
  cases α <;> cases β <;> cases h <;> decide

theorem Extra.xsys_pureJoin : Extra.xsys.PureJoin := XSys.pureJoin_of fun α β R h hj => by
  cases α <;> cases β <;> cases h <;> revert hj <;> decide

theorem Chain.xsys_oneJoin : Chain.xsys.OneJoin := XSys.oneJoin_of fun α β R h => by
  cases α <;> cases β <;> cases h <;> decide

theorem Chain.xsys_pureJoin : Chain.xsys.PureJoin := XSys.pureJoin_of fun α β R h hj => by
  cases α <;> cases β <;> cases h <;> revert hj <;> decide

theorem Eps.xsys_oneJoin : Eps.xsys.OneJoin := XSys.oneJoin_of fun α β R h => by
  cases α <;> cases β <;> cases h <;> decide

theorem Eps.xsys_pureJoin : Eps.xsys.PureJoin := XSys.pureJoin_of fun α β R h hj => by
  cases α <;> cases β <;> cases h <;> revert hj <;> decide

theorem Solo.xsystem_oneJoin : Solo.xsystem.OneJoin := XSys.oneJoin_of fun α β R h => by
  cases α <;> cases β <;> cases h <;> decide

theorem Solo.xsystem_pureJoin : Solo.xsystem.PureJoin := XSys.pureJoin_of fun α β R h hj => by
  cases α <;> cases β <;> cases h <;> revert hj <;> decide

theorem Comb.dsystem_pureJoin : Comb.dsystem.PureJoin := XSys.pureJoin_of fun α β R h hj => by
  cases α <;> cases β <;> cases h <;> revert hj <;> decide

/-- Two combinators of the same kind annihilate by joining two segments. -/
theorem Comb.dsystem_not_oneJoin : ¬ Comb.dsystem.OneJoin := fun h => by
  have := h Comb.γ Comb.γ _ [] [] rfl
  revert this
  decide

/-- **The walks of one thread of arithmetic cost `O(K log K + K²)`**, `K`
bounding the segments of the normal form. -/
theorem Arith.walked_bound {X : XNet Arith} (hX : X.toNet.WF Arith.xsys.sys.ar) {C D : Nat}
    (hb : Arith.xsys.Bounded C D) {n : Nat} {N' : Net Arith}
    (hs : Steps (Step Arith.xsys.sys) n X.toNet N') (hn : Normal (Step Arith.xsys.sys) N')
    (i : Nat) :
    JMach.walked Arith.xsys (fun _ => 0) (JMach.init X 1) i ≤
      3 * n + 4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        2 * ((X.wires.length + D * n) * (X.wires.length + D * n + 1)) +
        2 * (X.wires.length + D * n) :=
  JMach.walked_bound Arith.xsys_oneJoin Arith.xsys_pureJoin hX hb hs hn i

/-- **The walks of one thread of arithmetic cost `O(n + K log K)`**: at
most `3 n + 4 K log (K + 1) + 6 K`, with `n` the steps to the normal form
and `K = |wires| + 8 n`. -/
theorem Arith.walked_log {X : XNet Arith} (hX : X.toNet.WF Arith.xsys.sys.ar) {n : Nat}
    {N' : Net Arith} (hs : Steps (Step Arith.xsys.sys) n X.toNet N')
    (hn : Normal (Step Arith.xsys.sys) N') (i : Nat) :
    JMach.walked Arith.xsys (fun _ => 0) (JMach.init X 1) i ≤
      3 * n + 4 * ((X.wires.length + 8 * n) * Nat.log2 (X.wires.length + 8 * n + 1)) +
        6 * (X.wires.length + 8 * n) :=
  JMach.walked_log Arith.xsys_oneJoin Arith.xsys_pureJoin hX Arith.xsys_bounded hs hn i

set_option maxRecDepth 100000

/-- The counter of the bound counts what `jStats` counts: 39 actions of
walks in order, 53 with the bits reversed. -/
example : JMach.walked Arith.xsys (fun _ => 0) (JMach.init (joinChain 3 id) 1) 111 = 39 := by
  decide +kernel
example :
    JMach.walked Arith.xsys (fun _ => 0) (JMach.init (joinChain 3 (bitRev 3)) 1) 125 = 53 := by
  decide +kernel

end INet
