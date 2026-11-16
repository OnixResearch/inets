import InteractionNets.JoinMulti

/-! # A chain of annihilations

`combChain b order`: `2 ^ b` pairs of combinators `γ` facing each other,
each pair wired to the next by both auxiliary ports, so that every
annihilation joins two segments of one long double wire.  One thread of
`JMach` brings it to its normal form; the walks cost about `n log n` when
the pairs are listed with the bits of their positions reversed.

Measured with one thread (bit-reversed order), against the bound of
`Comb.rests_multi`:

| pairs | actions | walks  | bound      | ratio |
|-------|---------|--------|------------|-------|
| 16    | 441     | 265    | 29064      | 66    |
| 256   | 11017   | 8201   | 640696     | 58    |
| 1024  | 52233   | 40969  | 2921976    | 56    |
| 4096  | 241673  | 196617 | 13128248   | 54    |

In order, the actions are 20 per pair (81919 for 4096 pairs).  The bound
charges every claim the 16 segments of a commutation, while an annihilation
writes 4: with `K` the segments of the normal form (`10 n + 4` here,
measured), `JMach.rests_multi_sized` gives a bound 24 to 29 times the
actions.  The tables are measured, not proved; the run for `b = 3` is
checked in the kernel. -/

namespace INet

/-- `2 ^ b` facing pairs of `γ`, chained by both auxiliary ports, with four
free ports at the two ends. -/
def combChain (b : Nat) (order : Nat → Nat) : XNet Comb :=
  let n := 2 ^ b
  ⟨((List.range n).map order).flatMap fun i =>
      [([2 * i + 1], Comb.γ), ([2 * i + 2], Comb.γ)],
    [([0], 0), ([0], 1), ([0], 2), ([0], 3)],
    ((List.range n).flatMap fun i =>
      [(([2 * i + 1], 0), ([2 * i + 2], 0)), (([2 * i + 2], 0), ([2 * i + 1], 0))]) ++
    ((List.range (n - 1)).flatMap fun i =>
      [(([2 * i + 2], 1), ([2 * (i + 1) + 1], 1)), (([2 * (i + 1) + 1], 1), ([2 * i + 2], 1)),
       (([2 * i + 2], 2), ([2 * (i + 1) + 1], 2)), (([2 * (i + 1) + 1], 2), ([2 * i + 2], 2))]) ++
    [(([0], 0), ([1], 1)), (([1], 1), ([0], 0)), (([0], 1), ([1], 2)), (([1], 2), ([0], 1)),
     (([0], 2), ([2 * (n - 1) + 2], 1)), (([2 * (n - 1) + 2], 1), ([0], 2)),
     (([0], 3), ([2 * (n - 1) + 2], 2)), (([2 * (n - 1) + 2], 2), ([0], 3))]⟩
set_option maxRecDepth 100000
example : (combChain 3 (bitRev 3)).Ok Comb.dsystem.sys.ar := by decide +kernel
/-- Eight pairs, bits reversed: at rest after 193 actions, not before, 105
of them in walks. -/
example :
    JMach.walked Comb.dsystem (fun _ => 0) (JMach.init (combChain 3 (bitRev 3)) 1) 193 = 105 := by
  decide +kernel
example :
    ((JMach.init (combChain 3 (bitRev 3)) 1).trace Comb.dsystem (fun _ => 0) 193).1.resting =
      true := by
  decide +kernel
example :
    ((JMach.init (combChain 3 (bitRev 3)) 1).trace Comb.dsystem (fun _ => 0) 192).1.resting =
      false := by
  decide +kernel

end INet
