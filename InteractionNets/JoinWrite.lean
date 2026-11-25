import InteractionNets.JoinMulti

/-! # A rule that joins and writes

No system of the development has a rule that both joins two interface
ports and writes agents, so the bound of `JMach.rests_multi` for such rules
was not exercised.  `Mix` has one: an `m` (three auxiliary ports) facing an
`e` (one) joins the first two ports of `m`, and writes a new `e` whose
principal port takes the third port of `m` and whose auxiliary port takes
the port of the old `e`.  The system joins one segment at most and writes
one agent and eight ports at most (`Mix.xsys_joinsAtMost`,
`Mix.xsys_bounded`), so one thread is at rest after `O(n + K log K)`
actions (`Mix.rests`).  `mixChain` chains `m`s by their first two ports,
like `joinChain`; its run is checked in the kernel for eight pairs, and
measured: 4, 9, 21, 53, 133, 325, 773 actions of walks for 1 to 64 pairs
in bit-reversed order, the same as `joinChain` (`2 n b + 5` for `n = 2 ^ b`,
`b ≥ 1`). -/

namespace INet

/-- Two symbols. -/
inductive Mix
  | m | e
  deriving DecidableEq, Repr

namespace Mix

/-- `m` has three auxiliary ports, `e` one. -/
def ar : Mix → Nat
  | m => 3
  | e => 1

/-- `m ⋈ e` joins the first two ports of `m` and writes a new `e` between
the third port of `m` and the port of the old `e`; `e ⋈ m` is its mirror. -/
def data : SysData Mix :=
  ⟨ar, [((m, e), RuleData.ofWires [((none, 0), e)]
      [(.ifc false 0, .ifc false 1), (.ifc false 2, .new none 0 0),
        (.new none 0 1, .ifc true 0)]),
    ((e, m), RuleData.ofWires [((none, 0), e)]
      [(.ifc true 0, .ifc true 1), (.ifc true 2, .new none 0 0),
        (.new none 0 1, .ifc false 0)])]⟩

/-- The system, by evaluation of the check. -/
def xsys : XSys Mix := data.toXSys (by decide)

/-- The rule joins two interface ports and writes an agent. -/
theorem _root_.INet.Checks.JoinWrite.c1
    : ∃ R, xsys.rule m e = some R ∧ R.joins xsys.sys.ar m e = true ∧ R.slots ≠ [] :=
  ⟨_, rfl, by decide, by decide⟩

theorem xsys_joinsAtMost : xsys.JoinsAtMost 1 := XSys.joinsAtMost_of fun α β R h => by
  cases α <;> cases β <;> cases h <;> decide

theorem xsys_bounded : xsys.Bounded 1 8 := by
  intro α β R h
  cases α <;> cases β <;> cases h <;> decide

end Mix

/-- **One thread of `Mix` is at rest after `O(n + K log K)` actions**,
`K = |wires| + 8 n`, though its rule joins and writes. -/
theorem Mix.rests {X : XNet Mix} (hX : X.toNet.WF Mix.xsys.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {n : Nat} {N' : Net Mix}
    (hs : Steps (Step Mix.xsys.sys) n X.toNet N') (hn : Normal (Step Mix.xsys.sys) N')
    (i : Nat)
    (hi : 7 * X.agents.length + 2 * (X.wires.length + 8 * n) +
        1 * (4 * ((X.wires.length + 8 * n) * Nat.log2 (X.wires.length + 8 * n + 1)) +
          6 * (X.wires.length + 8 * n)) + n * (1 + 8 + 1 + 9 * 1) + 7 * (1 * n) < i) :
    ((JMach.init X 1).trace Mix.xsys (fun _ => 0) i).1.resting = true ∧
      ((JMach.init X 1).trace Mix.xsys (fun _ => 0) i).2 = n ∧
      ((JMach.init X 1).trace Mix.xsys (fun _ => 0) i).1.mem.toNet = N' :=
  JMach.rests_multi_final Mix.xsys_joinsAtMost hX hnd Mix.xsys_bounded hs hn i hi

/-- `2 ^ b` pairs `m ⋈ e`, the second port of each `m` wired to the first of
the next, the third port of each `m` and the port of each `e` free. -/
def mixChain (b : Nat) (order : Nat → Nat) : XNet Mix :=
  let n := 2 ^ b
  ⟨((List.range n).map order).flatMap fun i => [([2 * i + 1], Mix.m), ([2 * i + 2], Mix.e)],
    [([0], 0), ([0], 1)] ++ (List.range n).flatMap (fun i => [([0], 2 * i + 2), ([0], 2 * i + 3)]),
    ((List.range n).flatMap fun i =>
      [(([2 * i + 1], 0), ([2 * i + 2], 0)), (([2 * i + 2], 0), ([2 * i + 1], 0)),
        (([2 * i + 1], 3), ([0], 2 * i + 2)), (([0], 2 * i + 2), ([2 * i + 1], 3)),
        (([2 * i + 2], 1), ([0], 2 * i + 3)), (([0], 2 * i + 3), ([2 * i + 2], 1))]) ++
    ((List.range (n - 1)).flatMap fun i =>
      [(([2 * i + 1], 2), ([2 * (i + 1) + 1], 1)), (([2 * (i + 1) + 1], 1), ([2 * i + 1], 2))]) ++
    [(([0], 0), ([1], 1)), (([1], 1), ([0], 0)),
      (([2 * (n - 1) + 1], 2), ([0], 1)), (([0], 1), ([2 * (n - 1) + 1], 2))]⟩

set_option maxRecDepth 100000

theorem _root_.INet.Checks.JoinWrite.c2
    : (mixChain 3 (bitRev 3)).Ok Mix.xsys.sys.ar := by decide +kernel

/-- Eight pairs, bits reversed: at rest after 197 actions and not before,
eight claims, 53 actions of walks, as for `joinChain`: the agents the rule
writes do not lengthen the walks. -/
theorem _root_.INet.Checks.JoinWrite.c3 :
    ((JMach.init (mixChain 3 (bitRev 3)) 1).trace Mix.xsys (fun _ => 0) 197).1.resting = true ∧
      ((JMach.init (mixChain 3 (bitRev 3)) 1).trace Mix.xsys (fun _ => 0) 197).2 = 8 := by
  decide +kernel
theorem _root_.INet.Checks.JoinWrite.c4 :
    ((JMach.init (mixChain 3 (bitRev 3)) 1).trace Mix.xsys (fun _ => 0) 196).1.resting = false := by
  decide +kernel
theorem _root_.INet.Checks.JoinWrite.c5 :
    JMach.walked Mix.xsys (fun _ => 0) (JMach.init (mixChain 3 (bitRev 3)) 1) 197 = 53 := by
  decide +kernel

end INet
