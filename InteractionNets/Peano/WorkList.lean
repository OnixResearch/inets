import InteractionNets.WorkCount
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

/-! ### A bound on every fair run, from one evaluated run

One thread runs `inertThenPairs 10` to rest in 103 actions, making 10
claims, none of a rule that joins interface ports.  By
`WMach.fair_bound_ref`, every fair run, with any number of threads, is then
at rest with the normal form after `F * 992` actions, where `F` is the
window in which every thread acts: linear in the 10 steps, although the
system has a rule that joins interface ports (`0 + y`). -/

theorem inertThenPairs_ok : (inertThenPairs 10).Ok xsys.sys.ar := by
  decide +kernel

theorem inertThenPairs_ref :
    ((WMach.init (inertThenPairs 10) 1).trace xsys (fun _ => 0) 103).1.resting = true := by
  decide +kernel

theorem inertThenPairs_fair {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) (i : Nat)
    (hi : F * 992 ≤ i) :
    ((WMach.init (inertThenPairs 10) nt).trace xsys σ i).1.resting = true ∧
      ((WMach.init (inertThenPairs 10) nt).trace xsys σ i).2 = 10 := by
  have e₁ : ((WMach.init (inertThenPairs 10) 1).trace xsys (fun _ => 0) 103).2 = 10 := by
    decide +kernel
  have e₂ : WMach.joined xsys (fun _ => 0) (WMach.init (inertThenPairs 10) 1) 103 = 0 := by
    decide +kernel
  have ea : (inertThenPairs 10).agents.length = 31 := by decide +kernel
  have ew : (inertThenPairs 10).wires.length = 42 := by decide +kernel
  have hnd : ((inertThenPairs 10).agents.map Prod.fst).Nodup := by decide +kernel
  have h := WMach.fair_bound_ref inertThenPairs_ok.1 hnd xsys_bounded (Nat.one_pos)
    inertThenPairs_ref hnt σ hfair i (by rw [e₁, e₂, ea, ew]; exact hi)
  rw [e₁] at h
  exact ⟨h.1, h.2.1⟩

/-! ### Where a pass per joining claim is paid

The pass that `WMach.fair_bound` charges for each claim of a rule that
joins interface ports is not slack in the proof.  Beside a numeral listed
first, put `k` pairs of an adder facing a zero, each `0 + y` with `y` and
the result free: each claim joins, so the thread takes a fresh list after
it and reads the numeral again.  Both programs take the same, growing as
the square of `k`. -/

/-- `k` adders each facing a zero, with their other ports free. -/
def addZeroPairs (k : Nat) : XNet Peano :=
  ⟨(List.range k).flatMap fun j => [([2 * j + 1, 8], add), ([2 * j + 2, 8], zero)],
    (List.range k).flatMap fun j => [([2 * j + 1, 7], 0), ([2 * j + 2, 7], 0)],
    (List.range k).flatMap fun j =>
      [(([2 * j + 1, 8], 0), ([2 * j + 2, 8], 0)), (([2 * j + 2, 8], 0), ([2 * j + 1, 8], 0)),
       (([2 * j + 1, 8], 1), ([2 * j + 1, 7], 0)), (([2 * j + 1, 7], 0), ([2 * j + 1, 8], 1)),
       (([2 * j + 1, 8], 2), ([2 * j + 2, 7], 0)), (([2 * j + 2, 7], 0), ([2 * j + 1, 8], 2))]⟩

/-- The numeral `k` listed first, then `k` adders facing zeros. -/
def inertThenJoins (k : Nat) : XNet Peano := ((lit k).tag 0).union (addZeroPairs k)

example : (inertThenJoins 10).Ok xsys.sys.ar := by
  decide +kernel

/-- With `k` = 10, 20, 40 both programs take 443, 1483, 5363 actions, and
every claim joins. -/
example : xActions 10000 (XMach.init (inertThenJoins 10) 1) 0 = 443 := by
  decide +kernel
example : wActions 10000 (WMach.init (inertThenJoins 10) 1) 0 = 443 := by
  decide +kernel
example : WMach.joined xsys (fun _ => 0) (WMach.init (inertThenJoins 10) 1) 443 = 10 := by
  decide +kernel
example : wActions 10000 (WMach.init (inertThenJoins 20) 1) 0 = 1483 := by
  decide +kernel
example : wActions 100000 (WMach.init (inertThenJoins 40) 1) 0 = 5363 := by
  decide +kernel

end Peano
end INet
