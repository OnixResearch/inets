import InteractionNets.Arith.AnyNets
import InteractionNets.Union

/-! # Side by side in a system with an agent of neither side

The results of `Union` hold for any interaction system.  Here they are
used in the system `Solo`, whose only rule makes an agent that belongs to
neither of the two agents that meet, so that the tagged results of
`Arith/AnyNets` do not apply to it.  What the list reducer computes is
turned into a reduction by steps (`XNet.normalize_steps`), and two copies
of a net are run side by side under tags.
-/

namespace INet

section Bridge

variable {S : Type} [DecidableEq S]

/-- **What the reducer returns is reached by steps.**  If `normalize`
returns the memory `Y` after `k` steps, the net of the start reduces in
`k` steps to a normal form whose compact form is the net of `Y`. -/
theorem XNet.normalize_steps {xs : XSys S} {X Y : XNet S} {n k : Nat}
    (h : X.normalize xs n = some (Y, k)) :
    X.toNet.WF xs.sys.ar ∧ ∃ N', Steps (Step xs.sys) k X.toNet N' ∧
      Normal (Step xs.sys) N' ∧ Y.toNet = N'.compact xs.sys.ar := by
  obtain ⟨hX, -, sts, hn, -⟩ := XNet.normalize_spec h
  have sts' : Steps (CStep xs.sys) k (X.toNet.compact xs.sys.ar) Y.toNet := by
    rw [hX.2]
    exact sts
  obtain ⟨N', hs, e⟩ := Steps.lift hX.1 sts'
  refine ⟨hX.1, N', hs, ?_, e⟩
  refine (normal_compact (Steps.wf hX.1 hs)).2 ?_
  rw [← e]
  exact hn

end Bridge

namespace Solo

/-- The rule of `Solo` makes an agent that belongs to neither side. -/
theorem _root_.INet.Checks.UnionExamples.c1 : ¬ Solo.system.Sided := by
  intro h
  have h0 := h A A _ rfl 0
  cases h0

/-- Two copies of the net `aa` side by side under the tags `0` and `1`,
with any number of threads and any schedule: a run that ends at rest has
made two claims, one for each copy, and the memory holds two nets side by
side, each a renaming of a normal form of `aa` whose compact form is the
single `B` wired to itself. -/
theorem _root_.INet.Checks.UnionExamples.c2 {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init ((xaa.tag 0).union (xaa.tag 1)) nt).trace xsystem σ i).1.resting = true) :
    ((XMach.init ((xaa.tag 0).union (xaa.tag 1)) nt).trace xsystem σ i).2 = 2 ∧
      ∃ (g g' : Id → Id) (A' B' : Net Solo),
        ((XMach.init ((xaa.tag 0).union (xaa.tag 1)) nt).trace xsystem σ i).1.mem.toNet =
          (A'.map g).union (B'.map g') ∧
        Renaming g A' ∧ Renaming g' B' ∧
        xaaOut.toNet = A'.compact xsystem.sys.ar ∧ xaaOut.toNet = B'.compact xsystem.sys.ar := by
  obtain ⟨hX, A', sA, nA, eA⟩ := XNet.normalize_steps xaa_normalize
  obtain ⟨g, g', hg, hg', -, -, hc, hm⟩ :=
    XMach.tagged_rest xsystem hX hX (c := 0) (c' := 1) (by decide) sA nA sA nA hnt σ hr
  exact ⟨hc, g, g', A', A', hm, hg, hg', eA, eA⟩

end Solo

end INet
