import InteractionNets.Arith.Run
import InteractionNets.Embed

/-! # What is proved for `Arith`, in a larger system

Let the system of `Arith` be inside another system, by a map of symbols
that keeps the arities and the rules (`System.Embeds`).  Then whatever a
net of `Arith` reduces to, the thread machine of the larger system
reaches on the relabelled memory, with the same claims and the same
numerals (`carry_rest`, `carry_fair`).  In particular every expression of
additions comes out right there (`Expr.rest_embed`).
-/

namespace INet

namespace Arith

variable {S₂ : Type} [DecidableEq S₂] {ι : Arith → S₂}

/-- **What is proved for a net of `Arith` holds in a larger system.**
Let the system of `Arith` be inside the system of `xs₂`, and let a memory
hold a well-formed net of `Arith` that reduces in `n` steps to a normal
form.  Then, with any number of threads and any schedule, a run of the
program of `xs₂` on the relabelled memory that ends at rest has made `n`
claims, and every numeral of the normal form is in the memory. -/
theorem carry_rest (xs₂ : XSys S₂) (h : system.Embeds ι xs₂.sys) {X : XNet Arith}
    (hX : X.toNet.WF ar) {n : Nat} {N' : Net Arith} (s : Steps (Step system) n X.toNet N')
    (nN : Normal (Step system) N') {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.resting = true) :
    ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).2 = n ∧
      ∀ p k, IsNum N' p k → Addition.IsNum xs₂.sys.ar (ι zero) (ι succ)
        ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.mem.toNet p k := by
  obtain ⟨hc, hm⟩ := XMach.relabel_rest xs₂ h hX s nN hnt σ hr
  rw [hm]
  exact ⟨hc, fun p k hk => Addition.IsNum.relabel h hk⟩

/-- **The same under a fair schedule**: from some action on every thread
is at rest, the claims are `n`, and every numeral of the normal form is
in the memory. -/
theorem carry_fair (xs₂ : XSys S₂) (h : system.Embeds ι xs₂.sys) {X : XNet Arith}
    (hX : X.toNet.WF ar) {n : Nat} {N' : Net Arith} (s : Steps (Step system) n X.toNet N')
    (nN : Normal (Step system) N') {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.resting = true ∧
      ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).2 = n ∧
      ∀ p k, IsNum N' p k → Addition.IsNum xs₂.sys.ar (ι zero) (ι succ)
        ((XMach.init (X.relabel ι) nt).trace xs₂ σ i).1.mem.toNet p k := by
  obtain ⟨i₀, hh⟩ := XMach.relabel_fair xs₂ h hX s nN hnt σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, hc, hm⟩ := hh i hi
  rw [hm]
  exact ⟨hr, hc, fun p k hk => Addition.IsNum.relabel h hk⟩

/-- **Every expression comes out right in a larger system.**  With any
number of threads and any schedule, a run of the program of `xs₂` on the
relabelled net of an expression that ends at rest has made the
interactions counted by `Expr.cost`, and the memory has the numeral of
the value on the free port. -/
theorem Expr.rest_embed (xs₂ : XSys S₂) (h : system.Embeds ι xs₂.sys) (e : Expr) {nt : Nat}
    (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (e.net.relabel ι) nt).trace xs₂ σ i).1.resting = true) :
    ((XMach.init (e.net.relabel ι) nt).trace xs₂ σ i).2 = e.cost ∧
      Addition.IsNum xs₂.sys.ar (ι zero) (ι succ)
        ((XMach.init (e.net.relabel ι) nt).trace xs₂ σ i).1.mem.toNet e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  obtain ⟨hc, hm⟩ := carry_rest xs₂ h hX hs (normal_of_no_add hno) hnt σ hr
  exact ⟨hc, hm _ _ hA⟩

end Arith

end INet
