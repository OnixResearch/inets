import InteractionNets.Arith.Bound
import InteractionNets.WorkCount

/-! # Expressions of additions on the program that rechecks only what a rule touched

In unary addition every rule takes out as many adders as it writes, but
for `0 + y`, which joins two interface ports and takes its adder out.  So
the claims that join are at most the adders of the start
(`WMach.joined_le_census`), one per `+` of the expression (`Expr.adds`),
and `WMach.fair_bound` gives a bound in the size of the expression and its
steps, with no evaluated run (`Arith.Expr.wfair`).
-/

namespace INet
namespace Arith

/-- Every rule of `Arith` takes out as many adders as it writes, but for
the rule that joins interface ports. -/
theorem census_add : ∀ (α β : Arith) (R : XRhs Arith) (a b : Id), a ≠ b →
    xsys.rule α β = some R →
    (R.newAgents a b).countP (fun e => decide (e.2 = Arith.add)) +
      (if R.joins xsys.sys.ar α β then 1 else 0) =
      (if α = Arith.add then 1 else 0) + (if β = Arith.add then 1 else 0) := by
  intro α β R a b hab h
  cases α <;> cases β <;> cases h <;>
    first
    | rfl
    | simp (config := { decide := true }) [XRhs.newAgents, childList, child, dedupFst, addSucc,
        RuleData.toX, RuleData.swap, RuleData.ofWires, assoc, par, slot, hab, Ne.symm hab]

/-- The additions of an expression. -/
def Expr.adds : Expr → Nat
  | .lit _ => 0
  | .add e₁ e₂ => e₁.adds + e₂.adds + 1

theorem lit_adds (n : Nat) :
    (Arith.lit n).agents.countP (fun e => decide (e.2 = Arith.add)) = 0 :=
  List.countP_eq_zero.2 fun e he h => (good_lit n).none e.1
    (by rw [← of_decide_eq_true h]; exact he)

/-- **The adders of the net of an expression are its additions.** -/
theorem Expr.net_adds : ∀ e : Expr,
    e.net.agents.countP (fun x => decide (x.2 = Arith.add)) = e.adds
  | .lit n => lit_adds n
  | .add e₁ e₂ => by
    show (besides [(0, e₁.net), (1, e₂.net), (2, open2)]).agents.countP _ = _
    simp only [besides, flatA, flatG, List.countP_append, List.countP_map, List.append_nil]
    have h1 := Expr.net_adds e₁
    have h2 := Expr.net_adds e₂
    show List.countP (fun x => decide (x.snd = Arith.add)) e₁.net.agents +
      (List.countP (fun x => decide (x.snd = Arith.add)) e₂.net.agents +
        List.countP (fun x => decide (x.snd = Arith.add)) open2.agents) = _
    rw [h1, h2]
    rfl

/-- **Every fair run of the program on an expression of additions is at
rest with its value**, with any number of threads, after `F * (B + 1)`
actions, where `F` is the window in which every thread acts and `B` is
two passes over the net of the expression, the writes of its `e.cost`
steps, and a pass for each of its additions. -/
theorem Expr.wfair (e : Expr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((7 * e.net.agents.length + (e.net.wires.length + 8 * e.cost)) +
          e.cost * (2 + 8 + 1) +
          e.adds * (7 * (e.net.agents.length + (2 - 2) * e.cost) +
            (e.net.wires.length + 8 * e.cost)) +
          (7 * (2 * e.cost) + (e.net.wires.length + 8 * e.cost)) + 1) ≤ i →
      ((WMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((WMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      ∃ N', ((WMach.init e.net nt).trace xsys σ i).1.mem.toNet = N' ∧
        Addition.IsNum xsys.sys.ar zero succ N' e.res e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  have hnd := Expr.net_nodup e
  intro i hi
  have h := WMach.fair_bound hX hnd hnt xsys_bounded hs (normal_of_no_add hno) σ (m := e.adds)
    hfair (fun j => by
      have := WMach.joined_le_census census_add hX hnd hnt σ j
      rw [Expr.net_adds] at this
      exact this) i hi
  exact ⟨h.1, h.2.1, N', h.2.2, hA⟩

end Arith
end INet
