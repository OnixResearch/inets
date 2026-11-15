import InteractionNets.Arith.Run
import InteractionNets.Core.Bound

/-! # How many actions an expression of additions takes

The expressions of `Arith` run with threads that take turns return their
value after a bounded number of actions (`Arith.Expr.run_by`): the rules
of `Arith` write at most two agents and eight ports (`Arith.xsys_bounded`),
and the net of an expression lists no name twice (`Arith.Expr.net_nodup`),
so `XNet.runRead_bound` applies.
-/

namespace INet

namespace Arith

theorem lit_nodup : ∀ n, ((Arith.lit n).agents.map Prod.fst).Nodup
  | 0 => by decide
  | n + 1 => XNet.pushOn_nodup (good_lit n).below succ _ (lit_nodup n)

/-- Three memories side by side, as `besides` puts them, have the names of
`XNet.three`. -/
theorem besides_three_ids (X₀ X₁ X₂ : XNet Arith) :
    (besides [(0, X₀), (1, X₁), (2, X₂)]).agents.map Prod.fst =
      (XNet.three X₀ X₁ X₂).agents.map Prod.fst := by
  simp [besides, flatA, flatG, XNet.three, XNet.union, XNet.tag]
  rfl

theorem open2_nodup : (open2.agents.map Prod.fst).Nodup := by decide

/-- **The net of an expression lists no name twice.** -/
theorem Expr.net_nodup : ∀ e : Expr, (e.net.agents.map Prod.fst).Nodup
  | .lit n => lit_nodup n
  | .add e₁ e₂ => by
    show (((besides [(0, e₁.net), (1, e₂.net), (2, open2)]).agents).map Prod.fst).Nodup
    rw [besides_three_ids]
    exact XNet.three_nodup (Expr.net_nodup e₁) (Expr.net_nodup e₂) open2_nodup

/-- **How many actions are enough to run an expression of additions and
read its value.**  Run for at least

    nt * ((nt + e.cost) * e.net.passBound e.cost 2 8 + e.cost * (2 + 8 + 1) + 1)

actions, at least the segments of the net and of `e.cost` right-hand
sides, and at least the length of the value, `nt` threads taking turns
return the value. -/
theorem Expr.run_by (e : Expr) {nt : Nat} (hnt : 0 < nt) (s : Nat)
    (h₁ : nt * ((nt + e.cost) * e.net.passBound e.cost 2 8 + e.cost * (2 + 8 + 1) + 1) ≤ s)
    (h₂ : e.net.wires.length + 8 * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.run nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hno⟩ := Expr.good e
  exact XNet.runRead_bound (zero := zero) (succ := succ) (by decide) hX (Expr.net_nodup e) hnt
    xsys_bounded hs (normal_of_no_add hno) hA s h₁ h₂ h₃

end Arith

end INet
