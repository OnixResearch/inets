import InteractionNets.Peano.Basic
import InteractionNets.Core.Rec

/-! # The multiplier, the power and the factorial compute

The theorems on recursion applied to the rules of `Peano`
(`Peano.mul_computes`, `Peano.pow_computes`, `Peano.fac_computes`).
-/

namespace INet

namespace Peano

open Core
open Addition (gone gone2)

/-- The multiplier recurses on its parameter, with the adder. -/
theorem mulSucc_eq : mulSucc = iterSucc dup mul add := rfl

/-- The power recurses on its parameter, with the multiplier. -/
theorem powSucc_eq : powSucc = iterSucc dup pow mul := rfl

/-- The factorial recurses on the predecessor, with the multiplier. -/
theorem facSucc_eq : facSucc = primSucc succ dup fac mul := rfl

/-! ### The three rules, again -/

/-- The rule of the factorial on a zero, as a case. -/
theorem zero1_facZero {op : Peano} (hr : system.rule op zero = some facZero.toX.toRhs)
    (h0 : zero ≠ op) : Zero1 system op 1 1 :=
  zero1_const hr h0 ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- The rule of the multiplier on a zero, as a case. -/
theorem zero2_mulZero {op : Peano} (hr : system.rule op zero = some mulZero.toX.toRhs)
    (h0 : zero ≠ op) (h1 : succ ≠ op) : Zero2 system op (fun _ => 0) (fun n => n + 1 + 1) :=
  zero2_const hr h0 h1 ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide)

/-- The rule of the power on a zero, as a case. -/
theorem zero2_powZero {op : Peano} (hr : system.rule op zero = some powZero.toX.toRhs)
    (h0 : zero ≠ op) (h1 : succ ≠ op) : Zero2 system op (fun _ => 1) (fun n => n + 1 + 1) :=
  zero2_const hr h0 h1 ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide)

/-! ### The three agents, again -/

/-- **The multiplier computes the product**, from the theorem on
recursion: it recurses on its parameter with the adder. -/
theorem mul_computes : Computes2 mul (fun m n => m * n) prodCost :=
  (iter_computes rule_mul_succ ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ (zero2_mulZero rule_mul_zero (by decide) (by decide))
    (add_combines rules)).congr iter_mul iterCost_mul

theorem iter_pow (e b : Nat) : iter (fun _ => 1) (fun n v => n * v) e b = b ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    show b * iter _ _ e b = b ^ (e + 1)
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem iterCost_pow (e b : Nat) :
    iterCost (fun n => n + 1 + 1) prodCost (fun _ => 1) (fun n v => n * v) e b =
      powCost e b := by
  induction e with
  | zero => rfl
  | succ e ih =>
    show b + 1 + 1 + iterCost _ _ _ _ e b + prodCost b (iter _ _ e b) = powCost (e + 1) b
    rw [ih, iter_pow]
    rfl

/-- **The power computes the power**, from the theorem on recursion: it
recurses on its parameter, the base, with the multiplier. -/
theorem pow_computes : Computes2 pow (fun e b => b ^ e) powCost :=
  (iter_computes rule_pow_succ ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ (zero2_powZero rule_pow_zero (by decide) (by decide))
    mul_computes.combines).congr iter_pow iterCost_pow

theorem prim_fac (n : Nat) : prim 1 (fun v n => v * n) n = fact n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show prim _ _ n * (n + 1) = fact n * (n + 1)
    rw [ih]

theorem primCost_fac (n : Nat) : primCost 1 prodCost 1 (fun v n => v * n) n = facCost n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show n + 1 + 1 + primCost _ _ _ _ n + prodCost (prim _ _ n) (n + 1) = facCost (n + 1)
    rw [ih, prim_fac]
    rfl

/-- **The factorial computes the factorial**, from the theorem on
recursion: it recurses on the predecessor with the multiplier. -/
theorem fac_computes : Computes1 fac fact facCost :=
  (prim_computes rule_fac_succ ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ (zero1_facZero rule_fac_zero (by decide))
    mul_computes.combines).congr prim_fac primCost_fac

end Peano

end INet
