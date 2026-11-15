import InteractionNets.Core.GExpr
import InteractionNets.RoundRobin

/-! # How many actions an expression takes, in any system with the core

Threads that take turns on the net of an expression are at rest, with the
value on the free port, after a number of actions given by the size of
the net, the number of threads, the cost of the expression and a bound
on the rules (`Core.GExpr.rest_by`, and for any schedule with a window
`Core.GExpr.rest_within`), and running and reading returns the value
(`Core.GExpr.run_by`).  This is `XMach.roundRobin_rest`, with no name
listed twice in the net of an expression (`Core.GExpr.net_nodup`).
-/

namespace INet

open Arith (tagPort append_singleton)

/-- The names of a memory with a tag at the end of every name. -/
theorem XNet.tag_ids {S : Type} (c : Nat) (X : XNet S) :
    (X.tag c).agents.map Prod.fst = (X.agents.map Prod.fst).map (· ++ [c]) := by
  show (X.agents.map fun e => (e.1 ++ [c], e.2)).map Prod.fst = _
  rw [List.map_map, List.map_map]
  rfl

theorem XNet.tag_nodup {S : Type} (c : Nat) {X : XNet S} (h : (X.agents.map Prod.fst).Nodup) :
    ((X.tag c).agents.map Prod.fst).Nodup := by
  rw [XNet.tag_ids]
  exact List.Pairwise.map _ (fun _ _ hab e => hab (List.append_cancel_right e)) h

theorem XNet.mem_tag_ids {S : Type} {c : Nat} {X : XNet S} {i : Id}
    (h : i ∈ (X.tag c).agents.map Prod.fst) : ∃ j, i = j ++ [c] := by
  rw [XNet.tag_ids] at h
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
  exact ⟨j, rfl⟩

theorem XNet.union_nodup {S : Type} {X Y : XNet S} (hX : (X.agents.map Prod.fst).Nodup)
    (hY : (Y.agents.map Prod.fst).Nodup)
    (hd : ∀ i, i ∈ X.agents.map Prod.fst → i ∉ Y.agents.map Prod.fst) :
    ((X.union Y).agents.map Prod.fst).Nodup := by
  show ((X.agents ++ Y.agents).map Prod.fst).Nodup
  rw [List.map_append]
  exact List.nodup_append.2 ⟨hX, hY, fun a ha b hb e => hd a ha (e ▸ hb)⟩

theorem tag_last_ne {i j : Id} {c c' : Nat} (hc : c ≠ c') : i ++ [c] ≠ j ++ [c'] := by
  intro e
  have := congrArg List.getLast? e
  rw [List.getLast?_append, List.getLast?_append] at this
  simp at this
  exact hc this

/-- **Three memories side by side list no name twice**, if each of them
does. -/
theorem XNet.three_nodup {S : Type} {X₀ X₁ X₂ : XNet S}
    (h₀ : (X₀.agents.map Prod.fst).Nodup) (h₁ : (X₁.agents.map Prod.fst).Nodup)
    (h₂ : (X₂.agents.map Prod.fst).Nodup) :
    ((XNet.three X₀ X₁ X₂).agents.map Prod.fst).Nodup := by
  refine XNet.union_nodup (XNet.tag_nodup 0 h₀)
    (XNet.union_nodup (XNet.tag_nodup 1 h₁) (XNet.tag_nodup 2 h₂) ?_) ?_
  · intro i hi hj
    obtain ⟨a, rfl⟩ := XNet.mem_tag_ids hi
    obtain ⟨b, e⟩ := XNet.mem_tag_ids hj
    exact tag_last_ne (by decide) e
  · intro i hi hj
    obtain ⟨a, rfl⟩ := XNet.mem_tag_ids hi
    have hj' : a ++ [0] ∈ (X₁.tag 1).agents.map Prod.fst ++ (X₂.tag 2).agents.map Prod.fst := by
      have : ((X₁.tag 1).union (X₂.tag 2)).agents.map Prod.fst =
          (X₁.tag 1).agents.map Prod.fst ++ (X₂.tag 2).agents.map Prod.fst := List.map_append
      rw [← this]
      exact hj
    rcases List.mem_append.1 hj' with h | h
    · obtain ⟨b, e⟩ := XNet.mem_tag_ids h
      exact tag_last_ne (by decide) e
    · obtain ⟨b, e⟩ := XNet.mem_tag_ids h
      exact tag_last_ne (by decide) e

/-- One more agent on a wire, with a fresh name, lists no name twice. -/
theorem XNet.pushOn_nodup {S : Type} {X : XNet S} {b : Nat} (hb : X.Below b) (γ : S) (p : Port)
    (h : (X.agents.map Prod.fst).Nodup) : ((X.pushOn γ p [b]).agents.map Prod.fst).Nodup := by
  unfold XNet.pushOn
  split
  · show (([b], γ) :: X.agents).map Prod.fst |>.Nodup
    rw [List.map_cons]
    refine List.nodup_cons.2 ⟨fun hm => ?_, h⟩
    obtain ⟨⟨i, α⟩, he, e⟩ := List.mem_map.1 hm
    simp only at e
    subst e
    obtain ⟨j, hj, e⟩ := hb _ (.inl ⟨α, he⟩)
    have := List.head_eq_of_cons_eq e
    omega
  · exact h

namespace Core

variable {S : Type} [DecidableEq S] {xsys : XSys S} {zero succ dup era : S}
  [K : Core xsys.sys zero succ dup era]

include K


local notation "IsNum" => Addition.IsNum xsys.sys.ar zero succ

omit [DecidableEq S] in
theorem lit_nodup : ∀ n, ((lit zero succ n).agents.map Prod.fst).Nodup
  | 0 => List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | n + 1 => XNet.pushOn_nodup (good_lit (xsys := xsys) n).below succ _ (lit_nodup n)

omit [DecidableEq S] in
omit K in
theorem openOp_nodup (γ : S) : ((openOp γ).agents.map Prod.fst).Nodup :=
  List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩

omit [DecidableEq S] in
omit K in
theorem openOp1_nodup (γ : S) : ((openOp1 γ).agents.map Prod.fst).Nodup :=
  List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩

omit [DecidableEq S] in
/-- **The net of an expression lists no name twice.** -/
theorem GExpr.net_nodup : ∀ e : GExpr xsys, (e.net.agents.map Prod.fst).Nodup
  | .lit n => lit_nodup (xsys := xsys) n
  | .app1 o e =>
    XNet.three_nodup (GExpr.net_nodup e) List.nodup_nil (openOp1_nodup o.sym)
  | .app2 o e₁ e₂ =>
    XNet.three_nodup (GExpr.net_nodup e₁) (GExpr.net_nodup e₂) (openOp_nodup o.sym)

/-- **How many actions an expression takes.**  `nt` threads that take
turns on the net of an expression are at rest after

    nt * ((nt + e.cost) * e.net.passBound e.cost C D + e.cost * 17 + 1)

actions; from then on they have made `e.cost` interactions and the memory
holds the value on the free port. -/
theorem GExpr.rest_by {C D : Nat} (hb : xsys.Bounded C D) (e : GExpr xsys) {nt : Nat} (hnt : 0 < nt)
    :
    ∀ i, nt * ((nt + e.cost) * e.net.passBound e.cost C D + e.cost * (C + D + 1) + 1) ≤ i →
      ((XMach.init e.net nt).trace xsys (fun j => j % nt) i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys (fun j => j % nt) i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys (fun j => j % nt) i).1.mem.toNet e.res
        e.eval := by
  intro i hi
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  have hr := XMach.roundRobin_rest hX (GExpr.net_nodup e) hnt hb hs
    ((normal_of_numerals hag : Normal (Step xsys.sys) _)) i hi
  exact ⟨hr, e.rest hnt _ hr⟩

/-- **The same for any schedule in which every thread acts in every
window of `W` actions**: after `W` times the count, the threads are at
rest with the value in memory. -/
theorem GExpr.rest_within {C D : Nat} (hb : xsys.Bounded C D) (e : GExpr xsys) {nt : Nat} (hnt : 0 <
    nt) (σ : Nat → Nat) {W : Nat}
    (hwin : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + W ∧ σ j = u) :
    ∀ i, W * ((nt + e.cost) * e.net.passBound e.cost C D + e.cost * (C + D + 1) + 1) ≤ i →
      ((XMach.init e.net nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init e.net nt).trace xsys σ i).2 = e.cost ∧
      IsNum ((XMach.init e.net nt).trace xsys σ i).1.mem.toNet e.res e.eval := by
  intro i hi
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  have hr := XMach.window_rest hX (GExpr.net_nodup e) hnt hb hs
    ((normal_of_numerals hag : Normal (Step xsys.sys) _)) σ hwin i hi
  exact ⟨hr, e.rest hnt _ hr⟩

/-- **How many actions are enough to run an expression and read its
value.**  Run for at least the bound of `Peano.GExpr.rest_by`, the
segments of the net and of `e.cost` right-hand sides, and the length of
the value, `nt` threads taking turns return the value. -/
theorem GExpr.run_by {C D : Nat} (hb : xsys.Bounded C D) (e : GExpr xsys) {nt : Nat} (hnt : 0 < nt)
    (s : Nat)
    (h₁ : nt * ((nt + e.cost) * e.net.passBound e.cost C D + e.cost * (C + D + 1) + 1) ≤ s)
    (h₂ : e.net.wires.length + D * e.cost ≤ s) (h₃ : e.eval + 1 ≤ s) :
    e.run nt s = some e.eval := by
  obtain ⟨hX, -, N', hs, hA, hag⟩ := GExpr.good e
  exact XNet.runRead_bound (zero := zero) (succ := succ) K.zero_ne_succ hX (GExpr.net_nodup e) hnt
    hb hs ((normal_of_numerals hag : Normal (Step xsys.sys) _)) hA s h₁ h₂ h₃

end Core

end INet
