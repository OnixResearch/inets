import InteractionNets.Confluence

/-! # Steps with weights: every reduction to the normal form weighs the same

Give each step a weight.  If two different steps from a net can be
completed to a common net, each by a step of the other's weight, and the
same step always has the same weight, then every reduction to the normal
form has the same total weight, and no reduction weighs more.  For nets,
weigh a firing `1` when its rule wires two interface ports together: then
how many such firings a computation makes is fixed by the start, whatever
the order, as the number of steps is.
-/

namespace INet

universe u

section WRewriting

variable {A : Type u} {P : A → Prop} {r : Nat → A → A → Prop}

/-- `WSteps r n w a b`: `a` rewrites to `b` in `n` steps of total weight `w`. -/
inductive WSteps (r : Nat → A → A → Prop) : Nat → Nat → A → A → Prop
  | refl (a : A) : WSteps r 0 0 a a
  | head {n w v : Nat} {a b c : A} : r v a b → WSteps r n w b c → WSteps r (n + 1) (v + w) a c

/-- The diamond property with weights: two different steps can be
completed to a common term, each by a step of the other's weight; two equal
steps have equal weights. -/
structure WDiamond (P : A → Prop) (r : Nat → A → A → Prop) : Prop where
  inv : ∀ {w a b}, P a → r w a b → P b
  diamond : ∀ {v w a b c}, P a → r v a b → r w a c →
    (b = c ∧ v = w) ∨ ∃ d, r w b d ∧ r v c d

namespace WDiamond

theorem inv_steps (h : WDiamond P r) {n w : Nat} {a b : A} (ha : P a) (s : WSteps r n w a b) :
    P b := by
  induction s with
  | refl => exact ha
  | head st _ ih => exact ih (h.inv ha st)

/-- A first step can be taken out of a reduction to a term with no step. -/
theorem absorb (h : WDiamond P r) {n W v : Nat} {a b f : A} (ha : P a)
    (s : WSteps r n W a f) (hf : ∀ w g, ¬ r w f g) (st : r v a b) :
    v ≤ W ∧ WSteps r (n - 1) (W - v) b f := by
  induction s generalizing b v with
  | refl => exact absurd st (hf v b)
  | @head n w v' a c f st' rest ih =>
    rcases h.diamond ha st st' with ⟨rfl, rfl⟩ | ⟨d, h₁, h₂⟩
    · refine ⟨Nat.le_add_right _ _, ?_⟩
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
      exact rest
    · obtain ⟨hle, rest'⟩ := ih (h.inv ha st') hf h₂
      have hn : 0 < n := by
        cases rest with
        | refl => exact absurd h₂ (hf _ _)
        | head _ _ => omega
      refine ⟨by omega, ?_⟩
      have e1 : n + 1 - 1 = (n - 1) + 1 := by omega
      have e2 : v' + w - v = v' + (w - v) := by omega
      rw [e1, e2]
      exact .head h₁ rest'

/-- **No reduction weighs more than one to a term with no step.** -/
theorem bounded (h : WDiamond P r) {n m W V : Nat} {a f b : A} (ha : P a)
    (s : WSteps r n W a f) (hf : ∀ w g, ¬ r w f g) (t : WSteps r m V a b) : V ≤ W := by
  induction t generalizing n W with
  | refl => exact Nat.zero_le _
  | head st rest ih =>
    obtain ⟨hle, s'⟩ := h.absorb ha s hf st
    have := ih (h.inv ha st) s'
    omega

end WDiamond

end WRewriting

section WNets

variable {S : Type} {sys : System S}

/-- The rule wires two of its interface ports together. -/
def Rhs.Joins (R : Rhs S) : Prop := ∃ x y, R.link x y ∧ ¬ x.IsNew ∧ ¬ y.IsNew

open Classical in
/-- `1` for a rule that joins interface ports, `0` for one that does not. -/
noncomputable def Rhs.weight (R : Rhs S) : Nat := if R.Joins then 1 else 0

theorem LPort.isNew_swap {x : LPort} : x.swap.IsNew ↔ x.IsNew := by
  cases x <;> exact Iff.rfl

/-- A rule and its mirror image weigh the same. -/
theorem Rhs.Mirror.weight_eq {R R' : Rhs S} (h : R.Mirror R') : R.weight = R'.weight := by
  have e : R.Joins ↔ R'.Joins := by
    constructor
    · rintro ⟨x, y, hl, hx, hy⟩
      refine ⟨x.swap, y.swap, (h.2 _ _).2 (by rw [LPort.swap_swap, LPort.swap_swap]; exact hl),
        fun h' => hx (LPort.isNew_swap.1 h'), fun h' => hy (LPort.isNew_swap.1 h')⟩
    · rintro ⟨x, y, hl, hx, hy⟩
      exact ⟨x.swap, y.swap, (h.2 _ _).1 hl, fun h' => hx (LPort.isNew_swap.1 h'),
        fun h' => hy (LPort.isNew_swap.1 h')⟩
  unfold Rhs.weight
  by_cases hj : R.Joins
  · simp [hj, e.1 hj]
  · simp [hj, show ¬ R'.Joins from fun h' => hj (e.2 h')]

/-- A step of reduction, with the weight of its rule. -/
def WStep (sys : System S) (w : Nat) (N N' : Net S) : Prop :=
  ∃ a b α β R, Redex sys N a b α β R ∧ N' = N.fire a b R ∧ w = R.weight

theorem WStep.step {w : Nat} {N N' : Net S} (h : WStep sys w N N') : Step sys N N' := by
  obtain ⟨a, b, α, β, R, r, e, -⟩ := h
  exact ⟨a, b, α, β, R, r, e⟩

/-- **Weighted strong confluence.** -/
theorem wdiamond (sys : System S) : WDiamond (fun N : Net S => N.WF sys.ar) (WStep sys) := by
  refine ⟨fun hN h => Step.wf hN h.step, ?_⟩
  intro v w N N₁ N₂ hN h₁ h₂
  obtain ⟨a, b, α, β, R, r, rfl, rfl⟩ := h₁
  obtain ⟨c, d, γ, δ, R', r', rfl, rfl⟩ := h₂
  by_cases hac : a = c
  · subst hac
    obtain rfl := r.partner_unique r' hN
    obtain rfl := hN.agent_fun r.ha r'.ha
    obtain rfl := hN.agent_fun r.hb r'.hb
    obtain rfl := Option.some.inj (r.rule.symm.trans r'.rule)
    exact .inl ⟨rfl, rfl⟩
  by_cases had : a = d
  · subst had
    obtain ⟨R'', hR'', hm⟩ := sys.rule_symm r'.rule
    have r'' : Redex sys N a c δ γ R'' := ⟨r'.hb, r'.ha, r'.ne.symm, r'.conn.symm hN, hR''⟩
    obtain rfl := r.partner_unique r'' hN
    obtain rfl := hN.agent_fun r.ha r''.ha
    obtain rfl := hN.agent_fun r.hb r''.hb
    obtain rfl := Option.some.inj (r.rule.symm.trans r''.rule)
    exact .inl ⟨(fire_mirror N _ _ hm).symm, hm.weight_eq.symm⟩
  by_cases hbc : b = c
  · subst hbc
    obtain ⟨R'', r'', -⟩ := r.flip hN
    exact absurd (r''.partner_unique r' hN) had
  by_cases hbd : b = d
  · subst hbd
    obtain ⟨R₁, r₁, -⟩ := r.flip hN
    obtain ⟨R₂, r₂, -⟩ := r'.flip hN
    exact absurd (r₁.partner_unique r₂ hN) hac
  · refine .inr ⟨(N.fire a b R).fire c d R', ⟨c, d, γ, δ, R', ?_, rfl, rfl⟩,
      ⟨a, b, α, β, R, ?_, ?_, rfl⟩⟩
    · exact r.fire r' hN (Ne.symm hac) (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd)
    · exact r'.fire r hN hac had hbc hbd
    · have s := r.site hN
      have s' := r'.site hN
      exact fire_comm N R R'
        (fun t j => ⟨fun e => s.not_used_child t j (e ▸ .inl ⟨_, r'.ha⟩),
          fun e => s.not_used_child t j (e ▸ .inl ⟨_, r'.hb⟩)⟩)
        (fun t j => ⟨fun e => s'.not_used_child t j (e ▸ .inl ⟨_, r.ha⟩),
          fun e => s'.not_used_child t j (e ▸ .inl ⟨_, r.hb⟩)⟩)

/-- **The firings of rules that join interface ports are fixed by the
start**: no reduction makes more of them than a reduction to the normal
form. -/
theorem wsteps_bounded {N Nf N' : Net S} {n m W V : Nat} (hN : N.WF sys.ar)
    (s : WSteps (WStep sys) n W N Nf) (hf : Normal (Step sys) Nf)
    (t : WSteps (WStep sys) m V N N') : V ≤ W :=
  (wdiamond sys).bounded hN s (fun _ g h => hf g h.step) t

end WNets

end INet
