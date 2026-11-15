import InteractionNets.PeanoRun

/-! # A system of its own: the lazy caterer and the triangular numbers

A small system, apart from `Peano`, with numerals, an adder, a copier,
an eraser, and two agents of its own: the lazy caterer `cater`,
`c 0 = 1` and `c (S x) = c x + S x`, and the triangular numbers `tri`,
`t 0 = 0` and `t (S x) = t x + S x`.  It has the core (`Extra.core`) and
the rules of the adder (`Extra.rules`), so the theorems on recursion and
on the machine hold in it.  The two agents are proved with them and
nothing else: their rules on a successor are the template on the
predecessor with the adder, and their rules on a zero put down a
constant (`Extra.cater_computes`, `Extra.tri_computes`, and on the
machine `Extra.cater_rest`, `Extra.tri_rest`).
-/

namespace INet

/-- The symbols: numbers, addition, copying, erasing, the lazy caterer and
the triangular numbers. -/
inductive Extra
  | zero | succ | add | dup | era | cater | tri
  deriving DecidableEq, Repr

namespace Extra

/-- The arities. -/
def ar : Extra → Nat
  | zero => 0
  | succ => 1
  | add => 2
  | dup => 2
  | era => 0
  | cater => 1
  | tri => 1

/-- `1` on the result: a new successor on a new zero. -/
def oneData : RuleData Extra :=
  RuleData.ofWires [((some false, 0), succ), ((some false, 1), zero)]
    [(.ifc false 0, .new (some false) 0 0), (.new (some false) 0 1, .new (some false) 1 0)]

/-- `0` on the result: a new zero. -/
def zeroData : RuleData Extra :=
  RuleData.ofWires [((some false, 0), zero)] [(.ifc false 0, .new (some false) 0 0)]

def data : SysData Extra :=
  ⟨ar, [((add, zero), Addition.zeroData), ((zero, add), Addition.zeroData.swap),
    ((add, succ), Addition.succData succ add), ((succ, add), (Addition.succData succ add).swap),
    ((dup, zero), Copies.dupZeroData zero), ((zero, dup), (Copies.dupZeroData zero).swap),
    ((dup, succ), Copies.dupSuccData succ dup), ((succ, dup), (Copies.dupSuccData succ dup).swap),
    ((era, zero), Copies.eraZeroData), ((zero, era), Copies.eraZeroData.swap),
    ((era, succ), Copies.eraSuccData era), ((succ, era), (Copies.eraSuccData era).swap),
    ((cater, zero), oneData), ((zero, cater), oneData.swap),
    ((cater, succ), Core.primSucc succ dup cater add),
    ((succ, cater), (Core.primSucc succ dup cater add).swap),
    ((tri, zero), zeroData), ((zero, tri), zeroData.swap),
    ((tri, succ), Core.primSucc succ dup tri add),
    ((succ, tri), (Core.primSucc succ dup tri add).swap)]⟩

/-- The system, by evaluation of the check. -/
def xsys : XSys Extra := data.toXSys (by decide)

/-- The interaction system of `xsys`. -/
abbrev system : System Extra := xsys.sys

/-- **The system has the core.** -/
instance core : Core system zero succ dup era where
  zero_ne_dup := by decide
  succ_ne_dup := by decide
  zero_ne_era := by decide
  succ_ne_era := by decide
  rule_dup_zero := rfl
  rule_dup_succ := rfl
  rule_era_zero := rfl
  rule_era_succ := rfl
  numerals := by rintro α β (rfl | rfl) (rfl | rfl) <;> rfl
  ar_zero := rfl
  ar_succ := rfl

/-- **The system has the adder.** -/
theorem rules : Addition.Rules system zero succ add :=
  ⟨by decide, by decide, by decide, rfl, rfl⟩

/-! ### The lazy caterer -/

/-- The lazy caterer's numbers. -/
def cate : Nat → Nat
  | 0 => 1
  | n + 1 => cate n + (n + 1)

/-- In closed form: `2 c n = n (n + 1) + 2`. -/
theorem two_mul_cate : ∀ n, 2 * cate n = n * (n + 1) + 2
  | 0 => rfl
  | n + 1 => by
    have ih := two_mul_cate n
    have e₁ : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (n + 1) := Nat.mul_succ _ _
    have e₂ : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := Nat.succ_mul _ _
    have e : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by omega
    show 2 * (cate n + (n + 1)) = (n + 1) * (n + 1 + 1) + 2
    rw [Nat.mul_add, ih, e]
    omega

/-- Its number of interactions: on a zero, one; on a successor, one, the
copy of the rest, the rest, and the addition. -/
def caterCost : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1 + 1 + caterCost n + (cate n + 1)

theorem prim_cate (n : Nat) : Core.prim 1 (fun m n => m + n) n = cate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Core.prim _ _ n + (n + 1) = cate n + (n + 1)
    rw [ih]

theorem primCost_cate (n : Nat) :
    Core.primCost 1 (fun m _ => m + 1) 1 (fun m n => m + n) n = caterCost n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show n + 1 + 1 + Core.primCost _ _ _ _ n + (Core.prim _ _ n + 1) = caterCost (n + 1)
    rw [ih, prim_cate]
    rfl

/-- **The lazy caterer computes its numbers**, in any net: the theorem on
recursion on the predecessor, with the theorem on constants for the zero
and the adder as combiner. -/
theorem cater_computes : Core.Computes1 system cater cate caterCost :=
  (Core.prim_computes
    (show system.rule cater succ = some (Core.primSucc succ dup cater add).toX.toRhs from rfl)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Core.zero1_const (show system.rule cater zero = some oneData.toX.toRhs from rfl)
      (by decide) ⟨by decide, by decide, by decide, by decide⟩ (by decide))
    (Core.add_combines rules)).congr prim_cate primCost_cate

/-- **The lazy caterer on the machine**: with any number of threads and
any schedule, a run on the net for `c n` that is at rest has made exactly
`caterCost n` interactions and holds the numeral `c n`. -/
theorem cater_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (Core.unaryNet zero succ cater n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (Core.unaryNet zero succ cater n) nt).trace xsys σ i).2 = caterCost n ∧
      Addition.IsNum ar zero succ
        ((XMach.init (Core.unaryNet zero succ cater n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (cate n) :=
  Core.unary_rest (xsys := xsys) cater_computes rfl (by decide) n hnt σ hr

/-- The reducer on the net for `c 3` stops after `caterCost 3 = 20` steps
on seven successors and a zero. -/
example : ((Core.unaryNet zero succ cater 3).normalize xsys 100).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) =
    some (caterCost 3, 7, 1, 8) := by
  decide +kernel

/-! ### The triangular numbers -/

/-- The triangular numbers. -/
def triN : Nat → Nat
  | 0 => 0
  | n + 1 => triN n + (n + 1)

/-- In closed form: `2 t n = n (n + 1)`. -/
theorem two_mul_triN : ∀ n, 2 * triN n = n * (n + 1)
  | 0 => rfl
  | n + 1 => by
    have ih := two_mul_triN n
    have e₁ : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (n + 1) := Nat.mul_succ _ _
    have e₂ : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := Nat.succ_mul _ _
    show 2 * (triN n + (n + 1)) = (n + 1) * (n + 1 + 1)
    rw [Nat.mul_add, ih]
    omega

/-- Its number of interactions: on a zero, one; on a successor, one, the
copy of the rest, the rest, and the addition. -/
def triCost : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1 + 1 + triCost n + (triN n + 1)

theorem prim_tri (n : Nat) : Core.prim 0 (fun m n => m + n) n = triN n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Core.prim _ _ n + (n + 1) = triN n + (n + 1)
    rw [ih]

theorem primCost_tri (n : Nat) :
    Core.primCost 1 (fun m _ => m + 1) 0 (fun m n => m + n) n = triCost n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show n + 1 + 1 + Core.primCost _ _ _ _ n + (Core.prim _ _ n + 1) = triCost (n + 1)
    rw [ih, prim_tri]
    rfl

/-- **The triangular numbers are computed**, in any net. -/
theorem tri_computes : Core.Computes1 system tri triN triCost :=
  (Core.prim_computes
    (show system.rule tri succ = some (Core.primSucc succ dup tri add).toX.toRhs from rfl)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Core.zero1_const (show system.rule tri zero = some zeroData.toX.toRhs from rfl)
      (by decide) ⟨by decide, by decide, by decide, by decide⟩ (by decide))
    (Core.add_combines rules)).congr prim_tri primCost_tri

/-- **The triangular numbers on the machine.** -/
theorem tri_rest (n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (Core.unaryNet zero succ tri n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (Core.unaryNet zero succ tri n) nt).trace xsys σ i).2 = triCost n ∧
      Addition.IsNum ar zero succ
        ((XMach.init (Core.unaryNet zero succ tri n) nt).trace xsys σ i).1.mem.toNet ([0], 0)
        (triN n) :=
  Core.unary_rest (xsys := xsys) tri_computes rfl (by decide) n hnt σ hr

/-- The reducer on the net for `t 4` stops after `triCost 4` steps on ten
successors and a zero. -/
example : ((Core.unaryNet zero succ tri 4).normalize xsys 200).map
    (fun r => (r.2, (r.1.agents.filter (·.2 = succ)).length,
      (r.1.agents.filter (·.2 = zero)).length, r.1.agents.length)) =
    some (triCost 4, 10, 1, 11) := by
  decide +kernel

end Extra

end INet
