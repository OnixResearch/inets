import InteractionNets.Arith.Carry

/-! # A larger system: addition, multiplication, powers, factorials

Eight symbols: `zero`, `succ` and `add` as in `Arith`, a multiplier
`mul`, the two agents that multiplication needs because it uses its
second argument once for every successor of the first: `dup`, which
copies a numeral, and `era`, which erases one; and `pow` and `fac`, for
powers and factorials, which use the multiplier as the multiplier uses
the adder.  The system
is given as data and validated by evaluating `SysData.check`.

It contains addition (`Peano.rules`), so the adder adds in it, with
multipliers and copiers around (`Addition.Config.steps`); and the system
of `Arith` is inside it (`Peano.embeds`), so what is proved for the nets
of `Arith` holds for them here (`Peano.expr_rest`).

One product is evaluated here.  That the multiplier multiplies, for all
inputs, is `Peano.mul_computes`, in `Peano.Rec`.
-/

namespace INet

/-- The symbols: numbers, addition, multiplication, copying, erasing,
powers and factorials. -/
inductive Peano
  | zero | succ | add | mul | dup | era | pow | fac
  deriving DecidableEq, Repr

namespace Peano

/-- The principal port of `add` and of `mul` is the first argument, the
auxiliary ports are the second argument and the result.  The principal
port of `dup` is what it copies, its auxiliary ports are the two copies;
`era` has only the port of what it erases.  The principal port of `pow`
is the exponent, its auxiliary ports are the base and the result.  The
principal port of `fac` is its argument, its auxiliary port the result. -/
def ar : Peano → Nat
  | zero => 0
  | succ => 1
  | add => 2
  | mul => 2
  | dup => 2
  | era => 0
  | pow => 2
  | fac => 1

/-- `0 * y = 0`: a new `zero` on the result, and `y` is erased. -/
def mulZero : RuleData Peano :=
  RuleData.ofWires [((some false, 0), zero), ((some true, 0), era)]
    [(.ifc false 1, .new (some false) 0 0),            -- result — the new `zero`
      (.ifc false 0, .new (some true) 0 0)]             -- `y` — the new `era`

/-- `S x * y = y + x * y`: `y` is copied; one copy is the first argument
of a new adder, the other the second argument of a new multiplier on `x`,
whose result is the second argument of the adder. -/
def mulSucc : RuleData Peano :=
  RuleData.ofWires [((some false, 0), dup), ((some false, 1), add), ((some true, 0), mul)]
    [(.ifc false 0, .new (some false) 0 0),            -- `y` — the new `dup`
      (.new (some false) 0 1, .new (some false) 1 0),   -- first copy — first argument of `add`
      (.new (some false) 0 2, .new (some true) 0 1),    -- second copy — second argument of `mul`
      (.ifc true 0, .new (some true) 0 0),              -- `x` — first argument of `mul`
      (.new (some true) 0 2, .new (some false) 1 1), -- result of `mul` — 2nd argument of `add`
      (.new (some false) 1 2, .ifc false 1)]            -- result of `add` — result

/-- A copy of `0` is two zeros. -/
def dupZero : RuleData Peano :=
  RuleData.ofWires [((some false, 0), zero), ((some true, 0), zero)]
    [(.ifc false 0, .new (some false) 0 0),
      (.ifc false 1, .new (some true) 0 0)]

/-- A copy of `S x` is two successors on the two copies of `x`. -/
def dupSucc : RuleData Peano :=
  RuleData.ofWires [((some false, 0), succ), ((some false, 1), succ), ((some true, 0), dup)]
    [(.ifc false 0, .new (some false) 0 0),
      (.ifc false 1, .new (some false) 1 0),
      (.new (some false) 0 1, .new (some true) 0 1),
      (.new (some false) 1 1, .new (some true) 0 2),
      (.new (some true) 0 0, .ifc true 0)]

/-- Erasing `0` leaves nothing. -/
def eraZero : RuleData Peano := RuleData.ofWires [] []

/-- Erasing `S x` erases `x`. -/
def eraSucc : RuleData Peano :=
  RuleData.ofWires [((some true, 0), era)] [(.ifc true 0, .new (some true) 0 0)]

/-- `y ^ 0 = 1`: a new `succ` on a new `zero` on the result, and `y` is
erased. -/
def powZero : RuleData Peano :=
  RuleData.ofWires [((some false, 0), succ), ((some false, 1), zero), ((some true, 0), era)]
    [(.ifc false 1, .new (some false) 0 0),            -- result — the new `succ`
      (.new (some false) 0 1, .new (some false) 1 0),   -- its argument — the new `zero`
      (.ifc false 0, .new (some true) 0 0)]             -- `y` — the new `era`

/-- `y ^ S x = y * y ^ x`: `y` is copied; one copy is the first argument
of a new multiplier, the other the base of a new power on `x`, whose
result is the second argument of the multiplier. -/
def powSucc : RuleData Peano :=
  RuleData.ofWires [((some false, 0), dup), ((some false, 1), mul), ((some true, 0), pow)]
    [(.ifc false 0, .new (some false) 0 0),            -- `y` — the new `dup`
      (.new (some false) 0 1, .new (some false) 1 0),   -- first copy — first argument of `mul`
      (.new (some false) 0 2, .new (some true) 0 1),    -- second copy — base of `pow`
      (.ifc true 0, .new (some true) 0 0),              -- `x` — exponent of `pow`
      (.new (some true) 0 2, .new (some false) 1 1), -- result of `pow` — 2nd argument of `mul`
      (.new (some false) 1 2, .ifc false 1)]            -- result of `mul` — result

/-- `0! = 1`: a new `succ` on a new `zero` on the result. -/
def facZero : RuleData Peano :=
  RuleData.ofWires [((some false, 0), succ), ((some false, 1), zero)]
    [(.ifc false 0, .new (some false) 0 0),            -- result — the new `succ`
      (.new (some false) 0 1, .new (some false) 1 0)]   -- its argument — the new `zero`

/-- `(S x)! = x! * S x`: `x` is copied; a new successor on one copy is
the second argument of a new multiplier, whose first argument is the
result of a new factorial on the other copy. -/
def facSucc : RuleData Peano :=
  RuleData.ofWires [((some false, 0), dup), ((some false, 1), succ), ((some false, 2), mul),
      ((some true, 0), fac)]
    [(.ifc true 0, .new (some false) 0 0),             -- `x` — the new `dup`
      (.new (some false) 0 1, .new (some false) 1 1),   -- first copy — under the new `succ`
      (.new (some false) 0 2, .new (some true) 0 0),    -- second copy — argument of `fac`
      (.new (some true) 0 1, .new (some false) 2 0),    -- result of `fac` — first argument of `mul`
      (.new (some false) 1 0, .new (some false) 2 1),   -- the new `succ` — second argument of `mul`
      (.new (some false) 2 2, .ifc false 0)]            -- result of `mul` — result

def data : SysData Peano :=
  ⟨ar, [((add, zero), Addition.zeroData), ((zero, add), Addition.zeroData.swap),
    ((add, succ), Addition.succData succ add), ((succ, add), (Addition.succData succ add).swap),
    ((mul, zero), mulZero), ((zero, mul), mulZero.swap),
    ((mul, succ), mulSucc), ((succ, mul), mulSucc.swap),
    ((dup, zero), dupZero), ((zero, dup), dupZero.swap),
    ((dup, succ), dupSucc), ((succ, dup), dupSucc.swap),
    ((era, zero), eraZero), ((zero, era), eraZero.swap),
    ((era, succ), eraSucc), ((succ, era), eraSucc.swap),
    ((pow, zero), powZero), ((zero, pow), powZero.swap),
    ((pow, succ), powSucc), ((succ, pow), powSucc.swap),
    ((fac, zero), facZero), ((zero, fac), facZero.swap),
    ((fac, succ), facSucc), ((succ, fac), facSucc.swap)]⟩

/-- The system, by evaluation of the check. -/
def xsys : XSys Peano := data.toXSys (by decide)

/-- The interaction system of `xsys`. -/
abbrev system : System Peano := xsys.sys

/-- **The system contains addition**: the adder adds in it
(`Addition.Config.steps`), whatever multipliers, copiers and erasers the
net also has. -/
theorem rules : Addition.Rules system zero succ add :=
  ⟨by decide, by decide, by decide, rfl, rfl⟩

/-- **The adder adds in this system.**  In a net whose only adder has the
numerals `m` and `n` as arguments, among any other agents, the adder runs
for `m + 1` steps, after which the result port carries the numeral
`j + m + n` and the net has no adder left. -/
theorem add_steps {N : Net Peano} {a : Id} {j m n : Nat} {r : Port}
    (c : Addition.Config ar zero succ add N a j m n r) :
    ∃ N', Steps (Step system) (m + 1) N N' ∧
      Addition.IsNum ar zero succ N' r (j + m + n) ∧ ∀ i, ¬ N'.agent i add :=
  Addition.Config.steps rules c

/-- The symbols of `Arith`, as symbols of this system. -/
def ofArith : Arith → Peano
  | .zero => zero
  | .succ => succ
  | .add => add

/-- **The system of `Arith` is inside this one.** -/
theorem embeds : Arith.system.Embeds ofArith system where
  ar := fun α => by cases α <;> rfl
  rule := fun α β => by
    cases α <;> cases β
    case add.zero =>
      show some (Addition.zeroData (S := Peano)).toX.toRhs =
        some (Arith.addZero.toX.toRhs.relabel ofArith)
      rw [RuleData.toRhs_relabel]
      rfl
    case zero.add =>
      show some (Addition.zeroData (S := Peano)).swap.toX.toRhs =
        some (Arith.addZero.swap.toX.toRhs.relabel ofArith)
      rw [RuleData.toRhs_relabel]
      rfl
    case add.succ =>
      show some (Addition.succData succ add).toX.toRhs =
        some (Arith.addSucc.toX.toRhs.relabel ofArith)
      rw [RuleData.toRhs_relabel]
      rfl
    case succ.add =>
      show some (Addition.succData succ add).swap.toX.toRhs =
        some (Arith.addSucc.swap.toX.toRhs.relabel ofArith)
      rw [RuleData.toRhs_relabel]
      rfl
    all_goals rfl

/-- **Every expression of additions comes out right in this system.**
With any number of threads and any schedule, a run of its program on the
net of an expression that ends at rest has made the interactions counted
by `Arith.Expr.cost`, and the memory has the numeral of the value on the
free port. -/
theorem expr_rest (e : Arith.Expr) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (e.net.relabel ofArith) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (e.net.relabel ofArith) nt).trace xsys σ i).2 = e.cost ∧
      Addition.IsNum ar zero succ
        ((XMach.init (e.net.relabel ofArith) nt).trace xsys σ i).1.mem.toNet e.res e.eval :=
  Arith.Expr.rest_embed xsys embeds e hnt σ hr

/-- The net for `2 * 3`, with the result on the free port `([0], 0)`. -/
def twoTimesThree : XNet Peano :=
  XNet.ofWires [([1], mul), ([2], succ), ([3], succ), ([4], zero),
      ([5], succ), ([6], succ), ([7], succ), ([8], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([2], 1), ([3], 0)), (([3], 1), ([4], 0)),   -- first argument: 2
      (([1], 1), ([5], 0)), (([5], 1), ([6], 0)), (([6], 1), ([7], 0)),   -- second argument: 3
      (([7], 1), ([8], 0)),
      (([1], 2), ([0], 0))]                                              -- result

/-- The reducer validates the net for `2 * 3` and stops after 23 steps on
a net whose agents are six successors and a zero.  This is one product,
evaluated; the proof for all products is `Peano.mul_computes`. -/
example : (twoTimesThree.normalize xsys 100).map (fun r => (r.2, r.1.agents.map (·.2))) =
    some (23, [zero, succ, succ, succ, succ, succ, succ]) := by
  decide +kernel

end Peano

end INet
