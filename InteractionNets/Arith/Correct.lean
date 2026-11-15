import InteractionNets.Addition

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## Example: unary addition, defined by data alone

Lafont's first example.  `zero` and `succ` build numbers; the principal port
of `add` is its first argument, its auxiliary ports are its second argument
and its result.  The system is validated by evaluating `SysData.check`, and
the first examples by evaluating `XNet.normalize`.  The last two parts prove
that the reducer adds, for all inputs. -/

inductive Arith
  | zero | succ | add
  deriving DecidableEq, Repr

namespace Arith

def ar : Arith → Nat
  | zero => 0
  | succ => 1
  | add => 2

/-- `0 + y = y`: the second argument is wired to the result. -/
def addZero : RuleData Arith :=
  RuleData.ofWires [] [(.ifc false 0, .ifc false 1)]

/-- `S x + y = S (x + y)`: a new `succ` on the result, a new `add` on `x`. -/
def addSucc : RuleData Arith :=
  RuleData.ofWires [((some false, 0), succ), ((some true, 0), add)]
    [(.ifc false 1, .new (some false) 0 0),            -- result — principal of the new `succ`
      (.new (some false) 0 1, .new (some true) 0 2),    -- its argument — result of the new `add`
      (.new (some true) 0 0, .ifc true 0),              -- first argument of the new `add` — `x`
      (.new (some true) 0 1, .ifc false 0)]             -- its second argument — `y`

def data : SysData Arith :=
  ⟨ar, [((add, zero), addZero), ((zero, add), addZero.swap),
    ((add, succ), addSucc), ((succ, add), addSucc.swap)]⟩

/-- The system, by evaluation of the check. -/
def xsys : XSys Arith := data.toXSys (by decide)

/-- The check rejects a table that lacks the mirror image of a rule ... -/
example : (⟨ar, [((add, zero), addZero)]⟩ : SysData Arith).check = false := by
  decide

/-- ... and a right-hand side that leaves a port unwired. -/
example :
    (⟨ar, [((add, zero), ⟨[], []⟩), ((zero, add), ⟨[], []⟩)]⟩ : SysData Arith).check = false := by
  decide

/-- The net for `1 + 1`, with the result on the free port `([5], 0)`. -/
def onePlusOne : XNet Arith :=
  XNet.ofWires [([0], add), ([1], succ), ([2], zero), ([3], succ), ([4], zero)] [([5], 0)]
    [(([0], 0), ([1], 0)),    -- first argument: `S`
      (([1], 1), ([2], 0)),   --   of `0`
      (([0], 1), ([3], 0)),   -- second argument: `S`
      (([3], 1), ([4], 0)),   --   of `0`
      (([0], 2), ([5], 0))]   -- result

/-- `S (S 0)` on the same free port. -/
def two : XNet Arith :=
  ⟨[([3], succ), ([4], zero), ([0, 0], succ)], [([5], 0)],
    [(([3], 1), ([4], 0)), (([0, 0], 0), ([5], 0)), (([3], 0), ([0, 0], 1)),
      (([4], 0), ([3], 1)), (([5], 0), ([0, 0], 0)), (([0, 0], 1), ([3], 0))]⟩

/-- `normalize` validates the net for `1 + 1` and reduces it to `2` in two
steps. -/
theorem onePlusOne_normalize : onePlusOne.normalize xsys 10 = some (two, 2) := by
  decide

/-- Hence `2` is the normal form of `1 + 1`, every reduction of `1 + 1` has
at most two steps, and every reduction to a normal form ends at `2`. -/
theorem onePlusOne_normal_form :
    Steps (CStep xsys.sys) 2 onePlusOne.toNet two.toNet ∧ Normal (CStep xsys.sys) two.toNet ∧
      ∀ {m : Nat} {C : Net Arith}, Steps (CStep xsys.sys) m onePlusOne.toNet C →
        m ≤ 2 ∧ (Normal (CStep xsys.sys) C → C = two.toNet ∧ m = 2) := by
  obtain ⟨-, -, h₁, h₂, h₃⟩ := XNet.normalize_spec onePlusOne_normalize
  exact ⟨h₁, h₂, h₃⟩

/-- Put a successor on the wire that leaves the port `p`. -/
def push (X : XNet Arith) (p : Port) (u : Id) : XNet Arith :=
  match assoc p X.wires with
  | some q => X.insert1 u succ p q
  | none => X

/-- The net for `0 + 0`, with the result on the free port `([0], 0)`. -/
def base : XNet Arith :=
  XNet.ofWires [([1], add), ([2], zero), ([3], zero)] [([0], 0)]
    [(([1], 0), ([2], 0)), (([1], 1), ([3], 0)), (([1], 2), ([0], 0))]

/-- The net for `0 + n`. -/
def sumSnd : Nat → XNet Arith
  | 0 => base
  | n + 1 => push (sumSnd n) ([1], 1) [n + 4]

/-- The net for `m + n`, with the result on the free port `([0], 0)`: `m`
successors are put on the first argument of the adder of `0 + 0`, and `n` on
the second. -/
def sum : Nat → Nat → XNet Arith
  | 0, n => sumSnd n
  | m + 1, n => push (sum m n) ([1], 0) [m + n + 4]

/-- Read the numeral whose principal port is wired to `p`, if there is one. -/
def readNat (X : XNet Arith) : Nat → Port → Option Nat
  | 0, _ => none
  | fuel + 1, p =>
    match assoc p X.wires with
    | some (i, 0) =>
      match assoc i X.agents with
      | some zero => some 0
      | some succ => (readNat X fuel (i, 1)).map (· + 1)
      | _ => none
    | _ => none

/-- `2 + 3 = 5`: the net for `2 + 3` is valid, normalizes in three steps,
and the numeral then wired to the free port is `5`. -/
theorem two_plus_three :
    ((sum 2 3).normalize xsys 20).map (fun r => (readNat r.1 10 ([0], 0), r.2)) =
      some (some 5, 3) := by
  decide

/-! ### Addition is correct, for all inputs -/

/-- The interaction system of `xsys`. -/
abbrev system : System Arith := xsys.sys

theorem rule_add_zero : system.rule add zero = some addZero.toX.toRhs := rfl
theorem rule_add_succ : system.rule add succ = some addSucc.toX.toRhs := rfl

/-- **The system of `Arith` contains addition**, in the sense of
`Addition.Rules`: what is proved in `Addition` for any such system holds
in it.  The notions below are those of `Addition` at the symbols of
`Arith`. -/
theorem rules : Addition.Rules system zero succ add :=
  ⟨by decide, by decide, by decide, rfl, rfl⟩

/-- Agent `i` is the head of the numeral `k`. -/
abbrev Num (N : Net Arith) : Id → Nat → Prop := Addition.Num ar zero succ N

/-- The port `p` is wired to the numeral `k`. -/
abbrev IsNum (N : Net Arith) (p : Port) (k : Nat) : Prop := Addition.IsNum ar zero succ N p k

/-- Above the port `x` there are `j` successors, the last of which has its
principal port wired to `r`. -/
abbrev Tower (N : Net Arith) : Port → Nat → Port → Prop := Addition.Tower ar succ N

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

theorem Num.label : ∀ {k : Nat} {i : Id}, Num N i k → N.agent i zero ∨ N.agent i succ :=
  Addition.Num.label

/-- Numerals are observations. -/
theorem Num.obs (ho : N.ObsEq ar M) : ∀ {k : Nat} {i : Id}, Num N i k → Num M i k :=
  Addition.Num.obs ho

theorem IsNum.obs (ho : N.ObsEq ar M) {p : Port} {k : Nat} (h : IsNum N p k) : IsNum M p k :=
  Addition.IsNum.obs ho h

/-- A numeral under a tower of `j` successors is a numeral `j` larger. -/
theorem Tower.num : ∀ {j : Nat} {x : Port} {n : Nat},
    Tower N x j r → IsNum N x n → IsNum N r (j + n) :=
  Addition.Tower.num

/-- The situation that addition is about: the only adder `a` of the net has
the numeral `m` as its first argument and the numeral `n` as its second, and
its result goes up a tower of `j` successors to the free port `r`. -/
abbrev Config (N : Net Arith) (a : Id) (j m n : Nat) (r : Port) : Prop :=
  Addition.Config ar zero succ add N a j m n r

variable {j m n : Nat}

/-- `0 + n = n`: the adder meets `zero`; one step later `r` carries the
numeral `j + n` and the net has no adder left. -/
theorem Config.zero_step (c : Config N a j 0 n r) :
    ∃ N', Step system N N' ∧ IsNum N' r (j + n) ∧ ∀ i, ¬ N'.agent i add :=
  Addition.Config.zero_step rules c

/-- `S m + n = S (m + n)`: the adder meets `succ`; one step later a new
adder faces `m`, under a tower one successor higher. -/
theorem Config.succ_step (c : Config N a j (m + 1) n r) :
    ∃ N' a', Step system N N' ∧ Config N' a' (j + 1) m n r :=
  Addition.Config.succ_step rules c

/-- The adder runs for `m + 1` steps, after which `r` carries the numeral
`j + m + n` and the net has no adder left. -/
theorem Config.steps : ∀ {m : Nat} {N : Net Arith} {a : Id} {j : Nat}, Config N a j m n r →
    ∃ N', Steps (Step system) (m + 1) N N' ∧ IsNum N' r (j + m + n) ∧ ∀ i, ¬ N'.agent i add :=
  fun c => Addition.Config.steps rules c

/-- A net without adders is normal. -/
theorem normal_of_no_add (h : ∀ i, ¬ N.agent i add) : Normal (Step system) N := by
  rintro N' ⟨a, b, α, β, R, red, -⟩
  have hα : α ≠ add := fun e => h a (e ▸ red.ha)
  have hβ : β ≠ add := fun e => h b (e ▸ red.hb)
  have hnone : system.rule α β = none := by
    cases α <;> cases β <;> first | rfl | exact absurd rfl hα | exact absurd rfl hβ
  have hr := red.rule
  rw [hnone] at hr
  cases hr

/-- **Addition is correct, for all inputs.**  A net whose only adder has the
numerals `m` and `n` as arguments and the free port `r` as result reduces in
`m + 1` steps to a normal form in which `r` carries the numeral `m + n`. -/
theorem add_correct (c : Config N a 0 m n r) :
    ∃ N', Steps (Step system) (m + 1) N N' ∧ Normal (Step system) N' ∧ IsNum N' r (m + n) := by
  obtain ⟨N', sts, hnum, hno⟩ := c.steps
  rw [Nat.zero_add] at hnum
  exact ⟨N', sts, normal_of_no_add hno, hnum⟩

/-- **The reducer adds.**  On a valid input in that situation, with fuel
for `m + 1` steps, the reducer stops after exactly `m + 1` steps on a net in
which `r` carries the numeral `m + n`. -/
theorem run_add {X : XNet Arith} (hX : X.Ok ar) (c : Config X.toNet a 0 m n r) {fuel : Nat}
    (hf : m + 1 ≤ fuel) :
    (X.run xsys fuel).1.step xsys = none ∧ (X.run xsys fuel).2 = m + 1 ∧
      IsNum (X.run xsys fuel).1.toNet r (m + n) := by
  obtain ⟨N', sts, hn, hnum⟩ := add_correct c
  have csts : Steps (CStep system) (m + 1) (X.toNet.compact ar) (N'.compact ar) :=
    Steps.cstep hX.1 sts
  rw [hX.2] at csts
  have hn' : Normal (CStep system) (N'.compact ar) := (normal_compact (Steps.wf hX.1 sts)).1 hn
  obtain ⟨stop, e₁, e₂⟩ := XNet.run_complete (xs := xsys) hX csts hn' hf
  refine ⟨stop, e₁, ?_⟩
  rw [e₂]
  exact hnum.obs (Net.compact_obs ar N')

/-! ### The nets for `m + n` are valid, for all `m` and `n` -/

theorem Num.insert1 (hm' : (N.insert1 u succ p q).Matching ar)
    (hm : N.Matching ar) (hp : ∀ i, N.agent i succ → (i, 1) ≠ p) (hq : ∀ i : Id, (i, 1) ≠ q) :
    ∀ {k : Nat} {i : Id}, Num N i k → Num (N.insert1 u succ p q) i k
  | 0, _, hz => .inl hz
  | _ + 1, i, ⟨hs, i', hp', hn⟩ =>
    ⟨.inl hs, i', hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hp', hp i hs, hq i⟩),
      Num.insert1 hm' hm hp hq hn⟩

/-- The identifiers in use are the one-element lists of the numbers below
`b`. -/
def Below (X : XNet Arith) (b : Nat) : Prop :=
  ∀ i, X.toNet.Used i → ∃ j, j < b ∧ i = [j]

theorem append_singleton {l : List Nat} {b j : Nat} (e : l ++ [b] = [j]) : l = [] ∧ b = j := by
  cases l with
  | nil => exact ⟨rfl, List.head_eq_of_cons_eq e⟩
  | cons x l' =>
    have e' : x :: (l' ++ [b]) = [j] := e
    have := (List.cons.inj e').2
    simp at this

theorem Below.fresh {X : XNet Arith} {b : Nat} (hb : Below X b) (l : List Nat) :
    ¬ X.toNet.Used (l ++ [b]) := by
  intro hu
  obtain ⟨j, hj, e⟩ := hb _ hu
  have := (append_singleton e).2
  omega

theorem Below.fresh' {X : XNet Arith} {b : Nat} (hb : Below X b) (l : List Nat) (i : Id)
    (α : Arith) (hi : X.toNet.agent i α) : [b] ≠ l ++ i := by
  intro e
  obtain ⟨j, hj, rfl⟩ := hb i (.inl ⟨α, hi⟩)
  have := (append_singleton e.symm).2
  omega

/-- The situation of addition, on a valid input whose identifiers are
numbered below `b`. -/
structure Good (X : XNet Arith) (m n b : Nat) : Prop where
  ok : X.Ok ar
  config : Config X.toNet [1] 0 m n ([0], 0)
  below : Below X b

theorem push_eq {X : XNet Arith} (hX : X.Ok ar) {p q : Port} (h : X.toNet.Paired ar p q)
    (u : Id) : push X p u = X.insert1 u succ p q := by
  have e : assoc p X.wires = some q := hX.exact.assoc_eq hX.1.wiring (hX.link_iff.2 h)
  unfold push
  rw [e]

theorem Below.push {X : XNet Arith} {b : Nat} (hb : Below X b) (hX : X.Ok ar) {p q : Port}
    (h : X.toNet.Paired ar p q) : Below (push X p [b]) (b + 1) := by
  intro i hi
  rw [push_eq hX h, XNet.insert1_toNet] at hi
  rcases Net.used_insert1 (hX.link_iff.2 h) hX.1.symm hi with hu | rfl
  · obtain ⟨j, hj, e⟩ := hb i hu
    exact ⟨j, by omega, e⟩
  · exact ⟨b, by omega, rfl⟩

/-- One more successor on the first argument. -/
theorem Good.push_fst {X : XNet Arith} {m n b : Nat} (g : Good X m n b) :
    Good (push X ([1], 0) [b]) (m + 1) n (b + 1) := by
  have c := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := c.fst
  obtain ⟨t, hpt, hnt⟩ := c.snd
  obtain ⟨x, hpx, htx⟩ := c.out
  have hm' : (X.toNet.insert1 [b] succ ([1], 0) (h, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hph) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Num X.toNet i k →
      Num (X.toNet.insert1 [b] succ ([1], 0) (h, 0)) i k :=
    Num.insert1 hm' hm (fun _ _ => port_ne_snd (by decide)) (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, g.below.push hX hph⟩
  · rw [push_eq hX hph, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [push_eq hX hph, XNet.insert1_toNet]
    refine ⟨hm'.wf, .inl c.ha, ?_, ?_, ?_, ?_, c.free⟩
    · rintro i (hi | ⟨-, e⟩)
      · exact c.only i hi
      · cases e
    · exact ⟨[b], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, h,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnh⟩
    · exact ⟨t, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hpt, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩), hnum hnt⟩
    · exact ⟨x, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hpx, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩), htx⟩

/-- One more successor on the second argument. -/
theorem Good.push_snd {X : XNet Arith} {m n b : Nat} (g : Good X m n b) :
    Good (push X ([1], 1) [b]) m (n + 1) (b + 1) := by
  have c := g.config
  have hX := g.ok
  have hm := XNet.ok_iff_matching.1 hX
  obtain ⟨h, hph, hnh⟩ := c.fst
  obtain ⟨t, hpt, hnt⟩ := c.snd
  obtain ⟨x, hpx, htx⟩ := c.out
  have hsucc : ∀ i, X.toNet.agent i succ → i ≠ [1] := by
    rintro i hi rfl
    exact absurd (c.wf.agent_fun hi c.ha) (by decide)
  have ht1 : t ≠ [1] := by
    rintro rfl
    rcases hnt.label with hl | hl
    · exact absurd (c.wf.agent_fun hl c.ha) (by decide)
    · exact absurd (c.wf.agent_fun hl c.ha) (by decide)
  have hm' : (X.toNet.insert1 [b] succ ([1], 1) (t, 0)).Matching ar :=
    hm.insert1 rfl (hm.paired_iff.1 hpt) g.below.fresh g.below.fresh'
  have hnum : ∀ {k : Nat} {i : Id}, Num X.toNet i k →
      Num (X.toNet.insert1 [b] succ ([1], 1) (t, 0)) i k :=
    Num.insert1 hm' hm (fun i hi e => hsucc i hi (congrArg Prod.fst e))
      (fun _ => port_ne_snd (by decide))
  refine ⟨?_, ?_, g.below.push hX hpt⟩
  · rw [push_eq hX hpt, XNet.ok_iff_matching, XNet.insert1_toNet]
    exact hm'
  · rw [push_eq hX hpt, XNet.insert1_toNet]
    refine ⟨hm'.wf, .inl c.ha, ?_, ?_, ?_, ?_, c.free⟩
    · rintro i (hi | ⟨-, e⟩)
      · exact c.only i hi
      · cases e
    · exact ⟨h, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hph, port_ne_snd (by decide),
        fun e => ht1 (congrArg Prod.fst e).symm⟩), hnum hnh⟩
    · exact ⟨[b], hm'.paired_iff.2 (.inr (.inl ⟨rfl, rfl⟩)), .inr ⟨rfl, rfl⟩, t,
        hm'.paired_iff.2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))), hnum hnt⟩
    · exact ⟨x, hm'.paired_iff.2 (.inl ⟨hm.paired_iff.1 hpx, port_ne_snd (by decide),
        port_ne_snd (by decide)⟩), htx⟩

/-- The identifiers of a finite net. -/
def usedIds (X : XNet Arith) : List Id :=
  X.agents.map (·.1) ++ X.wires.map (·.1.1) ++ X.free.map (·.1)

theorem mem_usedIds {X : XNet Arith} {i : Id} (h : X.toNet.Used i) : i ∈ usedIds X := by
  unfold usedIds
  rcases h with ⟨γ, hγ⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨(i, γ), hγ, rfl⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨((i, k), q), hl, rfl⟩))
  · exact List.mem_append_right _ (List.mem_map.2 ⟨(i, k), hf, rfl⟩)

theorem good_base : Good base 0 0 4 := by
  have hX : base.Ok ar := by decide
  refine ⟨hX, ⟨hX.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show ([1], add) ∈ base.agents
    decide
  · intro i hi
    have hi' : (i, add) ∈ [(([1] : Id), add), ([2], zero), ([3], zero)] := hi
    simpa using hi'
  · exact ⟨[2], hX.link_iff.1 (by decide), show ([2], zero) ∈ base.agents by decide⟩
  · exact ⟨[3], hX.link_iff.1 (by decide), show ([3], zero) ∈ base.agents by decide⟩
  · exact ⟨([0], 0), hX.link_iff.1 (by decide), rfl⟩
  · show ([0], 0) ∈ base.free
    decide
  · intro i hi
    have hall : ∀ i ∈ usedIds base, ∃ j, j < 4 ∧ i = [j] := by decide
    exact hall i (mem_usedIds hi)

theorem good_sumSnd : ∀ n, Good (sumSnd n) 0 n (n + 4)
  | 0 => good_base
  | n + 1 => (good_sumSnd n).push_snd

theorem good_sum : ∀ m n, Good (sum m n) m n (m + n + 4)
  | 0, n => by
    rw [Nat.zero_add]
    exact good_sumSnd n
  | m + 1, n => by
    have e : m + 1 + n + 4 = m + n + 4 + 1 := by omega
    rw [e]
    exact (good_sum m n).push_fst

/-- The nets for `m + n` are valid inputs of the reducer, for all `m` and
`n`. -/
theorem sum_ok (m n : Nat) : (sum m n).Ok ar := (good_sum m n).ok

theorem assoc_agent {X : XNet Arith} (hX : X.Ok ar) {i : Id} {γ : Arith}
    (h : X.toNet.agent i γ) : assoc i X.agents = some γ := by
  obtain ⟨γ', e⟩ := assoc_of_mem (show (i, γ) ∈ X.agents from h)
  rw [e, hX.1.agent_fun h (assoc_mem e)]

/-- Reading a numeral off a valid net gives its value. -/
theorem readNat_of_isNum {X : XNet Arith} (hX : X.Ok ar) :
    ∀ {k : Nat} {p : Port} {fuel : Nat}, IsNum X.toNet p k → k < fuel →
      readNat X fuel p = some k
  | 0, p, fuel, ⟨i, hp, hz⟩, hk => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have e₁ : assoc p X.wires = some (i, 0) :=
      hX.exact.assoc_eq hX.1.wiring (hX.link_iff.2 hp)
    have e₂ : assoc i X.agents = some zero := assoc_agent hX hz
    simp only [readNat, e₁, e₂]
  | k + 1, p, fuel, ⟨i, hp, hs, i', hp', hn⟩, hk => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have e₁ : assoc p X.wires = some (i, 0) :=
      hX.exact.assoc_eq hX.1.wiring (hX.link_iff.2 hp)
    have e₂ : assoc i X.agents = some succ := assoc_agent hX hs
    have ih : readNat X f (i, 1) = some k :=
      readNat_of_isNum hX ⟨i', hp', hn⟩ (by omega)
    simp only [readNat, e₁, e₂, ih, Option.map_some]

/-- **The reducer computes `m + n`, for all `m` and `n`.**  Given fuel for
`m + 1` steps, it takes exactly `m + 1` steps on the net for `m + n`, stops,
and the numeral then read off the free port is `m + n`. -/
theorem sum_correct (m n : Nat) :
    ((sum m n).run xsys (m + 1)).2 = m + 1 ∧
      ((sum m n).run xsys (m + 1)).1.step xsys = none ∧
      readNat ((sum m n).run xsys (m + 1)).1 (m + n + 1) ([0], 0) = some (m + n) := by
  have g := good_sum m n
  obtain ⟨stop, e, hnum⟩ := run_add g.ok g.config (Nat.le_refl (m + 1))
  have hY := (XNet.run_steps (xs := xsys) g.ok (m + 1)).2
  exact ⟨e, stop, readNat_of_isNum hY hnum (by omega)⟩

/-- Addition closes no loop. -/
example : ((sum 2 3).runLoops xsys 20).map (·.2) = some (3, 0) := by
  decide

/-- No rule of addition costs more than 81 operations. -/
theorem stepBound_le : ∀ α β R, xsys.rule α β = some R → stepBound ar α β R ≤ 81 := by
  intro α β R h
  cases α <;> cases β <;>
    first
      | (cases h; done)
      | (rw [← Option.some.inj h]; decide)

/-- **Addition in linear time**, counted in hash-map operations: the
hash-map reducer adds `m` and `n` with at most three operations per wire
entry of the input and 81 per step, of which there are `m + 1`. -/
theorem sum_cost (m n : Nat) :
    ((HNet.ofXNet (sum m n)).runC xsys (m + 1)).cost ≤
      3 * (sum m n).wires.length + 81 * (m + 1) := by
  have hX := sum_ok m n
  obtain ⟨hk, hstop, -⟩ := sum_correct m n
  obtain ⟨-, e, -⟩ := HNet.run_of_run (xs := xsys) hX hstop
  have h := HNet.runC_cost_ofXNet stepBound_le (sum m n) (m + 1)
  rw [e, hk] at h
  exact h

theorem insert1_wires_length_le (X : XNet Arith) (u : Id) (γ : Arith) (p q : Port) :
    (X.insert1 u γ p q).wires.length ≤ X.wires.length + 4 := by
  have h := List.length_filter_le (fun e : Port × Port => decide (e.1 ≠ p ∧ e.1 ≠ q)) X.wires
  show (X.wires.filter fun e => decide (e.1 ≠ p ∧ e.1 ≠ q)).length + 1 + 1 + 1 + 1 ≤ _
  omega

theorem push_wires_length_le (X : XNet Arith) (p : Port) (u : Id) :
    (push X p u).wires.length ≤ X.wires.length + 4 := by
  unfold push
  split
  · exact insert1_wires_length_le X u succ p _
  · omega

theorem sumSnd_wires_length_le : ∀ n, (sumSnd n).wires.length ≤ 4 * n + 6
  | 0 => by decide
  | n + 1 => by
    have h₁ := push_wires_length_le (sumSnd n) ([1], 1) [n + 4]
    have h₂ := sumSnd_wires_length_le n
    show (push (sumSnd n) ([1], 1) [n + 4]).wires.length ≤ _
    omega

theorem sum_wires_length_le : ∀ m n, (sum m n).wires.length ≤ 4 * (m + n) + 6
  | 0, n => by
    rw [Nat.zero_add]
    exact sumSnd_wires_length_le n
  | m + 1, n => by
    have h₁ := push_wires_length_le (sum m n) ([1], 0) [m + n + 4]
    have h₂ := sum_wires_length_le m n
    show (push (sum m n) ([1], 0) [m + n + 4]).wires.length ≤ _
    omega

/-- **Addition in linear time**, in closed form: at most `93 * m + 12 * n +
99` hash-map operations to add `m` and `n`. -/
theorem sum_cost_le (m n : Nat) :
    ((HNet.ofXNet (sum m n)).runC xsys (m + 1)).cost ≤ 93 * m + 12 * n + 99 := by
  have h₁ := sum_cost m n
  have h₂ := sum_wires_length_le m n
  omega

/-- **Addition on the machine.**  With any number of threads and any
schedule, an execution on the net for `m + n` that ends with every thread
idle and no active pair in memory has made `m + 1` claims, and the memory
holds the numeral `m + n`. -/
theorem sum_machine (m n : Nat) {k : Nat} {M : Mach Arith}
    (hr : MRun system k (Mach.init (sum m n).toNet) M) (hq : M.Quiet)
    (hn : Normal (Step system) M.mem) : k = m + 1 ∧ IsNum M.mem ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  obtain ⟨e, ek⟩ := ((hr.final g.ok.1 hq hn).2 hs).2 hn'
  rw [e] at hnum
  exact ⟨ek.symm, hnum⟩

/-- No execution on the net for `m + n` makes more than `m + 1` claims, and
every one of them can be continued to the end. -/
theorem sum_machine_complete (m n : Nat) {k : Nat} {M : Mach Arith}
    (hr : MRun system k (Mach.init (sum m n).toNet) M) :
    k ≤ m + 1 ∧ ∃ M', MRun system (m + 1 - k) M M' ∧ M'.Quiet ∧
      Normal (Step system) M'.mem ∧ IsNum M'.mem ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  obtain ⟨M', hr', hq, e⟩ := xsys.mrun_complete g.ok.1 hs hn' hr
  have hk := hr.claims_le g.ok.1 hs hn'
  rw [← e] at hn' hnum
  exact ⟨hk, M', hr', hq, hn', hnum⟩

/-- **Addition by the program**: a run on the net for `m + n` that ends with
every thread idle after `m + 1` claims leaves the numeral `m + n` in memory,
whatever the schedule and the number of threads. -/
theorem sum_exec {m n nt : Nat} {σ : List Nat}
    (hq : ((XMach.init (sum m n) nt).exec xsys σ).1.quiet = true)
    (hk : ((XMach.init (sum m n) nt).exec xsys σ).2 = m + 1) :
    IsNum ((XMach.init (sum m n) nt).exec xsys σ).1.mem.toNet ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  have hr := XMach.exec_mrun xsys (sum m n) nt σ
  rw [hk] at hr
  have e := hr.quiet_eq g.ok.1 hs hn' (XMach.quiet_toMach hq)
  rw [← e] at hnum
  exact hnum

/-- `1 + 1` on two threads taking turns: the first claim is made by one
thread and the second by the other. -/
example : IsNum ((XMach.init (sum 1 1) 2).exec xsys
    ((List.range 100).map (· % 2))).1.mem.toNet ([0], 0) 2 :=
  sum_exec (m := 1) (n := 1) (by decide +kernel) (by decide +kernel)

example : (XMach.init (sum 1 1) 2).claimers xsys ((List.range 100).map (· % 2)) = [0, 1] := by
  decide +kernel

/-- `2 + 3` on three threads taking turns. -/
example : IsNum ((XMach.init (sum 2 3) 3).exec xsys
    ((List.range 200).map (· % 3))).1.mem.toNet ([0], 0) 5 :=
  sum_exec (m := 2) (n := 3) (by decide +kernel) (by decide +kernel)

/-- Addition has one active pair at a time, and here the same thread finds
it each time. -/
example : (XMach.init (sum 2 3) 3).claimers xsys ((List.range 200).map (· % 3)) = [0, 0, 0] := by
  decide +kernel

/-- **One thread alone adds**: the program run with a single thread on the
net for `m + n` ends, after `m + 1` claims, with the numeral `m + n` in
memory. -/
theorem sum_solo (m n : Nat) : ∃ L, ∀ L', L ≤ L' →
    ((XMach.init (sum m n) 1).exec xsys (List.replicate L' 0)).1.quiet = true ∧
      ((XMach.init (sum m n) 1).exec xsys (List.replicate L' 0)).2 = m + 1 ∧
      IsNum ((XMach.init (sum m n) 1).exec xsys (List.replicate L' 0)).1.mem.toNet
        ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  obtain ⟨L, hL⟩ := XMach.solo_complete (xs := xsys) g.ok.1 hs hn'
  refine ⟨L, fun L' h => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hL L' h
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- **Addition by threads that take turns**: with any number of threads and
any order of turns in which every thread keeps getting turns, the threads
come to rest after `m + 1` claims, with the numeral `m + n` in memory. -/
theorem sum_turns (m n : Nat) {nt : Nat} (M : Nat → XMach Arith) (t c : Nat → Nat)
    (h0 : M 0 = XMach.init (sum m n) nt)
    (hturn : ∀ i, Turn xsys (M i) (t i) (M (i + 1)) (c i))
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ t j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → (M i).quiet = true ∧ claimsUpTo c i = m + 1 ∧
      IsNum (M i).mem.toNet ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  obtain ⟨i₀, h⟩ := XMach.turns_complete (xs := xsys) g.ok.1 hs hn' M t c h0 hturn hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨-, h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- **Addition, under any schedule**: a run on the net for `m + n` that ends
with every thread at rest has made `m + 1` claims and left the numeral
`m + n` in memory. -/
theorem sum_rest (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : List Nat)
    (hr : ((XMach.init (sum m n) nt).exec xsys σ).1.resting = true) :
    ((XMach.init (sum m n) nt).exec xsys σ).2 = m + 1 ∧
      IsNum ((XMach.init (sum m n) nt).exec xsys σ).1.mem.toNet ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  obtain ⟨h₁, h₂⟩ := XMach.exec_rest (xs := xsys) g.ok.1 hnt hs hn' σ hr
  refine ⟨h₁, ?_⟩
  rw [h₂]
  exact hnum

/-- `2 + 3` on three threads taking turns one action at a time: after three
hundred actions every thread is at rest. -/
example : IsNum ((XMach.init (sum 2 3) 3).exec xsys
    ((List.range 300).map (· % 3))).1.mem.toNet ([0], 0) 5 :=
  (sum_rest 2 3 (by decide) _ (by decide +kernel)).2

/-- **Addition under any fair schedule**: with any number of threads, whose
actions may overlap in any way, as long as every thread keeps being
scheduled the run comes to rest after `m + 1` claims with the numeral
`m + n` in memory. -/
theorem sum_fair (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((XMach.init (sum m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (sum m n) nt).trace xsys σ i).2 = m + 1 ∧
      IsNum ((XMach.init (sum m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) g.ok.1 hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h i hi
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- No rule of addition writes more than two agents or eight segments. -/
theorem xsys_bounded : xsys.Bounded 2 8 := by
  intro α β R h
  cases α <;> cases β <;>
    first
      | (cases h; done)
      | (rw [← Option.some.inj h]; decide)

theorem push_agents_length_le (X : XNet Arith) (p : Port) (u : Id) :
    (push X p u).agents.length ≤ X.agents.length + 1 := by
  unfold push
  split
  · exact Nat.le_refl _
  · exact Nat.le_succ _

theorem sumSnd_agents_length_le : ∀ n, (sumSnd n).agents.length ≤ n + 3
  | 0 => by decide
  | n + 1 => by
    have h₁ := push_agents_length_le (sumSnd n) ([1], 1) [n + 4]
    have h₂ := sumSnd_agents_length_le n
    show (push (sumSnd n) ([1], 1) [n + 4]).agents.length ≤ _
    omega

theorem sum_agents_length_le : ∀ m n, (sum m n).agents.length ≤ m + n + 3
  | 0, n => by
    rw [Nat.zero_add]
    exact sumSnd_agents_length_le n
  | m + 1, n => by
    have h₁ := push_agents_length_le (sum m n) ([1], 0) [m + n + 4]
    have h₂ := sum_agents_length_le m n
    show (push (sum m n) ([1], 0) [m + n + 4]).agents.length ≤ _
    omega

/-- A successor with a name above all the names in use is a new agent. -/
theorem push_nodup {X : XNet Arith} {b : Nat} (hb : Below X b) (p : Port)
    (h : (X.agents.map Prod.fst).Nodup) : ((push X p [b]).agents.map Prod.fst).Nodup := by
  unfold push
  split
  · show (([b] : Id) :: X.agents.map Prod.fst).Nodup
    refine List.nodup_cons.2 ⟨fun hm => ?_, h⟩
    obtain ⟨e, he, e1⟩ := List.mem_map.1 hm
    obtain ⟨j, hj, ej⟩ := hb e.1 (.inl ⟨e.2, he⟩)
    rw [e1] at ej
    have e2 : b = j := List.head_eq_of_cons_eq ej
    omega
  · exact h

theorem sumSnd_nodup : ∀ n, ((sumSnd n).agents.map Prod.fst).Nodup
  | 0 => by decide
  | n + 1 => push_nodup (good_sumSnd n).below ([1], 1) (sumSnd_nodup n)

/-- No agent is listed twice in the net for `m + n`. -/
theorem sum_nodup : ∀ m n, ((sum m n).agents.map Prod.fst).Nodup
  | 0, n => sumSnd_nodup n
  | m + 1, n => push_nodup (good_sum m n).below ([1], 0) (sum_nodup m n)

/-- The bound for one pass on the net for `m + n`, in closed form. -/
theorem sum_passBound_le (m n : Nat) :
    (sum m n).passBound (m + 1) 2 8 ≤ 33 * m + 11 * n + 49 := by
  have ha := sum_agents_length_le m n
  have hw := sum_wires_length_le m n
  show 7 * ((sum m n).agents.length + 2 * (m + 1)) + ((sum m n).wires.length + 8 * (m + 1)) ≤ _
  omega

/-- **Addition in a bounded number of actions.**  With any number of
threads, each scheduled in every window of `F` actions, the run on the net
for `m + n` is at rest with the numeral `m + n` after `F` times

    (m + 2) * (33 * m + 11 * n + 49) + 11 * (m + 1) + 1

actions. -/
theorem sum_fair_bound (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((m + 2) * (33 * m + 11 * n + 49) + 11 * (m + 1) + 1) ≤ i →
      ((XMach.init (sum m n) nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (sum m n) nt).trace xsys σ i).2 = m + 1 ∧
      IsNum ((XMach.init (sum m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m + n) := by
  intro i hi
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  have h₁ := Nat.mul_le_mul_left (m + 2) (sum_passBound_le m n)
  have hle : F * ((m + 1 + 1) * (sum m n).passBound (m + 1) 2 8 +
      (m + 1) * (2 + 8 + 1) + 1) ≤ i := by
    refine Nat.le_trans (Nat.mul_le_mul_left F ?_) hi
    show (m + 2) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) + 1 ≤
      (m + 2) * (33 * m + 11 * n + 49) + 11 * (m + 1) + 1
    omega
  obtain ⟨h₁, h₂, h₃⟩ :=
    XMach.fair_bound (xs := xsys) g.ok.1 (sum_nodup m n) hnt xsys_bounded hs hn' σ hfair i hle
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- `2 + 3` on three threads scheduled in turn: the bound is 1,878 actions.
(The run is in fact at rest after three hundred.) -/
example : ∀ i, 1878 ≤ i →
    ((XMach.init (sum 2 3) 3).trace xsys (· % 3) i).1.resting = true ∧
      ((XMach.init (sum 2 3) 3).trace xsys (· % 3) i).2 = 3 ∧
      IsNum ((XMach.init (sum 2 3) 3).trace xsys (· % 3) i).1.mem.toNet ([0], 0) 5 :=
  sum_fair_bound 2 3 (by decide) (· % 3) roundRobin_fair

/-- **Addition in a bounded number of turns.**  With any number of threads,
each of which gets a turn in every window of `W` turns, the threads rest
and the memory holds the numeral `m + n` after `W` times

    (m + 1) * (3 * m + n + 6) + m + n + 4

turns. -/
theorem sum_turns_bound (m n : Nat) {nt : Nat} (M : Nat → XMach Arith) (t c : Nat → Nat)
    (h0 : M 0 = XMach.init (sum m n) nt)
    (hturn : ∀ i, Turn xsys (M i) (t i) (M (i + 1)) (c i)) {W : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + W ∧ t j = u) :
    ∀ i, W * ((m + 1) * (3 * m + n + 6) + m + n + 4) ≤ i →
      (∀ u, u < nt → (M i).ths[u]? = some ⟨[], .idle⟩) ∧ claimsUpTo c i = m + 1 ∧
        IsNum (M i).mem.toNet ([0], 0) (m + n) := by
  intro i hi
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  have ha := sum_agents_length_le m n
  have hle : W * ((sum m n).agents.length +
      (m + 1) * ((sum m n).agents.length + 2 * (m + 1) + 1) + 1) ≤ i := by
    refine Nat.le_trans (Nat.mul_le_mul_left W ?_) hi
    have h₁ : (m + 1) * ((sum m n).agents.length + 2 * (m + 1) + 1) ≤
        (m + 1) * (3 * m + n + 6) := Nat.mul_le_mul_left (m + 1) (by omega)
    omega
  obtain ⟨h₁, h₂, h₃⟩ := XMach.turns_bound (xs := xsys) g.ok.1 xsys_bounded hs hn' M t c h0
    hturn hfair i hle
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact hnum

/-- **Addition in bounded time**, whatever the schedule: with `nt` threads
the run on the net for `m + n` never takes more time than

    ((nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)) * (18 * m + 6 * n + 35)
-/
theorem sum_time (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (XMach.init (sum m n) nt).time xsys σ i ≤
      ((nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)) * (18 * m + 6 * n + 35) := by
  intro i
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  have h := XMach.time_bound (xs := xsys) g.ok.1 (sum_nodup m n) hnt xsys_bounded hs hn' σ i
  refine Nat.le_trans h (Nat.mul_le_mul ?_ ?_)
  · have h₁ := Nat.mul_le_mul_left (nt + m + 1) (sum_passBound_le m n)
    show (nt + m + 1) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      (nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)
    omega
  · have ha := sum_agents_length_le m n
    have hw := sum_wires_length_le m n
    omega

/-- `2 + 3` on three threads, however they are scheduled: the bound on the
time is 81,969. -/
example : ∀ (σ : Nat → Nat) (i : Nat), (XMach.init (sum 2 3) 3).time xsys σ i ≤ 81969 :=
  fun σ => sum_time 2 3 (by decide) σ

/-- Scheduled in turn, the run in fact takes 1,213. -/
example : ∀ i, 300 ≤ i → (XMach.init (sum 2 3) 3).time xsys (· % 3) i = 1213 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  rw [XMach.time_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- **Addition on the indexed memory in bounded time**, in closed form: the
same number of actions as on lists, at seventeen each, and the agents
taken afresh once for each step. -/
theorem sum_itime (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (IMach.init (sum m n) nt).time xsys σ i ≤
      ((nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)) * 17 +
        (2 * m + 3) * (3 * m + n + 5) := by
  intro i
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  have h := IMach.time_bound (xs := xsys) g.ok.1 (sum_nodup m n) hnt xsys_bounded hs hn' σ i
  refine Nat.le_trans h (Nat.add_le_add (Nat.mul_le_mul ?_ (Nat.le_refl 17))
    (Nat.mul_le_mul ?_ ?_))
  · have h₁ := Nat.mul_le_mul_left (nt + m + 1) (sum_passBound_le m n)
    show (nt + m + 1) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      (nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)
    omega
  · show 2 * (m + 1) + 1 ≤ 2 * m + 3
    omega
  · have ha := sum_agents_length_le m n
    show (sum m n).agents.length + 2 * (m + 1) ≤ 3 * m + n + 5
    omega

/-- `2 + 3` on three threads on the indexed memory, however they are
scheduled: the bound on the time is 15,755, in operations on the maps. -/
example : ∀ (σ : Nat → Nat) (i : Nat), (IMach.init (sum 2 3) 3).time xsys σ i ≤ 15755 :=
  fun σ => sum_itime 2 3 (by decide) σ

/-- **`2 + 3` on three threads scheduled in turn, on the indexed memory**:
the run takes 420, where on lists it takes 1,213. -/
theorem sum23_itime : ∀ i, 300 ≤ i → (IMach.init (sum 2 3) 3).time xsys (· % 3) i = 420 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  have g := good_sum 2 3
  rw [IMach.time_rest (xs := xsys) g.ok.1 (sum_nodup 2 3) (by decide) (· % 3)
    (by decide +kernel) d,
    (IMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 2 3) (by decide) (· % 3) 300).1]
  decide +kernel

/-- Of the first three hundred actions of that run 107 are not rests, and
of the 420 the three threads spend 53 on taking the agents afresh. -/
theorem sum23_work : (XMach.init (sum 2 3) 3).work xsys (· % 3) 300 = 107 ∧
    (IMach.init (sum 2 3) 3).fresh xsys (· % 3) 300 = 53 := by
  have g := good_sum 2 3
  rw [(IMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 2 3) (by decide) (· % 3) 300).2.2]
  decide +kernel

/-- **`12 + 12` on one thread, on lists**: the run takes 10,514. -/
theorem sum12_time :
    ∀ i, 320 ≤ i → (XMach.init (sum 12 12) 1).time xsys (fun _ => 0) i = 10514 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  rw [XMach.time_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **The same run on the indexed memory** takes 2,028. -/
theorem sum12_itime :
    ∀ i, 320 ≤ i → (IMach.init (sum 12 12) 1).time xsys (fun _ => 0) i = 2028 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  have g := good_sum 12 12
  rw [IMach.time_rest (xs := xsys) g.ok.1 (sum_nodup 12 12) (by decide) (fun _ => 0)
    (by decide +kernel) d,
    (IMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 12 12) (by decide) (fun _ => 0) 320).1]
  decide +kernel

/-- The thread makes 313 actions that are not rests, and of the 2,028 it
spends 737 on taking the agents afresh, thirteen times. -/
theorem sum12_work : (XMach.init (sum 12 12) 1).work xsys (fun _ => 0) 320 = 313 ∧
    (IMach.init (sum 12 12) 1).fresh xsys (fun _ => 0) 320 = 737 ∧
    ((XMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).2 = 13 := by
  have g := good_sum 12 12
  rw [(IMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 12 12) (by decide) (fun _ => 0)
    320).2.2]
  decide +kernel

/-- **`12 + 12` on one thread with lazy lists** takes 1,394, where the
indexed memory takes 2,028 and lists take 10,514. -/
theorem sum12_ltime :
    ∀ i, 320 ≤ i → (LMach.init (sum 12 12) 1).time xsys (fun _ => 0) i = 1394 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  have g := good_sum 12 12
  have sh := LMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 12 12) (nt := 1) (by decide)
    (fun _ => 0) 320
  have sim := LMach.init_sim (xs := xsys) g.ok.1 (sum_nodup 12 12) (nt := 1) (by decide)
    (fun _ => 0) 320
  have hr : ((LMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).1.resting = true := by
    apply LMach.resting_of_flags
    · rw [sim.1]
      decide +kernel
    · rw [sh.2.2.2]
      decide +kernel
  rw [(LMach.time_rest (fun _ => 0) hr d).2, sh.1]
  decide +kernel

/-- In that run the thread drops 26 dead cells. -/
theorem sum12_lskips : (LMach.init (sum 12 12) 1).skips xsys (fun _ => 0) 320 = 26 := by
  have g := good_sum 12 12
  rw [(LMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 12 12) (nt := 1) (by decide)
    (fun _ => 0) 320).2.1]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, with lazy lists**: the
run takes 407. -/
theorem sum23_ltime : ∀ i, 300 ≤ i → (LMach.init (sum 2 3) 3).time xsys (· % 3) i = 407 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  have g := good_sum 2 3
  have sh := LMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 2 3) (nt := 3) (by decide)
    (· % 3) 300
  have sim := LMach.init_sim (xs := xsys) g.ok.1 (sum_nodup 2 3) (nt := 3) (by decide)
    (· % 3) 300
  have hr : ((LMach.init (sum 2 3) 3).trace xsys (· % 3) 300).1.resting = true := by
    apply LMach.resting_of_flags
    · rw [sim.1]
      decide +kernel
    · rw [sh.2.2.2]
      decide +kernel
  rw [(LMach.time_rest (· % 3) hr d).2, sh.1]
  decide +kernel

/-- **`12 + 12` on one thread on the packing memory** takes 1,444: fifty
more than with lazy lists alone, for one packing of the log. -/
theorem sum12_ptime :
    ∀ i, 320 ≤ i → (PMach.init (sum 12 12) 1).time xsys (fun _ => 0) i = 1444 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  have g := good_sum 12 12
  have sh := PMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 12 12) (nt := 1) (by decide)
    (fun _ => 0) 320
  have sim := PMach.init_sim (xs := xsys) g.ok.1 (sum_nodup 12 12) (nt := 1) (by decide)
    (fun _ => 0) 320
  have hr : ((PMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).1.resting = true := by
    apply PMach.resting_of_flags
    · rw [sim.1]
      decide +kernel
    · rw [sh.2.2.2]
      decide +kernel
  rw [(PMach.time_rest (fun _ => 0) hr d).2, sh.1]
  decide +kernel

/-- In that run the thread drops no dead cell, and the log ends with the
25 live cells. -/
theorem sum12_pskips : (PMach.init (sum 12 12) 1).skips xsys (fun _ => 0) 320 = 0 ∧
    ((PMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).1.mem.mem.flags.length = 25 := by
  have g := good_sum 12 12
  have sh := PMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 12 12) (nt := 1) (by decide)
    (fun _ => 0) 320
  rw [sh.2.1, sh.2.2.1]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, on the packing
memory**: the run takes 407, as with lazy lists; the log is not packed. -/
theorem sum23_ptime : ∀ i, 300 ≤ i → (PMach.init (sum 2 3) 3).time xsys (· % 3) i = 407 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  have g := good_sum 2 3
  have sh := PMach.time_shadow (xs := xsys) g.ok.1 (sum_nodup 2 3) (nt := 3) (by decide)
    (· % 3) 300
  have sim := PMach.init_sim (xs := xsys) g.ok.1 (sum_nodup 2 3) (nt := 3) (by decide)
    (· % 3) 300
  have hr : ((PMach.init (sum 2 3) 3).trace xsys (· % 3) 300).1.resting = true := by
    apply PMach.resting_of_flags
    · rw [sim.1]
      decide +kernel
    · rw [sh.2.2.2]
      decide +kernel
  rw [(PMach.time_rest (· % 3) hr d).2, sh.1]
  decide +kernel

/-- **`12 + 12` on one thread on the ordered memory** takes 1,444. -/
theorem sum12_ttime :
    ∀ i, 320 ≤ i → (TMach.init (sum 12 12) 1).time xsys (fun _ => 0) i = 1444 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  have g := good_sum 12 12
  rw [TMach.time_eq (xs := xsys) g.ok.1 (sum_nodup 12 12) (by decide) (fun _ => 0),
    XMach.ttime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, on the ordered memory**:
the run takes 451. -/
theorem sum23_ttime : ∀ i, 300 ≤ i → (TMach.init (sum 2 3) 3).time xsys (· % 3) i = 451 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  have g := good_sum 2 3
  rw [TMach.time_eq (xs := xsys) g.ok.1 (sum_nodup 2 3) (by decide) (· % 3),
    XMach.ttime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- **`12 + 12` on one thread, on the ordered memory with the depth of the
map charged**: the run takes 2,186, where it takes 1,444 when an
operation on the map counts one. -/
theorem sum12_lgtime :
    ∀ i, 320 ≤ i → (TMach.init (sum 12 12) 1).lgtime xsys (fun _ => 0) i = 2186 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  have g := good_sum 12 12
  rw [TMach.lgtime_eq (xs := xsys) g.ok.1 (sum_nodup 12 12) (by decide) (fun _ => 0),
    XMach.lgtime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, on the ordered memory
with the depth of the map charged**: the run takes 688. -/
theorem sum23_lgtime :
    ∀ i, 300 ≤ i → (TMach.init (sum 2 3) 3).lgtime xsys (· % 3) i = 688 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  have g := good_sum 2 3
  rw [TMach.lgtime_eq (xs := xsys) g.ok.1 (sum_nodup 2 3) (by decide) (· % 3),
    XMach.lgtime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- **`12 + 12` on one thread, the depth of the trees charged**: the run
takes 2,240, where the digits of the sizes charge 2,186.  The kernel
computes it on the replay, which keeps the trees of the run and no hash
map. -/
theorem sum12_dtime :
    ∀ i, 320 ≤ i → (TMach.init (sum 12 12) 1).dtime xsys (fun _ => 0) i = 2240 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  have g := good_sum 12 12
  rw [TMach.dtime_replay (xs := xsys) g.ok.1 (sum_nodup 12 12) (by decide) (fun _ => 0),
    RMach.dtime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, the depth of the trees
charged**: the run takes 692, where the digits of the sizes charge 688. -/
theorem sum23_dtime :
    ∀ i, 300 ≤ i → (TMach.init (sum 2 3) 3).dtime xsys (· % 3) i = 692 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  have g := good_sum 2 3
  rw [TMach.dtime_replay (xs := xsys) g.ok.1 (sum_nodup 2 3) (by decide) (· % 3),
    RMach.dtime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- **`12 + 12` on one thread, the calls on the trees counted**: the run
takes 2,007, where the depth of the trees charges 2,240.  The kernel
computes it on the replay. -/
theorem sum12_ctime :
    ∀ i, 320 ≤ i → (TMach.init (sum 12 12) 1).ctime xsys (fun _ => 0) i = 2007 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  have g := good_sum 12 12
  rw [TMach.ctime_replay (xs := xsys) g.ok.1 (sum_nodup 12 12) (by decide) (fun _ => 0),
    RMach.ctime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, the calls on the trees
counted**: the run takes 573, where the depth of the trees charges 692. -/
theorem sum23_ctime :
    ∀ i, 300 ≤ i → (TMach.init (sum 2 3) 3).ctime xsys (· % 3) i = 573 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  have g := good_sum 2 3
  rw [TMach.ctime_replay (xs := xsys) g.ok.1 (sum_nodup 2 3) (by decide) (· % 3),
    RMach.ctime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- **`12 + 12` on one thread, on ordered maps alone, every call
counted**: the run takes 4,343, where the ordered memory with its hash
maps counted one takes 2,007.  There is no hash map, so the kernel
computes the run as it stands. -/
theorem sum12_otime :
    ∀ i, 320 ≤ i → (OMach.init (sum 12 12) 1).ctime xsys (fun _ => 0) i = 4343 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  rw [OMach.ctime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, on ordered maps alone,
every call counted**: the run takes 948. -/
theorem sum23_otime :
    ∀ i, 300 ≤ i → (OMach.init (sum 2 3) 3).ctime xsys (· % 3) i = 948 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  rw [OMach.ctime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- **`12 + 12` on one thread, on ordered maps alone, everything
counted**: calls, the cells read to compare names, and the nodes built.
The run takes 11,902. -/
theorem sum12_ftime :
    ∀ i, 320 ≤ i → (OMach.init (sum 12 12) 1).ftime xsys (fun _ => 0) i = 11902 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  rw [OMach.ftime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, on ordered maps alone,
everything counted**: the run takes 2,195. -/
theorem sum23_ftime :
    ∀ i, 300 ≤ i → (OMach.init (sum 2 3) 3).ftime xsys (· % 3) i = 2195 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  rw [OMach.ftime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- **`12 + 12` on one thread, numbered, on ordered maps alone, everything
counted.**  The run takes 10,999; with names that grow it took 11,902. -/
theorem sum12_ztime :
    ∀ i, 320 ≤ i → (ZMach.init (sum 12 12) 1).ftime xsys (fun _ => 0) i = 10999 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  rw [ZMach.ftime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, numbered, everything
counted**: the run takes 2,126; with names that grow it took 2,195. -/
theorem sum23_ztime :
    ∀ i, 300 ≤ i → (ZMach.init (sum 2 3) 3).ftime xsys (· % 3) i = 2126 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  rw [ZMach.ftime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- No rule of addition needs more than three numbers. -/
theorem xsys_span : xsys.SpanLe 3 := by
  intro α β R h
  cases α <;> cases β <;>
    first
      | (cases h; done)
      | (rw [← Option.some.inj h]; decide)

/-- **The numbers of `12 + 12` on one thread.**  The net starts with its
numbers below 28.  At rest, after 13 claims, the counter is at 64, under
the bound `28 + 3 * 13`, and the next stamp is 51. -/
theorem sum12_numbers :
    (sum 12 12).top = 28 ∧
      ((ZMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).2 = 13 ∧
      ((ZMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).1.cnt = 64 ∧
      ((ZMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).1.mem.stamp = 51 := by
  decide +kernel

/-- **`12 + 12` on one thread, numbered, in bits.**  The run takes 28,984
bits, for a count of 10,999. -/
theorem sum12_btime :
    ∀ i, 320 ≤ i → (ZMach.init (sum 12 12) 1).btime xsys (fun _ => 0) i = 28984 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 320 + d := ⟨i - 320, by omega⟩
  rw [ZMach.btime_rest (xs := xsys) (fun _ => 0) (by decide +kernel) d]
  decide +kernel

/-- **`2 + 3` on three threads scheduled in turn, numbered, in bits**: the
run takes 4,220 bits, for a count of 2,126. -/
theorem sum23_btime :
    ∀ i, 300 ≤ i → (ZMach.init (sum 2 3) 3).btime xsys (· % 3) i = 4220 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 300 + d := ⟨i - 300, by omega⟩
  rw [ZMach.btime_rest (xs := xsys) (· % 3) (by decide +kernel) d]
  decide +kernel

/-- No port of a rule of addition has an index above two. -/
theorem xsys_ports : xsys.PortsLe 2 := by
  intro α β R h
  cases α <;> cases β <;>
    first
      | (cases h; done)
      | (rw [← Option.some.inj h]
         intro x hx
         refine ⟨?_, fun y hy => ?_⟩
         · revert x
           decide
         · revert y
           revert x
           decide)

/-- No port of a segment of `12 + 12` has an index above two. -/
theorem sum12_ports : (sum 12 12).PortsLe 2 := by
  show ∀ e ∈ (sum 12 12).wires, e.1.2 ≤ 2 ∧ e.2.2 ≤ 2
  decide +kernel

/-- **The names of a net numbered below `b` are numbers of one cell, below
`b`.** -/
theorem Below.sizes {X : XNet Arith} {b : Nat} (hb : Below X b)
    (hsym : ∀ {p q : Port}, X.toNet.link p q → X.toNet.link q p) :
    X.NamesLe 1 ∧ X.top ≤ b := by
  have hA : ∀ e ∈ X.agents, X.toNet.Used e.1 := fun e he => .inl ⟨e.2, he⟩
  have hW1 : ∀ e ∈ X.wires, X.toNet.Used e.1.1 := fun e he => .inr (.inl ⟨e.1.2, e.2, he⟩)
  have hW2 : ∀ e ∈ X.wires, X.toNet.Used e.2.1 := fun e he =>
    .inr (.inl ⟨e.2.2, e.1, hsym (p := e.1) (q := e.2) he⟩)
  have hF : ∀ p ∈ X.free, X.toNet.Used p.1 := fun p hp => .inr (.inr ⟨p.2, hp⟩)
  have len : ∀ i, X.toNet.Used i → i.length ≤ 1 := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := hb i hi
    exact Nat.le_refl 1
  refine ⟨⟨fun e he => len _ (hA e he), fun e he => ⟨len _ (hW1 e he), len _ (hW2 e he)⟩⟩, ?_⟩
  refine foldr_max_le _ _ (fun x hx => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, hkj⟩ := List.mem_flatten.1 hk
  have hU : X.toNet.Used j := by
    have hj' : j ∈ X.agents.map (·.1) ++ X.wires.map (·.1.1) ++ X.wires.map (·.2.1) ++
        X.free.map (·.1) := hj
    rcases List.mem_append.1 hj' with h | h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
          exact hA e he
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
          exact hW1 e he
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
        exact hW2 e he
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact hF p hp
  obtain ⟨j', hj', rfl⟩ := hb j hU
  have e : k = j' := List.mem_singleton.1 hkj
  show k + 1 ≤ b
  omega

/-- A successor put on a port makes no index above one. -/
theorem push_ports {X : XNet Arith} {P : Nat} (hX : X.PortsLe P) {p : Port} (hp : p.2 ≤ P)
    (h1 : 1 ≤ P) (u : Id) : (push X p u).PortsLe P := by
  unfold push
  cases hq : assoc p X.wires with
  | none => exact hX
  | some q =>
    have hq' : q.2 ≤ P := (hX _ (assoc_mem hq)).2
    intro e he
    have he' : e ∈ (p, (u, 0)) :: ((u, 0), p) :: ((u, 1), q) :: (q, (u, 1)) ::
        X.wires.filter (fun e => decide (e.1 ≠ p ∧ e.1 ≠ q)) := he
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨hp, Nat.zero_le _⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨Nat.zero_le _, hp⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨h1, hq'⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨hq', h1⟩
    · exact hX e (List.mem_filter.1 he').1

theorem base_ports : base.PortsLe 2 := by
  show ∀ e ∈ base.wires, e.1.2 ≤ 2 ∧ e.2.2 ≤ 2
  decide

theorem sumSnd_ports : ∀ n, (sumSnd n).PortsLe 2
  | 0 => base_ports
  | n + 1 => push_ports (sumSnd_ports n) (Nat.le_succ 1) (Nat.le_succ 1) _

/-- **No port of a net for a sum has an index above two.** -/
theorem sum_ports : ∀ m n, (sum m n).PortsLe 2
  | 0, n => sumSnd_ports n
  | m + 1, n => push_ports (sum_ports m n) (Nat.zero_le 2) (Nat.le_succ 1) _

/-- The bound on the actions of an addition that are not rests. -/
def sumWork (m n nt : Nat) : Nat := (nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)

/-- **Addition, numbered, in bounded time**, in closed form, with
everything counted and whatever the schedule. -/
theorem sum_ztime (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    (ZMach.init (sum m n) nt).ftime xsys σ i ≤
      sumWork m n nt * (15 + 84 * lg (15 * m + 5 * n + 19)) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, -⟩ := Below.sizes g.below g.ok.1.symm
  have h := ZMach.ftime_bound (xs := xsys) g.ok.1 (sum_nodup m n) hnt xsys_bounded hL hs hn'
    σ i
  refine Nat.le_trans h (Nat.mul_le_mul ?_ ?_)
  · have h₁ := Nat.mul_le_mul_left (nt + m + 1) (sum_passBound_le m n)
    show (nt + m + 1) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      (nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)
    omega
  · have ha := sum_agents_length_le m n
    have hw := sum_wires_length_le m n
    have hl := lg_mono (show (sum m n).agents.length + 2 * (m + 1) +
      ((sum m n).wires.length + 8 * (m + 1)) ≤ 15 * m + 5 * n + 19 by omega)
    show 2 + 8 + 5 + 4 * ((max 1 1 + 6) * (3 * lg ((sum m n).agents.length + 2 * (m + 1) +
      ((sum m n).wires.length + 8 * (m + 1))))) ≤ _
    rw [Nat.max_self]
    omega

/-- **Addition, numbered, in a bounded number of bits**, in closed form
and whatever the schedule: the bound on the count, times three times the
bits of a key.  A key has a port index of at most two, and one cell that
fits in the word of the first factor. -/
theorem sum_btime (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    (ZMach.init (sum m n) nt).btime xsys σ i ≤
      3 * ((lg (5 * m + 2 * n + 13 + sumWork m n nt) + 5) *
        (sumWork m n nt * (15 + 84 * lg (15 * m + 5 * n + 19)))) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, htop⟩ := Below.sizes g.below g.ok.1.symm
  have ha := sum_agents_length_le m n
  have hw := sum_wires_length_le m n
  have h₁ := Nat.mul_le_mul_left (nt + m + 1) (sum_passBound_le m n)
  have hwork : (nt + (m + 1)) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      sumWork m n nt := by
    show (nt + m + 1) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      (nt + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)
    omega
  have hpow := lt_pow_lg (5 * m + 2 * n + 13 + sumWork m n nt)
  have hW : (sum m n).top + 3 * (m + 1 + 1) <
      2 ^ lg (5 * m + 2 * n + 13 + sumWork m n nt) := by omega
  have hW' : (sum m n).agents.length + ((nt + (m + 1)) * (sum m n).passBound (m + 1) 2 8 +
      (m + 1) * (2 + 8 + 1)) < 2 ^ lg (5 * m + 2 * n + 13 + sumWork m n nt) := by omega
  have h := ZMach.btime_bound (xs := xsys) g.ok.1 (sum_nodup m n) xsys_span xsys_ports
    (sum_ports m n) hnt xsys_bounded hL hs hn' σ hW hW' i
  refine Nat.le_trans h (Nat.mul_le_mul_left 3 (Nat.mul_le_mul ?_ (Nat.mul_le_mul hwork ?_)))
  · have e1 : lg 2 = 3 := by decide
    rw [Nat.max_self, Nat.one_mul, e1]
    omega
  · have hl := lg_mono (show (sum m n).agents.length + 2 * (m + 1) +
      ((sum m n).wires.length + 8 * (m + 1)) ≤ 15 * m + 5 * n + 19 by omega)
    show 2 + 8 + 5 + 4 * ((max 1 1 + 6) * (3 * lg ((sum m n).agents.length + 2 * (m + 1) +
      ((sum m n).wires.length + 8 * (m + 1))))) ≤ _
    rw [Nat.max_self]
    omega

/-- `12 + 12` on one thread, numbered, however it is scheduled: the bound
on the count is 7,028,955.  The run takes 10,999. -/
example : ∀ (σ : Nat → Nat) (i : Nat),
    (ZMach.init (sum 12 12) 1).ftime xsys σ i ≤ 7028955 :=
  fun σ => sum_ztime 12 12 (by decide) σ

/-- In bits the bound is 421,737,300.  The run takes 28,984. -/
example : ∀ (σ : Nat → Nat) (i : Nat),
    (ZMach.init (sum 12 12) 1).btime xsys σ i ≤ 421737300 :=
  fun σ => sum_btime 12 12 (by decide) σ

/-- `2 + 3` on three threads, numbered, however they are scheduled: the
bounds are 632,727 counted and 30,370,896 bits.  Scheduled in turn the run
takes 2,126 and 4,220. -/
example : ∀ (σ : Nat → Nat) (i : Nat),
    (ZMach.init (sum 2 3) 3).ftime xsys σ i ≤ 632727 ∧
      (ZMach.init (sum 2 3) 3).btime xsys σ i ≤ 30370896 :=
  fun σ i => ⟨sum_ztime 2 3 (by decide) σ i, sum_btime 2 3 (by decide) σ i⟩

/-- The actions one thread takes to add `m` and `n`, as the runs show. -/
def soloWork (m n : Nat) : Nat := if m = 0 then 6 * n + 13 else 22 * m + 3 * n + 13

/-- The row `m = 0` of the table of `solo_work_checked`. -/
theorem solo_work_row0 : ∀ n, n < 9 →
    ((XMach.init (sum 0 n) 1).trace xsys (fun _ => 0) (soloWork 0 n)).1.resting = true ∧
      (XMach.init (sum 0 n) 1).work xsys (fun _ => 0) (soloWork 0 n) = soloWork 0 n := by
  decide +kernel

/-- The row `m = 1` of the table of `solo_work_checked`. -/
theorem solo_work_row1 : ∀ n, n < 9 →
    ((XMach.init (sum 1 n) 1).trace xsys (fun _ => 0) (soloWork 1 n)).1.resting = true ∧
      (XMach.init (sum 1 n) 1).work xsys (fun _ => 0) (soloWork 1 n) = soloWork 1 n := by
  decide +kernel

/-- The row `m = 2` of the table of `solo_work_checked`. -/
theorem solo_work_row2 : ∀ n, n < 9 →
    ((XMach.init (sum 2 n) 1).trace xsys (fun _ => 0) (soloWork 2 n)).1.resting = true ∧
      (XMach.init (sum 2 n) 1).work xsys (fun _ => 0) (soloWork 2 n) = soloWork 2 n := by
  decide +kernel

/-- The row `m = 3` of the table of `solo_work_checked`. -/
theorem solo_work_row3 : ∀ n, n < 9 →
    ((XMach.init (sum 3 n) 1).trace xsys (fun _ => 0) (soloWork 3 n)).1.resting = true ∧
      (XMach.init (sum 3 n) 1).work xsys (fun _ => 0) (soloWork 3 n) = soloWork 3 n := by
  decide +kernel

/-- The row `m = 4` of the table of `solo_work_checked`. -/
theorem solo_work_row4 : ∀ n, n < 9 →
    ((XMach.init (sum 4 n) 1).trace xsys (fun _ => 0) (soloWork 4 n)).1.resting = true ∧
      (XMach.init (sum 4 n) 1).work xsys (fun _ => 0) (soloWork 4 n) = soloWork 4 n := by
  decide +kernel

/-- The row `m = 5` of the table of `solo_work_checked`. -/
theorem solo_work_row5 : ∀ n, n < 9 →
    ((XMach.init (sum 5 n) 1).trace xsys (fun _ => 0) (soloWork 5 n)).1.resting = true ∧
      (XMach.init (sum 5 n) 1).work xsys (fun _ => 0) (soloWork 5 n) = soloWork 5 n := by
  decide +kernel

/-- The row `m = 6` of the table of `solo_work_checked`. -/
theorem solo_work_row6 : ∀ n, n < 9 →
    ((XMach.init (sum 6 n) 1).trace xsys (fun _ => 0) (soloWork 6 n)).1.resting = true ∧
      (XMach.init (sum 6 n) 1).work xsys (fun _ => 0) (soloWork 6 n) = soloWork 6 n := by
  decide +kernel

/-- The row `m = 7` of the table of `solo_work_checked`. -/
theorem solo_work_row7 : ∀ n, n < 9 →
    ((XMach.init (sum 7 n) 1).trace xsys (fun _ => 0) (soloWork 7 n)).1.resting = true ∧
      (XMach.init (sum 7 n) 1).work xsys (fun _ => 0) (soloWork 7 n) = soloWork 7 n := by
  decide +kernel

/-- The row `m = 8` of the table of `solo_work_checked`. -/
theorem solo_work_row8 : ∀ n, n < 9 →
    ((XMach.init (sum 8 n) 1).trace xsys (fun _ => 0) (soloWork 8 n)).1.resting = true ∧
      (XMach.init (sum 8 n) 1).work xsys (fun _ => 0) (soloWork 8 n) = soloWork 8 n := by
  decide +kernel

/-- **One thread adds in `22 * m + 3 * n + 13` actions, on every size
computed.**  For all `m` and `n` below nine the run of a single thread on
the net for `m + n` is at rest after exactly that many actions, none of
them a rest (`6 * n + 13` when `m` is zero).  This is a computation, size
by size; it is not a proof for every size.  The kernel computes the table
one row at a time (`solo_work_row0` to `solo_work_row8`): one computation
of all eighty-one runs needs about three times the memory of the largest
row. -/
theorem solo_work_checked : ∀ m, m < 9 → ∀ n, n < 9 →
    ((XMach.init (sum m n) 1).trace xsys (fun _ => 0) (soloWork m n)).1.resting = true ∧
      (XMach.init (sum m n) 1).work xsys (fun _ => 0) (soloWork m n) = soloWork m n
  | 0, _ => solo_work_row0
  | 1, _ => solo_work_row1
  | 2, _ => solo_work_row2
  | 3, _ => solo_work_row3
  | 4, _ => solo_work_row4
  | 5, _ => solo_work_row5
  | 6, _ => solo_work_row6
  | 7, _ => solo_work_row7
  | 8, _ => solo_work_row8
  | m + 9, h => absurd h (by omega)

/-- **A run whose work is known has its count bounded by it.**  When one
thread on the net for `m + n` is at rest after `B` actions of which `w`
are not rests, the time with everything counted is at most `w` times the
cost of an action. -/
theorem ztime_of_work (m n : Nat) {B w : Nat}
    (hr : ((XMach.init (sum m n) 1).trace xsys (fun _ => 0) B).1.resting = true)
    (hw : (XMach.init (sum m n) 1).work xsys (fun _ => 0) B = w) (i : Nat) :
    (ZMach.init (sum m n) 1).ftime xsys (fun _ => 0) i ≤
      w * (15 + 84 * lg (15 * m + 5 * n + 19)) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, -⟩ := Below.sizes g.below g.ok.1.symm
  have hwi : (XMach.init (sum m n) 1).work xsys (fun _ => 0) i ≤ w := by
    by_cases h : i ≤ B
    · have h' := XMach.work_mono (xs := xsys) (fun _ => 0) (XMach.init (sum m n) 1) h
      rw [hw] at h'
      exact h'
    · obtain ⟨d, rfl⟩ : ∃ d, i = B + d := ⟨i - B, by omega⟩
      rw [XMach.work_rest (xs := xsys) (fun _ => 0) hr d, hw]
      exact Nat.le_refl _
  have h := ZMach.ftime_le_work (xs := xsys) g.ok.1 (sum_nodup m n) (Nat.succ_pos 0)
    xsys_bounded hL hs hn' (fun _ => 0) i
  have ha := sum_agents_length_le m n
  have hwl := sum_wires_length_le m n
  have hl := lg_mono (show (sum m n).agents.length + 2 * (m + 1) +
    ((sum m n).wires.length + 8 * (m + 1)) ≤ 15 * m + 5 * n + 19 by omega)
  have hc : 2 + 8 + 5 + 4 * ((max 1 1 + 6) * (3 * lg ((sum m n).agents.length + 2 * (m + 1) +
      ((sum m n).wires.length + 8 * (m + 1))))) ≤ 15 + 84 * lg (15 * m + 5 * n + 19) := by
    rw [Nat.max_self]
    omega
  rw [Nat.mul_comm w]
  exact Nat.le_trans h (Nat.mul_le_mul hc hwi)

/-- The same in bits: at most three times the bits of a key for each unit
counted. -/
theorem btime_of_work (m n : Nat) {B w : Nat}
    (hr : ((XMach.init (sum m n) 1).trace xsys (fun _ => 0) B).1.resting = true)
    (hw : (XMach.init (sum m n) 1).work xsys (fun _ => 0) B = w) (i : Nat) :
    (ZMach.init (sum m n) 1).btime xsys (fun _ => 0) i ≤
      3 * ((lg (5 * m + 2 * n + 13 + sumWork m n 1) + 5) *
        (w * (15 + 84 * lg (15 * m + 5 * n + 19)))) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, htop⟩ := Below.sizes g.below g.ok.1.symm
  have ha := sum_agents_length_le m n
  have h₁ := Nat.mul_le_mul_left (1 + m + 1) (sum_passBound_le m n)
  have hwork : (1 + (m + 1)) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      sumWork m n 1 := by
    show (1 + m + 1) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      (1 + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)
    omega
  have hpow := lt_pow_lg (5 * m + 2 * n + 13 + sumWork m n 1)
  have hW : (sum m n).top + 3 * (m + 1 + 1) <
      2 ^ lg (5 * m + 2 * n + 13 + sumWork m n 1) := by omega
  have hW' : (sum m n).agents.length + ((1 + (m + 1)) * (sum m n).passBound (m + 1) 2 8 +
      (m + 1) * (2 + 8 + 1)) < 2 ^ lg (5 * m + 2 * n + 13 + sumWork m n 1) := by omega
  have h := ZMach.btime_le_ftime (xs := xsys) g.ok.1 (sum_nodup m n) xsys_span xsys_ports
    (sum_ports m n) (Nat.succ_pos 0) xsys_bounded hL hs hn' (fun _ => 0) hW hW' i
  refine Nat.le_trans h (Nat.mul_le_mul_left 3
    (Nat.mul_le_mul ?_ (ztime_of_work m n hr hw i)))
  have e1 : lg 2 = 3 := by decide
  rw [Nat.max_self, Nat.one_mul, e1]
  omega

/-- **On every size computed, one thread adds within the linear law times
the cost of an action**, counted and in bits. -/
theorem solo_ztime {m n : Nat} (hm : m < 9) (hn : n < 9) (i : Nat) :
    (ZMach.init (sum m n) 1).ftime xsys (fun _ => 0) i ≤
      soloWork m n * (15 + 84 * lg (15 * m + 5 * n + 19)) :=
  ztime_of_work m n (solo_work_checked m hm n hn).1 (solo_work_checked m hm n hn).2 i

theorem solo_btime {m n : Nat} (hm : m < 9) (hn : n < 9) (i : Nat) :
    (ZMach.init (sum m n) 1).btime xsys (fun _ => 0) i ≤
      3 * ((lg (5 * m + 2 * n + 13 + sumWork m n 1) + 5) *
        (soloWork m n * (15 + 84 * lg (15 * m + 5 * n + 19)))) :=
  btime_of_work m n (solo_work_checked m hm n hn).1 (solo_work_checked m hm n hn).2 i

/-- `12 + 12` on one thread: its 313 actions bound the count by 267,615
and the bits by 16,056,900, where the bounds for every schedule are
7,028,955 and 421,737,300.  The run takes 10,999 and 28,984. -/
theorem sum12_solo : ∀ i,
    (ZMach.init (sum 12 12) 1).ftime xsys (fun _ => 0) i ≤ 267615 ∧
      (ZMach.init (sum 12 12) 1).btime xsys (fun _ => 0) i ≤ 16056900 := by
  have hr : ((XMach.init (sum 12 12) 1).trace xsys (fun _ => 0) 320).1.resting = true := by
    decide +kernel
  exact fun i => ⟨ztime_of_work 12 12 hr sum12_work.1 i, btime_of_work 12 12 hr sum12_work.1 i⟩

/-- Where the chain of the first argument goes on: the successor numbered
`t`, or the zero at its end. -/
def below (n t : Nat) : Id := if n + 4 ≤ t then [t] else [2]

/-- **The chain of the first argument.**  The successors numbered from
`n + 4` to `hi` are agents of the memory, and the only segment at the
auxiliary port of each goes to the principal port of the one below. -/
structure Chain (n : Nat) (X : XNet Arith) (hi : Nat) : Prop where
  live : ∀ t, n + 4 ≤ t → t ≤ hi → assoc [t] X.agents = some .succ
  seg : ∀ t, n + 4 ≤ t → t ≤ hi → ∀ q, (([t], 1), q) ∈ X.wires ↔ q = (below n (t - 1), 0)

/-- **The memory before the first round**: the successor numbered `hi + 1`
is first in the list of agents and faces the adder. -/
structure Start (n : Nat) (X : XNet Arith) (hi : Nat) : Prop where
  head : ∃ rest, X.agents = ([hi + 1], .succ) :: rest
  top : n + 4 ≤ hi + 1
  adder : assoc [1] X.agents = some .add
  first : ∀ q, (([hi + 1], 0), q) ∈ X.wires ↔ q = ([1], 0)
  chain : Chain n X (hi + 1)
  fresh : ∀ t, n + 4 ≤ t → t ≤ hi + 1 → ∀ k q, (([0, t], k), q) ∉ X.wires

/-- **The memory before a later round**: the adder made in the last round
is first in the list of agents, and its principal port is one point away
from the next agent of the chain. -/
structure Steady (n : Nat) (X : XNet Arith) (hi : Nat) : Prop where
  head : ∃ rest, X.agents = ([0, hi + 1], .add) :: rest
  first : ∀ q, (([0, hi + 1], 0), q) ∈ X.wires ↔ q = ([hi + 1], 1)
  mid : ∀ q, (([hi + 1], 1), q) ∈ X.wires ↔ q = ([0, hi + 1], 0) ∨ q = (below n hi, 0)
  chain : Chain n X hi
  fresh : ∀ t, n + 4 ≤ t → t ≤ hi → ∀ k q, (([0, t], k), q) ∉ X.wires

/-- What the rounds need of the segments that a step between the adder `a`
and the successor `s` writes. -/
structure StepLinks (a s : Id) (L : List (Port × Port)) : Prop where
  adder : ∀ q, ((0 :: s, 0), q) ∈ L ↔ q = (s, 1)
  succ : ∀ q, ((s, 1), q) ∈ L ↔ q = (0 :: s, 0)
  names : ∀ e ∈ L, e.1.1 = a ∨ e.1.1 = s ∨ e.1.1 = 0 :: s ∨ e.1.1 = 0 :: a

theorem newLinks_add (a s : Id) : addSucc.toX.newLinks ar a s .add .succ =
    [((a, 1), (0 :: s, 1)), ((a, 2), (0 :: a, 0)), ((s, 1), (0 :: s, 0)),
     ((0 :: a, 0), (a, 2)), ((0 :: a, 1), (0 :: s, 2)), ((0 :: s, 0), (s, 1)),
     ((0 :: s, 1), (a, 1)), ((0 :: s, 2), (0 :: a, 1))] := rfl

theorem newLinks_swap (s a : Id) : addSucc.swap.toX.newLinks ar s a .succ .add =
    [((s, 1), (0 :: s, 0)), ((a, 1), (0 :: s, 1)), ((a, 2), (0 :: a, 0)),
     ((0 :: a, 0), (a, 2)), ((0 :: a, 1), (0 :: s, 2)), ((0 :: s, 0), (s, 1)),
     ((0 :: s, 1), (a, 1)), ((0 :: s, 2), (0 :: a, 1))] := rfl

theorem newAgents_add {a s : Id} (h : a ≠ s) :
    addSucc.toX.newAgents a s = [(0 :: a, .succ), (0 :: s, .add)] :=
  dedupFst_pair (x := (0 :: a, Arith.succ)) (y := (0 :: s, Arith.add))
    (fun e => h (List.cons.inj e).2)

theorem newAgents_swap {a s : Id} (h : a ≠ s) :
    addSucc.swap.toX.newAgents s a = [(0 :: a, .succ), (0 :: s, .add)] :=
  dedupFst_pair (x := (0 :: a, Arith.succ)) (y := (0 :: s, Arith.add))
    (fun e => h (List.cons.inj e).2)

theorem stepLinks_add {a s : Id} (h1 : a ≠ s) (h2 : s ≠ 0 :: a) :
    StepLinks a s (addSucc.toX.newLinks ar a s .add .succ) := by
  have hs : s ≠ 0 :: s := fun e => List.cons_ne_self 0 s e.symm
  rw [newLinks_add]
  refine ⟨fun q => ?_, fun q => ?_, fun e he => ?_⟩
  · simp [h1.symm, hs.symm]
  · simp [h1.symm, h2, hs]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem stepLinks_swap {a s : Id} (h1 : a ≠ s) (h2 : s ≠ 0 :: a) :
    StepLinks a s (addSucc.swap.toX.newLinks ar s a .succ .add) := by
  have hs : s ≠ 0 :: s := fun e => List.cons_ne_self 0 s e.symm
  rw [newLinks_swap]
  refine ⟨fun q => ?_, fun q => ?_, fun e he => ?_⟩
  · simp [h1.symm, hs.symm]
  · simp [h1.symm, h2, hs]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem below_pos {n t : Nat} (h : n + 4 ≤ t) : below n t = [t] := by
  unfold below
  rw [ite_pos' h]

/-- **After a step the memory is ready for the next round.**  When the
adder `a` and the successor numbered `h + 1` have fired, the new adder
`[0, h + 1]` is first in the list of agents, one point away from the next
agent of the chain, and the rest of the chain is as it was. -/
theorem steady_of_step {n : Nat} {X X' : XNet Arith} {a : Id} {h : Nat}
    {L : List (Port × Port)} (SL : StepLinks a [h + 1] L)
    (hW : ∀ e, e ∈ X'.wires ↔ e ∈ L ∨ e ∈ X.wires)
    (hHead : ∃ rest, X'.agents = ([0, h + 1], .add) :: rest)
    (hLive : ∀ t, n + 4 ≤ t → t ≤ h → assoc [t] X'.agents = assoc [t] X.agents)
    (ha1 : ∀ t, n + 4 ≤ t → a ≠ [t]) (ha2 : ∀ t, n + 4 ≤ t → t ≤ h → a ≠ [0, t])
    (ch : Chain n X (h + 1))
    (fr : ∀ t, n + 4 ≤ t → t ≤ h + 1 → ∀ k q, (([0, t], k), q) ∉ X.wires)
    (hn : n + 4 ≤ h + 1) : Steady n X' h := by
  have hname : ∀ t, n + 4 ≤ t → t ≤ h → ∀ k q, ((([t], k), q) : Port × Port) ∉ L := by
    intro t ht1 ht2 k q hm
    rcases SL.names _ hm with e | e | e | e
    · exact ha1 t ht1 e.symm
    · have e' : ([t] : Id) = [h + 1] := e
      injection e' with e1
      omega
    · have e' : ([t] : Id) = [0, h + 1] := e
      injection e' with _ e2
      cases e2
    · have e' : ([t] : Id) = 0 :: a := e
      injection e' with e1
      omega
  have hfresh : ∀ t, n + 4 ≤ t → t ≤ h → ∀ k q, ((([0, t], k), q) : Port × Port) ∉ L := by
    intro t ht1 ht2 k q hm
    rcases SL.names _ hm with e | e | e | e
    · exact ha2 t ht1 ht2 e.symm
    · have e' : ([0, t] : Id) = [h + 1] := e
      injection e' with _ e2
      cases e2
    · have e' : ([0, t] : Id) = [0, h + 1] := e
      injection e' with _ e2
      injection e2 with e3
      omega
    · have e' : ([0, t] : Id) = 0 :: a := e
      injection e' with _ e2
      exact ha1 t ht1 e2.symm
  refine ⟨hHead, fun q => ?_, fun q => ?_, ⟨fun t ht1 ht2 => ?_, fun t ht1 ht2 q => ?_⟩,
    fun t ht1 ht2 k q hm => ?_⟩
  · constructor
    · intro hm
      rcases (hW _).1 hm with hl | hx
      · exact (SL.adder q).1 hl
      · exact absurd hx (fr (h + 1) hn (Nat.le_refl _) 0 q)
    · intro e
      exact (hW _).2 (.inl ((SL.adder q).2 e))
  · have hseg := ch.seg (h + 1) hn (Nat.le_refl _) q
    rw [Nat.add_sub_cancel] at hseg
    constructor
    · intro hm
      rcases (hW _).1 hm with hl | hx
      · exact .inl ((SL.succ q).1 hl)
      · exact .inr (hseg.1 hx)
    · rintro (e | e)
      · exact (hW _).2 (.inl ((SL.succ q).2 e))
      · exact (hW _).2 (.inr (hseg.2 e))
  · rw [hLive t ht1 ht2]
    exact ch.live t ht1 (by omega)
  · have hseg := ch.seg t ht1 (by omega) q
    constructor
    · intro hm
      rcases (hW _).1 hm with hl | hx
      · exact absurd hl (hname t ht1 ht2 1 q)
      · exact hseg.1 hx
    · intro e
      exact (hW _).2 (.inr (hseg.2 e))
  · rcases (hW _).1 hm with hl | hx
    · exact hfresh t ht1 ht2 k q hl
    · exact fr t ht1 (by omega) k q hx

/-- **A later round of an addition, counted.**  The single thread takes the
adder, follows two segments to the next successor of the chain, claims,
writes two agents and eight segments, and is at a fresh start on a memory
ready for the next round: seventeen actions, none a rest. -/
theorem Steady.round {n : Nat} {X : XNet Arith} {h : Nat} (st : Steady n X (h + 1))
    (hn : n + 4 ≤ h + 1) :
    ∃ X', Works xsys X ⟨X.agents, .idle⟩ X' ⟨X'.agents, .idle⟩ 1 17 ∧ Steady n X' h := by
  obtain ⟨rest, hA⟩ := st.head
  have hb : below n (h + 1) = [h + 1] := below_pos hn
  have hne : ([0, h + 1 + 1] : Id) ≠ [h + 1] := fun e => by
    injection e with _ e2
    cases e2
  have h₁ : assoc [0, h + 1 + 1] X.agents = some .add := by
    rw [hA]
    show (if ([0, h + 1 + 1] : Id) = [0, h + 1 + 1] then some Arith.add
      else assoc _ rest) = _
    rw [ite_pos' rfl]
  have h₂ : assoc (([0, h + 1 + 1], 0) : Port) X.wires = some ([h + 1 + 1], 1) :=
    assoc_eq_of_unique ((st.first _).2 rfl) (fun q' hq => (st.first q').1 hq)
  have h₂' : nextSeg X.wires ([h + 1 + 1], 1) ([0, h + 1 + 1], 0) = some ([h + 1], 0) := by
    refine nextSeg_some ((st.mid _).2 (.inr (by rw [hb]))) (fun e => ?_) (fun q hq hqp => ?_)
    · injection e with e1 _
      injection e1 with _ e2
      cases e2
    · rcases (st.mid q).1 hq with e | e
      · exact absurd e hqp
      · rw [e, hb]
  have h₃ : assoc [h + 1] X.agents = some .succ := st.chain.live (h + 1) hn (Nat.le_refl _)
  have h₄ : assoc [h + 1] (X.takeAgent [0, h + 1 + 1]).agents = some .succ := by
    show assoc [h + 1] (X.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact h₃
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w := Works.claim_via (xs := xsys) (c := ([h + 1 + 1], 1)) rest h₁ h₂ rfl h₂' h₃ hne h₄ hR
  rw [← hA] at w
  have eA := newAgents_add (a := [0, h + 1 + 1]) (s := [h + 1]) hne
  have eK : 6 + ((addSucc.toX.newAgents [0, h + 1 + 1] [h + 1]).length +
      (addSucc.toX.newLinks xsys.sys.ar [0, h + 1 + 1] [h + 1] .add .succ).length + 1) =
      17 := by
    rw [eA]
    rfl
  rw [eK] at w
  refine ⟨_, w, ?_⟩
  have SL := stepLinks_add (a := [0, h + 1 + 1]) (s := [h + 1]) hne
    (fun e => by injection e with _ e2; cases e2)
  refine steady_of_step SL (fun e => XNet.mem_step_wires X _ _ _ _ e) ?_ ?_ ?_ ?_ st.chain
    st.fresh hn
  · rw [eA, XNet.step_agents]
    exact ⟨_, rfl⟩
  · intro t ht1 ht2
    have n1 : ¬ ([0, h + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n2 : ¬ ([0, 0, h + 1 + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n3 : ¬ ([h + 1] : Id) = [t] := fun e => by injection e with e1; omega
    have n4 : ¬ ([0, h + 1 + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    rw [eA, XNet.step_agents]
    show (if ([0, h + 1] : Id) = [t] then some Arith.add
      else if ([0, 0, h + 1 + 1] : Id) = [t] then some Arith.succ
      else assoc [t] ((X.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])).filter
        fun e => decide (e.1 ≠ [h + 1]))) = _
    rw [ite_neg' n1, ite_neg' n2, assoc_filter_ne, ite_neg' n3, assoc_filter_ne, ite_neg' n4]
  · intro t _ e
    injection e with _ e2
    cases e2
  · intro t _ ht2 e
    injection e with _ e2
    injection e2 with e3
    omega

/-- **The first round of an addition, counted.**  The single thread takes
the successor that faces the adder, claims, writes, and is at a fresh
start on a memory ready for the later rounds: sixteen actions, none a
rest. -/
theorem Start.round {n : Nat} {X : XNet Arith} {hi : Nat} (st : Start n X hi) :
    ∃ X', Works xsys X ⟨X.agents, .idle⟩ X' ⟨X'.agents, .idle⟩ 1 16 ∧ Steady n X' hi := by
  obtain ⟨rest, hA⟩ := st.head
  have ht := st.top
  have hne : ([hi + 1] : Id) ≠ [1] := fun e => by
    injection e with e1
    omega
  have hne' : ([1] : Id) ≠ [hi + 1] := fun e => hne e.symm
  have h₁ : assoc [hi + 1] X.agents = some .succ := by
    rw [hA]
    show (if ([hi + 1] : Id) = [hi + 1] then some Arith.succ else assoc _ rest) = _
    rw [ite_pos' rfl]
  have h₂ : assoc (([hi + 1], 0) : Port) X.wires = some ([1], 0) :=
    assoc_eq_of_unique ((st.first _).2 rfl) (fun q' hq => (st.first q').1 hq)
  have h₄ : assoc [1] (X.takeAgent [hi + 1]).agents = some .add := by
    show assoc [1] (X.agents.filter fun e => decide (e.1 ≠ [hi + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact st.adder
  have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
  have w := Works.claim_direct (xs := xsys) rest h₁ h₂ st.adder hne h₄ hR
  rw [← hA] at w
  have eA := newAgents_swap (a := [1]) (s := [hi + 1]) hne'
  have eK : 5 + ((addSucc.swap.toX.newAgents [hi + 1] [1]).length +
      (addSucc.swap.toX.newLinks xsys.sys.ar [hi + 1] [1] .succ .add).length + 1) = 16 := by
    rw [eA]
    rfl
  rw [eK] at w
  refine ⟨_, w, ?_⟩
  have SL := stepLinks_swap (a := [1]) (s := [hi + 1]) hne'
    (fun e => by injection e with _ e2; cases e2)
  refine steady_of_step SL (fun e => XNet.mem_step_wires X _ _ _ _ e) ?_ ?_ ?_ ?_ st.chain
    st.fresh ht
  · rw [eA, XNet.step_agents]
    exact ⟨_, rfl⟩
  · intro t ht1 ht2
    have n1 : ¬ ([0, hi + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n2 : ¬ ([0, 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n3 : ¬ ([1] : Id) = [t] := fun e => by injection e with e1; omega
    have n4 : ¬ ([hi + 1] : Id) = [t] := fun e => by injection e with e1; omega
    rw [eA, XNet.step_agents]
    show (if ([0, hi + 1] : Id) = [t] then some Arith.add
      else if ([0, 1] : Id) = [t] then some Arith.succ
      else assoc [t] ((X.agents.filter fun e => decide (e.1 ≠ [hi + 1])).filter
        fun e => decide (e.1 ≠ [1]))) = _
    rw [ite_neg' n1, ite_neg' n2, assoc_filter_ne, ite_neg' n3, assoc_filter_ne, ite_neg' n4]
  · intro t ht1 e
    injection e with e1
    omega
  · intro t _ _ e
    injection e with _ e2
    cases e2

/-- **The later rounds, one after the other**: `d` rounds of seventeen
actions each take the chain of the first argument down to its end. -/
theorem Steady.rounds {n : Nat} : ∀ (d : Nat) {X : XNet Arith}, Steady n X (n + 3 + d) →
    ∃ X', Works xsys X ⟨X.agents, .idle⟩ X' ⟨X'.agents, .idle⟩ d (17 * d) ∧
      Steady n X' (n + 3)
  | 0, X, st => ⟨X, .refl _ _, st⟩
  | d + 1, X, st => by
    obtain ⟨X₁, w₁, st₁⟩ := Steady.round (h := n + 3 + d) st (by omega)
    obtain ⟨X', w, st'⟩ := Steady.rounds d st₁
    refine ⟨X', ?_, st'⟩
    have w' := w₁.trans w
    have e1 : 1 + d = d + 1 := by omega
    have e2 : 17 + 17 * d = 17 * (d + 1) := by omega
    rw [e1, e2] at w'
    exact w'

/-- **All the rounds on the successors of the first argument, counted.**
From a memory in which `d + 1` successors are left, the single thread
claims each in turn, in `16 + 17 * d` actions, none of them a rest. -/
theorem Start.rounds {n d : Nat} {X : XNet Arith} (st : Start n X (n + 3 + d)) :
    ∃ X', Works xsys X ⟨X.agents, .idle⟩ X' ⟨X'.agents, .idle⟩ (d + 1) (16 + 17 * d) ∧
      Steady n X' (n + 3) := by
  obtain ⟨X₁, w₁, st₁⟩ := st.round
  obtain ⟨X', w, st'⟩ := Steady.rounds d st₁
  refine ⟨X', ?_, st'⟩
  have w' := w₁.trans w
  have e1 : 1 + d = d + 1 := by omega
  rw [e1] at w'
  exact w'

theorem push_some {X : XNet Arith} {p q : Port} (u : Id) (h : assoc p X.wires = some q) :
    push X p u = X.insert1 u .succ p q := by
  unfold push
  rw [h]

/-- What a successor put on the principal port of the adder does to the
segments. -/
theorem push_princ {X : XNet Arith} {u b : Id} (hu1 : u ≠ [1]) (hb1 : b ≠ [1]) (hbu : b ≠ u)
    (hfresh : ∀ k q, (((u, k), q) : Port × Port) ∉ X.wires) :
    (∀ q', ((([1], 0), q') : Port × Port) ∈ (X.insert1 u .succ ([1], 0) (b, 0)).wires ↔
        q' = (u, 0)) ∧
      (∀ q', (((u, 0), q') : Port × Port) ∈ (X.insert1 u .succ ([1], 0) (b, 0)).wires ↔
        q' = ([1], 0)) ∧
      (∀ q', (((u, 1), q') : Port × Port) ∈ (X.insert1 u .succ ([1], 0) (b, 0)).wires ↔
        q' = (b, 0)) ∧
      ∀ i q', i ≠ u → ((((i, 1), q') : Port × Port) ∈
        (X.insert1 u .succ ([1], 0) (b, 0)).wires ↔ ((i, 1), q') ∈ X.wires) := by
  have hu1' := hu1.symm
  have hb1' := hb1.symm
  have hbu' := hbu.symm
  refine ⟨fun q' => ?_, fun q' => ?_, fun q' => ?_, fun i q' hi => ?_⟩
  · rw [mem_insert1_wires]
    simp [*]
  · have h0 := hfresh 0 q'
    rw [mem_insert1_wires]
    simp [*]
  · have h1 := hfresh 1 q'
    rw [mem_insert1_wires]
    simp [*]
  · have hi' := hi.symm
    rw [mem_insert1_wires]
    simp [*]

theorem below_cases (n t : Nat) :
    (below n t = [t] ∧ n + 4 ≤ t) ∨ (below n t = [2] ∧ t < n + 4) := by
  unfold below
  by_cases h : n + 4 ≤ t
  · rw [ite_pos' h]
    exact .inl ⟨rfl, h⟩
  · rw [ite_neg' h]
    exact .inr ⟨rfl, by omega⟩

/-- In the net for `0 + n` the adder is an agent and its principal port
faces the zero numbered two. -/
theorem sumSnd_facts : ∀ n, assoc [1] (sumSnd n).agents = some .add ∧
    ∀ q, ((([1], 0), q) : Port × Port) ∈ (sumSnd n).wires ↔ q = ([2], 0)
  | 0 => by
    have hall : ∀ e ∈ base.wires, e.1 = ([1], 0) → e.2 = ([2], 0) := by decide
    have hmem : ((([1], 0), ([2], 0)) : Port × Port) ∈ base.wires := by decide
    refine ⟨by decide, fun q => ⟨fun h => hall _ h rfl, fun e => ?_⟩⟩
    rw [e]
    exact hmem
  | n + 1 => by
    obtain ⟨ad, pr⟩ := sumSnd_facts n
    have hu : ([n + 4] : Id) ≠ [1] := fun e => by
      injection e with e1
      omega
    cases hq : assoc (([1], 1) : Port) (sumSnd n).wires with
    | none =>
      have e : sumSnd (n + 1) = sumSnd n := by
        show push (sumSnd n) ([1], 1) [n + 4] = sumSnd n
        unfold push
        rw [hq]
      rw [e]
      exact ⟨ad, pr⟩
    | some q' =>
      have e : sumSnd (n + 1) = (sumSnd n).insert1 [n + 4] .succ ([1], 1) q' :=
        push_some [n + 4] hq
      have hs : (q', (([1], 1) : Port)) ∈ (sumSnd n).wires :=
        (good_sumSnd n).ok.1.symm (assoc_mem hq)
      have hq' : q' ≠ ([1], 0) := by
        intro e'
        rw [e'] at hs
        have h2 := (pr _).1 hs
        injection h2 with h3 _
        injection h3 with h4
        omega
      have hq'' := hq'.symm
      have hu' := hu.symm
      rw [e]
      refine ⟨?_, fun q => ?_⟩
      · show (if ([n + 4] : Id) = [1] then some Arith.succ
          else assoc [1] (sumSnd n).agents) = _
        rw [ite_neg' hu]
        exact ad
      · rw [mem_insert1_wires]
        simp [*]

/-- **The net for `m + n`, as the first round finds it.**  The adder is
an agent, its principal port faces the top of the chain of the first
argument, and the chain is in place. -/
structure Init (m n : Nat) (X : XNet Arith) : Prop where
  adder : assoc [1] X.agents = some .add
  princ : ∀ q, ((([1], 0), q) : Port × Port) ∈ X.wires ↔ q = (below n (m + n + 3), 0)
  chain : Chain n X (m + n + 3)

theorem init_sum : ∀ m n, Init m n (sum m n) ∧
    (1 ≤ m → (∃ rest, (sum m n).agents = ([m + n + 3], .succ) :: rest) ∧
      ∀ q, ((([m + n + 3], 0), q) : Port × Port) ∈ (sum m n).wires ↔ q = ([1], 0))
  | 0, n => by
    obtain ⟨ad, pr⟩ := sumSnd_facts n
    have e : below n (0 + n + 3) = [2] := by
      unfold below
      rw [ite_neg' (by omega)]
    refine ⟨⟨ad, fun q => ?_, ⟨fun t h1 h2 => absurd h2 (by omega),
      fun t h1 h2 => absurd h2 (by omega)⟩⟩, fun h => absurd h (by omega)⟩
    rw [e]
    exact pr q
  | m + 1, n => by
    obtain ⟨I, -⟩ := init_sum m n
    have hassoc : assoc (([1], 0) : Port) (sum m n).wires = some (below n (m + n + 3), 0) :=
      assoc_eq_of_unique ((I.princ _).2 rfl) (fun q' hq => (I.princ q').1 hq)
    have e : sum (m + 1) n =
        (sum m n).insert1 [m + n + 4] .succ ([1], 0) (below n (m + n + 3), 0) :=
      push_some [m + n + 4] hassoc
    have hu1 : ([m + n + 4] : Id) ≠ [1] := fun e => by
      injection e with e1
      omega
    have hb1 : below n (m + n + 3) ≠ [1] := by
      rcases below_cases n (m + n + 3) with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] <;> intro e' <;>
        injection e' with e1 <;> omega
    have hbu : below n (m + n + 3) ≠ [m + n + 4] := by
      rcases below_cases n (m + n + 3) with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] <;> intro e' <;>
        injection e' with e1 <;> omega
    have hfresh : ∀ k q, ((([m + n + 4], k), q) : Port × Port) ∉ (sum m n).wires := by
      intro k q hm
      obtain ⟨j, hj, ej⟩ := (good_sum m n).below [m + n + 4] (.inr (.inl ⟨k, q, hm⟩))
      injection ej with e1
      omega
    obtain ⟨F1, F2, F3, F4⟩ := push_princ hu1 hb1 hbu hfresh
    have e2 : m + 1 + n + 3 = m + n + 4 := by omega
    rw [e, e2]
    have hch : Chain n ((sum m n).insert1 [m + n + 4] .succ ([1], 0)
        (below n (m + n + 3), 0)) (m + n + 4) := by
      refine ⟨fun t h1 h2 => ?_, fun t h1 h2 q' => ?_⟩
      · show (if ([m + n + 4] : Id) = [t] then some Arith.succ
          else assoc [t] (sum m n).agents) = _
        by_cases ht : t = m + n + 4
        · rw [ite_pos' (by rw [ht])]
        · rw [ite_neg' (fun e' => ht (by injection e' with e1; omega))]
          exact I.chain.live t h1 (by omega)
      · by_cases ht : t = m + n + 4
        · have e3 : t - 1 = m + n + 3 := by omega
          rw [e3, ht]
          exact F3 q'
        · rw [F4 [t] q' (fun e' => ht (by injection e' with e1))]
          exact I.chain.seg t h1 (by omega) q'
    have hch' : Chain n ((sum m n).insert1 [m + n + 4] .succ ([1], 0)
        (below n (m + n + 3), 0)) (m + 1 + n + 3) := by
      rw [e2]
      exact hch
    refine ⟨⟨?_, fun q => ?_, hch'⟩, fun _ => ⟨⟨_, rfl⟩, F2⟩⟩
    · show (if ([m + n + 4] : Id) = [1] then some Arith.succ
        else assoc [1] (sum m n).agents) = _
      rw [ite_neg' hu1]
      exact I.adder
    · rw [e2, below_pos (t := m + n + 4) (by omega)]
      exact F1 q

/-- **The net for `(m + 1) + n` is ready for the first round.** -/
theorem start_sum (m n : Nat) : Start n (sum (m + 1) n) (m + n + 3) := by
  obtain ⟨I, h⟩ := init_sum (m + 1) n
  obtain ⟨hd, fst⟩ := h (Nat.succ_pos m)
  have e : m + 1 + n + 3 = m + n + 3 + 1 := by omega
  rw [e] at hd fst
  have ch := I.chain
  rw [e] at ch
  refine ⟨hd, by omega, I.adder, fst, ch, fun t _ _ k q hm => ?_⟩
  obtain ⟨j, -, ej⟩ := (good_sum (m + 1) n).below [0, t] (.inr (.inl ⟨k, q, hm⟩))
  injection ej with _ e2
  cases e2

/-- **One thread adds in linear time, for every size.**  On the net for
`(m + 1) + n` the single thread makes its `m + 1` claims on successors in
`16 + 17 * m` actions, and the rest of the run, one more claim and the
last pass, is bounded by the general bound on a net that is one step from
its normal form. -/
theorem solo_work_succ (m n : Nat) (i : Nat) :
    (XMach.init (sum (m + 1) n) 1).work xsys (fun _ => 0) i ≤ 83 * m + 22 * n + 235 := by
  have st := start_sum m n
  have e : m + n + 3 = n + 3 + m := by omega
  rw [e] at st
  obtain ⟨X', w, -⟩ := st.rounds
  have g := good_sum (m + 1) n
  have hX := g.ok.1
  have hnd := sum_nodup (m + 1) n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  have hK : (XMach.init (sum (m + 1) n) 1).trace xsys (fun _ => 0) (16 + 17 * m) =
      (XMach.init X' 1, m + 1) := by
    rw [XMach.init_one, XMach.init_one]
    exact w.trace.1
  -- the memory after the rounds is one step from the normal form
  have run : MRun xsys.sys ((XMach.init (sum (m + 1) n) 1).trace xsys (fun _ => 0)
      (16 + 17 * m)).2 (Mach.init (sum (m + 1) n).toNet)
      ((XMach.init (sum (m + 1) n) 1).trace xsys (fun _ => 0) (16 + 17 * m)).1.toMach := by
    have h := XMach.trace_run xsys (fun _ => 0) (XMach.init (sum (m + 1) n) 1) (16 + 17 * m)
    rw [XMach.init_toMach] at h
    exact h
  rw [hK] at run
  have run' : MRun xsys.sys (m + 1) (Mach.init (sum (m + 1) n).toNet)
      (Mach.init X'.toNet) := by
    have h : MRun xsys.sys (m + 1) (Mach.init (sum (m + 1) n).toNet)
        (XMach.init X' 1).toMach := run
    rw [XMach.init_toMach] at h
    exact h
  have sts : Steps (Step xsys.sys) (m + 1) (sum (m + 1) n).toNet X'.toNet :=
    run'.quiet hX (Mach.init_quiet _)
  obtain ⟨-, rest⟩ := reduction_bounded hX hs hn' sts
  have e1 : m + 1 + 1 - (m + 1) = 1 := by omega
  rw [e1] at rest
  have hX' : X'.toNet.WF xsys.sys.ar := Steps.wf hX sts
  -- no two agents of one name
  have live := XMach.trace_live (xs := xsys) (fun _ => 0)
    (XMach.init_live hX Nat.zero_lt_one)
  have nd : ∀ j, (((XMach.init (sum (m + 1) n) 1).trace xsys (fun _ => 0) j).1.mem.agents.map
      Prod.fst).Nodup := by
    intro j
    induction j with
    | zero => exact hnd
    | succ j ih => exact XMach.step_nodup (live j) ih 0
  have hnd' : (X'.agents.map Prod.fst).Nodup := by
    have h := nd (16 + 17 * m)
    rw [hK] at h
    exact h
  -- the sizes of the memory after the rounds
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd Nat.zero_lt_one xsys_bounded hs hn'
    (fun _ => 0)
  have hA' : X'.agents.length ≤ (sum (m + 1) n).agents.length + 2 * (m + 1 + 1) := by
    have h := (hΦ (16 + 17 * m)).1
    rw [hK] at h
    exact h
  have hW' : X'.wires.length ≤ (sum (m + 1) n).wires.length + 8 * (m + 1 + 1) := by
    have h := XMach.wires_le (xs := xsys) hX Nat.zero_lt_one xsys_bounded hs hn'
      (fun _ => 0) (16 + 17 * m)
    rw [hK] at h
    exact h
  have ha := sum_agents_length_le (m + 1) n
  have hwl := sum_wires_length_le (m + 1) n
  -- the rest of the run
  have tail : ∀ j, (XMach.init X' 1).work xsys (fun _ => 0) j ≤ 66 * m + 22 * n + 219 := by
    intro j
    have h := XMach.work_le hX' hnd' Nat.zero_lt_one xsys_bounded rest hn' (fun _ => 0) j
    have hp : X'.passBound 1 2 8 = 7 * (X'.agents.length + 2 * 1) + (X'.wires.length + 8 * 1) :=
      rfl
    rw [hp] at h
    omega
  -- the work up to the fresh start is the count of the rounds
  have hwK : ∀ j, (XMach.init (sum (m + 1) n) 1).work xsys (fun _ => 0) (16 + 17 * m + j) =
      16 + 17 * m + (XMach.init X' 1).work xsys (fun _ => 0) j := by
    intro j
    rw [XMach.init_one, XMach.init_one]
    exact w.work j
  by_cases hi : i ≤ 16 + 17 * m
  · have h := XMach.work_mono (xs := xsys) (fun _ => 0) (XMach.init (sum (m + 1) n) 1) hi
    have h0 : (XMach.init (sum (m + 1) n) 1).work xsys (fun _ => 0) (16 + 17 * m) =
        16 + 17 * m + (XMach.init X' 1).work xsys (fun _ => 0) 0 := hwK 0
    have t0 := tail 0
    rw [h0] at h
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = 16 + 17 * m + j := ⟨i - (16 + 17 * m), by omega⟩
    have t := tail j
    rw [hwK j]
    omega

/-- **One thread adds `m` and `n` in at most `83 * m + 22 * n + 152`
actions**, for every `m` and `n`.  The runs computed take
`22 * m + 3 * n + 13`. -/
theorem solo_work_le (m n : Nat) (i : Nat) :
    (XMach.init (sum m n) 1).work xsys (fun _ => 0) i ≤ 83 * m + 22 * n + 152 := by
  cases m with
  | zero =>
    have g := good_sum 0 n
    obtain ⟨N', hs, hn', -⟩ := add_correct g.config
    have h := XMach.work_le g.ok.1 (sum_nodup 0 n) Nat.zero_lt_one xsys_bounded hs hn'
      (fun _ => 0) i
    have ha := sum_agents_length_le 0 n
    have hw := sum_wires_length_le 0 n
    have hp : (sum 0 n).passBound (0 + 1) 2 8 =
        7 * ((sum 0 n).agents.length + 2 * (0 + 1)) + ((sum 0 n).wires.length + 8 * (0 + 1)) :=
      rfl
    rw [hp] at h
    omega
  | succ m =>
    have h := solo_work_succ m n i
    omega

/-- **One thread adds, numbered, in a count that is linear but for a
logarithm**, for every `m` and `n`: the linear bound on its work times
the cost of an action. -/
theorem solo_ztime_le (m n : Nat) (i : Nat) :
    (ZMach.init (sum m n) 1).ftime xsys (fun _ => 0) i ≤
      (83 * m + 22 * n + 152) * (15 + 84 * lg (15 * m + 5 * n + 19)) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, -⟩ := Below.sizes g.below g.ok.1.symm
  have hwi := solo_work_le m n i
  have h := ZMach.ftime_le_work (xs := xsys) g.ok.1 (sum_nodup m n) Nat.zero_lt_one
    xsys_bounded hL hs hn' (fun _ => 0) i
  have ha := sum_agents_length_le m n
  have hwl := sum_wires_length_le m n
  have hl := lg_mono (show (sum m n).agents.length + 2 * (m + 1) +
    ((sum m n).wires.length + 8 * (m + 1)) ≤ 15 * m + 5 * n + 19 by omega)
  have hc : 2 + 8 + 5 + 4 * ((max 1 1 + 6) * (3 * lg ((sum m n).agents.length + 2 * (m + 1) +
      ((sum m n).wires.length + 8 * (m + 1))))) ≤ 15 + 84 * lg (15 * m + 5 * n + 19) := by
    rw [Nat.max_self]
    omega
  rw [Nat.mul_comm (83 * m + 22 * n + 152)]
  exact Nat.le_trans h (Nat.mul_le_mul hc hwi)

/-- The same in bits. -/
theorem solo_btime_le (m n : Nat) (i : Nat) :
    (ZMach.init (sum m n) 1).btime xsys (fun _ => 0) i ≤
      3 * ((lg (5 * m + 2 * n + 13 + sumWork m n 1) + 5) *
        ((83 * m + 22 * n + 152) * (15 + 84 * lg (15 * m + 5 * n + 19)))) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, htop⟩ := Below.sizes g.below g.ok.1.symm
  have ha := sum_agents_length_le m n
  have h₁ := Nat.mul_le_mul_left (1 + m + 1) (sum_passBound_le m n)
  have hwork : (1 + (m + 1)) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      sumWork m n 1 := by
    show (1 + m + 1) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      (1 + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)
    omega
  have hpow := lt_pow_lg (5 * m + 2 * n + 13 + sumWork m n 1)
  have hW : (sum m n).top + 3 * (m + 1 + 1) <
      2 ^ lg (5 * m + 2 * n + 13 + sumWork m n 1) := by omega
  have hW' : (sum m n).agents.length + ((1 + (m + 1)) * (sum m n).passBound (m + 1) 2 8 +
      (m + 1) * (2 + 8 + 1)) < 2 ^ lg (5 * m + 2 * n + 13 + sumWork m n 1) := by omega
  have h := ZMach.btime_le_ftime (xs := xsys) g.ok.1 (sum_nodup m n) xsys_span xsys_ports
    (sum_ports m n) Nat.zero_lt_one xsys_bounded hL hs hn' (fun _ => 0) hW hW' i
  refine Nat.le_trans h (Nat.mul_le_mul_left 3
    (Nat.mul_le_mul ?_ (solo_ztime_le m n i)))
  have e1 : lg 2 = 3 := by decide
  rw [Nat.max_self, Nat.one_mul, e1]
  omega

/-- `12 + 12` on one thread, from the bound for every size: at most 1,412
actions that are not rests, 1,207,260 counted and 72,435,600 bits.  The
run takes 313, 10,999 and 28,984. -/
example : ∀ i : Nat,
    (XMach.init (sum 12 12) 1).work xsys (fun _ => 0) i ≤ 1412 ∧
      (ZMach.init (sum 12 12) 1).ftime xsys (fun _ => 0) i ≤ 1207260 ∧
      (ZMach.init (sum 12 12) 1).btime xsys (fun _ => 0) i ≤ 72435600 :=
  fun i => ⟨solo_work_le 12 12 i, solo_ztime_le 12 12 i, solo_btime_le 12 12 i⟩

end Arith

end INet
