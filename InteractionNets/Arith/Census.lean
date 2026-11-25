import InteractionNets.Arith.Late

/-! ### What the memory holds at rest: the count of the agents -/

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

namespace Arith

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

variable {j m n : Nat}

local macro "ports_differ" : tactic =>
  `(tactic| first | (intro e; simp at e; done) | (intro e; simp at e; omega))

local macro "under_wires" : tactic =>
  `(tactic| repeat (first | rw [wires_takeAgent] | rw [wires_putAgent] |
      rw [assoc_wires_putLink (by ports_differ)] | rw [nextSeg_putLink (by ports_differ)]))

local macro "under_agents" : tactic =>
  `(tactic| repeat (first | rw [agents_putLink] | rw [assoc_takeAgent_ne (by ports_differ)] |
      rw [assoc_putAgent_ne (by ports_differ)]))

theorem tagged_cons0 : ∀ a : Id, tagged 1 (0 :: a) = tagged 1 a
  | [] => rfl
  | _ :: _ => rfl

theorem tagb_az {t : Bool} {a b : Id} (ta : tagged 1 a = t) :
    (∀ e, e ∈ addZero.toX.newAgents a b → tagged 1 e.1 = t) ∧
      (∀ e, e ∈ addZero.toX.newLinks ar a b .add .zero →
        tagged 1 e.1.1 = t ∧ tagged 1 e.2.1 = t) := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_zero] at he
    cases he
  · rw [newLinks_zero] at he
    exact ids_zero (Q := fun i => tagged 1 i = t) ta he

theorem tagb_za {t : Bool} {a b : Id} (tb : tagged 1 b = t) :
    (∀ e, e ∈ addZero.swap.toX.newAgents a b → tagged 1 e.1 = t) ∧
      (∀ e, e ∈ addZero.swap.toX.newLinks ar a b .zero .add →
        tagged 1 e.1.1 = t ∧ tagged 1 e.2.1 = t) := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_zero_swap] at he
    cases he
  · rw [newLinks_zero_swap] at he
    exact ids_zero (Q := fun i => tagged 1 i = t) tb he

theorem tagb_as {t : Bool} {a b : Id} (ta : tagged 1 a = t) (tb : tagged 1 b = t)
    (hne : a ≠ b) :
    (∀ e, e ∈ addSucc.toX.newAgents a b → tagged 1 e.1 = t) ∧
      (∀ e, e ∈ addSucc.toX.newLinks ar a b .add .succ →
        tagged 1 e.1.1 = t ∧ tagged 1 e.2.1 = t) := by
  have t0a : tagged 1 (0 :: a) = t := (tagged_cons0 a).trans ta
  have t0b : tagged 1 (0 :: b) = t := (tagged_cons0 b).trans tb
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_add hne] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact t0a
    rcases List.mem_cons.1 he with rfl | he
    · exact t0b
    · cases he
  · rw [newLinks_add] at he
    exact ids_add (Q := fun i => tagged 1 i = t) ta tb t0a t0b he

theorem tagb_sa {t : Bool} {a b : Id} (ta : tagged 1 a = t) (tb : tagged 1 b = t)
    (hne : a ≠ b) :
    (∀ e, e ∈ addSucc.swap.toX.newAgents a b → tagged 1 e.1 = t) ∧
      (∀ e, e ∈ addSucc.swap.toX.newLinks ar a b .succ .add →
        tagged 1 e.1.1 = t ∧ tagged 1 e.2.1 = t) := by
  have t0a : tagged 1 (0 :: a) = t := (tagged_cons0 a).trans ta
  have t0b : tagged 1 (0 :: b) = t := (tagged_cons0 b).trans tb
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_swap (a := b) (s := a) (fun e => hne e.symm)] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact t0b
    rcases List.mem_cons.1 he with rfl | he
    · exact t0a
    · cases he
  · rw [newLinks_swap] at he
    exact ids_swap (Q := fun i => tagged 1 i = t) tb ta t0b t0a he

/-- **A rule writes in the net of its pair.** -/
theorem rule_tagb {α β : Arith} {R : XRhs Arith} {a b : Id} (hR : xsys.rule α β = some R)
    (hne : a ≠ b) {t : Bool} (ta : tagged 1 a = t) (tb : tagged 1 b = t) :
    (∀ e, e ∈ R.newAgents a b → tagged 1 e.1 = t) ∧
      (∀ e, e ∈ R.newLinks xsys.sys.ar a b α β →
        tagged 1 e.1.1 = t ∧ tagged 1 e.2.1 = t) := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       exact tagb_az ta)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       exact tagb_za tb)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       exact tagb_as ta tb hne)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       exact tagb_sa ta tb hne)

/-- **A thread that keeps to one net**: the port it has come to is in the
net of the agent it started from, a pair it has found or holds is in one
net, and what it has to write is in one net. -/
def StT : TState Arith → Prop
  | .idle => True
  | .look _ _ => True
  | .seek a _ _ c => tagged 1 c.1 = tagged 1 a
  | .ready a b _ _ => tagged 1 b = tagged 1 a
  | .half a b _ _ => tagged 1 b = tagged 1 a
  | .write as ls => ∃ t : Bool, (∀ e, e ∈ as → tagged 1 e.1 = t) ∧
      ∀ e, e ∈ ls → tagged 1 e.1.1 = t ∧ tagged 1 e.2.1 = t

/-- No segment of the memory joins the two nets. -/
def MemT (X : XNet Arith) : Prop := ∀ e, e ∈ X.wires → tagged 1 e.1.1 = tagged 1 e.2.1

/-- **Every action keeps the two nets apart.** -/
theorem act_tag {X : XNet Arith} {T : XThread Arith} (hM : MemT X) (hT : StT T.st) :
    MemT (XMach.act xsys X T).1 ∧ StT (XMach.act xsys X T).2.1.st := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨hM, trivial⟩
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        exact ⟨hM, trivial⟩
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        exact ⟨hM, trivial⟩
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      exact ⟨hM, trivial⟩
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      exact ⟨hM, (hM _ (assoc_mem hq)).symm⟩
  | seek a α p q =>
    have hT' : tagged 1 q.1 = tagged 1 a := hT
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        exact ⟨hM, trivial⟩
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        exact ⟨hM, (hM _ (nextSeg_spec hn).1).symm.trans hT'⟩
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        exact ⟨hM, hT'⟩
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        exact ⟨hM, trivial⟩
  | ready a b α β =>
    have hT' : tagged 1 b = tagged 1 a := hT
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact ⟨hM, hT'⟩
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact ⟨hM, trivial⟩
  | half a b α β =>
    have hT' : tagged 1 b = tagged 1 a := hT
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact ⟨hM, trivial⟩
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact ⟨hM, tagged 1 a, rule_tagb hR hc.2 rfl hT'⟩
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      exact ⟨hM, trivial⟩
  | write as ls =>
    have hT' : ∃ t : Bool, (∀ e, e ∈ as → tagged 1 e.1 = t) ∧
        ∀ e, e ∈ ls → tagged 1 e.1.1 = t ∧ tagged 1 e.2.1 = t := hT
    obtain ⟨t, hA, hL⟩ := hT'
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨hM, t, fun e he => hA e (List.mem_cons_of_mem _ he), hL⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        refine ⟨fun e he => ?_, t, hA, fun e he => hL e (List.mem_cons_of_mem _ he)⟩
        rcases List.mem_cons.1 he with rfl | he'
        · show tagged 1 p.1 = tagged 1 q.1
          rw [(hL (p, q) List.mem_cons_self).1, (hL (p, q) List.mem_cons_self).2]
        · exact hM e he'
      | nil => exact ⟨hM, trivial⟩

/-- A machine whose two nets are apart. -/
def MachT (M : XMach Arith) : Prop := MemT M.mem ∧ ∀ T, T ∈ M.ths → StT T.st

theorem step_tag {M : XMach Arith} (h : MachT M) (t : Nat) : MachT (M.step xsys t).1 := by
  cases ht : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [ht]
    rw [es]
    exact h
  | some T0 =>
    have es := XMach.step_eq (M := M) (t := t) ht (act_self M.mem T0)
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T0).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T0).1 := by rw [es]
    have hi := act_tag h.1 (h.2 T0 (List.mem_of_getElem? ht))
    refine ⟨?_, fun T hT => ?_⟩
    · rw [e3]
      exact hi.1
    · rw [e2] at hT
      rcases List.mem_or_eq_of_mem_set hT with h1 | h1
      · exact h.2 T h1
      · rw [h1]
        exact hi.2

/-- **The two nets stay apart in every run.** -/
theorem trace_tag (σ : Nat → Nat) {M : XMach Arith} (h : MachT M) :
    ∀ i, MachT (M.trace xsys σ i).1
  | 0 => h
  | i + 1 => step_tag (trace_tag σ h i) (σ i)

theorem init_tag {X : XNet Arith} (h : MemT X) (nt : Nat) : MachT (XMach.init X nt) := by
  refine ⟨h, fun T hT => ?_⟩
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
  exact trivial

/-- The successors of the second net in a list of agents. -/
def succs1 : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => (if tagged 1 e.1 = true then isSucc e.2 else 0) + succs1 l

theorem succs1_append : ∀ (l₁ l₂ : List (Id × Arith)),
    succs1 (l₁ ++ l₂) = succs1 l₁ + succs1 l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show (if tagged 1 e.1 = true then isSucc e.2 else 0) + succs1 (l₁ ++ l₂) =
      (if tagged 1 e.1 = true then isSucc e.2 else 0) + succs1 l₁ + succs1 l₂
    rw [succs1_append l₁ l₂, Nat.add_assoc]

/-- In a list of one net, they are all its successors or none. -/
theorem succs1_const {t : Bool} : ∀ {l : List (Id × Arith)}, (∀ e, e ∈ l → tagged 1 e.1 = t) →
    succs1 l = if t = true then succs l else 0
  | [], _ => by
    show 0 = if t = true then 0 else 0
    split <;> rfl
  | e :: l, h => by
    have ih := succs1_const (l := l) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    show (if tagged 1 e.1 = true then isSucc e.2 else 0) + succs1 l =
      if t = true then isSucc e.2 + succs l else 0
    rw [ih, he]
    cases t <;> rfl

/-- Taking an agent out of a memory that holds none twice takes it off
the count exactly if it is a successor of the second net. -/
theorem succs1_take {a : Id} {α : Arith} : ∀ {l : List (Id × Arith)},
    (l.map Prod.fst).Nodup → assoc a l = some α →
      succs1 (l.filter fun e => decide (e.1 ≠ a)) +
        (if tagged 1 a = true then isSucc α else 0) = succs1 l
  | [], _, h => by cases h
  | (i, γ) :: l, hnd, h => by
    have hnd' : i ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    by_cases hi : i = a
    · have e : γ = α := by
        have h' : (if i = a then some γ else assoc a l) = some α := h
        rw [ite_pos' hi] at h'
        exact Option.some.inj h'
      have hf : l.filter (fun e => decide (e.1 ≠ a)) = l := by
        refine List.filter_eq_self.2 fun e he => ?_
        show decide (e.1 ≠ a) = true
        refine decide_eq_true fun hea => hnd'.1 ?_
        rw [hi, ← hea]
        exact List.mem_map_of_mem (f := Prod.fst) he
      rw [List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show ¬ decide (i ≠ a) = true
          exact fun hd => of_decide_eq_true hd hi), hf]
      show succs1 l + (if tagged 1 a = true then isSucc α else 0) =
        (if tagged 1 i = true then isSucc γ else 0) + succs1 l
      rw [e, hi]
      omega
    · have h' : (if i = a then some γ else assoc a l) = some α := h
      rw [ite_neg' hi] at h'
      have ih := succs1_take (l := l) hnd'.2 h'
      rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show decide (i ≠ a) = true
          exact decide_eq_true hi)]
      show (if tagged 1 i = true then isSucc γ else 0) +
          succs1 (l.filter fun e => decide (e.1 ≠ a)) +
          (if tagged 1 a = true then isSucc α else 0) =
        (if tagged 1 i = true then isSucc γ else 0) + succs1 l
      omega

/-- The successors of the second net a thread holds. -/
def held1 : TState Arith → Nat
  | .half a _ α _ => if tagged 1 a = true then isSucc α else 0
  | .write as _ => succs1 as
  | _ => 0

/-- **No action moves a successor from one net to the other.** -/
theorem act_succs1 (X : XNet Arith) (T : XThread Arith) (hnd : (X.agents.map Prod.fst).Nodup)
    (hT : StT T.st) :
    succs1 (XMach.act xsys X T).1.agents + held1 (XMach.act xsys X T).2.1.st =
      succs1 X.agents + held1 T.st := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact rfl
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        all_goals rfl
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        all_goals rfl
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      all_goals rfl
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      all_goals rfl
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        all_goals rfl
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        all_goals rfl
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        all_goals rfl
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        all_goals rfl
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      have ht : succs1 (X.takeAgent a).agents + (if tagged 1 a = true then isSucc α else 0) =
          succs1 X.agents := succs1_take hnd ha
      show succs1 (X.takeAgent a).agents + (if tagged 1 a = true then isSucc α else 0) =
        succs1 X.agents + 0
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      all_goals rfl
  | half a b α β =>
    have hT' : tagged 1 b = tagged 1 a := hT
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show (if tagged 1 a = true then isSucc α else 0) + succs1 X.agents + 0 =
          succs1 X.agents + (if tagged 1 a = true then isSucc α else 0)
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have ht : succs1 (X.takeAgent b).agents + (if tagged 1 b = true then isSucc β else 0) =
            succs1 X.agents := succs1_take hnd hc.1
        have hr := (rule_succs hR hc.2).1
        have hn := succs1_const (rule_tagb hR hc.2 (t := tagged 1 a) rfl hT').1
        show succs1 (X.takeAgent b).agents + succs1 (R.newAgents a b) =
          succs1 X.agents + (if tagged 1 a = true then isSucc α else 0)
        rw [hn, hr]
        rw [hT'] at ht
        cases htag : tagged 1 a
        · rw [htag] at ht
          show succs1 (X.takeAgent b).agents + 0 = succs1 X.agents + 0
          have ht' : succs1 (X.takeAgent b).agents + 0 = succs1 X.agents := ht
          omega
        · rw [htag] at ht
          show succs1 (X.takeAgent b).agents + (isSucc α + isSucc β) =
            succs1 X.agents + isSucc α
          have ht' : succs1 (X.takeAgent b).agents + isSucc β = succs1 X.agents := ht
          omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show (if tagged 1 a = true then isSucc α else 0) + succs1 X.agents + 0 =
        succs1 X.agents + (if tagged 1 a = true then isSucc α else 0)
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show (if tagged 1 i = true then isSucc γ else 0) + succs1 X.agents + succs1 as =
        succs1 X.agents + ((if tagged 1 i = true then isSucc γ else 0) + succs1 as)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact rfl
      | nil => exact rfl

/-- The successors of the second net a thread holds. -/
def held1T (T : XThread Arith) : Nat := held1 T.st

theorem step_succs1 {M : XMach Arith} (hnd : (M.mem.agents.map Prod.fst).Nodup) (hT : MachT M)
    (t : Nat) :
    succs1 (M.step xsys t).1.mem.agents + total held1T (M.step xsys t).1.ths =
      succs1 M.mem.agents + total held1T M.ths := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    rw [es]
  | some T =>
    have es := XMach.step_eq (M := M) (t := t) h (act_self M.mem T)
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T).1 := by rw [es]
    rw [e2, e3]
    have sh := total_set held1T M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_succs1 M.mem T hnd (hT.2 T (List.mem_of_getElem? h))
    have h1 : held1T T = held1 T.st := rfl
    have h2 : held1T (XMach.act xsys M.mem T).2.1 = held1 (XMach.act xsys M.mem T).2.1.st := rfl
    omega

/-- **Each net keeps its successors**: at every action of every run, the
successors of the second net in memory or held are those it had at the
start. -/
theorem trace_succs1 {X : XNet Arith} (hX : X.toNet.WF ar) (hnd : (X.agents.map Prod.fst).Nodup)
    (hT : MemT X) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) : ∀ i,
    succs1 ((XMach.init X nt).trace xsys σ i).1.mem.agents +
        total held1T ((XMach.init X nt).trace xsys σ i).1.ths = succs1 X.agents
  | 0 => by
    have z := total_init held1T (fun _ => rfl) X nt
    show succs1 X.agents + total held1T (XMach.init X nt).ths = succs1 X.agents
    rw [z]
    rfl
  | i + 1 =>
    (step_succs1 (XMach.init_nodup (xs := xsys) hX hnd hnt σ i)
      (trace_tag σ (init_tag hT nt) i) (σ i)).trans (trace_succs1 hX hnd hT hnt σ i)

/-- The zero of a first argument. -/
def isZF : Id → Bool
  | [j, _] => decide (j = 2)
  | _ => false

/-- Those in a list of agents. -/
def zcnt : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => (if isZF e.1 = true then 1 else 0) + zcnt l

theorem zcnt_append : ∀ (l₁ l₂ : List (Id × Arith)), zcnt (l₁ ++ l₂) = zcnt l₁ + zcnt l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show (if isZF e.1 = true then 1 else 0) + zcnt (l₁ ++ l₂) =
      (if isZF e.1 = true then 1 else 0) + zcnt l₁ + zcnt l₂
    rw [zcnt_append l₁ l₂, Nat.add_assoc]

theorem zcnt_le_fcnt (N : Nat → Nat) : ∀ l : List (Id × Arith), zcnt l ≤ fcnt N l
  | [] => Nat.le_refl 0
  | e :: l => by
    have ih := zcnt_le_fcnt N l
    have h1 : (if isZF e.1 = true then 1 else 0) ≤ (if isF N e.1 = true then 1 else 0) := by
      by_cases hz : isZF e.1 = true
      · have hf : isF N e.1 = true := by
          obtain ⟨i, γ⟩ := e
          match i, hz with
          | [j, c], hz =>
            have hj : j = 2 := of_decide_eq_true hz
            exact decide_eq_true (.inl hj)
        rw [ite_pos' hz, ite_pos' hf]
        exact Nat.le_refl 1
      · rw [ite_neg' hz]
        exact Nat.zero_le _
    show (if isZF e.1 = true then 1 else 0) + zcnt l ≤
      (if isF N e.1 = true then 1 else 0) + fcnt N l
    omega

/-- Taking an agent out of a memory that holds none twice takes it off
both counts exactly. -/
theorem zcnt_take {a : Id} {α : Arith} : ∀ {l : List (Id × Arith)},
    (l.map Prod.fst).Nodup → assoc a l = some α →
      zcnt (l.filter fun e => decide (e.1 ≠ a)) + (if isZF a = true then 1 else 0) = zcnt l ∧
        adders (l.filter fun e => decide (e.1 ≠ a)) + isAdd α = adders l
  | [], _, h => by cases h
  | (i, γ) :: l, hnd, h => by
    have hnd' : i ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    by_cases hi : i = a
    · have e : γ = α := by
        have h' : (if i = a then some γ else assoc a l) = some α := h
        rw [ite_pos' hi] at h'
        exact Option.some.inj h'
      have hf : l.filter (fun e => decide (e.1 ≠ a)) = l := by
        refine List.filter_eq_self.2 fun e he => ?_
        show decide (e.1 ≠ a) = true
        refine decide_eq_true fun hea => hnd'.1 ?_
        rw [hi, ← hea]
        exact List.mem_map_of_mem (f := Prod.fst) he
      rw [List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show ¬ decide (i ≠ a) = true
          exact fun hd => of_decide_eq_true hd hi), hf]
      refine ⟨?_, ?_⟩
      · show zcnt l + (if isZF a = true then 1 else 0) =
          (if isZF i = true then 1 else 0) + zcnt l
        rw [hi]
        omega
      · show adders l + isAdd α = isAdd γ + adders l
        rw [e]
        omega
    · have h' : (if i = a then some γ else assoc a l) = some α := h
      rw [ite_neg' hi] at h'
      obtain ⟨ih1, ih2⟩ := zcnt_take (l := l) hnd'.2 h'
      rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show decide (i ≠ a) = true
          exact decide_eq_true hi)]
      refine ⟨?_, ?_⟩
      · show (if isZF i = true then 1 else 0) + zcnt (l.filter fun e => decide (e.1 ≠ a)) +
            (if isZF a = true then 1 else 0) = (if isZF i = true then 1 else 0) + zcnt l
        omega
      · show isAdd γ + adders (l.filter fun e => decide (e.1 ≠ a)) + isAdd α =
          isAdd γ + adders l
        omega

theorem adder_z {a : Id} (hka : KindOk a .add) : isZF a = false ∧ isZF (0 :: a) = false := by
  rcases kind_add hka with ⟨c, rfl⟩ | ⟨t, c, rfl, -⟩
  · exact ⟨decide_eq_false (by omega), rfl⟩
  · exact ⟨rfl, rfl⟩

theorem succ_z (N : Nat → Nat) {s : Id} (hks : KindOk s .succ) (hx : XP N (s, 0)) :
    isZF s = false ∧ isZF (0 :: s) = false := by
  obtain ⟨j, c, rfl, hj⟩ := succ_x N hks hx
  exact ⟨decide_eq_false (by omega), rfl⟩

theorem zero_z (N : Nat → Nat) {z : Id} (hkz : KindOk z .zero) (hx : XP N (z, 0)) :
    isZF z = true := by
  obtain ⟨c, rfl⟩ := zero_x N hkz hx
  exact decide_eq_true rfl

/-- **A rule ends an adder exactly when it takes the zero of a first
argument.** -/
theorem rule_zero (N : Nat → Nat) {α β : Arith} {R : XRhs Arith} {a b : Id}
    (hka : KindOk a α) (hkb : KindOk b β) (hxa : XP N (a, 0)) (hxb : XP N (b, 0))
    (hR : xsys.rule α β = some R) (hne : a ≠ b) :
    adders (R.newAgents a b) +
        ((if isZF a = true then 1 else 0) + (if isZF b = true then 1 else 0)) =
      zcnt (R.newAgents a b) + (isAdd α + isAdd β) := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_zero, (adder_z hka).1, zero_z N hkb hxb]
       rfl)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_zero_swap, (adder_z hkb).1, zero_z N hka hxa]
       rfl)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       obtain ⟨a1, a2⟩ := adder_z hka
       obtain ⟨s1, s2⟩ := succ_z N hkb hxb
       rw [newAgents_add hne, a1, s1]
       show isAdd Arith.succ + (isAdd Arith.add + 0) + (0 + 0) =
         (if isZF (0 :: a) = true then 1 else 0) +
           ((if isZF (0 :: b) = true then 1 else 0) + 0) + (isAdd Arith.add + isAdd Arith.succ)
       rw [a2, s2]
       rfl)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       obtain ⟨a1, a2⟩ := adder_z hkb
       obtain ⟨s1, s2⟩ := succ_z N hka hxa
       rw [newAgents_swap (a := b) (s := a) (fun e => hne e.symm), a1, s1]
       show isAdd Arith.succ + (isAdd Arith.add + 0) + (0 + 0) =
         (if isZF (0 :: b) = true then 1 else 0) +
           ((if isZF (0 :: a) = true then 1 else 0) + 0) + (isAdd Arith.succ + isAdd Arith.add)
       rw [a2, s2]
       rfl)

/-- The zeros of first arguments a thread holds. -/
def heldZ : TState Arith → Nat
  | .half a _ _ _ => if isZF a = true then 1 else 0
  | .write as _ => zcnt as
  | _ => 0

/-- **Adders and zeros of first arguments go together.**  In a memory in
order with no agent twice, no action changes the difference between the
adders and the zeros of first arguments, in memory or held. -/
theorem act_zf {N : Nat → Nat} {K : Nat} {X : XNet Arith} {T : XThread Arith}
    (hM : MemOk N K X) (hT : ThOk N T) (hnd : (X.agents.map Prod.fst).Nodup) :
    adders (XMach.act xsys X T).1.agents + heldAdd (XMach.act xsys X T).2.1.st +
        (zcnt X.agents + heldZ T.st) =
      zcnt (XMach.act xsys X T).1.agents + heldZ (XMach.act xsys X T).2.1.st +
        (adders X.agents + heldAdd T.st) := by
  have _ := hM.count
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show adders X.agents + 0 + (zcnt X.agents + 0) = zcnt X.agents + 0 + (adders X.agents + 0)
      omega
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show adders X.agents + 0 + (zcnt X.agents + 0) = zcnt X.agents + 0 + (adders X.agents + 0)
      omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show adders X.agents + 0 + (zcnt X.agents + 0) = zcnt X.agents + 0 + (adders X.agents + 0)
      omega
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      obtain ⟨t1, t2⟩ := zcnt_take hnd ha
      have t1' : zcnt (X.takeAgent a).agents + (if isZF a = true then 1 else 0) =
          zcnt X.agents := t1
      have t2' : adders (X.takeAgent a).agents + isAdd α = adders X.agents := t2
      show adders (X.takeAgent a).agents + isAdd α + (zcnt X.agents + 0) =
        zcnt (X.takeAgent a).agents + (if isZF a = true then 1 else 0) + (adders X.agents + 0)
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show adders X.agents + 0 + (zcnt X.agents + 0) = zcnt X.agents + 0 + (adders X.agents + 0)
      omega
  | half a b α β =>
    have hs : KindOk a α ∧ KindOk b β ∧ XP N (a, 0) ∧ XP N (b, 0) := hT.2
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show isAdd α + adders X.agents + 0 +
            (zcnt X.agents + (if isZF a = true then 1 else 0)) =
          (if isZF a = true then 1 else 0) + zcnt X.agents + 0 + (adders X.agents + isAdd α)
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        obtain ⟨t1, t2⟩ := zcnt_take hnd hc.1
        have t1' : zcnt (X.takeAgent b).agents + (if isZF b = true then 1 else 0) =
            zcnt X.agents := t1
        have t2' : adders (X.takeAgent b).agents + isAdd β = adders X.agents := t2
        have hr := rule_zero N hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hR hc.2
        show adders (X.takeAgent b).agents + adders (R.newAgents a b) +
            (zcnt X.agents + (if isZF a = true then 1 else 0)) =
          zcnt (X.takeAgent b).agents + zcnt (R.newAgents a b) + (adders X.agents + isAdd α)
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show isAdd α + adders X.agents + 0 +
          (zcnt X.agents + (if isZF a = true then 1 else 0)) =
        (if isZF a = true then 1 else 0) + zcnt X.agents + 0 + (adders X.agents + isAdd α)
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show isAdd γ + adders X.agents + adders as +
          (zcnt X.agents + ((if isZF i = true then 1 else 0) + zcnt as)) =
        (if isZF i = true then 1 else 0) + zcnt X.agents + zcnt as +
          (adders X.agents + (isAdd γ + adders as))
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega
      | nil =>
        show adders X.agents + 0 + (zcnt X.agents + 0) =
          zcnt X.agents + 0 + (adders X.agents + 0)
        omega

/-- The zeros of first arguments a thread holds. -/
def heldZT (T : XThread Arith) : Nat := heldZ T.st

theorem step_zf {N : Nat → Nat} {K : Nat} {M : XMach Arith} (hO : MachOk N K M)
    (hnd : (M.mem.agents.map Prod.fst).Nodup) (t : Nat) :
    adders (M.step xsys t).1.mem.agents + total heldAddT (M.step xsys t).1.ths +
        (zcnt M.mem.agents + total heldZT M.ths) =
      zcnt (M.step xsys t).1.mem.agents + total heldZT (M.step xsys t).1.ths +
        (adders M.mem.agents + total heldAddT M.ths) := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    rw [es]
    show adders M.mem.agents + total heldAddT M.ths + (zcnt M.mem.agents + total heldZT M.ths) =
      zcnt M.mem.agents + total heldZT M.ths + (adders M.mem.agents + total heldAddT M.ths)
    omega
  | some T =>
    have es := XMach.step_eq (M := M) (t := t) h (act_self M.mem T)
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T).1 := by rw [es]
    rw [e2, e3]
    have sa := total_set heldAddT M.ths t T (XMach.act xsys M.mem T).2.1 h
    have sz := total_set heldZT M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_zf hO.1 (hO.2 T (List.mem_of_getElem? h)) hnd
    have h1 : heldAddT T = heldAdd T.st := rfl
    have h2 : heldAddT (XMach.act xsys M.mem T).2.1 =
        heldAdd (XMach.act xsys M.mem T).2.1.st := rfl
    have h3 : heldZT T = heldZ T.st := rfl
    have h4 : heldZT (XMach.act xsys M.mem T).2.1 = heldZ (XMach.act xsys M.mem T).2.1.st := rfl
    omega

/-- **In every run the adders are as many more than the zeros of first
arguments as at the start**, in memory or held. -/
theorem trace_zf {N : Nat → Nat} {K : Nat} {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) (hO : MemOk N K X) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) : ∀ i,
    adders ((XMach.init X nt).trace xsys σ i).1.mem.agents +
        total heldAddT ((XMach.init X nt).trace xsys σ i).1.ths + zcnt X.agents =
      zcnt ((XMach.init X nt).trace xsys σ i).1.mem.agents +
        total heldZT ((XMach.init X nt).trace xsys σ i).1.ths + adders X.agents
  | 0 => by
    have z1 := total_init heldAddT (fun _ => rfl) X nt
    have z2 := total_init heldZT (fun _ => rfl) X nt
    show adders X.agents + total heldAddT (XMach.init X nt).ths + zcnt X.agents =
      zcnt X.agents + total heldZT (XMach.init X nt).ths + adders X.agents
    omega
  | i + 1 => by
    have ih := trace_zf hX hnd hO hnt σ i
    have hs := step_zf (trace_ok σ (init_ok hO nt) i)
      (XMach.init_nodup (xs := xsys) hX hnd hnt σ i) (σ i)
    show adders (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.mem.agents +
        total heldAddT (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
        zcnt X.agents =
      zcnt (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.mem.agents +
        total heldZT (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
        adders X.agents
    omega

def isZero (α : Arith) : Nat := if α = Arith.zero then 1 else 0

/-- The agents of one kind, counted by `f`, in the nets picked by `s`:
`s` is asked whether the agent is in the second net. -/
def wIn (s : Bool → Bool) (f : Arith → Nat) : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => (if s (tagged 1 e.1) = true then f e.2 else 0) + wIn s f l

theorem wIn_append (s : Bool → Bool) (f : Arith → Nat) : ∀ (l₁ l₂ : List (Id × Arith)),
    wIn s f (l₁ ++ l₂) = wIn s f l₁ + wIn s f l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show (if s (tagged 1 e.1) = true then f e.2 else 0) + wIn s f (l₁ ++ l₂) =
      (if s (tagged 1 e.1) = true then f e.2 else 0) + wIn s f l₁ + wIn s f l₂
    rw [wIn_append s f l₁ l₂, Nat.add_assoc]

/-- In a list of one net, they are all of that kind or none. -/
theorem wIn_const (s : Bool → Bool) (f : Arith → Nat) {t : Bool} :
    ∀ {l : List (Id × Arith)}, (∀ e, e ∈ l → tagged 1 e.1 = t) →
      wIn s f l = if s t = true then wIn (fun _ => true) f l else 0
  | [], _ => by
    show 0 = if s t = true then 0 else 0
    split <;> rfl
  | e :: l, h => by
    have ih := wIn_const s f (l := l) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    show (if s (tagged 1 e.1) = true then f e.2 else 0) + wIn s f l =
      if s t = true then f e.2 + wIn (fun _ => true) f l else 0
    rw [ih, he]
    by_cases hs : s t = true
    · rw [ite_pos' hs, ite_pos' hs, ite_pos' hs]
    · rw [ite_neg' hs, ite_neg' hs, ite_neg' hs]

theorem wIn_le (s : Bool → Bool) (f : Arith → Nat) : ∀ l : List (Id × Arith),
    wIn s f l ≤ wIn (fun _ => true) f l
  | [] => Nat.le_refl 0
  | e :: l => by
    have ih := wIn_le s f l
    show (if s (tagged 1 e.1) = true then f e.2 else 0) + wIn s f l ≤
      f e.2 + wIn (fun _ => true) f l
    by_cases hs : s (tagged 1 e.1) = true
    · rw [ite_pos' hs]
      omega
    · rw [ite_neg' hs]
      omega

theorem wIn_tag (f : Arith → Nat) (c : Nat) : ∀ l : List (Id × Arith),
    wIn (fun _ => true) f (l.map (tagA c)) = wIn (fun _ => true) f l
  | [] => rfl
  | e :: l => by
    show f e.2 + wIn (fun _ => true) f (l.map (tagA c)) = f e.2 + wIn (fun _ => true) f l
    rw [wIn_tag f c l]

theorem wIn_adders : ∀ l : List (Id × Arith), wIn (fun _ => true) isAdd l = adders l
  | [] => rfl
  | e :: l => by
    show isAdd e.2 + wIn (fun _ => true) isAdd l = isAdd e.2 + adders l
    rw [wIn_adders l]

theorem wIn_succs : ∀ l : List (Id × Arith), wIn (fun _ => true) isSucc l = succs l
  | [] => rfl
  | e :: l => by
    show isSucc e.2 + wIn (fun _ => true) isSucc l = isSucc e.2 + succs l
    rw [wIn_succs l]

/-- **Every agent is an adder, a successor or a zero.** -/
theorem length_census : ∀ l : List (Id × Arith),
    l.length = adders l + succs l + wIn (fun _ => true) isZero l
  | [] => rfl
  | (i, γ) :: l => by
    have ih := length_census l
    have h : isAdd γ + isSucc γ + isZero γ = 1 := by cases γ <;> rfl
    show l.length + 1 = isAdd γ + adders l + (isSucc γ + succs l) +
      (isZero γ + wIn (fun _ => true) isZero l)
    omega

/-- Taking an agent out of a memory that holds none twice takes it off
the count exactly. -/
theorem wIn_take (s : Bool → Bool) (f : Arith → Nat) {a : Id} {α : Arith} :
    ∀ {l : List (Id × Arith)}, (l.map Prod.fst).Nodup → assoc a l = some α →
      wIn s f (l.filter fun e => decide (e.1 ≠ a)) +
        (if s (tagged 1 a) = true then f α else 0) = wIn s f l
  | [], _, h => by cases h
  | (i, γ) :: l, hnd, h => by
    have hnd' : i ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    by_cases hi : i = a
    · have e : γ = α := by
        have h' : (if i = a then some γ else assoc a l) = some α := h
        rw [ite_pos' hi] at h'
        exact Option.some.inj h'
      have hf : l.filter (fun e => decide (e.1 ≠ a)) = l := by
        refine List.filter_eq_self.2 fun e he => ?_
        show decide (e.1 ≠ a) = true
        refine decide_eq_true fun hea => hnd'.1 ?_
        rw [hi, ← hea]
        exact List.mem_map_of_mem (f := Prod.fst) he
      rw [List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show ¬ decide (i ≠ a) = true
          exact fun hd => of_decide_eq_true hd hi), hf]
      show wIn s f l + (if s (tagged 1 a) = true then f α else 0) =
        (if s (tagged 1 i) = true then f γ else 0) + wIn s f l
      rw [e, hi]
      omega
    · have h' : (if i = a then some γ else assoc a l) = some α := h
      rw [ite_neg' hi] at h'
      have ih := wIn_take s f (l := l) hnd'.2 h'
      rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show decide (i ≠ a) = true
          exact decide_eq_true hi)]
      show (if s (tagged 1 i) = true then f γ else 0) +
          wIn s f (l.filter fun e => decide (e.1 ≠ a)) +
          (if s (tagged 1 a) = true then f α else 0) =
        (if s (tagged 1 i) = true then f γ else 0) + wIn s f l
      omega

/-- **A rule that ends an adder ends a zero.**  Among the agents a rule
makes there are as many more zeros than adders as in its pair. -/
theorem rule_census {α β : Arith} {R : XRhs Arith} {a b : Id} (hR : xsys.rule α β = some R)
    (hne : a ≠ b) :
    wIn (fun _ => true) isZero (R.newAgents a b) + (isAdd α + isAdd β) =
      wIn (fun _ => true) isAdd (R.newAgents a b) + (isZero α + isZero β) := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_zero]
       rfl)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_zero_swap]
       rfl)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_add hne]
       rfl)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_swap (a := b) (s := a) (fun e => hne e.symm)]
       rfl)

/-- What a thread holds of that count. -/
def heldW (s : Bool → Bool) (f : Arith → Nat) : TState Arith → Nat
  | .half a _ α _ => if s (tagged 1 a) = true then f α else 0
  | .write as _ => wIn s f as
  | _ => 0

/-- **Zeros and adders go together, in each net.**  In a memory with no
agent twice, an action of a thread that keeps to one net does not change
the difference between the zeros and the adders of the nets picked, in
memory or held. -/
theorem act_census (s : Bool → Bool) {X : XNet Arith} {T : XThread Arith}
    (hnd : (X.agents.map Prod.fst).Nodup) (hT : StT T.st) :
    wIn s isZero (XMach.act xsys X T).1.agents + heldW s isZero (XMach.act xsys X T).2.1.st +
        (wIn s isAdd X.agents + heldW s isAdd T.st) =
      wIn s isAdd (XMach.act xsys X T).1.agents + heldW s isAdd (XMach.act xsys X T).2.1.st +
        (wIn s isZero X.agents + heldW s isZero T.st) := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
        wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
      omega
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
        wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
      omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
        wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
      omega
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      have t1 : wIn s isZero (X.takeAgent a).agents +
          (if s (tagged 1 a) = true then isZero α else 0) = wIn s isZero X.agents :=
        wIn_take s isZero hnd ha
      have t2 : wIn s isAdd (X.takeAgent a).agents +
          (if s (tagged 1 a) = true then isAdd α else 0) = wIn s isAdd X.agents :=
        wIn_take s isAdd hnd ha
      show wIn s isZero (X.takeAgent a).agents +
          (if s (tagged 1 a) = true then isZero α else 0) + (wIn s isAdd X.agents + 0) =
        wIn s isAdd (X.takeAgent a).agents + (if s (tagged 1 a) = true then isAdd α else 0) +
          (wIn s isZero X.agents + 0)
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
        wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
      omega
  | half a b α β =>
    have hT' : tagged 1 b = tagged 1 a := hT
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show (if s (tagged 1 a) = true then isZero α else 0) + wIn s isZero X.agents + 0 +
            (wIn s isAdd X.agents + (if s (tagged 1 a) = true then isAdd α else 0)) =
          (if s (tagged 1 a) = true then isAdd α else 0) + wIn s isAdd X.agents + 0 +
            (wIn s isZero X.agents + (if s (tagged 1 a) = true then isZero α else 0))
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have t1 : wIn s isZero (X.takeAgent b).agents +
            (if s (tagged 1 b) = true then isZero β else 0) = wIn s isZero X.agents :=
          wIn_take s isZero hnd hc.1
        have t2 : wIn s isAdd (X.takeAgent b).agents +
            (if s (tagged 1 b) = true then isAdd β else 0) = wIn s isAdd X.agents :=
          wIn_take s isAdd hnd hc.1
        rw [hT'] at t1 t2
        have hn1 := wIn_const s isZero (rule_tagb hR hc.2 (t := tagged 1 a) rfl hT').1
        have hn2 := wIn_const s isAdd (rule_tagb hR hc.2 (t := tagged 1 a) rfl hT').1
        have hr := rule_census hR hc.2
        show wIn s isZero (X.takeAgent b).agents + wIn s isZero (R.newAgents a b) +
            (wIn s isAdd X.agents + (if s (tagged 1 a) = true then isAdd α else 0)) =
          wIn s isAdd (X.takeAgent b).agents + wIn s isAdd (R.newAgents a b) +
            (wIn s isZero X.agents + (if s (tagged 1 a) = true then isZero α else 0))
        rw [hn1, hn2]
        by_cases hs : s (tagged 1 a) = true
        · rw [ite_pos' hs] at t1 t2
          rw [ite_pos' hs, ite_pos' hs, ite_pos' hs, ite_pos' hs]
          omega
        · rw [ite_neg' hs] at t1 t2
          rw [ite_neg' hs, ite_neg' hs, ite_neg' hs, ite_neg' hs]
          omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show (if s (tagged 1 a) = true then isZero α else 0) + wIn s isZero X.agents + 0 +
          (wIn s isAdd X.agents + (if s (tagged 1 a) = true then isAdd α else 0)) =
        (if s (tagged 1 a) = true then isAdd α else 0) + wIn s isAdd X.agents + 0 +
          (wIn s isZero X.agents + (if s (tagged 1 a) = true then isZero α else 0))
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show (if s (tagged 1 i) = true then isZero γ else 0) + wIn s isZero X.agents +
          wIn s isZero as +
          (wIn s isAdd X.agents + ((if s (tagged 1 i) = true then isAdd γ else 0) +
            wIn s isAdd as)) =
        (if s (tagged 1 i) = true then isAdd γ else 0) + wIn s isAdd X.agents + wIn s isAdd as +
          (wIn s isZero X.agents + ((if s (tagged 1 i) = true then isZero γ else 0) +
            wIn s isZero as))
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega
      | nil =>
        show wIn s isZero X.agents + 0 + (wIn s isAdd X.agents + 0) =
          wIn s isAdd X.agents + 0 + (wIn s isZero X.agents + 0)
        omega

/-- What a thread holds of that count. -/
def heldWT (s : Bool → Bool) (f : Arith → Nat) (T : XThread Arith) : Nat := heldW s f T.st

theorem step_census (s : Bool → Bool) {M : XMach Arith}
    (hnd : (M.mem.agents.map Prod.fst).Nodup) (hT : MachT M) (t : Nat) :
    wIn s isZero (M.step xsys t).1.mem.agents + total (heldWT s isZero) (M.step xsys t).1.ths +
        (wIn s isAdd M.mem.agents + total (heldWT s isAdd) M.ths) =
      wIn s isAdd (M.step xsys t).1.mem.agents + total (heldWT s isAdd) (M.step xsys t).1.ths +
        (wIn s isZero M.mem.agents + total (heldWT s isZero) M.ths) := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    rw [es]
    show wIn s isZero M.mem.agents + total (heldWT s isZero) M.ths +
        (wIn s isAdd M.mem.agents + total (heldWT s isAdd) M.ths) =
      wIn s isAdd M.mem.agents + total (heldWT s isAdd) M.ths +
        (wIn s isZero M.mem.agents + total (heldWT s isZero) M.ths)
    omega
  | some T =>
    have es := XMach.step_eq (M := M) (t := t) h (act_self M.mem T)
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T).1 := by rw [es]
    rw [e2, e3]
    have sa := total_set (heldWT s isAdd) M.ths t T (XMach.act xsys M.mem T).2.1 h
    have sz := total_set (heldWT s isZero) M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_census s hnd (hT.2 T (List.mem_of_getElem? h))
    have h1 : heldWT s isAdd T = heldW s isAdd T.st := rfl
    have h2 : heldWT s isAdd (XMach.act xsys M.mem T).2.1 =
        heldW s isAdd (XMach.act xsys M.mem T).2.1.st := rfl
    have h3 : heldWT s isZero T = heldW s isZero T.st := rfl
    have h4 : heldWT s isZero (XMach.act xsys M.mem T).2.1 =
        heldW s isZero (XMach.act xsys M.mem T).2.1.st := rfl
    omega

/-- **In every run, each net keeps as many more zeros than adders as at
the start**, in memory or held. -/
theorem trace_census (s : Bool → Bool) {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) (hT : MemT X) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) : ∀ i,
    wIn s isZero ((XMach.init X nt).trace xsys σ i).1.mem.agents +
        total (heldWT s isZero) ((XMach.init X nt).trace xsys σ i).1.ths + wIn s isAdd X.agents =
      wIn s isAdd ((XMach.init X nt).trace xsys σ i).1.mem.agents +
        total (heldWT s isAdd) ((XMach.init X nt).trace xsys σ i).1.ths + wIn s isZero X.agents
  | 0 => by
    have z1 := total_init (heldWT s isAdd) (fun _ => rfl) X nt
    have z2 := total_init (heldWT s isZero) (fun _ => rfl) X nt
    show wIn s isZero X.agents + total (heldWT s isZero) (XMach.init X nt).ths +
        wIn s isAdd X.agents =
      wIn s isAdd X.agents + total (heldWT s isAdd) (XMach.init X nt).ths + wIn s isZero X.agents
    omega
  | i + 1 => by
    have ih := trace_census s hX hnd hT hnt σ i
    have hs := step_census s (XMach.init_nodup (xs := xsys) hX hnd hnt σ i)
      (trace_tag σ (init_tag hT nt) i) (σ i)
    show wIn s isZero (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.mem.agents +
        total (heldWT s isZero) (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
        wIn s isAdd X.agents =
      wIn s isAdd (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.mem.agents +
        total (heldWT s isAdd) (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
        wIn s isZero X.agents
    omega

/-- The zeros in a list of agents. -/
def zeros (l : List (Id × Arith)) : Nat := wIn (fun _ => true) isZero l

/-- Those of the second net. -/
def zeros1 (l : List (Id × Arith)) : Nat := wIn (fun b => b) isZero l

/-- Two additions side by side start with no segment between them. -/
theorem two_sums_memT (m n m' n' : Nat) : MemT (twoSums m n m' n') := fun e he => by
  have he' : e ∈ (sum m n).wires.map (tagL 0) ++ (sum m' n').wires.map (tagL 1) := he
  rcases List.mem_append.1 he' with h | h
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
    show tagged 1 (x.1.1 ++ [0]) = tagged 1 (x.2.1 ++ [0])
    rw [tagged_append, tagged_append]
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
    show tagged 1 (x.1.1 ++ [1]) = tagged 1 (x.2.1 ++ [1])
    rw [tagged_append, tagged_append]

/-- **Two additions never meet**: with any number of threads and any
schedule, no segment of the memory ever joins a cell of one to a cell of
the other. -/
theorem two_sums_apart (m n m' n' nt : Nat) (σ : Nat → Nat) (i : Nat) :
    ∀ e, e ∈ ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.wires →
      tagged 1 e.1.1 = tagged 1 e.2.1 :=
  (trace_tag σ (init_tag (two_sums_memT m n m' n') nt) i).1

theorem succs1_tag0 (l : List (Id × Arith)) : succs1 (l.map (tagA 0)) = 0 :=
  (succs1_const (t := false) fun _ he => mem_tag_other (by decide) he).trans rfl

theorem succs1_tag1 (l : List (Id × Arith)) : succs1 (l.map (tagA 1)) = succs l :=
  ((succs1_const (t := true) fun _ he => mem_tag_self he).trans rfl).trans (succs_tag 1 l)

theorem succs1_two_sums (m n m' n' : Nat) : succs1 (twoSums m n m' n').agents = m' + n' := by
  show succs1 ((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1)) = m' + n'
  rw [succs1_append, succs1_tag0, succs1_tag1, succs_sum, Nat.zero_add]

theorem base_zcnt (c : Nat) : zcnt (base.agents.map (tagA c)) = 1 := by
  have h1 : isZF [1, c] = false := decide_eq_false (by omega)
  have h2 : isZF [2, c] = true := decide_eq_true rfl
  have h3 : isZF [3, c] = false := decide_eq_false (by omega)
  show (if isZF [1, c] = true then 1 else 0) + ((if isZF [2, c] = true then 1 else 0) +
    ((if isZF [3, c] = true then 1 else 0) + 0)) = 1
  rw [h1, h2, h3]
  rfl

theorem sum_zcnt_ge (M n c : Nat) : 1 ≤ zcnt ((sum M n).agents.map (tagA c)) := by
  rw [sum_agents, List.map_append, List.map_append, zcnt_append, zcnt_append, base_zcnt]
  omega

theorem zcnt_two_sums_ge (m n m' n' : Nat) : 2 ≤ zcnt (twoSums m n m' n').agents := by
  show 2 ≤ zcnt ((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1))
  rw [zcnt_append]
  have a := sum_zcnt_ge m n 0
  have b := sum_zcnt_ge m' n' 1
  omega

theorem zeros_chainL (n : Nat) : ∀ r, wIn (fun _ => true) isZero (chainL n r) = 0
  | 0 => rfl
  | r + 1 => by
    show isZero Arith.succ + wIn (fun _ => true) isZero (chainL n r) = 0
    rw [zeros_chainL n r]
    rfl

theorem zeros_sndL : ∀ n, wIn (fun _ => true) isZero (sndL n) = 0
  | 0 => rfl
  | n + 1 => by
    show isZero Arith.succ + wIn (fun _ => true) isZero (sndL n) = 0
    rw [zeros_sndL n]
    rfl

/-- An addition starts with two zeros. -/
theorem zeros_sum (m n : Nat) : wIn (fun _ => true) isZero (sum m n).agents = 2 := by
  rw [sum_agents, wIn_append, wIn_append, zeros_chainL, zeros_sndL]
  rfl

theorem zeros_two_sums (m n m' n' : Nat) :
    wIn (fun _ => true) isZero (twoSums m n m' n').agents = 4 := by
  show wIn (fun _ => true) isZero
    ((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1)) = 4
  rw [wIn_append, wIn_tag, wIn_tag, zeros_sum, zeros_sum]

theorem wIn1_tag0 (f : Arith → Nat) (l : List (Id × Arith)) :
    wIn (fun b => b) f (l.map (tagA 0)) = 0 :=
  (wIn_const (fun b => b) f (t := false) fun _ he => mem_tag_other (by decide) he).trans rfl

theorem wIn1_tag1 (f : Arith → Nat) (l : List (Id × Arith)) :
    wIn (fun b => b) f (l.map (tagA 1)) = wIn (fun _ => true) f l :=
  ((wIn_const (fun b => b) f (t := true) fun _ he => mem_tag_self he).trans rfl).trans
    (wIn_tag f 1 l)

theorem zeros1_two_sums (m n m' n' : Nat) :
    wIn (fun b => b) isZero (twoSums m n m' n').agents = 2 := by
  show wIn (fun b => b) isZero
    ((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1)) = 2
  rw [wIn_append, wIn1_tag0, wIn1_tag1, zeros_sum]

theorem adders1_two_sums (m n m' n' : Nat) :
    wIn (fun b => b) isAdd (twoSums m n m' n').agents = 1 := by
  show wIn (fun b => b) isAdd
    ((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1)) = 1
  rw [wIn_append, wIn1_tag0, wIn1_tag1, wIn_adders, adders_sum]

/-- **Each addition keeps its own successors**, with any number of
threads and any schedule: at every action, the successors of the second
addition in memory or held are `m' + n'`, and those of both `m + n` more. -/
theorem two_sums_succs_each (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (i : Nat) :
    succs1 ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents +
        total held1T ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.ths = m' + n' ∧
      succs ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents +
        total held ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.ths =
          m + n + (m' + n') := by
  have S := trace_succs1 (two_sums_wf m n m' n') (two_sums_nodup m n m' n')
    (two_sums_memT m n m' n') hnt σ i
  obtain ⟨-, R, -⟩ := trace_read (two_sums_wf m n m' n') (two_sums_nodup m n m' n') hnt σ i
  rw [succs1_two_sums] at S
  rw [succs_two_sums] at R
  exact ⟨S, R⟩

/-- **At rest every cell of a first argument has been used**, with any
number of threads and any schedule. -/
theorem two_sums_rest_first (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    fcnt (sideN n n')
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents = 0 := by
  have F := trace_first σ (init_ok (two_sums_memOk m n m' n') nt) i
  have z := total_init (heldFT (sideN n n')) (fun _ => rfl) (twoSums (m + 1) n (m' + 1) n') nt
  have e0 : (XMach.init (twoSums (m + 1) n (m' + 1) n') nt).mem =
      twoSums (m + 1) n (m' + 1) n' := rfl
  rw [z, e0, two_sums_claims m n m' n' hnt σ hr] at F
  have f : fcnt (sideN n n') (twoSums (m + 1) n (m' + 1) n').agents ≤ m + m' + 4 := by
    show fcnt (sideN n n') ((sum (m + 1) n).agents.map (tagA 0) ++
      (sum (m' + 1) n').agents.map (tagA 1)) ≤ m + m' + 4
    rw [fcnt_append]
    have a := sum_fcnt_le (sideN n n') 0 n rfl (m + 1)
    have b := sum_fcnt_le (sideN n n') 1 n' rfl (m' + 1)
    omega
  omega

/-- **At rest no adder is left**, with any number of threads and any
schedule. -/
theorem two_sums_rest_adders (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    adders ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents = 0 := by
  have Z := trace_zf (two_sums_wf (m + 1) n (m' + 1) n') (two_sums_nodup (m + 1) n (m' + 1) n')
    (two_sums_memOk m n m' n') hnt σ i
  have hf := two_sums_rest_first m n m' n' hnt σ hr
  have hz := zcnt_le_fcnt (sideN n n')
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents
  have z1 : total heldAddT
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.ths = 0 :=
    total_rest heldAddT rfl _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z2 : total heldZT
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.ths = 0 :=
    total_rest heldZT rfl _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have a := adders_two_sums (m + 1) n (m' + 1) n'
  have b := zcnt_two_sums_ge (m + 1) n (m' + 1) n'
  omega

/-- **Two additions side by side come out whole, whatever the threads
do.**  With any number of threads and any schedule, a memory at rest
holds no adder; it holds the `m + n` and `m' + n'` successors of the two
results, those of the second addition in the second net; it holds two
zeros, one in each net; and it holds nothing else. -/
theorem two_sums_rest_census (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    adders ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents = 0 ∧
      succs ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents =
        m + 1 + n + (m' + 1 + n') ∧
      succs1 ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents =
        m' + 1 + n' ∧
      zeros ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents = 2 ∧
      zeros1 ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents = 1 ∧
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents.length =
        m + 1 + n + (m' + 1 + n') + 2 := by
  have A := two_sums_rest_adders m n m' n' hnt σ hr
  obtain ⟨S1, S⟩ := two_sums_succs_each (m + 1) n (m' + 1) n' hnt σ i
  have C0 := trace_census (fun _ => true) (two_sums_wf (m + 1) n (m' + 1) n')
    (two_sums_nodup (m + 1) n (m' + 1) n') (two_sums_memT (m + 1) n (m' + 1) n') hnt σ i
  have C1 := trace_census (fun b => b) (two_sums_wf (m + 1) n (m' + 1) n')
    (two_sums_nodup (m + 1) n (m' + 1) n') (two_sums_memT (m + 1) n (m' + 1) n') hnt σ i
  have hrest : ∀ T, T ∈ ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.ths →
      T = ⟨[], .idle⟩ := fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z1 := total_rest (heldWT (fun _ => true) isZero) rfl _ hrest
  have z2 := total_rest (heldWT (fun _ => true) isAdd) rfl _ hrest
  have z3 := total_rest (heldWT (fun b => b) isZero) rfl _ hrest
  have z4 := total_rest (heldWT (fun b => b) isAdd) rfl _ hrest
  have z5 := total_rest held1T rfl _ hrest
  have z6 := total_rest held rfl _ hrest
  have a0 := wIn_adders
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents
  have a1 := wIn_le (fun b => b) isAdd
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents
  have x0 := zeros_two_sums (m + 1) n (m' + 1) n'
  have x1 : wIn (fun _ => true) isAdd (twoSums (m + 1) n (m' + 1) n').agents = 2 :=
    (wIn_adders _).trans (adders_two_sums (m + 1) n (m' + 1) n')
  have x2 := zeros1_two_sums (m + 1) n (m' + 1) n'
  have x3 := adders1_two_sums (m + 1) n (m' + 1) n'
  have L := length_census
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents
  have Z0 : wIn (fun _ => true) isZero
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents = 2 := by
    omega
  have Z1 : wIn (fun b => b) isZero
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents = 1 := by
    omega
  exact ⟨A, by omega, by omega, Z0, Z1, by omega⟩

/-- `6 + 32` twice, with any number of threads and any schedule: a memory
at rest holds the two results, thirty-eight successors each, and two
zeros, seventy-eight agents in all. -/
theorem _root_.INet.Checks.Arith.Census.c1 {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums 6 32 6 32) nt).trace xsys σ i).1.resting = true) :
    succs ((XMach.init (twoSums 6 32 6 32) nt).trace xsys σ i).1.mem.agents = 76 ∧
      succs1 ((XMach.init (twoSums 6 32 6 32) nt).trace xsys σ i).1.mem.agents = 38 ∧
      ((XMach.init (twoSums 6 32 6 32) nt).trace xsys σ i).1.mem.agents.length = 78 := by
  obtain ⟨-, h1, h2, -, -, h3⟩ := two_sums_rest_census 5 32 5 32 hnt σ hr
  exact ⟨h1, h2, h3⟩

end Arith

end INet
