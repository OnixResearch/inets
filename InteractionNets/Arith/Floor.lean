import InteractionNets.Arith.Apart

/-! ### A floor on the rounds, for any number of threads -/

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
      rw [assoc_wires_putLink (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))] | rw [nextSeg_putLink (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))]))

local macro "under_agents" : tactic =>
  `(tactic| repeat (first | rw [agents_putLink] | rw [assoc_takeAgent_ne (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))] |
      rw [assoc_putAgent_ne (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))]))

/-- One for a successor. -/
def isSucc (α : Arith) : Nat := if α = Arith.succ then 1 else 0

theorem isSucc_le (α : Arith) : isSucc α ≤ 1 := by
  cases α <;> decide

/-- The successors in a list of agents. -/
def succs : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => isSucc e.2 + succs l

theorem succs_append : ∀ (l₁ l₂ : List (Id × Arith)), succs (l₁ ++ l₂) = succs l₁ + succs l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show isSucc e.2 + succs (l₁ ++ l₂) = isSucc e.2 + succs l₁ + succs l₂
    rw [succs_append l₁ l₂, Nat.add_assoc]

theorem succs_le_length : ∀ l : List (Id × Arith), succs l ≤ l.length
  | [] => Nat.le_refl 0
  | e :: l => by
    have ih := succs_le_length l
    have h1 := isSucc_le e.2
    show isSucc e.2 + succs l ≤ l.length + 1
    omega

/-- Taking an agent out of a memory that holds none twice takes it off
the count of successors exactly if it is one. -/
theorem succs_take {a : Id} {α : Arith} : ∀ {l : List (Id × Arith)},
    (l.map Prod.fst).Nodup → assoc a l = some α →
      succs (l.filter fun e => decide (e.1 ≠ a)) + isSucc α = succs l
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
      show succs l + isSucc α = isSucc γ + succs l
      rw [e]
      omega
    · have h' : (if i = a then some γ else assoc a l) = some α := h
      rw [ite_neg' hi] at h'
      have ih := succs_take (l := l) hnd'.2 h'
      rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show decide (i ≠ a) = true
          exact decide_eq_true hi)]
      show isSucc γ + succs (l.filter fun e => decide (e.1 ≠ a)) + isSucc α =
        isSucc γ + succs l
      omega

/-- **A rule of the addition keeps the successors**: it writes as many as
it takes, and never more than one. -/
theorem rule_succs {α β : Arith} {R : XRhs Arith} (hR : xsys.rule α β = some R) {a b : Id}
    (hne : a ≠ b) :
    succs (R.newAgents a b) = isSucc α + isSucc β ∧ succs (R.newAgents a b) ≤ 1 := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       exact ⟨rfl, Nat.zero_le 1⟩)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       exact ⟨rfl, Nat.zero_le 1⟩)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_add hne]
       exact ⟨rfl, Nat.le_refl 1⟩)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_swap (fun e => hne e.symm)]
       exact ⟨rfl, Nat.le_refl 1⟩)

/-- The actions a thread has made toward a claim after reading the agent:
one when it follows its wire, two when it has found the partner, three
when it has taken the first agent. -/
def credit2 : TState Arith → Nat
  | .idle => 0
  | .look _ _ => 0
  | .seek _ _ _ _ => 1
  | .ready _ _ _ _ => 2
  | .half _ _ _ _ => 3
  | .write _ _ => 0

/-- The successors a thread holds: the one it has taken, those it has to
write. -/
def heldSucc : TState Arith → Nat
  | .half _ _ α _ => isSucc α
  | .write as _ => succs as
  | _ => 0

/-- What a thread has still to read of its list, counted up to `B`. -/
def toRead (B : Nat) (T : XThread Arith) : Nat := min T.todo.length B

/-- **No action loses a successor**: those in memory and those the thread
holds stay as many. -/
theorem act_succs (X : XNet Arith) (T : XThread Arith) (hnd : (X.agents.map Prod.fst).Nodup) :
    succs (XMach.act xsys X T).1.agents + heldSucc (XMach.act xsys X T).2.1.st =
      succs X.agents + heldSucc T.st := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => rfl
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
      have ht : succs (X.takeAgent a).agents + isSucc α = succs X.agents := succs_take hnd ha
      show succs (X.takeAgent a).agents + isSucc α = succs X.agents + 0
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      all_goals rfl
  | half a b α β =>
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show isSucc α + succs X.agents + 0 = succs X.agents + isSucc α
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have ht : succs (X.takeAgent b).agents + isSucc β = succs X.agents :=
          succs_take hnd hc.1
        have hr := (rule_succs hR hc.2).1
        show succs (X.takeAgent b).agents + succs (R.newAgents a b) =
          succs X.agents + isSucc α
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show isSucc α + succs X.agents + 0 = succs X.agents + isSucc α
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show isSucc γ + succs X.agents + succs as = succs X.agents + (isSucc γ + succs as)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        rfl
      | nil => rfl

/-- **A thread never holds more than one successor.** -/
theorem act_held (X : XNet Arith) (T : XThread Arith) (h : heldSucc T.st ≤ 1) :
    heldSucc (XMach.act xsys X T).2.1.st ≤ 1 := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact Nat.zero_le 1
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        exact Nat.zero_le 1
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        exact Nat.zero_le 1
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      exact Nat.zero_le 1
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      exact Nat.zero_le 1
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        exact Nat.zero_le 1
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        exact Nat.zero_le 1
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        exact Nat.zero_le 1
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        exact Nat.zero_le 1
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact isSucc_le α
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact Nat.zero_le 1
  | half a b α β =>
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact Nat.zero_le 1
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact (rule_succs hR hc.2).2
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      exact Nat.zero_le 1
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have h' : isSucc γ + succs as ≤ 1 := h
      show succs as ≤ 1
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact Nat.zero_le 1
      | nil => exact Nat.zero_le 1

/-- **The price of one action, with the reading.**  Count fifteen for a
claim, the actions a thread has made toward a claim after reading the
agent, eight for each adder in memory or held, and what the thread has
still to read of its list, up to `B`; against them the action itself, if
it is not a rest, and the actions the thread still owes for its claim.
While the memory holds `B` agents or more, no action makes the first grow
more than the second: an action that takes an entry off the list is not
counted toward a claim, and a thread that reloads its list has `B`
entries to read again. -/
theorem act_cost2 (B : Nat) (X : XNet Arith) (T : XThread Arith) (hB : B ≤ X.agents.length) :
    15 * (XMach.act xsys X T).2.2 + credit2 (XMach.act xsys X T).2.1.st +
        8 * (adders (XMach.act xsys X T).1.agents + heldAdd (XMach.act xsys X T).2.1.st) +
        owed T.st + toRead B T ≤
      XThread.busy T + owed (XMach.act xsys X T).2.1.st + credit2 T.st +
        8 * (adders X.agents + heldAdd T.st) + toRead B (XMach.act xsys X T).2.1 := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min 0 B ≤
        0 + 0 + 0 + 8 * (adders X.agents + 0) + min 0 B
      omega
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min (rest.length + 1) B ≤
          1 + 0 + 0 + 8 * (adders X.agents + 0) + min rest.length B
        omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min (rest.length + 1) B ≤
          1 + 0 + 0 + 8 * (adders X.agents + 0) + min rest.length B
        omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B ≤
        1 + 0 + 0 + 8 * (adders X.agents + 0) + min todo.length B
      omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show 15 * 0 + 1 + 8 * (adders X.agents + 0) + 0 + min todo.length B ≤
        1 + 0 + 0 + 8 * (adders X.agents + 0) + min todo.length B
      omega
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 15 * 0 + 1 + 8 * (adders X.agents + 0) + 0 + min todo.length B ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show 15 * 0 + 2 + 8 * (adders X.agents + 0) + 0 + min todo.length B ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      have ht : adders (X.takeAgent a).agents + isAdd α ≤ adders X.agents := adders_take ha
      show 15 * 0 + 3 + 8 * (adders (X.takeAgent a).agents + isAdd α) + 0 + min todo.length B ≤
        1 + 0 + 2 + 8 * (adders X.agents + 0) + min todo.length B
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B ≤
        1 + 0 + 2 + 8 * (adders X.agents + 0) + min todo.length B
      omega
  | half a b α β =>
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show 15 * 0 + 0 + 8 * (isAdd α + adders X.agents + 0) + 0 + min todo.length B ≤
          1 + 0 + 3 + 8 * (adders X.agents + isAdd α) + min todo.length B
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have ht : adders (X.takeAgent b).agents + isAdd β ≤ adders X.agents := adders_take hc.1
        have hr := rule_cost hR hc.2
        show 15 * 1 + 0 + 8 * (adders (X.takeAgent b).agents + adders (R.newAgents a b)) + 0 +
            min todo.length B ≤
          1 + ((R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length + 1) + 3 +
            8 * (adders X.agents + isAdd α) + min todo.length B
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show 15 * 0 + 0 + 8 * (isAdd α + adders X.agents + 0) + 0 + min todo.length B ≤
        1 + 0 + 3 + 8 * (adders X.agents + isAdd α) + min todo.length B
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show 15 * 0 + 0 + 8 * (isAdd γ + adders X.agents + adders as) +
          (as.length + 1 + ls.length + 1) + min todo.length B ≤
        1 + (as.length + ls.length + 1) + 0 + 8 * (adders X.agents + (isAdd γ + adders as)) +
          min todo.length B
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + (0 + (ls.length + 1) + 1) +
            min todo.length B ≤
          1 + (0 + ls.length + 1) + 0 + 8 * (adders X.agents + 0) + min todo.length B
        omega
      | nil =>
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + (0 + 0 + 1) + min todo.length B ≤
          1 + 0 + 0 + 8 * (adders X.agents + 0) + min X.agents.length B
        omega

/-- What a thread has put toward a claim after reading the agent, and
eight for each adder it holds. -/
def paid2 (T : XThread Arith) : Nat := credit2 T.st + 8 * heldAdd T.st

/-- The successors a thread holds. -/
def held (T : XThread Arith) : Nat := heldSucc T.st

theorem total_ge_mul {f : XThread Arith → Nat} {P : Nat} :
    ∀ {ths : List (XThread Arith)}, (∀ T, T ∈ ths → P ≤ f T) → ths.length * P ≤ total f ths
  | [], _ => by
    show 0 * P ≤ 0
    omega
  | T :: ths, h => by
    have h1 := h T List.mem_cons_self
    have ih := total_ge_mul (f := f) (P := P) (ths := ths)
      (fun U hU => h U (List.mem_cons_of_mem _ hU))
    show (ths.length + 1) * P ≤ f T + total f ths
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem step_cost2 (B : Nat) (M : XMach Arith) (t : Nat) (hB : B ≤ M.mem.agents.length) :
    15 * (M.step xsys t).2 +
        (total paid2 (M.step xsys t).1.ths + 8 * adders (M.step xsys t).1.mem.agents) +
        total due M.ths + total (toRead B) M.ths ≤
      M.stepTally XThread.busy t + total due (M.step xsys t).1.ths +
        (total paid2 M.ths + 8 * adders M.mem.agents) +
        total (toRead B) (M.step xsys t).1.ths := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    have e4 : M.stepTally XThread.busy t = 0 := by
      unfold XMach.stepTally
      rw [h]
    rw [es, e4]
    show 15 * 0 + (total paid2 M.ths + 8 * adders M.mem.agents) + total due M.ths +
        total (toRead B) M.ths ≤
      0 + total due M.ths + (total paid2 M.ths + 8 * adders M.mem.agents) +
        total (toRead B) M.ths
    omega
  | some T =>
    have es := XMach.step_eq (M := M) (t := t) h (act_self M.mem T)
    have e1 : (M.step xsys t).2 = (XMach.act xsys M.mem T).2.2 := by rw [es]
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T).1 := by rw [es]
    have e4 : M.stepTally XThread.busy t = XThread.busy T := by
      unfold XMach.stepTally
      rw [h]
    rw [e1, e2, e3, e4]
    have sp := total_set paid2 M.ths t T (XMach.act xsys M.mem T).2.1 h
    have sd := total_set due M.ths t T (XMach.act xsys M.mem T).2.1 h
    have sr := total_set (toRead B) M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_cost2 B M.mem T hB
    have p1 : paid2 T = credit2 T.st + 8 * heldAdd T.st := rfl
    have p2 : paid2 (XMach.act xsys M.mem T).2.1 = credit2 (XMach.act xsys M.mem T).2.1.st +
        8 * heldAdd (XMach.act xsys M.mem T).2.1.st := rfl
    have d1 : due T = owed T.st := rfl
    have d2 : due (XMach.act xsys M.mem T).2.1 = owed (XMach.act xsys M.mem T).2.1.st := rfl
    omega

theorem step_succs (M : XMach Arith) (hnd : (M.mem.agents.map Prod.fst).Nodup) (t : Nat) :
    succs (M.step xsys t).1.mem.agents + total held (M.step xsys t).1.ths =
      succs M.mem.agents + total held M.ths := by
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
    have sh := total_set held M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_succs M.mem T hnd
    have h1 : held T = heldSucc T.st := rfl
    have h2 : held (XMach.act xsys M.mem T).2.1 = heldSucc (XMach.act xsys M.mem T).2.1.st :=
      rfl
    omega

theorem step_held (M : XMach Arith) (t : Nat) (hh : ∀ T, T ∈ M.ths → held T ≤ 1) :
    ∀ T, T ∈ (M.step xsys t).1.ths → held T ≤ 1 := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    rw [es]
    exact hh
  | some T0 =>
    have es := XMach.step_eq (M := M) (t := t) h (act_self M.mem T0)
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T0).2.1 := by rw [es]
    rw [e2]
    intro T hT
    rcases List.mem_or_eq_of_mem_set hT with h1 | h1
    · exact hh T h1
    · rw [h1]
      exact act_held M.mem T0 (hh T0 (List.mem_of_getElem? h))

theorem init_length (X : XNet Arith) (nt : Nat) : (XMach.init X nt).ths.length = nt := by
  show ((List.range nt).map _).length = nt
  rw [List.length_map, List.length_range]

/-- **The price of a run, with the reading.**  On a net with no agent
twice, at every action of a run from the start: no thread holds more than
one successor, the successors in memory and held are those of the start,
and fifteen for each claim, what the threads have put toward claims,
eight for each adder, and for each thread as many entries to read as the
net has successors less the number of threads, are never more than the
work done, what the threads still owe, and what they have still to
read. -/
theorem trace_read {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (∀ T, T ∈ ((XMach.init X nt).trace xsys σ i).1.ths → held T ≤ 1) ∧
      succs ((XMach.init X nt).trace xsys σ i).1.mem.agents +
          total held ((XMach.init X nt).trace xsys σ i).1.ths = succs X.agents ∧
      15 * ((XMach.init X nt).trace xsys σ i).2 +
          (total paid2 ((XMach.init X nt).trace xsys σ i).1.ths +
            8 * adders ((XMach.init X nt).trace xsys σ i).1.mem.agents) +
          nt * (succs X.agents - nt) ≤
        (XMach.init X nt).work xsys σ i +
          total due ((XMach.init X nt).trace xsys σ i).1.ths + 8 * adders X.agents +
          total (toRead (succs X.agents - nt)) ((XMach.init X nt).trace xsys σ i).1.ths
  | 0 => by
    have z1 := total_init paid2 (fun _ => rfl) X nt
    have z2 := total_init due (fun _ => rfl) X nt
    have z3 := total_init held (fun _ => rfl) X nt
    have hl := succs_le_length X.agents
    have z4 : (XMach.init X nt).ths.length * (succs X.agents - nt) ≤
        total (toRead (succs X.agents - nt)) (XMach.init X nt).ths :=
      total_ge_mul fun T hT => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
        show succs X.agents - nt ≤
          min (X.agents.drop t ++ X.agents.take t).length (succs X.agents - nt)
        rw [List.length_append, List.length_drop, List.length_take]
        omega
    rw [init_length] at z4
    refine ⟨fun T hT => ?_, ?_, ?_⟩
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      exact Nat.zero_le 1
    · show succs X.agents + total held (XMach.init X nt).ths = succs X.agents
      rw [z3]
      rfl
    · show 15 * 0 + (total paid2 (XMach.init X nt).ths + 8 * adders X.agents) +
          nt * (succs X.agents - nt) ≤
        0 + total due (XMach.init X nt).ths + 8 * adders X.agents +
          total (toRead (succs X.agents - nt)) (XMach.init X nt).ths
      rw [z1, z2]
      omega
  | i + 1 => by
    obtain ⟨ha, hb, hc⟩ := trace_read hX hnd hnt σ i
    have nd := XMach.init_nodup (xs := xsys) hX hnd hnt σ i
    have hlen : ((XMach.init X nt).trace xsys σ i).1.ths.length = nt :=
      (XMach.trace_length xsys σ _ i).trans (init_length X nt)
    have hle := total_le_mul (f := held) (P := 1) ha
    have hsl := succs_le_length ((XMach.init X nt).trace xsys σ i).1.mem.agents
    have hB : succs X.agents - nt ≤
        ((XMach.init X nt).trace xsys σ i).1.mem.agents.length := by
      rw [hlen] at hle
      omega
    have h1 := step_held ((XMach.init X nt).trace xsys σ i).1 (σ i) ha
    have h2 := step_succs ((XMach.init X nt).trace xsys σ i).1 nd (σ i)
    have h3 := step_cost2 (succs X.agents - nt) ((XMach.init X nt).trace xsys σ i).1 (σ i) hB
    refine ⟨h1, h2.trans hb, ?_⟩
    show 15 * (((XMach.init X nt).trace xsys σ i).2 +
          (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).2) +
        (total paid2 (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
          8 * adders (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.mem.agents) +
        nt * (succs X.agents - nt) ≤
      (XMach.init X nt).work xsys σ i +
          ((XMach.init X nt).trace xsys σ i).1.stepTally XThread.busy (σ i) +
        total due (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
        8 * adders X.agents +
        total (toRead (succs X.agents - nt))
          (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths
    omega

/-- **Every interaction costs fifteen actions and every thread reads the
memory.**  On any net of the addition with no agent twice, with any
number of threads and any schedule: when every thread is at rest, fifteen
times the claims made, and for each thread the successors of the net less
the number of threads, are at most the work done and eight for each adder
the net had. -/
theorem rest_read {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init X nt).trace xsys σ i).1.resting = true) :
    15 * ((XMach.init X nt).trace xsys σ i).2 + nt * (succs X.agents - nt) ≤
      (XMach.init X nt).work xsys σ i + 8 * adders X.agents := by
  obtain ⟨-, -, h⟩ := trace_read hX hnd hnt σ i
  have z3 : total due ((XMach.init X nt).trace xsys σ i).1.ths = 0 :=
    total_rest due rfl _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z4 : total (toRead (succs X.agents - nt)) ((XMach.init X nt).trace xsys σ i).1.ths = 0 :=
    total_rest (toRead (succs X.agents - nt)) (Nat.zero_min _) _
      fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  rw [z3, z4] at h
  omega

theorem succs_tag (c : Nat) : ∀ l : List (Id × Arith), succs (l.map (tagA c)) = succs l
  | [] => rfl
  | e :: l => by
    show isSucc e.2 + succs (l.map (tagA c)) = isSucc e.2 + succs l
    rw [succs_tag c l]

theorem succs_chainL (n : Nat) : ∀ r, succs (chainL n r) = r
  | 0 => rfl
  | r + 1 => by
    show isSucc Arith.succ + succs (chainL n r) = r + 1
    rw [succs_chainL n r]
    exact Nat.add_comm 1 r

theorem succs_sndL : ∀ n, succs (sndL n) = n
  | 0 => rfl
  | n + 1 => by
    show isSucc Arith.succ + succs (sndL n) = n + 1
    rw [succs_sndL n]
    exact Nat.add_comm 1 n

/-- An addition has the successors of its two arguments. -/
theorem succs_sum (m n : Nat) : succs (sum m n).agents = m + n := by
  rw [sum_agents, succs_append, succs_append, succs_chainL, succs_sndL]
  rfl

theorem succs_two_sums (m n m' n' : Nat) :
    succs (twoSums m n m' n').agents = m + n + (m' + n') := by
  show succs ((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1)) = _
  rw [succs_append, succs_tag, succs_tag, succs_sum, succs_sum]

theorem nodup_snoc (c : Nat) : ∀ l : List Id, l.Nodup → (l.map (· ++ [c])).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.1 h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_snoc c l h2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    exact h1 (List.append_cancel_right e ▸ hb)

theorem map_fst_tag (c : Nat) : ∀ l : List (Id × Arith),
    (l.map (tagA c)).map Prod.fst = (l.map Prod.fst).map (· ++ [c])
  | [] => rfl
  | e :: l => congrArg (List.cons (e.1 ++ [c])) (map_fst_tag c l)

/-- Two additions side by side have no agent twice. -/
theorem two_sums_nodup (m n m' n' : Nat) :
    ((twoSums m n m' n').agents.map Prod.fst).Nodup := by
  show (((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1)).map Prod.fst).Nodup
  rw [List.map_append, map_fst_tag, map_fst_tag]
  refine List.nodup_append.2 ⟨nodup_snoc 0 _ (sum_nodup m n), nodup_snoc 1 _ (sum_nodup m' n'),
    fun a ha b hb e => ?_⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
  exact absurd (snoc_inj e).2 (by decide)

/-- **Two additions side by side, any number of threads, any schedule**:
a run that ends at rest has done fifteen actions for each of its
`m + m' + 4` interactions, less sixteen, and for each thread as many as
the additions have successors, less the number of threads. -/
theorem two_sums_read_work (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    15 * (m + m') + 44 + nt * (m + n + m' + n' + 2 - nt) ≤
      (XMach.init (twoSums (m + 1) n (m' + 1) n') nt).work xsys σ i := by
  have h := rest_read (two_sums_wf (m + 1) n (m' + 1) n') (two_sums_nodup (m + 1) n (m' + 1) n')
    hnt σ hr
  rw [two_sums_claims m n m' n' hnt σ hr, adders_two_sums, succs_two_sums] at h
  have e : m + 1 + n + (m' + 1 + n') - nt = m + n + m' + n' + 2 - nt := by omega
  rw [e] at h
  omega

/-- **A limit that no number of threads lowers.**  With `c` threads in
turn on two additions side by side, the rounds to rest are at least the
successors of the additions less the number of threads, and more by the
fifteen actions of each interaction shared among the threads. -/
theorem two_sums_rounds_read (m n m' n' : Nat) {c R : Nat} (hc : 0 < c)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    15 * (m + m') + 44 + c * (m + n + m' + n' + 2 - c) ≤ c * R :=
  Nat.le_trans (two_sums_read_work m n m' n' hc (fun i => i % c) h.1)
    (XMach.work_le_count xsys _ _ _)

/-- So the rounds and the threads together are at least the successors of
the two additions, however many threads there are. -/
theorem two_sums_rounds_floor (m n m' n' : Nat) {c R : Nat} (hc : 0 < c)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    m + n + m' + n' + 2 < R + c := by
  have h1 := two_sums_rounds_read m n m' n' hc h
  have h2 : c * (m + n + m' + n' + 2 - c) < c * R := by omega
  have h3 := Nat.lt_of_mul_lt_mul_left h2
  omega

/-- **Two threads in turn on two additions** need at least
`8 * (m + m') + n + n' + 22` rounds, and a half round more for each odd
interaction. -/
theorem two_threads_read_ge (m n m' n' : Nat) {R : Nat}
    (h : Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2) R) :
    17 * (m + m') + 2 * (n + n') + 44 ≤ 2 * R := by
  have h1 := two_sums_rounds_read m n m' n' (Nat.succ_pos 1) h
  omega

/-- One addition: fifteen for each of its `m + 2` interactions, less
eight, and the reading. -/
theorem sum_rounds_read (m n : Nat) {c R : Nat} (hc : 0 < c)
    (h : Rounds c (XMach.init (sum (m + 1) n) c) R) :
    15 * m + 22 + c * (m + n + 1 - c) ≤ c * R := by
  have hr := h.1
  have h1 := rest_read (sum_ok (m + 1) n).1 (sum_nodup (m + 1) n) hc (fun i => i % c) hr
  rw [sum_claims m n hc _ hr, adders_sum, succs_sum] at h1
  have h2 := XMach.work_le_count xsys (fun i => i % c) (XMach.init (sum (m + 1) n) c) (c * R)
  have e : m + 1 + n - c = m + n + 1 - c := by omega
  rw [e] at h1
  omega

/-- `6 + 32` twice: two threads take 489 rounds and cannot take fewer
than 171; four threads cannot take fewer than 121, and sixteen not fewer
than 73. -/
example {R : Nat} (h : Rounds 2 (XMach.init (twoSums 6 32 6 32) 2) R) : 171 ≤ R := by
  have h' := two_threads_read_ge 5 32 5 32 h
  omega

example {R : Nat} (h : Rounds 4 (XMach.init (twoSums 6 32 6 32) 4) R) : 121 ≤ R := by
  have h' := two_sums_rounds_read 5 32 5 32 (by decide) h
  omega

example {R : Nat} (h : Rounds 16 (XMach.init (twoSums 6 32 6 32) 16) R) : 73 ≤ R := by
  have h' := two_sums_rounds_read 5 32 5 32 (by decide) h
  omega

/-- The successors of the second argument of the addition tagged `c`,
where `N c` is that argument. -/
def isSnd (N : Nat → Nat) : Id → Bool
  | [j, c] => decide (4 ≤ j ∧ j ≤ N c + 3)
  | _ => false

/-- **The side of the first argument.**  The principal ports of the
adders and of the zero of the first argument, and both ports of the
successors of the first argument.  Every other port is on the side of
the second argument and of the result. -/
def XP (N : Nat → Nat) : Port → Prop
  | ([j, c], k) => (j = 1 ∧ k = 0) ∨ (j = 2 ∧ k = 0) ∨ N c + 4 ≤ j
  | ([0, t, _], k) => t ≠ 1 ∧ k = 0
  | _ => False

theorem xp_base (N : Nat → Nat) (j c k : Nat) :
    XP N ([j, c], k) ↔ ((j = 1 ∧ k = 0) ∨ (j = 2 ∧ k = 0) ∨ N c + 4 ≤ j) := Iff.rfl

theorem xp_gen (N : Nat → Nat) (t c k : Nat) : XP N ([0, t, c], k) ↔ (t ≠ 1 ∧ k = 0) := Iff.rfl

theorem xp_res (N : Nat → Nat) (t c k : Nat) : XP N ([0, 0, t, c], k) ↔ False := Iff.rfl

/-- **The symbol an agent has by its name**: `1` is the first adder and
`0 :: t` a later one, `2` and `3` are the zeros, the other single names
are successors, and so are the names the rule gives the successors of
the result. -/
def KindOk : Id → Arith → Prop
  | [j, _], γ => (j = 1 ∧ γ = .add) ∨ ((j = 2 ∨ j = 3) ∧ γ = .zero) ∨ (4 ≤ j ∧ γ = .succ)
  | [0, t, _], γ => (t = 1 ∧ γ = .succ) ∨ (t ≠ 1 ∧ γ = .add)
  | [0, 0, _, _], γ => γ = .succ
  | _, _ => False

theorem kind_add : ∀ {a : Id}, KindOk a .add →
    (∃ c, a = [1, c]) ∨ (∃ t c, a = [0, t, c] ∧ t ≠ 1)
  | [], h => False.elim h
  | [_], h => False.elim h
  | [j, c], h => by
    have h' : (j = 1 ∧ Arith.add = .add) ∨ ((j = 2 ∨ j = 3) ∧ Arith.add = .zero) ∨
        (4 ≤ j ∧ Arith.add = .succ) := h
    rcases h' with ⟨rfl, -⟩ | ⟨-, e⟩ | ⟨-, e⟩
    · exact .inl ⟨c, rfl⟩
    · cases e
    · cases e
  | [0, t, c], h => by
    have h' : (t = 1 ∧ Arith.add = .succ) ∨ (t ≠ 1 ∧ Arith.add = .add) := h
    rcases h' with ⟨-, e⟩ | ⟨ht, -⟩
    · cases e
    · exact .inr ⟨t, c, rfl, ht⟩
  | [_ + 1, _, _], h => False.elim h
  | [0, 0, _, _], h => by
    have h' : Arith.add = .succ := h
    cases h'
  | [0, _ + 1, _, _], h => False.elim h
  | [_ + 1, 0, _, _], h => False.elim h
  | [_ + 1, _ + 1, _, _], h => False.elim h
  | _ :: _ :: _ :: _ :: _ :: _, h => False.elim h

/-- The principal port of an adder is on the side of the first
argument. -/
theorem add_x (N : Nat → Nat) {a : Id} (h : KindOk a .add) : XP N (a, 0) := by
  rcases kind_add h with ⟨c, rfl⟩ | ⟨t, c, rfl, ht⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact ⟨ht, rfl⟩

/-- A successor with its principal port on that side is one of the first
argument. -/
theorem succ_x (N : Nat → Nat) : ∀ {s : Id}, KindOk s .succ → XP N (s, 0) →
    ∃ j c, s = [j, c] ∧ N c + 4 ≤ j
  | [], h, _ => False.elim h
  | [_], h, _ => False.elim h
  | [j, c], h, hx => by
    have h' : (j = 1 ∧ Arith.succ = .add) ∨ ((j = 2 ∨ j = 3) ∧ Arith.succ = .zero) ∨
        (4 ≤ j ∧ Arith.succ = .succ) := h
    have hx' : (j = 1 ∧ 0 = 0) ∨ (j = 2 ∧ 0 = 0) ∨ N c + 4 ≤ j := hx
    rcases h' with ⟨-, e⟩ | ⟨-, e⟩ | ⟨h4, -⟩
    · cases e
    · cases e
    · exact ⟨j, c, rfl, by omega⟩
  | [0, t, c], h, hx => by
    have h' : (t = 1 ∧ Arith.succ = .succ) ∨ (t ≠ 1 ∧ Arith.succ = .add) := h
    have hx' : t ≠ 1 ∧ 0 = 0 := hx
    rcases h' with ⟨e, -⟩ | ⟨-, e⟩
    · exact absurd e hx'.1
    · cases e
  | [_ + 1, _, _], h, _ => False.elim h
  | [0, 0, _, _], _, hx => False.elim hx
  | [0, _ + 1, _, _], h, _ => False.elim h
  | [_ + 1, 0, _, _], h, _ => False.elim h
  | [_ + 1, _ + 1, _, _], h, _ => False.elim h
  | _ :: _ :: _ :: _ :: _ :: _, h, _ => False.elim h

theorem snd_shape (N : Nat → Nat) : ∀ {s : Id}, isSnd N s = true →
    ∃ j c, s = [j, c] ∧ 4 ≤ j ∧ j ≤ N c + 3
  | [j, c], h => ⟨j, c, rfl, of_decide_eq_true h⟩
  | [], h => by cases h
  | [_], h => by cases h
  | _ :: _ :: _ :: _, h => by cases h

/-- The principal port of a successor of the second argument is not on
the side of the first. -/
theorem snd_not_x (N : Nat → Nat) {s : Id} (h : isSnd N s = true) : ¬ XP N (s, 0) := by
  obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape N h
  intro hx
  have hx' : (j = 1 ∧ 0 = 0) ∨ (j = 2 ∧ 0 = 0) ∨ N c + 4 ≤ j := hx
  omega

theorem x_not_snd (N : Nat → Nat) {a : Id} (h : XP N (a, 0)) : isSnd N a = false := by
  cases hs : isSnd N a with
  | false => rfl
  | true => exact absurd h (snd_not_x N hs)

theorem kind_snd (N : Nat → Nat) {s : Id} {γ : Arith} (h : isSnd N s = true)
    (hk : KindOk s γ) : γ = .succ := by
  obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape N h
  have hk' : (j = 1 ∧ γ = .add) ∨ ((j = 2 ∨ j = 3) ∧ γ = .zero) ∨ (4 ≤ j ∧ γ = .succ) := hk
  rcases hk' with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, e⟩
  · omega
  · omega
  · exact e

/-- A rule fires on an adder. -/
theorem rule_adder {α β : Arith} (h : (xsys.rule α β).isSome = true) : α = .add ∨ β = .add := by
  cases α <;> cases β <;> first
    | exact .inl rfl
    | exact .inr rfl
    | (exfalso
       revert h
       show (none : Option (XRhs Arith)).isSome = true → False
       intro h
       cases h)

/-- The ports of an adder other than its principal port, and those of
the successor a rule names after it, are not on the side of the first
argument. -/
theorem adder_ports (N : Nat → Nat) {a : Id} (hka : KindOk a .add) :
    ¬ XP N (a, 1) ∧ ¬ XP N (a, 2) ∧ ¬ XP N (0 :: a, 0) ∧ ¬ XP N (0 :: a, 1) ∧
      KindOk (0 :: a) .succ ∧ isSnd N (0 :: a) = false := by
  rcases kind_add hka with ⟨c, rfl⟩ | ⟨t, c, rfl, ht⟩
  · refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, .inl ⟨rfl, rfl⟩, rfl⟩
    · have h' : (1 = 1 ∧ 1 = 0) ∨ (1 = 2 ∧ 1 = 0) ∨ N c + 4 ≤ 1 := h
      omega
    · have h' : (1 = 1 ∧ 2 = 0) ∨ (1 = 2 ∧ 2 = 0) ∨ N c + 4 ≤ 1 := h
      omega
    · have h' : (1 : Nat) ≠ 1 ∧ 0 = 0 := h
      exact h'.1 rfl
    · have h' : (1 : Nat) ≠ 1 ∧ 1 = 0 := h
      exact h'.1 rfl
  · refine ⟨fun h => ?_, fun h => ?_, fun h => (h : False), fun h => (h : False), rfl, rfl⟩
    · have h' : t ≠ 1 ∧ 1 = 0 := h
      omega
    · have h' : t ≠ 1 ∧ 2 = 0 := h
      omega

/-- The other port of a successor of the first argument, and the principal
port of the adder a rule names after it, are on the side of the first
argument; the other ports of that adder are not. -/
theorem succ_ports (N : Nat → Nat) {s : Id} (hks : KindOk s .succ) (hx : XP N (s, 0)) :
    XP N (s, 1) ∧ XP N (0 :: s, 0) ∧ ¬ XP N (0 :: s, 1) ∧ ¬ XP N (0 :: s, 2) ∧
      KindOk (0 :: s) .add ∧ isSnd N (0 :: s) = false := by
  obtain ⟨j, c, rfl, hj⟩ := succ_x N hks hx
  refine ⟨.inr (.inr hj), ⟨by omega, rfl⟩, fun h => ?_, fun h => ?_, .inr ⟨by omega, rfl⟩, rfl⟩
  · have h' : j ≠ 1 ∧ 1 = 0 := h
    omega
  · have h' : j ≠ 1 ∧ 2 = 0 := h
    omega

theorem succ_links {P : Port → Prop} {a s : Id} (h1 : ¬ P (a, 1)) (h2 : ¬ P (a, 2))
    (h3 : ¬ P (0 :: a, 0)) (h4 : ¬ P (0 :: a, 1)) (h5 : P (s, 1)) (h6 : P (0 :: s, 0))
    (h7 : ¬ P (0 :: s, 1)) (h8 : ¬ P (0 :: s, 2)) {e : Port × Port}
    (he : e ∈ [((a, 1), (0 :: s, 1)), ((a, 2), (0 :: a, 0)), ((s, 1), (0 :: s, 0)),
      ((0 :: a, 0), (a, 2)), ((0 :: a, 1), (0 :: s, 2)), ((0 :: s, 0), (s, 1)),
      ((0 :: s, 1), (a, 1)), ((0 :: s, 2), (0 :: a, 1))]) : P e.1 ↔ P e.2 := by
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h1 h7
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h2 h3
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_true h5 h6
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h3 h2
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h4 h8
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_true h6 h5
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h7 h1
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h8 h4
  · cases he

theorem swap_links {P : Port → Prop} {a s : Id} (h1 : ¬ P (a, 1)) (h2 : ¬ P (a, 2))
    (h3 : ¬ P (0 :: a, 0)) (h4 : ¬ P (0 :: a, 1)) (h5 : P (s, 1)) (h6 : P (0 :: s, 0))
    (h7 : ¬ P (0 :: s, 1)) (h8 : ¬ P (0 :: s, 2)) {e : Port × Port}
    (he : e ∈ [((s, 1), (0 :: s, 0)), ((a, 1), (0 :: s, 1)), ((a, 2), (0 :: a, 0)),
      ((0 :: a, 0), (a, 2)), ((0 :: a, 1), (0 :: s, 2)), ((0 :: s, 0), (s, 1)),
      ((0 :: s, 1), (a, 1)), ((0 :: s, 2), (0 :: a, 1))]) : P e.1 ↔ P e.2 := by
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_true h5 h6
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h1 h7
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h2 h3
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h3 h2
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h4 h8
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_true h6 h5
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h7 h1
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h8 h4
  · cases he

theorem zero_links {P : Port → Prop} {a : Id} (h1 : ¬ P (a, 1)) (h2 : ¬ P (a, 2))
    {e : Port × Port} (he : e ∈ [((a, 1), (a, 2)), ((a, 2), (a, 1))]) : P e.1 ↔ P e.2 := by
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h1 h2
  rcases List.mem_cons.1 he with rfl | he
  · exact iff_of_false h2 h1
  · cases he

theorem color_az (N : Nat → Nat) {a b : Id} (hka : KindOk a .add) :
    (∀ e, e ∈ addZero.toX.newAgents a b → KindOk e.1 e.2 ∧ isSnd N e.1 = false) ∧
      (∀ e, e ∈ addZero.toX.newLinks ar a b .add .zero → (XP N e.1 ↔ XP N e.2)) := by
  obtain ⟨a1, a2, -, -, -, -⟩ := adder_ports N hka
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_zero] at he
    cases he
  · rw [newLinks_zero] at he
    exact zero_links a1 a2 he

theorem color_za (N : Nat → Nat) {a b : Id} (hkb : KindOk b .add) :
    (∀ e, e ∈ addZero.swap.toX.newAgents a b → KindOk e.1 e.2 ∧ isSnd N e.1 = false) ∧
      (∀ e, e ∈ addZero.swap.toX.newLinks ar a b .zero .add → (XP N e.1 ↔ XP N e.2)) := by
  obtain ⟨a1, a2, -, -, -, -⟩ := adder_ports N hkb
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_zero_swap] at he
    cases he
  · rw [newLinks_zero_swap] at he
    exact zero_links a1 a2 he

theorem color_as (N : Nat → Nat) {a b : Id} (hka : KindOk a .add) (hkb : KindOk b .succ)
    (hxb : XP N (b, 0)) (hne : a ≠ b) :
    (∀ e, e ∈ addSucc.toX.newAgents a b → KindOk e.1 e.2 ∧ isSnd N e.1 = false) ∧
      (∀ e, e ∈ addSucc.toX.newLinks ar a b .add .succ → (XP N e.1 ↔ XP N e.2)) := by
  obtain ⟨a1, a2, a3, a4, ak, as⟩ := adder_ports N hka
  obtain ⟨s1, s2, s3, s4, sk, ss⟩ := succ_ports N hkb hxb
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_add hne] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨ak, as⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨sk, ss⟩
    · cases he
  · rw [newLinks_add] at he
    exact succ_links a1 a2 a3 a4 s1 s2 s3 s4 he

theorem color_sa (N : Nat → Nat) {a b : Id} (hka : KindOk a .succ) (hkb : KindOk b .add)
    (hxa : XP N (a, 0)) (hne : a ≠ b) :
    (∀ e, e ∈ addSucc.swap.toX.newAgents a b → KindOk e.1 e.2 ∧ isSnd N e.1 = false) ∧
      (∀ e, e ∈ addSucc.swap.toX.newLinks ar a b .succ .add → (XP N e.1 ↔ XP N e.2)) := by
  obtain ⟨a1, a2, a3, a4, ak, as⟩ := adder_ports N hkb
  obtain ⟨s1, s2, s3, s4, sk, ss⟩ := succ_ports N hka hxa
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_swap (a := b) (s := a) (fun e => hne e.symm)] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨ak, as⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨sk, ss⟩
    · cases he
  · rw [newLinks_swap] at he
    exact swap_links a1 a2 a3 a4 s1 s2 s3 s4 he

/-- **What a rule writes stays on its side.**  When the two agents of a
pair have the symbols of their names and their principal ports on the
side of the first argument, the agents the rule makes have the symbols
of their names, none is a successor of a second argument, and every
segment it writes joins two ports of the same side. -/
theorem rule_color (N : Nat → Nat) {α β : Arith} {R : XRhs Arith} {a b : Id}
    (hka : KindOk a α) (hkb : KindOk b β) (hxa : XP N (a, 0)) (hxb : XP N (b, 0))
    (hR : xsys.rule α β = some R) (hne : a ≠ b) :
    (∀ e, e ∈ R.newAgents a b → KindOk e.1 e.2 ∧ isSnd N e.1 = false) ∧
      (∀ e, e ∈ R.newLinks xsys.sys.ar a b α β → (XP N e.1 ↔ XP N e.2)) := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       exact color_az N hka)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       exact color_za N hkb)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       exact color_as N hka hkb hxb hne)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       exact color_sa N hka hkb hxa hne)

/-- The successors of second arguments in a list of agents. -/
def sndCnt (N : Nat → Nat) : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => (if isSnd N e.1 = true then 1 else 0) + sndCnt N l

theorem sndCnt_append (N : Nat → Nat) : ∀ (l₁ l₂ : List (Id × Arith)),
    sndCnt N (l₁ ++ l₂) = sndCnt N l₁ + sndCnt N l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show (if isSnd N e.1 = true then 1 else 0) + sndCnt N (l₁ ++ l₂) =
      (if isSnd N e.1 = true then 1 else 0) + sndCnt N l₁ + sndCnt N l₂
    rw [sndCnt_append N l₁ l₂, Nat.add_assoc]

/-- Taking out an agent that is not one of them leaves them all. -/
theorem sndCnt_take (N : Nat → Nat) {a : Id} (ha : isSnd N a = false) :
    ∀ l : List (Id × Arith), sndCnt N (l.filter fun e => decide (e.1 ≠ a)) = sndCnt N l
  | [] => rfl
  | e :: l => by
    have ih := sndCnt_take N ha l
    by_cases hi : e.1 = a
    · rw [List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show ¬ decide (e.1 ≠ a) = true
          exact fun hd => of_decide_eq_true hd hi)]
      have e0 : (if isSnd N e.1 = true then 1 else 0) = 0 := by
        rw [hi, ha]
        rfl
      show sndCnt N (l.filter fun e => decide (e.1 ≠ a)) =
        (if isSnd N e.1 = true then 1 else 0) + sndCnt N l
      rw [e0, ih, Nat.zero_add]
    · rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show decide (e.1 ≠ a) = true
          exact decide_eq_true hi)]
      show (if isSnd N e.1 = true then 1 else 0) +
          sndCnt N (l.filter fun e => decide (e.1 ≠ a)) =
        (if isSnd N e.1 = true then 1 else 0) + sndCnt N l
      rw [ih]

/-- **A memory in order**: every agent has the symbol of its name, every
segment joins two ports of one side, and the successors of the second
arguments are all there, each with a segment at its principal port. -/
structure MemOk (N : Nat → Nat) (K : Nat) (X : XNet Arith) : Prop where
  kinds : ∀ e, e ∈ X.agents → KindOk e.1 e.2
  wires : ∀ e, e ∈ X.wires → (XP N e.1 ↔ XP N e.2)
  alive : ∀ s, isSnd N s = true → assoc s X.agents = some .succ
  look : ∀ s, isSnd N s = true → ∃ q, assoc ((s, 0) : Port) X.wires = some q
  count : K ≤ sndCnt N X.agents

/-- **A state in order**: the agents a thread has read have the symbols
of their names, the port it has come to is on the side it started from,
and a pair it has found or holds has both principal ports on the side of
the first argument. -/
def StOk (N : Nat → Nat) : TState Arith → Prop
  | .idle => True
  | .look a α => KindOk a α
  | .seek a α _ c => KindOk a α ∧ (XP N c ↔ XP N (a, 0))
  | .ready a b α β => KindOk a α ∧ KindOk b β ∧ XP N (a, 0) ∧ XP N (b, 0)
  | .half a b α β => KindOk a α ∧ KindOk b β ∧ XP N (a, 0) ∧ XP N (b, 0)
  | .write as ls => (∀ e, e ∈ as → KindOk e.1 e.2 ∧ isSnd N e.1 = false) ∧
      (∀ e, e ∈ ls → (XP N e.1 ↔ XP N e.2))

/-- A thread in order: its list and its state. -/
def ThOk (N : Nat → Nat) (T : XThread Arith) : Prop :=
  (∀ e, e ∈ T.todo → KindOk e.1 e.2) ∧ StOk N T.st

theorem MemOk.take {N : Nat → Nat} {K : Nat} {X : XNet Arith} (h : MemOk N K X) {a : Id}
    (hx : XP N (a, 0)) : MemOk N K (X.takeAgent a) where
  kinds := fun e he => h.kinds e (List.mem_filter.1 he).1
  wires := h.wires
  alive := fun s hs => by
    have hne : a ≠ s := fun e => snd_not_x N hs (e ▸ hx)
    rw [assoc_takeAgent_ne hne]
    exact h.alive s hs
  look := h.look
  count := by
    show K ≤ sndCnt N (X.agents.filter fun e => decide (e.1 ≠ a))
    rw [sndCnt_take N (x_not_snd N hx)]
    exact h.count

theorem MemOk.put {N : Nat → Nat} {K : Nat} {X : XNet Arith} (h : MemOk N K X) {i : Id}
    {γ : Arith} (hk : KindOk i γ) : MemOk N K (X.putAgent i γ) where
  kinds := fun e he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact hk
    · exact h.kinds e he'
  wires := h.wires
  alive := fun s hs => by
    by_cases hi : i = s
    · have hγ : γ = Arith.succ := kind_snd N hs (by
        rw [← hi]
        exact hk)
      show (if i = s then some γ else assoc s X.agents) = some Arith.succ
      rw [ite_pos' hi, hγ]
    · rw [assoc_putAgent_ne hi]
      exact h.alive s hs
  look := h.look
  count := by
    have hc := h.count
    show K ≤ (if isSnd N i = true then 1 else 0) + sndCnt N X.agents
    omega

theorem MemOk.link {N : Nat → Nat} {K : Nat} {X : XNet Arith} (h : MemOk N K X) {p q : Port}
    (hpq : XP N p ↔ XP N q) : MemOk N K (X.putLink p q) where
  kinds := h.kinds
  wires := fun e he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact hpq
    · exact h.wires e he'
  alive := h.alive
  look := fun s hs => by
    by_cases hp : p = (s, 0)
    · exact ⟨q, by
        show (if p = (s, 0) then some q else assoc ((s, 0) : Port) X.wires) = some q
        rw [ite_pos' hp]⟩
    · obtain ⟨q', hq'⟩ := h.look s hs
      exact ⟨q', by
        show (if p = (s, 0) then some q else assoc ((s, 0) : Port) X.wires) = some q'
        rw [ite_neg' hp, hq']⟩
  count := h.count

/-- **Every action keeps the memory and the thread in order.** -/
theorem act_inv {N : Nat → Nat} {K : Nat} {X : XNet Arith} {T : XThread Arith}
    (hM : MemOk N K X) (hT : ThOk N T) :
    MemOk N K (XMach.act xsys X T).1 ∧ ThOk N (XMach.act xsys X T).2.1 := by
  obtain ⟨todo, st⟩ := T
  obtain ⟨hk, hs⟩ := hT
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨hM, hk, trivial⟩
    | cons e rest =>
      have hk' : ∀ e', e' ∈ rest → KindOk e'.1 e'.2 := fun e' he' =>
        hk e' (List.mem_cons_of_mem _ he')
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        exact ⟨hM, hk', hk e List.mem_cons_self⟩
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        exact ⟨hM, hk', trivial⟩
  | look a α =>
    have hka : KindOk a α := hs
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      exact ⟨hM, hk, trivial⟩
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      exact ⟨hM, hk, hka, (hM.wires _ (assoc_mem hq)).symm⟩
  | seek a α p q =>
    obtain ⟨b, k⟩ := q
    have hs' : KindOk a α ∧ (XP N (b, k) ↔ XP N (a, 0)) := hs
    obtain ⟨hka, hc⟩ := hs'
    cases hc' : (if ((b, k) : Port).2 = 0 then assoc ((b, k) : Port).1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires (b, k) p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc' hn]
        exact ⟨hM, hk, trivial⟩
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc' hn]
        exact ⟨hM, hk, hka, (hM.wires _ (nextSeg_spec hn).1).symm.trans hc⟩
    | some β =>
      by_cases hr : a ≠ ((b, k) : Port).1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc' hr]
        have hk0 : k = 0 := by
          by_cases h0 : k = 0
          · exact h0
          · have hc'' : (if k = 0 then assoc b X.agents else none) = some β := hc'
            rw [ite_neg' h0] at hc''
            cases hc''
        subst hk0
        have hc'' : (if (0 : Nat) = 0 then assoc b X.agents else none) = some β := hc'
        rw [ite_pos' rfl] at hc''
        have hkb : KindOk b β := hM.kinds _ (assoc_mem hc'')
        have hx : XP N (a, 0) ∧ XP N (b, 0) := by
          rcases rule_adder hr.2 with rfl | rfl
          · exact ⟨add_x N hka, hc.2 (add_x N hka)⟩
          · exact ⟨hc.1 (add_x N hkb), add_x N hkb⟩
        exact ⟨hM, hk, hka, hkb, hx.1, hx.2⟩
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc' hr]
        exact ⟨hM, hk, trivial⟩
  | ready a b α β =>
    have hs' : KindOk a α ∧ KindOk b β ∧ XP N (a, 0) ∧ XP N (b, 0) := hs
    obtain ⟨hka, hkb, hxa, hxb⟩ := hs'
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact ⟨hM.take hxa, hk, hka, hkb, hxa, hxb⟩
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact ⟨hM, hk, trivial⟩
  | half a b α β =>
    have hs' : KindOk a α ∧ KindOk b β ∧ XP N (a, 0) ∧ XP N (b, 0) := hs
    obtain ⟨hka, hkb, hxa, hxb⟩ := hs'
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact ⟨hM.put hka, hk, trivial⟩
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact ⟨hM.take hxb, hk, rule_color N hka hkb hxa hxb hR hc.2⟩
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      exact ⟨hM.put hka, hk, trivial⟩
  | write as ls =>
    have hs' : (∀ e, e ∈ as → KindOk e.1 e.2 ∧ isSnd N e.1 = false) ∧
        (∀ e, e ∈ ls → (XP N e.1 ↔ XP N e.2)) := hs
    obtain ⟨hA, hL⟩ := hs'
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨hM.put (hA (i, γ) List.mem_cons_self).1, hk,
        fun e he => hA e (List.mem_cons_of_mem _ he), hL⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨hM.link (hL (p, q) List.mem_cons_self), hk, hA,
          fun e he => hL e (List.mem_cons_of_mem _ he)⟩
      | nil => exact ⟨hM, hM.kinds, trivial⟩

/-- A machine in order: its memory and each of its threads. -/
def MachOk (N : Nat → Nat) (K : Nat) (M : XMach Arith) : Prop :=
  MemOk N K M.mem ∧ ∀ T, T ∈ M.ths → ThOk N T

theorem step_ok {N : Nat → Nat} {K : Nat} {M : XMach Arith} (h : MachOk N K M) (t : Nat) :
    MachOk N K (M.step xsys t).1 := by
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
    have hi := act_inv h.1 (h.2 T0 (List.mem_of_getElem? ht))
    refine ⟨?_, fun T hT => ?_⟩
    · rw [e3]
      exact hi.1
    · rw [e2] at hT
      rcases List.mem_or_eq_of_mem_set hT with h1 | h1
      · exact h.2 T h1
      · rw [h1]
        exact hi.2

/-- **A run from a memory in order stays in order**, whatever the number
of threads and the schedule. -/
theorem trace_ok {N : Nat → Nat} {K : Nat} (σ : Nat → Nat) {M : XMach Arith}
    (h : MachOk N K M) : ∀ i, MachOk N K (M.trace xsys σ i).1
  | 0 => h
  | i + 1 => step_ok (trace_ok σ h i) (σ i)

theorem init_ok {N : Nat → Nat} {K : Nat} {X : XNet Arith} (h : MemOk N K X) (nt : Nat) :
    MachOk N K (XMach.init X nt) := by
  refine ⟨h, fun T hT => ?_⟩
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
  refine ⟨fun e he => h.kinds e ?_, trivial⟩
  rcases List.mem_append.1 he with h1 | h1
  · exact List.mem_of_mem_drop h1
  · exact List.mem_of_mem_take h1

/-- **The successors of the second arguments never leave the memory**,
whatever the number of threads and the schedule. -/
theorem snd_forever {N : Nat → Nat} {K : Nat} {X : XNet Arith} (h : MemOk N K X) (nt : Nat)
    (σ : Nat → Nat) (i : Nat) {s : Id} (hs : isSnd N s = true) :
    assoc s ((XMach.init X nt).trace xsys σ i).1.mem.agents = some .succ :=
  (trace_ok σ (init_ok h nt) i).1.alive s hs

/-- **What a thread owes on a successor of a second argument**: two more
actions when it has read the agent, two when it follows the first segment
of its wire, one while it follows the next. -/
def walk (N : Nat → Nat) : TState Arith → Nat
  | .look a _ => if isSnd N a = true then 2 else 0
  | .seek a _ p _ => if isSnd N a = true then (if p = (a, 0) then 2 else 1) else 0
  | _ => 0

theorem walk_le_two (N : Nat → Nat) : ∀ st : TState Arith, walk N st ≤ 2
  | .idle => Nat.zero_le 2
  | .look a _ => by
    show (if isSnd N a = true then 2 else 0) ≤ 2
    split <;> omega
  | .seek a _ p _ => by
    show (if isSnd N a = true then (if p = (a, 0) then 2 else 1) else 0) ≤ 2
    split
    · split <;> omega
    · omega
  | .ready _ _ _ _ => Nat.zero_le 2
  | .half _ _ _ _ => Nat.zero_le 2
  | .write _ _ => Nat.zero_le 2

theorem walk_look_le (N : Nat → Nat) (a : Id) (α : Arith) (q : Port) :
    walk N (.look a α) ≤ walk N (.seek a α (a, 0) q) := by
  show (if isSnd N a = true then 2 else 0) ≤
    (if isSnd N a = true then (if ((a, 0) : Port) = (a, 0) then 2 else 1) else 0)
  by_cases h : isSnd N a = true
  · rw [ite_pos' h, ite_pos' h, ite_pos' rfl]
    exact Nat.le_refl 2
  · rw [ite_neg' h, ite_neg' h]
    exact Nat.le_refl 0

theorem walk_seek_next (N : Nat → Nat) (a : Id) (α : Arith) (p c q' : Port) :
    walk N (.seek a α p c) ≤ walk N (.seek a α c q') + 1 := by
  show (if isSnd N a = true then (if p = (a, 0) then 2 else 1) else 0) ≤
    (if isSnd N a = true then (if c = (a, 0) then 2 else 1) else 0) + 1
  by_cases h : isSnd N a = true
  · rw [ite_pos' h, ite_pos' h]
    split <;> split <;> omega
  · rw [ite_neg' h, ite_neg' h]
    omega

theorem walk_seek_x (N : Nat → Nat) {a : Id} (α : Arith) (p c : Port) (h : isSnd N a = false) :
    walk N (.seek a α p c) = 0 := by
  show (if isSnd N a = true then (if p = (a, 0) then 2 else 1) else 0) = 0
  rw [h]
  rfl

/-- What a thread has still to spend on the successors of the second
arguments: two for each in its list, counted up to `K` of them, and what
it owes on the one it is reading. -/
def extra (N : Nat → Nat) (K : Nat) (T : XThread Arith) : Nat :=
  2 * min (sndCnt N T.todo) K + walk N T.st

/-- **The price of one action, with three for each successor of a second
argument.**  In a memory in order such a successor is there with a
segment at its principal port, and it is never one of a pair; so a
thread that reads it makes three actions at least before it reads the
next entry of its list, none of them toward a claim. -/
theorem act_cost3 {N : Nat → Nat} {K : Nat} (B : Nat) {X : XNet Arith} {T : XThread Arith}
    (hB : B ≤ X.agents.length) (hM : MemOk N K X) (hT : ThOk N T) :
    15 * (XMach.act xsys X T).2.2 + credit2 (XMach.act xsys X T).2.1.st +
        8 * (adders (XMach.act xsys X T).1.agents + heldAdd (XMach.act xsys X T).2.1.st) +
        owed T.st + toRead B T + extra N K T ≤
      XThread.busy T + owed (XMach.act xsys X T).2.1.st + credit2 T.st +
        8 * (adders X.agents + heldAdd T.st) + toRead B (XMach.act xsys X T).2.1 +
        extra N K (XMach.act xsys X T).2.1 := by
  have hcnt := hM.count
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min 0 B + (2 * min 0 K + 0) ≤
        0 + 0 + 0 + 8 * (adders X.agents + 0) + min 0 B + (2 * min 0 K + 0)
      omega
    | cons e rest =>
      have sc : sndCnt N (e :: rest) = (if isSnd N e.1 = true then 1 else 0) + sndCnt N rest :=
        rfl
      have wl : walk N (.look e.1 e.2) = if isSnd N e.1 = true then 2 else 0 := rfl
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min (rest.length + 1) B +
            (2 * min (sndCnt N (e :: rest)) K + 0) ≤
          1 + 0 + 0 + 8 * (adders X.agents + 0) + min rest.length B +
            (2 * min (sndCnt N rest) K + walk N (.look e.1 e.2))
        by_cases hsn : isSnd N e.1 = true
        · rw [ite_pos' hsn] at sc
          rw [ite_pos' hsn] at wl
          omega
        · rw [ite_neg' hsn] at sc
          rw [ite_neg' hsn] at wl
          omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min (rest.length + 1) B +
            (2 * min (sndCnt N (e :: rest)) K + 0) ≤
          1 + 0 + 0 + 8 * (adders X.agents + 0) + min rest.length B +
            (2 * min (sndCnt N rest) K + 0)
        by_cases hsn : isSnd N e.1 = true
        · have h1 := hM.alive e.1 hsn
          have h2 := kind_snd N hsn (hT.1 e List.mem_cons_self)
          rw [← h2] at h1
          exact absurd h1 ha
        · rw [ite_neg' hsn] at sc
          omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B +
          (2 * min (sndCnt N todo) K + walk N (.look a α)) ≤
        1 + 0 + 0 + 8 * (adders X.agents + 0) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
      have wl : walk N (.look a α) = if isSnd N a = true then 2 else 0 := rfl
      by_cases hsn : isSnd N a = true
      · obtain ⟨q', hq'⟩ := hM.look a hsn
        rw [hq] at hq'
        cases hq'
      · rw [ite_neg' hsn] at wl
        omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show 15 * 0 + 1 + 8 * (adders X.agents + 0) + 0 + min todo.length B +
          (2 * min (sndCnt N todo) K + walk N (.look a α)) ≤
        1 + 0 + 0 + 8 * (adders X.agents + 0) + min todo.length B +
          (2 * min (sndCnt N todo) K + walk N (.seek a α (a, 0) q))
      have w := walk_look_le N a α q
      omega
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B +
            (2 * min (sndCnt N todo) K + walk N (.seek a α p q)) ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
        have w := walk_le_two N (.seek a α p q)
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 15 * 0 + 1 + 8 * (adders X.agents + 0) + 0 + min todo.length B +
            (2 * min (sndCnt N todo) K + walk N (.seek a α p q)) ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B +
            (2 * min (sndCnt N todo) K + walk N (.seek a α q q'))
        have w := walk_seek_next N a α p q q'
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · have hi := (act_inv hM hT).2.2
        rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr] at hi
        have hi' : KindOk a α ∧ KindOk q.1 β ∧ XP N (a, 0) ∧ XP N (q.1, 0) := hi
        have w := walk_seek_x N α p q (x_not_snd N hi'.2.2.1)
        rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show 15 * 0 + 2 + 8 * (adders X.agents + 0) + 0 + min todo.length B +
            (2 * min (sndCnt N todo) K + walk N (.seek a α p q)) ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B +
            (2 * min (sndCnt N todo) K + walk N (.seek a α p q)) ≤
          1 + 0 + 1 + 8 * (adders X.agents + 0) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
        have w := walk_le_two N (.seek a α p q)
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      have ht : adders (X.takeAgent a).agents + isAdd α ≤ adders X.agents := adders_take ha
      show 15 * 0 + 3 + 8 * (adders (X.takeAgent a).agents + isAdd α) + 0 + min todo.length B +
          (2 * min (sndCnt N todo) K + 0) ≤
        1 + 0 + 2 + 8 * (adders X.agents + 0) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show 15 * 0 + 0 + 8 * (adders X.agents + 0) + 0 + min todo.length B + (2 * min (sndCnt N todo) K + 0) ≤
        1 + 0 + 2 + 8 * (adders X.agents + 0) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
      omega
  | half a b α β =>
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show 15 * 0 + 0 + 8 * (isAdd α + adders X.agents + 0) + 0 + min todo.length B + (2 * min (sndCnt N todo) K + 0) ≤
          1 + 0 + 3 + 8 * (adders X.agents + isAdd α) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have ht : adders (X.takeAgent b).agents + isAdd β ≤ adders X.agents := adders_take hc.1
        have hr := rule_cost hR hc.2
        show 15 * 1 + 0 + 8 * (adders (X.takeAgent b).agents + adders (R.newAgents a b)) + 0 +
            min todo.length B + (2 * min (sndCnt N todo) K + 0) ≤
          1 + ((R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length + 1) + 3 +
            8 * (adders X.agents + isAdd α) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show 15 * 0 + 0 + 8 * (isAdd α + adders X.agents + 0) + 0 + min todo.length B + (2 * min (sndCnt N todo) K + 0) ≤
        1 + 0 + 3 + 8 * (adders X.agents + isAdd α) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show 15 * 0 + 0 + 8 * (isAdd γ + adders X.agents + adders as) +
          (as.length + 1 + ls.length + 1) + min todo.length B + (2 * min (sndCnt N todo) K + 0) ≤
        1 + (as.length + ls.length + 1) + 0 + 8 * (adders X.agents + (isAdd γ + adders as)) +
          min todo.length B + (2 * min (sndCnt N todo) K + 0)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + (0 + (ls.length + 1) + 1) +
            min todo.length B + (2 * min (sndCnt N todo) K + 0) ≤
          1 + (0 + ls.length + 1) + 0 + 8 * (adders X.agents + 0) + min todo.length B + (2 * min (sndCnt N todo) K + 0)
        omega
      | nil =>
        show 15 * 0 + 0 + 8 * (adders X.agents + 0) + (0 + 0 + 1) + min todo.length B + (2 * min (sndCnt N todo) K + 0) ≤
          1 + 0 + 0 + 8 * (adders X.agents + 0) + min X.agents.length B +
            (2 * min (sndCnt N X.agents) K + 0)
        omega

theorem step_cost3 {N : Nat → Nat} {K : Nat} (B : Nat) (M : XMach Arith) (t : Nat)
    (hB : B ≤ M.mem.agents.length) (hO : MachOk N K M) :
    15 * (M.step xsys t).2 +
        (total paid2 (M.step xsys t).1.ths + 8 * adders (M.step xsys t).1.mem.agents) +
        total due M.ths + total (toRead B) M.ths + total (extra N K) M.ths ≤
      M.stepTally XThread.busy t + total due (M.step xsys t).1.ths +
        (total paid2 M.ths + 8 * adders M.mem.agents) +
        total (toRead B) (M.step xsys t).1.ths + total (extra N K) (M.step xsys t).1.ths := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    have e4 : M.stepTally XThread.busy t = 0 := by
      unfold XMach.stepTally
      rw [h]
    rw [es, e4]
    show 15 * 0 + (total paid2 M.ths + 8 * adders M.mem.agents) + total due M.ths +
        total (toRead B) M.ths + total (extra N K) M.ths ≤
      0 + total due M.ths + (total paid2 M.ths + 8 * adders M.mem.agents) +
        total (toRead B) M.ths + total (extra N K) M.ths
    omega
  | some T =>
    have es := XMach.step_eq (M := M) (t := t) h (act_self M.mem T)
    have e1 : (M.step xsys t).2 = (XMach.act xsys M.mem T).2.2 := by rw [es]
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T).1 := by rw [es]
    have e4 : M.stepTally XThread.busy t = XThread.busy T := by
      unfold XMach.stepTally
      rw [h]
    rw [e1, e2, e3, e4]
    have sp := total_set paid2 M.ths t T (XMach.act xsys M.mem T).2.1 h
    have sd := total_set due M.ths t T (XMach.act xsys M.mem T).2.1 h
    have sr := total_set (toRead B) M.ths t T (XMach.act xsys M.mem T).2.1 h
    have se := total_set (extra N K) M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_cost3 B hB hO.1 (hO.2 T (List.mem_of_getElem? h))
    have p1 : paid2 T = credit2 T.st + 8 * heldAdd T.st := rfl
    have p2 : paid2 (XMach.act xsys M.mem T).2.1 = credit2 (XMach.act xsys M.mem T).2.1.st +
        8 * heldAdd (XMach.act xsys M.mem T).2.1.st := rfl
    have d1 : due T = owed T.st := rfl
    have d2 : due (XMach.act xsys M.mem T).2.1 = owed (XMach.act xsys M.mem T).2.1.st := rfl
    omega

/-- **The price of a run, with three actions for each successor of a
second argument.**  From a memory in order, at every action of a run:
fifteen for each claim, what the threads have put toward claims, eight
for each adder, and for each thread the successors of the net less the
number of threads and two more for each of the `K` successors of the
second arguments, are never more than the work done, what the threads
still owe, and what they have still to read. -/
theorem trace_read3 {N : Nat → Nat} {K : Nat} {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) (hO : MemOk N K X) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) :
    ∀ i, 15 * ((XMach.init X nt).trace xsys σ i).2 +
          (total paid2 ((XMach.init X nt).trace xsys σ i).1.ths +
            8 * adders ((XMach.init X nt).trace xsys σ i).1.mem.agents) +
          nt * (succs X.agents - nt) + nt * (2 * K) ≤
        (XMach.init X nt).work xsys σ i +
          total due ((XMach.init X nt).trace xsys σ i).1.ths + 8 * adders X.agents +
          total (toRead (succs X.agents - nt)) ((XMach.init X nt).trace xsys σ i).1.ths +
          total (extra N K) ((XMach.init X nt).trace xsys σ i).1.ths
  | 0 => by
    obtain ⟨-, -, hc⟩ := trace_read hX hnd hnt σ 0
    have z5 : (XMach.init X nt).ths.length * (2 * K) ≤
        total (extra N K) (XMach.init X nt).ths :=
      total_ge_mul fun T hT => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
        have e1 := sndCnt_append N (X.agents.drop t) (X.agents.take t)
        have e2 := sndCnt_append N (X.agents.take t) (X.agents.drop t)
        rw [List.take_append_drop] at e2
        have hc' := hO.count
        show 2 * K ≤ 2 * min (sndCnt N (X.agents.drop t ++ X.agents.take t)) K + 0
        omega
    rw [init_length] at z5
    have z5' : nt * (2 * K) ≤
        total (extra N K) ((XMach.init X nt).trace xsys σ 0).1.ths := z5
    omega
  | i + 1 => by
    obtain ⟨ha, hb, -⟩ := trace_read hX hnd hnt σ i
    have ih := trace_read3 hX hnd hO hnt σ i
    have hlen : ((XMach.init X nt).trace xsys σ i).1.ths.length = nt :=
      (XMach.trace_length xsys σ _ i).trans (init_length X nt)
    have hle := total_le_mul (f := held) (P := 1) ha
    have hsl := succs_le_length ((XMach.init X nt).trace xsys σ i).1.mem.agents
    have hB : succs X.agents - nt ≤
        ((XMach.init X nt).trace xsys σ i).1.mem.agents.length := by
      rw [hlen] at hle
      omega
    have h3 := step_cost3 (succs X.agents - nt) ((XMach.init X nt).trace xsys σ i).1 (σ i) hB
      (trace_ok σ (init_ok hO nt) i)
    show 15 * (((XMach.init X nt).trace xsys σ i).2 +
          (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).2) +
        (total paid2 (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
          8 * adders (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.mem.agents) +
        nt * (succs X.agents - nt) + nt * (2 * K) ≤
      (XMach.init X nt).work xsys σ i +
          ((XMach.init X nt).trace xsys σ i).1.stepTally XThread.busy (σ i) +
        total due (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
        8 * adders X.agents +
        total (toRead (succs X.agents - nt))
          (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths +
        total (extra N K) (((XMach.init X nt).trace xsys σ i).1.step xsys (σ i)).1.ths
    omega

/-- **Every thread spends three actions on each successor of a second
argument.**  From a memory in order, with any number of threads and any
schedule: when every thread is at rest, fifteen times the claims made,
and for each thread the successors of the net less the number of threads
and two more for each of the `K` successors of the second arguments, are
at most the work done and eight for each adder the net had. -/
theorem rest_read3 {N : Nat → Nat} {K : Nat} {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) (hO : MemOk N K X) {nt : Nat} (hnt : 0 < nt)
    (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init X nt).trace xsys σ i).1.resting = true) :
    15 * ((XMach.init X nt).trace xsys σ i).2 + nt * (succs X.agents - nt) + nt * (2 * K) ≤
      (XMach.init X nt).work xsys σ i + 8 * adders X.agents := by
  have h := trace_read3 hX hnd hO hnt σ i
  have z3 : total due ((XMach.init X nt).trace xsys σ i).1.ths = 0 :=
    total_rest due rfl _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z4 : total (toRead (succs X.agents - nt)) ((XMach.init X nt).trace xsys σ i).1.ths = 0 :=
    total_rest (toRead (succs X.agents - nt)) (Nat.zero_min _) _
      fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have e0 : extra N K ⟨[], .idle⟩ = 0 := by
    show 2 * min 0 K + 0 = 0
    rw [Nat.zero_min]
  have z5 : total (extra N K) ((XMach.init X nt).trace xsys σ i).1.ths = 0 :=
    total_rest (extra N K) e0 _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  rw [z3, z4, z5] at h
  omega

/-- The second arguments of two additions side by side, by tag. -/
def sideN (n n' : Nat) : Nat → Nat := fun c => if c = 0 then n else if c = 1 then n' else 0

theorem sum_kind (M n c : Nat) : ∀ e, e ∈ (sum M n).agents → KindOk (e.1 ++ [c]) e.2 := by
  intro e he
  rw [sum_agents] at he
  obtain ⟨i, γ⟩ := e
  rcases List.mem_append.1 he with h | h
  · obtain ⟨h1, j, h2, -, h3⟩ := mem_chainL h
    have h1' : γ = .succ := h1
    have h3' : i = [j] := h3
    subst h1'
    subst h3'
    show (j = 1 ∧ Arith.succ = .add) ∨ ((j = 2 ∨ j = 3) ∧ Arith.succ = .zero) ∨
      (4 ≤ j ∧ Arith.succ = .succ)
    exact .inr (.inr ⟨by omega, rfl⟩)
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨h1, j, h2, -, h3⟩ := mem_sndL h
      have h1' : γ = .succ := h1
      have h3' : i = [j] := h3
      subst h1'
      subst h3'
      show (j = 1 ∧ Arith.succ = .add) ∨ ((j = 2 ∨ j = 3) ∧ Arith.succ = .zero) ∨
        (4 ≤ j ∧ Arith.succ = .succ)
      exact .inr (.inr ⟨h2, rfl⟩)
    · have h' : (i, γ) ∈ [(([1] : Id), Arith.add), ([2], .zero), ([3], .zero)] := h
      rcases List.mem_cons.1 h' with e | h'
      · cases e
        exact .inl ⟨rfl, rfl⟩
      rcases List.mem_cons.1 h' with e | h'
      · cases e
        exact .inr (.inl ⟨.inl rfl, rfl⟩)
      rcases List.mem_cons.1 h' with e | h'
      · cases e
        exact .inr (.inl ⟨.inr rfl, rfl⟩)
      · cases h'

/-- Putting a successor on a wire keeps the sides, when both its ports
are on the side of the wire. -/
theorem push_color {P : Port → Prop} {X : XNet Arith} {p : Port} {u : Id}
    (hX : ∀ e, e ∈ X.wires → (P e.1 ↔ P e.2)) (h0 : P (u, 0) ↔ P p) (h1 : P (u, 1) ↔ P p) :
    ∀ e, e ∈ (push X p u).wires → (P e.1 ↔ P e.2) := by
  unfold push
  split
  · rename_i q hq
    have hpq : P p ↔ P q := hX (p, q) (assoc_mem hq)
    intro e he
    have he' : e ∈ (p, (u, 0)) :: ((u, 0), p) :: ((u, 1), q) :: (q, (u, 1)) ::
        X.wires.filter (fun e => decide (e.1 ≠ p ∧ e.1 ≠ q)) := he
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h0.symm
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h0
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h1.trans hpq
    rcases List.mem_cons.1 he' with rfl | he'
    · exact (h1.trans hpq).symm
    · exact hX e (List.mem_filter.1 he').1
  · exact hX

theorem base_color (N : Nat → Nat) (c : Nat) : ∀ e, e ∈ base.wires →
    (XP N (e.1.1 ++ [c], e.1.2) ↔ XP N (e.2.1 ++ [c], e.2.2)) := by
  intro e he
  have he' : e ∈ [((([1] : Id), 0), (([2] : Id), 0)), (([1], 1), ([3], 0)),
      (([1], 2), ([0], 0)), (([2], 0), ([1], 0)), (([3], 0), ([1], 1)),
      (([0], 0), ([1], 2))] := he
  rcases List.mem_cons.1 he' with rfl | he'
  · show XP N ([1, c], 0) ↔ XP N ([2, c], 0)
    rw [xp_base, xp_base]
    omega
  rcases List.mem_cons.1 he' with rfl | he'
  · show XP N ([1, c], 1) ↔ XP N ([3, c], 0)
    rw [xp_base, xp_base]
    omega
  rcases List.mem_cons.1 he' with rfl | he'
  · show XP N ([1, c], 2) ↔ XP N ([0, c], 0)
    rw [xp_base, xp_base]
    omega
  rcases List.mem_cons.1 he' with rfl | he'
  · show XP N ([2, c], 0) ↔ XP N ([1, c], 0)
    rw [xp_base, xp_base]
    omega
  rcases List.mem_cons.1 he' with rfl | he'
  · show XP N ([3, c], 0) ↔ XP N ([1, c], 1)
    rw [xp_base, xp_base]
    omega
  rcases List.mem_cons.1 he' with rfl | he'
  · show XP N ([0, c], 0) ↔ XP N ([1, c], 2)
    rw [xp_base, xp_base]
    omega
  · cases he'

theorem sumSnd_color (N : Nat → Nat) (c : Nat) : ∀ k, k ≤ N c → ∀ e, e ∈ (sumSnd k).wires →
    (XP N (e.1.1 ++ [c], e.1.2) ↔ XP N (e.2.1 ++ [c], e.2.2))
  | 0, _ => base_color N c
  | k + 1, hk => by
    show ∀ e, e ∈ (push (sumSnd k) ([1], 1) [k + 4]).wires → _
    refine push_color (P := fun p => XP N (p.1 ++ [c], p.2))
      (sumSnd_color N c k (by omega)) ?_ ?_
    · show XP N ([k + 4, c], 0) ↔ XP N ([1, c], 1)
      rw [xp_base, xp_base]
      omega
    · show XP N ([k + 4, c], 1) ↔ XP N ([1, c], 1)
      rw [xp_base, xp_base]
      omega

/-- **Every segment of an addition joins two ports of one side.** -/
theorem sum_color (N : Nat → Nat) (c n : Nat) (hN : N c = n) : ∀ M, ∀ e, e ∈ (sum M n).wires →
    (XP N (e.1.1 ++ [c], e.1.2) ↔ XP N (e.2.1 ++ [c], e.2.2))
  | 0 => by
    show ∀ e, e ∈ (sumSnd n).wires → _
    exact sumSnd_color N c n (by omega)
  | M + 1 => by
    show ∀ e, e ∈ (push (sum M n) ([1], 0) [M + n + 4]).wires → _
    refine push_color (P := fun p => XP N (p.1 ++ [c], p.2)) (sum_color N c n hN M) ?_ ?_
    · show XP N ([M + n + 4, c], 0) ↔ XP N ([1, c], 0)
      rw [xp_base, xp_base]
      omega
    · show XP N ([M + n + 4, c], 1) ↔ XP N ([1, c], 0)
      rw [xp_base, xp_base]
      omega

theorem sndL_sndCnt (N : Nat → Nat) (c : Nat) : ∀ k, k ≤ N c →
    sndCnt N ((sndL k).map (tagA c)) = k
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := sndL_sndCnt N c k (by omega)
    have hs : isSnd N [k + 4, c] = true := decide_eq_true ⟨by omega, by omega⟩
    show (if isSnd N [k + 4, c] = true then 1 else 0) + sndCnt N ((sndL k).map (tagA c)) = k + 1
    rw [ite_pos' hs, ih]
    omega

theorem sum_sndCnt (N : Nat → Nat) (c n : Nat) (hN : N c = n) (M : Nat) :
    n ≤ sndCnt N ((sum M n).agents.map (tagA c)) := by
  rw [sum_agents, List.map_append, List.map_append, sndCnt_append, sndCnt_append]
  have h := sndL_sndCnt N c n (by omega)
  omega

/-- **Two additions side by side are a memory in order.** -/
theorem two_sums_memOk (m n m' n' : Nat) :
    MemOk (sideN n n') (n + n') (twoSums (m + 1) n (m' + 1) n') where
  kinds := fun e he => by
    have he' : e ∈ (sum (m + 1) n).agents.map (tagA 0) ++
        (sum (m' + 1) n').agents.map (tagA 1) := he
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_kind (m + 1) n 0 x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_kind (m' + 1) n' 1 x hx
  wires := fun e he => by
    have he' : e ∈ (sum (m + 1) n).wires.map (tagL 0) ++
        (sum (m' + 1) n').wires.map (tagL 1) := he
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_color (sideN n n') 0 n rfl (m + 1) x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_color (sideN n n') 1 n' rfl (m' + 1) x hx
  alive := fun s hs => by
    obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape _ hs
    have h3' : j ≤ (if c = 0 then n else if c = 1 then n' else 0) + 3 := h3
    by_cases h0 : c = 0
    · subst h0
      rw [ite_pos' rfl] at h3'
      have hm := sndL_mem n (j - 4) (by omega)
      rw [show j - 4 + 4 = j by omega] at hm
      exact ((looks_left (sum (m + 1) n) (sum (m' + 1) n')).agent [j]).trans
        (sum_assoc_base m n (e := ([j], Arith.succ)) (List.mem_append_left _ hm))
    · rw [ite_neg' h0] at h3'
      by_cases h1 : c = 1
      · subst h1
        rw [ite_pos' rfl] at h3'
        have hm := sndL_mem n' (j - 4) (by omega)
        rw [show j - 4 + 4 = j by omega] at hm
        exact ((looks_right (sum (m + 1) n) (sum (m' + 1) n')).agent [j]).trans
          (sum_assoc_base m' n' (e := ([j], Arith.succ)) (List.mem_append_left _ hm))
      · rw [ite_neg' h1] at h3'
        omega
  look := fun s hs => by
    obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape _ hs
    have h3' : j ≤ (if c = 0 then n else if c = 1 then n' else 0) + 3 := h3
    by_cases h0 : c = 0
    · subst h0
      rw [ite_pos' rfl] at h3'
      have hq : ∃ q, assoc (([j], 0) : Port) (sum (m + 1) n).wires = some q := by
        by_cases hj : j = n + 3
        · subst hj
          exact ⟨_, solo_look_top m n 0⟩
        · exact ⟨_, (solo_look_snd m n (j := j) (by omega) (by omega) 0).1⟩
      obtain ⟨q, hq⟩ := hq
      exact ⟨tagPort 0 q, ((looks_left (sum (m + 1) n) (sum (m' + 1) n')).wire ([j], 0)).trans
        (congrArg (Option.map (tagPort 0)) hq)⟩
    · rw [ite_neg' h0] at h3'
      by_cases h1 : c = 1
      · subst h1
        rw [ite_pos' rfl] at h3'
        have hq : ∃ q, assoc (([j], 0) : Port) (sum (m' + 1) n').wires = some q := by
          by_cases hj : j = n' + 3
          · subst hj
            exact ⟨_, solo_look_top m' n' 0⟩
          · exact ⟨_, (solo_look_snd m' n' (j := j) (by omega) (by omega) 0).1⟩
        obtain ⟨q, hq⟩ := hq
        exact ⟨tagPort 1 q,
          ((looks_right (sum (m + 1) n) (sum (m' + 1) n')).wire ([j], 0)).trans
            (congrArg (Option.map (tagPort 1)) hq)⟩
      · rw [ite_neg' h1] at h3'
        omega
  count := by
    show n + n' ≤ sndCnt (sideN n n') ((sum (m + 1) n).agents.map (tagA 0) ++
      (sum (m' + 1) n').agents.map (tagA 1))
    rw [sndCnt_append]
    have h1 := sum_sndCnt (sideN n n') 0 n rfl (m + 1)
    have h2 := sum_sndCnt (sideN n n') 1 n' rfl (m' + 1)
    omega

/-- **On two additions side by side the successors of the second
arguments are in memory at every action of every run**, whatever the
number of threads and the schedule: no thread ever takes one. -/
theorem two_sums_snd_forever (m n m' n' nt : Nat) (σ : Nat → Nat) (i : Nat) {j : Nat}
    (h4 : 4 ≤ j) :
    (j ≤ n + 3 → assoc [j, 0] ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ
        i).1.mem.agents = some .succ) ∧
      (j ≤ n' + 3 → assoc [j, 1] ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ
        i).1.mem.agents = some .succ) :=
  ⟨fun h3 => snd_forever (two_sums_memOk m n m' n') nt σ i
      (s := [j, 0]) (decide_eq_true ⟨h4, h3⟩),
    fun h3 => snd_forever (two_sums_memOk m n m' n') nt σ i
      (s := [j, 1]) (decide_eq_true ⟨h4, h3⟩)⟩

/-- **Two additions side by side, any number of threads, any schedule**:
a run that ends at rest has done fifteen actions for each of its
`m + m' + 4` interactions, less sixteen, and for each thread one for each
successor of the first arguments, less the number of threads, and three
for each successor of the second arguments. -/
theorem two_sums_read3_work (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    15 * (m + m') + 44 + nt * (m + n + m' + n' + 2 - nt) + nt * (2 * (n + n')) ≤
      (XMach.init (twoSums (m + 1) n (m' + 1) n') nt).work xsys σ i := by
  have h := rest_read3 (two_sums_wf (m + 1) n (m' + 1) n')
    (two_sums_nodup (m + 1) n (m' + 1) n') (two_sums_memOk m n m' n') hnt σ hr
  rw [two_sums_claims m n m' n' hnt σ hr, adders_two_sums, succs_two_sums] at h
  have e : m + 1 + n + (m' + 1 + n') - nt = m + n + m' + n' + 2 - nt := by omega
  rw [e] at h
  omega

/-- **The limit with the reading of the second arguments.**  With `c`
threads in turn on two additions side by side. -/
theorem two_sums_rounds_read3 (m n m' n' : Nat) {c R : Nat} (hc : 0 < c)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    15 * (m + m') + 44 + c * (m + n + m' + n' + 2 - c) + c * (2 * (n + n')) ≤ c * R :=
  Nat.le_trans (two_sums_read3_work m n m' n' hc (fun i => i % c) h.1)
    (XMach.work_le_count xsys _ _ _)

/-- **No number of threads brings the rounds under three for each
successor of the second arguments**: the rounds and the threads together
are more than `m + m' + 3 * (n + n') + 2`. -/
theorem two_sums_rounds_floor3 (m n m' n' : Nat) {c R : Nat} (hc : 0 < c)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    m + m' + 3 * (n + n') + 2 < R + c := by
  have h1 := two_sums_rounds_read3 m n m' n' hc h
  have h2 : c * (m + n + m' + n' + 2 - c + 2 * (n + n')) < c * R := by
    rw [Nat.mul_add]
    omega
  have h3 := Nat.lt_of_mul_lt_mul_left h2
  omega

/-- **Two threads in turn on two additions** need
`(17 * (m + m') + 6 * (n + n') + 44) / 2` rounds at least. -/
theorem two_threads_read3_ge (m n m' n' : Nat) {R : Nat}
    (h : Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2) R) :
    17 * (m + m') + 6 * (n + n') + 44 ≤ 2 * R := by
  have h1 := two_sums_rounds_read3 m n m' n' (Nat.succ_pos 1) h
  omega

/-- `6 + 32` twice: two threads take 489 rounds and cannot take fewer
than 299; four threads cannot take fewer than 249, and sixteen not fewer
than 201. -/
example {R : Nat} (h : Rounds 2 (XMach.init (twoSums 6 32 6 32) 2) R) : 299 ≤ R := by
  have h' := two_threads_read3_ge 5 32 5 32 h
  omega

example {R : Nat} (h : Rounds 4 (XMach.init (twoSums 6 32 6 32) 4) R) : 249 ≤ R := by
  have h' := two_sums_rounds_read3 5 32 5 32 (by decide) h
  omega

example {R : Nat} (h : Rounds 16 (XMach.init (twoSums 6 32 6 32) 16) R) : 201 ≤ R := by
  have h' := two_sums_rounds_read3 5 32 5 32 (by decide) h
  omega

end Arith

end INet
