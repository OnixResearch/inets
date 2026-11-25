import InteractionNets.Arith.Floor

/-! ### The floor: the second addition is touched late -/

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

/-- What a thread owes, by its own actions alone, on a successor of a
second argument it is reading: two when it has read the agent, one while
it follows the wire. -/
def walk1 (N : Nat → Nat) : TState Arith → Nat
  | .look a _ => if isSnd N a = true then 2 else 0
  | .seek a _ _ _ => if isSnd N a = true then 1 else 0
  | _ => 0

/-- **What a thread has still to do by its own actions**: when it writes,
the cells left, the reload, and `G` after it; otherwise `g` of its list
and what it owes on the agent it is reading. -/
def lam (N : Nat → Nat) (g : List (Id × Arith) → Nat) (G : Nat) (T : XThread Arith) : Nat :=
  match T.st with
  | .write as ls => as.length + ls.length + 1 + G
  | st => g T.todo + walk1 N st

/-- **No action of a thread lowers it by more than one.**  In a memory in
order, for any measure `g` of the list that an entry raises by one at
most, or by three when it is a successor of a second argument, that is
never above `G`, and that is `G` on the memory. -/
theorem act_lam {N : Nat → Nat} {K : Nat} (g : List (Id × Arith) → Nat) (G : Nat)
    {X : XNet Arith} {T : XThread Arith} (hM : MemOk N K X) (hT : ThOk N T)
    (hg : ∀ e l, g (e :: l) ≤ g l + (if isSnd N e.1 = true then 3 else 1))
    (hG : ∀ l, g l ≤ G) (hR : G ≤ g X.agents) :
    lam N g G T ≤ lam N g G (XMach.act xsys X T).2.1 + 1 := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show g [] + 0 ≤ g [] + 0 + 1
      omega
    | cons e rest =>
      have h1 := hg e rest
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show g (e :: rest) + 0 ≤ g rest + (if isSnd N e.1 = true then 2 else 0) + 1
        by_cases hsn : isSnd N e.1 = true
        · rw [ite_pos' hsn] at h1
          rw [ite_pos' hsn]
          omega
        · rw [ite_neg' hsn] at h1
          rw [ite_neg' hsn]
          omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show g (e :: rest) + 0 ≤ g rest + 0 + 1
        by_cases hsn : isSnd N e.1 = true
        · have h2 := hM.alive e.1 hsn
          have h3 := kind_snd N hsn (hT.1 e List.mem_cons_self)
          rw [← h3] at h2
          exact absurd h2 ha
        · rw [ite_neg' hsn] at h1
          omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show g todo + (if isSnd N a = true then 2 else 0) ≤ g todo + 0 + 1
      by_cases hsn : isSnd N a = true
      · obtain ⟨q', hq'⟩ := hM.look a hsn
        rw [hq] at hq'
        cases hq'
      · rw [ite_neg' hsn]
        omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show g todo + (if isSnd N a = true then 2 else 0) ≤
        g todo + (if isSnd N a = true then 1 else 0) + 1
      by_cases hsn : isSnd N a = true
      · rw [ite_pos' hsn, ite_pos' hsn]
        omega
      · rw [ite_neg' hsn, ite_neg' hsn]
        omega
  | seek a α p q =>
    have hw : (if isSnd N a = true then 1 else 0) ≤ 1 := by
      split <;> omega
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show g todo + (if isSnd N a = true then 1 else 0) ≤ g todo + 0 + 1
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show g todo + (if isSnd N a = true then 1 else 0) ≤
          g todo + (if isSnd N a = true then 1 else 0) + 1
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show g todo + (if isSnd N a = true then 1 else 0) ≤ g todo + 0 + 1
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show g todo + (if isSnd N a = true then 1 else 0) ≤ g todo + 0 + 1
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show g todo + 0 ≤ g todo + 0 + 1
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show g todo + 0 ≤ g todo + 0 + 1
      omega
  | half a b α β =>
    have h1 := hG todo
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR' : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR')]
        show g todo + 0 ≤ g todo + 0 + 1
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR')]
        show g todo + 0 ≤
          (R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length + 1 + G + 1
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show g todo + 0 ≤ g todo + 0 + 1
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show as.length + 1 + ls.length + 1 + G ≤ as.length + ls.length + 1 + G + 1
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 0 + (ls.length + 1) + 1 + G ≤ 0 + ls.length + 1 + G + 1
        omega
      | nil =>
        show 0 + 0 + 1 + G ≤ g X.agents + 0 + 1
        omega

/-- **Threads in turn**: after `i + 1` actions the thread numbered `t`
has made one more than after `i` exactly when it is the one that acts. -/
theorem rr_own (c i t : Nat) (hc : 0 < c) (ht : t < c) :
    (i + 1) / c + (if t < (i + 1) % c then 1 else 0) =
      i / c + (if t < i % c then 1 else 0) + (if t = i % c then 1 else 0) := by
  have hd := Nat.div_add_mod i c
  have hm := Nat.mod_lt i hc
  obtain ⟨q, hq⟩ : ∃ q, i / c = q := ⟨_, rfl⟩
  obtain ⟨k, hk0⟩ : ∃ k, i % c = k := ⟨_, rfl⟩
  rw [hq, hk0] at hd
  rw [hk0] at hm
  rw [hq, hk0]
  by_cases hk : k + 1 < c
  · have e0 : i + 1 = (k + 1) + c * q := by omega
    have e1 : (i + 1) / c = q := by
      rw [e0, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hk]
      omega
    have e2 : (i + 1) % c = k + 1 := by
      rw [e0, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    rw [e1, e2]
    split <;> split <;> split <;> omega
  · have e0 : i + 1 = c * (q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have e1 : (i + 1) / c = q + 1 := by
      rw [e0, Nat.mul_div_cancel_left _ hc]
    have e2 : (i + 1) % c = 0 := by
      rw [e0, Nat.mul_mod_right]
    rw [e1, e2]
    split <;> split <;> split <;> omega

/-- **One action of threads in turn, seen from each thread**: a measure
that the thread that acts lowers by one at most stays, together with the
number of its own actions, at least what it was. -/
theorem rr_step (Λ : XThread Arith → Nat) {M : XMach Arith} {c : Nat} (hc : 0 < c)
    (hlen : M.ths.length = c) (i : Nat)
    (hdrop : ∀ T0, M.ths[i % c]? = some T0 →
      Λ T0 ≤ Λ (XMach.act xsys M.mem T0).2.1 + 1)
    {t : Nat} (ht : t < c) {T : XThread Arith} (hT : M.ths[t]? = some T) :
    ∃ T', (M.step xsys (i % c)).1.ths[t]? = some T' ∧
      Λ T + (i / c + (if t < i % c then 1 else 0)) ≤
        Λ T' + ((i + 1) / c + (if t < (i + 1) % c then 1 else 0)) := by
  have hk := Nat.mod_lt i hc
  rw [rr_own c i t hc ht]
  cases h0 : M.ths[i % c]? with
  | none =>
    have hle := List.getElem?_eq_none_iff.1 h0
    omega
  | some T0 =>
    have es := XMach.step_eq (M := M) (t := i % c) h0 (act_self M.mem T0)
    have e2 : (M.step xsys (i % c)).1.ths = M.ths.set (i % c) (XMach.act xsys M.mem T0).2.1 := by
      rw [es]
    rw [e2]
    by_cases e : t = i % c
    · have eT : T = T0 := by
        rw [e] at hT
        exact Option.some.inj (hT.symm.trans h0)
      refine ⟨(XMach.act xsys M.mem T0).2.1, ?_, ?_⟩
      · rw [e]
        exact List.getElem?_set_self (by omega)
      · have hd := hdrop T0 h0
        rw [ite_pos' e, eT]
        omega
    · refine ⟨T, ?_, ?_⟩
      · rw [List.getElem?_set_ne (fun h => e h.symm)]
        exact hT
      · rw [ite_neg' e]
        omega

/-- The agents an adder meets: the successors and the zero of a first
argument. -/
def isF (N : Nat → Nat) : Id → Bool
  | [j, c] => decide (j = 2 ∨ N c + 4 ≤ j)
  | _ => false

/-- Those in a list of agents. -/
def fcnt (N : Nat → Nat) : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => (if isF N e.1 = true then 1 else 0) + fcnt N l

theorem fcnt_append (N : Nat → Nat) : ∀ (l₁ l₂ : List (Id × Arith)),
    fcnt N (l₁ ++ l₂) = fcnt N l₁ + fcnt N l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show (if isF N e.1 = true then 1 else 0) + fcnt N (l₁ ++ l₂) =
      (if isF N e.1 = true then 1 else 0) + fcnt N l₁ + fcnt N l₂
    rw [fcnt_append N l₁ l₂, Nat.add_assoc]

theorem fcnt_filter_le (N : Nat → Nat) (p : Id × Arith → Bool) : ∀ l : List (Id × Arith),
    fcnt N (l.filter p) ≤ fcnt N l
  | [] => Nat.le_refl 0
  | e :: l => by
    have ih := fcnt_filter_le N p l
    by_cases h : p e = true
    · rw [List.filter_cons_of_pos h]
      show (if isF N e.1 = true then 1 else 0) + fcnt N (l.filter p) ≤
        (if isF N e.1 = true then 1 else 0) + fcnt N l
      omega
    · rw [List.filter_cons_of_neg h]
      show fcnt N (l.filter p) ≤ (if isF N e.1 = true then 1 else 0) + fcnt N l
      omega

/-- Taking an agent that is in memory takes it off the count. -/
theorem fcnt_take (N : Nat → Nat) {a : Id} {α : Arith} : ∀ {l : List (Id × Arith)},
    assoc a l = some α →
      fcnt N (l.filter fun e => decide (e.1 ≠ a)) + (if isF N a = true then 1 else 0) ≤ fcnt N l
  | [], h => by cases h
  | (i, γ) :: l, h => by
    by_cases hi : i = a
    · have hle := fcnt_filter_le N (fun e : Id × Arith => decide (e.1 ≠ a)) l
      rw [List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show ¬ decide (i ≠ a) = true
          exact fun hd => of_decide_eq_true hd hi)]
      show fcnt N (l.filter fun e => decide (e.1 ≠ a)) + (if isF N a = true then 1 else 0) ≤
        (if isF N i = true then 1 else 0) + fcnt N l
      rw [hi]
      omega
    · have h' : (if i = a then some γ else assoc a l) = some α := h
      rw [ite_neg' hi] at h'
      have ih := fcnt_take N (l := l) h'
      rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show decide (i ≠ a) = true
          exact decide_eq_true hi)]
      show (if isF N i = true then 1 else 0) + fcnt N (l.filter fun e => decide (e.1 ≠ a)) +
          (if isF N a = true then 1 else 0) ≤ (if isF N i = true then 1 else 0) + fcnt N l
      omega

/-- A zero with its principal port on the side of the first argument is
the zero of a first argument. -/
theorem zero_x (N : Nat → Nat) : ∀ {z : Id}, KindOk z .zero → XP N (z, 0) → ∃ c, z = [2, c]
  | [], h, _ => False.elim h
  | [_], h, _ => False.elim h
  | [j, c], h, hx => by
    have h' : (j = 1 ∧ Arith.zero = .add) ∨ ((j = 2 ∨ j = 3) ∧ Arith.zero = .zero) ∨
        (4 ≤ j ∧ Arith.zero = .succ) := h
    have hx' : (j = 1 ∧ 0 = 0) ∨ (j = 2 ∧ 0 = 0) ∨ N c + 4 ≤ j := hx
    rcases h' with ⟨-, e⟩ | ⟨h23, -⟩ | ⟨-, e⟩
    · cases e
    · have hj : j = 2 := by omega
      subst hj
      exact ⟨c, rfl⟩
    · cases e
  | [0, t, c], h, _ => by
    have h' : (t = 1 ∧ Arith.zero = .succ) ∨ (t ≠ 1 ∧ Arith.zero = .add) := h
    rcases h' with ⟨-, e⟩ | ⟨-, e⟩
    · cases e
    · cases e
  | [_ + 1, _, _], h, _ => False.elim h
  | [0, 0, _, _], h, _ => by
    have h' : Arith.zero = .succ := h
    cases h'
  | [0, _ + 1, _, _], h, _ => False.elim h
  | [_ + 1, 0, _, _], h, _ => False.elim h
  | [_ + 1, _ + 1, _, _], h, _ => False.elim h
  | _ :: _ :: _ :: _ :: _ :: _, h, _ => False.elim h

theorem adder_f (N : Nat → Nat) {a : Id} (hka : KindOk a .add) : isF N (0 :: a) = false := by
  rcases kind_add hka with ⟨c, rfl⟩ | ⟨t, c, rfl, -⟩
  · rfl
  · rfl

theorem succ_f (N : Nat → Nat) {s : Id} (hks : KindOk s .succ) (hx : XP N (s, 0)) :
    isF N s = true ∧ isF N (0 :: s) = false := by
  obtain ⟨j, c, rfl, hj⟩ := succ_x N hks hx
  exact ⟨decide_eq_true (.inr hj), rfl⟩

theorem zero_f (N : Nat → Nat) {z : Id} (hkz : KindOk z .zero) (hx : XP N (z, 0)) :
    isF N z = true := by
  obtain ⟨c, rfl⟩ := zero_x N hkz hx
  exact decide_eq_true (.inl rfl)

/-- **Every pair has an agent of a first argument, and a rule makes
none.** -/
theorem rule_first (N : Nat → Nat) {α β : Arith} {R : XRhs Arith} {a b : Id}
    (hka : KindOk a α) (hkb : KindOk b β) (hxa : XP N (a, 0)) (hxb : XP N (b, 0))
    (hR : xsys.rule α β = some R) (hne : a ≠ b) :
    1 ≤ (if isF N a = true then 1 else 0) + (if isF N b = true then 1 else 0) ∧
      fcnt N (R.newAgents a b) = 0 := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_zero, zero_f N hkb hxb, ite_pos' rfl]
       exact ⟨by omega, rfl⟩)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       rw [newAgents_zero_swap, zero_f N hka hxa, ite_pos' rfl]
       exact ⟨by omega, rfl⟩)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       have h1 := adder_f N hka
       obtain ⟨h2, h3⟩ := succ_f N hkb hxb
       rw [newAgents_add hne, h2, ite_pos' rfl]
       refine ⟨by omega, ?_⟩
       show (if isF N (0 :: a) = true then 1 else 0) +
         ((if isF N (0 :: b) = true then 1 else 0) + 0) = 0
       rw [h1, h3]
       rfl)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       have h1 := adder_f N hkb
       obtain ⟨h2, h3⟩ := succ_f N hka hxa
       rw [newAgents_swap (a := b) (s := a) (fun e => hne e.symm), h2, ite_pos' rfl]
       refine ⟨by omega, ?_⟩
       show (if isF N (0 :: b) = true then 1 else 0) +
         ((if isF N (0 :: a) = true then 1 else 0) + 0) = 0
       rw [h1, h3]
       rfl)

/-- The agents of a first argument a thread holds. -/
def heldF (N : Nat → Nat) : TState Arith → Nat
  | .half a _ _ _ => if isF N a = true then 1 else 0
  | .write as _ => fcnt N as
  | _ => 0

/-- **Every claim uses up an agent of a first argument.**  In a memory in
order, no action makes the claims, and the agents of the first arguments
in memory or held, more together than they were. -/
theorem act_first {N : Nat → Nat} {K : Nat} {X : XNet Arith} {T : XThread Arith}
    (hM : MemOk N K X) (hT : ThOk N T) :
    (XMach.act xsys X T).2.2 + fcnt N (XMach.act xsys X T).1.agents +
        heldF N (XMach.act xsys X T).2.1.st ≤ fcnt N X.agents + heldF N T.st := by
  have _ := hM.count
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
      omega
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
      omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
      omega
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      have ht : fcnt N (X.takeAgent a).agents + (if isF N a = true then 1 else 0) ≤
          fcnt N X.agents := fcnt_take N ha
      show 0 + fcnt N (X.takeAgent a).agents + (if isF N a = true then 1 else 0) ≤
        fcnt N X.agents + 0
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
      omega
  | half a b α β =>
    have hs : KindOk a α ∧ KindOk b β ∧ XP N (a, 0) ∧ XP N (b, 0) := hT.2
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show 0 + ((if isF N a = true then 1 else 0) + fcnt N X.agents) + 0 ≤
          fcnt N X.agents + (if isF N a = true then 1 else 0)
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have ht : fcnt N (X.takeAgent b).agents + (if isF N b = true then 1 else 0) ≤
            fcnt N X.agents := fcnt_take N hc.1
        obtain ⟨r1, r2⟩ := rule_first N hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hR hc.2
        show 1 + fcnt N (X.takeAgent b).agents + fcnt N (R.newAgents a b) ≤
          fcnt N X.agents + (if isF N a = true then 1 else 0)
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show 0 + ((if isF N a = true then 1 else 0) + fcnt N X.agents) + 0 ≤
        fcnt N X.agents + (if isF N a = true then 1 else 0)
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show 0 + ((if isF N i = true then 1 else 0) + fcnt N X.agents) + fcnt N as ≤
        fcnt N X.agents + ((if isF N i = true then 1 else 0) + fcnt N as)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega
      | nil =>
        show 0 + fcnt N X.agents + 0 ≤ fcnt N X.agents + 0
        omega

/-- The agents of a first argument a thread holds. -/
def heldFT (N : Nat → Nat) (T : XThread Arith) : Nat := heldF N T.st

theorem step_first {N : Nat → Nat} {K : Nat} {M : XMach Arith} (hO : MachOk N K M) (t : Nat) :
    (M.step xsys t).2 + fcnt N (M.step xsys t).1.mem.agents +
        total (heldFT N) (M.step xsys t).1.ths ≤
      fcnt N M.mem.agents + total (heldFT N) M.ths := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    rw [es]
    show 0 + fcnt N M.mem.agents + total (heldFT N) M.ths ≤ _
    omega
  | some T =>
    have es := XMach.step_eq (M := M) (t := t) h (act_self M.mem T)
    have e1 : (M.step xsys t).2 = (XMach.act xsys M.mem T).2.2 := by rw [es]
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T).1 := by rw [es]
    rw [e1, e2, e3]
    have sh := total_set (heldFT N) M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_first hO.1 (hO.2 T (List.mem_of_getElem? h))
    have h1 : heldFT N T = heldF N T.st := rfl
    have h2 : heldFT N (XMach.act xsys M.mem T).2.1 = heldF N (XMach.act xsys M.mem T).2.1.st :=
      rfl
    omega

/-- **The claims of a run and the agents of the first arguments still
there are never more together than those agents at the start.** -/
theorem trace_first {N : Nat → Nat} {K : Nat} (σ : Nat → Nat) {M : XMach Arith}
    (hO : MachOk N K M) : ∀ i,
    (M.trace xsys σ i).2 + fcnt N (M.trace xsys σ i).1.mem.agents +
        total (heldFT N) (M.trace xsys σ i).1.ths ≤
      fcnt N M.mem.agents + total (heldFT N) M.ths
  | 0 => by
    show 0 + fcnt N M.mem.agents + total (heldFT N) M.ths ≤ _
    omega
  | i + 1 => by
    have ih := trace_first σ hO i
    have hs := step_first (trace_ok σ hO i) (σ i)
    show (M.trace xsys σ i).2 + ((M.trace xsys σ i).1.step xsys (σ i)).2 +
        fcnt N ((M.trace xsys σ i).1.step xsys (σ i)).1.mem.agents +
        total (heldFT N) ((M.trace xsys σ i).1.step xsys (σ i)).1.ths ≤ _
    omega

/-- The successors of second arguments at the front of a list, before its
first cell of the second net. -/
def pre (N : Nat → Nat) : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => if tagged 1 e.1 = true then 0 else (if isSnd N e.1 = true then 1 else 0) + pre N l

/-- Three for each of them, up to `3 * n`. -/
def g1 (N : Nat → Nat) (n : Nat) (l : List (Id × Arith)) : Nat := min (3 * pre N l) (3 * n)

theorem g1_cons (N : Nat → Nat) (n : Nat) (e : Id × Arith) (l : List (Id × Arith)) :
    g1 N n (e :: l) ≤ g1 N n l + (if isSnd N e.1 = true then 3 else 1) := by
  show min (3 * (if tagged 1 e.1 = true then 0
    else (if isSnd N e.1 = true then 1 else 0) + pre N l)) (3 * n) ≤
      min (3 * pre N l) (3 * n) + (if isSnd N e.1 = true then 3 else 1)
  by_cases ht : tagged 1 e.1 = true
  · rw [ite_pos' ht]
    omega
  · rw [ite_neg' ht]
    by_cases hs : isSnd N e.1 = true
    · rw [ite_pos' hs, ite_pos' hs]
      omega
    · rw [ite_neg' hs, ite_neg' hs]
      omega

theorem g1_head (N : Nat → Nat) (n : Nat) {e : Id × Arith} {l : List (Id × Arith)}
    (h : 0 < g1 N n (e :: l)) : tagged 1 e.1 = false := by
  cases ht : tagged 1 e.1 with
  | false => rfl
  | true =>
    have h' : 0 < min (3 * (if tagged 1 e.1 = true then 0
      else (if isSnd N e.1 = true then 1 else 0) + pre N l)) (3 * n) := h
    rw [ite_pos' ht] at h'
    omega

/-- In front of a cell of the second net, the count is that of all the
successors of second arguments before it. -/
theorem pre_front (N : Nat → Nat) {b : Id × Arith} (hb : tagged 1 b.1 = true)
    (W : List (Id × Arith)) : ∀ L : List (Id × Arith), (∀ e, e ∈ L → tagged 1 e.1 = false) →
      pre N (L ++ b :: W) = sndCnt N L
  | [], _ => by
    show (if tagged 1 b.1 = true then 0 else _) = 0
    rw [ite_pos' hb]
  | e :: L, h => by
    have ih := pre_front N hb W L (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he : ¬ tagged 1 e.1 = true := by
      rw [h e List.mem_cons_self]
      exact Bool.false_ne_true
    show (if tagged 1 e.1 = true then 0
      else (if isSnd N e.1 = true then 1 else 0) + pre N (L ++ b :: W)) =
        (if isSnd N e.1 = true then 1 else 0) + sndCnt N L
    rw [ite_neg' he, ih]

theorem tagged_zero_cons : ∀ {a : Id}, tagged 1 a = false → tagged 1 (0 :: a) = false
  | [], _ => rfl
  | _ :: _, h => h

theorem ids_add {Q : Id → Prop} {a s : Id} (qa : Q a) (qs : Q s) (q0a : Q (0 :: a))
    (q0s : Q (0 :: s)) {e : Port × Port}
    (he : e ∈ [((a, 1), (0 :: s, 1)), ((a, 2), (0 :: a, 0)), ((s, 1), (0 :: s, 0)),
      ((0 :: a, 0), (a, 2)), ((0 :: a, 1), (0 :: s, 2)), ((0 :: s, 0), (s, 1)),
      ((0 :: s, 1), (a, 1)), ((0 :: s, 2), (0 :: a, 1))]) : Q e.1.1 ∧ Q e.2.1 := by
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qa, q0s⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qa, q0a⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qs, q0s⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0a, qa⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0a, q0s⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0s, qs⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0s, qa⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0s, q0a⟩
  · cases he

theorem ids_swap {Q : Id → Prop} {a s : Id} (qa : Q a) (qs : Q s) (q0a : Q (0 :: a))
    (q0s : Q (0 :: s)) {e : Port × Port}
    (he : e ∈ [((s, 1), (0 :: s, 0)), ((a, 1), (0 :: s, 1)), ((a, 2), (0 :: a, 0)),
      ((0 :: a, 0), (a, 2)), ((0 :: a, 1), (0 :: s, 2)), ((0 :: s, 0), (s, 1)),
      ((0 :: s, 1), (a, 1)), ((0 :: s, 2), (0 :: a, 1))]) : Q e.1.1 ∧ Q e.2.1 := by
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qs, q0s⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qa, q0s⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qa, q0a⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0a, qa⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0a, q0s⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0s, qs⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0s, qa⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨q0s, q0a⟩
  · cases he

theorem ids_zero {Q : Id → Prop} {a : Id} (qa : Q a) {e : Port × Port}
    (he : e ∈ [((a, 1), (a, 2)), ((a, 2), (a, 1))]) : Q e.1.1 ∧ Q e.2.1 := by
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qa, qa⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨qa, qa⟩
  · cases he

theorem tags_az {a b : Id} (ta : tagged 1 a = false) :
    (∀ e, e ∈ addZero.toX.newAgents a b → tagged 1 e.1 = false) ∧
      (∀ e, e ∈ addZero.toX.newLinks ar a b .add .zero →
        tagged 1 e.1.1 = false ∧ tagged 1 e.2.1 = false) := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_zero] at he
    cases he
  · rw [newLinks_zero] at he
    exact ids_zero (Q := fun i => tagged 1 i = false) ta he

theorem tags_za {a b : Id} (tb : tagged 1 b = false) :
    (∀ e, e ∈ addZero.swap.toX.newAgents a b → tagged 1 e.1 = false) ∧
      (∀ e, e ∈ addZero.swap.toX.newLinks ar a b .zero .add →
        tagged 1 e.1.1 = false ∧ tagged 1 e.2.1 = false) := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_zero_swap] at he
    cases he
  · rw [newLinks_zero_swap] at he
    exact ids_zero (Q := fun i => tagged 1 i = false) tb he

theorem tags_as {a b : Id} (ta : tagged 1 a = false) (tb : tagged 1 b = false) (hne : a ≠ b) :
    (∀ e, e ∈ addSucc.toX.newAgents a b → tagged 1 e.1 = false) ∧
      (∀ e, e ∈ addSucc.toX.newLinks ar a b .add .succ →
        tagged 1 e.1.1 = false ∧ tagged 1 e.2.1 = false) := by
  have t0a := tagged_zero_cons ta
  have t0b := tagged_zero_cons tb
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_add hne] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact t0a
    rcases List.mem_cons.1 he with rfl | he
    · exact t0b
    · cases he
  · rw [newLinks_add] at he
    exact ids_add (Q := fun i => tagged 1 i = false) ta tb t0a t0b he

theorem tags_sa {a b : Id} (ta : tagged 1 a = false) (tb : tagged 1 b = false) (hne : a ≠ b) :
    (∀ e, e ∈ addSucc.swap.toX.newAgents a b → tagged 1 e.1 = false) ∧
      (∀ e, e ∈ addSucc.swap.toX.newLinks ar a b .succ .add →
        tagged 1 e.1.1 = false ∧ tagged 1 e.2.1 = false) := by
  have t0a := tagged_zero_cons ta
  have t0b := tagged_zero_cons tb
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [newAgents_swap (a := b) (s := a) (fun e => hne e.symm)] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact t0b
    rcases List.mem_cons.1 he with rfl | he
    · exact t0a
    · cases he
  · rw [newLinks_swap] at he
    exact ids_swap (Q := fun i => tagged 1 i = false) tb ta t0b t0a he

/-- **A rule on a pair of the first net writes cells of the first net
only.** -/
theorem rule_tags {α β : Arith} {R : XRhs Arith} {a b : Id} (hR : xsys.rule α β = some R)
    (hne : a ≠ b) (ta : tagged 1 a = false) (tb : tagged 1 b = false) :
    (∀ e, e ∈ R.newAgents a b → tagged 1 e.1 = false) ∧
      (∀ e, e ∈ R.newLinks xsys.sys.ar a b α β →
        tagged 1 e.1.1 = false ∧ tagged 1 e.2.1 = false) := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       exact tags_az ta)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       exact tags_za tb)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       exact tags_as ta tb hne)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       exact tags_sa ta tb hne)

/-- **A memory whose second net is untouched**: its cells `B0` are the
last of the agents, in place, with cells of the first net alone before
them, and no segment joins the two nets. -/
structure Mem1 (B0 : List (Id × Arith)) (X : XNet Arith) : Prop where
  shape : ∃ L, X.agents = L ++ B0 ∧ ∀ e, e ∈ L → tagged 1 e.1 = false
  wires : ∀ e, e ∈ X.wires → tagged 1 e.1.1 = tagged 1 e.2.1

/-- A thread that works in the first net. -/
def Guard : TState Arith → Prop
  | .idle => True
  | .look a _ => tagged 1 a = false
  | .seek a _ _ c => tagged 1 a = false ∧ tagged 1 c.1 = false
  | .ready a b _ _ => tagged 1 a = false ∧ tagged 1 b = false
  | .half a b _ _ => tagged 1 a = false ∧ tagged 1 b = false
  | .write as ls => (∀ e, e ∈ as → tagged 1 e.1 = false) ∧
      (∀ e, e ∈ ls → tagged 1 e.1.1 = false ∧ tagged 1 e.2.1 = false)

theorem Mem1.take {B0 : List (Id × Arith)} {X : XNet Arith} (h : Mem1 B0 X)
    (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true) {a : Id} (ta : tagged 1 a = false) :
    Mem1 B0 (X.takeAgent a) := by
  obtain ⟨L, hL, hL'⟩ := h.shape
  refine ⟨⟨L.filter (fun e => decide (e.1 ≠ a)), ?_, fun e he => hL' e (List.mem_filter.1 he).1⟩,
    h.wires⟩
  show X.agents.filter (fun e => decide (e.1 ≠ a)) = _
  rw [hL, List.filter_append]
  have hf : B0.filter (fun e => decide (e.1 ≠ a)) = B0 :=
    List.filter_eq_self.2 fun e he => decide_eq_true fun hea => by
      have h1 := hB e he
      rw [hea, ta] at h1
      cases h1
  rw [hf]

theorem Mem1.put {B0 : List (Id × Arith)} {X : XNet Arith} (h : Mem1 B0 X) {i : Id}
    (γ : Arith) (ti : tagged 1 i = false) : Mem1 B0 (X.putAgent i γ) := by
  obtain ⟨L, hL, hL'⟩ := h.shape
  refine ⟨⟨(i, γ) :: L, ?_, fun e he => ?_⟩, h.wires⟩
  · show (i, γ) :: X.agents = (i, γ) :: L ++ B0
    rw [hL]
    rfl
  · rcases List.mem_cons.1 he with rfl | he'
    · exact ti
    · exact hL' e he'

theorem Mem1.link {B0 : List (Id × Arith)} {X : XNet Arith} (h : Mem1 B0 X) {p q : Port}
    (tp : tagged 1 p.1 = false) (tq : tagged 1 q.1 = false) : Mem1 B0 (X.putLink p q) :=
  ⟨h.shape, fun e he => by
    rcases List.mem_cons.1 he with rfl | he'
    · show tagged 1 p.1 = tagged 1 q.1
      rw [tp, tq]
    · exact h.wires e he'⟩

/-- **A thread that works in the first net leaves the second
untouched**, when the entry it reads next, if it is to read one, is of
the first net. -/
theorem act_phase1 {B0 : List (Id × Arith)} {X : XNet Arith} {T : XThread Arith}
    (h1 : Mem1 B0 X) (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true) (hG : Guard T.st)
    (hhead : ∀ e rest, T.st = .idle → T.todo = e :: rest → tagged 1 e.1 = false) :
    Mem1 B0 (XMach.act xsys X T).1 ∧ Guard (XMach.act xsys X T).2.1.st := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨h1, trivial⟩
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        exact ⟨h1, hhead e rest rfl rfl⟩
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        exact ⟨h1, trivial⟩
  | look a α =>
    have ta : tagged 1 a = false := hG
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      exact ⟨h1, trivial⟩
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      have hw : tagged 1 a = tagged 1 q.1 := h1.wires _ (assoc_mem hq)
      exact ⟨h1, ta, by rw [← hw]; exact ta⟩
  | seek a α p q =>
    have hG' : tagged 1 a = false ∧ tagged 1 q.1 = false := hG
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        exact ⟨h1, trivial⟩
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        have hw : tagged 1 q.1 = tagged 1 q'.1 := h1.wires _ (nextSeg_spec hn).1
        exact ⟨h1, hG'.1, by rw [← hw]; exact hG'.2⟩
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        exact ⟨h1, hG'⟩
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        exact ⟨h1, trivial⟩
  | ready a b α β =>
    have hG' : tagged 1 a = false ∧ tagged 1 b = false := hG
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact ⟨h1.take hB hG'.1, hG'⟩
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      exact ⟨h1, trivial⟩
  | half a b α β =>
    have hG' : tagged 1 a = false ∧ tagged 1 b = false := hG
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact ⟨h1.put α hG'.1, trivial⟩
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        exact ⟨h1.take hB hG'.2, rule_tags hR hc.2 hG'.1 hG'.2⟩
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      exact ⟨h1.put α hG'.1, trivial⟩
  | write as ls =>
    have hG' : (∀ e, e ∈ as → tagged 1 e.1 = false) ∧
        (∀ e, e ∈ ls → tagged 1 e.1.1 = false ∧ tagged 1 e.2.1 = false) := hG
    obtain ⟨hA, hL⟩ := hG'
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨h1.put γ (hA (i, γ) List.mem_cons_self),
        fun e he => hA e (List.mem_cons_of_mem _ he), hL⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨h1.link (hL (p, q) List.mem_cons_self).1 (hL (p, q) List.mem_cons_self).2,
          hA, fun e he => hL e (List.mem_cons_of_mem _ he)⟩
      | nil => exact ⟨h1, trivial⟩

/-- **The first stretch of threads in turn**, after `i` actions: the
second net is untouched, every thread works in the first net, and each
thread has, with the actions it has made, still three to make for each
of the `n` successors of the second argument of the first net before it
comes to a cell of the second. -/
structure Ph1 (N : Nat → Nat) (n : Nat) (B0 : List (Id × Arith)) (c i : Nat)
    (M : XMach Arith) : Prop where
  mem : Mem1 B0 M.mem
  guard : ∀ T, T ∈ M.ths → Guard T.st
  pot : ∀ t T, t < c → M.ths[t]? = some T →
    3 * n ≤ lam N (g1 N n) (3 * n) T + (i / c + (if t < i % c then 1 else 0))

theorem mem1_pre {N : Nat → Nat} {K n : Nat} {B0 : List (Id × Arith)} {X : XNet Arith}
    (hO : MemOk N K X) (h1 : Mem1 B0 X) (hb : ∃ b W, B0 = b :: W ∧ tagged 1 b.1 = true)
    (hB0 : n + sndCnt N B0 ≤ K) : n ≤ pre N X.agents := by
  obtain ⟨L, hL, hL'⟩ := h1.shape
  obtain ⟨b, W, rfl, tb⟩ := hb
  have hc := hO.count
  rw [hL, sndCnt_append] at hc
  rw [hL, pre_front N tb W L hL']
  omega

theorem ph1_step {N : Nat → Nat} {K n : Nat} {B0 : List (Id × Arith)} {c i : Nat}
    {M : XMach Arith} (hc : 0 < c) (hlen : M.ths.length = c) (hO : MachOk N K M)
    (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true)
    (hb : ∃ b W, B0 = b :: W ∧ tagged 1 b.1 = true) (hB0 : n + sndCnt N B0 ≤ K)
    (h : Ph1 N n B0 c i M) (hi : i / c < 3 * n) :
    Ph1 N n B0 c (i + 1) (M.step xsys (i % c)).1 := by
  have hk := Nat.mod_lt i hc
  have hR : 3 * n ≤ g1 N n M.mem.agents := by
    have hp := mem1_pre hO.1 h.mem hb hB0
    show 3 * n ≤ min (3 * pre N M.mem.agents) (3 * n)
    omega
  have hdrop : ∀ T0, M.ths[i % c]? = some T0 →
      lam N (g1 N n) (3 * n) T0 ≤
        lam N (g1 N n) (3 * n) (XMach.act xsys M.mem T0).2.1 + 1 :=
    fun T0 h0 => act_lam (g1 N n) (3 * n) hO.1 (hO.2 T0 (List.mem_of_getElem? h0))
      (g1_cons N n) (fun l => Nat.min_le_right _ _) hR
  cases h0 : M.ths[i % c]? with
  | none =>
    have hle := List.getElem?_eq_none_iff.1 h0
    omega
  | some T0 =>
    have es := XMach.step_eq (M := M) (t := i % c) h0 (act_self M.mem T0)
    have e2 : (M.step xsys (i % c)).1.ths =
        M.ths.set (i % c) (XMach.act xsys M.mem T0).2.1 := by rw [es]
    have e3 : (M.step xsys (i % c)).1.mem = (XMach.act xsys M.mem T0).1 := by rw [es]
    have hp0 := h.pot (i % c) T0 hk h0
    rw [ite_neg' (Nat.lt_irrefl _)] at hp0
    have hg0 := h.guard T0 (List.mem_of_getElem? h0)
    have hhead : ∀ e rest, T0.st = .idle → T0.todo = e :: rest → tagged 1 e.1 = false := by
      intro e rest hst htd
      obtain ⟨todo, st⟩ := T0
      have hst' : st = .idle := hst
      have htd' : todo = e :: rest := htd
      subst hst'
      subst htd'
      have hp0' : 3 * n ≤ g1 N n (e :: rest) + 0 + i / c := hp0
      have hpos : 0 < g1 N n (e :: rest) := by omega
      exact g1_head N n hpos
    have ha := act_phase1 h.mem hB hg0 hhead
    refine ⟨?_, fun T hT => ?_, fun t T' ht hT' => ?_⟩
    · rw [e3]
      exact ha.1
    · rw [e2] at hT
      rcases List.mem_or_eq_of_mem_set hT with h1 | h1
      · exact h.guard T h1
      · rw [h1]
        exact ha.2
    · cases hTo : M.ths[t]? with
      | none =>
        have hle := List.getElem?_eq_none_iff.1 hTo
        omega
      | some T =>
        obtain ⟨T'', hT'', hin⟩ := rr_step (lam N (g1 N n) (3 * n)) hc hlen i hdrop ht hTo
        rw [hT''] at hT'
        cases hT'
        have hp := h.pot t T ht hTo
        omega

/-- **Nothing of the second net is touched in the first `3 * n`
rounds.**  From a memory in order whose second net is in place, when each
thread starts with the `n` successors of the second argument of the first
net before the cells of the second: with `c` threads in turn, after any
number of actions up to `c * (3 * n)`, the cells of the second net are
all in memory, in place, and every thread works in the first net. -/
theorem phase1 {N : Nat → Nat} {K n : Nat} {B0 : List (Id × Arith)} {c : Nat} {X : XNet Arith}
    (hc : 0 < c) (hO : MemOk N K X) (h1 : Mem1 B0 X) (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true)
    (hb : ∃ b W, B0 = b :: W ∧ tagged 1 b.1 = true) (hB0 : n + sndCnt N B0 ≤ K)
    (hinit : ∀ t, t < c → n ≤ pre N (X.agents.drop t ++ X.agents.take t)) :
    ∀ i, i ≤ c * (3 * n) →
      Ph1 N n B0 c i ((XMach.init X c).trace xsys (fun i => i % c) i).1
  | 0, _ => by
    refine ⟨h1, fun T hT => ?_, fun t T ht hT => ?_⟩
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      exact trivial
    · have e : (XMach.init X c).ths[t]? =
          some ⟨X.agents.drop t ++ X.agents.take t, .idle⟩ := by
        show ((List.range c).map _)[t]? = _
        rw [List.getElem?_map, List.getElem?_range ht]
        rfl
      have hT' : (XMach.init X c).ths[t]? = some T := hT
      rw [e] at hT'
      cases hT'
      have hi := hinit t ht
      have h3 : 3 * n ≤ min (3 * pre N (X.agents.drop t ++ X.agents.take t)) (3 * n) + 0 := by
        omega
      exact Nat.le_trans h3 (Nat.le_add_right _ _)
  | i + 1, hi => by
    have ih := phase1 hc hO h1 hB hb hB0 hinit i (by omega)
    have hlen : ((XMach.init X c).trace xsys (fun i => i % c) i).1.ths.length = c :=
      (XMach.trace_length xsys _ _ i).trans (init_length X c)
    exact ph1_step hc hlen (trace_ok _ (init_ok hO c) i) hB hb hB0 ih
      (Nat.div_lt_of_lt_mul (by omega))

/-- What a list has still to cost a thread: one for each entry up to `B`,
and two more for each successor of a second argument up to `K`. -/
def g2 (N : Nat → Nat) (B K : Nat) (l : List (Id × Arith)) : Nat :=
  min l.length B + 2 * min (sndCnt N l) K

theorem g2_cons (N : Nat → Nat) (B K : Nat) (e : Id × Arith) (l : List (Id × Arith)) :
    g2 N B K (e :: l) ≤ g2 N B K l + (if isSnd N e.1 = true then 3 else 1) := by
  show min (l.length + 1) B + 2 * min ((if isSnd N e.1 = true then 1 else 0) + sndCnt N l) K ≤
    min l.length B + 2 * min (sndCnt N l) K + (if isSnd N e.1 = true then 3 else 1)
  by_cases hs : isSnd N e.1 = true
  · rw [ite_pos' hs, ite_pos' hs]
    omega
  · rw [ite_neg' hs, ite_neg' hs]
    omega

theorem g2_le (N : Nat → Nat) (B K : Nat) (l : List (Id × Arith)) : g2 N B K l ≤ B + 2 * K := by
  show min l.length B + 2 * min (sndCnt N l) K ≤ B + 2 * K
  omega

/-- **A thread that has just claimed has the reload and `G` before it.** -/
theorem act_claim_lam (N : Nat → Nat) (g : List (Id × Arith) → Nat) (G : Nat) (X : XNet Arith)
    (T : XThread Arith) (h : 0 < (XMach.act xsys X T).2.2) :
    1 + G ≤ lam N g G (XMach.act xsys X T).2.1 := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact absurd h (Nat.lt_irrefl 0)
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha] at h
        exact absurd h (Nat.lt_irrefl 0)
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha] at h
        exact absurd h (Nat.lt_irrefl 0)
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq] at h
      exact absurd h (Nat.lt_irrefl 0)
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq] at h
      exact absurd h (Nat.lt_irrefl 0)
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn] at h
        exact absurd h (Nat.lt_irrefl 0)
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn] at h
        exact absurd h (Nat.lt_irrefl 0)
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr] at h
        exact absurd h (Nat.lt_irrefl 0)
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr] at h
        exact absurd h (Nat.lt_irrefl 0)
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha] at h
      exact absurd h (Nat.lt_irrefl 0)
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha] at h
      exact absurd h (Nat.lt_irrefl 0)
  | half a b α β =>
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)] at h
        exact absurd h (Nat.lt_irrefl 0)
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show 1 + G ≤
          (R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length + 1 + G
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)] at h
      exact absurd h (Nat.lt_irrefl 0)
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact absurd h (Nat.lt_irrefl 0)
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact absurd h (Nat.lt_irrefl 0)
      | nil => exact absurd h (Nat.lt_irrefl 0)

theorem claims_mono (σ : Nat → Nat) (M : XMach Arith) : ∀ d i,
    (M.trace xsys σ i).2 ≤ (M.trace xsys σ (i + d)).2
  | 0, _ => Nat.le_refl _
  | d + 1, i => by
    have ih := claims_mono σ M d i
    show _ ≤ (M.trace xsys σ (i + d)).2 + ((M.trace xsys σ (i + d)).1.step xsys (σ (i + d))).2
    omega

/-- When the claims have grown, some action in between has claimed. -/
theorem claim_between (σ : Nat → Nat) (M : XMach Arith) : ∀ d i,
    (M.trace xsys σ i).2 < (M.trace xsys σ (i + d)).2 →
      ∃ j, i ≤ j ∧ j < i + d ∧ 0 < ((M.trace xsys σ j).1.step xsys (σ j)).2
  | 0, _, h => absurd h (Nat.lt_irrefl _)
  | d + 1, i, h => by
    have h' : (M.trace xsys σ i).2 <
        (M.trace xsys σ (i + d)).2 + ((M.trace xsys σ (i + d)).1.step xsys (σ (i + d))).2 := h
    by_cases hs : 0 < ((M.trace xsys σ (i + d)).1.step xsys (σ (i + d))).2
    · exact ⟨i + d, by omega, by omega, hs⟩
    · obtain ⟨j, h1, h2, h3⟩ := claim_between σ M d i (by omega)
      exact ⟨j, h1, by omega, h3⟩

/-- The memory of a run never has fewer agents than the net has
successors less the number of threads. -/
theorem trace_agents_ge {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    succs X.agents - nt ≤ ((XMach.init X nt).trace xsys σ i).1.mem.agents.length := by
  obtain ⟨ha, hb, -⟩ := trace_read hX hnd hnt σ i
  have hlen : ((XMach.init X nt).trace xsys σ i).1.ths.length = nt :=
    (XMach.trace_length xsys σ _ i).trans (init_length X nt)
  have hle := total_le_mul (f := held) (P := 1) ha
  have hsl := succs_le_length ((XMach.init X nt).trace xsys σ i).1.mem.agents
  rw [hlen] at hle
  omega

/-- **Threads in turn, seen from each thread, over any stretch of a
run**: what a thread has still to do and the number of its own actions
are together never less than they were. -/
theorem rr_track {N : Nat → Nat} {K : Nat} {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) (hO : MemOk N K X) {c : Nat} (hc : 0 < c) :
    ∀ d i t T, t < c → ((XMach.init X c).trace xsys (fun i => i % c) i).1.ths[t]? = some T →
      ∃ T', ((XMach.init X c).trace xsys (fun i => i % c) (i + d)).1.ths[t]? = some T' ∧
        lam N (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K) T +
            (i / c + (if t < i % c then 1 else 0)) ≤
          lam N (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K) T' +
            ((i + d) / c + (if t < (i + d) % c then 1 else 0))
  | 0, _, _, T, _, hT => ⟨T, hT, Nat.le_refl _⟩
  | d + 1, i, t, T, ht, hT => by
    obtain ⟨T1, hT1, h1⟩ := rr_track hX hnd hO hc d i t T ht hT
    have hOk := trace_ok (fun i => i % c) (init_ok hO c) (i + d)
    have hlen : ((XMach.init X c).trace xsys (fun i => i % c) (i + d)).1.ths.length = c :=
      (XMach.trace_length xsys _ _ (i + d)).trans (init_length X c)
    have hB := trace_agents_ge hX hnd hc (fun i => i % c) (i + d)
    have hK := hOk.1.count
    have hR : succs X.agents - c + 2 * K ≤ g2 N (succs X.agents - c) K
        ((XMach.init X c).trace xsys (fun i => i % c) (i + d)).1.mem.agents := by
      show _ ≤ min _ (succs X.agents - c) + 2 * min (sndCnt N _) K
      omega
    obtain ⟨T', hT', h2⟩ := rr_step
      (lam N (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K)) hc hlen (i + d)
      (fun T0 h0 => act_lam (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K) hOk.1
        (hOk.2 T0 (List.mem_of_getElem? h0)) (g2_cons N _ K) (g2_le N _ K) hR) ht hT1
    exact ⟨T', hT', Nat.le_trans h1 h2⟩

/-- **The limit with the first net read twice.**  From a memory in order
whose second net `B0` is in place, with each of `c` threads in turn
starting before the `n` successors of the second argument of the first
net: nothing of the second net is touched in the first `3 * n` rounds;
if every run at rest has made `C` claims and the first net has fewer than
`C` agents for an adder to meet, some thread claims after those rounds,
and has then the reload and the whole memory to read before it rests. -/
theorem late_floor {N : Nat → Nat} {K n : Nat} {B0 : List (Id × Arith)} {c : Nat}
    {X : XNet Arith} (hc : 0 < c) (hX : X.toNet.WF ar) (hnd : (X.agents.map Prod.fst).Nodup)
    (hO : MemOk N K X) (h1 : Mem1 B0 X) (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true)
    (hb : ∃ b W, B0 = b :: W ∧ tagged 1 b.1 = true) (hB0 : n + sndCnt N B0 ≤ K)
    (hinit : ∀ t, t < c → n ≤ pre N (X.agents.drop t ++ X.agents.take t)) {C R : Nat}
    (hF : fcnt N X.agents < fcnt N B0 + C)
    (hr : ((XMach.init X c).trace xsys (fun i => i % c) (c * R)).1.resting = true)
    (hC : ((XMach.init X c).trace xsys (fun i => i % c) (c * R)).2 = C) :
    3 * n + 2 + (succs X.agents - c) + 2 * K ≤ R := by
  -- the claims of the first `3 * n` rounds
  have P := phase1 hc hO h1 hB hb hB0 hinit (c * (3 * n)) (Nat.le_refl _)
  have F := trace_first (fun i => i % c) (init_ok hO c) (c * (3 * n))
  have z := total_init (heldFT N) (fun _ => rfl) X c
  obtain ⟨L, hL, -⟩ := P.mem.shape
  have e0 : (XMach.init X c).mem = X := rfl
  rw [z, e0, hL, fcnt_append] at F
  -- a claim after them
  have hlt : c * (3 * n) < c * R := by
    refine Nat.lt_of_not_le fun hle => ?_
    obtain ⟨d, hd⟩ : ∃ d, c * (3 * n) = c * R + d := ⟨c * (3 * n) - c * R, by omega⟩
    have hm := claims_mono (fun i => i % c) (XMach.init X c) d (c * R)
    rw [← hd, hC] at hm
    omega
  obtain ⟨d, hd⟩ : ∃ d, c * R = c * (3 * n) + d := ⟨c * R - c * (3 * n), by omega⟩
  have hgrow : ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n))).2 <
      ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n) + d)).2 := by
    rw [← hd, hC]
    omega
  obtain ⟨j, hj1, hj2, hj3⟩ := claim_between (fun i => i % c) (XMach.init X c) d _ hgrow
  -- the thread that makes it
  have hk := Nat.mod_lt j hc
  have hlen : ((XMach.init X c).trace xsys (fun i => i % c) j).1.ths.length = c :=
    (XMach.trace_length xsys _ _ j).trans (init_length X c)
  cases h0 : ((XMach.init X c).trace xsys (fun i => i % c) j).1.ths[j % c]? with
  | none =>
    have hle := List.getElem?_eq_none_iff.1 h0
    omega
  | some T0 =>
    have es := XMach.step_eq (M := ((XMach.init X c).trace xsys (fun i => i % c) j).1)
      (t := j % c) h0 (act_self _ T0)
    have hj3' : 0 < (((XMach.init X c).trace xsys (fun i => i % c) j).1.step xsys (j % c)).2 :=
      hj3
    rw [es] at hj3'
    have hcl := act_claim_lam N (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K) _ T0
      hj3'
    have hT1 : ((XMach.init X c).trace xsys (fun i => i % c) (j + 1)).1.ths[j % c]? =
        some (XMach.act xsys ((XMach.init X c).trace xsys (fun i => i % c) j).1.mem T0).2.1 := by
      show (((XMach.init X c).trace xsys (fun i => i % c) j).1.step xsys (j % c)).1.ths[j % c]? = _
      rw [es]
      exact List.getElem?_set_self (by omega)
    -- its own actions from there to the rest
    obtain ⟨d', hd'⟩ : ∃ d', c * R = j + 1 + d' := ⟨c * R - (j + 1), by omega⟩
    obtain ⟨T', hT', hin⟩ := rr_track hX hnd hO hc d' (j + 1) (j % c) _ hk hT1
    rw [← hd'] at hT' hin
    have hrest : T' = ⟨[], .idle⟩ :=
      XThread.eq_rest (List.all_eq_true.1 hr T' (List.mem_of_getElem? hT'))
    have hl0 : lam N (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K) T' = 0 := by
      rw [hrest]
      show min 0 _ + 2 * min 0 K + 0 = 0
      rw [Nat.zero_min, Nat.zero_min]
    have ho := rr_own c j (j % c) hc hk
    rw [ite_neg' (Nat.lt_irrefl _), ite_pos' rfl] at ho
    rw [hl0, ho, Nat.mul_div_cancel_left R hc, Nat.mul_mod_right,
      ite_neg' (Nat.not_lt_zero _)] at hin
    have hjc : 3 * n ≤ j / c := (Nat.le_div_iff_mul_le hc).2 (by
      rw [Nat.mul_comm]
      exact hj1)
    omega

theorem chainL_sndCnt (N : Nat → Nat) (c n : Nat) (hN : N c = n) : ∀ r,
    sndCnt N ((chainL n r).map (tagA c)) = 0
  | 0 => rfl
  | r + 1 => by
    have ih := chainL_sndCnt N c n hN r
    have hs : isSnd N [n + 3 + r + 1, c] = false := decide_eq_false (by omega)
    show (if isSnd N [n + 3 + r + 1, c] = true then 1 else 0) +
      sndCnt N ((chainL n r).map (tagA c)) = 0
    rw [hs, ih]
    rfl

theorem base_sndCnt (N : Nat → Nat) (c : Nat) : sndCnt N (base.agents.map (tagA c)) = 0 := by
  have h1 : isSnd N [1, c] = false := decide_eq_false (by omega)
  have h2 : isSnd N [2, c] = false := decide_eq_false (by omega)
  have h3 : isSnd N [3, c] = false := decide_eq_false (by omega)
  show (if isSnd N [1, c] = true then 1 else 0) + ((if isSnd N [2, c] = true then 1 else 0) +
    ((if isSnd N [3, c] = true then 1 else 0) + 0)) = 0
  rw [h1, h2, h3]
  rfl

/-- An addition has exactly the successors of its second argument. -/
theorem sum_sndCnt_le (N : Nat → Nat) (c n : Nat) (hN : N c = n) (M : Nat) :
    sndCnt N ((sum M n).agents.map (tagA c)) ≤ n := by
  rw [sum_agents, List.map_append, List.map_append, sndCnt_append, sndCnt_append,
    chainL_sndCnt N c n hN, sndL_sndCnt N c n (by omega), base_sndCnt]
  omega

theorem fcnt_le_length (N : Nat → Nat) : ∀ l : List (Id × Arith), fcnt N l ≤ l.length
  | [] => Nat.le_refl 0
  | e :: l => by
    have ih := fcnt_le_length N l
    show (if isF N e.1 = true then 1 else 0) + fcnt N l ≤ l.length + 1
    split <;> omega

theorem sndL_fcnt (N : Nat → Nat) (c : Nat) : ∀ k, k ≤ N c →
    fcnt N ((sndL k).map (tagA c)) = 0
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := sndL_fcnt N c k (by omega)
    have hs : isF N [k + 4, c] = false := decide_eq_false (by omega)
    show (if isF N [k + 4, c] = true then 1 else 0) + fcnt N ((sndL k).map (tagA c)) = 0
    rw [hs, ih]
    rfl

theorem base_fcnt (N : Nat → Nat) (c : Nat) : fcnt N (base.agents.map (tagA c)) = 1 := by
  have h1 : isF N [1, c] = false := decide_eq_false (by omega)
  have h2 : isF N [2, c] = true := decide_eq_true (.inl rfl)
  have h3 : isF N [3, c] = false := decide_eq_false (by omega)
  show (if isF N [1, c] = true then 1 else 0) + ((if isF N [2, c] = true then 1 else 0) +
    ((if isF N [3, c] = true then 1 else 0) + 0)) = 1
  rw [h1, h2, h3]
  rfl

/-- An addition with `M` successors in its first argument has `M + 1`
agents for an adder to meet, at most. -/
theorem sum_fcnt_le (N : Nat → Nat) (c n : Nat) (hN : N c = n) (M : Nat) :
    fcnt N ((sum M n).agents.map (tagA c)) ≤ M + 1 := by
  rw [sum_agents, List.map_append, List.map_append, fcnt_append, fcnt_append,
    sndL_fcnt N c n (by omega), base_fcnt]
  have h := fcnt_le_length N ((chainL n M).map (tagA c))
  rw [List.length_map, chainL_length] at h
  omega

/-- **Two additions side by side: the second is in place**, after the
cells of the first, and no segment joins them. -/
theorem two_sums_mem1 (m n m' n' : Nat) :
    Mem1 ((sum (m' + 1) n').agents.map (tagA 1)) (twoSums (m + 1) n (m' + 1) n') where
  shape := ⟨(sum (m + 1) n).agents.map (tagA 0), rfl, fun _ he => mem_tag_other (by decide) he⟩
  wires := fun e he => by
    have he' : e ∈ (sum (m + 1) n).wires.map (tagL 0) ++
        (sum (m' + 1) n').wires.map (tagL 1) := he
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
      show tagged 1 (x.1.1 ++ [0]) = tagged 1 (x.2.1 ++ [0])
      rw [tagged_append, tagged_append]
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
      show tagged 1 (x.1.1 ++ [1]) = tagged 1 (x.2.1 ++ [1])
      rw [tagged_append, tagged_append]

theorem two_sums_b0 (m' n' : Nat) :
    ∃ b W, (sum (m' + 1) n').agents.map (tagA 1) = b :: W ∧ tagged 1 b.1 = true := by
  obtain ⟨restB, hBa⟩ := (sum_start m' n').head
  exact ⟨tagA 1 ([n' + 3 + m' + 1], Arith.succ), restB.map (tagA 1), by
    rw [hBa]
    rfl, tagged_self 1 _⟩

theorem two_sums_b0_cnt (n m' n' : Nat) :
    n + sndCnt (sideN n n') ((sum (m' + 1) n').agents.map (tagA 1)) ≤ n + n' := by
  have h := sum_sndCnt_le (sideN n n') 1 n' rfl (m' + 1)
  omega

/-- A thread numbered `m + 1` or less starts with the `n` successors of
the second argument of the first addition before the cells of the
second. -/
theorem two_sums_init_pre (m n m' n' : Nat) {t : Nat} (ht : t ≤ m + 1) :
    n ≤ pre (sideN n n') ((twoSums (m + 1) n (m' + 1) n').agents.drop t ++
      (twoSums (m + 1) n (m' + 1) n').agents.take t) := by
  obtain ⟨restB, hBa⟩ := (sum_start m' n').head
  have eA : (twoSums (m + 1) n (m' + 1) n').agents =
      (chainL n (m + 1)).map (tagA 0) ++ ((sndL n ++ base.agents).map (tagA 0) ++
        (tagA 1 ([n' + 3 + m' + 1], Arith.succ) :: restB.map (tagA 1))) := by
    show (sum (m + 1) n).agents.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1) = _
    rw [sum_agents, hBa, List.map_append, List.append_assoc]
    rfl
  have e2 : ∀ (D S W Tk : List (Id × Arith)) (b : Id × Arith),
      D ++ (S ++ b :: W) ++ Tk = (D ++ S) ++ b :: (W ++ Tk) := by
    intro D S W Tk b
    simp
  have hL : ∀ e, e ∈ ((chainL n (m + 1)).map (tagA 0)).drop t ++
      (sndL n ++ base.agents).map (tagA 0) → tagged 1 e.1 = false := fun e he => by
    rcases List.mem_append.1 he with h | h
    · exact mem_tag_other (by decide) (List.mem_of_mem_drop h)
    · exact mem_tag_other (by decide) h
  rw [eA, List.drop_append_of_le_length (by
    rw [List.length_map, chainL_length]
    exact ht), e2, pre_front (sideN n n') (tagged_self 1 _) _ _ hL, sndCnt_append,
    List.map_append, sndCnt_append, sndL_sndCnt (sideN n n') 0 n (Nat.le_refl n)]
  omega

/-- **Nothing of the second addition is touched in the first `3 * n`
rounds.**  With `c` threads in turn, `c` at most `m + 2`, on
`(m + 1) + n` beside `(m' + 1) + n'`: after any number of actions up to
`c * (3 * n)` the cells of the second addition are all in memory, in
place, after cells of the first alone. -/
theorem two_sums_untouched (m n m' n' : Nat) {c : Nat} (hc : 0 < c) (hcm : c ≤ m + 2) {i : Nat}
    (hi : i ≤ c * (3 * n)) :
    ∃ L, ((XMach.init (twoSums (m + 1) n (m' + 1) n') c).trace xsys (fun i => i % c)
          i).1.mem.agents = L ++ (sum (m' + 1) n').agents.map (tagA 1) ∧
      ∀ e, e ∈ L → tagged 1 e.1 = false :=
  (phase1 (n := n) hc (two_sums_memOk m n m' n') (two_sums_mem1 m n m' n')
    (fun _ he => mem_tag_self he) (two_sums_b0 m' n') (two_sums_b0_cnt n m' n')
    (fun _ ht => two_sums_init_pre m n m' n' (by omega)) i hi).mem.shape

/-- **The limit with the first addition read twice.**  With `c` threads
in turn, `c` at most `m + 2`, on two additions side by side: the rounds
to rest and the threads together are at least
`6 * n + 3 * n' + m + m' + 4`.  Some thread claims after the first
`3 * n` rounds, and then reloads and reads the whole memory. -/
theorem two_sums_rounds_late (m n m' n' : Nat) {c R : Nat} (hc : 0 < c) (hcm : c ≤ m + 2)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    6 * n + 3 * n' + m + m' + 4 ≤ R + c := by
  have hr := h.1
  have hC := two_sums_claims m n m' n' hc (fun i => i % c) hr
  have hF : fcnt (sideN n n') (twoSums (m + 1) n (m' + 1) n').agents <
      fcnt (sideN n n') ((sum (m' + 1) n').agents.map (tagA 1)) + (m + m' + 4) := by
    show fcnt (sideN n n') ((sum (m + 1) n).agents.map (tagA 0) ++
      (sum (m' + 1) n').agents.map (tagA 1)) < _
    rw [fcnt_append]
    have h1 := sum_fcnt_le (sideN n n') 0 n rfl (m + 1)
    omega
  have hl := late_floor (n := n) hc (two_sums_wf (m + 1) n (m' + 1) n')
    (two_sums_nodup (m + 1) n (m' + 1) n') (two_sums_memOk m n m' n') (two_sums_mem1 m n m' n')
    (fun _ he => mem_tag_self he) (two_sums_b0 m' n') (two_sums_b0_cnt n m' n')
    (fun _ ht => two_sums_init_pre m n m' n' (by omega)) hF hr hC
  rw [succs_two_sums] at hl
  omega

/-- `6 + 32` twice: two threads take 489 rounds and cannot take fewer
than 300. -/
theorem Checks.Arith.Late.c1
    {R : Nat} (h : Rounds 2 (XMach.init (twoSums 6 32 6 32) 2) R) : 300 ≤ R := by
  have h' := two_sums_rounds_late 5 32 5 32 (by decide) (by decide) h
  omega

/-- `6 + 200` twice: two threads take 2,001 rounds, and cannot take fewer
than 1,812. -/
theorem Checks.Arith.Late.c2 : Rounds 2 (XMach.init (twoSums 6 200 6 200) 2) 2001 :=
  (twice_family 5 200 (by decide)).2.cast (by decide)

theorem Checks.Arith.Late.c3
    {R : Nat} (h : Rounds 2 (XMach.init (twoSums 6 200 6 200) 2) R) : 1812 ≤ R := by
  have h' := two_sums_rounds_late 5 200 5 200 (by decide) (by decide) h
  omega

/-- **What a rule of the addition writes**: ten cells at most, and no
more adders than it takes. -/
theorem rule_sizes {α β : Arith} {R : XRhs Arith} (hR : xsys.rule α β = some R) {a b : Id}
    (hne : a ≠ b) :
    (R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length ≤ 10 ∧
      adders (R.newAgents a b) ≤ isAdd α + isAdd β := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       show (addZero.toX.newAgents a b).length +
           (addZero.toX.newLinks ar a b .add .zero).length ≤ 10 ∧
         adders (addZero.toX.newAgents a b) ≤ isAdd .add + isAdd .zero
       rw [newAgents_zero, newLinks_zero]
       exact ⟨(by omega : (2 : Nat) ≤ 10), Nat.zero_le _⟩)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       show (addZero.swap.toX.newAgents a b).length +
           (addZero.swap.toX.newLinks ar a b .zero .add).length ≤ 10 ∧
         adders (addZero.swap.toX.newAgents a b) ≤ isAdd .zero + isAdd .add
       rw [newAgents_zero_swap, newLinks_zero_swap]
       exact ⟨(by omega : (2 : Nat) ≤ 10), Nat.zero_le _⟩)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       show (addSucc.toX.newAgents a b).length +
           (addSucc.toX.newLinks ar a b .add .succ).length ≤ 10 ∧
         adders (addSucc.toX.newAgents a b) ≤ isAdd .add + isAdd .succ
       rw [newAgents_add hne, newLinks_add]
       exact ⟨Nat.le_refl 10, Nat.le_refl 1⟩)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       show (addSucc.swap.toX.newAgents a b).length +
           (addSucc.swap.toX.newLinks ar a b .succ .add).length ≤ 10 ∧
         adders (addSucc.swap.toX.newAgents a b) ≤ isAdd .succ + isAdd .add
       rw [newAgents_swap (a := b) (s := a) (fun e => hne e.symm), newLinks_swap]
       exact ⟨Nat.le_refl 10, Nat.le_refl 1⟩)

/-- **A thread never owes more than eleven actions, and no action makes
an adder.** -/
theorem act_bnd (X : XNet Arith) (T : XThread Arith) (h : owed T.st ≤ 11) :
    owed (XMach.act xsys X T).2.1.st ≤ 11 ∧
      adders (XMach.act xsys X T).1.agents + heldAdd (XMach.act xsys X T).2.1.st ≤
        adders X.agents + heldAdd T.st := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
      omega
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
      omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
      omega
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      have ht : adders (X.takeAgent a).agents + isAdd α ≤ adders X.agents := adders_take ha
      show 0 ≤ 11 ∧ adders (X.takeAgent a).agents + isAdd α ≤ adders X.agents + 0
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
      omega
  | half a b α β =>
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none =>
        rw [XMach.act_half_none (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        show 0 ≤ 11 ∧ isAdd α + adders X.agents + 0 ≤ adders X.agents + isAdd α
        omega
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have ht : adders (X.takeAgent b).agents + isAdd β ≤ adders X.agents := adders_take hc.1
        obtain ⟨r1, r2⟩ := rule_sizes hR hc.2
        show (R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length + 1 ≤ 11 ∧
          adders (X.takeAgent b).agents + adders (R.newAgents a b) ≤
            adders X.agents + isAdd α
        omega
    · rw [XMach.act_half_none (xs := xsys) (todo := todo) (ite_neg' hc)]
      show 0 ≤ 11 ∧ isAdd α + adders X.agents + 0 ≤ adders X.agents + isAdd α
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have h' : as.length + 1 + ls.length + 1 ≤ 11 := h
      show as.length + ls.length + 1 ≤ 11 ∧
        isAdd γ + adders X.agents + adders as ≤ adders X.agents + (isAdd γ + adders as)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have h' : 0 + (ls.length + 1) + 1 ≤ 11 := h
        show 0 + ls.length + 1 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega
      | nil =>
        show 0 ≤ 11 ∧ adders X.agents + 0 ≤ adders X.agents + 0
        omega

/-- The adders a thread holds. -/
def heldAddT (T : XThread Arith) : Nat := heldAdd T.st

/-- What a thread has put toward a claim. -/
def creditT (T : XThread Arith) : Nat := credit T.st

theorem credit_le : ∀ st : TState Arith, credit st ≤ 4
  | .idle => Nat.zero_le 4
  | .look _ _ => (by omega : (1 : Nat) ≤ 4)
  | .seek _ _ _ _ => (by omega : (2 : Nat) ≤ 4)
  | .ready _ _ _ _ => (by omega : (3 : Nat) ≤ 4)
  | .half _ _ _ _ => Nat.le_refl 4
  | .write _ _ => Nat.zero_le 4

theorem total_paid : ∀ ths : List (XThread Arith),
    total paid ths = total creditT ths + 8 * total heldAddT ths
  | [] => rfl
  | T :: ths => by
    have ih := total_paid ths
    show credit T.st + 8 * heldAdd T.st + total paid ths =
      credit T.st + total creditT ths + 8 * (heldAdd T.st + total heldAddT ths)
    omega

theorem step_bnd (M : XMach Arith) (t : Nat) (h : ∀ T, T ∈ M.ths → due T ≤ 11) :
    (∀ T, T ∈ (M.step xsys t).1.ths → due T ≤ 11) ∧
      adders (M.step xsys t).1.mem.agents + total heldAddT (M.step xsys t).1.ths ≤
        adders M.mem.agents + total heldAddT M.ths := by
  cases ht : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [ht]
    rw [es]
    exact ⟨h, Nat.le_refl _⟩
  | some T0 =>
    have es := XMach.step_eq (M := M) (t := t) ht (act_self M.mem T0)
    have e2 : (M.step xsys t).1.ths = M.ths.set t (XMach.act xsys M.mem T0).2.1 := by rw [es]
    have e3 : (M.step xsys t).1.mem = (XMach.act xsys M.mem T0).1 := by rw [es]
    have hb := act_bnd M.mem T0 (h T0 (List.mem_of_getElem? ht))
    rw [e2, e3]
    refine ⟨fun T hT => ?_, ?_⟩
    · rcases List.mem_or_eq_of_mem_set hT with h1 | h1
      · exact h T h1
      · rw [h1]
        exact hb.1
    · have sh := total_set heldAddT M.ths t T0 (XMach.act xsys M.mem T0).2.1 ht
      have h1 : heldAddT T0 = heldAdd T0.st := rfl
      have h2 : heldAddT (XMach.act xsys M.mem T0).2.1 =
          heldAdd (XMach.act xsys M.mem T0).2.1.st := rfl
      have hb2 := hb.2
      omega

/-- **In every run no thread owes more than eleven actions, and the
adders in memory or held are never more than at the start.** -/
theorem trace_bnd (X : XNet Arith) (nt : Nat) (σ : Nat → Nat) : ∀ i,
    (∀ T, T ∈ ((XMach.init X nt).trace xsys σ i).1.ths → due T ≤ 11) ∧
      adders ((XMach.init X nt).trace xsys σ i).1.mem.agents +
          total heldAddT ((XMach.init X nt).trace xsys σ i).1.ths ≤ adders X.agents
  | 0 => by
    refine ⟨fun T hT => ?_, ?_⟩
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      exact Nat.zero_le 11
    · have z := total_init heldAddT (fun _ => rfl) X nt
      show adders X.agents + total heldAddT (XMach.init X nt).ths ≤ adders X.agents
      omega
  | i + 1 => by
    obtain ⟨h1, h2⟩ := trace_bnd X nt σ i
    obtain ⟨h3, h4⟩ := step_bnd ((XMach.init X nt).trace xsys σ i).1 (σ i) h1
    exact ⟨h3, Nat.le_trans h4 h2⟩

/-- **The price of a stretch of a run**: sixteen for each claim made in
`d` actions, with what the threads have put toward claims and eight for
each adder at the end, is at most `d`, what the threads owe at the end,
and what was put and held when the stretch began. -/
theorem seg_cost (σ : Nat → Nat) (M : XMach Arith) (i : Nat) : ∀ d,
    16 * (M.trace xsys σ (i + d)).2 +
        (total paid (M.trace xsys σ (i + d)).1.ths +
          8 * adders (M.trace xsys σ (i + d)).1.mem.agents) +
        total due (M.trace xsys σ i).1.ths ≤
      16 * (M.trace xsys σ i).2 + d + total due (M.trace xsys σ (i + d)).1.ths +
        (total paid (M.trace xsys σ i).1.ths + 8 * adders (M.trace xsys σ i).1.mem.agents)
  | 0 => by
    show 16 * (M.trace xsys σ i).2 +
        (total paid (M.trace xsys σ i).1.ths + 8 * adders (M.trace xsys σ i).1.mem.agents) +
        total due (M.trace xsys σ i).1.ths ≤
      16 * (M.trace xsys σ i).2 + 0 + total due (M.trace xsys σ i).1.ths +
        (total paid (M.trace xsys σ i).1.ths + 8 * adders (M.trace xsys σ i).1.mem.agents)
    omega
  | d + 1 => by
    have ih := seg_cost σ M i d
    have hs := step_cost (M.trace xsys σ (i + d)).1 (σ (i + d))
    have hb := XMach.stepTally_busy_le (M.trace xsys σ (i + d)).1 (σ (i + d))
    show 16 * ((M.trace xsys σ (i + d)).2 +
          ((M.trace xsys σ (i + d)).1.step xsys (σ (i + d))).2) +
        (total paid ((M.trace xsys σ (i + d)).1.step xsys (σ (i + d))).1.ths +
          8 * adders ((M.trace xsys σ (i + d)).1.step xsys (σ (i + d))).1.mem.agents) +
        total due (M.trace xsys σ i).1.ths ≤
      16 * (M.trace xsys σ i).2 + (d + 1) +
        total due ((M.trace xsys σ (i + d)).1.step xsys (σ (i + d))).1.ths +
        (total paid (M.trace xsys σ i).1.ths + 8 * adders (M.trace xsys σ i).1.mem.agents)
    omega

/-- **After a claim, the reload and the whole memory.**  With `c` threads
in turn from a memory in order: if an action numbered `j` claims and the
threads are at rest after `R` rounds, then `R` is at least the rounds
before that action, two, and what the thread has to read of the reloaded
memory. -/
theorem claim_rest {N : Nat → Nat} {K : Nat} {X : XNet Arith} (hX : X.toNet.WF ar)
    (hnd : (X.agents.map Prod.fst).Nodup) (hO : MemOk N K X) {c : Nat} (hc : 0 < c) {R j : Nat}
    (hr : ((XMach.init X c).trace xsys (fun i => i % c) (c * R)).1.resting = true)
    (hj : j < c * R)
    (hcl : 0 < (((XMach.init X c).trace xsys (fun i => i % c) j).1.step xsys (j % c)).2) :
    j / c + 2 + (succs X.agents - c + 2 * K) ≤ R := by
  -- the thread that makes it
  have hk := Nat.mod_lt j hc
  have hlen : ((XMach.init X c).trace xsys (fun i => i % c) j).1.ths.length = c :=
    (XMach.trace_length xsys _ _ j).trans (init_length X c)
  cases h0 : ((XMach.init X c).trace xsys (fun i => i % c) j).1.ths[j % c]? with
  | none =>
    have hle := List.getElem?_eq_none_iff.1 h0
    omega
  | some T0 =>
    have es := XMach.step_eq (M := ((XMach.init X c).trace xsys (fun i => i % c) j).1)
      (t := j % c) h0 (act_self _ T0)
    have hj3' : 0 < (((XMach.init X c).trace xsys (fun i => i % c) j).1.step xsys (j % c)).2 :=
      hcl
    rw [es] at hj3'
    have hcl := act_claim_lam N (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K) _ T0
      hj3'
    have hT1 : ((XMach.init X c).trace xsys (fun i => i % c) (j + 1)).1.ths[j % c]? =
        some (XMach.act xsys ((XMach.init X c).trace xsys (fun i => i % c) j).1.mem T0).2.1 := by
      show (((XMach.init X c).trace xsys (fun i => i % c) j).1.step xsys (j % c)).1.ths[j % c]? = _
      rw [es]
      exact List.getElem?_set_self (by omega)
    -- its own actions from there to the rest
    obtain ⟨d', hd'⟩ : ∃ d', c * R = j + 1 + d' := ⟨c * R - (j + 1), by omega⟩
    obtain ⟨T', hT', hin⟩ := rr_track hX hnd hO hc d' (j + 1) (j % c) _ hk hT1
    rw [← hd'] at hT' hin
    have hrest : T' = ⟨[], .idle⟩ :=
      XThread.eq_rest (List.all_eq_true.1 hr T' (List.mem_of_getElem? hT'))
    have hl0 : lam N (g2 N (succs X.agents - c) K) (succs X.agents - c + 2 * K) T' = 0 := by
      rw [hrest]
      show min 0 _ + 2 * min 0 K + 0 = 0
      rw [Nat.zero_min, Nat.zero_min]
    have ho := rr_own c j (j % c) hc hk
    rw [ite_neg' (Nat.lt_irrefl _), ite_pos' rfl] at ho
    rw [hl0, ho, Nat.mul_div_cancel_left R hc, Nat.mul_mod_right,
      ite_neg' (Nat.not_lt_zero _)] at hin
    omega

/-- **The limit with the interactions of the second net.**  As
`late_floor`, with the cost of the claims: in the first `3 * n` rounds
the claims are those of the first net, and in `D` more actions the
threads make one claim for each sixteen actions and no more, but for
what they had put toward claims and for the adders; so while claims are
left, the last comes after those actions. -/
theorem late_floor2 {N : Nat → Nat} {K n : Nat} {B0 : List (Id × Arith)} {c : Nat}
    {X : XNet Arith} (hc : 0 < c) (hX : X.toNet.WF ar) (hnd : (X.agents.map Prod.fst).Nodup)
    (hO : MemOk N K X) (h1 : Mem1 B0 X) (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true)
    (hb : ∃ b W, B0 = b :: W ∧ tagged 1 b.1 = true) (hB0 : n + sndCnt N B0 ≤ K)
    (hinit : ∀ t, t < c → n ≤ pre N (X.agents.drop t ++ X.agents.take t)) {C R D : Nat}
    (hD : 16 * fcnt N X.agents + D + 15 * c + 8 * adders X.agents < 16 * (fcnt N B0 + C))
    (hr : ((XMach.init X c).trace xsys (fun i => i % c) (c * R)).1.resting = true)
    (hC : ((XMach.init X c).trace xsys (fun i => i % c) (c * R)).2 = C) :
    3 * n + D / c + 2 + (succs X.agents - c) + 2 * K ≤ R := by
  -- the claims of the first `3 * n` rounds
  have P := phase1 hc hO h1 hB hb hB0 hinit (c * (3 * n)) (Nat.le_refl _)
  have F := trace_first (fun i => i % c) (init_ok hO c) (c * (3 * n))
  have z := total_init (heldFT N) (fun _ => rfl) X c
  obtain ⟨L, hL, -⟩ := P.mem.shape
  have e0 : (XMach.init X c).mem = X := rfl
  rw [z, e0, hL, fcnt_append] at F
  -- the claims of `D` more actions
  have S := seg_cost (fun i => i % c) (XMach.init X c) (c * (3 * n)) D
  obtain ⟨-, b2⟩ := trace_bnd X c (fun i => i % c) (c * (3 * n))
  obtain ⟨b3, -⟩ := trace_bnd X c (fun i => i % c) (c * (3 * n) + D)
  have hlen0 : ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n))).1.ths.length = c :=
    (XMach.trace_length xsys _ _ _).trans (init_length X c)
  have hlenD : ((XMach.init X c).trace xsys (fun i => i % c)
      (c * (3 * n) + D)).1.ths.length = c :=
    (XMach.trace_length xsys _ _ _).trans (init_length X c)
  have d1 := total_le_mul (f := due) (P := 11) b3
  have c1 := total_le_mul (f := creditT) (P := 4)
    (ths := ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n))).1.ths)
    (fun T _ => credit_le T.st)
  have p1 := total_paid ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n))).1.ths
  rw [hlenD] at d1
  rw [hlen0] at c1
  have hlt : ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n) + D)).2 < C := by
    omega
  -- a claim after them
  have hlt2 : c * (3 * n) + D < c * R := by
    refine Nat.lt_of_not_le fun hle => ?_
    obtain ⟨d, hd⟩ : ∃ d, c * (3 * n) + D = c * R + d := ⟨c * (3 * n) + D - c * R, by omega⟩
    have hm := claims_mono (fun i => i % c) (XMach.init X c) d (c * R)
    rw [← hd, hC] at hm
    omega
  obtain ⟨d, hd⟩ : ∃ d, c * R = c * (3 * n) + D + d := ⟨c * R - (c * (3 * n) + D), by omega⟩
  have hgrow : ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n) + D)).2 <
      ((XMach.init X c).trace xsys (fun i => i % c) (c * (3 * n) + D + d)).2 := by
    rw [← hd, hC]
    exact hlt
  obtain ⟨j, hj1, hj2, hj3⟩ := claim_between (fun i => i % c) (XMach.init X c) d _ hgrow
  have hcr := claim_rest hX hnd hO hc hr (by omega) hj3
  have e : (c * (3 * n) + D) / c = D / c + 3 * n := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hc]
  have hj' : (c * (3 * n) + D) / c ≤ j / c := Nat.div_le_div_right hj1
  omega

/-- **Two additions side by side, with the interactions of the second
counted.**  With `c` threads in turn, `c` at most `m + 2`: the rounds to
rest and the threads are together at least
`6 * n + 3 * n' + m + m' + 4`, less sixteen, and more by sixteen for
each of the `m' + 1` successors of the first argument of the second
addition, shared among the threads. -/
theorem two_sums_rounds_late2 (m n m' n' : Nat) {c R : Nat} (hc : 0 < c) (hcm : c ≤ m + 2)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    c * (6 * n + 3 * n' + m + m' + 4) + 16 * (m' + 1) ≤ c * (R + c + 16) := by
  by_cases hsmall : 16 * (m' + 2) ≤ 15 * c + 17
  · have h0 := two_sums_rounds_late m n m' n' hc hcm h
    have h1 : c * (6 * n + 3 * n' + m + m' + 4) ≤ c * (R + c) := Nat.mul_le_mul_left c h0
    rw [Nat.mul_add c (R + c) 16]
    omega
  · obtain ⟨D, hD⟩ : ∃ D, 16 * (m' + 2) = D + 15 * c + 17 :=
      ⟨16 * (m' + 2) - 15 * c - 17, by omega⟩
    have hr := h.1
    have hC := two_sums_claims m n m' n' hc (fun i => i % c) hr
    have hF : 16 * fcnt (sideN n n') (twoSums (m + 1) n (m' + 1) n').agents + D + 15 * c +
        8 * adders (twoSums (m + 1) n (m' + 1) n').agents <
        16 * (fcnt (sideN n n') ((sum (m' + 1) n').agents.map (tagA 1)) + (m + m' + 4)) := by
      rw [adders_two_sums]
      show 16 * fcnt (sideN n n') ((sum (m + 1) n).agents.map (tagA 0) ++
        (sum (m' + 1) n').agents.map (tagA 1)) + D + 15 * c + 8 * 2 < _
      rw [fcnt_append]
      have h1 := sum_fcnt_le (sideN n n') 0 n rfl (m + 1)
      omega
    have hl := late_floor2 (n := n) (D := D) hc (two_sums_wf (m + 1) n (m' + 1) n')
      (two_sums_nodup (m + 1) n (m' + 1) n') (two_sums_memOk m n m' n')
      (two_sums_mem1 m n m' n') (fun _ he => mem_tag_self he) (two_sums_b0 m' n')
      (two_sums_b0_cnt n m' n') (fun _ ht => two_sums_init_pre m n m' n' (by omega)) hF hr hC
    rw [succs_two_sums] at hl
    have hdm := Nat.div_add_mod D c
    have hml := Nat.mod_lt D hc
    have h2 : 6 * n + 3 * n' + m + m' + 4 + D / c ≤ R + c := by omega
    have h3 := Nat.mul_le_mul_left c h2
    rw [Nat.mul_add c _ (D / c)] at h3
    rw [Nat.mul_add c (R + c) 16]
    omega

/-- **Two threads in turn on two additions**: at least
`6 * n + 3 * n' + m + 9 * m' - 6` rounds. -/
theorem two_threads_late2 (m n m' n' : Nat) {R : Nat}
    (h : Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2) R) :
    6 * n + 3 * n' + m + 9 * m' ≤ R + 6 := by
  have h' := two_sums_rounds_late2 m n m' n' (by decide) (by omega) h
  omega

/-- `6 + 32` twice: two threads take 489 rounds and cannot take fewer
than 332. -/
theorem Checks.Arith.Late.c4
    {R : Nat} (h : Rounds 2 (XMach.init (twoSums 6 32 6 32) 2) R) : 332 ≤ R := by
  have h' := two_threads_late2 5 32 5 32 h
  omega

/-- `6 + 200` twice: two threads take 2,001 rounds and cannot take fewer
than 1,844. -/
theorem Checks.Arith.Late.c5
    {R : Nat} (h : Rounds 2 (XMach.init (twoSums 6 200 6 200) 2) R) : 1844 ≤ R := by
  have h' := two_threads_late2 5 200 5 200 h
  omega

theorem sndL_drop : ∀ (n j : Nat), j ≤ n → (sndL n).drop j = sndL (n - j)
  | _, 0, _ => rfl
  | 0, j + 1, h => absurd h (Nat.not_succ_le_zero j)
  | n + 1, j + 1, h => by
    have ih := sndL_drop n j (by omega)
    have e : n + 1 - (j + 1) = n - j := by omega
    rw [e]
    exact ih

/-- A thread numbered `m + 1 + j` starts with all but `j` of the `n`
successors of the second argument of the first addition before the cells
of the second. -/
theorem two_sums_init_pre2 (m n m' n' : Nat) {j : Nat} (hj : j ≤ n) :
    n - j ≤ pre (sideN n n') ((twoSums (m + 1) n (m' + 1) n').agents.drop (m + 1 + j) ++
      (twoSums (m + 1) n (m' + 1) n').agents.take (m + 1 + j)) := by
  obtain ⟨restB, hBa⟩ := (sum_start m' n').head
  have eA : (twoSums (m + 1) n (m' + 1) n').agents =
      (chainL n (m + 1)).map (tagA 0) ++ ((sndL n).map (tagA 0) ++
        (base.agents.map (tagA 0) ++
          (tagA 1 ([n' + 3 + m' + 1], Arith.succ) :: restB.map (tagA 1)))) := by
    show (sum (m + 1) n).agents.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1) = _
    rw [sum_agents, hBa, List.map_append, List.map_append, List.append_assoc,
      List.append_assoc]
    rfl
  have hlC : ((chainL n (m + 1)).map (tagA 0)).length = m + 1 := by
    rw [List.length_map, chainL_length]
  have hlS : ((sndL n).map (tagA 0)).length = n := by
    rw [List.length_map]
    exact sndL_length n
  have e1 : ((chainL n (m + 1)).map (tagA 0)).drop (m + 1 + j) = [] :=
    List.drop_eq_nil_of_le (by omega)
  have e2 : m + 1 + j - ((chainL n (m + 1)).map (tagA 0)).length = j := by omega
  have e3 : ((sndL n).map (tagA 0)).drop j = (sndL (n - j)).map (tagA 0) := by
    rw [← List.map_drop, sndL_drop n j hj]
  have e4 : ∀ (S Bs W Tk : List (Id × Arith)) (b : Id × Arith),
      [] ++ (S ++ (Bs ++ b :: W)) ++ Tk = (S ++ Bs) ++ b :: (W ++ Tk) := by
    intro S Bs W Tk b
    simp
  have hL : ∀ e, e ∈ (sndL (n - j)).map (tagA 0) ++ base.agents.map (tagA 0) →
      tagged 1 e.1 = false := fun e he => by
    rcases List.mem_append.1 he with h | h
    · exact mem_tag_other (by decide) h
    · exact mem_tag_other (by decide) h
  rw [eA, List.drop_append, e1, e2, List.drop_append_of_le_length (by omega), e3, e4,
    pre_front (sideN n n') (tagged_self 1 _) _ _ hL, sndCnt_append,
    sndL_sndCnt (sideN n n') 0 (n - j) (Nat.sub_le n j), base_sndCnt]
  omega

/-- With `c` threads, `c` at most `m + n + 2`, every thread starts with
`n - (c - (m + 2))` of those successors before the cells of the second
addition. -/
theorem two_sums_init_pre3 (m n m' n' : Nat) {c t : Nat} (hcn : c ≤ m + n + 2) (ht : t < c) :
    n - (c - (m + 2)) ≤ pre (sideN n n') ((twoSums (m + 1) n (m' + 1) n').agents.drop t ++
      (twoSums (m + 1) n (m' + 1) n').agents.take t) := by
  by_cases h : t ≤ m + 1
  · have h1 := two_sums_init_pre m n m' n' h
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, t = m + 1 + j := ⟨t - (m + 1), by omega⟩
    have h1 := two_sums_init_pre2 m n m' n' (j := j) (by omega)
    omega

/-- **Nothing of the second addition is touched in the first stretch,
for more threads.**  With `c` threads in turn, `c` at most `m + n + 2`:
after any number of actions up to `c * (3 * (n - (c - (m + 2))))` the
cells of the second addition are all in memory, in place. -/
theorem two_sums_untouched2 (m n m' n' : Nat) {c : Nat} (hc : 0 < c) (hcn : c ≤ m + n + 2)
    {i : Nat} (hi : i ≤ c * (3 * (n - (c - (m + 2))))) :
    ∃ L, ((XMach.init (twoSums (m + 1) n (m' + 1) n') c).trace xsys (fun i => i % c)
          i).1.mem.agents = L ++ (sum (m' + 1) n').agents.map (tagA 1) ∧
      ∀ e, e ∈ L → tagged 1 e.1 = false :=
  (phase1 (n := n - (c - (m + 2))) hc (two_sums_memOk m n m' n') (two_sums_mem1 m n m' n')
    (fun _ he => mem_tag_self he) (two_sums_b0 m' n')
    (by
      have h := two_sums_b0_cnt n m' n'
      omega)
    (fun _ ht => two_sums_init_pre3 m n m' n' hcn ht) i hi).mem.shape

/-- **The limit for more threads.**  With `c` threads in turn, `c` at
most `m + n + 2`, on two additions side by side: as for `m + 2` threads
or fewer, but for three rounds for each thread beyond `m + 2`, which
starts that much further in the first addition. -/
theorem two_sums_rounds_late3 (m n m' n' : Nat) {c R : Nat} (hc : 0 < c) (hcn : c ≤ m + n + 2)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    c * (6 * n + 3 * n' + m + m' + 4) + 16 * (m' + 1) ≤
      c * (R + c + 16 + 3 * (c - (m + 2))) := by
  have hr := h.1
  have hC := two_sums_claims m n m' n' hc (fun i => i % c) hr
  have hb0 : n - (c - (m + 2)) + sndCnt (sideN n n') ((sum (m' + 1) n').agents.map (tagA 1)) ≤
      n + n' := by
    have h1 := two_sums_b0_cnt n m' n'
    omega
  by_cases hsmall : 16 * (m' + 2) ≤ 15 * c + 17
  · have hF : fcnt (sideN n n') (twoSums (m + 1) n (m' + 1) n').agents <
        fcnt (sideN n n') ((sum (m' + 1) n').agents.map (tagA 1)) + (m + m' + 4) := by
      show fcnt (sideN n n') ((sum (m + 1) n).agents.map (tagA 0) ++
        (sum (m' + 1) n').agents.map (tagA 1)) < _
      rw [fcnt_append]
      have h1 := sum_fcnt_le (sideN n n') 0 n rfl (m + 1)
      omega
    have hl := late_floor (n := n - (c - (m + 2))) hc (two_sums_wf (m + 1) n (m' + 1) n')
      (two_sums_nodup (m + 1) n (m' + 1) n') (two_sums_memOk m n m' n')
      (two_sums_mem1 m n m' n') (fun _ he => mem_tag_self he) (two_sums_b0 m' n') hb0
      (fun _ ht => two_sums_init_pre3 m n m' n' hcn ht) hF hr hC
    rw [succs_two_sums] at hl
    have h2 : 6 * n + 3 * n' + m + m' + 4 ≤ R + c + 3 * (c - (m + 2)) := by omega
    have h3 := Nat.mul_le_mul_left c h2
    have e : c * (R + c + 16 + 3 * (c - (m + 2))) =
        c * (R + c + 3 * (c - (m + 2))) + c * 16 := by
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [e]
    omega
  · obtain ⟨D, hD⟩ : ∃ D, 16 * (m' + 2) = D + 15 * c + 17 :=
      ⟨16 * (m' + 2) - 15 * c - 17, by omega⟩
    have hF : 16 * fcnt (sideN n n') (twoSums (m + 1) n (m' + 1) n').agents + D + 15 * c +
        8 * adders (twoSums (m + 1) n (m' + 1) n').agents <
        16 * (fcnt (sideN n n') ((sum (m' + 1) n').agents.map (tagA 1)) + (m + m' + 4)) := by
      rw [adders_two_sums]
      show 16 * fcnt (sideN n n') ((sum (m + 1) n).agents.map (tagA 0) ++
        (sum (m' + 1) n').agents.map (tagA 1)) + D + 15 * c + 8 * 2 < _
      rw [fcnt_append]
      have h1 := sum_fcnt_le (sideN n n') 0 n rfl (m + 1)
      omega
    have hl := late_floor2 (n := n - (c - (m + 2))) (D := D) hc
      (two_sums_wf (m + 1) n (m' + 1) n') (two_sums_nodup (m + 1) n (m' + 1) n')
      (two_sums_memOk m n m' n') (two_sums_mem1 m n m' n') (fun _ he => mem_tag_self he)
      (two_sums_b0 m' n') hb0 (fun _ ht => two_sums_init_pre3 m n m' n' hcn ht) hF hr hC
    rw [succs_two_sums] at hl
    have hdm := Nat.div_add_mod D c
    have hml := Nat.mod_lt D hc
    have h2 : 6 * n + 3 * n' + m + m' + 4 + D / c ≤ R + c + 3 * (c - (m + 2)) := by omega
    have h3 := Nat.mul_le_mul_left c h2
    rw [Nat.mul_add c _ (D / c)] at h3
    have e : c * (R + c + 16 + 3 * (c - (m + 2))) =
        c * (R + c + 3 * (c - (m + 2))) + c * 16 := by
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [e]
    omega

/-- `6 + 32` twice with eight threads in turn: they take 458 rounds in
the run computed, and cannot take fewer than 287. -/
theorem Checks.Arith.Late.c6
    {R : Nat} (h : Rounds 8 (XMach.init (twoSums 6 32 6 32) 8) R) : 287 ≤ R := by
  have h' := two_sums_rounds_late3 5 32 5 32 (by decide) (by decide) h
  omega

/-- With sixteen: 399 rounds in the run computed, and not fewer than
249. -/
theorem Checks.Arith.Late.c7
    {R : Nat} (h : Rounds 16 (XMach.init (twoSums 6 32 6 32) 16) R) : 249 ≤ R := by
  have h' := two_sums_rounds_late3 5 32 5 32 (by decide) (by decide) h
  omega

/-- The actions the thread numbered `t` has made among the first `i` of a
schedule. -/
def ownCnt (σ : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ownCnt σ t i + (if σ i = t then 1 else 0)

/-- **The first stretch under any schedule**, after `i` actions: the
second net is untouched, every thread works in the first net, and each
thread has, with the actions it has made, still three to make for each
of the `n` successors of the second argument of the first net before it
comes to a cell of the second. -/
structure Ph1s (N : Nat → Nat) (n : Nat) (B0 : List (Id × Arith)) (σ : Nat → Nat) (i : Nat)
    (M : XMach Arith) : Prop where
  mem : Mem1 B0 M.mem
  guard : ∀ T, T ∈ M.ths → Guard T.st
  pot : ∀ t T, M.ths[t]? = some T →
    3 * n ≤ lam N (g1 N n) (3 * n) T + ownCnt σ t i

theorem ph1s_step {N : Nat → Nat} {K n : Nat} {B0 : List (Id × Arith)} {σ : Nat → Nat}
    {i : Nat} {M : XMach Arith} (hO : MachOk N K M) (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true)
    (hb : ∃ b W, B0 = b :: W ∧ tagged 1 b.1 = true) (hB0 : n + sndCnt N B0 ≤ K)
    (h : Ph1s N n B0 σ i M) (hi : ownCnt σ (σ i) i < 3 * n) :
    Ph1s N n B0 σ (i + 1) (M.step xsys (σ i)).1 := by
  have hR : 3 * n ≤ g1 N n M.mem.agents := by
    have hp := mem1_pre hO.1 h.mem hb hB0
    show 3 * n ≤ min (3 * pre N M.mem.agents) (3 * n)
    omega
  cases h0 : M.ths[σ i]? with
  | none =>
    have es : M.step xsys (σ i) = (M, 0) := by
      unfold XMach.step
      rw [h0]
    rw [es]
    refine ⟨h.mem, h.guard, fun t T hT => ?_⟩
    have hp := h.pot t T hT
    show 3 * n ≤ lam N (g1 N n) (3 * n) T + (ownCnt σ t i + (if σ i = t then 1 else 0))
    omega
  | some T0 =>
    have hlt : σ i < M.ths.length := Nat.lt_of_not_le fun hle => by
      rw [List.getElem?_eq_none_iff.2 hle] at h0
      cases h0
    have es := XMach.step_eq (M := M) (t := σ i) h0 (act_self M.mem T0)
    have e2 : (M.step xsys (σ i)).1.ths =
        M.ths.set (σ i) (XMach.act xsys M.mem T0).2.1 := by rw [es]
    have e3 : (M.step xsys (σ i)).1.mem = (XMach.act xsys M.mem T0).1 := by rw [es]
    have hp0 := h.pot (σ i) T0 h0
    have hg0 := h.guard T0 (List.mem_of_getElem? h0)
    have hdrop := act_lam (g1 N n) (3 * n) hO.1 (hO.2 T0 (List.mem_of_getElem? h0))
      (g1_cons N n) (fun l => Nat.min_le_right _ _) hR
    have hhead : ∀ e rest, T0.st = .idle → T0.todo = e :: rest → tagged 1 e.1 = false := by
      intro e rest hst htd
      obtain ⟨todo, st⟩ := T0
      have hst' : st = .idle := hst
      have htd' : todo = e :: rest := htd
      subst hst'
      subst htd'
      have hp0' : 3 * n ≤ g1 N n (e :: rest) + 0 + ownCnt σ (σ i) i := hp0
      have hpos : 0 < g1 N n (e :: rest) := by omega
      exact g1_head N n hpos
    have ha := act_phase1 h.mem hB hg0 hhead
    refine ⟨?_, fun T hT => ?_, fun t T' hT' => ?_⟩
    · rw [e3]
      exact ha.1
    · rw [e2] at hT
      rcases List.mem_or_eq_of_mem_set hT with h1 | h1
      · exact h.guard T h1
      · rw [h1]
        exact ha.2
    · rw [e2] at hT'
      by_cases e : σ i = t
      · subst e
        rw [List.getElem?_set_self hlt] at hT'
        cases hT'
        show 3 * n ≤ lam N (g1 N n) (3 * n) (XMach.act xsys M.mem T0).2.1 +
          (ownCnt σ (σ i) i + (if σ i = σ i then 1 else 0))
        rw [ite_pos' rfl]
        omega
      · rw [List.getElem?_set_ne e] at hT'
        have hp := h.pot t T' hT'
        show 3 * n ≤ lam N (g1 N n) (3 * n) T' + (ownCnt σ t i + (if σ i = t then 1 else 0))
        omega

/-- **Nothing of the second net is touched before some thread has made
`3 * n` actions of its own, whatever the schedule.**  From a memory in
order whose second net is in place, when each thread starts with the `n`
successors of the second argument of the first net before the cells of
the second: as long as every action is made by a thread that had made
fewer than `3 * n` before it, the cells of the second net are all in
memory, in place, and every thread works in the first net. -/
theorem phase1s {N : Nat → Nat} {K n : Nat} {B0 : List (Id × Arith)} {X : XNet Arith}
    (hO : MemOk N K X) (h1 : Mem1 B0 X) (hB : ∀ e, e ∈ B0 → tagged 1 e.1 = true)
    (hb : ∃ b W, B0 = b :: W ∧ tagged 1 b.1 = true) (hB0 : n + sndCnt N B0 ≤ K) (nt : Nat)
    (σ : Nat → Nat)
    (hinit : ∀ t, t < nt → n ≤ pre N (X.agents.drop t ++ X.agents.take t)) :
    ∀ i, (∀ j, j < i → ownCnt σ (σ j) j < 3 * n) →
      Ph1s N n B0 σ i ((XMach.init X nt).trace xsys σ i).1
  | 0, _ => by
    refine ⟨h1, fun T hT => ?_, fun t T hT => ?_⟩
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      exact trivial
    · have hT' : (XMach.init X nt).ths[t]? = some T := hT
      have ht : t < nt := Nat.lt_of_not_le fun hle => by
        have hn : (XMach.init X nt).ths[t]? = none :=
          List.getElem?_eq_none_iff.2 (by
            rw [init_length]
            exact hle)
        rw [hn] at hT'
        cases hT'
      have e : (XMach.init X nt).ths[t]? =
          some ⟨X.agents.drop t ++ X.agents.take t, .idle⟩ := by
        show ((List.range nt).map _)[t]? = _
        rw [List.getElem?_map, List.getElem?_range ht]
        rfl
      rw [e] at hT'
      cases hT'
      have hi := hinit t ht
      have h3 : 3 * n ≤ min (3 * pre N (X.agents.drop t ++ X.agents.take t)) (3 * n) + 0 := by
        omega
      exact Nat.le_trans h3 (Nat.le_add_right _ _)
  | i + 1, hi =>
    ph1s_step (trace_ok σ (init_ok hO nt) i) hB hb hB0
      (phase1s hO h1 hB hb hB0 nt σ hinit i (fun j hj => hi j (by omega)))
      (hi i (Nat.lt_succ_self i))

/-- **Two additions side by side, any schedule**: with `nt` threads, `nt`
at most `m + n + 2`, as long as every action is made by a thread that
had made fewer than `3 * (n - (nt - (m + 2)))` before it, the cells of
the second addition are all in memory, in place. -/
theorem two_sums_untouched_any (m n m' n' : Nat) {nt : Nat} (hcn : nt ≤ m + n + 2)
    (σ : Nat → Nat) {i : Nat}
    (hi : ∀ j, j < i → ownCnt σ (σ j) j < 3 * (n - (nt - (m + 2)))) :
    ∃ L, ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.agents =
        L ++ (sum (m' + 1) n').agents.map (tagA 1) ∧
      ∀ e, e ∈ L → tagged 1 e.1 = false :=
  (phase1s (n := n - (nt - (m + 2))) (two_sums_memOk m n m' n') (two_sums_mem1 m n m' n')
    (fun _ he => mem_tag_self he) (two_sums_b0 m' n')
    (by
      have h := two_sums_b0_cnt n m' n'
      omega)
    nt σ (fun _ ht => two_sums_init_pre3 m n m' n' hcn ht) i hi).mem.shape

end Arith

end INet
