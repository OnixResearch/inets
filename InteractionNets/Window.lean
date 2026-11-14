import InteractionNets.LongRun

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## Example: a run in which the window multiplies every pass

One symbol `c` with one auxiliary port, and one rule: two `c` facing each
other leave a segment between their auxiliary ports.  The net
`Chain.net k n` has `k` agents that lead nowhere, listed first, and `n`
pairs in a chain.  Only the first pair is active; when a pair fires, the
segment it leaves joins the principal ports of the next pair, through the
auxiliary ports of the pair that is gone.  So the pairs are found one at a
time, each after a pass over the `k` agents. -/

/-- A list made of one piece for each of `r` numbers from `s` on, the first
one first. -/
def asc {A : Type} (f : Nat → List A) : Nat → Nat → List A
  | _, 0 => []
  | s, r + 1 => f s ++ asc f (s + 1) r

theorem mem_asc {A : Type} {f : Nat → List A} {x : A} :
    ∀ {r s : Nat}, x ∈ asc f s r ↔ ∃ j, s ≤ j ∧ j < s + r ∧ x ∈ f j
  | 0, s => ⟨fun h => absurd h List.not_mem_nil, fun ⟨j, h₁, h₂, _⟩ => by omega⟩
  | r + 1, s => by
    show x ∈ f s ++ asc f (s + 1) r ↔ _
    rw [List.mem_append, mem_asc (r := r)]
    constructor
    · rintro (h | ⟨j, h₁, h₂, h⟩)
      · exact ⟨s, Nat.le_refl s, by omega, h⟩
      · exact ⟨j, by omega, by omega, h⟩
    · rintro ⟨j, h₁, h₂, h⟩
      rcases Nat.lt_or_eq_of_le h₁ with h' | h'
      · exact .inr ⟨j, by omega, by omega, h⟩
      · rw [← h'] at h
        exact .inl h

theorem length_asc {A : Type} {f : Nat → List A} {c : Nat} (h : ∀ j, (f j).length = c) :
    ∀ r s, (asc f s r).length = c * r
  | 0, _ => rfl
  | r + 1, s => by
    show (f s ++ asc f (s + 1) r).length = c * (r + 1)
    rw [List.length_append, h, length_asc h r (s + 1), Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem map_asc {A B : Type} (g : A → B) (f : Nat → List A) :
    ∀ r s, (asc f s r).map g = asc (fun j => (f j).map g) s r
  | 0, _ => rfl
  | r + 1, s => by
    show (f s ++ asc f (s + 1) r).map g = (f s).map g ++ asc (fun j => (f j).map g) (s + 1) r
    rw [List.map_append, map_asc g f r (s + 1)]

theorem nodup_asc {A : Type} {f : Nat → List A} (h₁ : ∀ j, (f j).Nodup)
    (h₂ : ∀ i j x, x ∈ f i → x ∈ f j → i = j) : ∀ r s, (asc f s r).Nodup
  | 0, _ => List.nodup_nil
  | r + 1, s => by
    show (f s ++ asc f (s + 1) r).Nodup
    refine List.nodup_append.2 ⟨h₁ s, nodup_asc h₁ h₂ r (s + 1), fun a ha b hb e => ?_⟩
    obtain ⟨j, hj, -, hb'⟩ := mem_asc.1 hb
    rw [← e] at hb'
    have := h₂ s j a ha hb'
    omega

/-- A list made of one piece for each of `r` numbers from `s` on, the last
one first. -/
def desc {A : Type} (f : Nat → List A) : Nat → Nat → List A
  | _, 0 => []
  | s, r + 1 => desc f (s + 1) r ++ f s

/-- The pieces of `asc`, in another order. -/
theorem desc_perm {A : Type} (f : Nat → List A) : ∀ r s, (desc f s r).Perm (asc f s r)
  | 0, _ => List.Perm.refl _
  | r + 1, s => by
    show (desc f (s + 1) r ++ f s).Perm (f s ++ asc f (s + 1) r)
    exact List.perm_append_comm.trans (List.Perm.append_left (f s) (desc_perm f r (s + 1)))

/-- A single symbol. -/
inductive Chain
  | c
  deriving DecidableEq, Repr

namespace Chain

/-- It has one auxiliary port. -/
def ar : Chain → Nat := fun _ => 1

/-- `c ⋈ c`: a segment between the two auxiliary ports. -/
def data : SysData Chain :=
  ⟨ar, [((c, c), RuleData.ofWires [] [(.ifc false 0, .ifc true 0)])]⟩

/-- The system, by evaluation of the check. -/
def xsys : XSys Chain := data.toXSys (by decide)

/-- Its rule writes no agent and two segments, one in each direction. -/
theorem xsys_bounded : xsys.Bounded 0 2 := by
  intro α β R h
  cases α
  cases β
  rw [← Option.some.inj h]
  decide

/-- The right-hand side of the rule. -/
def rhs : XRhs Chain := (RuleData.ofWires [] [(.ifc false 0, .ifc true 0)]).toX

theorem rule_cc : xsys.rule c c = some rhs := rfl

theorem rhs_agents (a b : Id) : rhs.newAgents a b = [] := rfl

theorem rhs_links (a b : Id) :
    rhs.newLinks xsys.sys.ar a b c c = [((a, 1), (b, 1)), ((b, 1), (a, 1))] := rfl

/-- `k` agents, each to be wired to two free ports of its own. -/
def lone (k : Nat) : List (Id × Chain) := gen (fun j => [([j, 0], c)]) k

def loneFree (k : Nat) : List Port := gen (fun j => [([j, 1], 0), ([j, 2], 0)]) k

def loneWires (k : Nat) : List (Port × Port) :=
  gen (fun j => [(([j, 0], 0), ([j, 1], 0)), (([j, 1], 0), ([j, 0], 0)),
    (([j, 0], 1), ([j, 2], 0)), (([j, 2], 0), ([j, 0], 1))]) k

/-- The pairs from number `s` on, `r` of them. -/
def pairsFrom (s r : Nat) : List (Id × Chain) := asc (fun j => [([j, 3], c), ([j, 4], c)]) s r

/-- The segment that makes the first pair active. -/
def headWires : List (Port × Port) := [(([0, 3], 0), ([0, 4], 0)), (([0, 4], 0), ([0, 3], 0))]

/-- From the auxiliary port of each agent of a pair, a segment to the
principal port of the agent of the next pair on the same side; after the
last pair, to a free port. -/
def chainWires (n : Nat) : List (Port × Port) :=
  gen (fun j => [(([j, 3], 1), ([j + 1, 3], 0)), (([j + 1, 3], 0), ([j, 3], 1)),
    (([j, 4], 1), ([j + 1, 4], 0)), (([j + 1, 4], 0), ([j, 4], 1))]) n

/-- The segments written by the first `w` firings, the last one first. -/
def written (w : Nat) : List (Port × Port) :=
  gen (fun j => [(([j, 4], 1), ([j, 3], 1)), (([j, 3], 1), ([j, 4], 1))]) w

def wires (k n w : Nat) : List (Port × Port) :=
  written w ++ (loneWires k ++ (headWires ++ chainWires n))

/-- A memory of a run on `k` agents that lead nowhere and `n` pairs: `w`
pairs have had their segment written, and the pairs from `s` on, `r` of
them, are still in memory. -/
def st (k n w s r : Nat) : XNet Chain :=
  ⟨lone k ++ pairsFrom s r, loneFree k ++ [([n, 3], 0), ([n, 4], 0)], wires k n w⟩

/-- `k` agents that lead nowhere, listed first, and a chain of `n` pairs. -/
def net (k n : Nat) : XNet Chain := st k n 0 0 n

theorem mem_lone {k : Nat} {e : Id × Chain} : e ∈ lone k ↔ ∃ j, j < k ∧ e = ([j, 0], c) := by
  unfold lone
  rw [mem_gen]
  exact exists_congr fun j => and_congr Iff.rfl List.mem_singleton

theorem lone_length (k : Nat) : (lone k).length = k := by
  have h := length_gen (f := fun j => [(([j, 0] : Id), c)]) (c := 1) (fun _ => rfl) k
  rw [Nat.one_mul] at h
  exact h

theorem mem_pairsFrom {s r : Nat} {e : Id × Chain} :
    e ∈ pairsFrom s r ↔ ∃ j, s ≤ j ∧ j < s + r ∧ (e = ([j, 3], c) ∨ e = ([j, 4], c)) := by
  unfold pairsFrom
  rw [mem_asc]
  exact exists_congr fun j => and_congr Iff.rfl (and_congr Iff.rfl
    (by rw [List.mem_cons, List.mem_singleton]))

theorem pairsFrom_length (s r : Nat) : (pairsFrom s r).length = 2 * r :=
  length_asc (f := fun j => [(([j, 3] : Id), c), ([j, 4], c)]) (fun _ => rfl) r s

theorem mem_wires {k n w : Nat} {p q : Port} :
    (p, q) ∈ wires k n w ↔
      (∃ j, j < w ∧ ((p, q) = (([j, 4], 1), ([j, 3], 1)) ∨
        (p, q) = (([j, 3], 1), ([j, 4], 1)))) ∨
      (∃ j, j < k ∧ ((p, q) = (([j, 0], 0), ([j, 1], 0)) ∨
        (p, q) = (([j, 1], 0), ([j, 0], 0)) ∨ (p, q) = (([j, 0], 1), ([j, 2], 0)) ∨
        (p, q) = (([j, 2], 0), ([j, 0], 1)))) ∨
      (p, q) = (([0, 3], 0), ([0, 4], 0)) ∨ (p, q) = (([0, 4], 0), ([0, 3], 0)) ∨
      ∃ j, j < n ∧ ((p, q) = (([j, 3], 1), ([j + 1, 3], 0)) ∨
        (p, q) = (([j + 1, 3], 0), ([j, 3], 1)) ∨ (p, q) = (([j, 4], 1), ([j + 1, 4], 0)) ∨
        (p, q) = (([j + 1, 4], 0), ([j, 4], 1))) := by
  unfold wires written loneWires headWires chainWires
  simp only [List.mem_append, mem_gen, List.mem_cons, List.not_mem_nil, or_false, or_assoc]

theorem assoc_some {A : Type} [DecidableEq A] {i : A} {l : List (A × Chain)}
    (h : (i, c) ∈ l) : assoc i l = some c :=
  assoc_eq_of_unique h fun q' _ => by cases q'; rfl

/-! Where the segments lead. -/

theorem wire_lone {k n w j : Nat} {q' : Port}
    (h : ((([j, 0] : Id), 0), q') ∈ wires k n w) : q' = ([j, 1], 0) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | simp at h

theorem wire_loneFree {k n w j : Nat} {q' : Port}
    (h : ((([j, 1] : Id), 0), q') ∈ wires k n w) : q' = ([j, 0], 0) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | simp at h

theorem wire_head {k n w : Nat} {q' : Port}
    (h : ((([0, 3] : Id), 0), q') ∈ wires k n w) : q' = ([0, 4], 0) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; rw [h])
      | simp at h

theorem wire_x {k n w j : Nat} {q' : Port}
    (h : ((([j + 1, 3] : Id), 0), q') ∈ wires k n w) : q' = ([j, 3], 1) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | simp at h

theorem wire_y {k n w j : Nat} {q' : Port}
    (h : ((([j + 1, 4] : Id), 0), q') ∈ wires k n w) : q' = ([j, 4], 1) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | simp at h

/-- From the auxiliary port of an agent on the first side: back to the next
pair, or, once the pair has fired, across to the other side. -/
theorem wire_x_aux {k n w j : Nat} {q' : Port}
    (h : ((([j, 3] : Id), 1), q') ∈ wires k n w) :
    q' = ([j + 1, 3], 0) ∨ (j < w ∧ q' = ([j, 4], 1)) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; exact .inl rfl)
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; exact .inr ⟨hj', rfl⟩)
      | simp at h

theorem wire_y_aux {k n w j : Nat} {q' : Port}
    (h : ((([j, 4] : Id), 1), q') ∈ wires k n w) :
    q' = ([j + 1, 4], 0) ∨ (j < w ∧ q' = ([j, 3], 1)) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; exact .inl rfl)
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; exact .inr ⟨hj', rfl⟩)
      | simp at h

/-! Which agents are in memory. -/

theorem agent_lone {k n w s r j : Nat} (hj : j < k) :
    assoc [j, 0] (st k n w s r).agents = some c :=
  assoc_some (List.mem_append_left _ (mem_lone.2 ⟨j, hj, rfl⟩))

theorem agent_x {k n w s r j : Nat} (h₁ : s ≤ j) (h₂ : j < s + r) :
    assoc [j, 3] (st k n w s r).agents = some c :=
  assoc_some (List.mem_append_right _ (mem_pairsFrom.2 ⟨j, h₁, h₂, .inl rfl⟩))

theorem agent_y {k n w s r j : Nat} (h₁ : s ≤ j) (h₂ : j < s + r) :
    assoc [j, 4] (st k n w s r).agents = some c :=
  assoc_some (List.mem_append_right _ (mem_pairsFrom.2 ⟨j, h₁, h₂, .inr rfl⟩))

/-- A name with last number `1` is not the name of an agent. -/
theorem agent_none {k n w s r j : Nat} : assoc [j, 1] (st k n w s r).agents = none := by
  cases h : assoc [j, 1] (st k n w s r).agents with
  | none => rfl
  | some v =>
    rcases List.mem_append.1 (assoc_mem h) with h' | h'
    · obtain ⟨j', -, e⟩ := mem_lone.1 h'
      simp at e
    · obtain ⟨j', -, -, e | e⟩ := mem_pairsFrom.1 h'
      · simp at e
      · simp at e

/-- A pair below the first one left is gone. -/
theorem agent_gone {k n w s r j : Nat} (hj : j < s) (x : Nat) (hx : 3 ≤ x) (v : Chain) :
    ¬ assoc [j, x] (st k n w s r).agents = some v := by
  intro h
  rcases List.mem_append.1 (assoc_mem h) with h' | h'
  · obtain ⟨j', -, e⟩ := mem_lone.1 h'
    simp at e
    omega
  · obtain ⟨j', h₁, -, e | e⟩ := mem_pairsFrom.1 h'
    · simp at e
      omega
    · simp at e
      omega

/-! Which agents lead nowhere. -/

theorem inert_lone {k n w s r j : Nat} (hj : j < k) : (st k n w s r).Inert ([j, 0], c) := by
  refine ⟨agent_lone hj, ([j, 1], 0), ?_, ?_, nextSeg_none fun q hq => wire_loneFree hq⟩
  · refine assoc_eq_of_unique ?_ fun q' hq' => wire_lone hq'
    exact mem_wires.2 (.inr (.inl ⟨j, hj, .inl rfl⟩))
  · show (if (0 : Nat) = 0 then assoc [j, 1] (st k n w s r).agents else none) = none
    rw [ite_pos' rfl]
    exact agent_none

/-- An agent of a pair is given up on as long as the pair before it has not
had its segment written. -/
theorem inert_x {k n w s r j : Nat} (hw : w ≤ j) (h₁ : s ≤ j + 1) (h₂ : j + 1 < s + r)
    (hn : j < n) : (st k n w s r).Inert ([j + 1, 3], c) := by
  refine ⟨agent_x h₁ h₂, ([j, 3], 1), ?_, ite_neg' (by simp), nextSeg_none fun q hq => ?_⟩
  · refine assoc_eq_of_unique ?_ fun q' hq' => wire_x hq'
    exact mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hn, .inr (.inl rfl)⟩))))
  · rcases wire_x_aux hq with h | ⟨h, -⟩
    · exact h
    · omega

theorem inert_y {k n w s r j : Nat} (hw : w ≤ j) (h₁ : s ≤ j + 1) (h₂ : j + 1 < s + r)
    (hn : j < n) : (st k n w s r).Inert ([j + 1, 4], c) := by
  refine ⟨agent_y h₁ h₂, ([j, 4], 1), ?_, ite_neg' (by simp), nextSeg_none fun q hq => ?_⟩
  · refine assoc_eq_of_unique ?_ fun q' hq' => wire_y hq'
    exact mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hn, .inr (.inr (.inr rfl))⟩))))
  · rcases wire_y_aux hq with h | ⟨h, -⟩
    · exact h
    · omega

/-- A thread passes the agents that lead nowhere in three actions each,
without writing. -/
theorem pass (k n w s r : Nat) (rest : List (Id × Chain)) :
    Stays xsys (st k n w s r) ⟨lone k ++ rest, .idle⟩ ⟨rest, .idle⟩ (3 * k) := by
  have h := Stays.inert_pass (xs := xsys) (X := st k n w s r) rest (lone k) fun e he => by
    obtain ⟨j, hj, rfl⟩ := mem_lone.1 he
    exact inert_lone hj
  rw [lone_length] at h
  exact h

/-! The actions of a thread on a pair. -/

/-- Taking the two agents of the first pair left leaves the rest. -/
theorem take_pair (k n w s r : Nat) :
    ((st k n w s (r + 1)).takeAgent [s, 3]).takeAgent [s, 4] = st k n w (s + 1) r := by
  have hl : ∀ e, e ∈ lone k → e.1 ≠ [s, 3] ∧ e.1 ≠ [s, 4] := by
    intro e he
    obtain ⟨j, -, rfl⟩ := mem_lone.1 he
    simp
  have hp : ∀ e, e ∈ pairsFrom (s + 1) r → e.1 ≠ [s, 3] ∧ e.1 ≠ [s, 4] := by
    intro e he
    obtain ⟨j, hj, -, rfl | rfl⟩ := mem_pairsFrom.1 he
    · constructor
      · intro h
        simp at h
        omega
      · intro h
        simp at h
    · constructor
      · intro h
        simp at h
      · intro h
        simp at h
        omega
  have hne : ([s, 4] : Id) ≠ [s, 3] := by simp
  have e1 : (lone k ++ pairsFrom s (r + 1)).filter (fun e => decide (e.1 ≠ [s, 3])) =
      lone k ++ (([s, 4], c) :: pairsFrom (s + 1) r) := by
    show (lone k ++ (([s, 3], c) :: ([s, 4], c) :: pairsFrom (s + 1) r)).filter _ = _
    rw [List.filter_append, filter_ne fun e he => (hl e he).1, filter_ne_cons_same,
      filter_ne_cons_other hne, filter_ne fun e he => (hp e he).1]
  have e2 : (lone k ++ (([s, 4], c) :: pairsFrom (s + 1) r)).filter
      (fun e => decide (e.1 ≠ [s, 4])) = lone k ++ pairsFrom (s + 1) r := by
    rw [List.filter_append, filter_ne fun e he => (hl e he).2, filter_ne_cons_same,
      filter_ne fun e he => (hp e he).2]
  show (⟨((lone k ++ pairsFrom s (r + 1)).filter fun e => decide (e.1 ≠ [s, 3])).filter
      fun e => decide (e.1 ≠ [s, 4]), loneFree k ++ [([n, 3], 0), ([n, 4], 0)],
      wires k n w⟩ : XNet Chain) =
    ⟨lone k ++ pairsFrom (s + 1) r, loneFree k ++ [([n, 3], 0), ([n, 4], 0)], wires k n w⟩
  rw [e1, e2]

/-- A thread that has found a pair takes its two agents, in two actions,
and has two segments to write. -/
theorem take (k n w s r : Nat) (rest : List (Id × Chain)) :
    Works xsys (st k n w s (r + 1)) ⟨rest, .ready [s, 3] [s, 4] c c⟩ (st k n w (s + 1) r)
      ⟨rest, .write [] [(([s, 3], 1), ([s, 4], 1)), (([s, 4], 1), ([s, 3], 1))]⟩ 1 2 := by
  have hne : ([s, 3] : Id) ≠ [s, 4] := by simp
  have ha : assoc [s, 3] (st k n w s (r + 1)).agents = some c :=
    agent_x (Nat.le_refl s) (by omega)
  have hb : (([s, 4] : Id), c) ∈ ((st k n w s (r + 1)).takeAgent [s, 3]).agents :=
    XNet.mem_takeAgent.2 ⟨List.mem_append_right _
      (mem_pairsFrom.2 ⟨s, Nat.le_refl s, by omega, .inr rfl⟩), Ne.symm hne⟩
  have s₁ : XMach.act xsys (st k n w s (r + 1)) ⟨rest, .ready [s, 3] [s, 4] c c⟩ =
      ((st k n w s (r + 1)).takeAgent [s, 3], ⟨rest, .half [s, 3] [s, 4] c c⟩, 0) :=
    XMach.act_ready ha
  have s₂ := XMach.act_half (xs := xsys) (X := (st k n w s (r + 1)).takeAgent [s, 3])
    (todo := rest) (a := [s, 3]) (b := [s, 4]) (α := c) (β := c) (R := rhs)
    (by rw [ite_pos' ⟨assoc_some hb, hne⟩]; exact rule_cc)
  rw [rhs_agents, rhs_links, take_pair] at s₂
  exact .step (c₁ := 0) (c := 1) (k := 1) (fun h => by cases h) s₁
    (.step (c₁ := 1) (c := 0) (k := 0) (fun h => by cases h) s₂ (.refl _ _))

/-- It writes them and takes a fresh list of agents, in three actions. -/
theorem writes (k n w r : Nat) (rest : List (Id × Chain)) :
    Works xsys (st k n w (w + 1) r)
      ⟨rest, .write [] [(([w, 3], 1), ([w, 4], 1)), (([w, 4], 1), ([w, 3], 1))]⟩
      (st k n (w + 1) (w + 1) r) ⟨(st k n (w + 1) (w + 1) r).agents, .idle⟩ 0 3 := by
  have s₁ : XMach.act xsys (st k n w (w + 1) r)
      ⟨rest, .write [] [(([w, 3], 1), ([w, 4], 1)), (([w, 4], 1), ([w, 3], 1))]⟩ =
      ((st k n w (w + 1) r).putLink ([w, 3], 1) ([w, 4], 1),
        ⟨rest, .write [] [(([w, 4], 1), ([w, 3], 1))]⟩, 0) := rfl
  have s₂ : XMach.act xsys ((st k n w (w + 1) r).putLink ([w, 3], 1) ([w, 4], 1))
      ⟨rest, .write [] [(([w, 4], 1), ([w, 3], 1))]⟩ =
      (st k n (w + 1) (w + 1) r, ⟨rest, .write [] []⟩, 0) := rfl
  have s₃ : XMach.act xsys (st k n (w + 1) (w + 1) r) ⟨rest, .write [] []⟩ =
      (st k n (w + 1) (w + 1) r, ⟨(st k n (w + 1) (w + 1) r).agents, .idle⟩, 0) := rfl
  exact .step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₁
    (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂
      (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₃ (.refl _ _)))

/-- The first pair: the two agents face each other, and a thread at the
first of them has both after five actions. -/
theorem fire0 (k n r : Nat) :
    Works xsys (st k n 0 0 (r + 1)) ⟨pairsFrom 0 (r + 1), .idle⟩ (st k n 0 1 r)
      ⟨([0, 4], c) :: pairsFrom 1 r,
        .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩ 1 5 := by
  have ha : assoc [0, 3] (st k n 0 0 (r + 1)).agents = some c :=
    agent_x (Nat.le_refl 0) (by omega)
  have hb : assoc [0, 4] (st k n 0 0 (r + 1)).agents = some c :=
    agent_y (Nat.le_refl 0) (by omega)
  have hwire : assoc (([0, 3] : Id), 0) (st k n 0 0 (r + 1)).wires = some ([0, 4], 0) :=
    assoc_eq_of_unique (mem_wires.2 (.inr (.inr (.inl rfl)))) fun q' hq' => wire_head hq'
  have s₁ : Stays xsys (st k n 0 0 (r + 1))
      ⟨([0, 3], c) :: (([0, 4], c) :: pairsFrom 1 r), .idle⟩
      ⟨([0, 4], c) :: pairsFrom 1 r, .ready [0, 3] [0, 4] c c⟩ 3 :=
    .step (k := 2) (fun h => by cases h) (XMach.act_idle_pos ha)
      (.step (k := 1) (fun h => by cases h) (XMach.act_look hwire)
        (.step (k := 0) (fun h => by cases h)
          (XMach.act_seek_found (c := ([0, 4], 0))
            (by
              show (if (0 : Nat) = 0 then assoc [0, 4] (st k n 0 0 (r + 1)).agents
                else none) = some c
              rw [ite_pos' rfl]
              exact hb)
            ⟨by simp, by rw [rule_cc]; rfl⟩) (.refl _)))
  exact s₁.works.trans (take k n 0 0 r _)

/-- A later pair: the wire from the first agent runs through the auxiliary
ports of the pair before it and the segment that pair left, and a thread
has both agents after seven actions. -/
theorem fireS (k n j r : Nat) (hj : j < n) :
    Works xsys (st k n (j + 1) (j + 1) (r + 1)) ⟨pairsFrom (j + 1) (r + 1), .idle⟩
      (st k n (j + 1) (j + 2) r)
      ⟨([j + 1, 4], c) :: pairsFrom (j + 2) r,
        .write [] [(([j + 1, 3], 1), ([j + 1, 4], 1)), (([j + 1, 4], 1), ([j + 1, 3], 1))]⟩
      1 7 := by
  have ha : assoc [j + 1, 3] (st k n (j + 1) (j + 1) (r + 1)).agents = some c :=
    agent_x (Nat.le_refl _) (by omega)
  have hb : assoc [j + 1, 4] (st k n (j + 1) (j + 1) (r + 1)).agents = some c :=
    agent_y (Nat.le_refl _) (by omega)
  have hwire : assoc (([j + 1, 3] : Id), 0) (st k n (j + 1) (j + 1) (r + 1)).wires =
      some ([j, 3], 1) :=
    assoc_eq_of_unique (mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inr (.inl rfl)⟩)))))
      fun q' hq' => wire_x hq'
  have hn₁ : nextSeg (st k n (j + 1) (j + 1) (r + 1)).wires ([j, 3], 1) ([j + 1, 3], 0) =
      some ([j, 4], 1) :=
    nextSeg_some (mem_wires.2 (.inl ⟨j, Nat.lt_succ_self j, .inr rfl⟩)) (by simp)
      fun q hq hne => by
        rcases wire_x_aux hq with h | ⟨-, h⟩
        · exact absurd h hne
        · exact h
  have hn₂ : nextSeg (st k n (j + 1) (j + 1) (r + 1)).wires ([j, 4], 1) ([j, 3], 1) =
      some ([j + 1, 4], 0) :=
    nextSeg_some
      (mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inr (.inr (.inl rfl))⟩))))) (by simp)
      fun q hq hne => by
        rcases wire_y_aux hq with h | ⟨-, h⟩
        · exact h
        · exact absurd h hne
  have s₁ : Stays xsys (st k n (j + 1) (j + 1) (r + 1))
      ⟨([j + 1, 3], c) :: (([j + 1, 4], c) :: pairsFrom (j + 2) r), .idle⟩
      ⟨([j + 1, 4], c) :: pairsFrom (j + 2) r, .ready [j + 1, 3] [j + 1, 4] c c⟩ 5 :=
    .step (k := 4) (fun h => by cases h) (XMach.act_idle_pos ha)
      (.step (k := 3) (fun h => by cases h) (XMach.act_look hwire)
        (.step (k := 2) (fun h => by cases h)
          (XMach.act_seek_next (c := ([j, 3], 1)) (ite_neg' (by simp)) hn₁)
          (.step (k := 1) (fun h => by cases h)
            (XMach.act_seek_next (c := ([j, 4], 1)) (ite_neg' (by simp)) hn₂)
            (.step (k := 0) (fun h => by cases h)
              (XMach.act_seek_found (c := ([j + 1, 4], 0))
                (by
                  show (if (0 : Nat) = 0 then
                    assoc [j + 1, 4] (st k n (j + 1) (j + 1) (r + 1)).agents else none) = some c
                  rw [ite_pos' rfl]
                  exact hb)
                ⟨by simp, by rw [rule_cc]; rfl⟩) (.refl _)))))
  exact s₁.works.trans (take k n (j + 1) (j + 1) r _)

/-! The run of one thread. -/

/-- From the second pair on: a pass over the agents that lead nowhere and
ten actions for each pair, and one more pass at the end. -/
theorem runsS (k n : Nat) : ∀ (r j : Nat), j + 1 + r ≤ n →
    Works xsys (st k n (j + 1) (j + 1) r) ⟨(st k n (j + 1) (j + 1) r).agents, .idle⟩
      (st k n (j + 1 + r) (j + 1 + r) 0) ⟨[], .idle⟩ r ((r + 1) * (3 * k) + 10 * r)
  | 0, j, _ => by
    have w := (pass k n (j + 1) (j + 1) 0 []).works
    have e : (0 + 1) * (3 * k) + 10 * 0 = 3 * k := by omega
    rw [e]
    exact w
  | r + 1, j, h => by
    have w₁ := (pass k n (j + 1) (j + 1) (r + 1) (pairsFrom (j + 1) (r + 1))).works
    have w₂ := fireS k n j r (by omega)
    have w₃ := writes k n (j + 1) r (([j + 1, 4], c) :: pairsFrom (j + 2) r)
    have w₄ := runsS k n r (j + 1) (by omega)
    have w := ((w₁.trans w₂).trans w₃).trans w₄
    have e₀ : j + 1 + 1 + r = j + 1 + (r + 1) := by omega
    have e₁ : 0 + 1 + 0 + r = r + 1 := by omega
    have e₂ : 3 * k + 7 + 3 + ((r + 1) * (3 * k) + 10 * r) =
        (r + 1 + 1) * (3 * k) + 10 * (r + 1) := by
      rw [Nat.add_mul (r + 1) 1 (3 * k), Nat.one_mul]
      omega
    rw [e₀, e₁, e₂] at w
    exact w

/-- A thread that has taken the first pair and has its segments to write
goes on alone to the end. -/
theorem paused (k n r : Nat) (h : r + 1 ≤ n) (rest : List (Id × Chain)) :
    Works xsys (st k n 0 1 r)
      ⟨rest, .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩
      (st k n (r + 1) (r + 1) 0) ⟨[], .idle⟩ r (3 + ((r + 1) * (3 * k) + 10 * r)) := by
  have w := (writes k n 0 r rest).trans (runsS k n r 0 (by omega))
  have e₀ : 0 + 1 + r = r + 1 := by omega
  have e₁ : 0 + r = r := by omega
  rw [e₀, e₁] at w
  exact w

/-- **The run of one thread on the chain, counted.** -/
theorem runs0 (k n r : Nat) (h : r + 1 ≤ n) :
    Works xsys (st k n 0 0 (r + 1)) ⟨(st k n 0 0 (r + 1)).agents, .idle⟩
      (st k n (r + 1) (r + 1) 0) ⟨[], .idle⟩ (r + 1)
      (3 * k + 8 + ((r + 1) * (3 * k) + 10 * r)) := by
  have w₁ := (pass k n 0 0 (r + 1) (pairsFrom 0 (r + 1))).works
  have w := (w₁.trans (fire0 k n r)).trans (paused k n r h _)
  have e₁ : 0 + 1 + r = r + 1 := by omega
  have e₂ : 3 * k + 5 + (3 + ((r + 1) * (3 * k) + 10 * r)) =
      3 * k + 8 + ((r + 1) * (3 * k) + 10 * r) := by omega
  rw [e₁, e₂] at w
  exact w

/-- With the first pair taken and nothing written yet, a second thread
finds nothing: the agents of the first pair are gone, and every other agent
leads nowhere. -/
theorem idle_pass (k n r : Nat) (h : r + 1 ≤ n) :
    Stays xsys (st (k + 1) n 0 1 r)
      ⟨lone k ++ (pairsFrom 0 (r + 1) ++ [([k, 0], c)]), .idle⟩ ⟨[], .idle⟩
      (3 * k + 2 + 6 * r + 3) := by
  have s₁ := Stays.inert_pass (xs := xsys) (X := st (k + 1) n 0 1 r)
    (pairsFrom 0 (r + 1) ++ [([k, 0], c)]) (lone k) fun e he => by
      obtain ⟨j, hj, rfl⟩ := mem_lone.1 he
      exact inert_lone (by omega)
  rw [lone_length] at s₁
  have s₂ : Stays xsys (st (k + 1) n 0 1 r)
      ⟨([0, 3], c) :: (([0, 4], c) :: (pairsFrom 1 r ++ [([k, 0], c)])), .idle⟩
      ⟨([0, 4], c) :: (pairsFrom 1 r ++ [([k, 0], c)]), .idle⟩ 1 :=
    Stays.absent _ (agent_gone (by omega) 3 (by omega) c)
  have s₃ : Stays xsys (st (k + 1) n 0 1 r)
      ⟨([0, 4], c) :: (pairsFrom 1 r ++ [([k, 0], c)]), .idle⟩
      ⟨pairsFrom 1 r ++ [([k, 0], c)], .idle⟩ 1 :=
    Stays.absent _ (agent_gone (by omega) 4 (by omega) c)
  have s₄ := Stays.inert_pass (xs := xsys) (X := st (k + 1) n 0 1 r) [([k, 0], c)]
    (pairsFrom 1 r) fun e he => by
      obtain ⟨j, h₁, h₂, he' | he'⟩ := mem_pairsFrom.1 he
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [he']
        exact inert_x (by omega) (by omega) (by omega) (by omega)
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [he']
        exact inert_y (by omega) (by omega) (by omega) (by omega)
  rw [pairsFrom_length] at s₄
  have s₅ : Stays xsys (st (k + 1) n 0 1 r) ⟨[([k, 0], c)], .idle⟩ ⟨[], .idle⟩ 3 :=
    Stays.inert _ (inert_lone (by omega))
  have w := (((s₁.trans s₂).trans s₃).trans s₄).trans s₅
  have e : 3 * k + 1 + 1 + 3 * (2 * r) + 3 = 3 * k + 2 + 6 * r + 3 := by omega
  rw [e] at w
  exact w

/-- **A starved thread makes every claim.**  On `k + 1` agents that lead
nowhere and a chain of `n + 1` pairs, with two threads: the first passes the
agents and takes the first pair; the second then makes its whole pass and
finds nothing; from then on the first gets every `F`-th action.  It has
`n` more pairs to fire, with a pass before each, and the program is not at
rest after `F` times its count of actions, less `F`, or fewer. -/
theorem starved_chain (k n F : Nat) (hF : 0 < F) :
    ∀ i, i + F ≤ F * (3 + ((n + 1) * (3 * (k + 1)) + 10 * n)) →
      ¬ ((XMach.init (net (k + 1) (n + 1)) 2).trace xsys
        (handoff (3 * (k + 1) + 5) (3 * k + 2 + 6 * n + 3) F) i).1.resting = true := by
  intro i hi hr
  have hinit : XMach.init (net (k + 1) (n + 1)) 2 =
      ⟨net (k + 1) (n + 1), [⟨(net (k + 1) (n + 1)).agents, .idle⟩,
        ⟨lone k ++ (pairsFrom 0 (n + 1) ++ [([k, 0], c)]), .idle⟩]⟩ := by
    rw [XMach.init_two]
    show (⟨net (k + 1) (n + 1), [⟨(net (k + 1) (n + 1)).agents, .idle⟩,
      ⟨(lone k ++ pairsFrom 0 (n + 1)) ++ [([k, 0], c)], .idle⟩]⟩ : XMach Chain) = _
    rw [List.append_assoc]
  have w₀ := ((pass (k + 1) (n + 1) 0 0 (n + 1) (pairsFrom 0 (n + 1))).works.trans
    (fire0 (k + 1) (n + 1) n)).trace_at
    [⟨(net (k + 1) (n + 1)).agents, .idle⟩,
      ⟨lone k ++ (pairsFrom 0 (n + 1) ++ [([k, 0], c)]), .idle⟩] 0 rfl
  have w₁ := (idle_pass k (n + 1) n (Nat.le_refl _)).works.trace_at
    [⟨([0, 4], c) :: pairsFrom 1 n,
        .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩,
      ⟨lone k ++ (pairsFrom 0 (n + 1) ++ [([k, 0], c)]), .idle⟩] 1 rfl
  have hs : ∀ d, ((⟨net (k + 1) (n + 1), [⟨(net (k + 1) (n + 1)).agents, .idle⟩,
        ⟨lone k ++ (pairsFrom 0 (n + 1) ++ [([k, 0], c)]), .idle⟩]⟩ : XMach Chain).trace xsys
        (handoff (3 * (k + 1) + 5) (3 * k + 2 + 6 * n + 3) F)
        (3 * (k + 1) + 5 + (3 * k + 2 + 6 * n + 3) + d)).1 =
      ((⟨st (k + 1) (n + 1) 0 1 n, [⟨([0, 4], c) :: pairsFrom 1 n,
          .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩,
        ⟨[], .idle⟩]⟩ : XMach Chain).trace xsys (starve F) d).1 :=
    XMach.trace_handoff (xs := xsys) (F := F) w₀ w₁
  have hr' := XMach.resting_trace (xs := xsys) _ hr
    (3 * (k + 1) + 5 + (3 * k + 2 + 6 * n + 3))
  rw [Nat.add_comm i, hinit, hs i] at hr'
  refine XMach.starved_worker (xs := xsys) (u := 0) (starve F) (M := ⟨st (k + 1) (n + 1) 0 1 n,
      [⟨([0, 4], c) :: pairsFrom 1 n,
        .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩,
      ⟨[], .idle⟩]⟩) rfl ?_ (paused (k + 1) (n + 1) n (Nat.le_refl _) _) hF
    (starve_sparse F) i hi hr'
  intro t T ht h
  cases t with
  | zero => exact absurd rfl ht
  | succ t =>
    cases t with
    | zero => exact (Option.some.inj h).symm
    | succ t => cases h

/-! The net is a valid input. -/

theorem wire_lone_aux {k n w j : Nat} {q' : Port}
    (h : ((([j, 0] : Id), 1), q') ∈ wires k n w) : q' = ([j, 2], 0) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | simp at h

theorem wire_loneFree2 {k n w j : Nat} {q' : Port}
    (h : ((([j, 2] : Id), 0), q') ∈ wires k n w) : q' = ([j, 0], 1) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | simp at h

theorem wire_head' {k n w : Nat} {q' : Port}
    (h : ((([0, 4] : Id), 0), q') ∈ wires k n w) : q' = ([0, 3], 0) := by
  rcases mem_wires.1 h with ⟨j', hj', h | h⟩ | ⟨j', hj', h | h | h | h⟩ | h | h |
      ⟨j', hj', h | h | h | h⟩ <;>
    first
      | (simp at h; rw [h])
      | simp at h

theorem agent_iff {k n : Nat} {i : Id} {α : Chain} :
    (net k n).toNet.agent i α ↔
      (∃ j, j < k ∧ i = [j, 0]) ∨ ∃ j, j < n ∧ (i = [j, 3] ∨ i = [j, 4]) := by
  show (i, α) ∈ lone k ++ pairsFrom 0 n ↔ _
  rw [List.mem_append, mem_lone, mem_pairsFrom]
  cases α
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, -, hj, h | h⟩)
    · exact .inl ⟨j, hj, (Prod.mk.inj h).1⟩
    · exact .inr ⟨j, by omega, .inl (Prod.mk.inj h).1⟩
    · exact .inr ⟨j, by omega, .inr (Prod.mk.inj h).1⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl | rfl⟩)
    · exact .inl ⟨j, hj, rfl⟩
    · exact .inr ⟨j, Nat.zero_le j, by omega, .inl rfl⟩
    · exact .inr ⟨j, Nat.zero_le j, by omega, .inr rfl⟩

theorem free_iff {k n : Nat} {p : Port} :
    (net k n).toNet.free p ↔
      (∃ j, j < k ∧ (p = ([j, 1], 0) ∨ p = ([j, 2], 0))) ∨ p = ([n, 3], 0) ∨ p = ([n, 4], 0) := by
  show p ∈ loneFree k ++ [([n, 3], 0), ([n, 4], 0)] ↔ _
  unfold loneFree
  simp only [List.mem_append, mem_gen, List.mem_cons, List.not_mem_nil, or_false]

theorem used_len {k n : Nat} {i : Id} (h : (net k n).toNet.Used i) : i.length = 2 := by
  rcases h with ⟨γ, hg⟩ | ⟨x, q, hl⟩ | ⟨x, hf⟩
  · rcases agent_iff.1 hg with ⟨j, -, rfl⟩ | ⟨j, -, rfl | rfl⟩ <;> rfl
  · rcases mem_wires.1 hl with ⟨j, hj, h | h⟩ | ⟨j, hj, h | h | h | h⟩ | h | h |
        ⟨j, hj, h | h | h | h⟩ <;>
      (rw [(Prod.mk.inj (Prod.mk.inj h).1).1]; rfl)
  · rcases free_iff.1 hf with ⟨j, -, e | e⟩ | e | e <;>
      (rw [(Prod.mk.inj e).1]; rfl)

/-- The net is a valid input: its segments match its ends in pairs. -/
theorem net_matching (k n : Nat) : (net k n).toNet.Matching ar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i α β _ _
    cases α
    cases β
    rfl
  · intro p q h
    rcases mem_wires.1 h with ⟨j, hj, h | h⟩ | ⟨j, hj, h | h | h | h⟩ | h | h |
      ⟨j, hj, h | h | h | h⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    · omega
    · omega
    · exact mem_wires.2 (.inr (.inl ⟨j, hj, .inr (.inl rfl)⟩))
    · exact mem_wires.2 (.inr (.inl ⟨j, hj, .inl rfl⟩))
    · exact mem_wires.2 (.inr (.inl ⟨j, hj, .inr (.inr (.inr rfl))⟩))
    · exact mem_wires.2 (.inr (.inl ⟨j, hj, .inr (.inr (.inl rfl))⟩))
    · exact mem_wires.2 (.inr (.inr (.inr (.inl rfl))))
    · exact mem_wires.2 (.inr (.inr (.inl rfl)))
    · exact mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inr (.inl rfl)⟩))))
    · exact mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inl rfl⟩))))
    · exact mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inr (.inr (.inr rfl))⟩))))
    · exact mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inr (.inr (.inl rfl))⟩))))
  · intro p h
    rcases mem_wires.1 h with ⟨j, hj, h | h⟩ | ⟨j, hj, h | h | h | h⟩ | h | h |
        ⟨j, hj, h | h | h | h⟩ <;>
      (obtain ⟨h₁, h₂⟩ := Prod.mk.inj h; rw [h₁] at h₂; simp at h₂)
  · intro p q q' h h'
    rcases mem_wires.1 h with ⟨j, hj, h | h⟩ | ⟨j, hj, h | h | h | h⟩ | h | h |
      ⟨j, hj, h | h | h | h⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    · omega
    · omega
    · exact (wire_lone h').symm
    · exact (wire_loneFree h').symm
    · exact (wire_lone_aux h').symm
    · exact (wire_loneFree2 h').symm
    · exact (wire_head h').symm
    · exact (wire_head' h').symm
    · rcases wire_x_aux h' with e | ⟨e, -⟩
      · exact e.symm
      · omega
    · exact (wire_x h').symm
    · rcases wire_y_aux h' with e | ⟨e, -⟩
      · exact e.symm
      · omega
    · exact (wire_y h').symm
  · intro p q h
    rcases mem_wires.1 h with ⟨j, hj, h | h⟩ | ⟨j, hj, h | h | h | h⟩ | h | h |
      ⟨j, hj, h | h | h | h⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    · omega
    · omega
    · exact .inr ⟨c, agent_iff.2 (.inl ⟨j, hj, rfl⟩), Nat.zero_le _⟩
    · exact .inl (free_iff.2 (.inl ⟨j, hj, .inl rfl⟩))
    · exact .inr ⟨c, agent_iff.2 (.inl ⟨j, hj, rfl⟩), Nat.le_refl _⟩
    · exact .inl (free_iff.2 (.inl ⟨j, hj, .inr rfl⟩))
    · cases n with
      | zero => exact .inl (free_iff.2 (.inr (.inl rfl)))
      | succ n' => exact .inr ⟨c, agent_iff.2 (.inr ⟨0, Nat.succ_pos n', .inl rfl⟩), Nat.zero_le _⟩
    · cases n with
      | zero => exact .inl (free_iff.2 (.inr (.inr rfl)))
      | succ n' => exact .inr ⟨c, agent_iff.2 (.inr ⟨0, Nat.succ_pos n', .inr rfl⟩), Nat.zero_le _⟩
    · exact .inr ⟨c, agent_iff.2 (.inr ⟨j, hj, .inl rfl⟩), Nat.le_refl _⟩
    · rcases Nat.lt_or_ge (j + 1) n with h' | h'
      · exact .inr ⟨c, agent_iff.2 (.inr ⟨j + 1, h', .inl rfl⟩), Nat.zero_le _⟩
      · have e : j + 1 = n := by omega
        rw [e]
        exact .inl (free_iff.2 (.inr (.inl rfl)))
    · exact .inr ⟨c, agent_iff.2 (.inr ⟨j, hj, .inr rfl⟩), Nat.le_refl _⟩
    · rcases Nat.lt_or_ge (j + 1) n with h' | h'
      · exact .inr ⟨c, agent_iff.2 (.inr ⟨j + 1, h', .inr rfl⟩), Nat.zero_le _⟩
      · have e : j + 1 = n := by omega
        rw [e]
        exact .inl (free_iff.2 (.inr (.inr rfl)))
  · intro p h
    rcases h with hf | ⟨γ, hag, hle⟩
    · rcases free_iff.1 hf with ⟨j, hj, rfl | rfl⟩ | rfl | rfl
      · exact ⟨([j, 0], 0), mem_wires.2 (.inr (.inl ⟨j, hj, .inr (.inl rfl)⟩))⟩
      · exact ⟨([j, 0], 1), mem_wires.2 (.inr (.inl ⟨j, hj, .inr (.inr (.inr rfl))⟩))⟩
      · cases n with
        | zero => exact ⟨([0, 4], 0), mem_wires.2 (.inr (.inr (.inl rfl)))⟩
        | succ n' =>
          exact ⟨([n', 3], 1), mem_wires.2 (.inr (.inr (.inr (.inr
            ⟨n', Nat.lt_succ_self n', .inr (.inl rfl)⟩))))⟩
      · cases n with
        | zero => exact ⟨([0, 3], 0), mem_wires.2 (.inr (.inr (.inr (.inl rfl))))⟩
        | succ n' =>
          exact ⟨([n', 4], 1), mem_wires.2 (.inr (.inr (.inr (.inr
            ⟨n', Nat.lt_succ_self n', .inr (.inr (.inr rfl))⟩))))⟩
    · obtain ⟨i, x⟩ := p
      have hag' : (net k n).toNet.agent i γ := hag
      have hle' : x ≤ 1 := hle
      have hx : x = 0 ∨ x = 1 := by omega
      rcases agent_iff.1 hag' with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl | rfl⟩
      · rcases hx with rfl | rfl
        · exact ⟨([j, 1], 0), mem_wires.2 (.inr (.inl ⟨j, hj, .inl rfl⟩))⟩
        · exact ⟨([j, 2], 0), mem_wires.2 (.inr (.inl ⟨j, hj, .inr (.inr (.inl rfl))⟩))⟩
      · rcases hx with rfl | rfl
        · cases j with
          | zero => exact ⟨([0, 4], 0), mem_wires.2 (.inr (.inr (.inl rfl)))⟩
          | succ j' =>
            exact ⟨([j', 3], 1), mem_wires.2 (.inr (.inr (.inr (.inr
              ⟨j', by omega, .inr (.inl rfl)⟩))))⟩
        · exact ⟨([j + 1, 3], 0), mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inl rfl⟩))))⟩
      · rcases hx with rfl | rfl
        · cases j with
          | zero => exact ⟨([0, 3], 0), mem_wires.2 (.inr (.inr (.inr (.inl rfl))))⟩
          | succ j' =>
            exact ⟨([j', 4], 1), mem_wires.2 (.inr (.inr (.inr (.inr
              ⟨j', by omega, .inr (.inr (.inr rfl))⟩))))⟩
        · exact ⟨([j + 1, 4], 0), mem_wires.2 (.inr (.inr (.inr (.inr
            ⟨j, hj, .inr (.inr (.inl rfl))⟩))))⟩
  · intro i x α hf hag
    rcases free_iff.1 hf with ⟨j, -, e | e⟩ | e | e <;>
      (have ei := (Prod.mk.inj e).1
       subst ei
       rcases agent_iff.1 hag with ⟨j', hj', e'⟩ | ⟨j', hj', e' | e'⟩ <;> simp at e' <;> omega)
  · intro a α l hag hu
    have ha : a.length = 2 := by
      rcases agent_iff.1 hag with ⟨j, -, rfl⟩ | ⟨j, -, rfl | rfl⟩ <;> rfl
    have hl := used_len hu
    rw [List.length_append, ha] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)

/-- The net is well formed. -/
theorem net_wf (k n : Nat) : (net k n).toNet.WF ar :=
  (XNet.ok_iff_matching.2 (net_matching k n)).1

/-- No agent is listed twice. -/
theorem net_nodup (k n : Nat) : ((net k n).agents.map Prod.fst).Nodup := by
  show ((lone k ++ pairsFrom 0 n).map Prod.fst).Nodup
  rw [List.map_append]
  refine List.nodup_append.2 ⟨?_, ?_, fun a ha b hb e => ?_⟩
  · unfold lone
    rw [map_gen]
    refine nodup_gen (fun j => List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
      (fun i j x hi hj => ?_) k
    have e₁ : x = [i, 0] := List.mem_singleton.1 hi
    have e₂ : x = [j, 0] := List.mem_singleton.1 hj
    rw [e₁] at e₂
    exact List.head_eq_of_cons_eq e₂
  · unfold pairsFrom
    rw [map_asc]
    refine nodup_asc (fun j => ?_) (fun i j x hi hj => ?_) n 0
    · show ([[j, 3], [j, 4]] : List Id).Nodup
      simp
    · have hi' : x = [i, 3] ∨ x = [i, 4] := by
        rcases List.mem_cons.1 hi with h | h
        · exact .inl h
        · exact .inr (List.mem_singleton.1 h)
      have hj' : x = [j, 3] ∨ x = [j, 4] := by
        rcases List.mem_cons.1 hj with h | h
        · exact .inl h
        · exact .inr (List.mem_singleton.1 h)
      rcases hi' with rfl | rfl <;> rcases hj' with h | h <;>
        exact List.head_eq_of_cons_eq h
  · obtain ⟨e₁, h₁, rfl⟩ := List.mem_map.1 ha
    obtain ⟨e₂, h₂, rfl⟩ := List.mem_map.1 hb
    obtain ⟨j, -, rfl⟩ := mem_lone.1 h₁
    obtain ⟨j', -, -, rfl | rfl⟩ := mem_pairsFrom.1 h₂ <;> simp at e

/-- The bound for one pass on this net: eleven actions for each agent that
leads nowhere and twenty for each pair, and two. -/
theorem net_passBound (k n : Nat) : (net k n).passBound n 0 2 = 11 * k + 20 * n + 2 := by
  have h₁ := length_gen
    (f := fun j => [((([j, 0] : Id), 0), (([j, 1] : Id), 0)), (([j, 1], 0), ([j, 0], 0)),
      (([j, 0], 1), ([j, 2], 0)), (([j, 2], 0), ([j, 0], 1))]) (c := 4) (fun _ => rfl) k
  have h₂ := length_gen
    (f := fun j => [((([j, 3] : Id), 1), (([j + 1, 3] : Id), 0)), (([j + 1, 3], 0), ([j, 3], 1)),
      (([j, 4], 1), ([j + 1, 4], 0)), (([j + 1, 4], 0), ([j, 4], 1))]) (c := 4) (fun _ => rfl) n
  have ha : (net k n).agents.length = k + 2 * n := by
    show (lone k ++ pairsFrom 0 n).length = _
    rw [List.length_append, lone_length, pairsFrom_length]
  have hw : (net k n).wires.length = 4 * k + (2 + 4 * n) := by
    show ([] ++ (loneWires k ++ (headWires ++ chainWires n))).length = _
    rw [List.nil_append, List.length_append, List.length_append]
    show (gen _ k).length + (2 + (gen _ n).length) = _
    rw [h₁, h₂]
  show 7 * ((net k n).agents.length + 0 * n) + ((net k n).wires.length + 2 * n) = _
  rw [ha, hw]
  omega

/-- **One thread alone on the chain**: with `n + 1` pairs it is at rest
after `3 * k + 8 + (n + 1) * (3 * k) + 10 * n` actions, with every pair
fired, and not before. -/
theorem solo_exact (k n : Nat) :
    (XMach.init (net k (n + 1)) 1).trace xsys (fun _ => 0)
        (3 * k + 8 + ((n + 1) * (3 * k) + 10 * n)) =
        (⟨st k (n + 1) (n + 1) (n + 1) 0, [⟨[], .idle⟩]⟩, n + 1) ∧
      ∀ i, i < 3 * k + 8 + ((n + 1) * (3 * k) + 10 * n) →
        ¬ ((XMach.init (net k (n + 1)) 1).trace xsys (fun _ => 0) i).1.resting = true := by
  have w := (runs0 k (n + 1) n (Nat.le_refl _)).trace
  rw [XMach.init_one]
  exact w

/-- The chain of `n + 1` pairs has a normal form, `n + 1` steps away. -/
theorem net_steps (k n : Nat) :
    ∃ N', Steps (Step xsys.sys) (n + 1) (net k (n + 1)).toNet N' ∧
      Normal (Step xsys.sys) N' := by
  obtain ⟨hL, -⟩ := solo_exact k n
  have hX : (net k (n + 1)).toNet.WF xsys.sys.ar := net_wf k (n + 1)
  have live := XMach.trace_live (xs := xsys) (fun _ => 0)
    (XMach.init_live hX (Nat.succ_pos 0))
  have hrest : ((XMach.init (net k (n + 1)) 1).trace xsys (fun _ => 0)
      (3 * k + 8 + ((n + 1) * (3 * k) + 10 * n))).1.resting = true := by
    rw [hL]
    rfl
  have hc : ((XMach.init (net k (n + 1)) 1).trace xsys (fun _ => 0)
      (3 * k + 8 + ((n + 1) * (3 * k) + 10 * n))).2 = n + 1 := by rw [hL]
  obtain ⟨hq, hnorm⟩ := (live _).rest hrest
  have run := XMach.trace_run xsys (fun _ => 0) (XMach.init (net k (n + 1)) 1)
    (3 * k + 8 + ((n + 1) * (3 * k) + 10 * n))
  rw [XMach.init_toMach, hc] at run
  exact ⟨_, (run.final hX hq hnorm).1, hnorm⟩

/-- **The window multiplies every pass.**  On `k + 1` agents that lead
nowhere and a chain of `n + 1` pairs, take two threads, a window `F` longer
than a pass over the agents and than a look at every pair, and the schedule
`handoff`, which is fair with that window.  The bound of `XMach.fair_bound`
puts the threads at rest after `F` times

    (n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4

actions, and they are not at rest after `F` times

    (n + 1) * (3 * (k + 1)) + 10 * n + 3

actions, less `F`: every one of the `n + 1` passes of the starved thread is
stretched by the window. -/
theorem window_chain (k n F : Nat) (hF : 3 * k + 6 * n + 8 < F) :
    (∀ u, u < 2 → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧
        handoff (3 * (k + 1) + 5) (3 * k + 2 + 6 * n + 3) F j = u) ∧
      (∀ i, F * ((n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4) ≤ i →
        ((XMach.init (net (k + 1) (n + 1)) 2).trace xsys
          (handoff (3 * (k + 1) + 5) (3 * k + 2 + 6 * n + 3) F) i).1.resting = true) ∧
      ∀ i, i + F ≤ F * ((n + 1) * (3 * (k + 1)) + 10 * n + 3) →
        ¬ ((XMach.init (net (k + 1) (n + 1)) 2).trace xsys
          (handoff (3 * (k + 1) + 5) (3 * k + 2 + 6 * n + 3) F) i).1.resting = true := by
  have hfair := handoff_fair (b := 3 * (k + 1) + 5) (c := 3 * k + 2 + 6 * n + 3) (F := F)
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨hfair, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨N', hs, hn⟩ := net_steps (k + 1) n
    have hX : (net (k + 1) (n + 1)).toNet.WF xsys.sys.ar := net_wf (k + 1) (n + 1)
    have hb := XMach.fair_bound (xs := xsys) hX (net_nodup (k + 1) (n + 1)) (nt := 2)
      (by decide) xsys_bounded hs hn _ hfair i
    refine (hb ?_).1
    rw [net_passBound]
    have e₁ : n + 1 + 1 = n + 2 := rfl
    have e₂ : 11 * (k + 1) + 20 * (n + 1) + 2 = 11 * k + 20 * n + 33 := by omega
    rw [e₁, e₂]
    have e₃ : (n + 2) * (11 * k + 20 * n + 33) + (n + 1) * (0 + 2 + 1) + 1 =
        (n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4 := by omega
    rw [e₃]
    exact hi
  · refine starved_chain k n F (by omega) i ?_
    have e : 3 + ((n + 1) * (3 * (k + 1)) + 10 * n) =
        (n + 1) * (3 * (k + 1)) + 10 * n + 3 := by omega
    rw [e]
    exact hi

/-! ### The chain listed from the last pair to the first

The same net with the pairs listed the other way round: a pass now meets
the pairs that are not active yet before the one that is.  With two threads
that take turns, the second, which starts one agent further down the list,
takes the first pair; the first thread, three actions behind, has passed
every other pair by then, finds the first pair gone, and rests for good.
From then on the second thread makes every claim, however short the window
in which it is starved. -/

/-- The pairs from number `s` on, `r` of them, the last one first. -/
def pairsDown (s r : Nat) : List (Id × Chain) := desc (fun j => [([j, 3], c), ([j, 4], c)]) s r

theorem pairsDown_perm (s r : Nat) : (pairsDown s r).Perm (pairsFrom s r) := desc_perm _ r s

theorem mem_pairsDown {s r : Nat} {e : Id × Chain} :
    e ∈ pairsDown s r ↔ ∃ j, s ≤ j ∧ j < s + r ∧ (e = ([j, 3], c) ∨ e = ([j, 4], c)) :=
  (pairsDown_perm s r).mem_iff.trans mem_pairsFrom

theorem pairsDown_length (s r : Nat) : (pairsDown s r).length = 2 * r := by
  rw [(pairsDown_perm s r).length_eq, pairsFrom_length]

/-- The memory `st` with the pairs listed the last one first. -/
def rst (k n w s r : Nat) : XNet Chain :=
  ⟨lone k ++ pairsDown s r, loneFree k ++ [([n, 3], 0), ([n, 4], 0)], wires k n w⟩

/-- `k` agents that lead nowhere, listed first, and a chain of `n` pairs
listed from the last to the first, which is the active one. -/
def rnet (k n : Nat) : XNet Chain := rst k n 0 0 n

theorem rst_perm (k n w s r : Nat) : (rst k n w s r).agents.Perm (st k n w s r).agents :=
  List.Perm.append_left (lone k) (pairsDown_perm s r)

/-- The same agents are in memory. -/
theorem rst_assoc (k n w s r : Nat) (i : Id) :
    assoc i (rst k n w s r).agents = assoc i (st k n w s r).agents := by
  have hm : ∀ e, e ∈ (rst k n w s r).agents ↔ e ∈ (st k n w s r).agents :=
    fun e => (rst_perm k n w s r).mem_iff
  cases h : assoc i (st k n w s r).agents with
  | some v =>
    cases v
    exact assoc_some ((hm _).2 (assoc_mem h))
  | none =>
    cases h' : assoc i (rst k n w s r).agents with
    | none => rfl
    | some v =>
      cases v
      have h'' := assoc_some ((hm _).1 (assoc_mem h'))
      rw [h] at h''
      cases h''

/-- An agent that leads nowhere does so in whatever order the agents are
listed. -/
theorem rst_inert {k n w s r : Nat} {e : Id × Chain} (h : (st k n w s r).Inert e) :
    (rst k n w s r).Inert e := by
  obtain ⟨h₁, q, h₂, h₃, h₄⟩ := h
  refine ⟨?_, q, h₂, ?_, h₄⟩
  · rw [rst_assoc]
    exact h₁
  · rw [rst_assoc]
    exact h₃

/-- A thread passes agents that lead nowhere in three actions each. -/
theorem rpass {k k' : Nat} (hk : k' ≤ k) (n w s r : Nat) (rest : List (Id × Chain)) :
    Stays xsys (rst k n w s r) ⟨lone k' ++ rest, .idle⟩ ⟨rest, .idle⟩ (3 * k') := by
  have h := Stays.inert_pass (xs := xsys) (X := rst k n w s r) rest (lone k') fun e he => by
    obtain ⟨j, hj, rfl⟩ := mem_lone.1 he
    exact rst_inert (inert_lone (by omega))
  rw [lone_length] at h
  exact h

/-- It passes the pairs that are not active yet in six actions each: none
of them is the first pair left, and the pair before each has not had its
segment written. -/
theorem rpending {k n w s r s' r' : Nat} (hw : w < s') (h₁ : s ≤ s') (h₂ : s' + r' ≤ s + r)
    (hn : s' + r' ≤ n + 1) (rest : List (Id × Chain)) :
    Stays xsys (rst k n w s r) ⟨pairsDown s' r' ++ rest, .idle⟩ ⟨rest, .idle⟩ (6 * r') := by
  have h := Stays.inert_pass (xs := xsys) (X := rst k n w s r) rest (pairsDown s' r')
    fun e he => by
      obtain ⟨j, hj₁, hj₂, he' | he'⟩ := mem_pairsDown.1 he
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [he']
        exact rst_inert (inert_x (by omega) (by omega) (by omega) (by omega))
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [he']
        exact rst_inert (inert_y (by omega) (by omega) (by omega) (by omega))
  rw [pairsDown_length] at h
  have e : 3 * (2 * r') = 6 * r' := by omega
  rw [e] at h
  exact h

/-- Taking the two agents of the first pair left leaves the rest. -/
theorem rtake_pair (k n w s r : Nat) :
    ((rst k n w s (r + 1)).takeAgent [s, 3]).takeAgent [s, 4] = rst k n w (s + 1) r := by
  have hl : ∀ e, e ∈ lone k → e.1 ≠ [s, 3] ∧ e.1 ≠ [s, 4] := by
    intro e he
    obtain ⟨j, -, rfl⟩ := mem_lone.1 he
    simp
  have hp : ∀ e, e ∈ pairsDown (s + 1) r → e.1 ≠ [s, 3] ∧ e.1 ≠ [s, 4] := by
    intro e he
    obtain ⟨j, hj, -, rfl | rfl⟩ := mem_pairsDown.1 he
    · constructor
      · intro h
        simp at h
        omega
      · intro h
        simp at h
    · constructor
      · intro h
        simp at h
      · intro h
        simp at h
        omega
  have hne : ([s, 4] : Id) ≠ [s, 3] := by simp
  have e1 : (lone k ++ pairsDown s (r + 1)).filter (fun e => decide (e.1 ≠ [s, 3])) =
      lone k ++ (pairsDown (s + 1) r ++ [([s, 4], c)]) := by
    show (lone k ++ (pairsDown (s + 1) r ++ (([s, 3], c) :: [([s, 4], c)]))).filter _ = _
    rw [List.filter_append, List.filter_append, filter_ne fun e he => (hl e he).1,
      filter_ne fun e he => (hp e he).1, filter_ne_cons_same, filter_ne_cons_other hne]
    rfl
  have e2 : (lone k ++ (pairsDown (s + 1) r ++ [([s, 4], c)])).filter
      (fun e => decide (e.1 ≠ [s, 4])) = lone k ++ pairsDown (s + 1) r := by
    rw [List.filter_append, List.filter_append, filter_ne fun e he => (hl e he).2,
      filter_ne fun e he => (hp e he).2, filter_ne_cons_same]
    show lone k ++ (pairsDown (s + 1) r ++ []) = _
    rw [List.append_nil]
  show (⟨((lone k ++ pairsDown s (r + 1)).filter fun e => decide (e.1 ≠ [s, 3])).filter
      fun e => decide (e.1 ≠ [s, 4]), loneFree k ++ [([n, 3], 0), ([n, 4], 0)],
      wires k n w⟩ : XNet Chain) =
    ⟨lone k ++ pairsDown (s + 1) r, loneFree k ++ [([n, 3], 0), ([n, 4], 0)], wires k n w⟩
  rw [e1, e2]

/-- A thread that has found the first pair left takes its first agent. -/
theorem rready (k n w s r : Nat) (rest : List (Id × Chain)) :
    XMach.act xsys (rst k n w s (r + 1)) ⟨rest, .ready [s, 3] [s, 4] c c⟩ =
      ((rst k n w s (r + 1)).takeAgent [s, 3], ⟨rest, .half [s, 3] [s, 4] c c⟩, 0) :=
  XMach.act_ready (by
    rw [rst_assoc]
    exact agent_x (Nat.le_refl s) (by omega))

/-- It then takes the second, which completes the claim, and has two
segments to write. -/
theorem rhalf (k n w s r : Nat) (rest : List (Id × Chain)) :
    XMach.act xsys ((rst k n w s (r + 1)).takeAgent [s, 3]) ⟨rest, .half [s, 3] [s, 4] c c⟩ =
      (rst k n w (s + 1) r,
        ⟨rest, .write [] [(([s, 3], 1), ([s, 4], 1)), (([s, 4], 1), ([s, 3], 1))]⟩, 1) := by
  have hne : ([s, 3] : Id) ≠ [s, 4] := by simp
  have hb : (([s, 4] : Id), c) ∈ ((rst k n w s (r + 1)).takeAgent [s, 3]).agents :=
    XNet.mem_takeAgent.2 ⟨List.mem_append_right _
      (mem_pairsDown.2 ⟨s, Nat.le_refl s, by omega, .inr rfl⟩), Ne.symm hne⟩
  have s₂ := XMach.act_half (xs := xsys) (X := (rst k n w s (r + 1)).takeAgent [s, 3])
    (todo := rest) (a := [s, 3]) (b := [s, 4]) (α := c) (β := c) (R := rhs)
    (by rw [ite_pos' ⟨assoc_some hb, hne⟩]; exact rule_cc)
  rw [rhs_agents, rhs_links, rtake_pair] at s₂
  exact s₂

theorem rtake (k n w s r : Nat) (rest : List (Id × Chain)) :
    Works xsys (rst k n w s (r + 1)) ⟨rest, .ready [s, 3] [s, 4] c c⟩ (rst k n w (s + 1) r)
      ⟨rest, .write [] [(([s, 3], 1), ([s, 4], 1)), (([s, 4], 1), ([s, 3], 1))]⟩ 1 2 :=
  .step (c₁ := 0) (c := 1) (k := 1) (fun h => by cases h) (rready k n w s r rest)
    (.step (c₁ := 1) (c := 0) (k := 0) (fun h => by cases h) (rhalf k n w s r rest) (.refl _ _))

/-- It writes them and takes a fresh list of agents, in three actions. -/
theorem rwrites (k n w r : Nat) (rest : List (Id × Chain)) :
    Works xsys (rst k n w (w + 1) r)
      ⟨rest, .write [] [(([w, 3], 1), ([w, 4], 1)), (([w, 4], 1), ([w, 3], 1))]⟩
      (rst k n (w + 1) (w + 1) r) ⟨(rst k n (w + 1) (w + 1) r).agents, .idle⟩ 0 3 := by
  have s₁ : XMach.act xsys (rst k n w (w + 1) r)
      ⟨rest, .write [] [(([w, 3], 1), ([w, 4], 1)), (([w, 4], 1), ([w, 3], 1))]⟩ =
      ((rst k n w (w + 1) r).putLink ([w, 3], 1) ([w, 4], 1),
        ⟨rest, .write [] [(([w, 4], 1), ([w, 3], 1))]⟩, 0) := rfl
  have s₂ : XMach.act xsys ((rst k n w (w + 1) r).putLink ([w, 3], 1) ([w, 4], 1))
      ⟨rest, .write [] [(([w, 4], 1), ([w, 3], 1))]⟩ =
      (rst k n (w + 1) (w + 1) r, ⟨rest, .write [] []⟩, 0) := rfl
  have s₃ : XMach.act xsys (rst k n (w + 1) (w + 1) r) ⟨rest, .write [] []⟩ =
      (rst k n (w + 1) (w + 1) r, ⟨(rst k n (w + 1) (w + 1) r).agents, .idle⟩, 0) := rfl
  exact .step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₁
    (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂
      (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₃ (.refl _ _)))

/-- At the first agent of the first pair, a thread finds the second in
three actions. -/
theorem rfound0 (k n r : Nat) (rest : List (Id × Chain)) :
    Stays xsys (rst k n 0 0 (r + 1)) ⟨([0, 3], c) :: rest, .idle⟩
      ⟨rest, .ready [0, 3] [0, 4] c c⟩ 3 := by
  have ha : assoc [0, 3] (rst k n 0 0 (r + 1)).agents = some c := by
    rw [rst_assoc]
    exact agent_x (Nat.le_refl 0) (by omega)
  have hb : assoc [0, 4] (rst k n 0 0 (r + 1)).agents = some c := by
    rw [rst_assoc]
    exact agent_y (Nat.le_refl 0) (by omega)
  have hwire : assoc (([0, 3] : Id), 0) (rst k n 0 0 (r + 1)).wires = some ([0, 4], 0) :=
    assoc_eq_of_unique (mem_wires.2 (.inr (.inr (.inl rfl)))) fun q' hq' => wire_head hq'
  exact .step (k := 2) (fun h => by cases h) (XMach.act_idle_pos ha)
    (.step (k := 1) (fun h => by cases h) (XMach.act_look hwire)
      (.step (k := 0) (fun h => by cases h)
        (XMach.act_seek_found (c := ([0, 4], 0))
          (by
            show (if (0 : Nat) = 0 then assoc [0, 4] (rst k n 0 0 (r + 1)).agents
              else none) = some c
            rw [ite_pos' rfl]
            exact hb)
          ⟨by simp, by rw [rule_cc]; rfl⟩) (.refl _)))

/-- At the first agent of a later pair, once the pair before it has had its
segment written, a thread finds the second in five actions. -/
theorem rfoundS (k n j r : Nat) (hj : j < n) (rest : List (Id × Chain)) :
    Stays xsys (rst k n (j + 1) (j + 1) (r + 1)) ⟨([j + 1, 3], c) :: rest, .idle⟩
      ⟨rest, .ready [j + 1, 3] [j + 1, 4] c c⟩ 5 := by
  have ha : assoc [j + 1, 3] (rst k n (j + 1) (j + 1) (r + 1)).agents = some c := by
    rw [rst_assoc]
    exact agent_x (Nat.le_refl _) (by omega)
  have hb : assoc [j + 1, 4] (rst k n (j + 1) (j + 1) (r + 1)).agents = some c := by
    rw [rst_assoc]
    exact agent_y (Nat.le_refl _) (by omega)
  have hwire : assoc (([j + 1, 3] : Id), 0) (rst k n (j + 1) (j + 1) (r + 1)).wires =
      some ([j, 3], 1) :=
    assoc_eq_of_unique (mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inr (.inl rfl)⟩)))))
      fun q' hq' => wire_x hq'
  have hn₁ : nextSeg (rst k n (j + 1) (j + 1) (r + 1)).wires ([j, 3], 1) ([j + 1, 3], 0) =
      some ([j, 4], 1) :=
    nextSeg_some (mem_wires.2 (.inl ⟨j, Nat.lt_succ_self j, .inr rfl⟩)) (by simp)
      fun q hq hne => by
        rcases wire_x_aux hq with h | ⟨-, h⟩
        · exact absurd h hne
        · exact h
  have hn₂ : nextSeg (rst k n (j + 1) (j + 1) (r + 1)).wires ([j, 4], 1) ([j, 3], 1) =
      some ([j + 1, 4], 0) :=
    nextSeg_some
      (mem_wires.2 (.inr (.inr (.inr (.inr ⟨j, hj, .inr (.inr (.inl rfl))⟩))))) (by simp)
      fun q hq hne => by
        rcases wire_y_aux hq with h | ⟨-, h⟩
        · exact h
        · exact absurd h hne
  exact .step (k := 4) (fun h => by cases h) (XMach.act_idle_pos ha)
    (.step (k := 3) (fun h => by cases h) (XMach.act_look hwire)
      (.step (k := 2) (fun h => by cases h)
        (XMach.act_seek_next (c := ([j, 3], 1)) (ite_neg' (by simp)) hn₁)
        (.step (k := 1) (fun h => by cases h)
          (XMach.act_seek_next (c := ([j, 4], 1)) (ite_neg' (by simp)) hn₂)
          (.step (k := 0) (fun h => by cases h)
            (XMach.act_seek_found (c := ([j + 1, 4], 0))
              (by
                show (if (0 : Nat) = 0 then
                  assoc [j + 1, 4] (rst k n (j + 1) (j + 1) (r + 1)).agents else none) = some c
                rw [ite_pos' rfl]
                exact hb)
              ⟨by simp, by rw [rule_cc]; rfl⟩) (.refl _)))))

/-- From the second pair on, one thread alone: before each pair a pass over
the agents that lead nowhere and over the pairs that are not active yet,
ten actions for the pair, and one more pass at the end. -/
theorem rrunsS (k n : Nat) : ∀ (r j : Nat), j + 1 + r ≤ n →
    Works xsys (rst k n (j + 1) (j + 1) r) ⟨(rst k n (j + 1) (j + 1) r).agents, .idle⟩
      (rst k n (j + 1 + r) (j + 1 + r) 0) ⟨[], .idle⟩ r
      ((r + 1) * (3 * k) + 3 * (r * r) + 7 * r)
  | 0, j, _ => by
    have w := (rpass (Nat.le_refl k) n (j + 1) (j + 1) 0 []).works
    have e : (0 + 1) * (3 * k) + 3 * (0 * 0) + 7 * 0 = 3 * k := by omega
    rw [e]
    exact w
  | r + 1, j, h => by
    have w₁ := (rpass (Nat.le_refl k) n (j + 1) (j + 1) (r + 1)
      (pairsDown (j + 2) r ++ [([j + 1, 3], c), ([j + 1, 4], c)])).works
    have w₂ := (rpending (k := k) (n := n) (w := j + 1) (s := j + 1) (r := r + 1)
      (s' := j + 2) (r' := r) (by omega) (by omega) (by omega) (by omega)
      [([j + 1, 3], c), ([j + 1, 4], c)]).works
    have w₃ := (rfoundS k n j r (by omega) [([j + 1, 4], c)]).works
    have w₄ := rtake k n (j + 1) (j + 1) r [([j + 1, 4], c)]
    have w₅ := rwrites k n (j + 1) r [([j + 1, 4], c)]
    have w₆ := rrunsS k n r (j + 1) (by omega)
    have w := ((((w₁.trans w₂).trans w₃).trans w₄).trans w₅).trans w₆
    have e₀ : j + 1 + 1 + r = j + 1 + (r + 1) := by omega
    have e₁ : 0 + 0 + 0 + 1 + 0 + r = r + 1 := by omega
    have sq : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    have e₂ : 3 * k + 6 * r + 5 + 2 + 3 + ((r + 1) * (3 * k) + 3 * (r * r) + 7 * r) =
        (r + 1 + 1) * (3 * k) + 3 * ((r + 1) * (r + 1)) + 7 * (r + 1) := by
      rw [Nat.add_mul (r + 1) 1 (3 * k), Nat.one_mul, sq]
      omega
    rw [e₀, e₁, e₂] at w
    exact w

/-- A thread that has taken the first pair and has its segments to write
goes on alone to the end. -/
theorem rpaused (k n r : Nat) (h : r + 1 ≤ n) (rest : List (Id × Chain)) :
    Works xsys (rst k n 0 1 r)
      ⟨rest, .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩
      (rst k n (r + 1) (r + 1) 0) ⟨[], .idle⟩ r
      (3 + ((r + 1) * (3 * k) + 3 * (r * r) + 7 * r)) := by
  have w := (rwrites k n 0 r rest).trans (rrunsS k n r 0 (by omega))
  have e₀ : 0 + 1 + r = r + 1 := by omega
  have e₁ : 0 + r = r := by omega
  rw [e₀, e₁] at w
  exact w

/-- **The opening.**  Two threads on the chain listed from the last pair,
taking turns, the second first.  After `3 * k + 6 * n + 5` actions each, the
second has passed every agent, found the first pair and taken it, and has
its segments to write; the first, which started one agent behind, has
passed every other pair, found the first pair gone, and is at rest. -/
theorem ropening (k n : Nat) :
    ((XMach.init (rnet (k + 1) (n + 1)) 2).trace xsys (fun i => (i + 1) % 2)
      (2 * (3 * k + 6 * n + 5))).1 =
      ⟨rst (k + 1) (n + 1) 0 1 n, [⟨[], .idle⟩,
        ⟨[([0, 4], c), ([k, 0], c)],
          .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩]⟩ := by
  have hinit : XMach.init (rnet (k + 1) (n + 1)) 2 =
      ⟨rst (k + 1) (n + 1) 0 0 (n + 1),
        [⟨([k, 0], c) :: (lone k ++ (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)])), .idle⟩,
          ⟨lone k ++ (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c), ([k, 0], c)]), .idle⟩]⟩ := by
    rw [XMach.init_two]
    show (⟨rst (k + 1) (n + 1) 0 0 (n + 1),
      [⟨([k, 0], c) :: (lone k ++ (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)])), .idle⟩,
        ⟨(lone k ++ (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)])) ++ [([k, 0], c)], .idle⟩]⟩ :
      XMach Chain) = _
    rw [List.append_assoc, List.append_assoc]
    rfl
  have r₁ : Stays xsys (rst (k + 1) (n + 1) 0 0 (n + 1))
      ⟨([k, 0], c) :: (lone k ++ (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)])), .idle⟩
      ⟨lone k ++ (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)]), .idle⟩ 3 :=
    Stays.inert _ (rst_inert (inert_lone (by omega)))
  have r₂ := rpass (k := k + 1) (k' := k) (by omega) (n + 1) 0 0 (n + 1)
    (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)])
  have r₃ := rpending (k := k + 1) (n := n + 1) (w := 0) (s := 0) (r := n + 1) (s' := 1)
    (r' := n) (by omega) (by omega) (by omega) (by omega) [([0, 3], c), ([0, 4], c)]
  have sR := (r₁.trans r₂).trans r₃
  have q₁ := rpass (k := k + 1) (k' := k) (by omega) (n + 1) 0 0 (n + 1)
    (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c), ([k, 0], c)])
  have q₂ := rpending (k := k + 1) (n := n + 1) (w := 0) (s := 0) (r := n + 1) (s' := 1)
    (r' := n) (by omega) (by omega) (by omega) (by omega)
    [([0, 3], c), ([0, 4], c), ([k, 0], c)]
  have q₃ := rfound0 (k + 1) (n + 1) n [([0, 4], c), ([k, 0], c)]
  have sS := (q₁.trans q₂).trans q₃
  have eR : 3 + 3 * k + 6 * n = 3 * k + 6 * n + 3 := by omega
  rw [eR] at sR
  have t₀ := XMach.trace_turns (xs := xsys) sR sS
  have a₁ := rready (k + 1) (n + 1) 0 0 n [([0, 4], c), ([k, 0], c)]
  have a₂ : XMach.act xsys ((rst (k + 1) (n + 1) 0 0 (n + 1)).takeAgent [0, 3])
      ⟨([0, 3], c) :: [([0, 4], c)], .idle⟩ =
      ((rst (k + 1) (n + 1) 0 0 (n + 1)).takeAgent [0, 3], ⟨[([0, 4], c)], .idle⟩, 0) :=
    XMach.act_idle_neg fun h => (XNet.mem_takeAgent.1 (assoc_mem h)).2 rfl
  have a₃ := rhalf (k + 1) (n + 1) 0 0 n [([0, 4], c), ([k, 0], c)]
  have a₄ : XMach.act xsys (rst (k + 1) (n + 1) 0 (0 + 1) n) ⟨[([0, 4], c)], .idle⟩ =
      (rst (k + 1) (n + 1) 0 (0 + 1) n, ⟨[], .idle⟩, 0) :=
    XMach.act_idle_neg (by
      rw [rst_assoc]
      exact agent_gone (by omega) 4 (by omega) c)
  have h₂ := XMach.trace_round (xs := xsys) a₃ a₄
  have e : 3 * k + 6 * n + 5 = 3 * k + 6 * n + 3 + 1 + 1 := by omega
  rw [hinit, e, XMach.trace_turns_add xsys _ (3 * k + 6 * n + 3 + 1) 1,
    XMach.trace_turns_add xsys _ (3 * k + 6 * n + 3) 1, t₀, XMach.trace_round a₁ a₂]
  exact h₂

/-- **A starved thread makes every claim, whatever the window.**  On
`k + 1` agents that lead nowhere and a chain of `n + 1` pairs listed from
the last to the first, with two threads: after the opening the first thread
is at rest, and the second gets every `F`-th action.  It has `n` more pairs
to fire, with a pass before each, and the program is not at rest after `F`
times its count of actions, less `F`, or fewer. -/
theorem starved_short (k n F : Nat) (hF : 0 < F) :
    ∀ i, i + F ≤ F * (3 + ((n + 1) * (3 * (k + 1)) + 3 * (n * n) + 7 * n)) →
      ¬ ((XMach.init (rnet (k + 1) (n + 1)) 2).trace xsys
        (abreast (3 * k + 6 * n + 5) F) i).1.resting = true := by
  intro i hi hr
  have hs := XMach.trace_abreast (xs := xsys) (F := F) (ropening k n)
  have hr' := XMach.resting_trace (xs := xsys) _ hr (2 * (3 * k + 6 * n + 5))
  rw [Nat.add_comm i, hs i] at hr'
  refine XMach.starved_worker (xs := xsys) (u := 1) (starveSnd F)
    (M := ⟨rst (k + 1) (n + 1) 0 1 n, [⟨[], .idle⟩,
      ⟨[([0, 4], c), ([k, 0], c)],
        .write [] [(([0, 3], 1), ([0, 4], 1)), (([0, 4], 1), ([0, 3], 1))]⟩]⟩) rfl ?_
    (rpaused (k + 1) (n + 1) n (Nat.le_refl _) _) hF (starveSnd_sparse F) i hi hr'
  intro t T ht h
  cases t with
  | zero => exact (Option.some.inj h).symm
  | succ t =>
    cases t with
    | zero => exact absurd rfl ht
    | succ t => cases h

/-! The net is the chain, listed in another order. -/

theorem rnet_toNet (k n : Nat) : (rnet k n).toNet = (net k n).toNet :=
  Net.ext' (fun _ _ => (rst_perm k n 0 0 n).mem_iff) (fun _ _ => Iff.rfl) (fun _ => Iff.rfl)

theorem rnet_wf (k n : Nat) : (rnet k n).toNet.WF ar := by
  rw [rnet_toNet]
  exact net_wf k n

theorem rnet_nodup (k n : Nat) : ((rnet k n).agents.map Prod.fst).Nodup :=
  ((rst_perm k n 0 0 n).map Prod.fst).nodup_iff.2 (net_nodup k n)

theorem rnet_passBound (k n : Nat) : (rnet k n).passBound n 0 2 = 11 * k + 20 * n + 2 := by
  show 7 * ((rst k n 0 0 n).agents.length + 0 * n) + ((net k n).wires.length + 2 * n) = _
  rw [(rst_perm k n 0 0 n).length_eq]
  exact net_passBound k n

theorem rnet_steps (k n : Nat) :
    ∃ N', Steps (Step xsys.sys) (n + 1) (rnet k (n + 1)).toNet N' ∧
      Normal (Step xsys.sys) N' := by
  rw [rnet_toNet]
  exact net_steps k n

/-- On these nets the bound is at most twelve times the count of the
starved thread's actions. -/
theorem short_bound_le (k n : Nat) :
    (n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4 ≤
      12 * ((n + 1) * (3 * (k + 1)) + 3 * (n * n) + 7 * n + 3) := by
  have h₁ : (n + 2) * (11 * k + 20 * n + 33) =
      11 * (n * k) + 20 * (n * n) + 33 * n + 2 * (11 * k + 20 * n + 33) := by
    rw [Nat.add_mul n 2 (11 * k + 20 * n + 33), Nat.mul_add n (11 * k + 20 * n) 33,
      Nat.mul_add n (11 * k) (20 * n), Nat.mul_left_comm n 11 k, Nat.mul_left_comm n 20 n,
      Nat.mul_comm n 33]
  have h₂ : (n + 1) * (3 * (k + 1)) = 3 * (n * k) + 3 * n + 3 * (k + 1) := by
    rw [Nat.add_mul n 1 (3 * (k + 1)), Nat.one_mul, Nat.mul_left_comm n 3 (k + 1),
      Nat.mul_add n k 1, Nat.mul_one, Nat.mul_add 3 (n * k) n]
  rw [h₁, h₂]
  omega

/-- **The window multiplies every pass, however short it is.**  On `k + 1`
agents that lead nowhere and a chain of `n + 1` pairs listed from the last
to the first, take two threads, any window `F` with room for both, and the
schedule `abreast`, which is fair with that window.  The bound of
`XMach.fair_bound` puts the threads at rest after `F` times

    (n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4

actions, and they are not at rest after `F` times

    (n + 1) * (3 * (k + 1)) + 3 * (n * n) + 7 * n + 3

actions, less `F`: every pass of the starved thread after its first claim
is stretched by the window.  The first count is at most twelve times the
second (`short_bound_le`), so on these nets the bound is right up to a
constant, for every window. -/
theorem window_short (k n F : Nat) (hF : 2 ≤ F) :
    (∀ u, u < 2 → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ abreast (3 * k + 6 * n + 5) F j = u) ∧
      (∀ i, F * ((n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4) ≤ i →
        ((XMach.init (rnet (k + 1) (n + 1)) 2).trace xsys
          (abreast (3 * k + 6 * n + 5) F) i).1.resting = true) ∧
      ∀ i, i + F ≤ F * ((n + 1) * (3 * (k + 1)) + 3 * (n * n) + 7 * n + 3) →
        ¬ ((XMach.init (rnet (k + 1) (n + 1)) 2).trace xsys
          (abreast (3 * k + 6 * n + 5) F) i).1.resting = true := by
  have hfair := abreast_fair (P := 3 * k + 6 * n + 5) hF
  refine ⟨hfair, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨N', hs, hn⟩ := rnet_steps (k + 1) n
    have hX : (rnet (k + 1) (n + 1)).toNet.WF xsys.sys.ar := rnet_wf (k + 1) (n + 1)
    have hb := XMach.fair_bound (xs := xsys) hX (rnet_nodup (k + 1) (n + 1)) (nt := 2)
      (by decide) xsys_bounded hs hn _ hfair i
    refine (hb ?_).1
    rw [rnet_passBound]
    have e₁ : n + 1 + 1 = n + 2 := rfl
    have e₂ : 11 * (k + 1) + 20 * (n + 1) + 2 = 11 * k + 20 * n + 33 := by omega
    rw [e₁, e₂]
    have e₃ : (n + 2) * (11 * k + 20 * n + 33) + (n + 1) * (0 + 2 + 1) + 1 =
        (n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4 := by omega
    rw [e₃]
    exact hi
  · refine starved_short k n F (by omega) i ?_
    have e : 3 + ((n + 1) * (3 * (k + 1)) + 3 * (n * n) + 7 * n) =
        (n + 1) * (3 * (k + 1)) + 3 * (n * n) + 7 * n + 3 := by omega
    rw [e]
    exact hi

/-! The time of a run with claims. -/

theorem wires_length (k n w : Nat) : (wires k n w).length = 2 * w + 4 * k + 4 * n + 2 := by
  have h₀ := length_gen
    (f := fun j => [((([j, 4] : Id), 1), (([j, 3] : Id), 1)), (([j, 3], 1), ([j, 4], 1))])
    (c := 2) (fun _ => rfl) w
  have h₁ := length_gen
    (f := fun j => [((([j, 0] : Id), 0), (([j, 1] : Id), 0)), (([j, 1], 0), ([j, 0], 0)),
      (([j, 0], 1), ([j, 2], 0)), (([j, 2], 0), ([j, 0], 1))]) (c := 4) (fun _ => rfl) k
  have h₂ := length_gen
    (f := fun j => [((([j, 3] : Id), 1), (([j + 1, 3] : Id), 0)), (([j + 1, 3], 0), ([j, 3], 1)),
      (([j, 4], 1), ([j + 1, 4], 0)), (([j + 1, 4], 0), ([j, 4], 1))]) (c := 4) (fun _ => rfl) n
  show (written w ++ (loneWires k ++ (headWires ++ chainWires n))).length = _
  rw [List.length_append, List.length_append, List.length_append]
  show (gen _ w).length + ((gen _ k).length + (2 + (gen _ n).length)) = _
  rw [h₀, h₁, h₂]
  omega

theorem rst_agents_length (k n w s r : Nat) : (rst k n w s r).agents.length = k + 2 * r := by
  show (lone k ++ pairsDown s r).length = _
  rw [List.length_append, lone_length, pairsDown_length]

/-- A pass over the agents that lead nowhere reads the whole memory for
each of them. -/
theorem rpass_spent {k k' : Nat} (hk : k' ≤ k) (n w s r : Nat) (rest : List (Id × Chain)) :
    k' * (5 * k + 4 * n + 5) ≤
      (⟨lone k' ++ rest, .idle⟩ : XThread Chain).spent xsys (rst k n w s r) (3 * k') := by
  have h := XThread.spent_inert_pass (xs := xsys) (X := rst k n w s r) rest (lone k')
    fun e he => by
      obtain ⟨j, hj, rfl⟩ := mem_lone.1 he
      exact ⟨rst_inert (inert_lone (by omega)), fun q hq => by rw [wire_lone (assoc_mem hq)]⟩
  have hw : (rst k n w s r).wires.length = 2 * w + 4 * k + 4 * n + 2 := wires_length k n w
  rw [lone_length, rst_agents_length, hw] at h
  exact Nat.le_trans (Nat.mul_le_mul_left k' (by omega)) h

/-- A pass over the pairs that are not active yet reads every segment for
each of their agents. -/
theorem rpending_spent {k n w s r s' r' : Nat} (hw : w < s') (h₁ : s ≤ s')
    (h₂ : s' + r' ≤ s + r) (hn : s' + r' ≤ n + 1) (rest : List (Id × Chain)) :
    2 * r' * (4 * k + 4 * n + 5) ≤
      (⟨pairsDown s' r' ++ rest, .idle⟩ : XThread Chain).spent xsys (rst k n w s r)
        (6 * r') := by
  have h := XThread.spent_stuck_pass (xs := xsys) (X := rst k n w s r) rest (pairsDown s' r')
    fun e he => by
      obtain ⟨j, hj₁, hj₂, he' | he'⟩ := mem_pairsDown.1 he
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [he']
        exact rst_inert (inert_x (by omega) (by omega) (by omega) (by omega))
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [he']
        exact rst_inert (inert_y (by omega) (by omega) (by omega) (by omega))
  have e : 3 * (2 * r') = 6 * r' := by omega
  have hwl : (rst k n w s r).wires.length = 2 * w + 4 * k + 4 * n + 2 := wires_length k n w
  rw [pairsDown_length, e, hwl] at h
  exact Nat.le_trans (Nat.mul_le_mul_left (2 * r') (by omega)) h

/-- The time of the run from the second pair on: before each pair a pass
that reads the whole memory for each agent that leads nowhere, and every
segment for each agent of a pair that is not active yet. -/
theorem rrunsS_time (k n : Nat) : ∀ (r j : Nat), j + 1 + r ≤ n →
    (r + 1) * (k * (5 * k + 4 * n + 5)) + (r * r - r) * (4 * k + 4 * n + 5) ≤
      XMach.soloTime xsys (rst k n (j + 1) (j + 1) r)
        ⟨(rst k n (j + 1) (j + 1) r).agents, .idle⟩
        ((r + 1) * (3 * k) + 3 * (r * r) + 7 * r)
  | 0, j, _ => by
    have st := rpass (Nat.le_refl k) n (j + 1) (j + 1) 0 []
    have sp := rpass_spent (Nat.le_refl k) n (j + 1) (j + 1) 0 []
    have e : (0 + 1) * (3 * k) + 3 * (0 * 0) + 7 * 0 = 3 * k := by omega
    have z : (0 * 0 - 0) * (4 * k + 4 * n + 5) = 0 := Nat.zero_mul _
    have o : (0 + 1) * (k * (5 * k + 4 * n + 5)) = k * (5 * k + 4 * n + 5) := Nat.one_mul _
    rw [e, z, o, Nat.add_zero]
    show _ ≤ XMach.soloTime xsys (rst k n (j + 1) (j + 1) 0) ⟨lone k ++ [], .idle⟩ (3 * k)
    rw [st.soloTime]
    exact sp
  | r + 1, j, h => by
    have p₁ := rpass (Nat.le_refl k) n (j + 1) (j + 1) (r + 1)
      (pairsDown (j + 2) r ++ [([j + 1, 3], c), ([j + 1, 4], c)])
    have p₂ := rpending (k := k) (n := n) (w := j + 1) (s := j + 1) (r := r + 1)
      (s' := j + 2) (r' := r) (by omega) (by omega) (by omega) (by omega)
      [([j + 1, 3], c), ([j + 1, 4], c)]
    have w₁ := p₁.works
    have w₂ := p₂.works
    have w₃ := (rfoundS k n j r (by omega) [([j + 1, 4], c)]).works
    have w₄ := rtake k n (j + 1) (j + 1) r [([j + 1, 4], c)]
    have w₅ := rwrites k n (j + 1) r [([j + 1, 4], c)]
    have t₁ : k * (5 * k + 4 * n + 5) ≤ XMach.soloTime xsys (rst k n (j + 1) (j + 1) (r + 1))
        ⟨lone k ++ (pairsDown (j + 2) r ++ [([j + 1, 3], c), ([j + 1, 4], c)]), .idle⟩
        (3 * k) := by
      rw [p₁.soloTime]
      exact rpass_spent (Nat.le_refl k) n (j + 1) (j + 1) (r + 1) _
    have t₂ : 2 * r * (4 * k + 4 * n + 5) ≤
        XMach.soloTime xsys (rst k n (j + 1) (j + 1) (r + 1))
          ⟨pairsDown (j + 2) r ++ [([j + 1, 3], c), ([j + 1, 4], c)], .idle⟩ (6 * r) := by
      rw [p₂.soloTime]
      exact rpending_spent (by omega) (by omega) (by omega) (by omega) _
    have s₂ := w₁.soloTime_ge t₁ t₂
    have s₃ := (w₁.trans w₂).soloTime_ge s₂ (b := 0) (j := 5) (Nat.zero_le _)
    have s₄ := ((w₁.trans w₂).trans w₃).soloTime_ge s₃ (b := 0) (j := 2) (Nat.zero_le _)
    have s₅ := (((w₁.trans w₂).trans w₃).trans w₄).soloTime_ge s₄ (b := 0) (j := 3)
      (Nat.zero_le _)
    have s₆ := ((((w₁.trans w₂).trans w₃).trans w₄).trans w₅).soloTime_ge s₅
      (rrunsS_time k n r (j + 1) (by omega))
    have sq : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    have e₂ : 3 * k + 6 * r + 5 + 2 + 3 + ((r + 1) * (3 * k) + 3 * (r * r) + 7 * r) =
        (r + 1 + 1) * (3 * k) + 3 * ((r + 1) * (r + 1)) + 7 * (r + 1) := by
      rw [Nat.add_mul (r + 1) 1 (3 * k), Nat.one_mul, sq]
      omega
    rw [e₂] at s₆
    have hr := Nat.le_mul_self r
    have e₃ : (r + 1) * (r + 1) - (r + 1) = (r * r - r) + 2 * r := by
      rw [sq]
      omega
    rw [e₃, Nat.add_mul (r * r - r) (2 * r) (4 * k + 4 * n + 5),
      Nat.add_mul (r + 1) 1 (k * (5 * k + 4 * n + 5)), Nat.one_mul]
    exact Nat.le_trans (by omega) s₆

/-- **The run of one thread on the chain listed from the last pair,
counted.** -/
theorem rruns0 (k n : Nat) :
    Works xsys (rst k (n + 1) 0 0 (n + 1)) ⟨(rst k (n + 1) 0 0 (n + 1)).agents, .idle⟩
      (rst k (n + 1) (n + 1) (n + 1) 0) ⟨[], .idle⟩ (n + 1)
      (3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n)) := by
  have v₁ := (rpass (Nat.le_refl k) (n + 1) 0 0 (n + 1)
    (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)])).works
  have v₂ := (rpending (k := k) (n := n + 1) (w := 0) (s := 0) (r := n + 1) (s' := 1)
    (r' := n) (by omega) (by omega) (by omega) (by omega) [([0, 3], c), ([0, 4], c)]).works
  have v₃ := (rfound0 k (n + 1) n [([0, 4], c)]).works
  have v₄ := rtake k (n + 1) 0 0 n [([0, 4], c)]
  have v₅ := rpaused k (n + 1) n (Nat.le_refl _) [([0, 4], c)]
  have w := (((v₁.trans v₂).trans v₃).trans v₄).trans v₅
  have e₁ : 0 + 0 + 0 + 1 + n = n + 1 := by omega
  have e₂ : 3 * k + 6 * n + 3 + 2 + (3 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n)) =
      3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n) := by omega
  rw [e₁, e₂] at w
  exact w

/-- **The time of that run**: `n + 2` passes that read the whole memory for
each agent that leads nowhere, and every segment for each agent of a pair
that is not active yet. -/
theorem rruns0_time (k n : Nat) :
    (n + 2) * (k * (5 * k + 4 * n + 9)) + (n * n + n) * (4 * k + 4 * n + 9) ≤
      XMach.soloTime xsys (rst k (n + 1) 0 0 (n + 1))
        ⟨(rst k (n + 1) 0 0 (n + 1)).agents, .idle⟩
        (3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n)) := by
  have p₁ := rpass (Nat.le_refl k) (n + 1) 0 0 (n + 1)
    (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)])
  have p₂ := rpending (k := k) (n := n + 1) (w := 0) (s := 0) (r := n + 1) (s' := 1)
    (r' := n) (by omega) (by omega) (by omega) (by omega) [([0, 3], c), ([0, 4], c)]
  have v₁ := p₁.works
  have v₂ := p₂.works
  have v₃ := (rfound0 k (n + 1) n [([0, 4], c)]).works
  have v₄ := rtake k (n + 1) 0 0 n [([0, 4], c)]
  have v₅ := rwrites k (n + 1) 0 n [([0, 4], c)]
  have t₁ : k * (5 * k + 4 * (n + 1) + 5) ≤ XMach.soloTime xsys (rst k (n + 1) 0 0 (n + 1))
      ⟨lone k ++ (pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)]), .idle⟩ (3 * k) := by
    rw [p₁.soloTime]
    exact rpass_spent (Nat.le_refl k) (n + 1) 0 0 (n + 1) _
  have t₂ : 2 * n * (4 * k + 4 * (n + 1) + 5) ≤
      XMach.soloTime xsys (rst k (n + 1) 0 0 (n + 1))
        ⟨pairsDown 1 n ++ [([0, 3], c), ([0, 4], c)], .idle⟩ (6 * n) := by
    rw [p₂.soloTime]
    exact rpending_spent (by omega) (by omega) (by omega) (by omega) _
  have s₂ := v₁.soloTime_ge t₁ t₂
  have s₃ := (v₁.trans v₂).soloTime_ge s₂ (b := 0) (j := 3) (Nat.zero_le _)
  have s₄ := ((v₁.trans v₂).trans v₃).soloTime_ge s₃ (b := 0) (j := 2) (Nat.zero_le _)
  have s₅ := (((v₁.trans v₂).trans v₃).trans v₄).soloTime_ge s₄ (b := 0) (j := 3)
    (Nat.zero_le _)
  have s₆ := ((((v₁.trans v₂).trans v₃).trans v₄).trans v₅).soloTime_ge s₅
    (rrunsS_time k (n + 1) n 0 (by omega))
  have e₂ : 3 * k + 6 * n + 3 + 2 + 3 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n) =
      3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n) := by omega
  rw [e₂] at s₆
  have a₁ : 5 * k + 4 * (n + 1) + 5 = 5 * k + 4 * n + 9 := by omega
  have a₂ : 4 * k + 4 * (n + 1) + 5 = 4 * k + 4 * n + 9 := by omega
  rw [a₁, a₂] at s₆
  have hn := Nat.le_mul_self n
  have e₃ : n * n + n = (n * n - n) + 2 * n := by omega
  rw [e₃, Nat.add_mul (n * n - n) (2 * n) (4 * k + 4 * n + 9),
    Nat.add_mul (n + 1) 1 (k * (5 * k + 4 * n + 9)), Nat.one_mul]
  exact Nat.le_trans (by omega) s₆

/-- **The bound on the time against a run with claims.**  One thread on
`k` agents that lead nowhere and a chain of `n + 1` pairs listed from the
last to the first: the bound of `XMach.time_bound` is the first count, and
by the time the thread is at rest it has taken the second or more.  After
every claim it reads the whole memory again for each agent that leads
nowhere, and every segment for each agent of a pair still to come. -/
theorem time_chain (k n : Nat) :
    (∀ i, (XMach.init (rnet k (n + 1)) 1).time xsys (fun _ => 0) i ≤
        ((n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3) * (6 * k + 10 * n + 15)) ∧
      ∀ i, ((XMach.init (rnet k (n + 1)) 1).trace xsys (fun _ => 0) i).1.resting = true →
        (n + 2) * (k * (5 * k + 4 * n + 9)) + (n * n + n) * (4 * k + 4 * n + 9) ≤
          (XMach.init (rnet k (n + 1)) 1).time xsys (fun _ => 0) i := by
  constructor
  · intro i
    obtain ⟨N', hs, hn⟩ := rnet_steps k n
    have hX : (rnet k (n + 1)).toNet.WF xsys.sys.ar := rnet_wf k (n + 1)
    have h := XMach.time_bound (xs := xsys) hX (rnet_nodup k (n + 1)) (nt := 1) (by decide)
      xsys_bounded hs hn (fun _ => 0) i
    have ha : (rnet k (n + 1)).agents.length = k + 2 * (n + 1) :=
      rst_agents_length k (n + 1) 0 0 (n + 1)
    have hw : (rnet k (n + 1)).wires.length = 2 * 0 + 4 * k + 4 * (n + 1) + 2 :=
      wires_length k (n + 1) 0
    rw [rnet_passBound, ha, hw] at h
    have a : 1 + (n + 1) = n + 2 := by omega
    have b : 11 * k + 20 * (n + 1) + 2 = 11 * k + 20 * n + 22 := by omega
    rw [a, b] at h
    have e₁ : (n + 2) * (11 * k + 20 * n + 22) + (n + 1) * (0 + 2 + 1) =
        (n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3 := by omega
    have e₂ : 2 * (k + 2 * (n + 1) + 0 * (n + 1)) +
        (2 * 0 + 4 * k + 4 * (n + 1) + 2 + 2 * (n + 1)) + 0 + 2 + 1 =
        6 * k + 10 * n + 15 := by omega
    rw [e₁, e₂] at h
    exact h
  · intro i hr
    have hinit : XMach.init (rnet k (n + 1)) 1 =
        ⟨rst k (n + 1) 0 0 (n + 1), [⟨(rst k (n + 1) 0 0 (n + 1)).agents, .idle⟩]⟩ :=
      XMach.init_one _
    rw [hinit] at hr ⊢
    have ht := XMach.time_lone (xs := xsys)
      (M := ⟨rst k (n + 1) 0 0 (n + 1), [⟨(rst k (n + 1) 0 0 (n + 1)).agents, .idle⟩]⟩)
      (u := 0) (fun _ => 0) rfl (fun t T ht h => by
        cases t with
        | zero => exact absurd rfl ht
        | succ t => cases h) i
    rw [hits_const] at ht
    rw [ht]
    have hi : 3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n) ≤ i := by
      rcases Nat.lt_or_ge i (3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n))
        with h | h
      · exact absurd hr ((rruns0 k n).trace.2 i h)
      · exact h
    exact Nat.le_trans (rruns0_time k n) (XMach.soloTime_mono xsys _ _ hi)

/-- With at least one agent that leads nowhere, the bound is at most 168
times that time. -/
theorem time_chain_le (k n : Nat) (hk : 0 < k) :
    ((n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3) * (6 * k + 10 * n + 15) ≤
      168 * ((n + 2) * (k * (5 * k + 4 * n + 9)) + (n * n + n) * (4 * k + 4 * n + 9)) := by
  have hX : n + 2 ≤ (n + 2) * k := Nat.le_mul_of_pos_right (n + 2) hk
  have hP : (n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3 ≤
      56 * ((n + 2) * k + (n * n + n)) := by
    have e : (n + 2) * (11 * k + 20 * n + 22) =
        11 * ((n + 2) * k) + 20 * (n * n + 2 * n) + (n + 2) * 22 := by
      rw [Nat.mul_add (n + 2) (11 * k + 20 * n) 22, Nat.mul_add (n + 2) (11 * k) (20 * n),
        Nat.mul_left_comm (n + 2) 11 k, Nat.mul_left_comm (n + 2) 20 n, Nat.add_mul n 2 n]
    rw [e]
    omega
  have hα : 6 * k + 10 * n + 15 ≤ 3 * (5 * k + 4 * n + 9) := by omega
  have hβ : 6 * k + 10 * n + 15 ≤ 3 * (4 * k + 4 * n + 9) := by omega
  have h₁ := Nat.mul_le_mul_left ((n + 2) * k) hα
  have h₂ := Nat.mul_le_mul_left (n * n + n) hβ
  have e₁ : (n + 2) * k * (3 * (5 * k + 4 * n + 9)) =
      3 * ((n + 2) * (k * (5 * k + 4 * n + 9))) := by
    rw [Nat.mul_left_comm ((n + 2) * k) 3 (5 * k + 4 * n + 9),
      Nat.mul_assoc (n + 2) k (5 * k + 4 * n + 9)]
  rw [e₁] at h₁
  rw [Nat.mul_left_comm (n * n + n) 3] at h₂
  have hGQ : ((n + 2) * k + (n * n + n)) * (6 * k + 10 * n + 15) ≤
      3 * ((n + 2) * (k * (5 * k + 4 * n + 9)) + (n * n + n) * (4 * k + 4 * n + 9)) := by
    rw [Nat.add_mul, Nat.mul_add 3]
    exact Nat.add_le_add h₁ h₂
  have s₁ := Nat.mul_le_mul_right (6 * k + 10 * n + 15) hP
  rw [Nat.mul_assoc 56] at s₁
  have s₃ := Nat.mul_le_mul_left 56 hGQ
  rw [← Nat.mul_assoc 56 3] at s₃
  exact Nat.le_trans s₁ s₃

/-- The bound on the indexed time for one thread on `k` agents that lead
nowhere and a chain of `n + 1` pairs listed from the last to the first. -/
theorem itime_chain (k n : Nat) (σ : Nat → Nat) :
    ∀ i, (IMach.init (rnet k (n + 1)) 1).time xsys σ i ≤
      9 * ((n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3) +
        (2 * n + 3) * (k + 2 * n + 2) := by
  intro i
  obtain ⟨N', hs, hn⟩ := rnet_steps k n
  have hX : (rnet k (n + 1)).toNet.WF xsys.sys.ar := rnet_wf k (n + 1)
  have h := IMach.time_bound (xs := xsys) hX (rnet_nodup k (n + 1)) (nt := 1) (by decide)
    xsys_bounded hs hn σ i
  have ha : (rnet k (n + 1)).agents.length = k + 2 * (n + 1) :=
    rst_agents_length k (n + 1) 0 0 (n + 1)
  rw [rnet_passBound, ha] at h
  have a : 1 + (n + 1) = n + 2 := by omega
  have b : 11 * k + 20 * (n + 1) + 2 = 11 * k + 20 * n + 22 := by omega
  rw [a, b] at h
  have e₁ : (n + 2) * (11 * k + 20 * n + 22) + (n + 1) * (0 + 2 + 1) =
      (n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3 := by omega
  have e₂ : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  have e₃ : k + 2 * (n + 1) + 0 * (n + 1) = k + 2 * n + 2 := by omega
  rw [e₁, e₂, e₃, Nat.mul_comm _ (0 + 2 + 7)] at h
  exact h

/-- **What the index gains on a run with claims.**  One thread on `k`
agents that lead nowhere, at least one, and a chain of `n + 1` pairs
listed from the last to the first: by the time the thread is at rest
lists have taken `(6 * k + 10 * n + 15) / 1680` times as long as the
indexed memory, or more.  The constant is crude; the gain grows with the
net. -/
theorem index_gain (k n : Nat) (hk : 0 < k) (i : Nat)
    (hr : ((XMach.init (rnet k (n + 1)) 1).trace xsys (fun _ => 0) i).1.resting = true) :
    (6 * k + 10 * n + 15) * (IMach.init (rnet k (n + 1)) 1).time xsys (fun _ => 0) i ≤
      1680 * (XMach.init (rnet k (n + 1)) 1).time xsys (fun _ => 0) i := by
  have h₁ := itime_chain k n (fun _ => 0) i
  have h₂ := (time_chain k n).2 i hr
  have h₃ := time_chain_le k n hk
  have hs : (2 * n + 3) * (k + 2 * n + 2) ≤ (n + 2) * (11 * k + 20 * n + 22) := by
    have a := Nat.mul_le_mul (show 2 * n + 3 ≤ 2 * (n + 2) by omega)
      (Nat.le_refl (k + 2 * n + 2))
    have b := Nat.mul_le_mul_left (n + 2)
      (show 2 * (k + 2 * n + 2) ≤ 11 * k + 20 * n + 22 by omega)
    have e : 2 * (n + 2) * (k + 2 * n + 2) = (n + 2) * (2 * (k + 2 * n + 2)) := by
      rw [Nat.mul_comm 2 (n + 2), Nat.mul_assoc]
    rw [e] at a
    exact Nat.le_trans a b
  have h₄ : (IMach.init (rnet k (n + 1)) 1).time xsys (fun _ => 0) i ≤
      10 * ((n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3) := by omega
  have h₅ := Nat.mul_le_mul_left (6 * k + 10 * n + 15) h₄
  have e : (6 * k + 10 * n + 15) * (10 * ((n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3)) =
      10 * (((n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3) * (6 * k + 10 * n + 15)) := by
    rw [Nat.mul_left_comm, Nat.mul_comm (6 * k + 10 * n + 15)]
  rw [e] at h₅
  have h₆ := Nat.mul_le_mul_left 10 h₃
  rw [← Nat.mul_assoc 10 168] at h₆
  exact Nat.le_trans h₅ (Nat.le_trans h₆ (Nat.mul_le_mul_left 1680 h₂))

/-- **The work of the run with claims.**  One thread on `k` agents that
lead nowhere and a chain of `n + 1` pairs listed from the last to the
first makes this many actions before it rests, and no other. -/
theorem work_chain (k n : Nat) (i : Nat)
    (hr : ((XMach.init (rnet k (n + 1)) 1).trace xsys (fun _ => 0) i).1.resting = true) :
    (XMach.init (rnet k (n + 1)) 1).work xsys (fun _ => 0) i =
      3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n) := by
  have hinit : XMach.init (rnet k (n + 1)) 1 =
      ⟨rst k (n + 1) 0 0 (n + 1), [⟨(rst k (n + 1) 0 0 (n + 1)).agents, .idle⟩]⟩ :=
    XMach.init_one _
  rw [hinit] at hr ⊢
  obtain ⟨tr, nr⟩ := (rruns0 k n).trace
  have hi : 3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n) ≤ i := by
    rcases Nat.lt_or_ge i (3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n))
      with h | h
    · exact absurd hr (nr i h)
    · exact h
  obtain ⟨d, rfl⟩ : ∃ d, i = 3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n) + d :=
    ⟨i - (3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n)), by omega⟩
  have hK : ((⟨rst k (n + 1) 0 0 (n + 1), [⟨(rst k (n + 1) 0 0 (n + 1)).agents, .idle⟩]⟩ :
      XMach Chain).trace xsys (fun _ => 0)
        (3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n))).1.resting = true := by
    rw [tr]
    rfl
  rw [XMach.work_rest (xs := xsys) (fun _ => 0) hK d]
  exact XMach.work_single nr _ (Nat.le_refl _)

/-- **The indexed time of that run from below.**  By the time the thread
is at rest the indexed program has taken twice its actions, less one for
each claim, or more. -/
theorem itime_ge (k n : Nat) (i : Nat)
    (hr : ((XMach.init (rnet k (n + 1)) 1).trace xsys (fun _ => 0) i).1.resting = true) :
    (n + 2) * (6 * k) + 6 * (n * n) + 25 * n + 15 ≤
      (IMach.init (rnet k (n + 1)) 1).time xsys (fun _ => 0) i := by
  have hw := work_chain k n i hr
  have hX : (rnet k (n + 1)).toNet.WF xsys.sys.ar := rnet_wf k (n + 1)
  have h := IMach.time_ge_work (xs := xsys) hX (rnet_nodup k (n + 1)) (nt := 1) (by decide)
    (fun _ => 0) i
  rw [hw] at h
  obtain ⟨N', hs, hn⟩ := rnet_steps k n
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure (xs := xsys) hX (rnet_nodup k (n + 1)) (nt := 1)
    (by decide) xsys_bounded hs hn (fun _ => 0)
  have hc := (hΦ i).2.1
  have e : (n + 2) * (6 * k) = 2 * ((n + 1) * (3 * k)) + 6 * k := by
    rw [Nat.add_mul n 2 (6 * k), Nat.add_mul n 1 (3 * k), Nat.mul_left_comm n 6 k,
      Nat.mul_left_comm n 3 k]
    omega
  omega

/-- The bound on the indexed time is at most thirty-one times that. -/
theorem itime_chain_le (k n : Nat) :
    9 * ((n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3) + (2 * n + 3) * (k + 2 * n + 2) ≤
      31 * ((n + 2) * (6 * k) + 6 * (n * n) + 25 * n + 15) := by
  have e₁ : (n + 2) * (11 * k + 20 * n + 22) =
      11 * (n * k) + 22 * k + 20 * (n * n) + 62 * n + 44 := by
    rw [Nat.mul_add, Nat.mul_add, Nat.add_mul n 2 (11 * k), Nat.add_mul n 2 (20 * n),
      Nat.add_mul n 2 22, Nat.mul_left_comm n 11 k, Nat.mul_left_comm n 20 n]
    omega
  have e₂ : (2 * n + 3) * (k + 2 * n + 2) =
      2 * (n * k) + 3 * k + 4 * (n * n) + 10 * n + 6 := by
    rw [Nat.mul_add, Nat.mul_add, Nat.add_mul (2 * n) 3 k, Nat.add_mul (2 * n) 3 (2 * n),
      Nat.add_mul (2 * n) 3 2, Nat.mul_assoc 2 n k, Nat.mul_assoc 2 n (2 * n),
      Nat.mul_left_comm n 2 n]
    omega
  have e₃ : (n + 2) * (6 * k) = 6 * (n * k) + 12 * k := by
    rw [Nat.add_mul n 2 (6 * k), Nat.mul_left_comm n 6 k]
    omega
  rw [e₁, e₂, e₃]
  omega

/-- The bound on the work for that run, whatever the schedule. -/
theorem work_bound (k n : Nat) (σ : Nat → Nat) :
    ∀ i, (XMach.init (rnet k (n + 1)) 1).work xsys σ i ≤
      (n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3 := by
  intro i
  obtain ⟨N', hs, hn⟩ := rnet_steps k n
  have hX : (rnet k (n + 1)).toNet.WF xsys.sys.ar := rnet_wf k (n + 1)
  have h := XMach.work_le (xs := xsys) hX (rnet_nodup k (n + 1)) (nt := 1) (by decide)
    xsys_bounded hs hn σ i
  rw [rnet_passBound] at h
  have a : 1 + (n + 1) = n + 2 := by omega
  have b : 11 * k + 20 * (n + 1) + 2 = 11 * k + 20 * n + 22 := by omega
  rw [a, b] at h
  have e₁ : (n + 2) * (11 * k + 20 * n + 22) + (n + 1) * (0 + 2 + 1) =
      (n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3 := by omega
  rw [e₁] at h
  exact h

/-- **The bound on the work is right up to a factor of seven** for one
thread on the chain: it is at most seven times the actions the thread
makes. -/
theorem work_bound_le (k n : Nat) :
    (n + 2) * (11 * k + 20 * n + 22) + 3 * n + 3 ≤
      7 * (3 * k + 6 * n + 8 + ((n + 1) * (3 * k) + 3 * (n * n) + 7 * n)) := by
  have e₁ : (n + 2) * (11 * k + 20 * n + 22) =
      11 * (n * k) + 22 * k + 20 * (n * n) + 62 * n + 44 := by
    rw [Nat.mul_add, Nat.mul_add, Nat.add_mul n 2 (11 * k), Nat.add_mul n 2 (20 * n),
      Nat.add_mul n 2 22, Nat.mul_left_comm n 11 k, Nat.mul_left_comm n 20 n]
    omega
  have e₂ : (n + 1) * (3 * k) = 3 * (n * k) + 3 * k := by
    rw [Nat.add_mul n 1 (3 * k), Nat.mul_left_comm n 3 k]
    omega
  rw [e₁, e₂]
  omega

end Chain

end INet
