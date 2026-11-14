import InteractionNets.Arith.Lists

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## Example: a run as long as the bound allows

One symbol `ε` without auxiliary ports, and one rule: two `ε` facing each
other leave nothing.  The net `Eps.net k n` has `k` agents on free ports,
listed first, and `n` active pairs.  One thread alone passes the `k` agents
before it finds a pair, once for every pair and once more at the end, so it
takes `(n + 1) * (3 * k) + 6 * n` actions, exactly.  The bound of
`XMach.solo_bound` for this net is `(n + 1) * (9 * k + 16 * n) + n + 1`. -/

/-- A list made of one piece for each number below `k`, the last one
first. -/
def gen {A : Type} (f : Nat → List A) : Nat → List A
  | 0 => []
  | k + 1 => f k ++ gen f k

theorem mem_gen {A : Type} {f : Nat → List A} {x : A} :
    ∀ {k : Nat}, x ∈ gen f k ↔ ∃ j, j < k ∧ x ∈ f j
  | 0 => ⟨fun h => absurd h List.not_mem_nil, fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1 => by
    show x ∈ f k ++ gen f k ↔ _
    rw [List.mem_append, mem_gen (k := k)]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨k, Nat.lt_succ_self k, h⟩
      · exact ⟨j, Nat.lt_succ_of_lt hj, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h' | h'
      · exact .inr ⟨j, h', h⟩
      · rw [h'] at h
        exact .inl h

theorem length_gen {A : Type} {f : Nat → List A} {c : Nat} (h : ∀ j, (f j).length = c) :
    ∀ k, (gen f k).length = c * k
  | 0 => rfl
  | k + 1 => by
    show (f k ++ gen f k).length = c * (k + 1)
    rw [List.length_append, h, length_gen h k, Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem map_gen {A B : Type} (g : A → B) (f : Nat → List A) :
    ∀ k, (gen f k).map g = gen (fun j => (f j).map g) k
  | 0 => rfl
  | k + 1 => by
    show (f k ++ gen f k).map g = (f k).map g ++ gen (fun j => (f j).map g) k
    rw [List.map_append, map_gen g f k]

theorem nodup_gen {A : Type} {f : Nat → List A} (h₁ : ∀ j, (f j).Nodup)
    (h₂ : ∀ i j x, x ∈ f i → x ∈ f j → i = j) : ∀ k, (gen f k).Nodup
  | 0 => List.nodup_nil
  | k + 1 => by
    show (f k ++ gen f k).Nodup
    refine List.nodup_append.2 ⟨h₁ k, nodup_gen h₁ h₂ k, fun a ha b hb e => ?_⟩
    obtain ⟨j, hj, hb'⟩ := mem_gen.1 hb
    rw [← e] at hb'
    have := h₂ k j a ha hb'
    omega

theorem filter_ne {A B : Type} [DecidableEq A] {l : List (A × B)} {a : A}
    (h : ∀ e, e ∈ l → e.1 ≠ a) : l.filter (fun e => decide (e.1 ≠ a)) = l :=
  List.filter_eq_self.2 fun e he => decide_eq_true (h e he)

theorem filter_ne_cons_same {A B : Type} [DecidableEq A] (a : A) (b : B) (l : List (A × B)) :
    ((a, b) :: l).filter (fun e => decide (e.1 ≠ a)) = l.filter (fun e => decide (e.1 ≠ a)) :=
  List.filter_cons_of_neg (by simp)

theorem filter_ne_cons_other {A B : Type} [DecidableEq A] {a a' : A} {b : B}
    {l : List (A × B)} (h : a' ≠ a) :
    ((a', b) :: l).filter (fun e => decide (e.1 ≠ a)) =
      (a', b) :: l.filter (fun e => decide (e.1 ≠ a)) :=
  List.filter_cons_of_pos (by simpa using h)

/-- A single symbol. -/
inductive Eps
  | ε
  deriving DecidableEq, Repr

namespace Eps

/-- It has no auxiliary port. -/
def ar : Eps → Nat := fun _ => 0

/-- `ε ⋈ ε`: the empty net. -/
def data : SysData Eps := ⟨ar, [((ε, ε), RuleData.ofWires [] [])]⟩

/-- The system, by evaluation of the check. -/
def xsys : XSys Eps := data.toXSys (by decide)

/-- Its rule writes nothing. -/
theorem xsys_bounded : xsys.Bounded 0 0 := by
  intro α β R h
  cases α
  cases β
  rw [← Option.some.inj h]
  decide

/-- `k` agents, each to be wired to a free port of its own. -/
def lone (k : Nat) : List (Id × Eps) := gen (fun j => [([j, 0], ε)]) k

def loneFree (k : Nat) : List Port := gen (fun j => [([j, 1], 0)]) k

def loneWires (k : Nat) : List (Port × Port) :=
  gen (fun j => [(([j, 0], 0), ([j, 1], 0)), (([j, 1], 0), ([j, 0], 0))]) k

/-- `m` pairs of agents, each to be wired to its partner. -/
def pairs (m : Nat) : List (Id × Eps) := gen (fun j => [([j, 2], ε), ([j, 3], ε)]) m

def pairWires (m : Nat) : List (Port × Port) :=
  gen (fun j => [(([j, 2], 0), ([j, 3], 0)), (([j, 3], 0), ([j, 2], 0))]) m

/-- The memory when `m` of the `n` pairs are left.  The segments of the
pairs that are gone are still there. -/
def mem (k n m : Nat) : XNet Eps :=
  ⟨lone k ++ pairs m, loneFree k, loneWires k ++ pairWires n⟩

/-- `k` agents on free ports, listed first, and `n` active pairs. -/
def net (k n : Nat) : XNet Eps := mem k n n

theorem mem_lone {k : Nat} {e : Id × Eps} : e ∈ lone k ↔ ∃ j, j < k ∧ e = ([j, 0], ε) := by
  unfold lone
  rw [mem_gen]
  exact exists_congr fun j => and_congr Iff.rfl List.mem_singleton

theorem mem_loneFree {k : Nat} {p : Port} : p ∈ loneFree k ↔ ∃ j, j < k ∧ p = ([j, 1], 0) := by
  unfold loneFree
  rw [mem_gen]
  exact exists_congr fun j => and_congr Iff.rfl List.mem_singleton

theorem mem_loneWires {k : Nat} {w : Port × Port} :
    w ∈ loneWires k ↔ ∃ j, j < k ∧
      (w = (([j, 0], 0), ([j, 1], 0)) ∨ w = (([j, 1], 0), ([j, 0], 0))) := by
  unfold loneWires
  rw [mem_gen]
  exact exists_congr fun j => and_congr Iff.rfl (by rw [List.mem_cons, List.mem_singleton])

theorem mem_pairs {m : Nat} {e : Id × Eps} :
    e ∈ pairs m ↔ ∃ j, j < m ∧ (e = ([j, 2], ε) ∨ e = ([j, 3], ε)) := by
  unfold pairs
  rw [mem_gen]
  exact exists_congr fun j => and_congr Iff.rfl (by rw [List.mem_cons, List.mem_singleton])

theorem mem_pairWires {m : Nat} {w : Port × Port} :
    w ∈ pairWires m ↔ ∃ j, j < m ∧
      (w = (([j, 2], 0), ([j, 3], 0)) ∨ w = (([j, 3], 0), ([j, 2], 0))) := by
  unfold pairWires
  rw [mem_gen]
  exact exists_congr fun j => and_congr Iff.rfl (by rw [List.mem_cons, List.mem_singleton])

theorem lone_length (k : Nat) : (lone k).length = k := by
  have h := length_gen (f := fun j => [(([j, 0] : Id), ε)]) (c := 1) (fun _ => rfl) k
  rw [Nat.one_mul] at h
  exact h

/-- An agent on a free port is given up on: its segment leads to a port
that is not a port of an agent. -/
theorem inert (k n m : Nat) {e : Id × Eps} (he : e ∈ lone k) : (mem k n m).Inert e := by
  obtain ⟨j, hj, rfl⟩ := mem_lone.1 he
  have hw : ∀ q', ((([j, 0] : Id), 0), q') ∈ (mem k n m).wires → q' = (([j, 1] : Id), 0) := by
    intro q' h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨j', -, h | h⟩ := mem_loneWires.1 h
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · simp at h
    · obtain ⟨j', -, h | h⟩ := mem_pairWires.1 h
      · simp at h
      · simp at h
  have hw' : ∀ q', ((([j, 1] : Id), 0), q') ∈ (mem k n m).wires → q' = (([j, 0] : Id), 0) := by
    intro q' h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨j', -, h | h⟩ := mem_loneWires.1 h
      · simp at h
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    · obtain ⟨j', -, h | h⟩ := mem_pairWires.1 h
      · simp at h
      · simp at h
  refine ⟨assoc_eq_of_unique (List.mem_append_left _ he) fun q' _ => by cases q'; rfl,
    ([j, 1], 0),
    assoc_eq_of_unique (List.mem_append_left _ (mem_loneWires.2 ⟨j, hj, .inl rfl⟩)) hw, ?_,
    nextSeg_none hw'⟩
  show (if (0 : Nat) = 0 then assoc [j, 1] (mem k n m).agents else none) = none
  rw [ite_pos' rfl]
  cases h : assoc [j, 1] (mem k n m).agents with
  | none => rfl
  | some v =>
    rcases List.mem_append.1 (assoc_mem h) with h' | h'
    · obtain ⟨j', -, e⟩ := mem_lone.1 h'
      simp at e
    · obtain ⟨j', -, e | e⟩ := mem_pairs.1 h'
      · simp at e
      · simp at e

/-- A thread at the first of the pairs claims it, in six actions, and is
left with one pair fewer. -/
theorem annihilate (k n m : Nat) (hm : m < n) :
    Works xsys (mem k n (m + 1)) ⟨pairs (m + 1), .idle⟩ (mem k n m)
      ⟨(mem k n m).agents, .idle⟩ 1 6 := by
  have ha : (([m, 2] : Id), ε) ∈ (mem k n (m + 1)).agents :=
    List.mem_append_right _ (mem_pairs.2 ⟨m, Nat.lt_succ_self m, .inl rfl⟩)
  have hb : (([m, 3] : Id), ε) ∈ (mem k n (m + 1)).agents :=
    List.mem_append_right _ (mem_pairs.2 ⟨m, Nat.lt_succ_self m, .inr rfl⟩)
  have hne : ([m, 2] : Id) ≠ [m, 3] := by simp
  have hw : ∀ q', ((([m, 2] : Id), 0), q') ∈ (mem k n (m + 1)).wires →
      q' = (([m, 3] : Id), 0) := by
    intro q' h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨j', -, h | h⟩ := mem_loneWires.1 h
      · simp at h
      · simp at h
    · obtain ⟨j', -, h | h⟩ := mem_pairWires.1 h
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · simp at h
  have hl : ∀ e, e ∈ lone k → e.1 ≠ [m, 2] ∧ e.1 ≠ [m, 3] := by
    intro e he
    obtain ⟨j, -, rfl⟩ := mem_lone.1 he
    simp
  have hp : ∀ e, e ∈ pairs m → e.1 ≠ [m, 2] ∧ e.1 ≠ [m, 3] := by
    intro e he
    obtain ⟨j, hj, rfl | rfl⟩ := mem_pairs.1 he
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
  have htake : ((mem k n (m + 1)).takeAgent [m, 2]).takeAgent [m, 3] = mem k n m := by
    have e1 : (lone k ++ pairs (m + 1)).filter (fun e => decide (e.1 ≠ [m, 2])) =
        lone k ++ (([m, 3], ε) :: pairs m) := by
      show (lone k ++ (([m, 2], ε) :: ([m, 3], ε) :: pairs m)).filter _ = _
      rw [List.filter_append, filter_ne fun e he => (hl e he).1, filter_ne_cons_same,
        filter_ne_cons_other (Ne.symm hne), filter_ne fun e he => (hp e he).1]
    have e2 : (lone k ++ (([m, 3], ε) :: pairs m)).filter (fun e => decide (e.1 ≠ [m, 3])) =
        lone k ++ pairs m := by
      rw [List.filter_append, filter_ne fun e he => (hl e he).2, filter_ne_cons_same,
        filter_ne fun e he => (hp e he).2]
    show (⟨((lone k ++ pairs (m + 1)).filter fun e => decide (e.1 ≠ [m, 2])).filter
        fun e => decide (e.1 ≠ [m, 3]), loneFree k, loneWires k ++ pairWires n⟩ : XNet Eps) =
      ⟨lone k ++ pairs m, loneFree k, loneWires k ++ pairWires n⟩
    rw [e1, e2]
  have w := Works.annihilate (xs := xsys) (X := mem k n (m + 1)) (a := [m, 2]) (b := [m, 3])
    (α := ε) (β := ε) (R := (RuleData.ofWires [] []).toX) (([m, 3], ε) :: pairs m)
    (assoc_eq_of_unique ha fun q' _ => by cases q'; rfl)
    (assoc_eq_of_unique (List.mem_append_right _ (mem_pairWires.2 ⟨m, hm, .inl rfl⟩)) hw)
    (assoc_eq_of_unique hb fun q' _ => by cases q'; rfl) hne
    (assoc_eq_of_unique (XNet.mem_takeAgent.2 ⟨hb, Ne.symm hne⟩) fun q' _ => by cases q'; rfl)
    rfl rfl rfl
  rw [htake] at w
  exact w

/-- **The run of one thread, counted**: with `m` pairs left, it passes the
`k` agents on free ports and claims a pair, `m` times, and passes them once
more. -/
theorem runs (k n : Nat) : ∀ m, m ≤ n →
    Works xsys (mem k n m) ⟨(mem k n m).agents, .idle⟩ (mem k n 0) ⟨[], .idle⟩ m
      (m * (3 * k + 6) + 3 * k)
  | 0, _ => by
    have w := Works.inert_pass (xs := xsys) (X := mem k n 0) [] (lone k)
      fun e he => inert k n 0 he
    rw [lone_length] at w
    have e : 0 * (3 * k + 6) + 3 * k = 3 * k := by omega
    rw [e]
    exact w
  | m + 1, h => by
    have w₁ := Works.inert_pass (xs := xsys) (X := mem k n (m + 1)) (pairs (m + 1)) (lone k)
      fun e he => inert k n (m + 1) he
    rw [lone_length] at w₁
    have w := (w₁.trans (annihilate k n m (by omega))).trans (runs k n m (by omega))
    have e₁ : 0 + 1 + m = m + 1 := by omega
    have e₂ : 3 * k + 6 + (m * (3 * k + 6) + 3 * k) = (m + 1) * (3 * k + 6) + 3 * k := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [e₁, e₂] at w
    exact w

theorem agent_iff {k n : Nat} {i : Id} {α : Eps} :
    (net k n).toNet.agent i α ↔
      (∃ j, j < k ∧ i = [j, 0]) ∨ ∃ j, j < n ∧ (i = [j, 2] ∨ i = [j, 3]) := by
  show (i, α) ∈ lone k ++ pairs n ↔ _
  rw [List.mem_append, mem_lone, mem_pairs]
  cases α
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h | h⟩)
    · exact .inl ⟨j, hj, (Prod.mk.inj h).1⟩
    · exact .inr ⟨j, hj, .inl (Prod.mk.inj h).1⟩
    · exact .inr ⟨j, hj, .inr (Prod.mk.inj h).1⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl | rfl⟩)
    · exact .inl ⟨j, hj, rfl⟩
    · exact .inr ⟨j, hj, .inl rfl⟩
    · exact .inr ⟨j, hj, .inr rfl⟩

theorem link_iff {k n : Nat} {p q : Port} :
    (net k n).toNet.link p q ↔
      (∃ j, j < k ∧ ((p = ([j, 0], 0) ∧ q = ([j, 1], 0)) ∨
        (p = ([j, 1], 0) ∧ q = ([j, 0], 0)))) ∨
      ∃ j, j < n ∧ ((p = ([j, 2], 0) ∧ q = ([j, 3], 0)) ∨
        (p = ([j, 3], 0) ∧ q = ([j, 2], 0))) := by
  show (p, q) ∈ loneWires k ++ pairWires n ↔ _
  rw [List.mem_append, mem_loneWires, mem_pairWires]
  simp only [Prod.mk.injEq]

theorem free_iff {k n : Nat} {p : Port} :
    (net k n).toNet.free p ↔ ∃ j, j < k ∧ p = ([j, 1], 0) :=
  mem_loneFree

theorem used_len {k n : Nat} {i : Id} (h : (net k n).toNet.Used i) : i.length = 2 := by
  rcases h with ⟨γ, hg⟩ | ⟨x, q, hl⟩ | ⟨x, hf⟩
  · rcases agent_iff.1 hg with ⟨j, -, rfl⟩ | ⟨j, -, rfl | rfl⟩ <;> rfl
  · rcases link_iff.1 hl with ⟨j, -, ⟨e, -⟩ | ⟨e, -⟩⟩ | ⟨j, -, ⟨e, -⟩ | ⟨e, -⟩⟩ <;>
      (rw [(Prod.mk.inj e).1]; rfl)
  · obtain ⟨j, -, e⟩ := free_iff.1 hf
    rw [(Prod.mk.inj e).1]
    rfl

/-- The net is a valid input: its segments match its ends in pairs. -/
theorem net_matching (k n : Nat) : (net k n).toNet.Matching ar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i α β _ _
    cases α
    cases β
    rfl
  · intro p q h
    rcases link_iff.1 h with ⟨j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact link_iff.2 (.inl ⟨j, hj, .inr ⟨rfl, rfl⟩⟩)
    · exact link_iff.2 (.inl ⟨j, hj, .inl ⟨rfl, rfl⟩⟩)
    · exact link_iff.2 (.inr ⟨j, hj, .inr ⟨rfl, rfl⟩⟩)
    · exact link_iff.2 (.inr ⟨j, hj, .inl ⟨rfl, rfl⟩⟩)
  · intro p h
    rcases link_iff.1 h with ⟨j, -, ⟨rfl, e⟩ | ⟨rfl, e⟩⟩ | ⟨j, -, ⟨rfl, e⟩ | ⟨rfl, e⟩⟩ <;>
      simp at e
  · intro p q q' h h'
    rcases link_iff.1 h with ⟨j, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨j, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      rcases link_iff.1 h' with
        ⟨j', -, ⟨e, rfl⟩ | ⟨e, rfl⟩⟩ | ⟨j', -, ⟨e, rfl⟩ | ⟨e, rfl⟩⟩ <;>
      simp at e <;> simp [e]
  · intro p q h
    rcases link_iff.1 h with ⟨j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact .inr ⟨ε, agent_iff.2 (.inl ⟨j, hj, rfl⟩), Nat.le_refl _⟩
    · exact .inl (free_iff.2 ⟨j, hj, rfl⟩)
    · exact .inr ⟨ε, agent_iff.2 (.inr ⟨j, hj, .inl rfl⟩), Nat.le_refl _⟩
    · exact .inr ⟨ε, agent_iff.2 (.inr ⟨j, hj, .inr rfl⟩), Nat.le_refl _⟩
  · intro p h
    rcases h with hf | ⟨γ, hag, hle⟩
    · obtain ⟨j, hj, rfl⟩ := free_iff.1 hf
      exact ⟨([j, 0], 0), link_iff.2 (.inl ⟨j, hj, .inr ⟨rfl, rfl⟩⟩)⟩
    · obtain ⟨i, x⟩ := p
      have hag' : (net k n).toNet.agent i γ := hag
      have hle' : x ≤ 0 := hle
      have hx : x = 0 := by omega
      subst hx
      rcases agent_iff.1 hag' with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl | rfl⟩
      · exact ⟨([j, 1], 0), link_iff.2 (.inl ⟨j, hj, .inl ⟨rfl, rfl⟩⟩)⟩
      · exact ⟨([j, 3], 0), link_iff.2 (.inr ⟨j, hj, .inl ⟨rfl, rfl⟩⟩)⟩
      · exact ⟨([j, 2], 0), link_iff.2 (.inr ⟨j, hj, .inr ⟨rfl, rfl⟩⟩)⟩
  · intro i x α hf hag
    obtain ⟨j, -, e⟩ := free_iff.1 hf
    have ei : i = [j, 1] := (Prod.mk.inj e).1
    subst ei
    rcases agent_iff.1 hag with ⟨j', -, e'⟩ | ⟨j', -, e' | e'⟩ <;> simp at e'
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
  show ((lone k ++ pairs n).map Prod.fst).Nodup
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
  · unfold pairs
    rw [map_gen]
    refine nodup_gen (fun j => ?_) (fun i j x hi hj => ?_) n
    · show ([[j, 2], [j, 3]] : List Id).Nodup
      simp
    · have hi' : x = [i, 2] ∨ x = [i, 3] := by
        rcases List.mem_cons.1 hi with h | h
        · exact .inl h
        · exact .inr (List.mem_singleton.1 h)
      have hj' : x = [j, 2] ∨ x = [j, 3] := by
        rcases List.mem_cons.1 hj with h | h
        · exact .inl h
        · exact .inr (List.mem_singleton.1 h)
      rcases hi' with rfl | rfl <;> rcases hj' with h | h <;>
        exact List.head_eq_of_cons_eq h
  · obtain ⟨e₁, h₁, rfl⟩ := List.mem_map.1 ha
    obtain ⟨e₂, h₂, rfl⟩ := List.mem_map.1 hb
    obtain ⟨j, -, rfl⟩ := mem_lone.1 h₁
    obtain ⟨j', -, rfl | rfl⟩ := mem_pairs.1 h₂ <;> simp at e

theorem net_agents_length (k n : Nat) : (net k n).agents.length = k + 2 * n := by
  show (lone k ++ pairs n).length = _
  have h := length_gen (f := fun j => [(([j, 2] : Id), ε), ([j, 3], ε)]) (c := 2)
    (fun _ => rfl) n
  rw [List.length_append, lone_length]
  show k + (gen (fun j => [(([j, 2] : Id), ε), ([j, 3], ε)]) n).length = _
  omega

theorem net_wires_length (k n : Nat) : (net k n).wires.length = 2 * k + 2 * n := by
  show (loneWires k ++ pairWires n).length = _
  have h₁ := length_gen
    (f := fun j => [((([j, 0] : Id), 0), (([j, 1] : Id), 0)), (([j, 1], 0), ([j, 0], 0))])
    (c := 2) (fun _ => rfl) k
  have h₂ := length_gen
    (f := fun j => [((([j, 2] : Id), 0), (([j, 3] : Id), 0)), (([j, 3], 0), ([j, 2], 0))])
    (c := 2) (fun _ => rfl) n
  rw [List.length_append]
  show (gen (fun j => [((([j, 0] : Id), 0), (([j, 1] : Id), 0)), (([j, 1], 0), ([j, 0], 0))])
      k).length +
    (gen (fun j => [((([j, 2] : Id), 0), (([j, 3] : Id), 0)), (([j, 3], 0), ([j, 2], 0))])
      n).length = _
  omega

/-- The bound for one pass on this net: nine actions for each agent on a
free port and sixteen for each pair. -/
theorem net_passBound (k n : Nat) : (net k n).passBound n 0 0 = 9 * k + 16 * n := by
  show 7 * ((net k n).agents.length + 0 * n) + ((net k n).wires.length + 0 * n) = _
  rw [net_agents_length, net_wires_length]
  omega

/-- **One thread alone takes `(n + 1) * (3 * k) + 6 * n` actions, exactly**:
after that many it is at rest with all `n` pairs claimed, and after any
smaller number it is not at rest. -/
theorem solo_exact (k n : Nat) :
    (XMach.init (net k n) 1).trace xsys (fun _ => 0) ((n + 1) * (3 * k) + 6 * n) =
        (⟨mem k n 0, [⟨[], .idle⟩]⟩, n) ∧
      ∀ i, i < (n + 1) * (3 * k) + 6 * n →
        ¬ ((XMach.init (net k n) 1).trace xsys (fun _ => 0) i).1.resting = true := by
  have w := (runs k n n (Nat.le_refl n)).trace
  have e : n * (3 * k + 6) + 3 * k = (n + 1) * (3 * k) + 6 * n := by
    rw [Nat.mul_add, Nat.add_mul, Nat.one_mul]
    omega
  rw [e] at w
  rw [XMach.init_one]
  exact w

/-- **The bound against the run.**  On the net with `k` agents on free
ports and `n` active pairs, the bound of `XMach.solo_bound` puts one thread
at rest after `(n + 1) * (9 * k + 16 * n) + n + 1` actions, and it is not at
rest before `(n + 1) * (3 * k) + 6 * n`. -/
theorem solo_tight (k n : Nat) :
    (∀ i, (n + 1) * (9 * k + 16 * n) + n + 1 ≤ i →
        ((XMach.init (net k n) 1).trace xsys (fun _ => 0) i).1.resting = true) ∧
      ∀ i, i < (n + 1) * (3 * k) + 6 * n →
        ¬ ((XMach.init (net k n) 1).trace xsys (fun _ => 0) i).1.resting = true := by
  obtain ⟨hL, hlow⟩ := solo_exact k n
  have hX : (net k n).toNet.WF xsys.sys.ar := net_wf k n
  have live := XMach.trace_live (xs := xsys) (fun _ => 0)
    (XMach.init_live hX (Nat.succ_pos 0))
  have hrest : ((XMach.init (net k n) 1).trace xsys (fun _ => 0)
      ((n + 1) * (3 * k) + 6 * n)).1.resting = true := by
    rw [hL]
    rfl
  have hc : ((XMach.init (net k n) 1).trace xsys (fun _ => 0)
      ((n + 1) * (3 * k) + 6 * n)).2 = n := by rw [hL]
  obtain ⟨hq, hnorm⟩ := (live _).rest hrest
  have run := XMach.trace_run xsys (fun _ => 0) (XMach.init (net k n) 1)
    ((n + 1) * (3 * k) + 6 * n)
  rw [XMach.init_toMach, hc] at run
  obtain ⟨hs, -⟩ := run.final hX hq hnorm
  have hb := XMach.solo_bound (xs := xsys) hX (net_nodup k n) xsys_bounded hs hnorm
  refine ⟨fun i hi => (hb i ?_).1, hlow⟩
  rw [net_passBound]
  omega

/-- With at least as many agents on free ports as pairs, the bound is at
most nine times the length of the run, plus one.  As the number of agents
on free ports grows the ratio tends to three. -/
theorem bound_le (k n : Nat) (h : n ≤ k) :
    (n + 1) * (9 * k + 16 * n) + n + 1 ≤ 9 * ((n + 1) * (3 * k) + 6 * n) + 1 := by
  have h1 : (n + 1) * (16 * n) ≤ (n + 1) * (16 * k) := Nat.mul_le_mul_left _ (by omega)
  have e1 : (n + 1) * (9 * k + 16 * n) = (n + 1) * (9 * k) + (n + 1) * (16 * n) :=
    Nat.mul_add _ _ _
  have e2 : (n + 1) * (9 * k) = 9 * ((n + 1) * k) := Nat.mul_left_comm _ _ _
  have e3 : (n + 1) * (16 * k) = 16 * ((n + 1) * k) := Nat.mul_left_comm _ _ _
  have e4 : (n + 1) * (3 * k) = 3 * ((n + 1) * k) := Nat.mul_left_comm _ _ _
  rw [e3] at h1
  rw [e1, e2, e4]
  omega

/-- The net with no pair is in normal form. -/
theorem net_normal (k : Nat) : Normal (Step xsys.sys) (net k 0).toNet := by
  obtain ⟨hL, -⟩ := solo_exact k 0
  have hX : (net k 0).toNet.WF xsys.sys.ar := net_wf k 0
  have live := XMach.trace_live (xs := xsys) (fun _ => 0)
    (XMach.init_live hX (Nat.succ_pos 0))
  have hrest : ((XMach.init (net k 0) 1).trace xsys (fun _ => 0)
      ((0 + 1) * (3 * k) + 6 * 0)).1.resting = true := by
    rw [hL]
    rfl
  have hn := ((live _).rest hrest).2
  rw [hL] at hn
  exact hn

/-- On the net with no pair, a thread that starts anywhere in the list
passes every agent without writing. -/
theorem reads (k nt : Nat) :
    ∀ T, T ∈ (XMach.init (net k 0) nt).ths → T.Reads xsys (net k 0) := by
  intro T hT
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
  have hin : ∀ e, e ∈ (net k 0).agents.drop t ++ (net k 0).agents.take t →
      (net k 0).Inert e := by
    intro e he
    have he' : e ∈ (net k 0).agents := by
      rcases List.mem_append.1 he with h | h
      · exact List.mem_of_mem_drop h
      · exact List.mem_of_mem_take h
    rcases List.mem_append.1 he' with h | h
    · exact inert k 0 0 h
    · exact absurd h List.not_mem_nil
  have st := Stays.inert_pass (xs := xsys) (X := net k 0) [] _ hin
  rw [List.append_nil] at st
  exact (st.after rfl).1

/-- **The window against the run.**  On the net with `k` agents on free
ports and nothing to reduce, one thread alone is at rest after `3 * k`
actions (`solo_exact`).  With two threads and the schedule that gives the
first every `F`-th action, which is fair with window `F`, the bound of
`XMach.fair_bound` puts them at rest after `F * (9 * k + 1)` actions, and
they are not at rest after `F * (3 * k) - F` actions or fewer: the window
multiplies the work of a thread. -/
theorem window_tight (k F : Nat) (hF : 2 ≤ F) :
    (∀ u, u < 2 → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ starve F j = u) ∧
      (∀ i, F * (9 * k + 1) ≤ i →
        ((XMach.init (net k 0) 2).trace xsys (starve F) i).1.resting = true) ∧
      ∀ i, i + F ≤ F * (3 * k) →
        ¬ ((XMach.init (net k 0) 2).trace xsys (starve F) i).1.resting = true := by
  have hX : (net k 0).toNet.WF xsys.sys.ar := net_wf k 0
  refine ⟨starve_fair hF, fun i hi => ?_, ?_⟩
  · have hb := XMach.fair_bound (xs := xsys) hX (net_nodup k 0) (nt := 2) (by decide)
      xsys_bounded (.refl _) (net_normal k) (starve F) (starve_fair hF) i
    refine (hb ?_).1
    rw [net_passBound]
    have e : (0 + 1) * (9 * k + 16 * 0) + 0 * (0 + 0 + 1) + 1 = 9 * k + 1 := by omega
    rw [e]
    exact hi
  · have h0 := XMach.init_thread (net k 0) (nt := 2) (u := 0) (by decide)
    have st := Stays.inert_pass (xs := xsys) (X := net k 0) []
      ((net k 0).agents.drop 0 ++ (net k 0).agents.take 0) fun e he => by
        have he' : e ∈ lone k ++ pairs 0 ++ [] := he
        rw [List.append_nil] at he'
        rcases List.mem_append.1 he' with h | h
        · exact inert k 0 0 h
        · exact absurd h List.not_mem_nil
    rw [List.append_nil] at st
    have hl : ((net k 0).agents.drop 0 ++ (net k 0).agents.take 0).length = k := by
      show (lone k ++ pairs 0 ++ []).length = k
      rw [List.append_nil, List.length_append, lone_length]
      rfl
    rw [hl] at st
    exact XMach.starved (xs := xsys) (starve F) (reads k 2) h0 st (by omega) (starve_sparse F)

/-- **The window against the run, for any number of threads.**  The same
with `nt` threads, as many as the window has room for: under a schedule
that gives each of them an action in every `F`, the bound puts them at rest
after `F * (9 * k + 1)` actions, and they are not at rest after
`F * (3 * k) - F` actions or fewer. -/
theorem window_many (k nt F : Nat) (hnt : 0 < nt) (hF : nt ≤ F) :
    (∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ starveAmong nt F j = u) ∧
      (∀ i, F * (9 * k + 1) ≤ i →
        ((XMach.init (net k 0) nt).trace xsys (starveAmong nt F) i).1.resting = true) ∧
      ∀ i, i + F ≤ F * (3 * k) →
        ¬ ((XMach.init (net k 0) nt).trace xsys (starveAmong nt F) i).1.resting = true := by
  have hX : (net k 0).toNet.WF xsys.sys.ar := net_wf k 0
  refine ⟨starveAmong_fair hF, fun i hi => ?_, ?_⟩
  · have hb := XMach.fair_bound (xs := xsys) hX (net_nodup k 0) hnt
      xsys_bounded (.refl _) (net_normal k) (starveAmong nt F) (starveAmong_fair hF) i
    refine (hb ?_).1
    rw [net_passBound]
    have e : (0 + 1) * (9 * k + 16 * 0) + 0 * (0 + 0 + 1) + 1 = 9 * k + 1 := by omega
    rw [e]
    exact hi
  · have h0 := XMach.init_thread (net k 0) (nt := nt) (u := 0) hnt
    have st := Stays.inert_pass (xs := xsys) (X := net k 0) []
      ((net k 0).agents.drop 0 ++ (net k 0).agents.take 0) fun e he => by
        have he' : e ∈ lone k ++ pairs 0 ++ [] := he
        rw [List.append_nil] at he'
        rcases List.mem_append.1 he' with h | h
        · exact inert k 0 0 h
        · exact absurd h List.not_mem_nil
    rw [List.append_nil] at st
    have hl : ((net k 0).agents.drop 0 ++ (net k 0).agents.take 0).length = k := by
      show (lone k ++ pairs 0 ++ []).length = k
      rw [List.append_nil, List.length_append, lone_length]
      rfl
    rw [hl] at st
    exact XMach.starved (xs := xsys) (starveAmong nt F) (reads k nt) h0 st (by omega)
      (starveAmong_sparse nt F)

/-- The segment at the principal port of an agent on a free port leads to
that port. -/
theorem lone_wire {k n m j : Nat} {q : Port}
    (h : ((([j, 0] : Id), 0), q) ∈ (mem k n m).wires) : q = (([j, 1] : Id), 0) := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨j', -, h | h⟩ := mem_loneWires.1 h
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp at h
  · obtain ⟨j', -, h | h⟩ := mem_pairWires.1 h
    · simp at h
    · simp at h

/-- On the net with no pair, the pass of a thread that starts anywhere in
the list takes `3 * k` actions and costs a look at every cell of the memory
for each agent. -/
theorem pass_spent (k nt : Nat) : ∀ T, T ∈ (XMach.init (net k 0) nt).ths →
    ∃ j, (∀ j', j' < j → T.after xsys (net k 0) j' ≠ ⟨[], .idle⟩) ∧
      k * (3 * k + 3) ≤ T.spent xsys (net k 0) j := by
  intro T hT
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
  have hin : ∀ e, e ∈ (net k 0).agents.drop t ++ (net k 0).agents.take t →
      (net k 0).Inert e ∧ ∀ q, assoc (e.1, 0) (net k 0).wires = some q → q.2 = 0 := by
    intro e he
    have he' : e ∈ (net k 0).agents := by
      rcases List.mem_append.1 he with h | h
      · exact List.mem_of_mem_drop h
      · exact List.mem_of_mem_take h
    rcases List.mem_append.1 he' with h | h
    · refine ⟨inert k 0 0 h, fun q hq => ?_⟩
      obtain ⟨j, -, rfl⟩ := mem_lone.1 h
      rw [lone_wire (assoc_mem hq)]
    · exact absurd h List.not_mem_nil
  have st := Stays.inert_pass (xs := xsys) (X := net k 0) [] _ fun e he => (hin e he).1
  have sp := XThread.spent_inert_pass (xs := xsys) (X := net k 0) [] _ hin
  rw [List.append_nil] at st sp
  have hl : ((net k 0).agents.drop t ++ (net k 0).agents.take t).length = k := by
    have h := net_agents_length k 0
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  rw [hl] at st
  rw [hl, net_agents_length, net_wires_length] at sp
  have e : 3 + (k + 2 * 0) + (2 * k + 2 * 0) = 3 * k + 3 := by omega
  rw [e] at sp
  exact ⟨3 * k, (st.after rfl).2.1, sp⟩

/-- **The bound on the time against the run.**  On the net with `k` agents
on free ports and nothing to reduce, with any number of threads and any
schedule, the bound of `XMach.time_bound` is `nt * (9 * k) * (4 * k + 1)`,
and by the time the program is at rest it has taken `nt * (k * (3 * k + 3))`
or more: every thread reads the whole memory once for each agent. -/
theorem time_tight (k nt : Nat) (hnt : 0 < nt) (σ : Nat → Nat) :
    (∀ i, (XMach.init (net k 0) nt).time xsys σ i ≤ nt * (9 * k) * (4 * k + 1)) ∧
      ∀ i, ((XMach.init (net k 0) nt).trace xsys σ i).1.resting = true →
        nt * (k * (3 * k + 3)) ≤ (XMach.init (net k 0) nt).time xsys σ i := by
  have hX : (net k 0).toNet.WF xsys.sys.ar := net_wf k 0
  constructor
  · intro i
    have h := XMach.time_bound (xs := xsys) hX (net_nodup k 0) hnt xsys_bounded (.refl _)
      (net_normal k) σ i
    rw [net_passBound, net_agents_length, net_wires_length] at h
    have e₁ : (nt + 0) * (9 * k + 16 * 0) + 0 * (0 + 0 + 1) = nt * (9 * k) := rfl
    have e₂ : 2 * (k + 2 * 0 + 0 * 0) + (2 * k + 2 * 0 + 0 * 0) + 0 + 0 + 1 = 4 * k + 1 := by
      omega
    rw [e₁, e₂] at h
    exact h
  · intro i hr
    have hl : (XMach.init (net k 0) nt).ths.length = nt := by
      show ((List.range nt).map _).length = nt
      rw [List.length_map, List.length_range]
    have h := XMach.time_ge_rest (xs := xsys) σ (reads k nt) (pass_spent k nt) i hr
    rw [hl] at h
    exact h

/-- The bound is at most twelve times that time. -/
theorem time_bound_le (k nt : Nat) :
    nt * (9 * k) * (4 * k + 1) ≤ 12 * (nt * (k * (3 * k + 3))) := by
  have h : 9 * k * (4 * k + 1) ≤ 12 * (k * (3 * k + 3)) := by
    have e₁ : 9 * k * (4 * k + 1) = k * (36 * k + 9) := by
      have e : 9 * (4 * k + 1) = 36 * k + 9 := by omega
      rw [Nat.mul_comm 9 k, Nat.mul_assoc, e]
    have e₂ : 12 * (k * (3 * k + 3)) = k * (36 * k + 36) := by
      have e : 12 * (3 * k + 3) = 36 * k + 36 := by omega
      rw [Nat.mul_left_comm, e]
    rw [e₁, e₂]
    exact Nat.mul_le_mul_left k (by omega)
  rw [Nat.mul_assoc, Nat.mul_left_comm 12 nt]
  exact Nat.mul_le_mul_left nt h

/-- On the net with no pair, the pass of a thread takes `3 * k` actions,
which cost seven for each agent on the indexed memory, or more. -/
theorem pass_least (k nt : Nat) : ∀ T, T ∈ (XMach.init (net k 0) nt).ths →
    ∃ j, (∀ j', j' < j → T.after xsys (net k 0) j' ≠ ⟨[], .idle⟩) ∧
      7 * k ≤ T.tally XThread.least xsys (net k 0) j := by
  intro T hT
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
  have hin : ∀ e, e ∈ (net k 0).agents.drop t ++ (net k 0).agents.take t →
      (net k 0).Inert e := by
    intro e he
    have he' : e ∈ (net k 0).agents := by
      rcases List.mem_append.1 he with h | h
      · exact List.mem_of_mem_drop h
      · exact List.mem_of_mem_take h
    rcases List.mem_append.1 he' with h | h
    · exact inert k 0 0 h
    · exact absurd h List.not_mem_nil
  have st := Stays.inert_pass (xs := xsys) (X := net k 0) [] _ hin
  have sp := XThread.least_inert_pass (xs := xsys) (X := net k 0) [] _ hin
  rw [List.append_nil] at st sp
  have hl : ((net k 0).agents.drop t ++ (net k 0).agents.take t).length = k := by
    have h := net_agents_length k 0
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  rw [hl] at st sp
  exact ⟨3 * k, (st.after rfl).2.1, sp⟩

/-- **The bound on the indexed time against the run.**  On the net with
`k` agents on free ports and nothing to reduce, with any number of threads
and any schedule, the bound of `IMach.time_bound` is `nt * (63 * k) + k`,
and by the time the program is at rest it has taken `nt * (7 * k)` or
more: the time is linear in the net, where on lists it is quadratic. -/
theorem itime_tight (k nt : Nat) (hnt : 0 < nt) (σ : Nat → Nat) :
    (∀ i, (IMach.init (net k 0) nt).time xsys σ i ≤ nt * (63 * k) + k) ∧
      ∀ i, ((XMach.init (net k 0) nt).trace xsys σ i).1.resting = true →
        nt * (7 * k) ≤ (IMach.init (net k 0) nt).time xsys σ i := by
  have hX : (net k 0).toNet.WF xsys.sys.ar := net_wf k 0
  constructor
  · intro i
    have h := IMach.time_bound (xs := xsys) hX (net_nodup k 0) hnt xsys_bounded (.refl _)
      (net_normal k) σ i
    rw [net_passBound, net_agents_length] at h
    have e₁ : ((nt + 0) * (9 * k + 16 * 0) + 0 * (0 + 0 + 1)) * (0 + 0 + 7) =
        nt * (63 * k) := by
      show nt * (9 * k) * 7 = nt * (63 * k)
      have e : 9 * k * 7 = 63 * k := by omega
      rw [Nat.mul_assoc, e]
    have e₂ : (2 * 0 + 1) * (k + 2 * 0 + 0 * 0) = k := by
      show 1 * k = k
      exact Nat.one_mul k
    rw [e₁, e₂] at h
    exact h
  · intro i hr
    have hl : (XMach.init (net k 0) nt).ths.length = nt := by
      show ((List.range nt).map _).length = nt
      rw [List.length_map, List.length_range]
    have h := XMach.tally_ge_rest (xs := xsys) XThread.least σ (reads k nt)
      (pass_least k nt) i hr
    rw [hl] at h
    exact Nat.le_trans h (IMach.time_ge_least hX (net_nodup k 0) hnt σ i)

/-- The bound is at most ten times that time. -/
theorem itime_bound_le (k nt : Nat) (hnt : 0 < nt) :
    nt * (63 * k) + k ≤ 10 * (nt * (7 * k)) := by
  have hk : k ≤ nt * k := Nat.le_mul_of_pos_left k hnt
  have e₁ : nt * (63 * k) = 63 * (nt * k) := Nat.mul_left_comm nt 63 k
  have e₂ : nt * (7 * k) = 7 * (nt * k) := Nat.mul_left_comm nt 7 k
  rw [e₁, e₂]
  omega

/-- **What the index gains where there is nothing to reduce.**  On `k`
agents on free ports, with any number of threads under any schedule, by
the time the program is at rest lists have taken `(3 * k + 3) / 64` times
as long as the indexed memory, or more: the gain grows with the net. -/
theorem index_gain (k nt : Nat) (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat)
    (hr : ((XMach.init (net k 0) nt).trace xsys σ i).1.resting = true) :
    (3 * k + 3) * (IMach.init (net k 0) nt).time xsys σ i ≤
      64 * (XMach.init (net k 0) nt).time xsys σ i := by
  have h₁ := (itime_tight k nt hnt σ).1 i
  have h₂ := (time_tight k nt hnt σ).2 i hr
  have hk : k ≤ nt * k := Nat.le_mul_of_pos_left k hnt
  have h₃ : (IMach.init (net k 0) nt).time xsys σ i ≤ 64 * (nt * k) := by
    have e : nt * (63 * k) = 63 * (nt * k) := Nat.mul_left_comm nt 63 k
    omega
  have h₄ := Nat.mul_le_mul_left (3 * k + 3) h₃
  have e : (3 * k + 3) * (64 * (nt * k)) = 64 * (nt * (k * (3 * k + 3))) := by
    rw [Nat.mul_left_comm (3 * k + 3) 64, Nat.mul_left_comm (3 * k + 3) nt,
      Nat.mul_comm (3 * k + 3) k]
  rw [e] at h₄
  exact Nat.le_trans h₄ (Nat.mul_le_mul_left 64 h₂)

end Eps

end INet
