import InteractionNets.Arith.Rounds

/-! ### Two additions side by side: tags, and one thread on both -/

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

/-- A port with `c` put at the end of the name of its agent. -/
def tagPort (c : Nat) (p : Port) : Port := (p.1 ++ [c], p.2)

/-- `tagNet c X`: the net `X` with `c` put at the end of every name.  A new
agent is named by putting a number in front of the name of one of the two
agents that make it, so a tag at the end is kept by every interaction. -/
def tagNet (c : Nat) (X : XNet Arith) : XNet Arith :=
  ⟨X.agents.map fun e => (e.1 ++ [c], e.2), X.free.map (tagPort c),
    X.wires.map fun e => (tagPort c e.1, tagPort c e.2)⟩

/-- Two nets side by side: the cells of the first, then those of the
second, and no wire between them. -/
def beside (X Y : XNet Arith) : XNet Arith :=
  ⟨X.agents ++ Y.agents, X.free ++ Y.free, X.wires ++ Y.wires⟩

/-- **Two additions side by side**: the net for `m + n` with its names
tagged `0`, then the net for `m' + n'` with its names tagged `1`. -/
def twoSums (m n m' n' : Nat) : XNet Arith :=
  beside (tagNet 0 (sum m n)) (tagNet 1 (sum m' n'))

/-- Both sums come out: `3 + 2` and `2 + 4` side by side reduce in seven
steps to `5` and `6`. -/
example : ((twoSums 3 2 2 4).normalize xsys 100).map
    (fun r => (readNat r.1 20 ([0, 0], 0), readNat r.1 20 ([0, 1], 0), r.2)) =
      some (some 5, some 6, 7) := by
  decide +kernel

/-- **The rounds one thread takes on two additions side by side, as the
runs show**: those of each addition alone, and one more pass over what the
first has left, `5 * m + 3 * n + 5` actions, at the very end. -/
def twoSolo (m n m' n' : Nat) : Nat := soloWork m n + soloWork m' n' + (5 * m + 3 * n + 5)

/-- A run that is at rest after `R` rounds and has done more work than
`R - 1` rounds can hold takes exactly `R` rounds. -/
theorem rounds_of_work {c : Nat} {M : XMach Arith} {R : Nat}
    (hr : (M.trace xsys (fun i => i % c) (c * R)).1.resting = true)
    (hw : c * (R - 1) < M.work xsys (fun i => i % c) (c * R)) : Rounds c M R := by
  refine ⟨hr, fun R' hR' hrest => ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, c * R = c * R' + d := ⟨c * R - c * R', by
    have h := Nat.mul_le_mul_left c (Nat.le_of_lt hR')
    omega⟩
  have e := XMach.work_rest (xs := xsys) (fun i => i % c) hrest d
  have le := XMach.work_le_count xsys (fun i => i % c) M (c * R')
  have h2 := Nat.mul_le_mul_left c (show R' ≤ R - 1 by omega)
  rw [hd] at hw
  omega

/-- A run that is at rest after `R + 1` rounds and not after `R` takes
exactly `R + 1`. -/
theorem rounds_of_not {c : Nat} {M : XMach Arith} {R : Nat}
    (hr : (M.trace xsys (fun i => i % c) (c * (R + 1))).1.resting = true)
    (hn : ¬ (M.trace xsys (fun i => i % c) (c * R)).1.resting = true) :
    Rounds c M (R + 1) := by
  refine ⟨hr, fun R' hR' hrest => hn ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, R = R' + d := ⟨R - R', by omega⟩
  have h2 := XMach.resting_trace (xs := xsys) (fun i => i % c) hrest (c * d)
  rw [← Nat.mul_add] at h2
  exact h2

/-- A run that is at rest after `R₀` rounds takes some number of rounds, at
most `R₀`. -/
theorem rounds_exists {c : Nat} {M : XMach Arith} : ∀ R₀,
    (M.trace xsys (fun i => i % c) (c * R₀)).1.resting = true →
    ∃ R, R ≤ R₀ ∧ Rounds c M R
  | 0, h => ⟨0, Nat.le_refl 0, h, fun R' hR' => absurd hR' (Nat.not_lt_zero R')⟩
  | R₀ + 1, h => by
    by_cases h' : (M.trace xsys (fun i => i % c) (c * R₀)).1.resting = true
    · obtain ⟨R, hR, r⟩ := rounds_exists R₀ h'
      exact ⟨R, Nat.le_succ_of_le hR, r⟩
    · exact ⟨R₀ + 1, Nat.le_refl _, rounds_of_not h h'⟩

/-- The work of a run that is at rest. -/
theorem total_of_rest {c : Nat} {M : XMach Arith} {N W : Nat}
    (hr : (M.trace xsys (fun i => i % c) N).1.resting = true)
    (hw : M.work xsys (fun i => i % c) N = W) : M.Total xsys (fun i => i % c) W :=
  ⟨N, fun i hi => by
    obtain ⟨d, rfl⟩ : ∃ d, i = N + d := ⟨i - N, by omega⟩
    rw [XMach.work_rest (fun i => i % c) hr d, hw]⟩

set_option maxRecDepth 100000 in
/-- **One thread on two additions side by side, on every pair of sizes
computed.**  For `m` and `m'` up to two and `n` and `n'` below three, the
thread is at rest after exactly `twoSolo` actions, none of them a rest.
This is a computation, size by size; it is not a proof for every size. -/
theorem two_sums_one_checked : ∀ m, m < 2 → ∀ n, n < 3 → ∀ m', m' < 2 → ∀ n', n' < 3 →
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') 1).trace xsys (fun i => i % 1)
        (1 * twoSolo (m + 1) n (m' + 1) n')).1.resting = true ∧
      (XMach.init (twoSums (m + 1) n (m' + 1) n') 1).work xsys (fun i => i % 1)
        (1 * twoSolo (m + 1) n (m' + 1) n') = twoSolo (m + 1) n (m' + 1) n' := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Two threads on the same nets are at rest two rounds sooner at
least**, on every pair of sizes computed. -/
theorem two_sums_two_checked : ∀ m, m < 2 → ∀ n, n < 3 → ∀ m', m' < 2 → ∀ n', n' < 3 →
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') 2).trace xsys (fun i => i % 2)
      (2 * (twoSolo (m + 1) n (m' + 1) n' - 2))).1.resting = true := by
  decide +kernel

/-- **One thread takes `twoSolo` rounds on two additions side by side**,
for the sizes computed. -/
theorem two_sums_one_thread (m n m' n' : Nat) (hm : m < 2) (hn : n < 3) (hm' : m' < 2)
    (hn' : n' < 3) :
    Rounds 1 (XMach.init (twoSums (m + 1) n (m' + 1) n') 1) (twoSolo (m + 1) n (m' + 1) n') := by
  obtain ⟨hr, hw⟩ := two_sums_one_checked m hm n hn m' hm' n' hn'
  refine rounds_of_work hr ?_
  rw [hw]
  have h : 1 ≤ twoSolo (m + 1) n (m' + 1) n' := by
    unfold twoSolo
    omega
  omega

/-- **Two threads take fewer rounds than one on two additions side by
side**, by two at least, for the sizes computed. -/
theorem two_sums_two_threads (m n m' n' : Nat) (hm : m < 2) (hn : n < 3) (hm' : m' < 2)
    (hn' : n' < 3) :
    ∃ R, R + 2 ≤ twoSolo (m + 1) n (m' + 1) n' ∧
      Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2) R := by
  obtain ⟨R, hR, r⟩ := rounds_exists _ (two_sums_two_checked m hm n hn m' hm' n' hn')
  have h : 2 ≤ twoSolo (m + 1) n (m' + 1) n' := by
    unfold twoSolo
    omega
  exact ⟨R, by omega, r⟩

set_option maxRecDepth 100000 in
/-- **`2 + 2` twice, side by side**: one thread takes 147 rounds, two
threads 106 and three threads 86; the work is 147, 191 and 255 actions that
are not rests. -/
theorem two_sums_2_2 :
    (Rounds 1 (XMach.init (twoSums 2 2 2 2) 1) 147 ∧
      (XMach.init (twoSums 2 2 2 2) 1).Total xsys (fun i => i % 1) 147) ∧
    (Rounds 2 (XMach.init (twoSums 2 2 2 2) 2) 106 ∧
      (XMach.init (twoSums 2 2 2 2) 2).Total xsys (fun i => i % 2) 191) ∧
    (Rounds 3 (XMach.init (twoSums 2 2 2 2) 3) 86 ∧
      (XMach.init (twoSums 2 2 2 2) 3).Total xsys (fun i => i % 3) 255) := by
  have a1 : ((XMach.init (twoSums 2 2 2 2) 1).trace xsys (fun i => i % 1) (1 * 147)).1.resting =
      true ∧ (XMach.init (twoSums 2 2 2 2) 1).work xsys (fun i => i % 1) (1 * 147) = 147 := by
    decide +kernel
  have a2 : ((XMach.init (twoSums 2 2 2 2) 2).trace xsys (fun i => i % 2) (2 * 106)).1.resting =
      true ∧ ¬ ((XMach.init (twoSums 2 2 2 2) 2).trace xsys (fun i => i % 2)
        (2 * 105)).1.resting = true ∧
      (XMach.init (twoSums 2 2 2 2) 2).work xsys (fun i => i % 2) (2 * 106) = 191 := by
    decide +kernel
  have a3 : ((XMach.init (twoSums 2 2 2 2) 3).trace xsys (fun i => i % 3) (3 * 86)).1.resting =
      true ∧ ¬ ((XMach.init (twoSums 2 2 2 2) 3).trace xsys (fun i => i % 3)
        (3 * 85)).1.resting = true ∧
      (XMach.init (twoSums 2 2 2 2) 3).work xsys (fun i => i % 3) (3 * 86) = 255 := by
    decide +kernel
  exact ⟨⟨rounds_of_work a1.1 (by
      rw [a1.2]
      decide), total_of_rest a1.1 a1.2⟩,
    ⟨rounds_of_not a2.1 a2.2.1, total_of_rest a2.1 a2.2.2⟩,
    ⟨rounds_of_not a3.1 a3.2.1, total_of_rest a3.1 a3.2.2⟩⟩

set_option maxRecDepth 100000 in
/-- **`4 + 3` twice, side by side**: one thread takes 254 rounds, two
threads 174; the work is 254 and 327. -/
theorem two_sums_4_3 :
    (Rounds 1 (XMach.init (twoSums 4 3 4 3) 1) 254 ∧
      (XMach.init (twoSums 4 3 4 3) 1).Total xsys (fun i => i % 1) 254) ∧
    (Rounds 2 (XMach.init (twoSums 4 3 4 3) 2) 174 ∧
      (XMach.init (twoSums 4 3 4 3) 2).Total xsys (fun i => i % 2) 327) := by
  have a1 : ((XMach.init (twoSums 4 3 4 3) 1).trace xsys (fun i => i % 1) (1 * 254)).1.resting =
      true ∧ (XMach.init (twoSums 4 3 4 3) 1).work xsys (fun i => i % 1) (1 * 254) = 254 := by
    decide +kernel
  have a2 : ((XMach.init (twoSums 4 3 4 3) 2).trace xsys (fun i => i % 2) (2 * 174)).1.resting =
      true ∧ ¬ ((XMach.init (twoSums 4 3 4 3) 2).trace xsys (fun i => i % 2)
        (2 * 173)).1.resting = true ∧
      (XMach.init (twoSums 4 3 4 3) 2).work xsys (fun i => i % 2) (2 * 174) = 327 := by
    decide +kernel
  exact ⟨⟨rounds_of_work a1.1 (by
      rw [a1.2]
      decide), total_of_rest a1.1 a1.2⟩,
    ⟨rounds_of_not a2.1 a2.2.1, total_of_rest a2.1 a2.2.2⟩⟩

/-- A name carries the tag `c`: its last number is `c`. -/
def tagged (c : Nat) : Id → Bool
  | [] => false
  | [x] => x == c
  | _ :: y :: l => tagged c (y :: l)

theorem tagged_append (c d : Nat) : ∀ i : Id, tagged c (i ++ [d]) = (d == c)
  | [] => rfl
  | [_] => rfl
  | _ :: y :: l => tagged_append c d (y :: l)

theorem tagged_self (c : Nat) (i : Id) : tagged c (i ++ [c]) = true := by
  rw [tagged_append]
  exact beq_self_eq_true c

theorem tagged_other {c d : Nat} (h : d ≠ c) (i : Id) : tagged c (i ++ [d]) = false := by
  rw [tagged_append]
  exact beq_false_of_ne h

/-- An agent cell with its name tagged. -/
def tagA (c : Nat) (e : Id × Arith) : Id × Arith := (e.1 ++ [c], e.2)

/-- A segment cell with both names tagged. -/
def tagL (c : Nat) (e : Port × Port) : Port × Port := (tagPort c e.1, tagPort c e.2)

theorem tagPort_inj {c : Nat} {p q : Port} (h : tagPort c p = tagPort c q) : p = q := by
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  have h1 : i ++ [c] = j ++ [c] := congrArg Prod.fst h
  have h2 : a = b := congrArg Prod.snd h
  rw [List.append_cancel_right h1, h2]

theorem filter_swap {A : Type} (p q : A → Bool) : ∀ l : List A,
    (l.filter p).filter q = (l.filter q).filter p
  | [] => rfl
  | x :: l => by
    have ih := filter_swap p q l
    by_cases hp : p x = true <;> by_cases hq : q x = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq, List.filter_cons_of_pos hq,
        List.filter_cons_of_pos hp, ih]
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg hq, List.filter_cons_of_neg hq, ih]
    · rw [List.filter_cons_of_neg hp, List.filter_cons_of_pos hq, List.filter_cons_of_neg hp, ih]
    · rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg hq, ih]

theorem assoc_tagged_filter (c : Nat) (k : Id) (hk : tagged c k = true) :
    ∀ l : List (Id × Arith), assoc k (l.filter fun e => tagged c e.1) = assoc k l
  | [] => rfl
  | (k', v) :: l => by
    have ih := assoc_tagged_filter c k hk l
    by_cases ht : tagged c k' = true
    · rw [List.filter_cons_of_pos (p := fun e : Id × Arith => tagged c e.1) ht]
      show (if k' = k then some v else assoc k (l.filter fun e => tagged c e.1)) =
        (if k' = k then some v else assoc k l)
      rw [ih]
    · rw [List.filter_cons_of_neg (p := fun e : Id × Arith => tagged c e.1) ht]
      have hne : ¬ k' = k := fun e => ht (by
        rw [e]
        exact hk)
      show _ = (if k' = k then some v else assoc k l)
      rw [ite_neg' hne]
      exact ih

theorem assoc_map_tag (c : Nat) (i : Id) : ∀ l : List (Id × Arith),
    assoc (i ++ [c]) (l.map (tagA c)) = assoc i l
  | [] => rfl
  | (k, v) :: l => by
    show (if k ++ [c] = i ++ [c] then some v else assoc (i ++ [c]) (l.map (tagA c))) =
      (if k = i then some v else assoc i l)
    by_cases e : k = i
    · rw [ite_pos' e, ite_pos' (by rw [e])]
    · rw [ite_neg' e, ite_neg' (fun h => e (List.append_cancel_right h))]
      exact assoc_map_tag c i l

theorem assoc_port_filter (c : Nat) (p : Port) (hp : tagged c p.1 = true) :
    ∀ l : List (Port × Port), assoc p (l.filter fun e => tagged c e.1.1) = assoc p l
  | [] => rfl
  | (k', v) :: l => by
    have ih := assoc_port_filter c p hp l
    by_cases ht : tagged c k'.1 = true
    · rw [List.filter_cons_of_pos (p := fun e : Port × Port => tagged c e.1.1) ht]
      show (if k' = p then some v else assoc p (l.filter fun e => tagged c e.1.1)) =
        (if k' = p then some v else assoc p l)
      rw [ih]
    · rw [List.filter_cons_of_neg (p := fun e : Port × Port => tagged c e.1.1) ht]
      have hne : ¬ k' = p := fun e => ht (by
        rw [e]
        exact hp)
      show _ = (if k' = p then some v else assoc p l)
      rw [ite_neg' hne]
      exact ih

theorem assoc_map_port (c : Nat) (p : Port) : ∀ l : List (Port × Port),
    assoc (tagPort c p) (l.map (tagL c)) = (assoc p l).map (tagPort c)
  | [] => rfl
  | (k, v) :: l => by
    show (if tagPort c k = tagPort c p then some (tagPort c v)
      else assoc (tagPort c p) (l.map (tagL c))) =
      (if k = p then some v else assoc p l).map (tagPort c)
    by_cases e : k = p
    · rw [ite_pos' e, ite_pos' (by rw [e])]
      rfl
    · rw [ite_neg' e, ite_neg' (fun h => e (tagPort_inj h))]
      exact assoc_map_port c p l

theorem nextSeg_port_filter (c : Nat) (q p : Port) (hq : tagged c q.1 = true) :
    ∀ l : List (Port × Port), nextSeg (l.filter fun e => tagged c e.1.1) q p = nextSeg l q p
  | [] => rfl
  | e :: l => by
    have ih := nextSeg_port_filter c q p hq l
    by_cases ht : tagged c e.1.1 = true
    · rw [List.filter_cons_of_pos (p := fun e : Port × Port => tagged c e.1.1) ht]
      show (if e.1 = q ∧ e.2 ≠ p then some e.2
        else nextSeg (l.filter fun e => tagged c e.1.1) q p) =
        (if e.1 = q ∧ e.2 ≠ p then some e.2 else nextSeg l q p)
      rw [ih]
    · rw [List.filter_cons_of_neg (p := fun e : Port × Port => tagged c e.1.1) ht]
      have hne : ¬ (e.1 = q ∧ e.2 ≠ p) := fun h => ht (by
        rw [h.1]
        exact hq)
      show _ = (if e.1 = q ∧ e.2 ≠ p then some e.2 else nextSeg l q p)
      rw [ite_neg' hne]
      exact ih

theorem nextSeg_map_port (c : Nat) (q p : Port) : ∀ l : List (Port × Port),
    nextSeg (l.map (tagL c)) (tagPort c q) (tagPort c p) = (nextSeg l q p).map (tagPort c)
  | [] => rfl
  | e :: l => by
    show (if tagPort c e.1 = tagPort c q ∧ tagPort c e.2 ≠ tagPort c p then some (tagPort c e.2)
      else nextSeg (l.map (tagL c)) (tagPort c q) (tagPort c p)) =
      (if e.1 = q ∧ e.2 ≠ p then some e.2 else nextSeg l q p).map (tagPort c)
    by_cases h : e.1 = q ∧ e.2 ≠ p
    · rw [ite_pos' h, ite_pos' ⟨by rw [h.1], fun h' => h.2 (tagPort_inj h')⟩]
      rfl
    · rw [ite_neg' h, ite_neg' (fun h' => h ⟨tagPort_inj h'.1, fun e2 => h'.2 (by rw [e2])⟩)]
      exact nextSeg_map_port c q p l

theorem filter_map_tag (c : Nat) (a : Id) : ∀ l : List (Id × Arith),
    (l.map (tagA c)).filter (fun e => decide (e.1 ≠ a ++ [c])) =
      (l.filter fun e => decide (e.1 ≠ a)).map (tagA c)
  | [] => rfl
  | e :: l => by
    have ih := filter_map_tag c a l
    by_cases he : e.1 = a
    · have h1 : ¬ decide ((tagA c e).1 ≠ a ++ [c]) = true := by
        show ¬ decide (e.1 ++ [c] ≠ a ++ [c]) = true
        rw [he]
        simp
      have h2 : ¬ decide (e.1 ≠ a) = true := by
        rw [he]
        simp
      show ((tagA c e) :: l.map (tagA c)).filter _ = _
      rw [List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a ++ [c])) h1,
        List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a)) h2]
      exact ih
    · have h1 : decide ((tagA c e).1 ≠ a ++ [c]) = true :=
        decide_eq_true fun e' => he (List.append_cancel_right e')
      have h2 : decide (e.1 ≠ a) = true := decide_eq_true he
      show ((tagA c e) :: l.map (tagA c)).filter _ = _
      rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a ++ [c])) h1,
        List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a)) h2, ih]
      rfl

theorem filter_other (d c : Nat) (hd : c ≠ d) (a : Id) (l : List (Id × Arith)) :
    ((l.filter fun e => decide (e.1 ≠ a ++ [c])).filter fun e => tagged d e.1) =
      l.filter fun e => tagged d e.1 := by
  rw [filter_swap]
  exact List.filter_eq_self.2 fun e he => by
    have ht : tagged d e.1 = true := (List.mem_filter.1 he).2
    exact decide_eq_true fun e' => by
      rw [e', tagged_other hd] at ht
      cases ht

/-- **A net seen inside a larger memory.**  `Looks c X Y`: the cells of the
memory `Y` whose names carry the tag `c` are those of `X`, in the same
order, with the tag put at the end of every name.  Whatever else `Y`
holds, a thread that looks up a name with the tag finds in `Y` what it
finds in `X`. -/
structure Looks (c : Nat) (X Y : XNet Arith) : Prop where
  agents : Y.agents.filter (fun e => tagged c e.1) = X.agents.map (tagA c)
  wires : Y.wires.filter (fun e => tagged c e.1.1) = X.wires.map (tagL c)

theorem Looks.agent {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (i : Id) :
    assoc (i ++ [c]) Y.agents = assoc i X.agents := by
  rw [← assoc_tagged_filter c (i ++ [c]) (tagged_self c i) Y.agents, h.agents, assoc_map_tag]

theorem Looks.wire {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (p : Port) :
    assoc (tagPort c p) Y.wires = (assoc p X.wires).map (tagPort c) := by
  rw [← assoc_port_filter c (tagPort c p) (tagged_self c p.1) Y.wires, h.wires, assoc_map_port]

theorem Looks.next {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (q p : Port) :
    nextSeg Y.wires (tagPort c q) (tagPort c p) = (nextSeg X.wires q p).map (tagPort c) := by
  rw [← nextSeg_port_filter c (tagPort c q) (tagPort c p) (tagged_self c q.1) Y.wires, h.wires,
    nextSeg_map_port]

theorem Looks.here {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (q : Port) :
    (if (tagPort c q).2 = 0 then assoc (tagPort c q).1 Y.agents else none) =
      (if q.2 = 0 then assoc q.1 X.agents else none) := by
  show (if q.2 = 0 then assoc (q.1 ++ [c]) Y.agents else none) = _
  rw [h.agent]

theorem Looks.take {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (a : Id) :
    Looks c (X.takeAgent a) (Y.takeAgent (a ++ [c])) :=
  ⟨by
    show ((Y.agents.filter fun e => decide (e.1 ≠ a ++ [c])).filter fun e => tagged c e.1) =
      (X.agents.filter fun e => decide (e.1 ≠ a)).map (tagA c)
    rw [filter_swap, h.agents, filter_map_tag], h.wires⟩

theorem Looks.take_other {d c : Nat} {X Y : XNet Arith} (h : Looks d X Y) (hd : c ≠ d)
    (a : Id) : Looks d X (Y.takeAgent (a ++ [c])) :=
  ⟨by
    show ((Y.agents.filter fun e => decide (e.1 ≠ a ++ [c])).filter fun e => tagged d e.1) = _
    rw [filter_other d c hd]
    exact h.agents, h.wires⟩

theorem Looks.put {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (i : Id) (γ : Arith) :
    Looks c (X.putAgent i γ) (Y.putAgent (i ++ [c]) γ) :=
  ⟨by
    show ((i ++ [c], γ) :: Y.agents).filter (fun e => tagged c e.1) =
      ((i, γ) :: X.agents).map (tagA c)
    rw [List.filter_cons_of_pos (p := fun e : Id × Arith => tagged c e.1) (tagged_self c i),
      h.agents]
    rfl, h.wires⟩

theorem Looks.put_other {d c : Nat} {X Y : XNet Arith} (h : Looks d X Y) (hd : c ≠ d)
    (i : Id) (γ : Arith) : Looks d X (Y.putAgent (i ++ [c]) γ) :=
  ⟨by
    show ((i ++ [c], γ) :: Y.agents).filter (fun e => tagged d e.1) = _
    rw [List.filter_cons_of_neg (p := fun e : Id × Arith => tagged d e.1) (by
      show ¬ tagged d (i ++ [c]) = true
      rw [tagged_other hd]
      exact Bool.false_ne_true)]
    exact h.agents, h.wires⟩

theorem Looks.link {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (p q : Port) :
    Looks c (X.putLink p q) (Y.putLink (tagPort c p) (tagPort c q)) :=
  ⟨h.agents, by
    show ((tagPort c p, tagPort c q) :: Y.wires).filter (fun e => tagged c e.1.1) =
      ((p, q) :: X.wires).map (tagL c)
    rw [List.filter_cons_of_pos (p := fun e : Port × Port => tagged c e.1.1)
      (tagged_self c p.1), h.wires]
    rfl⟩

theorem Looks.link_other {d c : Nat} {X Y : XNet Arith} (h : Looks d X Y) (hd : c ≠ d)
    (p q : Port) : Looks d X (Y.putLink (tagPort c p) (tagPort c q)) :=
  ⟨h.agents, by
    show ((tagPort c p, tagPort c q) :: Y.wires).filter (fun e => tagged d e.1.1) = _
    rw [List.filter_cons_of_neg (p := fun e : Port × Port => tagged d e.1.1) (by
      show ¬ tagged d (p.1 ++ [c]) = true
      rw [tagged_other hd]
      exact Bool.false_ne_true)]
    exact h.wires⟩

theorem Looks.puts {c : Nat} : ∀ (as : List (Id × Arith)) {X Y : XNet Arith}, Looks c X Y →
    Looks c (X.putAgents as) (Y.putAgents (as.map (tagA c)))
  | [], _, _, h => h
  | e :: as, _, _, h => Looks.puts as (h.put e.1 e.2)

theorem Looks.puts_other {d c : Nat} (hd : c ≠ d) : ∀ (as : List (Id × Arith))
    {X Y : XNet Arith}, Looks d X Y → Looks d X (Y.putAgents (as.map (tagA c)))
  | [], _, _, h => h
  | e :: as, _, _, h => Looks.puts_other hd as (h.put_other hd e.1 e.2)

theorem Looks.links {c : Nat} : ∀ (ls : List (Port × Port)) {X Y : XNet Arith}, Looks c X Y →
    Looks c (X.putLinks ls) (Y.putLinks (ls.map (tagL c)))
  | [], _, _, h => h
  | e :: ls, _, _, h => Looks.links ls (h.link e.1 e.2)

theorem Looks.links_other {d c : Nat} (hd : c ≠ d) : ∀ (ls : List (Port × Port))
    {X Y : XNet Arith}, Looks d X Y → Looks d X (Y.putLinks (ls.map (tagL c)))
  | [], _, _, h => h
  | e :: ls, _, _, h => Looks.links_other hd ls (h.link_other hd e.1 e.2)

/-- The memory after a pair has fired: the two agents taken, the new
agents and the new segments written. -/
def fire (X : XNet Arith) (a b : Id) (as : List (Id × Arith)) (ls : List (Port × Port)) :
    XNet Arith :=
  (((X.takeAgent a).takeAgent b).putAgents as).putLinks ls

/-- **A pair fires in the larger memory as it does in the net alone.** -/
theorem Looks.fired {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (a b : Id)
    (as : List (Id × Arith)) (ls : List (Port × Port)) :
    Looks c (fire X a b as ls)
      (fire Y (a ++ [c]) (b ++ [c]) (as.map (tagA c)) (ls.map (tagL c))) :=
  Looks.links ls (Looks.puts as ((h.take a).take b))

/-- And it leaves what carries another tag as it is. -/
theorem Looks.fired_other {d c : Nat} {X Y : XNet Arith} (h : Looks d X Y) (hd : c ≠ d)
    (a b : Id) (as : List (Id × Arith)) (ls : List (Port × Port)) :
    Looks d X (fire Y (a ++ [c]) (b ++ [c]) (as.map (tagA c)) (ls.map (tagL c))) :=
  Looks.links_other hd ls (Looks.puts_other hd as ((h.take_other hd a).take_other hd b))

theorem newAgents_swap_tag (c : Nat) {a s : Id} (h : a ≠ s) :
    addSucc.swap.toX.newAgents (s ++ [c]) (a ++ [c]) =
      (addSucc.swap.toX.newAgents s a).map (tagA c) := by
  rw [newAgents_swap h,
    newAgents_swap (a := a ++ [c]) (s := s ++ [c]) (fun e => h (List.append_cancel_right e))]
  rfl

theorem newLinks_swap_tag (c : Nat) (s a : Id) :
    addSucc.swap.toX.newLinks ar (s ++ [c]) (a ++ [c]) .succ .add =
      (addSucc.swap.toX.newLinks ar s a .succ .add).map (tagL c) := by
  rw [newLinks_swap, newLinks_swap]
  rfl

theorem newAgents_add_tag (c : Nat) {a s : Id} (h : a ≠ s) :
    addSucc.toX.newAgents (a ++ [c]) (s ++ [c]) = (addSucc.toX.newAgents a s).map (tagA c) := by
  rw [newAgents_add h,
    newAgents_add (a := a ++ [c]) (s := s ++ [c]) (fun e => h (List.append_cancel_right e))]
  rfl

theorem newLinks_add_tag (c : Nat) (a s : Id) :
    addSucc.toX.newLinks ar (a ++ [c]) (s ++ [c]) .add .succ =
      (addSucc.toX.newLinks ar a s .add .succ).map (tagL c) := by
  rw [newLinks_add, newLinks_add]
  rfl

theorem newLinks_zero_tag (c : Nat) (a z : Id) :
    addZero.toX.newLinks ar (a ++ [c]) (z ++ [c]) .add .zero =
      (addZero.toX.newLinks ar a z .add .zero).map (tagL c) := by
  rw [newLinks_zero, newLinks_zero]
  rfl

theorem stepS_tag (c : Nat) (Y : XNet Arith) {s a : Id} (h : a ≠ s) :
    stepS Y (s ++ [c]) (a ++ [c]) = fire Y (s ++ [c]) (a ++ [c])
      ((addSucc.swap.toX.newAgents s a).map (tagA c))
      ((addSucc.swap.toX.newLinks ar s a .succ .add).map (tagL c)) := by
  unfold stepS fire
  rw [newAgents_swap_tag c h,
    show addSucc.swap.toX.newLinks xsys.sys.ar (s ++ [c]) (a ++ [c]) .succ .add =
      (addSucc.swap.toX.newLinks ar s a .succ .add).map (tagL c) from newLinks_swap_tag c s a]

theorem stepA_tag (c : Nat) (Y : XNet Arith) {a s : Id} (h : a ≠ s) :
    stepA Y (a ++ [c]) (s ++ [c]) = fire Y (a ++ [c]) (s ++ [c])
      ((addSucc.toX.newAgents a s).map (tagA c))
      ((addSucc.toX.newLinks ar a s .add .succ).map (tagL c)) := by
  unfold stepA fire
  rw [newAgents_add_tag c h,
    show addSucc.toX.newLinks xsys.sys.ar (a ++ [c]) (s ++ [c]) .add .succ =
      (addSucc.toX.newLinks ar a s .add .succ).map (tagL c) from newLinks_add_tag c a s]

theorem stepZ_tag (c : Nat) (Y : XNet Arith) (a z : Id) :
    stepZ Y (a ++ [c]) (z ++ [c]) = fire Y (a ++ [c]) (z ++ [c])
      ((addZero.toX.newAgents a z).map (tagA c))
      ((addZero.toX.newLinks ar a z .add .zero).map (tagL c)) := by
  unfold stepZ fire
  rw [show addZero.toX.newLinks xsys.sys.ar (a ++ [c]) (z ++ [c]) .add .zero =
      (addZero.toX.newLinks ar a z .add .zero).map (tagL c) from newLinks_zero_tag c a z]
  rfl

/-- **The first round in a larger memory**: sixteen actions, as in the net
alone, whatever else is in the list of the thread. -/
theorem Looks.round_first {c n hi : Nat} {X Y : XNet Arith} (h : Looks c X Y)
    (st : Start n X hi) (rest : List (Id × Arith)) :
    Works xsys Y ⟨([hi + 1] ++ [c], .succ) :: rest, .idle⟩
      (stepS Y ([hi + 1] ++ [c]) ([1] ++ [c]))
      ⟨(stepS Y ([hi + 1] ++ [c]) ([1] ++ [c])).agents, .idle⟩ 1 16 := by
  obtain ⟨-, -, h₁, h₂, hne, h₄⟩ := st.pair
  have g₁ : assoc ([hi + 1] ++ [c]) Y.agents = some Arith.succ := (h.agent _).trans h₁
  have g₂ : assoc (([hi + 1] ++ [c], 0) : Port) Y.wires = some ([1] ++ [c], 0) :=
    (h.wire ([hi + 1], 0)).trans (congrArg (Option.map (tagPort c)) h₂)
  have g₃ : assoc ([1] ++ [c]) Y.agents = some Arith.add := (h.agent _).trans st.adder
  have gne : ([hi + 1] ++ [c] : Id) ≠ [1] ++ [c] := fun e => hne (List.append_cancel_right e)
  have g₄ : assoc ([1] ++ [c]) (Y.takeAgent ([hi + 1] ++ [c])).agents = some Arith.add :=
    ((h.take [hi + 1]).agent _).trans h₄
  have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
  have w := Works.claim_direct (xs := xsys) rest g₁ g₂ g₃ gne g₄ hR
  have eA := newAgents_swap (a := [1] ++ [c]) (s := [hi + 1] ++ [c]) (fun e => gne e.symm)
  have eK : 5 + ((addSucc.swap.toX.newAgents ([hi + 1] ++ [c]) ([1] ++ [c])).length +
      (addSucc.swap.toX.newLinks xsys.sys.ar ([hi + 1] ++ [c]) ([1] ++ [c]) .succ .add).length +
        1) = 16 := by
    rw [eA]
    rfl
  rw [eK] at w
  exact w

/-- **A later round in a larger memory**: seventeen actions. -/
theorem Looks.round_later {c n hh : Nat} {X Y : XNet Arith} (h : Looks c X Y)
    (st : Steady n X (hh + 1)) (hn : n + 4 ≤ hh + 1) (rest : List (Id × Arith)) :
    Works xsys Y ⟨([0, hh + 1 + 1] ++ [c], .add) :: rest, .idle⟩
      (stepA Y ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c]))
      ⟨(stepA Y ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c])).agents, .idle⟩ 1 17 := by
  obtain ⟨-, -, k₁, k₂, k₂', k₃, hne, k₄⟩ := st.round_pair hn
  have g₁ : assoc ([0, hh + 1 + 1] ++ [c]) Y.agents = some Arith.add := (h.agent _).trans k₁
  have g₂ : assoc (([0, hh + 1 + 1] ++ [c], 0) : Port) Y.wires =
      some ([hh + 1 + 1] ++ [c], 1) :=
    (h.wire ([0, hh + 1 + 1], 0)).trans (congrArg (Option.map (tagPort c)) k₂)
  have gc : (if (([hh + 1 + 1] ++ [c], 1) : Port).2 = 0
      then assoc (([hh + 1 + 1] ++ [c], 1) : Port).1 Y.agents else none) = none := rfl
  have g₂' : nextSeg Y.wires ([hh + 1 + 1] ++ [c], 1) ([0, hh + 1 + 1] ++ [c], 0) =
      some ([hh + 1] ++ [c], 0) :=
    (h.next ([hh + 1 + 1], 1) ([0, hh + 1 + 1], 0)).trans
      (congrArg (Option.map (tagPort c)) k₂')
  have g₃ : assoc ([hh + 1] ++ [c]) Y.agents = some Arith.succ := (h.agent _).trans k₃
  have gne : ([0, hh + 1 + 1] ++ [c] : Id) ≠ [hh + 1] ++ [c] :=
    fun e => hne (List.append_cancel_right e)
  have g₄ : assoc ([hh + 1] ++ [c]) (Y.takeAgent ([0, hh + 1 + 1] ++ [c])).agents =
      some Arith.succ := ((h.take [0, hh + 1 + 1]).agent _).trans k₄
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w := Works.claim_via (xs := xsys) rest g₁ g₂ gc g₂' g₃ gne g₄ hR
  have eA := newAgents_add (a := [0, hh + 1 + 1] ++ [c]) (s := [hh + 1] ++ [c]) gne
  have eK : 6 + ((addSucc.toX.newAgents ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c])).length +
      (addSucc.toX.newLinks xsys.sys.ar ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c])
        .add .succ).length + 1) = 17 := by
    rw [eA]
    rfl
  rw [eK] at w
  exact w

/-- **The last round in a larger memory**: nine actions. -/
theorem Looks.round_zero {c n : Nat} {X Y : XNet Arith} (h : Looks c X Y)
    (st : Steady n X (n + 3)) (hz : assoc [2] X.agents = some .zero)
    (rest : List (Id × Arith)) :
    Works xsys Y ⟨([0, n + 3 + 1] ++ [c], .add) :: rest, .idle⟩
      (stepZ Y ([0, n + 3 + 1] ++ [c]) ([2] ++ [c]))
      ⟨(stepZ Y ([0, n + 3 + 1] ++ [c]) ([2] ++ [c])).agents, .idle⟩ 1 9 := by
  obtain ⟨-, -, k₁, k₂, k₂', hne, k₄⟩ := st.zero_pair hz
  have g₁ : assoc ([0, n + 3 + 1] ++ [c]) Y.agents = some Arith.add := (h.agent _).trans k₁
  have g₂ : assoc (([0, n + 3 + 1] ++ [c], 0) : Port) Y.wires = some ([n + 3 + 1] ++ [c], 1) :=
    (h.wire ([0, n + 3 + 1], 0)).trans (congrArg (Option.map (tagPort c)) k₂)
  have gc : (if (([n + 3 + 1] ++ [c], 1) : Port).2 = 0
      then assoc (([n + 3 + 1] ++ [c], 1) : Port).1 Y.agents else none) = none := rfl
  have g₂' : nextSeg Y.wires ([n + 3 + 1] ++ [c], 1) ([0, n + 3 + 1] ++ [c], 0) =
      some ([2] ++ [c], 0) :=
    (h.next ([n + 3 + 1], 1) ([0, n + 3 + 1], 0)).trans (congrArg (Option.map (tagPort c)) k₂')
  have g₃ : assoc ([2] ++ [c]) Y.agents = some Arith.zero := (h.agent _).trans hz
  have gne : ([0, n + 3 + 1] ++ [c] : Id) ≠ [2] ++ [c] :=
    fun e => hne (List.append_cancel_right e)
  have g₄ : assoc ([2] ++ [c]) (Y.takeAgent ([0, n + 3 + 1] ++ [c])).agents =
      some Arith.zero := ((h.take [0, n + 3 + 1]).agent _).trans k₄
  have hR : xsys.rule .add .zero = some addZero.toX := rfl
  exact Works.claim_via (xs := xsys) rest g₁ g₂ gc g₂' g₃ gne g₄ hR

/-- The states of a thread that is looking for a pair and holds nothing. -/
def Scans : TState Arith → Prop
  | .idle => True
  | .look _ _ => True
  | .seek _ _ _ _ => True
  | .ready _ _ _ _ => True
  | _ => False

/-- A state with every name tagged. -/
def tagSt (c : Nat) : TState Arith → TState Arith
  | .idle => .idle
  | .look a α => .look (a ++ [c]) α
  | .seek a α p q => .seek (a ++ [c]) α (tagPort c p) (tagPort c q)
  | .ready a b α β => .ready (a ++ [c]) (b ++ [c]) α β
  | .half a b α β => .half (a ++ [c]) (b ++ [c]) α β
  | .write as ls => .write (as.map (tagA c)) (ls.map (tagL c))

theorem takeAgent_ne {X : XNet Arith} {a : Id} {α : Arith} (h : assoc a X.agents = some α) :
    X.takeAgent a ≠ X := fun e => by
  have hm : (a, α) ∈ X.agents := assoc_mem h
  have h2 : (X.takeAgent a).agents = X.agents := congrArg XNet.agents e
  rw [← h2] at hm
  exact (XNet.mem_takeAgent.1 hm).2 rfl

theorem stays_rest_zero {X : XNet Arith} {T' : XThread Arith} {k : Nat}
    (s : Stays xsys X ⟨[], .idle⟩ T' k) : k = 0 := by
  cases s with
  | refl => rfl
  | step hT _ _ => exact absurd rfl hT

theorem act_same {X X'' : XNet Arith} {T T₁ T₂ : XThread Arith} {c'' : Nat}
    (hact : XMach.act xsys X T = (X, T₁, 0)) (s : XMach.act xsys X T = (X'', T₂, c'')) :
    T₁ = T₂ ∧ X'' = X := by
  have e := s.symm.trans hact
  exact ⟨(Prod.mk.inj (Prod.mk.inj e).2).1.symm, (Prod.mk.inj e).1⟩

theorem look_ne_rest (l : List (Id × Arith)) (a : Id) (α : Arith) :
    (⟨l, .look a α⟩ : XThread Arith) ≠ ⟨[], .idle⟩ := fun e => by
  injection e with _ e2
  cases e2

theorem seek_ne_rest (l : List (Id × Arith)) (a : Id) (α : Arith) (p q : Port) :
    (⟨l, .seek a α p q⟩ : XThread Arith) ≠ ⟨[], .idle⟩ := fun e => by
  injection e with _ e2
  cases e2

theorem ready_ne_rest (l : List (Id × Arith)) (a b : Id) (α β : Arith) :
    (⟨l, .ready a b α β⟩ : XThread Arith) ≠ ⟨[], .idle⟩ := fun e => by
  injection e with _ e2
  cases e2

/-- **A thread that only reads on a net inside a larger memory acts as it
does on that net alone.**  If the thread, alone on `X`, passes the entries
of its list and comes to rest without writing, then in the memory `Y` it
passes the first entries `l1`, tagged, in as many actions as on `X`,
whatever comes after them in its list, and what is left of the pass on `X`
is the pass of the other entries `l2`. -/
theorem Looks.pass {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) {T T' : XThread Arith}
    {k : Nat} (st : Stays xsys X T T' k) : T' = ⟨[], .idle⟩ → Scans T.st →
      ∀ (l1 l2 r : List (Id × Arith)), T.todo = l1 ++ l2 →
        ∃ k1 k2, k1 + k2 = k ∧
          Stays xsys Y ⟨l1.map (tagA c) ++ r, tagSt c T.st⟩ ⟨r, .idle⟩ k1 ∧
          Stays xsys X ⟨l2, .idle⟩ ⟨[], .idle⟩ k2 := by
  induction st with
  | refl T =>
    intro hT _ l1 l2 r hl
    subst hT
    obtain ⟨e1, e2⟩ := List.append_eq_nil_iff.1 hl.symm
    subst e1
    subst e2
    exact ⟨0, 0, rfl, .refl _, .refl _⟩
  | @step T T₁ T' k hT hact st' ih =>
    intro hT' hS l1 l2 r hl
    subst hT'
    obtain ⟨todo, s⟩ := T
    cases s with
    | idle =>
      cases l1 with
      | nil =>
        have e : todo = l2 := hl
        subst e
        exact ⟨0, k + 1, by omega, .refl _, .step hT hact st'⟩
      | cons e l1' =>
        have e' : todo = e :: (l1' ++ l2) := hl
        subst e'
        by_cases ha : assoc e.1 X.agents = some e.2
        · have eT := (act_same hact
            (XMach.act_idle_pos (xs := xsys) (X := X) (rest := l1' ++ l2) ha)).1
          subst eT
          obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1' l2 r rfl
          have aY : XMach.act xsys Y ⟨tagA c e :: (l1'.map (tagA c) ++ r), .idle⟩ =
              (Y, ⟨l1'.map (tagA c) ++ r, .look (e.1 ++ [c]) e.2⟩, 0) :=
            XMach.act_idle_pos (xs := xsys) (X := Y) (e := tagA c e) ((h.agent e.1).trans ha)
          exact ⟨k1 + 1, k2, by omega,
            .step (fun e' => List.cons_ne_nil _ _ (congrArg XThread.todo e')) aY sY, sX⟩
        · have eT := (act_same hact
            (XMach.act_idle_neg (xs := xsys) (X := X) (rest := l1' ++ l2) ha)).1
          subst eT
          obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1' l2 r rfl
          have aY : XMach.act xsys Y ⟨tagA c e :: (l1'.map (tagA c) ++ r), .idle⟩ =
              (Y, ⟨l1'.map (tagA c) ++ r, .idle⟩, 0) :=
            XMach.act_idle_neg (xs := xsys) (X := Y) (e := tagA c e)
              (fun hh => ha ((h.agent e.1).symm.trans hh))
          exact ⟨k1 + 1, k2, by omega,
            .step (fun e' => List.cons_ne_nil _ _ (congrArg XThread.todo e')) aY sY, sX⟩
    | look a α =>
      cases hq : assoc ((a, 0) : Port) X.wires with
      | none =>
        have eT := (act_same hact
          (XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq)).1
        subst eT
        obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1 l2 r hl
        have aY : XMach.act xsys Y ⟨l1.map (tagA c) ++ r, .look (a ++ [c]) α⟩ =
            (Y, ⟨l1.map (tagA c) ++ r, .idle⟩, 0) :=
          XMach.act_look_none (xs := xsys)
            ((h.wire (a, 0)).trans (congrArg (Option.map (tagPort c)) hq))
        exact ⟨k1 + 1, k2, by omega, .step (look_ne_rest _ _ _) aY sY, sX⟩
      | some q =>
        have eT := (act_same hact (XMach.act_look (xs := xsys) (todo := todo) (α := α) hq)).1
        subst eT
        obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1 l2 r hl
        have aY : XMach.act xsys Y ⟨l1.map (tagA c) ++ r, .look (a ++ [c]) α⟩ =
            (Y, ⟨l1.map (tagA c) ++ r, .seek (a ++ [c]) α (a ++ [c], 0) (tagPort c q)⟩, 0) :=
          XMach.act_look (xs := xsys)
            ((h.wire (a, 0)).trans (congrArg (Option.map (tagPort c)) hq))
        exact ⟨k1 + 1, k2, by omega, .step (look_ne_rest _ _ _) aY sY, sX⟩
    | seek a α p q =>
      cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
      | none =>
        cases hn : nextSeg X.wires q p with
        | none =>
          have eT := (act_same hact
            (XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn)).1
          subst eT
          obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1 l2 r hl
          have aY : XMach.act xsys Y
              ⟨l1.map (tagA c) ++ r, .seek (a ++ [c]) α (tagPort c p) (tagPort c q)⟩ =
              (Y, ⟨l1.map (tagA c) ++ r, .idle⟩, 0) :=
            XMach.act_seek_stop (xs := xsys) ((h.here q).trans hc)
              ((h.next q p).trans (congrArg (Option.map (tagPort c)) hn))
          exact ⟨k1 + 1, k2, by omega, .step (seek_ne_rest _ _ _ _ _) aY sY, sX⟩
        | some q' =>
          have eT := (act_same hact
            (XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn)).1
          subst eT
          obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1 l2 r hl
          have aY : XMach.act xsys Y
              ⟨l1.map (tagA c) ++ r, .seek (a ++ [c]) α (tagPort c p) (tagPort c q)⟩ =
              (Y, ⟨l1.map (tagA c) ++ r,
                .seek (a ++ [c]) α (tagPort c q) (tagPort c q')⟩, 0) :=
            XMach.act_seek_next (xs := xsys) ((h.here q).trans hc)
              ((h.next q p).trans (congrArg (Option.map (tagPort c)) hn))
          exact ⟨k1 + 1, k2, by omega, .step (seek_ne_rest _ _ _ _ _) aY sY, sX⟩
      | some β =>
        by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
        · have eT := (act_same hact
            (XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr)).1
          subst eT
          obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1 l2 r hl
          have aY : XMach.act xsys Y
              ⟨l1.map (tagA c) ++ r, .seek (a ++ [c]) α (tagPort c p) (tagPort c q)⟩ =
              (Y, ⟨l1.map (tagA c) ++ r, .ready (a ++ [c]) (q.1 ++ [c]) α β⟩, 0) :=
            XMach.act_seek_found (xs := xsys) (c := tagPort c q) ((h.here q).trans hc)
              ⟨fun e => hr.1 (List.append_cancel_right e), hr.2⟩
          exact ⟨k1 + 1, k2, by omega, .step (seek_ne_rest _ _ _ _ _) aY sY, sX⟩
        · have eT := (act_same hact
            (XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr)).1
          subst eT
          obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1 l2 r hl
          have aY : XMach.act xsys Y
              ⟨l1.map (tagA c) ++ r, .seek (a ++ [c]) α (tagPort c p) (tagPort c q)⟩ =
              (Y, ⟨l1.map (tagA c) ++ r, .idle⟩, 0) :=
            XMach.act_seek_norule (xs := xsys) (c := tagPort c q) (β := β)
              ((h.here q).trans hc)
              (fun hh => hr ⟨fun e => hh.1 (congrArg (· ++ [c]) e), hh.2⟩)
          exact ⟨k1 + 1, k2, by omega, .step (seek_ne_rest _ _ _ _ _) aY sY, sX⟩
    | ready a b α β =>
      by_cases ha : assoc a X.agents = some α
      · exact absurd (act_same hact
          (XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha)).2
          (takeAgent_ne ha)
      · have eT := (act_same hact
          (XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha)).1
        subst eT
        obtain ⟨k1, k2, hk, sY, sX⟩ := ih rfl trivial l1 l2 r hl
        have aY : XMach.act xsys Y
            ⟨l1.map (tagA c) ++ r, .ready (a ++ [c]) (b ++ [c]) α β⟩ =
            (Y, ⟨l1.map (tagA c) ++ r, .idle⟩, 0) :=
          XMach.act_ready_neg (xs := xsys) (fun hh => ha ((h.agent a).symm.trans hh))
        exact ⟨k1 + 1, k2, by omega, .step (ready_ne_rest _ _ _ _ _) aY sY, sX⟩
    | half a b α β => exact False.elim hS
    | write as ls => exact False.elim hS

/-- **The last pass over two nets in one memory.**  When the memory holds
only cells tagged `0` or `1`, those tagged `0` being the net `XA` and those
tagged `1` the net `XB`, a thread that passes every entry takes the
actions of the pass over `XA` and those of the pass over `XB`, in whatever
order the entries come. -/
theorem pass_two {XA XB Y : XNet Arith} (hA : Looks 0 XA Y) (hB : Looks 1 XB Y) :
    ∀ (l la lb : List (Id × Arith)) (ka kb : Nat),
      (∀ e, e ∈ l → tagged 0 e.1 = true ∨ tagged 1 e.1 = true) →
      l.filter (fun e => tagged 0 e.1) = la.map (tagA 0) →
      l.filter (fun e => tagged 1 e.1) = lb.map (tagA 1) →
      Stays xsys XA ⟨la, .idle⟩ ⟨[], .idle⟩ ka → Stays xsys XB ⟨lb, .idle⟩ ⟨[], .idle⟩ kb →
      Stays xsys Y ⟨l, .idle⟩ ⟨[], .idle⟩ (ka + kb)
  | [], la, lb, ka, kb, _, fa, fb, sa, sb => by
    have ea : la = [] := List.map_eq_nil_iff.1 fa.symm
    have eb : lb = [] := List.map_eq_nil_iff.1 fb.symm
    subst ea
    subst eb
    rw [stays_rest_zero sa, stays_rest_zero sb]
    exact .refl _
  | e :: l, la, lb, ka, kb, ht, fa, fb, sa, sb => by
    rcases ht e List.mem_cons_self with t0 | t1
    · rw [List.filter_cons_of_pos (p := fun e : Id × Arith => tagged 0 e.1) t0] at fa
      cases la with
      | nil =>
        have fa2 : e :: l.filter (fun e => tagged 0 e.1) = [] := fa
        cases fa2
      | cons e₀ la' =>
        have fa2 : e :: l.filter (fun e => tagged 0 e.1) = tagA 0 e₀ :: la'.map (tagA 0) := fa
        have e1 : e = tagA 0 e₀ := (List.cons.inj fa2).1
        have fa' : l.filter (fun e => tagged 0 e.1) = la'.map (tagA 0) := (List.cons.inj fa2).2
        subst e1
        have t1 : ¬ tagged 1 (tagA 0 e₀).1 = true := by
          show ¬ tagged 1 (e₀.1 ++ [0]) = true
          rw [tagged_other (by decide)]
          exact Bool.false_ne_true
        rw [List.filter_cons_of_neg (p := fun e : Id × Arith => tagged 1 e.1) t1] at fb
        obtain ⟨k1, k2, hk, sY, sX⟩ := hA.pass sa rfl trivial [e₀] la' l rfl
        have ih := pass_two hA hB l la' lb k2 kb
          (fun x hx => ht x (List.mem_cons_of_mem _ hx)) fa' fb sX sb
        have s := sY.trans ih
        rw [← hk, Nat.add_assoc]
        exact s
    · rw [List.filter_cons_of_pos (p := fun e : Id × Arith => tagged 1 e.1) t1] at fb
      cases lb with
      | nil =>
        have fb2 : e :: l.filter (fun e => tagged 1 e.1) = [] := fb
        cases fb2
      | cons e₀ lb' =>
        have fb2 : e :: l.filter (fun e => tagged 1 e.1) = tagA 1 e₀ :: lb'.map (tagA 1) := fb
        have e1 : e = tagA 1 e₀ := (List.cons.inj fb2).1
        have fb' : l.filter (fun e => tagged 1 e.1) = lb'.map (tagA 1) := (List.cons.inj fb2).2
        subst e1
        have t0 : ¬ tagged 0 (tagA 1 e₀).1 = true := by
          show ¬ tagged 0 (e₀.1 ++ [1]) = true
          rw [tagged_other (by decide)]
          exact Bool.false_ne_true
        rw [List.filter_cons_of_neg (p := fun e : Id × Arith => tagged 0 e.1) t0] at fa
        obtain ⟨k1, k2, hk, sY, sX⟩ := hB.pass sb rfl trivial [e₀] lb' l rfl
        have ih := pass_two hA hB l la lb' ka k2
          (fun x hx => ht x (List.mem_cons_of_mem _ hx)) fa fb' sa sX
        have s := sY.trans ih
        rw [← hk, Nat.add_left_comm]
        exact s

theorem putAgents_agents' : ∀ (as : List (Id × Arith)) (X : XNet Arith),
    (X.putAgents as).agents = as.reverse ++ X.agents
  | [], _ => rfl
  | e :: as, X => by
    show ((X.putAgent e.1 e.2).putAgents as).agents = _
    rw [putAgents_agents' as, List.reverse_cons, List.append_assoc]
    rfl

theorem fire_agents (Y : XNet Arith) (x y : Id) (as : List (Id × Arith))
    (ls : List (Port × Port)) :
    (fire Y x y as ls).agents = as.reverse ++
      ((Y.agents.filter fun e => decide (e.1 ≠ x)).filter fun e => decide (e.1 ≠ y)) := by
  unfold fire
  rw [XNet.putLinks_agents, putAgents_agents']
  rfl

theorem mem_tag_self {c : Nat} {l : List (Id × Arith)} {e : Id × Arith}
    (he : e ∈ l.map (tagA c)) : tagged c e.1 = true := by
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact tagged_self c e₀.1

theorem mem_tag_other {c d : Nat} (hd : d ≠ c) {l : List (Id × Arith)} {e : Id × Arith}
    (he : e ∈ l.map (tagA d)) : tagged c e.1 = false := by
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact tagged_other hd e₀.1

/-- `Moves c Y Y'`: the memory `Y'` comes from `Y` by rounds on names
tagged `c` only.  What carries another tag looks as before, a part of the
list of agents without the tag that came last still comes last, and every
name is one that was there or carries the tag. -/
structure Moves (c : Nat) (Y Y' : XNet Arith) : Prop where
  other : ∀ (d : Nat) (Z : XNet Arith), c ≠ d → Looks d Z Y → Looks d Z Y'
  keep : ∀ (N Fr : List (Id × Arith)), Y.agents = N ++ Fr →
    (∀ e, e ∈ N → tagged c e.1 = true) → (∀ e, e ∈ Fr → tagged c e.1 = false) →
    ∃ N', Y'.agents = N' ++ Fr ∧ ∀ e, e ∈ N' → tagged c e.1 = true
  tags : ∀ P : Id → Prop, (∀ i, P (i ++ [c])) → (∀ e, e ∈ Y.agents → P e.1) →
    ∀ e, e ∈ Y'.agents → P e.1

theorem Moves.refl (c : Nat) (Y : XNet Arith) : Moves c Y Y :=
  ⟨fun _ _ _ h => h, fun N _ hY hN _ => ⟨N, hY, hN⟩, fun _ _ h => h⟩

theorem Moves.trans {c : Nat} {Y Y' Y'' : XNet Arith} (a : Moves c Y Y') (b : Moves c Y' Y'') :
    Moves c Y Y'' :=
  ⟨fun d Z hd h => b.other d Z hd (a.other d Z hd h),
    fun N Fr hY hN hFr => by
      obtain ⟨N', hY', hN'⟩ := a.keep N Fr hY hN hFr
      exact b.keep N' Fr hY' hN' hFr,
    fun P hP h => b.tags P hP (a.tags P hP h)⟩

theorem Moves.fired (c : Nat) (Y : XNet Arith) (a b : Id) (as : List (Id × Arith))
    (ls : List (Port × Port)) :
    Moves c Y (fire Y (a ++ [c]) (b ++ [c]) (as.map (tagA c)) (ls.map (tagL c))) := by
  refine ⟨fun d Z hd h => h.fired_other hd a b as ls, fun N Fr hY hN hFr => ?_,
    fun P hP h e he => ?_⟩
  · have hf : ∀ x : Id, (Fr.filter fun e => decide (e.1 ≠ x ++ [c])) = Fr := fun x =>
      List.filter_eq_self.2 fun e he => decide_eq_true fun e' => by
        have ht := hFr e he
        rw [e', tagged_self] at ht
        cases ht
    refine ⟨(as.map (tagA c)).reverse ++
      ((N.filter fun e => decide (e.1 ≠ a ++ [c])).filter fun e => decide (e.1 ≠ b ++ [c])), ?_,
      fun e he => ?_⟩
    · rw [fire_agents, hY, List.filter_append, List.filter_append, hf, hf, List.append_assoc]
    · rcases List.mem_append.1 he with he | he
      · exact mem_tag_self (List.mem_reverse.1 he)
      · exact hN e (List.mem_filter.1 (List.mem_filter.1 he).1).1
  · rw [fire_agents] at he
    rcases List.mem_append.1 he with he | he
    · obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 he)
      exact hP e₀.1
    · exact h e (List.mem_filter.1 (List.mem_filter.1 he).1).1

theorem Looks.afterS {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) {s a : Id} (hne : a ≠ s) :
    Looks c (stepS X s a) (stepS Y (s ++ [c]) (a ++ [c])) := by
  rw [stepS_tag c Y hne]
  exact h.fired s a _ _

theorem Looks.afterA {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) {a s : Id} (hne : a ≠ s) :
    Looks c (stepA X a s) (stepA Y (a ++ [c]) (s ++ [c])) := by
  rw [stepA_tag c Y hne]
  exact h.fired a s _ _

theorem Looks.afterZ {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (a z : Id) :
    Looks c (stepZ X a z) (stepZ Y (a ++ [c]) (z ++ [c])) := by
  rw [stepZ_tag c Y]
  exact h.fired a z _ _

theorem Moves.afterS (c : Nat) (Y : XNet Arith) {s a : Id} (hne : a ≠ s) :
    Moves c Y (stepS Y (s ++ [c]) (a ++ [c])) := by
  rw [stepS_tag c Y hne]
  exact Moves.fired c Y s a _ _

theorem Moves.afterA (c : Nat) (Y : XNet Arith) {a s : Id} (hne : a ≠ s) :
    Moves c Y (stepA Y (a ++ [c]) (s ++ [c])) := by
  rw [stepA_tag c Y hne]
  exact Moves.fired c Y a s _ _

theorem Moves.afterZ (c : Nat) (Y : XNet Arith) (a z : Id) :
    Moves c Y (stepZ Y (a ++ [c]) (z ++ [c])) := by
  rw [stepZ_tag c Y]
  exact Moves.fired c Y a z _ _

theorem stepS_head (c : Nat) (Y : XNet Arith) {s a : Id} (h : a ≠ s) :
    ∃ ry, (stepS Y (s ++ [c]) (a ++ [c])).agents = ((0 :: s) ++ [c], Arith.add) :: ry := by
  rw [stepS_tag c Y h, newAgents_swap h, fire_agents]
  exact ⟨_, rfl⟩

theorem stepA_head (c : Nat) (Y : XNet Arith) {a s : Id} (h : a ≠ s) :
    ∃ ry, (stepA Y (a ++ [c]) (s ++ [c])).agents = ((0 :: s) ++ [c], Arith.add) :: ry := by
  rw [stepA_tag c Y h, newAgents_add h, fire_agents]
  exact ⟨_, rfl⟩

/-- **The later rounds in a larger memory**, with the description of the
net alone carried along. -/
theorem Looks.rounds_later {c n : Nat} {X0 : XNet Arith} {T : Nat} :
    ∀ (r : Nat) {X Y : XNet Arith} {d : Nat}, Steady n X (n + 3 + r) → Hist n X0 X T r d →
      Looks c X Y → (∃ ry, Y.agents = ([0, n + 3 + r + 1] ++ [c], Arith.add) :: ry) →
      ∃ X' Y', Works xsys Y ⟨Y.agents, .idle⟩ Y' ⟨Y'.agents, .idle⟩ r (17 * r) ∧
        Steady n X' (n + 3) ∧ Hist n X0 X' T 0 (d + r) ∧ Looks c X' Y' ∧ Moves c Y Y' ∧
        ∃ ry, Y'.agents = ([0, n + 3 + 1] ++ [c], Arith.add) :: ry
  | 0, X, Y, _, st, H, h, hd => ⟨X, Y, .refl _ _, st, H, h, Moves.refl c Y, hd⟩
  | r + 1, X, Y, d, st, H, h, hd => by
    have st' : Steady n X (n + 3 + r + 1) := st
    obtain ⟨-, st1⟩ := Steady.round_exact st' (by omega)
    obtain ⟨ry, hy⟩ := hd
    have hne : ([0, n + 3 + r + 1 + 1] : Id) ≠ [n + 3 + r + 1] := fun e => by
      injection e with _ e2
      cases e2
    have w0 := h.round_later st' (by omega) ry
    have w : Works xsys Y ⟨Y.agents, .idle⟩
        (stepA Y ([0, n + 3 + r + 1 + 1] ++ [c]) ([n + 3 + r + 1] ++ [c]))
        ⟨(stepA Y ([0, n + 3 + r + 1 + 1] ++ [c]) ([n + 3 + r + 1] ++ [c])).agents, .idle⟩
        1 17 := by
      rw [hy]
      exact w0
    have h1 := h.afterA hne
    have mv1 := Moves.afterA c Y hne
    have hd1 := stepA_head c Y hne
    obtain ⟨X', Y', w', st2, H2, h2, mv2, hd2⟩ :=
      Looks.rounds_later (c := c) r st1 H.step h1 hd1
    refine ⟨X', Y', ?_, st2, ?_, h2, mv1.trans mv2, hd2⟩
    · have w2 := w.trans w'
      have e1 : 1 + r = r + 1 := by omega
      have e2 : 17 + 17 * r = 17 * (r + 1) := by omega
      rw [e1, e2] at w2
      exact w2
    · have e : d + 1 + r = d + (r + 1) := by omega
      rw [← e]
      exact H2

/-- **All the rounds of an addition in a larger memory.**  If the cells of
`Y` tagged `c` are the net for `(m + 1) + n`, a thread whose list starts
with the top successor makes the `m + 2` rounds in `17 * m + 25` actions,
as on the net alone, and leaves the cells with the tag as that run leaves
the net. -/
theorem Looks.rounds_all {c m n : Nat} {Y : XNet Arith} (h : Looks c (sum (m + 1) n) Y)
    (rest : List (Id × Arith)) :
    ∃ Xf Yf, Works xsys Y ⟨([n + 3 + m + 1] ++ [c], .succ) :: rest, .idle⟩ Yf
        ⟨Yf.agents, .idle⟩ (m + 2) (17 * m + 25) ∧
      Final n (sum (m + 1) n) Xf (n + 3 + m + 1) m ∧ Looks c Xf Yf ∧ Moves c Y Yf := by
  have st0 : Start n (sum (m + 1) n) (n + 3 + m) := by
    have h := start_sum m n
    have e : m + n + 3 = n + 3 + m := by omega
    rw [e] at h
    exact h
  obtain ⟨-, st1⟩ := Start.round_exact st0
  have hne : ([1] : Id) ≠ [n + 3 + m + 1] := fun e => by
    injection e with e1
    omega
  have w0 := h.round_first st0 rest
  have h1 := h.afterS hne
  have mv1 := Moves.afterS c Y hne
  have hd1 := stepS_head c Y hne
  have H0 : Hist n (sum (m + 1) n) (stepS (sum (m + 1) n) [n + 3 + m + 1] [1])
      (n + 3 + m + 1) m 0 := hist_start (sum_agents (m + 1) n)
  obtain ⟨X', Y', w1, st2, H1, h2, mv2, hd2⟩ :=
    Looks.rounds_later (c := c) m st1 H0 h1 hd1
  have hA : X'.agents = ([0, n + 3 + 1], Arith.add) :: (resL (n + 3) (0 + m) ++ tailA n) :=
    H1.agents
  have hz : assoc [2] X'.agents = some .zero := by
    rw [hA]
    show (if ([0, n + 3 + 1] : Id) = [2] then some Arith.add
      else assoc [2] (resL (n + 3) (0 + m) ++ (sndL n ++ [([2], Arith.zero), ([3], .zero)]))) = _
    rw [ite_neg' (fun e => by injection e with _ e2; cases e2),
      assoc_append_skip _ (fun e he => res_ne_single he 2),
      assoc_append_skip _ (fun e he e' => by
        obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
        rw [h3] at e'
        injection e' with e1
        omega)]
    rfl
  obtain ⟨ry, hy⟩ := hd2
  have w2' := h2.round_zero st2 hz ry
  have w2 : Works xsys Y' ⟨Y'.agents, .idle⟩ (stepZ Y' ([0, n + 3 + 1] ++ [c]) ([2] ++ [c]))
      ⟨(stepZ Y' ([0, n + 3 + 1] ++ [c]) ([2] ++ [c])).agents, .idle⟩ 1 9 := by
    rw [hy]
    exact w2'
  have h3 := h2.afterZ [0, n + 3 + 1] [2]
  have mv3 := Moves.afterZ c Y' [0, n + 3 + 1] [2]
  have F := H1.final
  have e0 : 0 + m = m := by omega
  rw [e0] at F
  refine ⟨_, _, ?_, F, h3, (mv1.trans mv2).trans mv3⟩
  have w := (w0.trans w1).trans w2
  have e1 : 1 + m + 1 = m + 2 := by omega
  have e2 : 16 + 17 * m + 9 = 17 * m + 25 := by omega
  rw [e1, e2] at w
  exact w

theorem filter_tag_self (c : Nat) (l : List (Id × Arith)) :
    (l.map (tagA c)).filter (fun e => tagged c e.1) = l.map (tagA c) :=
  List.filter_eq_self.2 fun _ he => mem_tag_self he

theorem filter_tag_none {c d : Nat} (hd : d ≠ c) (l : List (Id × Arith)) :
    (l.map (tagA d)).filter (fun e => tagged c e.1) = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    rw [mem_tag_other hd he]
    exact Bool.false_ne_true

theorem filterW_tag_self (c : Nat) (l : List (Port × Port)) :
    (l.map (tagL c)).filter (fun e => tagged c e.1.1) = l.map (tagL c) :=
  List.filter_eq_self.2 fun e he => by
    obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
    exact tagged_self c e₀.1.1

theorem filterW_tag_none {c d : Nat} (hd : d ≠ c) (l : List (Port × Port)) :
    (l.map (tagL d)).filter (fun e => tagged c e.1.1) = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
    show ¬ tagged c (e₀.1.1 ++ [d]) = true
    rw [tagged_other hd]
    exact Bool.false_ne_true

/-- The first of two nets side by side, seen in the memory of both. -/
theorem looks_left (A B : XNet Arith) : Looks 0 A (beside (tagNet 0 A) (tagNet 1 B)) :=
  ⟨by
    show ((A.agents.map (tagA 0)) ++ (B.agents.map (tagA 1))).filter (fun e => tagged 0 e.1) =
      A.agents.map (tagA 0)
    rw [List.filter_append, filter_tag_self, filter_tag_none (by decide), List.append_nil], by
    show ((A.wires.map (tagL 0)) ++ (B.wires.map (tagL 1))).filter (fun e => tagged 0 e.1.1) =
      A.wires.map (tagL 0)
    rw [List.filter_append, filterW_tag_self, filterW_tag_none (by decide), List.append_nil]⟩

/-- And the second. -/
theorem looks_right (A B : XNet Arith) : Looks 1 B (beside (tagNet 0 A) (tagNet 1 B)) :=
  ⟨by
    show ((A.agents.map (tagA 0)) ++ (B.agents.map (tagA 1))).filter (fun e => tagged 1 e.1) =
      B.agents.map (tagA 1)
    rw [List.filter_append, filter_tag_self, filter_tag_none (by decide), List.nil_append], by
    show ((A.wires.map (tagL 0)) ++ (B.wires.map (tagL 1))).filter (fun e => tagged 1 e.1.1) =
      B.wires.map (tagL 1)
    rw [List.filter_append, filterW_tag_self, filterW_tag_none (by decide), List.nil_append]⟩

/-- **One thread on two additions side by side, action by action.**  The
rounds of the first addition, a pass over what it leaves, the rounds of
the second, and a last pass over what both leave: `twoSolo` actions in
all, none of them a rest. -/
theorem two_sums_solo_works (m n m' n' : Nat) : ∃ Yf c,
    Works xsys (twoSums (m + 1) n (m' + 1) n')
      ⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩ Yf ⟨[], .idle⟩ c
      (twoSolo (m + 1) n (m' + 1) n') := by
  have hA0 : Looks 0 (sum (m + 1) n) (twoSums (m + 1) n (m' + 1) n') := looks_left _ _
  have hB0 : Looks 1 (sum (m' + 1) n') (twoSums (m + 1) n (m' + 1) n') := looks_right _ _
  have eY0 : (twoSums (m + 1) n (m' + 1) n').agents =
      (sum (m + 1) n).agents.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1) := rfl
  have stA : Start n (sum (m + 1) n) (n + 3 + m) := by
    have h := start_sum m n
    have e : m + n + 3 = n + 3 + m := by omega
    rw [e] at h
    exact h
  have stB : Start n' (sum (m' + 1) n') (n' + 3 + m') := by
    have h := start_sum m' n'
    have e : m' + n' + 3 = n' + 3 + m' := by omega
    rw [e] at h
    exact h
  obtain ⟨restA, hAa⟩ := stA.head
  obtain ⟨restB, hBa⟩ := stB.head
  obtain ⟨XAf, Y1, wA, FA, hA1, mvA⟩ :=
    hA0.rounds_all (restA.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1))
  have wA' : Works xsys (twoSums (m + 1) n (m' + 1) n')
      ⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩ Y1 ⟨Y1.agents, .idle⟩ (m + 2)
      (17 * m + 25) := by
    rw [eY0, hAa]
    exact wA
  have hB1 : Looks 1 (sum (m' + 1) n') Y1 := mvA.other 1 _ (by decide) hB0
  obtain ⟨N', hN', hNt⟩ := mvA.keep ((sum (m + 1) n).agents.map (tagA 0))
    ((sum (m' + 1) n').agents.map (tagA 1)) eY0 (fun _ he => mem_tag_self he)
    (fun _ he => mem_tag_other (by decide) he)
  have eN : N' = XAf.agents.map (tagA 0) := by
    have f := hA1.agents
    rw [hN', List.filter_append,
      (List.filter_eq_self (p := fun e : Id × Arith => tagged 0 e.1)).2 (fun e he => hNt e he),
      filter_tag_none (by decide), List.append_nil] at f
    exact f
  have eY1 : Y1.agents =
      XAf.agents.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1) := by
    rw [hN', eN]
  have sA := FA.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
  obtain ⟨k1, k2, hk, sY1, sX1⟩ := hA1.pass sA rfl trivial XAf.agents []
    ((sum (m' + 1) n').agents.map (tagA 1)) (List.append_nil _).symm
  have ek2 := stays_rest_zero sX1
  have pA : Works xsys Y1 ⟨Y1.agents, .idle⟩ Y1
      ⟨(sum (m' + 1) n').agents.map (tagA 1), .idle⟩ 0 (5 * m + 3 * n + 10) := by
    rw [eY1]
    have e : k1 = 5 * m + 3 * n + 10 := by omega
    rw [← e]
    exact sY1.works
  obtain ⟨XBf, Y2, wB, FB, hB2, mvB⟩ := hB1.rounds_all (restB.map (tagA 1))
  have wB' : Works xsys Y1 ⟨(sum (m' + 1) n').agents.map (tagA 1), .idle⟩ Y2
      ⟨Y2.agents, .idle⟩ (m' + 2) (17 * m' + 25) := by
    rw [hBa]
    exact wB
  have hA2 : Looks 0 XAf Y2 := mvB.other 0 _ (by decide) hA1
  have tg1 : ∀ e, e ∈ Y1.agents → tagged 0 e.1 = true ∨ tagged 1 e.1 = true := by
    intro e he
    rw [eY1] at he
    rcases List.mem_append.1 he with he | he
    · exact .inl (mem_tag_self he)
    · exact .inr (mem_tag_self he)
  have tg2 := mvB.tags (fun i => tagged 0 i = true ∨ tagged 1 i = true)
    (fun i => .inr (tagged_self 1 i)) tg1
  have sB := FB.pass_stays (snd_sum (m' + 1) n') (sum_fresh (m' + 1) n')
  have pF := pass_two hA2 hB2 Y2.agents XAf.agents XBf.agents _ _ tg2 hA2.agents hB2.agents
    sA sB
  have w := ((wA'.trans pA).trans wB').trans pF.works
  have e : 17 * m + 25 + (5 * m + 3 * n + 10) + (17 * m' + 25) +
      (5 * m + 3 * n + 10 + (5 * m' + 3 * n' + 10)) = twoSolo (m + 1) n (m' + 1) n' := by
    unfold twoSolo
    rw [soloWork_succ, soloWork_succ]
    omega
  rw [e] at w
  exact ⟨Y2, _, w⟩

/-- **One thread on two additions side by side takes `twoSolo` rounds, for
every size.**  On the net with `(m + 1) + n` and `(m' + 1) + n'` side by
side, one thread is at rest after exactly the rounds of each addition
alone and one more pass over what the first leaves, and not sooner. -/
theorem two_sums_solo (m n m' n' : Nat) :
    Rounds 1 (XMach.init (twoSums (m + 1) n (m' + 1) n') 1)
      (twoSolo (m + 1) n (m' + 1) n') := by
  obtain ⟨Yf, c, w⟩ := two_sums_solo_works m n m' n'
  obtain ⟨t1, t2⟩ := w.trace
  rw [XMach.init_one]
  have sch : ∀ i, (⟨twoSums (m + 1) n (m' + 1) n',
      [⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩]⟩ : XMach Arith).trace xsys
        (fun i => i % 1) i =
      (⟨twoSums (m + 1) n (m' + 1) n',
        [⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩]⟩ : XMach Arith).trace xsys
        (fun _ => 0) i := fun i => XMach.trace_congr xsys _ i (fun j _ => Nat.mod_one j)
  refine ⟨?_, fun R' hR' hrest => ?_⟩
  · rw [Nat.one_mul, sch, t1]
    rfl
  · rw [Nat.one_mul, sch] at hrest
    exact t2 R' hR' hrest

example : Rounds 1 (XMach.init (twoSums 6 10 6 10) 1) 415 :=
  (two_sums_solo 5 10 5 10).cast (by decide)

example : Rounds 1 (XMach.init (twoSums 20 30 12 40) 1) 1135 :=
  (two_sums_solo 19 30 11 40).cast (by decide)

/-- **Tagging the names commutes with every rule**: what a rule makes of
a tagged pair is what it makes of the pair, tagged. -/
theorem rule_tag (c : Nat) {α β : Arith} {R : XRhs Arith} (hR : xsys.rule α β = some R)
    {a b : Id} (hne : a ≠ b) :
    R.newAgents (a ++ [c]) (b ++ [c]) = (R.newAgents a b).map (tagA c) ∧
      R.newLinks xsys.sys.ar (a ++ [c]) (b ++ [c]) α β =
        (R.newLinks xsys.sys.ar a b α β).map (tagL c) := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       exact ⟨rfl, newLinks_zero_tag c a b⟩)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       exact ⟨rfl, rfl⟩)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       exact ⟨newAgents_add_tag c hne, newLinks_add_tag c a b⟩)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       exact ⟨newAgents_swap_tag c (fun e => hne e.symm), newLinks_swap_tag c a b⟩)

theorem Moves.take (c : Nat) (Y : XNet Arith) (a : Id) :
    Moves c Y (Y.takeAgent (a ++ [c])) := by
  refine ⟨fun d Z hd h => h.take_other hd a, fun N Fr hY hN hFr => ?_, fun P _ h e he => ?_⟩
  · have hf : (Fr.filter fun e => decide (e.1 ≠ a ++ [c])) = Fr :=
      List.filter_eq_self.2 fun e he => decide_eq_true fun e' => by
        have ht := hFr e he
        rw [e', tagged_self] at ht
        cases ht
    refine ⟨N.filter fun e => decide (e.1 ≠ a ++ [c]), ?_,
      fun e he => hN e (List.mem_filter.1 he).1⟩
    show (Y.agents.filter fun e => decide (e.1 ≠ a ++ [c])) = _
    rw [hY, List.filter_append, hf]
  · exact h e (XNet.mem_takeAgent.1 he).1

theorem Moves.put (c : Nat) (Y : XNet Arith) (i : Id) (γ : Arith) :
    Moves c Y (Y.putAgent (i ++ [c]) γ) := by
  refine ⟨fun d Z hd h => h.put_other hd i γ, fun N Fr hY hN _ => ?_, fun P hP h e he => ?_⟩
  · refine ⟨(i ++ [c], γ) :: N, ?_, fun e he => ?_⟩
    · show (i ++ [c], γ) :: Y.agents = _
      rw [hY]
      rfl
    · rcases List.mem_cons.1 he with e' | he
      · rw [e']
        exact tagged_self c i
      · exact hN e he
  · have he' : e ∈ (i ++ [c], γ) :: Y.agents := he
    rcases List.mem_cons.1 he' with e' | he'
    · rw [e']
      exact hP i
    · exact h e he'

theorem Moves.link (c : Nat) (Y : XNet Arith) (p q : Port) :
    Moves c Y (Y.putLink (tagPort c p) (tagPort c q)) :=
  ⟨fun _ _ hd h => h.link_other hd p q, fun N _ hY hN _ => ⟨N, hY, hN⟩, fun _ _ h => h⟩

/-- **An action on a net inside a larger memory is the action on the net
alone.**  Let the cells of `Y` tagged `c` be the net `X`.  A thread on `Y`
whose list starts with the entries `l`, tagged, and whose state is that of
a thread on `X`, tagged, does what that thread does on `X` with the list
`l`: the same reading, taking and writing, the same claim.  What comes
after `l` in either list plays no part, as long as `l` is not used up.
The cells with the tag stay the net the action leaves, and the cells with
another tag are not touched. -/
theorem Looks.act {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) (l s r : List (Id × Arith))
    (st : TState Arith) (hl : st = .idle → l ≠ []) (hw : st ≠ .write [] []) :
    ∃ (X' Y' : XNet Arith) (l' : List (Id × Arith)) (st' : TState Arith) (k : Nat),
      XMach.act xsys X ⟨l ++ s, st⟩ = (X', ⟨l' ++ s, st'⟩, k) ∧
      XMach.act xsys Y ⟨l.map (tagA c) ++ r, tagSt c st⟩ =
        (Y', ⟨l'.map (tagA c) ++ r, tagSt c st'⟩, k) ∧
      Looks c X' Y' ∧ Moves c Y Y' ∧ l'.length ≤ l.length ∧
      (Scans st → X' = X → Y' = Y ∧ Scans st') := by
  cases st with
  | idle =>
    cases l with
    | nil => exact absurd rfl (hl rfl)
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · exact ⟨X, Y, rest, .look e.1 e.2, 0,
          XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest ++ s) ha,
          XMach.act_idle_pos (xs := xsys) (X := Y) (e := tagA c e)
            (rest := rest.map (tagA c) ++ r) ((h.agent e.1).trans ha),
          h, Moves.refl c Y, Nat.le_succ _, fun _ _ => ⟨rfl, trivial⟩⟩
      · exact ⟨X, Y, rest, .idle, 0,
          XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest ++ s) ha,
          XMach.act_idle_neg (xs := xsys) (X := Y) (e := tagA c e)
            (rest := rest.map (tagA c) ++ r) (fun hh => ha ((h.agent e.1).symm.trans hh)),
          h, Moves.refl c Y, Nat.le_succ _, fun _ _ => ⟨rfl, trivial⟩⟩
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      exact ⟨X, Y, l, .idle, 0, XMach.act_look_none (xs := xsys) hq,
        XMach.act_look_none (xs := xsys)
          ((h.wire (a, 0)).trans (congrArg (Option.map (tagPort c)) hq)),
        h, Moves.refl c Y, Nat.le_refl _, fun _ _ => ⟨rfl, trivial⟩⟩
    | some q =>
      exact ⟨X, Y, l, .seek a α (a, 0) q, 0, XMach.act_look (xs := xsys) hq,
        XMach.act_look (xs := xsys)
          ((h.wire (a, 0)).trans (congrArg (Option.map (tagPort c)) hq)),
        h, Moves.refl c Y, Nat.le_refl _, fun _ _ => ⟨rfl, trivial⟩⟩
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        exact ⟨X, Y, l, .idle, 0, XMach.act_seek_stop (xs := xsys) hc hn,
          XMach.act_seek_stop (xs := xsys) ((h.here q).trans hc)
            ((h.next q p).trans (congrArg (Option.map (tagPort c)) hn)),
          h, Moves.refl c Y, Nat.le_refl _, fun _ _ => ⟨rfl, trivial⟩⟩
      | some q' =>
        exact ⟨X, Y, l, .seek a α q q', 0, XMach.act_seek_next (xs := xsys) hc hn,
          XMach.act_seek_next (xs := xsys) ((h.here q).trans hc)
            ((h.next q p).trans (congrArg (Option.map (tagPort c)) hn)),
          h, Moves.refl c Y, Nat.le_refl _, fun _ _ => ⟨rfl, trivial⟩⟩
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · exact ⟨X, Y, l, .ready a q.1 α β, 0, XMach.act_seek_found (xs := xsys) hc hr,
          XMach.act_seek_found (xs := xsys) (c := tagPort c q) ((h.here q).trans hc)
            ⟨fun e => hr.1 (List.append_cancel_right e), hr.2⟩,
          h, Moves.refl c Y, Nat.le_refl _, fun _ _ => ⟨rfl, trivial⟩⟩
      · exact ⟨X, Y, l, .idle, 0, XMach.act_seek_norule (xs := xsys) hc hr,
          XMach.act_seek_norule (xs := xsys) (c := tagPort c q) (β := β)
            ((h.here q).trans hc)
            (fun hh => hr ⟨fun e => hh.1 (congrArg (· ++ [c]) e), hh.2⟩),
          h, Moves.refl c Y, Nat.le_refl _, fun _ _ => ⟨rfl, trivial⟩⟩
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · exact ⟨X.takeAgent a, Y.takeAgent (a ++ [c]), l, .half a b α β, 0,
        XMach.act_ready (xs := xsys) ha, XMach.act_ready (xs := xsys) ((h.agent a).trans ha),
        h.take a, Moves.take c Y a, Nat.le_refl _, fun _ e => absurd e (takeAgent_ne ha)⟩
    · exact ⟨X, Y, l, .idle, 0, XMach.act_ready_neg (xs := xsys) ha,
        XMach.act_ready_neg (xs := xsys) (fun hh => ha ((h.agent a).symm.trans hh)),
        h, Moves.refl c Y, Nat.le_refl _, fun _ _ => ⟨rfl, trivial⟩⟩
  | half a b α β =>
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · have hcY : assoc (b ++ [c]) Y.agents = some β ∧ a ++ [c] ≠ b ++ [c] :=
        ⟨(h.agent b).trans hc.1, fun e => hc.2 (List.append_cancel_right e)⟩
      cases hR : xsys.rule α β with
      | none =>
        exact ⟨X.putAgent a α, Y.putAgent (a ++ [c]) α, l, .idle, 0,
          XMach.act_half_none (xs := xsys) ((ite_pos' hc).trans hR),
          XMach.act_half_none (xs := xsys) ((ite_pos' hcY).trans hR),
          h.put a α, Moves.put c Y a α, Nat.le_refl _, fun hS _ => False.elim hS⟩
      | some R =>
        have aY := XMach.act_half (xs := xsys) (X := Y) (todo := l.map (tagA c) ++ r)
          (a := a ++ [c]) (b := b ++ [c]) (α := α) (β := β) (R := R)
          ((ite_pos' hcY).trans hR)
        rw [(rule_tag c hR hc.2).1, (rule_tag c hR hc.2).2] at aY
        exact ⟨X.takeAgent b, Y.takeAgent (b ++ [c]), l,
          .write (R.newAgents a b) (R.newLinks xsys.sys.ar a b α β), 1,
          XMach.act_half (xs := xsys) ((ite_pos' hc).trans hR), aY, h.take b,
          Moves.take c Y b, Nat.le_refl _, fun hS _ => False.elim hS⟩
    · exact ⟨X.putAgent a α, Y.putAgent (a ++ [c]) α, l, .idle, 0,
        XMach.act_half_none (xs := xsys) (ite_neg' hc),
        XMach.act_half_none (xs := xsys) (ite_neg' (fun hh =>
          hc ⟨(h.agent b).symm.trans hh.1, fun e => hh.2 (congrArg (· ++ [c]) e)⟩)),
        h.put a α, Moves.put c Y a α, Nat.le_refl _, fun hS _ => False.elim hS⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨X.putAgent i γ, Y.putAgent (i ++ [c]) γ, l, .write as ls, 0, rfl, rfl,
        h.put i γ, Moves.put c Y i γ, Nat.le_refl _, fun hS _ => False.elim hS⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨X.putLink p q, Y.putLink (tagPort c p) (tagPort c q), l, .write [] ls, 0,
          rfl, rfl, h.link p q, Moves.link c Y p q, Nat.le_refl _,
          fun hS _ => False.elim hS⟩
      | nil => exact absurd rfl hw

/-- The part of the list of agents that carries the tag is the net. -/
theorem Looks.split {c : Nat} {X Y : XNet Arith} (h : Looks c X Y) {N Fr : List (Id × Arith)}
    (hY : Y.agents = N ++ Fr) (hN : ∀ e, e ∈ N → tagged c e.1 = true)
    (hFr : ∀ e, e ∈ Fr → tagged c e.1 = false) : N = X.agents.map (tagA c) := by
  have f := h.agents
  rw [hY, List.filter_append,
    (List.filter_eq_self (p := fun e : Id × Arith => tagged c e.1)).2 hN,
    (List.filter_eq_nil_iff (p := fun e : Id × Arith => tagged c e.1)).2 (fun e he => by
      rw [hFr e he]
      exact Bool.false_ne_true), List.append_nil] at f
  exact f

/-- `Inside c Fr X Y`: the cells of `Y` tagged `c` are the net `X`, and
they come first in the list of agents, before the cells `Fr` that do not
carry the tag. -/
structure Inside (c : Nat) (Fr : List (Id × Arith)) (X Y : XNet Arith) : Prop where
  looks : Looks c X Y
  agents : Y.agents = X.agents.map (tagA c) ++ Fr
  frame : ∀ e, e ∈ Fr → tagged c e.1 = false

theorem Inside.moves {c : Nat} {Fr : List (Id × Arith)} {X Y X' Y' : XNet Arith}
    (h : Inside c Fr X Y) (h' : Looks c X' Y') (mv : Moves c Y Y') : Inside c Fr X' Y' := by
  obtain ⟨N', hY', hN'⟩ := mv.keep (X.agents.map (tagA c)) Fr h.agents
    (fun _ he => mem_tag_self he) h.frame
  have e := h'.split hY' hN' h.frame
  rw [e] at hY'
  exact ⟨h', hY', h.frame⟩

/-- A thread on a net, moved to a larger memory: its list and its state
tagged, and `r` after its list. -/
def tagTh (c : Nat) (r : List (Id × Arith)) (T : XThread Arith) : XThread Arith :=
  ⟨T.todo.map (tagA c) ++ r, tagSt c T.st⟩

/-- **One action of a thread on a net that comes first in a larger
memory**, the reload of its list included: the list it loads is that of
the net, tagged, followed by the other cells. -/
theorem Inside.act {c : Nat} {Fr : List (Id × Arith)} {X Y : XNet Arith}
    (h : Inside c Fr X Y) (r : List (Id × Arith)) (T : XThread Arith)
    (hne : T ≠ ⟨[], .idle⟩) :
    ∃ Y' r', XMach.act xsys Y (tagTh c r T) =
        (Y', tagTh c r' (XMach.act xsys X T).2.1, (XMach.act xsys X T).2.2) ∧
      Inside c Fr (XMach.act xsys X T).1 Y' ∧ Moves c Y Y' ∧ (r' = r ∨ r' = Fr) := by
  obtain ⟨todo, st⟩ := T
  by_cases hw : st = .write [] []
  · subst hw
    refine ⟨Y, Fr, ?_, h, Moves.refl c Y, .inr rfl⟩
    show XMach.act xsys Y ⟨todo.map (tagA c) ++ r, .write [] []⟩ =
      (Y, ⟨X.agents.map (tagA c) ++ Fr, .idle⟩, 0)
    rw [← h.agents]
    rfl
  · obtain ⟨X', Y', l', st', k, aX, aY, lk, mv, -, -⟩ :=
      h.looks.act todo [] r st (fun e hl => hne (by rw [e, hl])) hw
    rw [List.append_nil, List.append_nil] at aX
    rw [aX]
    exact ⟨Y', r, aY, h.moves lk mv, mv, .inl rfl⟩

/-- **The run of one thread on a net that comes first in a larger memory
is its run on the net alone**, action for action, until it is at rest
there. -/
theorem Inside.solo {c : Nat} {Fr : List (Id × Arith)} :
    ∀ (a : Nat) {X Y : XNet Arith} (r : List (Id × Arith)) (T : XThread Arith),
      Inside c Fr X Y → (∀ j, j < a → (XMach.solo xsys X T j).2 ≠ ⟨[], .idle⟩) →
      ∃ Y' r', XMach.solo xsys Y (tagTh c r T) a =
          (Y', tagTh c r' (XMach.solo xsys X T a).2) ∧
        Inside c Fr (XMach.solo xsys X T a).1 Y' ∧ Moves c Y Y' ∧ (r' = r ∨ r' = Fr)
  | 0, _, Y, r, _, h, _ => ⟨Y, r, rfl, h, Moves.refl c Y, .inl rfl⟩
  | a + 1, X, Y, r, T, h, hne => by
    obtain ⟨Y1, r1, aY, h1, mv1, hr1⟩ := h.act r T (hne 0 (Nat.succ_pos a))
    obtain ⟨Y', r', sY, h', mv', hr'⟩ := Inside.solo a r1 (XMach.act xsys X T).2.1 h1
      (fun j hj => hne (j + 1) (Nat.succ_lt_succ hj))
    refine ⟨Y', r', ?_, h', mv1.trans mv', ?_⟩
    · show XMach.solo xsys (XMach.act xsys Y (tagTh c r T)).1
        (XMach.act xsys Y (tagTh c r T)).2.1 a = _
      rw [aY]
      exact sY
    · rcases hr' with e | e
      · rcases hr1 with e1 | e1
        · exact .inl (e.trans e1)
        · exact .inr (e.trans e1)
      · exact .inr e

end Arith

end INet
