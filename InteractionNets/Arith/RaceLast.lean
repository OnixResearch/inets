import InteractionNets.Arith.ThreeThreads

/-! ### Any number of threads in turn: the last one in the race -/

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

/-- A run of threads in turn, in two parts. -/
theorem trace_mod_add (c : Nat) (M : XMach Arith) (w w' : Nat) :
    (M.trace xsys (fun i => i % c) (c * (w + w'))).1 =
      ((M.trace xsys (fun i => i % c) (c * w)).1.trace xsys (fun i => i % c) (c * w')).1 := by
  rw [Nat.mul_add, XMach.trace_add xsys (fun i => i % c) M (c * w) (c * w')]
  show ((M.trace xsys (fun i => i % c) (c * w)).1.trace xsys
    (fun i => (c * w + i) % c) (c * w')).1 = _
  rw [XMach.trace_congr xsys _ (σ' := fun i => i % c) (c * w') fun j _ => Nat.mul_add_mod c w j]

/-- `Row Y Rs Rs'`: each thread of `Rs` acts once in the memory `Y`, leaves
it as it is and makes no claim, and `Rs'` are the threads after that. -/
inductive Row (Y : XNet Arith) : List (XThread Arith) → List (XThread Arith) → Prop
  | nil : Row Y [] []
  | cons {R R' : XThread Arith} {Rs Rs' : List (XThread Arith)} :
      XMach.act xsys Y R = (Y, R', 0) → Row Y Rs Rs' → Row Y (R :: Rs) (R' :: Rs')

theorem Row.length {Y : XNet Arith} {Rs Rs' : List (XThread Arith)} (h : Row Y Rs Rs') :
    Rs'.length = Rs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
    show _ + 1 = _ + 1
    rw [ih]

/-- **A row of threads that read, in the middle of a list of threads**:
each acts once, the memory and the other threads stay as they are. -/
theorem trace_row {Y : XNet Arith} {Rs Rs' : List (XThread Arith)} (h : Row Y Rs Rs') :
    ∀ (pre post : List (XThread Arith)),
      (⟨Y, pre ++ (Rs ++ post)⟩ : XMach Arith).trace xsys (fun i => pre.length + i) Rs.length =
        (⟨Y, pre ++ (Rs' ++ post)⟩, 0) := by
  induction h with
  | nil =>
    intro pre post
    rfl
  | @cons R R' Rs Rs' hR _ ih =>
    intro pre post
    have h1 : (XMach.act xsys Y R).1 = Y := by rw [hR]
    have h0 : (XMach.act xsys Y R).2.2 = 0 := by rw [hR]
    have e2 : (XMach.act xsys Y R).2.1 = R' := by rw [hR]
    have t1 := XMach.sweep_first xsys Y pre R (Rs ++ post) h1 h0
    rw [e2] at t1
    have ih' := ih (pre ++ [R']) post
    have cg := XMach.trace_congr xsys (⟨Y, (pre ++ [R']) ++ (Rs ++ post)⟩ : XMach Arith)
      (σ := fun i => pre.length + (1 + i)) (σ' := fun i => (pre ++ [R']).length + i) Rs.length
      (fun j _ => sweep_sched pre _ j)
    show (⟨Y, pre ++ R :: (Rs ++ post)⟩ : XMach Arith).trace xsys (fun i => pre.length + i)
      (Rs.length + 1) = _
    rw [Nat.add_comm Rs.length 1, XMach.trace_add xsys (fun i => pre.length + i) _ 1 Rs.length,
      t1]
    show ((XMach.trace xsys (fun i => pre.length + (1 + i))
        (⟨Y, (pre ++ [R']) ++ (Rs ++ post)⟩ : XMach Arith) Rs.length).1,
      0 + (XMach.trace xsys (fun i => pre.length + (1 + i))
        (⟨Y, (pre ++ [R']) ++ (Rs ++ post)⟩ : XMach Arith) Rs.length).2) = _
    rw [cg, ih', List.append_assoc]
    rfl

/-- One thread in the middle of a list acts. -/
theorem trace_at (Y Y1 : XNet Arith) (pre post : List (XThread Arith)) {P P' : XThread Arith}
    {c : Nat} (h : XMach.act xsys Y P = (Y1, P', c)) :
    (⟨Y, pre ++ P :: post⟩ : XMach Arith).trace xsys (fun i => pre.length + i) 1 =
      (⟨Y1, pre ++ P' :: post⟩, c) := by
  have st0 : XMach.step xsys ⟨Y, pre ++ P :: post⟩ pre.length =
      (⟨Y1, (pre ++ P :: post).set pre.length P'⟩, c) :=
    XMach.step_eq (M := ⟨Y, pre ++ P :: post⟩) (get_after pre P post) h
  rw [set_after] at st0
  show ((XMach.step xsys ⟨Y, pre ++ P :: post⟩ (pre.length + 0)).1,
    0 + (XMach.step xsys ⟨Y, pre ++ P :: post⟩ (pre.length + 0)).2) = _
  rw [Nat.add_zero, st0, Nat.zero_add]

/-- **One turn of each thread, two of them writing**: the first acts, the
threads between the two read in the memory it leaves, the second writer
acts, and the threads after it read in the memory that leaves. -/
theorem sweep_two {Y Y1 Y2 : XNet Arith} {F F' R R' : XThread Arith}
    {Qs Qs' Ps Ps' : List (XThread Arith)} {c1 c2 : Nat}
    (hF : XMach.act xsys Y F = (Y1, F', c1)) (hQ : Row Y1 Qs Qs')
    (hR : XMach.act xsys Y1 R = (Y2, R', c2)) (hP : Row Y2 Ps Ps') :
    ((⟨Y, F :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys (fun i => i)
      (1 + (Qs.length + (1 + Ps.length)))).1 = ⟨Y2, F' :: (Qs' ++ R' :: Ps')⟩ := by
  have b1 : (⟨Y, F :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys (fun i => i) 1 =
      (⟨Y1, F' :: (Qs ++ R :: Ps)⟩, c1) :=
    (XMach.trace_congr xsys (⟨Y, F :: (Qs ++ R :: Ps)⟩ : XMach Arith) (σ := fun i => i)
      (σ' := fun i => ([] : List (XThread Arith)).length + i) 1
      (fun j _ => (Nat.zero_add j).symm)).trans (trace_at Y Y1 [] (Qs ++ R :: Ps) hF)
  have b2 : (⟨Y1, F' :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys (fun i => 1 + i) Qs.length =
      (⟨Y1, F' :: (Qs' ++ R :: Ps)⟩, 0) := trace_row hQ [F'] (R :: Ps)
  have b3 : (⟨Y1, F' :: (Qs' ++ R :: Ps)⟩ : XMach Arith).trace xsys
      (fun i => 1 + (Qs.length + i)) 1 = (⟨Y2, F' :: (Qs' ++ R' :: Ps)⟩, c2) :=
    (XMach.trace_congr xsys (⟨Y1, F' :: (Qs' ++ R :: Ps)⟩ : XMach Arith)
      (σ := fun i => 1 + (Qs.length + i)) (σ' := fun i => (F' :: Qs').length + i) 1
      (fun j _ => by
        show 1 + (Qs.length + j) = Qs'.length + 1 + j
        rw [hQ.length]
        omega)).trans (trace_at Y1 Y2 (F' :: Qs') Ps hR)
  have e4 : ∀ L : List (XThread Arith),
      ((F' :: Qs') ++ [R']) ++ (L ++ []) = F' :: (Qs' ++ R' :: L) := fun L => by
    rw [List.append_nil, List.append_assoc]
    rfl
  have a4 := trace_row hP ((F' :: Qs') ++ [R']) []
  rw [e4 Ps, e4 Ps'] at a4
  have b4 : (⟨Y2, F' :: (Qs' ++ R' :: Ps)⟩ : XMach Arith).trace xsys
      (fun i => 1 + (Qs.length + (1 + i))) Ps.length = (⟨Y2, F' :: (Qs' ++ R' :: Ps')⟩, 0) :=
    (XMach.trace_congr xsys (⟨Y2, F' :: (Qs' ++ R' :: Ps)⟩ : XMach Arith)
      (σ := fun i => 1 + (Qs.length + (1 + i)))
      (σ' := fun i => ((F' :: Qs') ++ [R']).length + i) Ps.length
      (fun j _ => by
        rw [List.length_append]
        show 1 + (Qs.length + (1 + j)) = Qs'.length + 1 + 1 + j
        rw [hQ.length]
        omega)).trans a4
  have t1 : ((⟨Y, F :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys (fun i => i)
      (1 + (Qs.length + (1 + Ps.length)))).1 =
      ((⟨Y1, F' :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys (fun i => 1 + i)
        (Qs.length + (1 + Ps.length))).1 :=
    (congrArg Prod.fst (XMach.trace_add xsys (fun i => i) _ 1 (Qs.length + (1 + Ps.length)))).trans
      (by rw [b1])
  have t2 : ((⟨Y1, F' :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys (fun i => 1 + i)
      (Qs.length + (1 + Ps.length))).1 =
      ((⟨Y1, F' :: (Qs' ++ R :: Ps)⟩ : XMach Arith).trace xsys (fun i => 1 + (Qs.length + i))
        (1 + Ps.length)).1 :=
    (congrArg Prod.fst (XMach.trace_add xsys (fun i => 1 + i) _ Qs.length (1 + Ps.length))).trans
      (by rw [b2])
  have t3 : ((⟨Y1, F' :: (Qs' ++ R :: Ps)⟩ : XMach Arith).trace xsys
      (fun i => 1 + (Qs.length + i)) (1 + Ps.length)).1 =
      ((⟨Y2, F' :: (Qs' ++ R' :: Ps)⟩ : XMach Arith).trace xsys
        (fun i => 1 + (Qs.length + (1 + i))) Ps.length).1 :=
    (congrArg Prod.fst (XMach.trace_add xsys (fun i => 1 + (Qs.length + i)) _ 1 Ps.length)).trans
      (by rw [b3])
  exact t1.trans (t2.trans (t3.trans (congrArg Prod.fst b4)))

/-- `SweepsK M M' w`: `w` times, each thread acts in turn, the first and
one other writing and the rest only reading, and that takes `M` to `M'`. -/
inductive SweepsK : XMach Arith → XMach Arith → Nat → Prop
  | refl (M : XMach Arith) : SweepsK M M 0
  | step {Y Y1 Y2 : XNet Arith} {F F' R R' : XThread Arith}
      {Qs Qs' Ps Ps' : List (XThread Arith)} {c1 c2 : Nat} {M' : XMach Arith} {w : Nat} :
      XMach.act xsys Y F = (Y1, F', c1) → Row Y1 Qs Qs' →
      XMach.act xsys Y1 R = (Y2, R', c2) → Row Y2 Ps Ps' →
      SweepsK ⟨Y2, F' :: (Qs' ++ R' :: Ps')⟩ M' w →
      SweepsK ⟨Y, F :: (Qs ++ R :: Ps)⟩ M' (w + 1)

theorem two_len (F R : XThread Arith) (Qs Ps : List (XThread Arith)) :
    (F :: (Qs ++ R :: Ps)).length = 1 + (Qs.length + (1 + Ps.length)) := by
  show (Qs ++ R :: Ps).length + 1 = _
  rw [List.length_append]
  show Qs.length + (Ps.length + 1) + 1 = _
  omega

theorem SweepsK.len {M M' : XMach Arith} {w : Nat} (s : SweepsK M M' w) :
    M'.ths.length = M.ths.length := by
  induction s with
  | refl M => rfl
  | @step Y Y1 Y2 F F' R R' Qs Qs' Ps Ps' c1 c2 M' w hF hQ hR hP _ ih =>
    rw [ih]
    show (F' :: (Qs' ++ R' :: Ps')).length = (F :: (Qs ++ R :: Ps)).length
    rw [two_len, two_len, hQ.length, hP.length]

theorem SweepsK.trace {M M' : XMach Arith} {w : Nat} (s : SweepsK M M' w) :
    (M.trace xsys (fun i => i % M.ths.length) (M.ths.length * w)).1 = M' := by
  induction s with
  | refl M => rfl
  | @step Y Y1 Y2 F F' R R' Qs Qs' Ps Ps' c1 c2 M' w hF hQ hR hP _ ih =>
    have ih' : ((⟨Y2, F' :: (Qs' ++ R' :: Ps')⟩ : XMach Arith).trace xsys
        (fun i => i % (F' :: (Qs' ++ R' :: Ps')).length)
        ((F' :: (Qs' ++ R' :: Ps')).length * w)).1 = M' := ih
    rw [two_len, hQ.length, hP.length] at ih'
    show ((⟨Y, F :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys
      (fun i => i % (F :: (Qs ++ R :: Ps)).length)
      ((F :: (Qs ++ R :: Ps)).length * (w + 1))).1 = M'
    rw [two_len, show w + 1 = 1 + w from Nat.add_comm _ _, trace_mod_add]
    have one : ((⟨Y, F :: (Qs ++ R :: Ps)⟩ : XMach Arith).trace xsys
        (fun i => i % (1 + (Qs.length + (1 + Ps.length))))
        ((1 + (Qs.length + (1 + Ps.length))) * 1)).1 = ⟨Y2, F' :: (Qs' ++ R' :: Ps')⟩ := by
      rw [Nat.mul_one, XMach.trace_congr xsys _ (σ' := fun i => i)
        (1 + (Qs.length + (1 + Ps.length))) (fun j hj => Nat.mod_eq_of_lt hj)]
      exact sweep_two hF hQ hR hP
    rw [one]
    exact ih'

theorem hits_add (σ : Nat → Nat) (t a : Nat) : ∀ b,
    hits σ t (a + b) = hits σ t a + hits (fun i => σ (a + i)) t b
  | 0 => rfl
  | b + 1 => by
    show hits σ t (a + b) + (if σ (a + b) = t then 1 else 0) =
      hits σ t a + (hits (fun i => σ (a + i)) t b + (if σ (a + b) = t then 1 else 0))
    rw [hits_add σ t a b, Nat.add_assoc]

theorem hits_congr {σ σ' : Nat → Nat} (t : Nat) :
    ∀ i, (∀ j, j < i → σ j = σ' j) → hits σ t i = hits σ' t i
  | 0, _ => rfl
  | i + 1, h => by
    show hits σ t i + (if σ i = t then 1 else 0) = hits σ' t i + (if σ' i = t then 1 else 0)
    rw [hits_congr t i (fun j hj => h j (Nat.lt_succ_of_lt hj)), h i (Nat.lt_succ_self i)]

theorem hits_id (t : Nat) : ∀ j, hits (fun i => i) t j = if t < j then 1 else 0
  | 0 => (ite_neg' (Nat.not_lt_zero t)).symm
  | j + 1 => by
    show hits (fun i => i) t j + (if j = t then 1 else 0) = if t < j + 1 then 1 else 0
    rw [hits_id t j]
    by_cases h1 : t < j
    · rw [ite_pos' h1, ite_neg' (show ¬ j = t by omega), ite_pos' (show t < j + 1 by omega)]
    · by_cases h2 : j = t
      · rw [ite_neg' h1, ite_pos' h2, ite_pos' (show t < j + 1 by omega)]
      · rw [ite_neg' h1, ite_neg' h2, ite_neg' (show ¬ t < j + 1 by omega)]

/-- When `c` threads act in turn, each has had `w` actions after `c * w`. -/
theorem hits_mod (c t : Nat) (ht : t < c) : ∀ w, hits (fun i => i % c) t (c * w) = w
  | 0 => rfl
  | w + 1 => by
    have e : hits (fun i => (c * w + i) % c) t c = hits (fun i => i) t c :=
      hits_congr t c fun j hj => by
        show (c * w + j) % c = j
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    rw [Nat.mul_succ, hits_add (fun i => i % c) t (c * w) c, hits_mod c t ht w]
    show w + hits (fun i => (c * w + i) % c) t c = w + 1
    rw [e, hits_id, ite_pos' ht]

theorem hits_mono (σ : Nat → Nat) (t : Nat) {i j : Nat} (h : i ≤ j) :
    hits σ t i ≤ hits σ t j := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [hits_add]
  exact Nat.le_add_right _ _

/-- `StaysAll Y Ts W`: each thread of `Ts` only reads in the memory `Y` and
comes to rest, and the actions of all of them before they rest come to
`W`. -/
inductive StaysAll (Y : XNet Arith) : List (XThread Arith) → Nat → Prop
  | nil : StaysAll Y [] 0
  | cons {T : XThread Arith} {Ts : List (XThread Arith)} {k W : Nat} :
      Stays xsys Y T ⟨[], .idle⟩ k → StaysAll Y Ts W → StaysAll Y (T :: Ts) (k + W)

theorem StaysAll.reads {Y : XNet Arith} {Ts : List (XThread Arith)} {W : Nat}
    (h : StaysAll Y Ts W) : ∀ T, T ∈ Ts → T.Reads xsys Y := by
  induction h with
  | nil =>
    intro T hT
    cases hT
  | cons s _ ih =>
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (s.after rfl).1
    · exact ih T hT

theorem sumTo_shift (g : Nat → Nat) : ∀ m, sumTo g (m + 1) = g 0 + sumTo (fun t => g (t + 1)) m
  | 0 => by
    show 0 + g 0 = g 0 + 0
    omega
  | m + 1 => by
    show sumTo g (m + 1) + g (m + 1) = g 0 + (sumTo (fun t => g (t + 1)) m + g (m + 1))
    rw [sumTo_shift g m]
    omega

theorem StaysAll.sum {Y : XNet Arith} {Ts : List (XThread Arith)} {W : Nat}
    (h : StaysAll Y Ts W) : ∀ (hs : Nat → Nat), (∀ t, t < Ts.length → W ≤ hs t) →
      sumTo (fun t => (⟨Y, Ts⟩ : XMach Arith).tallyAt XThread.busy xsys t (hs t)) Ts.length =
        W := by
  induction h with
  | nil =>
    intro hs _
    rfl
  | @cons T Ts k W s _ ih =>
    intro hs hh
    have step : sumTo (fun t => (⟨Y, T :: Ts⟩ : XMach Arith).tallyAt XThread.busy xsys t (hs t))
        (Ts.length + 1) =
        T.tally XThread.busy xsys Y (hs 0) +
          sumTo (fun t => (⟨Y, Ts⟩ : XMach Arith).tallyAt XThread.busy xsys t (hs (t + 1)))
            Ts.length :=
      sumTo_shift _ Ts.length
    have e0 : T.tally XThread.busy xsys Y (hs 0) = k :=
      s.tally_eq rfl (hs 0) (by
        have := hh 0 (Nat.succ_pos _)
        omega)
    have e1 : sumTo (fun t => (⟨Y, Ts⟩ : XMach Arith).tallyAt XThread.busy xsys t (hs (t + 1)))
        Ts.length = W :=
      ih (fun t => hs (t + 1)) (fun t ht => by
        have := hh (t + 1) (Nat.succ_lt_succ ht)
        omega)
    show sumTo (fun t => (⟨Y, T :: Ts⟩ : XMach Arith).tallyAt XThread.busy xsys t (hs t))
      (Ts.length + 1) = k + W
    rw [step, e0, e1]

/-- **Any number of threads that only read, in turn, do exactly the work of
each.** -/
theorem total_stays {Y : XNet Arith} {Ts : List (XThread Arith)} {W : Nat}
    (h : StaysAll Y Ts W) :
    (⟨Y, Ts⟩ : XMach Arith).Total xsys (fun i => i % Ts.length) W := by
  refine ⟨Ts.length * W, fun i hi => ?_⟩
  have e := XMach.tally_reads XThread.busy (M := (⟨Y, Ts⟩ : XMach Arith))
    (fun i => i % Ts.length) h.reads i
  show (⟨Y, Ts⟩ : XMach Arith).tally XThread.busy xsys (fun i => i % Ts.length) i = W
  rw [e]
  exact h.sum (fun t => hits (fun i => i % Ts.length) t i) fun t ht => by
    have h1 := hits_mono (fun i => i % Ts.length) t hi
    rw [hits_mod Ts.length t ht W] at h1
    exact h1

/-- The work of a run of threads in turn, from a later state on. -/
theorem total_after (c : Nat) {M M' : XMach Arith} {E W : Nat}
    (h : (M.trace xsys (fun i => i % c) (c * E)).1 = M')
    (hw : M.work xsys (fun i => i % c) (c * E) = c * E)
    (tot : M'.Total xsys (fun i => i % c) W) : M.Total xsys (fun i => i % c) (c * E + W) := by
  subst h
  obtain ⟨N, hN⟩ := tot
  refine ⟨c * E + N, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = c * E + k := ⟨i - c * E, by omega⟩
  rw [work_mod_add c M E k, hw, hN k (by omega)]

/-- **Threads in turn, two of them writing for a while, to the end of the
run**: `w` actions of each, none at rest, and then each only reads. -/
theorem total_sweepsK {M : XMach Arith} {Y : XNet Arith} {Ts : List (XThread Arith)}
    {w W : Nat} (s : SweepsK M ⟨Y, Ts⟩ w) (hpos : 0 < M.ths.length) (h : StaysAll Y Ts W)
    (hb : ∀ T, T ∈ Ts → T ≠ ⟨[], .idle⟩) :
    M.Total xsys (fun i => i % M.ths.length) (M.ths.length * w + W) := by
  have hl : Ts.length = M.ths.length := s.len
  have hbt : ∀ (t : Nat) (T : XThread Arith),
      (M.trace xsys (fun i => i % M.ths.length) (M.ths.length * w)).1.ths[t]? = some T →
        T ≠ ⟨[], .idle⟩ := by
    rw [s.trace]
    intro t T hT
    exact hb T (List.mem_of_getElem? hT)
  have full := XMach.work_full (xs := xsys) (M := M) (σ := fun i => i % M.ths.length)
    (N := M.ths.length * w) hbt (fun i => Nat.mod_lt _ hpos) (M.ths.length * w) (Nat.le_refl _)
  have tot := total_stays h
  rw [hl] at tot
  exact total_after M.ths.length s.trace full tot

/-- `EntryAll m n E Ts Ss`: beside one thread on the net for `(m + 1) + n`,
each thread of `Ts` only reads for `E` actions, is then the thread of `Ss`
at its place, and is not at rest. -/
inductive EntryAll (m n E : Nat) : List (XThread Arith) → List (XThread Arith) → Prop
  | nil : EntryAll m n E [] []
  | cons {T S : XThread Arith} {Ts Ss : List (XThread Arith)} :
      RdAt m n T E S → S ≠ ⟨[], .idle⟩ → EntryAll m n E Ts Ss →
      EntryAll m n E (T :: Ts) (S :: Ss)

theorem EntryAll.reads {m n E : Nat} {Ts Ss : List (XThread Arith)} (h : EntryAll m n E Ts Ss) :
    ∀ T, T ∈ Ts → ∀ a, a < E →
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).1 =
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1 ∧
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).2.2 = 0 := by
  induction h with
  | nil =>
    intro T hT
    cases hT
  | cons r _ _ ih =>
    intro T hT a ha
    rcases List.mem_cons.1 hT with e | hT
    · rw [e]
      exact r.2 a ha
    · exact ih T hT a ha

theorem EntryAll.map {m n E : Nat} {Ts Ss : List (XThread Arith)} (h : EntryAll m n E Ts Ss) :
    Ts.map (fun T => XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T E) =
      Ss := by
  induction h with
  | nil => rfl
  | @cons T S Ts Ss r _ _ ih =>
    show XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T E ::
      Ts.map (fun T => XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T E) =
        S :: Ss
    rw [r.1, ih]

theorem EntryAll.tally {m n E : Nat} {Ts Ss : List (XThread Arith)} (h : EntryAll m n E Ts Ss) :
    total (fun T => seqTally XThread.busy
      (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T) E) Ts =
      Ts.length * E := by
  induction h with
  | nil => exact (Nat.zero_mul E).symm
  | @cons T S Ts Ss r hS _ ih =>
    have hb := reader_busy_upto (X := sum (m + 1) n)
      (F0 := ⟨(sum (m + 1) n).agents, .idle⟩) (T0 := T) (b := E) (fun e => by
        rw [r.1] at e
        exact hS e)
    show seqTally XThread.busy
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T) E +
      total (fun T => seqTally XThread.busy
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T) E) Ts =
      (Ts.length + 1) * E
    rw [ih, seqTally_full E (fun j hj => XThread.busy_of_ne_rest (hb j (by omega))),
      Nat.succ_mul]
    omega

/-- **Any number of threads in turn while all but the first only read**:
after each has acted `E` times the memory and the first thread are those of
one thread alone, the others are where their own actions took them, and
every action so far was work if none was at rest. -/
theorem entry_all {m n E : Nat} {Ts Ss : List (XThread Arith)} (h : EntryAll m n E Ts Ss)
    (hb0 : (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ E).2 ≠
      ⟨[], .idle⟩) :
    ((⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith).trace xsys
        (fun i => i % (Ts.length + 1)) ((Ts.length + 1) * E)).1 =
      ⟨(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ E).1,
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ E).2 :: Ss⟩ ∧
      (⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith).work xsys
        (fun i => i % (Ts.length + 1)) ((Ts.length + 1) * E) = (Ts.length + 1) * E := by
  have tr := XMach.trace_readers (xs := xsys) (X := sum (m + 1) n)
    (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩) (Ts := Ts) (A := E) h.reads E (Nat.le_refl _)
  have ht := XMach.tally_readers XThread.busy (xs := xsys) (X := sum (m + 1) n)
    (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩) (Ts := Ts) (A := E) h.reads E (Nat.le_refl _)
  constructor
  · rw [tr, h.map]
  · show (⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith).tally
      XThread.busy xsys (fun i => i % (Ts.length + 1)) ((Ts.length + 1) * E) = _
    rw [ht, h.tally, seqTally_full E (fun j hj =>
      XThread.busy_of_ne_rest (solo_busy_before hb0 j hj)), Nat.succ_mul]
    omega

/-- What a thread that reads the second argument needs of a memory: the
second argument is there, and the first adder is gone. -/
structure SndMem (n : Nat) (Y : XNet Arith) : Prop where
  three : assoc [3] Y.agents = some Arith.zero
  succ : ∀ j, 4 ≤ j → j ≤ n + 3 → assoc [j] Y.agents = some Arith.succ
  one : assoc [1] Y.agents = none

/-- **The five memories that the threads between the two of a race read
in**, one after each of the five actions of the first thread from the
moment the other is ready to take the zero of the first argument: what a
thread that only reads can find in them. -/
structure RaceViews (n : Nat) (Y0 Y1 Y2 Y3 Y4 : XNet Arith) : Prop where
  zero0 : assoc [2] Y0.agents = some Arith.zero
  look2_0 : assoc (([2], 0) : Port) Y0.wires = some ([n + 4], 1)
  look2_1 : assoc (([2], 0) : Port) Y1.wires = some ([n + 4], 1)
  seek2_1 : nextSeg Y1.wires ([n + 4], 1) ([2], 0) = some ([0, n + 4], 0)
  seek2_2 : nextSeg Y2.wires ([n + 4], 1) ([2], 0) = some ([0, n + 4], 0)
  goneA_2 : assoc [0, n + 4] Y2.agents = none
  goneA_3 : assoc [0, n + 4] Y3.agents = none
  stopA_2 : nextSeg Y2.wires ([0, n + 4], 0) ([n + 4], 1) = none
  stopA_3 : nextSeg Y3.wires ([0, n + 4], 0) ([n + 4], 1) = none
  snd0 : ∀ j, 3 ≤ j → j ≤ n + 2 → ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ Y0.wires
  sub01 : ∀ e, e ∈ Y0.wires → e ∈ Y1.wires
  sub12 : ∀ e, e ∈ Y1.wires → e ∈ Y2.wires
  sub23 : ∀ e, e ∈ Y2.wires → e ∈ Y3.wires
  sub34 : ∀ e, e ∈ Y3.wires → e ∈ Y4.wires
  m0 : SndMem n Y0
  m1 : SndMem n Y1
  m2 : SndMem n Y2
  m3 : SndMem n Y3
  m4 : SndMem n Y4
  two1 : assoc [2] Y1.agents = none
  two2 : assoc [2] Y2.agents = none
  two3 : assoc [2] Y3.agents = none
  two4 : assoc [2] Y4.agents = none

/-- A thread reads once in each of five memories. -/
def Reads5 (Y0 Y1 Y2 Y3 Y4 : XNet Arith) (Q Q' : XThread Arith) : Prop :=
  ∃ Q1 Q2 Q3 Q4, XMach.act xsys Y0 Q = (Y0, Q1, 0) ∧ XMach.act xsys Y1 Q1 = (Y1, Q2, 0) ∧
    XMach.act xsys Y2 Q2 = (Y2, Q3, 0) ∧ XMach.act xsys Y3 Q3 = (Y3, Q4, 0) ∧
    XMach.act xsys Y4 Q4 = (Y4, Q', 0)

/-- Each thread of a list does. -/
inductive Rows5 (Y0 Y1 Y2 Y3 Y4 : XNet Arith) :
    List (XThread Arith) → List (XThread Arith) → Prop
  | nil : Rows5 Y0 Y1 Y2 Y3 Y4 [] []
  | cons {Q Q' : XThread Arith} {Qs Qs' : List (XThread Arith)} :
      Reads5 Y0 Y1 Y2 Y3 Y4 Q Q' → Rows5 Y0 Y1 Y2 Y3 Y4 Qs Qs' →
      Rows5 Y0 Y1 Y2 Y3 Y4 (Q :: Qs) (Q' :: Qs')

theorem Rows5.rows {Y0 Y1 Y2 Y3 Y4 : XNet Arith} {Qs Qs' : List (XThread Arith)}
    (h : Rows5 Y0 Y1 Y2 Y3 Y4 Qs Qs') :
    ∃ L1 L2 L3 L4, Row Y0 Qs L1 ∧ Row Y1 L1 L2 ∧ Row Y2 L2 L3 ∧ Row Y3 L3 L4 ∧
      Row Y4 L4 Qs' := by
  induction h with
  | nil => exact ⟨[], [], [], [], .nil, .nil, .nil, .nil, .nil⟩
  | cons r _ ih =>
    obtain ⟨Q1, Q2, Q3, Q4, a0, a1, a2, a3, a4⟩ := r
    obtain ⟨L1, L2, L3, L4, r0, r1, r2, r3, r4⟩ := ih
    exact ⟨Q1 :: L1, Q2 :: L2, Q3 :: L3, Q4 :: L4, .cons a0 r0, .cons a1 r1, .cons a2 r2,
      .cons a3 r3, .cons a4 r4⟩

/-- `Beside1 m n Q k`: beside a race for the last pair on the net for
`(m + 1) + n`, the thread `Q` only reads during the five actions of the
race, and then comes to rest in `k` more actions, in the memory the race
leaves. -/
def Beside1 (m n : Nat) (Q : XThread Arith) (k : Nat) : Prop :=
  ∀ Y0 Y1 Y2 Y3 Y4 : XNet Arith, RaceViews n Y0 Y1 Y2 Y3 Y4 →
    Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m →
    ∃ Q', Reads5 Y0 Y1 Y2 Y3 Y4 Q Q' ∧ Stays xsys Y4 Q' ⟨[], .idle⟩ k ∧ Q' ≠ ⟨[], .idle⟩

/-- The same for a list of threads, `W` actions in all after the race. -/
def Beside (m n : Nat) (Qs : List (XThread Arith)) (W : Nat) : Prop :=
  ∀ Y0 Y1 Y2 Y3 Y4 : XNet Arith, RaceViews n Y0 Y1 Y2 Y3 Y4 →
    Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m →
    ∃ Qs', Rows5 Y0 Y1 Y2 Y3 Y4 Qs Qs' ∧ StaysAll Y4 Qs' W ∧ ∀ T, T ∈ Qs' → T ≠ ⟨[], .idle⟩

theorem Beside.nil (m n : Nat) : Beside m n [] 0 := fun _ _ _ _ _ _ _ =>
  ⟨[], .nil, .nil, fun T hT => by cases hT⟩

theorem Beside.cons {m n : Nat} {Q : XThread Arith} {k : Nat} {Qs : List (XThread Arith)}
    {W : Nat} (h1 : Beside1 m n Q k) (h : Beside m n Qs W) : Beside m n (Q :: Qs) (k + W) :=
  fun Y0 Y1 Y2 Y3 Y4 V F => by
    obtain ⟨Q', r, s, hne⟩ := h1 Y0 Y1 Y2 Y3 Y4 V F
    obtain ⟨Qs', rs, ss, hnes⟩ := h Y0 Y1 Y2 Y3 Y4 V F
    exact ⟨Q' :: Qs', .cons r rs, .cons s ss, fun T hT => by
      rcases List.mem_cons.1 hT with e | hT
      · rw [e]
        exact hne
      · exact hnes T hT⟩

/-- A list of successors of the first argument. -/
def Tops (n : Nat) (tq : List (Id × Arith)) : Prop := ∀ e, e ∈ tq → ∃ j, n + 3 < j ∧ e.1 = [j]

theorem tops_nil (n : Nat) : Tops n [] := fun _ he => by cases he

theorem tops_cons {n j : Nat} (hj : n + 3 < j) (γ : Arith) {tq : List (Id × Arith)}
    (h : Tops n tq) : Tops n (([j], γ) :: tq) := fun e he => by
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨j, hj, rfl⟩
  · exact h e he

/-- In a memory the rounds leave, the successors of the first argument are
gone: one action each. -/
theorem Final.tops_stays {m n : Nat} {Y : XNet Arith}
    (F : Final n (sum (m + 1) n) Y (n + 3 + m + 1) m) :
    ∀ (tq : List (Id × Arith)), Tops n tq → Stays xsys Y ⟨tq, .idle⟩ ⟨[], .idle⟩ tq.length
  | [], _ => .refl _
  | e :: tq, h => by
    obtain ⟨j, hj, ej⟩ := h e List.mem_cons_self
    have s2 : XMach.act xsys Y ⟨e :: tq, .idle⟩ = (Y, ⟨tq, .idle⟩, 0) :=
      XMach.act_idle_neg (e := e) (by
        rw [ej, F.no_top hj]
        exact fun h => by cases h)
    exact .step (fun h => by cases h) s2
      (F.tops_stays tq fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- What is left to a thread that has read the segment of the zero of the
second argument, with any successors of the first argument after it. -/
theorem Final.by_a {m n : Nat} {Y : XNet Arith}
    (F : Final n (sum (m + 1) n) Y (n + 3 + m + 1) m) (hn : 1 ≤ n) {tq : List (Id × Arith)}
    (ht : Tops n tq) :
    Stays xsys Y ⟨tq, .seek [3] .zero ([3], 0) ([4], 1)⟩ ⟨[], .idle⟩ (tq.length + 1) := by
  have S := snd_sum (m + 1) n
  have s1 : XMach.act xsys Y ⟨tq, .seek [3] .zero ([3], 0) ([4], 1)⟩ = (Y, ⟨tq, .idle⟩, 0) :=
    XMach.act_seek_stop (seek_aux_none Y _ 1 (by decide)) (nextSeg_none fun q hq =>
      (F.down S (j := 3) (by omega) (by omega) q).1 hq)
  exact .step (fun h => by
    injection h with _ h2
    cases h2) s1 (F.tops_stays tq ht)

theorem Final.by_b {m n : Nat} {Y : XNet Arith}
    (F : Final n (sum (m + 1) n) Y (n + 3 + m + 1) m) (hn : 1 ≤ n) {tq : List (Id × Arith)}
    (ht : Tops n tq) :
    Stays xsys Y ⟨tq, .look [3] .zero⟩ ⟨[], .idle⟩ (tq.length + 1 + 1) :=
  .step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look (F.look3 hn)) (F.by_a hn ht)

/-- **The thread next to the one that takes the pair, when it has read the
segment of the zero of the first argument**: it reads on to the last adder,
finds it gone, and goes on to the zero of the second argument. -/
theorem beside_adj_a (m : Nat) {n : Nat} (hn : 1 ≤ n) {tq : List (Id × Arith)}
    (ht : Tops n tq) :
    Beside1 m n ⟨([3], .zero) :: tq, .look [2] .zero⟩ (tq.length + 1) :=
  fun Y0 Y1 Y2 Y3 Y4 V F =>
    ⟨⟨tq, .seek [3] .zero ([3], 0) ([4], 1)⟩,
      ⟨⟨([3], .zero) :: tq, .seek [2] .zero ([2], 0) ([n + 4], 1)⟩,
        ⟨([3], .zero) :: tq, .seek [2] .zero ([n + 4], 1) ([0, n + 4], 0)⟩,
        ⟨([3], .zero) :: tq, .idle⟩, ⟨tq, .look [3] .zero⟩,
        XMach.act_look V.look2_0,
        XMach.act_seek_next (seek_aux_none _ _ 1 (by decide)) V.seek2_1,
        XMach.act_seek_stop ((ite_pos' rfl).trans V.goneA_2) V.stopA_2,
        XMach.act_idle_pos (e := ([3], Arith.zero)) V.m3.three,
        XMach.act_look (F.look3 hn)⟩,
      F.by_a hn ht, fun h => by
        injection h with _ h2
        cases h2⟩

/-- The same when it is about to pop that zero. -/
theorem beside_adj_b (m : Nat) {n : Nat} (hn : 1 ≤ n) {tq : List (Id × Arith)}
    (ht : Tops n tq) :
    Beside1 m n ⟨([2], .zero) :: ([3], .zero) :: tq, .idle⟩ (tq.length + 1 + 1) :=
  fun Y0 Y1 Y2 Y3 Y4 V F =>
    ⟨⟨tq, .look [3] .zero⟩,
      ⟨⟨([3], .zero) :: tq, .look [2] .zero⟩,
        ⟨([3], .zero) :: tq, .seek [2] .zero ([2], 0) ([n + 4], 1)⟩,
        ⟨([3], .zero) :: tq, .seek [2] .zero ([n + 4], 1) ([0, n + 4], 0)⟩,
        ⟨([3], .zero) :: tq, .idle⟩,
        XMach.act_idle_pos (e := ([2], Arith.zero)) V.zero0,
        XMach.act_look V.look2_1,
        XMach.act_seek_next (seek_aux_none _ _ 1 (by decide)) V.seek2_2,
        XMach.act_seek_stop ((ite_pos' rfl).trans V.goneA_3) V.stopA_3,
        XMach.act_idle_pos (e := ([3], Arith.zero)) V.m4.three⟩,
      F.by_b hn ht, fun h => by
        injection h with _ h2
        cases h2⟩

/-- **A thread two actions away from the zero of the first argument**, on
its way from the lowest successor of the second: it finds no second
segment, the first adder gone, that zero gone, and goes on to the zero of
the second argument. -/
theorem beside_late_s (m : Nat) {n : Nat} (hn : 2 ≤ n) {tq : List (Id × Arith)}
    (ht : Tops n tq) :
    Beside1 m n ⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq,
      .seek [4] .succ ([4], 0) ([5], 1)⟩ (tq.length + 1) :=
  fun Y0 Y1 Y2 Y3 Y4 V F =>
    ⟨⟨tq, .seek [3] .zero ([3], 0) ([4], 1)⟩,
      ⟨⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq, .idle⟩,
        ⟨([2], .zero) :: ([3], .zero) :: tq, .idle⟩, ⟨([3], .zero) :: tq, .idle⟩,
        ⟨tq, .look [3] .zero⟩,
        XMach.act_seek_stop (seek_aux_none _ _ 1 (by decide)) (nextSeg_none fun q hq =>
          (F.down (snd_sum (m + 1) n) (j := 4) (by omega) (by omega) q).1
            (V.sub34 _ (V.sub23 _ (V.sub12 _ (V.sub01 _ hq))))),
        XMach.act_idle_neg (e := ([1], Arith.add)) (by
          show ¬ assoc [1] Y1.agents = some Arith.add
          rw [V.m1.one]
          exact fun h => by cases h),
        XMach.act_idle_neg (e := ([2], Arith.zero)) (by
          show ¬ assoc [2] Y2.agents = some Arith.zero
          rw [V.two2]
          exact fun h => by cases h),
        XMach.act_idle_pos (e := ([3], Arith.zero)) V.m3.three,
        XMach.act_look (F.look3 (by omega))⟩,
      F.by_a (by omega) ht, fun h => by
        injection h with _ h2
        cases h2⟩

/-- **A thread three actions away from the zero of the first argument**,
reading the segment of the lowest successor of the second. -/
theorem beside_late_l (m : Nat) {n : Nat} (hn : 2 ≤ n) {tq : List (Id × Arith)}
    (ht : Tops n tq) :
    Beside1 m n ⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq, .look [4] .succ⟩
      (tq.length + 1 + 1) :=
  fun Y0 Y1 Y2 Y3 Y4 V F =>
    ⟨⟨tq, .look [3] .zero⟩,
      ⟨⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq, .seek [4] .succ ([4], 0) ([5], 1)⟩,
        ⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq, .idle⟩,
        ⟨([2], .zero) :: ([3], .zero) :: tq, .idle⟩, ⟨([3], .zero) :: tq, .idle⟩,
        XMach.act_look (assoc_eq_of_unique (V.snd0 4 (by omega) (by omega)) fun q' hq =>
          (F.up (snd_sum (m + 1) n) (j := 4) (by omega) (by omega) q').1
            (V.sub34 _ (V.sub23 _ (V.sub12 _ (V.sub01 _ hq))))),
        XMach.act_seek_stop (seek_aux_none _ _ 1 (by decide)) (nextSeg_none fun q hq =>
          (F.down (snd_sum (m + 1) n) (j := 4) (by omega) (by omega) q).1
            (V.sub34 _ (V.sub23 _ (V.sub12 _ hq)))),
        XMach.act_idle_neg (e := ([1], Arith.add)) (by
          show ¬ assoc [1] Y2.agents = some Arith.add
          rw [V.m2.one]
          exact fun h => by cases h),
        XMach.act_idle_neg (e := ([2], Arith.zero)) (by
          show ¬ assoc [2] Y3.agents = some Arith.zero
          rw [V.two3]
          exact fun h => by cases h),
        XMach.act_idle_pos (e := ([3], Arith.zero)) V.m4.three⟩,
      F.by_b (by omega) ht, fun h => by
        injection h with _ h2
        cases h2⟩

theorem StaysAll.cast {Y : XNet Arith} {Ts : List (XThread Arith)} {W W' : Nat}
    (h : StaysAll Y Ts W) (e : W = W') : StaysAll Y Ts W' := by
  subst e
  exact h

theorem StaysAll.snoc {Y : XNet Arith} {Ts : List (XThread Arith)} {W : Nat}
    (h : StaysAll Y Ts W) {T : XThread Arith} {k : Nat} (s : Stays xsys Y T ⟨[], .idle⟩ k) :
    StaysAll Y (Ts ++ [T]) (W + k) := by
  induction h with
  | nil => exact (StaysAll.cons s .nil).cast (by omega)
  | cons s' _ ih => exact (StaysAll.cons s' ih).cast (by omega)

theorem two_len' (F R : XThread Arith) (Qs : List (XThread Arith)) :
    (F :: (Qs ++ [R])).length = Qs.length + 2 := by
  show (Qs ++ [R]).length + 1 = _
  rw [List.length_append]
  rfl

/-- From the five sweeps of a race to the end of the run, with any threads
between the two that only read. -/
theorem race_close_k {M : XMach Arith} {Y : XNet Arith} {F5 R5 : XThread Arith}
    {Qs' : List (XThread Arith)} {kF kR WQ : Nat}
    (sw : SweepsK M ⟨Y, F5 :: (Qs' ++ [R5])⟩ 5) (hpos : 0 < M.ths.length)
    (sF : Stays xsys Y F5 ⟨[], .idle⟩ kF) (sR : Stays xsys Y R5 ⟨[], .idle⟩ kR)
    (hF : 1 ≤ kF) (hR : 1 ≤ kR) (ss : StaysAll Y Qs' WQ)
    (hne : ∀ T, T ∈ Qs' → T ≠ ⟨[], .idle⟩) :
    M.Total xsys (fun i => i % M.ths.length) (M.ths.length * 5 + (kF + (WQ + kR))) :=
  total_sweepsK sw hpos (.cons sF (ss.snoc sR)) fun T hT => by
    rcases List.mem_cons.1 hT with e | hT
    · rw [e]
      exact sF.ne_rest hF
    · rcases List.mem_append.1 hT with hT | hT
      · exact hne T hT
      · rcases List.mem_cons.1 hT with e | hT
        · rw [e]
          exact sR.ne_rest hR
        · cases hT

/-- **The race for the last pair with any number of threads reading between
the two**: the last thread takes the zero and the last adder, writes the
two segments and starts over, in five actions, and then every thread only
reads, in the memory the race leaves. -/
theorem race_wins_k {m n : Nat} {Y0 Y0' Y1' Y2' Y3' Y4' : XNet Arith}
    {F0 F1 F2 F3 F4 F5 : XThread Arith} {c0 c1 c2 c3 c4 : Nat} {l : List (Id × Arith)}
    {Qs : List (XThread Arith)} {kF kR WQ : Nat}
    (f0 : XMach.act xsys Y0 F0 = (Y0', F1, c0))
    (hZ : assoc [2] Y0'.agents = some .zero)
    (f1 : XMach.act xsys (Y0'.takeAgent [2]) F1 = (Y1', F2, c1))
    (hA : assoc [0, n + 4] Y1'.agents = some .add)
    (f2 : XMach.act xsys (Y1'.takeAgent [0, n + 4]) F2 = (Y2', F3, c2))
    (f3 : XMach.act xsys (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2)) F3 = (Y3', F4, c3))
    (f4 : XMach.act xsys (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1)) F4 = (Y4', F5, c4))
    (sF : Stays xsys Y4' F5 ⟨[], .idle⟩ kF)
    (sR : Stays xsys Y4' ⟨Y4'.agents, .idle⟩ ⟨[], .idle⟩ kR) (hF : 1 ≤ kF) (hR : 1 ≤ kR)
    (Fin : Final n (sum (m + 1) n) Y4' (n + 3 + m + 1) m)
    (V : RaceViews n Y0' Y1' Y2' Y3' Y4') (hQ : Beside m n Qs WQ) :
    (⟨Y0, F0 :: (Qs ++ [⟨l, .ready [2] [0, n + 4] .zero .add⟩])⟩ : XMach Arith).Total xsys
      (fun i => i % (Qs.length + 2)) ((Qs.length + 2) * 5 + (kF + (WQ + kR))) := by
  obtain ⟨Qs', rows, ss, hne⟩ := hQ Y0' Y1' Y2' Y3' Y4' V Fin
  obtain ⟨L1, L2, L3, L4, q0, q1, q2, q3, q4⟩ := rows.rows
  have r0 : XMach.act xsys Y0' ⟨l, .ready [2] [0, n + 4] .zero .add⟩ =
      (Y0'.takeAgent [2], ⟨l, .half [2] [0, n + 4] .zero .add⟩, 0) := XMach.act_ready hZ
  have r1 : XMach.act xsys Y1' ⟨l, .half [2] [0, n + 4] .zero .add⟩ =
      (Y1'.takeAgent [0, n + 4], ⟨l, .write []
        [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩, 1) :=
    XMach.act_half (R := addZero.swap.toX) (by
      rw [ite_pos' (show assoc [0, n + 4] Y1'.agents = some Arith.add ∧
        ([2] : Id) ≠ [0, n + 4] from ⟨hA, by ports_differ⟩)]
      rfl)
  have r2 : XMach.act xsys Y2' ⟨l, .write []
      [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2),
        ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩, 0) := rfl
  have r3 : XMach.act xsys Y3' ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1), ⟨l, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys Y4' ⟨l, .write [] []⟩ = (Y4', ⟨Y4'.agents, .idle⟩, 0) := rfl
  have sw : SweepsK ⟨Y0, F0 :: (Qs ++ [⟨l, .ready [2] [0, n + 4] .zero .add⟩])⟩
      ⟨Y4', F5 :: (Qs' ++ [⟨Y4'.agents, .idle⟩])⟩ 5 :=
    .step f0 q0 r0 .nil (.step f1 q1 r1 .nil (.step f2 q2 r2 .nil (.step f3 q3 r3 .nil
      (.step f4 q4 r4 .nil (.refl _)))))
  have tot : (⟨Y0, F0 :: (Qs ++ [⟨l, .ready [2] [0, n + 4] .zero .add⟩])⟩ : XMach Arith).Total
      xsys (fun i => i % (F0 :: (Qs ++ [(⟨l, .ready [2] [0, n + 4] .zero .add⟩ :
        XThread Arith)])).length)
      ((F0 :: (Qs ++ [(⟨l, .ready [2] [0, n + 4] .zero .add⟩ : XThread Arith)])).length * 5 +
        (kF + (WQ + kR))) :=
    race_close_k sw (Nat.succ_pos _) sF sR hF hR ss hne
  rw [two_len'] at tot
  exact tot

/-- `RaceEnd m n M0 F0 R0 kF kR`: from the memory `M0`, on the net for
`(m + 1) + n`, the first thread `F0` and the last thread `R0` race for the
last pair during five actions of each, whatever threads read between the
two; then no thread writes, the first comes to rest in `kF` actions and
the last in `kR`. -/
def RaceEnd (m n : Nat) (M0 : XNet Arith) (F0 R0 : XThread Arith) (kF kR : Nat) : Prop :=
  ∃ (Y0 Y1 Y2 Y3 Y4 : XNet Arith) (F5 R5 : XThread Arith),
    RaceViews n Y0 Y1 Y2 Y3 Y4 ∧ Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m ∧
    (∀ Qs Qs' : List (XThread Arith), Rows5 Y0 Y1 Y2 Y3 Y4 Qs Qs' →
      SweepsK ⟨M0, F0 :: (Qs ++ [R0])⟩ ⟨Y4, F5 :: (Qs' ++ [R5])⟩ 5) ∧
    Stays xsys Y4 F5 ⟨[], .idle⟩ kF ∧ Stays xsys Y4 R5 ⟨[], .idle⟩ kR ∧ 1 ≤ kF ∧ 1 ≤ kR

theorem RaceEnd.cast {m n : Nat} {M0 : XNet Arith} {F0 R0 : XThread Arith}
    {kF kR kF' kR' : Nat} (h : RaceEnd m n M0 F0 R0 kF kR) (eF : kF = kF') (eR : kR = kR') :
    RaceEnd m n M0 F0 R0 kF' kR' := by
  subst eF
  subst eR
  exact h

/-- The work of a run from the race on: five actions of each thread, then
what each still does. -/
theorem RaceEnd.total {m n : Nat} {M0 : XNet Arith} {F0 R0 : XThread Arith} {kF kR : Nat}
    (h : RaceEnd m n M0 F0 R0 kF kR) {Qs : List (XThread Arith)} {WQ : Nat}
    (hQ : Beside m n Qs WQ) :
    (⟨M0, F0 :: (Qs ++ [R0])⟩ : XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (kF + (WQ + kR))) := by
  obtain ⟨Y0, Y1, Y2, Y3, Y4, F5, R5, V, Fin, sw, sF, sR, hF, hR⟩ := h
  obtain ⟨Qs', rows, ss, hne⟩ := hQ Y0 Y1 Y2 Y3 Y4 V Fin
  have tot : (⟨M0, F0 :: (Qs ++ [R0])⟩ : XMach Arith).Total xsys
      (fun i => i % (F0 :: (Qs ++ [R0])).length)
      ((F0 :: (Qs ++ [R0])).length * 5 + (kF + (WQ + kR))) :=
    race_close_k (sw Qs Qs' rows) (Nat.succ_pos _) sF sR hF hR ss hne
  rw [two_len'] at tot
  exact tot

/-- **The race for the last pair, the last thread taking it**: what it
leaves each of the two threads to do. -/
theorem race_wins_e {m n : Nat} {Y0 Y0' Y1' Y2' Y3' Y4' : XNet Arith}
    {F0 F1 F2 F3 F4 F5 : XThread Arith} {c0 c1 c2 c3 c4 : Nat} {l : List (Id × Arith)}
    {kF kR : Nat}
    (f0 : XMach.act xsys Y0 F0 = (Y0', F1, c0))
    (hZ : assoc [2] Y0'.agents = some .zero)
    (f1 : XMach.act xsys (Y0'.takeAgent [2]) F1 = (Y1', F2, c1))
    (hA : assoc [0, n + 4] Y1'.agents = some .add)
    (f2 : XMach.act xsys (Y1'.takeAgent [0, n + 4]) F2 = (Y2', F3, c2))
    (f3 : XMach.act xsys (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2)) F3 = (Y3', F4, c3))
    (f4 : XMach.act xsys (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1)) F4 = (Y4', F5, c4))
    (sF : Stays xsys Y4' F5 ⟨[], .idle⟩ kF)
    (sR : Stays xsys Y4' ⟨Y4'.agents, .idle⟩ ⟨[], .idle⟩ kR) (hF : 1 ≤ kF) (hR : 1 ≤ kR)
    (Fin : Final n (sum (m + 1) n) Y4' (n + 3 + m + 1) m)
    (V : RaceViews n Y0' Y1' Y2' Y3' Y4') :
    RaceEnd m n Y0 F0 ⟨l, .ready [2] [0, n + 4] .zero .add⟩ kF kR := by
  have r0 : XMach.act xsys Y0' ⟨l, .ready [2] [0, n + 4] .zero .add⟩ =
      (Y0'.takeAgent [2], ⟨l, .half [2] [0, n + 4] .zero .add⟩, 0) := XMach.act_ready hZ
  have r1 : XMach.act xsys Y1' ⟨l, .half [2] [0, n + 4] .zero .add⟩ =
      (Y1'.takeAgent [0, n + 4], ⟨l, .write []
        [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩, 1) :=
    XMach.act_half (R := addZero.swap.toX) (by
      rw [ite_pos' (show assoc [0, n + 4] Y1'.agents = some Arith.add ∧
        ([2] : Id) ≠ [0, n + 4] from ⟨hA, by ports_differ⟩)]
      rfl)
  have r2 : XMach.act xsys Y2' ⟨l, .write []
      [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2),
        ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩, 0) := rfl
  have r3 : XMach.act xsys Y3' ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1), ⟨l, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys Y4' ⟨l, .write [] []⟩ = (Y4', ⟨Y4'.agents, .idle⟩, 0) := rfl
  exact ⟨Y0', Y1', Y2', Y3', Y4', F5, ⟨Y4'.agents, .idle⟩, V, Fin, fun Qs Qs' rows => by
    obtain ⟨L1, L2, L3, L4, q0, q1, q2, q3, q4⟩ := rows.rows
    exact .step f0 q0 r0 .nil (.step f1 q1 r1 .nil (.step f2 q2 r2 .nil (.step f3 q3 r3 .nil
      (.step f4 q4 r4 .nil (.refl _))))), sF, sR, hF, hR⟩

section Views

variable {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}

theorem RaceBase.by_succ (B : RaceBase (m' + 1) (n' + 1) X rest) (j : Nat) (h4 : 4 ≤ j)
    (hj : j ≤ n' + 1 + 3) : assoc [j] X.agents = some Arith.succ := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
  have hx : assoc [k + 4] (sum (m' + 1 + 1) (n' + 1)).agents = some Arith.succ :=
    sum_assoc_base (m' + 1) (n' + 1) (e := ([k + 4], Arith.succ))
      (List.mem_append_left _ (sndL_mem (n' + 1) k (by omega)))
  have h := solo_snd_forever (m' + 1) (n' + 1) (j := k + 4) (by omega) (by omega) hx
    (16 + 17 * (m' + 1))
  rw [B.solo] at h
  exact h

theorem RaceBase.by_one (B : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc [1] X.agents = none := by
  have h := (solo_gone5 (m' + 1) (n' + 1) (u := 16 + 17 * (m' + 1)) (by omega)).2
  rw [B.solo] at h
  exact h

theorem RaceBase.snd_mem (B : RaceBase (m' + 1) (n' + 1) X rest) (j : Nat) (h3 : 3 ≤ j)
    (hj : j ≤ n' + 1 + 2) : ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ X.wires := by
  have h := assoc_mem (solo_look_snd (m' + 1) (n' + 1) (j := j) h3 hj (16 + 17 * (m' + 1))).1
  rw [B.solo] at h
  exact h

end Views

/-- **The last thread takes the zero at the first moment it can, three segments before the end of the round of
the first, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d0 {m' n' : Nat} {V : XNet Arith} {p5 q5 p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith))
    (h0 : assoc (([2], 0) : Port) (V.putLink p5 q5).wires = some ([n' + 1 + 4], 1))
    (h1 : assoc (([2], 0) : Port) ((V.putLink p5 q5).putLink p6 q6).wires = some ([n' + 1 + 4], 1))
    (h2 : nextSeg ((V.putLink p5 q5).putLink p6 q6).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0))
    (h3 : nextSeg (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0))
    (hS : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 → ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires) :
    RaceEnd (m' + 1) (n' + 1) V ⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 10) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := by
    refine final_of B.hist ?_ fun e => ?_
    · rw [show ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = (((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents.filter fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) from rfl, filter_ne_comm]
      exact B.hist.final.agents
    · show e ∈ (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (p8, q8) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) ::
          (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ↔
        e ∈ (p8, q8) :: (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ∨
          e ∈ [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]
      constructor
      · intro h
        rcases List.mem_cons.1 h with rfl | h
        · exact .inr (List.mem_cons_of_mem _ List.mem_cons_self)
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl List.mem_cons_self
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inr List.mem_cons_self
            · exact .inl (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        · rcases List.mem_cons.1 h with rfl | h
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          · rcases List.mem_cons.1 h with rfl | h
            · exact List.mem_cons_self
            · cases h
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((V.putLink p5 q5), ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p5 q5).takeAgent [2])
      ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f4 : XMach.act xsys ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨todo, .write [] []⟩ =
      (((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 f4 sR sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (h0)
      look2_1 := (h1)
      seek2_1 := (h2)
      seek2_2 := (h3)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (nextSeg_none_sub B.by_stopA fun q hq => List.mem_cons_of_mem _ hq)
      stopA_3 := (nextSeg_none_sub B.by_stopA fun q hq => by
      have hq' : (([0, n' + 1 + 4], 0), q) ∈ (p8, q8) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).wires := hq
      show (([0, n' + 1 + 4], 0), q) ∈ (p8, q8) :: (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).wires
      rcases List.mem_cons.1 hq' with e | hq'
      · rw [e]
        exact List.mem_cons_self
      · rcases List.mem_cons.1 hq' with e | hq'
        · simp at e
        · exact List.mem_cons_of_mem _ hq')
      snd0 := (fun j a b => List.mem_cons_of_mem _ (hS j a b))
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d0 {m' n' : Nat} {V : XNet Arith} {p5 q5 p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (h0 : assoc (([2], 0) : Port) (V.putLink p5 q5).wires = some ([n' + 1 + 4], 1))
    (h1 : assoc (([2], 0) : Port) ((V.putLink p5 q5).putLink p6 q6).wires = some ([n' + 1 + 4], 1))
    (h2 : nextSeg ((V.putLink p5 q5).putLink p6 q6).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0))
    (h3 : nextSeg (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0))
    (hS : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 → ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires)
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨V, ⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 20) + WQ) :=
  ((race_e_d0 B todo l h0 h1 h2 h3 hS).total hQ).cast (by omega)

/-- **The last thread takes the zero two segments before the end of the round of the first, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d1 {m' n' : Nat} {V : XNet Arith} {p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (((V.putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith))
    (h0 : assoc (([2], 0) : Port) (V.putLink p6 q6).wires = some ([n' + 1 + 4], 1))
    (h1 : assoc (([2], 0) : Port) ((V.putLink p6 q6).putLink p7 q7).wires = some ([n' + 1 + 4], 1))
    (h2 : nextSeg ((V.putLink p6 q6).putLink p7 q7).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0))
    (hS : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 → ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires) :
    RaceEnd (m' + 1) (n' + 1) V ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 9) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).agents = resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((V.putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p6 q6).takeAgent [2]) ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨todo, .write [] []⟩ =
      (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f4 : XMach.act xsys (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 f4 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (h0)
      look2_1 := (h1)
      seek2_1 := (h2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (fun j a b => List.mem_cons_of_mem _ (hS j a b))
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d1 {m' n' : Nat} {V : XNet Arith} {p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (((V.putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (h0 : assoc (([2], 0) : Port) (V.putLink p6 q6).wires = some ([n' + 1 + 4], 1))
    (h1 : assoc (([2], 0) : Port) ((V.putLink p6 q6).putLink p7 q7).wires = some ([n' + 1 + 4], 1))
    (h2 : nextSeg ((V.putLink p6 q6).putLink p7 q7).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0))
    (hS : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 → ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires)
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨V, ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 19) + WQ) :=
  ((race_e_d1 B todo l h0 h1 h2 hS).total hQ).cast (by omega)

/-- **The last thread takes the zero as the first writes the last segment but one of its round, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d2 {m' n' : Nat} {V : XNet Arith} {p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((V.putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith))
    (h0 : assoc (([2], 0) : Port) (V.putLink p7 q7).wires = some ([n' + 1 + 4], 1))
    (hS : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 → ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires) :
    RaceEnd (m' + 1) (n' + 1) V ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 8) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).agents = resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((V.putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p7 q7).takeAgent [2]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] []⟩ =
      (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f3 : XMach.act xsys (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 f4 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (h0)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (fun j a b => List.mem_cons_of_mem _ (hS j a b))
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d2 {m' n' : Nat} {V : XNet Arith} {p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((V.putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (h0 : assoc (([2], 0) : Port) (V.putLink p7 q7).wires = some ([n' + 1 + 4], 1))
    (hS : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 → ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires)
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨V, ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 18) + WQ) :=
  ((race_e_d2 B todo l h0 hS).total hQ).cast (by omega)

/-- **The last thread takes the zero as the first writes the last segment of its round, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d3 {m' n' : Nat} {V : XNet Arith} {p8 q8 : Port} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (V.putLink p8 q8) rest) (todo l : List (Id × Arith)) :
    RaceEnd (m' + 1) (n' + 1) V ⟨todo, .write [] [(p8, q8)]⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 8) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hM1 : ((V.putLink p8 q8).takeAgent [2]).agents = ([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])) := by
    show List.filter (fun e => decide (e.1 ≠ [2])) (V.putLink p8 q8).agents = _
    rw [B.agents, List.filter_cons_of_pos (by simp), rest_filter_two]
  have gA : assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] (((V.putLink p8 q8).agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p8, q8)]⟩ =
      ((V.putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p8 q8).takeAgent [2]) ⟨todo, .write [] []⟩ =
      (((V.putLink p8 q8).takeAgent [2]), ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])), .idle⟩, 0) := by
    rw [← hM1]
    rfl
  have f2 : XMach.act xsys (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])), .idle⟩ =
      ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([0, n' + 1 + 4], Arith.add)) (by
      show ¬ assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = some Arith.add
      rw [gA]
      exact fun h => by cases h)
  have f3 : XMach.act xsys ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 f4 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (by
      under_wires
      exact B.by_look2)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (B.snd_mem)
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d3 {m' n' : Nat} {V : XNet Arith} {p8 q8 : Port} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (V.putLink p8 q8) rest) (todo l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨V, ⟨todo, .write [] [(p8, q8)]⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 18) + WQ) :=
  ((race_e_d3 B todo l).total hQ).cast (by omega)

/-- **The last thread takes the zero as the first starts over after its round on the lowest successor, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d4 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (todo l : List (Id × Arith)) :
    RaceEnd (m' + 1) (n' + 1) X ⟨todo, .write [] []⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 11) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨todo, .write [] []⟩ =
      (X, ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩, 0) := by
    rw [← B.agents]
    rfl
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩, 0) :=
    XMach.act_idle_pos (e := ([0, n' + 1 + 4], Arith.add)) B.adder1
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl (by
      show nextSeg ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([n' + 1 + 4], 1) ([0, n' + 1 + 4], 0) = _
      rw [nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.seek)
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) (by
      show nextSeg ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([2], 0)
        ([n' + 1 + 4], 1) = none
      rw [nextSeg_cons_ne _ _ _ (by ports_differ), nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.stop)
  have sF := (Stays.step (fun h => by cases h)
    (XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1)
    (Stays.step (fun h => by
      injection h with _ h2
      cases h2) (XMach.act_look k2) sE2)).trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 f4 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (by
      under_wires
      exact B.by_look2)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (B.snd_mem)
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d4 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (todo l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨X, ⟨todo, .write [] []⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 21) + WQ) :=
  ((race_e_d4 B todo l).total hQ).cast (by omega)

/-- **The last thread takes the zero as the first is about to pop the last adder, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d5 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    RaceEnd (m' + 1) (n' + 1) X ⟨X.agents, .idle⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 10) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  have f0 : XMach.act xsys X ⟨X.agents, .idle⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩, 0) := by
    rw [B.agents]
    exact XMach.act_idle_pos (e := ([0, n' + 1 + 4], Arith.add)) B.adder
  have f1 : XMach.act xsys (X.takeAgent [2])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (X.takeAgent [2], ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
        .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
        .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4],
        ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
          .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
        .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2),
        ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) (by
      show nextSeg ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([2], 0)
        ([n' + 1 + 4], 1) = none
      rw [nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.stop)
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
        ([0, n' + 1 + 4], 1))
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
        ([0, n' + 1 + 4], 1),
        ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans B.pass_two
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 f4 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (by
      under_wires
      exact B.by_look2)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (B.snd_mem)
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d5 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨X, ⟨X.agents, .idle⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 20) + WQ) :=
  ((race_e_d5 B l).total hQ).cast (by omega)

/-- **The last thread takes the zero while the first reads the segment of the last adder, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d6 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    RaceEnd (m' + 1) (n' + 1) X ⟨rest, .look [0, n' + 1 + 4] .add⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 9) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) B.stop
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sF := sE2.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 f4 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (by
      under_wires
      exact B.by_look2)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (B.snd_mem)
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d6 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨X, ⟨rest, .look [0, n' + 1 + 4] .add⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 19) + WQ) :=
  ((race_e_d6 B l).total hQ).cast (by omega)

/-- **The last thread takes the zero while the first is on its way from the last adder to it, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d7 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    RaceEnd (m' + 1) (n' + 1) X ⟨rest, .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 8) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero1) B.stop
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port) ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 B.zero f1 B.adder1 f2 f3 k3 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (by
      under_wires
      exact B.by_look2)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (B.snd_mem)
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d7 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨X, ⟨rest, .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 18) + WQ) :=
  ((race_e_d7 B l).total hQ).cast (by omega)

/-- **The last thread takes the zero in the round in which the first takes the last adder, with
any number of threads reading between the two.**  The five actions of the
race, and what the first thread and the last still do after it. -/
theorem race_e_d9 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    RaceEnd (m' + 1) (n' + 1) X ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 8) (5 * (m' + 1) + 3 * (n' + 1) + 10) := by
  have hr := B.rest
  subst hr
  have hA9 : ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) := by
    show List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) (([0, n' + 1 + 4], Arith.add) ::
      (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter (fun e => decide (e.1 ≠ [2]))) = _
    rw [List.filter_cons_of_neg (by simp),
      filter_ne_comm (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) [2] [0, n' + 1 + 4],
      filter_ne_idem, filter_ne_comm]
  have F := B.final hA9 rfl
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .ready [0, n' + 1 + 4] [2] .add .zero⟩ =
      ((X.takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half [0, n' + 1 + 4] [2] .add .zero⟩, 0) :=
    XMach.act_ready B.adder
  have hZ : assoc [2] (X.takeAgent [0, n' + 1 + 4]).agents = some .zero := by
    show assoc [2] (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = some .zero
    rw [assoc_filter_ne, ite_neg' (by ports_differ)]
    exact B.zero
  have gz : assoc [2] ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).agents = none := by
    show assoc [2] ((X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter fun e => decide (e.1 ≠ [2])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f1 : XMach.act xsys ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gz] at h1
      cases h1)
  have hA : assoc [0, n' + 1 + 4] (((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).agents = some .add := by
    show (if ([0, n' + 1 + 4] : Id) = [0, n' + 1 + 4] then some Arith.add else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) (by
      show assoc [0, 0, n' + 1 + 3 + 2] (List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) (([0, n' + 1 + 4], Arith.add) ::
        (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter (fun e => decide (e.1 ≠ [2])))) = some .succ
      rw [assoc_filter_ne, ite_neg' (by ports_differ), assoc_cons_ne _ (by ports_differ),
        assoc_filter_ne, ite_neg' (by ports_differ), assoc_filter_ne,
        ite_neg' (by ports_differ)]
      exact B.hist.agent_res (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) List.mem_cons_self)
  have f3 : XMach.act xsys (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port) ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact (race_wins_e (l := l) f0 hZ f1 hA f2 f3 k3 sF sR (by omega) (by omega) F
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (by
      under_wires
      exact B.by_look2)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (B.snd_mem)
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }).cast (by omega) (by omega)

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d9 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith))
    {Qs : List (XThread Arith)} {WQ : Nat}
    (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨X, ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩ ::
      (Qs ++ [⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (10 * (m' + 1) + 6 * (n' + 1) + 18) + WQ) :=
  ((race_e_d9 B l).total hQ).cast (by omega)

/-- **The one alignment in which the first thread keeps the last pair, with
any number of threads reading between the two**: the last thread takes the
zero, the first the adder; the last does not find the adder and puts the
zero back, and the first takes it.  The last thread then passes the zero of
the second argument and finds its successors gone.  The five actions of the
race, and what the two threads still do after it. -/
theorem race_e_d8 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) {tops : List (Id × Arith)}
    (ht : Tops (n' + 1) tops) (ht1 : 1 ≤ tops.length) :
    RaceEnd (m' + 1) (n' + 1) X ⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩
      ⟨([3], .zero) :: tops, .ready [2] [0, n' + 1 + 4] .zero .add⟩
      (5 * (m' + 1) + 3 * (n' + 1) + 10 + 1) tops.length := by
  have hA8 : ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents =
      (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) := by
    show List.filter (fun e => decide (e.1 ≠ [2])) (([2], Arith.zero) ::
      (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4]))) = _
    rw [List.filter_cons_of_neg (by simp),
      filter_ne_comm (X.agents.filter fun e => decide (e.1 ≠ [2])) [0, n' + 1 + 4] [2],
      filter_ne_idem]
  have F8 := B.final hA8 rfl
  have S := snd_sum (m' + 1 + 1) (n' + 1)
  have f0 : XMach.act xsys X ⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (X, ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩, 0) :=
    XMach.act_seek_found (c := ([2], 0)) ((ite_pos' rfl).trans B.zero) ⟨by ports_differ, rfl⟩
  have r0 : XMach.act xsys X ⟨(([3], .zero) :: tops), .ready [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((X.takeAgent [2]), ⟨(([3], .zero) :: tops), .half [2] [0, n' + 1 + 4] .zero .add⟩, 0) := XMach.act_ready B.zero
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩, 0) := XMach.act_ready B.adder1
  have gA : assoc [0, n' + 1 + 4] ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] ((X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have r1 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨(([3], .zero) :: tops), .half [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero), ⟨(([3], .zero) :: tops), .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gA] at h1
      cases h1)
  have hZ3 : assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).agents = some Arith.zero := by
    show (if ([2] : Id) = [2] then some Arith.zero else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero) ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 1) :=
    XMach.act_half (R := addZero.toX) (by
      rw [ite_pos' (show assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).agents = some Arith.zero ∧
        ([0, n' + 1 + 4] : Id) ≠ [2] from ⟨hZ3, by ports_differ⟩)]
      rfl)
  have h3 : assoc [3] ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).agents = some Arith.zero :=
    F8.agent (e := ([3], Arith.zero)) (by
      rw [F8.agents]
      exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self))
  have r2 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨(([3], .zero) :: tops), .idle⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨tops, .look [3] .zero⟩, 0) := XMach.act_idle_pos (e := ([3], Arith.zero)) h3
  have f3 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨rest, .write [] [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 0) := rfl
  have hl6 : assoc (([3], 0) : Port) ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).wires) = some ([4], 1) :=
    assoc_eq_of_unique ((F8.up S (j := 3) (by omega) (by omega) _).2 rfl)
      (fun q' hq => (F8.up S (j := 3) (by omega) (by omega) q').1 hq)
  rw [assoc_cons_ne _ (by ports_differ)] at hl6
  have r3 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨tops, .look [3] .zero⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨tops, .seek [3] .zero ([3], 0) ([4], 1)⟩, 0) := XMach.act_look hl6
  have f4 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨rest, .write [] [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨rest, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨tops, .seek [3] .zero ([3], 0) ([4], 1)⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨tops, .idle⟩, 0) :=
    XMach.act_seek_stop rfl (nextSeg_none fun q hq =>
      (F8.down S (j := 3) (by omega) (by omega) q).1 hq)
  have f5 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨rest, .write [] []⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have V8 : RaceViews (n' + 1) X ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2])
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) :=
    { zero0 := (by
      first | exact B.zero | exact hZ)
      look2_0 := (by
      under_wires
      exact B.by_look2)
      look2_1 := (by
      under_wires
      exact B.by_look2)
      seek2_1 := (by
      under_wires
      exact B.by_seek2)
      seek2_2 := (by
      under_wires
      exact B.by_seek2)
      goneA_2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      goneA_3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      stopA_2 := (by
      under_wires
      exact B.by_stopA)
      stopA_3 := (by
      under_wires
      exact B.by_stopA)
      snd0 := (B.snd_mem)
      sub01 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub12 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub23 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      sub34 := (fun e he => by
      first | exact he | exact List.mem_cons_of_mem _ he |
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      m0 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m1 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m2 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m3 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      m4 := (⟨by
        under_agents
        exact B.by_three, fun j h4 hj => by
        under_agents
        exact B.by_succ j h4 hj, by
        under_agents
        exact B.by_one⟩)
      two1 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two2 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two3 := (by
      under_agents
      exact assoc_takeAgent_self _ _)
      two4 := (by
      under_agents
      exact assoc_takeAgent_self _ _) }
  have sF := F8.pass_stays S (sum_fresh (m' + 1 + 1) (n' + 1))
  exact ⟨X, ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]),
    (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)),
    ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨rest, .write [] []⟩, ⟨tops, .idle⟩, V8, F8,
    fun Qs Qs' rows => by
      obtain ⟨L1, L2, L3, L4, q0, q1, q2, q3, q4⟩ := rows.rows
      exact .step f0 q0 r0 .nil (.step f1 q1 r1 .nil (.step f2 q2 r2 .nil (.step f3 q3 r3 .nil
        (.step f4 q4 r4 .nil (.refl _))))),
    Stays.step (fun h => by
      injection h with _ h2
      cases h2) f5 sF, F8.tops_stays tops ht, by omega, ht1⟩

/-- The work of the run in that case: threads in turn, to the end. -/
theorem race_k_d8 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) {tops : List (Id × Arith)}
    (ht : Tops (n' + 1) tops) (ht1 : 1 ≤ tops.length)
    {Qs : List (XThread Arith)} {WQ : Nat} (hQ : Beside (m' + 1) (n' + 1) Qs WQ) :
    (⟨X, ⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ ::
      (Qs ++ [⟨([3], .zero) :: tops, .ready [2] [0, n' + 1 + 4] .zero .add⟩])⟩ :
      XMach Arith).Total xsys (fun i => i % (Qs.length + 2))
      ((Qs.length + 2) * 5 + (5 * (m' + 1) + 3 * (n' + 1) + 11 + (WQ + tops.length))) :=
  ((race_e_d8 B ht ht1).total hQ).cast (by omega)

end Arith

end INet
