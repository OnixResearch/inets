import InteractionNets.Arith.ManyThreads

/-! ### The rounds of threads in turn on an addition -/

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

/-- `Rounds c M R`: the `c` threads of `M`, acting in turn, are all at rest
after `R` rounds, and not after fewer. -/
def Rounds (c : Nat) (M : XMach Arith) (R : Nat) : Prop :=
  (M.trace xsys (fun i => i % c) (c * R)).1.resting = true ∧
    ∀ R', R' < R → ¬ (M.trace xsys (fun i => i % c) (c * R')).1.resting = true

theorem Rounds.cast {c : Nat} {M : XMach Arith} {R R' : Nat} (h : Rounds c M R) (e : R = R') :
    Rounds c M R' := by
  subst e
  exact h

/-- A run takes one number of rounds. -/
theorem Rounds.unique {c : Nat} {M : XMach Arith} {R R' : Nat} (h : Rounds c M R)
    (h' : Rounds c M R') : R = R' := by
  have a : ¬ R < R' := fun lt => h'.2 R lt h.1
  have b : ¬ R' < R := fun lt => h.2 R' lt h'.1
  omega

/-- A run that is at rest after `N` actions has made all its work by then,
one action at most at a time. -/
theorem total_le_rest {c : Nat} {M : XMach Arith} {W N : Nat}
    (t : M.Total xsys (fun i => i % c) W)
    (h : (M.trace xsys (fun i => i % c) N).1.resting = true) : W ≤ N := by
  obtain ⟨N0, hN0⟩ := t
  have e := XMach.work_rest (xs := xsys) (fun i => i % c) h N0
  have e2 := hN0 (N + N0) (by omega)
  have le := XMach.work_le_count xsys (fun i => i % c) M N
  omega

theorem all_rest_resting {Y : XNet Arith} {Ts : List (XThread Arith)}
    (h : ∀ T, T ∈ Ts → T = ⟨[], .idle⟩) : (⟨Y, Ts⟩ : XMach Arith).resting = true :=
  List.all_eq_true.2 fun T hT => by
    rw [h T hT]
    rfl

theorem first_of_resting {Y : XNet Arith} {T : XThread Arith} {Ts : List (XThread Arith)}
    (h : (⟨Y, T :: Ts⟩ : XMach Arith).resting = true) : T = ⟨[], .idle⟩ :=
  XThread.eq_rest (List.all_eq_true.1 h T List.mem_cons_self)

/-- **The rounds of a run in which every thread but the first only reads.**
If the first thread alone is at rest after `A + 1` actions and not after
`A`, and the others, which leave the memory as it is, are at rest by then,
the run of all of them in turn takes exactly `A + 1` rounds. -/
theorem rounds_readers {X : XNet Arith} {T₀ : XThread Arith} {Ts : List (XThread Arith)}
    {A : Nat}
    (h : ∀ T, T ∈ Ts → ∀ a,
      (XMach.act xsys (XMach.solo xsys X T₀ (a + 1)).1 (XMach.reader xsys X T₀ T a)).1 =
          (XMach.solo xsys X T₀ (a + 1)).1 ∧
        (XMach.act xsys (XMach.solo xsys X T₀ (a + 1)).1 (XMach.reader xsys X T₀ T a)).2.2 = 0)
    (h0 : (XMach.solo xsys X T₀ A).2 ≠ ⟨[], .idle⟩)
    (h1 : (XMach.solo xsys X T₀ (A + 1)).2 = ⟨[], .idle⟩)
    (hr : ∀ T, T ∈ Ts → XMach.reader xsys X T₀ T (A + 1) = ⟨[], .idle⟩) :
    Rounds (Ts.length + 1) ⟨X, T₀ :: Ts⟩ (A + 1) := by
  have tr : ∀ a, ((⟨X, T₀ :: Ts⟩ : XMach Arith).trace xsys (fun i => i % (Ts.length + 1))
      ((Ts.length + 1) * a)).1 = ⟨(XMach.solo xsys X T₀ a).1, (XMach.solo xsys X T₀ a).2 ::
        Ts.map fun T => XMach.reader xsys X T₀ T a⟩ := fun a =>
    congrArg Prod.fst (XMach.trace_readers (xs := xsys) (A := a)
      (fun T hT a' _ => h T hT a') a (Nat.le_refl a))
  refine ⟨?_, fun R' hR' hrest => ?_⟩
  · rw [tr]
    exact all_rest_resting fun T hT => by
      rcases List.mem_cons.1 hT with e | hT
      · rw [e]
        exact h1
      · obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hT
        exact hr T' hT'
  · obtain ⟨d, rfl⟩ : ∃ d, A = R' + d := ⟨A - R', by omega⟩
    have h2 := XMach.resting_trace (xs := xsys) (fun i => i % (Ts.length + 1)) hrest
      ((Ts.length + 1) * d)
    rw [← Nat.mul_add, tr] at h2
    exact h0 (first_of_resting h2)

/-- Outside the race the thread numbered `t + 1` only reads and is at rest
after `turnRest m n t` actions. -/
theorem turn_reader_rest (m n t : Nat) (ht : t + 2 ≤ m)
    (hw : turnAt m n t ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n t)
    (hk : 20 * t ≤ 3 * m + 3 * n + 1) :
    RdAt m n ⟨(sum (m + 1) n).agents.drop (t + 1) ++ (sum (m + 1) n).agents.take (t + 1),
      .idle⟩ (turnRest m n t) ⟨[], .idle⟩ := by
  cases n with
  | zero =>
    obtain ⟨b, eb, r, -⟩ := turn_reader_zero m t ht (by omega)
    rw [turn_list_zero m t (by omega), eb]
    exact r
  | succ n' =>
    obtain ⟨b, eb, r, -⟩ := turn_reader_quiet m n' t ht hw (by
      unfold turnAt
      omega)
    rw [turn_list_succ m n' t (by omega), eb]
    exact r

/-- **Threads in turn outside the race take the rounds of one thread.**  On
the net for `(m + 1) + n` take `k + 1` threads that act in turn, with
`k + 1 ≤ m` and `20 * k ≤ 3 * m + 3 * n + 21`.  If none of the threads after
the first comes to the zero of the first argument at one of the ten moments
of the race, all are at rest after exactly `soloWork (m + 1) n` rounds, the
number of actions one thread alone needs: the others save no time. -/
theorem threads_rounds (m n k : Nat) (hm : k + 1 ≤ m) (hk : 20 * k ≤ 3 * m + 3 * n + 21)
    (hw : ∀ t, t < k → turnAt m n t ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n t) :
    Rounds (k + 1) (XMach.init (sum (m + 1) n) (k + 1)) (soloWork (m + 1) n) := by
  rw [XMach.init_succ]
  obtain ⟨hr, -, hb⟩ := solo_work (m + 1) n
  rw [XMach.init_one] at hr hb
  obtain ⟨A, hA⟩ : ∃ A, soloWork (m + 1) n = A + 1 := ⟨soloWork (m + 1) n - 1, by
    rw [soloWork_succ]
    omega⟩
  have s0 : (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ A).2 ≠
      ⟨[], .idle⟩ := fun e => by
    have h := hb A (by omega)
    rw [XMach.trace_one] at h
    exact h (all_rest_resting fun T hT => by
      rcases List.mem_cons.1 hT with e' | hT
      · rw [e']
        exact e
      · cases hT)
  have s1 : (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (A + 1)).2 =
      ⟨[], .idle⟩ := by
    rw [hA, XMach.trace_one] at hr
    exact XMach.resting_single hr
  have rd : ∀ T, T ∈ ((List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)) →
      RdAt m n T (A + 1) ⟨[], .idle⟩ := by
    intro T hT
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT
    have ht' : t < k := List.mem_range.1 ht
    have r := turn_reader_rest m n t (by omega) (hw t ht') (by omega)
    have tb := (turnRest_bounds m n t (by omega)).2
    obtain ⟨d, hd⟩ : ∃ d, A + 1 = turnRest m n t + d := ⟨A + 1 - turnRest m n t, by omega⟩
    rw [hd]
    exact r.rest d
  have res := rounds_readers (X := sum (m + 1) n) (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩)
    (Ts := (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)) (A := A)
    (fun T hT a => ((rd T hT).rest (a + 1)).2 a (by omega)) s0 s1 (fun T hT => (rd T hT).1)
  rw [List.length_map, List.length_range] at res
  rw [hA]
  exact res

/-- The same, the condition read off `racerOf`. -/
theorem threads_rounds_none (m n k : Nat) (hm : k + 1 ≤ m) (hk : 20 * k ≤ 3 * m + 3 * n + 21)
    (h : racerOf m n k = none) :
    Rounds (k + 1) (XMach.init (sum (m + 1) n) (k + 1)) (soloWork (m + 1) n) :=
  threads_rounds m n k hm hk fun t ht => by
    have g := racerOf_none k h t ht
    omega

/-- **Outside the race more threads are pure overhead**: the run takes the
rounds of one thread alone, and its work is that of one thread and the
actions of the others. -/
theorem threads_overhead (m n k : Nat) (hm : k + 1 ≤ m) (hk : 20 * k ≤ 3 * m + 3 * n + 21)
    (h : racerOf m n k = none) :
    Rounds (k + 1) (XMach.init (sum (m + 1) n) (k + 1)) (soloWork (m + 1) n) ∧
      (XMach.init (sum (m + 1) n) (k + 1)).Total xsys (fun i => i % (k + 1))
        (soloWork (m + 1) n + turnSum m n k) :=
  ⟨threads_rounds_none m n k hm hk h, threads_total m n k hm hk fun t ht => by
    have g := racerOf_none k h t ht
    omega⟩

/-- In every case the rounds are at least the work shared among the
threads. -/
theorem threads_rounds_ge (m n k R : Nat) (hm4 : 4 ≤ m) (hm : k + 1 ≤ m)
    (hn : 20 * k ≤ 3 * m + 3 * n + 21)
    (h : Rounds (k + 1) (XMach.init (sum (m + 1) n) (k + 1)) R) :
    allWork m n k ≤ (k + 1) * R :=
  total_le_rest (threads_exact m n k hm4 hm hn) h.1

/-- **Two threads in the race end at most nine rounds sooner than one**,
when the first thread does not keep the pair. -/
theorem two_threads_rounds_ge (m n R : Nat) (hm : 4 ≤ m)
    (h1 : 17 * m + 7 ≤ turnAt m n 0) (h2 : turnAt m n 0 ≤ 17 * m + 16)
    (h8 : turnAt m n 0 ≠ 17 * m + 15)
    (h : Rounds 2 (XMach.init (sum (m + 1) n) 2) R) : soloWork (m + 1) n ≤ R + 9 := by
  have e : twoAt m n = turnAt m n 0 := rfl
  have le := total_le_rest (two_threads_race_at m n hm h1 h2) h.1
  rw [soloWork_succ]
  rcases raceWork_cases m n (twoAt m n - (17 * m + 7)) with ⟨e8, -⟩ | ⟨-, lo, -⟩
  · omega
  · omega

example : Rounds 3 (XMach.init (sum 8 28) 3) 273 :=
  (threads_rounds_none 7 28 2 (by decide) (by decide) (by decide)).cast (by decide)

example : Rounds 5 (XMach.init (sum 9 34) 5) 313 :=
  (threads_rounds_none 8 34 4 (by decide) (by decide) (by decide)).cast (by decide)

/-- **The rounds of threads that only read.**  If each thread of `Ts` only
reads in the memory `Y` and comes to rest in `K` actions at most, and one
of them in exactly `K`, all of them in turn are at rest after `K` rounds
and not after fewer. -/
theorem rounds_stays {Y : XNet Arith} {Ts : List (XThread Arith)} {K : Nat}
    (hs : ∀ T, T ∈ Ts → ∃ k, k ≤ K ∧ Stays xsys Y T ⟨[], .idle⟩ k)
    (hK : ∃ T, T ∈ Ts ∧ Stays xsys Y T ⟨[], .idle⟩ K) :
    Rounds Ts.length ⟨Y, Ts⟩ K := by
  have hR : ∀ T, T ∈ Ts → T.Reads xsys Y := fun T hT => by
    obtain ⟨k, -, s⟩ := hs T hT
    exact (s.after rfl).1
  have tr : ∀ i (t : Nat) (T : XThread Arith), Ts[t]? = some T →
      ((⟨Y, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) i).1.ths[t]? =
        some (T.after xsys Y (hits (fun i => i % Ts.length) t i)) := fun i =>
    (XMach.trace_reads (xs := xsys) (M := ⟨Y, Ts⟩) (fun i => i % Ts.length) hR i).2.2
  have ln : ∀ i, ((⟨Y, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) i).1.ths.length =
      Ts.length := fun i =>
    (XMach.trace_reads (xs := xsys) (M := ⟨Y, Ts⟩) (fun i => i % Ts.length) hR i).2.1
  refine ⟨?_, fun R' hR' hrest => ?_⟩
  · refine List.all_eq_true.2 fun T' hT' => ?_
    obtain ⟨t, e⟩ := List.mem_iff_getElem?.1 hT'
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 e
    rw [ln] at hlt
    obtain ⟨T, hT⟩ : ∃ T, Ts[t]? = some T := ⟨Ts[t], List.getElem?_eq_getElem hlt⟩
    have e2 := tr (Ts.length * K) t T hT
    rw [hits_mod Ts.length t hlt K] at e2
    obtain ⟨k, hk, s⟩ := hs T (List.mem_of_getElem? hT)
    have e3 : T' = ⟨[], .idle⟩ := by
      have e4 := Option.some.inj (e.symm.trans e2)
      rw [e4]
      exact (s.after rfl).2.2 K hk
    rw [e3]
    rfl
  · obtain ⟨T, hT, s⟩ := hK
    obtain ⟨t, e⟩ := List.mem_iff_getElem?.1 hT
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 e
    have e2 := tr (Ts.length * R') t T e
    rw [hits_mod Ts.length t hlt R'] at e2
    exact (s.after rfl).2.1 R' hR'
      (XThread.eq_rest (List.all_eq_true.1 hrest _ (List.mem_of_getElem? e2)))

/-- The rounds of a run, in two parts. -/
theorem rounds_after (c : Nat) {M M' : XMach Arith} {E R : Nat}
    (h : (M.trace xsys (fun i => i % c) (c * E)).1 = M') (hR : Rounds c M' R) (R1 : 1 ≤ R) :
    Rounds c M (E + R) := by
  subst h
  refine ⟨?_, fun R' hR' hrest => ?_⟩
  · rw [trace_mod_add]
    exact hR.1
  · obtain ⟨d, hd⟩ : ∃ d, E + (R - 1) = R' + d := ⟨E + (R - 1) - R', by omega⟩
    have h2 := XMach.resting_trace (xs := xsys) (fun i => i % c) hrest (c * d)
    rw [← Nat.mul_add, ← hd, trace_mod_add] at h2
    exact hR.2 (R - 1) (by omega) h2

/-- **The rounds of a run that ends with every thread reading**: `w`
rounds to a memory in which each thread only reads, then the rounds of the
thread that reads longest. -/
theorem rounds_sweepsK {M : XMach Arith} {Y : XNet Arith} {Ts : List (XThread Arith)}
    {w K : Nat} (s : SweepsK M ⟨Y, Ts⟩ w)
    (hs : ∀ T, T ∈ Ts → ∃ k, k ≤ K ∧ Stays xsys Y T ⟨[], .idle⟩ k)
    (hK : ∃ T, T ∈ Ts ∧ Stays xsys Y T ⟨[], .idle⟩ K) (K1 : 1 ≤ K) :
    Rounds M.ths.length M (w + K) := by
  have hl : Ts.length = M.ths.length := s.len
  have r := rounds_stays hs hK
  rw [hl] at r
  exact rounds_after M.ths.length s.trace r K1

/-- **The rounds of two threads from the race on**: five rounds, then those
of the thread that still has more to do. -/
theorem RaceEnd.rounds_two {m n : Nat} {M0 : XNet Arith} {F0 R0 : XThread Arith}
    {kF kR K : Nat} (h : RaceEnd m n M0 F0 R0 kF kR) (hF : kF ≤ K) (hR : kR ≤ K)
    (hK : kF = K ∨ kR = K) : Rounds 2 ⟨M0, [F0, R0]⟩ (5 + K) := by
  obtain ⟨Y0, Y1, Y2, Y3, Y4, F5, R5, -, -, sw, sF, sR, h1F, -⟩ := h
  have s : SweepsK ⟨M0, [F0, R0]⟩ ⟨Y4, [F5, R5]⟩ 5 := sw [] [] .nil
  exact rounds_sweepsK s
    (fun T hT => by
      rcases List.mem_cons.1 hT with e | hT
      · rw [e]
        exact ⟨kF, hF, sF⟩
      · rcases List.mem_cons.1 hT with e | hT
        · rw [e]
          exact ⟨kR, hR, sR⟩
        · cases hT)
    (by
      rcases hK with e | e
      · exact ⟨F5, List.mem_cons_self, by
          rw [← e]
          exact sF⟩
      · exact ⟨R5, List.mem_cons_of_mem _ List.mem_cons_self, by
          rw [← e]
          exact sR⟩)
    (by omega)

/-- The rounds a race saves two threads, by the moment the second thread
comes to the zero of the first argument. -/
def raceSave : Nat → Nat
  | 0 => 9
  | 1 => 8
  | 2 => 7
  | 3 => 6
  | 4 => 4
  | 5 => 4
  | 6 => 3
  | 7 => 2
  | _ => 0

/-- From the entry to the race to the rest of both threads. -/
theorem rounds_close {m n aE c R : Nat} {X : XNet Arith} {T Rr : XThread Arith}
    (htr : (XMach.init (sum (m + 1) n) 2).trace xsys (fun i => i % 2) (2 * aE) =
      (⟨(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE).1,
        [(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE).2, Rr]⟩, c))
    (hs : XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE = (X, T))
    (hE : Rounds 2 (⟨X, [T, Rr]⟩ : XMach Arith) R) (R1 : 1 ≤ R) :
    Rounds 2 (XMach.init (sum (m + 1) n) 2) (aE + R) := by
  rw [hs] at htr
  exact rounds_after 2 (congrArg Prod.fst htr) hE R1

/-- **Two threads in the race, the rounds to the action.**  On the net for
`(m + 1) + n`, with `m` from four on: when the second thread comes to the
zero of the first argument after `17 * m + 7 + d` actions, `d` up to nine,
both threads are at rest after `raceSave d` rounds fewer than the actions
one thread alone needs, and not sooner. -/
theorem two_threads_race_rounds (m n : Nat) (hm : 4 ≤ m) (h1 : 17 * m + 7 ≤ turnAt m n 0)
    (h2 : turnAt m n 0 ≤ 17 * m + 16) :
    Rounds 2 (XMach.init (sum (m + 1) n) 2)
      (soloWork (m + 1) n - raceSave (turnAt m n 0 - (17 * m + 7))) := by
  have h1' : 17 * m + 7 ≤ twoAt m n := h1
  have h2' : twoAt m n ≤ 17 * m + 16 := h2
  show Rounds 2 (XMach.init (sum (m + 1) n) 2)
    (soloWork (m + 1) n - raceSave (twoAt m n - (17 * m + 7)))
  rw [soloWork_succ]
  unfold twoAt at h1' h2' ⊢
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, (3 * (m' + 1) + 11) / 16 = K + 1 :=
    ⟨(3 * (m' + 1) + 11) / 16 - 1, by omega⟩
  rw [hK] at h1' h2' ⊢
  obtain ⟨c, htr⟩ := two_entry_exact (m' + 1) n' K hm (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨V, todo, rest, p5, q5, p6, q6, p7, q7, p8, q8, B, s11, s12, s13, s14, s15⟩ :=
    race_write (m' + 1) (n' + 1) (by omega)
  obtain ⟨s16, s17, s18, s19, s20⟩ := B.states
  have lk12 := solo_look_two (m' + 1) (n' + 1) (17 * (m' + 1) + 12)
  rw [s12] at lk12
  have lk13 := solo_look_two (m' + 1) (n' + 1) (17 * (m' + 1) + 13)
  rw [s13] at lk13
  have lk14 := solo_look_two (m' + 1) (n' + 1) (17 * (m' + 1) + 14)
  rw [s14] at lk14
  have sk13 := (solo_seek_two (m' + 1) (n' + 1) (by omega) (17 * (m' + 1) + 13)).1 (by omega)
  rw [s13] at sk13
  have sk14 := (solo_seek_two (m' + 1) (n' + 1) (by omega) (17 * (m' + 1) + 14)).1 (by omega)
  rw [s14] at sk14
  have hS11 : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 →
      ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires := fun j a b => by
    have h := assoc_mem (solo_look_snd (m' + 1) (n' + 1) (j := j) a b (17 * (m' + 1) + 11)).1
    rw [s11] at h
    exact h
  have hS12 : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 →
      ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ (V.putLink p5 q5).wires := fun j a b => by
    have h := assoc_mem (solo_look_snd (m' + 1) (n' + 1) (j := j) a b (17 * (m' + 1) + 12)).1
    rw [s12] at h
    exact h
  have hS13 : ∀ j, 3 ≤ j → j ≤ n' + 1 + 2 →
      ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ ((V.putLink p5 q5).putLink p6 q6).wires :=
    fun j a b => by
      have h := assoc_mem (solo_look_snd (m' + 1) (n' + 1) (j := j) a b (17 * (m' + 1) + 13)).1
      rw [s13] at h
      exact h
  have ht : Tops (n' + 1) [([n' + 1 + 3 + (m' + 1) + 1], Arith.succ)] := fun e he => by
    rw [List.mem_singleton.1 he]
    exact ⟨n' + 1 + 3 + (m' + 1) + 1, by omega, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, 3 * (m' + 1) + 3 * n' + 5 + K = 17 * (m' + 1) + 7 + d :=
    ⟨3 * (m' + 1) + 3 * n' + 5 + K - (17 * (m' + 1) + 7), by omega⟩
  have e0 : 3 * (m' + 1) + 3 * (n' + 1) + 1 + (K + 1) - (17 * (m' + 1) + 7) = d := by omega
  rw [e0]
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
      d = 9 := by omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (rounds_close htr (solo_at s11 (by omega))
      ((race_e_d0 B todo _ lk12 lk13 sk13 sk14 hS11).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 9
        omega)
  · exact (rounds_close htr (solo_at s12 (by omega))
      ((race_e_d1 B todo _ lk13 lk14 sk14 hS12).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 8
        omega)
  · exact (rounds_close htr (solo_at s13 (by omega))
      ((race_e_d2 B todo _ lk14 hS13).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 7
        omega)
  · exact (rounds_close htr (solo_at s14 (by omega))
      ((race_e_d3 B todo _).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 6
        omega)
  · exact (rounds_close htr (solo_at s15 (by omega))
      ((race_e_d4 B todo _).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 11) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 4
        omega)
  · exact (rounds_close htr (solo_at s16 (by omega))
      ((race_e_d5 B _).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 4
        omega)
  · exact (rounds_close htr (solo_at s17 (by omega))
      ((race_e_d6 B _).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 3
        omega)
  · exact (rounds_close htr (solo_at s18 (by omega))
      ((race_e_d7 B _).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 2
        omega)
  · exact (rounds_close htr (solo_at s19 (by omega))
      (((race_e_d8 B ht (Nat.le_refl 1)).cast
          (kF' := 5 * (m' + 1) + 3 * (n' + 1) + 11) (kR' := 1) (by omega) rfl).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 11) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 0
        omega)
  · exact (rounds_close htr (solo_at s20 (by omega))
      ((race_e_d9 B _).rounds_two
        (K := 5 * (m' + 1) + 3 * (n' + 1) + 10) (by omega) (by omega) (by omega))
      (by omega)).cast (by
        show _ = 22 * (m' + 1 + 1) + 3 * (n' + 1) + 13 - 0
        omega)

/-- The rounds of two threads in turn on the net for `(m + 1) + n`: those
of one thread, less what the race saves when there is one. -/
def twoRounds (m n : Nat) : Nat :=
  if 17 * m + 7 ≤ turnAt m n 0 ∧ turnAt m n 0 ≤ 17 * m + 16 then
    soloWork (m + 1) n - raceSave (turnAt m n 0 - (17 * m + 7))
  else soloWork (m + 1) n

/-- **Two threads in turn, every size, the rounds to the action.**  On the
net for `(m + 1) + n`, with `m` from four on, two threads acting in turn
are at rest after exactly `twoRounds m n` rounds. -/
theorem two_threads_rounds (m n : Nat) (hm : 4 ≤ m) :
    Rounds 2 (XMach.init (sum (m + 1) n) 2) (twoRounds m n) := by
  unfold twoRounds
  by_cases hW : 17 * m + 7 ≤ turnAt m n 0 ∧ turnAt m n 0 ≤ 17 * m + 16
  · rw [ite_pos' hW]
    exact two_threads_race_rounds m n hm hW.1 hW.2
  · rw [ite_neg' hW]
    exact threads_rounds m n 1 (by omega) (by omega) fun t ht => by
      have e : t = 0 := by omega
      subst e
      omega

theorem raceSave_le (d : Nat) : raceSave d ≤ 9 := by
  unfold raceSave
  split <;> omega

/-- **A second thread saves nine rounds at most, and costs none.**  On the
net for `(m + 1) + n`, with `m` from four on, two threads in turn are at
rest after `R` rounds with `R` at most the actions of one thread alone and
at least nine fewer. -/
theorem two_threads_rounds_bounds (m n : Nat) (hm : 4 ≤ m) :
    ∃ R, Rounds 2 (XMach.init (sum (m + 1) n) 2) R ∧ R ≤ soloWork (m + 1) n ∧
      soloWork (m + 1) n ≤ R + 9 := by
  refine ⟨twoRounds m n, two_threads_rounds m n hm, ?_, ?_⟩
  · unfold twoRounds
    by_cases hW : 17 * m + 7 ≤ turnAt m n 0 ∧ turnAt m n 0 ≤ 17 * m + 16
    · rw [ite_pos' hW]
      omega
    · rw [ite_neg' hW]
      omega
  · unfold twoRounds
    by_cases hW : 17 * m + 7 ≤ turnAt m n 0 ∧ turnAt m n 0 ≤ 17 * m + 16
    · rw [ite_pos' hW]
      have s := raceSave_le (turnAt m n 0 - (17 * m + 7))
      omega
    · rw [ite_neg' hW]
      omega

example : Rounds 2 (XMach.init (sum 6 25) 2) 211 :=
  (two_threads_rounds 5 25 (by decide)).cast (by decide)

example : Rounds 2 (XMach.init (sum 6 26) 2) 217 :=
  (two_threads_rounds 5 26 (by decide)).cast (by decide)

example : Rounds 2 (XMach.init (sum 6 28) 2) 229 :=
  (two_threads_rounds 5 28 (by decide)).cast (by decide)

example : Rounds 2 (XMach.init (sum 10 46) 2) 371 :=
  (two_threads_rounds 9 46 (by decide)).cast (by decide)

example : soloWork 6 25 = 220 := by decide

/-- **One more thread at the end that only reads and is at rest in time
leaves the rounds of the run as they are.** -/
theorem rounds_beside_end {X : XNet Arith} {Ts : List (XThread Arith)}
    (s : Nat → XThread Arith)
    (hs : ∀ w, XMach.act xsys
        ((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * (w + 1))).1.mem
        (s w) =
      (((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * (w + 1))).1.mem,
        s (w + 1), 0))
    {R b : Nat} (rd : Rounds Ts.length ⟨X, Ts⟩ R)
    (h0 : ∀ j, b ≤ j → s j = ⟨[], .idle⟩) (hb : b ≤ R) :
    Rounds (Ts.length + 1) ⟨X, Ts ++ [s 0]⟩ R := by
  have q := beside_end s hs
  refine ⟨?_, fun R' hR' hrest => ?_⟩
  · rw [(q R).1]
    refine List.all_eq_true.2 fun T hT => ?_
    rcases List.mem_append.1 hT with hT | hT
    · exact List.all_eq_true.1 rd.1 T hT
    · rw [List.mem_singleton.1 hT, h0 R hb]
      rfl
  · rw [(q R').1] at hrest
    exact rd.2 R' hR' (List.all_eq_true.2 fun T hT =>
      List.all_eq_true.1 hrest T (List.mem_append_left _ hT))

/-- The same for the threads of a program. -/
theorem init_rounds_end (X : XNet Arith) (k : Nat) (s : Nat → XThread Arith)
    (e0 : s 0 = ⟨X.agents.drop (k + 1) ++ X.agents.take (k + 1), .idle⟩)
    (hs : ∀ w, XMach.act xsys
        ((XMach.init X (k + 1)).trace xsys (fun i => i % (k + 1)) ((k + 1) * (w + 1))).1.mem
        (s w) =
      (((XMach.init X (k + 1)).trace xsys (fun i => i % (k + 1)) ((k + 1) * (w + 1))).1.mem,
        s (w + 1), 0))
    {R b : Nat} (rd : Rounds (k + 1) (XMach.init X (k + 1)) R)
    (h0 : ∀ j, b ≤ j → s j = ⟨[], .idle⟩) (hb : b ≤ R) :
    Rounds (k + 1 + 1) (XMach.init X (k + 1 + 1)) R := by
  have hl : (XMach.init X (k + 1)).ths.length = k + 1 := init_len X (k + 1)
  have hmem : (XMach.init X (k + 1)).mem = X := rfl
  rw [init_snoc, ← e0]
  generalize XMach.init X (k + 1) = M at hs rd hl hmem ⊢
  obtain ⟨Y, Ts⟩ := M
  have hY : Y = X := hmem
  subst hY
  have hl' : Ts.length = k + 1 := hl
  rw [← hl'] at hs rd ⊢
  exact rounds_beside_end s hs rd h0 hb

/-- **A thread that passes the zero of the first argument before the race
leaves the rounds as they are**, when the run goes on long enough for it
to come to rest. -/
theorem threads_early_last_rounds (m n' k R : Nat) (hm : k + 2 ≤ m)
    (hA : turnAt m (n' + 1) k ≤ 17 * m + 6) (hG : 17 * k ≤ turnAt m (n' + 1) k + 1)
    (hR : turnAt m (n' + 1) k + 3 + 3 + (k + 1) ≤ R)
    (rd : Rounds (k + 1) (XMach.init (sum (m + 1) (n' + 1)) (k + 1)) R) :
    Rounds (k + 1 + 1) (XMach.init (sum (m + 1) (n' + 1)) (k + 1 + 1)) R := by
  obtain ⟨s, e0, hs, -, h0⟩ := early_reader_end m n' k hm hA hG
  exact init_rounds_end (sum (m + 1) (n' + 1)) k s e0 hs rd h0 hR

/-- So do any number of such threads. -/
theorem threads_early_many_rounds (m n' j R : Nat) (hA : turnAt m (n' + 1) j ≤ 17 * m + 6)
    (hR : turnAt m (n' + 1) j + j + 7 ≤ R)
    (rd : Rounds (j + 1) (XMach.init (sum (m + 1) (n' + 1)) (j + 1)) R) :
    ∀ k, j + k + 1 ≤ m → 20 * (j + k) ≤ 3 * m + 3 * (n' + 1) + 23 →
      Rounds (j + k + 1) (XMach.init (sum (m + 1) (n' + 1)) (j + k + 1)) R
  | 0, _, _ => rd
  | k + 1, hm, hk => by
    have ih := threads_early_many_rounds m n' j R hA hR rd k (by omega) (by omega)
    exact threads_early_last_rounds m n' (j + k) R (by omega)
      (by
        unfold turnAt at hA ⊢
        omega)
      (by
        unfold turnAt
        omega)
      (by
        unfold turnAt at hR ⊢
        omega) ih

/-- The same, if there are any. -/
theorem threads_early_opt_rounds (m n' j R : Nat)
    (rd : Rounds (j + 1) (XMach.init (sum (m + 1) (n' + 1)) (j + 1)) R) :
    ∀ k, (1 ≤ k → turnAt m (n' + 1) j ≤ 17 * m + 6 ∧ turnAt m (n' + 1) j + j + 7 ≤ R) →
      j + k + 1 ≤ m → 20 * (j + k) ≤ 3 * m + 3 * (n' + 1) + 23 →
      Rounds (j + k + 1) (XMach.init (sum (m + 1) (n' + 1)) (j + k + 1)) R
  | 0, _, _, _ => rd
  | k + 1, hA, hm, hk =>
    threads_early_many_rounds m n' j R (hA (Nat.succ_pos k)).1 (hA (Nat.succ_pos k)).2 rd
      (k + 1) hm hk

/-- `BesideBy m n Qs B`: beside a race for the last pair, each thread of
`Qs` only reads and comes to rest in `B` actions at most after it. -/
def BesideBy (m n : Nat) (Qs : List (XThread Arith)) (B : Nat) : Prop :=
  ∀ Q, Q ∈ Qs → ∃ k, k ≤ B ∧ Beside1 m n Q k

theorem BesideBy.mono {m n : Nat} {Qs : List (XThread Arith)} {B B' : Nat}
    (h : BesideBy m n Qs B) (hB : B ≤ B') : BesideBy m n Qs B' := fun Q hQ => by
  obtain ⟨k, hk, b⟩ := h Q hQ
  exact ⟨k, Nat.le_trans hk hB, b⟩

theorem BesideBy.rows {m n : Nat} {Y0 Y1 Y2 Y3 Y4 : XNet Arith}
    (V : RaceViews n Y0 Y1 Y2 Y3 Y4) (F : Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m)
    {B : Nat} : ∀ (Qs : List (XThread Arith)), BesideBy m n Qs B →
      ∃ Qs', Rows5 Y0 Y1 Y2 Y3 Y4 Qs Qs' ∧
        ∀ T, T ∈ Qs' → ∃ k, k ≤ B ∧ Stays xsys Y4 T ⟨[], .idle⟩ k
  | [], _ => ⟨[], .nil, fun T hT => by cases hT⟩
  | Q :: Qs, h => by
    obtain ⟨k, hk, b1⟩ := h Q List.mem_cons_self
    obtain ⟨Q', r, s, -⟩ := b1 Y0 Y1 Y2 Y3 Y4 V F
    obtain ⟨Qs', rs, hs⟩ := BesideBy.rows V F Qs fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)
    exact ⟨Q' :: Qs', .cons r rs, fun T hT => by
      rcases List.mem_cons.1 hT with e | hT
      · rw [e]
        exact ⟨k, hk, s⟩
      · exact hs T hT⟩

/-- **The rounds of a run from the race on, with any number of threads
reading between the two**: five rounds, then those of the thread that
still has most to do, which is one of the two that race. -/
theorem RaceEnd.rounds {m n : Nat} {M0 : XNet Arith} {F0 R0 : XThread Arith}
    {kF kR K : Nat} (h : RaceEnd m n M0 F0 R0 kF kR) {Qs : List (XThread Arith)}
    (hQ : BesideBy m n Qs K) (hF : kF ≤ K) (hR : kR ≤ K) (hK : kF = K ∨ kR = K) :
    Rounds (Qs.length + 2) ⟨M0, F0 :: (Qs ++ [R0])⟩ (5 + K) := by
  obtain ⟨Y0, Y1, Y2, Y3, Y4, F5, R5, V, Fin, sw, sF, sR, h1F, -⟩ := h
  obtain ⟨Qs', rows, hs⟩ := BesideBy.rows V Fin Qs hQ
  have r := rounds_sweepsK (sw Qs Qs' rows) (K := K)
    (fun T hT => by
      rcases List.mem_cons.1 hT with e | hT
      · rw [e]
        exact ⟨kF, hF, sF⟩
      · rcases List.mem_append.1 hT with hT | hT
        · exact hs T hT
        · rcases List.mem_cons.1 hT with e | hT
          · rw [e]
            exact ⟨kR, hR, sR⟩
          · cases hT)
    (by
      rcases hK with e | e
      · exact ⟨F5, List.mem_cons_self, by
          rw [← e]
          exact sF⟩
      · exact ⟨R5, List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self), by
          rw [← e]
          exact sR⟩)
    (by omega)
  have e : (F0 :: (Qs ++ [R0])).length = Qs.length + 2 := two_len' F0 R0 Qs
  rw [← e]
  exact r

theorem race_rounds_arith (M N E d c s : Nat) (hE : E = 17 * M + 11 + d)
    (hc : c + d + s = 19) :
    E + (5 + (5 * M + 3 * N + c)) = 22 * (M + 1) + 3 * N + 13 - s := by
  subst hE
  omega

/-- **Any number of threads in turn with the last in the race, the rounds
to the action.**  On the net for `(m + 1) + n` take `j + 3` threads in
turn, with `j + 3 ≤ m`, and let the last of them come to the zero of the
first argument after `17 * m + 7 + d` actions, `d` up to nine.  The threads
between the first and the last are at rest before these two, and all are
at rest `raceSave d` rounds sooner than one thread alone, and not before. -/
theorem threads_race_last_rounds (m n j : Nat) (hm : j + 3 ≤ m)
    (h1 : 17 * m + 7 ≤ turnAt m n (j + 1)) (h2 : turnAt m n (j + 1) ≤ 17 * m + 16) :
    Rounds (j + 3) (XMach.init (sum (m + 1) n) (j + 3))
      (soloWork (m + 1) n - raceSave (turnAt m n (j + 1) - (17 * m + 7))) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 + 1 := ⟨n - 2, by
    unfold turnAt at h1
    omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have eA : ∀ t, t ≤ j + 1 → turnAt (m' + 1) (p + 1 + 1) t =
      (3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) := fun t ht => by
    unfold turnAt
    omega
  rw [soloWork_succ, eA (j + 1) (Nat.le_refl _)]
  rw [eA (j + 1) (Nat.le_refl _)] at h1 h2
  obtain ⟨d, hd⟩ : ∃ d, (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) = 17 * (m' + 1) + 7 + d :=
    ⟨(3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) -
        (17 * (m' + 1) + 7), by omega⟩
  have e0 : (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) -
      (17 * (m' + 1) + 7) = d := by omega
  rw [e0]
  have early : Aside ((d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
      d = 9) ∧ ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) = 17 * (m' + 1) + 11 + d) :=
    Aside.intro ⟨by omega, by omega⟩
  have r1 := turn_reader_ready (m' + 1) (p + 1) (j + 1) ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)
      (by omega) (by omega) (by omega)
    (by omega) (by omega)
  rw [← turn_list_succ (m' + 1) (p + 1) (j + 1) (by omega)] at r1
  have neR : (⟨([3], .zero) :: ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
      ((j + 1) + 1)), .ready [2] [0, p + 1 + 1 + 4] .zero .add⟩ : XThread Arith) ≠
      ⟨[], .idle⟩ := fun h => by
    injection h with _ h2
    cases h2
  have q0 := turn_reader_at_zero (m' + 1) (p + 1) j ((3 * (m' + 1 - j) + 11) / 16 - 1) (by omega)
      (by omega) (by omega)
  rw [← turn_list_succ (m' + 1) (p + 1) j (by omega)] at q0
  have hKj : ((3 * (m' + 1 - j) + 11) / 16 - 1) = ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1) ∨
      ((3 * (m' + 1 - j) + 11) / 16 - 1) = ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1) + 1 := by omega
  have pkg : ∃ (Qadj : XThread Arith) (WQa : Nat),
      RdAt (m' + 1) (p + 1 + 1) (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (j + 1) ++
          (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (j + 1), .idle⟩ : XThread Arith)
          ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
          (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) Qadj ∧ Qadj ≠ ⟨[], .idle⟩ ∧
      Beside1 (m' + 1) (p + 1 + 1) Qadj WQa ∧ ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) + 5 + WQa =
          (3 * (m' + 1 - j) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - j) + 11) / 16 - 1)) +
          (j + 1) + 7 := by
    rcases hKj with e | e
    · have hal := solo_alive_zero (m' + 1) (p + 1 + 1) (j := 2)
          (u := (3 * (m' + 1 - j) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - j) + 11) / 16 - 1)) + 1)
          (by omega) (by omega)
        (by omega) (sum_zero_agent (m' + 1) (p + 1 + 1))
      have q1 := q0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
      have q1e : RdAt (m' + 1) (p + 1 + 1) (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (j + 1) ++
          (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (j + 1), .idle⟩ : XThread Arith)
          ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
          (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4)
          ⟨([3], .zero) :: ((chainL (p + 1 + 1) (m' + 1 - j + (j + 1))).take (j + 1)), .look
              [2] .zero⟩ := q1.cast (by omega)
      exact ⟨_, _, q1e, (fun h => by
        injection h with _ h2
        cases h2),
        beside_adj_a (m' + 1) (by omega) (tops_tops (p + 1 + 1) (m' + 1 - j) j), by
          rw [tops_length]
          omega⟩
    · have q0e : RdAt (m' + 1) (p + 1 + 1) (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (j + 1) ++
          (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (j + 1), .idle⟩ : XThread Arith)
          ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
          (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4)
          ⟨([2], .zero) :: ([3], .zero) :: ((chainL (p + 1 + 1) (m' + 1 - j + (j + 1))).take
              (j + 1)), .idle⟩ := q0.cast (by omega)
      exact ⟨_, _, q0e, (fun h => by cases h),
        beside_adj_b (m' + 1) (by omega) (tops_tops (p + 1 + 1) (m' + 1 - j) j), by
          rw [tops_length]
          omega⟩
  have hlate : ∀ t, t < j → RdAt (m' + 1) (p + 1 + 1)
      (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (t + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)
      ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4)
      (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
      ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))) ∧
      (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
          ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
          (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))) ≠
          ⟨[], .idle⟩ := by
    intro t ht
    have q := turn_reader_lp (m' + 1) (p + 1) t ((3 * (m' + 1 - t) + 11) / 16 - 1)
      (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) -
          (3 * (m' + 1 - t) + 4 + ((3 * (m' + 1 - t) + 11) / 16 - 1))) (by omega) (by omega)
          (by omega) (by omega)
      (by omega)
    rw [← turn_list_succ (m' + 1) (p + 1) t (by omega)] at q
    have e1 : 3 * (m' + 1 - t) + 4 + ((3 * (m' + 1 - t) + 11) / 16 - 1) +
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) - (3 * (m' + 1 - t) + 4 +
        ((3 * (m' + 1 - t) + 11) / 16 - 1))) =
        ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
            (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) := by omega
    have e2 : 3 * (p + 1) + 5 - (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
        ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) -
        (3 * (m' + 1 - t) + 4 + ((3 * (m' + 1 - t) + 11) / 16 - 1))) =
        (3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
            (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
            (m' + 1 - (j + 1)) + 11) / 16 - 1)) := by omega
    rw [e1, e2] at q
    refine ⟨q, ?_⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ, (3 * (m' + 1 - t) + 3 * (p + 1) + 5 +
        ((3 * (m' + 1 - t) + 11) / 16 - 1)) - (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
        ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) = ρ + 1 :=
      ⟨(3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
          (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) - 1,
          by omega⟩
    rw [hρ]
    exact LP_ne_rest _ ρ
  have hbl : ∀ t, t < j → Beside1 (m' + 1) (p + 1 + 1)
      (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
      ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1))))
      ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) - 5 +
      (t + 1)) := by
    intro t ht
    have b := beside_late (m' + 1) (n := p + 1 + 1) (by omega)
        (tops_tops (p + 1 + 1) (m' + 1 - t) t) (by
      rw [tops_length]
      omega) ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
          (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))
          (by omega) (by omega)
    rw [tops_length] at b
    exact b
  have hwl : ∀ t, t < j → ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - t) + 11) / 16 - 1)) - (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) - 5 + (t + 1)) ≤
      (5 * (m' + 1) + 3 * (p + 1 + 1) + 10) := by
    intro t ht
    omega
  obtain ⟨Qadj, WQa, hRd, hNe, hB1, hadj⟩ := pkg
  have hwa : WQa ≤ (5 * (m' + 1) + 3 * (p + 1 + 1) + 10) := by omega
  have EA : EntryAll (m' + 1) (p + 1 + 1) ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) ((List.range j).map
      (fun t => (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (t + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)) ++
      [(⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (j + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (j + 1), .idle⟩ : XThread Arith),
      (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop ((j + 1) + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take ((j + 1) + 1), .idle⟩ : XThread Arith)])
      (((List.range j).map (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
          ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
          (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
          (m' + 1 - (j + 1)) + 11) / 16 - 1)))))) ++ [Qadj,
          (⟨([3], .zero) :: ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
          ((j + 1) + 1)), .ready [2] [0, p + 1 + 1 + 4] .zero .add⟩ : XThread Arith)]) :=
    (entry_range (fun t => (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (t + 1) ++
        (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))
        (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
        ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
        (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1))))) j hlate).append
      (.cons hRd hNe (.cons r1 neR .nil))
  have hQB : BesideBy (m' + 1) (p + 1 + 1) (((List.range j).map
      (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
      ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))))) ++
      [Qadj]) (5 * (m' + 1) + 3 * (p + 1 + 1) + 10) := fun Q hQ => by
    rcases List.mem_append.1 hQ with hQ | hQ
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hQ
      exact ⟨_, hwl t (List.mem_range.1 ht), hbl t (List.mem_range.1 ht)⟩
    · rw [List.mem_singleton.1 hQ]
      exact ⟨WQa, hwa, hB1⟩
  have hTl : ((List.range j).map (fun t => (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (t + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)) ++
      [(⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (j + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (j + 1), .idle⟩ : XThread Arith),
      (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop ((j + 1) + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take ((j + 1) + 1),
      .idle⟩ : XThread Arith)]).length + 1 = j + 3 := by
    rw [List.length_append, List.length_map, List.length_range]
    rfl
  have hQl : (((List.range j).map (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take
      (t + 1)) ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))))) ++
      [Qadj]).length + 2 = j + 3 := by
    rw [List.length_append, List.length_map, List.length_range]
    rfl
  have eSs : (((List.range j).map (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take
      (t + 1)) ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))))) ++
      [Qadj]) ++ [(⟨([3], .zero) :: ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
      ((j + 1) + 1)), .ready [2] [0, p + 1 + 1 + 4] .zero .add⟩ : XThread Arith)] =
      ((List.range j).map (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
      ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))))) ++
      [Qadj, (⟨([3], .zero) :: ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
      ((j + 1) + 1)), .ready [2]
      [0, p + 1 + 1 + 4] .zero .add⟩ : XThread Arith)] := List.append_assoc _ _ _
  have etl : ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
      ((j + 1) + 1)).length = j + 2 := tops_length (p + 1 + 1) (m' + 1 - (j + 1)) (j + 1)
  have hj2 : ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1)).length ≤
      (5 * (m' + 1) + 3 * (p + 1 + 1) + 10) + 1 := by
    rw [etl]
    omega
  have ht2 : Tops (p + 1 + 1) ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
      ((j + 1) + 1)) := tops_tops (p + 1 + 1) (m' + 1 - (j + 1)) (j + 1)
  obtain ⟨V, todo, rest, p5, q5, p6, q6, p7, q7, p8, q8, B, s11, s12, s13, s14, s15⟩ :=
    race_write (m' + 1) (p + 1 + 1) (by omega)
  obtain ⟨s16, s17, s18, s19, s20⟩ := B.states
  have lk12 := solo_look_two (m' + 1) (p + 1 + 1) (17 * (m' + 1) + 12)
  rw [s12] at lk12
  have lk13 := solo_look_two (m' + 1) (p + 1 + 1) (17 * (m' + 1) + 13)
  rw [s13] at lk13
  have lk14 := solo_look_two (m' + 1) (p + 1 + 1) (17 * (m' + 1) + 14)
  rw [s14] at lk14
  have sk13 := (solo_seek_two (m' + 1) (p + 1 + 1) (by omega) (17 * (m' + 1) + 13)).1 (by omega)
  rw [s13] at sk13
  have sk14 := (solo_seek_two (m' + 1) (p + 1 + 1) (by omega) (17 * (m' + 1) + 14)).1 (by omega)
  rw [s14] at sk14
  have hS11 : ∀ j, 3 ≤ j → j ≤ p + 1 + 1 + 2 →
      ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ V.wires := fun j a b => by
    have h := assoc_mem (solo_look_snd (m' + 1) (p + 1 + 1) (j := j) a b (17 * (m' + 1) + 11)).1
    rw [s11] at h
    exact h
  have hS12 : ∀ j, 3 ≤ j → j ≤ p + 1 + 1 + 2 →
      ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ (V.putLink p5 q5).wires := fun j a b => by
    have h := assoc_mem (solo_look_snd (m' + 1) (p + 1 + 1) (j := j) a b (17 * (m' + 1) + 12)).1
    rw [s12] at h
    exact h
  have hS13 : ∀ j, 3 ≤ j → j ≤ p + 1 + 1 + 2 →
      ((([j], 0), ([j + 1], 1)) : Port × Port) ∈ ((V.putLink p5 q5).putLink p6 q6).wires :=
    fun j a b => by
      have h := assoc_mem (solo_look_snd (m' + 1) (p + 1 + 1) (j := j) a b (17 * (m' + 1) + 13)).1
      rw [s13] at h
      exact h
  have hinit : XMach.init (sum (m' + 1 + 1) (p + 1 + 1)) (j + 3) =
      ⟨(sum (m' + 1 + 1) (p + 1 + 1)), ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ ::
      ((List.range j).map (fun t => (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (t + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)) ++
      [(⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop (j + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take (j + 1), .idle⟩ : XThread Arith),
      (⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents.drop ((j + 1) + 1) ++
      (sum (m' + 1 + 1) (p + 1 + 1)).agents.take ((j + 1) + 1), .idle⟩ : XThread Arith)])⟩ := by
    rw [XMach.init_succ, List.range_succ, List.range_succ, List.map_append, List.map_append,
      List.append_assoc]
    rfl
  rw [hinit]
  obtain ⟨hd', hE⟩ := early.elim
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have es := solo_at s11 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠
          ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d0 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take
        ((j + 1) + 1))) lk12 lk13 sk13 sk14 hS11).rounds hQB (Nat.le_refl _) (Nat.le_refl _)
        (Or.inl rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 0 10 9 hE rfl)
  · have es := solo_at s12 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d1 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) lk13 lk14 sk14 hS12).rounds hQB
        (Nat.add_le_add_left (by decide) _) (Nat.le_refl _) (Or.inr rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 1 10 8 hE rfl)
  · have es := solo_at s13 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d2 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) lk14 hS13).rounds hQB
        (Nat.add_le_add_left (by decide) _) (Nat.le_refl _) (Or.inr rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 2 10 7 hE rfl)
  · have es := solo_at s14 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d3 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1)))).rounds hQB
        (Nat.add_le_add_left (by decide) _) (Nat.le_refl _) (Or.inr rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 3 10 6 hE rfl)
  · have es := solo_at s15 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] []⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d4 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1)))).rounds
        (hQB.mono (Nat.add_le_add_left (by decide : 10 ≤ 11) (5 * (m' + 1) + 3 * (p + 1 + 1))))
        (Nat.le_refl _) (Nat.add_le_add_left (by decide) _) (Or.inl rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 4 11 4 hE rfl)
  · have es := solo_at s16 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents,
          .idle⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      rw [B.agents]
      exact fun h => by cases h
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d5 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1)))).rounds hQB (Nat.le_refl _)
        (Nat.le_refl _) (Or.inl rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 5 10 4 hE rfl)
  · have es := solo_at s17 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .look [0, p + 1 + 1 + 4] .add⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d6 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1)))).rounds hQB
        (Nat.add_le_add_left (by decide) _) (Nat.le_refl _) (Or.inr rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 6 10 3 hE rfl)
  · have es := solo_at s18 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .seek [0, p + 1 + 1 + 4] .add ([0, p + 1 + 1 + 4], 0)
          ([p + 1 + 1 + 4], 1)⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d7 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1)))).rounds hQB
        (Nat.add_le_add_left (by decide) _) (Nat.le_refl _) (Or.inr rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 7 10 2 hE rfl)
  · have es := solo_at s19 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .seek [0, p + 1 + 1 + 4] .add ([p + 1 + 1 + 4], 1) ([2], 0)⟩ : XThread Arith) ≠
          ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d8 B (tops := ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
        ((j + 1) + 1))) ht2 (by
      rw [etl]
      exact Nat.le_add_left _ _)).rounds (hQB.mono (Nat.le_add_right
          (5 * (m' + 1) + 3 * (p + 1 + 1) + 10) 1)) (Nat.le_refl _) hj2 (Or.inl rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 8 11 0 hE rfl)
  · have es := solo_at s20 (hE.trans rfl)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1))
        ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩
        (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
        (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4))).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .ready [0, p + 1 + 1 + 4] [2] .add .zero⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, -⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr
    rw [← eSs] at tr
    have rd := (race_e_d9 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1)))).rounds hQB
        (Nat.add_le_add_left (by decide) _) (Nat.le_refl _) (Or.inr rfl)
    rw [hQl] at rd
    exact (rounds_after (j + 3) tr rd (Nat.le_trans (by decide) (Nat.le_add_right 5 _))).cast
      (race_rounds_arith (m' + 1) (p + 1 + 1) _ 9 10 0 hE rfl)

/-- **The rounds of `k + 1` threads in turn on the net for `(m + 1) + n`**:
those of one thread alone, less what the race saves when one of the
threads after the first races. -/
def allRounds (m n k : Nat) : Nat :=
  match racerOf m n k with
  | none => soloWork (m + 1) n
  | some r => soloWork (m + 1) n - raceSave (turnAt m n r - (17 * m + 7))

/-- **Any number of threads in turn, every size, the rounds to the
action.**  On the net for `(m + 1) + n`, with `m` from four on, `k + 1`
threads acting in turn, `k + 1 ≤ m` and `20 * k ≤ 3 * m + 3 * n + 21`, are
all at rest after exactly `allRounds m n k` rounds: the thread that races
and the first are the last to rest, the threads between them and the
threads that passed the zero of the first argument early rest before. -/
theorem threads_rounds_exact (m n k : Nat) (hm4 : 4 ≤ m) (hm : k + 1 ≤ m)
    (hn : 20 * k ≤ 3 * m + 3 * n + 21) :
    Rounds (k + 1) (XMach.init (sum (m + 1) n) (k + 1)) (allRounds m n k) := by
  unfold allRounds
  cases hr : racerOf m n k with
  | none =>
    show Rounds (k + 1) (XMach.init (sum (m + 1) n) (k + 1)) (soloWork (m + 1) n)
    exact threads_rounds_none m n k hm hn hr
  | some r =>
    obtain ⟨hrk, hw, hlater⟩ := racerOf_some k r hr
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
      have h := hw.1
      unfold turnAt at h
      omega⟩
    show Rounds (k + 1) (XMach.init (sum (m + 1) (n' + 1)) (k + 1))
      (soloWork (m + 1) (n' + 1) - raceSave (turnAt m (n' + 1) r - (17 * m + 7)))
    have sv := raceSave_le (turnAt m (n' + 1) r - (17 * m + 7))
    have es := soloWork_succ m (n' + 1)
    cases r with
    | zero =>
      have base : Rounds (1 + 1) (XMach.init (sum (m + 1) (n' + 1)) (1 + 1))
          (soloWork (m + 1) (n' + 1) - raceSave (turnAt m (n' + 1) 0 - (17 * m + 7))) :=
        two_threads_race_rounds m (n' + 1) hm4 hw.1 hw.2
      have res := threads_early_opt_rounds m n' 1 _ base (k - 1) (fun h1 => by
        have hA : turnAt m (n' + 1) 1 ≤ 17 * m + 6 := by
          have hn1 := hlater 1 (by omega) (by omega)
          have h0 := hw.2
          unfold turnAt at hn1 h0 ⊢
          omega
        exact ⟨hA, by omega⟩) (by omega) (by omega)
      rw [show 1 + (k - 1) + 1 = k + 1 by omega] at res
      exact res
    | succ j =>
      have base : Rounds (j + 2 + 1) (XMach.init (sum (m + 1) (n' + 1)) (j + 2 + 1))
          (soloWork (m + 1) (n' + 1) -
            raceSave (turnAt m (n' + 1) (j + 1) - (17 * m + 7))) :=
        threads_race_last_rounds m (n' + 1) j (by omega) hw.1 hw.2
      have res := threads_early_opt_rounds m n' (j + 2) _ base (k - (j + 2)) (fun h1 => by
        have hA : turnAt m (n' + 1) (j + 2) ≤ 17 * m + 6 := by
          have hn1 := hlater (j + 2) (by omega) (by omega)
          have h0 := hw.2
          unfold turnAt at hn1 h0 ⊢
          omega
        exact ⟨hA, by omega⟩) (by omega) (by omega)
      rw [show j + 2 + (k - (j + 2)) + 1 = k + 1 by omega] at res
      exact res

/-- **More threads in turn save nine rounds at most, and cost none.**
Under the same conditions the run is at rest after `R` rounds, with `R` at
most the actions of one thread alone and at least nine fewer. -/
theorem threads_rounds_bounds (m n k : Nat) (hm4 : 4 ≤ m) (hm : k + 1 ≤ m)
    (hn : 20 * k ≤ 3 * m + 3 * n + 21) :
    ∃ R, Rounds (k + 1) (XMach.init (sum (m + 1) n) (k + 1)) R ∧ R ≤ soloWork (m + 1) n ∧
      soloWork (m + 1) n ≤ R + 9 := by
  refine ⟨allRounds m n k, threads_rounds_exact m n k hm4 hm hn, ?_, ?_⟩
  · unfold allRounds
    cases racerOf m n k with
    | none => exact Nat.le_refl _
    | some r => exact Nat.sub_le _ _
  · unfold allRounds
    cases racerOf m n k with
    | none => exact Nat.le_add_right _ _
    | some r =>
      have s := raceSave_le (turnAt m n r - (17 * m + 7))
      show soloWork (m + 1) n ≤
        soloWork (m + 1) n - raceSave (turnAt m n r - (17 * m + 7)) + 9
      omega

example : Rounds 3 (XMach.init (sum 8 36) 3) 290 :=
  (threads_rounds_exact 7 36 2 (by decide) (by decide) (by decide)).cast (by decide)

example : Rounds 5 (XMach.init (sum 9 41) 5) 325 :=
  (threads_rounds_exact 8 41 4 (by decide) (by decide) (by decide)).cast (by decide)

example : Rounds 6 (XMach.init (sum 11 52) 6) 405 :=
  (threads_rounds_exact 10 52 5 (by decide) (by decide) (by decide)).cast (by decide)

end Arith

end INet
