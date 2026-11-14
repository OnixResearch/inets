import InteractionNets.Arith.RaceLast

/-! ### Four threads in turn on an addition -/

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

/-- The second argument but for its lowest successor, three actions for
each agent. -/
theorem RdAt.snd_last {m n : Nat} {T0 : XThread Arith} {l : List (Id × Arith)} :
    ∀ (k a : Nat), k + 2 ≤ n →
      RdAt m n T0 a ⟨sndL (k + 1) ++ l, .idle⟩ →
      RdAt m n T0 (a + 3 * k) ⟨([4], .succ) :: l, .idle⟩
  | 0, _, _, h => h
  | k + 1, a, hk, h => by
    have h' : RdAt m n T0 a ⟨([k + 1 + 4], .succ) :: (sndL (k + 1) ++ l), .idle⟩ := h
    have hx : assoc [k + 1 + 4] (sum (m + 1) n).agents = some Arith.succ :=
      sum_assoc_base m n (e := ([k + 1 + 4], Arith.succ))
        (List.mem_append_left _ (sndL_mem n (k + 1) (by omega)))
    have hal := solo_snd_forever m n (j := k + 1 + 4) (by omega) (by omega) hx (a + 1)
    have h3 := h'.pass3 hal (solo_look_snd m n (j := k + 1 + 4) (by omega) (by omega) _).1
      (show ¬ (1 : Nat) = 0 by decide)
      (solo_look_snd m n (j := k + 1 + 4) (by omega) (by omega) _).2
    exact (RdAt.snd_last k (a + 3) (by omega) h3).cast (by omega)

/-- **The thread numbered `t + 1` comes to the lowest successor of the
second argument four actions before it comes to the zero of the first.** -/
theorem turn_reader_near_zero (m p t K : Nat) (ht : t + 2 ≤ m)
    (hK1 : 16 * K + 5 ≤ 3 * (m - t)) (hK2 : 3 * (m - t) < 16 * K + 21) :
    RdAt m (p + 1 + 1) ⟨chainL (p + 1 + 1) (m - t) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
          (chainL (p + 1 + 1) (m - t + (t + 1))).take (t + 1)))), .idle⟩
      (3 * (m - t) + 4 + K + 3 * p)
      ⟨([4], .succ) :: ([1], .add) :: ([2], .zero) :: ([3], .zero) ::
        (chainL (p + 1 + 1) (m - t + (t + 1))).take (t + 1), .idle⟩ := by
  have h0 := RdAt.start m (p + 1 + 1) ⟨chainL (p + 1 + 1) (m - t) ++ (([p + 1 + 1 + 3], .succ) ::
    (sndL (p + 1) ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
      (chainL (p + 1 + 1) (m - t + (t + 1))).take (t + 1)))), .idle⟩
  have h1 := RdAt.chain_turn (t := t) (m - t) (by omega) (h0.cast (by omega))
  have hx : assoc [p + 1 + 1 + 3] (sum (m + 1) (p + 1 + 1)).agents = some Arith.succ :=
    sum_assoc_base m (p + 1 + 1) (e := ([p + 1 + 1 + 3], Arith.succ))
      (List.mem_append_left _ (sndL_mem (p + 1 + 1) (p + 1) (by omega)))
  have h2 := RdAt.walk (by omega) hK1 hK2 (by omega) hx h1
  exact RdAt.snd_last p (3 * (m - t) + 4 + K) (by omega) h2

/-- **Four threads in turn with the fourth in the race, to the action.**
On the net for `(m + 1) + n`, with `m` from four on, when the fourth thread
comes to the zero of the first argument after `17 * m + 7 + d` actions, `d`
up to nine: it races the first for the last pair as the second of two
threads would.  The third thread, three or four actions behind it, reads on
to the last adder and finds it gone; the second, three or four actions
behind the third, finds that zero gone.  The work of the whole run is
exactly `raceWork m n d` for the first and the fourth thread, two more when
the first keeps the pair, `turnAt m n 1 + 9` for the third thread and
`turnAt m n 0 + 5` for the second. -/
theorem four_threads_race_last (m n : Nat) (hm : 4 ≤ m)
    (h1 : 17 * m + 7 ≤ turnAt m n 2) (h2 : turnAt m n 2 ≤ 17 * m + 16) :
    (XMach.init (sum (m + 1) n) 4).Total xsys (fun i => i % 4)
      (raceWork m n (turnAt m n 2 - (17 * m + 7)) +
        (if turnAt m n 2 = 17 * m + 15 then 2 else 0) + (turnAt m n 1 + 9) +
        (turnAt m n 0 + 5)) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 + 1 := ⟨n - 2, by
    unfold turnAt at h1
    omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K1, hK1⟩ : ∃ K, (3 * (m' + 1 - 0) + 11) / 16 = K + 1 :=
    ⟨(3 * (m' + 1 - 0) + 11) / 16 - 1, by omega⟩
  obtain ⟨K2, hK2⟩ : ∃ K, (3 * (m' + 1 - 1) + 11) / 16 = K + 1 :=
    ⟨(3 * (m' + 1 - 1) + 11) / 16 - 1, by omega⟩
  obtain ⟨K3, hK3⟩ : ∃ K, (3 * (m' + 1 - 2) + 11) / 16 = K + 1 :=
    ⟨(3 * (m' + 1 - 2) + 11) / 16 - 1, by omega⟩
  have eA1 : turnAt (m' + 1) (p + 1 + 1) 0 = 3 * (m' + 1 - 0) + 3 * (p + 1) + 5 + K1 := by
    unfold turnAt
    omega
  have eA2 : turnAt (m' + 1) (p + 1 + 1) 1 = 3 * (m' + 1 - 1) + 3 * (p + 1) + 5 + K2 := by
    unfold turnAt
    omega
  have eA3 : turnAt (m' + 1) (p + 1 + 1) 2 = 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 := by
    unfold turnAt
    omega
  rw [eA1, eA2, eA3]
  rw [eA3] at h1 h2
  obtain ⟨d, hd⟩ : ∃ d, 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 = 17 * (m' + 1) + 7 + d :=
    ⟨3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 - (17 * (m' + 1) + 7), by omega⟩
  have e0 : 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 - (17 * (m' + 1) + 7) = d := by omega
  rw [e0]
  have r1 := turn_reader_ready (m' + 1) (p + 1) 2 K3 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have r1e : RdAt (m' + 1) (p + 1 + 1) ⟨chainL (p + 1 + 1) (m' + 1 - 2) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 2 + (2 + 1))).take (2 + 1)))), .idle⟩
      (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) ⟨([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 2 + 2) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2) + 1], .succ)], .ready [2] [0, p + 1 + 1 + 4] .zero .add⟩ := r1
  have q0 := turn_reader_at_zero (m' + 1) (p + 1) 1 K2 (by omega) (by omega) (by omega)
  have p0 := turn_reader_near_zero (m' + 1) p 0 K1 (by omega) (by omega) (by omega)
  have hx4 : assoc [4] (sum (m' + 1 + 1) (p + 1 + 1)).agents = some Arith.succ :=
    sum_assoc_base (m' + 1) (p + 1 + 1) (e := ([4], Arith.succ))
      (List.mem_append_left _ (sndL_mem (p + 1 + 1) 0 (by omega)))
  have p1 := p0.step (XMach.act_idle_pos (e := ([4], Arith.succ))
    (solo_snd_forever (m' + 1) (p + 1 + 1) (j := 4) (by omega) (by omega) hx4 _))
  have p2 := p1.step (XMach.act_look
    (solo_look_snd (m' + 1) (p + 1 + 1) (j := 4) (by omega) (by omega) _).1)
  have ht0 : Tops (p + 1 + 1) [([p + 1 + 1 + 3 + (m' + 1 - 0) + 1], .succ)] := tops_cons (by omega) _ (tops_nil _)
  have ht1 : Tops (p + 1 + 1) [([p + 1 + 1 + 3 + (m' + 1 - 1 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 1) + 1], .succ)] :=
    tops_cons (by omega) _ (tops_cons (by omega) _ (tops_nil _))
  have ht2 : Tops (p + 1 + 1) [([p + 1 + 1 + 3 + (m' + 1 - 2 + 2) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2) + 1], .succ)] :=
    tops_cons (by omega) _ (tops_cons (by omega) _ (tops_cons (by omega) _ (tops_nil _)))
  have neR : (⟨([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 2 + 2) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2) + 1], .succ)], .ready [2] [0, p + 1 + 1 + 4] .zero .add⟩ : XThread Arith) ≠ ⟨[], .idle⟩ := fun h => by
    injection h with _ h2
    cases h2
  have hK : (K2 = K3 ∧ K1 = K3) ∨ (K2 = K3 + 1 ∧ K1 = K3 + 1) ∨ (K2 = K3 ∧ K1 = K3 + 1) := by
    omega
  have pkg : ∃ (Q1 Q2 : XThread Arith) (WQ : Nat),
      EntryAll (m' + 1) (p + 1 + 1) (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)
        [⟨chainL (p + 1 + 1) (m' + 1 - 0) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩,
          ⟨chainL (p + 1 + 1) (m' + 1 - 1) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩,
          ⟨chainL (p + 1 + 1) (m' + 1 - 2) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 2 + (2 + 1))).take (2 + 1)))), .idle⟩]
        [Q1, Q2, ⟨([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 2 + 2) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2) + 1], .succ)], .ready [2] [0, p + 1 + 1 + 4] .zero .add⟩] ∧
      Beside (m' + 1) (p + 1 + 1) [Q1, Q2] WQ ∧
      2 * (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) + 10 + WQ = 3 * (m' + 1 - 1) + 3 * (p + 1) + 5 + K2 + 9 + (3 * (m' + 1 - 0) + 3 * (p + 1) + 5 + K1 + 5) := by
    rcases hK with ⟨e2, e1⟩ | ⟨e2, e1⟩ | ⟨e2, e1⟩
    · have hal := solo_alive_zero (m' + 1) (p + 1 + 1) (j := 2) (u := 3 * (m' + 1 - 1) + 3 * (p + 1) + 5 + K2 + 1) (by omega) (by omega)
        (by omega) (sum_zero_agent (m' + 1) (p + 1 + 1))
      have q1 := q0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
      have q1e : RdAt (m' + 1) (p + 1 + 1) ⟨chainL (p + 1 + 1) (m' + 1 - 1) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩
          (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) ⟨([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 1 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 1) + 1], .succ)], .look [2] .zero⟩ := q1.cast (by omega)
      have p2e : RdAt (m' + 1) (p + 1 + 1) ⟨chainL (p + 1 + 1) (m' + 1 - 0) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩
          (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) ⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 0) + 1], .succ)], .seek [4] .succ ([4], 0) ([5], 1)⟩ := p2.cast (by omega)
      exact ⟨_, _, _, .cons p2e (fun h => by
          injection h with _ h2
          cases h2) (.cons q1e (fun h => by
          injection h with _ h2
          cases h2) (.cons r1e neR .nil)),
        .cons (beside_late_s (m' + 1) (by omega) ht0) (.cons (beside_adj_a (m' + 1) (by omega) ht1) (Beside.nil _ _)), by
          show 2 * (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) + 10 + ((1 + 1) + ((2 + 1) + 0)) = _
          omega⟩
    · have q0e : RdAt (m' + 1) (p + 1 + 1) ⟨chainL (p + 1 + 1) (m' + 1 - 1) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩
          (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) ⟨([2], .zero) :: ([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 1 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 1) + 1], .succ)], .idle⟩ := q0.cast (by omega)
      have p1e : RdAt (m' + 1) (p + 1 + 1) ⟨chainL (p + 1 + 1) (m' + 1 - 0) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩
          (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) ⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 0) + 1], .succ)], .look [4] .succ⟩ := p1.cast (by omega)
      exact ⟨_, _, _, .cons p1e (fun h => by
          injection h with _ h2
          cases h2) (.cons q0e (fun h => by cases h) (.cons r1e neR .nil)),
        .cons (beside_late_l (m' + 1) (by omega) ht0) (.cons (beside_adj_b (m' + 1) (by omega) ht1) (Beside.nil _ _)), by
          show 2 * (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) + 10 + ((1 + 1 + 1) + ((2 + 1 + 1) + 0)) = _
          omega⟩
    · have hal := solo_alive_zero (m' + 1) (p + 1 + 1) (j := 2) (u := 3 * (m' + 1 - 1) + 3 * (p + 1) + 5 + K2 + 1) (by omega) (by omega)
        (by omega) (sum_zero_agent (m' + 1) (p + 1 + 1))
      have q1 := q0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
      have q1e : RdAt (m' + 1) (p + 1 + 1) ⟨chainL (p + 1 + 1) (m' + 1 - 1) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩
          (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) ⟨([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 1 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 1) + 1], .succ)], .look [2] .zero⟩ := q1.cast (by omega)
      have p1e : RdAt (m' + 1) (p + 1 + 1) ⟨chainL (p + 1 + 1) (m' + 1 - 0) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩
          (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) ⟨([1], .add) :: ([2], .zero) :: ([3], .zero) :: [([p + 1 + 1 + 3 + (m' + 1 - 0) + 1], .succ)], .look [4] .succ⟩ := p1.cast (by omega)
      exact ⟨_, _, _, .cons p1e (fun h => by
          injection h with _ h2
          cases h2) (.cons q1e (fun h => by
          injection h with _ h2
          cases h2) (.cons r1e neR .nil)),
        .cons (beside_late_l (m' + 1) (by omega) ht0) (.cons (beside_adj_a (m' + 1) (by omega) ht1) (Beside.nil _ _)), by
          show 2 * (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4) + 10 + ((1 + 1 + 1) + ((2 + 1) + 0)) = _
          omega⟩
  obtain ⟨Q1, Q2, WQ, EA, hQ, hW⟩ := pkg
  have e2 : ([Q1, Q2] : List (XThread Arith)).length = 2 := rfl
  have e3 : ([([p + 1 + 1 + 3 + (m' + 1 - 2 + 2) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2) + 1], .succ)] : List (Id × Arith)).length = 3 := rfl
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
  have hinit : XMach.init (sum (m' + 1 + 1) (p + 1 + 1)) 4 = ⟨(sum (m' + 1 + 1) (p + 1 + 1)), [⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩,
      ⟨chainL (p + 1 + 1) (m' + 1 - 0) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩,
      ⟨chainL (p + 1 + 1) (m' + 1 - 1) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩,
      ⟨chainL (p + 1 + 1) (m' + 1 - 2) ++ (([p + 1 + 1 + 3], .succ) :: (sndL (p + 1) ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (p + 1 + 1) (m' + 1 - 2 + (2 + 1))).take (2 + 1)))), .idle⟩]⟩ :=
    (XMach.init_succ (sum (m' + 1 + 1) (p + 1 + 1)) 3).trans (by
      rw [← turn_list_succ (m' + 1) (p + 1) 0 (by omega), ← turn_list_succ (m' + 1) (p + 1) 1 (by omega),
        ← turn_list_succ (m' + 1) (p + 1) 2 (by omega)]
      rfl)
  rw [hinit]
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have es := solo_at s11 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 11 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 0 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 52 := rfl
    exact (total_after 4 tr wk (race_k_d0 B todo _ lk12 lk13 sk13 sk14 hS11 hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s12 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 12 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 1 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 53 := rfl
    exact (total_after 4 tr wk (race_k_d1 B todo _ lk13 lk14 sk14 hS12 hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s13 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 13 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 2 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 54 := rfl
    exact (total_after 4 tr wk (race_k_d2 B todo _ lk14 hS13 hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s14 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 14 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] [(p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 3 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 56 := rfl
    exact (total_after 4 tr wk (race_k_d3 B todo _ hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s15 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 15 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨todo, .write [] []⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 4 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 61 := rfl
    exact (total_after 4 tr wk (race_k_d4 B todo _ hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s16 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 16 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents, .idle⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      rw [B.agents]
      exact fun h => by cases h
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 5 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 62 := rfl
    exact (total_after 4 tr wk (race_k_d5 B _ hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s17 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 17 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .look [0, p + 1 + 1 + 4] .add⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 6 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 63 := rfl
    exact (total_after 4 tr wk (race_k_d6 B _ hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s18 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 18 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .seek [0, p + 1 + 1 + 4] .add ([0, p + 1 + 1 + 4], 0) ([p + 1 + 1 + 4], 1)⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 7 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 64 := rfl
    exact (total_after 4 tr wk (race_k_d7 B _ hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)
  · have es := solo_at s19 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 19 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .seek [0, p + 1 + 1 + 4] .add ([p + 1 + 1 + 4], 1) ([2], 0)⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 8 = 39 * (m' + 1) + 3 * (p + 1 + 1) + 60 := rfl
    exact (total_after 4 tr wk (race_k_d8 B (tops := [([p + 1 + 1 + 3 + (m' + 1 - 2 + 2) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2 + 1) + 1], .succ), ([p + 1 + 1 + 3 + (m' + 1 - 2) + 1], .succ)]) ht2 (by
          rw [e3]
          omega) hQ)).cast (by
      rw [eR, ite_pos' (by omega), e2, e3]
      omega)
  · have es := solo_at s20 (show 3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4 = 17 * (m' + 1) + 20 by omega)
    have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (p + 1 + 1)) ⟨(sum (m' + 1 + 1) (p + 1 + 1)).agents, .idle⟩ (3 * (m' + 1 - 2) + 3 * (p + 1) + 5 + K3 + 4)).2 ≠ ⟨[], .idle⟩ := by
      rw [es]
      show (⟨rest, .ready [0, p + 1 + 1 + 4] [2] .add .zero⟩ : XThread Arith) ≠ ⟨[], .idle⟩
      exact fun h => by
        injection h with _ h2
        cases h2
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    have eR : raceWork (m' + 1) (p + 1 + 1) 9 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 68 := rfl
    exact (total_after 4 tr wk (race_k_d9 B _ hQ)).cast (by
      rw [eR, ite_neg' (by omega), e2]
      omega)

example : (XMach.init (sum 7 32) 4).Total xsys (fun i => i % 4) 752 :=
  (four_threads_race_last 6 32 (by decide) (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 33) 4).Total xsys (fun i => i % 4) 772 :=
  (four_threads_race_last 6 33 (by decide) (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 34) 4).Total xsys (fun i => i % 4) 787 :=
  (four_threads_race_last 6 34 (by decide) (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 8 39) 4).Total xsys (fun i => i % 4) 744 :=
  (four_threads_race_last 7 39 (by decide) (by decide) (by decide)).cast (by decide)

/-- A step of one of the first threads of a list does not look at the
others. -/
theorem step_prefix (Y : XNet Arith) (L Rs : List (XThread Arith)) {t : Nat}
    (ht : t < L.length) :
    XMach.step xsys ⟨Y, L ++ Rs⟩ t =
      (⟨(XMach.step xsys ⟨Y, L⟩ t).1.mem, (XMach.step xsys ⟨Y, L⟩ t).1.ths ++ Rs⟩,
        (XMach.step xsys ⟨Y, L⟩ t).2) := by
  obtain ⟨T, hT⟩ : ∃ T, L[t]? = some T := ⟨_, List.getElem?_eq_getElem ht⟩
  have hT' : (L ++ Rs)[t]? = some T := by
    rw [List.getElem?_append_left ht]
    exact hT
  have e1 : XMach.step xsys ⟨Y, L⟩ t =
      (⟨(XMach.act xsys Y T).1, L.set t (XMach.act xsys Y T).2.1⟩, (XMach.act xsys Y T).2.2) :=
    XMach.step_eq (M := ⟨Y, L⟩) hT rfl
  have e2 : XMach.step xsys ⟨Y, L ++ Rs⟩ t =
      (⟨(XMach.act xsys Y T).1, (L ++ Rs).set t (XMach.act xsys Y T).2.1⟩,
        (XMach.act xsys Y T).2.2) :=
    XMach.step_eq (M := ⟨Y, L ++ Rs⟩) hT' rfl
  rw [e2, e1, List.set_append_left _ _ ht]

theorem stepTally_prefix (κ : XThread Arith → Nat) (Y : XNet Arith)
    (L Rs : List (XThread Arith)) {t : Nat} (ht : t < L.length) :
    (⟨Y, L ++ Rs⟩ : XMach Arith).stepTally κ t = (⟨Y, L⟩ : XMach Arith).stepTally κ t := by
  unfold XMach.stepTally
  dsimp only
  rw [List.getElem?_append_left ht]

/-- **A run in which only the first threads of a list act is the run of
those threads alone**, with the others beside them. -/
theorem trace_prefix (Rs : List (XThread Arith)) (σ : Nat → Nat) (M : XMach Arith) :
    ∀ i, (∀ j, j < i → σ j < M.ths.length) →
      (⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).trace xsys σ i =
          (⟨(M.trace xsys σ i).1.mem, (M.trace xsys σ i).1.ths ++ Rs⟩, (M.trace xsys σ i).2) ∧
        (⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).tally XThread.busy xsys σ i =
          M.tally XThread.busy xsys σ i
  | 0, _ => ⟨rfl, rfl⟩
  | i + 1, h => by
    obtain ⟨ih1, ih2⟩ := trace_prefix Rs σ M i (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hlt : σ i < (M.trace xsys σ i).1.ths.length := by
      rw [XMach.trace_length]
      exact h i (Nat.lt_succ_self i)
    have sp := step_prefix (M.trace xsys σ i).1.mem (M.trace xsys σ i).1.ths Rs hlt
    have st := stepTally_prefix XThread.busy (M.trace xsys σ i).1.mem (M.trace xsys σ i).1.ths Rs
      hlt
    constructor
    · have e : (⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).trace xsys σ (i + 1) =
          ((XMach.step xsys ⟨(M.trace xsys σ i).1.mem, (M.trace xsys σ i).1.ths ++ Rs⟩ (σ i)).1,
            (M.trace xsys σ i).2 +
              (XMach.step xsys ⟨(M.trace xsys σ i).1.mem, (M.trace xsys σ i).1.ths ++ Rs⟩
                (σ i)).2) := by
        show ((((⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).trace xsys σ i).1.step xsys (σ i)).1,
          ((⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).trace xsys σ i).2 +
            (((⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).trace xsys σ i).1.step xsys (σ i)).2) = _
        rw [ih1]
      rw [e, sp]
      rfl
    · show (⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).tally XThread.busy xsys σ i +
          ((⟨M.mem, M.ths ++ Rs⟩ : XMach Arith).trace xsys σ i).1.stepTally XThread.busy (σ i) =
        M.tally XThread.busy xsys σ i + (M.trace xsys σ i).1.stepTally XThread.busy (σ i)
      rw [ih2, ih1]
      exact congrArg (M.tally XThread.busy xsys σ i + ·) st

/-- **One turn of each thread with one more thread at the end that reads**:
the others act as they would without it, and it reads in the memory they
leave. -/
theorem sweep_end {Y : XNet Arith} {L : List (XThread Arith)} {q q' : XThread Arith}
    (hq : XMach.act xsys
        ((⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i % L.length) (L.length * 1)).1.mem q =
      (((⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i % L.length) (L.length * 1)).1.mem, q', 0)) :
    ((⟨Y, L ++ [q]⟩ : XMach Arith).trace xsys (fun i => i % (L.length + 1))
        ((L.length + 1) * 1)).1 =
      ⟨((⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i % L.length) (L.length * 1)).1.mem,
        ((⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i % L.length) (L.length * 1)).1.ths ++
          [q']⟩ ∧
      (⟨Y, L ++ [q]⟩ : XMach Arith).work xsys (fun i => i % (L.length + 1))
          ((L.length + 1) * 1) =
        (⟨Y, L⟩ : XMach Arith).work xsys (fun i => i % L.length) (L.length * 1) + q.busy := by
  have cg0 : (⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i % L.length) (L.length * 1) =
      (⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i) L.length := by
    rw [Nat.mul_one]
    exact XMach.trace_congr xsys _ L.length (fun j hj => Nat.mod_eq_of_lt hj)
  have tg0 : (⟨Y, L⟩ : XMach Arith).work xsys (fun i => i % L.length) (L.length * 1) =
      (⟨Y, L⟩ : XMach Arith).tally XThread.busy xsys (fun i => i) L.length := by
    rw [Nat.mul_one]
    exact XMach.tally_congr XThread.busy xsys _ L.length (fun j hj => Nat.mod_eq_of_lt hj)
  have cgB : (⟨Y, L ++ [q]⟩ : XMach Arith).trace xsys (fun i => i % (L.length + 1)) L.length =
      (⟨Y, L ++ [q]⟩ : XMach Arith).trace xsys (fun i => i) L.length :=
    XMach.trace_congr xsys _ L.length (fun j hj => Nat.mod_eq_of_lt (Nat.lt_succ_of_lt hj))
  have tgB : (⟨Y, L ++ [q]⟩ : XMach Arith).tally XThread.busy xsys (fun i => i % (L.length + 1))
      L.length = (⟨Y, L ++ [q]⟩ : XMach Arith).tally XThread.busy xsys (fun i => i) L.length :=
    XMach.tally_congr XThread.busy xsys _ L.length
      (fun j hj => Nat.mod_eq_of_lt (Nat.lt_succ_of_lt hj))
  obtain ⟨p1, p2⟩ := trace_prefix [q] (fun i => i) (⟨Y, L⟩ : XMach Arith) L.length
    (fun j hj => hj)
  have hlen := XMach.trace_length xsys (fun i => i) (⟨Y, L⟩ : XMach Arith) L.length
  rw [cg0] at hq ⊢
  rw [tg0]
  generalize hN : (⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i) L.length = N at p1 hq hlen ⊢
  obtain ⟨⟨Y', L'⟩, cN⟩ := N
  have hlen' : L'.length = L.length := hlen
  have hq' : XMach.act xsys Y' q = (Y', q', 0) := hq
  have p1' : (⟨Y, L ++ [q]⟩ : XMach Arith).trace xsys (fun i => i) L.length =
      (⟨Y', L' ++ [q]⟩, cN) := p1
  have one := trace_at Y' Y' L' [] hq'
  have cg1 : (⟨Y', L' ++ [q]⟩ : XMach Arith).trace xsys
      (fun i => (L.length + i) % (L.length + 1)) 1 =
      (⟨Y', L' ++ [q]⟩ : XMach Arith).trace xsys (fun i => L'.length + i) 1 :=
    XMach.trace_congr xsys _ 1 (fun j hj => by
      have e : j = 0 := by omega
      subst e
      show (L.length + 0) % (L.length + 1) = L'.length + 0
      rw [hlen', Nat.add_zero, Nat.mod_eq_of_lt (Nat.lt_succ_self _)])
  constructor
  · rw [Nat.mul_one, XMach.trace_add xsys (fun i => i % (L.length + 1)) _ L.length 1, cgB, p1']
    show ((⟨Y', L' ++ [q]⟩ : XMach Arith).trace xsys
      (fun i => (L.length + i) % (L.length + 1)) 1).1 = ⟨Y', L' ++ [q']⟩
    rw [cg1, one]
  · have sT : (⟨Y', L' ++ [q]⟩ : XMach Arith).stepTally XThread.busy (L.length % (L.length + 1)) =
        q.busy := by
      rw [Nat.mod_eq_of_lt (Nat.lt_succ_self _), ← hlen']
      unfold XMach.stepTally
      rw [get_after]
    show (⟨Y, L ++ [q]⟩ : XMach Arith).tally XThread.busy xsys (fun i => i % (L.length + 1))
      ((L.length + 1) * 1) = _
    rw [Nat.mul_one]
    show (⟨Y, L ++ [q]⟩ : XMach Arith).tally XThread.busy xsys (fun i => i % (L.length + 1))
        L.length +
      ((⟨Y, L ++ [q]⟩ : XMach Arith).trace xsys (fun i => i % (L.length + 1)) L.length).1.stepTally
        XThread.busy (L.length % (L.length + 1)) = _
    rw [tgB, p2, cgB, p1']
    exact congrArg ((⟨Y, L⟩ : XMach Arith).tally XThread.busy xsys (fun i => i) L.length + ·) sT

/-- **One more thread at the end that only reads**: if its actions, each
after a turn of all the others, leave the memory as it is and take it
through the states `s`, the run is the run of the others with that thread
beside it, and its work is theirs and the busy actions of that thread. -/
theorem beside_end {X : XNet Arith} {Ts : List (XThread Arith)} (s : Nat → XThread Arith)
    (hs : ∀ w, XMach.act xsys
        ((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * (w + 1))).1.mem
        (s w) =
      (((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * (w + 1))).1.mem,
        s (w + 1), 0)) :
    ∀ w, ((⟨X, Ts ++ [s 0]⟩ : XMach Arith).trace xsys (fun i => i % (Ts.length + 1))
          ((Ts.length + 1) * w)).1 =
        ⟨((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * w)).1.mem,
          ((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * w)).1.ths ++
            [s w]⟩ ∧
      (⟨X, Ts ++ [s 0]⟩ : XMach Arith).work xsys (fun i => i % (Ts.length + 1))
          ((Ts.length + 1) * w) =
        (⟨X, Ts⟩ : XMach Arith).work xsys (fun i => i % Ts.length) (Ts.length * w) +
          seqTally XThread.busy s w
  | 0 => ⟨rfl, rfl⟩
  | w + 1 => by
    obtain ⟨ih1, ih2⟩ := beside_end s hs w
    have hlen := XMach.trace_length xsys (fun i => i % Ts.length) (⟨X, Ts⟩ : XMach Arith)
      (Ts.length * w)
    have p2 := trace_mod_add Ts.length (⟨X, Ts⟩ : XMach Arith) w 1
    have hq := hs w
    rw [p2] at hq
    have w2' := work_mod_add Ts.length (⟨X, Ts⟩ : XMach Arith) w (Ts.length * 1)
    have p3 := trace_mod_add (Ts.length + 1) (⟨X, Ts ++ [s 0]⟩ : XMach Arith) w 1
    have w3' := work_mod_add (Ts.length + 1) (⟨X, Ts ++ [s 0]⟩ : XMach Arith) w
      ((Ts.length + 1) * 1)
    generalize hN : ((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length)
      (Ts.length * w)).1 = N at ih1 hlen p2 hq w2'
    obtain ⟨Y, L⟩ := N
    have hlen' : L.length = Ts.length := hlen
    have ih1' : ((⟨X, Ts ++ [s 0]⟩ : XMach Arith).trace xsys (fun i => i % (Ts.length + 1))
        ((Ts.length + 1) * w)).1 = ⟨Y, L ++ [s w]⟩ := ih1
    rw [ih1'] at p3 w3'
    have hq' : XMach.act xsys
        ((⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i % L.length) (L.length * 1)).1.mem (s w) =
        (((⟨Y, L⟩ : XMach Arith).trace xsys (fun i => i % L.length) (L.length * 1)).1.mem,
          s (w + 1), 0) := by
      rw [hlen']
      exact hq
    obtain ⟨t3, w3⟩ := sweep_end hq'
    rw [hlen'] at t3 w3
    constructor
    · rw [p3, p2]
      exact t3
    · rw [Nat.mul_add (Ts.length + 1) w 1, Nat.mul_add Ts.length w 1, w3', w2', ih2, w3]
      show _ = _ + (seqTally XThread.busy s w + XThread.busy (s w))
      omega

/-- **One more thread at the end that only reads and comes to rest adds
exactly its actions to the work of the others.** -/
theorem total_beside_end {X : XNet Arith} {Ts : List (XThread Arith)} (hpos : 0 < Ts.length)
    (s : Nat → XThread Arith)
    (hs : ∀ w, XMach.act xsys
        ((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * (w + 1))).1.mem
        (s w) =
      (((⟨X, Ts⟩ : XMach Arith).trace xsys (fun i => i % Ts.length) (Ts.length * (w + 1))).1.mem,
        s (w + 1), 0))
    {W b : Nat} (tot : (⟨X, Ts⟩ : XMach Arith).Total xsys (fun i => i % Ts.length) W)
    (h1 : ∀ j, j < b → s j ≠ ⟨[], .idle⟩) (h0 : ∀ j, b ≤ j → s j = ⟨[], .idle⟩) :
    (⟨X, Ts ++ [s 0]⟩ : XMach Arith).Total xsys (fun i => i % (Ts.length + 1)) (W + b) := by
  have q := beside_end s hs
  obtain ⟨N, hN⟩ := tot
  have st : ∀ a, b ≤ a → seqTally XThread.busy s a = b := fun a ha =>
    (seqTally_exact (B := b) (fun j hj => XThread.busy_of_ne_rest (h1 j hj))
      (fun j hj => by
        rw [h0 j hj]
        rfl) a).2 ha
  have even : ∀ v, N ≤ v → b ≤ v →
      (⟨X, Ts ++ [s 0]⟩ : XMach Arith).work xsys (fun i => i % (Ts.length + 1))
        ((Ts.length + 1) * v) = W + b := fun v hv hb => by
    have h1v : 1 * v ≤ Ts.length * v := Nat.mul_le_mul_right v hpos
    rw [(q v).2, st v hb, hN (Ts.length * v) (by omega)]
  refine ⟨(Ts.length + 1) * (N + b), fun i hi => ?_⟩
  have hc : 0 < Ts.length + 1 := Nat.succ_pos _
  have lo := XMach.work_mono (xs := xsys) (fun i => i % (Ts.length + 1))
    (⟨X, Ts ++ [s 0]⟩ : XMach Arith) (Nat.mul_div_le i (Ts.length + 1))
  have up := XMach.work_mono (xs := xsys) (fun i => i % (Ts.length + 1))
    (⟨X, Ts ++ [s 0]⟩ : XMach Arith) (Nat.le_of_lt (Nat.lt_mul_div_succ i hc))
  have hd : N + b ≤ i / (Ts.length + 1) :=
    (Nat.le_div_iff_mul_le hc).2 (by
      rw [Nat.mul_comm]
      exact hi)
  rw [even (i / (Ts.length + 1)) (by omega) (by omega)] at lo
  rw [even (i / (Ts.length + 1) + 1) (by omega) (by omega)] at up
  omega

/-- **An agent that is gone and that no thread can bring back stays gone**,
whatever the threads do and in whatever order. -/
theorem trace_gone {j : Nat} (hj : j ≠ 0) (σ : Nat → Nat) {M : XMach Arith}
    (h1 : assoc [j] M.mem.agents = none) (h2 : ∀ T, T ∈ M.ths → T.st.Clear [j]) :
    ∀ i, assoc [j] (M.trace xsys σ i).1.mem.agents = none ∧
      ∀ T, T ∈ (M.trace xsys σ i).1.ths → T.st.Clear [j]
  | 0 => ⟨h1, h2⟩
  | i + 1 => by
    obtain ⟨g, c⟩ := trace_gone hj σ h1 h2 i
    show assoc [j] ((M.trace xsys σ i).1.step xsys (σ i)).1.mem.agents = none ∧
      ∀ T, T ∈ ((M.trace xsys σ i).1.step xsys (σ i)).1.ths → T.st.Clear [j]
    generalize (M.trace xsys σ i).1 = N at g c
    cases hT : N.ths[σ i]? with
    | none =>
      have e : N.step xsys (σ i) = (N, 0) := by
        unfold XMach.step
        rw [hT]
      rw [e]
      exact ⟨g, c⟩
    | some T =>
      have e := XMach.step_eq (xs := xsys) (M := N) hT rfl
      rw [e]
      have ag := XMach.act_gone (xs := xsys) (x := [j])
        (fun hR he => single_ne_new hj (new_head hR he)) g (c T (List.mem_of_getElem? hT))
      exact ⟨ag.1, fun T' hT' => by
        rcases List.mem_or_eq_of_mem_set hT' with h | h
        · exact c T' h
        · rw [h]
          exact ag.2⟩

/-- A thread that is not holding an agent it has taken. -/
def Calm : TState Arith → Prop
  | .half _ _ _ _ => False
  | .write _ _ => False
  | _ => True

/-- A thread that is idle or reads the segment of an agent. -/
def St1 : TState Arith → Prop
  | .idle => True
  | .look _ _ => True
  | _ => False

theorem st1_reading {st : TState Arith} (h : St1 st) : st.Reading := by
  cases st <;> first | trivial | exact h.elim

theorem calm_clear {st : TState Arith} (h : Calm st) (x : Id) : st.Clear x := by
  cases st <;> first | trivial | exact h.elim

/-- **A thread that is idle or looking for a partner only reads**, in any
memory: its action changes nothing and makes no claim. -/
theorem act_reads (X : XNet Arith) {T : XThread Arith} (hT : T.st.Reading) :
    (XMach.act xsys X T).1 = X ∧ (XMach.act xsys X T).2.2 = 0 ∧
      Calm (XMach.act xsys X T).2.1.st := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨rfl, rfl, trivial⟩
    | cons e' rest =>
      by_cases h : assoc e'.1 X.agents = some e'.2
      · rw [XMach.act_idle_pos h]
        exact ⟨rfl, rfl, trivial⟩
      · rw [XMach.act_idle_neg h]
        exact ⟨rfl, rfl, trivial⟩
  | look a α =>
    cases h : assoc (a, 0) X.wires with
    | none =>
      rw [XMach.act_look_none h]
      exact ⟨rfl, rfl, trivial⟩
    | some q =>
      rw [XMach.act_look h]
      exact ⟨rfl, rfl, trivial⟩
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    split
    · split <;> exact ⟨rfl, rfl, trivial⟩
    · split <;> exact ⟨rfl, rfl, trivial⟩
  | ready a b α β => exact hT.elim
  | half a b α β => exact hT.elim
  | write as ls => exact hT.elim

theorem st1_of_idle (X : XNet Arith) {T : XThread Arith} (h : T.st = .idle) :
    St1 (XMach.act xsys X T).2.1.st := by
  obtain ⟨todo, st⟩ := T
  have h' : st = .idle := h
  subst h'
  cases todo with
  | nil => exact trivial
  | cons e' rest =>
    by_cases h : assoc e'.1 X.agents = some e'.2
    · rw [XMach.act_idle_pos h]
      exact trivial
    · rw [XMach.act_idle_neg h]
      exact trivial

theorem reading_of_st1 (X : XNet Arith) {T : XThread Arith} (h : St1 T.st) :
    (XMach.act xsys X T).2.1.st.Reading := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact trivial
    | cons e' rest =>
      by_cases h : assoc e'.1 X.agents = some e'.2
      · rw [XMach.act_idle_pos h]
        exact trivial
      · rw [XMach.act_idle_neg h]
        exact trivial
  | look a α =>
    cases h : assoc (a, 0) X.wires with
    | none =>
      rw [XMach.act_look_none h]
      exact trivial
    | some q =>
      rw [XMach.act_look h]
      exact trivial
  | seek a α p c => exact h.elim
  | ready a b α β => exact h.elim
  | half a b α β => exact h.elim
  | write as ls => exact h.elim

/-- A thread that holds no agent and whose action leaves the memory as it
is holds no agent after it. -/
theorem act_calm (X : XNet Arith) {T : XThread Arith} (hT : Calm T.st)
    (hr : (XMach.act xsys X T).1 = X) : Calm (XMach.act xsys X T).2.1.st := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle => exact (act_reads X (T := ⟨todo, .idle⟩) trivial).2.2
  | look a α => exact (act_reads X (T := ⟨todo, .look a α⟩) trivial).2.2
  | seek a α p c => exact (act_reads X (T := ⟨todo, .seek a α p c⟩) trivial).2.2
  | ready a b α β =>
    by_cases h : assoc a X.agents = some α
    · rw [XMach.act_ready h] at hr
      have hr' : X.takeAgent a = X := hr
      have g := assoc_takeAgent_self X a
      rw [hr', h] at g
      cases g
    · rw [XMach.act_ready_neg h]
      exact trivial
  | half a b α β => exact hT.elim
  | write as ls => exact hT.elim

theorem prod3 {A B C : Type} {x : A × B × C} {a : A} {b : B} {c : C} (h1 : x.1 = a)
    (h2 : x.2.1 = b) (h3 : x.2.2 = c) : x = (a, b, c) := by
  obtain ⟨x1, x2, x3⟩ := x
  have e1 : x1 = a := h1
  have e2 : x2 = b := h2
  have e3 : x3 = c := h3
  rw [e1, e2, e3]

/-- A thread that has only read beside the first holds no agent. -/
theorem reader_calm {m n : Nat} {T : XThread Arith} (hT : Calm T.st) :
    ∀ a, (∀ a', a' < a →
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a')).1 =
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1 ∧
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a')).2.2 = 0) →
      Calm (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a).st
  | 0, _ => hT
  | a + 1, h =>
    act_calm _ (reader_calm hT a (fun a' ha' => h a' (Nat.lt_succ_of_lt ha')))
      (h a (Nat.lt_succ_self a)).1

/-- **The three actions after a thread is idle read**, whatever the memory:
it takes at least four to be ready to take a pair. -/
theorem RdAt.three {m n : Nat} {T0 : XThread Arith} {a : Nat} {l : List (Id × Arith)}
    (h : RdAt m n T0 a ⟨l, .idle⟩) : ∀ a', a' < a + 3 →
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a')).1 =
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1 ∧
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a')).2.2 = 0 := by
  intro a' ha'
  have e0 : (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a).st =
      .idle := by rw [h.1]
  have r0 : (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a).st.Reading := by
    rw [e0]
    exact trivial
  have s1 : St1 (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0
      (a + 1)).st := st1_of_idle _ e0
  have r1 := st1_reading s1
  have r2 : (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0
      (a + 1 + 1)).st.Reading := reading_of_st1 _ s1
  by_cases c0 : a' < a
  · exact h.2 a' c0
  · have hc : a' = a ∨ a' = a + 1 ∨ a' = a + 1 + 1 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ⟨(act_reads _ r0).1, (act_reads _ r0).2.1⟩
    · exact ⟨(act_reads _ r1).1, (act_reads _ r1).2.1⟩
    · exact ⟨(act_reads _ r2).1, (act_reads _ r2).2.1⟩

theorem drop_succ' {A : Type} : ∀ (j : Nat) (l : List A), (l.drop j).drop 1 = l.drop (j + 1)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | j + 1, _ :: l => drop_succ' j l

/-- A thread that follows the states `R` for `a0` actions and then pops the
agents of `tops`, one at each action. -/
def thenPops (R : Nat → XThread Arith) (a0 : Nat) (tops : List (Id × Arith)) (w : Nat) :
    XThread Arith :=
  if w ≤ a0 then R w else ⟨tops.drop (w - a0), .idle⟩

theorem thenPops_le {R : Nat → XThread Arith} {a0 : Nat} {tops : List (Id × Arith)} {w : Nat}
    (h : w ≤ a0) : thenPops R a0 tops w = R w := ite_pos' h

theorem thenPops_gt {R : Nat → XThread Arith} {a0 : Nat} {tops : List (Id × Arith)} {w : Nat}
    (h : a0 < w) : thenPops R a0 tops w = ⟨tops.drop (w - a0), .idle⟩ :=
  ite_neg' (by omega)

/-- The successors at the end of the list of a thread. -/
theorem mem_tops {n r0 : Nat} : ∀ (s : Nat) (e : Id × Arith),
    e ∈ (chainL n (r0 + (s + 1))).take (s + 1) →
      ∃ r, r0 ≤ r ∧ r ≤ r0 + s ∧ e = ([n + 3 + r + 1], Arith.succ)
  | 0, e, he => by
    have he' : e ∈ [(([n + 3 + r0 + 1], Arith.succ) : Id × Arith)] := he
    rcases List.mem_cons.1 he' with rfl | h
    · exact ⟨r0, Nat.le_refl _, Nat.le_refl _, rfl⟩
    · cases h
  | s + 1, e, he => by
    have he' : e ∈ (([n + 3 + (r0 + (s + 1)) + 1], Arith.succ) : Id × Arith) ::
        (chainL n (r0 + (s + 1))).take (s + 1) := he
    rcases List.mem_cons.1 he' with rfl | h
    · exact ⟨r0 + (s + 1), by omega, by omega, rfl⟩
    · obtain ⟨r, a, b, c⟩ := mem_tops s e h
      exact ⟨r, a, by omega, c⟩

theorem tops_length (n r0 : Nat) : ∀ s, ((chainL n (r0 + (s + 1))).take (s + 1)).length = s + 1
  | 0 => rfl
  | s + 1 => by
    show ((([n + 3 + (r0 + (s + 1)) + 1], Arith.succ) : Id × Arith) ::
      (chainL n (r0 + (s + 1))).take (s + 1)).length = s + 1 + 1
    exact congrArg (· + 1) (tops_length n r0 s)

/-- From its fifth action on the first thread cannot bring the top
successor back. -/
theorem solo_clear5 (m n : Nat) {u : Nat} (hu : 5 ≤ u) :
    (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).2.st.Clear
      [n + 3 + m + 1] := by
  have st := start_sum m n
  obtain ⟨-, rest, as, ls, e5, has⟩ := st.five
  have eT : n + 3 + m + 1 = m + n + 3 + 1 := by omega
  have hne : ([m + n + 3 + 1] : Id) ≠ [1] := fun e => by
    injection e with e1
    omega
  have g1 : assoc [m + n + 3 + 1] (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ 5).1.agents = none := by
    rw [e5]
    show assoc [m + n + 3 + 1] (((sum (m + 1) n).agents.filter
      fun e => decide (e.1 ≠ [m + n + 3 + 1])).filter fun e => decide (e.1 ≠ [1])) = none
    rw [assoc_filter_ne, ite_neg' (fun e => hne e.symm), assoc_filter_ne, ite_pos' rfl]
  have c1 : (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ 5).2.st.Clear [m + n + 3 + 1] := by
    rw [e5]
    exact fun e he => single_ne_new (by omega) (has e he)
  have k1 := (XMach.solo_gone (xs := xsys) (x := [m + n + 3 + 1])
    (fun hR he => single_ne_new (by omega) (new_head hR he)) g1 c1 (u - 5)).2
  rw [show 5 + (u - 5) = u by omega] at k1
  rw [eT]
  exact k1

/-- Nor a successor of the chain, once its round has taken it. -/
theorem solo_clear_succ (m n : Nat) {d : Nat} (h1 : 1 ≤ d) (h2 : d ≤ m) {u : Nat}
    (hu : 17 * d + 5 ≤ u) :
    (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).2.st.Clear
      [n + 3 + m + 1 - d] := by
  obtain ⟨X1, w1, st⟩ := solo_steady m n (d - 1) (m + n + 4 - d) (by omega) (by omega)
  obtain ⟨h, eh⟩ : ∃ h, m + n + 4 - d = h + 1 := ⟨m + n + 3 - d, by omega⟩
  rw [eh] at st
  have hn : n + 4 ≤ h + 1 := by omega
  obtain ⟨rest, hA⟩ := st.head
  have hb : below n (h + 1) = [h + 1] := below_pos hn
  have hne : ([0, h + 1 + 1] : Id) ≠ [h + 1] := fun e => by
    injection e with _ e2
    cases e2
  have h₁ : assoc [0, h + 1 + 1] X1.agents = some .add := by
    rw [hA]
    show (if ([0, h + 1 + 1] : Id) = [0, h + 1 + 1] then some Arith.add
      else assoc _ rest) = _
    rw [ite_pos' rfl]
  have h₂ : assoc (([0, h + 1 + 1], 0) : Port) X1.wires = some ([h + 1 + 1], 1) :=
    assoc_eq_of_unique ((st.first _).2 rfl) (fun q' hq => (st.first q').1 hq)
  have h₂' : nextSeg X1.wires ([h + 1 + 1], 1) ([0, h + 1 + 1], 0) = some ([h + 1], 0) := by
    refine nextSeg_some ((st.mid _).2 (.inr (by rw [hb]))) (fun e => ?_) (fun q hq hqp => ?_)
    · injection e with e1 _
      injection e1 with _ e2
      cases e2
    · rcases (st.mid q).1 hq with e | e
      · exact absurd e hqp
      · rw [e, hb]
  have h₃ : assoc [h + 1] X1.agents = some .succ := st.chain.live (h + 1) hn (Nat.le_refl _)
  have h₄ : assoc [h + 1] (X1.takeAgent [0, h + 1 + 1]).agents = some .succ := by
    show assoc [h + 1] (X1.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact h₃
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w2 := Works.via_start (xs := xsys) (c := ([h + 1 + 1], 1)) rest h₁ h₂ rfl h₂' h₃ hne h₄
    hR
  rw [← hA] at w2
  have e22 := (w1.trans w2).solo.1
  have g : assoc [h + 1] (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ (16 + 17 * (d - 1) + 6)).1.agents = none := by
    rw [e22]
    show assoc [h + 1] ((X1.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])).filter
      fun e => decide (e.1 ≠ [h + 1])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have c : (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ (16 + 17 * (d - 1) + 6)).2.st.Clear [h + 1] := by
    rw [e22]
    exact fun e he => single_ne_new (by omega) (new_head hR he)
  have k := (XMach.solo_gone (xs := xsys) (x := [h + 1])
    (fun hR he => single_ne_new (by omega) (new_head hR he)) g c (u - (17 * d + 5))).2
  rw [show 16 + 17 * (d - 1) + 6 + (u - (17 * d + 5)) = u by omega] at k
  rw [show n + 3 + m + 1 - d = h + 1 by omega]
  exact k

theorem solo_clear_top (m n : Nat) {q u : Nat} (hq : q ≤ m) (hu : 17 * (m - q) + 5 ≤ u) :
    (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).2.st.Clear
      [n + 3 + q + 1] := by
  by_cases e : q = m
  · subst e
    exact solo_clear5 q n (by omega)
  · have hg := solo_clear_succ m n (d := m - q) (by omega) (by omega) hu
    rw [show n + 3 + m + 1 - (m - q) = n + 3 + q + 1 by omega] at hg
    exact hg

/-- With one thread more, the threads are those of the program before and
the new one at the end. -/
theorem init_snoc (X : XNet Arith) (k : Nat) :
    XMach.init X (k + 1 + 1) = ⟨X, (XMach.init X (k + 1)).ths ++
      [⟨X.agents.drop (k + 1) ++ X.agents.take (k + 1), .idle⟩]⟩ := by
  rw [XMach.init_succ, XMach.init_succ, List.range_succ, List.map_append]
  rfl

theorem init_len (X : XNet Arith) (n : Nat) : (XMach.init X n).ths.length = n := by
  show ((List.range n).map fun t =>
    (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread Arith)).length = n
  rw [List.length_map, List.length_range]

/-- **One more thread of the program that only reads and comes to rest adds
exactly its actions to the work of the others.** -/
theorem init_total_end (X : XNet Arith) (k : Nat) (s : Nat → XThread Arith)
    (e0 : s 0 = ⟨X.agents.drop (k + 1) ++ X.agents.take (k + 1), .idle⟩)
    (hs : ∀ w, XMach.act xsys
        ((XMach.init X (k + 1)).trace xsys (fun i => i % (k + 1)) ((k + 1) * (w + 1))).1.mem
        (s w) =
      (((XMach.init X (k + 1)).trace xsys (fun i => i % (k + 1)) ((k + 1) * (w + 1))).1.mem,
        s (w + 1), 0))
    {W b : Nat} (tot : (XMach.init X (k + 1)).Total xsys (fun i => i % (k + 1)) W)
    (h1 : ∀ j, j < b → s j ≠ ⟨[], .idle⟩) (h0 : ∀ j, b ≤ j → s j = ⟨[], .idle⟩) :
    (XMach.init X (k + 1 + 1)).Total xsys (fun i => i % (k + 1 + 1)) (W + b) := by
  have hl : (XMach.init X (k + 1)).ths.length = k + 1 := init_len X (k + 1)
  have hmem : (XMach.init X (k + 1)).mem = X := rfl
  rw [init_snoc, ← e0]
  generalize XMach.init X (k + 1) = M at hs tot hl hmem ⊢
  obtain ⟨Y, Ts⟩ := M
  have hY : Y = X := hmem
  subst hY
  have hl' : Ts.length = k + 1 := hl
  rw [← hl'] at hs tot ⊢
  exact total_beside_end (by
    rw [hl']
    exact Nat.succ_pos _) s hs tot h1 h0

/-- **A thread that passes the zero of the first argument before the race
only reads, whatever the threads before it do.**  On the net for
`(m + 1) + n`, `n` not zero, take `k + 2` threads in turn with `k + 2 ≤ m`.
If the last of them comes to that zero after `17 * m + 6` actions at most,
and to its `k + 1` top successors after their rounds, its states `s` are
these: each of its actions leaves the memory as it is, and it is at rest
after exactly `turnAt m n k + 3 + 3 + (k + 1)` actions, three for that
zero, three for the zero of the second argument and one for each top
successor, which is gone for good. -/
theorem early_reader_end (m n' k : Nat) (hm : k + 2 ≤ m)
    (hA : turnAt m (n' + 1) k ≤ 17 * m + 6) (hG : 17 * k ≤ turnAt m (n' + 1) k + 1) :
    ∃ s : Nat → XThread Arith, s 0 = (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith) ∧
      (∀ w, XMach.act xsys ((XMach.init (sum (m + 1) (n' + 1)) (k + 1)).trace xsys (fun i => i % (k + 1)) ((k + 1) * (w + 1))).1.mem (s w) =
        (((XMach.init (sum (m + 1) (n' + 1)) (k + 1)).trace xsys (fun i => i % (k + 1)) ((k + 1) * (w + 1))).1.mem, s (w + 1), 0)) ∧
      (∀ j, j < turnAt m (n' + 1) k + 3 + 3 + (k + 1) → s j ≠ ⟨[], .idle⟩) ∧
      (∀ j, turnAt m (n' + 1) k + 3 + 3 + (k + 1) ≤ j → s j = ⟨[], .idle⟩) := by
  obtain ⟨K, hK⟩ : ∃ K, (3 * (m - k) + 11) / 16 = K + 1 :=
    ⟨(3 * (m - k) + 11) / 16 - 1, by omega⟩
  have eA : turnAt m (n' + 1) k = 3 * (m - k) + 3 * n' + 5 + K := by
    unfold turnAt
    omega
  rw [XMach.init_succ, eA]
  rw [eA] at hA hG
  have q0 := turn_reader_at_zero m n' k K (by omega) (by omega) (by omega)
  have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * (m - k) + 3 * n' + 5 + K + 1) (by omega) (by omega)
    (by omega) (sum_zero_agent m (n' + 1))
  have q1 := q0.pass3 hal (solo_look_two m (n' + 1) _) (show ¬ (1 : Nat) = 0 by decide)
    ((solo_seek_two m (n' + 1) (by omega) _).2 (by omega))
  have hx3 : assoc [3] (sum (m + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base m (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have q2 := q1.pass3 (solo_snd_forever m (n' + 1) (j := 3) (by omega) (by omega) hx3 _)
    (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).1
    (show ¬ (1 : Nat) = 0 by decide)
    (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).2
  rw [← turn_list_succ m n' k (by omega)] at q2
  have hlenT : ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))).length = k := by
    rw [List.length_map, List.length_range]
  have hL : (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length = k + 1 := by
    show ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))).length + 1 = k + 1
    rw [hlenT]
  have hRds : ∀ T, T ∈ ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))) → ∀ a, a < 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 →
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (a + 1)).1 (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ T a)).1 = (XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (a + 1)).1 ∧
        (XMach.act xsys (XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (a + 1)).1 (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ T a)).2.2 = 0 := by
    intro T hT a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT
    have htk : t < k := List.mem_range.1 ht
    obtain ⟨Kt, hKt⟩ : ∃ K, (3 * (m - t) + 11) / 16 = K + 1 :=
      ⟨(3 * (m - t) + 11) / 16 - 1, by omega⟩
    have qt := turn_reader_at_zero m n' t Kt (by omega) (by omega) (by omega)
    rw [← turn_list_succ m n' t (by omega)] at qt
    exact qt.three a (by omega)
  have hcalm : ∀ T, T ∈ ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))) → ∀ a, a ≤ 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 →
      Calm (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ T a).st := by
    intro T hT a ha
    have hc : Calm T.st := by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      exact trivial
    exact reader_calm hc a (fun a' ha' => hRds T hT a' (by omega))
  have trB : ∀ a, a ≤ 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 →
      ((⟨(sum (m + 1) (n' + 1)), (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))))⟩ : XMach Arith).trace xsys (fun i => i % (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length) ((⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length * (a))).1 =
        ⟨(XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (a)).1, (XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (a)).2 ::
          ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))).map fun T => XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ T a⟩ := fun a ha =>
    congrArg Prod.fst (XMach.trace_readers (xs := xsys) (X := (sum (m + 1) (n' + 1)))
      (T₀ := ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩) (Ts := ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))) (A := 3 * (m - k) + 3 * n' + 5 + K + 3 + 3) hRds a ha)
  have hlenTops : ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).length = k + 1 := tops_length (n' + 1) (m - k) k
  have gone : ∀ e, e ∈ ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)) → ∀ v, 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 ≤ v →
      assoc e.1 ((⟨(sum (m + 1) (n' + 1)), (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))))⟩ : XMach Arith).trace xsys (fun i => i % (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length) ((⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length * (v))).1.mem.agents = none := by
    intro e he v hv
    obtain ⟨r, hr1, hr2, rfl⟩ := mem_tops k e he
    obtain ⟨d, rfl⟩ : ∃ d, v = 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + d := ⟨v - (3 * (m - k) + 3 * n' + 5 + K + 3 + 3), by omega⟩
    rw [trace_mod_add (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length (⟨(sum (m + 1) (n' + 1)), (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))))⟩ : XMach Arith) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) d, trB (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) (Nat.le_refl _)]
    exact (trace_gone (j := n' + 1 + 3 + r + 1) (by omega) (fun i => i % (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length)
      (M := ⟨(XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (3 * (m - k) + 3 * n' + 5 + K + 3 + 3)).1, (XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (3 * (m - k) + 3 * n' + 5 + K + 3 + 3)).2 ::
        ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))).map fun T => XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ T (3 * (m - k) + 3 * n' + 5 + K + 3 + 3)⟩)
      (solo_gone_top m (n' + 1) (by omega) (by omega))
      (fun T hT => by
        rcases List.mem_cons.1 hT with e | hT
        · rw [e]
          exact solo_clear_top m (n' + 1) (by omega) (by omega)
        · obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hT
          exact calm_clear (hcalm T' hT' (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) (Nat.le_refl _)) _)
      ((⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length * d)).1
  have hs : ∀ w, XMach.act xsys ((⟨(sum (m + 1) (n' + 1)), (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))))⟩ : XMach Arith).trace xsys (fun i => i % (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length) ((⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length * (w + 1))).1.mem ((thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))) w) =
      (((⟨(sum (m + 1) (n' + 1)), (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))))⟩ : XMach Arith).trace xsys (fun i => i % (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length) ((⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length * (w + 1))).1.mem, (thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))) (w + 1), 0) := by
    intro w
    by_cases hw : w < 3 * (m - k) + 3 * n' + 5 + K + 3 + 3
    · have em : ((⟨(sum (m + 1) (n' + 1)), (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))))⟩ : XMach Arith).trace xsys (fun i => i % (⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length) ((⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ :: ((List.range k).map (fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith)))).length * (w + 1))).1.mem = (XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (w + 1)).1 :=
        congrArg XMach.mem (trB (w + 1) (by omega))
      rw [em, thenPops_le (show w ≤ 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 by omega), thenPops_le (show w + 1 ≤ 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 by omega)]
      exact prod3 (q2.2 w hw).1 rfl (q2.2 w hw).2
    · obtain ⟨d, rfl⟩ : ∃ d, w = 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + d := ⟨w - (3 * (m - k) + 3 * n' + 5 + K + 3 + 3), by omega⟩
      have e1 : (thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + d) = ⟨((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).drop d, .idle⟩ := by
        by_cases hd : d = 0
        · subst hd
          show (thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) = ⟨((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)), .idle⟩
          rw [thenPops_le (Nat.le_refl _)]
          exact q2.1
        · rw [thenPops_gt (by omega), show 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + d - (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) = d by omega]
      have e2 : (thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + d + 1) = ⟨((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).drop (d + 1), .idle⟩ := by
        rw [thenPops_gt (by omega), show 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + d + 1 - (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) = d + 1 by omega]
      rw [e1, e2]
      cases hdr : ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).drop d with
      | nil =>
        have e3 : ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).drop (d + 1) = [] :=
          (drop_succ' d ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))).symm.trans (congrArg (List.drop 1) hdr)
        rw [e3]
        rfl
      | cons e L' =>
        have e3 : ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).drop (d + 1) = L' :=
          (drop_succ' d ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))).symm.trans (congrArg (List.drop 1) hdr)
        rw [e3]
        have he : e ∈ ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)) := List.mem_of_mem_drop (by
          rw [hdr]
          exact List.mem_cons_self)
        exact XMach.act_idle_neg (e := e) (fun h => by
          rw [gone e he (3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + d + 1) (by omega)] at h
          cases h)
  have hne0 : XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ≠ ⟨[], .idle⟩ := fun e => by
    rw [q2.1] at e
    have e' : ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).length = 0 := congrArg (fun T : XThread Arith => T.todo.length) e
    omega
  have h1 : ∀ j, j < 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + (k + 1) → (thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))) j ≠ ⟨[], .idle⟩ := by
    intro j hj
    by_cases c : j ≤ 3 * (m - k) + 3 * n' + 5 + K + 3 + 3
    · rw [thenPops_le c]
      exact reader_busy_upto (X := (sum (m + 1) (n' + 1))) (F0 := ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩) (T0 := (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith))
        (b := 3 * (m - k) + 3 * n' + 5 + K + 3 + 3) hne0 j c
    · rw [thenPops_gt (by omega)]
      intro e
      have e' : (((chainL (n' + 1) (m - k + (k + 1))).take (k + 1)).drop (j - (3 * (m - k) + 3 * n' + 5 + K + 3 + 3))).length = 0 :=
        congrArg (fun T : XThread Arith => T.todo.length) e
      rw [List.length_drop, hlenTops] at e'
      omega
  have h0 : ∀ j, 3 * (m - k) + 3 * n' + 5 + K + 3 + 3 + (k + 1) ≤ j → (thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))) j = ⟨[], .idle⟩ := by
    intro j hj
    rw [thenPops_gt (by omega), List.drop_eq_nil_of_le (by
      rw [hlenTops]
      omega)]
  rw [hL] at hs
  exact ⟨(thenPops (XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩ (⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++ (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)) (3 * (m - k) + 3 * n' + 5 + K + 3 + 3) ((chainL (n' + 1) (m - k + (k + 1))).take (k + 1))), thenPops_le (Nat.zero_le _), hs, h1, h0⟩

/-- **A thread that passes the zero of the first argument before the race
adds exactly its own actions to the work of the threads before it**:
`turnRest m n k` actions, under the conditions above. -/
theorem threads_early_last (m n' k W : Nat) (hm : k + 2 ≤ m)
    (hA : turnAt m (n' + 1) k ≤ 17 * m + 6) (hG : 17 * k ≤ turnAt m (n' + 1) k + 1)
    (tot : (XMach.init (sum (m + 1) (n' + 1)) (k + 1)).Total xsys (fun i => i % (k + 1)) W) :
    (XMach.init (sum (m + 1) (n' + 1)) (k + 1 + 1)).Total xsys (fun i => i % (k + 1 + 1))
      (W + turnRest m (n' + 1) k) := by
  obtain ⟨s, e0, hs, h1, h0⟩ := early_reader_end m n' k hm hA hG
  have eR : turnRest m (n' + 1) k =
      turnAt m (n' + 1) k + zeroCost m (turnAt m (n' + 1) k) + 3 + (k + 1) := rfl
  have ez : zeroCost m (turnAt m (n' + 1) k) = 3 := by
    unfold zeroCost
    exact ite_pos' hA
  rw [eR, ez]
  exact init_total_end (sum (m + 1) (n' + 1)) k s e0 hs tot h1 h0

/-- **What four threads in turn do in all on the net for `(m + 1) + n`**:
the race of the first and the fourth thread with the two others reading
beside them; or what three threads do and the actions of the fourth, which
passes the zero of the first argument before the race; or the work of one
thread and the actions of three readers. -/
def fourWork (m n : Nat) : Nat :=
  if 17 * m + 7 ≤ turnAt m n 2 ∧ turnAt m n 2 ≤ 17 * m + 16 then
    raceWork m n (turnAt m n 2 - (17 * m + 7)) +
      (if turnAt m n 2 = 17 * m + 15 then 2 else 0) + (turnAt m n 1 + 9) + (turnAt m n 0 + 5)
  else if turnAt m n 2 ≤ 17 * m + 6 then threeWork m n + turnRest m n 2
  else soloWork (m + 1) n + turnSum m n 3

/-- **Four threads in turn, every size, to the action.**  On the net for
`(m + 1) + n`, with `m` from four on and `39 ≤ 3 * m + 3 * n`, four threads
acting in turn make exactly `fourWork m n` actions that are not rests. -/
theorem four_threads_total (m n : Nat) (hm : 4 ≤ m) (hn : 39 ≤ 3 * m + 3 * n) :
    (XMach.init (sum (m + 1) n) 4).Total xsys (fun i => i % 4) (fourWork m n) := by
  unfold fourWork
  by_cases c1 : 17 * m + 7 ≤ turnAt m n 2 ∧ turnAt m n 2 ≤ 17 * m + 16
  · rw [ite_pos' c1]
    exact four_threads_race_last m n hm c1.1 c1.2
  · rw [ite_neg' c1]
    by_cases c2 : turnAt m n 2 ≤ 17 * m + 6
    · rw [ite_pos' c2]
      cases n with
      | zero =>
        have n1 : ¬ (17 * m + 7 ≤ turnAt m 0 1 ∧ turnAt m 0 1 ≤ 17 * m + 16) := by
          unfold turnAt
          omega
        have n0 : ¬ (17 * m + 7 ≤ turnAt m 0 0 ∧ turnAt m 0 0 ≤ 17 * m + 16) := by
          unfold turnAt
          omega
        have e3 : threeWork m 0 = soloWork (m + 1) 0 + turnSum m 0 2 := by
          unfold threeWork
          rw [ite_neg' n1, ite_neg' n0]
        rw [e3]
        exact (threads_total m 0 3 (by omega) (by omega) (fun t ht => .inl (by
          unfold turnAt
          omega))).cast (by
            show soloWork (m + 1) 0 + (turnSum m 0 2 + turnRest m 0 2) = _
            omega)
      | succ n' =>
        exact threads_early_last m n' 2 (threeWork m (n' + 1)) (by omega) c2 (by
          unfold turnAt
          omega) (three_threads_total m (n' + 1) hm (by omega))
    · rw [ite_neg' c2]
      exact threads_total m n 3 (by omega) (by omega) (fun t ht => .inr (by
        have h3 : 17 * m + 17 ≤ turnAt m n 2 := by omega
        have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
        unfold turnAt at h3 ⊢
        rcases ht' with rfl | rfl | rfl <;> omega))

example : (XMach.init (sum 7 28) 4).Total xsys (fun i => i % 4) 578 :=
  (four_threads_total 6 28 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 30) 4).Total xsys (fun i => i % 4) 725 :=
  (four_threads_total 6 30 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 31) 4).Total xsys (fun i => i % 4) 740 :=
  (four_threads_total 6 31 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 32) 4).Total xsys (fun i => i % 4) 752 :=
  (four_threads_total 6 32 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 35) 4).Total xsys (fun i => i % 4) 662 :=
  (four_threads_total 6 35 (by decide) (by decide)).cast (by decide)

/-- The actions before they rest of the `k` threads from the one numbered
`j + 1` on, when they only read. -/
def turnSumFrom (m n j : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => turnSumFrom m n j k + turnRest m n (j + k)

/-- **Any number of threads that pass the zero of the first argument
before the race add exactly their own actions.**  On the net for
`(m + 1) + n`, `n` not zero: if the thread numbered `j + 1` comes to that
zero after `17 * m + 6` actions at most, so do the `k` threads from it on,
and `j + k + 1` threads in turn do the work of the first `j + 1` and
`turnRest m n t` for each of the others. -/
theorem threads_early_many (m n' j W : Nat) (hA : turnAt m (n' + 1) j ≤ 17 * m + 6)
    (tot : (XMach.init (sum (m + 1) (n' + 1)) (j + 1)).Total xsys (fun i => i % (j + 1)) W) :
    ∀ k, j + k + 1 ≤ m → 20 * (j + k) ≤ 3 * m + 3 * (n' + 1) + 23 →
      (XMach.init (sum (m + 1) (n' + 1)) (j + k + 1)).Total xsys (fun i => i % (j + k + 1))
        (W + turnSumFrom m (n' + 1) j k)
  | 0, _, _ => tot
  | k + 1, hm, hk => by
    have ih := threads_early_many m n' j W hA tot k (by omega) (by omega)
    have h := threads_early_last m n' (j + k) (W + turnSumFrom m (n' + 1) j k) (by omega)
      (by
        unfold turnAt at hA ⊢
        omega)
      (by
        unfold turnAt
        omega) ih
    exact h.cast (Nat.add_assoc _ _ _)

/-- **Five threads or more in turn, to the action, when the fifth passes the
zero of the first argument before the race.**  The work is that of four
threads and `turnRest m n t` for each thread from the fifth on. -/
theorem threads_beyond_four (m n' k : Nat) (hm : 4 ≤ m) (hn : 39 ≤ 3 * m + 3 * (n' + 1))
    (hA : turnAt m (n' + 1) 3 ≤ 17 * m + 6) (hk : 3 + k + 1 ≤ m)
    (hk2 : 20 * (3 + k) ≤ 3 * m + 3 * (n' + 1) + 23) :
    (XMach.init (sum (m + 1) (n' + 1)) (3 + k + 1)).Total xsys (fun i => i % (3 + k + 1))
      (fourWork m (n' + 1) + turnSumFrom m (n' + 1) 3 k) :=
  threads_early_many m n' 3 (fourWork m (n' + 1)) hA (four_threads_total m (n' + 1) hm hn) k hk
    hk2

example : (XMach.init (sum 8 36) 5).Total xsys (fun i => i % 5) 984 :=
  (threads_beyond_four 7 35 1 (by decide) (by decide) (by decide) (by decide) (by decide)).cast
    (by decide)

example : (XMach.init (sum 14 64) 6).Total xsys (fun i => i % 6) 1956 :=
  (threads_beyond_four 13 63 2 (by decide) (by decide) (by decide) (by decide) (by decide)).cast
    (by decide)

end Arith

end INet
