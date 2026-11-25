import InteractionNets.Arith.FourThreads

/-! ### Any number of threads in turn on an addition, to the action -/

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

/-- What a thread that reads the agents of the second argument below its
top needs of a memory: they are there, the first adder is gone, and each
has one segment, to the next, at which no other segment starts. -/
structure LateMem (n : Nat) (Y : XNet Arith) : Prop where
  mem : SndMem n Y
  look : ∀ j, 3 ≤ j → j ≤ n + 2 → assoc (([j], 0) : Port) Y.wires = some ([j + 1], 1)
  stop : ∀ j, 3 ≤ j → j ≤ n + 2 → nextSeg Y.wires ([j + 1], 1) ([j], 0) = none

section ViewsLate

variable {m n : Nat} {Y0 Y1 Y2 Y3 Y4 : XNet Arith}

theorem RaceViews.late0 (V : RaceViews n Y0 Y1 Y2 Y3 Y4)
    (F : Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m) : LateMem n Y0 :=
  ⟨V.m0, fun j h1 h2 => assoc_eq_of_unique (V.snd0 j h1 h2) fun q' hq =>
      (F.up (snd_sum (m + 1) n) h1 h2 q').1 (V.sub34 _ (V.sub23 _ (V.sub12 _ (V.sub01 _ hq)))),
    fun _ h1 h2 => nextSeg_none fun q hq =>
      (F.down (snd_sum (m + 1) n) h1 h2 q).1 (V.sub34 _ (V.sub23 _ (V.sub12 _ (V.sub01 _ hq))))⟩

theorem RaceViews.late1 (V : RaceViews n Y0 Y1 Y2 Y3 Y4)
    (F : Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m) : LateMem n Y1 :=
  ⟨V.m1, fun j h1 h2 => assoc_eq_of_unique (V.sub01 _ (V.snd0 j h1 h2)) fun q' hq =>
      (F.up (snd_sum (m + 1) n) h1 h2 q').1 (V.sub34 _ (V.sub23 _ (V.sub12 _ hq))),
    fun _ h1 h2 => nextSeg_none fun q hq =>
      (F.down (snd_sum (m + 1) n) h1 h2 q).1 (V.sub34 _ (V.sub23 _ (V.sub12 _ hq)))⟩

theorem RaceViews.late2 (V : RaceViews n Y0 Y1 Y2 Y3 Y4)
    (F : Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m) : LateMem n Y2 :=
  ⟨V.m2, fun j h1 h2 => assoc_eq_of_unique (V.sub12 _ (V.sub01 _ (V.snd0 j h1 h2))) fun q' hq =>
      (F.up (snd_sum (m + 1) n) h1 h2 q').1 (V.sub34 _ (V.sub23 _ hq)),
    fun _ h1 h2 => nextSeg_none fun q hq =>
      (F.down (snd_sum (m + 1) n) h1 h2 q).1 (V.sub34 _ (V.sub23 _ hq))⟩

theorem RaceViews.late3 (V : RaceViews n Y0 Y1 Y2 Y3 Y4)
    (F : Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m) : LateMem n Y3 :=
  ⟨V.m3, fun j h1 h2 => assoc_eq_of_unique (V.sub23 _ (V.sub12 _ (V.sub01 _ (V.snd0 j h1 h2))))
      fun q' hq => (F.up (snd_sum (m + 1) n) h1 h2 q').1 (V.sub34 _ hq),
    fun _ h1 h2 => nextSeg_none fun q hq =>
      (F.down (snd_sum (m + 1) n) h1 h2 q).1 (V.sub34 _ hq)⟩

theorem RaceViews.late4 (V : RaceViews n Y0 Y1 Y2 Y3 Y4)
    (F : Final n (sum (m + 1) n) Y4 (n + 3 + m + 1) m) : LateMem n Y4 :=
  ⟨V.m4, fun j h1 h2 => assoc_eq_of_unique
      (V.sub34 _ (V.sub23 _ (V.sub12 _ (V.sub01 _ (V.snd0 j h1 h2)))))
      fun q' hq => (F.up (snd_sum (m + 1) n) h1 h2 q').1 hq,
    fun _ h1 h2 => nextSeg_none fun q hq => (F.down (snd_sum (m + 1) n) h1 h2 q).1 hq⟩

end ViewsLate

/-- The memory of one thread alone is such a memory from its fifth action
on. -/
theorem solo_lateMem (m n u : Nat) (hu : 5 ≤ u) :
    LateMem n (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1 := by
  have hx3 : assoc [3] (sum (m + 1) n).agents = some Arith.zero :=
    sum_assoc_base m n (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  refine ⟨⟨solo_snd_forever m n (j := 3) (by omega) (by omega) hx3 u, fun j h4 hj => ?_,
    (solo_gone5 m n hu).2⟩, fun j h1 h2 => (solo_look_snd m n h1 h2 u).1,
    fun j h1 h2 => (solo_look_snd m n h1 h2 u).2⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
  have hx : assoc [k + 4] (sum (m + 1) n).agents = some Arith.succ :=
    sum_assoc_base m n (e := ([k + 4], Arith.succ))
      (List.mem_append_left _ (sndL_mem n k (by omega)))
  exact solo_snd_forever m n (j := k + 4) (by omega) (by omega) hx u

/-- A thread inside the second argument, with `x` of its agents left
below the one in hand: idle, on its way from the agent in hand, or reading
its segment. -/
def LS (tq : List (Id × Arith)) (x : Nat) : Nat → XThread Arith
  | 0 => ⟨sndL x ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq), .idle⟩
  | 1 => ⟨sndL x ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq),
      .seek [x + 4] .succ ([x + 4], 0) ([x + 4 + 1], 1)⟩
  | _ => ⟨sndL x ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq), .look [x + 4] .succ⟩

/-- **The path of a thread that reads down the second argument and past the
zeros**, by the number of actions it has left before it comes to its top
successors `tq`: three for each agent of the second argument, one for the
first adder, one for the zero of the first argument, three for the zero of
the second. -/
def LP (tq : List (Id × Arith)) : Nat → XThread Arith
  | 0 => ⟨tq, .idle⟩
  | 1 => ⟨tq, .seek [3] .zero ([3], 0) ([4], 1)⟩
  | 2 => ⟨tq, .look [3] .zero⟩
  | 3 => ⟨([3], .zero) :: tq, .idle⟩
  | 4 => ⟨([2], .zero) :: ([3], .zero) :: tq, .idle⟩
  | ρ + 5 => LS tq (ρ / 3) (ρ % 3)

theorem LP_idle (tq : List (Id × Arith)) (x : Nat) :
    LP tq (3 * x + 5) =
      ⟨sndL x ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) :: tq), .idle⟩ := by
  have e1 : 3 * x / 3 = x := by omega
  have e2 : 3 * x % 3 = 0 := by omega
  show LS tq (3 * x / 3) (3 * x % 3) = _
  rw [e1, e2]
  rfl

/-- **One action along the path**, in a memory that has the second argument
and not the first adder, and not the zero of the first argument when the
thread comes to it. -/
theorem LP_step {n : Nat} {Y : XNet Arith} (hY : LateMem n Y) (hn : 2 ≤ n)
    (tq : List (Id × Arith)) : ∀ ρ, ρ + 1 ≤ 3 * n + 2 →
      (ρ = 3 → assoc [2] Y.agents = none) →
      XMach.act xsys Y (LP tq (ρ + 1)) = (Y, LP tq ρ, 0)
  | 0, _, _ => XMach.act_seek_stop (seek_aux_none Y _ 1 (by decide))
      (hY.stop 3 (by omega) (by omega))
  | 1, _, _ => XMach.act_look (hY.look 3 (by omega) (by omega))
  | 2, _, _ => XMach.act_idle_pos (e := ([3], Arith.zero)) hY.mem.three
  | 3, _, h2 => XMach.act_idle_neg (e := ([2], Arith.zero)) (by
      show ¬ assoc [2] Y.agents = some Arith.zero
      rw [h2 rfl]
      exact fun h => by cases h)
  | 4, _, _ => XMach.act_idle_neg (e := ([1], Arith.add)) (by
      show ¬ assoc [1] Y.agents = some Arith.add
      rw [hY.mem.one]
      exact fun h => by cases h)
  | ρ + 5, hb, _ => by
    show XMach.act xsys Y (LS tq ((ρ + 1) / 3) ((ρ + 1) % 3)) = (Y, LS tq (ρ / 3) (ρ % 3), 0)
    have hc : ρ % 3 = 0 ∨ ρ % 3 = 1 ∨ ρ % 3 = 2 := by omega
    rcases hc with h3 | h3 | h3
    · have e1 : (ρ + 1) / 3 = ρ / 3 := by omega
      have e2 : (ρ + 1) % 3 = 1 := by omega
      rw [e1, e2, h3]
      exact XMach.act_seek_stop (seek_aux_none Y _ 1 (by decide))
        (hY.stop (ρ / 3 + 4) (by omega) (by omega))
    · have e1 : (ρ + 1) / 3 = ρ / 3 := by omega
      have e2 : (ρ + 1) % 3 = 2 := by omega
      rw [e1, e2, h3]
      exact XMach.act_look (hY.look (ρ / 3 + 4) (by omega) (by omega))
    · have e1 : (ρ + 1) / 3 = ρ / 3 + 1 := by omega
      have e2 : (ρ + 1) % 3 = 0 := by omega
      rw [e1, e2, h3]
      exact XMach.act_idle_pos (e := ([ρ / 3 + 4], Arith.succ))
        (hY.mem.succ (ρ / 3 + 4) (by omega) (by omega))

theorem LS_ne_rest (tq : List (Id × Arith)) (x c : Nat) : LS tq x c ≠ ⟨[], .idle⟩ := by
  cases c with
  | zero =>
    intro h
    have e : (sndL x ++ (([1], Arith.add) :: ([2], Arith.zero) :: ([3], Arith.zero) :: tq)).length
        = 0 := congrArg (fun T : XThread Arith => T.todo.length) h
    rw [List.length_append] at e
    have e' : (sndL x).length + (tq.length + 1 + 1 + 1) = 0 := e
    omega
  | succ c =>
    cases c with
    | zero =>
      intro h
      injection h with _ h2
      cases h2
    | succ c =>
      intro h
      injection h with _ h2
      cases h2

theorem LP_ne_rest (tq : List (Id × Arith)) : ∀ ρ, LP tq (ρ + 1) ≠ ⟨[], .idle⟩
  | 0 => fun h => by
    injection h with _ h2
    cases h2
  | 1 => fun h => by
    injection h with _ h2
    cases h2
  | 2 => fun h => by cases h
  | 3 => fun h => by cases h
  | ρ + 4 => LS_ne_rest tq (ρ / 3) (ρ % 3)

/-- The rest of the path, in a memory the rounds leave. -/
theorem late_stays {m n : Nat} {Y : XNet Arith} (hY : LateMem n Y) (hn : 2 ≤ n)
    (h2 : assoc [2] Y.agents = none) (F : Final n (sum (m + 1) n) Y (n + 3 + m + 1) m)
    {tq : List (Id × Arith)} (ht : Tops n tq) :
    ∀ ρ, ρ ≤ 3 * n + 2 → Stays xsys Y (LP tq ρ) ⟨[], .idle⟩ (ρ + tq.length)
  | 0, _ => by
    rw [Nat.zero_add]
    exact F.tops_stays tq ht
  | ρ + 1, hb => by
    have s := LP_step hY hn tq ρ hb (fun _ => h2)
    have ih := late_stays hY hn h2 F ht ρ (by omega)
    rw [show ρ + 1 + tq.length = ρ + tq.length + 1 by omega]
    exact Stays.step (LP_ne_rest tq ρ) s ih

/-- **A thread at least five actions from its top successors, on the path
down the second argument, beside a race**: it reads on, and finds the zero
of the first argument gone when it comes to it. -/
theorem beside_late (m : Nat) {n : Nat} (hn : 2 ≤ n) {tq : List (Id × Arith)}
    (ht : Tops n tq) (hq : 1 ≤ tq.length) (ρ : Nat) (h5 : 5 ≤ ρ) (hb : ρ ≤ 3 * n + 2) :
    Beside1 m n (LP tq ρ) (ρ - 5 + tq.length) := fun Y0 Y1 Y2 Y3 Y4 V F => by
  obtain ⟨ρ', rfl⟩ : ∃ ρ', ρ = ρ' + 5 := ⟨ρ - 5, by omega⟩
  have st := late_stays (V.late4 F) hn V.two4 F ht ρ' (by omega)
  refine ⟨LP tq ρ', ⟨LP tq (ρ' + 4), LP tq (ρ' + 3), LP tq (ρ' + 2), LP tq (ρ' + 1),
    LP_step (V.late0 F) hn tq (ρ' + 4) (by omega) (fun h => absurd h (by omega)),
    LP_step (V.late1 F) hn tq (ρ' + 3) (by omega) (fun _ => V.two1),
    LP_step (V.late2 F) hn tq (ρ' + 2) (by omega) (fun _ => V.two2),
    LP_step (V.late3 F) hn tq (ρ' + 1) (by omega) (fun _ => V.two3),
    LP_step (V.late4 F) hn tq ρ' (by omega) (fun _ => V.two4)⟩, ?_, st.ne_rest (by omega)⟩
  rw [show ρ' + 5 - 5 + tq.length = ρ' + tq.length by omega]
  exact st

/-- Beside one thread alone, a thread goes down the path. -/
theorem RdAt.lp {m n : Nat} (hn : 2 ≤ n) {T0 : XThread Arith} {tq : List (Id × Arith)} :
    ∀ (c a ρ : Nat), 5 ≤ a → 4 ≤ ρ → ρ + c ≤ 3 * n + 2 →
      RdAt m n T0 a (LP tq (ρ + c)) → RdAt m n T0 (a + c) (LP tq ρ)
  | 0, _, _, _, _, _, h => h
  | c + 1, a, ρ, ha, hρ, hb, h => by
    have h' : RdAt m n T0 a (LP tq (ρ + c + 1)) := h
    have s := h'.step (LP_step (solo_lateMem m n (a + 1) (by omega)) hn tq (ρ + c) (by omega)
      (fun e => absurd e (by omega)))
    exact (RdAt.lp hn c (a + 1) ρ (by omega) hρ (by omega) s).cast (by omega)

/-- **The thread numbered `t + 1` on the path down the second argument**:
`c` actions after it has passed the top of the second argument it has
`3 * n' + 5 - c` actions left before it comes to its top successors, if
nothing changes on its way. -/
theorem turn_reader_lp (m n' t K c : Nat) (ht : t + 2 ≤ m)
    (hK1 : 16 * K + 5 ≤ 3 * (m - t)) (hK2 : 3 * (m - t) < 16 * K + 21) (hn : 1 ≤ n')
    (hc : c ≤ 3 * n' + 1) :
    RdAt m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
          (chainL (n' + 1) (m - t + (t + 1))).take (t + 1)))), .idle⟩
      (3 * (m - t) + 4 + K + c)
      (LP ((chainL (n' + 1) (m - t + (t + 1))).take (t + 1)) (3 * n' + 5 - c)) := by
  have h0 := RdAt.start m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) ::
    (sndL n' ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
      (chainL (n' + 1) (m - t + (t + 1))).take (t + 1)))), .idle⟩
  have h1 := RdAt.chain_turn (t := t) (m - t) (by omega) (h0.cast (by omega))
  have hx : assoc [n' + 1 + 3] (sum (m + 1) (n' + 1)).agents = some Arith.succ :=
    sum_assoc_base m (n' + 1) (e := ([n' + 1 + 3], Arith.succ))
      (List.mem_append_left _ (sndL_mem (n' + 1) n' (by omega)))
  have h2 := RdAt.walk (by omega) hK1 hK2 (by omega) hx h1
  rw [← LP_idle, show 3 * n' + 5 = 3 * n' + 5 - c + c by omega] at h2
  exact RdAt.lp (by omega) c _ _ (by omega) (by omega) (by omega) h2

theorem tops_tops (n r0 s : Nat) : Tops n ((chainL n (r0 + (s + 1))).take (s + 1)) :=
  fun e he => by
    obtain ⟨r, -, -, rfl⟩ := mem_tops s e he
    exact ⟨n + 3 + r + 1, by omega, rfl⟩

theorem EntryAll.append {m n E : Nat} {Ts1 Ss1 Ts2 Ss2 : List (XThread Arith)}
    (h1 : EntryAll m n E Ts1 Ss1) (h2 : EntryAll m n E Ts2 Ss2) :
    EntryAll m n E (Ts1 ++ Ts2) (Ss1 ++ Ss2) := by
  induction h1 with
  | nil => exact h2
  | cons r ne _ ih => exact .cons r ne ih

/-- The entry of the threads `f 0`, …, `f (j - 1)`. -/
theorem entry_range {m n E : Nat} (f g : Nat → XThread Arith) :
    ∀ j, (∀ t, t < j → RdAt m n (f t) E (g t) ∧ g t ≠ ⟨[], .idle⟩) →
      EntryAll m n E ((List.range j).map f) ((List.range j).map g)
  | 0, _ => .nil
  | j + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append]
    exact (entry_range f g j (fun t ht => h t (Nat.lt_succ_of_lt ht))).append
      (.cons (h j (Nat.lt_succ_self j)).1 (h j (Nat.lt_succ_self j)).2 .nil)

theorem StaysAll.append {Y : XNet Arith} {Ts1 Ts2 : List (XThread Arith)} {W1 W2 : Nat}
    (h1 : StaysAll Y Ts1 W1) (h2 : StaysAll Y Ts2 W2) : StaysAll Y (Ts1 ++ Ts2) (W1 + W2) := by
  induction h1 with
  | nil => exact h2.cast (by omega)
  | cons s _ ih => exact (StaysAll.cons s ih).cast (by omega)

theorem Rows5.append {Y0 Y1 Y2 Y3 Y4 : XNet Arith} {A A' B B' : List (XThread Arith)}
    (h1 : Rows5 Y0 Y1 Y2 Y3 Y4 A A') (h2 : Rows5 Y0 Y1 Y2 Y3 Y4 B B') :
    Rows5 Y0 Y1 Y2 Y3 Y4 (A ++ B) (A' ++ B') := by
  induction h1 with
  | nil => exact h2
  | cons r _ ih => exact .cons r ih

theorem Beside.cast {m n : Nat} {Qs : List (XThread Arith)} {W W' : Nat} (h : Beside m n Qs W)
    (e : W = W') : Beside m n Qs W' := by
  subst e
  exact h

theorem Beside.append {m n : Nat} {Qs1 Qs2 : List (XThread Arith)} {W1 W2 : Nat}
    (h1 : Beside m n Qs1 W1) (h2 : Beside m n Qs2 W2) : Beside m n (Qs1 ++ Qs2) (W1 + W2) :=
  fun Y0 Y1 Y2 Y3 Y4 V F => by
    obtain ⟨A, r1, s1, n1⟩ := h1 Y0 Y1 Y2 Y3 Y4 V F
    obtain ⟨B, r2, s2, n2⟩ := h2 Y0 Y1 Y2 Y3 Y4 V F
    exact ⟨A ++ B, r1.append r2, s1.append s2, fun T hT => by
      rcases List.mem_append.1 hT with h | h
      · exact n1 T h
      · exact n2 T h⟩

/-- The threads `g 0`, …, `g (j - 1)` beside a race. -/
theorem beside_range {m n : Nat} (g : Nat → XThread Arith) (w : Nat → Nat) :
    ∀ j, (∀ t, t < j → Beside1 m n (g t) (w t)) → Beside m n ((List.range j).map g) (sumTo w j)
  | 0, _ => Beside.nil m n
  | j + 1, h => by
    rw [List.range_succ, List.map_append]
    exact ((beside_range g w j (fun t ht => h t (Nat.lt_succ_of_lt ht))).append
      (Beside.cons (h j (Nat.lt_succ_self j)) (Beside.nil m n))).cast (by
        show sumTo w j + (w j + 0) = sumTo w j + w j
        omega)

theorem sumTo_shift_const {f g : Nat → Nat} {c : Nat} :
    ∀ j, (∀ t, t < j → g t + c = f t) → sumTo g j + j * c = sumTo f j
  | 0, _ => by
    show 0 + 0 * c = 0
    rw [Nat.zero_mul]
  | j + 1, h => by
    show sumTo g j + g j + (j + 1) * c = sumTo f j + f j
    rw [Nat.succ_mul, ← sumTo_shift_const j (fun t ht => h t (Nat.lt_succ_of_lt ht)),
      ← h j (Nat.lt_succ_self j)]
    omega

/-- The count of a run of `j + 3` threads through a race: the entry, the
five turns of the race, and what is left to each thread. -/
theorem race_sum_arith (j E cd WQl WQa S1 Aj R : Nat) (hsum : WQl + j * (E + 5) = S1)
    (hadj : E + 5 + WQa = Aj) (hR : R = 2 * E + 10 + cd) :
    (j + 3) * E + ((j + 3) * 5 + cd + (WQl + (WQa + 0))) = R + 0 + S1 + Aj := by
  subst hR
  rw [← hsum, ← hadj, Nat.add_mul, Nat.add_mul, Nat.mul_add]
  omega

theorem race_sum_arith8 (j E c8 WQl WQa tl S1 Aj R : Nat) (hsum : WQl + j * (E + 5) = S1)
    (hadj : E + 5 + WQa = Aj) (hR : R = 2 * E + 10 + c8 + 1) (htl : tl = j + 2) :
    (j + 3) * E + ((j + 3) * 5 + (c8 + (WQl + (WQa + 0) + tl))) = R + (j + 1) + S1 + Aj := by
  subst hR
  subst htl
  rw [← hsum, ← hadj, Nat.add_mul, Nat.add_mul, Nat.mul_add]
  omega

/-- A fact set aside, out of the way of the search for linear
arithmetic. -/
def Aside (P : Prop) : Prop := P

theorem Aside.intro {P : Prop} (h : P) : Aside P := h

theorem Aside.elim {P : Prop} (h : Aside P) : P := h

theorem race_R_arith (M N E d c' C : Nat) (hE : E = 17 * M + 11 + d)
    (hC : C = 32 + 2 * d + c') :
    44 * M + 6 * N + C = 2 * E + 10 + (10 * M + 6 * N + c') := by
  subst hE
  subst hC
  omega

theorem race_R_arith8 (M N E : Nat) (hE : E = 17 * M + 11 + 8) :
    39 * M + 3 * N + 60 = 2 * E + 10 + (5 * M + 3 * N + 11) + 1 := by
  subst hE
  omega

/-- **Any number of threads in turn with the last in the race, to the
action.**  On the net for `(m + 1) + n` take `j + 3` threads in turn, with
`j + 3 ≤ m`, and let the last of them come to the zero of the first
argument after `17 * m + 7 + d` actions, `d` up to nine.  It races the first
thread for the last pair as the second of two threads would.  The thread
before it, three or four actions behind, reads on to the last adder and
finds it gone; each of the `j` threads before that one is still on its way
down the second argument, reads on, and finds that zero gone.  The work of
the whole run is exactly `raceWork m n d` for the two that race, `j + 1`
more when the first keeps the pair, `turnAt m n j + j + 8` for the thread
next to the last, and `turnAt m n t + t + 5` for the thread numbered
`t + 1` before it. -/
theorem threads_race_last (m n j : Nat) (hm : j + 3 ≤ m)
    (h1 : 17 * m + 7 ≤ turnAt m n (j + 1)) (h2 : turnAt m n (j + 1) ≤ 17 * m + 16) :
    (XMach.init (sum (m + 1) n) (j + 3)).Total xsys (fun i => i % (j + 3))
      (raceWork m n (turnAt m n (j + 1) - (17 * m + 7)) +
        (if turnAt m n (j + 1) = 17 * m + 15 then j + 1 else 0) +
        sumTo (fun t => turnAt m n t + t + 5) j + (turnAt m n j + (j + 1) + 7)) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 + 1 := ⟨n - 2, by
    unfold turnAt at h1
    omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have eA : ∀ t, t ≤ j + 1 → turnAt (m' + 1) (p + 1 + 1) t =
      (3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) := fun t ht => by
    unfold turnAt
    omega
  rw [eA (j + 1) (Nat.le_refl _), eA j (by omega)]
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
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) = 17 * (m' + 1) + 11 + d ∧
      ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) = 17 *
          (m' + 1) + 15 ↔ d = 8)) :=
    Aside.intro ⟨by omega, by omega, by omega⟩
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
  obtain ⟨Qadj, WQa, hRd, hNe, hB1, hadj⟩ := pkg
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
  have hQ : Beside (m' + 1) (p + 1 + 1) (((List.range j).map
      (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
      ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
      (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))))) ++
      [Qadj]) (sumTo (fun t => ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - t) + 11) / 16 - 1)) - (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) - 5 + (t + 1))) j + (WQa + 0)) :=
    (beside_range (fun t => (LP ((chainL (p + 1 + 1) (m' + 1 - t + (t + 1))).take (t + 1))
        ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
        (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)))))
        (fun t => ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
        (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) - 5 +
        (t + 1))) j hbl).append
      (Beside.cons hB1 (Beside.nil _ _))
  have hsum : sumTo (fun t => ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - t) + 11) / 16 - 1)) - (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
      ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) - 5 + (t + 1))) j + j *
      (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
      (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) + 5) =
      sumTo (fun t => turnAt (m' + 1) (p + 1 + 1) t + t + 5) j :=
    sumTo_shift_const j (fun t ht => by
      show ((3 * (m' + 1 - t) + 3 * (p + 1) + 5 + ((3 * (m' + 1 - t) + 11) / 16 - 1)) -
          (3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 + ((3 *
          (m' + 1 - (j + 1)) + 11) / 16 - 1)) - 5 + (t + 1)) +
          (((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) + 5) = turnAt (m' + 1)
          (p + 1 + 1) t + t + 5
      rw [eA t (by omega)]
      omega)
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
  obtain ⟨hd', hE, hi⟩ := early.elim
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d0 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) lk12 lk13 sk13 sk14 hS11 hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 0 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 52 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 0 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d1 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) lk13 lk14 sk14 hS12 hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 1 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 53 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 1 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d2 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) lk14 hS13 hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 2 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 54 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 2 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d3 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 3 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 56 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 3 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d4 B todo (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 4 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 61 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 4 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d5 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 5 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 62 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 5 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d6 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 6 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 63 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 6 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d7 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 7 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 64 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 7 _ _ hE rfl))
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d8 B (tops := ((chainL (p + 1 + 1) (m' + 1 - (j + 1) + ((j + 1) + 1))).take
        ((j + 1) + 1))) ht2 (by
      rw [etl]
      exact Nat.le_add_left _ _) hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 8 = 39 * (m' + 1) + 3 * (p + 1 + 1) + 60 := rfl
    rw [etl] at tot
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_pos' (hi.2 rfl)]
      exact race_sum_arith8 j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ _ hsum hadj
          (race_R_arith8 _ _ _ hE) rfl)
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
    obtain ⟨tr, wk⟩ := entry_all EA hb0
    rw [es] at tr
    rw [hTl] at tr wk
    rw [← eSs] at tr
    have tot := race_k_d9 B (([3], .zero) :: ((chainL (p + 1 + 1)
        (m' + 1 - (j + 1) + ((j + 1) + 1))).take ((j + 1) + 1))) hQ
    rw [hQl] at tot
    have eR : raceWork (m' + 1) (p + 1 + 1) 9 = 44 * (m' + 1) + 6 * (p + 1 + 1) + 68 := rfl
    exact (total_after (j + 3) tr wk tot).cast (by
      rw [eR, ite_neg' (fun h => absurd (hi.1 h) (by decide))]
      exact race_sum_arith j ((3 * (m' + 1 - (j + 1)) + 3 * (p + 1) + 5 +
          ((3 * (m' + 1 - (j + 1)) + 11) / 16 - 1)) + 4) _ _ _ _ _ _ hsum hadj
          (race_R_arith _ _ _ 9 _ _ hE rfl))

/-- The thread that races among the `k` threads after the first: of those
that come to the zero of the first argument at one of the ten moments, the
one with the largest number, which is the first to come there. -/
def racerOf (m n : Nat) : Nat → Option Nat
  | 0 => none
  | t + 1 =>
    if 17 * m + 7 ≤ turnAt m n t ∧ turnAt m n t ≤ 17 * m + 16 then some t else racerOf m n t

theorem racerOf_none {m n : Nat} : ∀ k, racerOf m n k = none → ∀ t, t < k →
    ¬ (17 * m + 7 ≤ turnAt m n t ∧ turnAt m n t ≤ 17 * m + 16)
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | k + 1, h, t, ht => by
    have h' : (if 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16 then some k
      else racerOf m n k) = none := h
    by_cases c : 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16
    · rw [ite_pos' c] at h'
      cases h'
    · rw [ite_neg' c] at h'
      by_cases e : t = k
      · rw [e]
        exact c
      · exact racerOf_none k h' t (by omega)

theorem racerOf_some {m n : Nat} : ∀ k r, racerOf m n k = some r →
    r < k ∧ (17 * m + 7 ≤ turnAt m n r ∧ turnAt m n r ≤ 17 * m + 16) ∧
      ∀ t, r < t → t < k → ¬ (17 * m + 7 ≤ turnAt m n t ∧ turnAt m n t ≤ 17 * m + 16)
  | 0, _, h => by cases h
  | k + 1, r, h => by
    have h' : (if 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16 then some k
      else racerOf m n k) = some r := h
    by_cases c : 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16
    · rw [ite_pos' c] at h'
      have e : k = r := Option.some.inj h'
      subst e
      exact ⟨Nat.lt_succ_self _, c, fun t h1 h2 => absurd h2 (by omega)⟩
    · rw [ite_neg' c] at h'
      obtain ⟨a, b, d⟩ := racerOf_some k r h'
      exact ⟨Nat.lt_succ_of_lt a, b, fun t h1 h2 => by
        by_cases e : t = k
        · rw [e]
          exact c
        · exact d t h1 (by omega)⟩

/-- **What `k + 1` threads in turn do in all on the net for `(m + 1) + n`.**
If none of the `k` threads after the first comes to the zero of the first
argument at one of the ten moments of the race, the work of one thread and
the actions of `k` readers.  Otherwise the first of them to come there
then, `racerOf m n k`, races the first thread: `raceWork` for the two; for
the thread numbered one below it, which comes next, the actions to that
zero and four more for it, three for the zero of the second argument and
one for each top successor; for the threads numbered below that one, one
action for that zero instead of four; and for the threads numbered above
the one that races, which passed that zero before the race, three. -/
def allWork (m n k : Nat) : Nat :=
  match racerOf m n k with
  | none => soloWork (m + 1) n + turnSum m n k
  | some 0 => raceWork m n (turnAt m n 0 - (17 * m + 7)) + turnSumFrom m n 1 (k - 1)
  | some (j + 1) =>
    raceWork m n (turnAt m n (j + 1) - (17 * m + 7)) +
      (if turnAt m n (j + 1) = 17 * m + 15 then j + 1 else 0) +
      sumTo (fun t => turnAt m n t + t + 5) j + (turnAt m n j + (j + 1) + 7) +
      turnSumFrom m n (j + 2) (k - (j + 2))

/-- Threads that pass the zero of the first argument before the race, if
there are any. -/
theorem threads_early_opt (m n' j W : Nat)
    (tot : (XMach.init (sum (m + 1) (n' + 1)) (j + 1)).Total xsys (fun i => i % (j + 1)) W) :
    ∀ k, (1 ≤ k → turnAt m (n' + 1) j ≤ 17 * m + 6) → j + k + 1 ≤ m →
      20 * (j + k) ≤ 3 * m + 3 * (n' + 1) + 23 →
      (XMach.init (sum (m + 1) (n' + 1)) (j + k + 1)).Total xsys (fun i => i % (j + k + 1))
        (W + turnSumFrom m (n' + 1) j k)
  | 0, _, _, _ => tot
  | k + 1, hA, hm, hk => threads_early_many m n' j W (hA (Nat.succ_pos k)) tot (k + 1) hm hk

/-- **Any number of threads in turn, every size, to the action.**  On the
net for `(m + 1) + n`, with `m` from four on, `k + 1` threads acting in
turn, `k + 1 ≤ m` and `20 * k ≤ 3 * m + 3 * n + 21`, make exactly
`allWork m n k` actions that are not rests. -/
theorem threads_exact (m n k : Nat) (hm4 : 4 ≤ m) (hm : k + 1 ≤ m)
    (hn : 20 * k ≤ 3 * m + 3 * n + 21) :
    (XMach.init (sum (m + 1) n) (k + 1)).Total xsys (fun i => i % (k + 1)) (allWork m n k) := by
  unfold allWork
  cases hr : racerOf m n k with
  | none =>
    show (XMach.init (sum (m + 1) n) (k + 1)).Total xsys (fun i => i % (k + 1))
      (soloWork (m + 1) n + turnSum m n k)
    exact threads_total m n k (by omega) (by omega) (fun t ht => by
      have h := racerOf_none k hr t ht
      omega)
  | some r =>
    obtain ⟨hrk, hw, hlater⟩ := racerOf_some k r hr
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
      have h := hw.1
      unfold turnAt at h
      omega⟩
    cases r with
    | zero =>
      show (XMach.init (sum (m + 1) (n' + 1)) (k + 1)).Total xsys (fun i => i % (k + 1))
        (raceWork m (n' + 1) (turnAt m (n' + 1) 0 - (17 * m + 7)) +
          turnSumFrom m (n' + 1) 1 (k - 1))
      have base : (XMach.init (sum (m + 1) (n' + 1)) (1 + 1)).Total xsys (fun i => i % (1 + 1))
          (raceWork m (n' + 1) (turnAt m (n' + 1) 0 - (17 * m + 7))) :=
        two_threads_race_at m (n' + 1) hm4 hw.1 hw.2
      have res := threads_early_opt m n' 1 _ base (k - 1) (fun h1 => by
        have hn1 := hlater 1 (by omega) (by omega)
        have h0 := hw.2
        unfold turnAt at hn1 h0 ⊢
        omega) (by omega) (by omega)
      rw [show 1 + (k - 1) + 1 = k + 1 by omega] at res
      exact res
    | succ j =>
      show (XMach.init (sum (m + 1) (n' + 1)) (k + 1)).Total xsys (fun i => i % (k + 1))
        (raceWork m (n' + 1) (turnAt m (n' + 1) (j + 1) - (17 * m + 7)) +
          (if turnAt m (n' + 1) (j + 1) = 17 * m + 15 then j + 1 else 0) +
          sumTo (fun t => turnAt m (n' + 1) t + t + 5) j +
          (turnAt m (n' + 1) j + (j + 1) + 7) +
          turnSumFrom m (n' + 1) (j + 2) (k - (j + 2)))
      have base : (XMach.init (sum (m + 1) (n' + 1)) (j + 2 + 1)).Total xsys
          (fun i => i % (j + 2 + 1))
          (raceWork m (n' + 1) (turnAt m (n' + 1) (j + 1) - (17 * m + 7)) +
            (if turnAt m (n' + 1) (j + 1) = 17 * m + 15 then j + 1 else 0) +
            sumTo (fun t => turnAt m (n' + 1) t + t + 5) j +
            (turnAt m (n' + 1) j + (j + 1) + 7)) :=
        threads_race_last m (n' + 1) j (by omega) hw.1 hw.2
      have res := threads_early_opt m n' (j + 2) _ base (k - (j + 2)) (fun h1 => by
        have hn1 := hlater (j + 2) (by omega) (by omega)
        have h0 := hw.2
        unfold turnAt at hn1 h0 ⊢
        omega) (by omega) (by omega)
      rw [show j + 2 + (k - (j + 2)) + 1 = k + 1 by omega] at res
      exact res

theorem _root_.INet.Checks.Arith.ManyThreads.c1
    : (XMach.init (sum 8 38) 5).Total xsys (fun i => i % 5) 1014 :=
  (threads_exact 7 38 4 (by decide) (by decide) (by decide)).cast (by decide)

theorem _root_.INet.Checks.Arith.ManyThreads.c2
    : (XMach.init (sum 8 40) 5).Total xsys (fun i => i % 5) 898 :=
  (threads_exact 7 40 4 (by decide) (by decide) (by decide)).cast (by decide)

theorem _root_.INet.Checks.Arith.ManyThreads.c3
    : (XMach.init (sum 14 66) 6).Total xsys (fun i => i % 6) 1992 :=
  (threads_exact 13 66 5 (by decide) (by decide) (by decide)).cast (by decide)

theorem _root_.INet.Checks.Arith.ManyThreads.c4
    : (XMach.init (sum 8 38) 7).Total xsys (fun i => i % 7) 1284 :=
  (threads_exact 7 38 6 (by decide) (by decide) (by decide)).cast (by decide)

theorem _root_.INet.Checks.Arith.ManyThreads.c5
    : (XMach.init (sum 13 60) 8).Total xsys (fun i => i % 8) 2258 :=
  (threads_exact 12 60 7 (by decide) (by decide) (by decide)).cast (by decide)

/-- Each thread comes to the zero of the first argument three or four
actions before the thread numbered one below it. -/
theorem turnAt_step (m n t : Nat) (ht : t + 1 ≤ m) :
    turnAt m n t = turnAt m n (t + 1) + 3 ∨ turnAt m n t = turnAt m n (t + 1) + 4 := by
  unfold turnAt
  omega

/-- And at least three actions for each thread between them. -/
theorem turnAt_gap (m n : Nat) {t s : Nat} (h : t ≤ s) (hs : s ≤ m) :
    turnAt m n s + 3 * (s - t) ≤ turnAt m n t := by
  unfold turnAt
  omega

theorem turnAt_ge (m n t : Nat) (ht : t + 1 ≤ m) : 3 * n + 4 ≤ turnAt m n t := by
  unfold turnAt
  omega

theorem win_pos {m n t : Nat} (h : 17 * m + 7 ≤ turnAt m n t) : 1 ≤ n := by
  unfold turnAt at h
  omega

theorem racerOf_out {m n k : Nat}
    (h : ¬ (17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16)) :
    racerOf m n (k + 1) = racerOf m n k := by
  show (if 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16 then some k
    else racerOf m n k) = racerOf m n k
  rw [ite_neg' h]

theorem racerOf_in {m n k : Nat}
    (h : 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16) :
    racerOf m n (k + 1) = some k := by
  show (if 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16 then some k
    else racerOf m n k) = some k
  rw [ite_pos' h]

theorem racerOf_none_of {m n : Nat} : ∀ k,
    (∀ t, t < k → ¬ (17 * m + 7 ≤ turnAt m n t ∧ turnAt m n t ≤ 17 * m + 16)) →
    racerOf m n k = none
  | 0, _ => rfl
  | k + 1, h => by
    rw [racerOf_out (h k (Nat.lt_succ_self k))]
    exact racerOf_none_of k (fun t ht => h t (Nat.lt_succ_of_lt ht))

theorem allWork_none {m n k : Nat} (h : racerOf m n k = none) :
    allWork m n k = soloWork (m + 1) n + turnSum m n k := by
  unfold allWork
  simp only [h]

theorem allWork_first {m n k : Nat} (h : racerOf m n k = some 0) :
    allWork m n k =
      raceWork m n (turnAt m n 0 - (17 * m + 7)) + turnSumFrom m n 1 (k - 1) := by
  unfold allWork
  simp only [h]

theorem allWork_later {m n k j : Nat} (h : racerOf m n k = some (j + 1)) :
    allWork m n k = raceWork m n (turnAt m n (j + 1) - (17 * m + 7)) +
      (if turnAt m n (j + 1) = 17 * m + 15 then j + 1 else 0) +
      sumTo (fun t => turnAt m n t + t + 5) j + (turnAt m n j + (j + 1) + 7) +
      turnSumFrom m n (j + 2) (k - (j + 2)) := by
  unfold allWork
  simp only [h]

theorem allWork_zero (m n : Nat) : allWork m n 0 = soloWork (m + 1) n := rfl

/-- The work when the second thread races and there are no others. -/
theorem allWork_second (m n : Nat)
    (h : 17 * m + 7 ≤ turnAt m n 0 ∧ turnAt m n 0 ≤ 17 * m + 16) :
    allWork m n (0 + 1) = raceWork m n (turnAt m n 0 - (17 * m + 7)) := by
  rw [allWork_first (racerOf_in h)]
  rfl

/-- The work when the last thread races. -/
theorem allWork_last (m n j : Nat)
    (h : 17 * m + 7 ≤ turnAt m n (j + 1) ∧ turnAt m n (j + 1) ≤ 17 * m + 16) :
    allWork m n (j + 1 + 1) = raceWork m n (turnAt m n (j + 1) - (17 * m + 7)) +
      (if turnAt m n (j + 1) = 17 * m + 15 then j + 1 else 0) +
      sumTo (fun t => turnAt m n t + t + 5) j + (turnAt m n j + (j + 1) + 7) := by
  rw [allWork_later (racerOf_in h), show j + 1 + 1 - (j + 2) = 0 by omega]
  rfl

theorem turnSumFrom_succ (m n j q : Nat) :
    turnSumFrom m n j (q + 1) = turnSumFrom m n j q + turnRest m n (j + q) := rfl

/-- **A thread that is not in the race adds exactly its own actions.**  If
the thread numbered `k + 1` does not come to the zero of the first argument
at one of the ten moments, the work with it is the work without it and
`turnRest m n k`. -/
theorem allWork_succ_out (m n k : Nat)
    (h : ¬ (17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16)) :
    allWork m n (k + 1) = allWork m n k + turnRest m n k := by
  cases hr : racerOf m n k with
  | none =>
    rw [allWork_none hr, allWork_none ((racerOf_out h).trans hr)]
    show soloWork (m + 1) n + (turnSum m n k + turnRest m n k) = _
    omega
  | some r =>
    obtain ⟨hrk, -, -⟩ := racerOf_some k r hr
    cases r with
    | zero =>
      rw [allWork_first hr, allWork_first ((racerOf_out h).trans hr)]
      have e1 : k + 1 - 1 = (k - 1) + 1 := by omega
      have e2 : 1 + (k - 1) = k := by omega
      rw [e1, turnSumFrom_succ, e2]
      omega
    | succ j =>
      rw [allWork_later hr, allWork_later ((racerOf_out h).trans hr)]
      have e1 : k + 1 - (j + 2) = (k - (j + 2)) + 1 := by omega
      have e2 : j + 2 + (k - (j + 2)) = k := by omega
      rw [e1, turnSumFrom_succ, e2]
      omega

theorem turnRest_pos (m n t : Nat) (hn : 1 ≤ n) :
    turnRest m n t = turnAt m n t + zeroCost m (turnAt m n t) + 3 + (t + 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rfl

theorem zeroCost_le (m A : Nat) : zeroCost m A ≤ 4 := by
  unfold zeroCost
  by_cases h1 : A ≤ 17 * m + 6
  · rw [ite_pos' h1]
    omega
  · rw [ite_neg' h1]
    by_cases h2 : A ≤ 17 * m + 20
    · rw [ite_pos' h2]
      omega
    · rw [ite_neg' h2]
      omega

/-- A thread that only reads makes at least the actions that bring it to
the zero of the first argument, and two fewer than one thread alone makes
at most. -/
theorem turnRest_bounds (m n t : Nat) (ht : t ≤ m) :
    turnAt m n t ≤ turnRest m n t ∧ turnRest m n t + 2 ≤ soloWork (m + 1) n := by
  rw [soloWork_succ]
  cases n with
  | zero =>
    show turnAt m 0 t ≤ 3 * (m - t) + 8 + (3 * (m - t) + 15) / 16 + t ∧
      3 * (m - t) + 8 + (3 * (m - t) + 15) / 16 + t + 2 ≤ 22 * (m + 1) + 3 * 0 + 13
    unfold turnAt
    omega
  | succ n' =>
    rw [turnRest_pos m (n' + 1) t (by omega)]
    have z := zeroCost_le m (turnAt m (n' + 1) t)
    have a : turnAt m (n' + 1) t + t ≤ 3 * m + 3 * (n' + 1) + 1 + (3 * m + 11) / 16 := by
      unfold turnAt
      omega
    omega

theorem turnSum_late (m n : Nat) (hn : 1 ≤ n) : ∀ q,
    (∀ t, t < q → 17 * m + 21 ≤ turnAt m n t) →
    turnSum m n q = sumTo (fun t => turnAt m n t + t + 5) q
  | 0, _ => rfl
  | q + 1, h => by
    show turnSum m n q + turnRest m n q =
      sumTo (fun t => turnAt m n t + t + 5) q + (turnAt m n q + q + 5)
    rw [turnSum_late m n hn q (fun t ht => h t (Nat.lt_succ_of_lt ht)), turnRest_pos m n q hn]
    have hq := h q (Nat.lt_succ_self q)
    have z : zeroCost m (turnAt m n q) = 1 := by
      unfold zeroCost
      rw [ite_neg' (by omega), ite_neg' (by omega)]
    rw [z]
    omega

theorem turnSum_near (m n : Nat) (hn : 1 ≤ n) : ∀ q,
    (∀ t, t < q → 17 * m + 20 ≤ turnAt m n t) →
    (∀ t, t + 1 < q → 17 * m + 21 ≤ turnAt m n t) →
    sumTo (fun t => turnAt m n t + t + 5) q ≤ turnSum m n q ∧
      turnSum m n q ≤ sumTo (fun t => turnAt m n t + t + 5) q + 3
  | 0, _, _ => ⟨Nat.le_refl _, Nat.zero_le _⟩
  | q + 1, h1, h2 => by
    have e := turnSum_late m n hn q (fun t ht => h2 t (by omega))
    have tr := turnRest_pos m n q hn
    have hq := h1 q (Nat.lt_succ_self q)
    have z : zeroCost m (turnAt m n q) = 4 ∨ zeroCost m (turnAt m n q) = 1 := by
      unfold zeroCost
      rw [ite_neg' (by omega)]
      by_cases c : turnAt m n q ≤ 17 * m + 20
      · rw [ite_pos' c]
        exact Or.inl rfl
      · rw [ite_neg' c]
        exact Or.inr rfl
    show sumTo (fun t => turnAt m n t + t + 5) q + (turnAt m n q + q + 5) ≤
        turnSum m n q + turnRest m n q ∧
      turnSum m n q + turnRest m n q ≤
        sumTo (fun t => turnAt m n t + t + 5) q + (turnAt m n q + q + 5) + 3
    rw [e, tr]
    omega

/-- The work of the race is `39 * m + 3 * n + 60` when the first thread
keeps the pair, and from `44 * m + 6 * n + 52` to `44 * m + 6 * n + 68`
otherwise. -/
theorem raceWork_cases (m n d : Nat) :
    (d = 8 ∧ raceWork m n d = 39 * m + 3 * n + 60) ∨
    (d ≠ 8 ∧ 44 * m + 6 * n + 52 ≤ raceWork m n d ∧ raceWork m n d ≤ 44 * m + 6 * n + 68) := by
  by_cases h8 : d = 8
  · subst h8
    exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨h8, ?_, raceWork_le m n d⟩
    unfold raceWork
    split <;> omega

/-- The race of a thread and the race of the thread that comes three or
four actions after it. -/
theorem raceWork_next (m n d e : Nat) (h : e = d + 3 ∨ e = d + 4) (he : e ≤ 9) :
    (e = 8 ∧ raceWork m n d = raceWork m n e + 5 * m + 3 * n + (d - 3)) ∨
    (e ≠ 8 ∧ raceWork m n d ≤ raceWork m n e ∧ raceWork m n e ≤ raceWork m n d + 9) := by
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h with rfl | rfl <;>
    simp only [raceWork] <;> first | omega | (refine Or.inl ⟨trivial, ?_⟩; omega)

/-- **What one more thread in turn adds.**  With `k ≤ m`, the work of
`k + 2` threads is at least that of `k + 1` and the `turnAt m n k` actions
that bring the new thread to the zero of the first argument, and at most
that of `k + 1` and two fewer than the work of one thread alone. -/
theorem allWork_succ (m n k : Nat) (hk : k ≤ m) :
    allWork m n k + turnAt m n k ≤ allWork m n (k + 1) ∧
      allWork m n (k + 1) + 2 ≤ allWork m n k + soloWork (m + 1) n := by
  by_cases hW : 17 * m + 7 ≤ turnAt m n k ∧ turnAt m n k ≤ 17 * m + 16
  · have hn : 1 ≤ n := win_pos hW.1
    cases k with
    | zero =>
      rw [allWork_second m n hW, allWork_zero, soloWork_succ]
      rcases raceWork_cases m n (turnAt m n 0 - (17 * m + 7)) with ⟨h8, hR⟩ | ⟨h8, hR1, hR2⟩
      · omega
      · omega
    | succ k' =>
      have st := turnAt_step m n k' (by omega)
      by_cases hW' : 17 * m + 7 ≤ turnAt m n k' ∧ turnAt m n k' ≤ 17 * m + 16
      · have nx := raceWork_next m n (turnAt m n (k' + 1) - (17 * m + 7))
          (turnAt m n k' - (17 * m + 7)) (by omega) (by omega)
        have b : (if turnAt m n (k' + 1) = 17 * m + 15 then k' + 1 else 0) = 0 :=
          ite_neg' (by omega)
        cases k' with
        | zero =>
          have e2 := allWork_last m n 0 hW
          have s0 : sumTo (fun t => turnAt m n t + t + 5) 0 = 0 := rfl
          rw [b, s0] at e2
          rw [e2, allWork_second m n hW', soloWork_succ]
          rcases nx with ⟨h8, hR⟩ | ⟨h8, hR1, hR2⟩
          · omega
          · omega
        | succ j =>
          have e2 := allWork_last m n (j + 1) hW
          have s : sumTo (fun t => turnAt m n t + t + 5) (j + 1) =
              sumTo (fun t => turnAt m n t + t + 5) j + (turnAt m n j + j + 5) := rfl
          rw [b, s] at e2
          rw [e2, allWork_last m n j hW', soloWork_succ]
          rcases nx with ⟨h8, hR⟩ | ⟨h8, hR1, hR2⟩
          · have b1 : (if turnAt m n (j + 1) = 17 * m + 15 then j + 1 else 0) = j + 1 :=
              ite_pos' (by omega)
            rw [b1]
            omega
          · have b1 : (if turnAt m n (j + 1) = 17 * m + 15 then j + 1 else 0) = 0 :=
              ite_neg' (by omega)
            rw [b1]
            omega
      · have hlate : ∀ t, t ≤ k' → 17 * m + 17 + 3 * (k' - t) ≤ turnAt m n t := fun t ht => by
          have g := turnAt_gap m n ht (by omega : k' ≤ m)
          omega
        have hnone : racerOf m n (k' + 1) = none := racerOf_none_of (k' + 1) (fun t ht => by
          have g := hlate t (by omega)
          omega)
        have near := turnSum_near m n hn k'
          (fun t ht => by
            have g := hlate t (by omega)
            omega)
          (fun t ht => by
            have g := hlate t (by omega)
            omega)
        have ts : turnSum m n (k' + 1) = turnSum m n k' + turnRest m n k' := rfl
        have zc : zeroCost m (turnAt m n k') = 4 := by
          have g := hlate k' (Nat.le_refl k')
          unfold zeroCost
          rw [ite_neg' (by omega), ite_pos' (by omega)]
        rw [allWork_last m n k' hW, allWork_none hnone, ts, turnRest_pos m n k' hn, zc,
          soloWork_succ]
        rcases raceWork_cases m n (turnAt m n (k' + 1) - (17 * m + 7)) with
          ⟨h8, hR⟩ | ⟨h8, hR1, hR2⟩
        · have b1 : (if turnAt m n (k' + 1) = 17 * m + 15 then k' + 1 else 0) = k' + 1 :=
            ite_pos' (by omega)
          rw [b1]
          omega
        · have b1 : (if turnAt m n (k' + 1) = 17 * m + 15 then k' + 1 else 0) = 0 :=
            ite_neg' (by omega)
          rw [b1]
          omega
  · rw [allWork_succ_out m n k hW]
    have tb := turnRest_bounds m n k hk
    omega

/-- With `k ≤ m`, `k + 1` threads in turn do at most `k + 1` times the work
of one thread, less two for each thread after the first. -/
theorem allWork_le (m n : Nat) : ∀ k, k ≤ m →
    allWork m n k + 2 * k ≤ (k + 1) * soloWork (m + 1) n
  | 0, _ => by
    rw [allWork_zero]
    omega
  | k + 1, h => by
    have ih := allWork_le m n k (by omega)
    have st := (allWork_succ m n k (by omega)).2
    have e : (k + 1 + 1) * soloWork (m + 1) n =
        (k + 1) * soloWork (m + 1) n + soloWork (m + 1) n := Nat.succ_mul _ _
    rw [e]
    omega

/-- And at least the work of one thread and, for each thread after the
first, the actions that bring it to the zero of the first argument. -/
theorem allWork_ge (m n : Nat) : ∀ k, k ≤ m →
    soloWork (m + 1) n + sumTo (turnAt m n) k ≤ allWork m n k
  | 0, _ => Nat.le_refl _
  | k + 1, h => by
    have ih := allWork_ge m n k (by omega)
    have st := (allWork_succ m n k (by omega)).1
    show soloWork (m + 1) n + (sumTo (turnAt m n) k + turnAt m n k) ≤ allWork m n (k + 1)
    omega

/-- **One more thread in turn never saves work.**  On the net for
`(m + 1) + n`, with `m` from four on, `k + 2 ≤ m` and
`20 * (k + 1) ≤ 3 * m + 3 * n + 21`: the run of `k + 2` threads in turn
makes more actions that are not rests than the run of `k + 1`, by at least
the `turnAt m n k` actions that bring the new thread to the zero of the
first argument, and by at most two fewer than the work of one thread
alone. -/
theorem threads_more (m n k : Nat) (hm4 : 4 ≤ m) (hm : k + 2 ≤ m)
    (hn : 20 * (k + 1) ≤ 3 * m + 3 * n + 21) :
    ∃ W W', (XMach.init (sum (m + 1) n) (k + 1)).Total xsys (fun i => i % (k + 1)) W ∧
      (XMach.init (sum (m + 1) n) (k + 1 + 1)).Total xsys (fun i => i % (k + 1 + 1)) W' ∧
      W + turnAt m n k ≤ W' ∧ W' + 2 ≤ W + soloWork (m + 1) n :=
  ⟨allWork m n k, allWork m n (k + 1), threads_exact m n k hm4 (by omega) (by omega),
    threads_exact m n (k + 1) hm4 hm hn, allWork_succ m n k (by omega)⟩

/-- **Threads in turn: more than the work of one, less than the work of
each.**  On the net for `(m + 1) + n`, with `m` from four on, `k + 1 ≤ m`
and `20 * k ≤ 3 * m + 3 * n + 21`, the work `W` of `k + 1` threads in turn
is at least that of one thread and `3 * n + 4` for each thread after the
first, and at most `k + 1` times that of one thread, less two for each
thread after the first. -/
theorem threads_bounds (m n k : Nat) (hm4 : 4 ≤ m) (hm : k + 1 ≤ m)
    (hn : 20 * k ≤ 3 * m + 3 * n + 21) :
    ∃ W, (XMach.init (sum (m + 1) n) (k + 1)).Total xsys (fun i => i % (k + 1)) W ∧
      soloWork (m + 1) n + k * (3 * n + 4) ≤ W ∧
      W + 2 * k ≤ (k + 1) * soloWork (m + 1) n := by
  refine ⟨allWork m n k, threads_exact m n k hm4 hm hn, ?_, allWork_le m n k (by omega)⟩
  have g := allWork_ge m n k (by omega)
  have s : k * (3 * n + 4) ≤ sumTo (turnAt m n) k :=
    sumTo_ge k (fun t ht => turnAt_ge m n t (by omega))
  omega

theorem _root_.INet.Checks.Arith.ManyThreads.c6 : allWork 7 38 5 = allWork 7 38 4 + 136 := by decide

theorem _root_.INet.Checks.Arith.ManyThreads.c7 : allWork 7 38 6 = allWork 7 38 5 + 134 := by decide

theorem _root_.INet.Checks.Arith.ManyThreads.c8 : soloWork 8 38 = 303 := by decide

/-- The second bound is reached: two threads on `6 + 28` make 456 actions
that are not rests, one thread 229. -/
theorem _root_.INet.Checks.Arith.ManyThreads.c9
    : (XMach.init (sum 6 28) 2).Total xsys (fun i => i % 2) (2 * soloWork 6 28 - 2) :=
  (threads_exact 5 28 1 (by decide) (by decide) (by decide)).cast (by decide)

theorem _root_.INet.Checks.Arith.ManyThreads.c10 : 2 * soloWork 6 28 - 2 = 456 := by decide

end Arith

end INet
