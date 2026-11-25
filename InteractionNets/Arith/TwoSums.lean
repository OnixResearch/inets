import InteractionNets.Arith.SideBySide

/-! ### Two threads on two additions side by side -/

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

/-- **The second thread before the top successor**, second argument not
zero: outside the race it has only read, for one action less than
`turnRest m (n' + 1) 0`, and all that is left of its list is the top
successor of the first argument. -/
theorem reader_top_succ (m n' : Nat) (hm : 2 ≤ m)
    (hw : turnAt m (n' + 1) 0 ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m (n' + 1) 0) :
    ∃ b, turnRest m (n' + 1) 0 = b + 1 ∧
      RdAt m (n' + 1) ⟨chainL (n' + 1) (m - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - 0 + (0 + 1))).take
            (0 + 1)))), .idle⟩ b
        ⟨(chainL (n' + 1) (m - 0 + (0 + 1))).take (0 + 1), .idle⟩ := by
  obtain ⟨K, hK⟩ : ∃ K, (3 * (m - 0) + 11) / 16 = K + 1 :=
    ⟨(3 * (m - 0) + 11) / 16 - 1, by omega⟩
  have eA : turnAt m (n' + 1) 0 = 3 * (m - 0) + 3 * n' + 5 + K := by
    unfold turnAt
    omega
  rw [eA] at hw
  have hrest : turnRest m (n' + 1) 0 =
      turnAt m (n' + 1) 0 + zeroCost m (turnAt m (n' + 1) 0) + 3 + (0 + 1) := rfl
  have r0 := turn_reader_at_zero m n' 0 K (by omega) (by omega) (by omega)
  have hx3 : assoc [3] (sum (m + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base m (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tail : ∀ a, 17 * 0 + 1 ≤ a →
      RdAt m (n' + 1) ⟨chainL (n' + 1) (m - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - 0 + (0 + 1))).take
            (0 + 1)))), .idle⟩ a
        ⟨([3], .zero) :: (chainL (n' + 1) (m - 0 + (0 + 1))).take (0 + 1), .idle⟩ →
      RdAt m (n' + 1) ⟨chainL (n' + 1) (m - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - 0 + (0 + 1))).take
            (0 + 1)))), .idle⟩ (a + 3)
        ⟨(chainL (n' + 1) (m - 0 + (0 + 1))).take (0 + 1), .idle⟩ := fun a _ h =>
    h.pass3 (solo_snd_forever m (n' + 1) (j := 3) (by omega) (by omega) hx3 _)
      (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).1
      (show ¬ (1 : Nat) = 0 by decide)
      (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).2
  by_cases h1 : 3 * (m - 0) + 3 * n' + 5 + K ≤ 17 * m + 6
  · have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * (m - 0) + 3 * n' + 5 + K + 1)
        (by omega) (by omega)
      (by omega) (sum_zero_agent m (n' + 1))
    have r1 := r0.pass3 hal (solo_look_two m (n' + 1) _) (show ¬ (1 : Nat) = 0 by decide)
      ((solo_seek_two m (n' + 1) (by omega) _).2 (by omega))
    have ez : zeroCost m (turnAt m (n' + 1) 0) = 3 := by
      rw [eA]
      unfold zeroCost
      exact ite_pos' h1
    exact ⟨3 * (m - 0) + 3 * n' + 5 + K + 3 + 3, by omega, tail _ (by omega) r1⟩
  · by_cases h2 : 3 * (m - 0) + 3 * n' + 5 + K ≤ 17 * m + 20
    · have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * (m - 0) + 3 * n' + 5 + K + 1)
          (by omega) (by omega)
        (by omega) (sum_zero_agent m (n' + 1))
      have s1 := r0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
      have s2 := s1.step (XMach.act_look (solo_look_two m (n' + 1) _))
      have s3 := s2.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide))
        ((solo_seek_two m (n' + 1) (by omega) _).1 (by omega)))
      have hg := solo_gone_adder m (n' + 1) (u := 3 * (m - 0) + 3 * n' + 5 + K + 1 + 1 + 1 + 1)
          (by omega)
      have s4 := s3.step (XMach.act_seek_stop ((ite_pos' rfl).trans hg)
        (solo_stop_adder m (n' + 1) (by omega) _))
      have ez : zeroCost m (turnAt m (n' + 1) 0) = 4 := by
        rw [eA]
        unfold zeroCost
        exact (ite_neg' h1).trans (ite_pos' h2)
      exact ⟨3 * (m - 0) + 3 * n' + 5 + K + 1 + 1 + 1 + 1 + 3, by omega, tail _ (by omega) s4⟩
    · have r1 := r0.gone (solo_gone_zero m (n' + 1) (by omega))
      have ez : zeroCost m (turnAt m (n' + 1) 0) = 1 := by
        rw [eA]
        unfold zeroCost
        exact (ite_neg' h1).trans (ite_neg' h2)
      exact ⟨3 * (m - 0) + 3 * n' + 5 + K + 1 + 3, by omega, tail _ (by omega) r1⟩

/-- The same when the second argument is zero. -/
theorem reader_top_zero (m : Nat) (hm : 2 ≤ m) :
    ∃ b, turnRest m 0 0 = b + 1 ∧
      RdAt m 0 ⟨chainL 0 (m - 0) ++ (([1], .add) :: ([2], .zero) :: ([0 + 3], .zero) ::
        (chainL 0 (m - 0 + (0 + 1))).take (0 + 1)), .idle⟩ b
        ⟨(chainL 0 (m - 0 + (0 + 1))).take (0 + 1), .idle⟩ := by
  obtain ⟨K, hK⟩ : ∃ K, (3 * (m - 0) + 15) / 16 = K + 1 :=
    ⟨(3 * (m - 0) + 15) / 16 - 1, by omega⟩
  have h0 := RdAt.start m 0 ⟨chainL 0 (m - 0) ++ (([1], .add) :: ([2], .zero) :: ([0 + 3], .zero) ::
        (chainL 0 (m - 0 + (0 + 1))).take (0 + 1)), .idle⟩
  have h1 := RdAt.chain_turn (t := 0) (m - 0) (by omega) (h0.cast (by omega))
  have h2 := h1.gone (solo_gone5 m 0 (by omega)).2
  have hal := solo_alive_zero m 0 (j := 2) (u := 3 * (m - 0) + 1 + 1) (by omega) (by omega)
    (by omega) (sum_zero_agent m 0)
  have h3 := h2.pass3 hal (solo_look_two m 0 _) (show ¬ (1 : Nat) = 0 by decide)
    ((solo_seek_two m 0 (by omega) _).2 (by omega))
  have hx3 : assoc [0 + 3] (sum (m + 1) 0).agents = some Arith.zero :=
    sum_assoc_base m 0 (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h4 := RdAt.walk (K := K) (by omega) (by omega) (by omega) (by omega) hx3 h3
  have hrest : turnRest m 0 0 = 3 * (m - 0) + 8 + (3 * (m - 0) + 15) / 16 + 0 := rfl
  exact ⟨3 * (m - 0) + 8 + K, by omega, h4.cast (by omega)⟩

/-- **The second thread before the top successor.**  On the net for
`(m + 1) + n` beside the first thread, outside the race, the second thread
has only read for `turnRest m n 0 - 1` actions, and then has the top
successor of the first argument alone left in its list. -/
theorem reader_top (m n : Nat) (hm : 2 ≤ m)
    (hw : turnAt m n 0 ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n 0) :
    ∃ b, turnRest m n 0 = b + 1 ∧
      RdAt m n ⟨(sum (m + 1) n).agents.drop (0 + 1) ++ (sum (m + 1) n).agents.take (0 + 1),
        .idle⟩ b ⟨[([n + 3 + m + 1], .succ)], .idle⟩ := by
  cases n with
  | zero =>
    obtain ⟨b, eb, r⟩ := reader_top_zero m hm
    rw [turn_list_zero m 0 (by omega)]
    exact ⟨b, eb, r⟩
  | succ n' =>
    obtain ⟨b, eb, r⟩ := reader_top_succ m n' hm hw
    rw [turn_list_succ m n' 0 (by omega)]
    exact ⟨b, eb, r⟩

/-- A thread that is looking and leaves the memory as it is is still
looking, and its list is no longer. -/
theorem act_scan {X : XNet Arith} {T : XThread Arith} (hS : Scans T.st)
    (hX : (XMach.act xsys X T).1 = X) :
    Scans (XMach.act xsys X T).2.1.st ∧
      (XMach.act xsys X T).2.1.todo.length ≤ T.todo.length := by
  obtain ⟨todo, st⟩ := T
  by_cases hr : (⟨todo, st⟩ : XThread Arith) = ⟨[], .idle⟩
  · injection hr with h1 h2
    subst h1
    subst h2
    exact ⟨trivial, Nat.le_refl _⟩
  · have hw : st ≠ .write [] [] := fun e => by
      rw [e] at hS
      exact hS
    obtain ⟨X', Y', l', st', k, aX, -, -, -, hlen, hsc⟩ :=
      (looks_left X X).act todo [] [] st (fun e hl => hr (by rw [e, hl])) hw
    rw [List.append_nil, List.append_nil] at aX
    rw [aX] at hX ⊢
    exact ⟨(hsc hS hX).2, hlen⟩

theorem reader_scans {X : XNet Arith} {T0 T1 : XThread Arith} {b : Nat} (h1 : Scans T1.st)
    (hrd : ∀ a, a < b →
      (XMach.act xsys (XMach.solo xsys X T0 (a + 1)).1 (XMach.reader xsys X T0 T1 a)).1 =
        (XMach.solo xsys X T0 (a + 1)).1) :
    ∀ a, a ≤ b → Scans (XMach.reader xsys X T0 T1 a).st
  | 0, _ => h1
  | a + 1, ha => (act_scan (reader_scans h1 hrd a (Nat.le_of_succ_le ha)) (hrd a ha)).1

theorem reader_todo_le {X : XNet Arith} {T0 T1 : XThread Arith} {b : Nat} (h1 : Scans T1.st)
    (hrd : ∀ a, a < b →
      (XMach.act xsys (XMach.solo xsys X T0 (a + 1)).1 (XMach.reader xsys X T0 T1 a)).1 =
        (XMach.solo xsys X T0 (a + 1)).1) :
    ∀ d a, a + d ≤ b → (XMach.reader xsys X T0 T1 (a + d)).todo.length ≤
      (XMach.reader xsys X T0 T1 a).todo.length
  | 0, _, _ => Nat.le_refl _
  | d + 1, a, h => Nat.le_trans
      (act_scan (reader_scans h1 hrd (a + d) (by omega)) (hrd (a + d) (by omega))).2
      (reader_todo_le h1 hrd d a (by omega))

/-- **A thread that reads beside the first thread, on a net that comes
first in a larger memory.**  Beside the first thread on `X`, let a thread
whose list is `l0 ++ s` only read for `b` actions and still have the
entries `s` at the end.  Then beside the first thread on `Y`, the thread
whose list is `l0`, tagged, followed by anything, reads in the same way:
after each action its state is that of the thread on `X`, tagged. -/
theorem Inside.reader {c : Nat} {Fr : List (Id × Arith)} {X Y : XNet Arith}
    (hI : Inside c Fr X Y) (T0 : XThread Arith) (l0 s rY : List (Id × Arith)) (b : Nat)
    (hpos : 0 < s.length)
    (hrd : ∀ a, a < b →
      (XMach.act xsys (XMach.solo xsys X T0 (a + 1)).1
          (XMach.reader xsys X T0 ⟨l0 ++ s, .idle⟩ a)).1 = (XMach.solo xsys X T0 (a + 1)).1 ∧
        (XMach.act xsys (XMach.solo xsys X T0 (a + 1)).1
          (XMach.reader xsys X T0 ⟨l0 ++ s, .idle⟩ a)).2.2 = 0)
    (hend : s.length ≤ (XMach.reader xsys X T0 ⟨l0 ++ s, .idle⟩ b).todo.length)
    (hs : ∀ j, j < b → (XMach.solo xsys X T0 j).2 ≠ ⟨[], .idle⟩) :
    ∀ a, a ≤ b → ∃ l st, XMach.reader xsys X T0 ⟨l0 ++ s, .idle⟩ a = ⟨l ++ s, st⟩ ∧
      XMach.reader xsys Y (tagTh c Fr T0) ⟨l0.map (tagA c) ++ rY, .idle⟩ a =
        ⟨l.map (tagA c) ++ rY, tagSt c st⟩ ∧
      ∀ a', a' < a →
        (XMach.act xsys (XMach.solo xsys Y (tagTh c Fr T0) (a' + 1)).1
            (XMach.reader xsys Y (tagTh c Fr T0) ⟨l0.map (tagA c) ++ rY, .idle⟩ a')).1 =
            (XMach.solo xsys Y (tagTh c Fr T0) (a' + 1)).1 ∧
          (XMach.act xsys (XMach.solo xsys Y (tagTh c Fr T0) (a' + 1)).1
            (XMach.reader xsys Y (tagTh c Fr T0) ⟨l0.map (tagA c) ++ rY, .idle⟩ a')).2.2 = 0
  | 0, _ => ⟨l0, .idle, rfl, rfl, fun a' h => absurd h (Nat.not_lt_zero a')⟩
  | a + 1, ha => by
    obtain ⟨l, st, eX, eY, hprev⟩ :=
      Inside.reader hI T0 l0 s rY b hpos hrd hend hs a (Nat.le_of_succ_le ha)
    have hsc := reader_scans (X := X) (T0 := T0) (T1 := ⟨l0 ++ s, .idle⟩) (b := b) trivial
      (fun a h => (hrd a h).1) a (Nat.le_of_succ_le ha)
    rw [eX] at hsc
    obtain ⟨Y1, r1, sY, hI1, -, -⟩ :=
      Inside.solo (a + 1) Fr T0 hI (fun j hj => hs j (by omega))
    have hl : st = .idle → l ≠ [] := fun e1 e2 => by
      subst e1
      subst e2
      cases s with
      | nil => exact Nat.lt_irrefl 0 hpos
      | cons e s' =>
        have hpop : (XMach.reader xsys X T0 ⟨l0 ++ e :: s', .idle⟩ (a + 1)).todo = s' := by
          show (XMach.act xsys (XMach.solo xsys X T0 (a + 1)).1
            (XMach.reader xsys X T0 ⟨l0 ++ e :: s', .idle⟩ a)).2.1.todo = s'
          rw [eX]
          by_cases hag : assoc e.1 (XMach.solo xsys X T0 (a + 1)).1.agents = some e.2
          · exact congrArg (fun v : XNet Arith × XThread Arith × Nat => v.2.1.todo)
              (XMach.act_idle_pos (xs := xsys) (rest := s') hag)
          · exact congrArg (fun v : XNet Arith × XThread Arith × Nat => v.2.1.todo)
              (XMach.act_idle_neg (xs := xsys) (rest := s') hag)
        have hmono := reader_todo_le (X := X) (T0 := T0) (T1 := ⟨l0 ++ e :: s', .idle⟩)
          (b := b) trivial (fun a h => (hrd a h).1) (b - (a + 1)) (a + 1) (by omega)
        have hd : a + 1 + (b - (a + 1)) = b := by omega
        rw [hd, hpop] at hmono
        exact absurd (Nat.le_trans hend hmono) (Nat.not_succ_le_self _)
    have hw : st ≠ .write [] [] := fun e => by
      rw [e] at hsc
      exact hsc
    obtain ⟨X', Y', l', st', k, aX, aY, -, -, -, hscn⟩ := hI1.looks.act l s rY st hl hw
    obtain ⟨r1x, r2x⟩ := hrd a ha
    rw [eX, aX] at r1x r2x
    have eY' : Y' = Y1 := (hscn hsc r1x).1
    subst eY'
    have r2x' : k = 0 := r2x
    subst r2x'
    have eS : (XMach.solo xsys Y (tagTh c Fr T0) (a + 1)).1 = Y' := congrArg Prod.fst sY
    have eXn : XMach.reader xsys X T0 ⟨l0 ++ s, .idle⟩ (a + 1) = ⟨l' ++ s, st'⟩ := by
      show (XMach.act xsys (XMach.solo xsys X T0 (a + 1)).1
        (XMach.reader xsys X T0 ⟨l0 ++ s, .idle⟩ a)).2.1 = _
      rw [eX, aX]
    have eYn : XMach.reader xsys Y (tagTh c Fr T0) ⟨l0.map (tagA c) ++ rY, .idle⟩ (a + 1) =
        ⟨l'.map (tagA c) ++ rY, tagSt c st'⟩ := by
      show (XMach.act xsys (XMach.solo xsys Y (tagTh c Fr T0) (a + 1)).1
        (XMach.reader xsys Y (tagTh c Fr T0) ⟨l0.map (tagA c) ++ rY, .idle⟩ a)).2.1 = _
      rw [eY, eS, aY]
    refine ⟨l', st', eXn, eYn, fun a' ha' => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ha') with h | h
    · exact hprev a' h
    · rw [h, eY, eS, aY]
      exact ⟨rfl, rfl⟩

/-- **Two nets side by side, two threads: the first stretch.**  Let the
second thread, beside the first on the net `XA` alone, only read for `b`
actions and then have the first agent of `XA` alone left in its list.  On
`XA` and `XB` side by side, after `b` rounds the first thread is where it
is after `b` actions alone on `XA`, the cells of `XA` are what it has made
of them, the cells of `XB` are untouched, and the second thread has passed
the cells of `XA` and stands before those of `XB`. -/
theorem beside_stretch {XA : XNet Arith} (XB : XNet Arith) {top : Id × Arith}
    {restA : List (Id × Arith)} (hA : XA.agents = top :: restA) (b : Nat)
    (hrd : ∀ a, a < b →
      (XMach.act xsys (XMach.solo xsys XA ⟨XA.agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys XA ⟨XA.agents, .idle⟩ ⟨restA ++ [top], .idle⟩ a)).1 =
          (XMach.solo xsys XA ⟨XA.agents, .idle⟩ (a + 1)).1 ∧
        (XMach.act xsys (XMach.solo xsys XA ⟨XA.agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys XA ⟨XA.agents, .idle⟩ ⟨restA ++ [top], .idle⟩ a)).2.2 = 0)
    (hend : XMach.reader xsys XA ⟨XA.agents, .idle⟩ ⟨restA ++ [top], .idle⟩ b =
      ⟨[top], .idle⟩)
    (hs : ∀ j, j < b → (XMach.solo xsys XA ⟨XA.agents, .idle⟩ j).2 ≠ ⟨[], .idle⟩) :
    ∃ Yb, ((XMach.init (beside (tagNet 0 XA) (tagNet 1 XB)) 2).trace xsys
          (fun i => i % 2) (2 * b)).1 =
        ⟨Yb, [tagTh 0 (XB.agents.map (tagA 1))
            (XMach.solo xsys XA ⟨XA.agents, .idle⟩ b).2,
          ⟨XB.agents.map (tagA 1) ++ [tagA 0 top], .idle⟩]⟩ ∧
      Inside 0 (XB.agents.map (tagA 1)) (XMach.solo xsys XA ⟨XA.agents, .idle⟩ b).1 Yb ∧
      Moves 0 (beside (tagNet 0 XA) (tagNet 1 XB)) Yb := by
  have hI : Inside 0 (XB.agents.map (tagA 1)) XA (beside (tagNet 0 XA) (tagNet 1 XB)) :=
    ⟨looks_left XA XB, rfl, fun _ he => mem_tag_other (by decide) he⟩
  have eInit : XMach.init (beside (tagNet 0 XA) (tagNet 1 XB)) 2 =
      ⟨beside (tagNet 0 XA) (tagNet 1 XB),
        [tagTh 0 (XB.agents.map (tagA 1)) ⟨XA.agents, .idle⟩,
          ⟨restA.map (tagA 0) ++ (XB.agents.map (tagA 1) ++ [tagA 0 top]), .idle⟩]⟩ := by
    rw [XMach.init_succ]
    have e1 : (beside (tagNet 0 XA) (tagNet 1 XB)).agents =
        tagA 0 top :: (restA.map (tagA 0) ++ XB.agents.map (tagA 1)) := by
      show XA.agents.map (tagA 0) ++ XB.agents.map (tagA 1) = _
      rw [hA]
      rfl
    rw [e1, hA]
    show (⟨_, [⟨tagA 0 top :: (restA.map (tagA 0) ++ XB.agents.map (tagA 1)), .idle⟩,
        ⟨(restA.map (tagA 0) ++ XB.agents.map (tagA 1)) ++ [tagA 0 top], .idle⟩]⟩ :
        XMach Arith) = _
    rw [List.append_assoc]
    rfl
  rw [eInit]
  have hR := hI.reader ⟨XA.agents, .idle⟩ restA [top]
    (XB.agents.map (tagA 1) ++ [tagA 0 top]) b (Nat.succ_pos 0) hrd
    (by rw [hend]; exact Nat.le_refl 1) hs
  obtain ⟨l, st, eX, eY, hprev⟩ := hR b (Nat.le_refl b)
  have tr := XMach.trace_readers (xs := xsys) (X := beside (tagNet 0 XA) (tagNet 1 XB))
    (T₀ := tagTh 0 (XB.agents.map (tagA 1)) ⟨XA.agents, .idle⟩)
    (Ts := [⟨restA.map (tagA 0) ++ (XB.agents.map (tagA 1) ++ [tagA 0 top]), .idle⟩])
    (A := b) (fun T hT a ha => by
      rw [List.mem_singleton.1 hT]
      exact hprev a ha) b (Nat.le_refl b)
  obtain ⟨Yb, r', sY, hIb, mvb, hr'⟩ :=
    Inside.solo b (XB.agents.map (tagA 1)) ⟨XA.agents, .idle⟩ hI hs
  have er : r' = XB.agents.map (tagA 1) := by
    rcases hr' with e | e <;> exact e
  subst er
  refine ⟨Yb, ?_, hIb, mvb⟩
  have tr2 : ((⟨beside (tagNet 0 XA) (tagNet 1 XB),
      [tagTh 0 (XB.agents.map (tagA 1)) ⟨XA.agents, .idle⟩,
        ⟨restA.map (tagA 0) ++ (XB.agents.map (tagA 1) ++ [tagA 0 top]), .idle⟩]⟩ :
        XMach Arith).trace xsys (fun i => i % 2) (2 * b)).1 =
      ⟨(XMach.solo xsys (beside (tagNet 0 XA) (tagNet 1 XB))
          (tagTh 0 (XB.agents.map (tagA 1)) ⟨XA.agents, .idle⟩) b).1,
        [(XMach.solo xsys (beside (tagNet 0 XA) (tagNet 1 XB))
          (tagTh 0 (XB.agents.map (tagA 1)) ⟨XA.agents, .idle⟩) b).2,
          XMach.reader xsys (beside (tagNet 0 XA) (tagNet 1 XB))
            (tagTh 0 (XB.agents.map (tagA 1)) ⟨XA.agents, .idle⟩)
            ⟨restA.map (tagA 0) ++ (XB.agents.map (tagA 1) ++ [tagA 0 top]), .idle⟩ b]⟩ :=
    congrArg Prod.fst tr
  rw [tr2, sY, eY]
  have e2 := eX.symm.trans hend
  injection e2 with e3 e4
  have el : l = [] := by
    have hlen := congrArg List.length e3
    rw [List.length_append] at hlen
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst el
  subst e4
  rfl

theorem sum_start (m n : Nat) : Start n (sum (m + 1) n) (n + 3 + m) := by
  have h := start_sum m n
  have e : m + n + 3 = n + 3 + m := by omega
  rw [e] at h
  exact h

/-- One thread on the net for `(m + 1) + n` is not at rest before its last
action. -/
theorem sum_busy (m n : Nat) : ∀ j, j < soloWork (m + 1) n →
    (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ j).2 ≠ ⟨[], .idle⟩ := by
  intro j hj e
  obtain ⟨-, -, hb⟩ := solo_work (m + 1) n
  rw [XMach.init_one] at hb
  have h := hb j hj
  rw [XMach.trace_one] at h
  exact h (all_rest_resting fun T hT => by
    rcases List.mem_cons.1 hT with e' | hT
    · rw [e']
      exact e
    · cases hT)

theorem turnRest_room (m n : Nat) : turnRest m n 0 + 4 ≤ soloWork (m + 1) n := by
  rw [soloWork_succ]
  cases n with
  | zero =>
    show 3 * (m - 0) + 8 + (3 * (m - 0) + 15) / 16 + 0 + 4 ≤ _
    omega
  | succ n' =>
    have hz := zeroCost_le m (turnAt m (n' + 1) 0)
    have ht : turnAt m (n' + 1) 0 = 3 * (m - 0) + 3 * (n' + 1) + 1 + (3 * (m - 0) + 11) / 16 := rfl
    show turnAt m (n' + 1) 0 + zeroCost m (turnAt m (n' + 1) 0) + 3 + (0 + 1) + 4 ≤ _
    omega

/-- **Two additions side by side, two threads: the first stretch.**  With
`m` at least two and outside the race for the last pair of the first
addition, let `b + 1` be `turnRest m n 0`.  After `b` rounds the first
thread is where it is after `b` actions alone on the first addition, whose
cells are what it has made of them; the second thread has only read, has
passed the cells of the first addition, and has the cells of the second,
untouched, at the head of its list. -/
theorem two_sums_stretch (m n m' n' : Nat) (hm : 2 ≤ m)
    (hw : turnAt m n 0 ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n 0) :
    ∃ b Yb, turnRest m n 0 = b + 1 ∧
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') 2).trace xsys (fun i => i % 2)
          (2 * b)).1 =
        ⟨Yb, [tagTh 0 ((sum (m' + 1) n').agents.map (tagA 1))
            (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).2,
          ⟨(sum (m' + 1) n').agents.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)],
            .idle⟩]⟩ ∧
      Inside 0 ((sum (m' + 1) n').agents.map (tagA 1))
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).1 Yb ∧
      Looks 1 (sum (m' + 1) n') Yb := by
  obtain ⟨b, eb, rd⟩ := reader_top m n hm hw
  obtain ⟨restA, hAa⟩ := (sum_start m n).head
  have e : (sum (m + 1) n).agents.drop (0 + 1) ++ (sum (m + 1) n).agents.take (0 + 1) =
      restA ++ [([n + 3 + m + 1], .succ)] := by
    rw [hAa]
    rfl
  rw [e] at rd
  have room := turnRest_room m n
  obtain ⟨Yb, tr, hI, mv⟩ := beside_stretch (sum (m' + 1) n') hAa b
    (fun a ha => rd.2 a ha) rd.1 (fun j hj => sum_busy m n j (by omega))
  exact ⟨b, Yb, eb, tr, hI, mv.other 1 _ (by decide) (looks_right _ _)⟩

theorem Inside.take_other {c d : Nat} {Fr : List (Id × Arith)} {X Y : XNet Arith}
    (h : Inside c Fr X Y) (hd : d ≠ c) (a : Id) :
    Inside c (Fr.filter fun e => decide (e.1 ≠ a ++ [d])) X (Y.takeAgent (a ++ [d])) := by
  refine ⟨h.looks.take_other hd a, ?_, fun e he => h.frame e (List.mem_filter.1 he).1⟩
  show (Y.agents.filter fun e => decide (e.1 ≠ a ++ [d])) = _
  have hf : ((X.agents.map (tagA c)).filter fun e => decide (e.1 ≠ a ++ [d])) =
      X.agents.map (tagA c) :=
    List.filter_eq_self.2 fun e he => decide_eq_true fun e' => by
      have ht := mem_tag_self he
      rw [e', tagged_other hd] at ht
      cases ht
  rw [h.agents, List.filter_append, hf]

/-- One action of the thread on the net that comes first, with what is
known of its next actions carried along. -/
theorem Inside.step {c : Nat} {Fr : List (Id × Arith)} {X Y : XNet Arith}
    (h : Inside c Fr X Y) (r : List (Id × Arith)) (S : XThread Arith) {k : Nat}
    (hs : ∀ j, j < k + 1 → (XMach.solo xsys X S j).2 ≠ ⟨[], .idle⟩) :
    ∃ (X1 : XNet Arith) (S1 : XThread Arith) (Y1 : XNet Arith) (r1 : List (Id × Arith))
      (c1 : Nat), XMach.act xsys Y (tagTh c r S) = (Y1, tagTh c r1 S1, c1) ∧
      Inside c Fr X1 Y1 ∧ Moves c Y Y1 ∧
      ∀ j, j < k → (XMach.solo xsys X1 S1 j).2 ≠ ⟨[], .idle⟩ := by
  obtain ⟨Y1, r1, aY, I1, mv, -⟩ := h.act r S (hs 0 (Nat.succ_pos k))
  exact ⟨(XMach.act xsys X S).1, (XMach.act xsys X S).2.1, Y1, r1, (XMach.act xsys X S).2.2,
    aY, I1, mv, fun j hj => hs (j + 1) (Nat.succ_lt_succ hj)⟩

/-- A round of two threads in turn. -/
theorem round_two {Y Y1 Y2 : XNet Arith} {P P' Q Q' : XThread Arith} {c1 c2 : Nat}
    (a1 : XMach.act xsys Y P = (Y1, P', c1)) (a2 : XMach.act xsys Y1 Q = (Y2, Q', c2)) :
    ((⟨Y, [P, Q]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * 1)).1 = ⟨Y2, [P', Q']⟩ := by
  have e1 : XMach.step xsys ⟨Y, [P, Q]⟩ 0 = (⟨Y1, [P', Q]⟩, c1) :=
    XMach.step_eq (M := ⟨Y, [P, Q]⟩) (t := 0) rfl a1
  have e2 : XMach.step xsys ⟨Y1, [P', Q]⟩ 1 = (⟨Y2, [P', Q']⟩, c2) :=
    XMach.step_eq (M := ⟨Y1, [P', Q]⟩) (t := 1) rfl a2
  show (XMach.step xsys (XMach.step xsys ⟨Y, [P, Q]⟩ 0).1 1).1 = _
  rw [e1, e2]

theorem trace_succ_two (M : XMach Arith) (N : Nat) :
    (M.trace xsys (fun i => i % 2) (N + 1)).1 =
      ((M.trace xsys (fun i => i % 2) N).1.step xsys (N % 2)).1 := rfl

/-- **The five actions that claim the first pair of an addition inside a
larger memory**, whatever is done to the other cells in between: the
thread reads the top successor, follows its wire to the adder, takes the
successor, takes the adder, and then holds what the rule makes of them. -/
theorem Looks.claim_acts {c n hi : Nat} {X : XNet Arith} (st : Start n X hi)
    (rest : List (Id × Arith)) {Z0 Z1 Z2 Z3 Z4 : XNet Arith} (h0 : Looks c X Z0)
    (h1 : Looks c X Z1) (h2 : Looks c X Z2) (h3 : Looks c X Z3)
    (h4 : Looks c (X.takeAgent [hi + 1]) Z4) :
    XMach.act xsys Z0 ⟨([hi + 1] ++ [c], .succ) :: rest, .idle⟩ =
        (Z0, ⟨rest, .look ([hi + 1] ++ [c]) .succ⟩, 0) ∧
      XMach.act xsys Z1 ⟨rest, .look ([hi + 1] ++ [c]) .succ⟩ =
        (Z1, ⟨rest, .seek ([hi + 1] ++ [c]) .succ ([hi + 1] ++ [c], 0) ([1] ++ [c], 0)⟩, 0) ∧
      XMach.act xsys Z2
          ⟨rest, .seek ([hi + 1] ++ [c]) .succ ([hi + 1] ++ [c], 0) ([1] ++ [c], 0)⟩ =
        (Z2, ⟨rest, .ready ([hi + 1] ++ [c]) ([1] ++ [c]) .succ .add⟩, 0) ∧
      XMach.act xsys Z3 ⟨rest, .ready ([hi + 1] ++ [c]) ([1] ++ [c]) .succ .add⟩ =
        (Z3.takeAgent ([hi + 1] ++ [c]),
          ⟨rest, .half ([hi + 1] ++ [c]) ([1] ++ [c]) .succ .add⟩, 0) ∧
      XMach.act xsys Z4 ⟨rest, .half ([hi + 1] ++ [c]) ([1] ++ [c]) .succ .add⟩ =
        (Z4.takeAgent ([1] ++ [c]),
          ⟨rest, .write ((addSucc.swap.toX.newAgents [hi + 1] [1]).map (tagA c))
            ((addSucc.swap.toX.newLinks ar [hi + 1] [1] .succ .add).map (tagL c))⟩, 1) := by
  obtain ⟨-, -, h₁, h₂, hne, h₄⟩ := st.pair
  have gne : ([hi + 1] ++ [c] : Id) ≠ [1] ++ [c] := fun e => hne (List.append_cancel_right e)
  have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
  refine ⟨XMach.act_idle_pos (xs := xsys) (e := ([hi + 1] ++ [c], Arith.succ))
      ((h0.agent _).trans h₁),
    XMach.act_look (xs := xsys)
      ((h1.wire ([hi + 1], 0)).trans (congrArg (Option.map (tagPort c)) h₂)),
    XMach.act_seek_found (xs := xsys) (c := ([1] ++ [c], 0))
      ((ite_pos' rfl).trans ((h2.agent [1]).trans st.adder)) ⟨gne, rfl⟩,
    XMach.act_ready (xs := xsys) ((h3.agent _).trans h₁), ?_⟩
  have aY := XMach.act_half (xs := xsys) (X := Z4) (todo := rest) (a := [hi + 1] ++ [c])
    (b := [1] ++ [c]) (α := .succ) (β := .add) (R := addSucc.swap.toX)
    ((ite_pos' ⟨(h4.agent [1]).trans h₄, gne⟩).trans hR)
  rw [(rule_tag c hR hne).1, (rule_tag c hR hne).2] at aY
  exact aY

/-- **Four rounds and a half: the second thread claims the first pair of
the second net.**  The first thread acts on the net that comes first in
memory; the second thread has the top successor of an addition, tagged
`1`, at the head of its list.  After four rounds it has taken the
successor, and in the fifth, after the action of the first thread, it
takes the adder. -/
theorem claim_rounds {n' hi : Nat} {X XB W : XNet Arith} {Fr1 : List (Id × Arith)}
    (stB : Start n' XB hi) (hI : Inside 0 (([hi + 1] ++ [1], .succ) :: Fr1) X W)
    (hB : Looks 1 XB W) (S : XThread Arith) (r rest : List (Id × Arith))
    (hs : ∀ j, j < 4 + 1 → (XMach.solo xsys X S j).2 ≠ ⟨[], .idle⟩) :
    ∃ (W4 W5 : XNet Arith) (P4 P5 : XThread Arith) (c5 : Nat),
      ((⟨W, [tagTh 0 r S, ⟨([hi + 1] ++ [1], .succ) :: rest, .idle⟩]⟩ : XMach Arith).trace
          xsys (fun i => i % 2) (2 * 4)).1 =
        ⟨W4, [P4, ⟨rest, .half ([hi + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩]⟩ ∧
      XMach.act xsys W4 P4 = (W5, P5, c5) ∧
      XMach.act xsys W5 ⟨rest, .half ([hi + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩ =
        (W5.takeAgent ([1] ++ [1]),
          ⟨rest, .write ((addSucc.swap.toX.newAgents [hi + 1] [1]).map (tagA 1))
            ((addSucc.swap.toX.newLinks ar [hi + 1] [1] .succ .add).map (tagL 1))⟩, 1) := by
  obtain ⟨X1, S1, Z0, r1, c0, a0, I1, mv0, hs1⟩ := hI.step r S hs
  have B0 := mv0.other 1 XB (by decide) hB
  obtain ⟨X2, S2, Z1, r2, c1, a1, I2, mv1, hs2⟩ := I1.step r1 S1 hs1
  have B1 := mv1.other 1 XB (by decide) B0
  obtain ⟨X3, S3, Z2, r3, c2, a2, I3, mv2, hs3⟩ := I2.step r2 S2 hs2
  have B2 := mv2.other 1 XB (by decide) B1
  obtain ⟨X4, S4, Z3, r4, c3, a3, I4, mv3, hs4⟩ := I3.step r3 S3 hs3
  have B3 := mv3.other 1 XB (by decide) B2
  have I4' := I4.take_other (d := 1) (by decide) [hi + 1]
  have B4 : Looks 1 (XB.takeAgent [hi + 1]) (Z3.takeAgent ([hi + 1] ++ [1])) :=
    B3.take [hi + 1]
  obtain ⟨X5, S5, Z4, r5, c4, a4, -, mv4, -⟩ := I4'.step (k := 0) r4 S4 hs4
  have B5 := mv4.other 1 _ (by decide) B4
  obtain ⟨q0, q1, q2, q3, q4⟩ := Looks.claim_acts stB rest B0 B1 B2 B3 B5
  refine ⟨Z3.takeAgent ([hi + 1] ++ [1]), Z4, tagTh 0 r4 S4, tagTh 0 r5 S5, c4, ?_, a4, q4⟩
  have t1 := round_two a0 q0
  have t2 := round_two a1 q1
  have t3 := round_two a2 q2
  have t4 := round_two a3 q3
  rw [show (2 * 4 : Nat) = 2 * (1 + 3) from rfl, trace_mod_add, t1,
    show (2 * 3 : Nat) = 2 * (1 + 2) from rfl, trace_mod_add, t2,
    show (2 * 2 : Nat) = 2 * (1 + 1) from rfl, trace_mod_add, t3, t4]

/-- **With two threads the second addition starts in round
`turnRest m n 0 + 3`.**  On the net with `(m + 1) + n` and `(m' + 1) + n'`
side by side, `m` at least two and outside the race for the last pair of
the first addition, the second thread claims the first pair of the second
addition, its top successor and its adder, in its action of the round
numbered `turnRest m n 0 + 3`, and then holds what the rule makes of
them. -/
theorem two_sums_second_claim (m n m' n' : Nat) (hm : 2 ≤ m)
    (hw : turnAt m n 0 ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n 0) :
    ∃ b Y P l, turnRest m n 0 = b + 1 ∧
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') 2).trace xsys (fun i => i % 2)
          (2 * (b + 4) + 1)).1.step xsys 1 =
        (⟨Y, [P, ⟨l, .write ((addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).map (tagA 1))
          ((addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).map (tagL 1))⟩]⟩,
          1) := by
  obtain ⟨b, Yb, eb, tr, hIb, hBb⟩ := two_sums_stretch m n m' n' hm hw
  have stB := sum_start m' n'
  obtain ⟨restB, hBa⟩ := stB.head
  rw [hBa] at tr hIb
  have hI' : Inside 0 (([n' + 3 + m' + 1] ++ [1], .succ) :: restB.map (tagA 1))
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).1 Yb := hIb
  have room := turnRest_room m n
  obtain ⟨W4, W5, P4, P5, c5, t4, a4, q4⟩ := claim_rounds stB hI' hBb
    (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).2
    ((([n' + 3 + m' + 1], Arith.succ) :: restB).map (tagA 1))
    (restB.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)])
    (fun j hj => by
      rw [← XMach.solo_add]
      exact sum_busy m n (b + j) (by omega))
  have e1 : ((XMach.init (twoSums (m + 1) n (m' + 1) n') 2).trace xsys (fun i => i % 2)
      (2 * (b + 4))).1 =
      ⟨W4, [P4, ⟨restB.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)],
        .half ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩]⟩ := by
    rw [trace_mod_add, tr]
    exact t4
  refine ⟨b, W5.takeAgent ([1] ++ [1]), P5,
    restB.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)], eb, ?_⟩
  have s1 : XMach.step xsys ⟨W4, [P4, ⟨restB.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)],
      .half ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩]⟩ 0 =
      (⟨W5, [P5, ⟨restB.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)],
        .half ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩]⟩, c5) :=
    XMach.step_eq (M := ⟨W4, [P4, ⟨restB.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)],
      .half ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩]⟩) (t := 0) rfl a4
  rw [trace_succ_two, Nat.mul_mod_right, e1, s1]
  exact XMach.step_eq (M := ⟨W5, [P5, ⟨restB.map (tagA 1) ++ [([n + 3 + m + 1] ++ [0], .succ)],
    .half ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩]⟩) (t := 1) rfl q4

theorem act_self (W : XNet Arith) (P : XThread Arith) :
    XMach.act xsys W P =
      ((XMach.act xsys W P).1, (XMach.act xsys W P).2.1, (XMach.act xsys W P).2.2) := rfl

/-- A thread that has segments left to write writes them and reloads its
list, one action a round, whatever the other thread does. -/
theorem links_rounds : ∀ (ls : List (Port × Port)) (W : XNet Arith) (P : XThread Arith)
    (l : List (Id × Arith)),
    ∃ Y P', ((⟨W, [P, ⟨l, .write [] ls⟩]⟩ : XMach Arith).trace xsys (fun i => i % 2)
      (2 * (ls.length + 1))).1 = ⟨Y, [P', ⟨Y.agents, .idle⟩]⟩
  | [], W, P, l => by
    have a2 : XMach.act xsys (XMach.act xsys W P).1 ⟨l, .write [] []⟩ =
        ((XMach.act xsys W P).1, ⟨(XMach.act xsys W P).1.agents, .idle⟩, 0) := rfl
    exact ⟨(XMach.act xsys W P).1, (XMach.act xsys W P).2.1, round_two (act_self W P) a2⟩
  | (p, q) :: ls, W, P, l => by
    obtain ⟨Y, P', h⟩ :=
      links_rounds ls ((XMach.act xsys W P).1.putLink p q) (XMach.act xsys W P).2.1 l
    refine ⟨Y, P', ?_⟩
    have a2 : XMach.act xsys (XMach.act xsys W P).1 ⟨l, .write [] ((p, q) :: ls)⟩ =
        ((XMach.act xsys W P).1.putLink p q, ⟨l, .write [] ls⟩, 0) := rfl
    have t1 := round_two (act_self W P) a2
    have e : 2 * (((p, q) :: ls).length + 1) = 2 * (1 + (ls.length + 1)) := by
      rw [List.length_cons]
      omega
    rw [e, trace_mod_add, t1]
    exact h

/-- **A thread that has claimed a pair writes and reloads whatever the
other thread does**: with `as` agents and `ls` segments left to write, it
has the whole memory as its list after `as.length + ls.length + 1`
rounds. -/
theorem write_rounds : ∀ (as : List (Id × Arith)) (ls : List (Port × Port)) (W : XNet Arith)
    (P : XThread Arith) (l : List (Id × Arith)),
    ∃ Y P', ((⟨W, [P, ⟨l, .write as ls⟩]⟩ : XMach Arith).trace xsys (fun i => i % 2)
      (2 * (as.length + ls.length + 1))).1 = ⟨Y, [P', ⟨Y.agents, .idle⟩]⟩
  | [], ls, W, P, l => by
    obtain ⟨Y, P', h⟩ := links_rounds ls W P l
    refine ⟨Y, P', ?_⟩
    have e : 2 * (([] : List (Id × Arith)).length + ls.length + 1) = 2 * (ls.length + 1) := by
      rw [List.length_nil]
      omega
    rw [e]
    exact h
  | (i, γ) :: as, ls, W, P, l => by
    obtain ⟨Y, P', h⟩ :=
      write_rounds as ls ((XMach.act xsys W P).1.putAgent i γ) (XMach.act xsys W P).2.1 l
    refine ⟨Y, P', ?_⟩
    have a2 : XMach.act xsys (XMach.act xsys W P).1 ⟨l, .write ((i, γ) :: as) ls⟩ =
        ((XMach.act xsys W P).1.putAgent i γ, ⟨l, .write as ls⟩, 0) := rfl
    have t1 := round_two (act_self W P) a2
    have e : 2 * (((i, γ) :: as).length + ls.length + 1) =
        2 * (1 + (as.length + ls.length + 1)) := by
      rw [List.length_cons]
      omega
    rw [e, trace_mod_add, t1]
    exact h

/-- **With two threads the second thread has made the first interaction of
the second addition after round `turnRest m n 0 + 14`**: it then has the
whole memory as its list, sixteen rounds after it came to the second
addition, as a thread alone. -/
theorem two_sums_second_reload (m n m' n' : Nat) (hm : 2 ≤ m)
    (hw : turnAt m n 0 ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n 0) :
    ∃ b Y P, turnRest m n 0 = b + 1 ∧
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') 2).trace xsys (fun i => i % 2)
          (2 * (b + 16))).1 = ⟨Y, [P, ⟨Y.agents, .idle⟩]⟩ := by
  obtain ⟨b, Y5, P5, l, eb, h⟩ := two_sums_second_claim m n m' n' hm hw
  have e5 : ((XMach.init (twoSums (m + 1) n (m' + 1) n') 2).trace xsys (fun i => i % 2)
      (2 * (b + 5))).1 =
      ⟨Y5, [P5, ⟨l, .write ((addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).map (tagA 1))
        ((addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).map (tagL 1))⟩]⟩ := by
    have e : 2 * (b + 5) = 2 * (b + 4) + 1 + 1 := by omega
    rw [e, trace_succ_two, show (2 * (b + 4) + 1) % 2 = 1 by omega, h]
  obtain ⟨Y, P, hw'⟩ := write_rounds
    ((addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).map (tagA 1))
    ((addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).map (tagL 1)) Y5 P5 l
  have hlen : ((addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).map (tagA 1)).length +
      ((addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).map (tagL 1)).length +
        1 = 11 := by
    rw [List.length_map, List.length_map,
      newAgents_swap (a := [1]) (s := [n' + 3 + m' + 1]) (fun e => by
        injection e with e1
        omega), newLinks_swap]
    rfl
  rw [hlen] at hw'
  refine ⟨b, Y, P, eb, ?_⟩
  have e : 2 * (b + 16) = 2 * ((b + 5) + 11) := by omega
  rw [e, trace_mod_add, e5]
  exact hw'

/-- One thread on two additions side by side: after `22 * m + 3 * n + 35`
actions it has made the `m + 2` interactions of the first addition, has
passed what they leave, and has the cells of the second, untouched, as
its list. -/
theorem two_sums_first_done (m n m' n' : Nat) : ∃ Y1,
    Works xsys (twoSums (m + 1) n (m' + 1) n')
        ⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩ Y1
        ⟨(sum (m' + 1) n').agents.map (tagA 1), .idle⟩ (m + 2) (22 * m + 3 * n + 35) ∧
      Looks 1 (sum (m' + 1) n') Y1 := by
  have hA0 : Looks 0 (sum (m + 1) n) (twoSums (m + 1) n (m' + 1) n') := looks_left _ _
  have hB0 : Looks 1 (sum (m' + 1) n') (twoSums (m + 1) n (m' + 1) n') := looks_right _ _
  have eY0 : (twoSums (m + 1) n (m' + 1) n').agents =
      (sum (m + 1) n).agents.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1) := rfl
  obtain ⟨restA, hAa⟩ := (sum_start m n).head
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
  have eN := hA1.split hN' hNt (fun _ he => mem_tag_other (by decide) he)
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
  have w := wA'.trans pA
  have e2 : 17 * m + 25 + (5 * m + 3 * n + 10) = 22 * m + 3 * n + 35 := by omega
  rw [e2] at w
  exact ⟨Y1, w, hB1⟩

/-- **One thread claims the first pair of the second addition with its
action numbered `22 * m + 3 * n + 39`**, counting from zero: after the
rounds of the first addition and a pass over what they leave. -/
theorem two_sums_one_claim (m n m' n' : Nat) : ∃ Y l,
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') 1).trace xsys (fun _ => 0)
        (22 * m + 3 * n + 39)).1.step xsys 0 =
      (⟨Y, [⟨l, .write ((addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).map (tagA 1))
        ((addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).map (tagL 1))⟩]⟩,
        1) := by
  obtain ⟨Y1, w1, hB1⟩ := two_sums_first_done m n m' n'
  have stB := sum_start m' n'
  obtain ⟨restB, hBa⟩ := stB.head
  rw [hBa] at w1
  obtain ⟨q0, q1, q2, q3, q4⟩ := Looks.claim_acts stB (restB.map (tagA 1)) hB1 hB1 hB1 hB1
    (hB1.take [n' + 3 + m' + 1])
  have w4 : Works xsys Y1 ⟨([n' + 3 + m' + 1] ++ [1], .succ) :: restB.map (tagA 1), .idle⟩
      (Y1.takeAgent ([n' + 3 + m' + 1] ++ [1]))
      ⟨restB.map (tagA 1), .half ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩
      (0 + (0 + (0 + (0 + 0)))) (0 + 1 + 1 + 1 + 1) :=
    .step (fun e => List.cons_ne_nil _ _ (congrArg XThread.todo e)) q0
      (.step (look_ne_rest _ _ _) q1 (.step (seek_ne_rest _ _ _ _ _) q2
        (.step (ready_ne_rest _ _ _ _ _) q3 (.refl _ _))))
  have t := (w1.trans w4).trace.1
  refine ⟨(Y1.takeAgent ([n' + 3 + m' + 1] ++ [1])).takeAgent ([1] ++ [1]),
    restB.map (tagA 1), ?_⟩
  rw [XMach.init_one]
  have e : 22 * m + 3 * n + 39 = 22 * m + 3 * n + 35 + (0 + 1 + 1 + 1 + 1) := by omega
  rw [e, t]
  exact XMach.step_eq (M := ⟨Y1.takeAgent ([n' + 3 + m' + 1] ++ [1]),
    [⟨restB.map (tagA 1), .half ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) .succ .add⟩]⟩)
    (t := 0) rfl q4

/-- **The head start.**  With two threads the second addition starts at
least `18 * m + 20` rounds sooner than with one. -/
theorem head_start (m n : Nat) : turnRest m n 0 + 3 + (18 * m + 20) ≤ 22 * m + 3 * n + 39 := by
  cases n with
  | zero =>
    show 3 * (m - 0) + 8 + (3 * (m - 0) + 15) / 16 + 0 + 3 + (18 * m + 20) ≤ _
    omega
  | succ n' =>
    have hz := zeroCost_le m (turnAt m (n' + 1) 0)
    have ht : turnAt m (n' + 1) 0 = 3 * (m - 0) + 3 * (n' + 1) + 1 + (3 * (m - 0) + 11) / 16 := rfl
    show turnAt m (n' + 1) 0 + zeroCost m (turnAt m (n' + 1) 0) + 3 + (0 + 1) + 3 +
      (18 * m + 20) ≤ _
    omega

/-- `6 + 10` twice: the second thread claims the first pair of the second
addition in round 57, and one thread alone with its action 179. -/
theorem _root_.INet.Checks.Arith.TwoSums.c1
    : ∃ Y P l, ((XMach.init (twoSums 6 10 6 10) 2).trace xsys (fun i => i % 2)
      (2 * 57 + 1)).1.step xsys 1 =
    (⟨Y, [P, ⟨l, .write ((addSucc.swap.toX.newAgents [19] [1]).map (tagA 1))
      ((addSucc.swap.toX.newLinks ar [19] [1] .succ .add).map (tagL 1))⟩]⟩, 1) := by
  obtain ⟨b, Y, P, l, eb, h⟩ := two_sums_second_claim 5 10 5 10 (by decide) (by decide)
  have e : b = 53 := by
    have : turnRest 5 10 0 = 54 := by decide
    omega
  subst e
  exact ⟨Y, P, l, h⟩

theorem _root_.INet.Checks.Arith.TwoSums.c2
    : ∃ Y l, ((XMach.init (twoSums 6 10 6 10) 1).trace xsys (fun _ => 0) 179).1.step
      xsys 0 =
    (⟨Y, [⟨l, .write ((addSucc.swap.toX.newAgents [19] [1]).map (tagA 1))
      ((addSucc.swap.toX.newLinks ar [19] [1] .succ .add).map (tagL 1))⟩]⟩, 1) :=
  two_sums_one_claim 5 10 5 10

/-- The state of a thread that is about to reload its list. -/
def isReload : TState Arith → Bool
  | .write [] [] => true
  | _ => false

/-- The tag of a name: its last number. -/
def lastOf (i : Id) : Nat := i.getLast?.getD 9

/-- **The first collision of two threads on two nets side by side**: the
first reload, from round `r0` on, by a thread whose new list starts with a
cell of the other net, the first thread working on the net tagged `0` and
the second on the net tagged `1`.  Gives the round, the thread, and
whether that cell is an adder. -/
def firstForeign (r0 : Nat) : Nat → Nat → XMach Arith → Option (Nat × Nat × Bool)
  | 0, _, _ => none
  | f + 1, i, M =>
    match M.ths[i % 2]?, M.mem.agents.head? with
    | some T, some e =>
      if r0 ≤ i / 2 && isReload T.st && lastOf e.1 != i % 2 then
        some (i / 2, i % 2, e.2 == Arith.add)
      else firstForeign r0 f (i + 1) (M.step xsys (i % 2)).1
    | _, _ => firstForeign r0 f (i + 1) (M.step xsys (i % 2)).1

/-- Where the first collision is, by the round `b` in which the second
thread comes to the second addition: if `b % 17` is at most eight, the
first thread reloads in round `b + 15 - b % 17` and finds the new adder of
the second addition at the head of memory; if it is nine, the first thread
reloads in round `b + 6` and finds the new successor of the second
addition there, its own adder after it; otherwise the second thread
reloads in round `b + 15` and finds the adder of the first addition. -/
def crossLaw (b : Nat) : Nat × Nat × Bool :=
  if b % 17 ≤ 8 then (b + 15 - b % 17, 0, true)
  else if b % 17 = 9 then (b + 6, 0, false) else (b + 15, 1, true)

/-- The run on `(m + 1) + n` and `(m' + 1) + n'` side by side follows
`crossLaw`. -/
def crossOk (m n m' n' : Nat) : Bool :=
  firstForeign (turnRest m n 0 + 4) 400 0 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2) ==
    some (crossLaw (turnRest m n 0 - 1))

set_option maxRecDepth 100000 in
/-- **Where two threads first collide, checked by the kernel on every
phase.**  On `6 + n` beside `2 + 0`, for every `n` below seventeen, so
that the round in which the second thread comes to the second addition
takes every value modulo seventeen, the first reload that starts with a
cell of the other addition is where `crossLaw` says.  This is a
computation, size by size; it is not a proof for every size. -/
theorem first_collision_checked : ∀ n, n < 17 → crossOk 5 n 1 0 = true := by
  decide +kernel

/-- One for an adder. -/
def isAdd (α : Arith) : Nat := if α = Arith.add then 1 else 0

/-- The adders in a list of agents. -/
def adders : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => isAdd e.2 + adders l

theorem adders_append : ∀ (l₁ l₂ : List (Id × Arith)), adders (l₁ ++ l₂) = adders l₁ + adders l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show isAdd e.2 + adders (l₁ ++ l₂) = isAdd e.2 + adders l₁ + adders l₂
    rw [adders_append l₁ l₂, Nat.add_assoc]

theorem adders_filter_le (p : Id × Arith → Bool) : ∀ l : List (Id × Arith),
    adders (l.filter p) ≤ adders l
  | [] => Nat.le_refl 0
  | e :: l => by
    have ih := adders_filter_le p l
    by_cases h : p e = true
    · rw [List.filter_cons_of_pos h]
      show isAdd e.2 + adders (l.filter p) ≤ isAdd e.2 + adders l
      omega
    · rw [List.filter_cons_of_neg h]
      show adders (l.filter p) ≤ isAdd e.2 + adders l
      omega

/-- Taking an agent that is in memory takes it off the count of adders if
it is one. -/
theorem adders_take {a : Id} {α : Arith} : ∀ {l : List (Id × Arith)}, assoc a l = some α →
    adders (l.filter fun e => decide (e.1 ≠ a)) + isAdd α ≤ adders l
  | [], h => by cases h
  | (i, γ) :: l, h => by
    by_cases hi : i = a
    · have e : γ = α := by
        have h' : (if i = a then some γ else assoc a l) = some α := h
        rw [ite_pos' hi] at h'
        exact Option.some.inj h'
      have hle := adders_filter_le (fun e : Id × Arith => decide (e.1 ≠ a)) l
      rw [List.filter_cons_of_neg (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show ¬ decide (i ≠ a) = true
          exact fun hd => of_decide_eq_true hd hi)]
      show adders (l.filter fun e => decide (e.1 ≠ a)) + isAdd α ≤ isAdd γ + adders l
      rw [e]
      omega
    · have h' : (if i = a then some γ else assoc a l) = some α := h
      rw [ite_neg' hi] at h'
      have ih := adders_take (l := l) h'
      rw [List.filter_cons_of_pos (p := fun e : Id × Arith => decide (e.1 ≠ a))
        (by
          show decide (i ≠ a) = true
          exact decide_eq_true hi)]
      show isAdd γ + adders (l.filter fun e => decide (e.1 ≠ a)) + isAdd α ≤ isAdd γ + adders l
      omega

/-- The actions a thread has made toward a claim: one when it has read an
agent, two when it follows its wire, three when it has found the partner,
four when it has taken the first agent. -/
def credit : TState Arith → Nat
  | .idle => 0
  | .look _ _ => 1
  | .seek _ _ _ _ => 2
  | .ready _ _ _ _ => 3
  | .half _ _ _ _ => 4
  | .write _ _ => 0

/-- The actions a thread still has to make for the pair it has claimed:
one for each agent and each segment to write, and one to reload. -/
def owed : TState Arith → Nat
  | .write as ls => as.length + ls.length + 1
  | _ => 0

/-- The adders a thread holds: the one it has taken, those it has to
write. -/
def heldAdd : TState Arith → Nat
  | .half _ _ α _ => isAdd α
  | .write as _ => adders as
  | _ => 0

/-- **What a rule gives for its price.**  A rule of the addition writes at
least ten agents and segments, less eight for each adder it takes and
more eight for each it makes: the two rules of a successor write two
agents and eight segments and keep the adder, the two rules of zero write
two segments and end it. -/
theorem rule_cost {α β : Arith} {R : XRhs Arith} (hR : xsys.rule α β = some R) {a b : Id}
    (hne : a ≠ b) :
    10 + 8 * adders (R.newAgents a b) ≤
      (R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length +
        8 * (isAdd α + isAdd β) := by
  cases α <;> cases β <;> first
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)
    | (have e : R = addZero.toX := (Option.some.inj hR).symm
       subst e
       exact Nat.le_refl 10)
    | (have e : R = addZero.swap.toX := (Option.some.inj hR).symm
       subst e
       exact Nat.le_refl 10)
    | (have e : R = addSucc.toX := (Option.some.inj hR).symm
       subst e
       show 10 + 8 * adders (addSucc.toX.newAgents a b) ≤
         (addSucc.toX.newAgents a b).length +
           (addSucc.toX.newLinks ar a b .add .succ).length + 8 * (isAdd .add + isAdd .succ)
       rw [newAgents_add hne, newLinks_add]
       exact Nat.le_refl 18)
    | (have e : R = addSucc.swap.toX := (Option.some.inj hR).symm
       subst e
       show 10 + 8 * adders (addSucc.swap.toX.newAgents a b) ≤
         (addSucc.swap.toX.newAgents a b).length +
           (addSucc.swap.toX.newLinks ar a b .succ .add).length + 8 * (isAdd .succ + isAdd .add)
       rw [newAgents_swap (fun e => hne e.symm), newLinks_swap]
       exact Nat.le_refl 18)

/-- **The price of one action.**  Count sixteen for a claim, the actions a
thread has made toward a claim, and eight for each adder in memory or
held; against them the action itself, if it is not a rest, and the
actions the thread still owes for its claim.  No action makes the first
grow more than the second. -/
theorem act_cost (X : XNet Arith) (T : XThread Arith) :
    16 * (XMach.act xsys X T).2.2 + credit (XMach.act xsys X T).2.1.st +
        8 * (adders (XMach.act xsys X T).1.agents + heldAdd (XMach.act xsys X T).2.1.st) +
        owed T.st ≤
      XThread.busy T + owed (XMach.act xsys X T).2.1.st + credit T.st +
        8 * (adders X.agents + heldAdd T.st) := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil =>
      show 16 * 0 + 0 + 8 * (adders X.agents + 0) + 0 ≤ 0 + 0 + 0 + 8 * (adders X.agents + 0)
      omega
    | cons e rest =>
      by_cases ha : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos (xs := xsys) (X := X) (rest := rest) ha]
        show 16 * 0 + 1 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 0 + 8 * (adders X.agents + 0)
        omega
      · rw [XMach.act_idle_neg (xs := xsys) (X := X) (rest := rest) ha]
        show 16 * 0 + 0 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 0 + 8 * (adders X.agents + 0)
        omega
  | look a α =>
    cases hq : assoc ((a, 0) : Port) X.wires with
    | none =>
      rw [XMach.act_look_none (xs := xsys) (todo := todo) (α := α) hq]
      show 16 * 0 + 0 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 1 + 8 * (adders X.agents + 0)
      omega
    | some q =>
      rw [XMach.act_look (xs := xsys) (todo := todo) (α := α) hq]
      show 16 * 0 + 2 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 1 + 8 * (adders X.agents + 0)
      omega
  | seek a α p q =>
    cases hc : (if q.2 = 0 then assoc q.1 X.agents else none) with
    | none =>
      cases hn : nextSeg X.wires q p with
      | none =>
        rw [XMach.act_seek_stop (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 16 * 0 + 0 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 2 + 8 * (adders X.agents + 0)
        omega
      | some q' =>
        rw [XMach.act_seek_next (xs := xsys) (todo := todo) (a := a) (α := α) hc hn]
        show 16 * 0 + 2 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 2 + 8 * (adders X.agents + 0)
        omega
    | some β =>
      by_cases hr : a ≠ q.1 ∧ (xsys.rule α β).isSome
      · rw [XMach.act_seek_found (xs := xsys) (todo := todo) (p := p) hc hr]
        show 16 * 0 + 3 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 2 + 8 * (adders X.agents + 0)
        omega
      · rw [XMach.act_seek_norule (xs := xsys) (todo := todo) (p := p) hc hr]
        show 16 * 0 + 0 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 2 + 8 * (adders X.agents + 0)
        omega
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      have ht : adders (X.takeAgent a).agents + isAdd α ≤ adders X.agents := adders_take ha
      show 16 * 0 + 4 + 8 * (adders (X.takeAgent a).agents + isAdd α) + 0 ≤
        1 + 0 + 3 + 8 * (adders X.agents + 0)
      omega
    · rw [XMach.act_ready_neg (xs := xsys) (todo := todo) (b := b) (β := β) ha]
      show 16 * 0 + 0 + 8 * (adders X.agents + 0) + 0 ≤ 1 + 0 + 3 + 8 * (adders X.agents + 0)
      omega
  | half a b α β =>
    have fail : ∀ hcond : (if assoc b X.agents = some β ∧ a ≠ b then xsys.rule α β else none) =
        none,
        16 * (XMach.act xsys X ⟨todo, .half a b α β⟩).2.2 +
            credit (XMach.act xsys X ⟨todo, .half a b α β⟩).2.1.st +
            8 * (adders (XMach.act xsys X ⟨todo, .half a b α β⟩).1.agents +
              heldAdd (XMach.act xsys X ⟨todo, .half a b α β⟩).2.1.st) + 0 ≤
          1 + owed (XMach.act xsys X ⟨todo, .half a b α β⟩).2.1.st + 4 +
            8 * (adders X.agents + isAdd α) := fun hcond => by
      rw [XMach.act_half_none (xs := xsys) (todo := todo) hcond]
      show 16 * 0 + 0 + 8 * (isAdd α + adders X.agents + 0) + 0 ≤
        1 + 0 + 4 + 8 * (adders X.agents + isAdd α)
      omega
    by_cases hc : assoc b X.agents = some β ∧ a ≠ b
    · cases hR : xsys.rule α β with
      | none => exact fail ((ite_pos' hc).trans hR)
      | some R =>
        rw [XMach.act_half (xs := xsys) (todo := todo) ((ite_pos' hc).trans hR)]
        have ht : adders (X.takeAgent b).agents + isAdd β ≤ adders X.agents := adders_take hc.1
        have hr := rule_cost hR hc.2
        show 16 * 1 + 0 + 8 * (adders (X.takeAgent b).agents + adders (R.newAgents a b)) + 0 ≤
          1 + ((R.newAgents a b).length + (R.newLinks xsys.sys.ar a b α β).length + 1) + 4 +
            8 * (adders X.agents + isAdd α)
        omega
    · exact fail (ite_neg' hc)
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show 16 * 0 + 0 + 8 * (isAdd γ + adders X.agents + adders as) +
          (as.length + 1 + ls.length + 1) ≤
        1 + (as.length + ls.length + 1) + 0 + 8 * (adders X.agents + (isAdd γ + adders as))
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 16 * 0 + 0 + 8 * (adders X.agents + 0) + (0 + (ls.length + 1) + 1) ≤
          1 + (0 + ls.length + 1) + 0 + 8 * (adders X.agents + 0)
        omega
      | nil =>
        show 16 * 0 + 0 + 8 * (adders X.agents + 0) + (0 + 0 + 1) ≤
          1 + 0 + 0 + 8 * (adders X.agents + 0)
        omega

/-- What a thread has put toward a claim, and eight for each adder it
holds. -/
def paid (T : XThread Arith) : Nat := credit T.st + 8 * heldAdd T.st

/-- What a thread still owes for its claim. -/
def due (T : XThread Arith) : Nat := owed T.st

theorem step_cost (M : XMach Arith) (t : Nat) :
    16 * (M.step xsys t).2 +
        (total paid (M.step xsys t).1.ths + 8 * adders (M.step xsys t).1.mem.agents) +
        total due M.ths ≤
      M.stepTally XThread.busy t + total due (M.step xsys t).1.ths +
        (total paid M.ths + 8 * adders M.mem.agents) := by
  cases h : M.ths[t]? with
  | none =>
    have es : M.step xsys t = (M, 0) := by
      unfold XMach.step
      rw [h]
    have e4 : M.stepTally XThread.busy t = 0 := by
      unfold XMach.stepTally
      rw [h]
    rw [es, e4]
    show 16 * 0 + (total paid M.ths + 8 * adders M.mem.agents) + total due M.ths ≤
      0 + total due M.ths + (total paid M.ths + 8 * adders M.mem.agents)
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
    have sp := total_set paid M.ths t T (XMach.act xsys M.mem T).2.1 h
    have sd := total_set due M.ths t T (XMach.act xsys M.mem T).2.1 h
    have ac := act_cost M.mem T
    have p1 : paid T = credit T.st + 8 * heldAdd T.st := rfl
    have p2 : paid (XMach.act xsys M.mem T).2.1 = credit (XMach.act xsys M.mem T).2.1.st +
        8 * heldAdd (XMach.act xsys M.mem T).2.1.st := rfl
    have d1 : due T = owed T.st := rfl
    have d2 : due (XMach.act xsys M.mem T).2.1 = owed (XMach.act xsys M.mem T).2.1.st := rfl
    omega

/-- **The price of a run**: sixteen for each claim, what the threads have
put toward claims, and eight for each adder in memory or held, are never
more than the work done, what the threads still owe, and what was there
at the start. -/
theorem trace_cost (σ : Nat → Nat) (M : XMach Arith) : ∀ i,
    16 * (M.trace xsys σ i).2 +
        (total paid (M.trace xsys σ i).1.ths + 8 * adders (M.trace xsys σ i).1.mem.agents) +
        total due M.ths ≤
      M.work xsys σ i + total due (M.trace xsys σ i).1.ths +
        (total paid M.ths + 8 * adders M.mem.agents)
  | 0 => by
    show 16 * 0 + (total paid M.ths + 8 * adders M.mem.agents) + total due M.ths ≤
      0 + total due M.ths + (total paid M.ths + 8 * adders M.mem.agents)
    omega
  | i + 1 => by
    have ih := trace_cost σ M i
    have hs := step_cost (M.trace xsys σ i).1 (σ i)
    show 16 * ((M.trace xsys σ i).2 + ((M.trace xsys σ i).1.step xsys (σ i)).2) +
        (total paid ((M.trace xsys σ i).1.step xsys (σ i)).1.ths +
          8 * adders ((M.trace xsys σ i).1.step xsys (σ i)).1.mem.agents) + total due M.ths ≤
      M.work xsys σ i + (M.trace xsys σ i).1.stepTally XThread.busy (σ i) +
        total due ((M.trace xsys σ i).1.step xsys (σ i)).1.ths +
        (total paid M.ths + 8 * adders M.mem.agents)
    omega

theorem total_rest (f : XThread Arith → Nat) (hf : f ⟨[], .idle⟩ = 0) :
    ∀ ths : List (XThread Arith), (∀ T, T ∈ ths → T = ⟨[], .idle⟩) → total f ths = 0
  | [], _ => rfl
  | T :: ths, h => by
    show f T + total f ths = 0
    rw [h T List.mem_cons_self, hf,
      total_rest f hf ths (fun U hU => h U (List.mem_cons_of_mem _ hU))]

theorem total_init (f : XThread Arith → Nat) (hf : ∀ l, f ⟨l, .idle⟩ = 0) (X : XNet Arith)
    (nt : Nat) : total f (XMach.init X nt).ths = 0 := by
  have z : total f (XMach.init X nt).ths ≤ (XMach.init X nt).ths.length * 0 :=
    total_le_mul fun T hT => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      rw [hf]
      exact Nat.le_refl 0
  rw [Nat.mul_zero] at z
  omega

/-- **Every interaction costs sixteen actions, less eight for each adder
it ends.**  On any net of the addition, with any number of threads and any
schedule: when every thread is at rest, sixteen times the claims made are
at most the work done and eight for each adder the net had. -/
theorem rest_cost (X : XNet Arith) (nt : Nat) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init X nt).trace xsys σ i).1.resting = true) :
    16 * ((XMach.init X nt).trace xsys σ i).2 ≤
      (XMach.init X nt).work xsys σ i + 8 * adders X.agents := by
  have h := trace_cost σ (XMach.init X nt) i
  have z1 := total_init paid (fun _ => rfl) X nt
  have z2 := total_init due (fun _ => rfl) X nt
  have z3 : total due ((XMach.init X nt).trace xsys σ i).1.ths = 0 :=
    total_rest due rfl _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have e : (XMach.init X nt).mem = X := rfl
  rw [z1, z2, z3, e] at h
  omega

theorem snoc_inj {i j : Id} {c d : Nat} (h : i ++ [c] = j ++ [d]) : i = j ∧ c = d := by
  have h' := List.append_inj' h rfl
  exact ⟨h'.1, by injection h'.2⟩

theorem tagPort_snoc {c d : Nat} {p q : Port} (h : tagPort c p = tagPort d q) : p = q ∧ c = d := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, k'⟩ := q
  have h' : ((i ++ [c], k) : Port) = (j ++ [d], k') := h
  injection h' with h1 h2
  obtain ⟨e1, e2⟩ := snoc_inj h1
  rw [e1, h2]
  exact ⟨rfl, e2⟩

/-- **A net made of tagged parts**: every agent, segment and free port of
`U` is one of a part `P c` with `c` put at the end of its names, and
those of each part are in `U` in this way. -/
structure Parts (U : Net Arith) (P : Nat → Net Arith) : Prop where
  agent : ∀ {i γ}, U.agent i γ → ∃ c i', i = i' ++ [c] ∧ (P c).agent i' γ
  link : ∀ {p q}, U.link p q → ∃ c p' q', p = tagPort c p' ∧ q = tagPort c q' ∧ (P c).link p' q'
  free : ∀ {p}, U.free p → ∃ c p', p = tagPort c p' ∧ (P c).free p'
  agent' : ∀ {c i γ}, (P c).agent i γ → U.agent (i ++ [c]) γ
  link' : ∀ {c p q}, (P c).link p q → U.link (tagPort c p) (tagPort c q)
  free' : ∀ {c p}, (P c).free p → U.free (tagPort c p)

/-- **Parts whose segments match their ends make a net whose segments
match its ends.** -/
theorem Parts.matching {U : Net Arith} {P : Nat → Net Arith} (h : Parts U P)
    (hP : ∀ c, (P c).Matching ar) : U.Matching ar where
  agent_fun := fun h1 h2 => by
    obtain ⟨c, i1, e1, a1⟩ := h.agent h1
    obtain ⟨d, i2, e2, a2⟩ := h.agent h2
    obtain ⟨e3, e4⟩ := snoc_inj (e1.symm.trans e2)
    subst e3
    subst e4
    exact (hP c).agent_fun a1 a2
  symm := fun hl => by
    obtain ⟨c, p', q', e1, e2, l⟩ := h.link hl
    rw [e1, e2]
    exact h.link' ((hP c).symm l)
  irrefl := fun hl => by
    obtain ⟨c, p', q', e1, e2, l⟩ := h.link hl
    have e := (tagPort_snoc (e1.symm.trans e2)).1
    rw [e] at l
    exact (hP c).irrefl l
  functional := fun h1 h2 => by
    obtain ⟨c, p1, q1, e1, e1', l1⟩ := h.link h1
    obtain ⟨d, p2, q2, e2, e2', l2⟩ := h.link h2
    obtain ⟨e3, e4⟩ := tagPort_snoc (e1.symm.trans e2)
    subst e3
    subst e4
    rw [e1', e2', (hP c).functional l1 l2]
  ends := fun hl => by
    obtain ⟨c, p', q', e1, -, l⟩ := h.link hl
    rw [e1]
    rcases (hP c).ends l with hf | ⟨γ, hg, hk⟩
    · exact .inl (h.free' hf)
    · exact .inr ⟨γ, h.agent' hg, hk⟩
  wired := fun {p} he => by
    obtain ⟨i, k⟩ := p
    rcases he with hf | ⟨γ, hg, hk⟩
    · obtain ⟨c, p', e, hf'⟩ := h.free hf
      obtain ⟨q, hl⟩ := (hP c).wired (.inl hf')
      rw [e]
      exact ⟨tagPort c q, h.link' hl⟩
    · obtain ⟨c, i', e, hg'⟩ := h.agent hg
      have e' : i = i' ++ [c] := e
      subst e'
      obtain ⟨q, hl⟩ := (hP c).wired (p := (i', k)) (.inr ⟨γ, hg', hk⟩)
      exact ⟨tagPort c q, h.link' hl⟩
  free_agent := fun {i k α} hf ha => by
    obtain ⟨c, p', e, hf'⟩ := h.free hf
    obtain ⟨d, i', e2, ha'⟩ := h.agent ha
    obtain ⟨j, k'⟩ := p'
    have e' : ((i, k) : Port) = (j ++ [c], k') := e
    injection e' with e3 e4
    obtain ⟨e5, e6⟩ := snoc_inj (e3.symm.trans e2)
    subst e5
    subst e6
    exact (hP c).free_agent hf' ha'
  fresh := fun {a α} l ha hu => by
    obtain ⟨c, a', e, ha'⟩ := h.agent ha
    subst e
    rw [← List.append_assoc] at hu
    rcases hu with ⟨γ, hg⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
    · obtain ⟨d, j', e, hj⟩ := h.agent hg
      obtain ⟨e1, e2⟩ := snoc_inj e
      subst e1
      subst e2
      exact (hP c).fresh l ha' (.inl ⟨γ, hj⟩)
    · obtain ⟨d, p', q', e, -, hl'⟩ := h.link hl
      obtain ⟨j, k'⟩ := p'
      have e' : ((l ++ a' ++ [c], k) : Port) = (j ++ [d], k') := e
      injection e' with e3 e4
      obtain ⟨e1, e2⟩ := snoc_inj e3
      subst e1
      subst e2
      exact (hP c).fresh l ha' (.inr (.inl ⟨k', q', hl'⟩))
    · obtain ⟨d, p', e, hf'⟩ := h.free hf
      obtain ⟨j, k'⟩ := p'
      have e' : ((l ++ a' ++ [c], k) : Port) = (j ++ [d], k') := e
      injection e' with e3 e4
      obtain ⟨e1, e2⟩ := snoc_inj e3
      subst e1
      subst e2
      exact (hP c).fresh l ha' (.inr (.inr ⟨k', hf'⟩))

/-- The net with nothing in it. -/
def noNet : Net Arith := ⟨fun _ _ => False, fun _ _ => False, fun _ => False⟩

theorem noNet_matching : noNet.Matching ar where
  agent_fun := fun h => h.elim
  symm := fun h => h.elim
  irrefl := fun h => h
  functional := fun h => h.elim
  ends := fun h => h.elim
  wired := fun he => by
    rcases he with hf | ⟨γ, hg, -⟩
    · exact hf.elim
    · exact hg.elim
  free_agent := fun h => h.elim
  fresh := fun _ ha => ha.elim

/-- Two parts: the first tagged `0`, the second tagged `1`. -/
def parts2 (A B : Net Arith) (c : Nat) : Net Arith :=
  if c = 0 then A else if c = 1 then B else noNet

theorem parts2_matching {A B : Net Arith} (hA : A.Matching ar) (hB : B.Matching ar) (c : Nat) :
    (parts2 A B c).Matching ar := by
  unfold parts2
  by_cases h0 : c = 0
  · rw [ite_pos' h0]
    exact hA
  · rw [ite_neg' h0]
    by_cases h1 : c = 1
    · rw [ite_pos' h1]
      exact hB
    · rw [ite_neg' h1]
      exact noNet_matching

theorem parts2_cases {A B : Net Arith} {Q : Net Arith → Prop} {c : Nat} (h : Q (parts2 A B c))
    (hn : ¬ Q noNet) : (c = 0 ∧ Q A) ∨ (c = 1 ∧ Q B) := by
  unfold parts2 at h
  by_cases h0 : c = 0
  · rw [ite_pos' h0] at h
    exact .inl ⟨h0, h⟩
  · rw [ite_neg' h0] at h
    by_cases h1 : c = 1
    · rw [ite_pos' h1] at h
      exact .inr ⟨h1, h⟩
    · rw [ite_neg' h1] at h
      exact absurd h hn

/-- Two nets side by side are made of them as parts. -/
theorem parts_beside (XA XB : XNet Arith) :
    Parts (beside (tagNet 0 XA) (tagNet 1 XB)).toNet (parts2 XA.toNet XB.toNet) where
  agent := fun {i γ} h => by
    have h' : (i, γ) ∈ XA.agents.map (tagA 0) ++ XB.agents.map (tagA 1) := h
    rcases List.mem_append.1 h' with h | h
    · obtain ⟨⟨j, δ⟩, he, e⟩ := List.mem_map.1 h
      have e' : ((j ++ [0], δ) : Id × Arith) = (i, γ) := e
      injection e' with e1 e2
      subst e1
      subst e2
      exact ⟨0, j, rfl, he⟩
    · obtain ⟨⟨j, δ⟩, he, e⟩ := List.mem_map.1 h
      have e' : ((j ++ [1], δ) : Id × Arith) = (i, γ) := e
      injection e' with e1 e2
      subst e1
      subst e2
      exact ⟨1, j, rfl, he⟩
  link := fun {p q} h => by
    have h' : (p, q) ∈ XA.wires.map (tagL 0) ++ XB.wires.map (tagL 1) := h
    rcases List.mem_append.1 h' with h | h
    · obtain ⟨⟨p', q'⟩, he, e⟩ := List.mem_map.1 h
      have e' : ((tagPort 0 p', tagPort 0 q') : Port × Port) = (p, q) := e
      injection e' with e1 e2
      exact ⟨0, p', q', e1.symm, e2.symm, he⟩
    · obtain ⟨⟨p', q'⟩, he, e⟩ := List.mem_map.1 h
      have e' : ((tagPort 1 p', tagPort 1 q') : Port × Port) = (p, q) := e
      injection e' with e1 e2
      exact ⟨1, p', q', e1.symm, e2.symm, he⟩
  free := fun {p} h => by
    have h' : p ∈ XA.free.map (tagPort 0) ++ XB.free.map (tagPort 1) := h
    rcases List.mem_append.1 h' with h | h
    · obtain ⟨p', he, e⟩ := List.mem_map.1 h
      exact ⟨0, p', e.symm, he⟩
    · obtain ⟨p', he, e⟩ := List.mem_map.1 h
      exact ⟨1, p', e.symm, he⟩
  agent' := fun {c i γ} h => by
    rcases parts2_cases (Q := fun N => N.agent i γ) h (fun x => x) with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact List.mem_append_left _ (List.mem_map.2 ⟨(i, γ), h, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨(i, γ), h, rfl⟩)
  link' := fun {c p q} h => by
    rcases parts2_cases (Q := fun N => N.link p q) h (fun x => x) with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact List.mem_append_left _ (List.mem_map.2 ⟨(p, q), h, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨(p, q), h, rfl⟩)
  free' := fun {c p} h => by
    rcases parts2_cases (Q := fun N => N.free p) h (fun x => x) with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact List.mem_append_left _ (List.mem_map.2 ⟨p, h, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨p, h, rfl⟩)

/-- **Two well-formed compact nets side by side are a well-formed
net.** -/
theorem beside_wf {XA XB : XNet Arith} (hA : XA.Ok ar) (hB : XB.Ok ar) :
    (beside (tagNet 0 XA) (tagNet 1 XB)).toNet.WF ar :=
  ((parts_beside XA XB).matching
    (parts2_matching (XNet.ok_iff_matching.1 hA) (XNet.ok_iff_matching.1 hB))).wf

theorem two_sums_wf (m n m' n' : Nat) : (twoSums m n m' n').toNet.WF ar :=
  beside_wf (sum_ok m n) (sum_ok m' n')

/-- **Runs that end at rest have made the same number of claims**,
whatever the numbers of threads and the schedules. -/
theorem rest_claims_eq {X : XNet Arith} (hX : X.toNet.WF ar) {nt nt' : Nat} (hnt : 0 < nt)
    (hnt' : 0 < nt') (σ σ' : Nat → Nat) {i j : Nat}
    (h1 : ((XMach.init X nt).trace xsys σ i).1.resting = true)
    (h2 : ((XMach.init X nt').trace xsys σ' j).1.resting = true) :
    ((XMach.init X nt).trace xsys σ i).2 = ((XMach.init X nt').trace xsys σ' j).2 := by
  have L1 := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  have L2 := XMach.trace_live σ' (XMach.init_live (xs := xsys) hX hnt') j
  obtain ⟨q1, n1⟩ := L1.rest h1
  obtain ⟨q2, n2⟩ := L2.rest h2
  have r1 := XMach.trace_run xsys σ (XMach.init X nt) i
  have r2 := XMach.trace_run xsys σ' (XMach.init X nt') j
  rw [XMach.init_toMach] at r1 r2
  exact (MRun.confluent hX r1 r2 q1 q2 n1 n2).2

/-- One thread on two additions side by side, with its claims counted:
`m + 2` for the first addition and `m' + 2` for the second. -/
theorem two_sums_solo_count (m n m' n' : Nat) : ∃ Yf,
    Works xsys (twoSums (m + 1) n (m' + 1) n')
      ⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩ Yf ⟨[], .idle⟩ (m + m' + 4)
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
  have ec : m + 2 + 0 + (m' + 2) + 0 = m + m' + 4 := by omega
  rw [e, ec] at w
  exact ⟨Y2, w⟩

/-- **Any run on two additions that ends at rest has made `m + m' + 4`
claims.** -/
theorem two_sums_claims (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).2 = m + m' + 4 := by
  obtain ⟨Yf, w⟩ := two_sums_solo_count m n m' n'
  have t := w.trace.1
  have h1 : ((XMach.init (twoSums (m + 1) n (m' + 1) n') 1).trace xsys (fun _ => 0)
      (twoSolo (m + 1) n (m' + 1) n')).1.resting = true := by
    rw [XMach.init_one, t]
    rfl
  have e := rest_claims_eq (two_sums_wf (m + 1) n (m' + 1) n') hnt (Nat.succ_pos 0) σ
    (fun _ => 0) hr h1
  rw [e, XMach.init_one, t]

theorem adders_tag (c : Nat) : ∀ l : List (Id × Arith), adders (l.map (tagA c)) = adders l
  | [] => rfl
  | e :: l => by
    show isAdd e.2 + adders (l.map (tagA c)) = isAdd e.2 + adders l
    rw [adders_tag c l]

theorem adders_chainL (n : Nat) : ∀ r, adders (chainL n r) = 0
  | 0 => rfl
  | r + 1 => by
    show isAdd Arith.succ + adders (chainL n r) = 0
    rw [adders_chainL n r]
    rfl

theorem adders_sndL : ∀ n, adders (sndL n) = 0
  | 0 => rfl
  | n + 1 => by
    show isAdd Arith.succ + adders (sndL n) = 0
    rw [adders_sndL n]
    rfl

/-- An addition has one adder. -/
theorem adders_sum (m n : Nat) : adders (sum m n).agents = 1 := by
  rw [sum_agents, adders_append, adders_append, adders_chainL, adders_sndL]
  rfl

theorem adders_two_sums (m n m' n' : Nat) : adders (twoSums m n m' n').agents = 2 := by
  show adders ((sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1)) = 2
  rw [adders_append, adders_tag, adders_tag, adders_sum, adders_sum]

/-- **Two additions side by side cost at least `16 * (m + m' + 3)`
actions**, with any number of threads and any schedule: sixteen for each
interaction with a successor, eight for each of the two with zero.  A
run that ends at rest has done that much work. -/
theorem two_sums_work_ge (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    16 * (m + m' + 3) ≤ (XMach.init (twoSums (m + 1) n (m' + 1) n') nt).work xsys σ i := by
  have h := rest_cost (twoSums (m + 1) n (m' + 1) n') nt σ hr
  rw [two_sums_claims m n m' n' hnt σ hr, adders_two_sums] at h
  omega

/-- So it takes that many actions. -/
theorem two_sums_actions_ge (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    16 * (m + m' + 3) ≤ i :=
  Nat.le_trans (two_sums_work_ge m n m' n' hnt σ hr) (XMach.work_le_count xsys σ _ i)

/-- **What threads can save on two additions.**  With `c` threads in
turn, the rounds to rest times `c` are at least `16 * (m + m' + 3)`. -/
theorem two_sums_rounds_ge (m n m' n' : Nat) {c R : Nat} (hc : 0 < c)
    (h : Rounds c (XMach.init (twoSums (m + 1) n (m' + 1) n') c) R) :
    16 * (m + m' + 3) ≤ c * R :=
  two_sums_actions_ge m n m' n' hc (fun i => i % c) h.1

/-- **Two threads in turn need at least `8 * (m + m' + 3)` rounds on two
additions side by side.** -/
theorem two_threads_two_sums_ge (m n m' n' : Nat) {R : Nat}
    (h : Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2) R) :
    8 * (m + m' + 3) ≤ R := by
  have h' := two_sums_rounds_ge m n m' n' (Nat.succ_pos 1) h
  omega

/-- **Any run on one addition that ends at rest has made `m + 2`
claims.** -/
theorem sum_claims (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sum (m + 1) n) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (sum (m + 1) n) nt).trace xsys σ i).2 = m + 2 := by
  obtain ⟨Xf, run, F⟩ := solo_rounds m n
  have w := run.works.trans (F.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)).works
  have t := w.trace.1
  have h1 : ((XMach.init (sum (m + 1) n) 1).trace xsys (fun _ => 0)
      (17 * m + 25 + (5 * m + 3 * n + 10))).1.resting = true := by
    rw [XMach.init_one, t]
    rfl
  have e := rest_claims_eq (sum_ok (m + 1) n).1 hnt (Nat.succ_pos 0) σ (fun _ => 0) hr h1
  rw [e, XMach.init_one, t]

/-- **One addition costs at least `16 * m + 24` actions**, with any number
of threads and any schedule: sixteen for each of its `m + 1` interactions
with a successor and eight for the one with zero. -/
theorem sum_work_ge (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sum (m + 1) n) nt).trace xsys σ i).1.resting = true) :
    16 * m + 24 ≤ (XMach.init (sum (m + 1) n) nt).work xsys σ i := by
  have h := rest_cost (sum (m + 1) n) nt σ hr
  rw [sum_claims m n hnt σ hr, adders_sum] at h
  omega

/-- With `c` threads in turn, the rounds to rest times `c` are at least
`16 * m + 24`. -/
theorem sum_rounds_ge (m n : Nat) {c R : Nat} (hc : 0 < c)
    (h : Rounds c (XMach.init (sum (m + 1) n) c) R) : 16 * m + 24 ≤ c * R :=
  Nat.le_trans (sum_work_ge m n hc (fun i => i % c) h.1) (XMach.work_le_count xsys _ _ _)

/-- `6 + 10` twice: one thread takes 415 rounds, and two threads cannot
take fewer than 104. -/
theorem _root_.INet.Checks.Arith.TwoSums.c3
    {R : Nat} (h : Rounds 2 (XMach.init (twoSums 6 10 6 10) 2) R) : 104 ≤ R :=
  two_threads_two_sums_ge 5 10 5 10 h

/-- `20 + 30` beside `12 + 40`: one thread takes 1,135 rounds, two threads
at least 264, and four at least 132. -/
theorem _root_.INet.Checks.Arith.TwoSums.c4
    {R : Nat} (h : Rounds 2 (XMach.init (twoSums 20 30 12 40) 2) R) : 264 ≤ R :=
  two_threads_two_sums_ge 19 30 11 40 h

theorem _root_.INet.Checks.Arith.TwoSums.c5
    {R : Nat} (h : Rounds 4 (XMach.init (twoSums 20 30 12 40) 4) R) : 132 ≤ R := by
  have h' := two_sums_rounds_ge 19 30 11 40 (by decide) h
  omega

end Arith

end INet
