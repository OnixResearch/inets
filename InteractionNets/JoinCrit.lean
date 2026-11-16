import InteractionNets.JoinMulti

/-! # Several threads, one at a time through a claim

With several threads the walks of `JMach` can cost the square
(`Arith.JoinThreads`): claims run ahead of the walks.  If instead a thread
that has claimed keeps the turn until it has written and walked, from the
state `half` to the end of its writing (`JThread.critical`, a hypothesis on
the schedule), the walks cost what they cost with one thread: a walk then
runs on a memory that holds the goal (`JMach.like_goal_cs`), the goal does
not change between a claim and its walks, and the charge of `JoinMulti`
goes through, whatever the other threads are doing (`JMach.cs_step`).  The
actions of walks of any number of threads are at most
`9 J n + J (4 K log (K + 1) + 6 K)` (`JMach.walked_cs`).
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- The thread is in a claim: it holds an agent, or writes, or walks. -/
def JThread.critical (T : JThread S) : Bool :=
  match T.st with
  | .half _ _ _ _ => true
  | .write _ _ => true
  | _ => false

omit [DecidableEq S] in
/-- **While one thread walks and no other is in a claim, the memory holds
the goal.** -/
theorem JMach.like_goal_cs {M : JMach S} {s : Nat} {T : JThread S} (ht : M.ths[s]? = some T)
    (hs : T.st = .write [] [])
    (hall : ∀ u U, M.ths[u]? = some U → U.critical = true → u = s) :
    M.mem.Like M.toMach.goal := by
  have hth : ∀ t, ¬ (∃ a b α β, M.toMach.th t = .half a b α β) ∧
      ∀ as ls, M.toMach.th t = .write as ls → as = [] ∧ ls = [] := by
    intro t
    show ¬ (∃ a b α β, threadOf ((M.ths.map JThread.toW).map WThread.toX) t = _) ∧
      ∀ as ls, threadOf ((M.ths.map JThread.toW).map WThread.toX) t = _ → _
    cases hu : M.ths[t]? with
    | none =>
      have e : threadOf ((M.ths.map JThread.toW).map WThread.toX) t = .idle := by
        unfold threadOf
        rw [List.getElem?_map, List.getElem?_map, hu]
        rfl
      rw [e]
      refine ⟨?_, fun _ _ h => ?_⟩
      · rintro ⟨_, _, _, _, h⟩
        cases h
      · cases h
    | some U =>
      rw [threadOf_mapJ_eq hu]
      by_cases e : t = s
      · subst e
        rw [ht] at hu
        cases hu
        rw [hs]
        refine ⟨?_, fun as ls h => ?_⟩
        · rintro ⟨_, _, _, _, h⟩
          cases h
        · cases h
          exact ⟨rfl, rfl⟩
      · have hnc : U.critical = false := by
          cases hc : U.critical
          · rfl
          · exact absurd (hall t U hu hc) e
        refine ⟨fun ⟨a, b, α, β, h⟩ => ?_, fun as ls h => ?_⟩
        · unfold JThread.critical at hnc
          rw [h] at hnc
          cases hnc
        · unfold JThread.critical at hnc
          rw [h] at hnc
          cases hnc
  have nA : ∀ t i γ, ¬ (M.toMach.th t).pendA i γ := by
    intro t i γ h
    cases e : M.toMach.th t with
    | write as ls =>
      rw [e] at h
      obtain ⟨rfl, -⟩ := (hth t).2 as ls e
      exact List.not_mem_nil h
    | _ => rw [e] at h; exact h
  have nL : ∀ t p q, ¬ (M.toMach.th t).pendL p q := by
    intro t p q h
    cases e : M.toMach.th t with
    | write as ls =>
      rw [e] at h
      obtain ⟨-, rfl⟩ := (hth t).2 as ls e
      exact List.not_mem_nil h
    | _ => rw [e] at h; exact h
  have nH : ∀ t i γ, ¬ (M.toMach.th t).held i γ := by
    intro t i γ h
    cases e : M.toMach.th t with
    | half a b α β => exact (hth t).1 ⟨a, b, α, β, e⟩
    | _ => rw [e] at h; exact h
  refine ⟨fun i γ => ⟨fun h => .inl (.inl h), fun h => ?_⟩,
    fun p q => ⟨fun h => .inl h, fun h => ?_⟩⟩
  · rcases h with (h | ⟨t, h⟩) | ⟨t, h⟩
    · exact h
    · exact absurd h (nH t i γ)
    · exact absurd h (nA t i γ)
  · rcases h with h | ⟨t, h⟩
    · exact h
    · exact absurd h (nL t p q)

/-- What the threads owe to their walks: each the walk under way, then the
segments it has still to walk. -/
def JMach.OwesAll (H : Net S) (K : Nat) (M : JMach S) (b : Nat) : Prop :=
  ∀ (u : Nat) (T : JThread S), M.ths[u]? = some T →
    (∀ w, T.walk = some w → ∃ c, c ≤ b ∧
      (∃ n v, 1 ≤ n ∧ (JWalk.iter M.mem n w).found = some v ∧ n + pushCost H K v ≤ c) ∧
      JoinsOwe H K M.toMach.goal T.joins (b - c)) ∧
    (T.walk = none → JoinsOwe H K M.toMach.goal T.joins b)

/-- **One action, when the thread that acts is the only one in a claim, if
any is**: the actions of walks it takes and what all threads owe to walks,
with `J` times `payΦ` of the goal, grow at a claim by `9 J` at most, and do
not grow otherwise. -/
theorem JMach.cs_step {J : Nat} (hJ : xs.JoinsAtMost J) {M : JMach S} (hL : M.Live xs)
    {s : Nat} (hall : ∀ u U, M.ths[u]? = some U → U.critical = true → u = s)
    {H : Net S} {K : Nat} (hH : H.Sized K) (hM' : (M.step xs s).1.toW.toX.Ahead H)
    {W : List (Port × Port)} {l : List Id} (hWK : W.length ≤ K)
    (hok : PayOk xs.sys.ar W l M.toMach.goal)
    (hok' : PayOk xs.sys.ar W l (M.step xs s).1.toMach.goal) {b : Nat}
    (hb' : M.OwesAll H K b) :
    ∃ b', (M.step xs s).1.OwesAll H K b' ∧
      M.walkAct s + b' + J * payΦ K W l M.toMach.goal ≤
        b + J * payΦ K W l (M.step xs s).1.toMach.goal + (M.step xs s).2 * (9 * J) := by
  cases ht : M.ths[s]? with
  | none =>
    have e : M.step xs s = (M, 0) := by
      unfold JMach.step
      rw [ht]
    have hw0 : M.walkAct s = 0 := by
      unfold JMach.walkAct
      rw [ht]
    refine ⟨b, ?_, ?_⟩
    · rw [e]
      exact hb'
    · rw [e, hw0]
      dsimp only
      omega
  | some T =>
  obtain ⟨hbw, hbj⟩ := hb' s T ht
  have hlt : s < M.ths.length := (List.getElem?_eq_some_iff.1 ht).1
  have es := JMach.step_eq (X₁ := (JMach.act xs M.mem T).1) (T₁ := (JMach.act xs M.mem T).2.1)
    (c := (JMach.act xs M.mem T).2.2) ht rfl
  have ht' : (M.step xs s).1.ths[s]? = some (JMach.act xs M.mem T).2.1 := by
    rw [es]
    exact List.getElem?_set_self hlt
  have hother : ∀ u, u ≠ s → (M.step xs s).1.ths[u]? = M.ths[u]? := by
    intro u hu
    rw [es]
    exact List.getElem?_set_ne (Ne.symm hu)
  have hm' : (M.step xs s).1.mem = (JMach.act xs M.mem T).1 := by rw [es]
  have hc' : (M.step xs s).2 = (JMach.act xs M.mem T).2.2 := by rw [es]
  have hwa : M.walkAct s = if T.walking then 1 else 0 := by
    unfold JMach.walkAct
    rw [ht]
  -- the other threads owe nothing: they are not in a claim
  have quietU : ∀ u U, u ≠ s → M.ths[u]? = some U → U.joins = [] ∧ U.walk = none := by
    intro u U hu hU
    refine hL.quiet u U hU fun hw => ?_
    have : U.critical = true := by
      unfold JThread.critical
      cases e : U.st <;> rw [e] at hw <;> first | rfl | exact hw.elim
    exact hu (hall u U hU this)
  have mk : ∀ b', ((JMach.act xs M.mem T).2.1.walk = none →
      JoinsOwe H K (M.step xs s).1.toMach.goal (JMach.act xs M.mem T).2.1.joins b') →
      (∀ w, (JMach.act xs M.mem T).2.1.walk = some w → ∃ c, c ≤ b' ∧
        (∃ n v, 1 ≤ n ∧ (JWalk.iter (JMach.act xs M.mem T).1 n w).found = some v ∧
          n + pushCost H K v ≤ c) ∧
        JoinsOwe H K (M.step xs s).1.toMach.goal (JMach.act xs M.mem T).2.1.joins (b' - c)) →
      (M.step xs s).1.OwesAll H K b' := by
    intro b' hj hw u T' hT'
    by_cases hu : u = s
    · subst hu
      rw [ht'] at hT'
      cases hT'
      exact ⟨fun w h => by rw [← hm'] at hw; exact hw w h, hj⟩
    · rw [hother u hu] at hT'
      obtain ⟨hj0, hw0⟩ := quietU u T' hu hT'
      refine ⟨?_, ?_⟩
      · intro w h
        rw [hw0] at h
        cases h
      · intro _
        rw [hj0]
        trivial
  by_cases hw : T.st = .write [] [] ∧ T.again = true
  · have h0 : (M.step xs s).2 = 0 := by
      rcases JMach.act_wr (xs := xs) M.mem T hw.1 hw.2 with ⟨_, _, _, h⟩ |
        ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
    have eg := JMach.goal_of_zero hL h0
    have hlike := JMach.like_goal_cs ht hw.1 hall
    rw [h0, eg, Nat.zero_mul, Nat.add_zero, hwa]
    obtain ⟨todo, st, again, joins, walk⟩ := T
    obtain ⟨hst, hag⟩ := hw
    dsimp only at hst hag
    subst hst hag
    cases walk with
    | some w =>
      have hw1 : JThread.walking ⟨todo, .write [] [], true, joins, some w⟩ = true := rfl
      rw [hw1, ite_pos' rfl]
      obtain ⟨c, hcb, ⟨n, v, hn1, hfn, hnc⟩, hrest⟩ := hbw w rfl
      cases hf : (w.advance M.mem).found with
      | none =>
        have hn2 : 2 ≤ n := by
          rcases Nat.lt_or_ge n 2 with h | h
          · obtain rfl : n = 1 := by omega
            change (w.advance M.mem).found = some v at hfn
            rw [hf] at hfn
            cases hfn
          · exact h
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, joins, some w⟩ =
            (M.mem, ⟨todo, .write [] [], true, joins, some (w.advance M.mem)⟩, 0) := by
          unfold JMach.act
          dsimp only
          rw [hf]
          rfl
        refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), by omega⟩
        rw [hact] at h ⊢
        cases h
        refine ⟨c - 1, by omega, ⟨n - 1, v, by omega, ?_, by omega⟩, ?_⟩
        · have e : JWalk.iter M.mem n w = JWalk.iter M.mem (n - 1) (w.advance M.mem) := by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rfl
          rw [← e]
          exact hfn
        · rw [eg]
          exact hrest.mono (by omega)
      | some v' =>
        have hvv := JWalk.found_eq M.mem hn1 hfn hf
        subst hvv
        have hact := JMach.act_end (xs := xs) M.mem ⟨todo, .write [] [], true, joins, some w⟩ rfl
          rfl rfl hf
        refine ⟨b - c, mk _ (fun _ => ?_) (fun w' h => by rw [hact] at h; cases h), by omega⟩
        rw [hact, eg]
        exact hrest
    | none =>
      cases joins with
      | cons pq js =>
        obtain ⟨p, q⟩ := pq
        have hw1 : JThread.walking ⟨todo, .write [] [], true, (p, q) :: js, none⟩ = true := rfl
        rw [hw1, ite_pos' rfl]
        obtain ⟨c, hcb, hX, hrest⟩ := hbj rfl
        obtain ⟨n, v, hn1, hfn, hnc⟩ := hX M.mem hlike
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, (p, q) :: js, none⟩ =
            (M.mem, ⟨todo, .write [] [], true, js, some (JWalk.start p q)⟩, 0) := rfl
        refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), by omega⟩
        rw [hact] at h ⊢
        cases h
        refine ⟨c - 1, by omega, ⟨n, v, hn1, hfn, by omega⟩, ?_⟩
        rw [eg]
        exact hrest.mono (by omega)
      | nil =>
        have hw1 : JThread.walking ⟨todo, .write [] [], true, [], none⟩ = false := rfl
        rw [hw1]
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, [], none⟩ =
            (M.mem, ⟨todo, .idle, false, [], none⟩, 0) := rfl
        refine ⟨b, mk _ (fun _ => by rw [hact]; trivial)
          (fun w' h => by rw [hact] at h; cases h), by simp⟩
  · -- not walking
    have hwn : T.walk = none := by
      cases hwk : T.walk with
      | none => rfl
      | some w =>
        have hs := hL.wst s T w ht hwk
        cases ha : T.again
        · rw [(hL.nojoin s T ht ha).2] at hwk
          cases hwk
        · exact absurd ⟨hs, ha⟩ hw
    have hw0 : M.walkAct s = 0 := by
      rw [hwa]
      unfold JThread.walking
      rw [hwn]
      simp only [Option.isSome_none, Bool.false_or]
      split
      · rename_i hs
        cases ha : T.again
        · rfl
        · exact absurd ⟨hs, ha⟩ hw
      · rfl
    rw [hw0]
    have hcnt := JMach.act_count_eq (xs := xs) M.mem T
    rcases WMach.act_count (xs := xs) M.mem T.toW with h0 | ⟨a, b₀, α, β, R, hs, hh⟩
    · have h0' : (M.step xs s).2 = 0 := by rw [hc', hcnt, h0]
      have eg := JMach.goal_of_zero hL h0'
      rw [h0', eg, Nat.zero_mul, Nat.add_zero]
      refine ⟨b, ?_, by omega⟩
      rcases (JMach.act_shape (xs := xs) M.mem T hw).2.2.2 with ⟨ej, ew⟩ | ⟨ej, ew⟩ |
        ⟨a, b₀, α, β, R, hs, hh, -, -⟩
      · refine mk _ (fun _ => ?_) (fun w h => by rw [ew, hwn] at h; cases h)
        rw [ej, eg]
        exact hbj hwn
      · exact mk _ (fun _ => by rw [ej]; trivial) (fun w h => by rw [ew] at h; cases h)
      · have h1' := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
        have : (JMach.act xs M.mem T).2.2 = 1 := by rw [h1']
        rw [hcnt, h0] at this
        cases this
    · change T.st = _ at hs
      have hact := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
      obtain ⟨hR, rg, eg⟩ := JMach.claim_goal hL ht hs hh
      have hc1 : (M.step xs s).2 = 1 := by rw [hc', hact]
      rw [hc1, Nat.one_mul, eg]
      rw [eg] at hok'
      have hmono : payΦ K W l M.toMach.goal ≤ payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) :=
        payΦ_mono fun h => .inl h
      have hHG : ∀ {u v}, (M.toMach.goal.fire a b₀ R.toRhs).link u v → H.link u v :=
        fun {u v} h => hM'.link (show (M.step xs s).1.toMach.goal.link u v by rw [eg]; exact h)
      have hpr : ∀ k γ q, (M.toMach.goal.fire a b₀ R.toRhs).agent k γ → H.link (k, 0) q →
          (M.toMach.goal.fire a b₀ R.toRhs).link (k, 0) q := by
        intro k γ q hk hq
        have hu : (M.step xs s).1.toMach.goal.Used k := by
          rw [eg]
          exact .inl ⟨γ, hk⟩
        have := hM'.principal hu hq
        change (M.step xs s).1.toMach.goal.link (k, 0) q at this
        rw [eg] at this
        exact this
      let c₁ := 9 + payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) - payΦ K W l M.toMach.goal
      have hjl := hJ α β R a b₀ hR
      refine ⟨J * c₁, mk _ (fun _ => ?_) (fun w h => by rw [hact] at h; cases h), ?_⟩
      · rw [hact, eg]
        show JoinsOwe H K _ (R.joinPairs xs.sys.ar a b₀ α β) _
        refine JoinsOwe.mono (JoinsOwe.of_each fun pq hm X hX => ?_) (Nat.mul_le_mul_right _ hjl)
        have hJn := joined_fire hok.1 hR rg hm
        obtain ⟨n, v, hn1, hfn, hle'⟩ := walk_pays_found hok'.1 hJn hX
          (fun h => hok'.2.1 _ _ h) hWK hok'.2.2 hH.deg hHG hpr
        have hm2 : payΦ K W l M.toMach.goal ≤ payΦ K W l (M.toMach.goal.fireBut a b₀ R.toRhs pq) :=
          payΦ_mono fun h => .inl h
        exact ⟨n, v, hn1, hfn, by omega⟩
      · have e : J * c₁ + J * payΦ K W l M.toMach.goal =
            J * 9 + J * payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) := by
          rw [← Nat.mul_add, ← Nat.mul_add]
          congr 1
          omega
        omega

/-- **With any number of threads, if a thread that has claimed keeps the
turn until it has written and walked, the walks cost at most
`9 J n + J (4 K log (K + 1) + 6 K)`**, where `n` is the number of steps to
the normal form, `K = |wires| + D n`, and the rules join `J` segments at
most: what one thread costs. -/
theorem JMach.walked_cs {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt) {C D : Nat} (hb : xs.Bounded C D)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N')
    (σ : Nat → Nat)
    (hcs : ∀ i u U, ((JMach.init X nt).trace xs σ i).1.ths[u]? = some U → U.critical = true →
      σ i = u)
    (i : Nat) :
    JMach.walked xs σ (JMach.init X nt) i ≤ n * (9 * J) +
      J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        6 * (X.wires.length + D * n)) := by
  classical
  have live := JMach.trace_live (xs := xs) σ (JMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((JMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((JMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := JMach.trace_run xs σ (JMach.init X nt) i
    rw [JMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((JMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  have ahead : ∀ i, ((JMach.init X nt).trace xs σ i).1.toW.toX.Ahead N' :=
    fun i => XMach.ahead_of_run (M := ((JMach.init X nt).trace xs σ i).1.toW.toX)
      (live i).inv hX (run i) hs hn
  have hN' := Steps.wf hX hs
  have hH := XNet.normal_sized hX hb hs hn
  generalize X.wires.length + D * n = K at hH ⊢
  obtain ⟨W, hWK, hWl⟩ := hH.fin
  let l : List Id := (dedupList (W.map fun e => e.1.1)).filter
    fun k => decide (∀ x y, N'.link (k, 0) x → N'.link (k, 0) y → x = y)
  have hlnd : l.Nodup := (dedupList_nodup _).filter _
  have hok : ∀ j, PayOk xs.sys.ar W l ((JMach.init X nt).trace xs σ j).1.toMach.goal := by
    intro j
    have hG := (live j).inv.wf
    refine ⟨hG, fun u v h => hWl ((ahead j).link h), fun k γ hk => ?_⟩
    have hE : ((JMach.init X nt).trace xs σ j).1.toMach.goal.End xs.sys.ar (k, 0) :=
      .inr ⟨γ, hk, Nat.zero_le _⟩
    obtain ⟨q, hq⟩ := hG.end_wired hE
    refine List.mem_filter.2 ⟨mem_dedupList.2 (List.mem_map.2 ⟨_, hWl ((ahead j).link hq), rfl⟩),
      decide_eq_true fun x y hx hy => ?_⟩
    have hu : ((JMach.init X nt).trace xs σ j).1.toMach.goal.Used k := .inl ⟨γ, hk⟩
    exact hG.end_unique hE ((ahead j).principal hu hx) ((ahead j).principal hu hy)
  have hΦ : payΦ K W l ((JMach.init X nt).trace xs σ i).1.toMach.goal ≤
      4 * (K * Nat.log2 (K + 1)) + 6 * K := by
    have hmono : payΦ K W l ((JMach.init X nt).trace xs σ i).1.toMach.goal ≤
        payΦ K W l N' := payΦ_mono fun h => (ahead i).link h
    have hle := payΦ_le_ends (K := K) hN'.symm hN'.deg (fun h => hWl h) hlnd
      (fun k hk x y hx hy => of_decide_eq_true (List.mem_filter.1 hk).2 x y hx hy)
    have hllen : l.length ≤ W.length :=
      Nat.le_trans (List.length_filter_le _ _)
        (Nat.le_trans (dedupList_length _) (Nat.le_of_eq (List.length_map _)))
    have hmul₁ : W.length * Nat.log2 (K + 1) ≤ K * Nat.log2 (K + 1) := Nat.mul_le_mul_right _ hWK
    omega
  have key : ∀ i, ∃ b, ((JMach.init X nt).trace xs σ i).1.OwesAll N' K b ∧
      JMach.walked xs σ (JMach.init X nt) i + b + J * payΦ K W l X.toNet ≤
        J * payΦ K W l ((JMach.init X nt).trace xs σ i).1.toMach.goal +
          ((JMach.init X nt).trace xs σ i).2 * (9 * J) := by
    intro i
    induction i with
    | zero =>
      have eg : (JMach.init X nt).toMach.goal = X.toNet := by
        rw [JMach.init_toMach X nt]
        exact congrArg CState.goal (Mach.init_quiet X.toNet).abs
      refine ⟨0, fun u T hT => ?_, ?_⟩
      · change (JMach.init X nt).ths[u]? = some T at hT
        unfold JMach.init at hT
        rw [List.getElem?_map] at hT
        cases hr : (List.range nt)[u]? with
        | none => rw [hr] at hT; cases hT
        | some t =>
          rw [hr] at hT
          cases hT
          refine ⟨fun w h => ?_, fun _ => trivial⟩
          cases h
      · show 0 + 0 + _ ≤ J * payΦ K W l (JMach.init X nt).toMach.goal + 0 * (9 * J)
        rw [eg]
        omega
    | succ i ih =>
      obtain ⟨b, hb', hle⟩ := ih
      have hsucc : ((JMach.init X nt).trace xs σ (i + 1)) =
          ((((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1,
          ((JMach.init X nt).trace xs σ i).2 +
            (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).2) := rfl
      have hok' := hok (i + 1)
      have hM' := ahead (i + 1)
      rw [hsucc] at hok' hM'
      obtain ⟨b', hb'', hstep⟩ := JMach.cs_step hJ (live i)
        (fun u U hU hc => (hcs i u U hU hc).symm) hH hM' hWK (hok i) hok' hb'
      refine ⟨b', ?_, ?_⟩
      · rw [hsucc]
        exact hb''
      · show JMach.walked xs σ (JMach.init X nt) i +
            JMach.walkAct ((JMach.init X nt).trace xs σ i).1 (σ i) + b' +
            J * payΦ K W l X.toNet ≤
          J * payΦ K W l ((JMach.init X nt).trace xs σ (i + 1)).1.toMach.goal +
            ((JMach.init X nt).trace xs σ (i + 1)).2 * (9 * J)
        rw [hsucc]
        dsimp only
        rw [Nat.add_mul]
        omega
  obtain ⟨b, -, hle⟩ := key i
  have := Nat.mul_le_mul_left J hΦ
  have hc : ((JMach.init X nt).trace xs σ i).2 * (9 * J) ≤ n * (9 * J) :=
    Nat.mul_le_mul_right _ (bound i)
  omega

end INet
