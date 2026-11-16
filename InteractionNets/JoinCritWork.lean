import InteractionNets.JoinCrit

/-! # Several threads, one at a time through a claim: all the work

`JMach.walked_cs` bounds the walks of any number of threads when a thread
in a claim keeps the turn.  Here the other actions are counted too: the
measure `potV` of each thread goes down at each of its actions outside a
walk except a claim, and no action of another thread changes it.  So the
actions of threads at work, summed over all threads (`JMach.worked`), are at
most what each thread has to scan at the start, `nt (7 |agents| + K)` since
every thread starts with the whole list of agents, plus what claims write
and what walks cost (`JMach.worked_cs`).  Turns given to threads at rest are
not counted: they change nothing.
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- `1` if the thread `t` is at work: it has agents to try or is in an
attempt. -/
def JMach.busyAct (M : JMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => if T.todo.isEmpty && T.st.isIdle then 0 else 1
  | none => 0

/-- The actions of threads at work so far along a run. -/
def JMach.worked (xs : XSys S) (σ : Nat → Nat) (M : JMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => JMach.worked xs σ M i + JMach.busyAct (M.trace xs σ i).1 (σ i)

/-- The sum of the measures of the threads. -/
noncomputable def JMach.potAll (H : Net S) (K A : Nat) (M : JMach S) : Nat :=
  (M.ths.map (potV H K A)).sum

theorem sum_map_set {α : Type} (f : α → Nat) :
    ∀ (l : List α) (i : Nat) (x y : α), l[i]? = some x →
      ((l.set i y).map f).sum + f x = (l.map f).sum + f y
  | [], _, _, _, h => by cases h
  | a :: l, 0, x, y, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
    omega
  | a :: l, i + 1, x, y, h => by
    simp only [List.getElem?_cons_succ] at h
    have := sum_map_set f l i x y h
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
    omega

/-- **One action of a thread, the only one in a claim if any is**: as for
one thread, its measure plus what is owed to walks goes down by one at least
unless it is at rest or claims. -/
theorem JMach.cs_thread_step {J : Nat} (hJ : xs.JoinsAtMost J)
    {M : JMach S} (hL : M.Live xs) {s : Nat}
    (hall : ∀ u U, M.ths[u]? = some U → U.critical = true → u = s)
    {T : JThread S} (ht : M.ths[s]? = some T) (hnd : (M.mem.agents.map Prod.fst).Nodup)
    {C D : Nat} (hb : xs.Bounded C D) {H : Net S} {K A : Nat} (hH : H.Sized K)
    (hM : M.toW.toX.Ahead H) (hM' : (M.step xs s).1.toW.toX.Ahead H) (hA : M.toW.heads ≤ A)
    {W : List (Port × Port)} {l : List Id} (hWK : W.length ≤ K)
    (hok : PayOk xs.sys.ar W l M.toMach.goal)
    (hok' : PayOk xs.sys.ar W l (M.step xs s).1.toMach.goal) {b : Nat}
    (hb' : M.OwesAll H K b) :
    (T.todo = [] ∧ T.st = .idle) ∨
      ∃ b', (M.step xs s).1.OwesAll H K b' ∧
        1 + potV H K A ((JMach.act xs M.mem T).2.1) + b' + J * payΦ K W l M.toMach.goal ≤
          potV H K A T + b + J * payΦ K W l (M.step xs s).1.toMach.goal +
            (M.step xs s).2 * (C + D + 1 + 9 * J) + H.scan K (JMach.stepKids xs M s) := by
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
  have quietU : ∀ u U, u ≠ s → M.ths[u]? = some U → U.joins = [] ∧ U.walk = none := by
    intro u U hu hU
    refine hL.quiet u U hU fun hw => ?_
    have : U.critical = true := by
      unfold JThread.critical
      cases e : U.st <;> rw [e] at hw <;> first | rfl | exact hw.elim
    exact hu (hall u U hU this)
  have hm' : (M.step xs s).1.mem = (JMach.act xs M.mem T).1 := by rw [es]
  have hc' : (M.step xs s).2 = (JMach.act xs M.mem T).2.2 := by rw [es]
  have hk : JMach.stepKids xs M s = WMach.actKids xs M.mem T.toW := by
    unfold JMach.stepKids
    rw [ht]
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
  · refine .inr ?_
    have h0 : (M.step xs s).2 = 0 := by
      rcases JMach.act_wr (xs := xs) M.mem T hw.1 hw.2 with ⟨_, _, _, h⟩ |
        ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
    have eg := JMach.goal_of_zero hL h0
    have hk0 : JMach.stepKids xs M s = [] := by
      rw [hk]
      unfold WMach.actKids
      show (match T.st with
        | .half a b α β =>
          match (if assoc b M.mem.agents = some β ∧ a ≠ b then xs.rule α β else none) with
          | some R => R.newAgents a b
          | none => []
        | _ => []) = []
      rw [hw.1]
    rw [h0, eg, hk0, Nat.zero_mul, Nat.add_zero]
    have hsc : H.scan K ([] : List (Id × S)) = 0 := rfl
    rw [hsc, Nat.add_zero]
    obtain ⟨todo, st, again, joins, walk⟩ := T
    obtain ⟨hst, hag⟩ := hw
    dsimp only at hst hag
    subst hst hag
    have pvT : ∀ (js : List (Port × Port)) (wk : Option (JWalk S)) (todo' : List (Id × S)),
        potV H K A ⟨todo', .write [] [], true, js, wk⟩ = H.scan K todo' + (0 + 0 + 1) :=
      fun _ _ _ => rfl
    cases walk with
    | some w =>
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
        refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), ?_⟩
        · rw [hact] at h ⊢
          cases h
          refine ⟨c - 1, by omega, ⟨n - 1, v, by omega, ?_, by omega⟩, ?_⟩
          · have e : JWalk.iter M.mem n w = JWalk.iter M.mem (n - 1) (w.advance M.mem) := by
              obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              rfl
            rw [← e]
            exact hfn
          · rw [eg]
            exact hrest.mono (by omega)
        · rw [hact, pvT, pvT]
          omega
      | some v' =>
        have hvv := JWalk.found_eq M.mem hn1 hfn hf
        subst hvv
        have hact := JMach.act_end (xs := xs) M.mem ⟨todo, .write [] [], true, joins, some w⟩ rfl
          rfl rfl hf
        refine ⟨b - c, mk _ (fun _ => ?_) (fun w' h => by rw [hact] at h; cases h), ?_⟩
        · rw [hact, eg]
          exact hrest
        · rw [hact, pvT, pvT, scan_foundList]
          dsimp only
          omega
    | none =>
      cases joins with
      | cons pq js =>
        obtain ⟨p, q⟩ := pq
        obtain ⟨c, hcb, hX, hrest⟩ := hbj rfl
        obtain ⟨n, v, hn1, hfn, hnc⟩ := hX M.mem (JMach.like_goal_cs ht rfl hall)
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, (p, q) :: js, none⟩ =
            (M.mem, ⟨todo, .write [] [], true, js, some (JWalk.start p q)⟩, 0) := rfl
        refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), ?_⟩
        · rw [hact] at h ⊢
          cases h
          refine ⟨c - 1, by omega, ⟨n, v, hn1, hfn, by omega⟩, ?_⟩
          rw [eg]
          exact hrest.mono (by omega)
        · rw [hact, pvT, pvT]
          omega
      | nil =>
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, [], none⟩ =
            (M.mem, ⟨todo, .idle, false, [], none⟩, 0) := rfl
        refine ⟨b, mk _ (fun _ => by rw [hact]; trivial)
          (fun w' h => by rw [hact] at h; cases h), ?_⟩
        rw [hact, pvT]
        show 1 + H.scan K todo + b + _ ≤ _
        omega
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
    have hcnt := JMach.act_count_eq (xs := xs) M.mem T
    rcases JMach.act_potV hL hnd hb hH hM hA ht hw with ⟨-, hto, hst⟩ | ⟨h1c, hle⟩ | ⟨h0, hlt⟩
    · exact .inl ⟨hto, hst⟩
    · -- a claim
      refine .inr ?_
      rcases WMach.act_count (xs := xs) M.mem T.toW with h0 | ⟨a, b₀, α, β, R, hs, hh⟩
      · rw [hcnt, h0] at h1c
        cases h1c
      change T.st = _ at hs
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
      · rw [hk]
        have e : J * c₁ + J * payΦ K W l M.toMach.goal =
            J * 9 + J * payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) := by
          rw [← Nat.mul_add, ← Nat.mul_add]
          congr 1
          omega
        omega
    · -- a step that lowers the measure, without a claim
      refine .inr ?_
      have h0' : (M.step xs s).2 = 0 := by rw [hc', h0]
      have eg := JMach.goal_of_zero hL h0'
      rw [h0', eg, Nat.zero_mul, Nat.add_zero]
      refine ⟨b, ?_, by omega⟩
      have hw' : ¬ (T.st = .write [] [] ∧ T.again = true) := hw
      rcases (JMach.act_shape (xs := xs) M.mem T hw').2.2.2 with ⟨ej, ew⟩ | ⟨ej, ew⟩ |
        ⟨a, b₀, α, β, R, hs, hh, -, -⟩
      · refine mk _ (fun _ => ?_) (fun w h => by rw [ew, hwn] at h; cases h)
        rw [ej, eg]
        exact hbj hwn
      · exact mk _ (fun _ => by rw [ej]; trivial) (fun w h => by rw [ew] at h; cases h)
      · have h1' := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
        rw [hcnt] at h0
        have : (JMach.act xs M.mem T).2.2 = 1 := by rw [h1']
        rw [hcnt] at this
        rw [h0] at this
        cases this

/-- **One action of the run, when the thread that acts is the only one in a
claim, if any is**: the actions at work, the sum of the measures of the
threads and what they owe to walks, with `J` times `payΦ` of the goal, go
down at each action at work, but for what a claim adds. -/
theorem JMach.cs_total_step {J : Nat} (hJ : xs.JoinsAtMost J) {M : JMach S} (hL : M.Live xs)
    {s : Nat} (hall : ∀ u U, M.ths[u]? = some U → U.critical = true → u = s)
    (hnd : (M.mem.agents.map Prod.fst).Nodup)
    {C D : Nat} (hb : xs.Bounded C D) {H : Net S} {K A : Nat} (hH : H.Sized K)
    (hM : M.toW.toX.Ahead H) (hM' : (M.step xs s).1.toW.toX.Ahead H) (hA : M.toW.heads ≤ A)
    {W : List (Port × Port)} {l : List Id} (hWK : W.length ≤ K)
    (hok : PayOk xs.sys.ar W l M.toMach.goal)
    (hok' : PayOk xs.sys.ar W l (M.step xs s).1.toMach.goal) {b : Nat}
    (hb' : M.OwesAll H K b) :
    ∃ b', (M.step xs s).1.OwesAll H K b' ∧
      M.busyAct s + (M.step xs s).1.potAll H K A + b' + J * payΦ K W l M.toMach.goal ≤
        M.potAll H K A + b + J * payΦ K W l (M.step xs s).1.toMach.goal +
          (M.step xs s).2 * (C + D + 1 + 9 * J) + H.scan K (JMach.stepKids xs M s) := by
  cases ht : M.ths[s]? with
  | none =>
    have e : M.step xs s = (M, 0) := by
      unfold JMach.step
      rw [ht]
    have hw0 : M.busyAct s = 0 := by
      unfold JMach.busyAct
      rw [ht]
    refine ⟨b, ?_, ?_⟩
    · rw [e]
      exact hb'
    · rw [e, hw0]
      dsimp only
      omega
  | some T =>
    have es := JMach.step_eq (X₁ := (JMach.act xs M.mem T).1) (T₁ := (JMach.act xs M.mem T).2.1)
      (c := (JMach.act xs M.mem T).2.2) ht rfl
    have hsum : (M.step xs s).1.potAll H K A + potV H K A T =
        M.potAll H K A + potV H K A (JMach.act xs M.mem T).2.1 := by
      unfold JMach.potAll
      rw [es]
      exact sum_map_set (potV H K A) M.ths s T _ ht
    rcases JMach.cs_thread_step hJ hL hall ht hnd hb hH hM hM' hA hWK hok hok' hb' with
      ⟨hto, hst⟩ | ⟨b', hb'', hle⟩
    · -- at rest: nothing changes
      obtain ⟨todo, st, g, js, wk⟩ := T
      dsimp only at hto hst
      subst hto hst
      have hact := JMach.rest_act (xs := xs) M.mem g js wk
      have e : M.step xs s = (M, 0) := by
        rw [JMach.step_eq ht hact, set_self M.ths s _ ht]
      have hw0 : M.busyAct s = 0 := by
        unfold JMach.busyAct
        rw [ht]
        rfl
      refine ⟨b, ?_, ?_⟩
      · rw [e]
        exact hb'
      · rw [e, hw0]
        dsimp only
        omega
    · have hw1 : M.busyAct s ≤ 1 := by
        unfold JMach.busyAct
        rw [ht]
        dsimp only
        cases (T.todo.isEmpty && T.st.isIdle) <;> simp
      exact ⟨b', hb'', by omega⟩

end INet
