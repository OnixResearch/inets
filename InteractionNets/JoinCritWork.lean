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

/-- **With any number of threads, if a thread in a claim keeps the turn,
the actions of threads at work are at most
`nt (7 |agents| + K) + n (C + D + 1 + 9 J) + 7 C n + K + J (4 K log (K + 1) + 6 K)`**,
`K = |wires| + D n`: each thread scans every agent once at the start, then
claims and walks cost what they cost with one thread. -/
theorem JMach.worked_cs {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hcs : ∀ i u U, ((JMach.init X nt).trace xs σ i).1.ths[u]? = some U → U.critical = true →
      σ i = u)
    (i : Nat) :
    JMach.worked xs σ (JMach.init X nt) i ≤
      nt * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
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
  have hA : ∀ i, ((JMach.init X nt).trace xs σ i).1.toW.heads ≤
      X.agents.length + (C - 2) * n := by
    intro i
    have h := (JMach.trace_sizes σ (JMach.init X nt) hb i).2
    rw [JMach.init_toW, WMach.init_heads] at h
    exact Nat.le_trans h (Nat.add_le_add_left (Nat.mul_le_mul_left (C - 2) (bound i)) _)
  have nd : ∀ i, (((JMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact JMach.step_nodup (live i) ih (σ i)
  have ahead : ∀ i, ((JMach.init X nt).trace xs σ i).1.toW.toX.Ahead N' :=
    fun i => XMach.ahead_of_run (M := ((JMach.init X nt).trace xs σ i).1.toW.toX)
      (live i).inv hX (run i) hs hn
  have born := JMach.born_inv hb live ahead
  have hN' := Steps.wf hX hs
  have hH := XNet.normal_sized hX hb hs hn
  generalize hK : X.wires.length + D * n = K at hH
  generalize hAA : X.agents.length + (C - 2) * n = A at hA
  have hR : ∀ i, N'.scan K (JMach.born xs σ (JMach.init X nt) i) ≤ 7 * (C * n) + K := by
    intro i
    obtain ⟨h₁, -, h₃, h₄⟩ := born i
    have := Net.scan_le hH _ h₁ h₃
    have h5 : C * ((JMach.init X nt).trace xs σ i).2 ≤ C * n :=
      Nat.mul_le_mul_left C (bound i)
    omega
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
  -- the measures at the start: each thread scans every agent
  have h0 : (JMach.init X nt).potAll N' K A ≤ nt * (7 * X.agents.length + K) := by
    obtain ⟨-, pr⟩ := Steps.links hX hs
    have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
    have hscan : N'.scan K X.agents ≤ 7 * X.agents.length + K :=
      Net.scan_le hH X.agents hnd fun e he q q' h h' =>
        hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
          (pr (.inl ⟨e.2, hag e he⟩) h')
    have each : ∀ t, potV N' K A (⟨X.agents.drop t ++ X.agents.take t, .idle, false, [], none⟩ :
        JThread S) = N'.scan K X.agents := by
      intro t
      show N'.scan K (X.agents.drop t ++ X.agents.take t) = _
      rw [Net.scan_append]
      have e : N'.scan K X.agents = N'.scan K (X.agents.take t) +
          N'.scan K (X.agents.drop t) := by
        rw [← Net.scan_append, List.take_append_drop]
      rw [e]
      exact Nat.add_comm _ _
    unfold JMach.potAll JMach.init
    rw [List.map_map]
    have hm : ((List.range nt).map ((potV N' K A) ∘ fun t =>
        (⟨X.agents.drop t ++ X.agents.take t, .idle, false, [], none⟩ : JThread S))) =
        (List.range nt).map fun _ => N'.scan K X.agents :=
      List.map_congr_left fun t _ => each t
    rw [hm, sum_map_const, List.length_range]
    exact Nat.mul_le_mul_left _ hscan
  have key : ∀ i, ∃ b, ((JMach.init X nt).trace xs σ i).1.OwesAll N' K b ∧
      JMach.worked xs σ (JMach.init X nt) i + ((JMach.init X nt).trace xs σ i).1.potAll N' K A +
          b + J * payΦ K W l X.toNet ≤
        (JMach.init X nt).potAll N' K A +
          J * payΦ K W l ((JMach.init X nt).trace xs σ i).1.toMach.goal +
          ((JMach.init X nt).trace xs σ i).2 * (C + D + 1 + 9 * J) +
          N'.scan K (JMach.born xs σ (JMach.init X nt) i) := by
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
      · show 0 + (JMach.init X nt).potAll N' K A + 0 + _ ≤ _ +
          J * payΦ K W l (JMach.init X nt).toMach.goal + 0 * (C + D + 1 + 9 * J) + N'.scan K []
        rw [eg]
        have : N'.scan K ([] : List (Id × S)) = 0 := rfl
        omega
    | succ i ih =>
      obtain ⟨b, hb', hle⟩ := ih
      have hsucc : ((JMach.init X nt).trace xs σ (i + 1)) =
          ((((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1,
          ((JMach.init X nt).trace xs σ i).2 +
            (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).2) := rfl
      have hbs : JMach.born xs σ (JMach.init X nt) (i + 1) =
          JMach.born xs σ (JMach.init X nt) i ++
            JMach.stepKids xs ((JMach.init X nt).trace xs σ i).1 (σ i) := rfl
      have hok' := hok (i + 1)
      have hM' := ahead (i + 1)
      rw [hsucc] at hok' hM'
      obtain ⟨b', hb'', hstep⟩ := JMach.cs_total_step hJ (live i)
        (fun u U hU hc => (hcs i u U hU hc).symm) (nd i) hb hH (ahead i) hM' (hA i) hWK
        (hok i) hok' hb'
      refine ⟨b', ?_, ?_⟩
      · rw [hsucc]
        exact hb''
      · show JMach.worked xs σ (JMach.init X nt) i +
            JMach.busyAct ((JMach.init X nt).trace xs σ i).1 (σ i) +
            ((JMach.init X nt).trace xs σ (i + 1)).1.potAll N' K A + b' +
            J * payΦ K W l X.toNet ≤
          (JMach.init X nt).potAll N' K A +
            J * payΦ K W l ((JMach.init X nt).trace xs σ (i + 1)).1.toMach.goal +
            ((JMach.init X nt).trace xs σ (i + 1)).2 * (C + D + 1 + 9 * J) +
            N'.scan K (JMach.born xs σ (JMach.init X nt) (i + 1))
        rw [hbs, Net.scan_append, hsucc]
        dsimp only
        rw [Nat.add_mul]
        omega
  obtain ⟨b, -, hle⟩ := key i
  have := Nat.mul_le_mul_left J hΦ
  have := hR i
  have hc : ((JMach.init X nt).trace xs σ i).2 * (C + D + 1 + 9 * J) ≤
      n * (C + D + 1 + 9 * J) := Nat.mul_le_mul_right _ (bound i)
  omega

/-- **The same bound on the schedule where the first thread in a claim
keeps the turn**, with no hypothesis left. -/
theorem JMach.worked_csSched {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (i : Nat) :
    JMach.worked xs (JMach.csSched xs (JMach.init X nt) nt) (JMach.init X nt) i ≤
      nt * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n)) := by
  refine JMach.worked_cs hJ hX hnd hnt hb hs hn _ (JMach.csSched_hcs xs fun u U hU => ?_) i
  unfold JMach.init at hU
  rw [List.getElem?_map] at hU
  cases hr : (List.range nt)[u]? with
  | none => rw [hr] at hU; cases hU
  | some t =>
    rw [hr] at hU
    cases hU
    rfl

/-! ## All threads at rest -/

theorem JMach.worked_mono (xs : XSys S) (σ : Nat → Nat) (M : JMach S) {j : Nat} :
    ∀ d, JMach.worked xs σ M j ≤ JMach.worked xs σ M (j + d)
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (JMach.worked_mono xs σ M d) (Nat.le_add_right _ _)

theorem JMach.atRest_stays (xs : XSys S) (σ : Nat → Nat) (M : JMach S) {j u : Nat}
    (h : (M.trace xs σ j).1.AtRest u) : ∀ d, (M.trace xs σ (j + d)).1.AtRest u
  | 0 => h
  | d + 1 => by
    obtain ⟨g, js, wk, h'⟩ := JMach.atRest_stays xs σ M h d
    exact ⟨g, js, wk, JMach.step_rest _ _ h'⟩

omit [DecidableEq S] in
theorem JMach.busyAct_zero {M : JMach S} {t : Nat} {T : JThread S} (ht : M.ths[t]? = some T)
    (h : M.busyAct t = 0) : M.AtRest t := by
  unfold JMach.busyAct at h
  rw [ht] at h
  obtain ⟨todo, st, g, js, wk⟩ := T
  dsimp only at h
  cases hto : todo with
  | cons _ _ => rw [hto] at h; simp at h
  | nil =>
    cases st with
    | idle => subst hto; exact ⟨g, js, wk, ht⟩
    | _ => rw [hto] at h; simp [TState.isIdle] at h

omit [DecidableEq S] in
theorem JMach.busyAct_critical {M : JMach S} {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) (hc : T.critical = true) : M.busyAct t = 1 := by
  unfold JMach.busyAct
  rw [ht]
  obtain ⟨todo, st, g, js, wk⟩ := T
  unfold JThread.critical at hc
  dsimp only at hc ⊢
  cases st <;> simp_all [TState.isIdle]

/-- **On the schedule `csSched`, a window of `nt` actions none of which is
at work leaves every thread at rest.** -/
theorem JMach.csSched_window {X : XNet S} {nt : Nat} (hnt : 0 < nt) {j : Nat}
    (h : ∀ m, j ≤ m → m < j + nt →
      JMach.busyAct ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt) m).1
        (JMach.csSched xs (JMach.init X nt) nt m) = 0) :
    ∀ u, u < nt →
      ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt)
        (j + nt)).1.AtRest u := by
  intro u hu
  have hlen : ∀ m, ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt)
      m).1.ths.length = nt := by
    intro m
    rw [JMach.trace_length]
    simp [JMach.init]
  -- the action of the window that falls to `u`
  have hq := Nat.div_add_mod j nt
  have hjm := Nat.mod_lt j hnt
  obtain ⟨m, hm₁, hm₂, hmu⟩ : ∃ m, j ≤ m ∧ m < j + nt ∧ m % nt = u := by
    rcases Nat.lt_or_ge u (j % nt) with h' | h'
    · refine ⟨u + nt * (j / nt + 1), by rw [Nat.mul_add]; omega, by rw [Nat.mul_add]; omega, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
    · refine ⟨u + nt * (j / nt), by omega, by omega, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
  have hb := h m hm₁ hm₂
  -- no thread is in a claim then, so the turn is `m % nt`
  have hpick : JMach.csSched xs (JMach.init X nt) nt m = u := by
    unfold JMach.csSched JMach.csPick
    cases hf : (List.range (JMach.csState xs (JMach.init X nt) nt m).ths.length).find?
        (JMach.csState xs (JMach.init X nt) nt m).critAt with
    | none => exact hmu
    | some u₀ =>
      exfalso
      obtain ⟨U, hU, hc⟩ := JMach.critAt_iff.1 (List.find?_some hf)
      have hσ : JMach.csSched xs (JMach.init X nt) nt m = u₀ := by
        unfold JMach.csSched JMach.csPick
        rw [hf]
        rfl
      rw [← JMach.csState_trace] at hU
      have := JMach.busyAct_critical hU hc
      rw [hσ] at hb
      omega
  rw [hpick] at hb
  have hlt : u < ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt)
      m).1.ths.length := by
    rw [hlen]
    exact hu
  have hrest := JMach.busyAct_zero (List.getElem?_eq_getElem hlt) hb
  have e : j + nt = m + (j + nt - m) := by omega
  rw [e]
  exact JMach.atRest_stays xs _ _ hrest _

/-- **With any number of threads, on the schedule where the first thread in
a claim keeps the turn, all threads are at rest after `nt (B + 1)`
actions**, `B` the bound on the work of `JMach.worked_csSched`. -/
theorem JMach.rests_csSched {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (i : Nat)
    (hi : nt * (nt * (7 * X.agents.length + (X.wires.length + D * n)) +
        n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n)) + 1) ≤ i) :
    ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt) i).1.resting = true := by
  generalize hB : nt * (7 * X.agents.length + (X.wires.length + D * n)) +
      n * (C + D + 1 + 9 * J) +
      7 * (C * n) + (X.wires.length + D * n) +
      J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        6 * (X.wires.length + D * n)) = B at hi
  have hwork : ∀ i,
      JMach.worked xs (JMach.csSched xs (JMach.init X nt) nt) (JMach.init X nt) i ≤ B :=
    fun i => hB ▸ JMach.worked_csSched hJ hX hnd hnt hb hs hn i
  -- some window among the first `B + 1` has no action at work
  have hwin : ∃ k, k ≤ B ∧ ∀ m, k * nt ≤ m → m < k * nt + nt →
      JMach.busyAct ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt) m).1
        (JMach.csSched xs (JMach.init X nt) nt m) = 0 := by
    refine Classical.byContradiction fun hno => ?_
    have grow : ∀ k, k ≤ B + 1 →
        k ≤ JMach.worked xs (JMach.csSched xs (JMach.init X nt) nt) (JMach.init X nt)
          (k * nt) := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        obtain ⟨m, hm₁, hm₂, hm⟩ : ∃ m, k * nt ≤ m ∧ m < k * nt + nt ∧
            JMach.busyAct ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt)
              m).1 (JMach.csSched xs (JMach.init X nt) nt m) ≠ 0 := by
          refine Classical.byContradiction fun hall => hno ⟨k, by omega, fun m h₁ h₂ => ?_⟩
          exact Classical.byContradiction fun hne => hall ⟨m, h₁, h₂, hne⟩
        have step :
            JMach.worked xs (JMach.csSched xs (JMach.init X nt) nt) (JMach.init X nt) (m + 1) =
            JMach.worked xs (JMach.csSched xs (JMach.init X nt) nt) (JMach.init X nt) m +
              JMach.busyAct ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt)
                m).1 (JMach.csSched xs (JMach.init X nt) nt m) := rfl
        have m₁ := JMach.worked_mono xs (JMach.csSched xs (JMach.init X nt) nt) (JMach.init X nt)
          (j := k * nt) (m - k * nt)
        have m₂ := JMach.worked_mono xs (JMach.csSched xs (JMach.init X nt) nt) (JMach.init X nt)
          (j := m + 1) ((k + 1) * nt - (m + 1))
        rw [show k * nt + (m - k * nt) = m by omega] at m₁
        rw [show m + 1 + ((k + 1) * nt - (m + 1)) = (k + 1) * nt by
          rw [Nat.succ_mul]; omega] at m₂
        omega
    have := grow (B + 1) (Nat.le_refl _)
    have := hwork ((B + 1) * nt)
    omega
  obtain ⟨k, hk, hzero⟩ := hwin
  have hall := JMach.csSched_window (xs := xs) (X := X) hnt (j := k * nt) hzero
  -- all at rest at the end of that window, and so at `i`
  have hle : k * nt + nt ≤ i := by
    have : (k + 1) * nt ≤ (B + 1) * nt := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    have : (B + 1) * nt ≤ i := by rw [Nat.mul_comm]; exact hi
    omega
  refine List.all_eq_true.2 fun T hT => ?_
  obtain ⟨u, hu⟩ := List.getElem?_of_mem hT
  have hlen : ((JMach.init X nt).trace xs (JMach.csSched xs (JMach.init X nt) nt)
      i).1.ths.length = nt := by
    rw [JMach.trace_length]
    simp [JMach.init]
  have hlt : u < nt := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.1 hu).1
  obtain ⟨g, js, wk, h⟩ := hall u hlt
  have e : i = k * nt + nt + (i - (k * nt + nt)) := by omega
  obtain ⟨g', js', wk', h'⟩ := JMach.atRest_stays xs _ _ ⟨g, js, wk, h⟩ (i - (k * nt + nt))
  rw [← e, hu] at h'
  rw [Option.some.inj h']
  rfl

end INet
