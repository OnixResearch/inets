import InteractionNets.JoinBound
import InteractionNets.WireFar

/-! # Paying for the walks of one thread

`JoinBound` charges every walk of `JMach` the most a walk can cost, so its
bound grows like the number of claims times the size of the net, while the
walks measured in `MeasureJoin` cost `O(n log n)` in all.  This file reduces
a bound of that kind, for one thread, to a statement about one claim at a
time.

Let `Φ` measure nets.  Say a system *pays its walks* (`XSys.WalkPaid`) with
`c₀` per claim when, at every claim of a goal `G` that satisfies a property
`P`, the measure does not drop by more than `c₀`, and, when the rule joins a
segment `(p, q)`, the walk of that segment, on any memory holding the net
after the rule, finds what it finds within `n` advances, `n + 1` being paid
by `c₀` and the growth of the measure.  Then, along a run of one thread of
a system whose rules join one segment at most (`XSys.OneJoin`), the actions
of walks (starting one or advancing one, as `jStats` counts them) are at
most `c₀` per claim plus the growth of the measure from the first goal
(`JMach.walked_le`).

What remains to prove an `n log n` bound is the payment itself for a
measure such as the sum of the logarithms of the longest trails.
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- The walk the program starts on the joined segment from `p` to `q`. -/
def JWalk.start (p q : Port) : JWalk S := ⟨p, q, .go q p, .go p q, true⟩

/-- `n` steps of a walk on the memory `X`. -/
def JWalk.iter (X : XNet S) : Nat → JWalk S → JWalk S
  | 0, w => w
  | n + 1, w => JWalk.iter X n (w.advance X)

/-- The memory holds a net with the agents and segments of `G`. -/
def XNet.Like (X : XNet S) (G : Net S) : Prop :=
  (∀ i γ, (i, γ) ∈ X.agents ↔ G.agent i γ) ∧ ∀ p q, (p, q) ∈ X.wires ↔ G.link p q

/-- The action of the thread is part of a walk: it starts one or advances
one. -/
def JThread.walking (T : JThread S) : Bool :=
  T.walk.isSome ||
    (match T.st with
     | .write [] [] => T.again && !T.joins.isEmpty
     | _ => false)

/-- The actions of walks that thread `t` would take: one or none. -/
def JMach.walkAct (M : JMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => if T.walking then 1 else 0
  | none => 0

/-- The actions of walks so far along a run. -/
def JMach.walked (xs : XSys S) (σ : Nat → Nat) (M : JMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => JMach.walked xs σ M i + JMach.walkAct (M.trace xs σ i).1 (σ i)

/-- Every rule joins one segment at most. -/
def XSys.OneJoin (xs : XSys S) : Prop :=
  ∀ α β R a b, xs.rule α β = some R → (R.joinPairs xs.sys.ar a b α β).length ≤ 1

/-- **The system pays its walks** with the measure `Φ` and `c₀` per claim,
at goals with the property `P`, before and after the claim: a claim does not
lower the measure by more than `c₀`, and the walk of the segment a rule
joins finds what it finds within `n` advances, on any memory holding the
net after the rule, where `n + 1` is paid by `c₀` and the growth of the
measure. -/
def XSys.WalkPaid (xs : XSys S) (Φ : Net S → Nat) (c₀ : Nat) (P : Net S → Prop) : Prop :=
  ∀ (G : Net S) (a b : Id) (α β : S) (R : XRhs S), P G → P (G.fire a b R.toRhs) →
    xs.rule α β = some R → Redex xs.sys G a b α β R.toRhs →
    Φ G ≤ c₀ + Φ (G.fire a b R.toRhs) ∧
    ∀ p q, R.joinPairs xs.sys.ar a b α β = [(p, q)] → ∀ X : XNet S, X.Like (G.fire a b R.toRhs) →
      ∃ n, 1 ≤ n ∧ n + 1 + Φ G ≤ c₀ + Φ (G.fire a b R.toRhs) ∧
        (JWalk.iter X n (JWalk.start p q)).found ≠ none

/-- What the only thread still owes to its walks, at most `b` actions: the
walk under way finds what it finds within `b` advances, and the segment
still to walk is walked, once started on a memory holding the goal, within
`b - 1`. -/
def JMach.Owes (M : JMach S) (b : Nat) : Prop :=
  ∀ T, M.ths[0]? = some T →
    (∀ w, T.walk = some w → T.joins = [] ∧
      ∃ n, 1 ≤ n ∧ n ≤ b ∧ (JWalk.iter M.mem n w).found ≠ none) ∧
    (T.walk = none → ∀ p q js, T.joins = (p, q) :: js → js = [] ∧
      ∀ X : XNet S, X.Like M.toMach.goal →
        ∃ n, 1 ≤ n ∧ n + 1 ≤ b ∧ (JWalk.iter X n (JWalk.start p q)).found ≠ none)

omit [DecidableEq S] in
/-- With one thread that has everything written, the memory holds the
goal. -/
theorem JMach.like_goal {M : JMach S} {T : JThread S} (h1 : M.ths = [T])
    (hs : T.st = .write [] []) : M.mem.Like M.toMach.goal := by
  have hth : ∀ t, M.toMach.th t = .idle ∨ M.toMach.th t = .write [] [] := by
    intro t
    show threadOf ((M.ths.map JThread.toW).map WThread.toX) t = _ ∨
      threadOf ((M.ths.map JThread.toW).map WThread.toX) t = _
    rw [h1]
    unfold threadOf
    rcases t with _ | t
    · exact .inr hs
    · exact .inl rfl
  have nA : ∀ t i γ, ¬ (M.toMach.th t).pendA i γ := by
    intro t i γ h
    rcases hth t with e | e <;> rw [e] at h
    · exact h
    · exact List.not_mem_nil h
  have nL : ∀ t p q, ¬ (M.toMach.th t).pendL p q := by
    intro t p q h
    rcases hth t with e | e <;> rw [e] at h
    · exact h
    · exact List.not_mem_nil h
  have nH : ∀ t i γ, ¬ (M.toMach.th t).held i γ := by
    intro t i γ h
    rcases hth t with e | e <;> rw [e] at h <;> exact h
  refine ⟨fun i γ => ⟨fun h => .inl (.inl h), fun h => ?_⟩,
    fun p q => ⟨fun h => .inl h, fun h => ?_⟩⟩
  · rcases h with (h | ⟨t, h⟩) | ⟨t, h⟩
    · exact h
    · exact absurd h (nH t i γ)
    · exact absurd h (nA t i γ)
  · rcases h with h | ⟨t, h⟩
    · exact h
    · exact absurd h (nL t p q)

/-- A claim, read off the state of the thread that makes it. -/
theorem JMach.claim_goal {M : JMach S} (hL : M.Live xs) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) {a b : Id} {α β : S} {R : XRhs S} (hs : T.st = .half a b α β)
    (hh : (if assoc b M.mem.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    xs.rule α β = some R ∧ Redex xs.sys M.toMach.goal a b α β R.toRhs ∧
      (M.step xs t).1.toMach.goal = M.toMach.goal.fire a b R.toRhs := by
  have hact := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
  have hc : assoc b M.mem.agents = some β ∧ a ≠ b := by
    split at hh
    · rename_i hc
      exact hc
    · cases hh
  have hR : xs.rule α β = some R := by
    rw [ite_pos' hc] at hh
    exact hh
  obtain ⟨hsys, hw⟩ := xs.writes hc.2 hR
  have e : M.toMach.th t = .half a b α β := by
    rw [← hs]
    exact threadOf_mapJ_eq ht
  obtain ⟨rg, eg⟩ := hL.inv.cas₂_goal e (assoc_mem hc.1) hc.2 hsys hw
  have es' := JMach.step_eq ht hact
  have hmx : ((M.ths.map JThread.toW).map WThread.toX)[t]? = some T.toW.toX := by
    rw [List.getElem?_map, List.getElem?_map, ht]
    rfl
  refine ⟨hR, rg, ?_⟩
  rw [es']
  show Mach.goal ⟨(M.mem.takeAgent b).toNet,
    threadOf (((M.ths.set t _).map JThread.toW).map WThread.toX)⟩ = _
  rw [List.map_set, List.map_set, threadOf_set hmx, XNet.takeAgent_toNet]
  exact eg

/-- An action that makes no claim leaves the goal as it is. -/
theorem JMach.goal_of_zero {M : JMach S} (hL : M.Live xs) {t : Nat}
    (h0 : (M.step xs t).2 = 0) : (M.step xs t).1.toMach.goal = M.toMach.goal := by
  rcases JMach.step_goal hL t with ⟨-, eg, -⟩ | ⟨_, _, _, _, _, _, h1, -⟩
  · exact eg
  · rw [h1] at h0
    cases h0

/-- The actions of a thread with everything written and a rule that joined
segments: it starts a walk, advances one, or is done. -/
theorem JMach.act_wr (X : XNet S) (T : JThread S) (hs : T.st = .write [] [])
    (ha : T.again = true) :
    (∃ w, T.walk = some w ∧ (JWalk.advance X w).found = none ∧
      JMach.act xs X T = (X, ⟨T.todo, T.st, true, T.joins, some (JWalk.advance X w)⟩, 0)) ∨
    (∃ w, T.walk = some w ∧ (JWalk.advance X w).found ≠ none ∧
      (JMach.act xs X T).1 = X ∧ (JMach.act xs X T).2.1.joins = T.joins ∧
      (JMach.act xs X T).2.1.walk = none ∧ (JMach.act xs X T).2.2 = 0) ∨
    (∃ p q js, T.walk = none ∧ T.joins = (p, q) :: js ∧
      JMach.act xs X T = (X, ⟨T.todo, T.st, true, js, some (JWalk.start p q)⟩, 0)) ∨
    (T.walk = none ∧ T.joins = [] ∧
      JMach.act xs X T = (X, ⟨T.todo, .idle, false, [], none⟩, 0)) := by
  obtain ⟨todo, st, again, joins, walk⟩ := T
  dsimp only at hs ha
  subst hs ha
  cases walk with
  | some w =>
    cases hf : (w.advance X).found with
    | none =>
      refine .inl ⟨w, rfl, hf, ?_⟩
      unfold JMach.act
      simp only [hf]
      exact ite_pos' trivial
    | some e =>
      refine .inr (.inl ⟨w, rfl, by rw [hf]; exact Option.some_ne_none _, ?_⟩)
      unfold JMach.act
      cases e with
      | none => simp only [hf]; exact ⟨rfl, rfl, rfl, rfl⟩
      | some e => simp only [hf]; exact ⟨rfl, rfl, rfl, rfl⟩
  | none =>
    cases joins with
    | cons pq js =>
      obtain ⟨p, q⟩ := pq
      refine .inr (.inr (.inl ⟨p, q, js, rfl, rfl, ?_⟩))
      unfold JMach.act
      rfl
    | nil =>
      refine .inr (.inr (.inr ⟨rfl, rfl, ?_⟩))
      unfold JMach.act
      rfl

omit [DecidableEq S] in
theorem JMach.walkAct_eq {M : JMach S} {T : JThread S} (ht : M.ths[0]? = some T) :
    M.walkAct 0 = if T.walking then 1 else 0 := by
  unfold JMach.walkAct
  rw [ht]

/-- **One action of the only thread pays for its part of a walk**: what it
owes drops by the actions of walks it takes, and grows at a claim by `c₀`
and the growth of the measure. -/
theorem JMach.owes_step {Φ : Net S → Nat} {c₀ : Nat} {P : Net S → Prop} (hJ : xs.OneJoin)
    (hpay : xs.WalkPaid Φ c₀ P) {M : JMach S} (hL : M.Live xs) {T : JThread S}
    (h1 : M.ths = [T]) (hP : P M.toMach.goal) (hP' : P (M.step xs 0).1.toMach.goal) {b : Nat}
    (hb : M.Owes b) :
    ∃ b', (M.step xs 0).1.Owes b' ∧
      M.walkAct 0 + b' + Φ M.toMach.goal ≤
        b + c₀ * (M.step xs 0).2 + Φ (M.step xs 0).1.toMach.goal := by
  have ht : M.ths[0]? = some T := by rw [h1]; rfl
  obtain ⟨hbw, hbj⟩ := hb T ht
  have es := JMach.step_eq (X₁ := (JMach.act xs M.mem T).1) (T₁ := (JMach.act xs M.mem T).2.1)
    (c := (JMach.act xs M.mem T).2.2) ht rfl
  have hset : M.ths.set 0 (JMach.act xs M.mem T).2.1 = [(JMach.act xs M.mem T).2.1] := by
    rw [h1]; rfl
  rw [hset] at es
  have ht' : (M.step xs 0).1.ths[0]? = some (JMach.act xs M.mem T).2.1 := by rw [es]; rfl
  have hm' : (M.step xs 0).1.mem = (JMach.act xs M.mem T).1 := by rw [es]
  have hc' : (M.step xs 0).2 = (JMach.act xs M.mem T).2.2 := by rw [es]
  have hwa := JMach.walkAct_eq (M := M) ht
  -- the owing of the new state, from the new thread
  have mk : ∀ b', ((JMach.act xs M.mem T).2.1.walk = none →
      ∀ p q js, (JMach.act xs M.mem T).2.1.joins = (p, q) :: js → js = [] ∧
        ∀ X : XNet S, X.Like (M.step xs 0).1.toMach.goal →
          ∃ n, 1 ≤ n ∧ n + 1 ≤ b' ∧ (JWalk.iter X n (JWalk.start p q)).found ≠ none) →
      (∀ w, (JMach.act xs M.mem T).2.1.walk = some w → (JMach.act xs M.mem T).2.1.joins = [] ∧
        ∃ n, 1 ≤ n ∧ n ≤ b' ∧ (JWalk.iter (JMach.act xs M.mem T).1 n w).found ≠ none) →
      (M.step xs 0).1.Owes b' := by
    intro b' hj hw T' hT'
    rw [ht'] at hT'
    cases hT'
    exact ⟨fun w h => by rw [← hm'] at hw; exact hw w h, hj⟩
  by_cases hw : T.st = .write [] [] ∧ T.again = true
  · have h0 : (M.step xs 0).2 = 0 := by
      rcases JMach.act_wr (xs := xs) M.mem T hw.1 hw.2 with ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
    have eg := JMach.goal_of_zero hL h0
    rw [h0, eg, Nat.mul_zero, Nat.add_zero]
    rcases JMach.act_wr (xs := xs) M.mem T hw.1 hw.2 with ⟨w, hwk, hf, hact⟩ |
      ⟨w, hwk, hf, e1, ej, ew, -⟩ | ⟨p, q, js, hwk, hj, hact⟩ | ⟨hwk, hj, hact⟩
    · obtain ⟨hjn, n, hn1, hnb, hfn⟩ := hbw w hwk
      have hn2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · obtain rfl : n = 1 := by omega
          exact absurd hf hfn
        · exact h
      have hw1 : M.walkAct 0 = 1 := by
        rw [hwa]
        simp [JThread.walking, hwk]
      refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), by omega⟩
      rw [hact] at h ⊢
      cases h
      refine ⟨hjn, n - 1, by omega, by omega, ?_⟩
      have e : n = (n - 1) + 1 := by omega
      rw [e] at hfn
      exact hfn
    · obtain ⟨hjn, n, hn1, hnb, -⟩ := hbw w hwk
      have hw1 : M.walkAct 0 = 1 := by
        rw [hwa]
        simp [JThread.walking, hwk]
      refine ⟨b - 1, mk _ (fun _ p q js h => by rw [ej, hjn] at h; cases h)
        (fun w' h => by rw [ew] at h; cases h), by omega⟩
    · obtain ⟨hjs, hX⟩ := hbj hwk p q js hj
      obtain ⟨n, hn1, hnb, hfn⟩ := hX M.mem (JMach.like_goal h1 hw.1)
      have hw1 : M.walkAct 0 = 1 := by
        rw [hwa]
        simp [JThread.walking, hwk, hw.1, hw.2, hj]
      refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), by omega⟩
      rw [hact] at h ⊢
      cases h
      exact ⟨hjs, n, hn1, by omega, hfn⟩
    · have hw0 : M.walkAct 0 = 0 := by
        rw [hwa]
        simp [JThread.walking, hwk, hw.1, hj]
      refine ⟨b, mk _ (fun _ p q js h => by rw [hact] at h; cases h)
        (fun w' h => by rw [hact] at h; cases h), by omega⟩
  · -- not walking: no walk under way, and nothing to start
    have hwn : T.walk = none := by
      cases hwk : T.walk with
      | none => rfl
      | some w =>
        have hs := hL.wst 0 T w ht hwk
        cases ha : T.again
        · rw [(hL.nojoin 0 T ht ha).2] at hwk
          cases hwk
        · exact absurd ⟨hs, ha⟩ hw
    have hw0 : M.walkAct 0 = 0 := by
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
    have hcnt := JMach.act_count_eq (xs := xs) M.mem T
    rcases WMach.act_count (xs := xs) M.mem T.toW with h0 | ⟨a, b₀, α, β, R, hs, hh⟩
    · have h0' : (M.step xs 0).2 = 0 := by rw [hc', hcnt, h0]
      have eg := JMach.goal_of_zero hL h0'
      rw [h0', eg, Nat.mul_zero, Nat.add_zero, hw0]
      refine ⟨b, ?_, by omega⟩
      rcases (JMach.act_shape (xs := xs) M.mem T hw).2.2.2 with ⟨ej, ew⟩ | ⟨ej, ew⟩ |
        ⟨a, b₀, α, β, R, hs, hh, -, -⟩
      · refine mk _ (fun h p q js hj => ?_) (fun w h => by rw [ew, hwn] at h; cases h)
        rw [ej] at hj
        rw [eg]
        exact hbj hwn p q js hj
      · exact mk _ (fun _ p q js h => by rw [ej] at h; cases h)
          (fun w h => by rw [ew] at h; cases h)
      · have h1' := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
        rw [h1'] at hcnt
        rw [h0] at hcnt
        cases hcnt
    · change T.st = _ at hs
      have hact := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
      obtain ⟨hR, rg, eg⟩ := JMach.claim_goal hL ht hs hh
      obtain ⟨hmono, hjp⟩ := hpay _ a b₀ α β R hP (eg ▸ hP') hR rg
      have h1' : (M.step xs 0).2 = 1 := by rw [hc', hact]
      rw [h1', eg, hw0, Nat.mul_one]
      refine ⟨c₀ + Φ (M.toMach.goal.fire a b₀ R.toRhs) - Φ M.toMach.goal,
        mk _ (fun _ p q js hj => ?_) (fun w h => by rw [hact] at h; cases h), by omega⟩
      rw [hact] at hj
      have hl := hJ α β R a b₀ hR
      change R.joinPairs xs.sys.ar a b₀ α β = (p, q) :: js at hj
      rw [hj] at hl
      have hjs : js = [] := by
        cases js with
        | nil => rfl
        | cons _ _ => simp at hl
      subst hjs
      refine ⟨rfl, fun X hX => ?_⟩
      rw [eg] at hX
      obtain ⟨n, hn1, hn, hfn⟩ := hjp p q hj X hX
      exact ⟨n, hn1, by omega, hfn⟩

omit [DecidableEq S] in
theorem JMach.one_thread {M : JMach S} (h : M.ths.length = 1) : ∃ T, M.ths = [T] := by
  match e : M.ths, h with
  | [T], _ => exact ⟨T, rfl⟩

/-- **The actions of walks along a run of one thread are paid by `c₀` per
claim and the growth of the measure**, when every rule joins one segment at
most and the system pays its walks at the goals of the run. -/
theorem JMach.walked_le {Φ : Net S → Nat} {c₀ : Nat} {P : Net S → Prop} (hJ : xs.OneJoin)
    (hpay : xs.WalkPaid Φ c₀ P) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    {i : Nat} (hP : ∀ j, j ≤ i → P ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal) :
    JMach.walked xs (fun _ => 0) (JMach.init X 1) i + Φ X.toNet ≤
      c₀ * ((JMach.init X 1).trace xs (fun _ => 0) i).2 +
        Φ ((JMach.init X 1).trace xs (fun _ => 0) i).1.toMach.goal := by
  have live := JMach.trace_live (xs := xs) (fun _ => 0) (JMach.init_live hX Nat.one_pos)
  have eg : (JMach.init X 1).toMach.goal = X.toNet := by
    rw [JMach.init_toMach X 1]
    exact congrArg CState.goal (Mach.init_quiet X.toNet).abs
  have key : ∀ k, k ≤ i → ∃ b, ((JMach.init X 1).trace xs (fun _ => 0) k).1.Owes b ∧
      JMach.walked xs (fun _ => 0) (JMach.init X 1) k + b + Φ X.toNet ≤
        c₀ * ((JMach.init X 1).trace xs (fun _ => 0) k).2 +
          Φ ((JMach.init X 1).trace xs (fun _ => 0) k).1.toMach.goal := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, fun T hT => ?_, ?_⟩
      · change (JMach.init X 1).ths[0]? = some T at hT
        simp only [JMach.init, List.range_one, List.map_cons, List.map_nil,
          List.getElem?_cons_zero, Option.some.injEq] at hT
        subst hT
        refine ⟨fun w h => ?_, fun _ p q js h => ?_⟩
        · cases h
        · cases h
      · show 0 + 0 + Φ X.toNet ≤ c₀ * 0 + Φ (JMach.init X 1).toMach.goal
        rw [eg]
        omega
    | succ k ih =>
      intro hk
      obtain ⟨b, hb, hle⟩ := ih (by omega)
      have hl : ((JMach.init X 1).trace xs (fun _ => 0) k).1.ths.length = 1 := by
        rw [JMach.trace_length]
        simp [JMach.init]
      obtain ⟨T, h1⟩ := JMach.one_thread hl
      obtain ⟨b', hb', hle'⟩ :=
        JMach.owes_step hJ hpay (live k) h1 (hP k (by omega)) (hP (k + 1) hk) hb
      refine ⟨b', hb', ?_⟩
      show JMach.walked xs (fun _ => 0) (JMach.init X 1) k +
          JMach.walkAct ((JMach.init X 1).trace xs (fun _ => 0) k).1 0 + b' + Φ X.toNet ≤
        c₀ * (((JMach.init X 1).trace xs (fun _ => 0) k).2 +
          (((JMach.init X 1).trace xs (fun _ => 0) k).1.step xs 0).2) +
          Φ (((JMach.init X 1).trace xs (fun _ => 0) k).1.step xs 0).1.toMach.goal
      rw [Nat.mul_add]
      omega
  obtain ⟨b, -, hle⟩ := key i (Nat.le_refl _)
  omega

end INet
