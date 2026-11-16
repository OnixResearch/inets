import InteractionNets.JoinCritWork

/-! # The measuring runs, proved to be the schedules of the bounds

The tables of `MeasureJoin` count the actions of `JMach` until every thread
is at rest, and the actions of walks, under two schedules.  Those programs
are loops in `Id.run`; nothing proved about them.  Here a run is written
once more, by recursion on the fuel and for any choice of turn `pk`, and
proved to count exactly what the bounds are about: it stops at the first
state at rest (`JMach.pRun_spec`), and the actions of walks it counts are
`JMach.walked` along the same run.

So the counts it returns are bounded by the theorems themselves, with no
hypothesis on the fuel:
* `JMach.bfRun_rests`, `JMach.bfRun_walked`: the busy-first schedule
  `JMach.bfSched`, by `JMach.rests_bfSched` and `JMach.walked_cs`;
* `JMach.csRun_rests`, `JMach.csRun_walked`: the schedule `JMach.csSched`,
  by `JMach.rests_csSched` and `JMach.walked_csSched`;
* `Arith.bfRun_rests`: the busy-first schedule on any net of the adders.

The tables of `MeasureJoin` for several threads are taken with these runs.
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- The states of the run where `pk` chooses the turn from the state and the
number of actions so far. -/
def JMach.pState (xs : XSys S) (pk : JMach S → Nat → Nat) (M : JMach S) : Nat → JMach S
  | 0 => M
  | i + 1 => ((JMach.pState xs pk M i).step xs (pk (JMach.pState xs pk M i) i)).1

/-- The schedule where `pk` chooses the turn. -/
def JMach.pSched (xs : XSys S) (pk : JMach S → Nat → Nat) (M : JMach S) (i : Nat) : Nat :=
  pk (JMach.pState xs pk M i) i

theorem JMach.pState_trace (xs : XSys S) (pk : JMach S → Nat → Nat) (M : JMach S) :
    ∀ i, (M.trace xs (JMach.pSched xs pk M) i).1 = JMach.pState xs pk M i
  | 0 => rfl
  | i + 1 => by
    show ((M.trace xs (JMach.pSched xs pk M) i).1.step xs (JMach.pSched xs pk M i)).1 = _
    rw [JMach.pState_trace xs pk M i]
    rfl

theorem JMach.bfState_eq (xs : XSys S) (M : JMach S) (nt : Nat) :
    ∀ i, JMach.bfState xs M nt i = JMach.pState xs (fun M i => M.bfPick nt i) M i
  | 0 => rfl
  | i + 1 => by
    show ((JMach.bfState xs M nt i).step xs ((JMach.bfState xs M nt i).bfPick nt i)).1 = _
    rw [JMach.bfState_eq xs M nt i]
    rfl

theorem JMach.bfSched_eq (xs : XSys S) (M : JMach S) (nt : Nat) :
    JMach.bfSched xs M nt = JMach.pSched xs (fun M i => M.bfPick nt i) M := by
  funext i
  show (JMach.bfState xs M nt i).bfPick nt i = _
  rw [JMach.bfState_eq]
  rfl

theorem JMach.csState_eq (xs : XSys S) (M : JMach S) (nt : Nat) :
    ∀ i, JMach.csState xs M nt i = JMach.pState xs (fun M i => M.csPick nt i) M i
  | 0 => rfl
  | i + 1 => by
    show ((JMach.csState xs M nt i).step xs ((JMach.csState xs M nt i).csPick nt i)).1 = _
    rw [JMach.csState_eq xs M nt i]
    rfl

theorem JMach.csSched_eq (xs : XSys S) (M : JMach S) (nt : Nat) :
    JMach.csSched xs M nt = JMach.pSched xs (fun M i => M.csPick nt i) M := by
  funext i
  show (JMach.csState xs M nt i).csPick nt i = _
  rw [JMach.csState_eq]
  rfl

/-- **The measuring run.**  From the state `M` after `i` actions, with `w`
actions of walks so far: stop at a state at rest or when the fuel is out,
and return the actions and the actions of walks. -/
def JMach.pLoop (xs : XSys S) (pk : JMach S → Nat → Nat) :
    Nat → Nat → Nat → JMach S → Nat × Nat
  | 0, i, w, _ => (i, w)
  | f + 1, i, w, M =>
    if M.resting then (i, w)
    else JMach.pLoop xs pk f (i + 1) (w + M.walkAct (pk M i)) (M.step xs (pk M i)).1

/-- The actions until rest and the actions of walks, within `fuel` actions,
when `pk` chooses the turn. -/
def JMach.pRun (xs : XSys S) (pk : JMach S → Nat → Nat) (M : JMach S) (fuel : Nat) :
    Nat × Nat :=
  JMach.pLoop xs pk fuel 0 0 M

theorem JMach.pLoop_spec (xs : XSys S) (pk : JMach S → Nat → Nat) (M : JMach S) :
    ∀ f i, i ≤ (JMach.pLoop xs pk f i (JMach.walked xs (JMach.pSched xs pk M) M i)
        (JMach.pState xs pk M i)).1 ∧
      (JMach.pLoop xs pk f i (JMach.walked xs (JMach.pSched xs pk M) M i)
        (JMach.pState xs pk M i)).1 ≤ i + f ∧
      (JMach.pLoop xs pk f i (JMach.walked xs (JMach.pSched xs pk M) M i)
        (JMach.pState xs pk M i)).2 =
        JMach.walked xs (JMach.pSched xs pk M) M
          (JMach.pLoop xs pk f i (JMach.walked xs (JMach.pSched xs pk M) M i)
            (JMach.pState xs pk M i)).1 ∧
      ((JMach.pLoop xs pk f i (JMach.walked xs (JMach.pSched xs pk M) M i)
        (JMach.pState xs pk M i)).1 < i + f →
        (JMach.pState xs pk M (JMach.pLoop xs pk f i
          (JMach.walked xs (JMach.pSched xs pk M) M i) (JMach.pState xs pk M i)).1).resting =
          true) ∧
      ∀ k, i ≤ k → k < (JMach.pLoop xs pk f i (JMach.walked xs (JMach.pSched xs pk M) M i)
        (JMach.pState xs pk M i)).1 → (JMach.pState xs pk M k).resting = false
  | 0, i => by
    refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun h => absurd h (Nat.lt_irrefl _),
      fun k h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)⟩
  | f + 1, i => by
    by_cases hr : (JMach.pState xs pk M i).resting = true
    · have he : JMach.pLoop xs pk (f + 1) i (JMach.walked xs (JMach.pSched xs pk M) M i)
          (JMach.pState xs pk M i) = (i, JMach.walked xs (JMach.pSched xs pk M) M i) := by
        show (if (JMach.pState xs pk M i).resting then _ else _) = _
        rw [ite_pos' hr]
      rw [he]
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _, rfl, fun _ => hr,
        fun k h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)⟩
    · have hw : JMach.walked xs (JMach.pSched xs pk M) M i +
          (JMach.pState xs pk M i).walkAct (pk (JMach.pState xs pk M i) i) =
          JMach.walked xs (JMach.pSched xs pk M) M (i + 1) := by
        show _ = JMach.walked xs (JMach.pSched xs pk M) M i +
          JMach.walkAct (M.trace xs (JMach.pSched xs pk M) i).1 (JMach.pSched xs pk M i)
        rw [JMach.pState_trace]
        rfl
      have he : JMach.pLoop xs pk (f + 1) i (JMach.walked xs (JMach.pSched xs pk M) M i)
          (JMach.pState xs pk M i) = JMach.pLoop xs pk f (i + 1)
            (JMach.walked xs (JMach.pSched xs pk M) M (i + 1))
            (JMach.pState xs pk M (i + 1)) := by
        show (if (JMach.pState xs pk M i).resting then _ else _) = _
        rw [ite_neg' hr, hw]
        rfl
      rw [he]
      obtain ⟨h1, h2, h3, h4, h5⟩ := JMach.pLoop_spec xs pk M f (i + 1)
      refine ⟨by omega, by omega, h3, fun h => h4 (by omega), fun k hk1 hk2 => ?_⟩
      by_cases hk : k = i
      · subst hk
        cases h : (JMach.pState xs pk M k).resting
        · rfl
        · exact absurd h hr
      · exact h5 k (by omega) hk2

/-- **The measuring run counts what the bounds are about.**  It returns
`(i, w)` with `i` at most the fuel; no state before `i` is at rest; the
state after `i` actions is at rest unless the fuel ran out; and `w` is the
number of actions of walks among the first `i`, `JMach.walked`. -/
theorem JMach.pRun_spec (xs : XSys S) (pk : JMach S → Nat → Nat) (M : JMach S) (fuel : Nat) :
    (JMach.pRun xs pk M fuel).1 ≤ fuel ∧
      (JMach.pRun xs pk M fuel).2 =
        JMach.walked xs (JMach.pSched xs pk M) M (JMach.pRun xs pk M fuel).1 ∧
      ((JMach.pRun xs pk M fuel).1 < fuel →
        ((M.trace xs (JMach.pSched xs pk M) (JMach.pRun xs pk M fuel).1).1).resting = true) ∧
      ∀ k, k < (JMach.pRun xs pk M fuel).1 →
        ((M.trace xs (JMach.pSched xs pk M) k).1).resting = false := by
  have e : JMach.pRun xs pk M fuel = JMach.pLoop xs pk fuel 0
      (JMach.walked xs (JMach.pSched xs pk M) M 0) (JMach.pState xs pk M 0) := rfl
  rw [e]
  obtain ⟨_, h2, h3, h4, h5⟩ := JMach.pLoop_spec xs pk M fuel 0
  refine ⟨by simpa using h2, h3, fun h => ?_, fun k hk => ?_⟩
  · rw [JMach.pState_trace]
    exact h4 (by simpa using h)
  · rw [JMach.pState_trace]
    exact h5 k (Nat.zero_le _) hk

/-- If the run is at rest after `B + 1` actions or later, the measuring run
stops within `B + 1`. -/
theorem JMach.pRun_le {pk : JMach S → Nat → Nat} {M : JMach S} {B : Nat}
    (h : ∀ i, B < i → ((M.trace xs (JMach.pSched xs pk M) i).1).resting = true) (fuel : Nat) :
    (JMach.pRun xs pk M fuel).1 ≤ B + 1 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := (JMach.pRun_spec xs pk M fuel).2.2.2 (B + 1) hlt
  rw [h (B + 1) (Nat.lt_succ_self B)] at this
  cases this

/-- The busy-first measuring run, from a net with `nt` threads. -/
def JMach.bfRun (xs : XSys S) (X : XNet S) (nt fuel : Nat) : Nat × Nat :=
  JMach.pRun xs (fun M i => M.bfPick nt i) (JMach.init X nt) fuel

/-- The measuring run where a thread in a claim keeps the turn and
otherwise threads take turns, from a net with `nt` threads. -/
def JMach.csRun (xs : XSys S) (X : XNet S) (nt fuel : Nat) : Nat × Nat :=
  JMach.pRun xs (fun M i => M.csPick nt i) (JMach.init X nt) fuel

omit [DecidableEq S] in
theorem JMach.init_hcs (X : XNet S) (nt : Nat) :
    ∀ (u : Nat) (U : JThread S), (JMach.init X nt).ths[u]? = some U → U.critical = false :=
  fun u U hU => by
    unfold JMach.init at hU
    rw [List.getElem?_map] at hU
    cases hr : (List.range nt)[u]? with
    | none => rw [hr] at hU; cases hU
    | some t =>
      rw [hr] at hU
      cases hU
      rfl

/-- **The busy-first measuring run is within the proved bound**:
`nt (7 |agents| + K) + n (C + D + 1 + 9J) + 7Cn + K + J (4K log₂(K+1) + 6K)`
actions and one more, with `K = wires + Dn`, whatever the fuel. -/
theorem JMach.bfRun_rests {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (fuel : Nat) :
    (JMach.bfRun xs X nt fuel).1 ≤
      nt * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n)) + 1 := by
  refine JMach.pRun_le (fun i hi => ?_) fuel
  rw [← JMach.bfSched_eq]
  exact JMach.rests_bfSched hJ hX hnd hnt hb hs hn i hi

/-- **The walks the busy-first measuring run counts are within the bound of
one thread.** -/
theorem JMach.bfRun_walked {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt) {C D : Nat} (hb : xs.Bounded C D)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N')
    (fuel : Nat) :
    (JMach.bfRun xs X nt fuel).2 ≤ n * (9 * J) +
      J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        6 * (X.wires.length + D * n)) := by
  unfold JMach.bfRun
  rw [(JMach.pRun_spec xs _ _ fuel).2.1, ← JMach.bfSched_eq]
  exact JMach.walked_cs hJ hX hnt hb hs hn _
    (JMach.bfSched_hcs xs (JMach.init_hcs X nt)) _

/-- **The measuring run where turns go round is within the proved bound**
of `JMach.rests_csSched`, `nt` times the work bound. -/
theorem JMach.csRun_rests {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (fuel : Nat) :
    (JMach.csRun xs X nt fuel).1 ≤
      nt * (nt * (7 * X.agents.length + (X.wires.length + D * n)) +
        n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n)) + 1) := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := (JMach.pRun_spec xs _ _ fuel).2.2.2 _ hlt
  rw [← JMach.csSched_eq, JMach.rests_csSched hJ hX hnd hnt hb hs hn _ (Nat.le_refl _)] at this
  cases this

/-- **The walks the measuring run where turns go round counts are within
the bound of one thread.** -/
theorem JMach.csRun_walked {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt) {C D : Nat} (hb : xs.Bounded C D)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N')
    (fuel : Nat) :
    (JMach.csRun xs X nt fuel).2 ≤ n * (9 * J) +
      J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        6 * (X.wires.length + D * n)) := by
  unfold JMach.csRun
  rw [(JMach.pRun_spec xs _ _ fuel).2.1, ← JMach.csSched_eq]
  exact JMach.walked_csSched hJ hX hnt hb hs hn _

/-- Every rule of the adders joins one segment at most. -/
theorem Arith.xsys_joinsAtMost : Arith.xsys.JoinsAtMost 1 :=
  XSys.joinsAtMost_of fun α β R h => by
    cases α <;> cases β <;> cases h <;> decide

/-- **The busy-first measuring run on any net of the adders**, with any
number of threads, stops within
`nt (7 |agents| + K) + 20n + 14n + K + 4K log₂(K+1) + 6K + 1` actions, with
`K = wires + 8n`, where `n` is the number of steps to the normal form. -/
theorem Arith.bfRun_rests {X : XNet Arith} (hX : X.toNet.WF Arith.xsys.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {n : Nat} {N' : Net Arith}
    (hs : Steps (Step Arith.xsys.sys) n X.toNet N') (hn : Normal (Step Arith.xsys.sys) N')
    (fuel : Nat) :
    (JMach.bfRun Arith.xsys X nt fuel).1 ≤
      nt * (7 * X.agents.length + (X.wires.length + 8 * n)) + n * (2 + 8 + 1 + 9 * 1) +
        7 * (2 * n) + (X.wires.length + 8 * n) +
        1 * (4 * ((X.wires.length + 8 * n) * Nat.log2 (X.wires.length + 8 * n + 1)) +
          6 * (X.wires.length + 8 * n)) + 1 :=
  JMach.bfRun_rests Arith.xsys_joinsAtMost hX hnd hnt Arith.xsys_bounded hs hn fuel

end INet
