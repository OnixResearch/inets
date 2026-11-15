import InteractionNets.Program

namespace INet

variable {S : Type}

/-! # A program that rechecks only what a rule touched

`XMach.act` takes a fresh copy of the whole list of agents after every
claim, so every rewrite step may read all of memory again.  Here a thread
keeps its list after a claim and puts the agents the rule wrote in front of
it.  Every new active pair then involves one of them, except when the rule
wires two of its interface ports together: then the two old agents whose
principal wires ran into the fired pair may come to face each other.  After
a claim of such a rule (one that *joins*) the thread takes a fresh copy of
the list of agents, as `XMach` does after every claim.

A thread writes the segments of a right-hand side before its agents
(`Mach` lets the two lists be written in any order): while a segment is
missing, none of the new agents is in memory, so none can be taken, and a
thread that finds the segment missing has found a new agent still to be
written.  The program only reads memory where `XMach` does and writes the
same right-hand side, so it is still an execution of the machine `Mach`
(`WMach.act_sim`, `WMach.exec_run`), and the evaluable test of
`XMach.exec_agrees` carries over (`WMach.exec_agrees`).  That every active
pair a firing makes is an old one or has a new agent in it, when the rule
joins no interface ports, is `Redex.of_fire`; with it `WorkLive.lean` shows
that the threads never all rest before the normal form.

What it buys, measured by evaluation with one thread (actions until rest):

* a numeral of `k` successors listed first, then `k` pairs of an eraser and
  a zero: `XMach` takes 138, 423, 1443, 5283, 20163 actions for `k` = 5,
  10, 20, 40, 80 (about `3 * k ^ 2`), this program `10 * k + 3`;
* on the Peano expressions measured (sums, products, factorials, powers)
  the two are within 12% of each other, except `((5 + 0) + 0) + …`, where
  every claim joins and this program takes up to 1.7 times as many.

A version that walked the old side of each joined wire instead of
rescanning was quadratic on `0 + (0 + (… + 5))`: memory keeps every
segment ever written, so the walks grow. -/

section WMachine

/-- A thread of the program: the agents it has yet to try, its state, and
whether it must take a fresh list once it has written. -/
structure WThread (S : Type) where
  todo : List (Id × S)
  st : TState S
  again : Bool

/-- The thread of `XMach` it agrees with. -/
def WThread.toX (T : WThread S) : XThread S := ⟨T.todo, T.st⟩

/-- The machine as data. -/
structure WMach (S : Type) where
  mem : XNet S
  ths : List (WThread S)

/-- The machine it stands for. -/
def WMach.toMach (M : WMach S) : Mach S := ⟨M.mem.toNet, threadOf (M.ths.map WThread.toX)⟩

/-- The rule wires two of its interface ports together. -/
def XRhs.joins (R : XRhs S) (ar : S → Nat) (α β : S) : Bool :=
  (ifcPorts ar α β).any fun x =>
    match R.wire x with
    | some y => !y.isNew
    | none => false

variable [DecidableEq S]

/-- One action of a thread on the memory `X`: the new memory, the new
thread, and `1` if the action completed a claim. -/
def WMach.act (xs : XSys S) (X : XNet S) (T : WThread S) : XNet S × WThread S × Nat :=
  match T.st with
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (X.takeAgent b, ⟨R.newAgents a b ++ T.todo,
        .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β),
        T.again || R.joins xs.sys.ar α β⟩, 1)
    | none => (X.putAgent a α, ⟨T.todo, .idle, T.again⟩, 0)
  | .write as ((p, q) :: ls) => (X.putLink p q, ⟨T.todo, .write as ls, T.again⟩, 0)
  | .write ((i, γ) :: as) [] => (X.putAgent i γ, ⟨T.todo, .write as [], T.again⟩, 0)
  | .write [] [] =>
    if T.again then (X, ⟨X.agents, .idle, false⟩, 0) else (X, ⟨T.todo, .idle, false⟩, 0)
  | _ =>
    ((XMach.act xs X T.toX).1,
      ⟨(XMach.act xs X T.toX).2.1.todo, (XMach.act xs X T.toX).2.1.st, T.again⟩,
      (XMach.act xs X T.toX).2.2)

/-- Away from writing, an action of the program does to the memory and to
the state of the thread what an action of `XMach` does. -/
theorem WMach.act_agree (xs : XSys S) (X : XNet S) (T : WThread S)
    (hT : ∀ as ls, T.st ≠ .write as ls) :
    WMach.act xs X T = ((XMach.act xs X T.toX).1,
      ⟨(XMach.act xs X T.toX).2.1.todo, (XMach.act xs X T.toX).2.1.st, T.again⟩,
      (XMach.act xs X T.toX).2.2) ∨
    ∃ a b α β R, T.st = .half a b α β ∧
      (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R ∧
      WMach.act xs X T = (X.takeAgent b, ⟨R.newAgents a b ++ T.todo,
        .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β),
        T.again || R.joins xs.sys.ar α β⟩, 1) ∧
      XMach.act xs X T.toX = (X.takeAgent b,
        ⟨T.todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) := by
  obtain ⟨todo, st, again⟩ := T
  cases st with
  | idle => exact .inl rfl
  | look a α => exact .inl rfl
  | seek a α p c => exact .inl rfl
  | ready a b α β => exact .inl rfl
  | half a b α β =>
    cases h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      refine .inr ⟨a, b, α, β, R, rfl, h, ?_, ?_⟩
      · unfold WMach.act
        dsimp only
        rw [h]
      · unfold XMach.act
        dsimp only [WThread.toX]
        rw [h]
    | none =>
      refine .inl ?_
      unfold WMach.act XMach.act
      dsimp only [WThread.toX]
      rw [h]
      rfl
  | write as ls => exact absurd rfl (hT as ls)

/-- **An action of the program is an action of the machine**, or changes
neither the memory nor the state of the thread. -/
theorem WMach.act_sim (xs : XSys S) (X : XNet S) (T : WThread S) (th : Nat → TState S)
    (t : Nat) (hs : th t = T.st) :
    ((WMach.act xs X T).1 = X ∧ (WMach.act xs X T).2.1.st = T.st ∧
        (WMach.act xs X T).2.2 = 0) ∨
      MStep xs.sys (WMach.act xs X T).2.2 ⟨X.toNet, th⟩
        ⟨(WMach.act xs X T).1.toNet, upd th t (WMach.act xs X T).2.1.st⟩ := by
  by_cases hT : ∀ as ls, T.st ≠ .write as ls
  · rcases WMach.act_agree xs X T hT with e | ⟨a, b, α, β, R, -, -, e, ex⟩
    · rw [e]
      exact XMach.act_sim xs X T.toX th t hs
    · have h := XMach.act_sim xs X T.toX th t hs
      rw [ex] at h
      rw [e]
      rcases h with ⟨-, -, h⟩ | h
      · cases h
      · exact .inr h
  · obtain ⟨as, ls, hw⟩ : ∃ as ls, T.st = .write as ls := by
      apply Classical.byContradiction
      intro hn
      exact hT fun as ls e => hn ⟨as, ls, e⟩
    obtain ⟨todo, st, again⟩ := T
    dsimp only at hw
    subst hw
    refine .inr ?_
    cases ls with
    | cons e ls =>
      obtain ⟨p, q⟩ := e
      have hs' : th t = .write as ((p, q) :: ls) := hs
      show MStep xs.sys 0 ⟨X.toNet, th⟩ ⟨(X.putLink p q).toNet, upd th t (.write as ls)⟩
      rw [XNet.putLink_toNet]
      exact .link (M := ⟨X.toNet, th⟩) hs'
    | nil =>
      cases as with
      | cons e as =>
        obtain ⟨i, γ⟩ := e
        have hs' : th t = .write ((i, γ) :: as) [] := hs
        show MStep xs.sys 0 ⟨X.toNet, th⟩ ⟨(X.putAgent i γ).toNet, upd th t (.write as [])⟩
        rw [XNet.putAgent_toNet]
        exact .agent (M := ⟨X.toNet, th⟩) hs'
      | nil =>
        have hs' : th t = .write [] [] := hs
        unfold WMach.act
        dsimp only
        split
        · exact .done (M := ⟨X.toNet, th⟩) hs'
        · exact .done (M := ⟨X.toNet, th⟩) hs'

omit [DecidableEq S] in
theorem threadOf_map_eq {ths : List (WThread S)} {t : Nat} {T : WThread S}
    (h : ths[t]? = some T) : threadOf (ths.map WThread.toX) t = T.st := by
  have h' : (ths.map WThread.toX)[t]? = some T.toX := by
    rw [List.getElem?_map, h]
    rfl
  exact threadOf_eq h'

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def WMach.step (xs : XSys S) (M : WMach S) (t : Nat) : WMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(WMach.act xs M.mem T).1, M.ths.set t (WMach.act xs M.mem T).2.1⟩,
      (WMach.act xs M.mem T).2.2)
  | none => (M, 0)

theorem WMach.step_sim (xs : XSys S) (M : WMach S) (t : Nat) :
    ((M.step xs t).1.toMach = M.toMach ∧ (M.step xs t).2 = 0) ∨
      MStep xs.sys (M.step xs t).2 M.toMach (M.step xs t).1.toMach := by
  unfold WMach.step
  cases h : M.ths[t]? with
  | none => exact .inl ⟨rfl, rfl⟩
  | some T =>
    have hm : (M.ths.map WThread.toX)[t]? = some T.toX := by
      rw [List.getElem?_map, h]
      rfl
    have hset : (M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX =
        (M.ths.map WThread.toX).set t (WMach.act xs M.mem T).2.1.toX := by
      rw [List.map_set]
    rcases WMach.act_sim xs M.mem T (threadOf (M.ths.map WThread.toX)) t
        (threadOf_map_eq h) with ⟨e₁, e₂, e₃⟩ | hs
    · refine .inl ⟨?_, e₃⟩
      show Mach.mk (WMach.act xs M.mem T).1.toNet
        (threadOf ((M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX)) =
          ⟨M.mem.toNet, threadOf (M.ths.map WThread.toX)⟩
      rw [hset, threadOf_set hm, e₁]
      show Mach.mk M.mem.toNet (upd _ t (WMach.act xs M.mem T).2.1.st) = _
      rw [e₂, ← threadOf_map_eq h, upd_self]
    · refine .inr ?_
      show MStep xs.sys _ ⟨M.mem.toNet, threadOf (M.ths.map WThread.toX)⟩
        ⟨(WMach.act xs M.mem T).1.toNet,
          threadOf ((M.ths.set t (WMach.act xs M.mem T).2.1).map WThread.toX)⟩
      rw [hset, threadOf_set hm]
      exact hs

/-- Run the threads in the order given by a schedule.  Returns the final
state and the number of claims. -/
def WMach.exec (xs : XSys S) : List Nat → WMach S → WMach S × Nat
  | [], M => (M, 0)
  | t :: ts, M =>
    ((WMach.exec xs ts (M.step xs t).1).1,
      (M.step xs t).2 + (WMach.exec xs ts (M.step xs t).1).2)

/-- **A run of the program is an execution of the machine**, whatever the
schedule. -/
theorem WMach.exec_run (xs : XSys S) : ∀ (ts : List Nat) (M : WMach S),
    MRun xs.sys (M.exec xs ts).2 M.toMach (M.exec xs ts).1.toMach
  | [], M => .refl _
  | t :: ts, M => by
    have ih := WMach.exec_run xs ts (M.step xs t).1
    show MRun xs.sys ((M.step xs t).2 + (WMach.exec xs ts (M.step xs t).1).2) M.toMach
      (WMach.exec xs ts (M.step xs t).1).1.toMach
    rcases WMach.step_sim xs M t with ⟨e₁, e₂⟩ | hs
    · rw [e₂, Nat.zero_add, ← e₁]
      exact ih
    · exact .step hs ih

/-- The program before it starts: `n` idle threads, as for `XMach`. -/
def WMach.init (X : XNet S) (n : Nat) : WMach S :=
  ⟨X, (List.range n).map fun t => ⟨X.agents.drop t ++ X.agents.take t, .idle, false⟩⟩

omit [DecidableEq S] in
theorem WMach.init_toMach (X : XNet S) (n : Nat) :
    (WMach.init X n).toMach = Mach.init X.toNet := by
  refine congrArg (Mach.mk X.toNet) (funext fun u => ?_)
  show threadOf (((List.range n).map fun t =>
    (⟨X.agents.drop t ++ X.agents.take t, .idle, false⟩ : WThread S)).map WThread.toX) u =
      .idle
  unfold threadOf
  split
  · rename_i T hT
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hT)
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT'
    rfl
  · rfl

/-- Every thread is idle. -/
def WMach.quiet (M : WMach S) : Bool := M.ths.all fun T => T.st.isIdle

omit [DecidableEq S] in
theorem WMach.quiet_toMach {M : WMach S} (h : M.quiet = true) : M.toMach.Quiet := by
  have hx : (⟨M.mem, M.ths.map WThread.toX⟩ : XMach S).quiet = true := by
    show (M.ths.map WThread.toX).all _ = true
    rw [List.all_map]
    exact h
  exact XMach.quiet_toMach hx

/-- Nothing is left to do: every thread is idle, with nothing to try. -/
def WMach.resting (M : WMach S) : Bool :=
  M.ths.all fun T => T.todo.isEmpty && T.st.isIdle

/-- A run from a net, with `n` threads, is an execution of the machine from
that net. -/
theorem WMach.exec_mrun (xs : XSys S) (X : XNet S) (n : Nat) (σ : List Nat) :
    MRun xs.sys ((WMach.init X n).exec xs σ).2 (Mach.init X.toNet)
      ((WMach.init X n).exec xs σ).1.toMach := by
  have h := WMach.exec_run xs σ (WMach.init X n)
  rw [WMach.init_toMach] at h
  exact h

/-- **The program agrees with the list reducer.**  If a run ends with every
thread idle after as many claims as the list reducer took steps, then the
memory holds a normal form, and with its history forgotten it is the net
that the list reducer returned.  Both hypotheses can be evaluated. -/
theorem WMach.exec_agrees {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) {n : Nat} {σ : List Nat}
    (hq : ((WMach.init X n).exec xs σ).1.quiet = true)
    (hk : ((WMach.init X n).exec xs σ).2 = (X.run xs f).2) :
    Normal (Step xs.sys) ((WMach.init X n).exec xs σ).1.mem.toNet ∧
      ((WMach.init X n).exec xs σ).1.mem.toNet.compact xs.sys.ar = (X.run xs f).1.toNet := by
  have hr := WMach.exec_mrun xs X n σ
  have sts := hr.quiet hX.1 (WMach.quiet_toMach hq)
  have hwf := Steps.wf hX.1 sts
  have cs := Steps.cstep hX.1 sts
  rw [hX.2, hk] at cs
  have e := XNet.run_agree hX f stop cs
  refine ⟨(normal_compact hwf).2 ?_, e⟩
  rw [e]
  exact (XNet.run_normal hX f stop).1

/-- No run makes more claims than the list reducer takes steps. -/
theorem WMach.exec_le {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) (n : Nat) (σ : List Nat) :
    ((WMach.init X n).exec xs σ).2 ≤ (X.run xs f).2 := by
  have sts := (WMach.exec_mrun xs X n σ).sequential hX.1
  have cs := Steps.cstep hX.1 sts
  rw [hX.2] at cs
  exact ((XNet.run_normal hX f stop).2 cs).1

end WMachine

/-! ### The active pairs a firing makes

When a rule wires no two of its interface ports together, every active pair
after the firing was an active pair before, or has a new agent in it: a
wire between two old principal ports cannot run through the fired pair, for
it would have to enter an interface port by an old segment and leave it by
a new one, and a new segment that leaves an interface port goes to a port
of a new agent, which ends the wire. -/

section NewPairs

variable {sys : System S}

/-- The rule wires no two of its interface ports together. -/
def Rhs.NoJoin (R : Rhs S) : Prop := ∀ x y, R.link x y → x.IsNew ∨ y.IsNew

/-- A walk of the net after a firing by a rule that joins no interface
ports, which starts and ends away from the new agents and does not start at
a port of the fired pair, is a walk of the net before. -/
theorem walk_of_fire {G : Net S} {c d : Id} {γ δ : S} {R : Rhs S}
    (site : Site sys.ar G c d γ δ) (hR : R.NoJoin) (hRwf : R.WF sys.ar γ δ) :
    ∀ {u v x y : Port}, Walk (G.fire c d R).link ((G.fire c d R).End sys.ar) u v x y →
      (∀ o j, u.1 ≠ child c d o j) → ¬ (G.End sys.ar u ∧ (u.1 = c ∨ u.1 = d)) →
      (∀ o j, y.1 ≠ child c d o j) →
      Walk G.link (G.End sys.ar) u v x y := by
  have hG := site.wf
  -- a segment leaving a port that is not one of the fired pair's or a new
  -- agent's is old
  have old : ∀ {u v : Port}, (G.fire c d R).link u v → (∀ o j, u.1 ≠ child c d o j) →
      ¬ (G.End sys.ar u ∧ (u.1 = c ∨ u.1 = d)) → G.link u v := by
    intro u v h h1 h2
    rcases h with h | ⟨x', y', hxy, rfl, rfl⟩
    · exact h
    · cases x' with
      | ifc s k =>
        have hk : k < sys.ar (sel γ δ s) := hRwf.valid hxy
        refine absurd ⟨.inr ⟨sel γ δ s, site.agent_sel s, hk⟩, ?_⟩ h2
        cases s
        · exact .inl rfl
        · exact .inr rfl
      | new o j k => exact absurd rfl (h1 o j)
  -- a port of a new agent at the end of a new segment is an end
  have newEnd : ∀ {x' : LPort} {o : Option Bool} {j k : Nat}, R.link x' (.new o j k) →
      (G.fire c d R).End sys.ar (emb c d (.new o j k)) := by
    intro x' o j k h
    obtain ⟨γ', hl, hk⟩ := (hRwf.valid (hRwf.symm h) : R.Valid sys.ar γ δ (.new o j k))
    exact .inr ⟨γ', .inr ⟨o, j, rfl, hl⟩, hk⟩
  intro u v x y w
  induction w with
  | single h =>
    intro h1 h2 _
    exact .single (old h h1 h2)
  | cons h hT hne w ih =>
    rename_i u v w' x y
    intro h1 h2 hy
    have hl := old h h1 h2
    have hv1 : ∀ o j, v.1 ≠ child c d o j := by
      intro o j e
      apply site.not_used_child o j
      rw [← e]
      exact .inr (.inl ⟨v.2, u, hG.symm hl⟩)
    have hv2 : ¬ (G.End sys.ar v ∧ (v.1 = c ∨ v.1 = d)) := by
      rintro ⟨hE, -⟩
      -- the walk goes on from `v` by a segment to `w'`
      have next : (G.fire c d R).link v w' ∧
          ((G.fire c d R).End sys.ar w' → (∃ o j, w'.1 = child c d o j) → False) := by
        cases w with
        | single h' =>
          exact ⟨h', fun _ ⟨o, j, e⟩ => hy o j e⟩
        | cons h' hT' _ _ => exact ⟨h', fun hE' _ => hT' hE'⟩
      obtain ⟨hn, stop⟩ := next
      rcases hn with hn | ⟨x', y', hxy, ev, ew⟩
      · exact hne (hG.end_unique hE hn (hG.symm hl))
      · rcases hR x' y' hxy with hx | hy'
        · cases x' with
          | ifc s k => exact hx
          | new o j k => exact hv1 o j (congrArg Prod.fst ev)
        · cases y' with
          | ifc s k => exact hy'
          | new o j k =>
            rw [ew] at stop
            exact stop (newEnd hxy) ⟨o, j, rfl⟩
    have hTG : ¬ G.End sys.ar v := by
      intro hE
      rcases hE with hf | ⟨γ', hag, hk⟩
      · exact hT (.inl hf)
      · by_cases hcd : v.1 = c ∨ v.1 = d
        · exact hv2 ⟨.inr ⟨γ', hag, hk⟩, hcd⟩
        · refine hT (.inr ⟨γ', .inl ⟨hag, fun e => hcd (.inl e), fun e => hcd (.inr e)⟩, hk⟩)
    exact .cons hl hTG hne (ih hv1 hv2 hy)

/-- **After a firing by a rule that joins no interface ports, an active
pair was already one, or has a new agent in it.** -/
theorem Redex.of_fire {G : Net S} {c d a b : Id} {γ δ α β : S} {R R' : Rhs S}
    (hG : G.WF sys.ar) (r : Redex sys G c d γ δ R) (hR : R.NoJoin)
    (r' : Redex sys (G.fire c d R) a b α β R') :
    Redex sys G a b α β R' ∨ (∃ o j, a = child c d o j) ∨ ∃ o j, b = child c d o j := by
  have site : Site sys.ar G c d γ δ := ⟨hG, r.ha, r.hb, r.ne, r.conn⟩
  have hRwf := sys.rule_wf r.rule
  by_cases ha : ∃ o j, a = child c d o j
  · exact .inr (.inl ha)
  by_cases hb : ∃ o j, b = child c d o j
  · exact .inr (.inr hb)
  refine .inl ?_
  have oldAgent : ∀ {i : Id} {ε : S}, (G.fire c d R).agent i ε → ¬ (∃ o j, i = child c d o j) →
      G.agent i ε ∧ i ≠ c ∧ i ≠ d := by
    intro i ε h hi
    rcases h with h | ⟨o, j, e, -⟩
    · exact h
    · exact absurd ⟨o, j, e⟩ hi
  obtain ⟨hga, hac, had⟩ := oldAgent r'.ha ha
  obtain ⟨hgb, -, -⟩ := oldAgent r'.hb hb
  obtain ⟨v, x, w⟩ := r'.conn
  refine ⟨hga, hgb, r'.ne, ⟨v, x, walk_of_fire site hR hRwf w
    (fun o j e => ha ⟨o, j, e⟩) ?_ (fun o j e => hb ⟨o, j, e⟩)⟩, r'.rule⟩
  rintro ⟨-, e | e⟩
  · exact hac e
  · exact had e

end NewPairs

end INet
