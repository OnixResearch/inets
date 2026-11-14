import InteractionNets.Reducer

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## The machine as a program

`Mach` says which actions a thread may take.  Here each thread is a program
that says which action it takes.  The memory is three lists (agents, free
ports and segments, history included).  A thread keeps a private list of the
agents it has yet to try.  It reads the first of them, follows the wire from
its principal port, takes the pair if there is a rule for it, and writes
the right-hand side.  After a claim it takes a fresh copy of the list of
agents, and when its list is empty it rests.  `XMach.exec` runs the threads
in the order given by a schedule, a list of thread numbers, and counts the
claims.

`XMach.step_sim` shows that an action of the program is an action of `Mach`
or changes nothing, so every theorem about `Mach` applies to every
schedule.  A run is evaluated by the kernel, and `XMach.exec_agrees` turns
two facts that can be evaluated (every thread is idle, and the claims are as
many as the steps of the list reducer) into the statement that the memory
holds the normal form. -/

section XMachine

/-- Keep one pair for each first component. -/
def dedupFst {A B : Type} [DecidableEq A] : List (A × B) → List (A × B)
  | [] => []
  | e :: l => if e.1 ∈ (dedupFst l).map Prod.fst then dedupFst l else e :: dedupFst l

theorem dedupFst_nodup {A B : Type} [DecidableEq A] :
    ∀ l : List (A × B), ((dedupFst l).map Prod.fst).Nodup
  | [] => List.nodup_nil
  | e :: l => by
    unfold dedupFst
    split
    · exact dedupFst_nodup l
    · rename_i he
      exact List.nodup_cons.2 ⟨he, dedupFst_nodup l⟩

theorem mem_dedupFst {A B : Type} [DecidableEq A] : ∀ (l : List (A × B)),
    (∀ i γ γ', (i, γ) ∈ l → (i, γ') ∈ l → γ = γ') → ∀ x, x ∈ dedupFst l ↔ x ∈ l
  | [], _, _ => Iff.rfl
  | e :: l, hf, x => by
    have ih := mem_dedupFst l fun i γ γ' h₁ h₂ =>
      hf i γ γ' (List.mem_cons_of_mem _ h₁) (List.mem_cons_of_mem _ h₂)
    unfold dedupFst
    split
    · rename_i he
      refine ⟨fun hx => List.mem_cons_of_mem _ ((ih x).1 hx), fun hx => ?_⟩
      rcases List.mem_cons.1 hx with hx | hx
      · obtain ⟨e', he', ee⟩ := List.mem_map.1 he
        have h₁ : (e.1, e'.2) ∈ l := by
          rw [← ee]
          exact (ih e').1 he'
        have e2 : e'.2 = e.2 :=
          hf e.1 e'.2 e.2 (List.mem_cons_of_mem _ h₁) List.mem_cons_self
        have e3 : e' = e := Prod.ext ee e2
        rw [hx, ← e3]
        exact he'
      · exact (ih x).2 hx
    · rw [List.mem_cons, List.mem_cons, ih]

/-! ### Memory as lists -/

/-- Empty the cell of agent `a`. -/
def XNet.takeAgent (X : XNet S) (a : Id) : XNet S :=
  ⟨X.agents.filter fun e => decide (e.1 ≠ a), X.free, X.wires⟩

/-- Write an agent cell. -/
def XNet.putAgent (X : XNet S) (i : Id) (γ : S) : XNet S :=
  ⟨(i, γ) :: X.agents, X.free, X.wires⟩

/-- Write a segment cell. -/
def XNet.putLink (X : XNet S) (p q : Port) : XNet S :=
  ⟨X.agents, X.free, (p, q) :: X.wires⟩

theorem XNet.takeAgent_toNet (X : XNet S) (a : Id) :
    (X.takeAgent a).toNet = X.toNet.take a := by
  apply Net.ext'
  · intro i γ
    show (i, γ) ∈ X.agents.filter _ ↔ (i, γ) ∈ X.agents ∧ i ≠ a
    rw [List.mem_filter]
    exact and_congr Iff.rfl decide_eq_true_iff
  · exact fun _ _ => Iff.rfl
  · exact fun _ => Iff.rfl

theorem XNet.putAgent_toNet (X : XNet S) (i : Id) (γ : S) :
    (X.putAgent i γ).toNet = X.toNet.addAgent i γ := by
  apply Net.ext'
  · intro j δ
    show (j, δ) ∈ (i, γ) :: X.agents ↔ (j, δ) ∈ X.agents ∨ (j = i ∧ δ = γ)
    constructor
    · intro h
      rcases List.mem_cons.1 h with e | h
      · exact .inr ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
      · exact .inl h
    · rintro (h | ⟨rfl, rfl⟩)
      · exact List.mem_cons_of_mem _ h
      · exact List.mem_cons_self
  · exact fun _ _ => Iff.rfl
  · exact fun _ => Iff.rfl

theorem XNet.putLink_toNet (X : XNet S) (p q : Port) :
    (X.putLink p q).toNet = X.toNet.addLink p q := by
  apply Net.ext'
  · exact fun _ _ => Iff.rfl
  · intro x y
    show (x, y) ∈ (p, q) :: X.wires ↔ (x, y) ∈ X.wires ∨ (x = p ∧ y = q)
    constructor
    · intro h
      rcases List.mem_cons.1 h with e | h
      · exact .inr ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
      · exact .inl h
    · rintro (h | ⟨rfl, rfl⟩)
      · exact List.mem_cons_of_mem _ h
      · exact List.mem_cons_self
  · exact fun _ => Iff.rfl

/-- A segment that leaves `c` and does not go back to `p`. -/
def nextSeg : List (Port × Port) → Port → Port → Option Port
  | [], _, _ => none
  | e :: ws, c, p => if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg ws c p

theorem nextSeg_spec : ∀ {ws : List (Port × Port)} {c p q : Port},
    nextSeg ws c p = some q → (c, q) ∈ ws ∧ q ≠ p
  | [], _, _, _, h => by cases h
  | e :: ws, c, p, q, h => by
    unfold nextSeg at h
    split at h
    · rename_i hc
      have eq : e.2 = q := Option.some.inj h
      have ee : e = (c, q) := Prod.ext hc.1 eq
      rw [ee]
      exact ⟨List.mem_cons_self, eq ▸ hc.2⟩
    · obtain ⟨hm, hq⟩ := nextSeg_spec h
      exact ⟨List.mem_cons_of_mem _ hm, hq⟩

/-! ### The right-hand side as a list of writes -/

/-- The agents to write when `a` and `b` fire, each once. -/
def XRhs.newAgents (R : XRhs S) (a b : Id) : List (Id × S) :=
  dedupFst (childList a b R.lab R.slots)

/-- The segments to write when `a` and `b` fire. -/
def XRhs.newLinks (R : XRhs S) (ar : S → Nat) (a b : Id) (α β : S) : List (Port × Port) :=
  R.wiresFrom a b (ifcPorts ar α β ++ R.newPorts ar) fun _ => true

theorem XSys.writes (xs : XSys S) {a b : Id} {α β : S} {R : XRhs S} (hne : a ≠ b)
    (hr : xs.rule α β = some R) :
    xs.sys.rule α β = some R.toRhs ∧
      Writes a b R.toRhs (R.newAgents a b) (R.newLinks xs.sys.ar a b α β) := by
  have hs : xs.sys.rule α β = some R.toRhs := by
    rw [xs.rule_spec, hr]
    rfl
  have hwf := xs.sys.rule_wf hs
  have hsl : ∀ o j γ, R.lab o j = some γ → (o, j) ∈ R.slots :=
    fun o j γ hl => xs.slots_spec hr hl
  refine ⟨hs, ⟨fun {i γ} => ?_, dedupFst_nodup _, fun {p q} => ?_⟩⟩
  · exact (mem_dedupFst _ (childList_fun hne hsl) (i, γ)).trans (mem_childList hsl i γ)
  · show (p, q) ∈ R.wiresFrom a b _ _ ↔ _
    rw [XRhs.mem_wiresFrom]
    constructor
    · rintro ⟨x, -, y, hw, -, hp, hq⟩
      exact ⟨x, y, hw, hp, hq⟩
    · rintro ⟨x, y, hxy, hp, hq⟩
      refine ⟨x, ?_, y, hxy, rfl, hp, hq⟩
      have hv := hwf.valid hxy
      cases x with
      | ifc s k => exact List.mem_append_left _ (mem_ifcPorts.2 ⟨s, k, rfl, hv⟩)
      | new o j k =>
        obtain ⟨γ, hγ, hk⟩ := hv
        exact List.mem_append_right _
          (XRhs.mem_newPorts.2 ⟨o, j, k, γ, rfl, hsl o j γ hγ, hγ, hk⟩)

/-! ### Threads -/

/-- A thread of the program: the agents it has yet to try, and its state. -/
structure XThread (S : Type) where
  todo : List (Id × S)
  st : TState S

/-- The thread gives up an attempt. -/
def XThread.fail (T : XThread S) : XThread S := ⟨T.todo, .idle⟩

/-- The machine as data. -/
structure XMach (S : Type) where
  mem : XNet S
  ths : List (XThread S)

/-- The state of thread `t`; a thread that does not exist is idle. -/
def threadOf (ths : List (XThread S)) (t : Nat) : TState S :=
  match ths[t]? with
  | some T => T.st
  | none => .idle

/-- The machine it stands for. -/
def XMach.toMach (X : XMach S) : Mach S := ⟨X.mem.toNet, threadOf X.ths⟩

theorem threadOf_eq {ths : List (XThread S)} {t : Nat} {T : XThread S} (h : ths[t]? = some T) :
    threadOf ths t = T.st := by
  unfold threadOf
  rw [h]

theorem threadOf_set {ths : List (XThread S)} {t : Nat} {T : XThread S} (h : ths[t]? = some T)
    (T' : XThread S) : threadOf (ths.set t T') = upd (threadOf ths) t T'.st := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h
  funext u
  by_cases hu : u = t
  · rw [hu, upd_same]
    unfold threadOf
    rw [List.getElem?_set_self hlt]
  · rw [upd_ne _ _ hu]
    unfold threadOf
    rw [List.getElem?_set_ne (Ne.symm hu)]

theorem upd_self (th : Nat → TState S) (t : Nat) : upd th t (th t) = th := by
  funext u
  by_cases hu : u = t
  · rw [hu, upd_same]
  · rw [upd_ne _ _ hu]

/-! ### The program of a thread -/

variable [DecidableEq S]

/-- One action of a thread on the memory `X`: the new memory, the new state
of the thread, and `1` if the action completed a claim. -/
def XMach.act (xs : XSys S) (X : XNet S) (T : XThread S) : XNet S × XThread S × Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => (X, T, 0)
    | e :: rest =>
      if assoc e.1 X.agents = some e.2 then (X, ⟨rest, .look e.1 e.2⟩, 0)
      else (X, ⟨rest, .idle⟩, 0)
  | .look a α =>
    match assoc (a, 0) X.wires with
    | some q => (X, ⟨T.todo, .seek a α (a, 0) q⟩, 0)
    | none => (X, T.fail, 0)
  | .seek a α p c =>
    match (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some β =>
      if a ≠ c.1 ∧ (xs.rule α β).isSome then (X, ⟨T.todo, .ready a c.1 α β⟩, 0)
      else (X, T.fail, 0)
    | none =>
      match nextSeg X.wires c p with
      | some q => (X, ⟨T.todo, .seek a α c q⟩, 0)
      | none => (X, T.fail, 0)
  | .ready a b α β =>
    if assoc a X.agents = some α then (X.takeAgent a, ⟨T.todo, .half a b α β⟩, 0)
    else (X, T.fail, 0)
  | .half a b α β =>
    match (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (X.takeAgent b, ⟨T.todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1)
    | none => (X.putAgent a α, T.fail, 0)
  | .write ((i, γ) :: as) ls => (X.putAgent i γ, ⟨T.todo, .write as ls⟩, 0)
  | .write [] ((p, q) :: ls) => (X.putLink p q, ⟨T.todo, .write [] ls⟩, 0)
  | .write [] [] => (X, ⟨X.agents, .idle⟩, 0)

/-- **An action of the program is an action of the machine**, or changes
neither the memory nor the state of the thread. -/
theorem XMach.act_sim (xs : XSys S) (X : XNet S) (T : XThread S) (th : Nat → TState S)
    (t : Nat) (hs : th t = T.st) :
    ((XMach.act xs X T).1 = X ∧ (XMach.act xs X T).2.1.st = T.st ∧
        (XMach.act xs X T).2.2 = 0) ∨
      MStep xs.sys (XMach.act xs X T).2.2 ⟨X.toNet, th⟩
        ⟨(XMach.act xs X T).1.toNet, upd th t (XMach.act xs X T).2.1.st⟩ := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    have hs' : th t = .idle := hs
    cases todo with
    | nil => exact .inl ⟨rfl, rfl, rfl⟩
    | cons e rest =>
      unfold XMach.act
      dsimp only
      split
      · rename_i he
        exact .inr (.look (M := ⟨X.toNet, th⟩) hs' (assoc_mem he))
      · exact .inl ⟨rfl, rfl, rfl⟩
  | look a α =>
    have hs' : th t = .look a α := hs
    unfold XMach.act
    dsimp only
    split
    · rename_i q hq
      exact .inr (.first (M := ⟨X.toNet, th⟩) hs' (assoc_mem hq))
    · have hp : (th t).Passive := by
        rw [hs']
        trivial
      exact .inr (.quit (M := ⟨X.toNet, th⟩) (t := t) hp)
  | seek a α p c =>
    have hs' : th t = .seek a α p c := hs
    unfold XMach.act
    dsimp only
    split
    · rename_i β hβ
      split
      · split at hβ
        · rename_i hc
          have ec : c = (c.1, 0) := Prod.ext rfl hc
          have hs'' : th t = .seek a α p (c.1, 0) := by
            rw [← ec]
            exact hs'
          exact .inr (.found (M := ⟨X.toNet, th⟩) hs'' (assoc_mem hβ))
        · cases hβ
      · have hp : (th t).Passive := by
          rw [hs']
          trivial
        exact .inr (.quit (M := ⟨X.toNet, th⟩) (t := t) hp)
    · split
      · rename_i q hq
        obtain ⟨hl, hne⟩ := nextSeg_spec hq
        exact .inr (.next (M := ⟨X.toNet, th⟩) hs' hl hne)
      · have hp : (th t).Passive := by
          rw [hs']
          trivial
        exact .inr (.quit (M := ⟨X.toNet, th⟩) (t := t) hp)
  | ready a b α β =>
    have hs' : th t = .ready a b α β := hs
    unfold XMach.act
    dsimp only
    split
    · rename_i ha
      refine .inr ?_
      show MStep xs.sys 0 ⟨X.toNet, th⟩ ⟨(X.takeAgent a).toNet, upd th t (.half a b α β)⟩
      rw [XNet.takeAgent_toNet]
      exact .cas₁ (M := ⟨X.toNet, th⟩) hs' (assoc_mem ha)
    · have hp : (th t).Passive := by
        rw [hs']
        trivial
      exact .inr (.quit (M := ⟨X.toNet, th⟩) (t := t) hp)
  | half a b α β =>
    have hs' : th t = .half a b α β := hs
    unfold XMach.act
    dsimp only
    split
    · rename_i R hR
      split at hR
      · rename_i hc
        obtain ⟨hsys, hw⟩ := xs.writes hc.2 hR
        refine .inr ?_
        show MStep xs.sys 1 ⟨X.toNet, th⟩ ⟨(X.takeAgent b).toNet,
          upd th t (.write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β))⟩
        rw [XNet.takeAgent_toNet]
        exact .cas₂ (M := ⟨X.toNet, th⟩) hs' (assoc_mem hc.1) hc.2 hsys hw
      · cases hR
    · refine .inr ?_
      show MStep xs.sys 0 ⟨X.toNet, th⟩ ⟨(X.putAgent a α).toNet, upd th t .idle⟩
      rw [XNet.putAgent_toNet]
      exact .undo (M := ⟨X.toNet, th⟩) hs'
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have hs' : th t = .write ((i, γ) :: as) ls := hs
      refine .inr ?_
      show MStep xs.sys 0 ⟨X.toNet, th⟩ ⟨(X.putAgent i γ).toNet, upd th t (.write as ls)⟩
      rw [XNet.putAgent_toNet]
      exact .agent (M := ⟨X.toNet, th⟩) hs'
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have hs' : th t = .write [] ((p, q) :: ls) := hs
        refine .inr ?_
        show MStep xs.sys 0 ⟨X.toNet, th⟩ ⟨(X.putLink p q).toNet, upd th t (.write [] ls)⟩
        rw [XNet.putLink_toNet]
        exact .link (M := ⟨X.toNet, th⟩) hs'
      | nil =>
        have hs' : th t = .write [] [] := hs
        exact .inr (.done (M := ⟨X.toNet, th⟩) hs')

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def XMach.step (xs : XSys S) (X : XMach S) (t : Nat) : XMach S × Nat :=
  match X.ths[t]? with
  | some T =>
    (⟨(XMach.act xs X.mem T).1, X.ths.set t (XMach.act xs X.mem T).2.1⟩,
      (XMach.act xs X.mem T).2.2)
  | none => (X, 0)

theorem XMach.step_sim (xs : XSys S) (X : XMach S) (t : Nat) :
    ((X.step xs t).1.toMach = X.toMach ∧ (X.step xs t).2 = 0) ∨
      MStep xs.sys (X.step xs t).2 X.toMach (X.step xs t).1.toMach := by
  unfold XMach.step
  cases h : X.ths[t]? with
  | none => exact .inl ⟨rfl, rfl⟩
  | some T =>
    rcases XMach.act_sim xs X.mem T (threadOf X.ths) t (threadOf_eq h) with ⟨e₁, e₂, e₃⟩ | hs
    · refine .inl ⟨?_, e₃⟩
      show Mach.mk (XMach.act xs X.mem T).1.toNet
        (threadOf (X.ths.set t (XMach.act xs X.mem T).2.1)) = ⟨X.mem.toNet, threadOf X.ths⟩
      rw [threadOf_set h, e₁, e₂, ← threadOf_eq h, upd_self]
    · refine .inr ?_
      show MStep xs.sys _ ⟨X.mem.toNet, threadOf X.ths⟩ ⟨(XMach.act xs X.mem T).1.toNet,
        threadOf (X.ths.set t (XMach.act xs X.mem T).2.1)⟩
      rw [threadOf_set h]
      exact hs

/-- Run the threads in the order given by a schedule.  Returns the final
state and the number of claims. -/
def XMach.exec (xs : XSys S) : List Nat → XMach S → XMach S × Nat
  | [], X => (X, 0)
  | t :: ts, X =>
    ((XMach.exec xs ts (X.step xs t).1).1,
      (X.step xs t).2 + (XMach.exec xs ts (X.step xs t).1).2)

/-- The threads that make the claims of a run, in order. -/
def XMach.claimers (xs : XSys S) : List Nat → XMach S → List Nat
  | [], _ => []
  | t :: ts, X =>
    (if (X.step xs t).2 = 1 then [t] else []) ++ XMach.claimers xs ts (X.step xs t).1

/-- **A run of the program is an execution of the machine**, whatever the
schedule. -/
theorem XMach.exec_run (xs : XSys S) : ∀ (ts : List Nat) (X : XMach S),
    MRun xs.sys (X.exec xs ts).2 X.toMach (X.exec xs ts).1.toMach
  | [], X => .refl _
  | t :: ts, X => by
    have ih := XMach.exec_run xs ts (X.step xs t).1
    show MRun xs.sys ((X.step xs t).2 + (XMach.exec xs ts (X.step xs t).1).2) X.toMach
      (XMach.exec xs ts (X.step xs t).1).1.toMach
    rcases XMach.step_sim xs X t with ⟨e₁, e₂⟩ | hs
    · rw [e₂, Nat.zero_add, ← e₁]
      exact ih
    · exact .step hs ih

/-- The program before it starts: `n` idle threads.  Each has all the agents
to try, and thread `t` starts with the `t`-th. -/
def XMach.init (X : XNet S) (n : Nat) : XMach S :=
  ⟨X, (List.range n).map fun t => ⟨X.agents.drop t ++ X.agents.take t, .idle⟩⟩

omit [DecidableEq S] in
theorem XMach.init_toMach (X : XNet S) (n : Nat) :
    (XMach.init X n).toMach = Mach.init X.toNet := by
  refine congrArg (Mach.mk X.toNet) (funext fun u => ?_)
  show threadOf ((List.range n).map fun t =>
    (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S)) u = .idle
  unfold threadOf
  split
  · rename_i T hT
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hT)
    rfl
  · rfl

def TState.isIdle : TState S → Bool
  | .idle => true
  | _ => false

/-- Every thread is idle. -/
def XMach.quiet (X : XMach S) : Bool := X.ths.all fun T => T.st.isIdle

omit [DecidableEq S] in
theorem XMach.quiet_toMach {X : XMach S} (h : X.quiet = true) : X.toMach.Quiet := by
  intro u
  show threadOf X.ths u = .idle
  unfold threadOf
  split
  · rename_i T hT
    have hi : T.st.isIdle = true := List.all_eq_true.1 h T (List.mem_of_getElem? hT)
    cases hst : T.st with
    | idle => rfl
    | look a α => rw [hst] at hi; cases hi
    | seek a α p c => rw [hst] at hi; cases hi
    | ready a b α β => rw [hst] at hi; cases hi
    | half a b α β => rw [hst] at hi; cases hi
    | write as ls => rw [hst] at hi; cases hi
  · rfl

/-- A run from a net, with `n` threads, is an execution of the machine from
that net. -/
theorem XMach.exec_mrun (xs : XSys S) (X : XNet S) (n : Nat) (σ : List Nat) :
    MRun xs.sys ((XMach.init X n).exec xs σ).2 (Mach.init X.toNet)
      ((XMach.init X n).exec xs σ).1.toMach := by
  have h := XMach.exec_run xs σ (XMach.init X n)
  rw [XMach.init_toMach] at h
  exact h

/-- **The program agrees with the list reducer.**  If a run ends with every
thread idle after as many claims as the list reducer took steps, then the
memory holds a normal form, and with its history forgotten it is the net
that the list reducer returned.  Both hypotheses can be evaluated. -/
theorem XMach.exec_agrees {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) {n : Nat} {σ : List Nat}
    (hq : ((XMach.init X n).exec xs σ).1.quiet = true)
    (hk : ((XMach.init X n).exec xs σ).2 = (X.run xs f).2) :
    Normal (Step xs.sys) ((XMach.init X n).exec xs σ).1.mem.toNet ∧
      ((XMach.init X n).exec xs σ).1.mem.toNet.compact xs.sys.ar = (X.run xs f).1.toNet := by
  have hr := XMach.exec_mrun xs X n σ
  have sts := hr.quiet hX.1 (XMach.quiet_toMach hq)
  have hwf := Steps.wf hX.1 sts
  have cs := Steps.cstep hX.1 sts
  rw [hX.2, hk] at cs
  have e := XNet.run_agree hX f stop cs
  refine ⟨(normal_compact hwf).2 ?_, e⟩
  rw [e]
  exact (XNet.run_normal hX f stop).1

/-- No run makes more claims than the list reducer takes steps. -/
theorem XMach.exec_le {xs : XSys S} {X : XNet S} (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) (n : Nat) (σ : List Nat) :
    ((XMach.init X n).exec xs σ).2 ≤ (X.run xs f).2 := by
  have sts := (XMach.exec_mrun xs X n σ).sequential hX.1
  have cs := Steps.cstep hX.1 sts
  rw [hX.2] at cs
  exact ((XNet.run_normal hX f stop).2 cs).1

end XMachine

/-! ### One thread alone

The theorems above say that a run of the program is safe.  This section
shows that a run ends when one thread runs alone: on a net that has a normal
form, the thread makes the claims of the sequential reduction, leaves the
normal form in memory and rests. -/

section Solo

theorem ite_pos' {c : Prop} [Decidable c] {A : Type} {x y : A} (h : c) :
    (if c then x else y) = x := by
  split
  · rfl
  · rename_i hn
    exact absurd h hn

theorem ite_neg' {c : Prop} [Decidable c] {A : Type} {x y : A} (h : ¬ c) :
    (if c then x else y) = y := by
  split
  · rename_i hp
    exact absurd hp h
  · rfl

theorem assoc_eq_of_unique {A B : Type} [DecidableEq A] {p : A} {q : B} {l : List (A × B)}
    (h : (p, q) ∈ l) (hu : ∀ q', (p, q') ∈ l → q' = q) : assoc p l = some q := by
  obtain ⟨q', e⟩ := assoc_of_mem h
  rw [e, hu q' (assoc_mem e)]

theorem XNet.mem_takeAgent {X : XNet S} {a : Id} {e : Id × S} :
    e ∈ (X.takeAgent a).agents ↔ e ∈ X.agents ∧ e.1 ≠ a := by
  show e ∈ X.agents.filter _ ↔ _
  rw [List.mem_filter]
  exact and_congr Iff.rfl decide_eq_true_iff

theorem nextSeg_some : ∀ {ws : List (Port × Port)} {c p w : Port}, (c, w) ∈ ws → w ≠ p →
    (∀ q, (c, q) ∈ ws → q ≠ p → q = w) → nextSeg ws c p = some w
  | [], _, _, _, h, _, _ => absurd h List.not_mem_nil
  | e :: ws, c, p, w, h, hw, hu => by
    unfold nextSeg
    split
    · rename_i hc
      exact congrArg some (hu e.2 (List.mem_cons.2 (.inl (Prod.ext hc.1.symm rfl))) hc.2)
    · rename_i hc
      rcases List.mem_cons.1 h with he | h'
      · have h1 : e.1 = c := congrArg Prod.fst he.symm
        have h2 : e.2 = w := congrArg Prod.snd he.symm
        exact absurd ⟨h1, fun h3 => hw (h2 ▸ h3)⟩ hc
      · exact nextSeg_some h' hw fun q hq hqp => hu q (List.mem_cons_of_mem _ hq) hqp

theorem nextSeg_none : ∀ {ws : List (Port × Port)} {c p : Port},
    (∀ q, (c, q) ∈ ws → q = p) → nextSeg ws c p = none
  | [], _, _, _ => rfl
  | e :: ws, c, p, hu => by
    unfold nextSeg
    split
    · rename_i hc
      exact absurd (hu e.2 (List.mem_cons.2 (.inl (Prod.ext hc.1.symm rfl)))) hc.2
    · exact nextSeg_none fun q hq => hu q (List.mem_cons_of_mem _ hq)

variable [DecidableEq S] {xs : XSys S} {X : XNet S}

/-! #### What each action does -/

theorem XMach.act_idle_pos {e : Id × S} {rest : List (Id × S)}
    (h : assoc e.1 X.agents = some e.2) :
    XMach.act xs X ⟨e :: rest, .idle⟩ = (X, ⟨rest, .look e.1 e.2⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rfl
  · rename_i hn
    exact absurd h hn

theorem XMach.act_idle_neg {e : Id × S} {rest : List (Id × S)}
    (h : ¬ assoc e.1 X.agents = some e.2) :
    XMach.act xs X ⟨e :: rest, .idle⟩ = (X, ⟨rest, .idle⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i hp
    exact absurd hp h
  · rfl

theorem XMach.act_look {todo : List (Id × S)} {a : Id} {α : S} {q : Port}
    (h : assoc (a, 0) X.wires = some q) :
    XMach.act xs X ⟨todo, .look a α⟩ = (X, ⟨todo, .seek a α (a, 0) q⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i q' hq'
    rw [h] at hq'
    cases hq'
    rfl
  · rename_i hq'
    rw [h] at hq'
    cases hq'

theorem XMach.act_seek_next {todo : List (Id × S)} {a : Id} {α : S} {p c q : Port}
    (h₁ : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂ : nextSeg X.wires c p = some q) :
    XMach.act xs X ⟨todo, .seek a α p c⟩ = (X, ⟨todo, .seek a α c q⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i β hβ
    rw [h₁] at hβ
    cases hβ
  · split
    · rename_i q' hq'
      rw [h₂] at hq'
      cases hq'
      rfl
    · rename_i hq'
      rw [h₂] at hq'
      cases hq'

theorem XMach.act_seek_stop {todo : List (Id × S)} {a : Id} {α : S} {p c : Port}
    (h₁ : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂ : nextSeg X.wires c p = none) :
    XMach.act xs X ⟨todo, .seek a α p c⟩ = (X, ⟨todo, .idle⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i β hβ
    rw [h₁] at hβ
    cases hβ
  · split
    · rename_i q' hq'
      rw [h₂] at hq'
      cases hq'
    · rfl

theorem XMach.act_seek_found {todo : List (Id × S)} {a : Id} {α β : S} {p c : Port}
    (h₁ : (if c.2 = 0 then assoc c.1 X.agents else none) = some β)
    (h₂ : a ≠ c.1 ∧ (xs.rule α β).isSome) :
    XMach.act xs X ⟨todo, .seek a α p c⟩ = (X, ⟨todo, .ready a c.1 α β⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i β' hβ'
    rw [h₁] at hβ'
    cases hβ'
    split
    · rfl
    · rename_i hn
      exact absurd h₂ hn
  · rename_i hβ'
    rw [h₁] at hβ'
    cases hβ'

theorem XMach.act_seek_norule {todo : List (Id × S)} {a : Id} {α β : S} {p c : Port}
    (h₁ : (if c.2 = 0 then assoc c.1 X.agents else none) = some β)
    (h₂ : ¬ (a ≠ c.1 ∧ (xs.rule α β).isSome)) :
    XMach.act xs X ⟨todo, .seek a α p c⟩ = (X, ⟨todo, .idle⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i β' hβ'
    rw [h₁] at hβ'
    cases hβ'
    split
    · rename_i hp
      exact absurd hp h₂
    · rfl
  · rename_i hβ'
    rw [h₁] at hβ'
    cases hβ'

theorem XMach.act_ready {todo : List (Id × S)} {a b : Id} {α β : S}
    (h : assoc a X.agents = some α) :
    XMach.act xs X ⟨todo, .ready a b α β⟩ = (X.takeAgent a, ⟨todo, .half a b α β⟩, 0) := by
  unfold XMach.act
  dsimp only
  split
  · rfl
  · rename_i hn
    exact absurd h hn

theorem XMach.act_half {todo : List (Id × S)} {a b : Id} {α β : S} {R : XRhs S}
    (h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    XMach.act xs X ⟨todo, .half a b α β⟩ = (X.takeAgent b,
      ⟨todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) := by
  unfold XMach.act
  dsimp only
  split
  · rename_i R' hR'
    rw [h] at hR'
    cases hR'
    rfl
  · rename_i hR'
    rw [h] at hR'
    cases hR'

/-! #### Runs of one thread -/

/-- `Runs xs X T X' T' c k`: from memory `X` and thread `T`, the thread
running alone reaches memory `X'` and state `T'` in `k` actions, `c` of
which complete a claim. -/
inductive Runs (xs : XSys S) : XNet S → XThread S → XNet S → XThread S → Nat → Nat → Prop
  | refl (X : XNet S) (T : XThread S) : Runs xs X T X T 0 0
  | step {X X₁ X' : XNet S} {T T₁ T' : XThread S} {c₁ c k : Nat} :
      XMach.act xs X T = (X₁, T₁, c₁) → Runs xs X₁ T₁ X' T' c k →
      Runs xs X T X' T' (c₁ + c) (k + 1)

theorem Runs.trans {X₁ X₂ : XNet S} {T T₁ T₂ : XThread S} {c₁ c₂ k₁ k₂ : Nat}
    (r₁ : Runs xs X T X₁ T₁ c₁ k₁) (r₂ : Runs xs X₁ T₁ X₂ T₂ c₂ k₂) :
    Runs xs X T X₂ T₂ (c₁ + c₂) (k₁ + k₂) := by
  induction r₁ with
  | refl X T =>
    rw [Nat.zero_add, Nat.zero_add]
    exact r₂
  | step h _ ih =>
    rw [Nat.add_assoc, Nat.add_right_comm]
    exact .step h (ih r₂)

/-- A run of one thread is a run of the program under the schedule that
names that thread only. -/
theorem Runs.exec {X' : XNet S} {T T' : XThread S} {c k : Nat} (r : Runs xs X T X' T' c k) :
    XMach.exec xs (List.replicate k 0) ⟨X, [T]⟩ = (⟨X', [T']⟩, c) := by
  induction r with
  | refl X T => rfl
  | @step X X₁ X' T T₁ T' c₁ c k h _ ih =>
    have es : XMach.step xs ⟨X, [T]⟩ 0 = (⟨X₁, [T₁]⟩, c₁) := by
      show ((⟨(XMach.act xs X T).1, [(XMach.act xs X T).2.1]⟩ : XMach S),
        (XMach.act xs X T).2.2) = _
      rw [h]
    show ((XMach.exec xs (List.replicate k 0) (XMach.step xs ⟨X, [T]⟩ 0).1).1,
      (XMach.step xs ⟨X, [T]⟩ 0).2 +
        (XMach.exec xs (List.replicate k 0) (XMach.step xs ⟨X, [T]⟩ 0).1).2) = _
    rw [es, ih]

/-- A thread whose list is empty rests. -/
theorem Runs.rest (xs : XSys S) (X : XNet S) : ∀ k, Runs xs X ⟨[], .idle⟩ X ⟨[], .idle⟩ 0 k
  | 0 => .refl _ _
  | k + 1 => .step (c₁ := 0) rfl (Runs.rest xs X k)

theorem Runs.flush_links (xs : XSys S) (todo : List (Id × S)) :
    ∀ (ls : List (Port × Port)) (X : XNet S),
      ∃ k X', Runs xs X ⟨todo, .write [] ls⟩ X' ⟨X'.agents, .idle⟩ 0 k ∧
        X'.agents = X.agents ∧ (∀ e, e ∈ X'.wires ↔ e ∈ X.wires ∨ e ∈ ls) ∧ X'.free = X.free
  | [], X =>
    ⟨1, X, .step (c₁ := 0) rfl (.refl _ _), rfl,
      fun _ => ⟨fun h => .inl h, fun h => h.elim id fun x => absurd x List.not_mem_nil⟩, rfl⟩
  | (p, q) :: ls, X => by
    obtain ⟨k, X', r, hA, hW, hF⟩ := Runs.flush_links xs todo ls (X.putLink p q)
    refine ⟨k + 1, X', .step (c₁ := 0) rfl r, hA, fun e => ?_, hF⟩
    rw [hW]
    show (e ∈ (p, q) :: X.wires ∨ e ∈ ls) ↔ e ∈ X.wires ∨ e ∈ (p, q) :: ls
    rw [List.mem_cons, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h

/-- The thread writes everything it has left to write, and takes a fresh
copy of the list of agents. -/
theorem Runs.flush (xs : XSys S) (todo : List (Id × S)) (ls : List (Port × Port)) :
    ∀ (as : List (Id × S)) (X : XNet S),
      ∃ k X', Runs xs X ⟨todo, .write as ls⟩ X' ⟨X'.agents, .idle⟩ 0 k ∧
        (∀ e, e ∈ X'.agents ↔ e ∈ X.agents ∨ e ∈ as) ∧
        (∀ e, e ∈ X'.wires ↔ e ∈ X.wires ∨ e ∈ ls) ∧ X'.free = X.free
  | [], X => by
    obtain ⟨k, X', r, hA, hW, hF⟩ := Runs.flush_links xs todo ls X
    refine ⟨k, X', r, fun e => ?_, hW, hF⟩
    rw [hA]
    exact ⟨fun h => .inl h, fun h => h.elim id fun x => absurd x List.not_mem_nil⟩
  | (i, γ) :: as, X => by
    obtain ⟨k, X', r, hA, hW, hF⟩ := Runs.flush xs todo ls as (X.putAgent i γ)
    refine ⟨k + 1, X', .step (c₁ := 0) rfl r, fun e => ?_, hW, hF⟩
    rw [hA]
    show (e ∈ (i, γ) :: X.agents ∨ e ∈ as) ↔ e ∈ X.agents ∨ e ∈ (i, γ) :: as
    rw [List.mem_cons, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h

/-- The thread follows a wire to its end. -/
theorem Runs.follow (hX : X.toNet.WF xs.sys.ar) {todo : List (Id × S)} {a : Id} {α : S}
    {p c x y : Port} (w : Walk X.toNet.link (X.toNet.End xs.sys.ar) p c x y) :
    ∃ k, Runs xs X ⟨todo, .seek a α p c⟩ X ⟨todo, .seek a α x y⟩ 0 k := by
  induction w with
  | single h => exact ⟨0, .refl _ _⟩
  | @cons u v w' x y h hT hne w ih =>
    obtain ⟨k, r⟩ := ih
    have h₁ : (if v.2 = 0 then assoc v.1 X.agents else none) = none := by
      split
      · rename_i hv
        cases ha : assoc v.1 X.agents with
        | none => rfl
        | some β =>
          exact absurd (.inr ⟨β, assoc_mem ha, by rw [hv]; exact Nat.zero_le _⟩) hT
      · rfl
    have h₂ : nextSeg X.wires v u = some w' := by
      refine nextSeg_some w.link_first hne fun q hq hqu => ?_
      rcases hX.deg (hX.symm h) w.link_first hq with e | e | e
      · exact absurd e.symm hne
      · exact absurd e.symm hqu
      · exact e.symm
    exact ⟨k + 1, .step (XMach.act_seek_next h₁ h₂) r⟩

/-- **One attempt.**  From an agent of a well-formed memory, the thread
either comes back empty-handed, and then the agent is in no active pair
with a rule, or fires the pair of that agent and is idle again with a fresh
list of agents. -/
theorem Runs.attempt (hX : X.toNet.WF xs.sys.ar) (todo : List (Id × S)) {a : Id} {α : S}
    (ha : (a, α) ∈ X.agents) :
    (∃ k, Runs xs X ⟨todo, .look a α⟩ X ⟨todo, .idle⟩ 0 k ∧
        ∀ b β R, ¬ Redex xs.sys X.toNet a b α β R) ∨
      ∃ k X', Runs xs X ⟨todo, .look a α⟩ X' ⟨X'.agents, .idle⟩ 1 k ∧
        Step xs.sys X.toNet X'.toNet := by
  have hEa : X.toNet.End xs.sys.ar (a, 0) := .inr ⟨α, ha, Nat.zero_le _⟩
  obtain ⟨⟨qb, qk⟩, hEq, -, v, x, w⟩ := hX.end_conn hEa
  have hv : assoc (a, 0) X.wires = some v :=
    assoc_eq_of_unique w.link_first fun q' hq' => hX.end_unique hEa hq' w.link_first
  obtain ⟨k₁, r₁⟩ := Runs.follow hX (todo := todo) (a := a) (α := α) w
  have r₀ : Runs xs X ⟨todo, .look a α⟩ X ⟨todo, .seek a α x (qb, qk)⟩ 0 (k₁ + 1) :=
    .step (XMach.act_look hv) r₁
  have key : ∀ b β R, Redex xs.sys X.toNet a b α β R → (qb, qk) = (b, 0) := fun b β R r =>
    Net.Conn.det hX hEa hEq (.inr ⟨β, r.hb, Nat.zero_le _⟩) ⟨v, x, w⟩ r.conn
  cases hsc : (if qk = 0 then assoc qb X.agents else none) with
  | none =>
    have hstop : nextSeg X.wires (qb, qk) x = none :=
      nextSeg_none fun z hz => hX.end_unique hEq hz (hX.symm w.link_last)
    refine .inl ⟨_, r₀.trans (.step (XMach.act_seek_stop hsc hstop) (.refl _ _)), ?_⟩
    intro b β R r
    obtain ⟨e₁, e₂⟩ := Prod.mk.inj (key b β R r)
    rw [ite_pos' e₂, e₁] at hsc
    obtain ⟨β', hβ'⟩ := assoc_of_mem r.hb
    rw [hβ'] at hsc
    cases hsc
  | some β =>
    have hq : qk = 0 ∧ assoc qb X.agents = some β := by
      split at hsc
      · rename_i h0
        exact ⟨h0, hsc⟩
      · cases hsc
    obtain ⟨hk0, hqb⟩ := hq
    subst hk0
    have hb : (qb, β) ∈ X.agents := assoc_mem hqb
    by_cases hc : a ≠ qb ∧ (xs.rule α β).isSome
    · cases hR : xs.rule α β with
      | none =>
        rw [hR] at hc
        cases hc.2
      | some R =>
        obtain ⟨hsys, hw⟩ := xs.writes hc.1 hR
        have ha' : assoc a X.agents = some α :=
          assoc_eq_of_unique ha fun α' h' => hX.agent_fun h' ha
        have hb' : assoc qb (X.takeAgent a).agents = some β :=
          assoc_eq_of_unique (XNet.mem_takeAgent.2 ⟨hb, fun e => hc.1 e.symm⟩)
            fun β' h' => hX.agent_fun (XNet.mem_takeAgent.1 h').1 hb
        have hh : (if assoc qb (X.takeAgent a).agents = some β ∧ a ≠ qb then xs.rule α β
            else none) = some R := by
          rw [ite_pos' ⟨hb', hc.1⟩]
          exact hR
        obtain ⟨k₃, X', r₃, hA, hW, hF⟩ := Runs.flush xs todo
          (R.newLinks xs.sys.ar a qb α β) (R.newAgents a qb) ((X.takeAgent a).takeAgent qb)
        have hF' : X'.free = X.free := hF
        refine .inr ⟨_, X', r₀.trans (.step (XMach.act_seek_found hsc hc)
          (.step (XMach.act_ready ha') (.step (XMach.act_half hh) r₃))), ?_⟩
        refine ⟨a, qb, α, β, R.toRhs, ⟨ha, hb, hc.1, ⟨v, x, w⟩, hsys⟩, ?_⟩
        apply Net.ext'
        · intro i γ
          show (i, γ) ∈ X'.agents ↔ ((i, γ) ∈ X.agents ∧ i ≠ a ∧ i ≠ qb) ∨
            ∃ o j, i = child a qb o j ∧ R.toRhs.lab o j = some γ
          rw [hA]
          constructor
          · rintro (h | h)
            · obtain ⟨h₁, h₂⟩ := XNet.mem_takeAgent.1 h
              obtain ⟨h₃, h₄⟩ := XNet.mem_takeAgent.1 h₁
              exact .inl ⟨h₃, h₄, h₂⟩
            · exact .inr (hw.agent.1 h)
          · rintro (⟨h₁, h₂, h₃⟩ | h)
            · exact .inl (XNet.mem_takeAgent.2 ⟨XNet.mem_takeAgent.2 ⟨h₁, h₂⟩, h₃⟩)
            · exact .inr (hw.agent.2 h)
        · intro p q
          show (p, q) ∈ X'.wires ↔ (p, q) ∈ X.wires ∨
            ∃ x y, R.toRhs.link x y ∧ p = emb a qb x ∧ q = emb a qb y
          rw [hW]
          constructor
          · rintro (h | h)
            · exact .inl h
            · exact .inr (hw.link.1 h)
          · rintro (h | h)
            · exact .inl h
            · exact .inr (hw.link.2 h)
        · intro p
          show p ∈ X'.free ↔ p ∈ X.free
          rw [hF']
    · refine .inl ⟨_, r₀.trans (.step (XMach.act_seek_norule hsc hc) (.refl _ _)), ?_⟩
      intro b β' R r
      obtain ⟨e₁, -⟩ := Prod.mk.inj (key b β' R r)
      have eβ : β' = β := hX.agent_fun r.hb (e₁ ▸ hb)
      apply hc
      refine ⟨e₁ ▸ r.ne, ?_⟩
      have hr := r.rule
      rw [xs.rule_spec, eβ] at hr
      cases hx : xs.rule α β with
      | none =>
        rw [hx] at hr
        cases hr
      | some R' => rfl

/-- **One pass.**  A thread that is idle on a well-formed memory, and has
in its list every agent that it has not yet found to be in no active pair,
either empties its list, and then the memory is normal, or fires a pair. -/
theorem Runs.pass (hX : X.toNet.WF xs.sys.ar) : ∀ (todo : List (Id × S)),
    (∀ a α, (a, α) ∈ X.agents →
      (a, α) ∈ todo ∨ ∀ b β R, ¬ Redex xs.sys X.toNet a b α β R) →
    (∃ k, Runs xs X ⟨todo, .idle⟩ X ⟨[], .idle⟩ 0 k ∧ Normal (Step xs.sys) X.toNet) ∨
      ∃ k X', Runs xs X ⟨todo, .idle⟩ X' ⟨X'.agents, .idle⟩ 1 k ∧
        Step xs.sys X.toNet X'.toNet
  | [], h => by
    refine .inl ⟨0, .refl _ _, ?_⟩
    rintro N' ⟨a, b, α, β, R, r, -⟩
    rcases h a α r.ha with hm | hno
    · exact absurd hm List.not_mem_nil
    · exact hno b β R r
  | e :: rest, h => by
    by_cases he : assoc e.1 X.agents = some e.2
    · rcases Runs.attempt hX rest (assoc_mem he) with ⟨k, r, hn⟩ | ⟨k, X', r, hs⟩
      · have inv : ∀ a α, (a, α) ∈ X.agents →
            (a, α) ∈ rest ∨ ∀ b β R, ¬ Redex xs.sys X.toNet a b α β R := by
          intro a α ha
          rcases h a α ha with hm | hno
          · rcases List.mem_cons.1 hm with heq | hm
            · obtain ⟨e₁, e₂⟩ := Prod.mk.inj (show (a, α) = (e.1, e.2) from heq)
              rw [e₁, e₂]
              exact .inr hn
            · exact .inl hm
          · exact .inr hno
        rcases Runs.pass hX rest inv with ⟨k', r', hnorm⟩ | ⟨k', X', r', hs⟩
        · exact .inl ⟨_, (Runs.step (XMach.act_idle_pos he) r).trans r', hnorm⟩
        · exact .inr ⟨_, X', (Runs.step (XMach.act_idle_pos he) r).trans r', hs⟩
      · exact .inr ⟨_, X', .step (XMach.act_idle_pos he) r, hs⟩
    · have inv : ∀ a α, (a, α) ∈ X.agents →
          (a, α) ∈ rest ∨ ∀ b β R, ¬ Redex xs.sys X.toNet a b α β R := by
        intro a α ha
        rcases h a α ha with hm | hno
        · rcases List.mem_cons.1 hm with heq | hm
          · obtain ⟨e₁, e₂⟩ := Prod.mk.inj (show (a, α) = (e.1, e.2) from heq)
            rw [e₁, e₂] at ha
            exact absurd (assoc_eq_of_unique ha fun α' h' => hX.agent_fun h' ha) he
          · exact .inl hm
        · exact .inr hno
      rcases Runs.pass hX rest inv with ⟨k', r', hnorm⟩ | ⟨k', X', r', hs⟩
      · exact .inl ⟨_, .step (XMach.act_idle_neg he) r', hnorm⟩
      · exact .inr ⟨_, X', .step (XMach.act_idle_neg he) r', hs⟩

/-- The thread goes on until the memory is normal. -/
theorem Runs.run : ∀ (m : Nat) (X : XNet S) (todo : List (Id × S)) (N' : Net S),
    X.toNet.WF xs.sys.ar →
    (∀ a α, (a, α) ∈ X.agents →
      (a, α) ∈ todo ∨ ∀ b β R, ¬ Redex xs.sys X.toNet a b α β R) →
    Steps (Step xs.sys) m X.toNet N' → Normal (Step xs.sys) N' →
    ∃ k X', Runs xs X ⟨todo, .idle⟩ X' ⟨[], .idle⟩ m k ∧ X'.toNet = N'
  | m, X, todo, N', hX, inv, hs, hn => by
    rcases Runs.pass hX todo inv with ⟨k, r, hnorm⟩ | ⟨k, X₁, r, hstep⟩
    · obtain ⟨e₁, e₂⟩ := Steps.of_normal hnorm hs
      subst e₁
      exact ⟨k, X, r, e₂⟩
    · obtain ⟨hle, rest⟩ := reduction_bounded hX hs hn (Steps.single hstep)
      obtain ⟨k', X', r', e⟩ := Runs.run (m - 1) X₁ X₁.agents N' (Step.wf hX hstep)
        (fun a α ha => .inl ha) rest hn
      have h := r.trans r'
      have em : 1 + (m - 1) = m := by omega
      rw [em] at h
      exact ⟨k + k', X', h, e⟩
  termination_by m => m
  decreasing_by omega

/-- **One thread alone computes the normal form.**  On a well-formed net
that has a normal form, reached in `n` steps, the program run with a single
thread ends: after some number of actions, and for ever after, the thread is
idle, it has made `n` claims, and the memory holds the normal form. -/
theorem XMach.solo_complete (hX : X.toNet.WF xs.sys.ar) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') :
    ∃ L, ∀ L', L ≤ L' →
      ((XMach.init X 1).exec xs (List.replicate L' 0)).1.quiet = true ∧
        ((XMach.init X 1).exec xs (List.replicate L' 0)).2 = n ∧
        ((XMach.init X 1).exec xs (List.replicate L' 0)).1.mem.toNet = N' := by
  obtain ⟨k, X', r, e⟩ := Runs.run n X (X.agents.drop 0 ++ X.agents.take 0) N' hX
    (fun a α ha => .inl (List.mem_append_left _ ha)) hs hn
  refine ⟨k, fun L' hL => ?_⟩
  have r' := r.trans (Runs.rest xs X' (L' - k))
  have eL : k + (L' - k) = L' := by omega
  rw [Nat.add_zero, eL] at r'
  have ei : XMach.init X 1 = ⟨X, [⟨X.agents.drop 0 ++ X.agents.take 0, .idle⟩]⟩ := rfl
  rw [ei, r'.exec]
  exact ⟨rfl, rfl, e⟩

/-- **One thread alone computes what the list reducer computes**, with as
many claims as the reducer takes steps. -/
theorem XMach.solo_agrees (hX : X.Ok xs.sys.ar) {f : Nat}
    (stop : (X.run xs f).1.step xs = none) :
    ∃ L, ∀ L', L ≤ L' →
      ((XMach.init X 1).exec xs (List.replicate L' 0)).1.quiet = true ∧
        ((XMach.init X 1).exec xs (List.replicate L' 0)).2 = (X.run xs f).2 ∧
        ((XMach.init X 1).exec xs (List.replicate L' 0)).1.mem.toNet.compact xs.sys.ar =
          (X.run xs f).1.toNet := by
  obtain ⟨sts, -⟩ := XNet.run_steps hX f
  have hn := (XNet.run_normal hX f stop).1
  have sts' : Steps (CStep xs.sys) (X.run xs f).2 (X.toNet.compact xs.sys.ar)
      (X.run xs f).1.toNet := by
    rw [hX.2]
    exact sts
  obtain ⟨N', hs, e⟩ := Steps.lift hX.1 sts'
  have hN' : Normal (Step xs.sys) N' := by
    refine (normal_compact (Steps.wf hX.1 hs)).2 ?_
    rw [← e]
    exact hn
  obtain ⟨L, hL⟩ := XMach.solo_complete hX.1 hs hN'
  refine ⟨L, fun L' h => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hL L' h
  refine ⟨h₁, h₂, ?_⟩
  rw [h₃]
  exact e.symm

end Solo

/-! ### Threads taking turns

One thread alone ends.  So do several, when they take turns: a turn is one
attempt of one thread, run to its end while the others wait.  Whatever the
order of the turns, a turn of a thread whose list is not empty fires a pair
or shortens that list; and as long as every thread keeps getting turns, the
threads all come to rest, with the normal form in memory. -/

section Turns

theorem strong_ind {P : Nat → Prop} (h : ∀ n, (∀ m, m < n → P m) → P n) (n : Nat) : P n := by
  have aux : ∀ k m, m < k → P m := by
    intro k
    induction k with
    | zero =>
      intro m hm
      omega
    | succ k ih =>
      intro m hm
      exact h m fun l hl => ih l (by omega)
  exact aux (n + 1) n (by omega)

/-- Two numbers that at each step stay as they are, or of which the first
decreases, or the second decreases while the first stays, stay as they are
from some step on. -/
theorem lex_settles (a b : Nat → Nat) (still : Nat → Prop)
    (h : ∀ i, (still i ∧ a (i + 1) = a i ∧ b (i + 1) = b i) ∨ a (i + 1) < a i ∨
      (a (i + 1) = a i ∧ b (i + 1) < b i)) :
    ∃ i₀, ∀ i, i₀ ≤ i → still i := by
  have mono : ∀ i d, a (i + d) < a i ∨ (a (i + d) = a i ∧ b (i + d) ≤ b i) := by
    intro i d
    induction d with
    | zero => exact .inr ⟨rfl, Nat.le_refl _⟩
    | succ d ih =>
      show a (i + d + 1) < a i ∨ (a (i + d + 1) = a i ∧ b (i + d + 1) ≤ b i)
      have := h (i + d)
      omega
  have key : ∀ A B i, a i = A → b i = B → ∃ i₀, ∀ j, i₀ ≤ j → still j := by
    intro A
    refine strong_ind (P := fun A => ∀ B i, a i = A → b i = B → ∃ i₀, ∀ j, i₀ ≤ j → still j)
      (fun A ihA => ?_) A
    intro B
    refine strong_ind (P := fun B => ∀ i, a i = A → b i = B → ∃ i₀, ∀ j, i₀ ≤ j → still j)
      (fun B ihB => ?_) B
    intro i hA hB
    by_cases hall : ∀ j, i ≤ j → still j
    · exact ⟨i, hall⟩
    · obtain ⟨j, hj⟩ := Classical.not_forall.1 hall
      have hij : i ≤ j := Classical.byContradiction fun hn => hj fun h' => absurd h' hn
      have hns : ¬ still j := fun hs => hj fun _ => hs
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
      have hm := mono i d
      rcases h (i + d) with ⟨hs, -, -⟩ | h1 | ⟨e1, h1⟩
      · exact absurd hs hns
      · exact ihA (a (i + d + 1)) (by omega) _ _ rfl rfl
      · rcases hm with m1 | ⟨m1, m2⟩
        · exact ihA (a (i + d + 1)) (by omega) _ _ rfl rfl
        · exact ihB (b (i + d + 1)) (by omega) (i + d + 1) (by omega) rfl
  exact key (a 0) (b 0) 0 rfl rfl

theorem set_self {A : Type} : ∀ (l : List A) (t : Nat) (x : A), l[t]? = some x → l.set t x = l
  | [], _, _, _ => rfl
  | y :: l, 0, x, h => by
    rw [List.getElem?_cons_zero] at h
    rw [Option.some.inj h]
    rfl
  | y :: l, t + 1, x, h => by
    rw [List.getElem?_cons_succ] at h
    exact congrArg (y :: ·) (set_self l t x h)

/-- The lengths of the lists of the threads, added up. -/
def load : List (XThread S) → Nat
  | [] => 0
  | T :: ths => T.todo.length + load ths

theorem load_set : ∀ (ths : List (XThread S)) (t : Nat) (T T' : XThread S), ths[t]? = some T →
    load (ths.set t T') + T.todo.length = load ths + T'.todo.length
  | [], _, _, _, h => by cases h
  | U :: ths, 0, T, T', h => by
    rw [List.getElem?_cons_zero] at h
    rw [Option.some.inj h]
    show T'.todo.length + load ths + T.todo.length = T.todo.length + load ths + T'.todo.length
    omega
  | U :: ths, t + 1, T, T', h => by
    rw [List.getElem?_cons_succ] at h
    have ih := load_set ths t T T' h
    show U.todo.length + load (ths.set t T') + T.todo.length =
      U.todo.length + load ths + T'.todo.length
    omega

variable {xs : XSys S}

/-- The list covers the memory: every agent is in the list, or is in no
active pair that has a rule. -/
def Covers (xs : XSys S) (X : XNet S) (todo : List (Id × S)) : Prop :=
  ∀ a α, (a, α) ∈ X.agents → (a, α) ∈ todo ∨ ∀ b β R, ¬ Redex xs.sys X.toNet a b α β R

theorem Covers.normal {X : XNet S} (h : Covers xs X []) : Normal (Step xs.sys) X.toNet := by
  rintro N' ⟨a, b, α, β, R, r, -⟩
  rcases h a α r.ha with hm | hno
  · exact absurd hm List.not_mem_nil
  · exact hno b β R r

theorem Covers.pop {X : XNet S} {e : Id × S} {rest : List (Id × S)}
    (h : Covers xs X (e :: rest))
    (he : (e.1, e.2) ∈ X.agents → ∀ b β R, ¬ Redex xs.sys X.toNet e.1 b e.2 β R) :
    Covers xs X rest := by
  intro a α ha
  rcases h a α ha with hm | hno
  · rcases List.mem_cons.1 hm with heq | hm
    · obtain ⟨e₁, e₂⟩ := Prod.mk.inj (show (a, α) = (e.1, e.2) from heq)
      rw [e₁, e₂] at ha ⊢
      exact .inr (he ha)
    · exact .inl hm
  · exact .inr hno

variable [DecidableEq S]

/-- A run of thread `t` alone, among other threads that wait. -/
theorem Runs.exec_at {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (r : Runs xs X T X' T' c k) : ∀ (ths : List (XThread S)) (t : Nat), ths[t]? = some T →
      XMach.exec xs (List.replicate k t) ⟨X, ths⟩ = (⟨X', ths.set t T'⟩, c) := by
  induction r with
  | refl X T =>
    intro ths t ht
    show ((⟨X, ths⟩ : XMach S), 0) = (⟨X, ths.set t T⟩, 0)
    rw [set_self ths t T ht]
  | @step X X₁ X' T T₁ T' c₁ c k h _ ih =>
    intro ths t ht
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
    have es : XMach.step xs ⟨X, ths⟩ t = (⟨X₁, ths.set t T₁⟩, c₁) := by
      unfold XMach.step
      dsimp only
      rw [ht]
      dsimp only
      rw [h]
    show ((XMach.exec xs (List.replicate k t) (XMach.step xs ⟨X, ths⟩ t).1).1,
      (XMach.step xs ⟨X, ths⟩ t).2 +
        (XMach.exec xs (List.replicate k t) (XMach.step xs ⟨X, ths⟩ t).1).2) = _
    rw [es, ih (ths.set t T₁) t (List.getElem?_set_self hlt), List.set_set]

/-- **One turn** of thread `t`: from its idle state it makes one attempt and
is idle again, while the other threads wait.  It rests if its list is
empty; it drops an agent that is no longer there; it comes back
empty-handed from an agent that is in no active pair with a rule; or it
fires a pair and takes a fresh copy of the list of agents. -/
inductive Turn (xs : XSys S) : XMach S → Nat → XMach S → Nat → Prop
  | rest {M : XMach S} {t : Nat} : M.ths[t]? = some ⟨[], .idle⟩ → Turn xs M t M 0
  | stale {M : XMach S} {t : Nat} {e : Id × S} {rest : List (Id × S)} :
      M.ths[t]? = some ⟨e :: rest, .idle⟩ → ¬ assoc e.1 M.mem.agents = some e.2 →
      Turn xs M t ⟨M.mem, M.ths.set t ⟨rest, .idle⟩⟩ 0
  | fail {M : XMach S} {t : Nat} {e : Id × S} {rest : List (Id × S)} {k : Nat} :
      M.ths[t]? = some ⟨e :: rest, .idle⟩ → assoc e.1 M.mem.agents = some e.2 →
      Runs xs M.mem ⟨rest, .look e.1 e.2⟩ M.mem ⟨rest, .idle⟩ 0 k →
      (∀ b β R, ¬ Redex xs.sys M.mem.toNet e.1 b e.2 β R) →
      Turn xs M t ⟨M.mem, M.ths.set t ⟨rest, .idle⟩⟩ 0
  | fire {M : XMach S} {t : Nat} {e : Id × S} {rest : List (Id × S)} {k : Nat} {X' : XNet S} :
      M.ths[t]? = some ⟨e :: rest, .idle⟩ → assoc e.1 M.mem.agents = some e.2 →
      Runs xs M.mem ⟨rest, .look e.1 e.2⟩ X' ⟨X'.agents, .idle⟩ 1 k →
      Step xs.sys M.mem.toNet X'.toNet →
      Turn xs M t ⟨X', M.ths.set t ⟨X'.agents, .idle⟩⟩ 1

/-- **A turn is a run of the program**, under a schedule that names its
thread only. -/
theorem Turn.exec {M M' : XMach S} {t c : Nat} (h : Turn xs M t M' c) :
    ∃ k, XMach.exec xs (List.replicate k t) M = (M', c) := by
  cases h with
  | rest _ => exact ⟨0, rfl⟩
  | stale ht hn =>
    exact ⟨1, Runs.exec_at (.step (c₁ := 0) (XMach.act_idle_neg hn) (.refl _ _)) M.ths t ht⟩
  | fail ht he r _ => exact ⟨_, Runs.exec_at (.step (XMach.act_idle_pos he) r) M.ths t ht⟩
  | fire ht he r _ => exact ⟨_, Runs.exec_at (.step (XMach.act_idle_pos he) r) M.ths t ht⟩

/-- What a turn changes: nothing, if the thread rests; otherwise the state
of its thread, whose list gets shorter unless the turn makes a claim. -/
theorem Turn.effect {M M' : XMach S} {t c : Nat} (h : Turn xs M t M' c) :
    (M.ths[t]? = some ⟨[], .idle⟩ ∧ M' = M ∧ c = 0) ∨
      ∃ e rest T', M.ths[t]? = some ⟨e :: rest, .idle⟩ ∧ M'.ths = M.ths.set t T' ∧
        ((c = 0 ∧ T'.todo.length < (e :: rest).length) ∨ c = 1) := by
  cases h with
  | rest ht => exact .inl ⟨ht, rfl, rfl⟩
  | stale ht _ => exact .inr ⟨_, _, _, ht, rfl, .inl ⟨rfl, Nat.lt_succ_self _⟩⟩
  | fail ht _ _ _ => exact .inr ⟨_, _, _, ht, rfl, .inl ⟨rfl, Nat.lt_succ_self _⟩⟩
  | fire ht _ _ _ => exact .inr ⟨_, _, _, ht, rfl, .inr rfl⟩

/-- A turn is a reduction of as many steps as it makes claims. -/
theorem Turn.steps {M M' : XMach S} {t c : Nat} (h : Turn xs M t M' c) :
    Steps (Step xs.sys) c M.mem.toNet M'.mem.toNet := by
  cases h with
  | rest _ => exact .refl _
  | stale _ _ => exact .refl _
  | fail _ _ _ _ => exact .refl _
  | fire _ _ _ hs => exact .single hs

/-- Between turns: every thread is idle, the memory is well formed, and the
list of some thread covers the memory. -/
structure XMach.Calm (xs : XSys S) (nt : Nat) (M : XMach S) : Prop where
  idle : ∀ T, T ∈ M.ths → T.st = .idle
  len : M.ths.length = nt
  wf : M.mem.toNet.WF xs.sys.ar
  lead : ∃ (t : Nat) (T : XThread S), M.ths[t]? = some T ∧ Covers xs M.mem T.todo

omit [DecidableEq S] in
theorem XMach.Calm.pop {nt : Nat} {M : XMach S} (hc : M.Calm xs nt) {t : Nat} {e : Id × S}
    {rest : List (Id × S)} (ht : M.ths[t]? = some ⟨e :: rest, .idle⟩)
    (he : (e.1, e.2) ∈ M.mem.agents → ∀ b β R, ¬ Redex xs.sys M.mem.toNet e.1 b e.2 β R) :
    XMach.Calm xs nt ⟨M.mem, M.ths.set t ⟨rest, .idle⟩⟩ := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
  refine ⟨fun T hT => ?_, by rw [List.length_set]; exact hc.len, hc.wf, ?_⟩
  · rcases List.mem_or_eq_of_mem_set hT with h | h
    · exact hc.idle T h
    · rw [h]
  · obtain ⟨u, T, hu, hcov⟩ := hc.lead
    by_cases hut : u = t
    · rw [hut, ht] at hu
      rw [← Option.some.inj hu] at hcov
      exact ⟨t, _, List.getElem?_set_self hlt, hcov.pop he⟩
    · refine ⟨u, T, ?_, hcov⟩
      show (M.ths.set t _)[u]? = some T
      rw [List.getElem?_set_ne (Ne.symm hut)]
      exact hu

/-- Turns keep the state calm. -/
theorem Turn.calm {nt : Nat} {M M' : XMach S} {t c : Nat} (hc : M.Calm xs nt)
    (h : Turn xs M t M' c) : M'.Calm xs nt := by
  cases h with
  | rest _ => exact hc
  | stale ht hn =>
    refine hc.pop ht fun hm => absurd (assoc_eq_of_unique hm fun α' h' => ?_) hn
    exact hc.wf.agent_fun h' hm
  | fail ht _ _ hno => exact hc.pop ht fun _ => hno
  | fire ht _ _ hs =>
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
    refine ⟨fun T hT => ?_, by rw [List.length_set]; exact hc.len, Step.wf hc.wf hs,
      ⟨t, _, List.getElem?_set_self hlt, fun a α ha => .inl ha⟩⟩
    rcases List.mem_or_eq_of_mem_set hT with h | h
    · exact hc.idle T h
    · rw [h]

/-- **Every thread can take a turn**, in every calm state. -/
theorem Turn.exists {nt : Nat} {M : XMach S} (hc : M.Calm xs nt) {t : Nat} (ht : t < nt) :
    ∃ M' c, Turn xs M t M' c := by
  cases h : M.ths[t]? with
  | none =>
    have := List.getElem?_eq_none_iff.1 h
    rw [hc.len] at this
    omega
  | some T =>
    have hst := hc.idle T (List.mem_of_getElem? h)
    obtain ⟨todo, st⟩ := T
    have hst' : st = .idle := hst
    subst hst'
    cases todo with
    | nil => exact ⟨M, 0, .rest h⟩
    | cons e rest =>
      by_cases he : assoc e.1 M.mem.agents = some e.2
      · rcases Runs.attempt hc.wf rest (assoc_mem he) with ⟨k, r, hno⟩ | ⟨k, X', r, hs⟩
        · exact ⟨_, 0, .fail h he r hno⟩
        · exact ⟨_, 1, .fire h he r hs⟩
      · exact ⟨_, 0, .stale h he⟩

theorem Turn.thread {M M' : XMach S} {t c : Nat} (h : Turn xs M t M' c) :
    ∃ T, M.ths[t]? = some T := by
  cases h with
  | rest ht => exact ⟨_, ht⟩
  | stale ht _ => exact ⟨_, ht⟩
  | fail ht _ _ _ => exact ⟨_, ht⟩
  | fire ht _ _ _ => exact ⟨_, ht⟩

omit [DecidableEq S] in
theorem XMach.init_thread (X : XNet S) {nt u : Nat} (hu : u < nt) :
    (XMach.init X nt).ths[u]? = some ⟨X.agents.drop u ++ X.agents.take u, .idle⟩ := by
  show ((List.range nt).map fun t =>
    (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S))[u]? = _
  rw [List.getElem?_map, List.getElem?_range hu]
  rfl

omit [DecidableEq S] in
theorem XMach.init_calm {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt u : Nat} (hu : u < nt) :
    (XMach.init X nt).Calm xs nt := by
  refine ⟨fun T hT => ?_, ?_, hX, ⟨u, _, XMach.init_thread X hu, fun a α ha => .inl ?_⟩⟩
  · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
    rfl
  · show ((List.range nt).map _).length = nt
    rw [List.length_map, List.length_range]
  · have ha' : (a, α) ∈ X.agents.take u ++ X.agents.drop u := by
      rw [List.take_append_drop]
      exact ha
    rcases List.mem_append.1 ha' with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h

/-- The claims of the first `i` turns. -/
def claimsUpTo (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => claimsUpTo c i + c i

/-- **Turns can be taken in any order.**  Whatever the order in which the
threads are named, the program takes those turns. -/
theorem Turn.sequence {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (t : Nat → Nat)
    (ht : ∀ i, t i < nt) :
    ∃ (M : Nat → XMach S) (c : Nat → Nat), M 0 = XMach.init X nt ∧
      ∀ i, Turn xs (M i) (t i) (M (i + 1)) (c i) := by
  have step : ∀ (P : {M : XMach S // M.Calm xs nt}) (u : Nat), u < nt →
      ∃ (Q : {M : XMach S // M.Calm xs nt}) (c : Nat), Turn xs P.1 u Q.1 c := by
    intro P u hu
    obtain ⟨M', c, h⟩ := Turn.exists P.2 hu
    exact ⟨⟨M', h.calm P.2⟩, c, h⟩
  let f : Nat → {M : XMach S // M.Calm xs nt} := fun i =>
    Nat.rec (motive := fun _ => {M : XMach S // M.Calm xs nt})
      ⟨XMach.init X nt, XMach.init_calm hX (ht 0)⟩
      (fun j P => Classical.choose (step P (t j) (ht j))) i
  exact ⟨fun i => (f i).1,
    fun i => Classical.choose (Classical.choose_spec (step (f i) (t i) (ht i))), rfl,
    fun i => Classical.choose_spec (Classical.choose_spec (step (f i) (t i) (ht i)))⟩

/-- **Threads that take turns finish.**  Take any sequence of turns from a
well-formed net that has a normal form, reached in `n` steps, in which
every thread keeps getting turns.  From some turn on nothing changes any
more: every thread is idle with an empty list, `n` claims have been made,
and the memory holds the normal form. -/
theorem XMach.turns_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {nt : Nat}
    (M : Nat → XMach S) (t c : Nat → Nat) (h0 : M 0 = XMach.init X nt)
    (hturn : ∀ i, Turn xs (M i) (t i) (M (i + 1)) (c i))
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ t j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → M i = M i₀ ∧ (M i).quiet = true ∧ claimsUpTo c i = n ∧
      (M i).mem.toNet = N' := by
  have hnt : t 0 < nt := by
    obtain ⟨T, hT⟩ := (hturn 0).thread
    rw [h0] at hT
    have hlen : (XMach.init X nt).ths.length = nt := by
      show ((List.range nt).map _).length = nt
      rw [List.length_map, List.length_range]
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hT
    rw [hlen] at hlt
    exact hlt
  have calm : ∀ i, (M i).Calm xs nt := by
    intro i
    induction i with
    | zero =>
      rw [h0]
      exact XMach.init_calm hX hnt
    | succ i ih => exact (hturn i).calm ih
  have red : ∀ i, Steps (Step xs.sys) (claimsUpTo c i) X.toNet (M i).mem.toNet := by
    intro i
    induction i with
    | zero =>
      rw [h0]
      exact .refl _
    | succ i ih => exact ih.trans (hturn i).steps
  have bound : ∀ i, claimsUpTo c i ≤ n := fun i => (reduction_bounded hX hs hn (red i)).1
  obtain ⟨i₀, hi₀⟩ := lex_settles (fun i => n - claimsUpTo c i) (fun i => load (M i).ths)
    (fun i => (M i).ths[t i]? = some ⟨[], .idle⟩) (by
      intro i
      have hb := bound (i + 1)
      have hc : claimsUpTo c (i + 1) = claimsUpTo c i + c i := rfl
      rcases (hturn i).effect with ⟨hr, e, e0⟩ | ⟨e, rest, T', ht, eths, hcase⟩
      · refine .inl ⟨hr, ?_, ?_⟩
        · show n - claimsUpTo c (i + 1) = n - claimsUpTo c i
          omega
        · show load (M (i + 1)).ths = load (M i).ths
          rw [e]
      · have hl := load_set (M i).ths (t i) ⟨e :: rest, .idle⟩ T' ht
        rw [← eths] at hl
        have hlen : (⟨e :: rest, .idle⟩ : XThread S).todo.length = (e :: rest).length := rfl
        rcases hcase with ⟨e0, hlt⟩ | e1
        · refine .inr (.inr ⟨?_, ?_⟩)
          · show n - claimsUpTo c (i + 1) = n - claimsUpTo c i
            omega
          · show load (M (i + 1)).ths < load (M i).ths
            omega
        · refine .inr (.inl ?_)
          show n - claimsUpTo c (i + 1) < n - claimsUpTo c i
          omega)
  have stay : ∀ i, i₀ ≤ i → M (i + 1) = M i := by
    intro i hi
    have hst := hi₀ i hi
    rcases (hturn i).effect with ⟨-, e, -⟩ | ⟨e, rest, T', ht, -, -⟩
    · exact e
    · rw [ht] at hst
      cases hst
  have same : ∀ d, M (i₀ + d) = M i₀ := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => exact (stay (i₀ + d) (Nat.le_add_right _ _)).trans ih
  have empty : ∀ u, u < nt → (M i₀).ths[u]? = some ⟨[], .idle⟩ := by
    intro u hu
    obtain ⟨j, hj, hju⟩ := hfair u hu i₀
    obtain ⟨d, rfl⟩ : ∃ d, j = i₀ + d := ⟨j - i₀, by omega⟩
    have h := hi₀ (i₀ + d) hj
    rw [same d, hju] at h
    exact h
  have hnorm : Normal (Step xs.sys) (M i₀).mem.toNet := by
    obtain ⟨u, T, hu, hcov⟩ := (calm i₀).lead
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hu
    rw [(calm i₀).len] at hlt
    rw [empty u hlt] at hu
    rw [← Option.some.inj hu] at hcov
    exact hcov.normal
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, i = i₀ + d := ⟨i - i₀, by omega⟩
  have hsame := same d
  have hr := red (i₀ + d)
  rw [hsame] at hr
  obtain ⟨e₁, e₂⟩ := normal_form_unique hX hr hs hnorm hn
  refine ⟨hsame, ?_, e₂, ?_⟩
  · exact List.all_eq_true.2 fun T hT =>
      congrArg TState.isIdle ((calm (i₀ + d)).idle T hT)
  · rw [hsame]
    exact e₁

end Turns

/-! ### Paths that never come back

A thread that follows a wire could, for all the theorems so far say, go
round for ever.  It cannot.  The ports it visits form a *trail*: each is
linked to the next, and none is visited twice.  Following the segments of a
well-formed net from a port that lies on one segment only, without turning
back, always yields a trail, and a trail is not longer than the list of
segments. -/

section Trails

variable {V : Type} {L L' : V → V → Prop} {u : V}

/-- A trail from `u`, listed backwards: the head is the point reached. -/
inductive Trail (L : V → V → Prop) (u : V) : List V → Prop
  | start : Trail L u [u]
  | step {c q : V} {vs : List V} :
      Trail L u (c :: vs) → L c q → q ∉ c :: vs → Trail L u (q :: c :: vs)

theorem Trail.mono (h : ∀ {p q}, L p q → L' p q) {vs : List V} (t : Trail L u vs) :
    Trail L' u vs := by
  induction t with
  | start => exact .start
  | step _ hl hf ih => exact .step ih (h hl) hf

theorem Trail.nodup {vs : List V} (t : Trail L u vs) : vs.Nodup := by
  induction t with
  | start => exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | step _ _ hf ih => exact List.nodup_cons.2 ⟨hf, ih⟩

/-- Every point of a trail but the last one reached is linked to the
next. -/
theorem Trail.has_next : ∀ {ws : List V}, Trail L u ws → ∀ c vs, ws = c :: vs →
    ∀ x, x ∈ vs → ∃ y, L x y := by
  intro ws t
  induction t with
  | start =>
    intro c vs e x hx
    obtain ⟨-, rfl⟩ := List.cons.inj e
    exact absurd hx List.not_mem_nil
  | @step c₀ q₀ vs₀ _ hl _ ih =>
    intro c vs e x hx
    obtain ⟨-, rfl⟩ := List.cons.inj e
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨q₀, hl⟩
    · exact ih c₀ vs₀ rfl x hx

/-- In a wiring where a point lies on two segments at most, and the start
of the trail on one, every point of the trail but the last one reached has
all its neighbours on the trail. -/
theorem Trail.closed (hs : ∀ {p q}, L p q → L q p)
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z)
    (hu : ∀ q q', L u q → L u q' → q = q') :
    ∀ {ws : List V}, Trail L u ws → ∀ c vs, ws = c :: vs →
      ∀ x, x ∈ vs → ∀ y, L x y → y ∈ ws := by
  intro ws t
  induction t with
  | start =>
    intro c vs e x hx
    obtain ⟨-, rfl⟩ := List.cons.inj e
    exact absurd hx List.not_mem_nil
  | @step c₀ q₀ vs₀ t hl hf ih =>
    intro c vs e x hx y hy
    obtain ⟨-, rfl⟩ := List.cons.inj e
    rcases List.mem_cons.1 hx with rfl | hx
    · cases t with
      | start => exact List.mem_cons.2 (.inl (hu y q₀ hy hl))
      | step _ hl' _ =>
        rename_i p vs'
        rcases hd (hs hl') hl hy with e | e | e
        · exact absurd (e ▸ List.mem_cons_of_mem _ List.mem_cons_self) hf
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (e ▸ List.mem_cons_self))
        · exact List.mem_cons.2 (.inl e.symm)
    · exact List.mem_cons_of_mem _ (ih c₀ vs₀ rfl x hx y hy)

/-- **The next point is new**: following a segment that does not go back to
the point one came from leads to a point that is not on the trail. -/
theorem Trail.fresh (hs : ∀ {p q}, L p q → L q p) (hi : ∀ {p}, ¬ L p p)
    (hd : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z)
    (hu : ∀ q q', L u q → L u q' → q = q') {c p q : V} {vs : List V}
    (t : Trail L u (c :: p :: vs)) (hl : L c q) (hq : q ≠ p) : q ∉ c :: p :: vs := by
  intro hm
  cases t with
  | step t' _ hf =>
    rcases List.mem_cons.1 hm with e | hm
    · rw [e] at hl
      exact hi hl
    · rcases List.mem_cons.1 hm with e | hm
      · exact hq e
      · exact hf (Trail.closed hs hd hu t' p vs rfl q hm c (hs hl))

/-- A list without repetition, all of whose elements are in another list, is
not longer than it. -/
theorem nodup_length_le {A : Type} [DecidableEq A] : ∀ (l W : List A), l.Nodup →
    (∀ x, x ∈ l → x ∈ W) → l.length ≤ W.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l, W, hn, hW => by
    obtain ⟨hx, hn'⟩ := List.nodup_cons.1 hn
    have hxW := hW x List.mem_cons_self
    have ih := nodup_length_le l (W.erase x) hn' fun y hy =>
      (List.mem_erase_of_ne (fun (e : y = x) => hx (by rw [← e]; exact hy))).2
        (hW y (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem hxW] at ih
    have hpos := List.length_pos_of_mem hxW
    show l.length + 1 ≤ W.length
    omega

/-- **A trail is not longer than the list of segments**, plus one. -/
theorem Trail.length_le [DecidableEq V] {vs : List V} (t : Trail L u vs) (W : List (V × V))
    (hW : ∀ {p q}, L p q → (p, q) ∈ W) : vs.length ≤ W.length + 1 := by
  cases vs with
  | nil => exact Nat.zero_le _
  | cons c rest =>
    have hn := (List.nodup_cons.1 t.nodup).2
    have h := nodup_length_le rest (W.map Prod.fst) hn fun x hx => by
      obtain ⟨y, hy⟩ := Trail.has_next t c rest rfl x hx
      exact List.mem_map.2 ⟨(x, y), hW hy, rfl⟩
    rw [List.length_map] at h
    show rest.length + 1 ≤ W.length + 1
    omega

end Trails

/-- Writes leave the goal as it is. -/
theorem Run.goal_zero {k : Nat} {st st' : CState S} (h : Run sys k st st') (hk : k = 0) :
    st'.goal = st.goal := by
  induction h with
  | refl st => rfl
  | @step c k st st₁ st₂ hc _ ih =>
    have hc0 : c = 0 := by omega
    subst hc0
    have e : st₁.goal = st.goal := by
      cases hc with
      | agent _ _ => rfl
      | link _ _ => rfl
    rw [ih (by omega), e]

/-- An execution with one claim fires one active pair of the goal. -/
theorem Run.one_claim {k : Nat} {st st' : CState S} (h : Run sys k st st') :
    k = 1 → st.Sound sys.ar →
      ∃ a b α β R, Redex sys st.goal a b α β R ∧ st'.goal = st.goal.fire a b R := by
  induction h with
  | refl st =>
    intro hk
    omega
  | @step c k st st₁ st₂ hc hr ih =>
    intro hk hs
    cases hc with
    | @claim _ a b α β R r =>
      exact ⟨a, b, α, β, R, hs.redex r, hr.goal_zero (by omega)⟩
    | agent hg hn => exact ih (by omega) (Conc.sound hs (.agent hg hn)).1
    | link hg hn => exact ih (by omega) (Conc.sound hs (.link hg hn)).1

/-- A walk that has not reached a terminal can be continued, if the walk
with the same first segment reaches one. -/
theorem Walk.extend {V : Type} {L : V → V → Prop} {T : V → Prop} (hW : Wiring L T)
    {u v p c x y : V} (w₁ : Walk L T u v p c) (w₂ : Walk L T u v x y) (hc : ¬ T c)
    (hy : T y) : ∃ q, L c q ∧ q ≠ p := by
  induction w₁ generalizing x y with
  | single h =>
    cases w₂ with
    | single _ => exact absurd hy hc
    | cons _ _ hne w => exact ⟨_, w.link_first, hne⟩
  | cons h hT hne w ih =>
    cases w₂ with
    | single _ => exact absurd hy hT
    | cons _ _ hne' w' =>
      rcases hW.deg (hW.symm h) w.link_first w'.link_first with e | e | e
      · exact absurd e.symm hne
      · exact absurd e.symm hne'
      · subst e
        exact ih w' hc hy

/-- A name in use stays in use when a pair fires. -/
theorem Net.used_fire {G : Net S} {ar : S → Nat} (hG : G.WF ar) {i : Id} (h : G.Used i)
    (c d : Id) (R : Rhs S) : (G.fire c d R).Used i := by
  rcases h with ⟨γ, hg⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
  · obtain ⟨q, hq⟩ := hG.end_wired (p := (i, 0)) (.inr ⟨γ, hg, Nat.zero_le _⟩)
    exact .inr (.inl ⟨0, q, .inl hq⟩)
  · exact .inr (.inl ⟨k, q, .inl hl⟩)
  · exact .inr (.inr ⟨k, hf⟩)

end INet
