import InteractionNets.Bits

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### One thread, round by round

A single thread that has written a claim is back where the program
starts: idle, with every agent of the memory in its list.  So its run is
a sequence of rounds, each the start of the run on the memory left by the
last, and what a run costs can be counted one round at a time. -/

section Rounds

variable [DecidableEq S] {xs : XSys S}

/-- The work of a run is the work up to a cut and the work after it. -/
theorem XMach.work_add (xs : XSys S) (σ : Nat → Nat) (M : XMach S) (i : Nat) :
    ∀ k, M.work xs σ (i + k) =
      M.work xs σ i + (M.trace xs σ i).1.work xs (fun j => σ (i + j)) k
  | 0 => rfl
  | k + 1 => by
    have ih := XMach.work_add xs σ M i k
    have a : (M.trace xs σ (i + k)).1 =
        ((M.trace xs σ i).1.trace xs (fun j => σ (i + j)) k).1 :=
      by rw [XMach.trace_add xs σ M i k]
    show M.work xs σ (i + k) + (M.trace xs σ (i + k)).1.stepTally XThread.busy (σ (i + k)) =
      M.work xs σ i + ((M.trace xs σ i).1.work xs (fun j => σ (i + j)) k +
        ((M.trace xs σ i).1.trace xs (fun j => σ (i + j)) k).1.stepTally XThread.busy
          (σ (i + k)))
    rw [ih, a, Nat.add_assoc]

/-- The program with one thread. -/
def XMach.single (X : XNet S) (T : XThread S) : XMach S := ⟨X, [T]⟩

/-- **One action of the single thread, then the rest of the run.** -/
theorem XMach.single_front (xs : XSys S) (X : XNet S) (T : XThread S) (k : Nat) :
    ((XMach.single X T).trace xs (fun _ => 0) (k + 1)).1 =
        ((XMach.single (XMach.act xs X T).1 (XMach.act xs X T).2.1).trace xs
          (fun _ => 0) k).1 ∧
      ((XMach.single X T).trace xs (fun _ => 0) (k + 1)).2 =
        (XMach.act xs X T).2.2 +
          ((XMach.single (XMach.act xs X T).1 (XMach.act xs X T).2.1).trace xs
            (fun _ => 0) k).2 ∧
      (XMach.single X T).work xs (fun _ => 0) (k + 1) =
        T.busy + (XMach.single (XMach.act xs X T).1 (XMach.act xs X T).2.1).work xs
          (fun _ => 0) k := by
  have h := XMach.trace_add xs (fun _ => 0) (XMach.single X T) 1 k
  have hw := XMach.work_add xs (fun _ => 0) (XMach.single X T) 1 k
  rw [Nat.add_comm 1 k] at h hw
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]
    show 0 + (XMach.act xs X T).2.2 + _ = _
    rw [Nat.zero_add]
    rfl
  · rw [hw]
    show 0 + T.busy + _ = _
    rw [Nat.zero_add]
    rfl

/-- Write a list of agents, the first of the list first. -/
def XNet.putAgents (X : XNet S) (as : List (Id × S)) : XNet S :=
  as.foldl (fun X e => X.putAgent e.1 e.2) X

/-- Write a list of segments, the first of the list first. -/
def XNet.putLinks (X : XNet S) (ls : List (Port × Port)) : XNet S :=
  ls.foldl (fun X e => X.putLink e.1 e.2) X

/-- **The writes of a claim end in a fresh start.**  A single thread that
has agents and segments to write takes one action for each and one more,
none of them a rest and none a claim, and then the program is the program
started on the memory as it then is. -/
theorem XMach.single_write (xs : XSys S) (todo : List (Id × S)) :
    ∀ (as : List (Id × S)) (ls : List (Port × Port)) (X : XNet S),
      ((XMach.single X ⟨todo, .write as ls⟩).trace xs (fun _ => 0)
          (as.length + ls.length + 1)).1 = XMach.init ((X.putAgents as).putLinks ls) 1 ∧
        ((XMach.single X ⟨todo, .write as ls⟩).trace xs (fun _ => 0)
          (as.length + ls.length + 1)).2 = 0 ∧
        (XMach.single X ⟨todo, .write as ls⟩).work xs (fun _ => 0)
          (as.length + ls.length + 1) = as.length + ls.length + 1
  | e :: as, ls, X => by
    obtain ⟨i, γ⟩ := e
    obtain ⟨a, b, c⟩ := XMach.single_write xs todo as ls (X.putAgent i γ)
    obtain ⟨f1, f2, f3⟩ := XMach.single_front xs X ⟨todo, .write ((i, γ) :: as) ls⟩
      (as.length + ls.length + 1)
    have e : ((i, γ) :: as).length + ls.length + 1 = as.length + ls.length + 1 + 1 := by
      show as.length + 1 + ls.length + 1 = _
      omega
    rw [e]
    refine ⟨f1.trans a, ?_, ?_⟩
    · rw [f2]
      show 0 + _ = 0
      rw [Nat.zero_add]
      exact b
    · rw [f3]
      show 1 + (XMach.single (X.putAgent i γ) ⟨todo, .write as ls⟩).work xs (fun _ => 0)
        (as.length + ls.length + 1) = _
      rw [c]
      omega
  | [], e :: ls, X => by
    obtain ⟨p, q⟩ := e
    obtain ⟨a, b, c⟩ := XMach.single_write xs todo [] ls (X.putLink p q)
    obtain ⟨f1, f2, f3⟩ := XMach.single_front xs X ⟨todo, .write [] ((p, q) :: ls)⟩
      (([] : List (Id × S)).length + ls.length + 1)
    have e : ([] : List (Id × S)).length + ((p, q) :: ls).length + 1 =
        ([] : List (Id × S)).length + ls.length + 1 + 1 := by
      show 0 + (ls.length + 1) + 1 = 0 + ls.length + 1 + 1
      omega
    rw [e]
    refine ⟨f1.trans a, ?_, ?_⟩
    · rw [f2]
      show 0 + _ = 0
      rw [Nat.zero_add]
      exact b
    · rw [f3]
      show 1 + (XMach.single (X.putLink p q) ⟨todo, .write [] ls⟩).work xs (fun _ => 0)
        (([] : List (Id × S)).length + ls.length + 1) = _
      rw [c]
      omega
  | [], [], X => by
    refine ⟨?_, rfl, rfl⟩
    exact (XMach.init_one X).symm

/-- **From a claim to the fresh start.**  A single thread that holds one
agent and finds its partner claims, writes, and starts afresh on the memory
with the pair taken out and the right-hand side written: two actions more
than there are agents and segments to write, none of them a rest, and one
claim. -/
theorem XMach.single_claim {X : XNet S} {todo : List (Id × S)} {a b : Id} {α β : S} {R : XRhs S}
    (h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R) :
    ((XMach.single X ⟨todo, .half a b α β⟩).trace xs (fun _ => 0)
        ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1 + 1)).1 =
      XMach.init (((X.takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β)) 1 ∧
      ((XMach.single X ⟨todo, .half a b α β⟩).trace xs (fun _ => 0)
        ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1 + 1)).2 = 1 ∧
      (XMach.single X ⟨todo, .half a b α β⟩).work xs (fun _ => 0)
        ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1 + 1) =
        (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1 + 1 := by
  obtain ⟨f1, f2, f3⟩ := XMach.single_front xs X ⟨todo, .half a b α β⟩
    ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1)
  rw [XMach.act_half h] at f1 f2 f3
  obtain ⟨a', b', c'⟩ := XMach.single_write xs todo (R.newAgents a b)
    (R.newLinks xs.sys.ar a b α β) (X.takeAgent b)
  refine ⟨f1.trans a', ?_, ?_⟩
  · rw [f2]
    show 1 + ((XMach.single (X.takeAgent b) ⟨todo, .write (R.newAgents a b)
      (R.newLinks xs.sys.ar a b α β)⟩).trace xs (fun _ => 0)
        ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1)).2 = 1
    rw [b']
  · rw [f3]
    show 1 + (XMach.single (X.takeAgent b) ⟨todo, .write (R.newAgents a b)
      (R.newLinks xs.sys.ar a b α β)⟩).work xs (fun _ => 0)
        ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1) = _
    rw [c']
    omega

/-- **After a claim is written the program runs as from the start.**  If
the single thread has come back to its start on a memory `X'`, the rest of
the run is the run on `X'`, and the claims and the work add up. -/
theorem XMach.restart {X X' : XNet S} {i : Nat}
    (h : ((XMach.init X 1).trace xs (fun _ => 0) i).1 = XMach.init X' 1) (k : Nat) :
    ((XMach.init X 1).trace xs (fun _ => 0) (i + k)).1 =
        ((XMach.init X' 1).trace xs (fun _ => 0) k).1 ∧
      ((XMach.init X 1).trace xs (fun _ => 0) (i + k)).2 =
        ((XMach.init X 1).trace xs (fun _ => 0) i).2 +
          ((XMach.init X' 1).trace xs (fun _ => 0) k).2 ∧
      (XMach.init X 1).work xs (fun _ => 0) (i + k) =
        (XMach.init X 1).work xs (fun _ => 0) i +
          (XMach.init X' 1).work xs (fun _ => 0) k := by
  have ab := XMach.trace_add xs (fun _ => 0) (XMach.init X 1) i k
  have c := XMach.work_add xs (fun _ => 0) (XMach.init X 1) i k
  rw [h] at ab c
  have ab1 := congrArg Prod.fst ab
  have ab2 := congrArg Prod.snd ab
  exact ⟨ab1, ab2, c⟩

end Rounds

section CountedRounds

variable [DecidableEq S] {xs : XSys S}

omit [DecidableEq S] in
theorem XThread.busy_of_ne_rest {T : XThread S} (h : T ≠ ⟨[], .idle⟩) : T.busy = 1 := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact absurd rfl h
    | cons e rest => rfl
  | look a α => rfl
  | seek a α p c => rfl
  | ready a b α β => rfl
  | half a b α β => rfl
  | write as ls => rfl

/-- **A counted run without rests is all work**: after its `k` actions the
work is `k` more than nothing, and from there it is the work of the run
from the state reached. -/
theorem Works.work {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (w : Works xs X T X' T' c k) :
    ∀ j, (XMach.single X T).work xs (fun _ => 0) (k + j) =
      k + (XMach.single X' T').work xs (fun _ => 0) j := by
  induction w with
  | refl X T =>
    intro j
    rw [Nat.zero_add, Nat.zero_add]
  | @step X X₁ X' T T₁ T' c₁ c k hT h _ ih =>
    intro j
    have f := (XMach.single_front xs X T (k + j)).2.2
    rw [h] at f
    have e : k + 1 + j = k + j + 1 := by omega
    rw [e, f, XThread.busy_of_ne_rest hT]
    show 1 + (XMach.single X₁ T₁).work xs (fun _ => 0) (k + j) = _
    rw [ih j]
    omega

/-- **The writes of a claim, as a counted run**: one action for each agent
and each segment and one more, none a rest, and the thread is left idle
with every agent of the memory in its list. -/
theorem Works.write (xs : XSys S) (todo : List (Id × S)) :
    ∀ (as : List (Id × S)) (ls : List (Port × Port)) (X : XNet S),
      Works xs X ⟨todo, .write as ls⟩ ((X.putAgents as).putLinks ls)
        ⟨((X.putAgents as).putLinks ls).agents, .idle⟩ 0 (as.length + ls.length + 1)
  | e :: as, ls, X => by
    obtain ⟨i, γ⟩ := e
    have w := Works.write xs todo as ls (X.putAgent i γ)
    have s : XMach.act xs X ⟨todo, .write ((i, γ) :: as) ls⟩ =
        (X.putAgent i γ, ⟨todo, .write as ls⟩, 0) := rfl
    have e : ((i, γ) :: as).length + ls.length + 1 = as.length + ls.length + 1 + 1 := by
      show as.length + 1 + ls.length + 1 = _
      omega
    rw [e]
    exact .step (c₁ := 0) (c := 0) (fun h => by cases h) s w
  | [], e :: ls, X => by
    obtain ⟨p, q⟩ := e
    have w := Works.write xs todo [] ls (X.putLink p q)
    have s : XMach.act xs X ⟨todo, .write [] ((p, q) :: ls)⟩ =
        (X.putLink p q, ⟨todo, .write [] ls⟩, 0) := rfl
    exact .step (c₁ := 0) (c := 0) (fun h => by cases h) s w
  | [], [], X =>
    .step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) rfl (.refl _ _)

/-- **A round on a pair that faces the thread directly.**  A single thread
whose first agent has its principal port on a segment to the principal
port of an agent it has a rule with claims the pair, writes the right-hand
side, and is left idle with every agent of the new memory in its list:
five actions and the writes, none a rest, and one claim. -/
theorem Works.claim_direct {X : XNet S} {a b : Id} {α β : S} {R : XRhs S}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some (b, 0)) (h₃ : assoc b X.agents = some β) (hne : a ≠ b)
    (h₄ : assoc b (X.takeAgent a).agents = some β) (hR : xs.rule α β = some R) :
    Works xs X ⟨(a, α) :: rest, .idle⟩
      ((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β))
      ⟨((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β)).agents, .idle⟩ 1
      (5 + ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1)) := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) (b, 0)⟩, 0) :=
    XMach.act_look h₂
  have s₃ : XMach.act xs X ⟨rest, .seek a α (a, 0) (b, 0)⟩ =
      (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have s₅ : XMach.act xs (X.takeAgent a) ⟨rest, .half a b α β⟩ =
      ((X.takeAgent a).takeAgent b,
        ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) :=
    XMach.act_half (by rw [ite_pos' ⟨h₄, hne⟩]; exact hR)
  have w₁ : Works xs X ⟨(a, α) :: rest, .idle⟩ ((X.takeAgent a).takeAgent b)
      ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩ 1 5 :=
    .step (c₁ := 0) (c := 1) (k := 4) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 1) (k := 3) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 1) (k := 2) (fun h => by cases h) s₃
          (.step (c₁ := 0) (c := 1) (k := 1) (fun h => by cases h) s₄
            (.step (c₁ := 1) (c := 0) (k := 0) (fun h => by cases h) s₅ (.refl _ _)))))
  exact w₁.trans (Works.write xs rest _ _ _)

/-- **A round on a pair one point away.**  As `Works.claim_direct`, but the
segment from the principal port of the first agent goes to a point that is
not the principal port of an agent, and the next segment from that point
reaches the partner: six actions and the writes. -/
theorem Works.claim_via {X : XNet S} {a b : Id} {α β : S} {R : XRhs S} {c : Port}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some c)
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂' : nextSeg X.wires c (a, 0) = some (b, 0)) (h₃ : assoc b X.agents = some β)
    (hne : a ≠ b) (h₄ : assoc b (X.takeAgent a).agents = some β)
    (hR : xs.rule α β = some R) :
    Works xs X ⟨(a, α) :: rest, .idle⟩
      ((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β))
      ⟨((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β)).agents, .idle⟩ 1
      (6 + ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1)) := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) c⟩, 0) :=
    XMach.act_look h₂
  have s₂' : XMach.act xs X ⟨rest, .seek a α (a, 0) c⟩ =
      (X, ⟨rest, .seek a α c (b, 0)⟩, 0) := XMach.act_seek_next hc h₂'
  have s₃ : XMach.act xs X ⟨rest, .seek a α c (b, 0)⟩ = (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have s₅ : XMach.act xs (X.takeAgent a) ⟨rest, .half a b α β⟩ =
      ((X.takeAgent a).takeAgent b,
        ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) :=
    XMach.act_half (by rw [ite_pos' ⟨h₄, hne⟩]; exact hR)
  have w₁ : Works xs X ⟨(a, α) :: rest, .idle⟩ ((X.takeAgent a).takeAgent b)
      ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩ 1 6 :=
    .step (c₁ := 0) (c := 1) (k := 5) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 1) (k := 4) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 1) (k := 3) (fun h => by cases h) s₂'
          (.step (c₁ := 0) (c := 1) (k := 2) (fun h => by cases h) s₃
            (.step (c₁ := 0) (c := 1) (k := 1) (fun h => by cases h) s₄
              (.step (c₁ := 1) (c := 0) (k := 0) (fun h => by cases h) s₅ (.refl _ _))))))
  exact w₁.trans (Works.write xs rest _ _ _)

end CountedRounds

section StepMemory

theorem XNet.putLinks_agents : ∀ (ls : List (Port × Port)) (X : XNet S),
    (X.putLinks ls).agents = X.agents
  | [], _ => rfl
  | l :: ls, X => XNet.putLinks_agents ls (X.putLink l.1 l.2)

theorem XNet.putAgents_wires : ∀ (as : List (Id × S)) (X : XNet S),
    (X.putAgents as).wires = X.wires
  | [], _ => rfl
  | e :: as, X => XNet.putAgents_wires as (X.putAgent e.1 e.2)

theorem XNet.mem_putLinks {e : Port × Port} : ∀ (ls : List (Port × Port)) (X : XNet S),
    e ∈ (X.putLinks ls).wires ↔ e ∈ ls ∨ e ∈ X.wires
  | [], _ => ⟨.inr, fun h => h.elim (fun h' => absurd h' List.not_mem_nil) id⟩
  | l :: ls, X => by
    have ih := XNet.mem_putLinks (e := e) ls (X.putLink l.1 l.2)
    have hc : e ∈ (X.putLink l.1 l.2).wires ↔ e = l ∨ e ∈ X.wires := List.mem_cons
    show e ∈ ((X.putLink l.1 l.2).putLinks ls).wires ↔ _
    rw [ih, hc, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

/-- The segments of the memory after a round: those written and those
there before. -/
theorem XNet.mem_step_wires [DecidableEq S] (X : XNet S) (x y : Id) (as : List (Id × S))
    (L : List (Port × Port)) (e : Port × Port) :
    e ∈ ((((X.takeAgent x).takeAgent y).putAgents as).putLinks L).wires ↔
      e ∈ L ∨ e ∈ X.wires := by
  rw [XNet.mem_putLinks, XNet.putAgents_wires]
  rfl

/-- The agents of the memory after a round that writes two. -/
theorem XNet.step_agents [DecidableEq S] (X : XNet S) (x y : Id) (e₁ e₂ : Id × S)
    (L : List (Port × Port)) :
    ((((X.takeAgent x).takeAgent y).putAgents [e₁, e₂]).putLinks L).agents =
      e₂ :: e₁ :: (X.agents.filter fun e => decide (e.1 ≠ x)).filter
        fun e => decide (e.1 ≠ y) := by
  rw [XNet.putLinks_agents]
  rfl

theorem dedupFst_pair {A B : Type} [DecidableEq A] {x y : A × B} (h : x.1 ≠ y.1) :
    dedupFst [x, y] = [x, y] := by
  have e : dedupFst [y] = [y] := rfl
  show (if x.1 ∈ (dedupFst [y]).map Prod.fst then dedupFst [y] else x :: dedupFst [y]) = _
  rw [e, ite_neg' (fun hm : x.1 ∈ [y].map Prod.fst => h (List.mem_singleton.1 hm))]

end StepMemory

theorem mem_insert1_wires {S : Type} (X : XNet S) (u : Id) (γ : S) (p q : Port)
    (e : Port × Port) :
    e ∈ (X.insert1 u γ p q).wires ↔
      e = (p, (u, 0)) ∨ e = ((u, 0), p) ∨ e = ((u, 1), q) ∨ e = (q, (u, 1)) ∨
        (e ∈ X.wires ∧ e.1 ≠ p ∧ e.1 ≠ q) := by
  show e ∈ (p, (u, 0)) :: ((u, 0), p) :: ((u, 1), q) :: (q, (u, 1)) ::
    X.wires.filter (fun e => decide (e.1 ≠ p ∧ e.1 ≠ q)) ↔ _
  rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_filter,
    decide_eq_true_iff]

section DeadWalks

variable [DecidableEq S] {xs : XSys S}

/-- `X.Dead p c k`: a thread that has come from `p` to `c` along a segment
gives up after exactly `k` more actions: it follows `k - 1` segments, none
to the principal port of an agent in memory, and then finds no segment to
go on. -/
inductive XNet.Dead (X : XNet S) : Port → Port → Nat → Prop
  | stop {p c : Port} : (if c.2 = 0 then assoc c.1 X.agents else none) = none →
      nextSeg X.wires c p = none → XNet.Dead X p c 1
  | step {p c q : Port} {k : Nat} : (if c.2 = 0 then assoc c.1 X.agents else none) = none →
      nextSeg X.wires c p = some q → XNet.Dead X c q k → XNet.Dead X p c (k + 1)

theorem Stays.seek_dead {X : XNet S} {todo : List (Id × S)} {a : Id} {α : S} {p c : Port}
    {k : Nat} (h : X.Dead p c k) :
    Stays xs X ⟨todo, .seek a α p c⟩ ⟨todo, .idle⟩ k := by
  induction h with
  | stop h1 h2 =>
    exact .step (k := 0) (fun h => by cases h) (XMach.act_seek_stop h1 h2) (.refl _)
  | step h1 h2 _ ih =>
    exact .step (fun h => by cases h) (XMach.act_seek_next h1 h2) ih

/-- **A thread passes an agent whose wire leads nowhere in two actions and
the length of the walk**, without writing. -/
theorem Stays.dead {X : XNet S} {e : Id × S} {c : Port} {k : Nat} (rest : List (Id × S))
    (h₁ : assoc e.1 X.agents = some e.2) (h₂ : assoc (e.1, 0) X.wires = some c)
    (hd : X.Dead (e.1, 0) c k) :
    Stays xs X ⟨e :: rest, .idle⟩ ⟨rest, .idle⟩ (k + 2) :=
  .step (fun h => by cases h) (XMach.act_idle_pos h₁)
    (.step (fun h => by cases h) (XMach.act_look h₂) (Stays.seek_dead hd))

end DeadWalks

theorem assoc_append_skip {A B : Type} [DecidableEq A] {k : A} :
    ∀ {l : List (A × B)} (l' : List (A × B)), (∀ e ∈ l, e.1 ≠ k) →
      assoc k (l ++ l') = assoc k l'
  | [], _, _ => rfl
  | (k', v) :: l, l', h => by
    show (if k' = k then some v else assoc k (l ++ l')) = _
    rw [ite_neg' (h (k', v) List.mem_cons_self)]
    exact assoc_append_skip l' fun e' he' => h e' (List.mem_cons_of_mem _ he')

theorem filter_keep {S : Type} {l : List (Id × S)} {a : Id} (h : ∀ e ∈ l, e.1 ≠ a) :
    l.filter (fun e => decide (e.1 ≠ a)) = l :=
  List.filter_eq_self.2 fun e he => decide_eq_true (h e he)

/-- A successor put on a wire leaves the segments at other ports alone. -/
theorem insert1_frame {S : Type} (X : XNet S) (u : Id) (γ : S) (p q r : Port)
    (h1 : r ≠ p) (h2 : r ≠ q) (h3 : r.1 ≠ u) (q' : Port) :
    ((r, q') : Port × Port) ∈ (X.insert1 u γ p q).wires ↔ (r, q') ∈ X.wires := by
  rw [mem_insert1_wires]
  constructor
  · rintro (e | e | e | e | ⟨h, -, -⟩)
    · injection e with e1 _
      exact absurd e1 h1
    · injection e with e1 _
      exact absurd (by rw [e1]) h3
    · injection e with e1 _
      exact absurd (by rw [e1]) h3
    · injection e with e1 _
      exact absurd e1 h2
    · exact h
  · intro h
    exact .inr (.inr (.inr (.inr ⟨h, h1, h2⟩)))

/-- The segments at the four ports a new successor joins. -/
theorem insert1_new {S : Type} (X : XNet S) (u : Id) (γ : S) (p q : Port)
    (hp : p.1 ≠ u) (hq : q.1 ≠ u) (hpq : p ≠ q)
    (hfresh : ∀ k q', (((u, k), q') : Port × Port) ∉ X.wires) :
    (∀ q', ((p, q') : Port × Port) ∈ (X.insert1 u γ p q).wires ↔ q' = (u, 0)) ∧
    (∀ q', (((u, 0), q') : Port × Port) ∈ (X.insert1 u γ p q).wires ↔ q' = p) ∧
    (∀ q', (((u, 1), q') : Port × Port) ∈ (X.insert1 u γ p q).wires ↔ q' = q) ∧
    (∀ q', ((q, q') : Port × Port) ∈ (X.insert1 u γ p q).wires ↔ q' = (u, 1)) := by
  have a1 : p ≠ (u, 0) := fun e => hp (by rw [e])
  have a2 : p ≠ (u, 1) := fun e => hp (by rw [e])
  have a3 : q ≠ (u, 0) := fun e => hq (by rw [e])
  have a4 : q ≠ (u, 1) := fun e => hq (by rw [e])
  have b1 := a1.symm
  have b2 := a2.symm
  have b3 := a3.symm
  have b4 := a4.symm
  have hqp := hpq.symm
  clear hp hq
  refine ⟨fun q' => ?_, fun q' => ?_, fun q' => ?_, fun q' => ?_⟩
  · rw [mem_insert1_wires]
    simp [*]
  · have h0 := hfresh 0 q'
    rw [mem_insert1_wires]
    simp [*]
  · have h0 := hfresh 1 q'
    rw [mem_insert1_wires]
    simp [*]
  · rw [mem_insert1_wires]
    simp [*]

theorem assoc_none_of_forall {A B : Type} [DecidableEq A] {k : A} {l : List (A × B)}
    (h : ∀ e ∈ l, e.1 ≠ k) : assoc k l = none := by
  have h' := assoc_append_skip (l := l) [] h
  rw [List.append_nil] at h'
  exact h'

theorem assoc_of_nodup {A B : Type} [DecidableEq A] : ∀ {l : List (A × B)},
    (l.map Prod.fst).Nodup → ∀ {e : A × B}, e ∈ l → assoc e.1 l = some e.2
  | [], _, _, h => absurd h List.not_mem_nil
  | (k, v) :: l, hnd, e, h => by
    have hnd' : k ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    show (if k = e.1 then some v else assoc e.1 l) = some e.2
    rcases List.mem_cons.1 h with rfl | h'
    · rw [ite_pos' rfl]
    · rw [ite_neg' (fun ek => hnd'.1 (by rw [ek]; exact List.mem_map_of_mem h'))]
      exact assoc_of_nodup hnd'.2 h'

section OpsCount

variable [DecidableEq S] {xs : XSys S}

/-- **The operations on the maps of agents that an action is charged
for**, by the state of the thread alone: the list of the thread, the cells
and the names.  Four to take an entry from the list, one to look up the
agent at a point, three to take an agent, two for each agent written. -/
def XThread.opsA (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | _ :: _ => 4
  | .look _ _ => 0
  | .seek _ _ _ _ => 1
  | .ready _ _ _ _ => 3
  | .half _ _ _ _ => 3
  | .write (_ :: _) _ => 2
  | .write [] _ => 0

/-- **The operations on the map of segments that an action is charged
for**, by the state of the thread alone: one to look a port up, one to
follow a segment, two for each segment written. -/
def XThread.opsW (T : XThread S) : Nat :=
  match T.st with
  | .idle => 0
  | .look _ _ => 1
  | .seek _ _ _ _ => 1
  | .ready _ _ _ _ => 0
  | .half _ _ _ _ => 0
  | .write (_ :: _) _ => 0
  | .write [] (_ :: _) => 2
  | .write [] [] => 0

omit [DecidableEq S] in
theorem XThread.opsA_map (g : Id → Id) (T : XThread S) : (T.map g).opsA = T.opsA := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle => cases todo <;> rfl
  | write as ls => cases as <;> cases ls <;> rfl
  | _ => rfl

omit [DecidableEq S] in
theorem XThread.opsW_map (g : Id → Id) (T : XThread S) : (T.map g).opsW = T.opsW := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle => cases todo <;> rfl
  | write as ls => cases as <;> cases ls <;> rfl
  | _ => rfl

/-- What a run comes to at a rate is what it comes to up to a cut and
what the rest comes to. -/
theorem XMach.tally_add (κ : XThread S → Nat) (xs : XSys S) (σ : Nat → Nat) (M : XMach S)
    (i : Nat) : ∀ k, M.tally κ xs σ (i + k) =
      M.tally κ xs σ i + (M.trace xs σ i).1.tally κ xs (fun j => σ (i + j)) k
  | 0 => rfl
  | k + 1 => by
    have ih := XMach.tally_add κ xs σ M i k
    have a : (M.trace xs σ (i + k)).1 =
        ((M.trace xs σ i).1.trace xs (fun j => σ (i + j)) k).1 :=
      by rw [XMach.trace_add xs σ M i k]
    show M.tally κ xs σ (i + k) + (M.trace xs σ (i + k)).1.stepTally κ (σ (i + k)) =
      M.tally κ xs σ i + ((M.trace xs σ i).1.tally κ xs (fun j => σ (i + j)) k +
        ((M.trace xs σ i).1.trace xs (fun j => σ (i + j)) k).1.stepTally κ (σ (i + k)))
    rw [ih, a, Nat.add_assoc]

theorem XMach.single_tally (κ : XThread S → Nat) (xs : XSys S) (X : XNet S) (T : XThread S)
    (k : Nat) :
    (XMach.single X T).tally κ xs (fun _ => 0) (k + 1) =
      κ T + (XMach.single (XMach.act xs X T).1 (XMach.act xs X T).2.1).tally κ xs
        (fun _ => 0) k := by
  have hw := XMach.tally_add κ xs (fun _ => 0) (XMach.single X T) 1 k
  rw [Nat.add_comm 1 k] at hw
  rw [hw]
  show 0 + κ T + _ = _
  rw [Nat.zero_add]
  rfl

theorem XMach.tally_mono (κ : XThread S → Nat) (σ : Nat → Nat) (M : XMach S) {a b : Nat}
    (h : a ≤ b) : M.tally κ xs σ a ≤ M.tally κ xs σ b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  clear h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

omit [DecidableEq S] in
theorem XMach.stepTally_resting (κ : XThread S → Nat) (hκ : κ ⟨[], .idle⟩ = 0) {M : XMach S}
    (h : M.resting = true) (t : Nat) : M.stepTally κ t = 0 := by
  unfold XMach.stepTally
  split
  · rename_i T hT
    rw [XThread.eq_rest (List.all_eq_true.1 h T (List.mem_of_getElem? hT))]
    exact hκ
  · rfl

/-- Once the threads rest, a rate that charges a thread at rest nothing
charges no more. -/
theorem XMach.tally_rest (κ : XThread S → Nat) (hκ : κ ⟨[], .idle⟩ = 0) {M : XMach S}
    (σ : Nat → Nat) {B : Nat} (h : (M.trace xs σ B).1.resting = true) :
    ∀ d, M.tally κ xs σ (B + d) = M.tally κ xs σ B
  | 0 => rfl
  | d + 1 => by
    show M.tally κ xs σ (B + d) + (M.trace xs σ (B + d)).1.stepTally κ (σ (B + d)) = _
    rw [XMach.stepTally_resting κ hκ (XMach.resting_trace σ h d), Nat.add_zero]
    exact XMach.tally_rest κ hκ σ h d

/-- A run of one thread that comes to `w` at some rate on the way to the
empty list comes to `w` then, and to no more at any time. -/
theorem XMach.tally_total (κ : XThread S → Nat) (hκ : κ ⟨[], .idle⟩ = 0) {X X' : XNet S}
    {T : XThread S} {k w : Nat}
    (h : ∀ j, (XMach.single X T).tally κ xs (fun _ => 0) (k + j) =
      w + (XMach.single X' ⟨[], .idle⟩).tally κ xs (fun _ => 0) j) :
    (XMach.single X T).tally κ xs (fun _ => 0) k = w ∧
      ∀ i, (XMach.single X T).tally κ xs (fun _ => 0) i ≤ w := by
  have hz : ∀ j, (XMach.single X' ⟨[], .idle⟩).tally κ xs (fun _ => 0) j = 0 := by
    intro j
    have h' := XMach.tally_rest (xs := xs) κ hκ (M := XMach.single X' ⟨[], .idle⟩) (fun _ => 0)
      (B := 0) rfl j
    rw [Nat.zero_add] at h'
    exact h'
  have hk : (XMach.single X T).tally κ xs (fun _ => 0) k = w := by
    have h0 := h 0
    rw [hz 0] at h0
    exact h0
  refine ⟨hk, fun i => ?_⟩
  by_cases hi : i ≤ k
  · have hm := XMach.tally_mono (xs := xs) κ (fun _ => 0) (XMach.single X T) hi
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    rw [h j, hz j]
    exact Nat.le_refl _

/-- `Opers xs X T X' T' c k a s`: a counted run of one thread, as `Works`,
that is charged `a` operations on the maps of agents and `s` on the map of
segments. -/
inductive Opers (xs : XSys S) :
    XNet S → XThread S → XNet S → XThread S → Nat → Nat → Nat → Nat → Prop
  | refl (X : XNet S) (T : XThread S) : Opers xs X T X T 0 0 0 0
  | step {X X₁ X' : XNet S} {T T₁ T' : XThread S} {c₁ c k wa ws : Nat} :
      T ≠ ⟨[], .idle⟩ → XMach.act xs X T = (X₁, T₁, c₁) → Opers xs X₁ T₁ X' T' c k wa ws →
      Opers xs X T X' T' (c₁ + c) (k + 1) (T.opsA + wa) (T.opsW + ws)

theorem Opers.cast {X X' : XNet S} {T T' : XThread S} {c k a s c' k' a' s' : Nat}
    (r : Opers xs X T X' T' c k a s) (hc : c = c') (hk : k = k') (ha : a = a') (hs : s = s') :
    Opers xs X T X' T' c' k' a' s' := by
  subst hc hk ha hs
  exact r

theorem Opers.works {X X' : XNet S} {T T' : XThread S} {c k a s : Nat}
    (r : Opers xs X T X' T' c k a s) : Works xs X T X' T' c k := by
  induction r with
  | refl X T => exact .refl _ _
  | step hT h _ ih => exact .step hT h ih

theorem Opers.trans {X X₁ X₂ : XNet S} {T T₁ T₂ : XThread S}
    {c₁ c₂ k₁ k₂ a₁ a₂ s₁ s₂ : Nat}
    (r₁ : Opers xs X T X₁ T₁ c₁ k₁ a₁ s₁) (r₂ : Opers xs X₁ T₁ X₂ T₂ c₂ k₂ a₂ s₂) :
    Opers xs X T X₂ T₂ (c₁ + c₂) (k₁ + k₂) (a₁ + a₂) (s₁ + s₂) := by
  induction r₁ with
  | refl X T =>
    rw [Nat.zero_add, Nat.zero_add, Nat.zero_add, Nat.zero_add]
    exact r₂
  | @step X X₁ X' T T₁ T' c₁ c k wa ws hT h _ ih =>
    exact (Opers.step hT h (ih r₂)).cast (Nat.add_assoc _ _ _).symm
      (Nat.add_right_comm _ _ _) (Nat.add_assoc _ _ _).symm (Nat.add_assoc _ _ _).symm

/-- **What a counted run is charged on the maps of agents**: after its
`k` actions it has been charged `a` operations, and from there what the
run from the state reached is charged. -/
theorem Opers.tallyA {X X' : XNet S} {T T' : XThread S} {c k a s : Nat}
    (r : Opers xs X T X' T' c k a s) :
    ∀ j, (XMach.single X T).tally XThread.opsA xs (fun _ => 0) (k + j) =
      a + (XMach.single X' T').tally XThread.opsA xs (fun _ => 0) j := by
  induction r with
  | refl X T =>
    intro j
    rw [Nat.zero_add, Nat.zero_add]
  | @step X X₁ X' T T₁ T' c₁ c k wa ws hT h _ ih =>
    intro j
    have f := XMach.single_tally XThread.opsA xs X T (k + j)
    rw [h] at f
    have e : k + 1 + j = k + j + 1 := by omega
    rw [e, f]
    show T.opsA + (XMach.single X₁ T₁).tally XThread.opsA xs (fun _ => 0) (k + j) = _
    rw [ih j, Nat.add_assoc]

/-- The same on the map of segments. -/
theorem Opers.tallyW {X X' : XNet S} {T T' : XThread S} {c k a s : Nat}
    (r : Opers xs X T X' T' c k a s) :
    ∀ j, (XMach.single X T).tally XThread.opsW xs (fun _ => 0) (k + j) =
      s + (XMach.single X' T').tally XThread.opsW xs (fun _ => 0) j := by
  induction r with
  | refl X T =>
    intro j
    rw [Nat.zero_add, Nat.zero_add]
  | @step X X₁ X' T T₁ T' c₁ c k wa ws hT h _ ih =>
    intro j
    have f := XMach.single_tally XThread.opsW xs X T (k + j)
    rw [h] at f
    have e : k + 1 + j = k + j + 1 := by omega
    rw [e, f]
    show T.opsW + (XMach.single X₁ T₁).tally XThread.opsW xs (fun _ => 0) (k + j) = _
    rw [ih j, Nat.add_assoc]

/-- **A counted run to the empty list is charged its operations and no
more**, at any time, on the maps of agents and on the map of segments. -/
theorem Opers.total {X X' : XNet S} {T : XThread S} {c k a s : Nat}
    (r : Opers xs X T X' ⟨[], .idle⟩ c k a s) :
    ((XMach.single X T).tally XThread.opsA xs (fun _ => 0) k = a ∧
        ∀ i, (XMach.single X T).tally XThread.opsA xs (fun _ => 0) i ≤ a) ∧
      ((XMach.single X T).tally XThread.opsW xs (fun _ => 0) k = s ∧
        ∀ i, (XMach.single X T).tally XThread.opsW xs (fun _ => 0) i ≤ s) :=
  ⟨XMach.tally_total XThread.opsA rfl r.tallyA, XMach.tally_total XThread.opsW rfl r.tallyW⟩

theorem Opers.write (xs : XSys S) (todo : List (Id × S)) :
    ∀ (as : List (Id × S)) (ls : List (Port × Port)) (X : XNet S),
      Opers xs X ⟨todo, .write as ls⟩ ((X.putAgents as).putLinks ls)
        ⟨((X.putAgents as).putLinks ls).agents, .idle⟩ 0 (as.length + ls.length + 1)
        (2 * as.length) (2 * ls.length)
  | e :: as, ls, X => by
    obtain ⟨i, γ⟩ := e
    have w := Opers.write xs todo as ls (X.putAgent i γ)
    have hs : XMach.act xs X ⟨todo, .write ((i, γ) :: as) ls⟩ =
        (X.putAgent i γ, ⟨todo, .write as ls⟩, 0) := rfl
    have r : Opers xs X ⟨todo, .write ((i, γ) :: as) ls⟩
        (((X.putAgent i γ).putAgents as).putLinks ls)
        ⟨(((X.putAgent i γ).putAgents as).putLinks ls).agents, .idle⟩ (0 + 0)
        (as.length + ls.length + 1 + 1) (2 + 2 * as.length) (0 + 2 * ls.length) :=
      .step (fun h => by cases h) hs w
    exact r.cast rfl (by show _ = as.length + 1 + ls.length + 1; omega)
      (by show _ = 2 * (as.length + 1); omega) (Nat.zero_add _)
  | [], e :: ls, X => by
    obtain ⟨p, q⟩ := e
    have w := Opers.write xs todo [] ls (X.putLink p q)
    have hs : XMach.act xs X ⟨todo, .write [] ((p, q) :: ls)⟩ =
        (X.putLink p q, ⟨todo, .write [] ls⟩, 0) := rfl
    have r : Opers xs X ⟨todo, .write [] ((p, q) :: ls)⟩
        (((X.putLink p q).putAgents []).putLinks ls)
        ⟨(((X.putLink p q).putAgents []).putLinks ls).agents, .idle⟩ (0 + 0)
        (([] : List (Id × S)).length + ls.length + 1 + 1)
        (0 + 2 * ([] : List (Id × S)).length) (2 + 2 * ls.length) :=
      .step (fun h => by cases h) hs w
    exact r.cast rfl rfl rfl (by show _ = 2 * (ls.length + 1); omega)
  | [], [], X =>
    .step (c₁ := 0) (c := 0) (k := 0) (wa := 0) (ws := 0) (fun h => by cases h) rfl
      (.refl _ _)

/-- **A round on a pair that faces the thread directly, with what it is
charged**: eleven operations on the maps of agents and two for each agent
written, two on the map of segments and two for each segment written. -/
theorem Opers.claim_direct {X : XNet S} {a b : Id} {α β : S} {R : XRhs S}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some (b, 0)) (h₃ : assoc b X.agents = some β) (hne : a ≠ b)
    (h₄ : assoc b (X.takeAgent a).agents = some β) (hR : xs.rule α β = some R) :
    Opers xs X ⟨(a, α) :: rest, .idle⟩
      ((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β))
      ⟨((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β)).agents, .idle⟩ 1
      (5 + ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1))
      (11 + 2 * (R.newAgents a b).length)
      (2 + 2 * (R.newLinks xs.sys.ar a b α β).length) := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) (b, 0)⟩, 0) :=
    XMach.act_look h₂
  have s₃ : XMach.act xs X ⟨rest, .seek a α (a, 0) (b, 0)⟩ =
      (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have s₅ : XMach.act xs (X.takeAgent a) ⟨rest, .half a b α β⟩ =
      ((X.takeAgent a).takeAgent b,
        ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) :=
    XMach.act_half (by rw [ite_pos' ⟨h₄, hne⟩]; exact hR)
  have w₁ : Opers xs X ⟨(a, α) :: rest, .idle⟩ ((X.takeAgent a).takeAgent b)
      ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩ 1 5 11 2 :=
    .step (c₁ := 0) (c := 1) (k := 4) (wa := 7) (ws := 2) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 1) (k := 3) (wa := 7) (ws := 1) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 1) (k := 2) (wa := 6) (ws := 0) (fun h => by cases h) s₃
          (.step (c₁ := 0) (c := 1) (k := 1) (wa := 3) (ws := 0) (fun h => by cases h) s₄
            (.step (c₁ := 1) (c := 0) (k := 0) (wa := 0) (ws := 0) (fun h => by cases h) s₅
              (.refl _ _)))))
  exact w₁.trans (Opers.write xs rest _ _ _)

/-- **A round on a pair one point away, with what it is charged**: one
more operation on each kind of map than a round on a pair that faces the
thread. -/
theorem Opers.claim_via {X : XNet S} {a b : Id} {α β : S} {R : XRhs S} {c : Port}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some c)
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂' : nextSeg X.wires c (a, 0) = some (b, 0)) (h₃ : assoc b X.agents = some β)
    (hne : a ≠ b) (h₄ : assoc b (X.takeAgent a).agents = some β)
    (hR : xs.rule α β = some R) :
    Opers xs X ⟨(a, α) :: rest, .idle⟩
      ((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β))
      ⟨((((X.takeAgent a).takeAgent b).putAgents (R.newAgents a b)).putLinks
        (R.newLinks xs.sys.ar a b α β)).agents, .idle⟩ 1
      (6 + ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1))
      (12 + 2 * (R.newAgents a b).length)
      (3 + 2 * (R.newLinks xs.sys.ar a b α β).length) := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) c⟩, 0) :=
    XMach.act_look h₂
  have s₂' : XMach.act xs X ⟨rest, .seek a α (a, 0) c⟩ =
      (X, ⟨rest, .seek a α c (b, 0)⟩, 0) := XMach.act_seek_next hc h₂'
  have s₃ : XMach.act xs X ⟨rest, .seek a α c (b, 0)⟩ = (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have s₅ : XMach.act xs (X.takeAgent a) ⟨rest, .half a b α β⟩ =
      ((X.takeAgent a).takeAgent b,
        ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) :=
    XMach.act_half (by rw [ite_pos' ⟨h₄, hne⟩]; exact hR)
  have w₁ : Opers xs X ⟨(a, α) :: rest, .idle⟩ ((X.takeAgent a).takeAgent b)
      ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩ 1 6 12 3 :=
    .step (c₁ := 0) (c := 1) (k := 5) (wa := 8) (ws := 3) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 1) (k := 4) (wa := 8) (ws := 2) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 1) (k := 3) (wa := 7) (ws := 1) (fun h => by cases h) s₂'
          (.step (c₁ := 0) (c := 1) (k := 2) (wa := 6) (ws := 0) (fun h => by cases h) s₃
            (.step (c₁ := 0) (c := 1) (k := 1) (wa := 3) (ws := 0) (fun h => by cases h) s₄
              (.step (c₁ := 1) (c := 0) (k := 0) (wa := 0) (ws := 0) (fun h => by cases h)
                s₅ (.refl _ _))))))
  exact w₁.trans (Opers.write xs rest _ _ _)

theorem Opers.seek_dead {X : XNet S} {todo : List (Id × S)} {a : Id} {α : S} {p c : Port}
    {k : Nat} (h : X.Dead p c k) :
    Opers xs X ⟨todo, .seek a α p c⟩ X ⟨todo, .idle⟩ 0 k k k := by
  induction h with
  | stop h1 h2 =>
    exact .step (c₁ := 0) (c := 0) (k := 0) (wa := 0) (ws := 0) (fun h => by cases h)
      (XMach.act_seek_stop h1 h2) (.refl _ _)
  | @step p c q k h1 h2 _ ih =>
    exact (Opers.step (fun h => by cases h) (XMach.act_seek_next h1 h2) ih).cast rfl rfl
      (Nat.add_comm 1 k) (Nat.add_comm 1 k)

/-- **A thread passes an agent whose wire leads nowhere, charged four
operations on the maps of agents and one on the map of segments, and one
of each for each point of the walk.** -/
theorem Opers.dead {X : XNet S} {e : Id × S} {c : Port} {k : Nat} (rest : List (Id × S))
    (h₁ : assoc e.1 X.agents = some e.2) (h₂ : assoc (e.1, 0) X.wires = some c)
    (hd : X.Dead (e.1, 0) c k) :
    Opers xs X ⟨e :: rest, .idle⟩ X ⟨rest, .idle⟩ 0 (k + 2) (k + 4) (k + 1) := by
  have w := Opers.seek_dead (xs := xs) (todo := rest) (a := e.1) (α := e.2) hd
  have r : Opers xs X ⟨e :: rest, .idle⟩ X ⟨rest, .idle⟩ (0 + (0 + 0)) (k + 1 + 1)
      (4 + (0 + k)) (0 + (1 + k)) :=
    .step (fun h => by cases h) (XMach.act_idle_pos h₁)
      (.step (fun h => by cases h) (XMach.act_look h₂) w)
  exact r.cast rfl rfl (by omega) (by omega)

theorem Opers.inert {X : XNet S} {e : Id × S} (rest : List (Id × S)) (h : X.Inert e) :
    Opers xs X ⟨e :: rest, .idle⟩ X ⟨rest, .idle⟩ 0 3 5 2 := by
  obtain ⟨h₁, q, h₂, h₃, h₄⟩ := h
  exact Opers.dead (k := 1) rest h₁ h₂ (.stop h₃ h₄)

theorem Opers.inert_pass {X : XNet S} (rest : List (Id × S)) : ∀ (l : List (Id × S)),
    (∀ e, e ∈ l → X.Inert e) →
      Opers xs X ⟨l ++ rest, .idle⟩ X ⟨rest, .idle⟩ 0 (3 * l.length) (5 * l.length)
        (2 * l.length)
  | [], _ => .refl _ _
  | e :: l, h => by
    have w₁ : Opers xs X ⟨e :: (l ++ rest), .idle⟩ X ⟨l ++ rest, .idle⟩ 0 3 5 2 :=
      Opers.inert _ (h e List.mem_cons_self)
    have w₂ := Opers.inert_pass rest l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    exact (w₁.trans w₂).cast rfl (by show _ = 3 * (l.length + 1); omega)
      (by show _ = 5 * (l.length + 1); omega) (by show _ = 2 * (l.length + 1); omega)

/-- **Everything counted, an action costs the size of a rule, four, and
its operations**, each at the depth of its own tree: at most `L + 5` for
each level of a tree of agents under `DA` deep, and `L + 6` for each
level of the tree of segments, under `DW` deep. -/
theorem OMach.fcost_ops {C D : Nat} (hb : xs.Bounded C D) (O : OMem S) (T : TThread S)
    {DA DW L : Nat} (hc : tdepth O.cells + 1 ≤ DA) (hl : ndepth O.live + 1 ≤ DA)
    (hn : ndepth O.nbrs + 1 ≤ DW) (ht : tdepth T.todo + 1 ≤ DA)
    (hf : ∀ p c, findCells p (O.nb c) ≤ 2) (hN : T.toX.NamesLe L) :
    OMach.fcost xs O T ≤ (C + D + 4) * T.toX.busy + (L + 5) * DA * T.toX.opsA +
      (L + 6) * DW * T.toX.opsW := by
  have hD : DA ≤ (L + 5) * DA := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have symB : ∀ i : Id, i.length ≤ L → O.symF i ≤ (L + 5) * DA := fun i hi =>
    op_le (ngetF_snd O.live i) (by omega) hl (by omega)
  have nbB : ∀ p : Port, p.1.length ≤ L → O.nbF p ≤ (L + 6) * DW := fun p hp =>
    op_le (ngetF_snd O.nbrs (portKey p)) (by omega)
      hn (by show (p.2 :: p.1).length + 5 ≤ L + 6; show p.1.length + 1 + 5 ≤ L + 6; omega)
  have takeB : ∀ a : Id, a.length ≤ L → O.takeF a ≤ 2 * ((L + 5) * DA) := by
    intro a ha
    unfold OMem.takeF
    cases O.live[a]? with
    | none => exact Nat.zero_le _
    | some v =>
      have h₁ := op_le (L := L + 5) (teraseF_snd O.cells v.1) (by omega) hc (by omega)
      have h₂ := op_le (L := L + 5) (neraseF_snd O.live a) (by omega) hl (by omega)
      show (teraseF O.cells v.1).2 + (neraseF O.live a).2 ≤ 2 * ((L + 5) * DA)
      omega
  have putB : ∀ (i : Id) (γ : S), i.length ≤ L → O.putF i γ ≤ 2 * ((L + 5) * DA) := by
    intro i γ hi
    have h₁ := op_le (L := L + 5) (tinsertF_snd O.cells O.stamp (i, γ)) (by omega) hc
      (by omega)
    have h₂ := op_le (L := L + 5) (ninsertF_snd O.live i (O.stamp, γ)) (by omega) hl
      (by omega)
    show (tinsertF O.cells O.stamp (i, γ)).2 + (ninsertF O.live i (O.stamp, γ)).2 ≤
      2 * ((L + 5) * DA)
    omega
  have linkB : ∀ p q : Port, p.1.length ≤ L → O.linkF p q ≤ 2 * ((L + 6) * DW) := by
    intro p q hp
    have h₁ := nbB p hp
    have h₂ := op_le (L := L + 6)
      (ninsertF_snd O.nbrs (portKey p) (pushNb q (O.nb p))) (by omega) hn
      (by show (p.2 :: p.1).length + 5 ≤ L + 6; show p.1.length + 1 + 5 ≤ L + 6; omega)
    show O.nbF p + (ninsertF O.nbrs (portKey p) (pushNb q (O.nb p))).2 ≤ 2 * ((L + 6) * DW)
    omega
  obtain ⟨todo, s⟩ := T
  have ht' : tdepth todo + 1 ≤ DA := ht
  obtain ⟨hNd, hNs⟩ := hN
  cases s with
  | idle =>
    cases hmax : (tmaxC todo).1 with
    | none =>
      have e : OMach.fcost xs O ⟨todo, .idle⟩ = 0 := by
        unfold OMach.fcost
        dsimp only
        rw [hmax]
      rw [e]
      exact Nat.zero_le _
    | some s =>
      have hmax' : todo.maxKey? = some s := by rw [← tmaxC_fst, hmax]
      obtain ⟨v, -, hlst⟩ := treeList_max todo hmax'
      have eb : (TThread.toX (⟨todo, .idle⟩ : TThread S)).busy = 1 := by
        show XThread.busy ⟨treeList todo, .idle⟩ = 1
        rw [hlst]
        rfl
      have eo : (TThread.toX (⟨todo, .idle⟩ : TThread S)).opsA = 4 := by
        show XThread.opsA ⟨treeList todo, .idle⟩ = 4
        rw [hlst]
        rfl
      have h₁ := tmaxC_snd todo
      have h₂ := op_le (L := L + 5) (tgetF_snd todo s) (by omega) ht' (by omega)
      have h₃ := op_le (L := L + 5) (teraseF_snd todo s) (by omega) ht' (by omega)
      have e : OMach.fcost xs O ⟨todo, .idle⟩ =
          match todo[s]? with
          | some e =>
            1 + ((tmaxC todo).2 + (tgetF todo s).2 + (teraseF todo s).2) + O.symF e.1
          | none => 1 + ((tmaxC todo).2 + (tgetF todo s).2) := by
        unfold OMach.fcost
        dsimp only
        rw [hmax] <;> rfl
      rw [e, eb, eo]
      cases hg : todo[s]? with
      | none =>
        show 1 + ((tmaxC todo).2 + (tgetF todo s).2) ≤
          (C + D + 4) * 1 + (L + 5) * DA * 4 + (L + 6) * DW * 0
        omega
      | some e =>
        have h₄ := symB e.1 (hNd e ((mem_treeList todo e).2 ⟨s, hg⟩))
        show 1 + ((tmaxC todo).2 + (tgetF todo s).2 + (teraseF todo s).2) + O.symF e.1 ≤
          (C + D + 4) * 1 + (L + 5) * DA * 4 + (L + 6) * DW * 0
        omega
  | look a α =>
    have ha : a.length ≤ L := hNs
    have h₁ := nbB (a, 0) ha
    show 2 + O.nbF (a, 0) ≤ (C + D + 4) * 1 + (L + 5) * DA * 0 + (L + 6) * DW * 1
    omega
  | seek a α p c =>
    obtain ⟨-, -, hc'⟩ : a.length ≤ L ∧ p.1.length ≤ L ∧ c.1.length ≤ L := hNs
    have h₁ := symB c.1 hc'
    have h₂ := nbB c hc'
    have h₃ := hf p c
    show (if c.2 = 0 then
        1 + O.symF c.1 + (if (O.sym c.1).isSome then 0 else O.nbF c + findCells p (O.nb c))
      else 1 + O.nbF c + findCells p (O.nb c)) ≤
      (C + D + 4) * 1 + (L + 5) * DA * 1 + (L + 6) * DW * 1
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    obtain ⟨ha, -⟩ : a.length ≤ L ∧ b.length ≤ L := hNs
    have h₁ := symB a ha
    have h₂ := takeB a ha
    show 1 + O.symF a + (if O.sym a = some α then O.takeF a else 0) ≤
      (C + D + 4) * 1 + (L + 5) * DA * 3 + (L + 6) * DW * 0
    split <;> omega
  | half a b α β =>
    obtain ⟨ha, hb'⟩ : a.length ≤ L ∧ b.length ≤ L := hNs
    have h₁ := symB b hb'
    have h₂ := takeB b hb'
    have h₃ := putB a α ha
    have eb : (TThread.toX (⟨todo, .half a b α β⟩ : TThread S)).busy = 1 := rfl
    have eo : (TThread.toX (⟨todo, .half a b α β⟩ : TThread S)).opsA = 3 := rfl
    have eo' : (TThread.toX (⟨todo, .half a b α β⟩ : TThread S)).opsW = 0 := rfl
    rw [eb, eo, eo']
    unfold OMach.fcost
    dsimp only
    split
    · split
      · rename_i R hR
        obtain ⟨hC, hD'⟩ := hb α β R hR
        have hal := Nat.le_trans (R.newAgents_length a b) hC
        have hll := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD'
        show 1 + O.symF b + (O.takeF b + (R.newAgents a b).length +
          (R.newLinks xs.sys.ar a b α β).length) ≤
          (C + D + 4) * 1 + (L + 5) * DA * 3 + (L + 6) * DW * 0
        omega
      · show 1 + O.symF b + O.putF a α ≤ (C + D + 4) * 1 + (L + 5) * DA * 3 + (L + 6) * DW * 0
        omega
    · show 1 + O.symF b + O.putF a α ≤ (C + D + 4) * 1 + (L + 5) * DA * 3 + (L + 6) * DW * 0
      omega
  | write as ls =>
    obtain ⟨has, hls⟩ : (∀ e ∈ as, e.1.length ≤ L) ∧
        ∀ e ∈ ls, e.1.1.length ≤ L ∧ e.2.1.length ≤ L := hNs
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have h₁ := putB i γ (has (i, γ) List.mem_cons_self)
      show 1 + O.putF i γ ≤ (C + D + 4) * 1 + (L + 5) * DA * 2 + (L + 6) * DW * 0
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have h₁ := linkB p q (hls (p, q) List.mem_cons_self).1
        show 4 + O.linkF p q ≤ (C + D + 4) * 1 + (L + 5) * DA * 0 + (L + 6) * DW * 2
        omega
      | nil =>
        show 1 ≤ (C + D + 4) * 1 + (L + 5) * DA * 0 + (L + 6) * DW * 0
        omega

/-- The same for the numbered program: the size of a rule, five, and the
operations of the action, each at the depth of its own tree. -/
theorem ZMach.fcost_ops {C D : Nat} (hb : xs.Bounded C D) (O : OMem S) (cnt : Nat)
    (T : TThread S) {DA DW L : Nat} (hc : tdepth O.cells + 1 ≤ DA)
    (hl : ndepth O.live + 1 ≤ DA) (hn : ndepth O.nbrs + 1 ≤ DW)
    (ht : tdepth T.todo + 1 ≤ DA) (hf : ∀ p c, findCells p (O.nb c) ≤ 2)
    (hN : T.toX.NamesLe L) :
    ZMach.fcost xs O cnt T ≤ (C + D + 5) * T.toX.busy + (L + 5) * DA * T.toX.opsA +
      (L + 6) * DW * T.toX.opsW := by
  have h₁ := ZMach.fcost_le_named xs O cnt T
  have h₂ := OMach.fcost_ops hb O T hc hl hn ht hf hN
  have e : (C + D + 5) * T.toX.busy = (C + D + 4) * T.toX.busy + T.toX.busy := by
    rw [show C + D + 5 = (C + D + 4) + 1 from rfl, Nat.add_mul, Nat.one_mul]
  omega

/-- What one action of the numbered program costs, against the named
program: the size of a rule and five if it is not a rest, and its
operations, those on the maps of agents at the depth of a tree of `A`
entries and those on the map of segments at the depth of one of `W`. -/
theorem ZMach.stepFcost_ops {C D : Nat} (hb : xs.Bounded C D) {Z : ZMach S} {H : TMem S}
    (hA : Z.mem.Agree H) (hk : H.Ok) (hsz : Z.mem.Sized) {g : Id → Id} {M : XMach S}
    (hM : M = Z.toY.toX.map g) {L A W : Nat} (hN : Z.toY.toX.NamesLe L)
    (hAg : M.mem.agents.length ≤ A) (hW : M.mem.wires.length ≤ W)
    (htd : ∀ T ∈ M.ths, T.todo.length ≤ A) (t : Nat) :
    Z.stepFcost xs t ≤ (C + D + 5) * M.stepTally XThread.busy t +
      (L + 5) * (3 * lg A) * M.stepTally XThread.opsA t +
      (L + 6) * (3 * lg W) * M.stepTally XThread.opsW t := by
  subst hM
  have hcells : Z.mem.cells.size ≤ A := by
    rw [← treeList_length]
    have e : ((treeList Z.mem.cells).map fun e => (g e.1, e.2)).length ≤ A := hAg
    rw [List.length_map] at e
    exact e
  have hwires : Z.mem.wires.length ≤ W := by
    have e : (Z.mem.wires.map fun e => (mapPort g e.1, mapPort g e.2)).length ≤ W := hW
    rw [List.length_map] at e
    exact e
  have hm : (Z.toY.toX.map g).ths[t]? = (Z.ths[t]?).map fun T => T.toX.map g := by
    show ((Z.ths.map TThread.toX).map (XThread.map g))[t]? = _
    rw [List.getElem?_map, List.getElem?_map]
    cases Z.ths[t]? <;> rfl
  have d₁ := tdepth_lt Z.mem.cells
  have d₂ := ndepth_lt Z.mem.live
  have d₃ := ndepth_lt Z.mem.nbrs
  have m₁ := lg_mono hcells
  have m₂ := lg_mono (Nat.le_trans hsz.live hcells)
  have m₃ := lg_mono (Nat.le_trans hsz.nbrs hwires)
  have hfc : ∀ p c, findCells p (Z.mem.nb c) ≤ 2 := by
    intro p c
    rw [hA.nb c, hk.nbrs c]
    exact findCells_nbOf _ c p
  unfold ZMach.stepFcost XMach.stepTally
  rw [hm]
  cases hT : Z.ths[t]? with
  | none => exact Nat.zero_le _
  | some T =>
    have hTm : T ∈ Z.ths := List.mem_of_getElem? hT
    have hTX : T.toX.map g ∈ (Z.toY.toX.map g).ths :=
      List.mem_map.2 ⟨T.toX, List.mem_map.2 ⟨T, hTm, rfl⟩, rfl⟩
    have htodo : T.todo.size ≤ A := by
      have e : ((treeList T.todo).map fun e => (g e.1, e.2)).length ≤ A := htd _ hTX
      rw [List.length_map, treeList_length] at e
      exact e
    have m₄ := lg_mono htodo
    have d₄ := tdepth_lt T.todo
    have hNT : T.toX.NamesLe L := hN.2 T.toX (List.mem_map.2 ⟨T, hTm, rfl⟩)
    have hb' := ZMach.fcost_ops hb Z.mem Z.cnt T (DA := 3 * lg A) (DW := 3 * lg W)
      (by omega) (by omega) (by omega) (by omega) hfc hNT
    show ZMach.fcost xs Z.mem Z.cnt T ≤
      (C + D + 5) * (T.toX.map g).busy + (L + 5) * (3 * lg A) * (T.toX.map g).opsA +
        (L + 6) * (3 * lg W) * (T.toX.map g).opsW
    rw [XThread.busy_map, XThread.opsA_map, XThread.opsW_map]
    exact hb'

/-- **The running time of the numbered program, everything counted, by
its work and its operations.**  Under any schedule the time is at most
the size of a rule and five for each action that is not a rest, and for
each operation charged the cost of one on its own tree at full depth:

    (max L 1 + 5) * (3 * lg a)      on the maps of agents
    (max L 1 + 6) * (3 * lg w)      on the map of segments

with `a` the agents and `w` the segments that the memory can hold. -/
theorem ZMach.ftime_le_ops {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {L : Nat} (hL : X.NamesLe L) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (ZMach.init X nt).ftime xs σ i ≤
      (C + D + 5) * (XMach.init X nt).work xs σ i +
        (max L 1 + 5) * (3 * lg (X.agents.length + C * n)) *
          (XMach.init X nt).tally XThread.opsA xs σ i +
        (max L 1 + 6) * (3 * lg (X.wires.length + D * n)) *
          (XMach.init X nt).tally XThread.opsW xs σ i := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have htodo := TMach.todo_le (xs := xs) hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨a, -, H, hA, hk⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨g, hr, -⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
    obtain ⟨tsim, -, -⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨hAg, -, -⟩ := hΦ i
    have hW := XMach.wires_le (xs := xs) hX hnt hb hs hn σ i
    have hNm := ZMach.names_le (xs := xs) hX hnd hnt hL σ i
    have sz := ZMach.trace_sized xs σ (M := ZMach.init X nt) (OMem.ofX_sized X) i
    have hXtodo : ∀ T ∈ ((XMach.init X nt).trace xs σ i).1.ths,
        T.todo.length ≤ X.agents.length + C * n := by
      intro T hT
      rw [← tsim] at hT
      have hT' : T ∈ ((TMach.init X nt).trace xs σ i).1.ths.map TThread.toX := hT
      obtain ⟨T', hT'', rfl⟩ := List.mem_map.1 hT'
      have h := htodo i T' hT''
      show (treeList T'.todo).length ≤ _
      rw [treeList_length]
      exact h
    have hM : ((XMach.init X nt).trace xs σ i).1 =
        ((ZMach.init X nt).trace xs σ i).1.toY.toX.map g := by
      rw [a]
      exact hr.eq
    have hstep := ZMach.stepFcost_ops (xs := xs) hb hA hk sz hM hNm hAg hW hXtodo (σ i)
    show (ZMach.init X nt).ftime xs σ i +
        ((ZMach.init X nt).trace xs σ i).1.stepFcost xs (σ i) ≤
      (C + D + 5) * ((XMach.init X nt).work xs σ i +
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i)) +
        (max L 1 + 5) * (3 * lg (X.agents.length + C * n)) *
          ((XMach.init X nt).tally XThread.opsA xs σ i +
            ((XMach.init X nt).trace xs σ i).1.stepTally XThread.opsA (σ i)) +
        (max L 1 + 6) * (3 * lg (X.wires.length + D * n)) *
          ((XMach.init X nt).tally XThread.opsW xs σ i +
            ((XMach.init X nt).trace xs σ i).1.stepTally XThread.opsW (σ i))
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega

/-- Every action that is not a rest costs at least one. -/
theorem ZMach.busy_le_fcost (xs : XSys S) (O : OMem S) (cnt : Nat) (T : TThread S) :
    T.toX.busy ≤ ZMach.fcost xs O cnt T := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases hmax : (tmaxC todo).1 with
    | none =>
      have hl : treeList todo = [] := by
        unfold treeList
        rw [tmax_none todo (by rw [← tmaxC_fst, hmax])]
        rfl
      have eb : (TThread.toX (⟨todo, .idle⟩ : TThread S)).busy = 0 := by
        show XThread.busy ⟨treeList todo, .idle⟩ = 0
        rw [hl]
        rfl
      rw [eb]
      exact Nat.zero_le _
    | some s =>
      have hb := XThread.busy_le (TThread.toX (⟨todo, .idle⟩ : TThread S))
      have e : ZMach.fcost xs O cnt ⟨todo, .idle⟩ =
          match todo[s]? with
          | some e =>
            1 + ((tmaxC todo).2 + (tgetF todo s).2 + (teraseF todo s).2) + O.symF e.1
          | none => 1 + ((tmaxC todo).2 + (tgetF todo s).2) := by
        show OMach.fcost xs O ⟨todo, .idle⟩ = _
        unfold OMach.fcost
        dsimp only
        rw [hmax] <;> rfl
      rw [e]
      cases todo[s]? with
      | none =>
        show _ ≤ 1 + ((tmaxC todo).2 + (tgetF todo s).2)
        omega
      | some e =>
        show _ ≤ 1 + ((tmaxC todo).2 + (tgetF todo s).2 + (teraseF todo s).2) + O.symF e.1
        omega
  | look a α =>
    show 1 ≤ 2 + O.nbF (a, 0)
    omega
  | seek a α p c =>
    show 1 ≤ (if c.2 = 0 then
        1 + O.symF c.1 + (if (O.sym c.1).isSome then 0 else O.nbF c + findCells p (O.nb c))
      else 1 + O.nbF c + findCells p (O.nb c))
    split <;> omega
  | ready a b α β =>
    show 1 ≤ 1 + O.symF a + _
    omega
  | half a b α β =>
    show 1 ≤ 1 + O.symF b + _
    omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show 1 ≤ 1 + O.putF i γ
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 1 ≤ 4 + O.linkF p q
        omega
      | nil => exact Nat.le_refl 1

theorem ZMach.stepTally_le_fcost (xs : XSys S) (Z : ZMach S) (g : Id → Id) (t : Nat) :
    (Z.toY.toX.map g).stepTally XThread.busy t ≤ Z.stepFcost xs t := by
  have hm : (Z.toY.toX.map g).ths[t]? = (Z.ths[t]?).map fun T => T.toX.map g := by
    show ((Z.ths.map TThread.toX).map (XThread.map g))[t]? = _
    rw [List.getElem?_map, List.getElem?_map]
    cases Z.ths[t]? <;> rfl
  unfold ZMach.stepFcost XMach.stepTally
  rw [hm]
  cases hT : Z.ths[t]? with
  | none => exact Nat.le_refl _
  | some T =>
    show (T.toX.map g).busy ≤ ZMach.fcost xs Z.mem Z.cnt T
    rw [XThread.busy_map]
    exact ZMach.busy_le_fcost xs Z.mem Z.cnt T

/-- **The count is at least the work.**  Under any schedule, with
everything counted, the numbered program has taken at least one for each
action that is not a rest. -/
theorem ZMach.work_le_ftime {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (XMach.init X nt).work xs σ i ≤ (ZMach.init X nt).ftime xs σ i
  | 0 => Nat.le_refl _
  | i + 1 => by
    have ih := ZMach.work_le_ftime hX hnd hnt σ i
    obtain ⟨a, -, -⟩ := ZMach.trace_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨g, hr, -⟩ := YMach.trace_rel (xs := xs) hX hnt σ i
    have hM : ((XMach.init X nt).trace xs σ i).1 =
        ((ZMach.init X nt).trace xs σ i).1.toY.toX.map g := by
      rw [a]
      exact hr.eq
    have hstep := ZMach.stepTally_le_fcost xs ((ZMach.init X nt).trace xs σ i).1 g (σ i)
    rw [← hM] at hstep
    show (XMach.init X nt).work xs σ i +
        ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i) ≤
      (ZMach.init X nt).ftime xs σ i + ((ZMach.init X nt).trace xs σ i).1.stepFcost xs (σ i)
    omega

end OpsCount

section Blocks

variable [DecidableEq S] {xs : XSys S}

/-- **A schedule given by blocks**: the first thread named, for as many
actions as its block says, then the next; after the last block, thread
zero. -/
def blockSched : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (t, k) :: bs, i => if i < k then t else blockSched bs (i - k)

theorem blockSched_lt (t k : Nat) (bs : List (Nat × Nat)) {i : Nat} (h : i < k) :
    blockSched ((t, k) :: bs) i = t := by
  show (if i < k then t else blockSched bs (i - k)) = t
  rw [ite_pos' h]

theorem blockSched_add (t k : Nat) (bs : List (Nat × Nat)) (i : Nat) :
    blockSched ((t, k) :: bs) (k + i) = blockSched bs i := by
  show (if k + i < k then t else blockSched bs (k + i - k)) = _
  rw [ite_neg' (by omega), Nat.add_sub_cancel_left]

/-- What a run comes to at a rate depends on the schedule up to the point
reached only. -/
theorem XMach.tally_congr (κ : XThread S → Nat) (xs : XSys S) (M : XMach S)
    {σ σ' : Nat → Nat} :
    ∀ i, (∀ j, j < i → σ j = σ' j) → M.tally κ xs σ i = M.tally κ xs σ' i
  | 0, _ => rfl
  | i + 1, h => by
    have ih := XMach.tally_congr κ xs M i fun j hj => h j (Nat.lt_succ_of_lt hj)
    have ht := XMach.trace_congr xs M i fun j hj => h j (Nat.lt_succ_of_lt hj)
    show M.tally κ xs σ i + (M.trace xs σ i).1.stepTally κ (σ i) =
      M.tally κ xs σ' i + (M.trace xs σ' i).1.stepTally κ (σ' i)
    rw [ih, ht, h i (Nat.lt_succ_self i)]

/-- With one thread scheduled all along: its first action, then the
rest. -/
theorem XMach.tally_shift (κ : XThread S → Nat) (xs : XSys S) (t : Nat) (M : XMach S)
    (i : Nat) :
    M.tally κ xs (fun _ => t) (i + 1) =
      M.stepTally κ t + (M.step xs t).1.tally κ xs (fun _ => t) i := by
  have h := XMach.tally_add κ xs (fun _ => t) M 1 i
  rw [Nat.add_comm 1 i] at h
  rw [h]
  show 0 + M.stepTally κ t + _ = _
  rw [Nat.zero_add]
  rfl

/-- **A counted run of one thread among others that wait is all work.** -/
theorem Works.work_at {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (w : Works xs X T X' T' c k) : ∀ (ths : List (XThread S)) (t : Nat), ths[t]? = some T →
      (⟨X, ths⟩ : XMach S).work xs (fun _ => t) k = k := by
  induction w with
  | refl X T =>
    intro ths t _
    rfl
  | @step X X₁ X' T T₁ T' c₁ c k hT h _ ih =>
    intro ths t ht
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
    have es : XMach.step xs ⟨X, ths⟩ t = (⟨X₁, ths.set t T₁⟩, c₁) :=
      XMach.step_eq (M := ⟨X, ths⟩) ht h
    have hb : (⟨X, ths⟩ : XMach S).stepTally XThread.busy t = 1 := by
      show (match ths[t]? with
        | some T => XThread.busy T
        | none => 0) = 1
      rw [ht]
      exact XThread.busy_of_ne_rest hT
    have f := XMach.tally_shift XThread.busy xs t (⟨X, ths⟩ : XMach S) k
    rw [es, hb] at f
    show (⟨X, ths⟩ : XMach S).tally XThread.busy xs (fun _ => t) (k + 1) = k + 1
    rw [f]
    show 1 + (⟨X₁, ths.set t T₁⟩ : XMach S).work xs (fun _ => t) k = k + 1
    rw [ih (ths.set t T₁) t (List.getElem?_set_self hlt)]
    omega

/-- **A run under a schedule of blocks, after the first block**: the run
of the first thread alone, then the run under the rest of the blocks. -/
theorem XMach.trace_block (xs : XSys S) (M : XMach S) (t k : Nat) (bs : List (Nat × Nat))
    (j : Nat) :
    M.trace xs (blockSched ((t, k) :: bs)) (k + j) =
      (((M.trace xs (fun _ => t) k).1.trace xs (blockSched bs) j).1,
        (M.trace xs (fun _ => t) k).2 +
          ((M.trace xs (fun _ => t) k).1.trace xs (blockSched bs) j).2) := by
  have e1 : M.trace xs (blockSched ((t, k) :: bs)) k = M.trace xs (fun _ => t) k :=
    XMach.trace_congr xs M k fun j hj => blockSched_lt t k bs hj
  have e2 : (fun i => blockSched ((t, k) :: bs) (k + i)) = blockSched bs :=
    funext fun i => blockSched_add t k bs i
  rw [XMach.trace_add xs (blockSched ((t, k) :: bs)) M k j, e1, e2]

/-- The work of a run under a schedule of blocks: the work of the first
block, and the work under the rest. -/
theorem XMach.work_block (xs : XSys S) (M : XMach S) (t k : Nat) (bs : List (Nat × Nat))
    (j : Nat) :
    M.work xs (blockSched ((t, k) :: bs)) (k + j) =
      M.work xs (fun _ => t) k +
        (M.trace xs (fun _ => t) k).1.work xs (blockSched bs) j := by
  have e0 : M.work xs (blockSched ((t, k) :: bs)) k = M.work xs (fun _ => t) k :=
    XMach.tally_congr XThread.busy xs M k fun j hj => blockSched_lt t k bs hj
  have e1 : M.trace xs (blockSched ((t, k) :: bs)) k = M.trace xs (fun _ => t) k :=
    XMach.trace_congr xs M k fun j hj => blockSched_lt t k bs hj
  have e2 : (fun i => blockSched ((t, k) :: bs) (k + i)) = blockSched bs :=
    funext fun i => blockSched_add t k bs i
  rw [XMach.work_add xs (blockSched ((t, k) :: bs)) M k j, e0, e1, e2]

/-- `BlockRun xs M bs K`: under the schedule of the blocks `bs`, the first
`K` actions from `M` are, block by block, counted runs of the thread
scheduled while the others wait.  None of them is a rest. -/
inductive BlockRun (xs : XSys S) : XMach S → List (Nat × Nat) → Nat → Prop
  | done (M : XMach S) (bs : List (Nat × Nat)) : BlockRun xs M bs 0
  | cons {X X' : XNet S} {ths : List (XThread S)} {t : Nat} {T T' : XThread S} {c k K : Nat}
      {bs : List (Nat × Nat)} :
      ths[t]? = some T → Works xs X T X' T' c k → BlockRun xs ⟨X', ths.set t T'⟩ bs K →
      BlockRun xs ⟨X, ths⟩ ((t, k) :: bs) (k + K)

/-- **A run by blocks is all work.** -/
theorem BlockRun.work {M : XMach S} {bs : List (Nat × Nat)} {K : Nat}
    (r : BlockRun xs M bs K) : M.work xs (blockSched bs) K = K := by
  induction r with
  | done M bs => rfl
  | @cons X X' ths t T T' c k K bs hT w _ ih =>
    rw [XMach.work_block xs ⟨X, ths⟩ t k bs K, w.work_at ths t hT, w.trace_at ths t hT]
    show k + (⟨X', ths.set t T'⟩ : XMach S).work xs (blockSched bs) K = k + K
    rw [ih]

theorem BlockRun.work_ge {M : XMach S} {bs : List (Nat × Nat)} {K : Nat}
    (r : BlockRun xs M bs K) {i : Nat} (hi : K ≤ i) : K ≤ M.work xs (blockSched bs) i := by
  have h := XMach.work_mono (xs := xs) (blockSched bs) M hi
  rw [r.work] at h
  exact h

omit [DecidableEq S] in
/-- A walk of two points that ends nowhere, from what is at the two
points. -/
theorem XNet.dead_two_of {X : XNet S} {p c w : Port}
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (hw : (if w.2 = 0 then assoc w.1 X.agents else none) = none)
    (h1 : ((c, w) : Port × Port) ∈ X.wires) (hwp : w ≠ p)
    (u1 : ∀ q, ((c, q) : Port × Port) ∈ X.wires → q = p ∨ q = w)
    (u2 : ∀ q, ((w, q) : Port × Port) ∈ X.wires → q = c) : X.Dead p c 2 :=
  .step hc (nextSeg_some h1 hwp fun q hq hqp => (u1 q hq).resolve_left hqp)
    (.stop hw (nextSeg_none u2))

end Blocks

theorem filter_comm' {A : Type} (p q : A → Bool) (l : List A) :
    (l.filter p).filter q = (l.filter q).filter p := by
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext a
  exact Bool.and_comm _ _

section Reader

variable [DecidableEq S] {xs : XSys S}

/-- An action removes no segment. -/
theorem XMach.act_wires_sub (xs : XSys S) (X : XNet S) (T : XThread S) :
    ∀ e ∈ X.wires, e ∈ (XMach.act xs X T).1.wires := by
  intro e he
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact he
    | cons e' rest =>
      by_cases h : assoc e'.1 X.agents = some e'.2
      · rw [XMach.act_idle_pos h]
        exact he
      · rw [XMach.act_idle_neg h]
        exact he
  | look a α =>
    cases h : assoc (a, 0) X.wires with
    | none =>
      rw [XMach.act_look_none h]
      exact he
    | some q =>
      rw [XMach.act_look h]
      exact he
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    split
    · split <;> exact he
    · split <;> exact he
  | ready a b α β =>
    by_cases h : assoc a X.agents = some α
    · rw [XMach.act_ready h]
      exact he
    · rw [XMach.act_ready_neg h]
      exact he
  | half a b α β =>
    cases h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | none =>
      rw [XMach.act_half_none h]
      exact he
    | some R =>
      rw [XMach.act_half h]
      exact he
  | write as ls =>
    cases as with
    | cons y as =>
      obtain ⟨i, γ⟩ := y
      exact he
    | nil =>
      cases ls with
      | nil => exact he
      | cons z ls =>
        obtain ⟨p, q⟩ := z
        exact List.mem_cons_of_mem _ he

/-- The segments of a thread running alone only grow. -/
theorem XMach.solo_wires_mono (xs : XSys S) (X : XNet S) (T : XThread S) (u : Nat) :
    ∀ d, ∀ e ∈ (XMach.solo xs X T u).1.wires, e ∈ (XMach.solo xs X T (u + d)).1.wires
  | 0 => fun _ h => h
  | d + 1 => fun e h => by
    have ih := XMach.solo_wires_mono xs X T u d e h
    rw [show u + (d + 1) = u + d + 1 from rfl, XMach.solo_succ]
    exact XMach.act_wires_sub xs _ _ e ih

/-- The state of a thread cannot bring the agent `x` back. -/
def TState.Clear (x : Id) : TState S → Prop
  | .half a _ _ _ => a ≠ x
  | .write as _ => ∀ e ∈ as, e.1 ≠ x
  | _ => True

/-- **An agent that is gone stays gone**, when no rule makes an agent of
its name. -/
theorem XMach.act_gone {x : Id}
    (hx : ∀ {α β : S} {R : XRhs S} {a b : Id} {e : Id × S}, xs.rule α β = some R →
      e ∈ R.newAgents a b → e.1 ≠ x)
    {X : XNet S} {T : XThread S} (h1 : assoc x X.agents = none) (h2 : T.st.Clear x) :
    assoc x (XMach.act xs X T).1.agents = none ∧ (XMach.act xs X T).2.1.st.Clear x := by
  obtain ⟨todo, st⟩ := T
  have take : ∀ a, assoc x (X.takeAgent a).agents = none := by
    intro a
    show assoc x (X.agents.filter fun e => decide (e.1 ≠ a)) = none
    rw [assoc_filter_ne]
    by_cases e : a = x
    · rw [ite_pos' e]
    · rw [ite_neg' e]
      exact h1
  have put : ∀ (i : Id) (γ : S), i ≠ x → assoc x (X.putAgent i γ).agents = none := by
    intro i γ hi
    show (if i = x then some γ else assoc x X.agents) = none
    rw [ite_neg' hi]
    exact h1
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨h1, trivial⟩
    | cons e' rest =>
      by_cases h : assoc e'.1 X.agents = some e'.2
      · rw [XMach.act_idle_pos h]
        exact ⟨h1, trivial⟩
      · rw [XMach.act_idle_neg h]
        exact ⟨h1, trivial⟩
  | look a α =>
    cases h : assoc (a, 0) X.wires with
    | none =>
      rw [XMach.act_look_none h]
      exact ⟨h1, trivial⟩
    | some q =>
      rw [XMach.act_look h]
      exact ⟨h1, trivial⟩
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    split
    · split <;> exact ⟨h1, trivial⟩
    · split <;> exact ⟨h1, trivial⟩
  | ready a b α β =>
    by_cases h : assoc a X.agents = some α
    · rw [XMach.act_ready h]
      refine ⟨take a, ?_⟩
      show a ≠ x
      intro e
      rw [e, h1] at h
      cases h
    · rw [XMach.act_ready_neg h]
      exact ⟨h1, trivial⟩
  | half a b α β =>
    have h2' : a ≠ x := h2
    cases h : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | none =>
      rw [XMach.act_half_none h]
      exact ⟨put a α h2', trivial⟩
    | some R =>
      rw [XMach.act_half h]
      refine ⟨take b, ?_⟩
      show ∀ e ∈ R.newAgents a b, e.1 ≠ x
      intro e he
      by_cases hc : assoc b X.agents = some β ∧ a ≠ b
      · rw [ite_pos' hc] at h
        exact hx h he
      · rw [ite_neg' hc] at h
        cases h
  | write as ls =>
    cases as with
    | cons y as =>
      obtain ⟨i, γ⟩ := y
      have h2' : ∀ e ∈ (i, γ) :: as, e.1 ≠ x := h2
      exact ⟨put i γ (h2' (i, γ) List.mem_cons_self),
        fun e he => h2' e (List.mem_cons_of_mem _ he)⟩
    | nil =>
      cases ls with
      | nil => exact ⟨h1, trivial⟩
      | cons z ls =>
        obtain ⟨p, q⟩ := z
        exact ⟨h1, fun e he => nomatch he⟩

/-- The same along the run of a thread on its own. -/
theorem XMach.solo_gone {x : Id}
    (hx : ∀ {α β : S} {R : XRhs S} {a b : Id} {e : Id × S}, xs.rule α β = some R →
      e ∈ R.newAgents a b → e.1 ≠ x)
    {X : XNet S} {T : XThread S} {u : Nat}
    (h1 : assoc x (XMach.solo xs X T u).1.agents = none)
    (h2 : (XMach.solo xs X T u).2.st.Clear x) :
    ∀ d, assoc x (XMach.solo xs X T (u + d)).1.agents = none ∧
      (XMach.solo xs X T (u + d)).2.st.Clear x
  | 0 => ⟨h1, h2⟩
  | d + 1 => by
    obtain ⟨i1, i2⟩ := XMach.solo_gone hx h1 h2 d
    rw [show u + (d + 1) = u + d + 1 from rfl, XMach.solo_succ]
    exact XMach.act_gone hx i1 i2

/-- **The first five actions of a round on a facing pair**: three that
read, then the two agents are taken. -/
theorem XMach.solo_claim_start {X : XNet S} {a b : Id} {α β : S} {R : XRhs S}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some (b, 0)) (h₃ : assoc b X.agents = some β) (hne : a ≠ b)
    (h₄ : assoc b (X.takeAgent a).agents = some β) (hR : xs.rule α β = some R) :
    (XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 3).1 = X ∧
      XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 5 = ((X.takeAgent a).takeAgent b,
        ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩) := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) (b, 0)⟩, 0) :=
    XMach.act_look h₂
  have s₃ : XMach.act xs X ⟨rest, .seek a α (a, 0) (b, 0)⟩ =
      (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have s₅ : XMach.act xs (X.takeAgent a) ⟨rest, .half a b α β⟩ =
      ((X.takeAgent a).takeAgent b,
        ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) :=
    XMach.act_half (by rw [ite_pos' ⟨h₄, hne⟩]; exact hR)
  have w₃ : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .ready a b α β⟩ 0 3 :=
    .step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₃ (.refl _ _)))
  have w₅ : Works xs X ⟨rest, .ready a b α β⟩ ((X.takeAgent a).takeAgent b)
      ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩ 1 2 :=
    .step (c₁ := 0) (c := 1) (k := 1) (fun h => by cases h) s₄
      (.step (c₁ := 1) (c := 0) (k := 0) (fun h => by cases h) s₅ (.refl _ _))
  refine ⟨?_, (w₃.trans w₅).solo.1⟩
  rw [w₃.solo.1]

/-- The states of a second thread that acts after each action of the
first, as long as it leaves the memory as it is. -/
def XMach.reader (xs : XSys S) (X : XNet S) (T₀ T₁ : XThread S) : Nat → XThread S
  | 0 => T₁
  | a + 1 => (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T₁ a)).2.1

/-- What a sequence of states comes to at the rate `κ`. -/
def seqTally (κ : XThread S → Nat) (R : Nat → XThread S) : Nat → Nat
  | 0 => 0
  | a + 1 => seqTally κ R a + κ (R a)

omit [DecidableEq S] in
theorem seqTally_le {κ : XThread S → Nat} {R : Nat → XThread S} {B : Nat}
    (h1 : ∀ j, κ (R j) ≤ 1) (h2 : ∀ j, κ (R j) ≠ 0 → j < B) :
    ∀ a, seqTally κ R a ≤ a ∧ seqTally κ R a ≤ B
  | 0 => ⟨Nat.le_refl 0, Nat.zero_le B⟩
  | a + 1 => by
    obtain ⟨i1, i2⟩ := seqTally_le h1 h2 a
    have k1 := h1 a
    have k2 := h2 a
    show seqTally κ R a + κ (R a) ≤ a + 1 ∧ seqTally κ R a + κ (R a) ≤ B
    by_cases hz : κ (R a) = 0
    · omega
    · have := k2 hz
      omega

/-- One thread on its own, as a run of the program. -/
theorem XMach.trace_one (xs : XSys S) (X : XNet S) (T : XThread S) :
    ∀ a, ((⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) a).1 =
      ⟨(XMach.solo xs X T a).1, [(XMach.solo xs X T a).2]⟩
  | 0 => rfl
  | a + 1 => by
    have ih := XMach.trace_one xs X T a
    show (XMach.step xs ((⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) a).1 0).1 = _
    rw [ih, XMach.solo_succ]
    rfl

theorem XMach.tally_one (κ : XThread S → Nat) (xs : XSys S) (X : XNet S) (T : XThread S) :
    ∀ a, (⟨X, [T]⟩ : XMach S).tally κ xs (fun _ => 0) a =
      seqTally κ (fun j => (XMach.solo xs X T j).2) a
  | 0 => rfl
  | a + 1 => by
    have ih := XMach.tally_one κ xs X T a
    show (⟨X, [T]⟩ : XMach S).tally κ xs (fun _ => 0) a +
        ((⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) a).1.stepTally κ 0 =
      seqTally κ (fun j => (XMach.solo xs X T j).2) a + κ (XMach.solo xs X T a).2
    rw [ih, XMach.trace_one]
    rfl

/-- A thread that reads: it is idle, or looking for a partner. -/
def TState.Reading : TState S → Prop
  | .idle => True
  | .look _ _ => True
  | .seek _ _ _ _ => True
  | _ => False

/-- A thread that reads keeps its list, or drops the first agent of it. -/
theorem XMach.act_todo_suffix (xs : XSys S) (X : XNet S) {T : XThread S}
    (hT : T.st.Reading) : ∃ pre, pre ++ (XMach.act xs X T).2.1.todo = T.todo := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨[], rfl⟩
    | cons e' rest =>
      by_cases h : assoc e'.1 X.agents = some e'.2
      · rw [XMach.act_idle_pos h]
        exact ⟨[e'], rfl⟩
      · rw [XMach.act_idle_neg h]
        exact ⟨[e'], rfl⟩
  | look a α =>
    cases h : assoc (a, 0) X.wires with
    | none =>
      rw [XMach.act_look_none h]
      exact ⟨[], rfl⟩
    | some q =>
      rw [XMach.act_look h]
      exact ⟨[], rfl⟩
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    split
    · split <;> exact ⟨[], rfl⟩
    · split <;> exact ⟨[], rfl⟩
  | ready a b α β => exact hT.elim
  | half a b α β => exact hT.elim
  | write as ls => exact hT.elim

omit [DecidableEq S] in
/-- The share of a thread that reads: a pass over its list, and one trail
at most. -/
theorem potIn_reading_le (H : Net S) (K A : Nat) {T : XThread S} (hT : T.st.Reading) :
    potIn H K A T ≤ H.scan K T.todo + K + 6 := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    show H.scan K todo ≤ H.scan K todo + K + 6
    omega
  | look a α =>
    have h : H.far K (a, 0) ≤ K + 1 := supBelow_le _ _
    show H.scan K todo + H.far K (a, 0) + 5 ≤ H.scan K todo + K + 6
    omega
  | seek a α p c =>
    have h : H.far K (a, 0) ≤ K + 1 := supBelow_le _ _
    show H.scan K todo + (H.far K (a, 0) - supBelow (TrailLen H a p c) (K + 1)) + 3 ≤
      H.scan K todo + K + 6
    omega
  | ready a b α β => exact hT.elim
  | half a b α β => exact hT.elim
  | write as ls => exact hT.elim

omit [DecidableEq S] in
/-- A pass over the agents in memory costs seven actions for each and one
for each segment of a net that lies ahead. -/
theorem XMach.scan_agents {M : XMach S} (hL : M.Live xs)
    (hnd : (M.mem.agents.map Prod.fst).Nodup) {H : Net S} {K : Nat} (hH : H.Sized K)
    (hM : M.Ahead H) : H.scan K M.mem.agents ≤ 7 * M.mem.agents.length + K := by
  have hG := hL.inv.wf
  have memG : ∀ {i : Id} {γ : S}, (i, γ) ∈ M.mem.agents → M.toMach.goal.agent i γ :=
    fun h => .inl (.inl h)
  exact Net.scan_le hH M.mem.agents hnd fun e he q q' h h' =>
    hG.end_unique (.inr ⟨e.2, memG (i := e.1) (γ := e.2) he, Nat.zero_le _⟩)
      (hM.principal (.inl ⟨e.2, memG (i := e.1) (γ := e.2) he⟩) h)
      (hM.principal (.inl ⟨e.2, memG (i := e.1) (γ := e.2) he⟩) h')

/-- A pass over agents of the net at the start costs as much, measured in
its normal form. -/
theorem XNet.scan_start {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D) {n : Nat}
    {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') :
    N'.scan (X.wires.length + D * n) X.agents ≤
      7 * X.agents.length + (X.wires.length + D * n) := by
  have hH := XNet.normal_sized hX hb hs hn
  obtain ⟨-, pr⟩ := Steps.links hX hs
  have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
  exact Net.scan_le hH X.agents hnd fun e he q q' h h' =>
    hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
      (pr (.inl ⟨e.2, hag e he⟩) h')

/-- **What holds at every moment of a run**, whatever the schedule: the
program is live, no agent is listed twice, the normal form lies ahead, and
the agents and the claims are bounded. -/
theorem XMach.run_facts {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    N'.Sized (X.wires.length + D * n) ∧
      ∀ i, ((XMach.init X nt).trace xs σ i).1.Live xs ∧
        (((XMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup ∧
        ((XMach.init X nt).trace xs σ i).1.Ahead N' ∧
        ((XMach.init X nt).trace xs σ i).1.heads ≤ X.agents.length + C * n ∧
        ((XMach.init X nt).trace xs σ i).2 ≤ n := by
  have live := XMach.trace_live (xs := xs) σ (XMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((XMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((XMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := XMach.trace_run xs σ (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((XMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  obtain ⟨is, ih⟩ := XMach.init_sizes X nt
  have sizes := XMach.seq_sizes (xs := xs) ((XMach.init X nt).trace xs σ) σ (fun _ => rfl)
    live hb (W := X.wires.length) (A₀ := X.agents.length)
    ⟨Nat.le_trans (Nat.le_of_eq is) (Nat.le_add_right _ _),
      Nat.le_trans (Nat.le_of_eq ih) (Nat.le_add_right _ _)⟩
  have hA : ∀ i, ((XMach.init X nt).trace xs σ i).1.heads ≤ X.agents.length + C * n :=
    fun i => Nat.le_trans (sizes i).2
      (Nat.add_le_add_left (Nat.mul_le_mul_left C (bound i)) _)
  have nd : ∀ i, (((XMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact XMach.step_nodup (live i) ih (σ i)
  have hH := XNet.normal_sized hX hb hs hn
  have ahead : ∀ i, ((XMach.init X nt).trace xs σ i).1.Ahead N' :=
    fun i => XMach.ahead_of_run (live i).inv hX (run i) hs hn
  exact ⟨hH, fun i => ⟨live i, nd i, ahead i, hA i, bound i⟩⟩

/-- **The measure of the general bound, in the open**: the work done, the
shares of the threads, and a pass and the writes of a rule for each claim
still to come, never go up together. -/
theorem XMach.work_energy {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    (XMach.init X nt).work xs σ (i + 1) +
        (((XMach.init X nt).trace xs σ (i + 1)).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + C * n) +
          (n - ((XMach.init X nt).trace xs σ (i + 1)).2) *
            (C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1)) ≤
      (XMach.init X nt).work xs σ i +
        (((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + C * n) +
          (n - ((XMach.init X nt).trace xs σ i).2) *
            (C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1)) := by
  obtain ⟨hH, hf⟩ := XMach.run_facts hX hnd hnt hb hs hn σ
  obtain ⟨live, nd, ahead, hA, -⟩ := hf i
  have hb1 : ((XMach.init X nt).trace xs σ i).2 +
      (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2 ≤ n := (hf (i + 1)).2.2.2.2
  have hbz := XMach.stepTally_busy_le ((XMach.init X nt).trace xs σ i).1 (σ i)
  show (XMach.init X nt).work xs σ i +
        ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i) +
      ((((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.energyIn N'
          (X.wires.length + D * n) (X.agents.length + C * n) +
        (n - (((XMach.init X nt).trace xs σ i).2 +
          (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) *
          (C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1)) ≤ _
  rcases XMach.step_work live nd hb hH ahead hA (σ i) with ⟨e, hz⟩ | ⟨h1, hce⟩ | ⟨h0, hlt⟩
  · rw [XMach.stepTally_busy_rest hz, e]
    exact Nat.le_refl _
  · rw [h1] at hb1 ⊢
    have e1 : n - ((XMach.init X nt).trace xs σ i).2 =
        (n - (((XMach.init X nt).trace xs σ i).2 + 1)) + 1 := by omega
    rw [e1, Nat.add_mul, Nat.one_mul]
    omega
  · rw [h0, Nat.add_zero]
    omega

/-- **The work from any moment on**: no more than the shares of the
threads at that moment, and a pass and the writes of a rule for each claim
still to come.  The general bound is this at the start, where all the
claims are still to come. -/
theorem XMach.work_tail {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (t : Nat) (d : Nat) :
    (XMach.init X nt).work xs σ (t + d) ≤
      (XMach.init X nt).work xs σ t +
        (((XMach.init X nt).trace xs σ t).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + C * n) +
          (n - ((XMach.init X nt).trace xs σ t).2) *
            (C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1)) := by
  have key : ∀ d, (XMach.init X nt).work xs σ (t + d) +
        (((XMach.init X nt).trace xs σ (t + d)).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + C * n) +
          (n - ((XMach.init X nt).trace xs σ (t + d)).2) *
            (C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1)) ≤
      (XMach.init X nt).work xs σ t +
        (((XMach.init X nt).trace xs σ t).1.energyIn N' (X.wires.length + D * n)
            (X.agents.length + C * n) +
          (n - ((XMach.init X nt).trace xs σ t).2) *
            (C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1)) := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans (XMach.work_energy hX hnd hnt hb hs hn σ (t + d)) ih
  exact Nat.le_trans (Nat.le_add_right _ _) (key d)

/-- The work is at most the number of actions. -/
theorem XMach.work_le_count (xs : XSys S) (σ : Nat → Nat) (M : XMach S) :
    ∀ i, M.work xs σ i ≤ i
  | 0 => Nat.le_refl 0
  | i + 1 => by
    have ih := XMach.work_le_count xs σ M i
    have h := XMach.stepTally_busy_le (M.trace xs σ i).1 (σ i)
    show M.work xs σ i + (M.trace xs σ i).1.stepTally XThread.busy (σ i) ≤ i + 1
    omega

/-- **From a moment where one thread starts a pass and the others read.**
Suppose that after `t` actions, however scheduled, the first thread is
idle with the list of the agents in memory, every other thread reads and
its list is an end of a turn of the first list, and `c` claims are made.
Then the work never passes `t`, a pass for the first thread, two passes
for each other thread, and a pass and the writes of a rule for each claim
still to come. -/
theorem XMach.work_after_reading {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {t c : Nat} {Xt : XNet S}
    {Rs : List (XThread S)}
    (hst : ((XMach.init X nt).trace xs σ t).1 = ⟨Xt, ⟨Xt.agents, .idle⟩ :: Rs⟩)
    (hc : ((XMach.init X nt).trace xs σ t).2 = c)
    (hR : ∀ R, R ∈ Rs → R.st.Reading ∧
      ∃ pre k, pre ++ R.todo = X.agents.drop k ++ X.agents.take k) (i : Nat) :
    (XMach.init X nt).work xs σ i ≤
      t + (7 * (X.agents.length + C * n) + (X.wires.length + D * n)) +
        Rs.length *
          (7 * X.agents.length + (X.wires.length + D * n) + (X.wires.length + D * n) + 6) +
        (n - c) * (C + D + 7 * (X.agents.length + C * n) + (X.wires.length + D * n) + 1) := by
  obtain ⟨hH, hf⟩ := XMach.run_facts hX hnd hnt hb hs hn σ
  obtain ⟨live, nd, ahead, hA, -⟩ := hf t
  have sc := XMach.scan_agents live nd hH ahead
  rw [hst] at sc hA
  have sc' : N'.scan (X.wires.length + D * n) Xt.agents ≤
      7 * Xt.agents.length + (X.wires.length + D * n) := sc
  have hA' : Xt.agents.length ≤ X.agents.length + C * n :=
    Nat.le_trans (Nat.le_add_right _ _) hA
  have s0 := XNet.scan_start hX hnd hb hs hn
  have each : ∀ R, R ∈ Rs →
      potIn N' (X.wires.length + D * n) (X.agents.length + C * n) R ≤
        7 * X.agents.length + (X.wires.length + D * n) + (X.wires.length + D * n) + 6 := by
    intro R hRm
    obtain ⟨hr, pre, k, hp⟩ := hR R hRm
    have h1 := Net.scan_append N' (X.wires.length + D * n) pre R.todo
    have h2 : N'.scan (X.wires.length + D * n) X.agents =
        N'.scan (X.wires.length + D * n) (X.agents.take k) +
          N'.scan (X.wires.length + D * n) (X.agents.drop k) := by
      rw [← Net.scan_append, List.take_append_drop]
    rw [hp, Net.scan_append] at h1
    have pr := potIn_reading_le N' (X.wires.length + D * n) (X.agents.length + C * n) hr
    omega
  have tot := total_le_mul (f := potIn N' (X.wires.length + D * n) (X.agents.length + C * n))
    each
  have tail := XMach.work_tail hX hnd hnt hb hs hn σ t i
  rw [hst, hc] at tail
  have een : (⟨Xt, ⟨Xt.agents, .idle⟩ :: Rs⟩ : XMach S).energyIn N' (X.wires.length + D * n)
      (X.agents.length + C * n) = N'.scan (X.wires.length + D * n) Xt.agents +
        total (potIn N' (X.wires.length + D * n) (X.agents.length + C * n)) Rs := rfl
  rw [een] at tail
  have mono := XMach.work_mono (xs := xs) σ (XMach.init X nt) (show i ≤ t + i by omega)
  have cnt := XMach.work_le_count xs σ (XMach.init X nt) t
  omega

/-- The first six actions of a round on a pair one point away: four that
read, then the two agents are taken. -/
theorem Works.via_start {X : XNet S} {a b : Id} {α β : S} {R : XRhs S} {c : Port}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some c)
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂' : nextSeg X.wires c (a, 0) = some (b, 0)) (h₃ : assoc b X.agents = some β)
    (hne : a ≠ b) (h₄ : assoc b (X.takeAgent a).agents = some β)
    (hR : xs.rule α β = some R) :
    Works xs X ⟨(a, α) :: rest, .idle⟩ ((X.takeAgent a).takeAgent b)
      ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩ 1 6 := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) c⟩, 0) :=
    XMach.act_look h₂
  have s₂' : XMach.act xs X ⟨rest, .seek a α (a, 0) c⟩ =
      (X, ⟨rest, .seek a α c (b, 0)⟩, 0) := XMach.act_seek_next hc h₂'
  have s₃ : XMach.act xs X ⟨rest, .seek a α c (b, 0)⟩ = (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have s₅ : XMach.act xs (X.takeAgent a) ⟨rest, .half a b α β⟩ =
      ((X.takeAgent a).takeAgent b,
        ⟨rest, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1) :=
    XMach.act_half (by rw [ite_pos' ⟨h₄, hne⟩]; exact hR)
  exact .step (c₁ := 0) (c := 1) (k := 5) (fun h => by cases h) s₁
    (.step (c₁ := 0) (c := 1) (k := 4) (fun h => by cases h) s₂
      (.step (c₁ := 0) (c := 1) (k := 3) (fun h => by cases h) s₂'
        (.step (c₁ := 0) (c := 1) (k := 2) (fun h => by cases h) s₃
          (.step (c₁ := 0) (c := 1) (k := 1) (fun h => by cases h) s₄
            (.step (c₁ := 1) (c := 0) (k := 0) (fun h => by cases h) s₅ (.refl _ _))))))

theorem get_after {A : Type} : ∀ (pre : List A) (x : A) (l : List A),
    (pre ++ x :: l)[pre.length]? = some x
  | [], _, _ => rfl
  | _ :: pre, x, l => get_after pre x l

theorem set_after {A : Type} : ∀ (pre : List A) (x y : A) (l : List A),
    (pre ++ x :: l).set pre.length y = pre ++ y :: l
  | [], _, _, _ => rfl
  | a :: pre, x, y, l => congrArg (a :: ·) (set_after pre x y l)

omit [DecidableEq S] in
theorem total_map (f : XThread S → Nat) (g : XThread S → XThread S) :
    ∀ ths : List (XThread S), total f (ths.map g) = total (fun T => f (g T)) ths
  | [] => rfl
  | T :: ths => congrArg (f (g T) + ·) (total_map f g ths)

omit [DecidableEq S] in
theorem total_add (f g : XThread S → Nat) :
    ∀ ths : List (XThread S), total (fun T => f T + g T) ths = total f ths + total g ths
  | [] => rfl
  | T :: ths => by
    show f T + g T + total (fun T => f T + g T) ths = f T + total f ths + (g T + total g ths)
    rw [total_add f g ths]
    omega

omit [DecidableEq S] in
theorem total_zero : ∀ ths : List (XThread S), total (fun _ => 0) ths = 0
  | [] => rfl
  | _ :: ths => by
    show 0 + total (fun _ => 0) ths = 0
    rw [total_zero ths]

/-- The first of a row of threads that read acts: the memory stays, and
the thread joins those that have acted. -/
theorem XMach.sweep_first (xs : XSys S) (Y : XNet S) (pre : List (XThread S)) (R : XThread S)
    (Rs : List (XThread S)) (h1 : (XMach.act xs Y R).1 = Y)
    (h0 : (XMach.act xs Y R).2.2 = 0) :
    (⟨Y, pre ++ R :: Rs⟩ : XMach S).trace xs (fun i => pre.length + i) 1 =
      (⟨Y, (pre ++ [(XMach.act xs Y R).2.1]) ++ Rs⟩, 0) := by
  have st0 : XMach.step xs ⟨Y, pre ++ R :: Rs⟩ pre.length =
      (⟨(XMach.act xs Y R).1, (pre ++ R :: Rs).set pre.length (XMach.act xs Y R).2.1⟩,
        (XMach.act xs Y R).2.2) :=
    XMach.step_eq (M := ⟨Y, pre ++ R :: Rs⟩) (get_after pre R Rs) rfl
  have st : XMach.step xs ⟨Y, pre ++ R :: Rs⟩ pre.length =
      (⟨Y, (pre ++ [(XMach.act xs Y R).2.1]) ++ Rs⟩, 0) := by
    rw [st0, h1, h0, set_after, List.append_assoc]
    rfl
  show ((XMach.step xs ⟨Y, pre ++ R :: Rs⟩ (pre.length + 0)).1,
    0 + (XMach.step xs ⟨Y, pre ++ R :: Rs⟩ (pre.length + 0)).2) = _
  rw [Nat.add_zero, st]
  rfl

theorem sweep_sched {A : Type} (pre : List A) (x : A) (j : Nat) :
    pre.length + (1 + j) = (pre ++ [x]).length + j := by
  rw [List.length_append]
  show pre.length + (1 + j) = pre.length + 1 + j
  omega

/-- **A row of threads that read, one after the other**: each acts once,
the memory stays as it is, and no claim is made. -/
theorem XMach.trace_sweep (xs : XSys S) (Y : XNet S) : ∀ (Rs pre : List (XThread S)),
    (∀ R, R ∈ Rs → (XMach.act xs Y R).1 = Y ∧ (XMach.act xs Y R).2.2 = 0) →
    (⟨Y, pre ++ Rs⟩ : XMach S).trace xs (fun i => pre.length + i) Rs.length =
      (⟨Y, pre ++ Rs.map fun R => (XMach.act xs Y R).2.1⟩, 0)
  | [], _, _ => rfl
  | R :: Rs, pre, h => by
    obtain ⟨h1, h0⟩ := h R List.mem_cons_self
    have t1 := XMach.sweep_first xs Y pre R Rs h1 h0
    have ih := XMach.trace_sweep xs Y Rs (pre ++ [(XMach.act xs Y R).2.1])
      fun R' hR' => h R' (List.mem_cons_of_mem _ hR')
    have cg := XMach.trace_congr xs
      (⟨Y, (pre ++ [(XMach.act xs Y R).2.1]) ++ Rs⟩ : XMach S)
      (σ := fun i => pre.length + (1 + i))
      (σ' := fun i => (pre ++ [(XMach.act xs Y R).2.1]).length + i) Rs.length
      (fun j _ => sweep_sched pre _ j)
    show (⟨Y, pre ++ R :: Rs⟩ : XMach S).trace xs (fun i => pre.length + i)
      (Rs.length + 1) = _
    rw [Nat.add_comm Rs.length 1, XMach.trace_add xs (fun i => pre.length + i) _ 1 Rs.length,
      t1]
    show ((XMach.trace xs (fun i => pre.length + (1 + i))
        (⟨Y, (pre ++ [(XMach.act xs Y R).2.1]) ++ Rs⟩ : XMach S) Rs.length).1,
      0 + (XMach.trace xs (fun i => pre.length + (1 + i))
        (⟨Y, (pre ++ [(XMach.act xs Y R).2.1]) ++ Rs⟩ : XMach S) Rs.length).2) = _
    rw [cg, ih, List.append_assoc]
    rfl

/-- What such a row comes to: what each thread comes to. -/
theorem XMach.tally_sweep (κ : XThread S → Nat) (xs : XSys S) (Y : XNet S) :
    ∀ (Rs pre : List (XThread S)),
    (∀ R, R ∈ Rs → (XMach.act xs Y R).1 = Y ∧ (XMach.act xs Y R).2.2 = 0) →
    (⟨Y, pre ++ Rs⟩ : XMach S).tally κ xs (fun i => pre.length + i) Rs.length = total κ Rs
  | [], _, _ => rfl
  | R :: Rs, pre, h => by
    obtain ⟨h1, h0⟩ := h R List.mem_cons_self
    have t1 := XMach.sweep_first xs Y pre R Rs h1 h0
    have ih := XMach.tally_sweep κ xs Y Rs (pre ++ [(XMach.act xs Y R).2.1])
      fun R' hR' => h R' (List.mem_cons_of_mem _ hR')
    have cg := XMach.tally_congr κ xs
      (⟨Y, (pre ++ [(XMach.act xs Y R).2.1]) ++ Rs⟩ : XMach S)
      (σ := fun i => pre.length + (1 + i))
      (σ' := fun i => (pre ++ [(XMach.act xs Y R).2.1]).length + i) Rs.length
      (fun j _ => sweep_sched pre _ j)
    have sT : (⟨Y, pre ++ R :: Rs⟩ : XMach S).stepTally κ pre.length = κ R := by
      unfold XMach.stepTally
      rw [get_after]
    show (⟨Y, pre ++ R :: Rs⟩ : XMach S).tally κ xs (fun i => pre.length + i)
      (Rs.length + 1) = κ R + total κ Rs
    rw [Nat.add_comm Rs.length 1, XMach.tally_add κ xs (fun i => pre.length + i) _ 1 Rs.length,
      t1]
    show (0 + (⟨Y, pre ++ R :: Rs⟩ : XMach S).stepTally κ (pre.length + 0)) +
      XMach.tally κ xs (fun i => pre.length + (1 + i))
        (⟨Y, (pre ++ [(XMach.act xs Y R).2.1]) ++ Rs⟩ : XMach S) Rs.length = _
    rw [cg, ih, Nat.add_zero, sT, Nat.zero_add]

/-- **One turn of each thread, all but the first reading**: the first
acts, then each of the others, in the memory the first leaves. -/
theorem XMach.trace_round_readers (xs : XSys S) (Y : XNet S) (P : XThread S)
    (Rs : List (XThread S))
    (h : ∀ R, R ∈ Rs → (XMach.act xs (XMach.act xs Y P).1 R).1 = (XMach.act xs Y P).1 ∧
      (XMach.act xs (XMach.act xs Y P).1 R).2.2 = 0) :
    (⟨Y, P :: Rs⟩ : XMach S).trace xs (fun i => i) (Rs.length + 1) =
      (⟨(XMach.act xs Y P).1, (XMach.act xs Y P).2.1 ::
          Rs.map fun R => (XMach.act xs (XMach.act xs Y P).1 R).2.1⟩,
        (XMach.act xs Y P).2.2) := by
  have sw := XMach.trace_sweep xs (XMach.act xs Y P).1 Rs [(XMach.act xs Y P).2.1] h
  rw [Nat.add_comm Rs.length 1, XMach.trace_add xs (fun i => i) _ 1 Rs.length]
  show ((XMach.trace xs (fun i => 1 + i)
      (⟨(XMach.act xs Y P).1, (XMach.act xs Y P).2.1 :: Rs⟩ : XMach S) Rs.length).1,
    0 + (XMach.act xs Y P).2.2 + (XMach.trace xs (fun i => 1 + i)
      (⟨(XMach.act xs Y P).1, (XMach.act xs Y P).2.1 :: Rs⟩ : XMach S) Rs.length).2) = _
  rw [show XMach.trace xs (fun i => 1 + i)
    (⟨(XMach.act xs Y P).1, (XMach.act xs Y P).2.1 :: Rs⟩ : XMach S) Rs.length = _ from sw,
    Nat.zero_add]
  rfl

theorem XMach.tally_round_readers (κ : XThread S → Nat) (xs : XSys S) (Y : XNet S)
    (P : XThread S) (Rs : List (XThread S))
    (h : ∀ R, R ∈ Rs → (XMach.act xs (XMach.act xs Y P).1 R).1 = (XMach.act xs Y P).1 ∧
      (XMach.act xs (XMach.act xs Y P).1 R).2.2 = 0) :
    (⟨Y, P :: Rs⟩ : XMach S).tally κ xs (fun i => i) (Rs.length + 1) = κ P + total κ Rs := by
  have sw := XMach.tally_sweep κ xs (XMach.act xs Y P).1 Rs [(XMach.act xs Y P).2.1] h
  rw [Nat.add_comm Rs.length 1, XMach.tally_add κ xs (fun i => i) _ 1 Rs.length]
  show (0 + κ P) + XMach.tally κ xs (fun i => 1 + i)
    (⟨(XMach.act xs Y P).1, (XMach.act xs Y P).2.1 :: Rs⟩ : XMach S) Rs.length = _
  rw [show XMach.tally κ xs (fun i => 1 + i)
    (⟨(XMach.act xs Y P).1, (XMach.act xs Y P).2.1 :: Rs⟩ : XMach S) Rs.length = _ from sw,
    Nat.zero_add]

/-- **Threads in turn, all but the first only reading**: after each has
acted `a` times the memory, the first thread and the claims are those of
the first thread running alone, as long as the others have left the
memory as it is and made no claim. -/
theorem XMach.trace_readers {X : XNet S} {T₀ : XThread S} {Ts : List (XThread S)} {A : Nat}
    (h : ∀ T, T ∈ Ts → ∀ a, a < A →
      (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).1 =
          (XMach.solo xs X T₀ (a + 1)).1 ∧
        (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).2.2 = 0) :
    ∀ a, a ≤ A → (⟨X, T₀ :: Ts⟩ : XMach S).trace xs (fun i => i % (Ts.length + 1))
        ((Ts.length + 1) * a) =
      (⟨(XMach.solo xs X T₀ a).1, (XMach.solo xs X T₀ a).2 ::
          Ts.map fun T => XMach.reader xs X T₀ T a⟩,
        ((⟨X, [T₀]⟩ : XMach S).trace xs (fun _ => 0) a).2)
  | 0, _ => by
    have e : Ts.map (fun T => XMach.reader xs X T₀ T 0) = Ts := List.map_id' Ts
    rw [Nat.mul_zero, e]
    rfl
  | a + 1, ha => by
    have ih := XMach.trace_readers h a (Nat.le_of_succ_le ha)
    have t1 := XMach.trace_one xs X T₀ a
    have a1 : (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1 =
        (XMach.solo xs X T₀ (a + 1)).1 := by rw [XMach.solo_succ]
    have a2 : (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).2.1 =
        (XMach.solo xs X T₀ (a + 1)).2 := by rw [XMach.solo_succ]
    have hr : ∀ R, R ∈ Ts.map (fun T => XMach.reader xs X T₀ T a) →
        (XMach.act xs (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1
            R).1 = (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1 ∧
          (XMach.act xs (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1
            R).2.2 = 0 := by
      intro R hR
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hR
      rw [a1]
      exact h T hT a ha
    have rd := XMach.trace_round_readers xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2
      (Ts.map fun T => XMach.reader xs X T₀ T a) hr
    rw [List.length_map] at rd
    have cg := XMach.trace_congr xs
      (⟨(XMach.solo xs X T₀ a).1, (XMach.solo xs X T₀ a).2 ::
        Ts.map fun T => XMach.reader xs X T₀ T a⟩ : XMach S)
      (σ := fun i => ((Ts.length + 1) * a + i) % (Ts.length + 1)) (σ' := fun i => i)
      (Ts.length + 1) (fun j hj => by
        show ((Ts.length + 1) * a + j) % (Ts.length + 1) = j
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj])
    rw [Nat.mul_succ, XMach.trace_add xs (fun i => i % (Ts.length + 1)) _
      ((Ts.length + 1) * a) (Ts.length + 1), ih]
    show ((XMach.trace xs (fun i => ((Ts.length + 1) * a + i) % (Ts.length + 1))
        (⟨(XMach.solo xs X T₀ a).1, (XMach.solo xs X T₀ a).2 ::
          Ts.map fun T => XMach.reader xs X T₀ T a⟩ : XMach S) (Ts.length + 1)).1,
      ((⟨X, [T₀]⟩ : XMach S).trace xs (fun _ => 0) a).2 +
        (XMach.trace xs (fun i => ((Ts.length + 1) * a + i) % (Ts.length + 1))
          (⟨(XMach.solo xs X T₀ a).1, (XMach.solo xs X T₀ a).2 ::
            Ts.map fun T => XMach.reader xs X T₀ T a⟩ : XMach S) (Ts.length + 1)).2) = _
    rw [cg, rd, List.map_map, a1, a2]
    show (_, ((⟨X, [T₀]⟩ : XMach S).trace xs (fun _ => 0) a).2 +
        (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).2.2) =
      (_, ((⟨X, [T₀]⟩ : XMach S).trace xs (fun _ => 0) a).2 +
        (XMach.step xs ((⟨X, [T₀]⟩ : XMach S).trace xs (fun _ => 0) a).1 0).2)
    rw [t1]
    rfl

/-- What such a run comes to: the states of the first thread alone, and
the states of each of the others. -/
theorem XMach.tally_readers (κ : XThread S → Nat) {X : XNet S} {T₀ : XThread S}
    {Ts : List (XThread S)} {A : Nat}
    (h : ∀ T, T ∈ Ts → ∀ a, a < A →
      (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).1 =
          (XMach.solo xs X T₀ (a + 1)).1 ∧
        (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).2.2 = 0) :
    ∀ a, a ≤ A → (⟨X, T₀ :: Ts⟩ : XMach S).tally κ xs (fun i => i % (Ts.length + 1))
        ((Ts.length + 1) * a) =
      seqTally κ (fun j => (XMach.solo xs X T₀ j).2) a +
        total (fun T => seqTally κ (XMach.reader xs X T₀ T) a) Ts
  | 0, _ => by
    rw [Nat.mul_zero]
    show 0 = 0 + total (fun _ => 0) Ts
    rw [total_zero]
  | a + 1, ha => by
    have ih := XMach.tally_readers κ h a (Nat.le_of_succ_le ha)
    have tr := XMach.trace_readers h a (Nat.le_of_succ_le ha)
    have a1 : (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1 =
        (XMach.solo xs X T₀ (a + 1)).1 := by rw [XMach.solo_succ]
    have hr : ∀ R, R ∈ Ts.map (fun T => XMach.reader xs X T₀ T a) →
        (XMach.act xs (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1
            R).1 = (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1 ∧
          (XMach.act xs (XMach.act xs (XMach.solo xs X T₀ a).1 (XMach.solo xs X T₀ a).2).1
            R).2.2 = 0 := by
      intro R hR
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hR
      rw [a1]
      exact h T hT a ha
    have rd := XMach.tally_round_readers κ xs (XMach.solo xs X T₀ a).1
      (XMach.solo xs X T₀ a).2 (Ts.map fun T => XMach.reader xs X T₀ T a) hr
    rw [List.length_map] at rd
    have cg := XMach.tally_congr κ xs
      (⟨(XMach.solo xs X T₀ a).1, (XMach.solo xs X T₀ a).2 ::
        Ts.map fun T => XMach.reader xs X T₀ T a⟩ : XMach S)
      (σ := fun i => ((Ts.length + 1) * a + i) % (Ts.length + 1)) (σ' := fun i => i)
      (Ts.length + 1) (fun j hj => by
        show ((Ts.length + 1) * a + j) % (Ts.length + 1) = j
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj])
    rw [Nat.mul_succ, XMach.tally_add κ xs (fun i => i % (Ts.length + 1)) _
      ((Ts.length + 1) * a) (Ts.length + 1), ih, tr]
    show seqTally κ (fun j => (XMach.solo xs X T₀ j).2) a +
        total (fun T => seqTally κ (XMach.reader xs X T₀ T) a) Ts +
        XMach.tally κ xs (fun i => ((Ts.length + 1) * a + i) % (Ts.length + 1))
          (⟨(XMach.solo xs X T₀ a).1, (XMach.solo xs X T₀ a).2 ::
            Ts.map fun T => XMach.reader xs X T₀ T a⟩ : XMach S) (Ts.length + 1) =
      (seqTally κ (fun j => (XMach.solo xs X T₀ j).2) a + κ (XMach.solo xs X T₀ a).2) +
        total (fun T => seqTally κ (XMach.reader xs X T₀ T) a +
          κ (XMach.reader xs X T₀ T a)) Ts
    rw [cg, rd, total_map, total_add]
    omega

/-- **Threads in turn, all but the first only reading, do the work of the
first alone and the actions of the others**: at most `B` more for each,
if each is at rest from its `B`-th action on. -/
theorem XMach.work_readers {X : XNet S} {T₀ : XThread S} {Ts : List (XThread S)} {B : Nat}
    (h : ∀ T, T ∈ Ts → ∀ a,
      (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).1 =
          (XMach.solo xs X T₀ (a + 1)).1 ∧
        (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).2.2 = 0)
    (hB : ∀ T, T ∈ Ts → ∀ a, XMach.reader xs X T₀ T a ≠ ⟨[], .idle⟩ → a < B) (i : Nat) :
    (⟨X, T₀ :: Ts⟩ : XMach S).work xs (fun i => i % (Ts.length + 1)) i ≤
      (⟨X, [T₀]⟩ : XMach S).work xs (fun _ => 0) i + Ts.length * B := by
  have hm := XMach.work_mono (xs := xs) (fun i => i % (Ts.length + 1)) ⟨X, T₀ :: Ts⟩
    (show i ≤ (Ts.length + 1) * i from Nat.le_mul_of_pos_left i (Nat.succ_pos Ts.length))
  have ht : (⟨X, T₀ :: Ts⟩ : XMach S).work xs (fun i => i % (Ts.length + 1))
      ((Ts.length + 1) * i) =
      seqTally XThread.busy (fun j => (XMach.solo xs X T₀ j).2) i +
        total (fun T => seqTally XThread.busy (XMach.reader xs X T₀ T) i) Ts :=
    XMach.tally_readers XThread.busy (A := i) (fun T hT a _ => h T hT a) i (Nat.le_refl i)
  have e1 : (⟨X, [T₀]⟩ : XMach S).work xs (fun _ => 0) i =
      seqTally XThread.busy (fun j => (XMach.solo xs X T₀ j).2) i :=
    XMach.tally_one XThread.busy xs X T₀ i
  have tot : total (fun T => seqTally XThread.busy (XMach.reader xs X T₀ T) i) Ts ≤
      Ts.length * B :=
    total_le_mul fun T hT =>
      (seqTally_le (κ := XThread.busy) (R := XMach.reader xs X T₀ T) (B := B)
        (fun j => XThread.busy_le _)
        (fun j hj => hB T hT j fun e => hj (by rw [e]; rfl)) i).2
  omega

/-- And no less than the work of the first alone. -/
theorem XMach.work_readers_ge {X : XNet S} {T₀ : XThread S} {Ts : List (XThread S)}
    (h : ∀ T, T ∈ Ts → ∀ a,
      (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).1 =
          (XMach.solo xs X T₀ (a + 1)).1 ∧
        (XMach.act xs (XMach.solo xs X T₀ (a + 1)).1 (XMach.reader xs X T₀ T a)).2.2 = 0)
    (a : Nat) :
    (⟨X, [T₀]⟩ : XMach S).work xs (fun _ => 0) a ≤
      (⟨X, T₀ :: Ts⟩ : XMach S).work xs (fun i => i % (Ts.length + 1))
        ((Ts.length + 1) * a) := by
  have ht : (⟨X, T₀ :: Ts⟩ : XMach S).work xs (fun i => i % (Ts.length + 1))
      ((Ts.length + 1) * a) =
      seqTally XThread.busy (fun j => (XMach.solo xs X T₀ j).2) a +
        total (fun T => seqTally XThread.busy (XMach.reader xs X T₀ T) a) Ts :=
    XMach.tally_readers XThread.busy (A := a) (fun T hT a _ => h T hT a) a (Nat.le_refl a)
  have e1 : (⟨X, [T₀]⟩ : XMach S).work xs (fun _ => 0) a =
      seqTally XThread.busy (fun j => (XMach.solo xs X T₀ j).2) a :=
    XMach.tally_one XThread.busy xs X T₀ a
  omega

omit [DecidableEq S] in
/-- The threads at the start: the first has the list of agents, and the
thread numbered `t + 1` has it turned by `t + 1`. -/
theorem XMach.init_succ (X : XNet S) (k : Nat) :
    XMach.init X (k + 1) = ⟨X, ⟨X.agents, .idle⟩ ::
      (List.range k).map fun t => ⟨X.agents.drop (t + 1) ++ X.agents.take (t + 1), .idle⟩⟩ := by
  show (⟨X, (List.range (k + 1)).map
    fun t => ⟨X.agents.drop t ++ X.agents.take t, .idle⟩⟩ : XMach S) = _
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  show (⟨X, ⟨X.agents ++ [], .idle⟩ :: _⟩ : XMach S) = _
  rw [List.append_nil]
  rfl

/-- A run of one thread in two parts. -/
theorem XMach.solo_add (xs : XSys S) : ∀ (j₁ : Nat) (X : XNet S) (T : XThread S) (j₂ : Nat),
    XMach.solo xs X T (j₁ + j₂) =
      XMach.solo xs (XMach.solo xs X T j₁).1 (XMach.solo xs X T j₁).2 j₂
  | 0, X, T, j₂ => by
    rw [Nat.zero_add]
    rfl
  | j₁ + 1, X, T, j₂ => by
    rw [Nat.add_right_comm]
    exact XMach.solo_add xs j₁ (XMach.act xs X T).1 (XMach.act xs X T).2.1 j₂

/-- Writing segments takes no agent away. -/
theorem XMach.solo_links_keep (xs : XSys S) {x : Id} {γ : S} (rest : List (Id × S)) :
    ∀ (ls : List (Port × Port)) (Y : XNet S) (j : Nat), j ≤ ls.length + 1 →
      assoc x Y.agents = some γ →
      assoc x (XMach.solo xs Y ⟨rest, .write [] ls⟩ j).1.agents = some γ
  | _, _, 0, _, h => h
  | [], Y, j + 1, hj, h => by
    have e : j = 0 := by
      have : j + 1 ≤ 0 + 1 := hj
      omega
    subst e
    exact h
  | (p, q) :: ls, Y, j + 1, hj, h =>
    XMach.solo_links_keep xs rest ls (Y.putLink p q) j (Nat.le_of_succ_le_succ hj) h

/-- **The writes of a round take no agent away**: an agent that no new
agent is named after is there after each of them. -/
theorem XMach.solo_write_keeps (xs : XSys S) {x : Id} {γ : S} (rest : List (Id × S)) :
    ∀ (as : List (Id × S)) (ls : List (Port × Port)) (Y : XNet S) (j : Nat),
      j ≤ as.length + ls.length + 1 → (∀ e ∈ as, e.1 ≠ x) → assoc x Y.agents = some γ →
      assoc x (XMach.solo xs Y ⟨rest, .write as ls⟩ j).1.agents = some γ
  | _, _, _, 0, _, _, h => h
  | [], ls, Y, j + 1, hj, _, h =>
    XMach.solo_links_keep xs rest ls Y (j + 1) (by
      have h' : j + 1 ≤ 0 + ls.length + 1 := hj
      omega) h
  | (i, δ) :: as, ls, Y, j + 1, hj, hn, h =>
    XMach.solo_write_keeps xs rest as ls (Y.putAgent i δ) j (by
      have h' : j + 1 ≤ as.length + 1 + ls.length + 1 := hj
      omega) (fun e he => hn e (List.mem_cons_of_mem _ he)) (by
      show (if i = x then some δ else assoc x Y.agents) = some γ
      rw [ite_neg' (hn (i, δ) List.mem_cons_self)]
      exact h)

/-- **A round on a facing pair takes only its pair**: any other agent is
there after each action of the round. -/
theorem XMach.solo_direct_keeps {X : XNet S} {a b : Id} {α β : S} {R : XRhs S}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some (b, 0)) (h₃ : assoc b X.agents = some β) (hne : a ≠ b)
    (h₄ : assoc b (X.takeAgent a).agents = some β) (hR : xs.rule α β = some R)
    {x : Id} {γ : S} (hx : assoc x X.agents = some γ) (hxa : a ≠ x) (hxb : b ≠ x)
    (hnew : ∀ e ∈ R.newAgents a b, e.1 ≠ x) (j : Nat)
    (hj : j ≤ 5 + ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1)) :
    assoc x (XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ j).1.agents = some γ := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) (b, 0)⟩, 0) :=
    XMach.act_look h₂
  have s₃ : XMach.act xs X ⟨rest, .seek a α (a, 0) (b, 0)⟩ =
      (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have w1 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .look a α⟩ 0 1 :=
    .step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₁ (.refl _ _)
  have w2 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .seek a α (a, 0) (b, 0)⟩ 0 2 :=
    .step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₂ (.refl _ _))
  have w3 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .ready a b α β⟩ 0 3 :=
    .step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₃ (.refl _ _)))
  have w4 : Works xs X ⟨(a, α) :: rest, .idle⟩ (X.takeAgent a) ⟨rest, .half a b α β⟩ 0 4 :=
    .step (c₁ := 0) (c := 0) (k := 3) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₃
          (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₄ (.refl _ _))))
  have e5 := (XMach.solo_claim_start (xs := xs) rest h₁ h₂ h₃ hne h₄ hR).2
  have keepA : assoc x (X.takeAgent a).agents = some γ := by
    show assoc x (X.agents.filter fun e => decide (e.1 ≠ a)) = some γ
    rw [assoc_filter_ne, ite_neg' hxa]
    exact hx
  have keepB : assoc x ((X.takeAgent a).takeAgent b).agents = some γ := by
    show assoc x ((X.takeAgent a).agents.filter fun e => decide (e.1 ≠ b)) = some γ
    rw [assoc_filter_ne, ite_neg' hxb]
    exact keepA
  by_cases h5 : 5 ≤ j
  · obtain ⟨j', rfl⟩ : ∃ j', j = 5 + j' := ⟨j - 5, by omega⟩
    rw [XMach.solo_add, e5]
    exact XMach.solo_write_keeps xs rest _ _ _ j' (by omega) hnew keepB
  · have e : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases e with rfl | rfl | rfl | rfl | rfl
    · exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 1 = _ from w1.solo.1]
      exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 2 = _ from w2.solo.1]
      exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 3 = _ from w3.solo.1]
      exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 4 = _ from w4.solo.1]
      exact keepA

/-- **A round on a pair one point away takes only its pair.** -/
theorem XMach.solo_via_keeps {X : XNet S} {a b : Id} {α β : S} {R : XRhs S} {c : Port}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some c)
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂' : nextSeg X.wires c (a, 0) = some (b, 0)) (h₃ : assoc b X.agents = some β)
    (hne : a ≠ b) (h₄ : assoc b (X.takeAgent a).agents = some β)
    (hR : xs.rule α β = some R)
    {x : Id} {γ : S} (hx : assoc x X.agents = some γ) (hxa : a ≠ x) (hxb : b ≠ x)
    (hnew : ∀ e ∈ R.newAgents a b, e.1 ≠ x) (j : Nat)
    (hj : j ≤ 6 + ((R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length + 1)) :
    assoc x (XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ j).1.agents = some γ := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) c⟩, 0) :=
    XMach.act_look h₂
  have s₂' : XMach.act xs X ⟨rest, .seek a α (a, 0) c⟩ =
      (X, ⟨rest, .seek a α c (b, 0)⟩, 0) := XMach.act_seek_next hc h₂'
  have s₃ : XMach.act xs X ⟨rest, .seek a α c (b, 0)⟩ = (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have w1 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .look a α⟩ 0 1 :=
    .step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₁ (.refl _ _)
  have w2 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .seek a α (a, 0) c⟩ 0 2 :=
    .step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₂ (.refl _ _))
  have w3 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .seek a α c (b, 0)⟩ 0 3 :=
    .step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₂' (.refl _ _)))
  have w4 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .ready a b α β⟩ 0 4 :=
    .step (c₁ := 0) (c := 0) (k := 3) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂'
          (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₃ (.refl _ _))))
  have w5 : Works xs X ⟨(a, α) :: rest, .idle⟩ (X.takeAgent a) ⟨rest, .half a b α β⟩ 0 5 :=
    .step (c₁ := 0) (c := 0) (k := 4) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 3) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₂'
          (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₃
            (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₄ (.refl _ _)))))
  have e6 := (Works.via_start (xs := xs) rest h₁ h₂ hc h₂' h₃ hne h₄ hR).solo.1
  have keepA : assoc x (X.takeAgent a).agents = some γ := by
    show assoc x (X.agents.filter fun e => decide (e.1 ≠ a)) = some γ
    rw [assoc_filter_ne, ite_neg' hxa]
    exact hx
  have keepB : assoc x ((X.takeAgent a).takeAgent b).agents = some γ := by
    show assoc x ((X.takeAgent a).agents.filter fun e => decide (e.1 ≠ b)) = some γ
    rw [assoc_filter_ne, ite_neg' hxb]
    exact keepA
  by_cases h6 : 6 ≤ j
  · obtain ⟨j', rfl⟩ : ∃ j', j = 6 + j' := ⟨j - 6, by omega⟩
    rw [XMach.solo_add, e6]
    exact XMach.solo_write_keeps xs rest _ _ _ j' (by omega) hnew keepB
  · have e : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases e with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 1 = _ from w1.solo.1]
      exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 2 = _ from w2.solo.1]
      exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 3 = _ from w3.solo.1]
      exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 4 = _ from w4.solo.1]
      exact hx
    · rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 5 = _ from w5.solo.1]
      exact keepA

/-- A thread at rest stays at rest, and the memory with it. -/
theorem XMach.solo_rest (xs : XSys S) (X : XNet S) :
    ∀ d, XMach.solo xs X ⟨[], .idle⟩ d = (X, ⟨[], .idle⟩)
  | 0 => rfl
  | d + 1 => XMach.solo_rest xs X d

/-- The first five actions of a round on a pair one point away: four that
read, then the first agent of the pair is taken. -/
theorem XMach.solo_via_reads {X : XNet S} {a b : Id} {α β : S} {R : XRhs S} {c : Port}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some c)
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂' : nextSeg X.wires c (a, 0) = some (b, 0)) (h₃ : assoc b X.agents = some β)
    (hne : a ≠ b) (hR : xs.rule α β = some R) (j : Nat) (hj : j ≤ 5) :
    (XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ j).1 = X ∨
      (XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ j).1 = X.takeAgent a := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) c⟩, 0) :=
    XMach.act_look h₂
  have s₂' : XMach.act xs X ⟨rest, .seek a α (a, 0) c⟩ =
      (X, ⟨rest, .seek a α c (b, 0)⟩, 0) := XMach.act_seek_next hc h₂'
  have s₃ : XMach.act xs X ⟨rest, .seek a α c (b, 0)⟩ = (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  have w1 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .look a α⟩ 0 1 :=
    .step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₁ (.refl _ _)
  have w2 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .seek a α (a, 0) c⟩ 0 2 :=
    .step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₂ (.refl _ _))
  have w3 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .seek a α c (b, 0)⟩ 0 3 :=
    .step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₂' (.refl _ _)))
  have w4 : Works xs X ⟨(a, α) :: rest, .idle⟩ X ⟨rest, .ready a b α β⟩ 0 4 :=
    .step (c₁ := 0) (c := 0) (k := 3) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₂'
          (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₃ (.refl _ _))))
  have w5 : Works xs X ⟨(a, α) :: rest, .idle⟩ (X.takeAgent a) ⟨rest, .half a b α β⟩ 0 5 :=
    .step (c₁ := 0) (c := 0) (k := 4) (fun h => by cases h) s₁
      (.step (c₁ := 0) (c := 0) (k := 3) (fun h => by cases h) s₂
        (.step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₂'
          (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₃
            (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₄ (.refl _ _)))))
  have e : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inl (by rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 1 = _ from w1.solo.1])
  · exact .inl (by rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 2 = _ from w2.solo.1])
  · exact .inl (by rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 3 = _ from w3.solo.1])
  · exact .inl (by rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 4 = _ from w4.solo.1])
  · exact .inr (by rw [show XMach.solo xs X ⟨(a, α) :: rest, .idle⟩ 5 = _ from w5.solo.1])

/-- The first five actions of a round on a pair one point away, as a run:
four that read, then the first agent of the pair is taken. -/
theorem Works.via_half {X : XNet S} {a b : Id} {α β : S} {R : XRhs S} {c : Port}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some c)
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂' : nextSeg X.wires c (a, 0) = some (b, 0)) (h₃ : assoc b X.agents = some β)
    (hne : a ≠ b) (hR : xs.rule α β = some R) :
    Works xs X ⟨(a, α) :: rest, .idle⟩ (X.takeAgent a) ⟨rest, .half a b α β⟩ 0 5 := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) c⟩, 0) :=
    XMach.act_look h₂
  have s₂' : XMach.act xs X ⟨rest, .seek a α (a, 0) c⟩ =
      (X, ⟨rest, .seek a α c (b, 0)⟩, 0) := XMach.act_seek_next hc h₂'
  have s₃ : XMach.act xs X ⟨rest, .seek a α c (b, 0)⟩ = (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  have s₄ : XMach.act xs X ⟨rest, .ready a b α β⟩ =
      (X.takeAgent a, ⟨rest, .half a b α β⟩, 0) := XMach.act_ready h₁
  exact .step (c₁ := 0) (c := 0) (k := 4) (fun h => by cases h) s₁
    (.step (c₁ := 0) (c := 0) (k := 3) (fun h => by cases h) s₂
      (.step (c₁ := 0) (c := 0) (k := 2) (fun h => by cases h) s₂'
        (.step (c₁ := 0) (c := 0) (k := 1) (fun h => by cases h) s₃
          (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₄ (.refl _ _)))))

/-- Writing an agent is one action. -/
theorem Works.write_agent (X : XNet S) (todo : List (Id × S)) (i : Id) (γ : S)
    (as : List (Id × S)) (ls : List (Port × Port)) :
    Works xs X ⟨todo, .write ((i, γ) :: as) ls⟩ (X.putAgent i γ) ⟨todo, .write as ls⟩ 0 1 :=
  .step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) rfl (.refl _ _)

/-- Writing a segment is one action. -/
theorem Works.write_link (X : XNet S) (todo : List (Id × S)) (p q : Port)
    (ls : List (Port × Port)) :
    Works xs X ⟨todo, .write [] ((p, q) :: ls)⟩ (X.putLink p q) ⟨todo, .write [] ls⟩ 0 1 :=
  .step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) rfl (.refl _ _)

/-- Where a run is after a number of actions that equals its length. -/
theorem Works.solo_at {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (w : Works xs X T X' T' c k) (k' : Nat) (h : k' = k) :
    XMach.solo xs X T k' = (X', T') := by
  subst h
  exact w.solo.1

/-- A run that leaves the memory alone leaves it alone at each action. -/
theorem Stays.solo_mem {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k) :
    ∀ j, j ≤ k → (XMach.solo xs X T j).1 = X := by
  induction st with
  | refl T =>
    intro j hj
    have e : j = 0 := by omega
    subst e
    rfl
  | @step T T₁ T' k _ h _ ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      show (XMach.solo xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 j).1 = X
      rw [h]
      exact ih j (by omega)

/-- Writing a list of segments takes one action for each. -/
theorem Works.write_links (todo : List (Id × S)) :
    ∀ (ls₁ ls₂ : List (Port × Port)) (X : XNet S),
      Works xs X ⟨todo, .write [] (ls₁ ++ ls₂)⟩ (X.putLinks ls₁) ⟨todo, .write [] ls₂⟩ 0
        ls₁.length
  | [], _, _ => .refl _ _
  | (p, q) :: ls₁, ls₂, X => by
    have w := (Works.write_link (xs := xs) X todo p q (ls₁ ++ ls₂)).trans
      (Works.write_links todo ls₁ ls₂ (X.putLink p q))
    have e : 1 + ls₁.length = ls₁.length + 1 := Nat.add_comm _ _
    rw [e] at w
    exact w

/-- The first four actions of a round on a pair one point away only
read. -/
theorem Stays.via_reads {X : XNet S} {a b : Id} {α β : S} {R : XRhs S} {c : Port}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some c)
    (hc : (if c.2 = 0 then assoc c.1 X.agents else none) = none)
    (h₂' : nextSeg X.wires c (a, 0) = some (b, 0)) (h₃ : assoc b X.agents = some β)
    (hne : a ≠ b) (hR : xs.rule α β = some R) :
    Stays xs X ⟨(a, α) :: rest, .idle⟩ ⟨rest, .ready a b α β⟩ 4 := by
  have s₁ : XMach.act xs X ⟨(a, α) :: rest, .idle⟩ = (X, ⟨rest, .look a α⟩, 0) :=
    XMach.act_idle_pos h₁
  have s₂ : XMach.act xs X ⟨rest, .look a α⟩ = (X, ⟨rest, .seek a α (a, 0) c⟩, 0) :=
    XMach.act_look h₂
  have s₂' : XMach.act xs X ⟨rest, .seek a α (a, 0) c⟩ =
      (X, ⟨rest, .seek a α c (b, 0)⟩, 0) := XMach.act_seek_next hc h₂'
  have s₃ : XMach.act xs X ⟨rest, .seek a α c (b, 0)⟩ = (X, ⟨rest, .ready a b α β⟩, 0) :=
    XMach.act_seek_found (c := (b, 0))
      (by
        show (if (0 : Nat) = 0 then assoc b X.agents else none) = some β
        rw [ite_pos' rfl]
        exact h₃)
      ⟨hne, by rw [hR]; rfl⟩
  exact .step (k := 3) (fun h => by cases h) s₁
    (.step (k := 2) (fun h => by cases h) s₂
      (.step (k := 1) (fun h => by cases h) s₂'
        (.step (k := 0) (fun h => by cases h) s₃ (.refl _))))

/-- One action of each of two threads in turn, the first first. -/
theorem XMach.trace_pair {X X₁ X₂ : XNet S} {T₀ T₀' T₁ T₁' : XThread S} {c₁ c₂ : Nat}
    (a₁ : XMach.act xs X T₀ = (X₁, T₀', c₁)) (a₂ : XMach.act xs X₁ T₁ = (X₂, T₁', c₂)) :
    ((⟨X, [T₀, T₁]⟩ : XMach S).trace xs (fun i => i % 2) (2 * 1)).1 = ⟨X₂, [T₀', T₁']⟩ := by
  have e₁ : XMach.step xs ⟨X, [T₀, T₁]⟩ 0 = (⟨X₁, [T₀', T₁]⟩, c₁) :=
    XMach.step_eq (M := ⟨X, [T₀, T₁]⟩) (t := 0) rfl a₁
  have e₂ : XMach.step xs ⟨X₁, [T₀', T₁]⟩ 1 = (⟨X₂, [T₀', T₁']⟩, c₂) :=
    XMach.step_eq (M := ⟨X₁, [T₀', T₁]⟩) (t := 1) rfl a₂
  show (XMach.step xs (XMach.step xs ⟨X, [T₀, T₁]⟩ 0).1 1).1 = _
  rw [e₁, e₂]

/-- A run of two threads in turn, the first first, in two parts. -/
theorem XMach.trace_pair_add (xs : XSys S) (M : XMach S) (w w' : Nat) :
    (M.trace xs (fun i => i % 2) (2 * (w + w'))).1 =
      ((M.trace xs (fun i => i % 2) (2 * w)).1.trace xs (fun i => i % 2) (2 * w')).1 := by
  rw [Nat.mul_add, XMach.trace_add xs (fun i => i % 2) M (2 * w) (2 * w')]
  show ((M.trace xs (fun i => i % 2) (2 * w)).1.trace xs
    (fun i => (2 * w + i) % 2) (2 * w')).1 = _
  rw [XMach.trace_congr xs _ (σ' := fun i => i % 2) (2 * w') fun j _ => by
    show (2 * w + j) % 2 = j % 2
    omega]

/-- `Sweeps xs M M' w`: `w` times, the first thread of two acts and then the
second, and that takes the machine `M` to `M'`. -/
inductive Sweeps (xs : XSys S) : XMach S → XMach S → Nat → Prop
  | refl (M : XMach S) : Sweeps xs M M 0
  | step {X X₁ X₂ : XNet S} {T₀ T₀' T₁ T₁' : XThread S} {c₁ c₂ : Nat} {M' : XMach S}
      {w : Nat} : XMach.act xs X T₀ = (X₁, T₀', c₁) → XMach.act xs X₁ T₁ = (X₂, T₁', c₂) →
      Sweeps xs ⟨X₂, [T₀', T₁']⟩ M' w → Sweeps xs ⟨X, [T₀, T₁]⟩ M' (w + 1)

theorem Sweeps.trace {M M' : XMach S} {w : Nat} (s : Sweeps xs M M' w) :
    (M.trace xs (fun i => i % 2) (2 * w)).1 = M' := by
  induction s with
  | refl M => rfl
  | @step X X₁ X₂ T₀ T₀' T₁ T₁' c₁ c₂ M' w a₁ a₂ _ ih =>
    rw [show w + 1 = 1 + w from Nat.add_comm _ _, XMach.trace_pair_add,
      XMach.trace_pair a₁ a₂]
    exact ih

/-- **The work after a known stretch of a run of two threads in turn** is
at most the length of the stretch and the work from the state reached. -/
theorem XMach.work_pair_after {M M' : XMach S} {w B : Nat}
    (h : (M.trace xs (fun i => i % 2) (2 * w)).1 = M')
    (hB : ∀ i, M'.work xs (fun i => i % 2) i ≤ B) (i : Nat) :
    M.work xs (fun i => i % 2) i ≤ 2 * w + B := by
  by_cases hi : i ≤ 2 * w
  · have h1 := XMach.work_le_count xs (fun i => i % 2) M i
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, i = 2 * w + k := ⟨i - 2 * w, by omega⟩
    have e : (M.trace xs (fun i => i % 2) (2 * w)).1.work xs (fun j => (2 * w + j) % 2) k =
        M'.work xs (fun i => i % 2) k := by
      rw [h]
      exact XMach.tally_congr XThread.busy xs M' k fun j _ => by
        show (2 * w + j) % 2 = j % 2
        omega
    have h0 : M.work xs (fun i => i % 2) (2 * w + k) = M.work xs (fun i => i % 2) (2 * w) +
        (M.trace xs (fun i => i % 2) (2 * w)).1.work xs (fun j => (2 * w + j) % 2) k :=
      XMach.work_add xs (fun i => i % 2) M (2 * w) k
    have h1 := XMach.work_le_count xs (fun i => i % 2) M (2 * w)
    have h2 := hB k
    omega

theorem XThread.tally_busy_rest (xs : XSys S) (X : XNet S) :
    ∀ h, (⟨[], .idle⟩ : XThread S).tally XThread.busy xs X h = 0
  | 0 => rfl
  | h + 1 => by
    show 0 + XThread.tally XThread.busy xs X ⟨[], .idle⟩ h = 0
    rw [Nat.zero_add]
    exact XThread.tally_busy_rest xs X h

/-- A thread that comes to rest in `k` actions without writing is at work
`k` times at most. -/
theorem Stays.tally_le {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k)
    (hT' : T' = ⟨[], .idle⟩) : ∀ h, T.tally XThread.busy xs X h ≤ k := by
  induction st with
  | refl T =>
    subst hT'
    intro h
    rw [XThread.tally_busy_rest]
    exact Nat.le_refl 0
  | @step T T₁ T' k _ ha _ ih =>
    intro h
    cases h with
    | zero => exact Nat.zero_le _
    | succ h =>
      have h1 := ih hT' h
      have h2 := XThread.busy_le T
      show XThread.busy T + XThread.tally XThread.busy xs X (XMach.act xs X T).2.1 h ≤ k + 1
      rw [ha]
      show XThread.busy T + XThread.tally XThread.busy xs X T₁ h ≤ k + 1
      omega

/-- **Two threads that only read do the work of each**: in a memory that
neither changes, under any schedule. -/
theorem XMach.work_two_stays {X : XNet S} {P Q : XThread S} {kP kQ : Nat}
    (sP : Stays xs X P ⟨[], .idle⟩ kP) (sQ : Stays xs X Q ⟨[], .idle⟩ kQ) (σ : Nat → Nat)
    (i : Nat) : (⟨X, [P, Q]⟩ : XMach S).work xs σ i ≤ kP + kQ := by
  have hR : ∀ T, T ∈ (⟨X, [P, Q]⟩ : XMach S).ths →
      T.Reads xs (⟨X, [P, Q]⟩ : XMach S).mem := by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (sP.after rfl).1
    · rcases List.mem_cons.1 hT with rfl | hT
      · exact (sQ.after rfl).1
      · cases hT
  have e := XMach.tally_reads XThread.busy σ hR i
  have h1 := sP.tally_le rfl (hits σ 0 i)
  have h2 := sQ.tally_le rfl (hits σ 1 i)
  show (⟨X, [P, Q]⟩ : XMach S).tally XThread.busy xs σ i ≤ kP + kQ
  rw [e]
  show 0 + P.tally XThread.busy xs X (hits σ 0 i) + Q.tally XThread.busy xs X (hits σ 1 i) ≤
    kP + kQ
  omega

/-- The next action of a thread running alone. -/
theorem XMach.solo_step {X X' : XNet S} {T T' : XThread S} {c : Nat}
    (h : XMach.act xs X T = (X', T', c)) (j : Nat) :
    XMach.solo xs X T (j + 1) = XMach.solo xs X' T' j := by
  show XMach.solo xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 j = _
  rw [h]

/-- The entries a thread still has to deal with: the one in hand, then its
list. -/
def XThread.pend (T : XThread S) : List (Id × S) :=
  match T.st with
  | .look a α => (a, α) :: T.todo
  | .seek a α _ _ => (a, α) :: T.todo
  | .ready a _ α _ => (a, α) :: T.todo
  | .half a _ α _ => (a, α) :: T.todo
  | _ => T.todo

/-- A thread that reads keeps the entries it still has to deal with, or
drops the first of them. -/
theorem XMach.act_pend (xs : XSys S) (X : XNet S) {T : XThread S} (hT : T.st.Reading) :
    ∃ pre, pre ++ (XMach.act xs X T).2.1.pend = T.pend := by
  obtain ⟨todo, st⟩ := T
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨[], rfl⟩
    | cons e' rest =>
      by_cases h : assoc e'.1 X.agents = some e'.2
      · rw [XMach.act_idle_pos h]
        exact ⟨[], rfl⟩
      · rw [XMach.act_idle_neg h]
        exact ⟨[e'], rfl⟩
  | look a α =>
    cases h : assoc (a, 0) X.wires with
    | none =>
      rw [XMach.act_look_none h]
      exact ⟨[(a, α)], rfl⟩
    | some q =>
      rw [XMach.act_look h]
      exact ⟨[], rfl⟩
  | seek a α p c =>
    unfold XMach.act
    dsimp only
    split
    · split
      · exact ⟨[], rfl⟩
      · exact ⟨[(a, α)], rfl⟩
    · split
      · exact ⟨[], rfl⟩
      · exact ⟨[(a, α)], rfl⟩
  | ready a b α β => exact hT.elim
  | half a b α β => exact hT.elim
  | write as ls => exact hT.elim

end Reader

/-- Where an entry that occurs once splits a list. -/
theorem split_unique {α : Type} {x : α} : ∀ {l₁ pre l₂ s : List α}, x ∉ l₁ → x ∉ l₂ →
    pre ++ x :: s = l₁ ++ x :: l₂ → s = l₂
  | [], [], _, _, _, _, h => (List.cons.inj h).2
  | [], y :: p, l₂, s, _, h2, h => by
    have e : p ++ x :: s = l₂ := (List.cons.inj h).2
    exact absurd (e ▸ List.mem_append_right p List.mem_cons_self) h2
  | y :: l₁, [], l₂, s, h1, _, h => by
    have e : x = y := (List.cons.inj h).1
    exact absurd (e ▸ List.mem_cons_self) h1
  | y :: l₁, y' :: p, l₂, s, h1, h2, h =>
    split_unique (fun hm => h1 (List.mem_cons_of_mem _ hm)) h2 (List.cons.inj h).2

theorem append_split3 {α : Type} (a b t : List α) (e1 e2 e3 : α) :
    a ++ ((b ++ [e1, e2, e3]) ++ t) = (a ++ (b ++ [e1])) ++ (e2 :: ([e3] ++ t)) := by
  rw [List.append_assoc a, List.append_assoc b, List.append_assoc b]
  rfl

/-- A property that holds for some number holds for a least one. -/
theorem least_of_exists {P : Nat → Prop} : ∀ N, (∃ a, a ≤ N ∧ P a) →
    ∃ a, P a ∧ ∀ b, b < a → ¬ P b
  | 0, ⟨a, ha, hp⟩ => by
    have e : a = 0 := by omega
    subst e
    exact ⟨0, hp, fun b hb => absurd hb (Nat.not_lt_zero b)⟩
  | N + 1, ⟨a, ha, hp⟩ => by
    by_cases h : ∃ a, a ≤ N ∧ P a
    · exact least_of_exists N h
    · exact ⟨a, hp, fun b hb hpb => h ⟨b, by omega, hpb⟩⟩

section Exact

variable [DecidableEq S] {xs : XSys S}

/-- A thread at rest stays at rest through a run. -/
theorem XMach.trace_rest {M : XMach S} {σ : Nat → Nat} {t i : Nat}
    (h : (M.trace xs σ i).1.ths[t]? = some ⟨[], .idle⟩) :
    ∀ k, (M.trace xs σ (i + k)).1.ths[t]? = some ⟨[], .idle⟩
  | 0 => h
  | k + 1 => XMach.step_rest _ (σ (i + k)) (XMach.trace_rest h k)

/-- If no thread is at rest at some moment of a run, none was at the
start. -/
theorem XMach.busy_of_later {M M' : XMach S} {σ : Nat → Nat} {i : Nat}
    (h : (M.trace xs σ i).1 = M')
    (hb : ∀ (t : Nat) (T : XThread S), M'.ths[t]? = some T → T ≠ ⟨[], .idle⟩) :
    ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T → T ≠ ⟨[], .idle⟩ := by
  subst h
  intro t T hT e
  subst e
  have h1 := XMach.trace_rest (xs := xs) (M := M) (σ := σ) (i := 0) hT i
  rw [Nat.zero_add] at h1
  exact hb t _ h1 rfl

/-- **While no thread is at rest every action is work**: if no thread is
at rest after `N` actions, the work of the first `i` of them is `i`. -/
theorem XMach.work_full {M : XMach S} {σ : Nat → Nat} {N : Nat}
    (hb : ∀ (t : Nat) (T : XThread S), (M.trace xs σ N).1.ths[t]? = some T → T ≠ ⟨[], .idle⟩)
    (hσ : ∀ i, σ i < M.ths.length) : ∀ i, i ≤ N → M.work xs σ i = i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := XMach.work_full hb hσ i (by omega)
    have hlt : σ i < (M.trace xs σ i).1.ths.length := by
      rw [XMach.trace_length]
      exact hσ i
    obtain ⟨T, hT⟩ : ∃ T, (M.trace xs σ i).1.ths[σ i]? = some T :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hne : T ≠ ⟨[], .idle⟩ := fun e => by
      subst e
      have h := XMach.trace_rest hT (N - i)
      have e' : i + (N - i) = N := by omega
      rw [e'] at h
      exact hb _ _ h rfl
    show M.work xs σ i + (M.trace xs σ i).1.stepTally XThread.busy (σ i) = i + 1
    rw [ih]
    unfold XMach.stepTally
    rw [hT]
    show i + T.busy = i + 1
    rw [XThread.busy_of_ne_rest hne]

/-- A thread that comes to rest in `k` actions without writing is at work
exactly `k` times once it has had `k` actions. -/
theorem Stays.tally_eq {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k)
    (hT' : T' = ⟨[], .idle⟩) : ∀ h, k ≤ h → T.tally XThread.busy xs X h = k := by
  induction st with
  | refl T =>
    subst hT'
    intro h _
    exact XThread.tally_busy_rest xs X h
  | @step T T₁ T' k hT ha _ ih =>
    intro h hh
    cases h with
    | zero => exact absurd hh (by omega)
    | succ h =>
      have h1 := ih hT' h (by omega)
      show XThread.busy T + XThread.tally XThread.busy xs X (XMach.act xs X T).2.1 h = k + 1
      rw [ha]
      show XThread.busy T + XThread.tally XThread.busy xs X T₁ h = k + 1
      rw [h1, XThread.busy_of_ne_rest hT]
      omega

/-- A thread that still has actions to make before it rests is not at
rest. -/
theorem Stays.ne_rest {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k)
    (hk : 1 ≤ k) : T ≠ ⟨[], .idle⟩ := by
  cases st with
  | refl => exact absurd hk (by omega)
  | step hT _ _ => exact hT

/-- When two threads act in turn, each has had `w` actions after `2 * w`. -/
theorem hits_alt : ∀ w, hits (fun i => i % 2) 0 (2 * w) = w ∧
    hits (fun i => i % 2) 1 (2 * w) = w
  | 0 => ⟨rfl, rfl⟩
  | w + 1 => by
    obtain ⟨h0, h1⟩ := hits_alt w
    rw [Nat.mul_succ]
    constructor
    · show hits (fun i => i % 2) 0 (2 * w) + (if (2 * w) % 2 = 0 then 1 else 0) +
        (if (2 * w + 1) % 2 = 0 then 1 else 0) = w + 1
      rw [h0, ite_pos' (by omega), ite_neg' (by omega)]
    · show hits (fun i => i % 2) 1 (2 * w) + (if (2 * w) % 2 = 1 then 1 else 0) +
        (if (2 * w + 1) % 2 = 1 then 1 else 0) = w + 1
      rw [h1, ite_neg' (by omega), ite_pos' (by omega)]

/-- `M.Total xs σ W`: the work of the run of `M` under the schedule `σ`
comes to exactly `W`: it is `W` from some action on. -/
def XMach.Total (xs : XSys S) (σ : Nat → Nat) (M : XMach S) (W : Nat) : Prop :=
  ∃ N, ∀ i, N ≤ i → M.work xs σ i = W

/-- The work never exceeds what it comes to. -/
theorem XMach.Total.le {M : XMach S} {σ : Nat → Nat} {W : Nat} (t : M.Total xs σ W)
    (i : Nat) : M.work xs σ i ≤ W := by
  obtain ⟨N, h⟩ := t
  have h1 := h (i + N) (by omega)
  have h2 := XMach.work_mono (xs := xs) σ M (show i ≤ i + N by omega)
  omega

/-- A run comes to one amount of work only. -/
theorem XMach.Total.unique {M : XMach S} {σ : Nat → Nat} {W W' : Nat}
    (t : M.Total xs σ W) (t' : M.Total xs σ W') : W = W' := by
  obtain ⟨N, h⟩ := t
  obtain ⟨N', h'⟩ := t'
  have h1 := h (N + N') (by omega)
  have h2 := h' (N + N') (by omega)
  omega

theorem XMach.Total.cast {M : XMach S} {σ : Nat → Nat} {W W' : Nat}
    (t : M.Total xs σ W) (h : W = W') : M.Total xs σ W' := by
  subst h
  exact t

/-- **Two threads that only read, in turn, do exactly the work of each**:
`kP + kQ` if they come to rest in `kP` and `kQ` actions. -/
theorem XMach.total_two_stays {X : XNet S} {P Q : XThread S} {kP kQ : Nat}
    (sP : Stays xs X P ⟨[], .idle⟩ kP) (sQ : Stays xs X Q ⟨[], .idle⟩ kQ) :
    (⟨X, [P, Q]⟩ : XMach S).Total xs (fun i => i % 2) (kP + kQ) := by
  have hR : ∀ T, T ∈ (⟨X, [P, Q]⟩ : XMach S).ths →
      T.Reads xs (⟨X, [P, Q]⟩ : XMach S).mem := by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (sP.after rfl).1
    · rcases List.mem_cons.1 hT with rfl | hT
      · exact (sQ.after rfl).1
      · cases hT
  have e := XMach.tally_reads XThread.busy (fun i => i % 2) hR (2 * (kP + kQ))
  obtain ⟨h0, h1⟩ := hits_alt (kP + kQ)
  have t1 := sP.tally_eq rfl (kP + kQ) (by omega)
  have t2 := sQ.tally_eq rfl (kP + kQ) (by omega)
  have at0 : (⟨X, [P, Q]⟩ : XMach S).work xs (fun i => i % 2) (2 * (kP + kQ)) = kP + kQ := by
    show (⟨X, [P, Q]⟩ : XMach S).tally XThread.busy xs (fun i => i % 2) (2 * (kP + kQ)) =
      kP + kQ
    rw [e]
    show 0 + P.tally XThread.busy xs X (hits (fun i => i % 2) 0 (2 * (kP + kQ))) +
      Q.tally XThread.busy xs X (hits (fun i => i % 2) 1 (2 * (kP + kQ))) = kP + kQ
    rw [h0, h1, t1, t2, Nat.zero_add]
  refine ⟨2 * (kP + kQ), fun i hi => ?_⟩
  have up := XMach.work_two_stays sP sQ (fun i => i % 2) i
  have lo := XMach.work_mono (xs := xs) (fun i => i % 2) (⟨X, [P, Q]⟩ : XMach S) hi
  omega

/-- **The work of a run of two threads in turn, from a later state on**:
if neither thread is at rest when each has made `a` actions, the run has
done `2 * a` work by then, and comes in all to that and what the run from
there comes to. -/
theorem XMach.Total.after {M M' : XMach S} {a W : Nat}
    (h : (M.trace xs (fun i => i % 2) (2 * a)).1 = M') (hlen : M.ths.length = 2)
    (hb : ∀ (t : Nat) (T : XThread S), M'.ths[t]? = some T → T ≠ ⟨[], .idle⟩)
    (tot : M'.Total xs (fun i => i % 2) W) : M.Total xs (fun i => i % 2) (2 * a + W) := by
  subst h
  obtain ⟨N, hN⟩ := tot
  have full := XMach.work_full (xs := xs) (M := M) (σ := fun i => i % 2) (N := 2 * a) hb
    (fun i => by
      show i % 2 < M.ths.length
      rw [hlen]
      exact Nat.mod_lt _ (by omega)) (2 * a) (Nat.le_refl _)
  refine ⟨2 * a + N, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = 2 * a + k := ⟨i - 2 * a, by omega⟩
  have e : (M.trace xs (fun i => i % 2) (2 * a)).1.work xs (fun j => (2 * a + j) % 2) k =
      (M.trace xs (fun i => i % 2) (2 * a)).1.work xs (fun i => i % 2) k :=
    XMach.tally_congr XThread.busy xs _ k fun j _ => by
      show (2 * a + j) % 2 = j % 2
      omega
  have h0 : M.work xs (fun i => i % 2) (2 * a + k) = M.work xs (fun i => i % 2) (2 * a) +
      (M.trace xs (fun i => i % 2) (2 * a)).1.work xs (fun j => (2 * a + j) % 2) k :=
    XMach.work_add xs (fun i => i % 2) M (2 * a) k
  have h2 := hN k (by omega)
  omega

/-- `M.Ends xs W`: neither thread of `M` is at rest, and the run of the two
in turn comes to exactly `W` work. -/
structure XMach.Ends (xs : XSys S) (M : XMach S) (W : Nat) : Prop where
  total : M.Total xs (fun i => i % 2) W
  busy : ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T → T ≠ ⟨[], .idle⟩

/-- **Two threads in turn, to the end of the run**: `w` pairs of actions,
then each thread only reads, `kP` and `kQ` actions; the work is all of
these. -/
theorem XMach.ends_sweeps {M : XMach S} {X : XNet S} {P Q : XThread S} {w kP kQ W : Nat}
    (s : Sweeps xs M ⟨X, [P, Q]⟩ w) (hlen : M.ths.length = 2)
    (sP : Stays xs X P ⟨[], .idle⟩ kP) (sQ : Stays xs X Q ⟨[], .idle⟩ kQ)
    (hP : 1 ≤ kP) (hQ : 1 ≤ kQ) (hW : W = 2 * w + (kP + kQ)) : M.Ends xs W := by
  subst hW
  have hb : ∀ (t : Nat) (T : XThread S), (⟨X, [P, Q]⟩ : XMach S).ths[t]? = some T → T ≠ ⟨[], .idle⟩ := by
    intro t T hT
    cases t with
    | zero =>
      have e : P = T := Option.some.inj hT
      subst e
      exact sP.ne_rest hP
    | succ t =>
      cases t with
      | zero =>
        have e : Q = T := Option.some.inj hT
        subst e
        exact sQ.ne_rest hQ
      | succ t => exact absurd hT (by simp)
  exact ⟨(XMach.total_two_stays sP sQ).after s.trace hlen hb, XMach.busy_of_later s.trace hb⟩

/-- The same from an earlier state of the run. -/
theorem XMach.Ends.after {M M' : XMach S} {a W : Nat}
    (h : (M.trace xs (fun i => i % 2) (2 * a)).1 = M') (hlen : M.ths.length = 2)
    (e : M'.Ends xs W) : M.Ends xs (2 * a + W) :=
  ⟨e.total.after h hlen e.busy, XMach.busy_of_later h e.busy⟩

end Exact

end INet
