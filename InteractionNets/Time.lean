import InteractionNets.Fair

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### Runs of one thread, action by action

To count the actions of a run exactly, `Works` is `Runs` with one more
condition: the thread is not at rest before any of its actions. -/

section Works

variable [DecidableEq S] {xs : XSys S}

/-- `Works xs X T X' T' c k`: from memory `X` and thread `T`, the thread
running alone reaches memory `X'` and state `T'` in `k` actions, `c` of
which complete a claim, and it is not at rest before any of them. -/
inductive Works (xs : XSys S) : XNet S → XThread S → XNet S → XThread S → Nat → Nat → Prop
  | refl (X : XNet S) (T : XThread S) : Works xs X T X T 0 0
  | step {X X₁ X' : XNet S} {T T₁ T' : XThread S} {c₁ c k : Nat} :
      T ≠ ⟨[], .idle⟩ → XMach.act xs X T = (X₁, T₁, c₁) → Works xs X₁ T₁ X' T' c k →
      Works xs X T X' T' (c₁ + c) (k + 1)

theorem Works.trans {X X₁ X₂ : XNet S} {T T₁ T₂ : XThread S} {c₁ c₂ k₁ k₂ : Nat}
    (r₁ : Works xs X T X₁ T₁ c₁ k₁) (r₂ : Works xs X₁ T₁ X₂ T₂ c₂ k₂) :
    Works xs X T X₂ T₂ (c₁ + c₂) (k₁ + k₂) := by
  induction r₁ with
  | refl X T =>
    rw [Nat.zero_add, Nat.zero_add]
    exact r₂
  | step hT h _ ih =>
    rw [Nat.add_assoc, Nat.add_right_comm]
    exact .step hT h (ih r₂)

/-- The run with the same thread scheduled at every action, one action
later: the first action, then the run from the state it leads to. -/
theorem XMach.trace_shift (xs : XSys S) (t : Nat) (M : XMach S) : ∀ i,
    M.trace xs (fun _ => t) (i + 1) =
      (((M.step xs t).1.trace xs (fun _ => t) i).1,
        (M.step xs t).2 + ((M.step xs t).1.trace xs (fun _ => t) i).2)
  | 0 => by
    show (((M.step xs t).1, 0 + (M.step xs t).2) : XMach S × Nat) =
      ((M.step xs t).1, (M.step xs t).2 + 0)
    rw [Nat.zero_add, Nat.add_zero]
  | i + 1 => by
    have ih := XMach.trace_shift xs t M i
    show ((((M.trace xs (fun _ => t) (i + 1)).1.step xs t).1,
        (M.trace xs (fun _ => t) (i + 1)).2 +
          ((M.trace xs (fun _ => t) (i + 1)).1.step xs t).2) : XMach S × Nat) =
      ((((M.step xs t).1.trace xs (fun _ => t) i).1.step xs t).1,
        (M.step xs t).2 + (((M.step xs t).1.trace xs (fun _ => t) i).2 +
          (((M.step xs t).1.trace xs (fun _ => t) i).1.step xs t).2))
    rw [ih]
    exact congrArg (Prod.mk _) (Nat.add_assoc _ _ _)

omit [DecidableEq S] in
theorem XThread.eq_rest {T : XThread S} (h : (T.todo.isEmpty && T.st.isIdle) = true) :
    T = ⟨[], .idle⟩ := by
  obtain ⟨todo, st⟩ := T
  cases todo with
  | cons e rest => cases h
  | nil =>
    cases st with
    | idle => rfl
    | look a α => cases h
    | seek a α p c => cases h
    | ready a b α β => cases h
    | half a b α β => cases h
    | write as ls => cases h

omit [DecidableEq S] in
theorem XMach.resting_single {X : XNet S} {T : XThread S}
    (h : (⟨X, [T]⟩ : XMach S).resting = true) : T = ⟨[], .idle⟩ :=
  XThread.eq_rest (List.all_eq_true.1 h T List.mem_cons_self)

omit [DecidableEq S] in
/-- With one thread, the program starts with the list of agents as it is. -/
theorem XMach.init_one (X : XNet S) : XMach.init X 1 = ⟨X, [⟨X.agents, .idle⟩]⟩ := by
  show (⟨X, [⟨X.agents ++ [], .idle⟩]⟩ : XMach S) = _
  rw [List.append_nil]

/-- **A counted run of one thread**: after its `k` actions the program is
in the state reached, with `c` claims made, and it is not at rest after any
smaller number of actions. -/
theorem Works.trace {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (w : Works xs X T X' T' c k) :
    (⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) k = (⟨X', [T']⟩, c) ∧
      ∀ i, i < k → ¬ ((⟨X, [T]⟩ : XMach S).trace xs (fun _ => 0) i).1.resting = true := by
  induction w with
  | refl X T => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @step X X₁ X' T T₁ T' c₁ c k hT h _ ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have es : XMach.step xs ⟨X, [T]⟩ 0 = (⟨X₁, [T₁]⟩, c₁) := by
      show ((⟨(XMach.act xs X T).1, [(XMach.act xs X T).2.1]⟩ : XMach S),
        (XMach.act xs X T).2.2) = _
      rw [h]
    constructor
    · rw [XMach.trace_shift xs 0 ⟨X, [T]⟩ k, es]
      show (((⟨X₁, [T₁]⟩ : XMach S).trace xs (fun _ => 0) k).1,
        c₁ + ((⟨X₁, [T₁]⟩ : XMach S).trace xs (fun _ => 0) k).2) = _
      rw [ih₁]
    · intro i hi
      cases i with
      | zero => exact fun hr => hT (XMach.resting_single hr)
      | succ i =>
        rw [XMach.trace_shift xs 0 ⟨X, [T]⟩ i, es]
        exact ih₂ i (by omega)

/-- An agent that a thread gives up on after three actions: it is in
memory, and the segment at its principal port leads to a port that is not
the principal port of an agent in memory and from which no segment goes
on. -/
def XNet.Inert (X : XNet S) (e : Id × S) : Prop :=
  assoc e.1 X.agents = some e.2 ∧ ∃ q, assoc (e.1, 0) X.wires = some q ∧
    (if q.2 = 0 then assoc q.1 X.agents else none) = none ∧
    nextSeg X.wires q (e.1, 0) = none

/-- `Stays xs X T T' k`: `k` actions of a thread running alone take it from
`T` to `T'`; none of them changes the memory `X` or completes a claim, and
the thread is not at rest before any of them. -/
inductive Stays (xs : XSys S) (X : XNet S) : XThread S → XThread S → Nat → Prop
  | refl (T : XThread S) : Stays xs X T T 0
  | step {T T₁ T' : XThread S} {k : Nat} :
      T ≠ ⟨[], .idle⟩ → XMach.act xs X T = (X, T₁, 0) → Stays xs X T₁ T' k →
      Stays xs X T T' (k + 1)

theorem Stays.trans {X : XNet S} {T T₁ T₂ : XThread S} {k₁ k₂ : Nat}
    (r₁ : Stays xs X T T₁ k₁) (r₂ : Stays xs X T₁ T₂ k₂) : Stays xs X T T₂ (k₁ + k₂) := by
  induction r₁ with
  | refl T =>
    rw [Nat.zero_add]
    exact r₂
  | step hT h _ ih =>
    rw [Nat.add_right_comm]
    exact .step hT h (ih r₂)

theorem Stays.works {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k) :
    Works xs X T X T' 0 k := by
  induction st with
  | refl T => exact .refl _ _
  | step hT h _ ih => exact .step (c₁ := 0) (c := 0) hT h ih

/-- A thread passes an agent that leads nowhere in three actions, without
writing. -/
theorem Stays.inert {X : XNet S} {e : Id × S} (rest : List (Id × S)) (h : X.Inert e) :
    Stays xs X ⟨e :: rest, .idle⟩ ⟨rest, .idle⟩ 3 := by
  obtain ⟨h₁, q, h₂, h₃, h₄⟩ := h
  exact .step (k := 2) (fun h => by cases h) (XMach.act_idle_pos h₁)
    (.step (k := 1) (fun h => by cases h) (XMach.act_look h₂)
      (.step (k := 0) (fun h => by cases h) (XMach.act_seek_stop h₃ h₄) (.refl _)))

/-- A thread passes a list of such agents in three actions each, without
writing. -/
theorem Stays.inert_pass {X : XNet S} (rest : List (Id × S)) : ∀ (l : List (Id × S)),
    (∀ e, e ∈ l → X.Inert e) → Stays xs X ⟨l ++ rest, .idle⟩ ⟨rest, .idle⟩ (3 * l.length)
  | [], _ => .refl _
  | e :: l, h => by
    have w₁ : Stays xs X ⟨e :: (l ++ rest), .idle⟩ ⟨l ++ rest, .idle⟩ 3 :=
      Stays.inert _ (h e List.mem_cons_self)
    have w₂ := Stays.inert_pass rest l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have w := w₁.trans w₂
    have e1 : 3 * (e :: l).length = 3 + 3 * l.length := by
      show 3 * (l.length + 1) = _
      omega
    rw [e1]
    exact w

theorem Works.inert_pass {X : XNet S} (rest : List (Id × S)) (l : List (Id × S))
    (h : ∀ e, e ∈ l → X.Inert e) :
    Works xs X ⟨l ++ rest, .idle⟩ X ⟨rest, .idle⟩ 0 (3 * l.length) :=
  (Stays.inert_pass rest l h).works

/-- A thread that reaches the first agent of an active pair whose rule
writes nothing claims the pair and takes a fresh list of agents, in six
actions. -/
theorem Works.annihilate {X : XNet S} {a b : Id} {α β : S} {R : XRhs S}
    (rest : List (Id × S)) (h₁ : assoc a X.agents = some α)
    (h₂ : assoc (a, 0) X.wires = some (b, 0)) (h₃ : assoc b X.agents = some β) (hne : a ≠ b)
    (h₄ : assoc b (X.takeAgent a).agents = some β) (hR : xs.rule α β = some R)
    (hA : R.newAgents a b = []) (hL : R.newLinks xs.sys.ar a b α β = []) :
    Works xs X ⟨(a, α) :: rest, .idle⟩ ((X.takeAgent a).takeAgent b)
      ⟨((X.takeAgent a).takeAgent b).agents, .idle⟩ 1 6 := by
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
      ((X.takeAgent a).takeAgent b, ⟨rest, .write [] []⟩, 1) := by
    have h := XMach.act_half (xs := xs) (X := X.takeAgent a) (todo := rest) (a := a) (b := b)
      (α := α) (β := β) (R := R) (by rw [ite_pos' ⟨h₄, hne⟩]; exact hR)
    rw [hA, hL] at h
    exact h
  have s₆ : XMach.act xs ((X.takeAgent a).takeAgent b) ⟨rest, .write [] []⟩ =
      ((X.takeAgent a).takeAgent b, ⟨((X.takeAgent a).takeAgent b).agents, .idle⟩, 0) := rfl
  exact .step (c₁ := 0) (c := 1) (k := 5) (fun h => by cases h) s₁
    (.step (c₁ := 0) (c := 1) (k := 4) (fun h => by cases h) s₂
      (.step (c₁ := 0) (c := 1) (k := 3) (fun h => by cases h) s₃
        (.step (c₁ := 0) (c := 1) (k := 2) (fun h => by cases h) s₄
          (.step (c₁ := 1) (c := 0) (k := 1) (fun h => by cases h) s₅
            (.step (c₁ := 0) (c := 0) (k := 0) (fun h => by cases h) s₆ (.refl _ _))))))

/-- The state of a thread after `j` actions of its own on the memory `X`,
as long as the memory stays as it is. -/
def XThread.after (xs : XSys S) (X : XNet S) : XThread S → Nat → XThread S
  | T, 0 => T
  | T, j + 1 => XThread.after xs X (XMach.act xs X T).2.1 j

theorem XThread.after_succ (xs : XSys S) (X : XNet S) : ∀ (j : Nat) (T : XThread S),
    T.after xs X (j + 1) = (XMach.act xs X (T.after xs X j)).2.1
  | 0, _ => rfl
  | j + 1, T => XThread.after_succ xs X j (XMach.act xs X T).2.1

/-- A thread none of whose actions changes the memory `X`. -/
def XThread.Reads (xs : XSys S) (X : XNet S) (T : XThread S) : Prop :=
  ∀ j, (XMach.act xs X (T.after xs X j)).1 = X

/-- A thread that comes to rest in `k` actions without writing never writes,
is not at rest before its `k`-th action, and is at rest from then on. -/
theorem Stays.after {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k)
    (hT' : T' = ⟨[], .idle⟩) :
    T.Reads xs X ∧ (∀ j, j < k → T.after xs X j ≠ ⟨[], .idle⟩) ∧
      ∀ j, k ≤ j → T.after xs X j = ⟨[], .idle⟩ := by
  induction st with
  | refl T =>
    subst hT'
    have hr : ∀ j, (⟨[], .idle⟩ : XThread S).after xs X j = ⟨[], .idle⟩ := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => exact ih
    refine ⟨fun j => ?_, fun j hj => absurd hj (Nat.not_lt_zero j), fun j _ => hr j⟩
    rw [hr j]
    rfl
  | @step T T₁ T' k hT h _ ih =>
    obtain ⟨r, lo, hi⟩ := ih hT'
    have e : (XMach.act xs X T).2.1 = T₁ := by rw [h]
    have sh : ∀ j, T.after xs X (j + 1) = T₁.after xs X j := by
      intro j
      show XThread.after xs X (XMach.act xs X T).2.1 j = _
      rw [e]
    refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero =>
        show (XMach.act xs X T).1 = X
        rw [h]
      | succ j =>
        rw [sh j]
        exact r j
    · cases j with
      | zero => exact hT
      | succ j =>
        rw [sh j]
        exact lo j (by omega)
    · cases j with
      | zero => omega
      | succ j =>
        rw [sh j]
        exact hi j (by omega)

/-- How many of the first `i` actions of a schedule go to thread `t`. -/
def hits (σ : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => hits σ t i + if σ i = t then 1 else 0

/-- **Threads that only read do not disturb each other**: under any
schedule the memory stays as it is, and each thread is where its own actions
alone would have taken it. -/
theorem XMach.trace_reads {M : XMach S} (σ : Nat → Nat)
    (hR : ∀ T, T ∈ M.ths → T.Reads xs M.mem) :
    ∀ i, (M.trace xs σ i).1.mem = M.mem ∧ (M.trace xs σ i).1.ths.length = M.ths.length ∧
      ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T →
        (M.trace xs σ i).1.ths[t]? = some (T.after xs M.mem (hits σ t i))
  | 0 => ⟨rfl, rfl, fun _ _ h => h⟩
  | i + 1 => by
    obtain ⟨hm, hl, ht⟩ := XMach.trace_reads σ hR i
    show ((M.trace xs σ i).1.step xs (σ i)).1.mem = M.mem ∧
      ((M.trace xs σ i).1.step xs (σ i)).1.ths.length = M.ths.length ∧
      ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T →
        ((M.trace xs σ i).1.step xs (σ i)).1.ths[t]? =
          some (T.after xs M.mem (hits σ t i + if σ i = t then 1 else 0))
    cases hs : M.ths[σ i]? with
    | none =>
      have hn : (M.trace xs σ i).1.ths[σ i]? = none := by
        rw [List.getElem?_eq_none_iff] at hs ⊢
        rw [hl]
        exact hs
      have e : (M.trace xs σ i).1.step xs (σ i) = ((M.trace xs σ i).1, 0) := by
        unfold XMach.step
        rw [hn]
      rw [e]
      refine ⟨hm, hl, fun t T h => ?_⟩
      have hne : ¬ σ i = t := by
        intro e'
        rw [e', h] at hs
        cases hs
      rw [ite_neg' hne]
      exact ht t T h
    | some T' =>
      have hU := ht (σ i) T' hs
      have hlt : σ i < (M.trace xs σ i).1.ths.length := (List.getElem?_eq_some_iff.1 hU).1
      have es := XMach.step_eq (xs := xs) hU
        (rfl : XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i)) =
          ((XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i))).1,
            (XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i))).2.1,
            (XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i))).2.2))
      rw [es]
      refine ⟨?_, ?_, fun t T h => ?_⟩
      · show (XMach.act xs (M.trace xs σ i).1.mem
          (T'.after xs M.mem (hits σ (σ i) i))).1 = M.mem
        rw [hm]
        exact hR T' (List.mem_of_getElem? hs) _
      · show ((M.trace xs σ i).1.ths.set (σ i) _).length = M.ths.length
        rw [List.length_set]
        exact hl
      · by_cases hst : σ i = t
        · subst hst
          have eT : T = T' := by
            rw [hs] at h
            exact (Option.some.inj h).symm
          subst eT
          show ((M.trace xs σ i).1.ths.set (σ i) (XMach.act xs (M.trace xs σ i).1.mem
              (T.after xs M.mem (hits σ (σ i) i))).2.1)[σ i]? =
            some (T.after xs M.mem (hits σ (σ i) i + if σ i = σ i then 1 else 0))
          rw [List.getElem?_set_self hlt, ite_pos' rfl, hm, XThread.after_succ]
        · show ((M.trace xs σ i).1.ths.set (σ i) _)[t]? =
            some (T.after xs M.mem (hits σ t i + if σ i = t then 1 else 0))
          rw [List.getElem?_set_ne hst, ite_neg' hst]
          exact ht t T h

/-- If thread `u` gets one action at most in any `F` actions in a row, its
hit number `c + 1` comes after `F * c` actions or more. -/
theorem hits_sparse {σ : Nat → Nat} {F u : Nat}
    (hσ : ∀ i j, i < j → σ i = u → σ j = u → i + F ≤ j) :
    ∀ i c, hits σ u i = c + 1 → ∃ l, l < i ∧ σ l = u ∧ F * c ≤ l
  | 0, c, h => by
    have h' : (0 : Nat) = c + 1 := h
    omega
  | i + 1, c, h => by
    by_cases h0 : σ i = u
    · have e : hits σ u i + 1 = c + 1 := by
        have h' : hits σ u i + (if σ i = u then 1 else 0) = c + 1 := h
        rw [ite_pos' h0] at h'
        exact h'
      refine ⟨i, Nat.lt_succ_self i, h0, ?_⟩
      cases c with
      | zero => omega
      | succ c' =>
        obtain ⟨l, hl, hl0, hle⟩ := hits_sparse hσ i c' (by omega)
        have := hσ l i hl hl0 h0
        rw [Nat.mul_add, Nat.mul_one]
        omega
    · have e : hits σ u i = c + 1 := by
        have h' : hits σ u i + (if σ i = u then 1 else 0) = c + 1 := h
        rw [ite_neg' h0] at h'
        exact h'
      obtain ⟨l, hl, hl0, hle⟩ := hits_sparse hσ i c e
      exact ⟨l, Nat.lt_succ_of_lt hl, hl0, hle⟩

/-- A thread that gets one action at most in any `F` in a row has had fewer
than `k` actions after `F * k - F` actions of the program. -/
theorem hits_lt {σ : Nat → Nat} {F k u : Nat} (hF : 0 < F)
    (hσ : ∀ i j, i < j → σ i = u → σ j = u → i + F ≤ j) {i : Nat} (hi : i + F ≤ F * k) :
    hits σ u i < k := by
  cases hc' : hits σ u i with
  | zero =>
    cases k with
    | zero => omega
    | succ k' => exact Nat.succ_pos k'
  | succ c =>
    obtain ⟨l, hl, -, hle⟩ := hits_sparse hσ i c hc'
    have h1 : F * (c + 1) < F * k := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact Nat.lt_of_mul_lt_mul_left h1

/-- **A starved thread stretches the run.**  Take threads that only read,
one of which needs `k` actions of its own to come to rest, and a
schedule that gives it one action at most in any `F` actions in a row.  The
program is not at rest after `F * k - F` actions or fewer. -/
theorem XMach.starved {M : XMach S} {T₀ : XThread S} {k F u : Nat} (σ : Nat → Nat)
    (hR : ∀ T, T ∈ M.ths → T.Reads xs M.mem) (h0 : M.ths[u]? = some T₀)
    (hk : Stays xs M.mem T₀ ⟨[], .idle⟩ k) (hF : 0 < F)
    (hσ : ∀ i j, i < j → σ i = u → σ j = u → i + F ≤ j) :
    ∀ i, i + F ≤ F * k → ¬ (M.trace xs σ i).1.resting = true := by
  intro i hi hr
  obtain ⟨-, -, ht⟩ := XMach.trace_reads (xs := xs) σ hR i
  have h₀ := ht u T₀ h0
  obtain ⟨-, lo, -⟩ := hk.after rfl
  exact lo _ (hits_lt hF hσ hi)
    (XThread.eq_rest (List.all_eq_true.1 hr _ (List.mem_of_getElem? h₀)))

/-- The schedule that gives thread `0` every `F`-th action and thread `1`
the others. -/
def starve (F : Nat) : Nat → Nat := fun i => if i % F = 0 then 0 else 1

/-- It gives each of two threads an action in every window of `F`. -/
theorem starve_fair {F : Nat} (hF : 2 ≤ F) :
    ∀ u, u < 2 → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ starve F j = u := by
  intro u hu i
  rcases Nat.lt_or_ge u 1 with h | h
  · obtain ⟨j, h₁, h₂, h₃⟩ := roundRobin_fair (nt := F) 0 (by omega) i
    refine ⟨j, h₁, h₂, ?_⟩
    show (if j % F = 0 then 0 else 1) = u
    rw [ite_pos' h₃]
    omega
  · obtain ⟨j, h₁, h₂, h₃⟩ := roundRobin_fair (nt := F) 1 (by omega) i
    refine ⟨j, h₁, h₂, ?_⟩
    show (if j % F = 0 then 0 else 1) = u
    rw [ite_neg' (by omega)]
    omega

/-- It gives thread `0` one action in any `F` in a row. -/
theorem starve_sparse (F : Nat) :
    ∀ i j, i < j → starve F i = 0 → starve F j = 0 → i + F ≤ j := by
  intro i j hij hi hj
  have mz : ∀ x, starve F x = 0 → x % F = 0 := by
    intro x hx
    by_cases h : x % F = 0
    · exact h
    · have hx' : (if x % F = 0 then 0 else 1) = 0 := hx
      rw [ite_neg' h] at hx'
      omega
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero (mz i hi)
  obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero (mz j hj)
  have hab : a < b := Nat.lt_of_mul_lt_mul_left hij
  have h := Nat.mul_le_mul_left F (Nat.succ_le_of_lt hab)
  rw [Nat.mul_succ] at h
  exact h

/-- A thread drops an entry of its list whose agent is not in memory, in
one action. -/
theorem Stays.absent {X : XNet S} {e : Id × S} (rest : List (Id × S))
    (h : ¬ assoc e.1 X.agents = some e.2) :
    Stays xs X ⟨e :: rest, .idle⟩ ⟨rest, .idle⟩ 1 :=
  .step (k := 0) (fun h => by cases h) (XMach.act_idle_neg h) (.refl _)

/-- A run depends on the schedule up to the point reached only. -/
theorem XMach.trace_congr (xs : XSys S) (M : XMach S) {σ σ' : Nat → Nat} :
    ∀ i, (∀ j, j < i → σ j = σ' j) → M.trace xs σ i = M.trace xs σ' i
  | 0, _ => rfl
  | i + 1, h => by
    have ih := XMach.trace_congr xs M i fun j hj => h j (Nat.lt_succ_of_lt hj)
    show (((M.trace xs σ i).1.step xs (σ i)).1,
        (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2) =
      (((M.trace xs σ' i).1.step xs (σ' i)).1,
        (M.trace xs σ' i).2 + ((M.trace xs σ' i).1.step xs (σ' i)).2)
    rw [ih, h i (Nat.lt_succ_self i)]

/-- A run in two parts: the second part is the run from the state reached,
under the rest of the schedule. -/
theorem XMach.trace_add (xs : XSys S) (σ : Nat → Nat) (M : XMach S) (a : Nat) : ∀ b,
    M.trace xs σ (a + b) =
      (((M.trace xs σ a).1.trace xs (fun i => σ (a + i)) b).1,
        (M.trace xs σ a).2 + ((M.trace xs σ a).1.trace xs (fun i => σ (a + i)) b).2)
  | 0 => rfl
  | b + 1 => by
    have ih := XMach.trace_add xs σ M a b
    show (((M.trace xs σ (a + b)).1.step xs (σ (a + b))).1,
        (M.trace xs σ (a + b)).2 + ((M.trace xs σ (a + b)).1.step xs (σ (a + b))).2) = _
    rw [ih]
    exact congrArg (Prod.mk _) (Nat.add_assoc _ _ _)

/-- A counted run of one thread among others that wait. -/
theorem Works.trace_at {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (w : Works xs X T X' T' c k) : ∀ (ths : List (XThread S)) (t : Nat), ths[t]? = some T →
      (⟨X, ths⟩ : XMach S).trace xs (fun _ => t) k = (⟨X', ths.set t T'⟩, c) := by
  induction w with
  | refl X T =>
    intro ths t ht
    show ((⟨X, ths⟩ : XMach S), 0) = (⟨X, ths.set t T⟩, 0)
    rw [set_self ths t T ht]
  | @step X X₁ X' T T₁ T' c₁ c k hT h _ ih =>
    intro ths t ht
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
    have es : XMach.step xs ⟨X, ths⟩ t = (⟨X₁, ths.set t T₁⟩, c₁) :=
      XMach.step_eq (M := ⟨X, ths⟩) ht h
    rw [XMach.trace_shift xs t ⟨X, ths⟩ k, es]
    show (((⟨X₁, ths.set t T₁⟩ : XMach S).trace xs (fun _ => t) k).1,
      c₁ + ((⟨X₁, ths.set t T₁⟩ : XMach S).trace xs (fun _ => t) k).2) = _
    rw [ih (ths.set t T₁) t (List.getElem?_set_self hlt), List.set_set]

/-- Once at rest, the program stays at rest. -/
theorem XMach.resting_trace (σ : Nat → Nat) {M : XMach S} {i : Nat}
    (h : (M.trace xs σ i).1.resting = true) : ∀ d, (M.trace xs σ (i + d)).1.resting = true
  | 0 => h
  | d + 1 => by
    have ih := XMach.resting_trace σ h d
    show ((M.trace xs σ (i + d)).1.step xs (σ (i + d))).1.resting = true
    rw [XMach.resting_step ih]
    exact ih

/-- The memory and the state of a thread after `j` actions of its own, no
other thread acting. -/
def XMach.solo (xs : XSys S) : XNet S → XThread S → Nat → XNet S × XThread S
  | X, T, 0 => (X, T)
  | X, T, j + 1 => XMach.solo xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 j

theorem XMach.solo_succ (xs : XSys S) : ∀ (j : Nat) (X : XNet S) (T : XThread S),
    XMach.solo xs X T (j + 1) =
      ((XMach.act xs (XMach.solo xs X T j).1 (XMach.solo xs X T j).2).1,
        (XMach.act xs (XMach.solo xs X T j).1 (XMach.solo xs X T j).2).2.1)
  | 0, _, _ => rfl
  | j + 1, X, T => XMach.solo_succ xs j (XMach.act xs X T).1 (XMach.act xs X T).2.1

/-- A counted run, as a sequence of states: the thread is not at rest
before the end. -/
theorem Works.solo {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (w : Works xs X T X' T' c k) :
    XMach.solo xs X T k = (X', T') ∧ ∀ j, j < k → (XMach.solo xs X T j).2 ≠ ⟨[], .idle⟩ := by
  induction w with
  | refl X T => exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | @step X X₁ X' T T₁ T' c₁ c k hT h _ ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have sh : ∀ j, XMach.solo xs X T (j + 1) = XMach.solo xs X₁ T₁ j := by
      intro j
      show XMach.solo xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 j = _
      rw [h]
    refine ⟨by rw [sh k]; exact ih₁, fun j hj => ?_⟩
    cases j with
    | zero => exact hT
    | succ j =>
      rw [sh j]
      exact ih₂ j (by omega)

/-- **One thread at work, the others at rest**: under any schedule the
program is where the thread's own actions alone would have taken it. -/
theorem XMach.trace_lone {M : XMach S} {T₀ : XThread S} {u : Nat} (σ : Nat → Nat)
    (h0 : M.ths[u]? = some T₀)
    (hrest : ∀ (t : Nat) (T : XThread S), t ≠ u → M.ths[t]? = some T → T = ⟨[], .idle⟩) :
    ∀ i, (M.trace xs σ i).1.mem = (XMach.solo xs M.mem T₀ (hits σ u i)).1 ∧
      (M.trace xs σ i).1.ths = M.ths.set u (XMach.solo xs M.mem T₀ (hits σ u i)).2
  | 0 => ⟨rfl, (set_self M.ths u T₀ h0).symm⟩
  | i + 1 => by
    obtain ⟨hm, ht⟩ := XMach.trace_lone σ h0 hrest i
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h0
    show ((M.trace xs σ i).1.step xs (σ i)).1.mem =
        (XMach.solo xs M.mem T₀ (hits σ u i + if σ i = u then 1 else 0)).1 ∧
      ((M.trace xs σ i).1.step xs (σ i)).1.ths =
        M.ths.set u (XMach.solo xs M.mem T₀ (hits σ u i + if σ i = u then 1 else 0)).2
    by_cases hs : σ i = u
    · have hU : (M.trace xs σ i).1.ths[σ i]? =
          some (XMach.solo xs M.mem T₀ (hits σ u i)).2 := by
        rw [hs, ht]
        exact List.getElem?_set_self hlt
      have es := XMach.step_eq (xs := xs) hU
        (rfl : XMach.act xs (M.trace xs σ i).1.mem (XMach.solo xs M.mem T₀ (hits σ u i)).2 =
          ((XMach.act xs (M.trace xs σ i).1.mem (XMach.solo xs M.mem T₀ (hits σ u i)).2).1,
            (XMach.act xs (M.trace xs σ i).1.mem (XMach.solo xs M.mem T₀ (hits σ u i)).2).2.1,
            (XMach.act xs (M.trace xs σ i).1.mem
              (XMach.solo xs M.mem T₀ (hits σ u i)).2).2.2))
      rw [es, ite_pos' hs, XMach.solo_succ]
      constructor
      · show (XMach.act xs (M.trace xs σ i).1.mem
          (XMach.solo xs M.mem T₀ (hits σ u i)).2).1 = _
        rw [hm]
      · show (M.trace xs σ i).1.ths.set (σ i) (XMach.act xs (M.trace xs σ i).1.mem
          (XMach.solo xs M.mem T₀ (hits σ u i)).2).2.1 = _
        rw [ht, hs, List.set_set, hm]
    · rw [ite_neg' hs]
      cases hU : (M.trace xs σ i).1.ths[σ i]? with
      | none =>
        have e : (M.trace xs σ i).1.step xs (σ i) = ((M.trace xs σ i).1, 0) := by
          unfold XMach.step
          rw [hU]
        rw [e]
        exact ⟨hm, ht⟩
      | some U =>
        have hU' : M.ths[σ i]? = some U := by
          rw [ht, List.getElem?_set_ne (Ne.symm hs)] at hU
          exact hU
        have eU := hrest (σ i) U hs hU'
        rw [eU] at hU
        have es := XMach.step_eq (xs := xs) hU
          (rfl : XMach.act xs (M.trace xs σ i).1.mem ⟨[], .idle⟩ =
            ((M.trace xs σ i).1.mem, ⟨[], .idle⟩, 0))
        rw [es, set_self _ _ _ hU]
        exact ⟨hm, ht⟩

/-- **A starved worker stretches the run.**  If a thread has `k`
actions of its own to make, whatever they do, the other threads are at rest,
and the schedule gives it one action at most in any `F` in a row, the
program is not at rest after `F * k - F` actions or fewer. -/
theorem XMach.starved_worker {M : XMach S} {T₀ T' : XThread S} {X' : XNet S} {c k F u : Nat}
    (σ : Nat → Nat) (h0 : M.ths[u]? = some T₀)
    (hrest : ∀ (t : Nat) (T : XThread S), t ≠ u → M.ths[t]? = some T → T = ⟨[], .idle⟩)
    (hk : Works xs M.mem T₀ X' T' c k) (hF : 0 < F)
    (hσ : ∀ i j, i < j → σ i = u → σ j = u → i + F ≤ j) :
    ∀ i, i + F ≤ F * k → ¬ (M.trace xs σ i).1.resting = true := by
  intro i hi hr
  obtain ⟨-, ht⟩ := XMach.trace_lone (xs := xs) σ h0 hrest i
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h0
  have hmem : (XMach.solo xs M.mem T₀ (hits σ u i)).2 ∈ (M.trace xs σ i).1.ths := by
    rw [ht]
    exact List.mem_of_getElem? (List.getElem?_set_self hlt)
  exact hk.solo.2 _ (hits_lt hF hσ hi) (XThread.eq_rest (List.all_eq_true.1 hr _ hmem))

end Works

section Handoff

variable [DecidableEq S] {xs : XSys S}

omit [DecidableEq S] in
/-- With two threads, the second starts one agent further down the list. -/
theorem XMach.init_two (X : XNet S) :
    XMach.init X 2 =
      ⟨X, [⟨X.agents, .idle⟩, ⟨X.agents.drop 1 ++ X.agents.take 1, .idle⟩]⟩ := by
  show (⟨X, [⟨X.agents ++ [], .idle⟩, ⟨X.agents.drop 1 ++ X.agents.take 1, .idle⟩]⟩ :
    XMach S) = _
  rw [List.append_nil]

/-- The schedule that gives thread `0` the first `b` actions, thread `1`
the next `c`, and from then on thread `0` every `F`-th action and thread `1`
the others. -/
def handoff (b c F : Nat) : Nat → Nat := fun i =>
  if i < b then 0 else if i < b + c then 1 else if (i - (b + c)) % F = 0 then 0 else 1

theorem handoff_first {b c F i : Nat} (h : i < b) : handoff b c F i = 0 :=
  ite_pos' h

theorem handoff_second {b c F i : Nat} (h₁ : b ≤ i) (h₂ : i < b + c) : handoff b c F i = 1 := by
  show (if i < b then 0 else if i < b + c then 1 else
    if (i - (b + c)) % F = 0 then 0 else 1) = 1
  rw [ite_neg' (by omega), ite_pos' h₂]

theorem handoff_tail (b c F j : Nat) : handoff b c F (b + c + j) = starve F j := by
  show (if b + c + j < b then 0 else if b + c + j < b + c then 1 else
    if (b + c + j - (b + c)) % F = 0 then 0 else 1) = if j % F = 0 then 0 else 1
  rw [ite_neg' (by omega), ite_neg' (by omega), Nat.add_sub_cancel_left]

/-- It gives each of two threads an action in every window of `F`, if
neither turn at the start is as long as the window. -/
theorem handoff_fair {b c F : Nat} (hb : 0 < b) (hc : 0 < c) (hbF : b < F) (hcF : c < F) :
    ∀ u, u < 2 → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ handoff b c F j = u := by
  intro u hu i
  rcases Nat.lt_or_ge i (b + c) with hi | hi
  · rcases Nat.lt_or_ge u 1 with h | h
    · have e : u = 0 := by omega
      subst e
      rcases Nat.lt_or_ge i b with hib | hib
      · exact ⟨i, Nat.le_refl i, by omega, handoff_first hib⟩
      · refine ⟨b + c, by omega, by omega, ?_⟩
        have e := handoff_tail b c F 0
        rw [Nat.add_zero] at e
        rw [e]
        show (if 0 % F = 0 then 0 else 1) = 0
        rw [ite_pos' (Nat.zero_mod F)]
    · have e : u = 1 := by omega
      subst e
      rcases Nat.lt_or_ge i b with hib | hib
      · exact ⟨b, by omega, by omega, handoff_second (Nat.le_refl b) (by omega)⟩
      · exact ⟨i, Nat.le_refl i, by omega, handoff_second hib hi⟩
  · obtain ⟨j, h₁, h₂, h₃⟩ := starve_fair (F := F) (by omega) u hu (i - (b + c))
    refine ⟨b + c + j, by omega, by omega, ?_⟩
    rw [handoff_tail]
    exact h₃

/-- The run under that schedule: after the two turns at the start, it is
the run from the state they lead to, with thread `0` starved. -/
theorem XMach.trace_handoff {M M₁ M₂ : XMach S} {b c F c₁ c₂ : Nat}
    (h₁ : M.trace xs (fun _ => 0) b = (M₁, c₁)) (h₂ : M₁.trace xs (fun _ => 1) c = (M₂, c₂)) :
    ∀ d, (M.trace xs (handoff b c F) (b + c + d)).1 = (M₂.trace xs (starve F) d).1 := by
  intro d
  have e₁ : M.trace xs (handoff b c F) b = (M₁, c₁) := by
    rw [XMach.trace_congr xs M (σ' := fun _ => 0) b fun j hj => handoff_first hj]
    exact h₁
  have e₂ : M.trace xs (handoff b c F) (b + c) = (M₂, c₁ + c₂) := by
    rw [XMach.trace_add xs (handoff b c F) M b c, e₁]
    show ((M₁.trace xs (fun i => handoff b c F (b + i)) c).1,
      c₁ + (M₁.trace xs (fun i => handoff b c F (b + i)) c).2) = _
    rw [XMach.trace_congr xs M₁ (σ' := fun _ => 1) c fun j hj =>
      handoff_second (Nat.le_add_right b j) (by omega), h₂]
  rw [XMach.trace_add xs (handoff b c F) M (b + c) d, e₂]
  show (M₂.trace xs (fun i => handoff b c F (b + c + i)) d).1 = _
  rw [XMach.trace_congr xs M₂ (σ' := starve F) d fun j _ => handoff_tail b c F j]

end Handoff

/-! ### Two threads in step

Threads that only read for a while can each be followed on its own.  Two
threads that take turns stay in step, so one can reach an agent just behind
the other; after that, one of them may be starved. -/

section Abreast

variable [DecidableEq S] {xs : XSys S}

/-- A run that leaves the memory alone, as a sequence of states: where the
thread is after it, and that none of its actions writes. -/
theorem Stays.after_eq {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k) :
    T.after xs X k = T' ∧ ∀ j, j < k → (XMach.act xs X (T.after xs X j)).1 = X := by
  induction st with
  | refl T => exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | @step T T₁ T' k hT h _ ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have e : (XMach.act xs X T).2.1 = T₁ := by rw [h]
    have sh : ∀ j, T.after xs X (j + 1) = T₁.after xs X j := by
      intro j
      show XThread.after xs X (XMach.act xs X T).2.1 j = _
      rw [e]
    refine ⟨by rw [sh k]; exact ih₁, fun j hj => ?_⟩
    cases j with
    | zero =>
      show (XMach.act xs X T).1 = X
      rw [h]
    | succ j =>
      rw [sh j]
      exact ih₂ j (by omega)

/-- **Threads that only read for a while do not disturb each other
meanwhile**: if thread `t` does not write in its first `b t` actions on the
memory as it is, then under any schedule, as long as no thread has had more
actions than that, the memory stays as it is and each thread is where its
own actions alone would have taken it. -/
theorem XMach.trace_quiet {M : XMach S} (σ : Nat → Nat) (b : Nat → Nat)
    (hR : ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T → ∀ j, j < b t →
      (XMach.act xs M.mem (T.after xs M.mem j)).1 = M.mem) :
    ∀ i, (∀ (t : Nat) (T : XThread S), M.ths[t]? = some T → hits σ t i ≤ b t) →
      (M.trace xs σ i).1.mem = M.mem ∧ (M.trace xs σ i).1.ths.length = M.ths.length ∧
      ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T →
        (M.trace xs σ i).1.ths[t]? = some (T.after xs M.mem (hits σ t i))
  | 0, _ => ⟨rfl, rfl, fun _ _ h => h⟩
  | i + 1, hb => by
    have hb' : ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T → hits σ t i ≤ b t := by
      intro t T h
      have h' : hits σ t i + (if σ i = t then 1 else 0) ≤ b t := hb t T h
      omega
    obtain ⟨hm, hl, ht⟩ := XMach.trace_quiet σ b hR i hb'
    show ((M.trace xs σ i).1.step xs (σ i)).1.mem = M.mem ∧
      ((M.trace xs σ i).1.step xs (σ i)).1.ths.length = M.ths.length ∧
      ∀ (t : Nat) (T : XThread S), M.ths[t]? = some T →
        ((M.trace xs σ i).1.step xs (σ i)).1.ths[t]? =
          some (T.after xs M.mem (hits σ t i + if σ i = t then 1 else 0))
    cases hs : M.ths[σ i]? with
    | none =>
      have hn : (M.trace xs σ i).1.ths[σ i]? = none := by
        rw [List.getElem?_eq_none_iff] at hs ⊢
        rw [hl]
        exact hs
      have e : (M.trace xs σ i).1.step xs (σ i) = ((M.trace xs σ i).1, 0) := by
        unfold XMach.step
        rw [hn]
      rw [e]
      refine ⟨hm, hl, fun t T h => ?_⟩
      have hne : ¬ σ i = t := by
        intro e'
        rw [e', h] at hs
        cases hs
      rw [ite_neg' hne]
      exact ht t T h
    | some T' =>
      have hU := ht (σ i) T' hs
      have hlt : σ i < (M.trace xs σ i).1.ths.length := (List.getElem?_eq_some_iff.1 hU).1
      have es := XMach.step_eq (xs := xs) hU
        (rfl : XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i)) =
          ((XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i))).1,
            (XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i))).2.1,
            (XMach.act xs (M.trace xs σ i).1.mem (T'.after xs M.mem (hits σ (σ i) i))).2.2))
      rw [es]
      refine ⟨?_, ?_, fun t T h => ?_⟩
      · show (XMach.act xs (M.trace xs σ i).1.mem
          (T'.after xs M.mem (hits σ (σ i) i))).1 = M.mem
        rw [hm]
        refine hR (σ i) T' hs _ ?_
        have h' : hits σ (σ i) i + (if σ i = σ i then 1 else 0) ≤ b (σ i) := hb (σ i) T' hs
        rw [ite_pos' rfl] at h'
        omega
      · show ((M.trace xs σ i).1.ths.set (σ i) _).length = M.ths.length
        rw [List.length_set]
        exact hl
      · by_cases hst : σ i = t
        · subst hst
          have eT : T = T' := by
            rw [hs] at h
            exact (Option.some.inj h).symm
          subst eT
          show ((M.trace xs σ i).1.ths.set (σ i) (XMach.act xs (M.trace xs σ i).1.mem
              (T.after xs M.mem (hits σ (σ i) i))).2.1)[σ i]? =
            some (T.after xs M.mem (hits σ (σ i) i + if σ i = σ i then 1 else 0))
          rw [List.getElem?_set_self hlt, ite_pos' rfl, hm, XThread.after_succ]
        · show ((M.trace xs σ i).1.ths.set (σ i) _)[t]? =
            some (T.after xs M.mem (hits σ t i + if σ i = t then 1 else 0))
          rw [List.getElem?_set_ne hst, ite_neg' hst]
          exact ht t T h

/-- With two threads taking turns, the second first, each has had `m` of
the first `2 * m` actions. -/
theorem hits_turns (m : Nat) :
    hits (fun i => (i + 1) % 2) 0 (2 * m) = m ∧ hits (fun i => (i + 1) % 2) 1 (2 * m) = m := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [Nat.mul_succ]
    constructor
    · show hits (fun i => (i + 1) % 2) 0 (2 * m) + (if (2 * m + 1) % 2 = 0 then 1 else 0) +
        (if (2 * m + 1 + 1) % 2 = 0 then 1 else 0) = m + 1
      rw [h0, ite_neg' (by omega), ite_pos' (by omega)]
    · show hits (fun i => (i + 1) % 2) 1 (2 * m) + (if (2 * m + 1) % 2 = 1 then 1 else 0) +
        (if (2 * m + 1 + 1) % 2 = 1 then 1 else 0) = m + 1
      rw [h1, ite_pos' (by omega), ite_neg' (by omega)]

/-- A list of two entries is its two entries. -/
theorem list_two {A : Type} {l : List A} {a b : A} (hl : l.length = 2) (h0 : l[0]? = some a)
    (h1 : l[1]? = some b) : l = [a, b] := by
  match l, hl with
  | [x, y], _ =>
    rw [List.getElem?_cons_zero] at h0
    rw [List.getElem?_cons_succ, List.getElem?_cons_zero] at h1
    rw [Option.some.inj h0, Option.some.inj h1]

/-- **Two threads that only read, in turn**: if neither writes in its first
`m` actions on the memory as it is, then after `m` actions each the memory
is as it was and each thread is where its own actions have taken it. -/
theorem XMach.trace_turns {X : XNet S} {T₀ T₁ T₀' T₁' : XThread S} {m : Nat}
    (s₀ : Stays xs X T₀ T₀' m) (s₁ : Stays xs X T₁ T₁' m) :
    ((⟨X, [T₀, T₁]⟩ : XMach S).trace xs (fun i => (i + 1) % 2) (2 * m)).1 = ⟨X, [T₀', T₁']⟩ := by
  obtain ⟨a₀, r₀⟩ := s₀.after_eq
  obtain ⟨a₁, r₁⟩ := s₁.after_eq
  obtain ⟨h0, h1⟩ := hits_turns m
  obtain ⟨hm, hl, ht⟩ := XMach.trace_quiet (xs := xs) (M := ⟨X, [T₀, T₁]⟩)
    (fun i => (i + 1) % 2) (fun _ => m)
    (fun t T h j hj => by
      cases t with
      | zero =>
        rw [← Option.some.inj h]
        exact r₀ j hj
      | succ t =>
        cases t with
        | zero =>
          rw [← Option.some.inj h]
          exact r₁ j hj
        | succ t => cases h)
    (2 * m)
    (fun t T h => by
      cases t with
      | zero => exact Nat.le_of_eq h0
      | succ t =>
        cases t with
        | zero => exact Nat.le_of_eq h1
        | succ t => cases h)
  have e₀ := ht 0 T₀ rfl
  have e₁ := ht 1 T₁ rfl
  rw [h0] at e₀
  rw [h1] at e₁
  have el := list_two hl
    (e₀.trans (congrArg some a₀)) (e₁.trans (congrArg some a₁))
  have eM : ((⟨X, [T₀, T₁]⟩ : XMach S).trace xs (fun i => (i + 1) % 2) (2 * m)).1 =
      ⟨((⟨X, [T₀, T₁]⟩ : XMach S).trace xs (fun i => (i + 1) % 2) (2 * m)).1.mem,
        ((⟨X, [T₀, T₁]⟩ : XMach S).trace xs (fun i => (i + 1) % 2) (2 * m)).1.ths⟩ := rfl
  rw [eM, hm, el]

/-- A run of two threads in turn, in two parts. -/
theorem XMach.trace_turns_add (xs : XSys S) (M : XMach S) (m m' : Nat) :
    (M.trace xs (fun i => (i + 1) % 2) (2 * (m + m'))).1 =
      ((M.trace xs (fun i => (i + 1) % 2) (2 * m)).1.trace xs (fun i => (i + 1) % 2)
        (2 * m')).1 := by
  rw [Nat.mul_add, XMach.trace_add xs (fun i => (i + 1) % 2) M (2 * m) (2 * m')]
  show ((M.trace xs (fun i => (i + 1) % 2) (2 * m)).1.trace xs
    (fun i => (2 * m + i + 1) % 2) (2 * m')).1 = _
  rw [XMach.trace_congr xs _ (σ' := fun i => (i + 1) % 2) (2 * m') fun j _ => by
    show (2 * m + j + 1) % 2 = (j + 1) % 2
    omega]

/-- One action of each of two threads in turn, the second first. -/
theorem XMach.trace_round {X X₁ X₂ : XNet S} {T₀ T₀' T₁ T₁' : XThread S} {c₁ c₂ : Nat}
    (a₁ : XMach.act xs X T₁ = (X₁, T₁', c₁)) (a₂ : XMach.act xs X₁ T₀ = (X₂, T₀', c₂)) :
    ((⟨X, [T₀, T₁]⟩ : XMach S).trace xs (fun i => (i + 1) % 2) (2 * 1)).1 =
      ⟨X₂, [T₀', T₁']⟩ := by
  have e₁ : XMach.step xs ⟨X, [T₀, T₁]⟩ 1 = (⟨X₁, [T₀, T₁']⟩, c₁) :=
    XMach.step_eq (M := ⟨X, [T₀, T₁]⟩) (t := 1) rfl a₁
  have e₂ : XMach.step xs ⟨X₁, [T₀, T₁']⟩ 0 = (⟨X₂, [T₀', T₁']⟩, c₂) :=
    XMach.step_eq (M := ⟨X₁, [T₀, T₁']⟩) (t := 0) rfl a₂
  show (XMach.step xs (XMach.step xs ⟨X, [T₀, T₁]⟩ 1).1 0).1 = _
  rw [e₁, e₂]

/-- The schedule that gives thread `1` every `F`-th action and thread `0`
the others. -/
def starveSnd (F : Nat) : Nat → Nat := fun i => if i % F = 0 then 1 else 0

/-- It gives each of two threads an action in every window of `F`. -/
theorem starveSnd_fair {F : Nat} (hF : 2 ≤ F) :
    ∀ u, u < 2 → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ starveSnd F j = u := by
  intro u hu i
  rcases Nat.lt_or_ge u 1 with h | h
  · obtain ⟨j, h₁, h₂, h₃⟩ := roundRobin_fair (nt := F) 1 (by omega) i
    refine ⟨j, h₁, h₂, ?_⟩
    show (if j % F = 0 then 1 else 0) = u
    rw [ite_neg' (by omega)]
    omega
  · obtain ⟨j, h₁, h₂, h₃⟩ := roundRobin_fair (nt := F) 0 (by omega) i
    refine ⟨j, h₁, h₂, ?_⟩
    show (if j % F = 0 then 1 else 0) = u
    rw [ite_pos' h₃]
    omega

/-- It gives thread `1` one action in any `F` in a row. -/
theorem starveSnd_sparse (F : Nat) :
    ∀ i j, i < j → starveSnd F i = 1 → starveSnd F j = 1 → i + F ≤ j := by
  intro i j hij hi hj
  have mz : ∀ x, starveSnd F x = 1 → x % F = 0 := by
    intro x hx
    by_cases h : x % F = 0
    · exact h
    · have hx' : (if x % F = 0 then 1 else 0) = 1 := hx
      rw [ite_neg' h] at hx'
      omega
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero (mz i hi)
  obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero (mz j hj)
  have hab : a < b := Nat.lt_of_mul_lt_mul_left hij
  have h := Nat.mul_le_mul_left F (Nat.succ_le_of_lt hab)
  rw [Nat.mul_succ] at h
  exact h

/-- The schedule that gives two threads an action each in turn, thread `1`
first, for `P` actions each, and from then on thread `1` every `F`-th
action and thread `0` the others. -/
def abreast (P F : Nat) : Nat → Nat := fun i =>
  if i < 2 * P then (i + 1) % 2 else starveSnd F (i - 2 * P)

theorem abreast_head {P F i : Nat} (h : i < 2 * P) : abreast P F i = (i + 1) % 2 :=
  ite_pos' h

theorem abreast_tail (P F j : Nat) : abreast P F (2 * P + j) = starveSnd F j := by
  show (if 2 * P + j < 2 * P then (2 * P + j + 1) % 2 else starveSnd F (2 * P + j - 2 * P)) = _
  rw [ite_neg' (by omega), Nat.add_sub_cancel_left]

/-- It gives each of two threads an action in every window of `F`, whatever
the window, as long as it has room for both. -/
theorem abreast_fair {P F : Nat} (hF : 2 ≤ F) :
    ∀ u, u < 2 → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ abreast P F j = u := by
  intro u hu i
  rcases Nat.lt_or_ge i (2 * P) with hi | hi
  · rcases Nat.lt_or_ge (i + 1) (2 * P) with hi' | hi'
    · by_cases h : (i + 1) % 2 = u
      · exact ⟨i, Nat.le_refl i, by omega, by rw [abreast_head hi]; exact h⟩
      · exact ⟨i + 1, by omega, by omega, by rw [abreast_head hi']; omega⟩
    · by_cases h : u = 0
      · refine ⟨i, Nat.le_refl i, by omega, ?_⟩
        rw [abreast_head hi]
        omega
      · refine ⟨2 * P, by omega, by omega, ?_⟩
        have e := abreast_tail P F 0
        rw [Nat.add_zero] at e
        rw [e]
        show (if 0 % F = 0 then 1 else 0) = u
        rw [ite_pos' (Nat.zero_mod F)]
        omega
  · obtain ⟨j, h₁, h₂, h₃⟩ := starveSnd_fair hF u hu (i - 2 * P)
    refine ⟨2 * P + j, by omega, by omega, ?_⟩
    rw [abreast_tail]
    exact h₃

/-- The run under that schedule: after the turns at the start, it is the
run from the state they lead to, with thread `1` starved. -/
theorem XMach.trace_abreast {M M₁ : XMach S} {P F : Nat}
    (h₁ : (M.trace xs (fun i => (i + 1) % 2) (2 * P)).1 = M₁) :
    ∀ d, (M.trace xs (abreast P F) (2 * P + d)).1 = (M₁.trace xs (starveSnd F) d).1 := by
  intro d
  rw [XMach.trace_add xs (abreast P F) M (2 * P) d]
  show ((M.trace xs (abreast P F) (2 * P)).1.trace xs (fun i => abreast P F (2 * P + i)) d).1 = _
  rw [XMach.trace_congr xs M (σ' := fun i => (i + 1) % 2) (2 * P) fun j hj => abreast_head hj,
    h₁, XMach.trace_congr xs M₁ (σ' := starveSnd F) d fun j _ => abreast_tail P F j]

/-- The schedule that gives each of `nt` threads one action in every `F`,
thread `0` no more than that, and the actions left over to thread `1`. -/
def starveAmong (nt F : Nat) : Nat → Nat := fun i => if i % F < nt then i % F else 1

/-- It gives each thread an action in every window of `F`, if the window
has room for them all. -/
theorem starveAmong_fair {nt F : Nat} (h : nt ≤ F) :
    ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ starveAmong nt F j = u := by
  intro u hu i
  obtain ⟨j, h₁, h₂, h₃⟩ := roundRobin_fair (nt := F) u (by omega) i
  refine ⟨j, h₁, h₂, ?_⟩
  show (if j % F < nt then j % F else 1) = u
  rw [ite_pos' (by omega)]
  exact h₃

/-- It gives thread `0` one action in any `F` in a row. -/
theorem starveAmong_sparse (nt F : Nat) :
    ∀ i j, i < j → starveAmong nt F i = 0 → starveAmong nt F j = 0 → i + F ≤ j := by
  intro i j hij hi hj
  have mz : ∀ x, starveAmong nt F x = 0 → x % F = 0 := by
    intro x hx
    have hx' : (if x % F < nt then x % F else 1) = 0 := hx
    by_cases h : x % F < nt
    · rw [ite_pos' h] at hx'
      exact hx'
    · rw [ite_neg' h] at hx'
      omega
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero (mz i hi)
  obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero (mz j hj)
  have hab : a < b := Nat.lt_of_mul_lt_mul_left hij
  have h := Nat.mul_le_mul_left F (Nat.succ_le_of_lt hab)
  rw [Nat.mul_succ] at h
  exact h

end Abreast

/-! ### Running time

The memory is lists, so an action that looks something up reads cells of
them.  An action is charged one unit, one more for each cell its lookups
pass, the whole list of agents when it takes an agent out or takes the list
afresh, and one for each cell of a right-hand side it builds.  The lookup
of a rule is part of the unit.  A thread at rest is charged nothing, since
the schedule never ends.  So time is work done, and its bound does not
depend on the schedule: a window stretches the run with rests, which are
free. -/

section Time

variable [DecidableEq S] {xs : XSys S}

/-- The cells of a list that a lookup reads: up to the first entry with the
key, that entry included. -/
def assocCells {A B : Type} [DecidableEq A] (p : A) : List (A × B) → Nat
  | [] => 0
  | (k, _) :: l => if k = p then 1 else assocCells p l + 1

theorem assocCells_le {A B : Type} [DecidableEq A] (p : A) :
    ∀ l : List (A × B), assocCells p l ≤ l.length
  | [] => Nat.le_refl 0
  | (k, v) :: l => by
    have ih := assocCells_le p l
    show (if k = p then 1 else assocCells p l + 1) ≤ l.length + 1
    split <;> omega

/-- The lookup depends on those cells only. -/
theorem assoc_take {A B : Type} [DecidableEq A] (p : A) :
    ∀ l : List (A × B), assoc p (l.take (assocCells p l)) = assoc p l
  | [] => rfl
  | (k, v) :: l => by
    by_cases h : k = p
    · have e : assocCells p ((k, v) :: l) = 1 := ite_pos' h
      rw [e]
      show (if k = p then some v else assoc p []) = (if k = p then some v else assoc p l)
      rw [ite_pos' h, ite_pos' h]
    · have e : assocCells p ((k, v) :: l) = assocCells p l + 1 := ite_neg' h
      rw [e]
      show (if k = p then some v else assoc p (l.take (assocCells p l))) =
        (if k = p then some v else assoc p l)
      rw [ite_neg' h, ite_neg' h]
      exact assoc_take p l

/-- The cells that the search for the next segment reads. -/
def nextSegCells : List (Port × Port) → Port → Port → Nat
  | [], _, _ => 0
  | e :: ws, c, p => if e.1 = c ∧ e.2 ≠ p then 1 else nextSegCells ws c p + 1

theorem nextSegCells_le : ∀ (ws : List (Port × Port)) (c p : Port),
    nextSegCells ws c p ≤ ws.length
  | [], _, _ => Nat.le_refl 0
  | e :: ws, c, p => by
    have ih := nextSegCells_le ws c p
    show (if e.1 = c ∧ e.2 ≠ p then 1 else nextSegCells ws c p + 1) ≤ ws.length + 1
    split <;> omega

/-- The search depends on those cells only. -/
theorem nextSeg_take : ∀ (ws : List (Port × Port)) (c p : Port),
    nextSeg (ws.take (nextSegCells ws c p)) c p = nextSeg ws c p
  | [], _, _ => rfl
  | e :: ws, c, p => by
    by_cases h : e.1 = c ∧ e.2 ≠ p
    · have e' : nextSegCells (e :: ws) c p = 1 := ite_pos' h
      rw [e']
      show (if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg [] c p) =
        (if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg ws c p)
      rw [ite_pos' h, ite_pos' h]
    · have e' : nextSegCells (e :: ws) c p = nextSegCells ws c p + 1 := ite_neg' h
      rw [e']
      show (if e.1 = c ∧ e.2 ≠ p then some e.2
          else nextSeg (ws.take (nextSegCells ws c p)) c p) =
        (if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg ws c p)
      rw [ite_neg' h, ite_neg' h]
      exact nextSeg_take ws c p

/-- **What an action costs**: one for the action, one for each cell of the
memory that its lookups read, the whole list of agents when it takes an
agent out or takes the list afresh, and one for each cell of a right-hand
side it builds.  A thread at rest costs nothing. -/
def XMach.cost (xs : XSys S) (X : XNet S) (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo with
    | [] => 0
    | e :: _ => 1 + assocCells e.1 X.agents
  | .look a _ => 1 + assocCells (a, 0) X.wires
  | .seek _ _ p c =>
    if c.2 = 0 then
      1 + assocCells c.1 X.agents +
        if (assoc c.1 X.agents).isSome then 0 else nextSegCells X.wires c p
    else 1 + nextSegCells X.wires c p
  | .ready a _ α _ =>
    1 + assocCells a X.agents + if assoc a X.agents = some α then X.agents.length else 0
  | .half a b α β =>
    1 + assocCells b X.agents +
      if assoc b X.agents = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          X.agents.length + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 0
      else 0
  | .write (_ :: _) _ => 1
  | .write [] (_ :: _) => 1
  | .write [] [] => 1 + X.agents.length

/-- An action costs at most twice the agents in memory, the segments, and
the size of a rule. -/
theorem XMach.cost_le {C D : Nat} (hb : xs.Bounded C D) (X : XNet S) (T : XThread S) :
    XMach.cost xs X T ≤ 2 * X.agents.length + X.wires.length + C + D + 1 := by
  have hA : ∀ i, assocCells i X.agents ≤ X.agents.length := fun i => assocCells_le i X.agents
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.zero_le _
    | cons e rest =>
      have h := hA e.1
      show 1 + assocCells e.1 X.agents ≤ _
      omega
  | look a α =>
    have h := assocCells_le (a, 0) X.wires
    show 1 + assocCells (a, 0) X.wires ≤ _
    omega
  | seek a α p c =>
    have h₁ := hA c.1
    have h₂ := nextSegCells_le X.wires c p
    show (if c.2 = 0 then 1 + assocCells c.1 X.agents +
        (if (assoc c.1 X.agents).isSome then 0 else nextSegCells X.wires c p)
      else 1 + nextSegCells X.wires c p) ≤ _
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    have h := hA a
    show 1 + assocCells a X.agents +
      (if assoc a X.agents = some α then X.agents.length else 0) ≤ _
    split <;> omega
  | half a b α β =>
    have h := hA b
    unfold XMach.cost
    dsimp only
    split
    · split
      · rename_i R hR
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        show 1 + assocCells b X.agents + (X.agents.length + (R.newAgents a b).length +
          (R.newLinks xs.sys.ar a b α β).length) ≤ _
        omega
      · omega
    · omega
  | write as ls =>
    cases as with
    | cons e as => exact Nat.le_add_left 1 _
    | nil =>
      cases ls with
      | cons e ls => exact Nat.le_add_left 1 _
      | nil =>
        show 1 + X.agents.length ≤ _
        omega

/-- What the action of thread `t` costs. -/
def XMach.stepCost (xs : XSys S) (M : XMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => XMach.cost xs M.mem T
  | none => 0

theorem XMach.stepCost_le {C D : Nat} (hb : xs.Bounded C D) (M : XMach S) (t : Nat) :
    M.stepCost xs t ≤ 2 * M.mem.agents.length + M.mem.wires.length + C + D + 1 := by
  unfold XMach.stepCost
  split
  · exact XMach.cost_le hb _ _
  · exact Nat.zero_le _

/-- At rest, actions cost nothing. -/
theorem XMach.stepCost_rest {M : XMach S} (h : M.resting = true) (t : Nat) :
    M.stepCost xs t = 0 := by
  unfold XMach.stepCost
  split
  · rename_i T hT
    rw [XThread.eq_rest (List.all_eq_true.1 h T (List.mem_of_getElem? hT))]
    rfl
  · rfl

/-- **The running time** of the first `i` actions of a run: what they cost,
added up. -/
def XMach.time (xs : XSys S) (σ : Nat → Nat) (M : XMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => XMach.time xs σ M i + (M.trace xs σ i).1.stepCost xs (σ i)

/-- Once the program is at rest its running time stays what it is. -/
theorem XMach.time_rest {M : XMach S} (σ : Nat → Nat) {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) : ∀ d, M.time xs σ (B + d) = M.time xs σ B
  | 0 => rfl
  | d + 1 => by
    show M.time xs σ (B + d) + (M.trace xs σ (B + d)).1.stepCost xs (σ (B + d)) = _
    rw [XMach.stepCost_rest (XMach.resting_trace σ h d), Nat.add_zero]
    exact XMach.time_rest σ h d

theorem assocCells_none {A B : Type} [DecidableEq A] (p : A) :
    ∀ l : List (A × B), assoc p l = none → assocCells p l = l.length
  | [], _ => rfl
  | (k, v) :: l, h => by
    by_cases hk : k = p
    · have h' : (if k = p then some v else assoc p l) = none := h
      rw [ite_pos' hk] at h'
      cases h'
    · have h' : (if k = p then some v else assoc p l) = none := h
      rw [ite_neg' hk] at h'
      show (if k = p then 1 else assocCells p l + 1) = l.length + 1
      rw [ite_neg' hk, assocCells_none p l h']

theorem nextSegCells_none : ∀ (ws : List (Port × Port)) (c p : Port),
    nextSeg ws c p = none → nextSegCells ws c p = ws.length
  | [], _, _, _ => rfl
  | e :: ws, c, p, h => by
    by_cases hk : e.1 = c ∧ e.2 ≠ p
    · have h' : (if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg ws c p) = none := h
      rw [ite_pos' hk] at h'
      cases h'
    · have h' : (if e.1 = c ∧ e.2 ≠ p then some e.2 else nextSeg ws c p) = none := h
      rw [ite_neg' hk] at h'
      show (if e.1 = c ∧ e.2 ≠ p then 1 else nextSegCells ws c p + 1) = ws.length + 1
      rw [ite_neg' hk, nextSegCells_none ws c p h']

/-- What the threads together still have to do before the next claim,
measured in `H`: their shares, added up. -/
noncomputable def XMach.energyIn (M : XMach S) (H : Net S) (K A : Nat) : Nat :=
  total (potIn H K A) M.ths

omit [DecidableEq S] in
/-- Before the program starts every thread has one pass over the agents to
make. -/
theorem XMach.init_energyIn (X : XNet S) (nt : Nat) (H : Net S) (K A : Nat) :
    (XMach.init X nt).energyIn H K A ≤ nt * H.scan K X.agents := by
  have h : total (potIn H K A) (XMach.init X nt).ths ≤
      (XMach.init X nt).ths.length * H.scan K X.agents :=
    total_le_mul fun T hT => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
      show H.scan K (X.agents.drop t ++ X.agents.take t) ≤ _
      have e : H.scan K X.agents =
          H.scan K (X.agents.take t) + H.scan K (X.agents.drop t) := by
        rw [← Net.scan_append, List.take_append_drop]
      rw [Net.scan_append]
      omega
  have hl : (XMach.init X nt).ths.length = nt := by
    show ((List.range nt).map _).length = nt
    rw [List.length_map, List.length_range]
  rw [hl] at h
  exact h

/-- **Every action is free and changes nothing, or is a claim, or brings
the shares down**, added up over the threads and measured in a net that
lies ahead of the goal.  A claim raises the sum by at most the writes of
one rule and one pass over the agents. -/
theorem XMach.step_work {M : XMach S} (hL : M.Live xs)
    (hnd : (M.mem.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D)
    {H : Net S} {K A : Nat} (hH : H.Sized K) (hM : M.Ahead H) (hA : M.heads ≤ A) (t : Nat) :
    (M.step xs t = (M, 0) ∧ M.stepCost xs t = 0) ∨
      ((M.step xs t).2 = 1 ∧
        (M.step xs t).1.energyIn H K A ≤ M.energyIn H K A + (C + D + 7 * A + K)) ∨
      ((M.step xs t).2 = 0 ∧ (M.step xs t).1.energyIn H K A < M.energyIn H K A) := by
  cases ht : M.ths[t]? with
  | none =>
    refine .inl ⟨?_, ?_⟩
    · unfold XMach.step
      rw [ht]
    · unfold XMach.stepCost
      rw [ht]
  | some T =>
    have es : M.step xs t = (⟨(XMach.act xs M.mem T).1,
        M.ths.set t (XMach.act xs M.mem T).2.1⟩, (XMach.act xs M.mem T).2.2) :=
      XMach.step_eq ht rfl
    have ts := total_set (potIn H K A) M.ths t T (XMach.act xs M.mem T).2.1 ht
    rcases XMach.act_pot hL hnd hb hH hM hA ht with ⟨e, rfl⟩ | ⟨h1, hle⟩ | ⟨h0, hlt⟩
    · refine .inl ⟨?_, ?_⟩
      · rw [XMach.step_eq ht e, set_self M.ths t _ ht]
      · unfold XMach.stepCost
        rw [ht]
        rfl
    · rw [es]
      refine .inr (.inl ⟨h1, ?_⟩)
      show total (potIn H K A) (M.ths.set t (XMach.act xs M.mem T).2.1) ≤
        total (potIn H K A) M.ths + (C + D + 7 * A + K)
      omega
    · rw [es]
      refine .inr (.inr ⟨h0, ?_⟩)
      show total (potIn H K A) (M.ths.set t (XMach.act xs M.mem T).2.1) <
        total (potIn H K A) M.ths
      omega

/-- A cost that is paid only when a measure goes down adds up to at most
the measure at the start, times the largest payment. -/
theorem paid_le (τ Φ : Nat → Nat) (c : Nat)
    (h : ∀ i, (τ (i + 1) = τ i ∧ Φ (i + 1) = Φ i) ∨ (τ (i + 1) ≤ τ i + c ∧ Φ (i + 1) < Φ i)) :
    ∀ i, τ i + c * Φ i ≤ τ 0 + c * Φ 0
  | 0 => Nat.le_refl _
  | i + 1 => by
    have ih := paid_le τ Φ c h i
    rcases h i with ⟨e₁, e₂⟩ | ⟨h₁, h₂⟩
    · rw [e₁, e₂]
      exact ih
    · have h₃ := Nat.mul_le_mul_left c (Nat.succ_le_of_lt h₂)
      rw [Nat.mul_succ] at h₃
      omega

/-- **A bound on the running time, whatever the schedule.**  Take a
well-formed net in which no agent is listed twice, with a normal form `n`
steps away, rules that write at most `C` agents and `D` segments, and `nt`
threads, at least one.  However the threads are scheduled, fairly or not,
the run never takes more time than

    (nt + n) * X.passBound n C D + n * (C + D + 1)

actions that are not rests, one pass for each thread, one more for each
claim, and the writes, times

    2 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + C + D + 1

the most an action can cost in a memory that never holds more than the
agents of the net and `C - 2` more for each of the `n` claims.  A window stretches the run, not the work. -/
theorem XMach.time_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (XMach.init X nt).time xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) *
        (2 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + C + D + 1) := by
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
  have hA : ∀ i, ((XMach.init X nt).trace xs σ i).1.heads ≤ X.agents.length + (C - 2) * n :=
    fun i => Nat.le_trans (sizes i).2
      (Nat.add_le_add_left (Nat.mul_le_mul_left (C - 2) (bound i)) _)
  have hK : ∀ i, ((XMach.init X nt).trace xs σ i).1.segs ≤ X.wires.length + D * n :=
    fun i => Nat.le_trans (sizes i).1
      (Nat.add_le_add_left (Nat.mul_le_mul_left D (bound i)) _)
  have nd : ∀ i, (((XMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact XMach.step_nodup (live i) ih (σ i)
  have hH := XNet.normal_sized hX hb hs hn
  have ahead : ∀ i, ((XMach.init X nt).trace xs σ i).1.Ahead N' :=
    fun i => XMach.ahead_of_run (live i).inv hX (run i) hs hn
  have hc : ∀ i, ((XMach.init X nt).trace xs σ i).1.stepCost xs (σ i) ≤
      2 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + C + D + 1 := by
    intro i
    have h := XMach.stepCost_le hb ((XMach.init X nt).trace xs σ i).1 (σ i)
    have a₁ : ((XMach.init X nt).trace xs σ i).1.mem.agents.length ≤
        ((XMach.init X nt).trace xs σ i).1.heads := Nat.le_add_right _ _
    have a₂ : ((XMach.init X nt).trace xs σ i).1.mem.wires.length ≤
        ((XMach.init X nt).trace xs σ i).1.segs := Nat.le_add_right _ _
    have := hA i
    have := hK i
    omega
  have key := paid_le (fun i => (XMach.init X nt).time xs σ i)
    (fun i => ((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
        (X.agents.length + (C - 2) * n) +
      (n - ((XMach.init X nt).trace xs σ i).2) *
        (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1))
    (2 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + C + D + 1) (fun i => by
      have hb1 : ((XMach.init X nt).trace xs σ i).2 +
          (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2 ≤ n := bound (i + 1)
      show ((XMach.init X nt).time xs σ i +
            ((XMach.init X nt).trace xs σ i).1.stepCost xs (σ i) =
              (XMach.init X nt).time xs σ i ∧
          (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.energyIn N'
              (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
            (n - (((XMach.init X nt).trace xs σ i).2 +
              (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) *
              (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) =
            ((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
              (X.agents.length + (C - 2) * n) +
            (n - ((XMach.init X nt).trace xs σ i).2) *
              (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1)) ∨
        ((XMach.init X nt).time xs σ i +
            ((XMach.init X nt).trace xs σ i).1.stepCost xs (σ i) ≤
              (XMach.init X nt).time xs σ i +
                (2 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + C + D + 1) ∧
          (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.energyIn N'
              (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
            (n - (((XMach.init X nt).trace xs σ i).2 +
              (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) *
              (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) <
            ((XMach.init X nt).trace xs σ i).1.energyIn N' (X.wires.length + D * n)
              (X.agents.length + (C - 2) * n) +
            (n - ((XMach.init X nt).trace xs σ i).2) *
              (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1))
      rcases XMach.step_work (live i) (nd i) hb hH (ahead i) (hA i) (σ i) with
        ⟨e, hz⟩ | ⟨h1, hce⟩ | ⟨h0, hlt⟩
      · refine .inl ⟨by rw [hz]; rfl, ?_⟩
        rw [e]
        rfl
      · refine .inr ⟨Nat.add_le_add_left (hc i) _, ?_⟩
        have e1 : n - ((XMach.init X nt).trace xs σ i).2 =
            (n - (((XMach.init X nt).trace xs σ i).2 +
              (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).2)) + 1 := by omega
        rw [e1, Nat.add_mul, Nat.one_mul]
        omega
      · refine .inr ⟨Nat.add_le_add_left (hc i) _, ?_⟩
        rw [h0]
        exact Nat.add_lt_add_right hlt _)
  intro i
  have k := key i
  have e0 := XMach.init_energyIn X nt N' (X.wires.length + D * n) (X.agents.length + (C - 2) * n)
  obtain ⟨-, pr⟩ := Steps.links hX hs
  have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
  have hscan : N'.scan (X.wires.length + D * n) X.agents ≤
      7 * X.agents.length + (X.wires.length + D * n) :=
    Net.scan_le hH X.agents hnd fun e he q q' h h' =>
      hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
        (pr (.inl ⟨e.2, hag e he⟩) h')
  have hsc : nt * N'.scan (X.wires.length + D * n) X.agents ≤ nt * X.passBound n C D :=
    Nat.mul_le_mul_left nt (Nat.le_trans hscan (by
      show 7 * X.agents.length + (X.wires.length + D * n) ≤
        7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)
      omega))
  have e1 : C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1 =
      X.passBound n C D + (C + D + 1) := by
    show _ = 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + (C + D + 1)
    omega
  have hΦ : (XMach.init X nt).energyIn N' (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
      (n - 0) * (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1) ≤
      (nt + n) * X.passBound n C D + n * (C + D + 1) := by
    rw [Nat.sub_zero, e1, Nat.mul_add n (X.passBound n C D) (C + D + 1),
      Nat.add_mul nt n (X.passBound n C D)]
    omega
  have h₂ := Nat.mul_le_mul_left
    (2 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + C + D + 1) hΦ
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  have k' : (XMach.init X nt).time xs σ i ≤
      0 + (2 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + C + D + 1) *
        ((XMach.init X nt).energyIn N' (X.wires.length + D * n) (X.agents.length + (C - 2) * n) +
          (n - 0) *
            (C + D + 7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) + 1)) :=
    Nat.le_trans (Nat.le_add_right _ _) k
  rw [Nat.zero_add] at k'
  exact Nat.le_trans k' h₂

/-- What the next `j` actions of a thread cost, as long as the memory stays
as it is. -/
def XThread.spent (xs : XSys S) (X : XNet S) : XThread S → Nat → Nat
  | _, 0 => 0
  | T, j + 1 => XMach.cost xs X T + XThread.spent xs X (XMach.act xs X T).2.1 j

theorem XThread.spent_add (xs : XSys S) (X : XNet S) : ∀ (a b : Nat) (T : XThread S),
    T.spent xs X (a + b) = T.spent xs X a + (T.after xs X a).spent xs X b
  | 0, b, T => by
    rw [Nat.zero_add]
    show _ = 0 + _
    rw [Nat.zero_add]
    rfl
  | a + 1, b, T => by
    have ih := XThread.spent_add xs X a b (XMach.act xs X T).2.1
    have e : a + 1 + b = a + b + 1 := by omega
    rw [e]
    show XMach.cost xs X T + XThread.spent xs X (XMach.act xs X T).2.1 (a + b) =
      XMach.cost xs X T + XThread.spent xs X (XMach.act xs X T).2.1 a +
        (XThread.after xs X (XMach.act xs X T).2.1 a).spent xs X b
    rw [ih]
    omega

theorem XThread.spent_succ (xs : XSys S) (X : XNet S) (j : Nat) (T : XThread S) :
    T.spent xs X (j + 1) = T.spent xs X j + XMach.cost xs X (T.after xs X j) := by
  rw [XThread.spent_add xs X j 1 T]
  show _ = _ + (XMach.cost xs X (T.after xs X j) + 0)
  rfl

theorem XThread.spent_mono (xs : XSys S) (X : XNet S) (T : XThread S) {a b : Nat}
    (h : a ≤ b) : T.spent xs X a ≤ T.spent xs X b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  rw [XThread.spent_add]
  exact Nat.le_add_right _ _

/-- An agent that leads to a principal port which is not that of an agent in
memory costs three actions and one look at every cell of the memory: the
last of the three reads every agent and every segment, to no avail. -/
theorem XThread.spent_inert {X : XNet S} {e : Id × S} (rest : List (Id × S)) (h : X.Inert e)
    (hq : ∀ q, assoc (e.1, 0) X.wires = some q → q.2 = 0) :
    3 + X.agents.length + X.wires.length ≤
        (⟨e :: rest, .idle⟩ : XThread S).spent xs X 3 ∧
      (⟨e :: rest, .idle⟩ : XThread S).after xs X 3 = ⟨rest, .idle⟩ := by
  obtain ⟨h₁, q, h₂, h₃, h₄⟩ := h
  have hq0 := hq q h₂
  rw [ite_pos' hq0] at h₃
  have a₁ : XMach.act xs X ⟨e :: rest, .idle⟩ = (X, ⟨rest, .look e.1 e.2⟩, 0) :=
    XMach.act_idle_pos h₁
  have a₂ : XMach.act xs X ⟨rest, .look e.1 e.2⟩ =
      (X, ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩, 0) := XMach.act_look h₂
  have a₃ : XMach.act xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩ = (X, ⟨rest, .idle⟩, 0) :=
    XMach.act_seek_stop (by rw [ite_pos' hq0]; exact h₃) h₄
  have c₃ : XMach.cost xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩ =
      1 + X.agents.length + X.wires.length := by
    show (if q.2 = 0 then 1 + assocCells q.1 X.agents +
        (if (assoc q.1 X.agents).isSome then 0 else nextSegCells X.wires q (e.1, 0))
      else 1 + nextSegCells X.wires q (e.1, 0)) = _
    rw [ite_pos' hq0, assocCells_none _ _ h₃, h₃, nextSegCells_none _ _ _ h₄]
    rfl
  constructor
  · show 3 + X.agents.length + X.wires.length ≤
      XMach.cost xs X ⟨e :: rest, .idle⟩ +
        (XMach.cost xs X (XMach.act xs X ⟨e :: rest, .idle⟩).2.1 +
          (XMach.cost xs X (XMach.act xs X (XMach.act xs X ⟨e :: rest, .idle⟩).2.1).2.1 + 0))
    rw [a₁]
    show _ ≤ XMach.cost xs X ⟨e :: rest, .idle⟩ + (XMach.cost xs X ⟨rest, .look e.1 e.2⟩ +
      (XMach.cost xs X (XMach.act xs X ⟨rest, .look e.1 e.2⟩).2.1 + 0))
    rw [a₂]
    show _ ≤ XMach.cost xs X ⟨e :: rest, .idle⟩ + (XMach.cost xs X ⟨rest, .look e.1 e.2⟩ +
      (XMach.cost xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩ + 0))
    rw [c₃]
    have u₁ : 1 ≤ XMach.cost xs X ⟨e :: rest, .idle⟩ := Nat.le_add_right 1 _
    have u₂ : 1 ≤ XMach.cost xs X ⟨rest, .look e.1 e.2⟩ := Nat.le_add_right 1 _
    omega
  · show XThread.after xs X (XMach.act xs X (XMach.act xs X
      (XMach.act xs X ⟨e :: rest, .idle⟩).2.1).2.1).2.1 0 = _
    rw [a₁]
    show XThread.after xs X (XMach.act xs X (XMach.act xs X ⟨rest, .look e.1 e.2⟩).2.1).2.1 0 = _
    rw [a₂]
    show XThread.after xs X (XMach.act xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩).2.1 0 = _
    rw [a₃]
    rfl

/-- A pass over such agents costs as much for each of them. -/
theorem XThread.spent_inert_pass {X : XNet S} (rest : List (Id × S)) :
    ∀ (l : List (Id × S)), (∀ e, e ∈ l → X.Inert e ∧
        ∀ q, assoc (e.1, 0) X.wires = some q → q.2 = 0) →
      l.length * (3 + X.agents.length + X.wires.length) ≤
        (⟨l ++ rest, .idle⟩ : XThread S).spent xs X (3 * l.length)
  | [], _ => Nat.le_of_eq (Nat.zero_mul _)
  | e :: l, h => by
    obtain ⟨c, a⟩ := XThread.spent_inert (xs := xs) (l ++ rest) (h e List.mem_cons_self).1
      (h e List.mem_cons_self).2
    have ih := XThread.spent_inert_pass rest l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have e1 : 3 * (e :: l).length = 3 + 3 * l.length := by
      show 3 * (l.length + 1) = _
      omega
    have e2 : (e :: l).length * (3 + X.agents.length + X.wires.length) =
        l.length * (3 + X.agents.length + X.wires.length) +
          (3 + X.agents.length + X.wires.length) := Nat.succ_mul _ _
    rw [e1, e2]
    show _ ≤ (⟨e :: (l ++ rest), .idle⟩ : XThread S).spent xs X (3 + 3 * l.length)
    rw [XThread.spent_add, a]
    omega

/-- The sum of the first `m` values of a function. -/
def sumTo (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumTo g m + g m

theorem sumTo_bump {g g' : Nat → Nat} {s d : Nat} (h : ∀ t, t ≠ s → g' t = g t)
    (hs : g' s = g s + d) : ∀ m, sumTo g' m = sumTo g m + if s < m then d else 0
  | 0 => rfl
  | m + 1 => by
    have ih := sumTo_bump h hs m
    show sumTo g' m + g' m = sumTo g m + g m + if s < m + 1 then d else 0
    by_cases hm : m = s
    · subst hm
      rw [ih, hs, ite_neg' (Nat.lt_irrefl m), ite_pos' (Nat.lt_succ_self m)]
      omega
    · rw [ih, h m hm]
      by_cases hlt : s < m
      · rw [ite_pos' hlt, ite_pos' (Nat.lt_succ_of_lt hlt)]
        omega
      · rw [ite_neg' hlt, ite_neg' (by omega)]
        omega

theorem sumTo_ge {g : Nat → Nat} {L : Nat} : ∀ m, (∀ t, t < m → L ≤ g t) → m * L ≤ sumTo g m
  | 0, _ => Nat.le_of_eq (Nat.zero_mul _)
  | m + 1, h => by
    have ih := sumTo_ge m fun t ht => h t (Nat.lt_succ_of_lt ht)
    have hm := h m (Nat.lt_succ_self m)
    show (m + 1) * L ≤ sumTo g m + g m
    rw [Nat.succ_mul]
    omega

/-- What thread `t` has spent after `h` actions of its own, the memory
staying as it is. -/
def XMach.spentAt (xs : XSys S) (M : XMach S) (t h : Nat) : Nat :=
  match M.ths[t]? with
  | some T => T.spent xs M.mem h
  | none => 0

/-- **The time of threads that only read** is what each has spent on its
own, added up, whatever the schedule. -/
theorem XMach.time_reads {M : XMach S} (σ : Nat → Nat)
    (hR : ∀ T, T ∈ M.ths → T.Reads xs M.mem) :
    ∀ i, M.time xs σ i = sumTo (fun t => M.spentAt xs t (hits σ t i)) M.ths.length
  | 0 => by
    have z : ∀ m, sumTo (fun t => M.spentAt xs t (hits σ t 0)) m = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        show sumTo (fun t => M.spentAt xs t (hits σ t 0)) m + M.spentAt xs m 0 = 0
        rw [ih]
        unfold XMach.spentAt
        split <;> rfl
    rw [z]
    rfl
  | i + 1 => by
    obtain ⟨hm, hl, ht⟩ := XMach.trace_reads (xs := xs) σ hR i
    have ih := XMach.time_reads σ hR i
    have hd : M.spentAt xs (σ i) (hits σ (σ i) (i + 1)) =
        M.spentAt xs (σ i) (hits σ (σ i) i) + (M.trace xs σ i).1.stepCost xs (σ i) ∧
        (¬ σ i < M.ths.length → (M.trace xs σ i).1.stepCost xs (σ i) = 0) := by
      cases hs : M.ths[σ i]? with
      | none =>
        have hn : (M.trace xs σ i).1.ths[σ i]? = none := by
          rw [List.getElem?_eq_none_iff] at hs ⊢
          rw [hl]
          exact hs
        have z : (M.trace xs σ i).1.stepCost xs (σ i) = 0 := by
          unfold XMach.stepCost
          rw [hn]
        refine ⟨?_, fun _ => z⟩
        rw [z]
        unfold XMach.spentAt
        rw [hs]
      | some T =>
        have hU := ht (σ i) T hs
        have c : (M.trace xs σ i).1.stepCost xs (σ i) =
            XMach.cost xs M.mem (T.after xs M.mem (hits σ (σ i) i)) := by
          unfold XMach.stepCost
          rw [hU, hm]
        refine ⟨?_, fun h => absurd (List.getElem?_eq_some_iff.1 hs).1 h⟩
        rw [c]
        unfold XMach.spentAt
        rw [hs]
        show T.spent xs M.mem (hits σ (σ i) i + if σ i = σ i then 1 else 0) = _
        rw [ite_pos' rfl, XThread.spent_succ]
    have hb := sumTo_bump (g := fun t => M.spentAt xs t (hits σ t i))
      (g' := fun t => M.spentAt xs t (hits σ t (i + 1))) (s := σ i)
      (d := (M.trace xs σ i).1.stepCost xs (σ i))
      (fun t hne => by
        show M.spentAt xs t (hits σ t i + if σ i = t then 1 else 0) = _
        rw [ite_neg' (Ne.symm hne)]
        rfl)
      hd.1 M.ths.length
    show M.time xs σ i + (M.trace xs σ i).1.stepCost xs (σ i) = _
    rw [hb, ih]
    by_cases hlt : σ i < M.ths.length
    · rw [ite_pos' hlt]
    · rw [ite_neg' hlt, hd.2 hlt]

/-- **By the time readers are at rest each has paid for its own pass.**  If
no thread writes, and each has spent `L` or more before it can be at rest,
then the program has taken `L` for each thread, or more, when it is at
rest. -/
theorem XMach.time_ge_rest {M : XMach S} (σ : Nat → Nat)
    (hR : ∀ T, T ∈ M.ths → T.Reads xs M.mem) {L : Nat}
    (hL : ∀ T, T ∈ M.ths → ∃ j, (∀ j', j' < j → T.after xs M.mem j' ≠ ⟨[], .idle⟩) ∧
      L ≤ T.spent xs M.mem j) :
    ∀ i, (M.trace xs σ i).1.resting = true → M.ths.length * L ≤ M.time xs σ i := by
  intro i hr
  obtain ⟨-, -, ht⟩ := XMach.trace_reads (xs := xs) σ hR i
  rw [XMach.time_reads σ hR i]
  refine sumTo_ge _ fun t hlt => ?_
  have hT : M.ths[t]? = some M.ths[t] := List.getElem?_eq_getElem hlt
  obtain ⟨j, lo, hj⟩ := hL _ (List.mem_of_getElem? hT)
  have hrest : (M.ths[t]).after xs M.mem (hits σ t i) = ⟨[], .idle⟩ :=
    XThread.eq_rest (List.all_eq_true.1 hr _ (List.mem_of_getElem? (ht t _ hT)))
  have hge : j ≤ hits σ t i := by
    rcases Nat.lt_or_ge (hits σ t i) j with h | h
    · exact absurd hrest (lo _ h)
    · exact h
  show L ≤ M.spentAt xs t (hits σ t i)
  unfold XMach.spentAt
  rw [hT]
  exact Nat.le_trans hj (XThread.spent_mono xs M.mem _ hge)

/-- What the first `j` actions of a thread running alone cost. -/
def XMach.soloTime (xs : XSys S) : XNet S → XThread S → Nat → Nat
  | _, _, 0 => 0
  | X, T, j + 1 =>
    XMach.cost xs X T + XMach.soloTime xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 j

theorem XMach.soloTime_add (xs : XSys S) : ∀ (a b : Nat) (X : XNet S) (T : XThread S),
    XMach.soloTime xs X T (a + b) = XMach.soloTime xs X T a +
      XMach.soloTime xs (XMach.solo xs X T a).1 (XMach.solo xs X T a).2 b
  | 0, b, X, T => by
    rw [Nat.zero_add]
    show _ = 0 + _
    rw [Nat.zero_add]
    rfl
  | a + 1, b, X, T => by
    have ih := XMach.soloTime_add xs a b (XMach.act xs X T).1 (XMach.act xs X T).2.1
    have e : a + 1 + b = a + b + 1 := by omega
    rw [e]
    show XMach.cost xs X T +
        XMach.soloTime xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 (a + b) =
      XMach.cost xs X T + XMach.soloTime xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 a +
        XMach.soloTime xs
          (XMach.solo xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 a).1
          (XMach.solo xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 a).2 b
    rw [ih]
    omega

theorem XMach.soloTime_succ (xs : XSys S) (j : Nat) (X : XNet S) (T : XThread S) :
    XMach.soloTime xs X T (j + 1) = XMach.soloTime xs X T j +
      XMach.cost xs (XMach.solo xs X T j).1 (XMach.solo xs X T j).2 := by
  rw [XMach.soloTime_add xs j 1 X T]
  show _ = _ + (XMach.cost xs (XMach.solo xs X T j).1 (XMach.solo xs X T j).2 + 0)
  rfl

theorem XMach.soloTime_mono (xs : XSys S) (X : XNet S) (T : XThread S) {a b : Nat}
    (h : a ≤ b) : XMach.soloTime xs X T a ≤ XMach.soloTime xs X T b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  rw [XMach.soloTime_add]
  exact Nat.le_add_right _ _

/-- The time of a counted run in two parts: what each part takes at
least. -/
theorem Works.soloTime_ge {X X' : XNet S} {T T' : XThread S} {c k : Nat}
    (w : Works xs X T X' T' c k) {a b j : Nat} (ha : a ≤ XMach.soloTime xs X T k)
    (hb : b ≤ XMach.soloTime xs X' T' j) : a + b ≤ XMach.soloTime xs X T (k + j) := by
  rw [XMach.soloTime_add xs k j X T, w.solo.1]
  exact Nat.add_le_add ha hb

/-- While a thread only reads, its time is what it spends. -/
theorem Stays.soloTime {X : XNet S} {T T' : XThread S} {k : Nat} (st : Stays xs X T T' k) :
    XMach.soloTime xs X T k = T.spent xs X k := by
  induction st with
  | refl T => rfl
  | @step T T₁ T' k hT h _ ih =>
    show XMach.cost xs X T +
        XMach.soloTime xs (XMach.act xs X T).1 (XMach.act xs X T).2.1 k =
      XMach.cost xs X T + XThread.spent xs X (XMach.act xs X T).2.1 k
    rw [h]
    show XMach.cost xs X T + XMach.soloTime xs X T₁ k =
      XMach.cost xs X T + XThread.spent xs X T₁ k
    rw [ih]

/-- **The time of one thread at work, the others at rest**, is the time of
its own actions, whatever the schedule. -/
theorem XMach.time_lone {M : XMach S} {T₀ : XThread S} {u : Nat} (σ : Nat → Nat)
    (h0 : M.ths[u]? = some T₀)
    (hrest : ∀ (t : Nat) (T : XThread S), t ≠ u → M.ths[t]? = some T → T = ⟨[], .idle⟩) :
    ∀ i, M.time xs σ i = XMach.soloTime xs M.mem T₀ (hits σ u i)
  | 0 => rfl
  | i + 1 => by
    obtain ⟨hm, ht⟩ := XMach.trace_lone (xs := xs) σ h0 hrest i
    have ih := XMach.time_lone σ h0 hrest i
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h0
    show M.time xs σ i + (M.trace xs σ i).1.stepCost xs (σ i) =
      XMach.soloTime xs M.mem T₀ (hits σ u i + if σ i = u then 1 else 0)
    rw [ih]
    by_cases hs : σ i = u
    · have hU : (M.trace xs σ i).1.ths[σ i]? =
          some (XMach.solo xs M.mem T₀ (hits σ u i)).2 := by
        rw [hs, ht]
        exact List.getElem?_set_self hlt
      have c : (M.trace xs σ i).1.stepCost xs (σ i) =
          XMach.cost xs (XMach.solo xs M.mem T₀ (hits σ u i)).1
            (XMach.solo xs M.mem T₀ (hits σ u i)).2 := by
        unfold XMach.stepCost
        rw [hU, hm]
      rw [ite_pos' hs, XMach.soloTime_succ, c]
    · have z : (M.trace xs σ i).1.stepCost xs (σ i) = 0 := by
        unfold XMach.stepCost
        cases hU : (M.trace xs σ i).1.ths[σ i]? with
        | none => rfl
        | some U =>
          have hU' : M.ths[σ i]? = some U := by
            rw [ht, List.getElem?_set_ne (Ne.symm hs)] at hU
            exact hU
          rw [hrest (σ i) U hs hU']
          rfl
      rw [ite_neg' hs, z]
      rfl

/-- A thread scheduled at every action has had them all. -/
theorem hits_const (t : Nat) : ∀ i, hits (fun _ => t) t i = i
  | 0 => rfl
  | i + 1 => by
    show hits (fun _ => t) t i + (if t = t then 1 else 0) = i + 1
    rw [hits_const t i, ite_pos' rfl]

/-- An agent that leads nowhere costs three actions and a look at every
segment, at least. -/
theorem XThread.spent_stuck {X : XNet S} {e : Id × S} (rest : List (Id × S))
    (h : X.Inert e) :
    3 + X.wires.length ≤ (⟨e :: rest, .idle⟩ : XThread S).spent xs X 3 ∧
      (⟨e :: rest, .idle⟩ : XThread S).after xs X 3 = ⟨rest, .idle⟩ := by
  have ha := (Stays.inert (xs := xs) rest h).after_eq.1
  obtain ⟨h₁, q, h₂, h₃, h₄⟩ := h
  have a₁ : XMach.act xs X ⟨e :: rest, .idle⟩ = (X, ⟨rest, .look e.1 e.2⟩, 0) :=
    XMach.act_idle_pos h₁
  have a₂ : XMach.act xs X ⟨rest, .look e.1 e.2⟩ =
      (X, ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩, 0) := XMach.act_look h₂
  have c₃ : 1 + X.wires.length ≤ XMach.cost xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩ := by
    show 1 + X.wires.length ≤ (if q.2 = 0 then 1 + assocCells q.1 X.agents +
        (if (assoc q.1 X.agents).isSome then 0 else nextSegCells X.wires q (e.1, 0))
      else 1 + nextSegCells X.wires q (e.1, 0))
    rw [nextSegCells_none _ _ _ h₄]
    by_cases hq0 : q.2 = 0
    · rw [ite_pos' hq0] at h₃
      rw [ite_pos' hq0, h₃]
      show 1 + X.wires.length ≤ 1 + assocCells q.1 X.agents + X.wires.length
      omega
    · rw [ite_neg' hq0]
      exact Nat.le_refl _
  refine ⟨?_, ha⟩
  show 3 + X.wires.length ≤
    XMach.cost xs X ⟨e :: rest, .idle⟩ +
      (XMach.cost xs X (XMach.act xs X ⟨e :: rest, .idle⟩).2.1 +
        (XMach.cost xs X (XMach.act xs X (XMach.act xs X ⟨e :: rest, .idle⟩).2.1).2.1 + 0))
  rw [a₁]
  show _ ≤ XMach.cost xs X ⟨e :: rest, .idle⟩ + (XMach.cost xs X ⟨rest, .look e.1 e.2⟩ +
    (XMach.cost xs X (XMach.act xs X ⟨rest, .look e.1 e.2⟩).2.1 + 0))
  rw [a₂]
  show _ ≤ XMach.cost xs X ⟨e :: rest, .idle⟩ + (XMach.cost xs X ⟨rest, .look e.1 e.2⟩ +
    (XMach.cost xs X ⟨rest, .seek e.1 e.2 (e.1, 0) q⟩ + 0))
  have u₁ : 1 ≤ XMach.cost xs X ⟨e :: rest, .idle⟩ := Nat.le_add_right 1 _
  have u₂ : 1 ≤ XMach.cost xs X ⟨rest, .look e.1 e.2⟩ := Nat.le_add_right 1 _
  omega

/-- A pass over such agents costs as much for each of them. -/
theorem XThread.spent_stuck_pass {X : XNet S} (rest : List (Id × S)) :
    ∀ (l : List (Id × S)), (∀ e, e ∈ l → X.Inert e) →
      l.length * (3 + X.wires.length) ≤
        (⟨l ++ rest, .idle⟩ : XThread S).spent xs X (3 * l.length)
  | [], _ => Nat.le_of_eq (Nat.zero_mul _)
  | e :: l, h => by
    obtain ⟨c, a⟩ := XThread.spent_stuck (xs := xs) (l ++ rest) (h e List.mem_cons_self)
    have ih := XThread.spent_stuck_pass rest l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have e1 : 3 * (e :: l).length = 3 + 3 * l.length := by
      show 3 * (l.length + 1) = _
      omega
    have e2 : (e :: l).length * (3 + X.wires.length) =
        l.length * (3 + X.wires.length) + (3 + X.wires.length) := Nat.succ_mul _ _
    rw [e1, e2]
    show _ ≤ (⟨e :: (l ++ rest), .idle⟩ : XThread S).spent xs X (3 + 3 * l.length)
    rw [XThread.spent_add, a]
    omega

end Time

/-! ### How many turns

Threads that take turns each shorten their list at every turn, or make a
claim and take the agents in memory as their list.  So the turns can be
counted. -/

section TurnBound

variable [DecidableEq S] {xs : XSys S}

/-- **One action and the agents in memory**: with those the thread still
has to write, they are no more than before, apart from the new agents of a
claim. -/
theorem XMach.act_heads {C D : Nat} (hb : xs.Bounded C D) (X : XNet S) (T : XThread S) :
    (XMach.act xs X T).1.agents.length + (XMach.act xs X T).2.1.owes ≤
      X.agents.length + T.owes + C * (XMach.act xs X T).2.2 := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    cases todo with
    | nil => exact Nat.le_add_right _ _
    | cons e rest =>
      by_cases he : assoc e.1 X.agents = some e.2
      · rw [XMach.act_idle_pos he]
        exact Nat.le_add_right _ _
      · rw [XMach.act_idle_neg he]
        exact Nat.le_add_right _ _
  | look a α =>
    cases hv : assoc (a, 0) X.wires with
    | some q =>
      rw [XMach.act_look hv]
      exact Nat.le_add_right _ _
    | none =>
      rw [XMach.act_look_none hv]
      exact Nat.le_add_right _ _
  | seek a α p c =>
    cases hsc : (if c.2 = 0 then assoc c.1 X.agents else none) with
    | some β' =>
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β').isSome
      · rw [XMach.act_seek_found hsc hc]
        exact Nat.le_add_right _ _
      · rw [XMach.act_seek_norule hsc hc]
        exact Nat.le_add_right _ _
    | none =>
      cases hns : nextSeg X.wires c p with
      | some q =>
        rw [XMach.act_seek_next hsc hns]
        exact Nat.le_add_right _ _
      | none =>
        rw [XMach.act_seek_stop hsc hns]
        exact Nat.le_add_right _ _
  | ready a b α β =>
    by_cases ha : assoc a X.agents = some α
    · rw [XMach.act_ready ha]
      have h := XNet.takeAgent_length (assoc_mem ha)
      show (X.takeAgent a).agents.length + 1 ≤ X.agents.length + 0 + C * 0
      omega
    · rw [XMach.act_ready_neg ha]
      exact Nat.le_add_right _ _
  | half a b α β =>
    cases hh : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      rw [XMach.act_half hh]
      split at hh
      · rename_i hcond
        obtain ⟨hC, -⟩ := hb α β R hh
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have h := XNet.takeAgent_length (assoc_mem hcond.1)
        show (X.takeAgent b).agents.length + (R.newAgents a b).length ≤
          X.agents.length + 1 + C * 1
        omega
      · cases hh
    | none =>
      rw [XMach.act_half_none hh]
      show X.agents.length + 1 + 0 ≤ X.agents.length + 1 + C * 0
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show X.agents.length + 1 + as.length ≤ X.agents.length + (as.length + 1) + C * 0
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact Nat.le_add_right _ _
      | nil => exact Nat.le_add_right _ _

/-- The same for a run of a thread. -/
theorem Runs.heads {C D : Nat} (hb : xs.Bounded C D) {X X' : XNet S} {T T' : XThread S}
    {c k : Nat} (r : Runs xs X T X' T' c k) :
    X'.agents.length + T'.owes ≤ X.agents.length + T.owes + C * c := by
  induction r with
  | refl X T => exact Nat.le_add_right _ _
  | @step X X₁ X' T T₁ T' c₁ c k h _ ih =>
    have h₁ := XMach.act_heads hb X T
    rw [h] at h₁
    have h₁' : X₁.agents.length + T₁.owes ≤ X.agents.length + T.owes + C * c₁ := h₁
    rw [Nat.mul_add]
    omega

/-- A turn adds no more agents to the memory than its claim writes. -/
theorem Turn.agents {C D : Nat} (hb : xs.Bounded C D) {M M' : XMach S} {t c : Nat}
    (h : Turn xs M t M' c) : M'.mem.agents.length ≤ M.mem.agents.length + C * c := by
  cases h with
  | rest _ => exact Nat.le_add_right _ _
  | stale _ _ => exact Nat.le_add_right _ _
  | fail _ _ _ _ => exact Nat.le_add_right _ _
  | fire ht he r _ => exact (Runs.step (XMach.act_idle_pos he) r).heads hb

/-- What a turn changes, with the list a thread takes after a claim. -/
theorem Turn.effect' {M M' : XMach S} {t c : Nat} (h : Turn xs M t M' c) :
    (M.ths[t]? = some ⟨[], .idle⟩ ∧ M' = M ∧ c = 0) ∨
      ∃ e rest T', M.ths[t]? = some ⟨e :: rest, .idle⟩ ∧ M'.ths = M.ths.set t T' ∧
        ((c = 0 ∧ T'.todo.length < (e :: rest).length) ∨
          (c = 1 ∧ T'.todo = M'.mem.agents)) := by
  cases h with
  | rest ht => exact .inl ⟨ht, rfl, rfl⟩
  | stale ht _ => exact .inr ⟨_, _, _, ht, rfl, .inl ⟨rfl, Nat.lt_succ_self _⟩⟩
  | fail ht _ _ _ => exact .inr ⟨_, _, _, ht, rfl, .inl ⟨rfl, Nat.lt_succ_self _⟩⟩
  | fire ht _ _ _ => exact .inr ⟨_, _, _, ht, rfl, .inr ⟨rfl, rfl⟩⟩

/-- The length of the list of thread `u`. -/
def XMach.todoAt (M : XMach S) (u : Nat) : Nat :=
  match M.ths[u]? with
  | some T => T.todo.length
  | none => 0

/-- **A bound on the number of turns.**  Take a well-formed net with a
normal form `n` steps away, rules that write at most `C` agents, and a
sequence of turns in which every thread gets a turn in every window of `W`
turns.  After `W` times

    X.agents.length + n * (X.agents.length + C * n + 1) + 1

turns every thread rests, `n` claims have been made and the memory holds
the normal form: a turn of a thread shortens its list or makes a claim, and
after a claim the list is as long as the memory has agents. -/
theorem XMach.turns_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') {nt : Nat} (M : Nat → XMach S) (t c : Nat → Nat)
    (h0 : M 0 = XMach.init X nt) (hturn : ∀ i, Turn xs (M i) (t i) (M (i + 1)) (c i))
    {W : Nat} (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + W ∧ t j = u) :
    ∀ i, W * (X.agents.length + n * (X.agents.length + C * n + 1) + 1) ≤ i →
      (∀ u, u < nt → (M i).ths[u]? = some ⟨[], .idle⟩) ∧ claimsUpTo c i = n ∧
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
  have ag : ∀ i, (M i).mem.agents.length ≤ X.agents.length + C * claimsUpTo c i := by
    intro i
    induction i with
    | zero =>
      rw [h0]
      exact Nat.le_add_right _ _
    | succ i ih =>
      have h := (hturn i).agents hb
      show _ ≤ X.agents.length + C * (claimsUpTo c i + c i)
      rw [Nat.mul_add]
      omega
  have agA : ∀ i, (M i).mem.agents.length ≤ X.agents.length + C * n := fun i =>
    Nat.le_trans (ag i) (Nat.add_le_add_left (Nat.mul_le_mul_left C (bound i)) _)
  have each : ∀ u, u < nt → ∀ i,
      W * (X.agents.length + n * (X.agents.length + C * n + 1) + 1) ≤ i →
      (M i).ths[u]? = some ⟨[], .idle⟩ := by
    intro u hu i hi
    have keep : ∀ i, t i ≠ u → (M (i + 1)).ths[u]? = (M i).ths[u]? := by
      intro i hne
      rcases (hturn i).effect' with ⟨-, e, -⟩ | ⟨e, rest, T', -, eths, -⟩
      · rw [e]
      · rw [eths, List.getElem?_set_ne hne]
    have restk : ∀ i, (M i).ths[u]? = some ⟨[], .idle⟩ →
        (M (i + 1)).ths[u]? = some ⟨[], .idle⟩ := by
      intro i h
      by_cases hu' : t i = u
      · rcases (hturn i).effect' with ⟨-, e, -⟩ | ⟨e, rest, T', ht, -, -⟩
        · rw [e]
          exact h
        · rw [hu', h] at ht
          cases ht
      · rw [keep i hu']
        exact h
    have e0 : (M 0).todoAt u + (n - claimsUpTo c 0) * (X.agents.length + C * n + 1) =
        X.agents.length + n * (X.agents.length + C * n + 1) := by
      have hl : (M 0).todoAt u = X.agents.length := by
        unfold XMach.todoAt
        rw [h0, XMach.init_thread X hu]
        show (X.agents.drop u ++ X.agents.take u).length = X.agents.length
        rw [List.length_append, List.length_drop, List.length_take]
        omega
      rw [hl]
      rfl
    have hi' : W * ((M 0).todoAt u +
        (n - claimsUpTo c 0) * (X.agents.length + C * n + 1) + 1) ≤ i := by
      rw [e0]
      exact hi
    refine window_settles
      (fun i => (M i).todoAt u + (n - claimsUpTo c i) * (X.agents.length + C * n + 1))
      (fun i => t i ≠ u ∨ (M i).ths[u]? = some ⟨[], .idle⟩)
      (fun i => (M i).ths[u]? = some ⟨[], .idle⟩) W ?_ ?_ restk i hi'
    · intro i
      have hb1 : claimsUpTo c i + c i ≤ n := bound (i + 1)
      show (_ ∧ (M (i + 1)).todoAt u +
            (n - (claimsUpTo c i + c i)) * (X.agents.length + C * n + 1) =
          (M i).todoAt u + (n - claimsUpTo c i) * (X.agents.length + C * n + 1)) ∨
        (M (i + 1)).todoAt u + (n - (claimsUpTo c i + c i)) * (X.agents.length + C * n + 1) <
          (M i).todoAt u + (n - claimsUpTo c i) * (X.agents.length + C * n + 1)
      rcases (hturn i).effect' with ⟨hr, e, ez⟩ | ⟨e, rest, T', ht, eths, hcase⟩
      · refine .inl ⟨?_, ?_⟩
        · by_cases hu' : t i = u
          · rw [hu'] at hr
            exact .inr hr
          · exact .inl hu'
        · rw [e, ez]
          rfl
      · by_cases hu' : t i = u
        · rw [hu'] at ht eths
          have hlt := (List.getElem?_eq_some_iff.1 ht).1
          have tu : (M i).todoAt u = (e :: rest).length := by
            unfold XMach.todoAt
            rw [ht]
          have tu' : (M (i + 1)).todoAt u = T'.todo.length := by
            unfold XMach.todoAt
            rw [eths, List.getElem?_set_self hlt]
          refine .inr ?_
          rw [tu, tu']
          rcases hcase with ⟨ez, hl⟩ | ⟨e1, htodo⟩
          · rw [ez]
            exact Nat.add_lt_add_right hl _
          · have hA := agA (i + 1)
            rw [e1] at hb1
            have e1' : n - claimsUpTo c i = (n - (claimsUpTo c i + 1)) + 1 := by omega
            rw [htodo, e1, e1', Nat.add_mul, Nat.one_mul]
            have hpos : 0 < (e :: rest).length := Nat.succ_pos _
            omega
        · have same : (M (i + 1)).todoAt u = (M i).todoAt u := by
            unfold XMach.todoAt
            rw [eths, List.getElem?_set_ne hu']
          rw [same]
          rcases Nat.eq_zero_or_pos (c i) with hz | hp
          · refine .inl ⟨.inl hu', ?_⟩
            rw [hz]
            rfl
          · refine .inr ?_
            have e1 : (n - (claimsUpTo c i + c i)) + 1 ≤ n - claimsUpTo c i := by omega
            have h2 := Nat.mul_le_mul_right (X.agents.length + C * n + 1) e1
            rw [Nat.add_mul, Nat.one_mul] at h2
            omega
    · intro i hall
      have same : ∀ d, d ≤ W → (M (i + d)).ths[u]? = (M i).ths[u]? := by
        intro d
        induction d with
        | zero => exact fun _ => rfl
        | succ d ih =>
          intro hd
          have ih' := ih (by omega)
          show (M (i + d + 1)).ths[u]? = (M i).ths[u]?
          rcases hall (i + d) (by omega) (by omega) with hne | hr
          · rw [keep (i + d) hne]
            exact ih'
          · rw [restk (i + d) hr, ← ih', hr]
      obtain ⟨j, hj₁, hj₂, hju⟩ := hfair u hu i
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
      rcases hall (i + d) hj₁ hj₂ with hne | hr
      · exact absurd hju hne
      · show (M i).ths[u]? = some ⟨[], .idle⟩
        rw [← same d (by omega)]
        exact hr
  intro i hi
  have hall := fun u hu => each u hu i hi
  have hnorm : Normal (Step xs.sys) (M i).mem.toNet := by
    obtain ⟨u, T, hu, hcov⟩ := (calm i).lead
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hu
    rw [(calm i).len] at hlt
    rw [hall u hlt] at hu
    rw [← Option.some.inj hu] at hcov
    exact hcov.normal
  obtain ⟨e₁, e₂⟩ := normal_form_unique hX (red i) hs hnorm hn
  exact ⟨hall, e₂, e₁⟩

end TurnBound

end INet
