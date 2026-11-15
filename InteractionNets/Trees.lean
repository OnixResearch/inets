import InteractionNets.Ordered

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### The runs replayed on the trees alone

The kernel computes on the trees of the library but not on its hash maps,
and the ordered memory keeps the names of the agents and the neighbours of
the ports in hash maps.  `RMach` is the same program with the hash maps
left out: it finds an agent by going through the map of the agents, and
the neighbours of a port by going through the segments.  It is proved to
keep the trees, the stamp and the threads of the run action by action, so
the time by the depth of the trees is the time of the replay, and the
kernel computes that. -/

/-- **The largest key of an ordered map, read off its list.**  The
library finds it by a recursion the kernel does not unfold; this is the
same key and the kernel computes it. -/
def tmaxKey {V : Type} (t : Std.TreeMap Nat V) : Option Nat := t.toList.getLast?.map (·.1)

theorem tmaxKey_eq {V : Type} (t : Std.TreeMap Nat V) : tmaxKey t = t.maxKey? := by
  cases h : t.maxKey? with
  | none =>
    show t.toList.getLast?.map (·.1) = none
    rw [tmax_none t h]
    rfl
  | some s =>
    obtain ⟨v, -, hl⟩ := toList_max t h
    show t.toList.getLast?.map (·.1) = some s
    rw [hl, List.getLast?_concat]
    rfl

section Replay

variable [DecidableEq S] {xs : XSys S}

/-- **The ordered memory without its hash maps**: the ordered map of the
agents, the next stamp, the free ports and the segments.  What the hash
maps answer is found here by going through the map and the list. -/
structure RMem (S : Type) where
  cells : Std.TreeMap Nat (Id × S)
  stamp : Nat
  free : List Port
  wires : List (Port × Port)

/-- The ordered memory with its hash maps left out. -/
def TMem.strip (H : TMem S) : RMem S := ⟨H.cells, H.stamp, H.free, H.wires⟩

/-- The stamp and the symbol of an agent, found by going through the
map. -/
def RMem.find (R : RMem S) (a : Id) : Option (Nat × S) :=
  (R.cells.toList.find? fun e => decide (e.2.1 = a)).map fun e => (e.1, e.2.2)

/-- The symbol of an agent. -/
def RMem.sym (R : RMem S) (i : Id) : Option S := (R.find i).map (·.2)

/-- The neighbours of a port. -/
def RMem.nb (R : RMem S) (p : Port) : List Port := nbOf R.wires p

/-- Take an agent out. -/
def RMem.take (R : RMem S) (a : Id) : RMem S :=
  match R.find a with
  | some v => ⟨R.cells.erase v.1, R.stamp, R.free, R.wires⟩
  | none => R

/-- Write an agent. -/
def RMem.put (R : RMem S) (i : Id) (γ : S) : RMem S :=
  ⟨R.cells.insert R.stamp (i, γ), R.stamp + 1, R.free, R.wires⟩

/-- Write a segment. -/
def RMem.link (R : RMem S) (p q : Port) : RMem S :=
  ⟨R.cells, R.stamp, R.free, (p, q) :: R.wires⟩

/-- **One action replayed on the trees alone**: `TMach.act`, with every
lookup in a hash map answered from the map of the agents and the list of
the segments. -/
def RMach.act (xs : XSys S) (R : RMem S) (T : TThread S) : RMem S × TThread S :=
  match T.st with
  | .idle =>
    match tmaxKey T.todo with
    | none => (R, T)
    | some s =>
      match T.todo[s]? with
      | some e =>
        if R.sym e.1 = some e.2 then (R, ⟨T.todo.erase s, .look e.1 e.2⟩)
        else (R, ⟨T.todo.erase s, .idle⟩)
      | none => (R, T)
  | .look a α =>
    match (R.nb (a, 0)).head? with
    | some q => (R, ⟨T.todo, .seek a α (a, 0) q⟩)
    | none => (R, T.fail)
  | .seek a α p c =>
    match (if c.2 = 0 then R.sym c.1 else none) with
    | some β =>
      if a ≠ c.1 ∧ (xs.rule α β).isSome then (R, ⟨T.todo, .ready a c.1 α β⟩)
      else (R, T.fail)
    | none =>
      match (R.nb c).find? (fun q => decide (q ≠ p)) with
      | some q => (R, ⟨T.todo, .seek a α c q⟩)
      | none => (R, T.fail)
  | .ready a b α β =>
    if R.sym a = some α then (R.take a, ⟨T.todo, .half a b α β⟩)
    else (R, T.fail)
  | .half a b α β =>
    match (if R.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | some Rl =>
      (R.take b, ⟨T.todo, .write (Rl.newAgents a b) (Rl.newLinks xs.sys.ar a b α β)⟩)
    | none => (R.put a α, T.fail)
  | .write ((i, γ) :: as) ls => (R.put i γ, ⟨T.todo, .write as ls⟩)
  | .write [] ((p, q) :: ls) => (R.link p q, ⟨T.todo, .write [] ls⟩)
  | .write [] [] => (R, ⟨R.cells, .idle⟩)

/-- The state of the replay: the memory without its hash maps, and the
threads as they are. -/
structure RMach (S : Type) where
  mem : RMem S
  ths : List (TThread S)

/-- The program on the ordered memory with the hash maps left out. -/
def TMach.strip (M : TMach S) : RMach S := ⟨M.mem.strip, M.ths⟩

/-- One action of thread `t`, replayed. -/
def RMach.step (xs : XSys S) (M : RMach S) (t : Nat) : RMach S :=
  match M.ths[t]? with
  | some T => ⟨(RMach.act xs M.mem T).1, M.ths.set t (RMach.act xs M.mem T).2⟩
  | none => M

/-- The run replayed. -/
def RMach.trace (xs : XSys S) (σ : Nat → Nat) (M : RMach S) : Nat → RMach S
  | 0 => M
  | i + 1 => (RMach.trace xs σ M i).step xs (σ i)

/-- The memory of a net, without hash maps. -/
def RMem.ofX (X : XNet S) : RMem S :=
  X.wires.foldr (fun e R => R.link e.1 e.2)
    (X.agents.foldr (fun e R => R.put e.1 e.2) ⟨∅, 0, X.free, []⟩)

/-- The replay before it starts. -/
def RMach.init (X : XNet S) (n : Nat) : RMach S :=
  ⟨RMem.ofX X, (List.range n).map fun t =>
    ⟨treeOf (X.agents.drop t ++ X.agents.take t), .idle⟩⟩

/-- What an action costs, the depth of the trees charged, told without
the hash maps. -/
def RMach.dcost (xs : XSys S) (R : RMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match tmaxKey T.todo with
    | none => 0
    | some _ => 2 + 3 * (tdepth T.todo + 1)
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (R.sym c.1).isSome then 0 else 1 + findCells p (R.nb c)
    else 2 + findCells p (R.nb c)
  | .ready a _ α _ => 2 + if R.sym a = some α then 1 + (tdepth R.cells + 1) else 0
  | .half a b α β =>
    2 + if R.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some Rl =>
          1 + (tdepth R.cells + 1) + (Rl.newAgents a b).length +
            (Rl.newLinks xs.sys.ar a b α β).length
        | none => 1 + (tdepth R.cells + 1)
      else 1 + (tdepth R.cells + 1)
  | .write (_ :: _) _ => 2 + (tdepth R.cells + 1)
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- What the action of thread `t` costs in the replay. -/
def RMach.stepDcost (xs : XSys S) (M : RMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => RMach.dcost xs M.mem T
  | none => 0

/-- The time of the replay, the depth of the trees charged. -/
def RMach.dtime (xs : XSys S) (σ : Nat → Nat) (M : RMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => RMach.dtime xs σ M i + (RMach.trace xs σ M i).stepDcost xs (σ i)

/-- Every thread rests: nothing in hand and an empty map. -/
def RMach.resting (M : RMach S) : Bool :=
  M.ths.all fun T => (tmaxKey T.todo).isNone && T.st.isIdle

omit [DecidableEq S] in
/-- **The map of the names says what going through the map of the agents
finds.** -/
theorem TMem.Ok.find {H : TMem S} (h : H.Ok) (a : Id) : H.live[a]? = H.strip.find a := by
  show H.live[a]? =
    (H.cells.toList.find? fun e => decide (e.2.1 = a)).map fun e => (e.1, e.2.2)
  cases hf : H.cells.toList.find? (fun e => decide (e.2.1 = a)) with
  | none =>
    cases hl : H.live[a]? with
    | none => rfl
    | some v =>
      obtain ⟨s, γ⟩ := v
      have hm := (tmem_toList H.cells s (a, γ)).2 (h.fwd a s γ hl)
      have hn := List.find?_eq_none.1 hf (s, (a, γ)) hm
      exact absurd (decide_eq_true rfl) hn
  | some e =>
    obtain ⟨s, i, γ⟩ := e
    have hp₀ : decide ((s, i, γ).2.1 = a) = true :=
      List.find?_some (p := fun e : Nat × Id × S => decide (e.2.1 = a)) hf
    have hp : i = a := of_decide_eq_true hp₀
    have hc := (tmem_toList H.cells s (i, γ)).1 (List.mem_of_find?_eq_some hf)
    subst hp
    exact h.bwd s i γ hc

omit [DecidableEq S] in
theorem TMem.Ok.sym_strip {H : TMem S} (h : H.Ok) (i : Id) : H.strip.sym i = H.sym i := by
  show (H.strip.find i).map (·.2) = (H.live[i]?).map (·.2)
  rw [h.find i]

omit [DecidableEq S] in
theorem TMem.Ok.nb_strip {H : TMem S} (h : H.Ok) (p : Port) : H.strip.nb p = H.nb p :=
  (h.nbrs p).symm

omit [DecidableEq S] in
theorem TMem.Ok.take_strip {H : TMem S} (h : H.Ok) (a : Id) :
    H.strip.take a = (H.take a).strip := by
  unfold RMem.take TMem.take
  rw [← h.find a]
  cases H.live[a]? with
  | none => rfl
  | some v => rfl

/-- **The replay does what the program on the ordered memory does**: one
action leaves the same trees, the same stamp, the same segments and the
same thread. -/
theorem TMach.act_strip (xs : XSys S) {H : TMem S} (h : H.Ok) (T : TThread S) :
    ((TMach.act xs H T).1.strip, (TMach.act xs H T).2.1) = RMach.act xs H.strip T := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold TMach.act RMach.act
    dsimp only
    rw [tmaxKey_eq]
    cases todo.maxKey? with
    | none => rfl
    | some s =>
      dsimp only
      cases todo[s]? with
      | none => rfl
      | some e =>
        dsimp only
        rw [h.sym_strip]
        by_cases hc : H.sym e.1 = some e.2
        · rw [ite_pos' hc, ite_pos' hc] <;> rfl
        · rw [ite_neg' hc, ite_neg' hc] <;> rfl
  | look a α =>
    unfold TMach.act RMach.act
    dsimp only
    rw [h.nb_strip]
    cases (H.nb (a, 0)).head? with
    | none => rfl
    | some q => rfl
  | seek a α p c =>
    unfold TMach.act RMach.act
    dsimp only
    rw [h.sym_strip, h.nb_strip]
    cases (if c.2 = 0 then H.sym c.1 else none) with
    | some β =>
      dsimp only
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β).isSome
      · rw [ite_pos' hc, ite_pos' hc] <;> rfl
      · rw [ite_neg' hc, ite_neg' hc] <;> rfl
    | none =>
      dsimp only
      cases (H.nb c).find? (fun q => decide (q ≠ p)) with
      | none => rfl
      | some q => rfl
  | ready a b α β =>
    unfold TMach.act RMach.act
    dsimp only
    rw [h.sym_strip, h.take_strip]
    by_cases hc : H.sym a = some α
    · rw [ite_pos' hc, ite_pos' hc] <;> rfl
    · rw [ite_neg' hc, ite_neg' hc] <;> rfl
  | half a b α β =>
    unfold TMach.act RMach.act
    dsimp only
    rw [h.sym_strip, h.take_strip]
    cases (if H.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | none => rfl
    | some Rl => rfl
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      rfl
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        rfl
      | nil => rfl

theorem TMach.step_strip (xs : XSys S) {M : TMach S} (h : M.mem.Ok) (t : Nat) :
    (M.step xs t).1.strip = M.strip.step xs t := by
  have e : M.strip.step xs t = match M.ths[t]? with
      | some T =>
        ⟨(RMach.act xs M.mem.strip T).1, M.ths.set t (RMach.act xs M.mem.strip T).2⟩
      | none => M.strip := rfl
  rw [e]
  unfold TMach.step
  cases M.ths[t]? with
  | none => rfl
  | some T =>
    show (⟨(TMach.act xs M.mem T).1.strip, M.ths.set t (TMach.act xs M.mem T).2.1⟩ : RMach S) =
      ⟨(RMach.act xs M.mem.strip T).1, M.ths.set t (RMach.act xs M.mem.strip T).2⟩
    rw [← TMach.act_strip xs h T]

omit [DecidableEq S] in
theorem TMem.ofX_strip (X : XNet S) : (TMem.ofX X).strip = RMem.ofX X := by
  have hp : ∀ (l : List (Id × S)) (H₀ : TMem S),
      (l.foldr (fun e H => H.put e.1 e.2) H₀).strip =
        l.foldr (fun e R => R.put e.1 e.2) H₀.strip := by
    intro l H₀
    induction l with
    | nil => rfl
    | cons e l ih => exact congrArg (fun R => RMem.put R e.1 e.2) ih
  have hl : ∀ (l : List (Port × Port)) (H₀ : TMem S),
      (l.foldr (fun e H => H.link e.1 e.2) H₀).strip =
        l.foldr (fun e R => R.link e.1 e.2) H₀.strip := by
    intro l H₀
    induction l with
    | nil => rfl
    | cons e l ih => exact congrArg (fun R => RMem.link R e.1 e.2) ih
  show (X.wires.foldr (fun e H => H.link e.1 e.2)
    (X.agents.foldr (fun e H => H.put e.1 e.2) (TMem.empty X.free))).strip = _
  rw [hl, hp]
  rfl

omit [DecidableEq S] in
theorem TMach.init_strip (X : XNet S) (n : Nat) : (TMach.init X n).strip = RMach.init X n := by
  show (⟨(TMem.ofX X).strip, _⟩ : RMach S) = ⟨RMem.ofX X, _⟩
  rw [TMem.ofX_strip] <;> rfl

/-- **The replay keeps the trees of the run**, action by action, under any
schedule. -/
theorem TMach.trace_strip {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, ((TMach.init X nt).trace xs σ i).1.strip = (RMach.init X nt).trace xs σ i
  | 0 => TMach.init_strip X nt
  | i + 1 => by
    obtain ⟨-, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    show (((TMach.init X nt).trace xs σ i).1.step xs (σ i)).1.strip =
      ((RMach.init X nt).trace xs σ i).step xs (σ i)
    rw [TMach.step_strip xs ok, TMach.trace_strip hX hnd hnt σ i]

theorem TMach.dcost_strip (xs : XSys S) {H : TMem S} (h : H.Ok) (T : TThread S) :
    TMach.dcost xs H T = RMach.dcost xs H.strip T := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold TMach.dcost RMach.dcost
    dsimp only
    rw [tmaxKey_eq] <;> rfl
  | look a α => rfl
  | seek a α p c =>
    unfold TMach.dcost RMach.dcost
    dsimp only
    rw [h.sym_strip, h.nb_strip] <;> rfl
  | ready a b α β =>
    unfold TMach.dcost RMach.dcost
    dsimp only
    rw [h.sym_strip] <;> rfl
  | half a b α β =>
    unfold TMach.dcost RMach.dcost
    dsimp only
    rw [h.sym_strip] <;> rfl
  | write as ls =>
    cases as with
    | cons e as => rfl
    | nil =>
      cases ls with
      | cons e ls => rfl
      | nil => rfl

theorem TMach.stepDcost_strip (xs : XSys S) {M : TMach S} (h : M.mem.Ok) (t : Nat) :
    M.stepDcost xs t = M.strip.stepDcost xs t := by
  have e : M.strip.stepDcost xs t = match M.ths[t]? with
      | some T => RMach.dcost xs M.mem.strip T
      | none => 0 := rfl
  rw [e]
  unfold TMach.stepDcost
  cases M.ths[t]? with
  | none => rfl
  | some T => exact TMach.dcost_strip xs h T

/-- **The time by the depth of the trees is the time of the replay**, on
every run of the program on the ordered memory.  The replay has no hash
map, so the kernel computes it. -/
theorem TMach.dtime_replay {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (TMach.init X nt).dtime xs σ i = (RMach.init X nt).dtime xs σ i
  | 0 => rfl
  | i + 1 => by
    obtain ⟨-, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    show (TMach.init X nt).dtime xs σ i +
        ((TMach.init X nt).trace xs σ i).1.stepDcost xs (σ i) =
      (RMach.init X nt).dtime xs σ i + ((RMach.init X nt).trace xs σ i).stepDcost xs (σ i)
    rw [TMach.stepDcost_strip xs ok, TMach.trace_strip hX hnd hnt σ i,
      TMach.dtime_replay hX hnd hnt σ i]

omit [DecidableEq S] in
theorem RMach.rest_thread {M : RMach S} (h : M.resting = true) {t : Nat} {T : TThread S}
    (hT : M.ths[t]? = some T) : ∃ todo, T = ⟨todo, .idle⟩ ∧ tmaxKey todo = none := by
  have hr := List.all_eq_true.1 h T (List.mem_of_getElem? hT)
  obtain ⟨todo, st⟩ := T
  have hr' : ((tmaxKey todo).isNone && st.isIdle) = true := hr
  rw [Bool.and_eq_true] at hr'
  obtain ⟨h₁, h₂⟩ := hr'
  refine ⟨todo, ?_, Option.isNone_iff_eq_none.1 h₁⟩
  cases st with
  | idle => rfl
  | look a α => cases h₂
  | seek a α p c => cases h₂
  | ready a b α β => cases h₂
  | half a b α β => cases h₂
  | write as ls => cases h₂

/-- A replay at rest stays as it is. -/
theorem RMach.step_rest (xs : XSys S) {M : RMach S} (h : M.resting = true) (t : Nat) :
    M.step xs t = M := by
  unfold RMach.step
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := RMach.rest_thread h hT
    have e : RMach.act xs M.mem ⟨todo, .idle⟩ = (M.mem, ⟨todo, .idle⟩) := by
      unfold RMach.act
      dsimp only
      rw [hmax]
    show (⟨(RMach.act xs M.mem ⟨todo, .idle⟩).1,
      M.ths.set t (RMach.act xs M.mem ⟨todo, .idle⟩).2⟩ : RMach S) = M
    rw [e]
    show (⟨M.mem, M.ths.set t ⟨todo, .idle⟩⟩ : RMach S) = M
    rw [set_self M.ths t _ hT]

theorem RMach.trace_rest (σ : Nat → Nat) {M : RMach S} {B : Nat}
    (h : (M.trace xs σ B).resting = true) : ∀ d, M.trace xs σ (B + d) = M.trace xs σ B
  | 0 => rfl
  | d + 1 => by
    show (M.trace xs σ (B + d)).step xs (σ (B + d)) = _
    rw [RMach.trace_rest σ h d]
    exact RMach.step_rest xs h _

theorem RMach.stepDcost_rest (xs : XSys S) {M : RMach S} (h : M.resting = true) (t : Nat) :
    M.stepDcost xs t = 0 := by
  unfold RMach.stepDcost
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := RMach.rest_thread h hT
    show RMach.dcost xs M.mem ⟨todo, .idle⟩ = 0
    unfold RMach.dcost
    dsimp only
    rw [hmax]

/-- Once the replay is at rest its time stays what it is. -/
theorem RMach.dtime_rest (σ : Nat → Nat) {M : RMach S} {B : Nat}
    (h : (M.trace xs σ B).resting = true) : ∀ d, M.dtime xs σ (B + d) = M.dtime xs σ B
  | 0 => rfl
  | d + 1 => by
    have z : (M.trace xs σ (B + d)).stepDcost xs (σ (B + d)) = 0 := by
      rw [RMach.trace_rest σ h d]
      exact RMach.stepDcost_rest xs h _
    show M.dtime xs σ (B + d) + (M.trace xs σ (B + d)).stepDcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact RMach.dtime_rest σ h d

end Replay

/-! ### The steps of the operations on the trees

`TMach.dtime` charges an operation on an ordered map the depth of its tree
and one.  Here each operation the program makes on an ordered map (the
lookup, the search for the largest key, the insertion and the erasure) is
written again with a counter of its calls.  The equations are those of the
library's definitions, the results are proved to be the library's, and
each is proved to make at most one call for each level of the tree, and
one.  A call makes one comparison at most and one call of a balancing
function of the library, which is not recursive.  The running time with
those calls counted is then at most the time by the depth. -/

section TreeSteps

open Std.DTreeMap.Internal

variable {α : Type} {β : α → Type}

/-- **The lookup of the library, written again with a counter of its
calls.**  The equations are those of `Impl.Const.get?`; the second
component counts one for each call. -/
def implGetC {δ : Type} [Ord α] : Impl α (fun _ => δ) → α → Option δ × Nat
  | .leaf, _ => (none, 1)
  | .inner _ k' v' l r, k =>
    match compare k k' with
    | .lt => ((implGetC l k).1, (implGetC l k).2 + 1)
    | .gt => ((implGetC r k).1, (implGetC r k).2 + 1)
    | .eq => (some v', 1)

/-- The copy returns what the library returns. -/
theorem implGetC_fst {δ : Type} [Ord α] (t : Impl α (fun _ => δ)) (k : α) :
    (implGetC t k).1 = Impl.Const.get? t k := by
  induction t with
  | leaf => rw [Impl.Const.get?.eq_def] <;> rfl
  | inner sz k' v' l r ihl ihr =>
    rw [Impl.Const.get?.eq_def, implGetC]
    dsimp only
    cases compare k k' with
    | lt => exact ihl
    | gt => exact ihr
    | eq => rfl

/-- **A lookup makes at most one call for each level of the tree, and
one.** -/
theorem implGetC_snd {δ : Type} [Ord α] (t : Impl α (fun _ => δ)) (k : α) :
    (implGetC t k).2 ≤ implDepth t + 1 := by
  induction t with
  | leaf => exact Nat.le_refl _
  | inner sz k' v' l r ihl ihr =>
    have h₁ := Nat.le_max_left (implDepth l) (implDepth r)
    have h₂ := Nat.le_max_right (implDepth l) (implDepth r)
    rw [implGetC]
    show _ ≤ max (implDepth l) (implDepth r) + 1 + 1
    cases compare k k' with
    | lt =>
      show (implGetC l k).2 + 1 ≤ _
      omega
    | gt =>
      show (implGetC r k).2 + 1 ≤ _
      omega
    | eq =>
      show 1 ≤ _
      omega

/-- **The search for the largest key, written again with a counter.** -/
def implMaxC : Impl α β → Option α × Nat
  | .leaf => (none, 1)
  | .inner _ k _ _ r =>
    match r with
    | .leaf => (some k, 1)
    | .inner .. => ((implMaxC r).1, (implMaxC r).2 + 1)

theorem implMaxC_fst (t : Impl α β) : (implMaxC t).1 = t.maxKey? := by
  induction t with
  | leaf => rw [Impl.maxKey?.eq_1] <;> rfl
  | inner sz k v l r ihl ihr =>
    cases r with
    | leaf => rw [Impl.maxKey?.eq_2] <;> rfl
    | inner sz' k' v' l' r' =>
      rw [Impl.maxKey?.eq_3]
      exact ihr

theorem implMaxC_snd (t : Impl α β) : (implMaxC t).2 ≤ implDepth t + 1 := by
  induction t with
  | leaf => exact Nat.le_refl _
  | inner sz k v l r ihl ihr =>
    have h₂ := Nat.le_max_right (implDepth l) (implDepth r)
    cases r with
    | leaf =>
      show 1 ≤ max (implDepth l) (implDepth (Impl.leaf : Impl α β)) + 1 + 1
      omega
    | inner sz' k' v' l' r' =>
      show (implMaxC (Impl.inner sz' k' v' l' r')).2 + 1 ≤
        max (implDepth l) (implDepth (Impl.inner sz' k' v' l' r')) + 1 + 1
      omega

/-- **The insertion of the library, written again with a counter.**  The
equations are those of `Impl.insert!`, which the library proves to return
the tree of `Impl.insert`.  Each call makes one comparison at most and
one call of a balancing function, which is not recursive. -/
def implInsertC [Ord α] (k : α) (v : β k) : Impl α β → Impl α β × Nat
  | .leaf => (.inner 1 k v .leaf .leaf, 1)
  | .inner sz k' v' l r =>
    match compare k k' with
    | .lt => (Impl.balanceL! k' v' (implInsertC k v l).1 r, (implInsertC k v l).2 + 1)
    | .gt => (Impl.balanceR! k' v' l (implInsertC k v r).1, (implInsertC k v r).2 + 1)
    | .eq => (.inner sz k v l r, 1)

theorem implInsertC_fst [Ord α] (k : α) (v : β k) (t : Impl α β) :
    (implInsertC k v t).1 = Impl.insert! k v t := by
  induction t with
  | leaf => rw [Impl.insert!.eq_def] <;> rfl
  | inner sz k' v' l r ihl ihr =>
    rw [Impl.insert!.eq_def, implInsertC]
    dsimp only
    cases compare k k' with
    | lt =>
      show Impl.balanceL! k' v' (implInsertC k v l).1 r = _
      rw [ihl]
    | gt =>
      show Impl.balanceR! k' v' l (implInsertC k v r).1 = _
      rw [ihr]
    | eq => rfl

theorem implInsertC_snd [Ord α] (k : α) (v : β k) (t : Impl α β) :
    (implInsertC k v t).2 ≤ implDepth t + 1 := by
  induction t with
  | leaf => exact Nat.le_refl _
  | inner sz k' v' l r ihl ihr =>
    have h₁ := Nat.le_max_left (implDepth l) (implDepth r)
    have h₂ := Nat.le_max_right (implDepth l) (implDepth r)
    rw [implInsertC]
    show _ ≤ max (implDepth l) (implDepth r) + 1 + 1
    cases compare k k' with
    | lt =>
      show (implInsertC k v l).2 + 1 ≤ _
      omega
    | gt =>
      show (implInsertC k v r).2 + 1 ≤ _
      omega
    | eq =>
      show 1 ≤ _
      omega

/-- Taking the least entry out, with a counter: the equations of
`Impl.minView!`. -/
def implMinViewC : (k : α) → β k → Impl α β → Impl α β → Impl.RawView α β × Nat
  | k, v, .leaf, r => (⟨k, v, r⟩, 1)
  | k, v, .inner _ k' v' l' r', r =>
    (⟨(implMinViewC k' v' l' r').1.k, (implMinViewC k' v' l' r').1.v,
        Impl.balanceR! k v (implMinViewC k' v' l' r').1.tree r⟩,
      (implMinViewC k' v' l' r').2 + 1)

theorem implMinViewC_fst (k : α) (v : β k) (l r : Impl α β) :
    (implMinViewC k v l r).1 = Impl.minView! k v l r := by
  induction l generalizing k v r with
  | leaf => rw [Impl.minView!.eq_def] <;> rfl
  | inner sz k' v' l' r' ihl ihr =>
    rw [Impl.minView!.eq_def, implMinViewC]
    dsimp only
    rw [ihl k' v' r']

theorem implMinViewC_snd (k : α) (v : β k) (l r : Impl α β) :
    (implMinViewC k v l r).2 ≤ implDepth l + 1 := by
  induction l generalizing k v r with
  | leaf => exact Nat.le_refl _
  | inner sz k' v' l' r' ihl ihr =>
    have h₁ := Nat.le_max_left (implDepth l') (implDepth r')
    have ih := ihl k' v' r'
    show (implMinViewC k' v' l' r').2 + 1 ≤ max (implDepth l') (implDepth r') + 1 + 1
    omega

/-- Taking the greatest entry out, with a counter: the equations of
`Impl.maxView!`. -/
def implMaxViewC : (k : α) → β k → Impl α β → Impl α β → Impl.RawView α β × Nat
  | k, v, l, .leaf => (⟨k, v, l⟩, 1)
  | k, v, l, .inner _ k' v' l' r' =>
    (⟨(implMaxViewC k' v' l' r').1.k, (implMaxViewC k' v' l' r').1.v,
        Impl.balanceL! k v l (implMaxViewC k' v' l' r').1.tree⟩,
      (implMaxViewC k' v' l' r').2 + 1)

theorem implMaxViewC_fst (k : α) (v : β k) (l r : Impl α β) :
    (implMaxViewC k v l r).1 = Impl.maxView! k v l r := by
  induction r generalizing k v l with
  | leaf => rw [Impl.maxView!.eq_def] <;> rfl
  | inner sz k' v' l' r' ihl ihr =>
    rw [Impl.maxView!.eq_def, implMaxViewC]
    dsimp only
    rw [ihr k' v' l']

theorem implMaxViewC_snd (k : α) (v : β k) (l r : Impl α β) :
    (implMaxViewC k v l r).2 ≤ implDepth r + 1 := by
  induction r generalizing k v l with
  | leaf => exact Nat.le_refl _
  | inner sz k' v' l' r' ihl ihr =>
    have h₂ := Nat.le_max_right (implDepth l') (implDepth r')
    have ih := ihr k' v' l'
    show (implMaxViewC k' v' l' r').2 + 1 ≤ max (implDepth l') (implDepth r') + 1 + 1
    omega

/-- Joining the two sides of a node taken out, with the count of the calls
it makes below: the equations of `Impl.glue!`. -/
def implGlueC (l r : Impl α β) : Impl α β × Nat :=
  match l with
  | .leaf => (r, 0)
  | .inner sz k v l' r' =>
    match r with
    | .leaf => (l, 0)
    | .inner sz' k' v' l'' r'' =>
      if sz < sz' then
        (Impl.balanceL! (implMinViewC k' v' l'' r'').1.k (implMinViewC k' v' l'' r'').1.v l
            (implMinViewC k' v' l'' r'').1.tree, (implMinViewC k' v' l'' r'').2)
      else
        (Impl.balanceR! (implMaxViewC k v l' r').1.k (implMaxViewC k v l' r').1.v
            (implMaxViewC k v l' r').1.tree r, (implMaxViewC k v l' r').2)

theorem implGlueC_fst (l r : Impl α β) : (implGlueC l r).1 = l.glue! r := by
  cases l with
  | leaf => rw [Impl.glue!.eq_def] <;> rfl
  | inner sz k v l' r' =>
    cases r with
    | leaf => rw [Impl.glue!.eq_def] <;> rfl
    | inner sz' k' v' l'' r'' =>
      rw [Impl.glue!.eq_def]
      unfold implGlueC
      dsimp only
      by_cases h : sz < sz'
      · rw [ite_pos' h, ite_pos' h]
        show Impl.balanceL! (implMinViewC k' v' l'' r'').1.k (implMinViewC k' v' l'' r'').1.v
          (Impl.inner sz k v l' r') (implMinViewC k' v' l'' r'').1.tree = _
        rw [implMinViewC_fst]
      · rw [ite_neg' h, ite_neg' h]
        show Impl.balanceR! (implMaxViewC k v l' r').1.k (implMaxViewC k v l' r').1.v
          (implMaxViewC k v l' r').1.tree (Impl.inner sz' k' v' l'' r'') = _
        rw [implMaxViewC_fst]

theorem implGlueC_snd (l r : Impl α β) :
    (implGlueC l r).2 ≤ max (implDepth l) (implDepth r) := by
  cases l with
  | leaf => exact Nat.zero_le _
  | inner sz k v l' r' =>
    cases r with
    | leaf => exact Nat.zero_le _
    | inner sz' k' v' l'' r'' =>
      have h₁ := Nat.le_max_left (implDepth (Impl.inner sz k v l' r'))
        (implDepth (Impl.inner sz' k' v' l'' r''))
      have h₂ := Nat.le_max_right (implDepth (Impl.inner sz k v l' r'))
        (implDepth (Impl.inner sz' k' v' l'' r''))
      have e₁ : implDepth (Impl.inner sz k v l' r') = max (implDepth l') (implDepth r') + 1 := rfl
      have e₂ : implDepth (Impl.inner sz' k' v' l'' r'') =
          max (implDepth l'') (implDepth r'') + 1 := rfl
      have m₁ := Nat.le_max_right (implDepth l') (implDepth r')
      have m₂ := Nat.le_max_left (implDepth l'') (implDepth r'')
      have s₁ := implMinViewC_snd k' v' l'' r''
      have s₂ := implMaxViewC_snd k v l' r'
      unfold implGlueC
      dsimp only
      by_cases h : sz < sz'
      · rw [ite_pos' h]
        show (implMinViewC k' v' l'' r'').2 ≤ _
        omega
      · rw [ite_neg' h]
        show (implMaxViewC k v l' r').2 ≤ _
        omega

/-- **The erasure of the library, written again with a counter.**  The
equations are those of `Impl.erase!`, which the library proves to return
the tree of `Impl.erase`. -/
def implEraseC [Ord α] (k : α) : Impl α β → Impl α β × Nat
  | .leaf => (.leaf, 1)
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => (Impl.balanceR! k' v' (implEraseC k l).1 r, (implEraseC k l).2 + 1)
    | .gt => (Impl.balanceL! k' v' l (implEraseC k r).1, (implEraseC k r).2 + 1)
    | .eq => ((implGlueC l r).1, (implGlueC l r).2 + 1)

theorem implEraseC_fst [Ord α] (k : α) (t : Impl α β) :
    (implEraseC k t).1 = Impl.erase! k t := by
  induction t with
  | leaf => rw [Impl.erase!.eq_def] <;> rfl
  | inner sz k' v' l r ihl ihr =>
    rw [Impl.erase!.eq_def, implEraseC]
    dsimp only
    cases compare k k' with
    | lt =>
      show Impl.balanceR! k' v' (implEraseC k l).1 r = _
      rw [ihl]
    | gt =>
      show Impl.balanceL! k' v' l (implEraseC k r).1 = _
      rw [ihr]
    | eq => exact implGlueC_fst l r

theorem implEraseC_snd [Ord α] (k : α) (t : Impl α β) :
    (implEraseC k t).2 ≤ implDepth t + 1 := by
  induction t with
  | leaf => exact Nat.le_refl _
  | inner sz k' v' l r ihl ihr =>
    have h₁ := Nat.le_max_left (implDepth l) (implDepth r)
    have h₂ := Nat.le_max_right (implDepth l) (implDepth r)
    have hg := implGlueC_snd l r
    rw [implEraseC]
    show _ ≤ max (implDepth l) (implDepth r) + 1 + 1
    cases compare k k' with
    | lt =>
      show (implEraseC k l).2 + 1 ≤ _
      omega
    | gt =>
      show (implEraseC k r).2 + 1 ≤ _
      omega
    | eq =>
      show (implGlueC l r).2 + 1 ≤ _
      omega

variable {V : Type}

/-- The lookup in an ordered map, with the count of its calls. -/
def tgetC (t : Std.TreeMap Nat V) (k : Nat) : Option V × Nat := implGetC t.inner.inner k

/-- The largest key of an ordered map, with the count of the calls. -/
def tmaxC (t : Std.TreeMap Nat V) : Option Nat × Nat := implMaxC t.inner.inner

/-- The tree of an insertion in an ordered map, with the count of the
calls. -/
def tinsertC (t : Std.TreeMap Nat V) (k : Nat) (v : V) : Impl Nat (fun _ => V) × Nat :=
  implInsertC k v t.inner.inner

/-- The tree of an erasure in an ordered map, with the count of the
calls. -/
def teraseC (t : Std.TreeMap Nat V) (k : Nat) : Impl Nat (fun _ => V) × Nat :=
  implEraseC k t.inner.inner

/-- **The counted operations are those of the library**: each returns
what the operation of `Std.TreeMap` returns. -/
theorem tgetC_fst (t : Std.TreeMap Nat V) (k : Nat) : (tgetC t k).1 = t[k]? :=
  implGetC_fst t.inner.inner k

theorem tmaxC_fst (t : Std.TreeMap Nat V) : (tmaxC t).1 = t.maxKey? :=
  implMaxC_fst t.inner.inner

theorem tinsertC_fst (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (tinsertC t k v).1 = (t.insert k v).inner.inner := by
  show (implInsertC k v t.inner.inner).1 =
    (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl
  rw [implInsertC_fst, Impl.insert_eq_insert!]

theorem teraseC_fst (t : Std.TreeMap Nat V) (k : Nat) :
    (teraseC t k).1 = (t.erase k).inner.inner := by
  show (implEraseC k t.inner.inner).1 = (Impl.erase k t.inner.inner t.inner.wf.balanced).impl
  rw [implEraseC_fst, Impl.erase_eq_erase!]

/-- **Each operation on an ordered map makes at most one call for each
level of its tree, and one**: the charge of `TMach.dtime`. -/
theorem tgetC_snd (t : Std.TreeMap Nat V) (k : Nat) : (tgetC t k).2 ≤ tdepth t + 1 :=
  implGetC_snd t.inner.inner k

theorem tmaxC_snd (t : Std.TreeMap Nat V) : (tmaxC t).2 ≤ tdepth t + 1 :=
  implMaxC_snd t.inner.inner

theorem tinsertC_snd (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (tinsertC t k v).2 ≤ tdepth t + 1 :=
  implInsertC_snd (β := fun _ => V) k v t.inner.inner

theorem teraseC_snd (t : Std.TreeMap Nat V) (k : Nat) : (teraseC t k).2 ≤ tdepth t + 1 :=
  implEraseC_snd k t.inner.inner

/-- **So each makes at most `3 * lg n` calls on a map of `n` entries.** -/
theorem tsteps_le_lg (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (tgetC t k).2 ≤ 3 * lg t.size ∧ (tmaxC t).2 ≤ 3 * lg t.size ∧
      (tinsertC t k v).2 ≤ 3 * lg t.size ∧ (teraseC t k).2 ≤ 3 * lg t.size := by
  have h := tdepth_lt t
  have h₁ := tgetC_snd t k
  have h₂ := tmaxC_snd t
  have h₃ := tinsertC_snd t k v
  have h₄ := teraseC_snd t k
  exact ⟨by omega, by omega, by omega, by omega⟩

end TreeSteps

section Counted

variable [DecidableEq S] {xs : XSys S}

/-- The calls that taking an agent out of the ordered memory makes on the
tree. -/
def TMem.takeC (H : TMem S) (a : Id) : Nat :=
  match H.live[a]? with
  | some v => (teraseC H.cells v.1).2
  | none => 0

omit [DecidableEq S] in
theorem TMem.takeC_le (H : TMem S) (a : Id) : H.takeC a ≤ tdepth H.cells + 1 := by
  unfold TMem.takeC
  cases H.live[a]? with
  | none => exact Nat.zero_le _
  | some v => exact teraseC_snd H.cells v.1

/-- **What an action costs on the ordered memory when each operation on an
ordered map is charged the calls it makes**: as `TMach.dcost`, with the
counts of the counted operations where that has the depth of the tree and
one. -/
def TMach.ccost (xs : XSys S) (H : TMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match T.todo.maxKey? with
    | none => 0
    | some s => 2 + ((tmaxC T.todo).2 + (tgetC T.todo s).2 + (teraseC T.todo s).2)
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (H.sym c.1).isSome then 0 else 1 + findCells p (H.nb c)
    else 2 + findCells p (H.nb c)
  | .ready a _ α _ => 2 + if H.sym a = some α then 1 + H.takeC a else 0
  | .half a b α β =>
    2 + if H.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          1 + H.takeC b + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 1 + (tinsertC H.cells H.stamp (a, α)).2
      else 1 + (tinsertC H.cells H.stamp (a, α)).2
  | .write ((i, γ) :: _) _ => 2 + (tinsertC H.cells H.stamp (i, γ)).2
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- **The calls counted are never more than the depth charged.** -/
theorem TMach.ccost_le_dcost (xs : XSys S) (H : TMem S) (T : TThread S) :
    TMach.ccost xs H T ≤ TMach.dcost xs H T := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold TMach.ccost TMach.dcost
    dsimp only
    cases todo.maxKey? with
    | none => exact Nat.le_refl _
    | some s =>
      have h₁ := tmaxC_snd todo
      have h₂ := tgetC_snd todo s
      have h₃ := teraseC_snd todo s
      show 2 + ((tmaxC todo).2 + (tgetC todo s).2 + (teraseC todo s).2) ≤
        2 + 3 * (tdepth todo + 1)
      omega
  | look a α => exact Nat.le_refl _
  | seek a α p c => exact Nat.le_refl _
  | ready a b α β =>
    have ht := H.takeC_le a
    show 2 + (if H.sym a = some α then 1 + H.takeC a else 0) ≤
      2 + (if H.sym a = some α then 1 + (tdepth H.cells + 1) else 0)
    by_cases hc : H.sym a = some α
    · rw [ite_pos' hc, ite_pos' hc]
      omega
    · rw [ite_neg' hc, ite_neg' hc]
      exact Nat.le_refl _
  | half a b α β =>
    have ht := H.takeC_le b
    have hi := tinsertC_snd H.cells H.stamp (a, α)
    unfold TMach.ccost TMach.dcost
    dsimp only
    by_cases hc : H.sym b = some β ∧ a ≠ b
    · rw [ite_pos' hc, ite_pos' hc]
      cases xs.rule α β with
      | none =>
        show 2 + (1 + (tinsertC H.cells H.stamp (a, α)).2) ≤ 2 + (1 + (tdepth H.cells + 1))
        omega
      | some R =>
        show 2 + (1 + H.takeC b + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length) ≤
          2 + (1 + (tdepth H.cells + 1) + (R.newAgents a b).length +
            (R.newLinks xs.sys.ar a b α β).length)
        omega
    · rw [ite_neg' hc, ite_neg' hc]
      show 2 + (1 + (tinsertC H.cells H.stamp (a, α)).2) ≤ 2 + (1 + (tdepth H.cells + 1))
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have hi := tinsertC_snd H.cells H.stamp (i, γ)
      show 2 + (tinsertC H.cells H.stamp (i, γ)).2 ≤ 2 + (tdepth H.cells + 1)
      omega
    | nil =>
      cases ls with
      | cons e ls => exact Nat.le_refl _
      | nil => exact Nat.le_refl _

/-- What the action of thread `t` costs, the calls counted. -/
def TMach.stepCcost (xs : XSys S) (M : TMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => TMach.ccost xs M.mem T
  | none => 0

/-- **The running time on the ordered memory, the calls on the trees
counted.** -/
def TMach.ctime (xs : XSys S) (σ : Nat → Nat) (M : TMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => TMach.ctime xs σ M i + (M.trace xs σ i).1.stepCcost xs (σ i)

/-- **The time by the calls counted is at most the time by the depth of
the trees**, on every run from every state. -/
theorem TMach.ctime_le_dtime (xs : XSys S) (σ : Nat → Nat) (M : TMach S) :
    ∀ i, M.ctime xs σ i ≤ M.dtime xs σ i
  | 0 => Nat.le_refl _
  | i + 1 => by
    have ih := TMach.ctime_le_dtime xs σ M i
    have hstep : (M.trace xs σ i).1.stepCcost xs (σ i) ≤
        (M.trace xs σ i).1.stepDcost xs (σ i) := by
      unfold TMach.stepCcost TMach.stepDcost
      cases (M.trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.le_refl _
      | some T => exact TMach.ccost_le_dcost xs _ T
    show M.ctime xs σ i + (M.trace xs σ i).1.stepCcost xs (σ i) ≤
      M.dtime xs σ i + (M.trace xs σ i).1.stepDcost xs (σ i)
    omega

/-- **A bound on the running time with the calls on the trees counted,
whatever the schedule.** -/
theorem TMach.ctime_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    (TMach.init X nt).ctime xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) *
        (C + D + 3 + 9 * lg (X.agents.length + C * n)) :=
  Nat.le_trans (TMach.ctime_le_dtime xs σ _ i) (TMach.dtime_bound hX hnd hnt hb hs hn σ i)

/-- The calls of taking an agent out, told without the hash maps. -/
def RMem.takeC (R : RMem S) (a : Id) : Nat :=
  match R.find a with
  | some v => (teraseC R.cells v.1).2
  | none => 0

omit [DecidableEq S] in
theorem TMem.Ok.takeC_strip {H : TMem S} (h : H.Ok) (a : Id) :
    H.strip.takeC a = H.takeC a := by
  unfold RMem.takeC TMem.takeC
  rw [← h.find a]
  cases H.live[a]? with
  | none => rfl
  | some v => rfl

/-- What an action costs, the calls counted, told without the hash
maps. -/
def RMach.ccost (xs : XSys S) (R : RMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match tmaxKey T.todo with
    | none => 0
    | some s => 2 + ((tmaxC T.todo).2 + (tgetC T.todo s).2 + (teraseC T.todo s).2)
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then 2 + if (R.sym c.1).isSome then 0 else 1 + findCells p (R.nb c)
    else 2 + findCells p (R.nb c)
  | .ready a _ α _ => 2 + if R.sym a = some α then 1 + R.takeC a else 0
  | .half a b α β =>
    2 + if R.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some Rl =>
          1 + R.takeC b + (Rl.newAgents a b).length + (Rl.newLinks xs.sys.ar a b α β).length
        | none => 1 + (tinsertC R.cells R.stamp (a, α)).2
      else 1 + (tinsertC R.cells R.stamp (a, α)).2
  | .write ((i, γ) :: _) _ => 2 + (tinsertC R.cells R.stamp (i, γ)).2
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

theorem TMach.ccost_strip (xs : XSys S) {H : TMem S} (h : H.Ok) (T : TThread S) :
    TMach.ccost xs H T = RMach.ccost xs H.strip T := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold TMach.ccost RMach.ccost
    dsimp only
    rw [tmaxKey_eq] <;> rfl
  | look a α => rfl
  | seek a α p c =>
    unfold TMach.ccost RMach.ccost
    dsimp only
    rw [h.sym_strip, h.nb_strip] <;> rfl
  | ready a b α β =>
    unfold TMach.ccost RMach.ccost
    dsimp only
    rw [h.sym_strip, h.takeC_strip] <;> rfl
  | half a b α β =>
    unfold TMach.ccost RMach.ccost
    dsimp only
    rw [h.sym_strip, h.takeC_strip] <;> rfl
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      rfl
    | nil =>
      cases ls with
      | cons e ls => rfl
      | nil => rfl

/-- What the action of thread `t` costs in the replay, the calls
counted. -/
def RMach.stepCcost (xs : XSys S) (M : RMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => RMach.ccost xs M.mem T
  | none => 0

/-- The time of the replay, the calls counted. -/
def RMach.ctime (xs : XSys S) (σ : Nat → Nat) (M : RMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => RMach.ctime xs σ M i + (RMach.trace xs σ M i).stepCcost xs (σ i)

theorem TMach.stepCcost_strip (xs : XSys S) {M : TMach S} (h : M.mem.Ok) (t : Nat) :
    M.stepCcost xs t = M.strip.stepCcost xs t := by
  have e : M.strip.stepCcost xs t = match M.ths[t]? with
      | some T => RMach.ccost xs M.mem.strip T
      | none => 0 := rfl
  rw [e]
  unfold TMach.stepCcost
  cases M.ths[t]? with
  | none => rfl
  | some T => exact TMach.ccost_strip xs h T

/-- **The time by the calls counted is the time of the replay.** -/
theorem TMach.ctime_replay {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (TMach.init X nt).ctime xs σ i = (RMach.init X nt).ctime xs σ i
  | 0 => rfl
  | i + 1 => by
    obtain ⟨-, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    show (TMach.init X nt).ctime xs σ i +
        ((TMach.init X nt).trace xs σ i).1.stepCcost xs (σ i) =
      (RMach.init X nt).ctime xs σ i + ((RMach.init X nt).trace xs σ i).stepCcost xs (σ i)
    rw [TMach.stepCcost_strip xs ok, TMach.trace_strip hX hnd hnt σ i,
      TMach.ctime_replay hX hnd hnt σ i]

theorem RMach.stepCcost_rest (xs : XSys S) {M : RMach S} (h : M.resting = true) (t : Nat) :
    M.stepCcost xs t = 0 := by
  unfold RMach.stepCcost
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := RMach.rest_thread h hT
    show RMach.ccost xs M.mem ⟨todo, .idle⟩ = 0
    unfold RMach.ccost
    dsimp only
    rw [hmax]

/-- Once the replay is at rest this time too stays what it is. -/
theorem RMach.ctime_rest (σ : Nat → Nat) {M : RMach S} {B : Nat}
    (h : (M.trace xs σ B).resting = true) : ∀ d, M.ctime xs σ (B + d) = M.ctime xs σ B
  | 0 => rfl
  | d + 1 => by
    have z : (M.trace xs σ (B + d)).stepCcost xs (σ (B + d)) = 0 := by
      rw [RMach.trace_rest σ h d]
      exact RMach.stepCcost_rest xs h _
    show M.ctime xs σ (B + d) + (M.trace xs σ (B + d)).stepCcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact RMach.ctime_rest σ h d

end Counted

/-! ### Ordered maps alone

The ordered memory keeps two hash maps, and an operation on a hash map is
counted one, which holds on average.  Here they are replaced by ordered
maps of the library keyed by names, so that every operation on every map
has a count of calls that is proved, in the worst case.  The program is
proved to stay in step with the program on the ordered memory, and its
time, with every call counted, is bounded for every schedule. -/

section NameMaps

variable {V : Type}

theorem oget_insert (t : Std.TreeMap (List Nat) V) (k a : List Nat) (v : V) :
    (t.insert k v)[a]? = if k = a then some v else t[a]? := by
  rw [Std.TreeMap.getElem?_insert]
  simp

theorem oget_erase (t : Std.TreeMap (List Nat) V) (k a : List Nat) :
    (t.erase k)[a]? = if k = a then none else t[a]? := by
  rw [Std.TreeMap.getElem?_erase]
  simp

theorem oget_empty (a : List Nat) : (∅ : Std.TreeMap (List Nat) V)[a]? = none :=
  Std.TreeMap.getElem?_emptyc

/-- **A port as a name**: its index, then the name of its agent.  The map
of the neighbours is keyed by it. -/
def portKey (p : Port) : List Nat := p.2 :: p.1

theorem portKey_inj {p q : Port} : portKey p = portKey q ↔ p = q := by
  constructor
  · intro h
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    have h' : i :: a = j :: b := h
    injection h' with h₁ h₂
    rw [h₁, h₂]
  · intro h
    rw [h]

end NameMaps

section AllOrdered

variable [DecidableEq S] {xs : XSys S}

/-- **The memory on ordered maps alone.**  As the ordered memory, but the
map of the names and the map of the neighbours are ordered maps too, keyed
by names in the order of lists of numbers.  No operation on it rests on a
hash. -/
structure OMem (S : Type) where
  cells : Std.TreeMap Nat (Id × S)
  stamp : Nat
  live : Std.TreeMap (List Nat) (Nat × S)
  free : List Port
  wires : List (Port × Port)
  nbrs : Std.TreeMap (List Nat) (List Port)

/-- The memory of lists that it stands for. -/
def OMem.toX (O : OMem S) : XNet S := ⟨treeList O.cells, O.free, O.wires⟩

/-- The symbol of an agent: one lookup. -/
def OMem.sym (O : OMem S) (i : Id) : Option S := (O.live[i]?).map (·.2)

/-- The neighbours of a port: one lookup. -/
def OMem.nb (O : OMem S) (p : Port) : List Port := (O.nbrs[portKey p]?).getD []

/-- Take an agent out: two erasures. -/
def OMem.take (O : OMem S) (a : Id) : OMem S :=
  match O.live[a]? with
  | some v => ⟨O.cells.erase v.1, O.stamp, O.live.erase a, O.free, O.wires, O.nbrs⟩
  | none => O

/-- Write an agent: two insertions. -/
def OMem.put (O : OMem S) (i : Id) (γ : S) : OMem S :=
  ⟨O.cells.insert O.stamp (i, γ), O.stamp + 1, O.live.insert i (O.stamp, γ), O.free,
    O.wires, O.nbrs⟩

/-- Write a segment. -/
def OMem.link (O : OMem S) (p q : Port) : OMem S :=
  ⟨O.cells, O.stamp, O.live, O.free, (p, q) :: O.wires,
    O.nbrs.insert (portKey p) (pushNb q (O.nb p))⟩

def OMem.empty (free : List Port) : OMem S := ⟨∅, 0, ∅, free, [], ∅⟩

/-- The memory of a net: its agents written one by one, the last first,
then its segments. -/
def OMem.ofX (X : XNet S) : OMem S :=
  X.wires.foldr (fun e O => O.link e.1 e.2)
    (X.agents.foldr (fun e O => O.put e.1 e.2) (OMem.empty X.free))

/-- **The two memories answer alike**: the same map of the agents, the
same stamp, free ports and segments, and every lookup of a name or of the
neighbours of a port gives the same in both. -/
structure OMem.Agree (O : OMem S) (H : TMem S) : Prop where
  cells : O.cells = H.cells
  stamp : O.stamp = H.stamp
  free : O.free = H.free
  wires : O.wires = H.wires
  live : ∀ a : Id, O.live[a]? = H.live[a]?
  nbrs : ∀ p : Port, O.nbrs[portKey p]? = H.nbrs[p]?

omit [DecidableEq S] in
theorem OMem.Agree.sym {O : OMem S} {H : TMem S} (h : O.Agree H) (i : Id) :
    O.sym i = H.sym i := by
  show (O.live[i]?).map (·.2) = (H.live[i]?).map (·.2)
  rw [h.live i]

omit [DecidableEq S] in
theorem OMem.Agree.nb {O : OMem S} {H : TMem S} (h : O.Agree H) (p : Port) :
    O.nb p = H.nb p := by
  show (O.nbrs[portKey p]?).getD [] = (H.nbrs[p]?).getD []
  rw [h.nbrs p]

omit [DecidableEq S] in
theorem OMem.Agree.take {O : OMem S} {H : TMem S} (h : O.Agree H) (a : Id) :
    (O.take a).Agree (H.take a) := by
  unfold OMem.take TMem.take
  rw [h.live a]
  cases H.live[a]? with
  | none => exact h
  | some v =>
    refine ⟨?_, h.stamp, h.free, h.wires, fun x => ?_, h.nbrs⟩
    · show O.cells.erase v.1 = H.cells.erase v.1
      rw [h.cells]
    · show (O.live.erase a)[x]? = (H.live.erase a)[x]?
      rw [oget_erase, hget_erase, h.live x]

omit [DecidableEq S] in
theorem OMem.Agree.put {O : OMem S} {H : TMem S} (h : O.Agree H) (i : Id) (γ : S) :
    (O.put i γ).Agree (H.put i γ) := by
  refine ⟨?_, ?_, h.free, h.wires, fun x => ?_, h.nbrs⟩
  · show O.cells.insert O.stamp (i, γ) = H.cells.insert H.stamp (i, γ)
    rw [h.cells, h.stamp]
  · show O.stamp + 1 = H.stamp + 1
    rw [h.stamp]
  · show (O.live.insert i (O.stamp, γ))[x]? = (H.live.insert i (H.stamp, γ))[x]?
    rw [oget_insert, hget_insert, h.live x, h.stamp]

omit [DecidableEq S] in
theorem OMem.Agree.link {O : OMem S} {H : TMem S} (h : O.Agree H) (p q : Port) :
    (O.link p q).Agree (H.link p q) := by
  refine ⟨h.cells, h.stamp, h.free, ?_, h.live, fun x => ?_⟩
  · show (p, q) :: O.wires = (p, q) :: H.wires
    rw [h.wires]
  · show (O.nbrs.insert (portKey p) (pushNb q (O.nb p)))[portKey x]? =
      (H.nbrs.insert p (pushNb q (H.nb p)))[x]?
    rw [oget_insert, hget_insert, h.nb p, h.nbrs x]
    by_cases e : p = x
    · rw [ite_pos' e, ite_pos' (congrArg portKey e)]
    · rw [ite_neg' e, ite_neg' (fun e' => e (portKey_inj.1 e'))]

omit [DecidableEq S] in
theorem OMem.empty_agree (free : List Port) :
    (OMem.empty free : OMem S).Agree (TMem.empty free) := by
  refine ⟨rfl, rfl, rfl, rfl, fun a => ?_, fun p => ?_⟩
  · show (∅ : Std.TreeMap (List Nat) (Nat × S))[a]? = (∅ : Std.HashMap Id (Nat × S))[a]?
    rw [oget_empty, Std.HashMap.getElem?_empty]
  · show (∅ : Std.TreeMap (List Nat) (List Port))[portKey p]? =
      (∅ : Std.HashMap Port (List Port))[p]?
    rw [oget_empty, Std.HashMap.getElem?_empty]

omit [DecidableEq S] in
theorem OMem.ofX_agree (X : XNet S) : (OMem.ofX X).Agree (TMem.ofX X) := by
  have hp : ∀ (l : List (Id × S)) {O : OMem S} {H : TMem S}, O.Agree H →
      (l.foldr (fun e O => O.put e.1 e.2) O).Agree (l.foldr (fun e H => H.put e.1 e.2) H) := by
    intro l O H h
    induction l with
    | nil => exact h
    | cons e l ih => exact ih.put e.1 e.2
  have hl : ∀ (l : List (Port × Port)) {O : OMem S} {H : TMem S}, O.Agree H →
      (l.foldr (fun e O => O.link e.1 e.2) O).Agree
        (l.foldr (fun e H => H.link e.1 e.2) H) := by
    intro l O H h
    induction l with
    | nil => exact h
    | cons e l ih => exact ih.link e.1 e.2
  exact hl X.wires (hp X.agents (OMem.empty_agree X.free))

/-- **One action of a thread on ordered maps alone.**  The action of
`TMach.act`; the largest key is found by the counted search, which the
kernel computes. -/
def OMach.act (xs : XSys S) (O : OMem S) (T : TThread S) : OMem S × TThread S × Nat :=
  match T.st with
  | .idle =>
    match (tmaxC T.todo).1 with
    | none => (O, T, 0)
    | some s =>
      match T.todo[s]? with
      | some e =>
        if O.sym e.1 = some e.2 then (O, ⟨T.todo.erase s, .look e.1 e.2⟩, 0)
        else (O, ⟨T.todo.erase s, .idle⟩, 0)
      | none => (O, T, 0)
  | .look a α =>
    match (O.nb (a, 0)).head? with
    | some q => (O, ⟨T.todo, .seek a α (a, 0) q⟩, 0)
    | none => (O, T.fail, 0)
  | .seek a α p c =>
    match (if c.2 = 0 then O.sym c.1 else none) with
    | some β =>
      if a ≠ c.1 ∧ (xs.rule α β).isSome then (O, ⟨T.todo, .ready a c.1 α β⟩, 0)
      else (O, T.fail, 0)
    | none =>
      match (O.nb c).find? (fun q => decide (q ≠ p)) with
      | some q => (O, ⟨T.todo, .seek a α c q⟩, 0)
      | none => (O, T.fail, 0)
  | .ready a b α β =>
    if O.sym a = some α then (O.take a, ⟨T.todo, .half a b α β⟩, 0)
    else (O, T.fail, 0)
  | .half a b α β =>
    match (if O.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      (O.take b, ⟨T.todo, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1)
    | none => (O.put a α, T.fail, 0)
  | .write ((i, γ) :: as) ls => (O.put i γ, ⟨T.todo, .write as ls⟩, 0)
  | .write [] ((p, q) :: ls) => (O.link p q, ⟨T.todo, .write [] ls⟩, 0)
  | .write [] [] => (O, ⟨O.cells, .idle⟩, 0)

/-- **On memories that answer alike, the action on ordered maps alone is
the action on the ordered memory**: the same thread, the same claim, and
memories that answer alike again. -/
theorem OMach.act_agree (xs : XSys S) {O : OMem S} {H : TMem S} (h : O.Agree H)
    (T : TThread S) :
    (OMach.act xs O T).1.Agree (TMach.act xs H T).1 ∧
      (OMach.act xs O T).2 = (TMach.act xs H T).2 := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold OMach.act TMach.act
    dsimp only
    rw [tmaxC_fst]
    cases todo.maxKey? with
    | none => exact ⟨h, rfl⟩
    | some s =>
      dsimp only
      cases todo[s]? with
      | none => exact ⟨h, rfl⟩
      | some e =>
        dsimp only
        rw [h.sym]
        by_cases hc : H.sym e.1 = some e.2
        · rw [ite_pos' hc, ite_pos' hc]
          exact ⟨h, rfl⟩
        · rw [ite_neg' hc, ite_neg' hc]
          exact ⟨h, rfl⟩
  | look a α =>
    unfold OMach.act TMach.act
    dsimp only
    rw [h.nb]
    cases (H.nb (a, 0)).head? with
    | none => exact ⟨h, rfl⟩
    | some q => exact ⟨h, rfl⟩
  | seek a α p c =>
    unfold OMach.act TMach.act
    dsimp only
    rw [h.sym, h.nb]
    cases (if c.2 = 0 then H.sym c.1 else none) with
    | some β =>
      dsimp only
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β).isSome
      · rw [ite_pos' hc, ite_pos' hc]
        exact ⟨h, rfl⟩
      · rw [ite_neg' hc, ite_neg' hc]
        exact ⟨h, rfl⟩
    | none =>
      dsimp only
      cases (H.nb c).find? (fun q => decide (q ≠ p)) with
      | none => exact ⟨h, rfl⟩
      | some q => exact ⟨h, rfl⟩
  | ready a b α β =>
    unfold OMach.act TMach.act
    dsimp only
    rw [h.sym]
    by_cases hc : H.sym a = some α
    · rw [ite_pos' hc, ite_pos' hc]
      exact ⟨h.take a, rfl⟩
    · rw [ite_neg' hc, ite_neg' hc]
      exact ⟨h, rfl⟩
  | half a b α β =>
    unfold OMach.act TMach.act
    dsimp only
    rw [h.sym]
    cases (if H.sym b = some β ∧ a ≠ b then xs.rule α β else none) with
    | none => exact ⟨h.put a α, rfl⟩
    | some R => exact ⟨h.take b, rfl⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨h.put i γ, rfl⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨h.link p q, rfl⟩
      | nil =>
        refine ⟨h, ?_⟩
        show ((⟨O.cells, .idle⟩ : TThread S), 0) = ((⟨H.cells, .idle⟩ : TThread S), 0)
        rw [h.cells]

/-- The state of the program on ordered maps alone. -/
structure OMach (S : Type) where
  mem : OMem S
  ths : List (TThread S)

/-- The program on lists that it stands for. -/
def OMach.toX (M : OMach S) : XMach S := ⟨M.mem.toX, M.ths.map TThread.toX⟩

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def OMach.step (xs : XSys S) (M : OMach S) (t : Nat) : OMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(OMach.act xs M.mem T).1, M.ths.set t (OMach.act xs M.mem T).2.1⟩,
      (OMach.act xs M.mem T).2.2)
  | none => (M, 0)

/-- The run under an unending schedule. -/
def OMach.trace (xs : XSys S) (σ : Nat → Nat) (M : OMach S) : Nat → OMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((OMach.trace xs σ M i).1.step xs (σ i)).1,
      (OMach.trace xs σ M i).2 + ((OMach.trace xs σ M i).1.step xs (σ i)).2)

/-- The program before it starts. -/
def OMach.init (X : XNet S) (n : Nat) : OMach S :=
  ⟨OMem.ofX X, (List.range n).map fun t =>
    ⟨treeOf (X.agents.drop t ++ X.agents.take t), .idle⟩⟩

/-- The two programs are in step: memories that answer alike, and the
same threads. -/
def OMach.Agree (M : OMach S) (N : TMach S) : Prop := M.mem.Agree N.mem ∧ M.ths = N.ths

theorem OMach.step_agree (xs : XSys S) {M : OMach S} {N : TMach S} (h : M.Agree N) (t : Nat) :
    (M.step xs t).1.Agree (N.step xs t).1 ∧ (M.step xs t).2 = (N.step xs t).2 := by
  obtain ⟨hm, ht⟩ := h
  unfold OMach.step TMach.step
  rw [ht]
  cases N.ths[t]? with
  | none => exact ⟨⟨hm, ht⟩, rfl⟩
  | some T =>
    obtain ⟨a, b⟩ := OMach.act_agree xs hm T
    refine ⟨⟨a, ?_⟩, ?_⟩
    · show N.ths.set t (OMach.act xs M.mem T).2.1 = N.ths.set t (TMach.act xs N.mem T).2.1
      rw [b]
    · show (OMach.act xs M.mem T).2.2 = (TMach.act xs N.mem T).2.2
      rw [b]

/-- **The two programs stay in step**, action by action, under any
schedule, and claim as often. -/
theorem OMach.trace_agree (xs : XSys S) (σ : Nat → Nat) {M : OMach S} {N : TMach S}
    (h : M.Agree N) :
    ∀ i, (M.trace xs σ i).1.Agree (N.trace xs σ i).1 ∧ (M.trace xs σ i).2 = (N.trace xs σ i).2
  | 0 => ⟨h, rfl⟩
  | i + 1 => by
    obtain ⟨a, b⟩ := OMach.trace_agree xs σ h i
    obtain ⟨c, d⟩ := OMach.step_agree xs a (σ i)
    refine ⟨c, ?_⟩
    show (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2 =
      (N.trace xs σ i).2 + ((N.trace xs σ i).1.step xs (σ i)).2
    rw [b, d]

omit [DecidableEq S] in
theorem OMach.init_agree (X : XNet S) (n : Nat) : (OMach.init X n).Agree (TMach.init X n) :=
  ⟨OMem.ofX_agree X, rfl⟩

omit [DecidableEq S] in
theorem OMach.Agree.toX {M : OMach S} {N : TMach S} (h : M.Agree N) : M.toX = N.toX := by
  obtain ⟨hm, ht⟩ := h
  show (⟨⟨treeList M.mem.cells, M.mem.free, M.mem.wires⟩, M.ths.map TThread.toX⟩ : XMach S) =
    ⟨⟨treeList N.mem.cells, N.mem.free, N.mem.wires⟩, N.ths.map TThread.toX⟩
  rw [hm.cells, hm.free, hm.wires, ht]

/-- **The program on ordered maps alone stands for the program on
lists**, action by action, under any schedule, and claims as often. -/
theorem OMach.init_sim {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((OMach.init X nt).trace xs σ i).1.toX = ((XMach.init X nt).trace xs σ i).1 ∧
      ((OMach.init X nt).trace xs σ i).2 = ((XMach.init X nt).trace xs σ i).2 := by
  obtain ⟨a, b⟩ := OMach.trace_agree xs σ (OMach.init_agree X nt) i
  obtain ⟨c, d, -⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
  exact ⟨a.toX.trans c, b.trans d⟩

/-- **Under a fair schedule the program on ordered maps alone comes to
rest with the normal form.** -/
theorem OMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((OMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((OMach.init X nt).trace xs σ i).2 = n ∧
      ((OMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  obtain ⟨i₀, h⟩ := XMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨a, b⟩ := OMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((OMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- **The bound on the length of a fair run holds on ordered maps
alone.** -/
theorem OMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((n + 1) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((OMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((OMach.init X nt).trace xs σ i).2 = n ∧
      ((OMach.init X nt).trace xs σ i).1.mem.toX.toNet = N' := by
  intro i hi
  obtain ⟨a, b⟩ := OMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := XMach.fair_bound hX hnd hnt hb hs hn σ hfair i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((OMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

end AllOrdered

section NameSteps

open Std.DTreeMap.Internal

variable {V : Type}

/-- The depth of the tree of a map keyed by names. -/
def ndepth (t : Std.TreeMap (List Nat) V) : Nat := implDepth t.inner.inner

/-- It is under three times `lg` of the size, as for every map of the
library. -/
theorem ndepth_lt (t : Std.TreeMap (List Nat) V) : ndepth t < 3 * lg t.size :=
  depth_lt_of_pow (implDepth_pow t.inner.wf.balanced)

/-- The lookup of a name, with the count of its calls.  Each call compares
two names once. -/
def ngetC (t : Std.TreeMap (List Nat) V) (k : List Nat) : Option V × Nat :=
  implGetC t.inner.inner k

/-- The tree of an insertion at a name, with the count of the calls. -/
def ninsertC (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    Impl (List Nat) (fun _ => V) × Nat :=
  implInsertC k v t.inner.inner

/-- The tree of an erasure at a name, with the count of the calls. -/
def neraseC (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    Impl (List Nat) (fun _ => V) × Nat :=
  implEraseC k t.inner.inner

theorem ngetC_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) : (ngetC t k).1 = t[k]? :=
  implGetC_fst t.inner.inner k

theorem ninsertC_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    (ninsertC t k v).1 = (t.insert k v).inner.inner := by
  show (implInsertC k v t.inner.inner).1 =
    (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl
  rw [implInsertC_fst, Impl.insert_eq_insert!]

theorem neraseC_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (neraseC t k).1 = (t.erase k).inner.inner := by
  show (implEraseC k t.inner.inner).1 = (Impl.erase k t.inner.inner t.inner.wf.balanced).impl
  rw [implEraseC_fst, Impl.erase_eq_erase!]

theorem ngetC_snd (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (ngetC t k).2 ≤ ndepth t + 1 :=
  implGetC_snd t.inner.inner k

theorem ninsertC_snd (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    (ninsertC t k v).2 ≤ ndepth t + 1 :=
  implInsertC_snd (β := fun _ => V) k v t.inner.inner

theorem neraseC_snd (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (neraseC t k).2 ≤ ndepth t + 1 :=
  implEraseC_snd k t.inner.inner

end NameSteps

section AllOrderedCost

variable [DecidableEq S] {xs : XSys S}

/-- **The sizes of the three maps.**  The stamps are below the next stamp,
the map of the names is no larger than the map of the agents, and the map
of the neighbours has no more keys than there are segments. -/
structure OMem.Sized (O : OMem S) : Prop where
  lt : ∀ (k : Nat) v, O.cells[k]? = some v → k < O.stamp
  live : O.live.size ≤ O.cells.size
  nbrs : O.nbrs.size ≤ O.wires.length

omit [DecidableEq S] in
theorem OMem.Sized.take {O : OMem S} (h : O.Sized) (a : Id) : (O.take a).Sized := by
  unfold OMem.take
  cases hl : O.live[a]? with
  | none => exact h
  | some v =>
    refine ⟨fun k w hk => ?_, ?_, h.nbrs⟩
    · have hk' : (O.cells.erase v.1)[k]? = some w := hk
      rw [tget_erase] at hk'
      by_cases e : v.1 = k
      · rw [ite_pos' e] at hk'
        cases hk'
      · rw [ite_neg' e] at hk'
        exact h.lt k w hk'
    · show (O.live.erase a).size ≤ (O.cells.erase v.1).size
      have hc : O.live.contains a = true := by
        rw [Std.TreeMap.contains_eq_isSome_getElem?, hl]
        rfl
      have h₁ : (O.live.erase a).size = O.live.size - 1 := by
        rw [Std.TreeMap.size_erase, ite_pos' hc]
      have h₂ : O.cells.size - 1 ≤ (O.cells.erase v.1).size := by
        rw [Std.TreeMap.size_erase]
        split <;> omega
      have h₃ := h.live
      omega

omit [DecidableEq S] in
theorem OMem.Sized.put {O : OMem S} (h : O.Sized) (i : Id) (γ : S) : (O.put i γ).Sized := by
  refine ⟨fun k w hk => ?_, ?_, h.nbrs⟩
  · have hk' : (O.cells.insert O.stamp (i, γ))[k]? = some w := hk
    rw [tget_insert] at hk'
    show k < O.stamp + 1
    by_cases e : O.stamp = k
    · omega
    · rw [ite_neg' e] at hk'
      have := h.lt k w hk'
      omega
  · show (O.live.insert i (O.stamp, γ)).size ≤ (O.cells.insert O.stamp (i, γ)).size
    have h₁ := Std.TreeMap.size_insert_le (t := O.live) (k := i) (v := (O.stamp, γ))
    have hc : O.cells.contains O.stamp = false := by
      rw [Std.TreeMap.contains_eq_isSome_getElem?]
      cases hg : O.cells[O.stamp]? with
      | none => rfl
      | some w => exact absurd (h.lt _ w hg) (Nat.lt_irrefl _)
    have h₂ : (O.cells.insert O.stamp (i, γ)).size = O.cells.size + 1 := by
      rw [Std.TreeMap.size_insert, hc]
      rfl
    have h₃ := h.live
    omega

omit [DecidableEq S] in
theorem OMem.Sized.link {O : OMem S} (h : O.Sized) (p q : Port) : (O.link p q).Sized := by
  refine ⟨h.lt, h.live, ?_⟩
  show (O.nbrs.insert (portKey p) (pushNb q (O.nb p))).size ≤ O.wires.length + 1
  have h₁ := Std.TreeMap.size_insert_le (t := O.nbrs) (k := portKey p)
    (v := pushNb q (O.nb p))
  have h₂ := h.nbrs
  omega

omit [DecidableEq S] in
theorem OMem.empty_sized (free : List Port) : (OMem.empty free : OMem S).Sized := by
  refine ⟨fun k v hk => ?_, Nat.le_of_eq rfl, Nat.le_of_eq rfl⟩
  have hk' : (∅ : Std.TreeMap Nat (Id × S))[k]? = some v := hk
  rw [tget_empty] at hk'
  cases hk'

omit [DecidableEq S] in
theorem OMem.ofX_sized (X : XNet S) : (OMem.ofX X).Sized := by
  have hp : ∀ (l : List (Id × S)) {O : OMem S}, O.Sized →
      (l.foldr (fun e O => O.put e.1 e.2) O).Sized := by
    intro l O h
    induction l with
    | nil => exact h
    | cons e l ih => exact ih.put e.1 e.2
  have hl : ∀ (l : List (Port × Port)) {O : OMem S}, O.Sized →
      (l.foldr (fun e O => O.link e.1 e.2) O).Sized := by
    intro l O h
    induction l with
    | nil => exact h
    | cons e l ih => exact ih.link e.1 e.2
  exact hl X.wires (hp X.agents (OMem.empty_sized X.free))

/-- An action keeps the sizes. -/
theorem OMach.act_sized (xs : XSys S) {O : OMem S} (h : O.Sized) (T : TThread S) :
    (OMach.act xs O T).1.Sized := by
  obtain ⟨todo, s⟩ := T
  cases s with
  | idle =>
    unfold OMach.act
    dsimp only
    repeat' split
    all_goals exact h
  | look a α =>
    unfold OMach.act
    dsimp only
    repeat' split
    all_goals exact h
  | seek a α p c =>
    unfold OMach.act
    dsimp only
    repeat' split
    all_goals exact h
  | ready a b α β =>
    unfold OMach.act
    dsimp only
    split
    · exact h.take a
    · exact h
  | half a b α β =>
    unfold OMach.act
    dsimp only
    split
    · exact h.take b
    · exact h.put a α
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact h.put i γ
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact h.link p q
      | nil => exact h

theorem OMach.step_sized (xs : XSys S) {M : OMach S} (h : M.mem.Sized) (t : Nat) :
    (M.step xs t).1.mem.Sized := by
  unfold OMach.step
  cases M.ths[t]? with
  | none => exact h
  | some T => exact OMach.act_sized xs h T

theorem OMach.trace_sized (xs : XSys S) (σ : Nat → Nat) {M : OMach S} (h : M.mem.Sized) :
    ∀ i, (M.trace xs σ i).1.mem.Sized
  | 0 => h
  | i + 1 => OMach.step_sized xs (OMach.trace_sized xs σ h i) (σ i)

/-- **The segments of the memory are never more than those of the net and
`D` for each interaction.** -/
theorem XMach.wires_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (i : Nat) :
    ((XMach.init X nt).trace xs σ i).1.mem.wires.length ≤ X.wires.length + D * n := by
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
  have hK : ((XMach.init X nt).trace xs σ i).1.segs ≤ X.wires.length + D * n :=
    Nat.le_trans (sizes i).1 (Nat.add_le_add_left (Nat.mul_le_mul_left D (bound i)) _)
  exact Nat.le_trans (Nat.le_add_right _ _) hK

/-- The calls of looking a name up. -/
def OMem.symC (O : OMem S) (i : Id) : Nat := (ngetC O.live i).2

/-- The calls of looking the neighbours of a port up. -/
def OMem.nbC (O : OMem S) (p : Port) : Nat := (ngetC O.nbrs (portKey p)).2

/-- The calls of taking an agent out: one erasure in each map of the
agents. -/
def OMem.takeC (O : OMem S) (a : Id) : Nat :=
  match O.live[a]? with
  | some v => (teraseC O.cells v.1).2 + (neraseC O.live a).2
  | none => 0

/-- The calls of writing an agent: one insertion in each map of the
agents. -/
def OMem.putC (O : OMem S) (i : Id) (γ : S) : Nat :=
  (tinsertC O.cells O.stamp (i, γ)).2 + (ninsertC O.live i (O.stamp, γ)).2

/-- The calls of writing a segment: one lookup and one insertion in the
map of the neighbours. -/
def OMem.linkC (O : OMem S) (p q : Port) : Nat :=
  O.nbC p + (ninsertC O.nbrs (portKey p) (pushNb q (O.nb p))).2

/-- **What an action costs on ordered maps alone, every call counted.**
As `TMach.cost`: one for the action, one for each cell of a list of
neighbours it reads, one for each cell of a segment it writes; and for
each operation on a map, the calls it makes, whichever of the three maps
it is on.  A thread at rest costs nothing. -/
def OMach.ccost (xs : XSys S) (O : OMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match (tmaxC T.todo).1 with
    | none => 0
    | some s =>
      match T.todo[s]? with
      | some e =>
        1 + ((tmaxC T.todo).2 + (tgetC T.todo s).2 + (teraseC T.todo s).2) + O.symC e.1
      | none => 1 + ((tmaxC T.todo).2 + (tgetC T.todo s).2)
  | .look a _ => 2 + O.nbC (a, 0)
  | .seek _ _ p c =>
    if c.2 = 0 then
      1 + O.symC c.1 + if (O.sym c.1).isSome then 0 else O.nbC c + findCells p (O.nb c)
    else 1 + O.nbC c + findCells p (O.nb c)
  | .ready a _ α _ => 1 + O.symC a + if O.sym a = some α then O.takeC a else 0
  | .half a b α β =>
    1 + O.symC b + if O.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          O.takeC b + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => O.putC a α
      else O.putC a α
  | .write ((i, γ) :: _) _ => 1 + O.putC i γ
  | .write [] ((p, q) :: _) => 4 + O.linkC p q
  | .write [] [] => 1

/-- **Every action costs the size of a rule, four, and four operations on
trees no deeper than `k` less one.** -/
theorem OMach.ccost_le {C D : Nat} (hb : xs.Bounded C D) (O : OMem S) (T : TThread S)
    {k : Nat} (hc : tdepth O.cells + 1 ≤ k) (hl : ndepth O.live + 1 ≤ k)
    (hn : ndepth O.nbrs + 1 ≤ k) (ht : tdepth T.todo + 1 ≤ k)
    (hf : ∀ p c, findCells p (O.nb c) ≤ 2) :
    OMach.ccost xs O T ≤ (C + D + 4 + 4 * k) * T.toX.busy := by
  have sym_le : ∀ i, O.symC i ≤ k := fun i => Nat.le_trans (ngetC_snd O.live i) hl
  have nb_le : ∀ p, O.nbC p ≤ k := fun p => Nat.le_trans (ngetC_snd O.nbrs (portKey p)) hn
  have take_le : ∀ a, O.takeC a ≤ 2 * k := by
    intro a
    unfold OMem.takeC
    cases O.live[a]? with
    | none => exact Nat.zero_le _
    | some v =>
      have h₁ := teraseC_snd O.cells v.1
      have h₂ := neraseC_snd O.live a
      show (teraseC O.cells v.1).2 + (neraseC O.live a).2 ≤ 2 * k
      omega
  have put_le : ∀ i γ, O.putC i γ ≤ 2 * k := by
    intro i γ
    have h₁ := tinsertC_snd O.cells O.stamp (i, γ)
    have h₂ := ninsertC_snd O.live i (O.stamp, γ)
    show (tinsertC O.cells O.stamp (i, γ)).2 + (ninsertC O.live i (O.stamp, γ)).2 ≤ 2 * k
    omega
  have link_le : ∀ p q, O.linkC p q ≤ 2 * k := by
    intro p q
    have h₁ := nb_le p
    have h₂ := ninsertC_snd O.nbrs (portKey p) (pushNb q (O.nb p))
    show O.nbC p + (ninsertC O.nbrs (portKey p) (pushNb q (O.nb p))).2 ≤ 2 * k
    omega
  obtain ⟨todo, s⟩ := T
  have ht' : tdepth todo + 1 ≤ k := ht
  cases s with
  | idle =>
    cases hmax : (tmaxC todo).1 with
    | none =>
      have e : OMach.ccost xs O ⟨todo, .idle⟩ = 0 := by
        unfold OMach.ccost
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
      have h₁ := tmaxC_snd todo
      have h₂ := tgetC_snd todo s
      have h₃ := teraseC_snd todo s
      have e : OMach.ccost xs O ⟨todo, .idle⟩ =
          match todo[s]? with
          | some e =>
            1 + ((tmaxC todo).2 + (tgetC todo s).2 + (teraseC todo s).2) + O.symC e.1
          | none => 1 + ((tmaxC todo).2 + (tgetC todo s).2) := by
        unfold OMach.ccost
        dsimp only
        rw [hmax]
      rw [e, eb]
      cases todo[s]? with
      | none =>
        show 1 + ((tmaxC todo).2 + (tgetC todo s).2) ≤ (C + D + 4 + 4 * k) * 1
        omega
      | some e =>
        have h₄ := sym_le e.1
        show 1 + ((tmaxC todo).2 + (tgetC todo s).2 + (teraseC todo s).2) + O.symC e.1 ≤
          (C + D + 4 + 4 * k) * 1
        omega
  | look a α =>
    have h₁ := nb_le (a, 0)
    show 2 + O.nbC (a, 0) ≤ (C + D + 4 + 4 * k) * 1
    omega
  | seek a α p c =>
    have h₁ := sym_le c.1
    have h₂ := nb_le c
    have h₃ := hf p c
    show (if c.2 = 0 then
        1 + O.symC c.1 + (if (O.sym c.1).isSome then 0 else O.nbC c + findCells p (O.nb c))
      else 1 + O.nbC c + findCells p (O.nb c)) ≤ (C + D + 4 + 4 * k) * 1
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    have h₁ := sym_le a
    have h₂ := take_le a
    show 1 + O.symC a + (if O.sym a = some α then O.takeC a else 0) ≤ (C + D + 4 + 4 * k) * 1
    split <;> omega
  | half a b α β =>
    have h₁ := sym_le b
    have h₂ := take_le b
    have h₃ := put_le a α
    have eb : (TThread.toX (⟨todo, .half a b α β⟩ : TThread S)).busy = 1 := rfl
    rw [eb]
    unfold OMach.ccost
    dsimp only
    split
    · split
      · rename_i R hR
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl' := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        show 1 + O.symC b + (O.takeC b + (R.newAgents a b).length +
          (R.newLinks xs.sys.ar a b α β).length) ≤ (C + D + 4 + 4 * k) * 1
        omega
      · show 1 + O.symC b + O.putC a α ≤ (C + D + 4 + 4 * k) * 1
        omega
    · show 1 + O.symC b + O.putC a α ≤ (C + D + 4 + 4 * k) * 1
      omega
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have h₁ := put_le i γ
      show 1 + O.putC i γ ≤ (C + D + 4 + 4 * k) * 1
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have h₁ := link_le p q
        show 4 + O.linkC p q ≤ (C + D + 4 + 4 * k) * 1
        omega
      | nil =>
        show 1 ≤ (C + D + 4 + 4 * k) * 1
        omega

/-- What the action of thread `t` costs, every call counted. -/
def OMach.stepCcost (xs : XSys S) (M : OMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => OMach.ccost xs M.mem T
  | none => 0

/-- **The running time on ordered maps alone, every call counted.** -/
def OMach.ctime (xs : XSys S) (σ : Nat → Nat) (M : OMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => OMach.ctime xs σ M i + (M.trace xs σ i).1.stepCcost xs (σ i)

/-- **The time on ordered maps alone, every call on a map counted.**
Under the hypotheses of `IMach.time_bound`, on every run the time is at
most

    C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n))

for each action that is not a rest: four operations at most, each on a
tree under three times as deep as `lg` of what the memory can hold, agents
and segments together.  No operation is counted one on the strength of a
hash. -/
theorem OMach.ctime_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (OMach.init X nt).ctime xs σ i ≤
      (C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n))) *
        (XMach.init X nt).work xs σ i := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have htodo := TMach.todo_le (xs := xs) hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨⟨am, at'⟩, -⟩ := OMach.trace_agree xs σ (OMach.init_agree X nt) i
    obtain ⟨a, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨hA, -, -⟩ := hΦ i
    replace hA := Nat.le_trans hA
      (Nat.add_le_add_left (Nat.mul_le_mul_right n (Nat.sub_le C 2)) _)
    have hW := XMach.wires_le (xs := xs) hX hnt hb hs hn σ i
    have sz := OMach.trace_sized xs σ (M := OMach.init X nt) (OMem.ofX_sized X) i
    have emem : ((TMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    have hm : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
        (((OMach.init X nt).trace xs σ i).1.ths[σ i]?).map TThread.toX := by
      rw [← a, at']
      show (((TMach.init X nt).trace xs σ i).1.ths.map TThread.toX)[σ i]? = _
      rw [List.getElem?_map]
    have hcells : ((OMach.init X nt).trace xs σ i).1.mem.cells.size ≤
        X.agents.length + C * n := by
      rw [am.cells, ← treeList_length]
      show ((TMach.init X nt).trace xs σ i).1.mem.toX.agents.length ≤ _
      rw [emem]
      exact hA
    have hwires : ((OMach.init X nt).trace xs σ i).1.mem.wires.length ≤
        X.wires.length + D * n := by
      rw [am.wires]
      show ((TMach.init X nt).trace xs σ i).1.mem.toX.wires.length ≤ _
      rw [emem]
      exact hW
    have hlive := sz.live
    have hnbrs := sz.nbrs
    have d₁ := tdepth_lt ((OMach.init X nt).trace xs σ i).1.mem.cells
    have d₂ := ndepth_lt ((OMach.init X nt).trace xs σ i).1.mem.live
    have d₃ := ndepth_lt ((OMach.init X nt).trace xs σ i).1.mem.nbrs
    have m₁ := lg_mono (Nat.le_trans hcells
      (Nat.le_add_right _ (X.wires.length + D * n)))
    have m₂ := lg_mono (Nat.le_trans (Nat.le_trans hlive hcells)
      (Nat.le_add_right _ (X.wires.length + D * n)))
    have m₃ := lg_mono (Nat.le_trans (Nat.le_trans hnbrs hwires)
      (Nat.le_add_left _ (X.agents.length + C * n)))
    have hfc : ∀ p c, findCells p (((OMach.init X nt).trace xs σ i).1.mem.nb c) ≤ 2 := by
      intro p c
      rw [am.nb c, ok.nbrs c]
      exact findCells_nbOf _ c p
    have hstep : ((OMach.init X nt).trace xs σ i).1.stepCcost xs (σ i) ≤
        (C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n))) *
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i) := by
      unfold OMach.stepCcost XMach.stepTally
      rw [hm]
      cases hT : ((OMach.init X nt).trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.zero_le _
      | some T =>
        have hT' : ((TMach.init X nt).trace xs σ i).1.ths[σ i]? = some T := by
          rw [← at']
          exact hT
        have m₄ := lg_mono (Nat.le_trans (htodo i T (List.mem_of_getElem? hT'))
          (Nat.le_add_right _ (X.wires.length + D * n)))
        have d₄ := tdepth_lt T.todo
        have e : C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n)) =
            C + D + 4 + 4 * (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))) := by
          omega
        show OMach.ccost xs ((OMach.init X nt).trace xs σ i).1.mem T ≤
          (C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n))) *
            T.toX.busy
        rw [e]
        exact OMach.ccost_le hb _ T (by omega) (by omega) (by omega) (by omega) hfc
    show (OMach.init X nt).ctime xs σ i +
        ((OMach.init X nt).trace xs σ i).1.stepCcost xs (σ i) ≤
      (C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n))) *
        ((XMach.init X nt).work xs σ i +
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i))
    rw [Nat.mul_add]
    omega

/-- **A bound on the running time on ordered maps alone, every call
counted, whatever the schedule.** -/
theorem OMach.ctime_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) (i : Nat) :
    (OMach.init X nt).ctime xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) *
        (C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n))) := by
  have h₁ := OMach.ctime_le_work (xs := xs) hX hnd hnt hb hs hn σ i
  have h₂ := Nat.mul_le_mul_left
    (C + D + 4 + 12 * lg (X.agents.length + C * n + (X.wires.length + D * n)))
    (XMach.work_le hX hnd hnt hb hs hn σ i)
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  omega

end AllOrderedCost

section AllOrderedRest

variable [DecidableEq S] {xs : XSys S}

/-- Every thread rests: nothing in hand and an empty map. -/
def OMach.resting (M : OMach S) : Bool :=
  M.ths.all fun T => (tmaxC T.todo).1.isNone && T.st.isIdle

omit [DecidableEq S] in
theorem OMach.rest_thread {M : OMach S} (h : M.resting = true) {t : Nat} {T : TThread S}
    (hT : M.ths[t]? = some T) : ∃ todo, T = ⟨todo, .idle⟩ ∧ (tmaxC todo).1 = none := by
  have hr := List.all_eq_true.1 h T (List.mem_of_getElem? hT)
  obtain ⟨todo, st⟩ := T
  have hr' : ((tmaxC todo).1.isNone && st.isIdle) = true := hr
  rw [Bool.and_eq_true] at hr'
  obtain ⟨h₁, h₂⟩ := hr'
  refine ⟨todo, ?_, Option.isNone_iff_eq_none.1 h₁⟩
  cases st with
  | idle => rfl
  | look a α => cases h₂
  | seek a α p c => cases h₂
  | ready a b α β => cases h₂
  | half a b α β => cases h₂
  | write as ls => cases h₂

/-- A program at rest stays as it is. -/
theorem OMach.step_rest (xs : XSys S) {M : OMach S} (h : M.resting = true) (t : Nat) :
    M.step xs t = (M, 0) := by
  unfold OMach.step
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := OMach.rest_thread h hT
    have e : OMach.act xs M.mem ⟨todo, .idle⟩ = (M.mem, ⟨todo, .idle⟩, 0) := by
      unfold OMach.act
      dsimp only
      rw [hmax]
    show ((⟨(OMach.act xs M.mem ⟨todo, .idle⟩).1,
      M.ths.set t (OMach.act xs M.mem ⟨todo, .idle⟩).2.1⟩ : OMach S),
        (OMach.act xs M.mem ⟨todo, .idle⟩).2.2) = (M, 0)
    rw [e]
    show ((⟨M.mem, M.ths.set t ⟨todo, .idle⟩⟩ : OMach S), 0) = (M, 0)
    rw [set_self M.ths t _ hT]

theorem OMach.trace_rest (σ : Nat → Nat) {M : OMach S} {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) : ∀ d, M.trace xs σ (B + d) = M.trace xs σ B
  | 0 => rfl
  | d + 1 => by
    show (((M.trace xs σ (B + d)).1.step xs (σ (B + d))).1,
      (M.trace xs σ (B + d)).2 + ((M.trace xs σ (B + d)).1.step xs (σ (B + d))).2) = _
    rw [OMach.trace_rest σ h d, OMach.step_rest xs h] <;> rfl

theorem OMach.stepCcost_rest (xs : XSys S) {M : OMach S} (h : M.resting = true) (t : Nat) :
    M.stepCcost xs t = 0 := by
  unfold OMach.stepCcost
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := OMach.rest_thread h hT
    show OMach.ccost xs M.mem ⟨todo, .idle⟩ = 0
    unfold OMach.ccost
    dsimp only
    rw [hmax]

/-- Once the program is at rest its time stays what it is. -/
theorem OMach.ctime_rest (σ : Nat → Nat) {M : OMach S} {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) : ∀ d, M.ctime xs σ (B + d) = M.ctime xs σ B
  | 0 => rfl
  | d + 1 => by
    have z : (M.trace xs σ (B + d)).1.stepCcost xs (σ (B + d)) = 0 := by
      rw [OMach.trace_rest σ h d]
      exact OMach.stepCcost_rest xs h _
    show M.ctime xs σ (B + d) + (M.trace xs σ (B + d)).1.stepCcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact OMach.ctime_rest σ h d

end AllOrderedRest

end INet
