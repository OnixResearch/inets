import InteractionNets.Lazy

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### Packing the log

With lazy lists the log keeps every cell ever written.  Here the memory
counts its live cells and the length of its log, and drops the dead cells
of the log as soon as they are more than half of it.  The threads keep the
lists they took: a list is not changed when the log is packed, and the
notes of the deaths stay.  The log is then never more than twice the
agents, a thread that takes the agents afresh finds at most as many dead
cells as live ones, and the packing is paid for by the agents taken out. -/

section Packed

variable [DecidableEq S]

/-- Drop the dead cells of the log; the notes of the deaths stay, for the
threads that still hold the old log. -/
def LMem.pack (L : LMem S) : LMem S := ⟨L.core.pack, L.dead⟩

theorem LMem.toX_pack (L : LMem S) : L.pack.toX = L.toX := L.core.toX_pack

theorem LMem.Ok.pack {L : LMem S} (h : L.Ok) : L.pack.Ok :=
  ⟨h.core.pack,
    fun c hc c' hc' e => h.uniq c (List.mem_filter.1 hc).1 c' (List.mem_filter.1 hc').1 e,
    h.born, fun s i γ hc => h.gone s i γ (List.mem_filter.1 hc).1⟩

omit [DecidableEq S] in
theorem LMem.Keeps.trans {L L' L'' : LMem S} (k₁ : L.Keeps L') (k₂ : L'.Keeps L'') :
    L.Keeps L'' :=
  ⟨Nat.le_trans k₁.stamp k₂.stamp, fun t₀ ht c =>
    (k₂.seen t₀ (Nat.le_trans ht k₁.stamp) c).trans (k₁.seen t₀ ht c)⟩

theorem LMem.Keeps.pack (L : LMem S) : L.Keeps L.pack :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

omit [DecidableEq S] in
/-- Taking out an agent that is listed once makes the list one shorter. -/
theorem filter_ne_length {a : Id} {α : S} : ∀ l : List (Id × S), (l.map Prod.fst).Nodup →
    assoc a l = some α → (l.filter fun e => decide (e.1 ≠ a)).length + 1 = l.length
  | [], _, h => by cases h
  | (k, v) :: l, hnd, h => by
    have hnd' : k ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    by_cases hk : k = a
    · rw [List.filter_cons_of_neg (by simpa using hk)]
      have e : l.filter (fun e => decide (e.1 ≠ a)) = l :=
        List.filter_eq_self.2 fun e he => by
          have hm : e.1 ∈ l.map Prod.fst := List.mem_map_of_mem he
          have : e.1 ≠ a := fun h' => hnd'.1 (hk ▸ h' ▸ hm)
          simpa using this
      rw [e]
      rfl
    · have h' : (if k = a then some v else assoc a l) = some α := h
      rw [ite_neg' hk] at h'
      rw [List.filter_cons_of_pos (by simpa using hk)]
      show (l.filter fun e => decide (e.1 ≠ a)).length + 1 + 1 = l.length + 1
      rw [filter_ne_length l hnd'.2 h']

/-- **A memory with lazy lists that packs its log**: the lazy memory, with
the number of live cells and the length of the log kept at hand. -/
structure PMem (S : Type) where
  mem : LMem S
  live : Nat
  cells : Nat

/-- Pack the log if more than half of it is dead. -/
def PMem.settle (P : PMem S) : PMem S :=
  if 2 * P.live < P.cells then ⟨P.mem.pack, P.live, P.live⟩ else P

/-- Take an agent out, and pack the log if more than half of it is dead
now. -/
def PMem.take (P : PMem S) (a : Id) : PMem S :=
  PMem.settle ⟨P.mem.take a, P.live - 1, P.cells⟩

/-- Write an agent. -/
def PMem.put (P : PMem S) (i : Id) (γ : S) : PMem S :=
  ⟨P.mem.put i γ, P.live + 1, P.cells + 1⟩

/-- Write a segment. -/
def PMem.link (P : PMem S) (p q : Port) : PMem S := ⟨P.mem.link p q, P.live, P.cells⟩

/-- The lazy memory is right, the two numbers are what they are said to
be, and at most half of the log is dead. -/
structure PMem.Ok (P : PMem S) : Prop where
  mem : P.mem.Ok
  cells : P.cells = P.mem.core.log.length
  live : P.live = P.mem.toX.agents.length
  half : P.cells ≤ 2 * P.live

theorem PMem.settle_spec {P : PMem S} (hm : P.mem.Ok) (hc : P.cells = P.mem.core.log.length)
    (hl : P.live = P.mem.toX.agents.length) :
    P.settle.Ok ∧ P.settle.mem.toX = P.mem.toX ∧ P.mem.Keeps P.settle.mem := by
  unfold PMem.settle
  split
  · refine ⟨⟨hm.pack, ?_, ?_, ?_⟩, P.mem.toX_pack, LMem.Keeps.pack P.mem⟩
    · show P.live = P.mem.core.pack.log.length
      rw [IMem.pack_length]
      exact hl
    · show P.live = P.mem.pack.toX.agents.length
      rw [P.mem.toX_pack]
      exact hl
    · show P.live ≤ 2 * P.live
      omega
  · rename_i hn
    exact ⟨⟨hm, hc, hl, Nat.le_of_not_lt hn⟩, rfl, LMem.Keeps.refl P.mem⟩

theorem PMem.take_live (P : PMem S) (a : Id) : (P.take a).live = P.live - 1 := by
  unfold PMem.take PMem.settle
  dsimp only
  split <;> rfl

theorem PMem.take_cells (P : PMem S) (a : Id) :
    (P.take a).cells = if 2 * (P.live - 1) < P.cells then P.live - 1 else P.cells := by
  unfold PMem.take PMem.settle
  dsimp only
  split <;> rfl

/-- Taking out an agent that is in memory, once: the memory stays right,
it stands for the list without the agent, it keeps what earlier clocks
saw, and it has one live cell less. -/
theorem PMem.Ok.take {P : PMem S} (h : P.Ok) (hnd : (P.mem.toX.agents.map Prod.fst).Nodup)
    {a : Id} {α : S} (ha : assoc a P.mem.toX.agents = some α) :
    (P.take a).Ok ∧ (P.take a).mem.toX = P.mem.toX.takeAgent a ∧
      P.mem.Keeps (P.take a).mem ∧ (P.take a).live + 1 = P.live := by
  have etx : (P.mem.take a).toX = P.mem.toX.takeAgent a := P.mem.core.toX_take a
  have hlen := filter_ne_length P.mem.toX.agents hnd ha
  have hl : P.live - 1 = (P.mem.take a).toX.agents.length := by
    rw [etx]
    have := h.live
    show P.live - 1 = (P.mem.toX.agents.filter fun e => decide (e.1 ≠ a)).length
    omega
  obtain ⟨o, tx, k⟩ := PMem.settle_spec (P := ⟨P.mem.take a, P.live - 1, P.cells⟩)
    (h.mem.take a) h.cells hl
  refine ⟨o, tx.trans etx, (LMem.Keeps.take h.mem a).trans k, ?_⟩
  rw [PMem.take_live]
  have := h.live
  omega

theorem PMem.Ok.put {P : PMem S} (h : P.Ok) {i : Id}
    (hi : assoc i P.mem.toX.agents = none) (γ : S) : (P.put i γ).Ok := by
  refine ⟨h.mem.put hi γ, ?_, ?_, ?_⟩
  · show P.cells + 1 = P.mem.core.log.length + 1
    rw [h.cells]
  · show P.live + 1 = (P.mem.core.put i γ).toX.agents.length
    rw [IMem.toX_put h.mem.core hi γ, h.live]
    rfl
  · show P.cells + 1 ≤ 2 * (P.live + 1)
    have := h.half
    omega

theorem PMem.Ok.link {P : PMem S} (h : P.Ok) (p q : Port) : (P.link p q).Ok :=
  ⟨h.mem.link p q, h.cells, h.live, h.half⟩

/-- **One action of a thread on the memory that packs its log**: the
action with lazy lists, on a memory that drops its dead cells as soon as
they are more than half of the log. -/
def PMach.act (xs : XSys S) (P : PMem S) (T : LThread S) : PMem S × LThread S × Nat :=
  match T.st with
  | .idle =>
    match T.raw.dropWhile (fun c => !P.mem.seen T.snap c) with
    | [] => (P, ⟨[], T.snap, .idle⟩, 0)
    | c :: rest =>
      if P.mem.core.sym c.2.1 = some c.2.2 then (P, ⟨rest, T.snap, .look c.2.1 c.2.2⟩, 0)
      else (P, ⟨rest, T.snap, .idle⟩, 0)
  | .look a α =>
    match (P.mem.core.nb (a, 0)).head? with
    | some q => (P, ⟨T.raw, T.snap, .seek a α (a, 0) q⟩, 0)
    | none => (P, T.fail, 0)
  | .seek a α p c =>
    match (if c.2 = 0 then P.mem.core.sym c.1 else none) with
    | some β =>
      if a ≠ c.1 ∧ (xs.rule α β).isSome then (P, ⟨T.raw, T.snap, .ready a c.1 α β⟩, 0)
      else (P, T.fail, 0)
    | none =>
      match (P.mem.core.nb c).find? (fun q => decide (q ≠ p)) with
      | some q => (P, ⟨T.raw, T.snap, .seek a α c q⟩, 0)
      | none => (P, T.fail, 0)
  | .ready a b α β =>
    if P.mem.core.sym a = some α then (P.take a, ⟨T.raw, T.snap, .half a b α β⟩, 0)
    else (P, T.fail, 0)
  | .half a b α β =>
    if P.mem.core.sym b = some β ∧ a ≠ b then
      match xs.rule α β with
      | some R =>
        (P.take b,
          ⟨T.raw, T.snap, .write (R.newAgents a b) (R.newLinks xs.sys.ar a b α β)⟩, 1)
      | none => (P.put a α, T.fail, 0)
    else (P.put a α, T.fail, 0)
  | .write ((i, γ) :: as) ls => (P.put i γ, ⟨T.raw, T.snap, .write as ls⟩, 0)
  | .write [] ((p, q) :: ls) => (P.link p q, ⟨T.raw, T.snap, .write [] ls⟩, 0)
  | .write [] [] => (P, ⟨P.mem.core.log, P.mem.core.stamp, .idle⟩, 0)

/-- **The action on the packing memory is the action of the program.** -/
theorem PMach.act_sim (xs : XSys S) {P : PMem S} (h : P.Ok) (T : LThread S)
    (hT : T.snap ≤ P.mem.core.stamp)
    (hnd0 : (P.mem.toX.agents.map Prod.fst).Nodup)
    (hnd : ((XMach.act xs P.mem.toX (T.toX P.mem)).1.agents.map Prod.fst).Nodup) :
    (PMach.act xs P T).1.mem.toX = (XMach.act xs P.mem.toX (T.toX P.mem)).1 ∧
      (PMach.act xs P T).2.1.toX (PMach.act xs P T).1.mem =
        (XMach.act xs P.mem.toX (T.toX P.mem)).2.1 ∧
      (PMach.act xs P T).2.2 = (XMach.act xs P.mem.toX (T.toX P.mem)).2.2 ∧
      (PMach.act xs P T).1.Ok ∧
      (PMach.act xs P T).2.1.snap ≤ (PMach.act xs P T).1.mem.core.stamp ∧
      P.mem.Keeps (PMach.act xs P T).1.mem := by
  obtain ⟨raw, snap, s⟩ := T
  have hT' : snap ≤ P.mem.core.stamp := hT
  have hm := h.mem
  cases s with
  | idle =>
    rcases dropWhile_not_spec (P.mem.seen snap) raw with ⟨hd, hf⟩ | ⟨c, rest, hd, -, hf⟩
    · have eL : PMach.act xs P ⟨raw, snap, .idle⟩ = (P, ⟨[], snap, .idle⟩, 0) := by
        unfold PMach.act
        dsimp only
        rw [hd]
      have eT : LThread.toX P.mem ⟨raw, snap, .idle⟩ = ⟨[], .idle⟩ := by
        show (⟨(raw.filter (P.mem.seen snap)).map (·.2), .idle⟩ : XThread S) = _
        rw [hf]
        rfl
      rw [eL, eT]
      exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
    · have eL : PMach.act xs P ⟨raw, snap, .idle⟩ =
          (if P.mem.core.sym c.2.1 = some c.2.2 then
            (P, ⟨rest, snap, .look c.2.1 c.2.2⟩, 0)
          else (P, ⟨rest, snap, .idle⟩, 0)) := by
        unfold PMach.act
        dsimp only
        rw [hd]
      have eT : LThread.toX P.mem ⟨raw, snap, .idle⟩ =
          ⟨c.2 :: (rest.filter (P.mem.seen snap)).map (·.2), .idle⟩ := by
        show (⟨(raw.filter (P.mem.seen snap)).map (·.2), .idle⟩ : XThread S) = _
        rw [hf]
        rfl
      have eX : XMach.act xs P.mem.toX
          ⟨c.2 :: (rest.filter (P.mem.seen snap)).map (·.2), .idle⟩ =
          (if assoc c.2.1 P.mem.toX.agents = some c.2.2 then
            (P.mem.toX, ⟨(rest.filter (P.mem.seen snap)).map (·.2), .look c.2.1 c.2.2⟩, 0)
          else (P.mem.toX, ⟨(rest.filter (P.mem.seen snap)).map (·.2), .idle⟩, 0)) := rfl
      rw [eL, eT, eX, hm.core.sym c.2.1]
      by_cases hs : assoc c.2.1 P.mem.toX.agents = some c.2.2
      · rw [ite_pos' hs, ite_pos' hs]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
      · rw [ite_neg' hs, ite_neg' hs]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
  | look a α =>
    have eT : LThread.toX P.mem ⟨raw, snap, .look a α⟩ =
        ⟨(raw.filter (P.mem.seen snap)).map (·.2), .look a α⟩ := rfl
    rw [eT]
    unfold PMach.act XMach.act
    dsimp only
    rw [hm.core.first (a, 0)]
    cases assoc (a, 0) P.mem.core.toX.wires <;>
      exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
  | seek a α p c =>
    have eT : LThread.toX P.mem ⟨raw, snap, .seek a α p c⟩ =
        ⟨(raw.filter (P.mem.seen snap)).map (·.2), .seek a α p c⟩ := rfl
    rw [eT]
    unfold PMach.act XMach.act
    dsimp only
    rw [hm.core.sym c.1, hm.core.next c p]
    cases (if c.2 = 0 then assoc c.1 P.mem.core.toX.agents else none) with
    | some β =>
      dsimp only
      by_cases hc : a ≠ c.1 ∧ (xs.rule α β).isSome
      · rw [ite_pos' hc, ite_pos' hc]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
      · rw [ite_neg' hc, ite_neg' hc]
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
    | none =>
      dsimp only
      cases nextSeg P.mem.core.toX.wires c p <;>
        exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
  | ready a b α β =>
    have eT : LThread.toX P.mem ⟨raw, snap, .ready a b α β⟩ =
        ⟨(raw.filter (P.mem.seen snap)).map (·.2), .ready a b α β⟩ := rfl
    rw [eT]
    unfold PMach.act XMach.act
    dsimp only
    rw [hm.core.sym a]
    by_cases hc : assoc a P.mem.core.toX.agents = some α
    · rw [ite_pos' hc, ite_pos' hc]
      obtain ⟨o, tx, k, -⟩ := h.take hnd0 hc
      exact ⟨tx, LThread.toX_keeps k hT', rfl, o, Nat.le_trans hT' k.stamp, k⟩
    · rw [ite_neg' hc, ite_neg' hc]
      exact ⟨rfl, rfl, rfl, h, hT', LMem.Keeps.refl _⟩
  | half a b α β =>
    have eT : LThread.toX P.mem ⟨raw, snap, .half a b α β⟩ =
        ⟨(raw.filter (P.mem.seen snap)).map (·.2), .half a b α β⟩ := rfl
    rw [eT] at hnd ⊢
    unfold XMach.act at hnd
    dsimp only at hnd
    unfold PMach.act XMach.act
    dsimp only
    rw [hm.core.sym b]
    by_cases hc : assoc b P.mem.core.toX.agents = some β ∧ a ≠ b
    · rw [ite_pos' hc, ite_pos' hc]
      rw [ite_pos' hc] at hnd
      cases hR : xs.rule α β with
      | some R =>
        obtain ⟨o, tx, k, -⟩ := h.take hnd0 hc.1
        exact ⟨tx, LThread.toX_keeps k hT', rfl, o, Nat.le_trans hT' k.stamp, k⟩
      | none =>
        rw [hR] at hnd
        have hi := assoc_none_of_nodup_cons hnd
        exact ⟨IMem.toX_put hm.core hi α, LThread.toX_keeps (.put P.mem a α) hT', rfl,
          h.put hi α, Nat.le_succ_of_le hT', .put P.mem a α⟩
    · rw [ite_neg' hc, ite_neg' hc]
      rw [ite_neg' hc] at hnd
      have hi := assoc_none_of_nodup_cons hnd
      exact ⟨IMem.toX_put hm.core hi α, LThread.toX_keeps (.put P.mem a α) hT', rfl,
        h.put hi α, Nat.le_succ_of_le hT', .put P.mem a α⟩
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have hi := assoc_none_of_nodup_cons hnd
      exact ⟨IMem.toX_put hm.core hi γ, LThread.toX_keeps (.put P.mem i γ) hT', rfl,
        h.put hi γ, Nat.le_succ_of_le hT', .put P.mem i γ⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨P.mem.core.toX_link p q, LThread.toX_keeps (.link P.mem p q) hT', rfl,
          h.link p q, hT', .link P.mem p q⟩
      | nil =>
        refine ⟨rfl, ?_, rfl, h, Nat.le_refl _, LMem.Keeps.refl _⟩
        show (⟨(P.mem.core.log.filter (P.mem.seen P.mem.core.stamp)).map (·.2), .idle⟩ :
          XThread S) = ⟨P.mem.core.toX.agents, .idle⟩
        rw [List.filter_congr (LMem.seen_now hm)]
        rfl

/-- The program with lazy lists on the memory that packs its log. -/
structure PMach (S : Type) where
  mem : PMem S
  ths : List (LThread S)

/-- The program on lists that it stands for. -/
def PMach.toX (M : PMach S) : XMach S :=
  ⟨M.mem.mem.toX, M.ths.map (LThread.toX M.mem.mem)⟩

/-- The memory is right and no thread took its list later than now. -/
structure PMach.Ok (M : PMach S) : Prop where
  mem : M.mem.Ok
  snap : ∀ T, T ∈ M.ths → T.snap ≤ M.mem.mem.core.stamp

/-- One action of thread `t`.  A thread that does not exist does nothing. -/
def PMach.step (xs : XSys S) (M : PMach S) (t : Nat) : PMach S × Nat :=
  match M.ths[t]? with
  | some T =>
    (⟨(PMach.act xs M.mem T).1, M.ths.set t (PMach.act xs M.mem T).2.1⟩,
      (PMach.act xs M.mem T).2.2)
  | none => (M, 0)

/-- The run under an unending schedule. -/
def PMach.trace (xs : XSys S) (σ : Nat → Nat) (M : PMach S) : Nat → PMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((PMach.trace xs σ M i).1.step xs (σ i)).1,
      (PMach.trace xs σ M i).2 + ((PMach.trace xs σ M i).1.step xs (σ i)).2)

/-- The program before it starts. -/
def PMach.init (X : XNet S) (n : Nat) : PMach S :=
  ⟨⟨LMem.ofX X, X.agents.length, X.agents.length⟩, (LMach.init X n).ths⟩

theorem PMach.init_ok {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (PMach.init X n).Ok := by
  obtain ⟨-, tx, len⟩ := IMem.ofX_toX hnd
  refine ⟨⟨(LMem.ofX_ok hnd).1, len.symm, ?_, ?_⟩, (LMach.init_ok hnd n).snap⟩
  · show X.agents.length = (IMem.ofX X).toX.agents.length
    rw [tx]
  · show X.agents.length ≤ 2 * X.agents.length
    omega

theorem PMach.init_toX {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (n : Nat) :
    (PMach.init X n).toX = XMach.init X n :=
  LMach.init_toX hnd n

/-- One action on the packing memory is one action of the program. -/
theorem PMach.step_sim (xs : XSys S) {M : PMach S} (h : M.Ok) (t : Nat)
    (hnd0 : (M.toX.mem.agents.map Prod.fst).Nodup)
    (hnd : ((M.toX.step xs t).1.mem.agents.map Prod.fst).Nodup) :
    (M.step xs t).1.toX = (M.toX.step xs t).1 ∧ (M.step xs t).2 = (M.toX.step xs t).2 ∧
      (M.step xs t).1.Ok := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold PMach.step
      rw [ht]
    have ht' : M.toX.ths[t]? = none := by
      show (M.ths.map (LThread.toX M.mem.mem))[t]? = none
      rw [List.getElem?_map, ht]
      rfl
    have e₂ : M.toX.step xs t = (M.toX, 0) := by
      unfold XMach.step
      rw [ht']
    rw [e₁, e₂]
    exact ⟨rfl, rfl, h⟩
  | some T =>
    have ht' : M.toX.ths[t]? = some (T.toX M.mem.mem) := by
      show (M.ths.map (LThread.toX M.mem.mem))[t]? = _
      rw [List.getElem?_map, ht]
      rfl
    have e₂ : M.toX.step xs t = (⟨(XMach.act xs M.mem.mem.toX (T.toX M.mem.mem)).1,
        (M.ths.map (LThread.toX M.mem.mem)).set t
          (XMach.act xs M.mem.mem.toX (T.toX M.mem.mem)).2.1⟩,
        (XMach.act xs M.mem.mem.toX (T.toX M.mem.mem)).2.2) := XMach.step_eq ht' rfl
    rw [e₂] at hnd
    have hTm := List.mem_of_getElem? ht
    obtain ⟨a, b, c, d, e, k⟩ := PMach.act_sim xs h.mem T (h.snap T hTm) hnd0 hnd
    have e₁ : M.step xs t = (⟨(PMach.act xs M.mem T).1,
        M.ths.set t (PMach.act xs M.mem T).2.1⟩, (PMach.act xs M.mem T).2.2) := by
      unfold PMach.step
      rw [ht]
    have em : M.ths.map (LThread.toX (PMach.act xs M.mem T).1.mem) =
        M.ths.map (LThread.toX M.mem.mem) :=
      List.map_congr_left fun U hU => LThread.toX_keeps k (h.snap U hU)
    rw [e₁, e₂]
    refine ⟨?_, c, d, fun U hU => ?_⟩
    · show (⟨(PMach.act xs M.mem T).1.mem.toX,
        (M.ths.set t (PMach.act xs M.mem T).2.1).map
          (LThread.toX (PMach.act xs M.mem T).1.mem)⟩ : XMach S) = _
      rw [List.map_set, em, a, b]
    · rcases List.mem_or_eq_of_mem_set hU with hU' | rfl
      · exact Nat.le_trans (h.snap U hU') k.stamp
      · exact e

variable {xs : XSys S}

/-- **The program on the packing memory runs as the program does.** -/
theorem PMach.trace_sim {M : PMach S} (h : M.Ok) (hL : M.toX.Live xs)
    (hnd : (M.toX.mem.agents.map Prod.fst).Nodup) (σ : Nat → Nat) :
    ∀ i, (M.trace xs σ i).1.toX = (M.toX.trace xs σ i).1 ∧
      (M.trace xs σ i).2 = (M.toX.trace xs σ i).2 ∧ (M.trace xs σ i).1.Ok := by
  have live := XMach.trace_live (xs := xs) σ hL
  have nd : ∀ i, ((M.toX.trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact XMach.step_nodup (live i) ih (σ i)
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl, h⟩
  | succ i ih =>
    obtain ⟨a, b, c⟩ := ih
    have hn0 : ((M.trace xs σ i).1.toX.mem.agents.map Prod.fst).Nodup := by
      rw [a]
      exact nd i
    have hn : (((M.trace xs σ i).1.toX.step xs (σ i)).1.mem.agents.map Prod.fst).Nodup := by
      rw [a]
      exact nd (i + 1)
    obtain ⟨a', b', c'⟩ := PMach.step_sim xs c (σ i) hn0 hn
    refine ⟨?_, ?_, c'⟩
    · show ((M.trace xs σ i).1.step xs (σ i)).1.toX = ((M.toX.trace xs σ i).1.step xs (σ i)).1
      rw [a', a]
    · show (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2 =
        (M.toX.trace xs σ i).2 + ((M.toX.trace xs σ i).1.step xs (σ i)).2
      rw [b', b, a]

/-- The run from a net: the program on the packing memory stands for the
program on lists at every action. -/
theorem PMach.init_sim {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((PMach.init X nt).trace xs σ i).1.toX = ((XMach.init X nt).trace xs σ i).1 ∧
      ((PMach.init X nt).trace xs σ i).2 = ((XMach.init X nt).trace xs σ i).2 ∧
      ((PMach.init X nt).trace xs σ i).1.Ok := by
  have e := PMach.init_toX hnd nt
  have hL : (PMach.init X nt).toX.Live xs := by
    rw [e]
    exact XMach.init_live hX hnt
  have hn : ((PMach.init X nt).toX.mem.agents.map Prod.fst).Nodup := by
    rw [e]
    exact hnd
  have k := PMach.trace_sim (PMach.init_ok hnd nt) hL hn σ i
  rw [e] at k
  exact k

/-- **Under a fair schedule the program on the packing memory comes to
rest with the normal form.** -/
theorem PMach.fair_complete {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i → ((PMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((PMach.init X nt).trace xs σ i).2 = n ∧
      ((PMach.init X nt).trace xs σ i).1.mem.mem.toX.toNet = N' := by
  obtain ⟨i₀, h⟩ := XMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨a, b, -⟩ := PMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((PMach.init X nt).trace xs σ i).1.mem.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- **The bound on the length of a fair run holds on the packing
memory.** -/
theorem PMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((n + 1) * X.passBound n C D + n * (C + D + 1) + 1) ≤ i →
      ((PMach.init X nt).trace xs σ i).1.toX.resting = true ∧
      ((PMach.init X nt).trace xs σ i).2 = n ∧
      ((PMach.init X nt).trace xs σ i).1.mem.mem.toX.toNet = N' := by
  intro i hi
  obtain ⟨a, b, -⟩ := PMach.init_sim hX hnd hnt σ i
  obtain ⟨r, c, m⟩ := XMach.fair_bound hX hnd hnt hb hs hn σ hfair i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [a]
    exact r
  · rw [b]
    exact c
  · have e : ((PMach.init X nt).trace xs σ i).1.mem.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    rw [e]
    exact m

/-- **The log is never more than twice the agents**: at every action of
every run, at most half of its cells are dead. -/
theorem PMach.log_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    ((PMach.init X nt).trace xs σ i).1.mem.mem.core.log.length ≤
      2 * ((XMach.init X nt).trace xs σ i).1.mem.agents.length := by
  obtain ⟨a, -, ok⟩ := PMach.init_sim (xs := xs) hX hnd hnt σ i
  have e : ((PMach.init X nt).trace xs σ i).1.mem.mem.toX =
      ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
  have h₁ := ok.mem.cells
  have h₂ := ok.mem.live
  have h₃ := ok.mem.half
  rw [e] at h₂
  omega

/-- No agent is in memory twice at any action of a run, if none was at the
start. -/
theorem XMach.init_nodup {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (((XMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup
  | 0 => hnd
  | i + 1 =>
    XMach.step_nodup (XMach.trace_live (xs := xs) σ (XMach.init_live hX hnt) i)
      (XMach.init_nodup hX hnd hnt σ i) (σ i)

/-- What taking an agent out costs: an erasure and a note of the time,
and, when the log is packed, the log read and the live cells written. -/
def PMem.takeCost (P : PMem S) : Nat :=
  2 + if 2 * (P.live - 1) < P.cells then P.cells + (P.live - 1) else 0

/-- **What an action costs on the packing memory**: as with lazy lists,
and the packing when an agent is taken out. -/
def PMach.cost (xs : XSys S) (P : PMem S) (T : LThread S) : Nat :=
  match T.st with
  | .idle =>
    idleCost (!(T.raw.dropWhile (fun c => !P.mem.seen T.snap c)).isEmpty)
      (T.raw.length - (T.raw.dropWhile (fun c => !P.mem.seen T.snap c)).length)
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then
      2 + if (P.mem.core.sym c.1).isSome then 0 else 1 + findCells p (P.mem.core.nb c)
    else 2 + findCells p (P.mem.core.nb c)
  | .ready a _ α _ => 2 + if P.mem.core.sym a = some α then P.takeCost else 0
  | .half a b α β =>
    2 + if P.mem.core.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          P.takeCost + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 2
      else 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- **Packing pays for itself.**  Count three for every dead cell in the
log.  Then an action that is not a rest costs at most the size of a rule
and eleven, and two for each dead cell an idle thread drops, with what it
adds to that count: the packing is paid by the dead cells it removes. -/
theorem PMach.cost_le {C D : Nat} (hb : xs.Bounded C D) {P : PMem S} (h : P.Ok)
    (T : LThread S) (hnd0 : (P.mem.toX.agents.map Prod.fst).Nodup) :
    PMach.cost xs P T + 3 * (PMach.act xs P T).1.cells + 3 * P.live ≤
      (C + D + 11) * (T.toX P.mem).busy + 2 * T.skips P.mem + 3 * P.cells +
        3 * (PMach.act xs P T).1.live := by
  obtain ⟨raw, snap, s⟩ := T
  have htake : ∀ {a : Id} {α : S}, assoc a P.mem.toX.agents = some α → ∀ k : Nat,
      k ≤ C + D → 2 + (P.takeCost + k) + 3 * (P.take a).cells + 3 * P.live ≤
        (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * (P.take a).live := by
    intro a α ha k hk
    obtain ⟨-, -, -, hl⟩ := h.take hnd0 ha
    rw [PMem.take_live] at hl
    unfold PMem.takeCost
    rw [PMem.take_cells, PMem.take_live]
    by_cases hp : 2 * (P.live - 1) < P.cells
    · rw [ite_pos' hp, ite_pos' hp]
      omega
    · rw [ite_neg' hp, ite_neg' hp]
      omega
  cases s with
  | idle =>
    have e : (PMach.act xs P ⟨raw, snap, .idle⟩).1 = P := by
      unfold PMach.act
      dsimp only
      split
      · rfl
      · split <;> rfl
    have hc := LMach.cost_le hb h.mem ⟨raw, snap, .idle⟩
    have ec : PMach.cost xs P ⟨raw, snap, .idle⟩ = LMach.cost xs P.mem ⟨raw, snap, .idle⟩ := rfl
    have hm := Nat.mul_le_mul_right (LThread.toX P.mem ⟨raw, snap, .idle⟩).busy
      (show C + D + 8 ≤ C + D + 11 by omega)
    rw [e, ec]
    omega
  | look a α =>
    have e : (PMach.act xs P ⟨raw, snap, .look a α⟩).1 = P := by
      unfold PMach.act
      dsimp only
      split <;> rfl
    rw [e]
    show 3 + 3 * P.cells + 3 * P.live ≤ (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * P.live
    omega
  | seek a α p c =>
    have e : (PMach.act xs P ⟨raw, snap, .seek a α p c⟩).1 = P := by
      unfold PMach.act
      dsimp only
      split
      · split <;> rfl
      · split <;> rfl
    have hf := findCells_nbOf P.mem.core.wires c p
    rw [← h.mem.core.nbrs c] at hf
    rw [e]
    show (if c.2 = 0 then 2 + (if (P.mem.core.sym c.1).isSome then 0
          else 1 + findCells p (P.mem.core.nb c))
        else 2 + findCells p (P.mem.core.nb c)) + 3 * P.cells + 3 * P.live ≤
      (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * P.live
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    by_cases hc : P.mem.core.sym a = some α
    · have ha : assoc a P.mem.toX.agents = some α := by
        rw [← h.mem.core.sym a]
        exact hc
      have e : (PMach.act xs P ⟨raw, snap, .ready a b α β⟩).1 = P.take a := by
        unfold PMach.act
        dsimp only
        rw [ite_pos' hc]
      have ec : PMach.cost xs P ⟨raw, snap, .ready a b α β⟩ = 2 + (P.takeCost + 0) := by
        show (2 + if P.mem.core.sym a = some α then P.takeCost else 0) = _
        rw [ite_pos' hc]
        rfl
      rw [e, ec]
      exact htake ha 0 (Nat.zero_le _)
    · have e : (PMach.act xs P ⟨raw, snap, .ready a b α β⟩).1 = P := by
        unfold PMach.act
        dsimp only
        rw [ite_neg' hc]
      have ec : PMach.cost xs P ⟨raw, snap, .ready a b α β⟩ = 2 + 0 := by
        show (2 + if P.mem.core.sym a = some α then P.takeCost else 0) = _
        rw [ite_neg' hc]
      rw [e, ec]
      show 2 + 0 + 3 * P.cells + 3 * P.live ≤
        (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * P.live
      omega
  | half a b α β =>
    have hput : (2 + 2) + 3 * (P.put a α).cells + 3 * P.live ≤
        (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * (P.put a α).live := by
      show (2 + 2) + 3 * (P.cells + 1) + 3 * P.live ≤
        (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * (P.live + 1)
      omega
    by_cases hc : P.mem.core.sym b = some β ∧ a ≠ b
    · cases hR : xs.rule α β with
      | some R =>
        have hb' : assoc b P.mem.toX.agents = some β := by
          rw [← h.mem.core.sym b]
          exact hc.1
        obtain ⟨hC, hD⟩ := hb α β R hR
        have ha := Nat.le_trans (R.newAgents_length a b) hC
        have hl := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD
        have e : (PMach.act xs P ⟨raw, snap, .half a b α β⟩).1 = P.take b := by
          unfold PMach.act
          dsimp only
          rw [ite_pos' hc, hR]
        have ec : PMach.cost xs P ⟨raw, snap, .half a b α β⟩ =
            2 + (P.takeCost + (R.newAgents a b).length +
              (R.newLinks xs.sys.ar a b α β).length) := by
          unfold PMach.cost
          dsimp only
          rw [ite_pos' hc, hR]
        rw [e, ec, Nat.add_assoc P.takeCost]
        exact htake hb' _ (by omega)
      | none =>
        have e : (PMach.act xs P ⟨raw, snap, .half a b α β⟩).1 = P.put a α := by
          unfold PMach.act
          dsimp only
          rw [ite_pos' hc, hR]
        have ec : PMach.cost xs P ⟨raw, snap, .half a b α β⟩ = 2 + 2 := by
          unfold PMach.cost
          dsimp only
          rw [ite_pos' hc, hR]
        rw [e, ec]
        exact hput
    · have e : (PMach.act xs P ⟨raw, snap, .half a b α β⟩).1 = P.put a α := by
        unfold PMach.act
        dsimp only
        rw [ite_neg' hc]
      have ec : PMach.cost xs P ⟨raw, snap, .half a b α β⟩ = 2 + 2 := by
        unfold PMach.cost
        dsimp only
        rw [ite_neg' hc]
      rw [e, ec]
      exact hput
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      show 3 + 3 * (P.cells + 1) + 3 * P.live ≤
        (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * (P.live + 1)
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show 6 + 3 * P.cells + 3 * P.live ≤
          (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * P.live
        omega
      | nil =>
        show 1 + 3 * P.cells + 3 * P.live ≤
          (C + D + 11) * 1 + 2 * 0 + 3 * P.cells + 3 * P.live
        omega

/-- What the action of thread `t` costs. -/
def PMach.stepCost (xs : XSys S) (M : PMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => PMach.cost xs M.mem T
  | none => 0

/-- The cells the action of thread `t` drops. -/
def PMach.stepSkips (M : PMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => T.skips M.mem.mem
  | none => 0

/-- **The running time on the packing memory** of the first `i` actions of
a run. -/
def PMach.time (xs : XSys S) (σ : Nat → Nat) (M : PMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => PMach.time xs σ M i + (M.trace xs σ i).1.stepCost xs (σ i)

/-- The dead cells the threads drop in the first `i` actions of a run. -/
def PMach.skips (xs : XSys S) (σ : Nat → Nat) (M : PMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => PMach.skips xs σ M i + (M.trace xs σ i).1.stepSkips (σ i)

theorem PMach.stepCost_le {C D : Nat} (hb : xs.Bounded C D) {M : PMach S} (h : M.Ok)
    (hnd0 : (M.toX.mem.agents.map Prod.fst).Nodup) (t : Nat) :
    M.stepCost xs t + 3 * (M.step xs t).1.mem.cells + 3 * M.mem.live ≤
      (C + D + 11) * M.toX.stepTally XThread.busy t + 2 * M.stepSkips t + 3 * M.mem.cells +
        3 * (M.step xs t).1.mem.live := by
  have hm : M.toX.ths[t]? = (M.ths[t]?).map (LThread.toX M.mem.mem) := by
    show (M.ths.map (LThread.toX M.mem.mem))[t]? = _
    rw [List.getElem?_map]
  unfold PMach.stepCost PMach.stepSkips XMach.stepTally PMach.step
  rw [hm]
  cases M.ths[t]? with
  | none =>
    show 0 + 3 * M.mem.cells + 3 * M.mem.live ≤
      (C + D + 11) * 0 + 2 * 0 + 3 * M.mem.cells + 3 * M.mem.live
    omega
  | some T => exact PMach.cost_le hb h.mem T hnd0

/-- **The time on the packing memory is the work, up to a constant, and
the dead cells dropped.**  On every run, whatever the schedule, the time
is at most

    (C + D + 11)

for each action that is not a rest and two for each dead cell dropped:
the packing is paid for by the agents taken out. -/
theorem PMach.time_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) (σ : Nat → Nat) :
    ∀ i, (PMach.init X nt).time xs σ i ≤
      (C + D + 11) * (XMach.init X nt).work xs σ i + 2 * (PMach.init X nt).skips xs σ i := by
  have nd := XMach.init_nodup (xs := xs) hX hnd hnt σ
  have key : ∀ i, (PMach.init X nt).time xs σ i +
        3 * ((PMach.init X nt).trace xs σ i).1.mem.cells + 3 * X.agents.length ≤
      (C + D + 11) * (XMach.init X nt).work xs σ i + 2 * (PMach.init X nt).skips xs σ i +
        3 * X.agents.length + 3 * ((PMach.init X nt).trace xs σ i).1.mem.live := by
    intro i
    induction i with
    | zero =>
      show 0 + 3 * X.agents.length + 3 * X.agents.length ≤
        (C + D + 11) * 0 + 2 * 0 + 3 * X.agents.length + 3 * X.agents.length
      omega
    | succ i ih =>
      obtain ⟨a, -, ok⟩ := PMach.init_sim (xs := xs) hX hnd hnt σ i
      have hn0 : (((PMach.init X nt).trace xs σ i).1.toX.mem.agents.map Prod.fst).Nodup := by
        rw [a]
        exact nd i
      have hs := PMach.stepCost_le hb ok hn0 (σ i)
      rw [a] at hs
      show (PMach.init X nt).time xs σ i +
            ((PMach.init X nt).trace xs σ i).1.stepCost xs (σ i) +
          3 * (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.cells +
          3 * X.agents.length ≤
        (C + D + 11) * ((XMach.init X nt).work xs σ i +
            ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i)) +
          2 * ((PMach.init X nt).skips xs σ i +
            ((PMach.init X nt).trace xs σ i).1.stepSkips (σ i)) +
          3 * X.agents.length +
          3 * (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.live
      rw [Nat.mul_add (C + D + 11)]
      omega
  intro i
  have k := key i
  obtain ⟨-, -, ok⟩ := PMach.init_sim (xs := xs) hX hnd hnt σ i
  have h₁ := ok.mem.cells
  have h₂ := ok.mem.live
  have h₃ : ((PMach.init X nt).trace xs σ i).1.mem.mem.toX.agents.length ≤
      ((PMach.init X nt).trace xs σ i).1.mem.mem.core.log.length := by
    show ((((PMach.init X nt).trace xs σ i).1.mem.mem.core.log.filter _).map _).length ≤ _
    rw [List.length_map]
    exact List.length_filter_le _ _
  omega

/-- The cells of a thread's list that were dead when it took the list:
those it has still to drop. -/
def LThread.stale (L : LMem S) (T : LThread S) : Nat :=
  (T.raw.filter fun c => !L.seen T.snap c).length

omit [DecidableEq S] in
theorem LThread.stale_keeps {L L' : LMem S} (k : L.Keeps L') {T : LThread S}
    (hT : T.snap ≤ L.core.stamp) : T.stale L' = T.stale L := by
  have e : L'.seen T.snap = L.seen T.snap := funext (k.seen T.snap hT)
  show (T.raw.filter fun c => !L'.seen T.snap c).length =
    (T.raw.filter fun c => !L.seen T.snap c).length
  rw [e]

theorem length_dropWhile_le' {A : Type} (q : A → Bool) :
    ∀ l : List A, (l.dropWhile q).length ≤ l.length
  | [] => Nat.le_refl 0
  | x :: l => by
    by_cases hx : q x = true
    · rw [List.dropWhile_cons_of_pos hx]
      exact Nat.le_succ_of_le (length_dropWhile_le' q l)
    · rw [List.dropWhile_cons_of_neg hx]
      exact Nat.le_refl _

/-- The cells that fail a test are those dropped at the front and those
that fail it further on. -/
theorem stale_dropWhile {A : Type} (p : A → Bool) : ∀ l : List A,
    (l.filter fun c => !p c).length =
      l.length - (l.dropWhile fun c => !p c).length +
        ((l.dropWhile fun c => !p c).filter fun c => !p c).length
  | [] => rfl
  | x :: l => by
    by_cases hx : p x = true
    · have e : (x :: l).dropWhile (fun c => !p c) = x :: l :=
        List.dropWhile_cons_of_neg (by simpa using hx)
      rw [e]
      show _ = (l.length + 1) - (l.length + 1) + _
      omega
    · have e : (x :: l).dropWhile (fun c => !p c) = l.dropWhile (fun c => !p c) :=
        List.dropWhile_cons_of_pos (by simpa using hx)
      have ih := stale_dropWhile p l
      have hl := length_dropWhile_le' (fun c => !p c) l
      rw [e, List.filter_cons_of_pos (by simpa using hx)]
      show (l.filter fun c => !p c).length + 1 = (l.length + 1) - _ + _
      omega

theorem filter_not_length {A : Type} (p : A → Bool) : ∀ l : List A,
    (l.filter p).length + (l.filter fun c => !p c).length = l.length
  | [] => rfl
  | x :: l => by
    have ih := filter_not_length p l
    by_cases hx : p x = true
    · rw [List.filter_cons_of_pos hx, List.filter_cons_of_neg (by simpa using hx)]
      show (l.filter p).length + 1 + _ = l.length + 1
      omega
    · rw [List.filter_cons_of_neg hx, List.filter_cons_of_pos (by simpa using hx)]
      show (l.filter p).length + ((l.filter fun c => !p c).length + 1) = l.length + 1
      omega

/-- **A thread drops only what was dead when it took its list, and that is
at most the live cells of that moment.**  The cells an action drops and the
cells the thread has still to drop afterwards are those it had to drop
before; a thread that takes the agents afresh starts with at most as many
as there are live cells. -/
theorem PMach.act_stale (xs : XSys S) {P : PMem S} (h : P.Ok) (T : LThread S)
    (hT : T.snap ≤ P.mem.core.stamp) (hnd0 : (P.mem.toX.agents.map Prod.fst).Nodup)
    (hnd : ((XMach.act xs P.mem.toX (T.toX P.mem)).1.agents.map Prod.fst).Nodup) :
    T.skips P.mem + (PMach.act xs P T).2.1.stale (PMach.act xs P T).1.mem ≤
      T.stale P.mem + T.st.fin * P.live := by
  obtain ⟨-, -, -, -, -, k⟩ := PMach.act_sim xs h T hT hnd0 hnd
  obtain ⟨raw, snap, s⟩ := T
  have hT' : snap ≤ P.mem.core.stamp := hT
  have keep : ∀ s' : TState S,
      LThread.stale (PMach.act xs P ⟨raw, snap, s⟩).1.mem ⟨raw, snap, s'⟩ =
        LThread.stale P.mem ⟨raw, snap, s⟩ := fun s' =>
    LThread.stale_keeps (T := ⟨raw, snap, s'⟩) k hT'
  cases s with
  | idle =>
    have e : (PMach.act xs P ⟨raw, snap, .idle⟩).1 = P := by
      unfold PMach.act
      dsimp only
      split
      · rfl
      · split <;> rfl
    have hsd := stale_dropWhile (P.mem.seen snap) raw
    rcases dropWhile_not_spec (P.mem.seen snap) raw with ⟨hd, -⟩ | ⟨c, rest, hd, hc, -⟩
    · have eT : (PMach.act xs P ⟨raw, snap, .idle⟩).2.1 = ⟨[], snap, .idle⟩ := by
        unfold PMach.act
        dsimp only
        rw [hd]
      rw [e, eT]
      rw [hd] at hsd
      show raw.length - (raw.dropWhile fun c => !P.mem.seen snap c).length + 0 ≤
        (raw.filter fun c => !P.mem.seen snap c).length + 0 * P.live
      rw [hd, hsd]
      omega
    · have eT : (PMach.act xs P ⟨raw, snap, .idle⟩).2.1.raw = rest ∧
          (PMach.act xs P ⟨raw, snap, .idle⟩).2.1.snap = snap := by
        unfold PMach.act
        dsimp only
        rw [hd]
        dsimp only
        split <;> exact ⟨rfl, rfl⟩
      rw [hd, List.filter_cons_of_neg (by simpa using hc)] at hsd
      rw [e]
      show raw.length - (raw.dropWhile fun c => !P.mem.seen snap c).length +
          ((PMach.act xs P ⟨raw, snap, .idle⟩).2.1.raw.filter fun c =>
            !P.mem.seen (PMach.act xs P ⟨raw, snap, .idle⟩).2.1.snap c).length ≤
        (raw.filter fun c => !P.mem.seen snap c).length + 0 * P.live
      rw [eT.1, eT.2, hd, hsd]
      omega
  | look a α =>
    have e : ∃ s', (PMach.act xs P ⟨raw, snap, .look a α⟩).2.1 = ⟨raw, snap, s'⟩ := by
      unfold PMach.act
      dsimp only
      split <;> exact ⟨_, rfl⟩
    obtain ⟨s', e⟩ := e
    rw [e, keep s']
    show 0 + _ ≤ _ + 0 * P.live
    omega
  | seek a α p c =>
    have e : ∃ s', (PMach.act xs P ⟨raw, snap, .seek a α p c⟩).2.1 = ⟨raw, snap, s'⟩ := by
      unfold PMach.act
      dsimp only
      split
      · split <;> exact ⟨_, rfl⟩
      · split <;> exact ⟨_, rfl⟩
    obtain ⟨s', e⟩ := e
    rw [e, keep s']
    show 0 + _ ≤ _ + 0 * P.live
    omega
  | ready a b α β =>
    have e : ∃ s', (PMach.act xs P ⟨raw, snap, .ready a b α β⟩).2.1 = ⟨raw, snap, s'⟩ := by
      unfold PMach.act
      dsimp only
      split <;> exact ⟨_, rfl⟩
    obtain ⟨s', e⟩ := e
    rw [e, keep s']
    show 0 + _ ≤ _ + 0 * P.live
    omega
  | half a b α β =>
    have e : ∃ s', (PMach.act xs P ⟨raw, snap, .half a b α β⟩).2.1 = ⟨raw, snap, s'⟩ := by
      unfold PMach.act
      dsimp only
      split
      · split <;> exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨s', e⟩ := e
    rw [e, keep s']
    show 0 + _ ≤ _ + 0 * P.live
    omega
  | write as ls =>
    cases as with
    | cons x as =>
      obtain ⟨i, γ⟩ := x
      have e : (PMach.act xs P ⟨raw, snap, .write ((i, γ) :: as) ls⟩).2.1 =
          ⟨raw, snap, .write as ls⟩ := rfl
      rw [e, keep _]
      show 0 + _ ≤ _ + 0 * P.live
      omega
    | nil =>
      cases ls with
      | cons x ls =>
        obtain ⟨p, q⟩ := x
        have e : (PMach.act xs P ⟨raw, snap, .write [] ((p, q) :: ls)⟩).2.1 =
            ⟨raw, snap, .write [] ls⟩ := rfl
        rw [e, keep _]
        show 0 + _ ≤ _ + 0 * P.live
        omega
      | nil =>
        have hpart := filter_not_length P.mem.core.isLive P.mem.core.log
        have hlive : (P.mem.core.log.filter P.mem.core.isLive).length = P.live := by
          rw [h.live]
          show _ = ((P.mem.core.log.filter P.mem.core.isLive).map _).length
          rw [List.length_map]
        have hcong : (P.mem.core.log.filter fun c => !P.mem.seen P.mem.core.stamp c) =
            P.mem.core.log.filter fun c => !P.mem.core.isLive c :=
          List.filter_congr fun c hc => by
            show (!P.mem.seen P.mem.core.stamp c) = !P.mem.core.isLive c
            rw [LMem.seen_now h.mem c hc]
        have hcells := h.cells
        have hhalf := h.half
        show 0 + (P.mem.core.log.filter fun c => !P.mem.seen P.mem.core.stamp c).length ≤
          (raw.filter fun c => !P.mem.seen snap c).length + 1 * P.live
        rw [hcong]
        omega

/-- A sum over the threads with lazy lists. -/
def ltotal (f : LThread S → Nat) : List (LThread S) → Nat
  | [] => 0
  | T :: ths => f T + ltotal f ths

omit [DecidableEq S] in
theorem ltotal_set (f : LThread S → Nat) : ∀ (ths : List (LThread S)) (t : Nat)
    (T T' : LThread S), ths[t]? = some T → ltotal f (ths.set t T') + f T = ltotal f ths + f T'
  | [], _, _, _, h => by cases h
  | U :: ths, 0, T, T', h => by
    rw [List.getElem?_cons_zero] at h
    rw [Option.some.inj h]
    show f T' + ltotal f ths + f T = f T + ltotal f ths + f T'
    omega
  | U :: ths, t + 1, T, T', h => by
    rw [List.getElem?_cons_succ] at h
    have ih := ltotal_set f ths t T T' h
    show f U + ltotal f (ths.set t T') + f T = f U + ltotal f ths + f T'
    omega

omit [DecidableEq S] in
theorem ltotal_congr {f g : LThread S → Nat} : ∀ {ths : List (LThread S)},
    (∀ T, T ∈ ths → f T = g T) → ltotal f ths = ltotal g ths
  | [], _ => rfl
  | U :: ths, h => by
    show f U + ltotal f ths = g U + ltotal g ths
    rw [h U List.mem_cons_self, ltotal_congr fun T hT => h T (List.mem_cons_of_mem _ hT)]

omit [DecidableEq S] in
theorem ltotal_zero {f : LThread S → Nat} : ∀ {ths : List (LThread S)},
    (∀ T, T ∈ ths → f T = 0) → ltotal f ths = 0
  | [], _ => rfl
  | U :: ths, h => by
    show f U + ltotal f ths = 0
    rw [h U List.mem_cons_self, ltotal_zero fun T hT => h T (List.mem_cons_of_mem _ hT)]

/-- One action: what it drops and what the threads have still to drop
afterwards is what they had to drop before, and the live cells if the
thread takes the agents afresh. -/
theorem PMach.step_stale (xs : XSys S) {M : PMach S} (h : M.Ok)
    (hnd0 : (M.toX.mem.agents.map Prod.fst).Nodup)
    (hnd : ((M.toX.step xs t).1.mem.agents.map Prod.fst).Nodup) :
    M.stepSkips t + ltotal (LThread.stale (M.step xs t).1.mem.mem) (M.step xs t).1.ths ≤
      ltotal (LThread.stale M.mem.mem) M.ths + (threadOf M.toX.ths t).fin * M.mem.live := by
  cases ht : M.ths[t]? with
  | none =>
    have e₁ : M.step xs t = (M, 0) := by
      unfold PMach.step
      rw [ht]
    have e₂ : M.stepSkips t = 0 := by
      unfold PMach.stepSkips
      rw [ht]
    rw [e₁, e₂]
    show 0 + ltotal (LThread.stale M.mem.mem) M.ths ≤ _
    omega
  | some T =>
    have ht' : M.toX.ths[t]? = some (T.toX M.mem.mem) := by
      show (M.ths.map (LThread.toX M.mem.mem))[t]? = _
      rw [List.getElem?_map, ht]
      rfl
    have e₂ : M.toX.step xs t = (⟨(XMach.act xs M.mem.mem.toX (T.toX M.mem.mem)).1,
        (M.ths.map (LThread.toX M.mem.mem)).set t
          (XMach.act xs M.mem.mem.toX (T.toX M.mem.mem)).2.1⟩,
        (XMach.act xs M.mem.mem.toX (T.toX M.mem.mem)).2.2) := XMach.step_eq ht' rfl
    rw [e₂] at hnd
    have hTm := List.mem_of_getElem? ht
    have hT := h.snap T hTm
    obtain ⟨-, -, -, -, -, k⟩ := PMach.act_sim xs h.mem T hT hnd0 hnd
    have hs := PMach.act_stale xs h.mem T hT hnd0 hnd
    have e₁ : M.step xs t = (⟨(PMach.act xs M.mem T).1,
        M.ths.set t (PMach.act xs M.mem T).2.1⟩, (PMach.act xs M.mem T).2.2) := by
      unfold PMach.step
      rw [ht]
    have e₃ : M.stepSkips t = T.skips M.mem.mem := by
      unfold PMach.stepSkips
      rw [ht]
    have ts := ltotal_set (LThread.stale (PMach.act xs M.mem T).1.mem) M.ths t T
      (PMach.act xs M.mem T).2.1 ht
    have tc : ltotal (LThread.stale (PMach.act xs M.mem T).1.mem) M.ths =
        ltotal (LThread.stale M.mem.mem) M.ths :=
      ltotal_congr fun U hU => LThread.stale_keeps k (h.snap U hU)
    have tk : T.stale (PMach.act xs M.mem T).1.mem = T.stale M.mem.mem :=
      LThread.stale_keeps k hT
    rw [e₁, e₃, threadOf_eq ht']
    show T.skips M.mem.mem + ltotal (LThread.stale (PMach.act xs M.mem T).1.mem)
        (M.ths.set t (PMach.act xs M.mem T).2.1) ≤
      ltotal (LThread.stale M.mem.mem) M.ths + T.st.fin * M.mem.live
    omega

/-- **The dead cells dropped are bounded.**  Under the hypotheses of
`IMach.time_bound`, on every run the threads drop at most

    n * (X.agents.length + C * n)

dead cells: a thread drops only cells that were dead when it took its
list, the log is never more than half dead, and the agents are taken
afresh once for each claim. -/
theorem PMach.skips_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (PMach.init X nt).skips xs σ i ≤ n * (X.agents.length + C * n) := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have nd := XMach.init_nodup (xs := xs) hX hnd hnt σ
  have key : ∀ i, (PMach.init X nt).skips xs σ i +
        ltotal (LThread.stale ((PMach.init X nt).trace xs σ i).1.mem.mem)
          ((PMach.init X nt).trace xs σ i).1.ths ≤
      (XMach.init X nt).packs xs σ i * (X.agents.length + C * n) := by
    intro i
    induction i with
    | zero =>
      have hseen : ∀ (t₀ : Nat) (c : Nat × Id × S), (LMem.ofX X).seen t₀ c = true := by
        intro t₀ c
        show (match (∅ : Std.HashMap Nat Nat)[c.1]? with
          | none => true
          | some d => decide (t₀ ≤ d)) = true
        rw [Std.HashMap.getElem?_empty]
      have z : ltotal (LThread.stale (LMem.ofX X)) (PMach.init X nt).ths = 0 :=
        ltotal_zero fun T _ => by
          show (T.raw.filter fun c => !(LMem.ofX X).seen T.snap c).length = 0
          have e : T.raw.filter (fun c => !(LMem.ofX X).seen T.snap c) = [] :=
            List.filter_eq_nil_iff.2 fun c _ => by
              rw [hseen]
              exact fun h' => by cases h'
          rw [e]
          rfl
      show 0 + ltotal (LThread.stale (LMem.ofX X)) (PMach.init X nt).ths ≤
        0 * (X.agents.length + C * n)
      rw [z]
      omega
    | succ i ih =>
      obtain ⟨a, -, ok⟩ := PMach.init_sim (xs := xs) hX hnd hnt σ i
      obtain ⟨hA, -, -⟩ := hΦ i
      have hn0 : (((PMach.init X nt).trace xs σ i).1.toX.mem.agents.map Prod.fst).Nodup := by
        rw [a]
        exact nd i
      have hn1 : ((((PMach.init X nt).trace xs σ i).1.toX.step xs (σ i)).1.mem.agents.map
          Prod.fst).Nodup := by
        rw [a]
        exact nd (i + 1)
      have hst := PMach.step_stale xs ok hn0 hn1 (t := σ i)
      rw [a] at hst
      have hlive : ((PMach.init X nt).trace xs σ i).1.mem.live ≤ X.agents.length + C * n := by
        have h₂ := ok.mem.live
        have e : ((PMach.init X nt).trace xs σ i).1.mem.mem.toX =
            ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
        rw [e] at h₂
        have := Nat.mul_le_mul_right n (Nat.sub_le C 2)
        omega
      have hm := Nat.mul_le_mul_left
        (threadOf ((XMach.init X nt).trace xs σ i).1.ths (σ i)).fin hlive
      show (PMach.init X nt).skips xs σ i +
            ((PMach.init X nt).trace xs σ i).1.stepSkips (σ i) +
          ltotal (LThread.stale (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.mem)
            (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.ths ≤
        ((XMach.init X nt).packs xs σ i +
          (threadOf ((XMach.init X nt).trace xs σ i).1.ths (σ i)).fin) *
          (X.agents.length + C * n)
      rw [Nat.add_mul]
      omega
  intro i
  have k := key i
  have hp : (XMach.init X nt).packs xs σ i ≤ n :=
    Nat.le_trans (XMach.packs_le_claims X nt σ i) (hΦ i).2.1
  have h₁ := Nat.mul_le_mul_right (X.agents.length + C * n) hp
  omega

/-- **A bound on the running time on the packing memory, whatever the
schedule.**  Under the hypotheses of `IMach.time_bound` the run never
takes more time than

    ((nt + n) * X.passBound n C D + n * (C + D + 1)) * (C + D + 11)

for the actions that are not rests, the packing included, and

    2 * n * (X.agents.length + C * n)

for the dead cells dropped.  It is the bound of the indexed memory up to
the constants; what differs is that the second part is paid only for the
cells a thread in fact walks past. -/
theorem PMach.time_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (PMach.init X nt).time xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) * (C + D + 11) +
        2 * n * (X.agents.length + C * n) := by
  intro i
  have h₁ := PMach.time_le_work (xs := xs) hX hnd hnt hb σ i
  have h₂ := XMach.work_le hX hnd hnt hb hs hn σ i
  have h₃ := PMach.skips_le (xs := xs) hX hnd hnt hb hs hn σ i
  have h₄ := Nat.mul_le_mul_left (C + D + 11) h₂
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1)), Nat.mul_assoc 2 n]
  omega

theorem LMem.flags_pack (L : LMem S) : L.pack.flags = L.flags.filter (·.2) := by
  show (L.core.log.filter L.core.isLive).map (fun c => (c.2.1, L.core.isLive c)) =
    (L.core.log.map fun c => (c.2.1, L.core.isLive c)).filter (·.2)
  rw [List.filter_map]
  rfl

theorem PMem.Ok.cells_flags {P : PMem S} (h : P.Ok) : P.cells = P.mem.flags.length := by
  rw [h.cells]
  exact (List.length_map (f := fun c : Nat × Id × S => (c.2.1, P.mem.core.isLive c))).symm

theorem PMem.Ok.live_flags {P : PMem S} (h : P.Ok) :
    P.live = (P.mem.flags.filter (·.2)).length := by
  rw [h.live]
  show ((P.mem.core.log.filter P.mem.core.isLive).map (·.2)).length =
    ((P.mem.core.log.map fun c => (c.2.1, P.mem.core.isLive c)).filter (·.2)).length
  rw [List.filter_map, List.length_map, List.length_map]
  rfl

theorem PMem.keeps_take {P : PMem S} (hm : P.mem.Ok) (a : Id) :
    P.mem.Keeps (P.take a).mem := by
  unfold PMem.take PMem.settle
  dsimp only
  split
  · exact (LMem.Keeps.take hm a).trans (LMem.Keeps.pack _)
  · exact LMem.Keeps.take hm a

/-- What taking an agent out costs, told from the marks of the log. -/
def packCost (lf : List (Id × Bool)) : Nat :=
  2 + if 2 * ((lf.filter (·.2)).length - 1) < lf.length then
    lf.length + ((lf.filter (·.2)).length - 1) else 0

/-- The marks of the log after an agent is taken out. -/
def packLog (a : Id) (lf : List (Id × Bool)) : List (Id × Bool) :=
  if 2 * ((lf.filter (·.2)).length - 1) < lf.length then
    (lf.map fun e => (e.1, e.2 && decide (e.1 ≠ a))).filter (·.2)
  else lf.map fun e => (e.1, e.2 && decide (e.1 ≠ a))

theorem PMem.Ok.takeCost_flags {P : PMem S} (h : P.Ok) : P.takeCost = packCost P.mem.flags := by
  unfold PMem.takeCost packCost
  rw [← h.cells_flags, ← h.live_flags]

theorem PMem.Ok.flags_take {P : PMem S} (h : P.Ok) (a : Id) :
    (P.take a).mem.flags = packLog a P.mem.flags := by
  unfold PMem.take PMem.settle packLog
  dsimp only
  rw [← h.cells_flags, ← h.live_flags]
  by_cases hp : 2 * (P.live - 1) < P.cells
  · rw [ite_pos' hp, ite_pos' hp]
    show (P.mem.take a).pack.flags = _
    rw [LMem.flags_pack, LMem.flags_take]
  · rw [ite_neg' hp, ite_neg' hp]
    exact LMem.flags_take P.mem a

/-- What an action costs on the packing memory, told from the lists of the
program and the marks. -/
def XMach.kcost (xs : XSys S) (X : XNet S) (lf : List (Id × Bool)) (fs : List Bool)
    (T : XThread S) : Nat :=
  match T.st with
  | .idle =>
    idleCost (!(fs.dropWhile (fun b => !b)).isEmpty)
      (fs.length - (fs.dropWhile (fun b => !b)).length)
  | .look _ _ => 3
  | .seek _ _ p c =>
    if c.2 = 0 then
      2 + if (assoc c.1 X.agents).isSome then 0 else 1 + findCells p (nbOf X.wires c)
    else 2 + findCells p (nbOf X.wires c)
  | .ready a _ α _ => 2 + if assoc a X.agents = some α then packCost lf else 0
  | .half a b α β =>
    2 + if assoc b X.agents = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          packCost lf + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => 2
      else 2
  | .write (_ :: _) _ => 3
  | .write [] (_ :: _) => 6
  | .write [] [] => 1

/-- The marks of the log after an action on the packing memory. -/
def XMach.klog (xs : XSys S) (X : XNet S) (lf : List (Id × Bool)) (T : XThread S) :
    List (Id × Bool) :=
  match T.st with
  | .idle => lf
  | .look _ _ => lf
  | .seek _ _ _ _ => lf
  | .ready a _ α _ => if assoc a X.agents = some α then packLog a lf else lf
  | .half a b α β =>
    if assoc b X.agents = some β ∧ a ≠ b then
      match xs.rule α β with
      | some _ => packLog b lf
      | none => (a, true) :: lf
    else (a, true) :: lf
  | .write (e :: _) _ => (e.1, true) :: lf
  | .write [] (_ :: _) => lf
  | .write [] [] => lf

/-- **An action on the packing memory, told from the lists.** -/
theorem PMach.act_shadow (xs : XSys S) {P : PMem S} (h : P.Ok) (T : LThread S)
    (hT : T.snap ≤ P.mem.core.stamp)
    (hnd : ((XMach.act xs P.mem.toX (T.toX P.mem)).1.agents.map Prod.fst).Nodup) :
    PMach.cost xs P T = XMach.kcost xs P.mem.toX P.mem.flags (T.flags P.mem) (T.toX P.mem) ∧
      T.skips P.mem = XMach.jskips (T.flags P.mem) (T.toX P.mem) ∧
      (PMach.act xs P T).1.mem.flags = XMach.klog xs P.mem.toX P.mem.flags (T.toX P.mem) ∧
      (PMach.act xs P T).2.1.flags (PMach.act xs P T).1.mem =
        XMach.jflags P.mem.flags (T.flags P.mem) (T.toX P.mem) := by
  obtain ⟨raw, snap, s⟩ := T
  have hT' : snap ≤ P.mem.core.stamp := hT
  have hm := h.mem
  cases s with
  | idle =>
    have hdm := dropWhile_map_not (P.mem.seen snap) raw
    have hsk : raw.length - (raw.dropWhile fun c => !P.mem.seen snap c).length =
        (raw.map (P.mem.seen snap)).length -
          ((raw.map (P.mem.seen snap)).dropWhile fun b => !b).length := by
      rw [hdm, List.length_map, List.length_map]
    have hem : (raw.dropWhile fun c => !P.mem.seen snap c).isEmpty =
        ((raw.map (P.mem.seen snap)).dropWhile fun b => !b).isEmpty := by
      rw [hdm]
      cases raw.dropWhile fun c => !P.mem.seen snap c <;> rfl
    refine ⟨?_, hsk, ?_, ?_⟩
    · show idleCost (!(raw.dropWhile fun c => !P.mem.seen snap c).isEmpty)
          (raw.length - (raw.dropWhile fun c => !P.mem.seen snap c).length) =
        idleCost (!((raw.map (P.mem.seen snap)).dropWhile fun b => !b).isEmpty)
          ((raw.map (P.mem.seen snap)).length -
            ((raw.map (P.mem.seen snap)).dropWhile fun b => !b).length)
      rw [hsk, hem]
    · have e : (PMach.act xs P ⟨raw, snap, .idle⟩).1 = P := by
        unfold PMach.act
        dsimp only
        split
        · rfl
        · split <;> rfl
      rw [e]
      rfl
    · show LThread.flags (PMach.act xs P ⟨raw, snap, .idle⟩).1.mem
          (PMach.act xs P ⟨raw, snap, .idle⟩).2.1 =
        ((raw.map (P.mem.seen snap)).dropWhile fun b => !b).tail
      rw [hdm]
      unfold PMach.act
      dsimp only
      split
      · rename_i hd
        rw [hd]
        rfl
      · rename_i c rest hd
        rw [hd]
        split <;> rfl
  | look a α =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have e : (PMach.act xs P ⟨raw, snap, .look a α⟩).1 = P := by
        unfold PMach.act
        dsimp only
        split <;> rfl
      rw [e]
      rfl
    · unfold PMach.act
      dsimp only
      split <;> rfl
  | seek a α p c =>
    refine ⟨?_, rfl, ?_, ?_⟩
    · show (if c.2 = 0 then 2 + (if (P.mem.core.sym c.1).isSome then 0
          else 1 + findCells p (P.mem.core.nb c))
        else 2 + findCells p (P.mem.core.nb c)) = _
      rw [hm.core.sym c.1, hm.core.nbrs c]
      rfl
    · have e : (PMach.act xs P ⟨raw, snap, .seek a α p c⟩).1 = P := by
        unfold PMach.act
        dsimp only
        split
        · split <;> rfl
        · split <;> rfl
      rw [e]
      rfl
    · unfold PMach.act
      dsimp only
      split
      · split <;> rfl
      · split <;> rfl
  | ready a b α β =>
    have eT : LThread.toX P.mem ⟨raw, snap, .ready a b α β⟩ =
        ⟨(raw.filter (P.mem.seen snap)).map (·.2), .ready a b α β⟩ := rfl
    refine ⟨?_, rfl, ?_, ?_⟩
    · show (2 + if P.mem.core.sym a = some α then P.takeCost else 0) = _
      rw [hm.core.sym a, h.takeCost_flags]
      rfl
    · rw [eT]
      unfold PMach.act XMach.klog
      dsimp only
      rw [hm.core.sym a]
      by_cases hc : assoc a P.mem.core.toX.agents = some α
      · rw [ite_pos' hc, ite_pos' hc]
        exact h.flags_take a
      · rw [ite_neg' hc, ite_neg' hc]
    · unfold PMach.act
      dsimp only
      by_cases hc : P.mem.core.sym a = some α
      · rw [ite_pos' hc]
        exact LThread.flags_keeps (PMem.keeps_take hm a) hT'
      · rw [ite_neg' hc]
        rfl
  | half a b α β =>
    have eT : LThread.toX P.mem ⟨raw, snap, .half a b α β⟩ =
        ⟨(raw.filter (P.mem.seen snap)).map (·.2), .half a b α β⟩ := rfl
    rw [eT] at hnd
    unfold XMach.act at hnd
    dsimp only at hnd
    refine ⟨?_, rfl, ?_, ?_⟩
    · unfold PMach.cost XMach.kcost
      dsimp only
      rw [hm.core.sym b, h.takeCost_flags]
      rfl
    · rw [eT]
      unfold PMach.act XMach.klog
      dsimp only
      rw [hm.core.sym b]
      by_cases hc : assoc b P.mem.core.toX.agents = some β ∧ a ≠ b
      · rw [ite_pos' hc, ite_pos' hc]
        rw [ite_pos' hc] at hnd
        cases hR : xs.rule α β with
        | some R => exact h.flags_take b
        | none =>
          rw [hR] at hnd
          exact LMem.flags_put hm (assoc_none_of_nodup_cons hnd) α
      · rw [ite_neg' hc, ite_neg' hc]
        rw [ite_neg' hc] at hnd
        exact LMem.flags_put hm (assoc_none_of_nodup_cons hnd) α
    · unfold PMach.act
      dsimp only
      by_cases hc : P.mem.core.sym b = some β ∧ a ≠ b
      · rw [ite_pos' hc]
        cases xs.rule α β with
        | some R => exact LThread.flags_keeps (PMem.keeps_take hm b) hT'
        | none => exact LThread.flags_keeps (.put P.mem a α) hT'
      · rw [ite_neg' hc]
        exact LThread.flags_keeps (.put P.mem a α) hT'
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨rfl, rfl, LMem.flags_put hm (assoc_none_of_nodup_cons hnd) γ,
        LThread.flags_keeps (.put P.mem i γ) hT'⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact ⟨rfl, rfl, rfl, LThread.flags_keeps (.link P.mem p q) hT'⟩
      | nil =>
        refine ⟨rfl, rfl, rfl, ?_⟩
        show P.mem.core.log.map (P.mem.seen P.mem.core.stamp) =
          (P.mem.core.log.map fun c => (c.2.1, P.mem.core.isLive c)).map (·.2)
        rw [List.map_map]
        exact List.map_congr_left (LMem.seen_now hm)

/-- What every earlier clock saw is kept by an action on the packing
memory. -/
theorem PMach.act_keeps (xs : XSys S) {P : PMem S} (hm : P.mem.Ok) (T : LThread S) :
    P.mem.Keeps (PMach.act xs P T).1.mem := by
  obtain ⟨raw, snap, s⟩ := T
  cases s with
  | idle =>
    unfold PMach.act
    dsimp only
    split
    · exact LMem.Keeps.refl _
    · split <;> exact LMem.Keeps.refl _
  | look a α =>
    unfold PMach.act
    dsimp only
    split <;> exact LMem.Keeps.refl _
  | seek a α p c =>
    unfold PMach.act
    dsimp only
    split
    · split <;> exact LMem.Keeps.refl _
    · split <;> exact LMem.Keeps.refl _
  | ready a b α β =>
    unfold PMach.act
    dsimp only
    split
    · exact PMem.keeps_take hm a
    · exact LMem.Keeps.refl _
  | half a b α β =>
    unfold PMach.act
    dsimp only
    split
    · split
      · exact PMem.keeps_take hm b
      · exact LMem.Keeps.put P.mem a α
    · exact LMem.Keeps.put P.mem a α
  | write as ls =>
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact LMem.Keeps.put P.mem i γ
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        exact LMem.Keeps.link P.mem p q
      | nil => exact LMem.Keeps.refl _

/-- **A run on the packing memory, told from the lists**: what the first
`i` actions cost, the dead cells they drop, the marks of the log and the
marks of every thread after them, computed along the run of the program on
lists. -/
def XMach.packRun (xs : XSys S) (σ : Nat → Nat) (X : XNet S) (nt : Nat) :
    Nat → Nat × Nat × List (Id × Bool) × List (List Bool)
  | 0 => (0, 0, X.agents.map fun e => (e.1, true),
      (List.range nt).map fun _ => List.replicate X.agents.length true)
  | i + 1 =>
    match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
    | some T =>
      ((XMach.packRun xs σ X nt i).1 +
          XMach.kcost xs ((XMach.init X nt).trace xs σ i).1.mem
            (XMach.packRun xs σ X nt i).2.2.1
            (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
        (XMach.packRun xs σ X nt i).2.1 +
          XMach.jskips (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
        XMach.klog xs ((XMach.init X nt).trace xs σ i).1.mem
          (XMach.packRun xs σ X nt i).2.2.1 T,
        (XMach.packRun xs σ X nt i).2.2.2.set (σ i)
          (XMach.jflags (XMach.packRun xs σ X nt i).2.2.1
            (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD []) T))
    | none => XMach.packRun xs σ X nt i

/-- One action on the packing memory, told from the lists. -/
theorem PMach.step_shadow (xs : XSys S) {M : PMach S} (h : M.Ok) {t : Nat} {T : LThread S}
    (ht : M.ths[t]? = some T)
    (hnd : ((XMach.act xs M.mem.mem.toX (T.toX M.mem.mem)).1.agents.map Prod.fst).Nodup) :
    M.stepCost xs t =
        XMach.kcost xs M.mem.mem.toX M.mem.mem.flags (T.flags M.mem.mem) (T.toX M.mem.mem) ∧
      M.stepSkips t = XMach.jskips (T.flags M.mem.mem) (T.toX M.mem.mem) ∧
      (M.step xs t).1.mem.mem.flags =
        XMach.klog xs M.mem.mem.toX M.mem.mem.flags (T.toX M.mem.mem) ∧
      (M.step xs t).1.ths.map (LThread.flags (M.step xs t).1.mem.mem) =
        (M.ths.map (LThread.flags M.mem.mem)).set t
          (XMach.jflags M.mem.mem.flags (T.flags M.mem.mem) (T.toX M.mem.mem)) := by
  have hT := h.snap T (List.mem_of_getElem? ht)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := PMach.act_shadow xs h.mem T hT hnd
  have k := PMach.act_keeps xs h.mem.mem T
  have e₁ : M.step xs t = (⟨(PMach.act xs M.mem T).1,
      M.ths.set t (PMach.act xs M.mem T).2.1⟩, (PMach.act xs M.mem T).2.2) := by
    unfold PMach.step
    rw [ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PMach.stepCost
    rw [ht]
    exact c₁
  · unfold PMach.stepSkips
    rw [ht]
    exact c₂
  · rw [e₁]
    exact c₃
  · rw [e₁]
    have em : M.ths.map (LThread.flags (PMach.act xs M.mem T).1.mem) =
        M.ths.map (LThread.flags M.mem.mem) :=
      List.map_congr_left fun U hU => LThread.flags_keeps k (h.snap U hU)
    show (M.ths.set t (PMach.act xs M.mem T).2.1).map
      (LThread.flags (PMach.act xs M.mem T).1.mem) = _
    rw [List.map_set, em, c₄]

/-- **The time on the packing memory can be computed on lists.** -/
theorem PMach.time_shadow {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, (PMach.init X nt).time xs σ i = (XMach.packRun xs σ X nt i).1 ∧
      (PMach.init X nt).skips xs σ i = (XMach.packRun xs σ X nt i).2.1 ∧
      ((PMach.init X nt).trace xs σ i).1.mem.mem.flags = (XMach.packRun xs σ X nt i).2.2.1 ∧
      ((PMach.init X nt).trace xs σ i).1.ths.map
          (LThread.flags ((PMach.init X nt).trace xs σ i).1.mem.mem) =
        (XMach.packRun xs σ X nt i).2.2.2
  | 0 => by
    obtain ⟨-, -, h₃, h₄⟩ := LMach.time_shadow (xs := xs) hX hnd hnt σ 0
    exact ⟨rfl, rfl, h₃, h₄⟩
  | i + 1 => by
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := PMach.time_shadow hX hnd hnt σ i
    obtain ⟨a, -, ok⟩ := PMach.init_sim (xs := xs) hX hnd hnt σ i
    have nd := XMach.init_nodup (xs := xs) hX hnd hnt σ
    have emem : ((PMach.init X nt).trace xs σ i).1.mem.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    have hm : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
        (((PMach.init X nt).trace xs σ i).1.ths[σ i]?).map
          (LThread.toX ((PMach.init X nt).trace xs σ i).1.mem.mem) := by
      rw [← a]
      show (((PMach.init X nt).trace xs σ i).1.ths.map _)[σ i]? = _
      rw [List.getElem?_map]
    cases hT : ((PMach.init X nt).trace xs σ i).1.ths[σ i]? with
    | none =>
      rw [hT] at hm
      have hm' : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? = none := hm
      have es : XMach.packRun xs σ X nt (i + 1) = XMach.packRun xs σ X nt i := by
        show (match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
          | some T => _
          | none => XMach.packRun xs σ X nt i) = _
        rw [hm']
      have e₁ : ((PMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = 0 := by
        unfold PMach.stepCost
        rw [hT]
      have e₂ : ((PMach.init X nt).trace xs σ i).1.stepSkips (σ i) = 0 := by
        unfold PMach.stepSkips
        rw [hT]
      have e₃ : ((PMach.init X nt).trace xs σ i).1.step xs (σ i) =
          (((PMach.init X nt).trace xs σ i).1, 0) := by
        unfold PMach.step
        rw [hT]
      rw [es]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show (PMach.init X nt).time xs σ i +
          ((PMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [e₁, ih₁]
        rfl
      · show (PMach.init X nt).skips xs σ i +
          ((PMach.init X nt).trace xs σ i).1.stepSkips (σ i) = _
        rw [e₂, ih₂]
        rfl
      · show (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.mem.flags = _
        rw [e₃]
        exact ih₃
      · show (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.ths.map
          (LThread.flags (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.mem) = _
        rw [e₃]
        exact ih₄
    | some T =>
      rw [hT] at hm
      have hm' : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
          some (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem) := hm
      have hfl : ((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD [] =
          T.flags ((PMach.init X nt).trace xs σ i).1.mem.mem := by
        rw [← ih₄, List.getElem?_map, hT]
        rfl
      have hstep : (((XMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem =
          (XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
            (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem)).1 := by
        have e : ((XMach.init X nt).trace xs σ i).1.step xs (σ i) =
            (⟨(XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
                (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem)).1,
              ((XMach.init X nt).trace xs σ i).1.ths.set (σ i)
                (XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
                  (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem)).2.1⟩,
              (XMach.act xs ((XMach.init X nt).trace xs σ i).1.mem
                (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem)).2.2) :=
          XMach.step_eq hm' rfl
        rw [e]
      have hn : ((XMach.act xs ((PMach.init X nt).trace xs σ i).1.mem.mem.toX
          (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem)).1.agents.map
            Prod.fst).Nodup := by
        rw [emem, ← hstep]
        exact nd (i + 1)
      obtain ⟨s₁, s₂, s₃, s₄⟩ := PMach.step_shadow xs ok hT hn
      rw [emem] at s₁ s₃
      have es : XMach.packRun xs σ X nt (i + 1) =
          ((XMach.packRun xs σ X nt i).1 +
              XMach.kcost xs ((XMach.init X nt).trace xs σ i).1.mem
                (XMach.packRun xs σ X nt i).2.2.1
                (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD [])
                (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem),
            (XMach.packRun xs σ X nt i).2.1 +
              XMach.jskips (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD [])
                (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem),
            XMach.klog xs ((XMach.init X nt).trace xs σ i).1.mem
              (XMach.packRun xs σ X nt i).2.2.1
              (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem),
            (XMach.packRun xs σ X nt i).2.2.2.set (σ i)
              (XMach.jflags (XMach.packRun xs σ X nt i).2.2.1
                (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD [])
                (T.toX ((PMach.init X nt).trace xs σ i).1.mem.mem))) := by
        show (match ((XMach.init X nt).trace xs σ i).1.ths[σ i]? with
          | some T =>
            ((XMach.packRun xs σ X nt i).1 +
                XMach.kcost xs ((XMach.init X nt).trace xs σ i).1.mem
                  (XMach.packRun xs σ X nt i).2.2.1
                  (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
              (XMach.packRun xs σ X nt i).2.1 +
                XMach.jskips (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD []) T,
              XMach.klog xs ((XMach.init X nt).trace xs σ i).1.mem
                (XMach.packRun xs σ X nt i).2.2.1 T,
              (XMach.packRun xs σ X nt i).2.2.2.set (σ i)
                (XMach.jflags (XMach.packRun xs σ X nt i).2.2.1
                  (((XMach.packRun xs σ X nt i).2.2.2[σ i]?).getD []) T))
          | none => XMach.packRun xs σ X nt i) = _
        rw [hm']
      rw [es, hfl]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show (PMach.init X nt).time xs σ i +
          ((PMach.init X nt).trace xs σ i).1.stepCost xs (σ i) = _
        rw [s₁, ih₁, ih₃]
      · show (PMach.init X nt).skips xs σ i +
          ((PMach.init X nt).trace xs σ i).1.stepSkips (σ i) = _
        rw [s₂, ih₂]
      · show (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.mem.flags = _
        rw [s₃, ih₃]
      · show (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.ths.map
          (LThread.flags (((PMach.init X nt).trace xs σ i).1.step xs (σ i)).1.mem.mem) = _
        rw [s₄, ih₃, ih₄]

/-- Every thread is idle with nothing left in its list, dead cells
included. -/
def PMach.resting (M : PMach S) : Bool := M.ths.all fun T => T.raw.isEmpty && T.st.isIdle

theorem PMach.step_resting (xs : XSys S) {M : PMach S} (h : M.resting = true) (t : Nat) :
    M.step xs t = (M, 0) ∧ M.stepCost xs t = 0 := by
  cases ht : M.ths[t]? with
  | none =>
    refine ⟨?_, ?_⟩
    · unfold PMach.step
      rw [ht]
    · unfold PMach.stepCost
      rw [ht]
  | some T =>
    have hT := List.all_eq_true.1 h T (List.mem_of_getElem? ht)
    obtain ⟨raw, snap, s⟩ := T
    cases raw with
    | cons x r => cases hT
    | nil =>
      cases s with
      | idle =>
        refine ⟨?_, ?_⟩
        · unfold PMach.step
          rw [ht]
          show ((⟨M.mem, M.ths.set t ⟨[], snap, .idle⟩⟩ : PMach S), 0) = (M, 0)
          rw [set_self M.ths t _ ht]
        · unfold PMach.stepCost
          rw [ht]
          rfl
      | look a α => cases hT
      | seek a α p c => cases hT
      | ready a b α β => cases hT
      | half a b α β => cases hT
      | write as ls => cases hT

/-- Once the program on the packing memory is at rest it stays as it is,
and so does its time. -/
theorem PMach.time_rest {M : PMach S} (σ : Nat → Nat) {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) :
    ∀ d, (M.trace xs σ (B + d)).1 = (M.trace xs σ B).1 ∧
      M.time xs σ (B + d) = M.time xs σ B
  | 0 => ⟨rfl, rfl⟩
  | d + 1 => by
    obtain ⟨e₁, e₂⟩ := PMach.time_rest σ h d
    have hr : (M.trace xs σ (B + d)).1.resting = true := by
      rw [e₁]
      exact h
    obtain ⟨s₁, s₂⟩ := PMach.step_resting xs hr (σ (B + d))
    refine ⟨?_, ?_⟩
    · show ((M.trace xs σ (B + d)).1.step xs (σ (B + d))).1 = _
      rw [s₁]
      exact e₁
    · show M.time xs σ (B + d) + (M.trace xs σ (B + d)).1.stepCost xs (σ (B + d)) = _
      rw [s₂, Nat.add_zero]
      exact e₂

theorem PMach.resting_of_flags {M : PMach S} (hX : M.toX.resting = true)
    (hf : (M.ths.map (LThread.flags M.mem.mem)).all List.isEmpty = true) :
    M.resting = true := by
  refine List.all_eq_true.2 fun T hT => ?_
  have h₁ : (T.flags M.mem.mem).isEmpty = true :=
    List.all_eq_true.1 hf _ (List.mem_map_of_mem hT)
  have h₂ : ((T.toX M.mem.mem).todo.isEmpty && (T.toX M.mem.mem).st.isIdle) = true :=
    List.all_eq_true.1 hX _ (List.mem_map_of_mem hT)
  have h₃ : T.st.isIdle = true := (Bool.and_eq_true _ _ ▸ h₂ : _ ∧ _).2
  have h₄ : T.raw.isEmpty = true := by
    obtain ⟨raw, snap, s⟩ := T
    cases raw with
    | nil => rfl
    | cons x r => cases h₁
  rw [h₃, h₄]
  rfl

end Packed

end INet
