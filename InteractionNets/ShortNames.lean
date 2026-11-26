import InteractionNets.IndexedJoin
import Std.Data.HashMap

/-! # Short names at the start

On the indexed memory an operation on a map counts one, but hashing a name
takes time with its length, and the net of a nested expression names its
agents by their depth: on `((5 + 0) + 0) + …` with 1,024 additions the
longest name has 1,025 cells before anything runs (`MeasureJoin`).  Here
every identifier in use is renamed, before the run, to a name of one cell,
its place in the list of identifiers of the net (`XNet.short`).  That is a
renaming (`XNet.short_renaming`), so the net stays well formed and lists no
name twice (`XNet.short_wf`, `XNet.short_nodup`), has as many agents and
segments (`XNet.short_agents_length`, `XNet.short_wires_length`), every
name in it has one cell (`XNet.short_names`), and it reduces in the same
number of steps to the renamed normal form (`XNet.short_steps`).  So every
bound proved for a net holds for its short form with the same figures
(`IJMach.time_short`, `Arith.Expr.itime_short`), and the program computes
the normal form of the input up to the renaming.  Names still gain a cell
at most at each step during the run; that the time of an operation then
stays near a constant is measured (`MeasureJoin`), not proved. -/

namespace INet

variable {S : Type}

/-- The identifiers a net mentions: its agents, its free ports and the ends
of its segments, in that order, with repetitions. -/
def XNet.allIds (X : XNet S) : List Id :=
  X.agents.map (·.1) ++ X.free.map (·.1) ++ X.wires.flatMap (fun e => [e.1.1, e.2.1])

/-- The first place of an identifier in a list. -/
def firstIdx : List Id → Id → Option Nat
  | [], _ => none
  | x :: xs, i => if x = i then some 0 else (firstIdx xs i).map (· + 1)

theorem firstIdx_get : ∀ {l : List Id} {i : Id} {k : Nat}, firstIdx l i = some k → l[k]? = some i
  | [], _, _, h => by cases h
  | x :: xs, i, k, h => by
    unfold firstIdx at h
    by_cases hx : x = i
    · rw [ite_pos' hx] at h
      cases h
      rw [hx]
      rfl
    · rw [ite_neg' hx] at h
      cases hk : firstIdx xs i with
      | none => rw [hk] at h; cases h
      | some k' =>
        rw [hk] at h
        cases h
        show xs[k']? = some i
        exact firstIdx_get hk

theorem firstIdx_mem : ∀ {l : List Id} {i : Id}, i ∈ l → ∃ k, firstIdx l i = some k
  | [], _, h => by cases h
  | x :: xs, i, h => by
    unfold firstIdx
    by_cases hx : x = i
    · exact ⟨0, by rw [ite_pos' hx]⟩
    · rw [ite_neg' hx]
      have hm : i ∈ xs := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm hx
        · exact e
      obtain ⟨k, hk⟩ := firstIdx_mem hm
      exact ⟨k + 1, by rw [hk]; rfl⟩

/-- **The short name of an identifier**: its first place among the
identifiers of the net, as a name of one cell.  An identifier the net does
not mention keeps its name. -/
def XNet.shortName (X : XNet S) (i : Id) : Id :=
  match firstIdx X.allIds i with
  | some k => [k]
  | none => i

/-- The first places of the identifiers of a list, counted from `k`, in a
hash map: built once, so that renaming a net takes one lookup a name. -/
def idxMap : List Id → Nat → Std.HashMap Id Nat
  | [], _ => ∅
  | x :: xs, k => (idxMap xs (k + 1)).insert x k

theorem idxMap_get : ∀ (l : List Id) (k : Nat) (i : Id),
    (idxMap l k)[i]? = (firstIdx l i).map (· + k)
  | [], _, _ => Std.HashMap.getElem?_empty
  | x :: xs, k, i => by
    show ((idxMap xs (k + 1)).insert x k)[i]? = _
    rw [Std.HashMap.getElem?_insert, idxMap_get xs (k + 1) i]
    have e : firstIdx (x :: xs) i = if x = i then some 0 else (firstIdx xs i).map (· + 1) := rfl
    rw [e]
    by_cases hx : x = i
    · rw [ite_pos' hx, hx]
      simp
    · rw [ite_neg' hx]
      have : (x == i) = false := by simpa using hx
      rw [this]
      cases firstIdx xs i with
      | none => rfl
      | some j =>
        show some (j + (k + 1)) = some (j + 1 + k)
        rw [Nat.add_comm k 1, Nat.add_assoc]

/-- **The net with short names**, renamed through the map of first places,
built once. -/
def XNet.short (X : XNet S) : XNet S :=
  let m := idxMap X.allIds 0
  X.map fun i =>
    match m[i]? with
    | some k => [k]
    | none => i

/-- The short form is the net renamed by `XNet.shortName`. -/
theorem XNet.short_eq (X : XNet S) : X.short = X.map X.shortName := by
  unfold XNet.short
  dsimp only
  congr 1
  funext i
  unfold XNet.shortName
  rw [idxMap_get]
  cases firstIdx X.allIds i with
  | none => rfl
  | some k => rfl

theorem XNet.used_ids {X : XNet S} {i : Id} (h : X.toNet.Used i) : i ∈ X.allIds := by
  unfold XNet.allIds
  rcases h with ⟨γ, hg⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨(i, γ), hg, rfl⟩))
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨((i, k), q), hl, ?_⟩)
    exact List.mem_cons_self
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨(i, k), hf, rfl⟩))

theorem XNet.shortName_of_mem {X : XNet S} {i : Id} (h : i ∈ X.allIds) :
    ∃ k, X.shortName i = [k] ∧ X.allIds[k]? = some i := by
  obtain ⟨k, hk⟩ := firstIdx_mem h
  refine ⟨k, ?_, firstIdx_get hk⟩
  unfold XNet.shortName
  rw [hk]

theorem XNet.shortName_inj {X : XNet S} {i j : Id} (hi : i ∈ X.allIds) (hj : j ∈ X.allIds)
    (e : X.shortName i = X.shortName j) : i = j := by
  obtain ⟨k, ek, gk⟩ := XNet.shortName_of_mem hi
  obtain ⟨k', ek', gk'⟩ := XNet.shortName_of_mem hj
  rw [ek, ek'] at e
  cases e
  rw [gk] at gk'
  cases gk'
  rfl

/-- **Short names are a renaming** of the net: names in use stay apart, and
no name in use extends the name of a live agent. -/
theorem XNet.short_renaming (X : XNet S) : Renaming X.shortName X.toNet where
  inj := fun hi hj e => XNet.shortName_inj (XNet.used_ids hi) (XNet.used_ids hj) e
  fresh := fun {a α i} l ha hi e => by
    obtain ⟨k, ek, -⟩ := XNet.shortName_of_mem (XNet.used_ids (X := X) (.inl ⟨α, ha⟩))
    obtain ⟨k', ek', -⟩ := XNet.shortName_of_mem (XNet.used_ids hi)
    rw [ek, ek'] at e
    have := congrArg List.length e
    simp only [List.length_cons, List.length_nil, List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)

theorem XNet.short_toNet (X : XNet S) : X.short.toNet = X.toNet.map X.shortName := by
  rw [XNet.short_eq]
  exact XNet.map_toNet _ _

/-- The short form of a well-formed net is well formed. -/
theorem XNet.short_wf {ar : S → Nat} {X : XNet S} (hX : X.toNet.WF ar) : X.short.toNet.WF ar := by
  rw [XNet.short_toNet]
  exact (XNet.short_renaming X).wf_map hX

theorem XNet.short_agents_length (X : XNet S) : X.short.agents.length = X.agents.length := by
  rw [XNet.short_eq]
  exact List.length_map _

theorem XNet.short_wires_length (X : XNet S) : X.short.wires.length = X.wires.length := by
  rw [XNet.short_eq]
  exact List.length_map _

theorem XNet.allIds_map (f : Id → Id) (X : XNet S) :
    (X.map f).allIds = X.allIds.map f := by
  unfold XNet.allIds XNet.map
  simp only [List.map_append, List.map_map, List.flatMap_map, List.map_flatMap]
  rfl

/-- **Every name of the short form has one cell**: the agents, the free
ports and the ends of the segments. -/
theorem XNet.short_names (X : XNet S) : ∀ i ∈ X.short.allIds, i.length = 1 := by
  intro i hi
  rw [XNet.short_eq, XNet.allIds_map] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  obtain ⟨k, ek, -⟩ := XNet.shortName_of_mem hj
  rw [ek]
  rfl

/-- The short form lists no name twice if the net does not. -/
theorem XNet.short_nodup {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) :
    (X.short.agents.map Prod.fst).Nodup := by
  rw [XNet.short_eq]
  show ((X.agents.map fun e => (X.shortName e.1, e.2)).map Prod.fst).Nodup
  rw [List.map_map]
  have hm : ∀ e ∈ X.agents, e.1 ∈ X.allIds := fun e he =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨e, he, rfl⟩))
  have key : ∀ l : List (Id × S), (∀ e ∈ l, e.1 ∈ X.allIds) → (l.map Prod.fst).Nodup →
      (l.map (Prod.fst ∘ fun e => (X.shortName e.1, e.2))).Nodup := by
    intro l
    induction l with
    | nil => intro _ _; exact List.nodup_nil
    | cons e l ih =>
      intro hl hn
      rw [List.map_cons, List.nodup_cons] at hn ⊢
      refine ⟨fun hmem => hn.1 ?_, ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) hn.2⟩
      obtain ⟨e', he', ee⟩ := List.mem_map.1 hmem
      have := XNet.shortName_inj (hl e' (List.mem_cons_of_mem _ he')) (hl e List.mem_cons_self) ee
      exact List.mem_map.2 ⟨e', he', this⟩
  exact key X.agents hm hnd

variable [DecidableEq S] {sys : System S}

omit [DecidableEq S] in
/-- **The short form reduces as the net does**: in the same number of steps,
to the normal form renamed by a renaming that agrees with the short names
on every name of the net. -/
theorem XNet.short_steps {X : XNet S} (hX : X.toNet.WF sys.ar) {n : Nat} {N' : Net S}
    (hs : Steps (Step sys) n X.toNet N') (hn : Normal (Step sys) N') :
    ∃ g, Renaming g N' ∧ (∀ i, X.toNet.Used i → g i = X.shortName i) ∧
      Steps (Step sys) n X.short.toNet (N'.map g) ∧ Normal (Step sys) (N'.map g) := by
  obtain ⟨g, hg, e, s⟩ := Steps.map hX (XNet.short_renaming X) hs
  refine ⟨g, hg, e, ?_, (hg.normal (Steps.wf hX hs)).1 hn⟩
  rw [XNet.short_toNet]
  exact s

variable {xs : XSys S}

/-- **The time bound holds for the short form with the same figures**: the
busy-first schedule of `IJMach.time_bfSched`, on the net renamed to names
of one cell. -/
theorem IJMach.time_short {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (i : Nat) :
    (IJMach.init X.short nt).time xs (JMach.bfSched xs (JMach.init X.short nt) nt) i ≤
      (2 * C + 3 * D + 6) *
      (nt * (7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) +
        7 * (C * n) + (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n))) := by
  obtain ⟨g, -, -, hs', hn'⟩ := XNet.short_steps hX hs hn
  have k := IJMach.time_bfSched hJ (XNet.short_wf hX) (XNet.short_nodup hnd) hnt hb hs' hn' i
  rw [XNet.short_agents_length, XNet.short_wires_length] at k
  exact k

/-- **Every expression of additions, renamed short**: the bound of
`Arith.Expr.itime_bfSched` on the net with names of one cell. -/
theorem Arith.Expr.itime_short (e : Arith.Expr) {nt : Nat} (hnt : 0 < nt) (i : Nat) :
    (IJMach.init e.net.short nt).time Arith.xsys
        (JMach.bfSched Arith.xsys (JMach.init e.net.short nt) nt) i ≤
      (2 * 2 + 3 * 8 + 6) *
      (nt * (7 * e.net.agents.length + (e.net.wires.length + 8 * e.cost)) +
        e.cost * (2 + 8 + 1 + 9 * 1) + 7 * (2 * e.cost) + (e.net.wires.length + 8 * e.cost) +
        1 * (4 * ((e.net.wires.length + 8 * e.cost) *
          Nat.log2 (e.net.wires.length + 8 * e.cost + 1)) +
          6 * (e.net.wires.length + 8 * e.cost))) := by
  obtain ⟨hX, -, N', hs, -, hno⟩ := Arith.Expr.good e
  exact IJMach.time_short Arith.xsys_joinsAtMost hX (Arith.Expr.net_nodup e) hnt
    Arith.xsys_bounded hs (Arith.normal_of_no_add hno) i

end INet
