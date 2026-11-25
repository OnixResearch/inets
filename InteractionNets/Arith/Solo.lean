import InteractionNets.Arith.Correct

/-! ### One thread on an addition: the rounds and the memory they leave -/

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

namespace Arith

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

variable {j m n : Nat}

local macro "ports_differ" : tactic =>
  `(tactic| first | (intro e; simp at e; done) | (intro e; simp at e; omega))

/-- The memory after the first round: the successor `s` has fired with the
adder `a`. -/
def stepS (X : XNet Arith) (s a : Id) : XNet Arith :=
  (((X.takeAgent s).takeAgent a).putAgents (addSucc.swap.toX.newAgents s a)).putLinks
    (addSucc.swap.toX.newLinks xsys.sys.ar s a .succ .add)

/-- The memory after a later round: the adder `a` has fired with the
successor `s`. -/
def stepA (X : XNet Arith) (a s : Id) : XNet Arith :=
  (((X.takeAgent a).takeAgent s).putAgents (addSucc.toX.newAgents a s)).putLinks
    (addSucc.toX.newLinks xsys.sys.ar a s .add .succ)

/-- The memory after the last round: the adder `a` has fired with the zero
`z`. -/
def stepZ (X : XNet Arith) (a z : Id) : XNet Arith :=
  (((X.takeAgent a).takeAgent z).putAgents (addZero.toX.newAgents a z)).putLinks
    (addZero.toX.newLinks xsys.sys.ar a z .add .zero)

theorem newLinks_zero (a z : Id) : addZero.toX.newLinks ar a z .add .zero =
    [((a, 1), (a, 2)), ((a, 2), (a, 1))] := rfl

theorem newAgents_zero (a z : Id) : addZero.toX.newAgents a z = [] := rfl

/-- **The first round, with the memory it leaves**: sixteen actions,
charged fifteen operations on the maps of agents and eighteen on the map
of segments. -/
theorem Start.round_exact {n : Nat} {X : XNet Arith} {hi : Nat} (st : Start n X hi) :
    Opers xsys X ⟨X.agents, .idle⟩ (stepS X [hi + 1] [1])
        ⟨(stepS X [hi + 1] [1]).agents, .idle⟩ 1 16 15 18 ∧
      Steady n (stepS X [hi + 1] [1]) hi := by
  obtain ⟨rest, hA⟩ := st.head
  have ht := st.top
  have hne : ([hi + 1] : Id) ≠ [1] := fun e => by
    injection e with e1
    omega
  have hne' : ([1] : Id) ≠ [hi + 1] := fun e => hne e.symm
  have h₁ : assoc [hi + 1] X.agents = some .succ := by
    rw [hA]
    show (if ([hi + 1] : Id) = [hi + 1] then some Arith.succ else assoc _ rest) = _
    rw [ite_pos' rfl]
  have h₂ : assoc (([hi + 1], 0) : Port) X.wires = some ([1], 0) :=
    assoc_eq_of_unique ((st.first _).2 rfl) (fun q' hq => (st.first q').1 hq)
  have h₄ : assoc [1] (X.takeAgent [hi + 1]).agents = some .add := by
    show assoc [1] (X.agents.filter fun e => decide (e.1 ≠ [hi + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact st.adder
  have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
  have w := Opers.claim_direct (xs := xsys) rest h₁ h₂ st.adder hne h₄ hR
  rw [← hA] at w
  have eA := newAgents_swap (a := [1]) (s := [hi + 1]) hne'
  have eK : 5 + ((addSucc.swap.toX.newAgents [hi + 1] [1]).length +
      (addSucc.swap.toX.newLinks xsys.sys.ar [hi + 1] [1] .succ .add).length + 1) = 16 := by
    rw [eA]
    rfl
  have eW : 11 + 2 * (addSucc.swap.toX.newAgents [hi + 1] [1]).length = 15 := by
    rw [eA]
    rfl
  have eL : 2 + 2 * (addSucc.swap.toX.newLinks xsys.sys.ar [hi + 1] [1] .succ .add).length =
      18 := rfl
  rw [eK, eW, eL] at w
  refine ⟨w, ?_⟩
  unfold stepS
  have SL := stepLinks_swap (a := [1]) (s := [hi + 1]) hne'
    (fun e => by injection e with _ e2; cases e2)
  refine steady_of_step SL (fun e => XNet.mem_step_wires X _ _ _ _ e) ?_ ?_ ?_ ?_ st.chain
    st.fresh ht
  · rw [eA, XNet.step_agents]
    exact ⟨_, rfl⟩
  · intro t ht1 ht2
    have n1 : ¬ ([0, hi + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n2 : ¬ ([0, 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n3 : ¬ ([1] : Id) = [t] := fun e => by injection e with e1; omega
    have n4 : ¬ ([hi + 1] : Id) = [t] := fun e => by injection e with e1; omega
    rw [eA, XNet.step_agents]
    show (if ([0, hi + 1] : Id) = [t] then some Arith.add
      else if ([0, 1] : Id) = [t] then some Arith.succ
      else assoc [t] ((X.agents.filter fun e => decide (e.1 ≠ [hi + 1])).filter
        fun e => decide (e.1 ≠ [1]))) = _
    rw [ite_neg' n1, ite_neg' n2, assoc_filter_ne, ite_neg' n3, assoc_filter_ne, ite_neg' n4]
  · intro t ht1 e
    injection e with e1
    omega
  · intro t _ _ e
    injection e with _ e2
    cases e2

/-- **A later round, with the memory it leaves**: seventeen actions,
charged sixteen operations on the maps of agents and nineteen on the map
of segments. -/
theorem Steady.round_exact {n : Nat} {X : XNet Arith} {h : Nat} (st : Steady n X (h + 1))
    (hn : n + 4 ≤ h + 1) :
    Opers xsys X ⟨X.agents, .idle⟩ (stepA X [0, h + 1 + 1] [h + 1])
        ⟨(stepA X [0, h + 1 + 1] [h + 1]).agents, .idle⟩ 1 17 16 19 ∧
      Steady n (stepA X [0, h + 1 + 1] [h + 1]) h := by
  obtain ⟨rest, hA⟩ := st.head
  have hb : below n (h + 1) = [h + 1] := below_pos hn
  have hne : ([0, h + 1 + 1] : Id) ≠ [h + 1] := fun e => by
    injection e with _ e2
    cases e2
  have h₁ : assoc [0, h + 1 + 1] X.agents = some .add := by
    rw [hA]
    show (if ([0, h + 1 + 1] : Id) = [0, h + 1 + 1] then some Arith.add
      else assoc _ rest) = _
    rw [ite_pos' rfl]
  have h₂ : assoc (([0, h + 1 + 1], 0) : Port) X.wires = some ([h + 1 + 1], 1) :=
    assoc_eq_of_unique ((st.first _).2 rfl) (fun q' hq => (st.first q').1 hq)
  have h₂' : nextSeg X.wires ([h + 1 + 1], 1) ([0, h + 1 + 1], 0) = some ([h + 1], 0) := by
    refine nextSeg_some ((st.mid _).2 (.inr (by rw [hb]))) (fun e => ?_) (fun q hq hqp => ?_)
    · injection e with e1 _
      injection e1 with _ e2
      cases e2
    · rcases (st.mid q).1 hq with e | e
      · exact absurd e hqp
      · rw [e, hb]
  have h₃ : assoc [h + 1] X.agents = some .succ := st.chain.live (h + 1) hn (Nat.le_refl _)
  have h₄ : assoc [h + 1] (X.takeAgent [0, h + 1 + 1]).agents = some .succ := by
    show assoc [h + 1] (X.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact h₃
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w := Opers.claim_via (xs := xsys) (c := ([h + 1 + 1], 1)) rest h₁ h₂ rfl h₂' h₃ hne h₄ hR
  rw [← hA] at w
  have eA := newAgents_add (a := [0, h + 1 + 1]) (s := [h + 1]) hne
  have eK : 6 + ((addSucc.toX.newAgents [0, h + 1 + 1] [h + 1]).length +
      (addSucc.toX.newLinks xsys.sys.ar [0, h + 1 + 1] [h + 1] .add .succ).length + 1) =
      17 := by
    rw [eA]
    rfl
  have eW : 12 + 2 * (addSucc.toX.newAgents [0, h + 1 + 1] [h + 1]).length = 16 := by
    rw [eA]
    rfl
  have eL : 3 + 2 *
      (addSucc.toX.newLinks xsys.sys.ar [0, h + 1 + 1] [h + 1] .add .succ).length = 19 := rfl
  rw [eK, eW, eL] at w
  refine ⟨w, ?_⟩
  unfold stepA
  have SL := stepLinks_add (a := [0, h + 1 + 1]) (s := [h + 1]) hne
    (fun e => by injection e with _ e2; cases e2)
  refine steady_of_step SL (fun e => XNet.mem_step_wires X _ _ _ _ e) ?_ ?_ ?_ ?_ st.chain
    st.fresh hn
  · rw [eA, XNet.step_agents]
    exact ⟨_, rfl⟩
  · intro t ht1 ht2
    have n1 : ¬ ([0, h + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n2 : ¬ ([0, 0, h + 1 + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    have n3 : ¬ ([h + 1] : Id) = [t] := fun e => by injection e with e1; omega
    have n4 : ¬ ([0, h + 1 + 1] : Id) = [t] := fun e => by injection e with _ e2; cases e2
    rw [eA, XNet.step_agents]
    show (if ([0, h + 1] : Id) = [t] then some Arith.add
      else if ([0, 0, h + 1 + 1] : Id) = [t] then some Arith.succ
      else assoc [t] ((X.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])).filter
        fun e => decide (e.1 ≠ [h + 1]))) = _
    rw [ite_neg' n1, ite_neg' n2, assoc_filter_ne, ite_neg' n3, assoc_filter_ne, ite_neg' n4]
  · intro t _ e
    injection e with _ e2
    cases e2
  · intro t _ ht2 e
    injection e with _ e2
    injection e2 with e3
    omega

/-- **The last round**: the adder fires with the zero at the end of the
chain, in nine actions charged twelve operations on the maps of agents
and seven on the map of segments, and writes two segments. -/
theorem Steady.zero_round {n : Nat} {X : XNet Arith} (st : Steady n X (n + 3))
    (hz : assoc [2] X.agents = some .zero) :
    Opers xsys X ⟨X.agents, .idle⟩ (stepZ X [0, n + 3 + 1] [2])
      ⟨(stepZ X [0, n + 3 + 1] [2]).agents, .idle⟩ 1 9 12 7 := by
  obtain ⟨rest, hA⟩ := st.head
  have hb : below n (n + 3) = [2] := by
    unfold below
    rw [ite_neg' (by omega)]
  have hne : ([0, n + 3 + 1] : Id) ≠ [2] := fun e => by
    injection e with _ e2
    cases e2
  have h₁ : assoc [0, n + 3 + 1] X.agents = some .add := by
    rw [hA]
    show (if ([0, n + 3 + 1] : Id) = [0, n + 3 + 1] then some Arith.add
      else assoc _ rest) = _
    rw [ite_pos' rfl]
  have h₂ : assoc (([0, n + 3 + 1], 0) : Port) X.wires = some ([n + 3 + 1], 1) :=
    assoc_eq_of_unique ((st.first _).2 rfl) (fun q' hq => (st.first q').1 hq)
  have h₂' : nextSeg X.wires ([n + 3 + 1], 1) ([0, n + 3 + 1], 0) = some ([2], 0) := by
    refine nextSeg_some ((st.mid _).2 (.inr (by rw [hb]))) (fun e => ?_) (fun q hq hqp => ?_)
    · injection e with e1 _
      injection e1 with _ e2
      cases e2
    · rcases (st.mid q).1 hq with e | e
      · exact absurd e hqp
      · rw [e, hb]
  have h₄ : assoc [2] (X.takeAgent [0, n + 3 + 1]).agents = some .zero := by
    show assoc [2] (X.agents.filter fun e => decide (e.1 ≠ [0, n + 3 + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact hz
  have hR : xsys.rule .add .zero = some addZero.toX := rfl
  have w := Opers.claim_via (xs := xsys) (c := ([n + 3 + 1], 1)) rest h₁ h₂ rfl h₂' hz hne h₄ hR
  rw [← hA] at w
  exact w

/-- The segments the first round writes: the successor `[T]` meets the
adder `[1]`. -/
def linksS (T : Nat) : List (Port × Port) :=
  addSucc.swap.toX.newLinks ar [T] [1] .succ .add

/-- The segments a later round writes: the adder `[0, t + 1]` meets the
successor `[t]`. -/
def linksA (t : Nat) : List (Port × Port) :=
  addSucc.toX.newLinks ar [0, t + 1] [t] .add .succ

/-- The segments the last round writes: the adder `[0, t]` meets the zero. -/
def linksZ (t : Nat) : List (Port × Port) :=
  addZero.toX.newLinks ar [0, t] [2] .add .zero

theorem mem_linksS (T : Nat) (p q : Port) : ((p, q) : Port × Port) ∈ linksS T ↔
    p = ([T], 1) ∧ q = ([0, T], 0) ∨ p = ([1], 1) ∧ q = ([0, T], 1) ∨
    p = ([1], 2) ∧ q = ([0, 1], 0) ∨ p = ([0, 1], 0) ∧ q = ([1], 2) ∨
    p = ([0, 1], 1) ∧ q = ([0, T], 2) ∨ p = ([0, T], 0) ∧ q = ([T], 1) ∨
    p = ([0, T], 1) ∧ q = ([1], 1) ∨ p = ([0, T], 2) ∧ q = ([0, 1], 1) := by
  unfold linksS
  rw [newLinks_swap]
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false]

theorem mem_linksA (t : Nat) (p q : Port) : ((p, q) : Port × Port) ∈ linksA t ↔
    p = ([0, t + 1], 1) ∧ q = ([0, t], 1) ∨ p = ([0, t + 1], 2) ∧ q = ([0, 0, t + 1], 0) ∨
    p = ([t], 1) ∧ q = ([0, t], 0) ∨ p = ([0, 0, t + 1], 0) ∧ q = ([0, t + 1], 2) ∨
    p = ([0, 0, t + 1], 1) ∧ q = ([0, t], 2) ∨ p = ([0, t], 0) ∧ q = ([t], 1) ∨
    p = ([0, t], 1) ∧ q = ([0, t + 1], 1) ∨ p = ([0, t], 2) ∧ q = ([0, 0, t + 1], 1) := by
  unfold linksA
  rw [newLinks_add]
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false]

theorem mem_linksZ (t : Nat) (p q : Port) : ((p, q) : Port × Port) ∈ linksZ t ↔
    p = ([0, t], 1) ∧ q = ([0, t], 2) ∨ p = ([0, t], 2) ∧ q = ([0, t], 1) := by
  unfold linksZ
  rw [newLinks_zero]
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false]

/-- **The second argument and the result wire**, as the rounds leave
them: the segments at the ports of the second chain, of the second
argument of the first adder and of its result. -/
structure Snd (n : Nat) (X : XNet Arith) : Prop where
  one : ∀ q, ((([1], 1), q) : Port × Port) ∈ X.wires ↔ q = ([n + 3], 0)
  top : ∀ q, ((([n + 3], 0), q) : Port × Port) ∈ X.wires ↔ q = ([1], 1)
  up : ∀ j, 3 ≤ j → j ≤ n + 2 → ∀ q,
    ((([j], 0), q) : Port × Port) ∈ X.wires ↔ q = ([j + 1], 1)
  down : ∀ j, 3 ≤ j → j ≤ n + 2 → ∀ q,
    ((([j + 1], 1), q) : Port × Port) ∈ X.wires ↔ q = ([j], 0)
  res : ∀ q, ((([1], 2), q) : Port × Port) ∈ X.wires ↔ q = ([0], 0)
  out : ∀ q, ((([0], 0), q) : Port × Port) ∈ X.wires ↔ q = ([1], 2)

theorem base_port (p q0 : Port) (hall : ∀ e ∈ base.wires, e.1 = p → e.2 = q0)
    (hmem : ((p, q0) : Port × Port) ∈ base.wires) (q : Port) :
    ((p, q) : Port × Port) ∈ base.wires ↔ q = q0 :=
  ⟨fun h => hall _ h rfl, fun e => by rw [e]; exact hmem⟩

theorem snd_sumSnd : ∀ n, Snd n (sumSnd n)
  | 0 =>
    ⟨base_port _ _ (by decide) (by decide), base_port _ _ (by decide) (by decide),
      fun j h1 h2 => absurd h2 (by omega), fun j h1 h2 => absurd h2 (by omega),
      base_port _ _ (by decide) (by decide), base_port _ _ (by decide) (by decide)⟩
  | n + 1 => by
    have S := snd_sumSnd n
    have hassoc : assoc (([1], 1) : Port) (sumSnd n).wires = some ([n + 3], 0) :=
      assoc_eq_of_unique ((S.one _).2 rfl) (fun q' hq => (S.one q').1 hq)
    have e : sumSnd (n + 1) = (sumSnd n).insert1 [n + 4] .succ ([1], 1) ([n + 3], 0) :=
      push_some [n + 4] hassoc
    have hfresh : ∀ k q, ((([n + 4], k), q) : Port × Port) ∉ (sumSnd n).wires := by
      intro k q hm
      obtain ⟨j, hj, ej⟩ := (good_sumSnd n).below [n + 4] (.inr (.inl ⟨k, q, hm⟩))
      injection ej with e1
      omega
    obtain ⟨N1, N2, N3, N4⟩ := insert1_new (sumSnd n) [n + 4] .succ ([1], 1) ([n + 3], 0)
      (by ports_differ) (by ports_differ) (by ports_differ) hfresh
    rw [e]
    refine ⟨fun q => N1 q, fun q => N2 q, fun j h1 h2 q => ?_, fun j h1 h2 q => ?_,
      fun q => ?_, fun q => ?_⟩
    · by_cases hj : j = n + 3
      · rw [hj]
        exact N4 q
      · rw [insert1_frame (sumSnd n) [n + 4] .succ ([1], 1) ([n + 3], 0) ([j], 0)
          (by ports_differ) (by ports_differ) (by ports_differ)]
        exact S.up j h1 (by omega) q
    · by_cases hj : j = n + 3
      · rw [hj]
        exact N3 q
      · rw [insert1_frame (sumSnd n) [n + 4] .succ ([1], 1) ([n + 3], 0) ([j + 1], 1)
          (by ports_differ) (by ports_differ) (by ports_differ)]
        exact S.down j h1 (by omega) q
    · rw [insert1_frame (sumSnd n) [n + 4] .succ ([1], 1) ([n + 3], 0) ([1], 2)
        (by ports_differ) (by ports_differ) (by ports_differ)]
      exact S.res q
    · rw [insert1_frame (sumSnd n) [n + 4] .succ ([1], 1) ([n + 3], 0) ([0], 0)
        (by ports_differ) (by ports_differ) (by ports_differ)]
      exact S.out q

theorem Snd.insert {n : Nat} {X : XNet Arith} (S : Snd n X) {u : Nat} {b : Id}
    (hu : n + 4 ≤ u) (hb : b = [2] ∨ ∃ t, n + 4 ≤ t ∧ b = [t]) :
    Snd n (X.insert1 [u] .succ ([1], 0) (b, 0)) := by
  have hb' : ∀ j, (j ≤ 1 ∨ 3 ≤ j) → j ≤ n + 3 → ([j], 0) ≠ ((b, 0) : Port) := by
    intro j h1 h2 e
    injection e with e1 _
    rcases hb with hb | ⟨t, ht, hb⟩
    · rw [hb] at e1
      injection e1 with e2
      omega
    · rw [hb] at e1
      injection e1 with e2
      omega
  refine ⟨fun q => ?_, fun q => ?_, fun j h1 h2 q => ?_, fun j h1 h2 q => ?_,
    fun q => ?_, fun q => ?_⟩
  · rw [insert1_frame X [u] .succ ([1], 0) (b, 0) ([1], 1)
      (by ports_differ) (by ports_differ) (by ports_differ)]
    exact S.one q
  · rw [insert1_frame X [u] .succ ([1], 0) (b, 0) ([n + 3], 0)
      (by ports_differ) (hb' (n + 3) (by omega) (by omega)) (by ports_differ)]
    exact S.top q
  · rw [insert1_frame X [u] .succ ([1], 0) (b, 0) ([j], 0)
      (by ports_differ) (hb' j (by omega) (by omega)) (by ports_differ)]
    exact S.up j h1 h2 q
  · rw [insert1_frame X [u] .succ ([1], 0) (b, 0) ([j + 1], 1)
      (by ports_differ) (by ports_differ) (by ports_differ)]
    exact S.down j h1 h2 q
  · rw [insert1_frame X [u] .succ ([1], 0) (b, 0) ([1], 2)
      (by ports_differ) (by ports_differ) (by ports_differ)]
    exact S.res q
  · rw [insert1_frame X [u] .succ ([1], 0) (b, 0) ([0], 0)
      (by ports_differ) (hb' 0 (by omega) (by omega)) (by ports_differ)]
    exact S.out q

theorem sum_push (m n : Nat) : sum (m + 1) n =
    (sum m n).insert1 [m + n + 4] .succ ([1], 0) (below n (m + n + 3), 0) := by
  have I := (init_sum m n).1
  exact push_some [m + n + 4]
    (assoc_eq_of_unique ((I.princ _).2 rfl) (fun q' hq => (I.princ q').1 hq))

/-- **The second argument is in place in the net for `m + n`.** -/
theorem snd_sum : ∀ m n, Snd n (sum m n)
  | 0, n => snd_sumSnd n
  | m + 1, n => by
    rw [sum_push]
    refine (snd_sum m n).insert (by omega) ?_
    rcases below_cases n (m + n + 3) with ⟨hb, hle⟩ | ⟨hb, -⟩
    · exact .inr ⟨_, hle, hb⟩
    · exact .inl hb

/-- The successors of the second argument, the newest first. -/
def sndL : Nat → List (Id × Arith)
  | 0 => []
  | n + 1 => ([n + 4], .succ) :: sndL n

/-- The successors of the first argument that are left, the top first. -/
def chainL (n : Nat) : Nat → List (Id × Arith)
  | 0 => []
  | r + 1 => ([n + 3 + r + 1], .succ) :: chainL n r

/-- The successors of the result, the newest first. -/
def resL : Nat → Nat → List (Id × Arith)
  | _, 0 => [([0, 1], .succ)]
  | h, d + 1 => ([0, 0, h + 2], .succ) :: resL (h + 1) d

/-- The second argument and the zero of the first, in the order of the
list of agents. -/
def tailA (n : Nat) : List (Id × Arith) := sndL n ++ [([2], .zero), ([3], .zero)]

theorem mem_sndL : ∀ {n : Nat} {e : Id × Arith}, e ∈ sndL n →
    e.2 = .succ ∧ ∃ j, 4 ≤ j ∧ j ≤ n + 3 ∧ e.1 = [j]
  | 0, _, h => by cases h
  | n + 1, e, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨rfl, n + 4, by omega, by omega, rfl⟩
    · obtain ⟨h1, j, h2, h3, h4⟩ := mem_sndL h'
      exact ⟨h1, j, h2, by omega, h4⟩

theorem mem_chainL {n : Nat} : ∀ {r : Nat} {e : Id × Arith}, e ∈ chainL n r →
    e.2 = .succ ∧ ∃ j, n + 4 ≤ j ∧ j ≤ n + 3 + r ∧ e.1 = [j]
  | 0, _, h => by cases h
  | r + 1, e, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨rfl, n + 3 + r + 1, by omega, by omega, rfl⟩
    · obtain ⟨h1, j, h2, h3, h4⟩ := mem_chainL h'
      exact ⟨h1, j, h2, by omega, h4⟩

theorem mem_resL : ∀ {d h : Nat} {e : Id × Arith}, e ∈ resL h d →
    e.2 = .succ ∧ (e.1 = [0, 1] ∨ ∃ x, h + 2 ≤ x ∧ x ≤ h + d + 1 ∧ e.1 = [0, 0, x])
  | 0, h, e, hm => by
    rcases List.mem_cons.1 hm with rfl | h'
    · exact ⟨rfl, .inl rfl⟩
    · cases h'
  | d + 1, h, e, hm => by
    rcases List.mem_cons.1 hm with rfl | h'
    · exact ⟨rfl, .inr ⟨h + 2, by omega, by omega, rfl⟩⟩
    · obtain ⟨h1, h2⟩ := mem_resL h'
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | ⟨x, h3, h4, h5⟩
      · exact .inl h2
      · exact .inr ⟨x, by omega, by omega, h5⟩

theorem mem_tailA {n : Nat} {e : Id × Arith} (h : e ∈ tailA n) :
    ∃ j, 2 ≤ j ∧ j ≤ n + 3 ∧ e.1 = [j] := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨-, j, h1, h2, h3⟩ := mem_sndL h
    exact ⟨j, by omega, h2, h3⟩
  · rcases List.mem_cons.1 h with rfl | h
    · exact ⟨2, by omega, by omega, rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨3, by omega, by omega, rfl⟩
      · cases h

/-- The names of the agents that are not results: one number each. -/
theorem mem_rest {n r : Nat} {e : Id × Arith} (h : e ∈ chainL n r ++ tailA n) :
    ∃ j, 2 ≤ j ∧ j ≤ n + 3 + r ∧ e.1 = [j] := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨-, j, h1, h2, h3⟩ := mem_chainL h
    exact ⟨j, by omega, h2, h3⟩
  · obtain ⟨j, h1, h2, h3⟩ := mem_tailA h
    exact ⟨j, h1, by omega, h3⟩

theorem sumSnd_agents : ∀ n, (sumSnd n).agents = sndL n ++ base.agents
  | 0 => rfl
  | n + 1 => by
    have S := snd_sumSnd n
    have hassoc : assoc (([1], 1) : Port) (sumSnd n).wires = some ([n + 3], 0) :=
      assoc_eq_of_unique ((S.one _).2 rfl) (fun q' hq => (S.one q').1 hq)
    have e : sumSnd (n + 1) = (sumSnd n).insert1 [n + 4] .succ ([1], 1) ([n + 3], 0) :=
      push_some [n + 4] hassoc
    rw [e]
    show ([n + 4], Arith.succ) :: (sumSnd n).agents = ([n + 4], Arith.succ) :: (sndL n ++ _)
    rw [sumSnd_agents n]

/-- **The agents of the net for `m + n`, in order.** -/
theorem sum_agents : ∀ m n, (sum m n).agents = chainL n m ++ (sndL n ++ base.agents)
  | 0, n => sumSnd_agents n
  | m + 1, n => by
    have e : m + n + 4 = n + 3 + m + 1 := by omega
    rw [sum_push]
    show ([m + n + 4], Arith.succ) :: (sum m n).agents =
      ([n + 3 + m + 1], Arith.succ) :: (chainL n m ++ (sndL n ++ base.agents))
    rw [sum_agents m n, e]

/-- **The memory in the middle of the run**, after the first round and
`d` later ones, with `r` successors of the first argument left: the
agents in order, and the segments as those of the net at the start and
those each round wrote. -/
structure Hist (n : Nat) (X0 X : XNet Arith) (T r d : Nat) : Prop where
  top : T = n + 3 + r + d + 1
  agents : X.agents =
    ([0, n + 3 + r + 1], .add) :: (resL (n + 3 + r) d ++ (chainL n r ++ tailA n))
  wires : ∀ e, e ∈ X.wires ↔
    e ∈ X0.wires ∨ e ∈ linksS T ∨ ∃ t, n + 3 + r < t ∧ t < T ∧ e ∈ linksA t

theorem res_ne_single {d h : Nat} {e : Id × Arith} (he : e ∈ resL h d) (t : Nat) :
    e.1 ≠ [t] := by
  intro e'
  rcases (mem_resL he).2 with h1 | ⟨x, -, -, h1⟩ <;> rw [h1] at e' <;>
    injection e' with _ e2 <;> cases e2

theorem res_ne_adder {d h : Nat} {e : Id × Arith} (he : e ∈ resL h d) (t : Nat) (ht : t ≠ 1) :
    e.1 ≠ [0, t] := by
  intro e'
  rcases (mem_resL he).2 with h1 | ⟨x, -, -, h1⟩
  · rw [h1] at e'
    injection e' with _ e2
    injection e2 with e3
    omega
  · rw [h1] at e'
    injection e' with _ e2
    injection e2 with e3 e4
    cases e4

theorem rest_ne_adder {n r : Nat} {e : Id × Arith} (he : e ∈ chainL n r ++ tailA n)
    (t : Nat) : e.1 ≠ [0, t] := by
  intro e'
  obtain ⟨j, -, -, h1⟩ := mem_rest he
  rw [h1] at e'
  injection e' with _ e2
  cases e2

/-- **After the first round.** -/
theorem hist_start {n r : Nat} {X0 : XNet Arith}
    (hA : X0.agents = chainL n (r + 1) ++ (sndL n ++ base.agents)) :
    Hist n X0 (stepS X0 [n + 3 + r + 1] [1]) (n + 3 + r + 1) r 0 := by
  have hne' : ([1] : Id) ≠ [n + 3 + r + 1] := fun e => by
    injection e with e1
    omega
  refine ⟨rfl, ?_, fun e => ?_⟩
  · have f1 : (chainL n (r + 1) ++ (sndL n ++ base.agents)).filter
        (fun e => decide (e.1 ≠ [n + 3 + r + 1])) = chainL n r ++ (sndL n ++ base.agents) := by
      show ((([n + 3 + r + 1], Arith.succ) :: (chainL n r ++ (sndL n ++ base.agents))).filter
        (fun e => decide (e.1 ≠ [n + 3 + r + 1]))) = _
      rw [List.filter_cons_of_neg (by simp)]
      refine filter_keep fun e he e' => ?_
      rcases List.mem_append.1 he with h | h
      · obtain ⟨-, j, -, h2, h3⟩ := mem_chainL h
        rw [h3] at e'
        injection e' with e1
        omega
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨-, j, -, h2, h3⟩ := mem_sndL h
          rw [h3] at e'
          injection e' with e1
          omega
        · have hall : ∀ x ∈ base.agents, x.1 = [1] ∨ x.1 = [2] ∨ x.1 = [3] := by decide
          rcases hall e h with h3 | h3 | h3 <;> rw [h3] at e' <;> injection e' with e1 <;>
            omega
    have f2 : (chainL n r ++ (sndL n ++ base.agents)).filter
        (fun e => decide (e.1 ≠ [1])) = chainL n r ++ tailA n := by
      rw [List.filter_append, List.filter_append]
      have k1 : (chainL n r).filter (fun e => decide (e.1 ≠ [1])) = chainL n r :=
        filter_keep fun e he e' => by
          obtain ⟨-, j, h1, -, h3⟩ := mem_chainL he
          rw [h3] at e'
          injection e' with e1
          omega
      have k2 : (sndL n).filter (fun e => decide (e.1 ≠ [1])) = sndL n :=
        filter_keep fun e he e' => by
          obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
          rw [h3] at e'
          injection e' with e1
          omega
      rw [k1, k2]
      rfl
    unfold stepS
    rw [newAgents_swap hne', XNet.step_agents, hA, f1, f2]
    rfl
  · unfold stepS
    rw [XNet.mem_step_wires]
    show e ∈ linksS (n + 3 + r + 1) ∨ e ∈ X0.wires ↔ _
    constructor
    · rintro (h | h)
      · exact .inr (.inl h)
      · exact .inl h
    · rintro (h | h | ⟨t, h1, h2, -⟩)
      · exact .inr h
      · exact .inl h
      · omega

/-- **A later round keeps the description.** -/
theorem Hist.step {n : Nat} {X0 X : XNet Arith} {T r d : Nat} (H : Hist n X0 X T (r + 1) d) :
    Hist n X0 (stepA X [0, n + 3 + r + 1 + 1] [n + 3 + r + 1]) T r (d + 1) := by
  have hne : ([0, n + 3 + r + 1 + 1] : Id) ≠ [n + 3 + r + 1] := fun e => by
    injection e with _ e2
    cases e2
  have hT := H.top
  refine ⟨by omega, ?_, fun e => ?_⟩
  · have f1 : ((([0, n + 3 + r + 1 + 1], Arith.add) ::
        (resL (n + 3 + r + 1) d ++ (chainL n (r + 1) ++ tailA n))).filter
        (fun e => decide (e.1 ≠ [0, n + 3 + r + 1 + 1]))) =
        resL (n + 3 + r + 1) d ++ (chainL n (r + 1) ++ tailA n) := by
      rw [List.filter_cons_of_neg (by simp)]
      refine filter_keep fun e he => ?_
      rcases List.mem_append.1 he with h | h
      · exact res_ne_adder h _ (by omega)
      · exact rest_ne_adder h _
    have f2 : (resL (n + 3 + r + 1) d ++ (chainL n (r + 1) ++ tailA n)).filter
        (fun e => decide (e.1 ≠ [n + 3 + r + 1])) =
        resL (n + 3 + r + 1) d ++ (chainL n r ++ tailA n) := by
      rw [List.filter_append, filter_keep (fun e he => res_ne_single he _)]
      show _ ++ ((([n + 3 + r + 1], Arith.succ) :: (chainL n r ++ tailA n)).filter
        (fun e => decide (e.1 ≠ [n + 3 + r + 1]))) = _
      have k : (chainL n r ++ tailA n).filter (fun e => decide (e.1 ≠ [n + 3 + r + 1])) =
          chainL n r ++ tailA n :=
        filter_keep fun e he e' => by
          obtain ⟨j, -, h2, h3⟩ := mem_rest he
          rw [h3] at e'
          injection e' with e1
          omega
      rw [List.filter_cons_of_neg (by simp), k]
    have hA : X.agents = ([0, n + 3 + r + 1 + 1], Arith.add) ::
        (resL (n + 3 + r + 1) d ++ (chainL n (r + 1) ++ tailA n)) := H.agents
    unfold stepA
    rw [newAgents_add hne, XNet.step_agents, hA, f1, f2]
    rfl
  · unfold stepA
    rw [XNet.mem_step_wires, H.wires]
    show e ∈ linksA (n + 3 + r + 1) ∨ _ ↔ _
    constructor
    · rintro (h | h | h | ⟨t, h1, h2, h3⟩)
      · exact .inr (.inr ⟨n + 3 + r + 1, by omega, by omega, h⟩)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨t, by omega, h2, h3⟩)
    · rintro (h | h | ⟨t, h1, h2, h3⟩)
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · by_cases ht : t = n + 3 + r + 1
        · rw [ht] at h3
          exact .inl h3
        · exact .inr (.inr (.inr ⟨t, by omega, h2, h3⟩))

/-- **The memory at the end of the rounds**: the agents in order, the
successors of the result and then the second argument, and the segments
as those of the net at the start and those each round wrote. -/
structure Final (n : Nat) (X0 X : XNet Arith) (T d : Nat) : Prop where
  top : T = n + 3 + d + 1
  agents : X.agents = resL (n + 3) d ++ (sndL n ++ [([3], .zero)])
  wires : ∀ e, e ∈ X.wires ↔ e ∈ X0.wires ∨ e ∈ linksS T ∨
    (∃ t, n + 3 < t ∧ t < T ∧ e ∈ linksA t) ∨ e ∈ linksZ (n + 3 + 1)

/-- **The last round leaves the final description.** -/
theorem Hist.final {n : Nat} {X0 X : XNet Arith} {T d : Nat} (H : Hist n X0 X T 0 d) :
    Final n X0 (stepZ X [0, n + 3 + 1] [2]) T d := by
  have hT := H.top
  refine ⟨by omega, ?_, fun e => ?_⟩
  · have hA : X.agents = ([0, n + 3 + 1], Arith.add) :: (resL (n + 3) d ++ tailA n) := H.agents
    have f1 : ((([0, n + 3 + 1], Arith.add) :: (resL (n + 3) d ++ tailA n)).filter
        (fun e => decide (e.1 ≠ [0, n + 3 + 1]))) = resL (n + 3) d ++ tailA n := by
      rw [List.filter_cons_of_neg (by simp)]
      refine filter_keep fun e he => ?_
      rcases List.mem_append.1 he with h | h
      · exact res_ne_adder h _ (by omega)
      · intro e'
        obtain ⟨j, -, -, h3⟩ := mem_tailA h
        rw [h3] at e'
        injection e' with _ e2
        cases e2
    have f2 : (resL (n + 3) d ++ tailA n).filter (fun e => decide (e.1 ≠ [2])) =
        resL (n + 3) d ++ (sndL n ++ [([3], Arith.zero)]) := by
      rw [List.filter_append, filter_keep (fun e he => res_ne_single he _)]
      show _ ++ (List.filter (fun e : Id × Arith => decide (e.1 ≠ [2]))
        (sndL n ++ [([2], Arith.zero), ([3], Arith.zero)])) = _
      have k : (sndL n).filter (fun e => decide (e.1 ≠ [2])) = sndL n :=
        filter_keep fun e he e' => by
          obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
          rw [h3] at e'
          injection e' with e1
          omega
      rw [List.filter_append, k]
      rfl
    unfold stepZ
    rw [XNet.putLinks_agents]
    show ((X.agents.filter (fun e => decide (e.1 ≠ [0, n + 3 + 1]))).filter
      (fun e => decide (e.1 ≠ [2]))) = _
    rw [hA, f1, f2]
  · unfold stepZ
    rw [XNet.mem_step_wires, H.wires]
    show e ∈ linksZ (n + 3 + 1) ∨ _ ↔ _
    constructor
    · rintro (h | h | h | ⟨t, h1, h2, h3⟩)
      · exact .inr (.inr (.inr h))
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl ⟨t, by omega, h2, h3⟩))
    · rintro (h | h | ⟨t, h1, h2, h3⟩ | h)
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr ⟨t, by omega, h2, h3⟩))
      · exact .inl h

/-- The later rounds, with the description carried along. -/
theorem Steady.rounds_hist {n : Nat} {X0 : XNet Arith} {T : Nat} :
    ∀ (r : Nat) {X : XNet Arith} {d : Nat}, Steady n X (n + 3 + r) → Hist n X0 X T r d →
      ∃ X', Opers xsys X ⟨X.agents, .idle⟩ X' ⟨X'.agents, .idle⟩ r (17 * r) (16 * r)
        (19 * r) ∧
        Steady n X' (n + 3) ∧ Hist n X0 X' T 0 (d + r)
  | 0, X, d, st, H => ⟨X, .refl _ _, st, H⟩
  | r + 1, X, d, st, H => by
    have st' : Steady n X (n + 3 + r + 1) := st
    obtain ⟨w, st1⟩ := Steady.round_exact st' (by omega)
    obtain ⟨X', w', st2, H2⟩ := Steady.rounds_hist r st1 H.step
    refine ⟨X', ?_, st2, ?_⟩
    · have w2 := w.trans w'
      have e1 : 1 + r = r + 1 := by omega
      have e2 : 17 + 17 * r = 17 * (r + 1) := by omega
      have e3 : 16 + 16 * r = 16 * (r + 1) := by omega
      have e4 : 19 + 19 * r = 19 * (r + 1) := by omega
      rw [e1, e2, e3, e4] at w2
      exact w2
    · have e : d + 1 + r = d + (r + 1) := by omega
      rw [← e]
      exact H2

/-- **All the rounds of one thread on the net for `(m + 1) + n`**: `m + 2`
claims in `17 * m + 25` actions, charged `16 * m + 27` operations on the
maps of agents and `19 * m + 25` on the map of segments, and the memory
they leave. -/
theorem solo_rounds (m n : Nat) : ∃ Xf,
    Opers xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ Xf ⟨Xf.agents, .idle⟩
      (m + 2) (17 * m + 25) (16 * m + 27) (19 * m + 25) ∧
      Final n (sum (m + 1) n) Xf (n + 3 + m + 1) m := by
  have st0 : Start n (sum (m + 1) n) (n + 3 + m) := by
    have h := start_sum m n
    have e : m + n + 3 = n + 3 + m := by omega
    rw [e] at h
    exact h
  obtain ⟨w0, st1⟩ := Start.round_exact st0
  have H0 : Hist n (sum (m + 1) n) (stepS (sum (m + 1) n) [n + 3 + m + 1] [1])
      (n + 3 + m + 1) m 0 := hist_start (sum_agents (m + 1) n)
  obtain ⟨X', w1, st2, H1⟩ := Steady.rounds_hist m st1 H0
  have hA : X'.agents = ([0, n + 3 + 1], Arith.add) :: (resL (n + 3) (0 + m) ++ tailA n) :=
    H1.agents
  have hz : assoc [2] X'.agents = some .zero := by
    rw [hA]
    show (if ([0, n + 3 + 1] : Id) = [2] then some Arith.add
      else assoc [2] (resL (n + 3) (0 + m) ++ (sndL n ++ [([2], Arith.zero), ([3], .zero)]))) = _
    rw [ite_neg' (fun e => by injection e with _ e2; cases e2),
      assoc_append_skip _ (fun e he => res_ne_single he 2),
      assoc_append_skip _ (fun e he e' => by
        obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
        rw [h3] at e'
        injection e' with e1
        omega)]
    rfl
  have w2 := Steady.zero_round st2 hz
  have F := H1.final
  have e0 : 0 + m = m := by omega
  rw [e0] at F
  refine ⟨_, ?_, F⟩
  have w := (w0.trans w1).trans w2
  have e1 : 1 + m + 1 = m + 2 := by omega
  have e2 : 16 + 17 * m + 9 = 17 * m + 25 := by omega
  have e3 : 15 + 16 * m + 12 = 16 * m + 27 := by omega
  have e4 : 18 + 19 * m + 7 = 19 * m + 25 := by omega
  rw [e1, e2, e3, e4] at w
  exact w

theorem linksS_single (T j k : Nat) (q : Port) : ((([j], k), q) : Port × Port) ∈ linksS T ↔
    j = T ∧ k = 1 ∧ q = ([0, T], 0) ∨ j = 1 ∧ k = 1 ∧ q = ([0, T], 1) ∨
      j = 1 ∧ k = 2 ∧ q = ([0, 1], 0) := by
  simp [mem_linksS, and_assoc]

theorem linksS_adder (T x k : Nat) (q : Port) : ((([0, x], k), q) : Port × Port) ∈ linksS T ↔
    x = 1 ∧ k = 0 ∧ q = ([1], 2) ∨ x = 1 ∧ k = 1 ∧ q = ([0, T], 2) ∨
      x = T ∧ k = 0 ∧ q = ([T], 1) ∨ x = T ∧ k = 1 ∧ q = ([1], 1) ∨
      x = T ∧ k = 2 ∧ q = ([0, 1], 1) := by
  simp [mem_linksS, and_assoc]

theorem linksS_res (T x k : Nat) (q : Port) :
    ((([0, 0, x], k), q) : Port × Port) ∉ linksS T := by
  simp [mem_linksS]

theorem linksA_single (t j k : Nat) (q : Port) : ((([j], k), q) : Port × Port) ∈ linksA t ↔
    j = t ∧ k = 1 ∧ q = ([0, t], 0) := by
  simp [mem_linksA, and_assoc]

theorem linksA_adder (t x k : Nat) (q : Port) : ((([0, x], k), q) : Port × Port) ∈ linksA t ↔
    x = t + 1 ∧ k = 1 ∧ q = ([0, t], 1) ∨ x = t + 1 ∧ k = 2 ∧ q = ([0, 0, t + 1], 0) ∨
      x = t ∧ k = 0 ∧ q = ([t], 1) ∨ x = t ∧ k = 1 ∧ q = ([0, t + 1], 1) ∨
      x = t ∧ k = 2 ∧ q = ([0, 0, t + 1], 1) := by
  simp [mem_linksA, and_assoc]

theorem linksA_res (t x k : Nat) (q : Port) : ((([0, 0, x], k), q) : Port × Port) ∈ linksA t ↔
    x = t + 1 ∧ k = 0 ∧ q = ([0, t + 1], 2) ∨ x = t + 1 ∧ k = 1 ∧ q = ([0, t], 2) := by
  simp [mem_linksA, and_assoc]

theorem linksZ_single (t j k : Nat) (q : Port) :
    ((([j], k), q) : Port × Port) ∉ linksZ t := by
  simp [mem_linksZ]

theorem linksZ_adder (t x k : Nat) (q : Port) : ((([0, x], k), q) : Port × Port) ∈ linksZ t ↔
    x = t ∧ k = 1 ∧ q = ([0, t], 2) ∨ x = t ∧ k = 2 ∧ q = ([0, t], 1) := by
  simp [mem_linksZ, and_assoc]

theorem linksZ_res (t x k : Nat) (q : Port) :
    ((([0, 0, x], k), q) : Port × Port) ∉ linksZ t := by
  simp [mem_linksZ]

section FinalFacts

variable {n d T : Nat} {X0 X : XNet Arith}

/-- The segments at a port of an agent of the net at the start, at the
end of the rounds. -/
theorem Final.single (F : Final n X0 X T d) (j k : Nat) (q : Port) :
    ((([j], k), q) : Port × Port) ∈ X.wires ↔ ((([j], k), q) : Port × Port) ∈ X0.wires ∨
      j = T ∧ k = 1 ∧ q = ([0, T], 0) ∨ j = 1 ∧ k = 1 ∧ q = ([0, T], 1) ∨
      j = 1 ∧ k = 2 ∧ q = ([0, 1], 0) ∨ n + 3 < j ∧ j < T ∧ k = 1 ∧ q = ([0, j], 0) := by
  rw [F.wires, linksS_single]
  constructor
  · rintro (h | (h | h | h) | ⟨t, h1, h2, h⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · rw [linksA_single] at h
      obtain ⟨rfl, hk, hq⟩ := h
      exact .inr (.inr (.inr (.inr ⟨h1, h2, hk, hq⟩)))
    · exact absurd h (linksZ_single _ _ _ _)
  · rintro (h | h | h | h | ⟨h1, h2, hk, hq⟩)
    · exact .inl h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inl (.inr (.inl h)))
    · exact .inr (.inl (.inr (.inr h)))
    · exact .inr (.inr (.inl ⟨j, h1, h2, (linksA_single _ _ _ _).2 ⟨rfl, hk, hq⟩⟩))

/-- The rounds leave the principal ports of the old agents, and the ports
of the second chain, as they were. -/
theorem Final.old (F : Final n X0 X T d) {j k : Nat} (h : k = 0 ∨ k = 1 ∧ 1 < j ∧ j ≤ n + 3)
    (q : Port) :
    ((([j], k), q) : Port × Port) ∈ X.wires ↔ ((([j], k), q) : Port × Port) ∈ X0.wires := by
  have hT := F.top
  rw [F.single]
  constructor
  · rintro (h' | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, h3, -⟩)
    · exact h'
    all_goals omega
  · exact .inl

/-- The segments at a port of an agent the rounds made are those the
rounds wrote. -/
theorem Final.fresh (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    {i : Id} (hi : ∀ j, i ≠ [j]) (k : Nat) (q : Port) :
    (((i, k), q) : Port × Port) ∈ X.wires ↔ (((i, k), q) : Port × Port) ∈ linksS T ∨
      (∃ t, n + 3 < t ∧ t < T ∧ (((i, k), q) : Port × Port) ∈ linksA t) ∨
      (((i, k), q) : Port × Port) ∈ linksZ (n + 3 + 1) := by
  rw [F.wires]
  constructor
  · rintro (h | h)
    · obtain ⟨j, ej⟩ := hfr i k q h
      exact absurd ej (hi j)
    · exact h
  · exact .inr

theorem Final.one_one (F : Final n X0 X T d) (S : Snd n X0) (q : Port) :
    ((([1], 1), q) : Port × Port) ∈ X.wires ↔ q = ([n + 3], 0) ∨ q = ([0, T], 1) := by
  have hT := F.top
  rw [F.single, S.one]
  constructor
  · rintro (h | ⟨h1, -, -⟩ | ⟨-, -, h⟩ | ⟨-, h1, -⟩ | ⟨h1, -, -, -⟩)
    · exact .inl h
    · omega
    · exact .inr h
    · omega
    · omega
  · rintro (h | h)
    · exact .inl h
    · exact .inr (.inr (.inl ⟨rfl, rfl, h⟩))

theorem Final.one_two (F : Final n X0 X T d) (S : Snd n X0) (q : Port) :
    ((([1], 2), q) : Port × Port) ∈ X.wires ↔ q = ([0], 0) ∨ q = ([0, 1], 0) := by
  have hT := F.top
  rw [F.single, S.res]
  constructor
  · rintro (h | ⟨h1, -, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, h⟩ | ⟨h1, -, -, -⟩)
    · exact .inl h
    · omega
    · omega
    · exact .inr h
    · omega
  · rintro (h | h)
    · exact .inl h
    · exact .inr (.inr (.inr (.inl ⟨rfl, rfl, h⟩)))

theorem Final.out (F : Final n X0 X T d) (S : Snd n X0) (q : Port) :
    ((([0], 0), q) : Port × Port) ∈ X.wires ↔ q = ([1], 2) := by
  rw [F.old (.inl rfl), S.out]

theorem Final.top_snd (F : Final n X0 X T d) (S : Snd n X0) (q : Port) :
    ((([n + 3], 0), q) : Port × Port) ∈ X.wires ↔ q = ([1], 1) := by
  rw [F.old (.inl rfl), S.top]

theorem Final.up (F : Final n X0 X T d) (S : Snd n X0) {j : Nat} (h1 : 3 ≤ j)
    (h2 : j ≤ n + 2) (q : Port) :
    ((([j], 0), q) : Port × Port) ∈ X.wires ↔ q = ([j + 1], 1) := by
  rw [F.old (.inl rfl), S.up j h1 h2]

theorem Final.down (F : Final n X0 X T d) (S : Snd n X0) {j : Nat} (h1 : 3 ≤ j)
    (h2 : j ≤ n + 2) (q : Port) :
    ((([j + 1], 1), q) : Port × Port) ∈ X.wires ↔ q = ([j], 0) := by
  rw [F.old (.inr ⟨rfl, by omega, by omega⟩), S.down j h1 h2]

/-- The segments at the second argument of an adder the rounds made: to
the adder before it, or to the second argument of the first, and to the
adder after it, or, for the last, round to its own result. -/
theorem Final.adder_one (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    {x : Nat} (hx : n + 3 < x) (hx' : x ≤ T) (q : Port) :
    ((([0, x], 1), q) : Port × Port) ∈ X.wires ↔
      x = T ∧ q = ([1], 1) ∨ (n + 3 + 1 < x ∧ ∃ t, x = t + 1 ∧ q = ([0, t], 1)) ∨
      x < T ∧ q = ([0, x + 1], 1) ∨ x = n + 3 + 1 ∧ q = ([0, x], 2) := by
  rw [F.fresh hfr (fun j e => by injection e with _ e2; cases e2)]
  constructor
  · rintro (h | ⟨t, h1, h2, h⟩ | h)
    · rw [linksS_adder] at h
      rcases h with ⟨-, h, -⟩ | ⟨h, -, -⟩ | ⟨-, h, -⟩ | ⟨h, -, hq⟩ | ⟨-, h, -⟩
      · omega
      · omega
      · omega
      · exact .inl ⟨h, hq⟩
      · omega
    · rw [linksA_adder] at h
      rcases h with ⟨h, -, hq⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -, hq⟩ | ⟨-, h, -⟩
      · exact .inr (.inl ⟨by omega, t, h, hq⟩)
      · omega
      · omega
      · subst h
        exact .inr (.inr (.inl ⟨h2, hq⟩))
      · omega
    · rw [linksZ_adder] at h
      rcases h with ⟨h, -, hq⟩ | ⟨-, h, -⟩
      · subst h
        exact .inr (.inr (.inr ⟨rfl, hq⟩))
      · omega
  · rintro (⟨h, hq⟩ | ⟨h, t, ht, hq⟩ | ⟨h, hq⟩ | ⟨h, hq⟩)
    · exact .inl ((linksS_adder _ _ _ _).2 (.inr (.inr (.inr (.inl ⟨h, rfl, hq⟩)))))
    · exact .inr (.inl ⟨t, by omega, by omega, (linksA_adder _ _ _ _).2 (.inl ⟨ht, rfl, hq⟩)⟩)
    · exact .inr (.inl ⟨x, hx, h,
        (linksA_adder _ _ _ _).2 (.inr (.inr (.inr (.inl ⟨rfl, rfl, hq⟩))))⟩)
    · subst h
      exact .inr (.inr ((linksZ_adder _ _ _ _).2 (.inl ⟨rfl, rfl, hq⟩)))

/-- The segments at the result of an adder the rounds made: to the
successor it made, or, for the last, round to its own second argument,
and to the argument of the successor the adder before it made. -/
theorem Final.adder_two (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    {x : Nat} (hx : n + 3 < x) (hx' : x ≤ T) (q : Port) :
    ((([0, x], 2), q) : Port × Port) ∈ X.wires ↔
      x = T ∧ q = ([0, 1], 1) ∨ x < T ∧ q = ([0, 0, x + 1], 1) ∨
      n + 3 + 1 < x ∧ q = ([0, 0, x], 0) ∨ x = n + 3 + 1 ∧ q = ([0, x], 1) := by
  rw [F.fresh hfr (fun j e => by injection e with _ e2; cases e2)]
  constructor
  · rintro (h | ⟨t, h1, h2, h⟩ | h)
    · rw [linksS_adder] at h
      rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -, hq⟩
      · omega
      · omega
      · omega
      · omega
      · exact .inl ⟨h, hq⟩
    · rw [linksA_adder] at h
      rcases h with ⟨-, h, -⟩ | ⟨h, -, hq⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -, hq⟩
      · omega
      · subst h
        exact .inr (.inr (.inl ⟨by omega, hq⟩))
      · omega
      · omega
      · subst h
        exact .inr (.inl ⟨h2, hq⟩)
    · rw [linksZ_adder] at h
      rcases h with ⟨-, h, -⟩ | ⟨h, -, hq⟩
      · omega
      · subst h
        exact .inr (.inr (.inr ⟨rfl, hq⟩))
  · rintro (⟨h, hq⟩ | ⟨h, hq⟩ | ⟨h, hq⟩ | ⟨h, hq⟩)
    · exact .inl ((linksS_adder _ _ _ _).2 (.inr (.inr (.inr (.inr ⟨h, rfl, hq⟩)))))
    · exact .inr (.inl ⟨x, hx, h,
        (linksA_adder _ _ _ _).2 (.inr (.inr (.inr (.inr ⟨rfl, rfl, hq⟩))))⟩)
    · obtain ⟨t, rfl⟩ : ∃ t, x = t + 1 := ⟨x - 1, by omega⟩
      exact .inr (.inl ⟨t, by omega, by omega,
        (linksA_adder _ _ _ _).2 (.inr (.inl ⟨rfl, rfl, hq⟩))⟩)
    · subst h
      exact .inr (.inr ((linksZ_adder _ _ _ _).2 (.inr ⟨rfl, rfl, hq⟩)))

theorem Final.res_zero (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    {t : Nat} (h1 : n + 3 < t) (h2 : t < T) (q : Port) :
    ((([0, 0, t + 1], 0), q) : Port × Port) ∈ X.wires ↔ q = ([0, t + 1], 2) := by
  rw [F.fresh hfr (fun j e => by injection e with _ e2; cases e2)]
  constructor
  · rintro (h | ⟨t', -, -, h⟩ | h)
    · exact absurd h (linksS_res _ _ _ _)
    · rw [linksA_res] at h
      rcases h with ⟨h, -, hq⟩ | ⟨-, h, -⟩
      · have e : t' = t := by omega
        subst e
        exact hq
      · omega
    · exact absurd h (linksZ_res _ _ _ _)
  · intro hq
    exact .inr (.inl ⟨t, h1, h2, (linksA_res _ _ _ _).2 (.inl ⟨rfl, rfl, hq⟩)⟩)

theorem Final.res_one (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    {t : Nat} (h1 : n + 3 < t) (h2 : t < T) (q : Port) :
    ((([0, 0, t + 1], 1), q) : Port × Port) ∈ X.wires ↔ q = ([0, t], 2) := by
  rw [F.fresh hfr (fun j e => by injection e with _ e2; cases e2)]
  constructor
  · rintro (h | ⟨t', -, -, h⟩ | h)
    · exact absurd h (linksS_res _ _ _ _)
    · rw [linksA_res] at h
      rcases h with ⟨-, h, -⟩ | ⟨h, -, hq⟩
      · omega
      · have e : t' = t := by omega
        subst e
        exact hq
    · exact absurd h (linksZ_res _ _ _ _)
  · intro hq
    exact .inr (.inl ⟨t, h1, h2, (linksA_res _ _ _ _).2 (.inr ⟨rfl, rfl, hq⟩)⟩)

theorem Final.first_zero (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j]) (q : Port) :
    ((([0, 1], 0), q) : Port × Port) ∈ X.wires ↔ q = ([1], 2) := by
  have hT := F.top
  rw [F.fresh hfr (fun j e => by injection e with _ e2; cases e2)]
  constructor
  · rintro (h | ⟨t, h1, h2, h⟩ | h)
    · rw [linksS_adder] at h
      rcases h with ⟨-, -, hq⟩ | ⟨-, h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · exact hq
      all_goals omega
    · rw [linksA_adder] at h
      rcases h with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> omega
    · rw [linksZ_adder] at h
      rcases h with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> omega
  · intro hq
    exact .inl ((linksS_adder _ _ _ _).2 (.inl ⟨rfl, rfl, hq⟩))

theorem Final.first_one (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j]) (q : Port) :
    ((([0, 1], 1), q) : Port × Port) ∈ X.wires ↔ q = ([0, T], 2) := by
  have hT := F.top
  rw [F.fresh hfr (fun j e => by injection e with _ e2; cases e2)]
  constructor
  · rintro (h | ⟨t, h1, h2, h⟩ | h)
    · rw [linksS_adder] at h
      rcases h with ⟨-, h, -⟩ | ⟨-, -, hq⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · omega
      · exact hq
      all_goals omega
    · rw [linksA_adder] at h
      rcases h with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> omega
    · rw [linksZ_adder] at h
      rcases h with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> omega
  · intro hq
    exact .inl ((linksS_adder _ _ _ _).2 (.inr (.inl ⟨rfl, rfl, hq⟩)))

theorem final_sym {e : Id × Arith}
    (he : e ∈ resL (n + 3) d ++ (sndL n ++ [([3], .zero)])) :
    e.2 = if e.1 = [3] then .zero else .succ := by
  rcases List.mem_append.1 he with h | h
  · rw [ite_neg' (res_ne_single h 3)]
    exact (mem_resL h).1
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨h1, j, h2, -, h3⟩ := mem_sndL h
      rw [ite_neg' (fun e' => by rw [h3] at e'; injection e' with e1; omega)]
      exact h1
    · rcases List.mem_cons.1 h with rfl | h
      · rfl
      · cases h

/-- Every entry of the list of agents at the end is an agent of the
memory, under its own symbol. -/
theorem Final.agent (F : Final n X0 X T d) {e : Id × Arith} (he : e ∈ X.agents) :
    assoc e.1 X.agents = some e.2 := by
  refine assoc_eq_of_unique he (fun γ hγ => ?_)
  rw [F.agents] at he hγ
  have h1 := final_sym he
  have h2 := final_sym hγ
  exact h2.trans h1.symm

theorem Final.no_zero (F : Final n X0 X T d) : assoc [0] X.agents = none := by
  rw [F.agents]
  refine assoc_none_of_forall fun e he e' => ?_
  rcases List.mem_append.1 he with h | h
  · exact res_ne_single h 0 e'
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨-, j, h2, -, h3⟩ := mem_sndL h
      rw [h3] at e'
      injection e' with e1
      omega
    · rcases List.mem_cons.1 h with rfl | h
      · exact absurd e' (by decide)
      · cases h

/-- **From the result of an adder a thread goes one segment on and
stops.** -/
theorem Final.dead_two (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    {x : Nat} (hx : n + 3 < x) (hx' : x ≤ T) {p : Port}
    (hp : p = ([0, 0, x], 0) ∧ n + 3 + 1 < x ∨ p = ([0, x], 1) ∧ x = n + 3 + 1) :
    X.Dead p ([0, x], 2) 2 := by
  have W := F.adder_two hfr hx hx'
  have key : ∀ q, ((([0, x], 2), q) : Port × Port) ∈ X.wires → q ≠ p →
      x = T ∧ q = ([0, 1], 1) ∨ x < T ∧ q = ([0, 0, x + 1], 1) := by
    intro q hq hqp
    rcases (W q).1 hq with h | h | ⟨h, hq'⟩ | ⟨h, hq'⟩
    · exact .inl h
    · exact .inr h
    · rcases hp with ⟨hp, -⟩ | ⟨-, hp⟩
      · exact absurd (hq'.trans hp.symm) hqp
      · omega
    · rcases hp with ⟨-, hp⟩ | ⟨hp, -⟩
      · omega
      · exact absurd (hq'.trans hp.symm) hqp
  by_cases hxT : x = T
  · have hn : nextSeg X.wires ([0, x], 2) p = some ([0, 1], 1) := by
      refine nextSeg_some ((W _).2 (.inl ⟨hxT, rfl⟩)) ?_ (fun q hq hqp => ?_)
      · rcases hp with ⟨hp, -⟩ | ⟨hp, -⟩ <;> rw [hp] <;> ports_differ
      · rcases key q hq hqp with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · omega
    have hs : nextSeg X.wires ([0, 1], 1) ([0, x], 2) = none :=
      nextSeg_none fun q hq => by
        rw [(F.first_one hfr q).1 hq, hxT]
    exact .step rfl hn (.stop rfl hs)
  · have hlt : x < T := by omega
    have hn : nextSeg X.wires ([0, x], 2) p = some ([0, 0, x + 1], 1) := by
      refine nextSeg_some ((W _).2 (.inr (.inl ⟨hlt, rfl⟩))) ?_ (fun q hq hqp => ?_)
      · rcases hp with ⟨hp, -⟩ | ⟨hp, -⟩ <;> rw [hp] <;> ports_differ
      · rcases key q hq hqp with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h hxT
        · exact h
    have hs : nextSeg X.wires ([0, 0, x + 1], 1) ([0, x], 2) = none :=
      nextSeg_none fun q hq => (F.res_one hfr hx hlt q).1 hq
    exact .step rfl hn (.stop rfl hs)

/-- **The walk down the adders.**  From the second argument of the adder
numbered `n + 4 + i` a thread passes the `i` adders below it, turns at
the last one to its result, goes one segment on and stops. -/
theorem Final.dead_adder (F : Final n X0 X T d)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j]) :
    ∀ i, n + 3 + 1 + i ≤ T →
      X.Dead (if n + 3 + 1 + i = T then ([1], 1) else ([0, n + 3 + 1 + i + 1], 1))
        ([0, n + 3 + 1 + i], 1) (i + 3)
  | 0, hi => by
    have hi' : n + 3 + 1 ≤ T := hi
    have W := F.adder_one hfr (x := n + 3 + 1) (by omega) hi'
    have hn : nextSeg X.wires ([0, n + 3 + 1], 1)
        (if n + 3 + 1 = T then ([1], 1) else ([0, n + 3 + 1 + 1], 1)) =
        some ([0, n + 3 + 1], 2) := by
      refine nextSeg_some ((W _).2 (.inr (.inr (.inr ⟨rfl, rfl⟩)))) ?_ (fun q hq hqp => ?_)
      · by_cases h : n + 3 + 1 = T
        · rw [ite_pos' h]
          ports_differ
        · rw [ite_neg' h]
          ports_differ
      · rcases (W q).1 hq with ⟨h, hq'⟩ | ⟨h, -⟩ | ⟨h, hq'⟩ | ⟨-, hq'⟩
        · rw [ite_pos' h] at hqp
          exact absurd hq' hqp
        · omega
        · rw [ite_neg' (by omega)] at hqp
          exact absurd hq' hqp
        · exact hq'
    show X.Dead (if n + 3 + 1 = T then ([1], 1) else ([0, n + 3 + 1 + 1], 1))
      ([0, n + 3 + 1], 1) (2 + 1)
    exact .step rfl hn (F.dead_two hfr (by omega) hi' (.inr ⟨rfl, rfl⟩))
  | i + 1, hi => by
    have hi' : n + 3 + 1 + i + 1 ≤ T := hi
    have W := F.adder_one hfr (x := n + 3 + 1 + i + 1) (by omega) hi'
    have ih := Final.dead_adder F hfr i (by omega)
    rw [ite_neg' (by omega)] at ih
    have hn : nextSeg X.wires ([0, n + 3 + 1 + i + 1], 1)
        (if n + 3 + 1 + i + 1 = T then ([1], 1) else ([0, n + 3 + 1 + i + 1 + 1], 1)) =
        some ([0, n + 3 + 1 + i], 1) := by
      refine nextSeg_some ((W _).2 (.inr (.inl ⟨by omega, n + 3 + 1 + i, rfl, rfl⟩))) ?_
        (fun q hq hqp => ?_)
      · by_cases h : n + 3 + 1 + i + 1 = T
        · rw [ite_pos' h]
          ports_differ
        · rw [ite_neg' h]
          ports_differ
      · rcases (W q).1 hq with ⟨h, hq'⟩ | ⟨-, t, ht, hq'⟩ | ⟨h, hq'⟩ | ⟨h, -⟩
        · rw [ite_pos' h] at hqp
          exact absurd hq' hqp
        · have e : t = n + 3 + 1 + i := by omega
          rw [e] at hq'
          exact hq'
        · rw [ite_neg' (by omega)] at hqp
          exact absurd hq' hqp
        · omega
    show X.Dead (if n + 3 + 1 + i + 1 = T then ([1], 1) else ([0, n + 3 + 1 + i + 1 + 1], 1))
      ([0, n + 3 + 1 + i + 1], 1) (i + 3 + 1)
    exact .step rfl hn ih

/-- **The walk from the top of the second argument**: to the first
adder, down all the adders the rounds made, and on to the stop. -/
theorem Final.dead_top (F : Final n X0 X T d) (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j]) :
    X.Dead ([n + 3], 0) ([1], 1) (d + 3 + 1) := by
  have hT := F.top
  have W := F.one_one S
  have hn : nextSeg X.wires ([1], 1) ([n + 3], 0) = some ([0, T], 1) := by
    refine nextSeg_some ((W _).2 (.inr rfl)) (by ports_differ) (fun q hq hqp => ?_)
    rcases (W q).1 hq with h | h
    · exact absurd h hqp
    · exact h
  have hd := F.dead_adder hfr d (by omega)
  have e : n + 3 + 1 + d = T := by omega
  rw [ite_pos' e, e] at hd
  exact .step rfl hn hd

/-- The pass over the successors of the result: four actions each,
charged six operations on the maps of agents and three on the map of
segments. -/
theorem Final.pass_res (F : Final n X0 X T d) (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    (rest : List (Id × Arith)) : ∀ (d' h : Nat), n + 3 ≤ h → h + d' + 1 = T →
      (∀ e ∈ resL h d', e ∈ X.agents) →
      Opers xsys X ⟨resL h d' ++ rest, .idle⟩ X ⟨rest, .idle⟩ 0 (4 * (d' + 1))
        (6 * (d' + 1)) (3 * (d' + 1))
  | 0, h, _, _, hm => by
    have h₁ : assoc [0, 1] X.agents = some Arith.succ := F.agent (hm _ List.mem_cons_self)
    have h₂ : assoc (([0, 1], 0) : Port) X.wires = some ([1], 2) :=
      assoc_eq_of_unique ((F.first_zero hfr _).2 rfl) (fun q' hq => (F.first_zero hfr q').1 hq)
    have W := F.one_two S
    have hn : nextSeg X.wires ([1], 2) ([0, 1], 0) = some ([0], 0) := by
      refine nextSeg_some ((W _).2 (.inl rfl)) (by ports_differ) (fun q hq hqp => ?_)
      rcases (W q).1 hq with h | h
      · exact h
      · exact absurd h hqp
    have hs : nextSeg X.wires ([0], 0) ([1], 2) = none :=
      nextSeg_none fun q hq => (F.out S q).1 hq
    have hd : X.Dead ([0, 1], 0) ([1], 2) 2 :=
      .step rfl hn (.stop ((ite_pos' rfl).trans F.no_zero) hs)
    exact Opers.dead (xs := xsys) (e := ([0, 1], Arith.succ)) (k := 2) rest h₁ h₂ hd
  | d' + 1, h, hh, hT', hm => by
    have hx1 : n + 3 < h + 1 := by omega
    have hx2 : h + 1 < T := by omega
    have h₁ : assoc [0, 0, h + 2] X.agents = some Arith.succ :=
      F.agent (hm _ List.mem_cons_self)
    have h₂ : assoc (([0, 0, h + 2], 0) : Port) X.wires = some ([0, h + 2], 2) :=
      assoc_eq_of_unique ((F.res_zero hfr hx1 hx2 _).2 rfl)
        (fun q' hq => (F.res_zero hfr hx1 hx2 q').1 hq)
    have hd : X.Dead ([0, 0, h + 2], 0) ([0, h + 2], 2) 2 :=
      F.dead_two hfr (x := h + 2) (by omega) (by omega) (.inl ⟨rfl, by omega⟩)
    have w₁ : Opers xsys X ⟨([0, 0, h + 2], Arith.succ) :: (resL (h + 1) d' ++ rest), .idle⟩ X
        ⟨resL (h + 1) d' ++ rest, .idle⟩ 0 4 6 3 :=
      Opers.dead (xs := xsys) (e := ([0, 0, h + 2], Arith.succ)) (k := 2) _ h₁ h₂ hd
    have w₂ := Final.pass_res F S hfr rest d' (h + 1) (by omega) (by omega)
      (fun e he => hm e (List.mem_cons_of_mem _ he))
    have w := w₁.trans w₂
    have e1 : 4 + 4 * (d' + 1) = 4 * (d' + 1 + 1) := by omega
    have e2 : 6 + 6 * (d' + 1) = 6 * (d' + 1 + 1) := by omega
    have e3 : 3 + 3 * (d' + 1) = 3 * (d' + 1 + 1) := by omega
    rw [e1, e2, e3] at w
    exact w

theorem sndL_length : ∀ n, (sndL n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (sndL_length n)

/-- The second argument at the end: its top entry, and below it entries
that a thread gives up on at once. -/
theorem snd_split (n : Nat) : ∃ (γ : Arith) (low : List (Id × Arith)),
    sndL n ++ [([3], Arith.zero)] = ([n + 3], γ) :: low ∧ low.length = n ∧
      ∀ e ∈ low, ∃ j, 3 ≤ j ∧ j ≤ n + 2 ∧ e.1 = [j] := by
  cases n with
  | zero => exact ⟨.zero, [], rfl, rfl, fun e he => absurd he List.not_mem_nil⟩
  | succ n =>
    refine ⟨.succ, sndL n ++ [([3], Arith.zero)], rfl, ?_, fun e he => ?_⟩
    · rw [List.length_append, sndL_length]
      rfl
    · rcases List.mem_append.1 he with h | h
      · obtain ⟨-, j, h1, h2, h3⟩ := mem_sndL h
        exact ⟨j, by omega, by omega, h3⟩
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨3, by omega, by omega, rfl⟩
        · cases h

theorem Final.inert (F : Final n X0 X T d) (S : Snd n X0) {e : Id × Arith}
    (he : e ∈ X.agents) {j : Nat} (h1 : 3 ≤ j) (h2 : j ≤ n + 2) (hj : e.1 = [j]) :
    X.Inert e := by
  refine ⟨F.agent he, ([j + 1], 1), ?_, rfl, ?_⟩
  · rw [hj]
    exact assoc_eq_of_unique ((F.up S h1 h2 _).2 rfl) (fun q' hq => (F.up S h1 h2 q').1 hq)
  · rw [hj]
    exact nextSeg_none fun q hq => (F.down S h1 h2 q).1 hq

/-- **The last pass, entry by entry.**  Four actions for each successor
of the result, `d + 6` for the top of the second argument, three for each
entry below it; nothing is written.  The pass is charged
`7 * d + 5 * n + 14` operations on the maps of agents and
`4 * d + 2 * n + 8` on the map of segments. -/
theorem Final.pass (F : Final n X0 X T d) (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j]) :
    Opers xsys X ⟨X.agents, .idle⟩ X ⟨[], .idle⟩ 0 (5 * d + 3 * n + 10)
      (7 * d + 5 * n + 14) (4 * d + 2 * n + 8) := by
  have hT := F.top
  obtain ⟨γ, low, hsplit, hlen, hlow⟩ := snd_split n
  have hA : X.agents = resL (n + 3) d ++ (([n + 3], γ) :: low) := by
    rw [F.agents, hsplit]
  have hmem : ∀ e ∈ ([n + 3], γ) :: low, e ∈ X.agents := fun e he => by
    rw [hA]
    exact List.mem_append_right _ he
  have w₁ := F.pass_res S hfr (([n + 3], γ) :: low) d (n + 3) (Nat.le_refl _) (by omega)
    (fun e he => by
      rw [hA]
      exact List.mem_append_left _ he)
  have h₁ : assoc [n + 3] X.agents = some γ := F.agent (hmem _ List.mem_cons_self)
  have h₂ : assoc (([n + 3], 0) : Port) X.wires = some ([1], 1) :=
    assoc_eq_of_unique ((F.top_snd S _).2 rfl) (fun q' hq => (F.top_snd S q').1 hq)
  have w₂ : Opers xsys X ⟨([n + 3], γ) :: low, .idle⟩ X ⟨low, .idle⟩ 0 (d + 3 + 1 + 2)
      (d + 3 + 1 + 4) (d + 3 + 1 + 1) :=
    Opers.dead (xs := xsys) (e := ([n + 3], γ)) _ h₁ h₂ (F.dead_top S hfr)
  have w₃ := Opers.inert_pass (xs := xsys) (X := X) [] low (fun e he => by
    obtain ⟨j, h1, h2, h3⟩ := hlow e he
    exact F.inert S (hmem e (List.mem_cons_of_mem _ he)) h1 h2 h3)
  rw [List.append_nil, hlen] at w₃
  have w := (w₁.trans w₂).trans w₃
  have e : 4 * (d + 1) + (d + 3 + 1 + 2) + 3 * n = 5 * d + 3 * n + 10 := by omega
  have e' : 6 * (d + 1) + (d + 3 + 1 + 4) + 5 * n = 7 * d + 5 * n + 14 := by omega
  have e'' : 3 * (d + 1) + (d + 3 + 1 + 1) + 2 * n = 4 * d + 2 * n + 8 := by omega
  rw [e, e', e''] at w
  rw [hA]
  exact w

end FinalFacts

theorem sum_fresh (m n : Nat) (i : Id) (k : Nat) (q : Port)
    (h : (((i, k), q) : Port × Port) ∈ (sum m n).wires) : ∃ j, i = [j] := by
  obtain ⟨j, -, ej⟩ := (good_sum m n).below i (.inr (.inl ⟨k, q, h⟩))
  exact ⟨j, ej⟩

/-- **The whole run of one thread on the net for `(m + 1) + n`**, action
by action: `m + 2` claims, and `22 * (m + 1) + 3 * n + 13` actions to the
empty list, charged `23 * (m + 1) + 5 * n + 18` operations on the maps of
agents and `23 * (m + 1) + 2 * n + 10` on the map of segments. -/
theorem solo_run_succ (m n : Nat) : ∃ Xf,
    Opers xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ Xf ⟨[], .idle⟩ (m + 2)
      (22 * (m + 1) + 3 * n + 13) (23 * (m + 1) + 5 * n + 18)
      (23 * (m + 1) + 2 * n + 10) := by
  obtain ⟨Xf, w, F⟩ := solo_rounds m n
  have p := F.pass (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
  have w' := w.trans p
  have e : 17 * m + 25 + (5 * m + 3 * n + 10) = 22 * (m + 1) + 3 * n + 13 := by omega
  have e' : 16 * m + 27 + (7 * m + 5 * n + 14) = 23 * (m + 1) + 5 * n + 18 := by omega
  have e'' : 19 * m + 25 + (4 * m + 2 * n + 8) = 23 * (m + 1) + 2 * n + 10 := by omega
  rw [e, e', e'', Nat.add_zero] at w'
  exact ⟨Xf, w'⟩

theorem zero0_single (j k : Nat) (q : Port) :
    ((([j], k), q) : Port × Port) ∈ addZero.toX.newLinks ar [1] [2] .add .zero ↔
      j = 1 ∧ k = 1 ∧ q = ([1], 2) ∨ j = 1 ∧ k = 2 ∧ q = ([1], 1) := by
  rw [newLinks_zero]
  simp [and_assoc]

/-- **The memory after the only round of `0 + n`**: the second argument
and its zero, and the two segments the round wrote. -/
structure Final0 (n : Nat) (X0 X : XNet Arith) : Prop where
  agents : X.agents = sndL n ++ [([3], .zero)]
  wires : ∀ e, e ∈ X.wires ↔
    e ∈ addZero.toX.newLinks ar [1] [2] .add .zero ∨ e ∈ X0.wires

theorem final0_sumSnd (n : Nat) : Final0 n (sumSnd n) (stepZ (sumSnd n) [1] [2]) := by
  refine ⟨?_, fun e => ?_⟩
  · have k1 : (sndL n).filter (fun e => decide (e.1 ≠ [1])) = sndL n :=
      filter_keep fun e he e' => by
        obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
        rw [h3] at e'
        injection e' with e1
        omega
    have k2 : (sndL n).filter (fun e => decide (e.1 ≠ [2])) = sndL n :=
      filter_keep fun e he e' => by
        obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
        rw [h3] at e'
        injection e' with e1
        omega
    unfold stepZ
    rw [XNet.putLinks_agents]
    show (((sumSnd n).agents.filter (fun e => decide (e.1 ≠ [1]))).filter
      (fun e => decide (e.1 ≠ [2]))) = _
    rw [sumSnd_agents, List.filter_append, List.filter_append, k1, k2]
    rfl
  · unfold stepZ
    exact XNet.mem_step_wires _ _ _ _ _ e

section Final0Facts

variable {n : Nat} {X0 X : XNet Arith}

theorem Final0.old (F : Final0 n X0 X) {j k : Nat} (h : j ≠ 1 ∨ k = 0) (q : Port) :
    ((([j], k), q) : Port × Port) ∈ X.wires ↔ ((([j], k), q) : Port × Port) ∈ X0.wires := by
  rw [F.wires, zero0_single]
  constructor
  · rintro ((⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) | h')
    · omega
    · omega
    · exact h'
  · exact .inr

theorem Final0.one_one (F : Final0 n X0 X) (S : Snd n X0) (q : Port) :
    ((([1], 1), q) : Port × Port) ∈ X.wires ↔ q = ([1], 2) ∨ q = ([n + 3], 0) := by
  rw [F.wires, zero0_single, S.one]
  constructor
  · rintro ((⟨-, -, h⟩ | ⟨-, h, -⟩) | h)
    · exact .inl h
    · omega
    · exact .inr h
  · rintro (h | h)
    · exact .inl (.inl ⟨rfl, rfl, h⟩)
    · exact .inr h

theorem Final0.one_two (F : Final0 n X0 X) (S : Snd n X0) (q : Port) :
    ((([1], 2), q) : Port × Port) ∈ X.wires ↔ q = ([1], 1) ∨ q = ([0], 0) := by
  rw [F.wires, zero0_single, S.res]
  constructor
  · rintro ((⟨-, h, -⟩ | ⟨-, -, h⟩) | h)
    · omega
    · exact .inl h
    · exact .inr h
  · rintro (h | h)
    · exact .inl (.inr ⟨rfl, rfl, h⟩)
    · exact .inr h

theorem Final0.agent (F : Final0 n X0 X) {e : Id × Arith} (he : e ∈ X.agents) :
    assoc e.1 X.agents = some e.2 := by
  refine assoc_eq_of_unique he (fun γ hγ => ?_)
  rw [F.agents] at he hγ
  have h1 := final_sym (n := n) (d := 0) (List.mem_append_right _ he)
  have h2 := final_sym (n := n) (d := 0) (List.mem_append_right _ hγ)
  exact h2.trans h1.symm

theorem Final0.no_zero (F : Final0 n X0 X) : assoc [0] X.agents = none := by
  rw [F.agents]
  refine assoc_none_of_forall fun e he e' => ?_
  rcases List.mem_append.1 he with h | h
  · obtain ⟨-, j, h2, -, h3⟩ := mem_sndL h
    rw [h3] at e'
    injection e' with e1
    omega
  · rcases List.mem_cons.1 h with rfl | h
    · exact absurd e' (by decide)
    · cases h

/-- **The last pass of `0 + n`**: five actions for the top of the second
argument, which a thread follows round the adder that is gone and out to
the result, and three for each entry below it. -/
theorem Final0.pass (F : Final0 n X0 X) (S : Snd n X0) :
    Opers xsys X ⟨X.agents, .idle⟩ X ⟨[], .idle⟩ 0 (3 * n + 5) (5 * n + 7)
      (2 * n + 4) := by
  obtain ⟨γ, low, hsplit, hlen, hlow⟩ := snd_split n
  have hA : X.agents = ([n + 3], γ) :: low := by
    rw [F.agents, hsplit]
  have hmem : ∀ e ∈ ([n + 3], γ) :: low, e ∈ X.agents := fun e he => by
    rw [hA]
    exact he
  have h₁ : assoc [n + 3] X.agents = some γ := F.agent (hmem _ List.mem_cons_self)
  have h₂ : assoc (([n + 3], 0) : Port) X.wires = some ([1], 1) := by
    refine assoc_eq_of_unique ?_ (fun q' hq => ?_)
    · rw [F.old (.inr rfl)]
      exact (S.top _).2 rfl
    · rw [F.old (.inr rfl)] at hq
      exact (S.top q').1 hq
  have W1 := F.one_one S
  have W2 := F.one_two S
  have hn1 : nextSeg X.wires ([1], 1) ([n + 3], 0) = some ([1], 2) := by
    refine nextSeg_some ((W1 _).2 (.inl rfl)) (by ports_differ) (fun q hq hqp => ?_)
    rcases (W1 q).1 hq with h | h
    · exact h
    · exact absurd h hqp
  have hn2 : nextSeg X.wires ([1], 2) ([1], 1) = some ([0], 0) := by
    refine nextSeg_some ((W2 _).2 (.inr rfl)) (by ports_differ) (fun q hq hqp => ?_)
    rcases (W2 q).1 hq with h | h
    · exact absurd h hqp
    · exact h
  have hs : nextSeg X.wires ([0], 0) ([1], 2) = none :=
    nextSeg_none fun q hq => by
      rw [F.old (.inr rfl)] at hq
      exact (S.out q).1 hq
  have hd : X.Dead ([n + 3], 0) ([1], 1) 3 :=
    .step rfl hn1 (.step rfl hn2 (.stop ((ite_pos' rfl).trans F.no_zero) hs))
  have w₂ : Opers xsys X ⟨([n + 3], γ) :: low, .idle⟩ X ⟨low, .idle⟩ 0 5 7 4 :=
    Opers.dead (xs := xsys) (e := ([n + 3], γ)) (k := 3) _ h₁ h₂ hd
  have w₃ := Opers.inert_pass (xs := xsys) (X := X) [] low (fun e he => by
    obtain ⟨j, h1, h2, h3⟩ := hlow e he
    refine ⟨F.agent (hmem e (List.mem_cons_of_mem _ he)), ([j + 1], 1), ?_, rfl, ?_⟩
    · rw [h3]
      refine assoc_eq_of_unique ?_ (fun q' hq => ?_)
      · rw [F.old (.inr rfl)]
        exact (S.up j h1 h2 _).2 rfl
      · rw [F.old (.inr rfl)] at hq
        exact (S.up j h1 h2 q').1 hq
    · rw [h3]
      refine nextSeg_none fun q hq => ?_
      rw [F.old (.inl (by omega))] at hq
      exact (S.down j h1 h2 q).1 hq)
  rw [List.append_nil, hlen] at w₃
  have w := w₂.trans w₃
  have e : 5 + 3 * n = 3 * n + 5 := by omega
  have e' : 7 + 5 * n = 5 * n + 7 := by omega
  have e'' : 4 + 2 * n = 2 * n + 4 := by omega
  rw [e, e', e''] at w
  rw [hA]
  exact w

end Final0Facts

/-- In the net for `0 + n` a thread gives up at once on every successor
of the second argument. -/
theorem sumSnd_inert (n : Nat) {e : Id × Arith} (he : e ∈ sndL n) : (sumSnd n).Inert e := by
  have S := snd_sumSnd n
  obtain ⟨-, j, h1, h2, h3⟩ := mem_sndL he
  have hin : e ∈ (sumSnd n).agents := by
    rw [sumSnd_agents]
    exact List.mem_append_left _ he
  refine ⟨assoc_of_nodup (sumSnd_nodup n) hin, ?_⟩
  by_cases hj : j = n + 3
  · refine ⟨([1], 1), ?_, rfl, ?_⟩
    · rw [h3, hj]
      exact assoc_eq_of_unique ((S.top _).2 rfl) (fun q' hq => (S.top q').1 hq)
    · rw [h3, hj]
      exact nextSeg_none fun q hq => (S.one q).1 hq
  · refine ⟨([j + 1], 1), ?_, rfl, ?_⟩
    · rw [h3]
      exact assoc_eq_of_unique ((S.up j (by omega) (by omega) _).2 rfl)
        (fun q' hq => (S.up j (by omega) (by omega) q').1 hq)
    · rw [h3]
      exact nextSeg_none fun q hq => (S.down j (by omega) (by omega) q).1 hq

/-- **The whole run of one thread on the net for `0 + n`**: a pass over
the second argument, the one claim, and the last pass, `6 * n + 13`
actions in all, charged `10 * n + 18` operations on the maps of agents
and `4 * n + 10` on the map of segments. -/
theorem solo_run_zero (n : Nat) : ∃ Xf,
    Opers xsys (sum 0 n) ⟨(sum 0 n).agents, .idle⟩ Xf ⟨[], .idle⟩ 1 (6 * n + 13)
      (10 * n + 18) (4 * n + 10) := by
  show ∃ Xf, Opers xsys (sumSnd n) ⟨(sumSnd n).agents, .idle⟩ Xf ⟨[], .idle⟩ 1 (6 * n + 13)
    (10 * n + 18) (4 * n + 10)
  have S := snd_sumSnd n
  obtain ⟨ad, pr⟩ := sumSnd_facts n
  have hA := sumSnd_agents n
  have w₁ : Opers xsys (sumSnd n) ⟨sndL n ++ base.agents, .idle⟩ (sumSnd n)
      ⟨base.agents, .idle⟩ 0 (3 * (sndL n).length) (5 * (sndL n).length)
      (2 * (sndL n).length) :=
    Opers.inert_pass (xs := xsys) base.agents (sndL n) (fun e he => sumSnd_inert n he)
  rw [sndL_length] at w₁
  have h₂ : assoc (([1], 0) : Port) (sumSnd n).wires = some ([2], 0) :=
    assoc_eq_of_unique ((pr _).2 rfl) (fun q' hq => (pr q').1 hq)
  have hz : (([2], Arith.zero) : Id × Arith) ∈ (sumSnd n).agents := by
    rw [hA]
    exact List.mem_append_right _ (by decide)
  have h₃ : assoc [2] (sumSnd n).agents = some .zero := assoc_of_nodup (sumSnd_nodup n) hz
  have hne : ([1] : Id) ≠ [2] := by decide
  have h₄ : assoc [2] ((sumSnd n).takeAgent [1]).agents = some .zero := by
    show assoc [2] ((sumSnd n).agents.filter fun e => decide (e.1 ≠ [1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact h₃
  have hR : xsys.rule .add .zero = some addZero.toX := rfl
  have w₂ : Opers xsys (sumSnd n) ⟨base.agents, .idle⟩ (stepZ (sumSnd n) [1] [2])
      ⟨(stepZ (sumSnd n) [1] [2]).agents, .idle⟩ 1 8 11 6 :=
    Opers.claim_direct (xs := xsys) [([2], Arith.zero), ([3], Arith.zero)] ad h₂ h₃ hne h₄ hR
  have w₃ := (final0_sumSnd n).pass S
  have w := (w₁.trans w₂).trans w₃
  have e : 3 * n + 8 + (3 * n + 5) = 6 * n + 13 := by omega
  have e' : 5 * n + 11 + (5 * n + 7) = 10 * n + 18 := by omega
  have e'' : 2 * n + 6 + (2 * n + 4) = 4 * n + 10 := by omega
  rw [e, e', e''] at w
  rw [hA]
  exact ⟨_, w⟩

/-- The operations on the maps of agents that one thread is charged to
add `m` and `n`. -/
def soloOpsA (m n : Nat) : Nat := if m = 0 then 10 * n + 18 else 23 * m + 5 * n + 18

/-- The operations on the map of segments that one thread is charged to
add `m` and `n`. -/
def soloOpsW (m n : Nat) : Nat := if m = 0 then 4 * n + 10 else 23 * m + 2 * n + 10

/-- **The whole run of one thread on the net for `m + n`**, action by
action, to the empty list, with the operations it is charged. -/
theorem solo_run (m n : Nat) : ∃ Xf c,
    Opers xsys (sum m n) ⟨(sum m n).agents, .idle⟩ Xf ⟨[], .idle⟩ c (soloWork m n)
      (soloOpsA m n) (soloOpsW m n) := by
  cases m with
  | zero =>
    obtain ⟨Xf, w⟩ := solo_run_zero n
    exact ⟨Xf, 1, w⟩
  | succ m =>
    obtain ⟨Xf, w⟩ := solo_run_succ m n
    have e : soloWork (m + 1) n = 22 * (m + 1) + 3 * n + 13 := by
      unfold soloWork
      rw [ite_neg' (Nat.succ_ne_zero m)]
    have e' : soloOpsA (m + 1) n = 23 * (m + 1) + 5 * n + 18 := by
      unfold soloOpsA
      rw [ite_neg' (Nat.succ_ne_zero m)]
    have e'' : soloOpsW (m + 1) n = 23 * (m + 1) + 2 * n + 10 := by
      unfold soloOpsW
      rw [ite_neg' (Nat.succ_ne_zero m)]
    rw [e, e', e'']
    exact ⟨Xf, m + 2, w⟩

/-- **One thread adds in exactly `22 * m + 3 * n + 13` actions, for every
size** (`6 * n + 13` when `m` is zero).  On the net for `m + n` the run of
a single thread is at rest after that many actions and not before, and
none of them is a rest. -/
theorem solo_work (m n : Nat) :
    ((XMach.init (sum m n) 1).trace xsys (fun _ => 0) (soloWork m n)).1.resting = true ∧
      (XMach.init (sum m n) 1).work xsys (fun _ => 0) (soloWork m n) = soloWork m n ∧
      ∀ i, i < soloWork m n →
        ¬ ((XMach.init (sum m n) 1).trace xsys (fun _ => 0) i).1.resting = true := by
  obtain ⟨Xf, c, r⟩ := solo_run m n
  have w := r.works
  obtain ⟨t1, t2⟩ := w.trace
  have h := w.work 0
  rw [XMach.init_one]
  refine ⟨?_, h, t2⟩
  rw [t1]
  rfl

/-- The work of one thread on an addition never passes the law. -/
theorem solo_work_all (m n : Nat) (i : Nat) :
    (XMach.init (sum m n) 1).work xsys (fun _ => 0) i ≤ soloWork m n := by
  obtain ⟨hr, hw, -⟩ := solo_work m n
  by_cases h : i ≤ soloWork m n
  · have h' := XMach.work_mono (xs := xsys) (fun _ => 0) (XMach.init (sum m n) 1) h
    rw [hw] at h'
    exact h'
  · obtain ⟨d, rfl⟩ : ∃ d, i = soloWork m n + d := ⟨i - soloWork m n, by omega⟩
    rw [XMach.work_rest (fun _ => 0) hr d, hw]
    exact Nat.le_refl _

/-- **One thread adds `m` and `n` charged `23 * m + 5 * n + 18`
operations on the maps of agents and `23 * m + 2 * n + 10` on the map of
segments, for every size** (`10 * n + 18` and `4 * n + 10` when `m` is
zero): that many when it comes to rest, and never more. -/
theorem solo_ops (m n : Nat) :
    ((XMach.init (sum m n) 1).tally XThread.opsA xsys (fun _ => 0) (soloWork m n) =
          soloOpsA m n ∧
        ∀ i, (XMach.init (sum m n) 1).tally XThread.opsA xsys (fun _ => 0) i ≤
          soloOpsA m n) ∧
      ((XMach.init (sum m n) 1).tally XThread.opsW xsys (fun _ => 0) (soloWork m n) =
          soloOpsW m n ∧
        ∀ i, (XMach.init (sum m n) 1).tally XThread.opsW xsys (fun _ => 0) i ≤
          soloOpsW m n) := by
  obtain ⟨Xf, c, r⟩ := solo_run m n
  rw [XMach.init_one]
  exact r.total

/-- **One thread adds, numbered, in fifteen for each action and, for each
operation, the depth of its own tree, for every size**: the trees of
agents hold at most `3 * m + n + 5` entries and the tree of segments at
most `12 * m + 4 * n + 14`. -/
theorem solo_ztime_ops (m n : Nat) (i : Nat) :
    (ZMach.init (sum m n) 1).ftime xsys (fun _ => 0) i ≤
      15 * soloWork m n + 18 * lg (3 * m + n + 5) * soloOpsA m n +
        21 * lg (12 * m + 4 * n + 14) * soloOpsW m n := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, -⟩ := Below.sizes g.below g.ok.1.symm
  have h := ZMach.ftime_le_ops (xs := xsys) g.ok.1 (sum_nodup m n) Nat.zero_lt_one
    xsys_bounded hL hs hn' (fun _ => 0) i
  have hwi := solo_work_all m n i
  obtain ⟨⟨-, hA⟩, -, hW⟩ := solo_ops m n
  have ha := sum_agents_length_le m n
  have hwl := sum_wires_length_le m n
  have hl1 := lg_mono (show (sum m n).agents.length + 2 * (m + 1) ≤ 3 * m + n + 5 by omega)
  have hl2 := lg_mono
    (show (sum m n).wires.length + 8 * (m + 1) ≤ 12 * m + 4 * n + 14 by omega)
  have hc1 : (max 1 1 + 5) * (3 * lg ((sum m n).agents.length + 2 * (m + 1))) ≤
      18 * lg (3 * m + n + 5) := by
    rw [Nat.max_self]
    omega
  have hc2 : (max 1 1 + 6) * (3 * lg ((sum m n).wires.length + 8 * (m + 1))) ≤
      21 * lg (12 * m + 4 * n + 14) := by
    rw [Nat.max_self]
    omega
  exact Nat.le_trans h (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ hwi) (Nat.mul_le_mul hc1 (hA i)))
    (Nat.mul_le_mul hc2 (hW i)))

/-- **The count is at least the work**: once one thread has added `m` and
`n`, the numbered program has taken at least `22 * m + 3 * n + 13`. -/
theorem solo_ztime_ge (m n : Nat) {i : Nat} (hi : soloWork m n ≤ i) :
    soloWork m n ≤ (ZMach.init (sum m n) 1).ftime xsys (fun _ => 0) i := by
  obtain ⟨hr, hw, -⟩ := solo_work m n
  obtain ⟨d, rfl⟩ : ∃ d, i = soloWork m n + d := ⟨i - soloWork m n, by omega⟩
  have h := ZMach.work_le_ftime (xs := xsys) (good_sum m n).ok.1 (sum_nodup m n)
    Nat.zero_lt_one (fun _ => 0) (soloWork m n + d)
  rw [XMach.work_rest (fun _ => 0) hr d, hw] at h
  exact h

/-- **A run whose count is bounded has its bits bounded**: at most three
times the bits of a key for each unit counted. -/
theorem btime_of_ftime (m n : Nat) {F : Nat}
    (hF : ∀ i, (ZMach.init (sum m n) 1).ftime xsys (fun _ => 0) i ≤ F) (i : Nat) :
    (ZMach.init (sum m n) 1).btime xsys (fun _ => 0) i ≤
      3 * ((lg (5 * m + 2 * n + 13 + sumWork m n 1) + 5) * F) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  obtain ⟨hL, htop⟩ := Below.sizes g.below g.ok.1.symm
  have ha := sum_agents_length_le m n
  have h₁ := Nat.mul_le_mul_left (1 + m + 1) (sum_passBound_le m n)
  have hwork : (1 + (m + 1)) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      sumWork m n 1 := by
    show (1 + m + 1) * (sum m n).passBound (m + 1) 2 8 + (m + 1) * (2 + 8 + 1) ≤
      (1 + m + 1) * (33 * m + 11 * n + 49) + 11 * (m + 1)
    omega
  have hpow := lt_pow_lg (5 * m + 2 * n + 13 + sumWork m n 1)
  have hW : (sum m n).top + 3 * (m + 1 + 1) <
      2 ^ lg (5 * m + 2 * n + 13 + sumWork m n 1) := by omega
  have hW' : (sum m n).agents.length + ((1 + (m + 1)) * (sum m n).passBound (m + 1) 2 8 +
      (m + 1) * (2 + 8 + 1)) < 2 ^ lg (5 * m + 2 * n + 13 + sumWork m n 1) := by omega
  have h := ZMach.btime_le_ftime (xs := xsys) g.ok.1 (sum_nodup m n) xsys_span xsys_ports
    (sum_ports m n) (Nat.succ_pos 0) xsys_bounded hL hs hn' (fun _ => 0) hW hW' i
  refine Nat.le_trans h (Nat.mul_le_mul_left 3 (Nat.mul_le_mul ?_ (hF i)))
  have e1 : lg 2 = 3 := by decide
  rw [Nat.max_self, Nat.one_mul, e1]
  omega

/-- The same in bits. -/
theorem solo_btime_ops (m n : Nat) (i : Nat) :
    (ZMach.init (sum m n) 1).btime xsys (fun _ => 0) i ≤
      3 * ((lg (5 * m + 2 * n + 13 + sumWork m n 1) + 5) *
        (15 * soloWork m n + 18 * lg (3 * m + n + 5) * soloOpsA m n +
          21 * lg (12 * m + 4 * n + 14) * soloOpsW m n)) :=
  btime_of_ftime m n (solo_ztime_ops m n) i

/-- `1000 + 1000` on one thread: exactly 25,013 actions, charged 28,018
operations on the maps of agents and 25,010 on the map of segments; so at
least 25,013 counted once it rests, and at most 14,809,557, and at most
1,421,717,472 bits. -/
theorem _root_.INet.Checks.Arith.Solo.c1
    : (XMach.init (sum 1000 1000) 1).work xsys (fun _ => 0) 25013 = 25013 ∧
    (XMach.init (sum 1000 1000) 1).tally XThread.opsA xsys (fun _ => 0) 25013 = 28018 ∧
    (XMach.init (sum 1000 1000) 1).tally XThread.opsW xsys (fun _ => 0) 25013 = 25010 ∧
    ∀ i, (25013 ≤ i → 25013 ≤ (ZMach.init (sum 1000 1000) 1).ftime xsys (fun _ => 0) i) ∧
      (ZMach.init (sum 1000 1000) 1).ftime xsys (fun _ => 0) i ≤ 14809557 ∧
      (ZMach.init (sum 1000 1000) 1).btime xsys (fun _ => 0) i ≤ 1421717472 := by
  have e : soloWork 1000 1000 = 25013 := by decide
  have ea : soloOpsA 1000 1000 = 28018 := by decide
  have ew : soloOpsW 1000 1000 = 25010 := by decide
  have h := (solo_work 1000 1000).2.1
  have ha := (solo_ops 1000 1000).1.1
  have hw := (solo_ops 1000 1000).2.1
  rw [e] at h ha hw
  rw [ea] at ha
  rw [ew] at hw
  refine ⟨h, ha, hw, fun i => ⟨fun hi => ?_, ?_, ?_⟩⟩
  · have h0 := solo_ztime_ge 1000 1000 (i := i) (by rw [e]; exact hi)
    rw [e] at h0
    exact h0
  · have h1 := solo_ztime_ops 1000 1000 i
    have e1 : 15 * soloWork 1000 1000 + 18 * lg (3 * 1000 + 1000 + 5) * soloOpsA 1000 1000 +
        21 * lg (12 * 1000 + 4 * 1000 + 14) * soloOpsW 1000 1000 = 14809557 := by
      decide +kernel
    rw [e1] at h1
    exact h1
  · have h2 := solo_btime_ops 1000 1000 i
    have e2 : 3 * ((lg (5 * 1000 + 2 * 1000 + 13 + sumWork 1000 1000 1) + 5) *
        (15 * soloWork 1000 1000 + 18 * lg (3 * 1000 + 1000 + 5) * soloOpsA 1000 1000 +
          21 * lg (12 * 1000 + 4 * 1000 + 14) * soloOpsW 1000 1000)) = 1421717472 := by
      decide +kernel
    rw [e2] at h2
    exact h2

/-- `12 + 12` on one thread: 313 actions, charged 354 operations on trees
of at most 53 agents and 310 on a tree of at most 206 segments, so at most
107,889 counted and 6,473,340 bits, where four operations for every action
on trees of 379 entries gave 267,615 and 16,056,900.  The run takes 10,999
and 28,984. -/
theorem _root_.INet.Checks.Arith.Solo.c2
    : ∀ i, (ZMach.init (sum 12 12) 1).ftime xsys (fun _ => 0) i ≤ 107889 ∧
    (ZMach.init (sum 12 12) 1).btime xsys (fun _ => 0) i ≤ 6473340 := by
  intro i
  have h1 := solo_ztime_ops 12 12 i
  have h2 := solo_btime_ops 12 12 i
  have e1 : 15 * soloWork 12 12 + 18 * lg (3 * 12 + 12 + 5) * soloOpsA 12 12 +
      21 * lg (12 * 12 + 4 * 12 + 14) * soloOpsW 12 12 = 107889 := by decide +kernel
  have e2 : 3 * ((lg (5 * 12 + 2 * 12 + 13 + sumWork 12 12 1) + 5) *
      (15 * soloWork 12 12 + 18 * lg (3 * 12 + 12 + 5) * soloOpsA 12 12 +
        21 * lg (12 * 12 + 4 * 12 + 14) * soloOpsW 12 12)) = 6473340 := by decide +kernel
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩


/-- The invariant of the rounds is about the agents and the set of
segments only. -/
theorem Steady.congr {n hi : Nat} {X Y : XNet Arith} (hA : Y.agents = X.agents)
    (hW : ∀ e, e ∈ Y.wires ↔ e ∈ X.wires) (st : Steady n X hi) : Steady n Y hi := by
  obtain ⟨rest, hr⟩ := st.head
  refine ⟨⟨rest, by rw [hA, hr]⟩, fun q => ?_, fun q => ?_,
    ⟨fun t h1 h2 => ?_, fun t h1 h2 q => ?_⟩, fun t h1 h2 k q hm => ?_⟩
  · rw [hW]
    exact st.first q
  · rw [hW]
    exact st.mid q
  · rw [hA]
    exact st.chain.live t h1 h2
  · rw [hW]
    exact st.chain.seg t h1 h2 q
  · exact st.fresh t h1 h2 k q ((hW _).1 hm)

theorem Hist.congr {n T r d : Nat} {X0 X Y : XNet Arith} (hA : Y.agents = X.agents)
    (hW : ∀ e, e ∈ Y.wires ↔ e ∈ X.wires) (H : Hist n X0 X T r d) : Hist n X0 Y T r d :=
  ⟨H.top, by rw [hA, H.agents], fun e => by rw [hW]; exact H.wires e⟩

/-- The two presentations of the rule for a successor write the same
segments. -/
theorem mem_swap_links (s a : Id) (e : Port × Port) :
    e ∈ addSucc.swap.toX.newLinks ar s a .succ .add ↔
      e ∈ addSucc.toX.newLinks ar a s .add .succ := by
  rw [newLinks_swap, newLinks_add]
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  constructor <;> rintro (h | h | h | h | h | h | h | h) <;> simp [h]

/-- **A round leaves the same memory whichever agent of the pair the
thread came from**: the same agents in the same order, and the same
segments. -/
theorem stepS_agents {X : XNet Arith} {s a : Id} (hne : a ≠ s) :
    (stepS X s a).agents = (stepA X a s).agents := by
  unfold stepS stepA
  rw [newAgents_swap hne, newAgents_add hne, XNet.step_agents, XNet.step_agents, filter_comm']

theorem stepS_wires (X : XNet Arith) (s a : Id) (e : Port × Port) :
    e ∈ (stepS X s a).wires ↔ e ∈ (stepA X a s).wires := by
  unfold stepS stepA
  rw [XNet.mem_step_wires, XNet.mem_step_wires]
  show e ∈ addSucc.swap.toX.newLinks ar s a .succ .add ∨ _ ↔
    e ∈ addSucc.toX.newLinks ar a s .add .succ ∨ _
  rw [mem_swap_links]

/-- **The principal port of a successor below the top of the first
argument is wired to the successor above it.** -/
theorem sum_princ : ∀ (m n t : Nat), n + 4 ≤ t → t < m + n + 3 → ∀ q,
    ((([t], 0), q) : Port × Port) ∈ (sum m n).wires ↔ q = ([t + 1], 1)
  | 0, n, t, h1, h2 => absurd h2 (by omega)
  | m + 1, n, t, h1, h2 => by
    intro q
    have hfresh : ∀ k q, ((([m + n + 4], k), q) : Port × Port) ∉ (sum m n).wires := by
      intro k q hm
      obtain ⟨j, hj, ej⟩ := (good_sum m n).below [m + n + 4] (.inr (.inl ⟨k, q, hm⟩))
      injection ej with e1
      omega
    rw [sum_push]
    by_cases ht : t = m + n + 3
    · have hb : below n (m + n + 3) = [m + n + 3] := below_pos (by omega)
      obtain ⟨-, -, -, N4⟩ := insert1_new (sum m n) [m + n + 4] .succ ([1], 0)
        ([m + n + 3], 0) (by ports_differ) (by ports_differ) (by ports_differ) hfresh
      rw [hb, ht]
      exact N4 q
    · have hq : (([t], 0) : Port) ≠ (below n (m + n + 3), 0) := by
        rcases below_cases n (m + n + 3) with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] <;> ports_differ
      rw [insert1_frame (sum m n) [m + n + 4] .succ ([1], 0) (below n (m + n + 3), 0) ([t], 0)
        (by ports_differ) hq (by ports_differ)]
      exact sum_princ m n t h1 (by omega) q

section MidRun

variable {n T r d : Nat} {X0 X : XNet Arith}

/-- The rounds write no segment at a principal port of an old agent. -/
theorem Hist.old (H : Hist n X0 X T r d) (j : Nat) (q : Port) :
    ((([j], 0), q) : Port × Port) ∈ X.wires ↔ ((([j], 0), q) : Port × Port) ∈ X0.wires := by
  rw [H.wires]
  constructor
  · rintro (h | h | ⟨t, -, -, h⟩)
    · exact h
    · rw [linksS_single] at h
      rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    · rw [linksA_single] at h
      omega
  · exact .inl

/-- Every segment of the memory in the middle of the run is a segment of
the memory at the end of the rounds. -/
theorem Hist.sub (H : Hist n X0 X T r d) {Xf : XNet Arith} {dF : Nat}
    (F : Final n X0 Xf T dF) (e : Port × Port) (he : e ∈ X.wires) : e ∈ Xf.wires := by
  rcases (H.wires e).1 he with h | h | ⟨t, h1, h2, h3⟩
  · exact (F.wires e).2 (.inl h)
  · exact (F.wires e).2 (.inr (.inl h))
  · exact (F.wires e).2 (.inr (.inr (.inl ⟨t, by omega, h2, h3⟩)))

/-- A name that is not the adder, a successor of the result or one of the
old agents left is not an agent of the memory. -/
theorem Hist.no_name (H : Hist n X0 X T r d) {i : Id} (h1 : i ≠ [0, n + 3 + r + 1])
    (h2 : ∀ e ∈ resL (n + 3 + r) d, e.1 ≠ i) (h3 : ∀ j, 2 ≤ j → j ≤ n + 3 + r → i ≠ [j]) :
    assoc i X.agents = none := by
  rw [H.agents]
  show (if ([0, n + 3 + r + 1] : Id) = i then some Arith.add
    else assoc i (resL (n + 3 + r) d ++ (chainL n r ++ tailA n))) = none
  rw [ite_neg' (fun e => h1 e.symm)]
  refine assoc_none_of_forall fun e he e' => ?_
  rcases List.mem_append.1 he with h | h
  · exact h2 e h e'
  · obtain ⟨j, hj1, hj2, hj3⟩ := mem_rest h
    exact h3 j hj1 hj2 (e'.symm.trans hj3)

theorem Hist.no_zero (H : Hist n X0 X T r d) : assoc [0] X.agents = none :=
  H.no_name (fun e => by injection e with _ e2; cases e2) (fun e he => res_ne_single he 0)
    (fun j hj _ e => by injection e with e1; omega)

/-- A successor of the result is an agent of the memory. -/
theorem Hist.agent_res (H : Hist n X0 X T r d) {e : Id × Arith}
    (he : e ∈ resL (n + 3 + r) d) : assoc e.1 X.agents = some e.2 := by
  have hin : e ∈ X.agents := by
    rw [H.agents]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ he)
  refine assoc_eq_of_unique hin (fun γ hγ => ?_)
  rw [H.agents] at hγ
  have hs := (mem_resL he).1
  rcases List.mem_cons.1 hγ with h | h
  · exfalso
    injection h with e1 _
    exact res_ne_adder he _ (by omega) e1
  · rcases List.mem_append.1 h with h | h
    · have hγs : γ = Arith.succ := (mem_resL h).1
      rw [hγs]
      exact hs.symm
    · exfalso
      obtain ⟨j, -, -, hj⟩ := mem_rest h
      exact res_ne_single he j hj

/-- **In the middle of the run a thread passes the successors of the
result as at the end**: four actions each, and nothing written. -/
theorem Hist.pass_res (H : Hist n X0 X T r d) {Xf : XNet Arith} {dF : Nat}
    (F : Final n X0 Xf T dF) (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    (rest : List (Id × Arith)) : ∀ (d' h : Nat), n + 3 + r ≤ h → h + d' + 1 = T →
      (∀ e ∈ resL h d', e ∈ resL (n + 3 + r) d) →
      Stays xsys X ⟨resL h d' ++ rest, .idle⟩ ⟨rest, .idle⟩ (4 * (d' + 1))
  | 0, h, _, _, hm => by
    have h₁ : assoc [0, 1] X.agents = some Arith.succ :=
      H.agent_res (hm _ List.mem_cons_self)
    have h₂ : assoc (([0, 1], 0) : Port) X.wires = some ([1], 2) :=
      assoc_eq_of_unique
        ((H.wires _).2 (.inr (.inl ((linksS_adder _ _ _ _).2 (.inl ⟨rfl, rfl, rfl⟩)))))
        (fun q' hq => (F.first_zero hfr q').1 (H.sub F _ hq))
    have hd : X.Dead ([0, 1], 0) ([1], 2) 2 :=
      XNet.dead_two_of rfl ((ite_pos' rfl).trans H.no_zero)
        ((H.wires _).2 (.inl ((S.res _).2 rfl))) (by ports_differ)
        (fun q hq => ((F.one_two S q).1 (H.sub F _ hq)).symm)
        (fun q hq => (F.out S q).1 (H.sub F _ hq))
    exact Stays.dead (xs := xsys) (e := ([0, 1], Arith.succ)) (k := 2) rest h₁ h₂ hd
  | d' + 1, h, hh, hT', hm => by
    have hx1 : n + 3 < h + 1 := by omega
    have hx2 : h + 1 < T := by omega
    have h₁ : assoc [0, 0, h + 2] X.agents = some Arith.succ :=
      H.agent_res (hm _ List.mem_cons_self)
    have h₂ : assoc (([0, 0, h + 2], 0) : Port) X.wires = some ([0, h + 2], 2) :=
      assoc_eq_of_unique
        ((H.wires _).2 (.inr (.inr ⟨h + 1, by omega, hx2,
          (linksA_res _ _ _ _).2 (.inl ⟨rfl, rfl, rfl⟩)⟩)))
        (fun q' hq => (F.res_zero hfr hx1 hx2 q').1 (H.sub F _ hq))
    have W := F.adder_two hfr (x := h + 2) (by omega) (by omega)
    have hd : X.Dead ([0, 0, h + 2], 0) ([0, h + 2], 2) 2 := by
      by_cases hxT : h + 2 = T
      · refine XNet.dead_two_of (w := ([0, 1], 1)) rfl rfl ?_ (by ports_differ)
          (fun q hq => ?_) (fun q hq => ?_)
        · exact (H.wires _).2 (.inr (.inl ((linksS_adder _ _ _ _).2
            (.inr (.inr (.inr (.inr ⟨hxT, rfl, rfl⟩)))))))
        · rcases (W q).1 (H.sub F _ hq) with ⟨-, h'⟩ | ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩
          · exact .inr h'
          · omega
          · exact .inl h'
          · omega
        · rw [(F.first_one hfr q).1 (H.sub F _ hq), hxT]
      · refine XNet.dead_two_of (w := ([0, 0, h + 2 + 1], 1)) rfl rfl ?_ (by ports_differ)
          (fun q hq => ?_) (fun q hq => ?_)
        · exact (H.wires _).2 (.inr (.inr ⟨h + 2, by omega, by omega,
            (linksA_adder _ _ _ _).2 (.inr (.inr (.inr (.inr ⟨rfl, rfl, rfl⟩))))⟩))
        · rcases (W q).1 (H.sub F _ hq) with ⟨h', -⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨h', -⟩
          · exact absurd h' hxT
          · exact .inr h'
          · exact .inl h'
          · omega
        · exact (F.res_one hfr (t := h + 2) (by omega) (by omega) q).1 (H.sub F _ hq)
    have w₁ : Stays xsys X ⟨([0, 0, h + 2], Arith.succ) :: (resL (h + 1) d' ++ rest), .idle⟩
        ⟨resL (h + 1) d' ++ rest, .idle⟩ 4 :=
      Stays.dead (xs := xsys) (e := ([0, 0, h + 2], Arith.succ)) (k := 2) _ h₁ h₂ hd
    have w₂ := Hist.pass_res H F S hfr rest d' (h + 1) (by omega) (by omega)
      (fun e he => hm e (List.mem_cons_of_mem _ he))
    have w := w₁.trans w₂
    have e1 : 4 + 4 * (d' + 1) = 4 * (d' + 1 + 1) := by omega
    rw [e1] at w
    exact w

end MidRun

/-- **A round from the side of the successor.**  A thread whose first
agent is the next successor of the chain reaches the adder through the
port of the successor above, claims the pair and writes: seventeen
actions, and the memory is that of the round made from the adder, with
its segments written in another order. -/
theorem Steady.round_swap {n : Nat} {X : XNet Arith} {h : Nat} (st : Steady n X (h + 1))
    (hn : n + 4 ≤ h + 1)
    (hp : ∀ q, ((([h + 1], 0), q) : Port × Port) ∈ X.wires ↔ q = ([h + 1 + 1], 1))
    (rest : List (Id × Arith)) :
    Works xsys X ⟨([h + 1], .succ) :: rest, .idle⟩ (stepS X [h + 1] [0, h + 1 + 1])
      ⟨(stepS X [h + 1] [0, h + 1 + 1]).agents, .idle⟩ 1 17 := by
  obtain ⟨rest', hA⟩ := st.head
  have hb : below n (h + 1) = [h + 1] := below_pos hn
  have hne : ([h + 1] : Id) ≠ [0, h + 1 + 1] := fun e => by
    injection e with _ e2
    cases e2
  have hne' : ([0, h + 1 + 1] : Id) ≠ [h + 1] := fun e => hne e.symm
  have h₁ : assoc [h + 1] X.agents = some .succ := st.chain.live (h + 1) hn (Nat.le_refl _)
  have h₂ : assoc (([h + 1], 0) : Port) X.wires = some ([h + 1 + 1], 1) :=
    assoc_eq_of_unique ((hp _).2 rfl) (fun q' hq => (hp q').1 hq)
  have h₂' : nextSeg X.wires ([h + 1 + 1], 1) ([h + 1], 0) = some ([0, h + 1 + 1], 0) := by
    refine nextSeg_some ((st.mid _).2 (.inl rfl)) (by ports_differ) (fun q hq hqp => ?_)
    rcases (st.mid q).1 hq with e | e
    · exact e
    · rw [hb] at e
      exact absurd e hqp
  have h₃ : assoc [0, h + 1 + 1] X.agents = some .add := by
    rw [hA]
    show (if ([0, h + 1 + 1] : Id) = [0, h + 1 + 1] then some Arith.add
      else assoc _ rest') = _
    rw [ite_pos' rfl]
  have h₄ : assoc [0, h + 1 + 1] (X.takeAgent [h + 1]).agents = some .add := by
    show assoc [0, h + 1 + 1] (X.agents.filter fun e => decide (e.1 ≠ [h + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact h₃
  have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
  have w := Works.claim_via (xs := xsys) (c := ([h + 1 + 1], 1)) rest h₁ h₂ rfl h₂' h₃ hne h₄ hR
  have eA := newAgents_swap (a := [0, h + 1 + 1]) (s := [h + 1]) hne'
  have eK : 6 + ((addSucc.swap.toX.newAgents [h + 1] [0, h + 1 + 1]).length +
      (addSucc.swap.toX.newLinks xsys.sys.ar [h + 1] [0, h + 1 + 1] .succ .add).length + 1) =
      17 := by
    rw [eA]
    rfl
  rw [eK] at w
  exact w

/-- **A block of the alternating run.**  The thread whose list is that of
the memory before the last round finds its first agent gone, passes the
successors of the result, finds the next successor gone, and claims the
pair from the successor after it: four actions for each successor of the
result that it lists and nineteen more. -/
theorem alt_block {n T r d' : Nat} {X0 X Xf : XNet Arith} {dF : Nat}
    (H : Hist n X0 X T (r + 1) (d' + 1)) (st : Steady n X (n + 3 + r + 1))
    (F : Final n X0 Xf T dF) (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    (hP : ∀ t, n + 4 ≤ t → t < T → ∀ q,
      ((([t], 0), q) : Port × Port) ∈ X0.wires ↔ q = ([t + 1], 1)) :
    Works xsys X
        ⟨([0, n + 3 + r + 3], .add) ::
          (resL (n + 3 + r + 2) d' ++ (chainL n (r + 2) ++ tailA n)), .idle⟩
        (stepS X [n + 3 + r + 1] [0, n + 3 + r + 1 + 1])
        ⟨(stepS X [n + 3 + r + 1] [0, n + 3 + r + 1 + 1]).agents, .idle⟩ 1
        (4 * (d' + 1) + 19) ∧
      Steady n (stepS X [n + 3 + r + 1] [0, n + 3 + r + 1 + 1]) (n + 3 + r) ∧
      Hist n X0 (stepS X [n + 3 + r + 1] [0, n + 3 + r + 1 + 1]) T r (d' + 2) := by
  have hT := H.top
  have a1 : assoc [0, n + 3 + r + 3] X.agents = none :=
    H.no_name (fun e => by injection e with _ e2; injection e2 with e3; omega)
      (fun e he => res_ne_adder he _ (by omega))
      (fun j _ _ e => by injection e with _ e2; cases e2)
  have w₁ : Stays xsys X
      ⟨([0, n + 3 + r + 3], Arith.add) ::
        (resL (n + 3 + r + 2) d' ++ (chainL n (r + 2) ++ tailA n)), .idle⟩
      ⟨resL (n + 3 + r + 2) d' ++ (chainL n (r + 2) ++ tailA n), .idle⟩ 1 :=
    Stays.absent _ (fun h => by
      have h' : assoc [0, n + 3 + r + 3] X.agents = some Arith.add := h
      rw [a1] at h'
      cases h')
  have w₂ := H.pass_res F S hfr (chainL n (r + 2) ++ tailA n) d' (n + 3 + r + 2) (by omega)
    (by omega) (fun e he => List.mem_cons_of_mem _ he)
  have a2 : assoc [n + 3 + r + 2] X.agents = none :=
    H.no_name (fun e => by injection e with _ e2; cases e2) (fun e he => res_ne_single he _)
      (fun j _ hj e => by injection e with e1; omega)
  have w₃ : Stays xsys X
      ⟨([n + 3 + r + 2], Arith.succ) ::
        (([n + 3 + r + 1], Arith.succ) :: (chainL n r ++ tailA n)), .idle⟩
      ⟨([n + 3 + r + 1], Arith.succ) :: (chainL n r ++ tailA n), .idle⟩ 1 :=
    Stays.absent _ (fun h => by
      have h' : assoc [n + 3 + r + 2] X.agents = some Arith.succ := h
      rw [a2] at h'
      cases h')
  have hp : ∀ q, ((([n + 3 + r + 1], 0), q) : Port × Port) ∈ X.wires ↔
      q = ([n + 3 + r + 1 + 1], 1) := fun q => by
    rw [H.old]
    exact hP (n + 3 + r + 1) (by omega) (by omega) q
  have w₄ := Steady.round_swap st (by omega) hp (chainL n r ++ tailA n)
  have hne' : ([0, n + 3 + r + 1 + 1] : Id) ≠ [n + 3 + r + 1] := fun e => by
    injection e with _ e2
    cases e2
  have st' := (Steady.round_exact st (by omega)).2
  have H' := H.step
  refine ⟨?_, Steady.congr (stepS_agents hne') (stepS_wires X _ _) st',
    Hist.congr (stepS_agents hne') (stepS_wires X _ _) H'⟩
  have w := ((w₁.trans w₂).trans w₃).works.trans w₄
  have e : 1 + 4 * (d' + 1) + 1 + 17 = 4 * (d' + 1) + 19 := by omega
  rw [e, Nat.zero_add] at w
  exact w

/-- The blocks of the alternating run: `r` of them, the first for thread
`t`, which lists `d` successors of the result. -/
def altTail : Nat → Nat → Nat → List (Nat × Nat)
  | _, _, 0 => []
  | t, d, r + 1 => (t, 4 * d + 19) :: altTail (1 - t) (d + 1) r

/-- The actions of those blocks. -/
def altSum : Nat → Nat → Nat
  | _, 0 => 0
  | d, r + 1 => 4 * d + 19 + altSum (d + 1) r

theorem altSum_eq : ∀ r d, altSum d r = 2 * (r * r) + 4 * (d * r) + 17 * r
  | 0, _ => rfl
  | r + 1, d => by
    have ih := altSum_eq r (d + 1)
    have e1 : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by
      rw [Nat.mul_succ, Nat.succ_mul]
      omega
    have e2 : d * (r + 1) = d * r + d := Nat.mul_succ d r
    have e3 : (d + 1) * r = d * r + r := Nat.succ_mul d r
    show 4 * d + 19 + altSum (d + 1) r = _
    rw [ih, e1, e2, e3]
    omega

/-- **The alternating run.**  From a memory with `r + 1` successors left
on the first argument, with one thread holding the list of that memory
and the other the list of the memory one round before, the threads claim
the pairs in turn: every block is a counted run of the thread that holds
the older list. -/
theorem alt_run {n T : Nat} {X0 Xf : XNet Arith} {dF : Nat} (F : Final n X0 Xf T dF)
    (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    (hP : ∀ t, n + 4 ≤ t → t < T → ∀ q,
      ((([t], 0), q) : Port × Port) ∈ X0.wires ↔ q = ([t + 1], 1)) :
    ∀ (r d' : Nat) (X : XNet Arith), Hist n X0 X T (r + 1) (d' + 1) →
      Steady n X (n + 3 + r + 1) →
      BlockRun xsys
          ⟨X, [⟨([0, n + 3 + r + 3], .add) ::
            (resL (n + 3 + r + 2) d' ++ (chainL n (r + 2) ++ tailA n)), .idle⟩,
            ⟨X.agents, .idle⟩]⟩
          (altTail 0 (d' + 1) (r + 1)) (altSum (d' + 1) (r + 1)) ∧
        BlockRun xsys
          ⟨X, [⟨X.agents, .idle⟩, ⟨([0, n + 3 + r + 3], .add) ::
            (resL (n + 3 + r + 2) d' ++ (chainL n (r + 2) ++ tailA n)), .idle⟩]⟩
          (altTail 1 (d' + 1) (r + 1)) (altSum (d' + 1) (r + 1))
  | 0, d', X, H, st => by
    obtain ⟨w, -, -⟩ := alt_block H st F S hfr hP
    exact ⟨.cons (t := 0) rfl w (.done _ _), .cons (t := 1) rfl w (.done _ _)⟩
  | r + 1, d', X, H, st => by
    obtain ⟨w, st', H'⟩ := alt_block H st F S hfr hP
    obtain ⟨ih0, ih1⟩ := alt_run F S hfr hP r (d' + 1) _ H' st'
    have hA := H.agents
    refine ⟨.cons (t := 0) rfl w ?_, .cons (t := 1) rfl w ?_⟩
    · show BlockRun xsys ⟨_, [_, ⟨X.agents, .idle⟩]⟩ _ _
      rw [hA]
      exact ih1
    · show BlockRun xsys ⟨_, [⟨X.agents, .idle⟩, _]⟩ _ _
      rw [hA]
      exact ih0

/-- The schedule of the alternating run on the net for `(m + 2) + n`:
thread zero for the first round, thread one for the second, and then the
threads in turn, each for as long as its block. -/
def altSched (m : Nat) : Nat → Nat := blockSched ((0, 16) :: (1, 17) :: altTail 0 1 m)

/-- **Two threads in turn on the net for `(m + 2) + n`**: under the
alternating schedule every one of the first `2 * m * m + 21 * m + 33`
actions is a counted action of the thread scheduled. -/
theorem two_run (m n : Nat) :
    BlockRun xsys (XMach.init (sum (m + 2) n) 2) ((0, 16) :: (1, 17) :: altTail 0 1 m)
      (16 + (17 + altSum 1 m)) := by
  obtain ⟨Xf, -, F⟩ := solo_rounds (m + 1) n
  have S := snd_sum (m + 2) n
  have hfr := sum_fresh (m + 2) n
  have hP : ∀ t, n + 4 ≤ t → t < n + 3 + (m + 1) + 1 → ∀ q,
      ((([t], 0), q) : Port × Port) ∈ (sum (m + 2) n).wires ↔ q = ([t + 1], 1) :=
    fun t h1 h2 q => sum_princ (m + 2) n t h1 (by omega) q
  have st0 : Start n (sum (m + 2) n) (n + 3 + (m + 1)) := by
    have h := start_sum (m + 1) n
    have e : m + 1 + n + 3 = n + 3 + (m + 1) := by omega
    rw [e] at h
    exact h
  obtain ⟨o1, st1⟩ := Start.round_exact st0
  have w1 := o1.works
  have hAg := sum_agents (m + 2) n
  have H1 : Hist n (sum (m + 2) n) (stepS (sum (m + 2) n) [n + 3 + (m + 1) + 1] [1])
      (n + 3 + (m + 1) + 1) (m + 1) 0 := hist_start hAg
  have st1' : Steady n (stepS (sum (m + 2) n) [n + 3 + (m + 1) + 1] [1]) (n + 3 + m + 1) := st1
  have hp1 : ∀ q, ((([n + 3 + m + 1], 0), q) : Port × Port) ∈
      (stepS (sum (m + 2) n) [n + 3 + (m + 1) + 1] [1]).wires ↔
      q = ([n + 3 + m + 1 + 1], 1) := fun q => by
    rw [H1.old]
    exact hP _ (by omega) (by omega) q
  have w2 := Steady.round_swap st1' (by omega) hp1
    ((chainL n m ++ (sndL n ++ base.agents)) ++ [([n + 3 + (m + 1) + 1], Arith.succ)])
  have hne' : ([0, n + 3 + m + 1 + 1] : Id) ≠ [n + 3 + m + 1] := fun e => by
    injection e with _ e2
    cases e2
  have st2 := Steady.congr (stepS_agents hne')
    (stepS_wires (stepS (sum (m + 2) n) [n + 3 + (m + 1) + 1] [1]) _ _)
    (Steady.round_exact st1' (by omega)).2
  have H2 := Hist.congr (stepS_agents hne')
    (stepS_wires (stepS (sum (m + 2) n) [n + 3 + (m + 1) + 1] [1]) _ _) H1.step
  have e1 : (sum (m + 2) n).agents.drop 1 ++ (sum (m + 2) n).agents.take 1 =
      ([n + 3 + m + 1], Arith.succ) ::
        ((chainL n m ++ (sndL n ++ base.agents)) ++
          [([n + 3 + (m + 1) + 1], Arith.succ)]) := by
    rw [hAg]
    rfl
  have hinit : XMach.init (sum (m + 2) n) 2 =
      ⟨sum (m + 2) n, [⟨(sum (m + 2) n).agents, .idle⟩,
        ⟨([n + 3 + m + 1], Arith.succ) ::
          ((chainL n m ++ (sndL n ++ base.agents)) ++
            [([n + 3 + (m + 1) + 1], Arith.succ)]), .idle⟩]⟩ := by
    show (⟨sum (m + 2) n, [⟨(sum (m + 2) n).agents ++ [], .idle⟩,
      ⟨(sum (m + 2) n).agents.drop 1 ++ (sum (m + 2) n).agents.take 1, .idle⟩]⟩ :
        XMach Arith) = _
    rw [List.append_nil, e1]
  rw [hinit]
  refine .cons (t := 0) rfl w1 (.cons (t := 1) rfl w2 ?_)
  cases m with
  | zero => exact .done _ _
  | succ m =>
    obtain ⟨r0, -⟩ := alt_run F S hfr hP m 0 _ H2 st2
    have hA1 := H1.agents
    show BlockRun xsys ⟨_, [⟨(stepS (sum (m + 1 + 2) n) [n + 3 + (m + 1 + 1) + 1] [1]).agents,
      .idle⟩, _]⟩ _ _
    rw [hA1]
    exact r0

/-- **With two threads and a schedule that takes turns, addition takes
quadratic work.**  On the net for `(m + 2) + n`, under the alternating
schedule, the first `2 * m * m + 21 * m + 33` actions are all work, so
the work is at least that from then on. -/
theorem two_threads_quadratic (m n : Nat) :
    (XMach.init (sum (m + 2) n) 2).work xsys (altSched m) (2 * (m * m) + 21 * m + 33) =
        2 * (m * m) + 21 * m + 33 ∧
      ∀ i, 2 * (m * m) + 21 * m + 33 ≤ i →
        2 * (m * m) + 21 * m + 33 ≤ (XMach.init (sum (m + 2) n) 2).work xsys (altSched m) i := by
  have r := two_run m n
  have e : 16 + (17 + altSum 1 m) = 2 * (m * m) + 21 * m + 33 := by
    rw [altSum_eq, Nat.one_mul]
    omega
  rw [e] at r
  exact ⟨r.work, fun i hi => r.work_ge hi⟩

/-- **A second thread can make addition slower by any factor.**  For
`m` at least five and `n` at most `m`, the work of two threads under the
alternating schedule passes the whole work of one thread. -/
theorem two_threads_slower (m n : Nat) (hm : 5 ≤ m) (hn : n ≤ m) :
    soloWork (m + 2) n < (XMach.init (sum (m + 2) n) 2).work xsys (altSched m)
      (2 * (m * m) + 21 * m + 33) := by
  rw [(two_threads_quadratic m n).1]
  have e : soloWork (m + 2) n = 22 * (m + 2) + 3 * n + 13 := by
    unfold soloWork
    rw [ite_neg' (Nat.succ_ne_zero (m + 1))]
  have h := Nat.mul_le_mul_right m hm
  rw [e]
  omega

/-- The same for any schedule that begins as the alternating one: the
work is at least `2 * m * m + 21 * m + 33` from that many actions on,
however the threads are scheduled afterwards. -/
theorem two_threads_any (m n : Nat) (σ : Nat → Nat)
    (hσ : ∀ j, j < 2 * (m * m) + 21 * m + 33 → σ j = altSched m j) :
    ∀ i, 2 * (m * m) + 21 * m + 33 ≤ i →
      2 * (m * m) + 21 * m + 33 ≤ (XMach.init (sum (m + 2) n) 2).work xsys σ i := by
  intro i hi
  have h := XMach.work_mono (xs := xsys) σ (XMach.init (sum (m + 2) n) 2) hi
  have e : (XMach.init (sum (m + 2) n) 2).work xsys σ (2 * (m * m) + 21 * m + 33) =
      (XMach.init (sum (m + 2) n) 2).work xsys (altSched m) (2 * (m * m) + 21 * m + 33) :=
    XMach.tally_congr XThread.busy xsys _ _ hσ
  rw [e, (two_threads_quadratic m n).1] at h
  exact h

/-- **A second thread can make addition slower by any factor.**  For `n`
at most `m` and `m` at least thirteen times `c`, the work of two threads
under the alternating schedule passes `c` times the whole work of one
thread. -/
theorem two_threads_factor (c m n : Nat) (hc : 13 * c ≤ m) (hn : n ≤ m) :
    c * soloWork (m + 2) n < (XMach.init (sum (m + 2) n) 2).work xsys (altSched m)
      (2 * (m * m) + 21 * m + 33) := by
  rw [(two_threads_quadratic m n).1]
  have e : soloWork (m + 2) n = 22 * (m + 2) + 3 * n + 13 := by
    unfold soloWork
    rw [ite_neg' (Nat.succ_ne_zero (m + 1))]
  have h1 : 13 * (c * m) ≤ m * m := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right m hc
  have h2 : c * soloWork (m + 2) n ≤ c * (25 * m + 57) :=
    Nat.mul_le_mul_left c (by rw [e]; omega)
  have h3 : c * (25 * m + 57) = 25 * (c * m) + 57 * c := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm c 57]
  omega

/-- `100 + 0` with two more successors: one thread takes 2,257 actions in
all; two threads taking turns have taken 22,133 before the successors of
the first argument are gone. -/
theorem _root_.INet.Checks.Arith.Solo.c3
    : (XMach.init (sum 102 0) 1).work xsys (fun _ => 0) 2257 = 2257 ∧
    (∀ i, (XMach.init (sum 102 0) 1).work xsys (fun _ => 0) i ≤ 2257) ∧
    ∀ i, 22133 ≤ i → 22133 ≤ (XMach.init (sum 102 0) 2).work xsys (altSched 100) i := by
  have e : soloWork 102 0 = 2257 := by decide
  have h := (solo_work 102 0).2.1
  have ha := solo_work_all 102 0
  rw [e] at h ha
  exact ⟨h, ha, (two_threads_quadratic 100 0).2⟩

end Arith

end INet
