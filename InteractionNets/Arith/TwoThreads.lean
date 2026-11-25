import InteractionNets.Arith.Solo

/-! ### Two threads on an addition: the reader and the race for the last pair -/

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

namespace Arith

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

variable {j m n : Nat}

local macro "ports_differ" : tactic =>
  `(tactic| first | (intro e; simp at e; done) | (intro e; simp at e; omega))

/-- The zero of the first argument faces the lowest successor of the
chain. -/
theorem sum_two : ∀ (m n : Nat) (q : Port),
    ((([2], 0), q) : Port × Port) ∈ (sum (m + 1) n).wires ↔ q = ([n + 4], 1)
  | 0, n, q => by
    have hfresh : ∀ k q, ((([0 + n + 4], k), q) : Port × Port) ∉ (sum 0 n).wires := by
      intro k q hm
      obtain ⟨j, hj, ej⟩ := (good_sum 0 n).below [0 + n + 4] (.inr (.inl ⟨k, q, hm⟩))
      injection ej with e1
      omega
    have hb : below n (0 + n + 3) = [2] := by
      rcases below_cases n (0 + n + 3) with ⟨-, h⟩ | ⟨hb, -⟩
      · omega
      · exact hb
    obtain ⟨-, -, -, N4⟩ := insert1_new (sum 0 n) [0 + n + 4] .succ ([1], 0)
      ([2], 0) (by ports_differ) (by ports_differ) (by ports_differ) hfresh
    rw [sum_push, hb, N4 q, Nat.zero_add]
  | m + 1, n, q => by
    have hb : below n (m + 1 + n + 3) = [m + 1 + n + 3] := below_pos (by omega)
    rw [sum_push, hb, insert1_frame (sum (m + 1) n) [m + 1 + n + 4] .succ ([1], 0)
      ([m + 1 + n + 3], 0) ([2], 0) (by ports_differ) (by ports_differ) (by ports_differ)]
    exact sum_two m n q

/-- The four rules of the system. -/
theorem rule_cases {α β : Arith} {R : XRhs Arith} (hR : xsys.rule α β = some R) :
    R = addZero.toX ∨ R = addZero.swap.toX ∨ R = addSucc.toX ∨ R = addSucc.swap.toX := by
  cases α <;> cases β <;> first
    | exact .inl (Option.some.inj hR).symm
    | exact .inr (.inl (Option.some.inj hR).symm)
    | exact .inr (.inr (.inl (Option.some.inj hR).symm))
    | exact .inr (.inr (.inr (Option.some.inj hR).symm))
    | (exfalso
       revert hR
       show (none : Option (XRhs Arith)) = some R → False
       intro h
       cases h)

/-- Every agent a rule makes has a name that begins with `0`. -/
theorem new_head {α β : Arith} {R : XRhs Arith} {a b : Id} {e : Id × Arith}
    (hR : xsys.rule α β = some R) (he : e ∈ R.newAgents a b) : ∃ i, e.1 = 0 :: i := by
  have he' := dedupFst_sub _ _ he
  rcases rule_cases hR with rfl | rfl | rfl | rfl
  · cases (show e ∈ ([] : List (Id × Arith)) from he')
  · cases (show e ∈ ([] : List (Id × Arith)) from he')
  · have h2 : e ∈ [(0 :: a, Arith.succ), (0 :: b, Arith.add)] := he'
    rcases List.mem_cons.1 h2 with e1 | h3
    · exact ⟨a, by rw [e1]⟩
    · rcases List.mem_cons.1 h3 with e1 | h4
      · exact ⟨b, by rw [e1]⟩
      · cases h4
  · have h2 : e ∈ [(0 :: b, Arith.succ), (0 :: a, Arith.add)] := he'
    rcases List.mem_cons.1 h2 with e1 | h3
    · exact ⟨b, by rw [e1]⟩
    · rcases List.mem_cons.1 h3 with e1 | h4
      · exact ⟨a, by rw [e1]⟩
      · cases h4

theorem single_ne_new {k : Nat} (hk : k ≠ 0) {e : Id × Arith} (h : ∃ i, e.1 = 0 :: i) :
    e.1 ≠ [k] := by
  obtain ⟨i, hi⟩ := h
  intro e'
  rw [hi] at e'
  injection e' with e1 _
  exact hk e1.symm

/-- **The first actions of the first round**: three that read, then the
top successor and the adder are taken. -/
theorem Start.five {n : Nat} {X : XNet Arith} {hi : Nat} (st : Start n X hi) :
    (XMach.solo xsys X ⟨X.agents, .idle⟩ 3).1 = X ∧
      ∃ rest as ls, XMach.solo xsys X ⟨X.agents, .idle⟩ 5 =
          ((X.takeAgent [hi + 1]).takeAgent [1], ⟨rest, .write as ls⟩) ∧
        ∀ e ∈ as, ∃ i, e.1 = 0 :: i := by
  obtain ⟨rest, hA⟩ := st.head
  have hne : ([hi + 1] : Id) ≠ [1] := fun e => by
    have ht := st.top
    injection e with e1
    omega
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
  have w := XMach.solo_claim_start (xs := xsys) rest h₁ h₂ st.adder hne h₄ hR
  rw [← hA] at w
  exact ⟨w.1, rest, _, _, w.2, fun e he => new_head hR he⟩

/-- The run of one thread after its first round and `j` more: the memory
is ready for the next round. -/
theorem solo_steady (m n : Nat) : ∀ j h, j + h = m + n + 3 → n + 3 ≤ h →
    ∃ X, Works xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ X ⟨X.agents, .idle⟩
        (1 + j) (16 + 17 * j) ∧ Steady n X h
  | 0, h, e, _ => by
    have e' : h = m + n + 3 := by omega
    subst e'
    obtain ⟨w, st⟩ := (start_sum m n).round_exact
    exact ⟨_, w.works, st⟩
  | j + 1, h, e, hh => by
    obtain ⟨X, w, st⟩ := solo_steady m n j (h + 1) (by omega) (by omega)
    obtain ⟨w', st'⟩ := st.round_exact (by omega)
    refine ⟨_, ?_, st'⟩
    have w2 := w.trans w'.works
    rw [show 1 + (j + 1) = 1 + j + 1 by omega, show 16 + 17 * (j + 1) = 16 + 17 * j + 17 by omega]
    exact w2

/-- **When a successor of the chain still has only its old segment**: the
top one during the first three actions of the first thread, the one
numbered `t` until the round that takes it is written. -/
theorem solo_seg (m n : Nat) {u t : Nat} (h1 : n + 4 ≤ t) (h2 : t ≤ n + 3 + m + 1)
    (hu : t = n + 3 + m + 1 ∧ u ≤ 3 ∨ u + 17 * t + 1 ≤ 17 * (n + 3 + m + 1)) (q : Port)
    (hq : ((([t], 1), q) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires) :
    q = (below n (t - 1), 0) := by
  rcases hu with ⟨et, hu⟩ | hu
  · have st := start_sum m n
    have h3 := XMach.solo_wires_mono xsys _ _ u (3 - u) _ hq
    rw [show u + (3 - u) = 3 by omega, st.five.1] at h3
    exact (st.chain.seg t h1 (by omega) q).1 h3
  · obtain ⟨j, hj⟩ : ∃ j, j + t = m + n + 3 := ⟨n + 3 + m + 1 - t - 1, by omega⟩
    obtain ⟨X, w, st⟩ := solo_steady m n j t hj (by omega)
    have h3 := XMach.solo_wires_mono xsys _ _ u (16 + 17 * j - u) _ hq
    rw [show u + (16 + 17 * j - u) = 16 + 17 * j by omega, w.solo.1] at h3
    exact (st.chain.seg t h1 (Nat.le_refl t) q).1 h3

/-- **The segments of the run of one thread are segments of the memory it
leaves**, at every moment: through the rounds, the last pass, and at
rest. -/
theorem solo_fin (m n : Nat) : ∃ Xf, Final n (sum (m + 1) n) Xf (n + 3 + m + 1) m ∧
    ∀ u, ∀ e ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires,
      e ∈ Xf.wires := by
  obtain ⟨Xf, r, F⟩ := solo_rounds m n
  have p := (F.pass (snd_sum (m + 1) n) (sum_fresh (m + 1) n)).works
  have eK := (r.works.trans p).solo.1
  refine ⟨Xf, F, fun u e he => ?_⟩
  by_cases hu : u ≤ 17 * m + 25 + (5 * m + 3 * n + 10)
  · have h3 := XMach.solo_wires_mono xsys _ _ u
      (17 * m + 25 + (5 * m + 3 * n + 10) - u) e he
    rw [show u + (17 * m + 25 + (5 * m + 3 * n + 10) - u) =
      17 * m + 25 + (5 * m + 3 * n + 10) by omega, eK] at h3
    exact h3
  · obtain ⟨d, rfl⟩ : ∃ d, u = 17 * m + 25 + (5 * m + 3 * n + 10) + d :=
      ⟨u - (17 * m + 25 + (5 * m + 3 * n + 10)), by omega⟩
    rw [XMach.solo_add, eK] at he
    have he' : e ∈ (XMach.solo xsys Xf ⟨[], .idle⟩ d).1.wires := he
    rw [XMach.solo_rest] at he'
    exact he'

/-- **From the fifth action of the first thread on, the top successor and
the first adder are gone for good.** -/
theorem solo_gone5 (m n : Nat) {u : Nat} (hu : 5 ≤ u) :
    assoc [n + 3 + m + 1]
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = none ∧
      assoc [1]
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = none := by
  have st := start_sum m n
  obtain ⟨-, rest, as, ls, e5, has⟩ := st.five
  have eT : n + 3 + m + 1 = m + n + 3 + 1 := by omega
  have hne : ([m + n + 3 + 1] : Id) ≠ [1] := fun e => by
    injection e with e1
    omega
  have g1 : assoc [m + n + 3 + 1] (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ 5).1.agents = none := by
    rw [e5]
    show assoc [m + n + 3 + 1] (((sum (m + 1) n).agents.filter
      fun e => decide (e.1 ≠ [m + n + 3 + 1])).filter fun e => decide (e.1 ≠ [1])) = none
    rw [assoc_filter_ne, ite_neg' (fun e => hne e.symm), assoc_filter_ne, ite_pos' rfl]
  have g2 : assoc [1] (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ 5).1.agents = none := by
    rw [e5]
    show assoc [1] (((sum (m + 1) n).agents.filter
      fun e => decide (e.1 ≠ [m + n + 3 + 1])).filter fun e => decide (e.1 ≠ [1])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have c1 : (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ 5).2.st.Clear [m + n + 3 + 1] := by
    rw [e5]
    exact fun e he => single_ne_new (by omega) (has e he)
  have c2 : (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ 5).2.st.Clear [1] := by
    rw [e5]
    exact fun e he => single_ne_new (by omega) (has e he)
  have k1 := (XMach.solo_gone (xs := xsys) (x := [m + n + 3 + 1])
    (fun hR he => single_ne_new (by omega) (new_head hR he)) g1 c1 (u - 5)).1
  have k2 := (XMach.solo_gone (xs := xsys) (x := [1])
    (fun hR he => single_ne_new (by omega) (new_head hR he)) g2 c2 (u - 5)).1
  rw [show 5 + (u - 5) = u by omega] at k1 k2
  rw [eT]
  exact ⟨k1, k2⟩

/-- **A successor of the chain is gone for good once its round has taken
it**: the one `d` below the top, from the action `17 * d + 5` of the first
thread on. -/
theorem solo_gone_succ (m n : Nat) {d : Nat} (h1 : 1 ≤ d) (h2 : d ≤ m) {u : Nat}
    (hu : 17 * d + 5 ≤ u) :
    assoc [n + 3 + m + 1 - d]
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = none := by
  obtain ⟨X1, w1, st⟩ := solo_steady m n (d - 1) (m + n + 4 - d) (by omega) (by omega)
  obtain ⟨h, eh⟩ : ∃ h, m + n + 4 - d = h + 1 := ⟨m + n + 3 - d, by omega⟩
  rw [eh] at st
  have hn : n + 4 ≤ h + 1 := by omega
  obtain ⟨rest, hA⟩ := st.head
  have hb : below n (h + 1) = [h + 1] := below_pos hn
  have hne : ([0, h + 1 + 1] : Id) ≠ [h + 1] := fun e => by
    injection e with _ e2
    cases e2
  have h₁ : assoc [0, h + 1 + 1] X1.agents = some .add := by
    rw [hA]
    show (if ([0, h + 1 + 1] : Id) = [0, h + 1 + 1] then some Arith.add
      else assoc _ rest) = _
    rw [ite_pos' rfl]
  have h₂ : assoc (([0, h + 1 + 1], 0) : Port) X1.wires = some ([h + 1 + 1], 1) :=
    assoc_eq_of_unique ((st.first _).2 rfl) (fun q' hq => (st.first q').1 hq)
  have h₂' : nextSeg X1.wires ([h + 1 + 1], 1) ([0, h + 1 + 1], 0) = some ([h + 1], 0) := by
    refine nextSeg_some ((st.mid _).2 (.inr (by rw [hb]))) (fun e => ?_) (fun q hq hqp => ?_)
    · injection e with e1 _
      injection e1 with _ e2
      cases e2
    · rcases (st.mid q).1 hq with e | e
      · exact absurd e hqp
      · rw [e, hb]
  have h₃ : assoc [h + 1] X1.agents = some .succ := st.chain.live (h + 1) hn (Nat.le_refl _)
  have h₄ : assoc [h + 1] (X1.takeAgent [0, h + 1 + 1]).agents = some .succ := by
    show assoc [h + 1] (X1.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])) = _
    rw [assoc_filter_ne, ite_neg' hne]
    exact h₃
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w2 := Works.via_start (xs := xsys) (c := ([h + 1 + 1], 1)) rest h₁ h₂ rfl h₂' h₃ hne h₄
    hR
  rw [← hA] at w2
  have e22 := (w1.trans w2).solo.1
  have g : assoc [h + 1] (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ (16 + 17 * (d - 1) + 6)).1.agents = none := by
    rw [e22]
    show assoc [h + 1] ((X1.agents.filter fun e => decide (e.1 ≠ [0, h + 1 + 1])).filter
      fun e => decide (e.1 ≠ [h + 1])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have c : (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ (16 + 17 * (d - 1) + 6)).2.st.Clear [h + 1] := by
    rw [e22]
    exact fun e he => single_ne_new (by omega) (new_head hR he)
  have k := (XMach.solo_gone (xs := xsys) (x := [h + 1])
    (fun hR he => single_ne_new (by omega) (new_head hR he)) g c (u - (17 * d + 5))).1
  rw [show 16 + 17 * (d - 1) + 6 + (u - (17 * d + 5)) = u by omega] at k
  rw [show n + 3 + m + 1 - d = h + 1 by omega]
  exact k

/-- What the first round needs of the memory at the start: the top
successor is first in the list and faces the adder. -/
theorem Start.pair {n : Nat} {X : XNet Arith} {hi : Nat} (st : Start n X hi) :
    ∃ rest, X.agents = ([hi + 1], .succ) :: rest ∧ assoc [hi + 1] X.agents = some .succ ∧
      assoc (([hi + 1], 0) : Port) X.wires = some ([1], 0) ∧ ([hi + 1] : Id) ≠ [1] ∧
      assoc [1] (X.takeAgent [hi + 1]).agents = some .add := by
  obtain ⟨rest, hA⟩ := st.head
  have hne : ([hi + 1] : Id) ≠ [1] := fun e => by
    have ht := st.top
    injection e with e1
    omega
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
  exact ⟨rest, hA, h₁, h₂, hne, h₄⟩

/-- What a later round needs of the memory before it: the adder is first
in the list, and one point away from the next successor of the chain. -/
theorem Steady.pair {n : Nat} {X : XNet Arith} {h : Nat} (st : Steady n X (h + 1))
    (hn : n + 4 ≤ h + 1) :
    ∃ rest, X.agents = ([0, h + 1 + 1], .add) :: rest ∧
      assoc [0, h + 1 + 1] X.agents = some .add ∧
      assoc (([0, h + 1 + 1], 0) : Port) X.wires = some ([h + 1 + 1], 1) ∧
      nextSeg X.wires ([h + 1 + 1], 1) ([0, h + 1 + 1], 0) = some ([h + 1], 0) ∧
      assoc [h + 1] X.agents = some .succ ∧ ([0, h + 1 + 1] : Id) ≠ [h + 1] ∧
      assoc [h + 1] (X.takeAgent [0, h + 1 + 1]).agents = some .succ := by
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
  exact ⟨rest, hA, h₁, h₂, h₂', h₃, hne, h₄⟩

/-- **What the first thread has not taken is still there.**  On the net for
`(m + 1) + n`, through the first `ρ + 1` rounds of one thread, that is its
first `16 + 17 * ρ` actions, every agent of the start numbered from `2` up
to the successor `ρ + 1` below the top one is in memory with its symbol,
after every action: the rounds have taken the first adder and the `ρ + 1`
top successors, and nothing else. -/
theorem solo_alive (m n : Nat) : ∀ ρ, ρ ≤ m → ∀ (j : Nat) (γ : Arith) (u : Nat), 2 ≤ j →
    j + ρ ≤ n + 3 + m → u ≤ 16 + 17 * ρ →
    assoc [j] (sum (m + 1) n).agents = some γ →
    assoc [j]
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = some γ
  | 0, _, j, γ, u, hj2, hj, hu, hx => by
    have st := start_sum m n
    obtain ⟨rest, hA, h₁, h₂, hne, h₄⟩ := st.pair
    have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
    have k := XMach.solo_direct_keeps (xs := xsys) rest h₁ h₂ st.adder hne h₄ hR
      (x := [j]) (γ := γ) hx (by ports_differ) (by ports_differ)
      (fun e he => single_ne_new (by omega) (new_head hR he)) u (by
        rw [newAgents_swap (a := [1]) (s := [m + n + 3 + 1]) (fun e => hne e.symm)]
        show u ≤ 5 + (2 + 8 + 1)
        omega)
    rw [← hA] at k
    exact k
  | ρ + 1, hρ, j, γ, u, hj2, hj, hu, hx => by
    by_cases hu' : u ≤ 16 + 17 * ρ
    · exact solo_alive m n ρ (by omega) j γ u hj2 (by omega) hu' hx
    · obtain ⟨X1, w1, st⟩ := solo_steady m n ρ (m + n + 3 - ρ) (by omega) (by omega)
      have ih := solo_alive m n ρ (by omega) j γ (16 + 17 * ρ) hj2 (by omega)
        (Nat.le_refl _) hx
      rw [w1.solo.1] at ih
      obtain ⟨h, eh⟩ : ∃ h, m + n + 3 - ρ = h + 1 := ⟨m + n + 2 - ρ, by omega⟩
      rw [eh] at st
      obtain ⟨rest, hA, h₁, h₂, h₂', h₃, hne, h₄⟩ := st.pair (by omega)
      have hR : xsys.rule .add .succ = some addSucc.toX := rfl
      obtain ⟨u', rfl⟩ : ∃ u', u = 16 + 17 * ρ + u' := ⟨u - (16 + 17 * ρ), by omega⟩
      have k := XMach.solo_via_keeps (xs := xsys) (c := ([h + 1 + 1], 1)) rest h₁ h₂ rfl h₂'
        h₃ hne h₄ hR (x := [j]) (γ := γ) ih (by ports_differ) (by ports_differ)
        (fun e he => single_ne_new (by omega) (new_head hR he)) u' (by
          rw [newAgents_add hne]
          show u' ≤ 6 + (2 + 8 + 1)
          omega)
      rw [← hA] at k
      rw [XMach.solo_add, w1.solo.1]
      exact k

/-- In particular the second argument and the zero of the first are there
through all the rounds on the successors of the first argument. -/
theorem solo_alive_snd (m n : Nat) {j : Nat} {γ : Arith} {u : Nat} (hj2 : 2 ≤ j)
    (hj : j ≤ n + 3) (hu : u ≤ 16 + 17 * m)
    (hx : assoc [j] (sum (m + 1) n).agents = some γ) :
    assoc [j]
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = some γ :=
  solo_alive m n m (Nat.le_refl m) j γ u hj2 (by omega) hu hx

theorem sum_zero_agent (m n : Nat) : assoc [2] (sum (m + 1) n).agents = some .zero :=
  assoc_of_nodup (sum_nodup (m + 1) n) (e := ([2], Arith.zero)) (by
    rw [sum_agents]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- What the last round needs of the memory before it: the adder is first
in the list, and one point away from the zero of the first argument. -/
theorem Steady.zero_pair {n : Nat} {X : XNet Arith} (st : Steady n X (n + 3))
    (hz : assoc [2] X.agents = some .zero) :
    ∃ rest, X.agents = ([0, n + 3 + 1], .add) :: rest ∧
      assoc [0, n + 3 + 1] X.agents = some .add ∧
      assoc (([0, n + 3 + 1], 0) : Port) X.wires = some ([n + 3 + 1], 1) ∧
      nextSeg X.wires ([n + 3 + 1], 1) ([0, n + 3 + 1], 0) = some ([2], 0) ∧
      ([0, n + 3 + 1] : Id) ≠ [2] ∧
      assoc [2] (X.takeAgent [0, n + 3 + 1]).agents = some .zero := by
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
  exact ⟨rest, hA, h₁, h₂, h₂', hne, h₄⟩

/-- **The second argument and the zero of the first are there until the
last round takes the zero**: through the rounds on the successors and the
first five actions of the last round. -/
theorem solo_alive_zero (m n : Nat) {j : Nat} {γ : Arith} {u : Nat} (hj2 : 2 ≤ j)
    (hj : j ≤ n + 3) (hu : u ≤ 17 * m + 21)
    (hx : assoc [j] (sum (m + 1) n).agents = some γ) :
    assoc [j]
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents =
        some γ := by
  by_cases hu' : u ≤ 16 + 17 * m
  · exact solo_alive_snd m n hj2 hj hu' hx
  · obtain ⟨X1, w1, st⟩ := solo_steady m n m (n + 3) (by omega) (Nat.le_refl _)
    have ih := solo_alive_snd m n hj2 hj (Nat.le_refl (16 + 17 * m)) hx
    have hz := solo_alive_snd m n (j := 2) (by omega) (by omega) (Nat.le_refl (16 + 17 * m))
      (sum_zero_agent m n)
    rw [w1.solo.1] at ih hz
    obtain ⟨rest, hA, h₁, h₂, h₂', hne, -⟩ := st.zero_pair hz
    have hR : xsys.rule .add .zero = some addZero.toX := rfl
    obtain ⟨u', rfl⟩ : ∃ u', u = 16 + 17 * m + u' := ⟨u - (16 + 17 * m), by omega⟩
    have k := XMach.solo_via_reads (xs := xsys) (c := ([n + 3 + 1], 1)) rest h₁ h₂ rfl h₂' hz
      hne hR u' (by omega)
    rw [← hA] at k
    rw [XMach.solo_add, w1.solo.1]
    show assoc [j] (XMach.solo xsys X1 ⟨X1.agents, .idle⟩ u').1.agents = some γ
    rcases k with e | e
    · rw [e]
      exact ih
    · rw [e]
      show assoc [j] (X1.agents.filter fun e => decide (e.1 ≠ [0, n + 3 + 1])) = some γ
      rw [assoc_filter_ne, ite_neg' (by ports_differ)]
      exact ih

/-- **The zero of the first argument is gone for good once the last round
has taken it**, from the action `17 * m + 22` of the first thread on. -/
theorem solo_gone_zero (m n : Nat) {u : Nat} (hu : 17 * m + 22 ≤ u) :
    assoc [2]
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = none := by
  obtain ⟨X1, w1, st⟩ := solo_steady m n m (n + 3) (by omega) (Nat.le_refl _)
  have hz := solo_alive_snd m n (j := 2) (by omega) (by omega) (Nat.le_refl (16 + 17 * m))
    (sum_zero_agent m n)
  rw [w1.solo.1] at hz
  obtain ⟨rest, hA, h₁, h₂, h₂', hne, h₄⟩ := st.zero_pair hz
  have hR : xsys.rule .add .zero = some addZero.toX := rfl
  have w2 := Works.via_start (xs := xsys) (c := ([n + 3 + 1], 1)) rest h₁ h₂ rfl h₂' hz hne h₄
    hR
  rw [← hA] at w2
  have e22 := (w1.trans w2).solo.1
  have g : assoc [2] (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ (16 + 17 * m + 6)).1.agents = none := by
    rw [e22]
    show assoc [2] ((X1.agents.filter fun e => decide (e.1 ≠ [0, n + 3 + 1])).filter
      fun e => decide (e.1 ≠ [2])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have c : (XMach.solo xsys (sum (m + 1) n)
      ⟨(sum (m + 1) n).agents, .idle⟩ (16 + 17 * m + 6)).2.st.Clear [2] := by
    rw [e22]
    exact fun e he => single_ne_new (by omega) (new_head hR he)
  have k := (XMach.solo_gone (xs := xsys) (x := [2])
    (fun hR he => single_ne_new (by omega) (new_head hR he)) g c (u - (17 * m + 22))).1
  rw [show 16 + 17 * m + 6 + (u - (17 * m + 22)) = u by omega] at k
  exact k

/-- The run of one thread after its first round and `j` more, with the
exact segments of the memory: those of the start and those the rounds
wrote. -/
theorem solo_hist (m n : Nat) : ∀ j r, j + r = m →
    ∃ X, Works xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ X ⟨X.agents, .idle⟩
        (1 + j) (16 + 17 * j) ∧ Steady n X (n + 3 + r) ∧
      Hist n (sum (m + 1) n) X (n + 3 + m + 1) r j
  | 0, r, e => by
    have e' : r = m := by omega
    subst e'
    have st0 : Start n (sum (r + 1) n) (n + 3 + r) := by
      have h := start_sum r n
      have e2 : r + n + 3 = n + 3 + r := by omega
      rw [e2] at h
      exact h
    obtain ⟨w, st1⟩ := st0.round_exact
    exact ⟨_, w.works, st1, hist_start (sum_agents (r + 1) n)⟩
  | j + 1, r, e => by
    obtain ⟨X, w, st, H⟩ := solo_hist m n j (r + 1) (by omega)
    have st' : Steady n X (n + 3 + r + 1) := st
    obtain ⟨w', st1⟩ := Steady.round_exact st' (by omega)
    refine ⟨_, ?_, st1, H.step⟩
    have w2 := w.trans w'.works
    rw [show 1 + (j + 1) = 1 + j + 1 by omega,
      show 16 + 17 * (j + 1) = 16 + 17 * j + 17 by omega]
    exact w2

/-- **The segment from the first adder to the one the first round makes**
is in memory from the end of that round on. -/
theorem solo_link_top (m n : Nat) {u : Nat} (hu : 16 ≤ u) :
    ((([1], 1), ([0, n + 3 + m + 1], 1)) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires := by
  obtain ⟨X, w, -, H⟩ := solo_hist m n 0 m (by omega)
  have h0 : ((([1], 1), ([0, n + 3 + m + 1], 1)) : Port × Port) ∈ X.wires :=
    (H.wires _).2 (.inr (.inl ((mem_linksS _ _ _).2 (.inr (.inl ⟨rfl, rfl⟩)))))
  have hw := XMach.solo_wires_mono xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
    (16 + 17 * 0) (u - 16) ((([1], 1), ([0, n + 3 + m + 1], 1)) : Port × Port) (by
      rw [w.solo.1]
      exact h0)
  rw [show 16 + 17 * 0 + (u - 16) = u by omega] at hw
  exact hw

/-- **The segment from an adder to the next** is in memory from the end of
the round that makes the next: the adder `[0, t]` is made by the round on
the successor `[t]`, which ends at the action `16 + 17 * d` when `[t]` is
`d` below the top. -/
theorem solo_link (m n : Nat) {t u : Nat} (h1 : n + 4 ≤ t) (h2 : t < n + 3 + m + 1)
    (hu : 16 + 17 * (n + 3 + m + 1 - t) ≤ u) :
    ((([0, t + 1], 1), ([0, t], 1)) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires := by
  obtain ⟨r, rfl⟩ : ∃ r, t = n + 3 + r + 1 := ⟨t - (n + 4), by omega⟩
  obtain ⟨X, w, -, H⟩ := solo_hist m n (m - r) r (by omega)
  have h0 : ((([0, n + 3 + r + 1 + 1], 1), ([0, n + 3 + r + 1], 1)) : Port × Port) ∈ X.wires :=
    (H.wires _).2 (.inr (.inr ⟨n + 3 + r + 1, by omega, by omega,
      (mem_linksA _ _ _).2 (.inl ⟨rfl, rfl⟩)⟩))
  have hw := XMach.solo_wires_mono xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
    (16 + 17 * (m - r)) (u - (16 + 17 * (m - r)))
    ((([0, n + 3 + r + 1 + 1], 1), ([0, n + 3 + r + 1], 1)) : Port × Port) (by
      rw [w.solo.1]
      exact h0)
  rw [show 16 + 17 * (m - r) + (u - (16 + 17 * (m - r))) = u by omega] at hw
  exact hw

/-- **And it is not there before that round starts**: when it is in
memory, the first thread has made `17 * d` actions at least. -/
theorem solo_no_link (m n : Nat) {t u : Nat} (h1 : n + 4 ≤ t) (h2 : t < n + 3 + m + 1)
    (hq : ((([0, t + 1], 1), ([0, t], 1)) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires) :
    17 * (n + 3 + m + 1 - t) ≤ u := by
  obtain ⟨r, rfl⟩ : ∃ r, t = n + 3 + r := ⟨t - (n + 3), by omega⟩
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨X, w, -, H⟩ := solo_hist m n (m - r) r (by omega)
  have h3 := XMach.solo_wires_mono xsys _ _ u (16 + 17 * (m - r) - u) _ hq
  rw [show u + (16 + 17 * (m - r) - u) = 16 + 17 * (m - r) by omega, w.solo.1] at h3
  rcases (H.wires _).1 h3 with h | h | ⟨t', t1, t2, h⟩
  · obtain ⟨j, ej⟩ := sum_fresh (m + 1) n _ _ _ h
    injection ej with _ e2
    cases e2
  · rcases (mem_linksS _ _ _).1 h with h | h | h | h | h | h | h | h <;>
      first | (simp at h; done) | (simp at h; omega)
  · rcases (mem_linksA _ _ _).1 h with h | h | h | h | h | h | h | h <;>
      first | (simp at h; done) | (simp at h; omega)

/-- What a later round needs of the memory before it: the adder is first
in the list, one point away from the successor it meets. -/
theorem Steady.round_pair {n : Nat} {X : XNet Arith} {h : Nat} (st : Steady n X (h + 1))
    (hn : n + 4 ≤ h + 1) :
    ∃ rest, X.agents = ([0, h + 1 + 1], .add) :: rest ∧
      assoc [0, h + 1 + 1] X.agents = some .add ∧
      assoc (([0, h + 1 + 1], 0) : Port) X.wires = some ([h + 1 + 1], 1) ∧
      nextSeg X.wires ([h + 1 + 1], 1) ([0, h + 1 + 1], 0) = some ([h + 1], 0) ∧
      assoc [h + 1] X.agents = some .succ ∧ ([0, h + 1 + 1] : Id) ≠ [h + 1] ∧
      assoc [h + 1] (X.takeAgent [0, h + 1 + 1]).agents = some .succ := by
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
  exact ⟨rest, hA, h₁, h₂, h₂', h₃, hne, h₄⟩

/-- **The segment from the lowest successor of the chain to the last
adder** is the third that the round on that successor writes: when it is
in memory, the first thread has made `17 * m + 10` actions at least. -/
theorem solo_no_link3 (m n : Nat) (hm : 1 ≤ m) {u : Nat}
    (hq : ((([n + 3 + 1], 1), ([0, n + 3 + 1], 0)) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires) :
    17 * m + 10 ≤ u := by
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨X, w, st, -⟩ := solo_hist m n (m - 1) 1 (by omega)
  obtain ⟨rest, hA, h₁, h₂, h₂', h₃, hne, h₄⟩ := st.round_pair (h := n + 3) (by omega)
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w1 := Works.via_start (xs := xsys) (c := ([n + 3 + 1 + 1], 1)) rest h₁ h₂ rfl h₂' h₃
    hne h₄ hR
  rw [← hA, newAgents_add hne,
    show addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + 1 + 1] [n + 3 + 1] .add .succ = _ from
      newLinks_add _ _] at w1
  have w2 := (((w1.trans (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)).trans (Works.write_link (xs := xsys) _ _ _ _ _)
  have e := (w.trans w2).solo_at (17 * m + 9) (by omega)
  have h3 := XMach.solo_wires_mono xsys _ _ u (17 * m + 9 - u) _ hq
  rw [show u + (17 * m + 9 - u) = 17 * m + 9 by omega, e] at h3
  have hb2 : below n (n + 3 + 1 - 1) = [2] := by
    rcases below_cases n (n + 3 + 1 - 1) with ⟨-, h⟩ | ⟨hb, -⟩
    · omega
    · exact hb
  rcases List.mem_cons.1 h3 with h | h
  · simp at h
  · rcases List.mem_cons.1 h with h | h
    · simp at h
    · have hs := (st.chain.seg (n + 3 + 1) (by omega) (Nat.le_refl _) _).1 h
      rw [hb2] at hs
      simp at hs

/-- The pass over the successors of the result, as a run that only
reads. -/
theorem Final.pass_res_stays {n : Nat} {X0 X : XNet Arith} {T d : Nat}
    (F : Final n X0 X T d) (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    (rest : List (Id × Arith)) : ∀ (d' h : Nat), n + 3 ≤ h → h + d' + 1 = T →
      (∀ e ∈ resL h d', e ∈ X.agents) →
      Stays xsys X ⟨resL h d' ++ rest, .idle⟩ ⟨rest, .idle⟩ (4 * (d' + 1))
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
    exact Stays.dead (xs := xsys) (e := ([0, 1], Arith.succ)) (k := 2) rest h₁ h₂ hd
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
    have w₁ : Stays xsys X ⟨([0, 0, h + 2], Arith.succ) :: (resL (h + 1) d' ++ rest), .idle⟩
        ⟨resL (h + 1) d' ++ rest, .idle⟩ (2 + 2) :=
      Stays.dead (xs := xsys) (e := ([0, 0, h + 2], Arith.succ)) (k := 2) _ h₁ h₂ hd
    have w₂ := Final.pass_res_stays F S hfr rest d' (h + 1) (by omega) (by omega)
      (fun e he => hm e (List.mem_cons_of_mem _ he))
    have w := w₁.trans w₂
    have e1 : 2 + 2 + 4 * (d' + 1) = 4 * (d' + 1 + 1) := by omega
    rw [e1] at w
    exact w

/-- **The last pass only reads**: `5 * d + 3 * n + 10` actions, none of
which changes the memory. -/
theorem Final.pass_stays {n : Nat} {X0 X : XNet Arith} {T d : Nat}
    (F : Final n X0 X T d) (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j]) :
    Stays xsys X ⟨X.agents, .idle⟩ ⟨[], .idle⟩ (5 * d + 3 * n + 10) := by
  have hT := F.top
  obtain ⟨γ, low, hsplit, hlen, hlow⟩ := snd_split n
  have hA : X.agents = resL (n + 3) d ++ (([n + 3], γ) :: low) := by
    rw [F.agents, hsplit]
  have hmem : ∀ e ∈ ([n + 3], γ) :: low, e ∈ X.agents := fun e he => by
    rw [hA]
    exact List.mem_append_right _ he
  have w₁ := F.pass_res_stays S hfr (([n + 3], γ) :: low) d (n + 3) (Nat.le_refl _) (by omega)
    (fun e he => by
      rw [hA]
      exact List.mem_append_left _ he)
  have h₁ : assoc [n + 3] X.agents = some γ := F.agent (hmem _ List.mem_cons_self)
  have h₂ : assoc (([n + 3], 0) : Port) X.wires = some ([1], 1) :=
    assoc_eq_of_unique ((F.top_snd S _).2 rfl) (fun q' hq => (F.top_snd S q').1 hq)
  have w₂ : Stays xsys X ⟨([n + 3], γ) :: low, .idle⟩ ⟨low, .idle⟩ (d + 3 + 1 + 2) :=
    Stays.dead (xs := xsys) (e := ([n + 3], γ)) _ h₁ h₂ (F.dead_top S hfr)
  have w₃ := Stays.inert_pass (xs := xsys) (X := X) [] low (fun e he => by
    obtain ⟨j, h1, h2, h3⟩ := hlow e he
    exact F.inert S (hmem e (List.mem_cons_of_mem _ he)) h1 h2 h3)
  rw [List.append_nil, hlen] at w₃
  have w := (w₁.trans w₂).trans w₃
  have e : 4 * (d + 1) + (d + 3 + 1 + 2) + 3 * n = 5 * d + 3 * n + 10 := by omega
  rw [e] at w
  rw [hA]
  exact w

/-- **After its last round the first thread leaves the memory as it is**:
from its action `17 * m + 25` on, through the last pass and at rest, the
memory is the one the rounds leave. -/
theorem solo_final_mem (m n : Nat) : ∃ Xf, Final n (sum (m + 1) n) Xf (n + 3 + m + 1) m ∧
    ∀ u, 17 * m + 25 ≤ u →
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1 = Xf := by
  obtain ⟨Xf, r, F⟩ := solo_rounds m n
  have p := F.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
  have e25 := r.works.solo_at (17 * m + 25) rfl
  refine ⟨Xf, F, fun u hu => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, u = 17 * m + 25 + d := ⟨u - (17 * m + 25), by omega⟩
  rw [XMach.solo_add, e25]
  show (XMach.solo xsys Xf ⟨Xf.agents, .idle⟩ d).1 = Xf
  by_cases hd : d ≤ 5 * m + 3 * n + 10
  · exact p.solo_mem d hd
  · obtain ⟨d', rfl⟩ : ∃ d', d = 5 * m + 3 * n + 10 + d' :=
      ⟨d - (5 * m + 3 * n + 10), by omega⟩
    rw [XMach.solo_add, p.works.solo.1]
    show (XMach.solo xsys Xf ⟨[], .idle⟩ d').1 = Xf
    rw [XMach.solo_rest]

/-- The last adder is not in the memory the rounds leave. -/
theorem Final.no_adder {n : Nat} {X0 X : XNet Arith} {T d : Nat} (F : Final n X0 X T d)
    (t : Nat) (ht : t ≠ 1) : assoc [0, t] X.agents = none := by
  rw [F.agents]
  refine assoc_none_of_forall fun e he e' => ?_
  rcases List.mem_append.1 he with h | h
  · exact res_ne_adder h t ht e'
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨-, j, -, -, h3⟩ := mem_sndL h
      rw [h3] at e'
      injection e' with _ e2
      cases e2
    · rcases List.mem_cons.1 h with rfl | h
      · injection e' with _ e2
        cases e2
      · cases h

/-- **The last adder is gone for good once the last round has taken it**,
from the action `17 * m + 21` of the first thread on. -/
theorem solo_gone_adder (m n : Nat) {u : Nat} (hu : 17 * m + 21 ≤ u) :
    assoc [0, n + 3 + 1]
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = none := by
  by_cases h25 : 17 * m + 25 ≤ u
  · obtain ⟨Xf, F, hf⟩ := solo_final_mem m n
    rw [hf u h25]
    exact F.no_adder (n + 3 + 1) (by omega)
  · obtain ⟨X1, w1, st⟩ := solo_steady m n m (n + 3) (by omega) (Nat.le_refl _)
    have hz := solo_alive_snd m n (j := 2) (by omega) (by omega) (Nat.le_refl (16 + 17 * m))
      (sum_zero_agent m n)
    rw [w1.solo.1] at hz
    obtain ⟨rest, hA, h₁, h₂, h₂', hne, h₄⟩ := st.zero_pair hz
    have hR : xsys.rule .add .zero = some addZero.toX := rfl
    have g5 : assoc [0, n + 3 + 1] (X1.takeAgent [0, n + 3 + 1]).agents = none := by
      show assoc [0, n + 3 + 1] (X1.agents.filter fun e => decide (e.1 ≠ [0, n + 3 + 1])) =
        none
      rw [assoc_filter_ne, ite_pos' rfl]
    have g6 : assoc [0, n + 3 + 1]
        ((X1.takeAgent [0, n + 3 + 1]).takeAgent [2]).agents = none := by
      show assoc [0, n + 3 + 1] ((X1.agents.filter fun e => decide (e.1 ≠ [0, n + 3 + 1])).filter
        fun e => decide (e.1 ≠ [2])) = none
      rw [assoc_filter_ne, ite_neg' (fun e => hne e.symm), assoc_filter_ne, ite_pos' rfl]
    have w5 := Works.via_half (xs := xsys) (c := ([n + 3 + 1], 1)) rest h₁ h₂ rfl h₂' hz hne hR
    have w6 := Works.via_start (xs := xsys) (c := ([n + 3 + 1], 1)) rest h₁ h₂ rfl h₂' hz hne h₄
      hR
    rw [← hA] at w5 w6
    rw [show addZero.toX.newAgents [0, n + 3 + 1] [2] = [] from rfl,
      show addZero.toX.newLinks xsys.sys.ar [0, n + 3 + 1] [2] .add .zero = _ from
        newLinks_zero _ _] at w6
    have w7 := w6.trans (Works.write_link (xs := xsys) _ _ _ _ _)
    have w8 := w7.trans (Works.write_link (xs := xsys) _ _ _ _ _)
    have c : u = 17 * m + 21 ∨ u = 17 * m + 22 ∨ u = 17 * m + 23 ∨ u = 17 * m + 24 := by omega
    rcases c with rfl | rfl | rfl | rfl
    · rw [(w1.trans w5).solo_at (17 * m + 21) (by omega)]
      exact g5
    · rw [(w1.trans w6).solo_at (17 * m + 22) (by omega)]
      exact g6
    · rw [(w1.trans w7).solo_at (17 * m + 23) (by omega)]
      exact g6
    · rw [(w1.trans w8).solo_at (17 * m + 24) (by omega)]
      exact g6

/-- The segments at the second port of the lowest successor of the chain,
in the memory the rounds leave: to the zero of the first argument, as at
the start, and to the last adder. -/
theorem Final.low_one {m n : Nat} {X : XNet Arith}
    (F : Final n (sum (m + 1) n) X (n + 3 + m + 1) m) (q : Port)
    (h : ((([n + 3 + 1], 1), q) : Port × Port) ∈ X.wires) :
    q = ([2], 0) ∨ q = ([0, n + 3 + 1], 0) := by
  have hb2 : below n (n + 3 + 1 - 1) = [2] := by
    rcases below_cases n (n + 3 + 1 - 1) with ⟨-, h⟩ | ⟨hb, -⟩
    · omega
    · exact hb
  rcases (F.single (n + 3 + 1) 1 q).1 h with h | ⟨h1, -, e⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩ |
    ⟨-, -, -, e⟩
  · have hs := ((start_sum m n).chain.seg (n + 3 + 1) (by omega) (by omega) q).1 h
    rw [hb2] at hs
    exact .inl hs
  · have e' : q = ([0, n + 3 + 1], 0) := by rw [e, ← h1]
    exact .inr e'
  · omega
  · omega
  · exact .inr e

/-- The first port of the last adder has one segment, to the successor
that its round took. -/
theorem Final.adder_zero {m n : Nat} {X : XNet Arith}
    (F : Final n (sum (m + 1) n) X (n + 3 + m + 1) m) (hm : 1 ≤ m) (q : Port)
    (h : ((([0, n + 3 + 1], 0), q) : Port × Port) ∈ X.wires) : q = ([n + 3 + 1], 1) := by
  rcases (F.fresh (sum_fresh (m + 1) n) (i := [0, n + 3 + 1])
    (fun j e => by injection e with _ e2; cases e2) 0 q).1 h with h | ⟨t, t1, t2, h⟩ | h
  · rcases (mem_linksS _ _ _).1 h with h | h | h | h | h | h | h | h <;>
      first | (simp at h; done) | (simp at h; omega)
  · rcases (mem_linksA _ _ _).1 h with h | h | h | h | h | h | h | h <;>
      first | (simp at h; done) | (simp at h; omega) |
        (obtain ⟨e1, e2⟩ := h; simp at e1; rw [e2, ← e1])
  · rcases (mem_linksZ _ _ _).1 h with h | h <;> simp at h

/-- **The last adder is in memory from the moment it is written until the
last round takes it**: for the actions `17 * m + 7` to `17 * m + 20` of the
first thread. -/
theorem solo_adder_alive (m n : Nat) (hm : 1 ≤ m) {u : Nat} (h1 : 17 * m + 7 ≤ u)
    (h2 : u ≤ 17 * m + 20) :
    assoc [0, n + 3 + 1]
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents =
        some .add := by
  by_cases h16 : u ≤ 17 * m + 15
  · obtain ⟨X, w, st, -⟩ := solo_hist m n (m - 1) 1 (by omega)
    obtain ⟨rest, hA, k₁, k₂, k₂', k₃, hne, k₄⟩ := st.round_pair (h := n + 3) (by omega)
    have hR : xsys.rule .add .succ = some addSucc.toX := rfl
    have w1 := Works.via_start (xs := xsys) (c := ([n + 3 + 1 + 1], 1)) rest k₁ k₂ rfl k₂' k₃
      hne k₄ hR
    rw [← hA, newAgents_add hne] at w1
    have w2 := (w1.trans (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
      (Works.write_agent (xs := xsys) _ _ _ _ _ _)
    obtain ⟨j, rfl⟩ : ∃ j, u = 17 * m + 7 + j := ⟨u - (17 * m + 7), by omega⟩
    have hlen : (addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + 1 + 1] [n + 3 + 1]
        .add .succ).length = 8 := rfl
    have hl : ((addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + 1 + 1] [n + 3 + 1]
        .add .succ).take j).length = j := by
      rw [List.length_take, hlen]
      exact Nat.min_eq_left (by omega)
    have w3 := Works.write_links (xs := xsys) rest
      ((addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + 1 + 1] [n + 3 + 1] .add .succ).take j)
      ((addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + 1 + 1] [n + 3 + 1] .add .succ).drop j)
      ((((X.takeAgent [0, n + 3 + 1 + 1]).takeAgent [n + 3 + 1]).putAgent
        [0, 0, n + 3 + 1 + 1] .succ).putAgent [0, n + 3 + 1] .add)
    rw [List.take_append_drop, hl] at w3
    rw [((w.trans w2).trans w3).solo_at (17 * m + 7 + j) (by omega)]
    show assoc [0, n + 3 + 1] (XNet.putLinks _ _).agents = some Arith.add
    rw [XNet.putLinks_agents]
    show (if ([0, n + 3 + 1] : Id) = [0, n + 3 + 1] then some Arith.add else _) = _
    rw [ite_pos' rfl]
  · obtain ⟨X1, w1, st⟩ := solo_steady m n m (n + 3) (by omega) (Nat.le_refl _)
    have hz := solo_alive_snd m n (j := 2) (by omega) (by omega) (Nat.le_refl (16 + 17 * m))
      (sum_zero_agent m n)
    rw [w1.solo.1] at hz
    obtain ⟨rest, hA, h₁, h₂, h₂', hne, -⟩ := st.zero_pair hz
    have hR : xsys.rule .add .zero = some addZero.toX := rfl
    have sv := Stays.via_reads (xs := xsys) (c := ([n + 3 + 1], 1)) rest h₁ h₂ rfl h₂' hz hne hR
    rw [← hA] at sv
    obtain ⟨j, rfl⟩ : ∃ j, u = 16 + 17 * m + j := ⟨u - (16 + 17 * m), by omega⟩
    rw [XMach.solo_add, w1.solo.1]
    show assoc [0, n + 3 + 1] (XMach.solo xsys X1 ⟨X1.agents, .idle⟩ j).1.agents = some .add
    rw [sv.solo_mem j (by omega)]
    exact h₁

/-- What every thread has in its list after the chain of the first
argument: the second argument, the first adder, and the two zeros. -/
def sndBase (n : Nat) : List (Id × Arith) :=
  sndL n ++ [([1], .add), ([2], .zero), ([3], .zero)]

theorem mem_sndBase {n : Nat} {e : Id × Arith} (h : e ∈ sndBase n) :
    ∃ j, 1 ≤ j ∧ j ≤ n + 3 ∧ e.1 = [j] := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨-, j, h1, h2, h3⟩ := mem_sndL h
    exact ⟨j, by omega, h2, h3⟩
  · rcases List.mem_cons.1 h with e1 | h
    · exact ⟨1, by omega, by omega, by rw [e1]⟩
    · rcases List.mem_cons.1 h with e1 | h
      · exact ⟨2, by omega, by omega, by rw [e1]⟩
      · rcases List.mem_cons.1 h with e1 | h
        · exact ⟨3, by omega, by omega, by rw [e1]⟩
        · cases h

/-- The actions an agent of a list can cost a thread that reads: the top
of the second argument starts a walk along the adders; the zero of the
first argument costs four at most, when the thread finds it but not the
last adder; the first adder, which is gone, two; any other agent three. -/
def passCost (m n : Nat) (e : Id × Arith) : Nat :=
  if e.1 = [n + 3] then m + 6 else if e.1 = [2] then 4 else if e.1 = [1] then 2 else 3

def passSum (m n : Nat) : List (Id × Arith) → Nat
  | [] => 0
  | e :: l => passCost m n e + passSum m n l

theorem passCost_ne {m n : Nat} {e : Id × Arith} (h : e.1 ≠ [n + 3]) (h2 : e.1 ≠ [2])
    (h1 : e.1 ≠ [1]) : passCost m n e = 3 :=
  (ite_neg' h).trans ((ite_neg' h2).trans (ite_neg' h1))

theorem passCost_top (m n : Nat) (α : Arith) : passCost m n ([n + 3], α) = m + 6 :=
  ite_pos' rfl

theorem passCost_two (m n : Nat) (α : Arith) : passCost m n ([2], α) = 4 :=
  (ite_neg' (by ports_differ)).trans (ite_pos' rfl)

theorem passCost_one (m n : Nat) (α : Arith) : passCost m n ([1], α) = 2 :=
  (ite_neg' (by ports_differ)).trans ((ite_neg' (by ports_differ)).trans (ite_pos' rfl))

theorem passCost_ge (m n : Nat) (e : Id × Arith) : 1 ≤ passCost m n e := by
  unfold passCost
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem passSum_three {m n : Nat} : ∀ {l : List (Id × Arith)},
    (∀ e ∈ l, e.1 ≠ [n + 3] ∧ e.1 ≠ [2] ∧ e.1 ≠ [1]) → passSum m n l = 3 * l.length
  | [], _ => rfl
  | e :: l, h => by
    show passCost m n e + passSum m n l = 3 * (l.length + 1)
    obtain ⟨k1, k2, k3⟩ := h e List.mem_cons_self
    rw [passCost_ne k1 k2 k3,
      passSum_three fun x hx => h x (List.mem_cons_of_mem _ hx)]
    omega

theorem passSum_append (m n : Nat) : ∀ l₁ l₂ : List (Id × Arith),
    passSum m n (l₁ ++ l₂) = passSum m n l₁ + passSum m n l₂
  | [], l₂ => (Nat.zero_add _).symm
  | e :: l₁, l₂ => by
    show passCost m n e + passSum m n (l₁ ++ l₂) =
      passCost m n e + passSum m n l₁ + passSum m n l₂
    rw [passSum_append m n l₁ l₂]
    omega

theorem passSum_sndBase (m n : Nat) : passSum m n (sndBase n) = m + 3 * n + 12 := by
  cases n with
  | zero =>
    show passCost m 0 ([1], .add) + (passCost m 0 ([2], .zero) +
      (passCost m 0 ([3], .zero) + 0)) = _
    rw [passCost_one, passCost_two, passCost_top m 0]
    omega
  | succ k =>
    have e1 : passCost m (k + 1) ([k + 4], Arith.succ) = m + 6 := passCost_top m (k + 1) .succ
    have e2 : passSum m (k + 1) (sndL k) = 3 * k := by
      rw [passSum_three, sndL_length]
      intro e he
      obtain ⟨-, j, h1, h2, h3⟩ := mem_sndL he
      rw [h3]
      exact ⟨by ports_differ, by ports_differ, by ports_differ⟩
    have e3 : passSum m (k + 1) [([1], .add), ([2], .zero), ([3], .zero)] = 9 := by
      show passCost m (k + 1) ([1], .add) + (passCost m (k + 1) ([2], .zero) +
        (passCost m (k + 1) ([3], .zero) + 0)) = 9
      rw [passCost_one, passCost_two,
        passCost_ne (by ports_differ) (by ports_differ) (by ports_differ)]
    show passCost m (k + 1) ([k + 4], Arith.succ) + passSum m (k + 1) (sndL k ++
      [([1], .add), ([2], .zero), ([3], .zero)]) = _
    rw [e1, passSum_append, e2, e3]
    omega

/-- The agents after the chain have their symbols at the start. -/
theorem sum_assoc_base (m n : Nat) {e : Id × Arith} (he : e ∈ sndBase n) :
    assoc e.1 (sum (m + 1) n).agents = some e.2 :=
  assoc_of_nodup (sum_nodup (m + 1) n) (by
    rw [sum_agents]
    exact List.mem_append_right _ he)

/-- **A list that a thread can read after its chain, when it comes to it
after `lo` actions at least and `hi` at most.**  An agent of the second
argument below its top, or the zero of the first, costs three actions
while it is in memory.  When the thread finds the zero of the first
argument in memory, it is early enough to pass it before the segment to
the last adder is written, or late enough to find the last adder gone, or
else `Z` holds: the thread may get ready to take the two.  The top of the second argument starts a
walk along the adders that the first thread has made, `Hlo` hops at least and `Hhi`
at most.  The first adder must be gone, which it is after four actions; a
successor `d` below the top one must be gone, which it is after
`17 * d + 4`; each costs one action. -/
inductive TailOk (Z : Prop) (m n : Nat) : Nat → Nat → List (Id × Arith) → Prop
  | nil {lo hi : Nat} : TailOk Z m n lo hi []
  | snd {lo hi : Nat} {l : List (Id × Arith)} (j : Nat) (α : Arith) (h1 : 2 ≤ j)
      (h2 : j ≤ n + 2) (hz : j = 2 → Z ∨ hi ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ lo)
      (ha : assoc [j] (sum (m + 1) n).agents = some α)
      (hl : TailOk Z m n (lo + 3) (hi + 3) l) : TailOk Z m n lo hi (([j], α) :: l)
  | top {lo hi : Nat} {l : List (Id × Arith)} (α : Arith) (Hlo Hhi : Nat)
      (h1 : 16 * Hlo ≤ lo + 3) (h2 : hi + 4 ≤ 16 * Hhi) (h3 : Hlo ≤ m) (h4 : Hhi ≤ m)
      (ha : assoc [n + 3] (sum (m + 1) n).agents = some α)
      (hl : TailOk Z m n (lo + 3 + Hlo) (hi + 3 + Hhi) l) :
      TailOk Z m n lo hi (([n + 3], α) :: l)
  | gone {lo hi : Nat} {l : List (Id × Arith)} (j : Nat) (α : Arith)
      (h : j = 1 ∧ 4 ≤ lo ∨
        (n + 4 ≤ j ∧ j ≤ n + 3 + m + 1 ∧ 17 * (n + 3 + m + 1 - j) + 4 ≤ lo))
      (hl : TailOk Z m n (lo + 1) (hi + 1) l) : TailOk Z m n lo hi (([j], α) :: l)

/-- Once the first thread has taken the zero of the first argument, the
count of the actions no longer matters. -/
theorem TailOk.late {Z : Prop} {m n lo hi : Nat} {l : List (Id × Arith)}
    (h : TailOk Z m n lo hi l) : ∀ L, 17 * m + 21 ≤ L → TailOk Z m n L hi l := by
  induction h with
  | nil => exact fun _ _ => .nil
  | snd j α h1 h2 _ ha _ ih =>
    exact fun L hL => .snd j α h1 h2 (fun _ => .inr (.inr (by omega))) ha
      (ih (L + 3) (by omega))
  | top α Hlo Hhi _ h2 h3 h4 ha _ ih =>
    exact fun L hL => .top α Hlo Hhi (by omega) h2 h3 h4 ha (ih (L + 3 + Hlo) (by omega))
  | gone j α h _ ih =>
    intro L hL
    refine .gone j α ?_ (ih (L + 1) (by omega))
    rcases h with ⟨e, -⟩ | ⟨j1, j2, -⟩
    · exact .inl ⟨e, by omega⟩
    · exact .inr ⟨j1, j2, by omega⟩

/-- **A list that a thread can read while the first thread works**: `r0`
successors of the chain, the lowest last, three actions each, then a list
`tl` that can be read after them, whose agents cost `W` actions in all at
most; the thread has `4 * m + 3 * n + 15` actions for the whole.  With
`Z` the thread may get ready to take the zero of the first argument and
the last adder. -/
structure ReadList (Z : Prop) (m n r0 : Nat) (tl : List (Id × Arith)) (W : Nat) : Prop where
  four : 4 ≤ r0
  le : r0 ≤ m
  names : TailOk Z m n (3 * r0) (3 * r0) tl
  sum : passSum m n tl = W
  low : m + 3 * n + 15 ≤ W
  fits : 3 * r0 + W ≤ 4 * m + 3 * n + 15

/-- **What a thread that reads can be while the first works**, with the
actions it has left at most, and the least and the greatest number it has
made unless the first thread has taken the zero of the first argument: in
the chain it pops a successor, reads its segment, and finds the point above
without a second segment, three actions for each; after the chain it does
the same with the second argument and the zeros, walks along the adders
from the top of the second argument, one hop for each adder whose round is
written, and finds the first adder and the successors that the first
rounds took gone.  From the zero of the first argument it can come to the
last adder, when the segment between them is written; it finds it gone,
or else it gets ready to take the two, which is the one way out of these
states. -/
inductive Reads (Z : Prop) (m n r0 : Nat) (tl : List (Id × Arith)) (W : Nat) :
    XThread Arith → Nat → Nat → Nat → Prop
  | cIdle (r : Nat) (hr : r ≤ r0) :
      Reads Z m n r0 tl W ⟨chainL n r ++ tl, .idle⟩ (3 * r + W) (3 * (r0 - r)) (3 * (r0 - r))
  | cLook (r : Nat) (hr : r < r0) :
      Reads Z m n r0 tl W ⟨chainL n r ++ tl, .look [n + 3 + r + 1] .succ⟩
        (3 * r + W + 2) (3 * (r0 - (r + 1)) + 1) (3 * (r0 - (r + 1)) + 1)
  | cSeek (r : Nat) (hr : r < r0) :
      Reads Z m n r0 tl W ⟨chainL n r ++ tl,
        .seek [n + 3 + r + 1] .succ ([n + 3 + r + 1], 0) ([n + 3 + r + 1 + 1], 1)⟩
        (3 * r + W + 1) (3 * (r0 - (r + 1)) + 2) (3 * (r0 - (r + 1)) + 2)
  | tIdle (l : List (Id × Arith)) (lo hi : Nat) (hl : TailOk Z m n lo hi l) :
      Reads Z m n r0 tl W ⟨l, .idle⟩ (passSum m n l) lo hi
  | tLook (l : List (Id × Arith)) (lo hi : Nat) (hl : TailOk Z m n (lo + 3) (hi + 3) l)
      (j : Nat) (α : Arith) (h1 : 2 ≤ j) (h2 : j ≤ n + 2)
      (hz : j = 2 → Z ∨ (lo ≤ hi ∧ hi ≤ 17 * m + 6) ∨ 17 * m + 17 ≤ lo)
      (hα : j = 2 → α = Arith.zero) :
      Reads Z m n r0 tl W ⟨l, .look [j] α⟩ (passCost m n ([j], α) - 1 + passSum m n l)
        (lo + 1) (hi + 1)
  | tSeek (l : List (Id × Arith)) (lo hi : Nat) (hl : TailOk Z m n (lo + 3) (hi + 3) l)
      (j : Nat) (α : Arith) (h1 : 3 ≤ j) (h2 : j ≤ n + 2) :
      Reads Z m n r0 tl W ⟨l, .seek [j] α ([j], 0) ([j + 1], 1)⟩ (1 + passSum m n l)
        (lo + 2) (hi + 2)
  | tTwo (l : List (Id × Arith)) (lo hi : Nat) (hl : TailOk Z m n (lo + 3) (hi + 3) l)
      (α : Arith) (hz : Z ∨ (lo ≤ hi ∧ hi ≤ 17 * m + 6) ∨ 17 * m + 17 ≤ lo)
      (hα : α = Arith.zero) :
      Reads Z m n r0 tl W ⟨l, .seek [2] α ([2], 0) ([n + 4], 1)⟩ (2 + passSum m n l)
        (lo + 2) (hi + 2)
  | eOne (l : List (Id × Arith)) (lo hi lo' : Nat)
      (hl : TailOk Z m n (lo + 3) (hi + 3) l) (α : Arith) (hα : α = Arith.zero)
      (h1 : lo + 3 ≤ lo') (h2 : 17 * m + 10 ≤ lo') (hz : Z ∨ 17 * m + 17 ≤ lo) :
      Reads Z m n r0 tl W ⟨l, .seek [2] α ([n + 4], 1) ([0, n + 4], 0)⟩ (1 + passSum m n l)
        lo' (hi + 3)
  | tTop (l : List (Id × Arith)) (lo hi Hlo Hhi : Nat) (k1 : 16 * Hlo ≤ lo + 3)
      (k2 : hi + 4 ≤ 16 * Hhi) (k3 : Hlo ≤ m) (k4 : Hhi ≤ m)
      (hl : TailOk Z m n (lo + 3 + Hlo) (hi + 3 + Hhi) l) (α : Arith) :
      Reads Z m n r0 tl W ⟨l, .look [n + 3] α⟩ (m + 5 + passSum m n l) (lo + 1) (hi + 1)
  | w0 (l : List (Id × Arith)) (lo hi Hlo Hhi : Nat) (k1 : 16 * Hlo ≤ lo + 3)
      (k2 : hi + 4 ≤ 16 * Hhi) (k3 : Hlo ≤ m) (k4 : Hhi ≤ m)
      (hl : TailOk Z m n (lo + 3 + Hlo) (hi + 3 + Hhi) l) (α : Arith) :
      Reads Z m n r0 tl W ⟨l, .seek [n + 3] α ([n + 3], 0) ([1], 1)⟩
        (m + 4 + passSum m n l) (lo + 2) (hi + 2)
  | wx (l : List (Id × Arith)) (lo hi Hlo Hhi : Nat) (k1 : 16 * Hlo ≤ lo + 3)
      (k2 : hi + 4 ≤ 16 * Hhi) (k3 : Hlo ≤ m) (k4 : Hhi ≤ m)
      (hl : TailOk Z m n (lo + 3 + Hlo) (hi + 3 + Hhi) l) (α : Arith)
      (x : Nat) (hx1 : n + 3 + 1 ≤ x) (hx2 : x ≤ n + 3 + m + 1)
      (hd : n + 3 + m + 2 - x ≤ Hhi ∨ 17 * m + 21 ≤ lo + 2 + (n + 3 + m + 2 - x)) :
      Reads Z m n r0 tl W ⟨l, .seek [n + 3] α
          (if x = n + 3 + m + 1 then ([1], 1) else ([0, x + 1], 1)) ([0, x], 1)⟩
        (x - (n + 4) + 3 + passSum m n l) (lo + 2 + (n + 3 + m + 2 - x))
        (hi + 2 + (n + 3 + m + 2 - x))
  | w2 (l : List (Id × Arith)) (hi : Nat) (hl : TailOk Z m n (17 * m + 21) hi l) (α : Arith) :
      Reads Z m n r0 tl W ⟨l, .seek [n + 3] α ([0, n + 3 + 1], 1) ([0, n + 3 + 1], 2)⟩
        (2 + passSum m n l) (17 * m + 21) hi
  | w1 (l : List (Id × Arith)) (hi : Nat) (hl : TailOk Z m n (17 * m + 21) hi l) (α : Arith) :
      Reads Z m n r0 tl W ⟨l, .seek [n + 3] α ([0, n + 3 + 1], 2) ([0, 0, n + 3 + 1 + 1], 1)⟩
        (1 + passSum m n l) (17 * m + 21) hi

/-- In each of these states the thread reads. -/
theorem Reads.reading {Z : Prop} {m n r0 : Nat} {tl : List (Id × Arith)} {W : Nat}
    {T : XThread Arith} {b lo hi : Nat} (h : Reads Z m n r0 tl W T b lo hi) :
    T.st.Reading := by
  cases h <;> exact trivial

theorem seek_aux_none (X : XNet Arith) (i : Id) (k : Nat) (hk : k ≠ 0) :
    (if ((i, k) : Port).2 = 0 then assoc ((i, k) : Port).1 X.agents else none) = none :=
  ite_neg' hk

/-- **One action of a thread that reads**, in a memory of the run of the
first: it changes nothing, makes no claim, and has one action fewer
left.  The thread stays in the states of `Reads`, with one exception that
needs `Z`: when it has come from the zero of the first argument to the last
adder and finds it in memory, which can only be at the actions
`17 * m + 10` to `17 * m + 19`, it gets ready to take the two.  The count
of the actions made stays between its two bounds, unless the first thread
has taken the zero of the first argument: on the walk from the top of the
second argument the thread makes a hop when the segment is written and
stops when it is not. -/
theorem Reads.step {Z : Prop} {m n r0 : Nat} {tl : List (Id × Arith)} {W : Nat}
    (RL : ReadList Z m n r0 tl W) {Xf X : XNet Arith}
    (F : Final n (sum (m + 1) n) Xf (n + 3 + m + 1) m) {a : Nat}
    (hfin : ∀ e ∈ X.wires, e ∈ Xf.wires)
    (hseg : ∀ t, n + 4 ≤ t → t ≤ n + 3 + m + 1 →
      (t = n + 3 + m + 1 ∧ a + 1 ≤ 3 ∨ a + 1 + 17 * t + 1 ≤ 17 * (n + 3 + m + 1)) →
      ∀ q, ((([t], 1), q) : Port × Port) ∈ X.wires → q = (below n (t - 1), 0))
    (hgone : 5 ≤ a + 1 → assoc [n + 3 + m + 1] X.agents = none ∧ assoc [1] X.agents = none)
    (hgone' : ∀ j, n + 4 ≤ j → j ≤ n + 3 + m → 17 * (n + 3 + m + 1 - j) + 5 ≤ a + 1 →
      assoc [j] X.agents = none)
    (halive : ∀ t, n + 4 ≤ t → t ≤ n + 3 + m → a + 2 ≤ 17 * (n + 3 + m + 1 - t) →
      assoc [t] X.agents = some .succ)
    (halive' : ∀ j α, 2 ≤ j → j ≤ n + 3 → a + 1 ≤ 17 * m + 21 →
      assoc [j] (sum (m + 1) n).agents = some α → assoc [j] X.agents = some α)
    (hgone2 : 17 * m + 22 ≤ a + 1 → assoc [2] X.agents = none)
    (hl3 : ((([n + 4], 1), ([0, n + 4], 0)) : Port × Port) ∈ X.wires → 17 * m + 10 ≤ a + 1)
    (hAg : 17 * m + 21 ≤ a + 1 → assoc [0, n + 4] X.agents = none)
    (hAal : 17 * m + 10 ≤ a + 1 → a + 1 ≤ 17 * m + 20 →
      assoc [0, n + 4] X.agents = some .add)
    (htop : 16 ≤ a + 1 → ((([1], 1), ([0, n + 3 + m + 1], 1)) : Port × Port) ∈ X.wires)
    (hpres : ∀ t, n + 4 ≤ t → t < n + 3 + m + 1 → 16 + 17 * (n + 3 + m + 1 - t) ≤ a + 1 →
      ((([0, t + 1], 1), ([0, t], 1)) : Port × Port) ∈ X.wires)
    (habs : ∀ t, n + 4 ≤ t → t < n + 3 + m + 1 →
      ((([0, t + 1], 1), ([0, t], 1)) : Port × Port) ∈ X.wires →
      17 * (n + 3 + m + 1 - t) ≤ a + 1)
    (hstart : ∀ e ∈ (sum (m + 1) n).wires, e ∈ X.wires)
    {T1 : XThread Arith} {b lo hi : Nat} (h : Reads Z m n r0 tl W T1 b lo hi)
    (hb : a + b ≤ 4 * m + 3 * n + 15) (hlo : lo ≤ a ∧ (a ≤ hi ∨ 17 * m + 21 ≤ lo)) :
    T1 = ⟨[], .idle⟩ ∨
      (Z ∧ 17 * m + 10 ≤ a ∧ a + 1 ≤ 17 * m + 20 ∧ 1 ≤ b ∧
        ∃ l, XMach.act xsys X T1 = (X, ⟨l, .ready [2] [0, n + 4] .zero .add⟩, 0)) ∨
      ∃ T1' b' lo' hi', XMach.act xsys X T1 = (X, T1', 0) ∧
        Reads Z m n r0 tl W T1' b' lo' hi' ∧ b' + 1 ≤ b ∧
          (lo' ≤ a + 1 ∧ (a + 1 ≤ hi' ∨ 17 * m + 21 ≤ lo')) := by
  have S := snd_sum (m + 1) n
  have hfr := sum_fresh (m + 1) n
  have h4 := RL.four
  have hle := RL.le
  have hlow := RL.low
  have tailIdle : ∀ l lo hi, TailOk Z m n lo hi l → (lo ≤ a ∧ (a ≤ hi ∨ 17 * m + 21 ≤ lo)) →
      (⟨l, .idle⟩ : XThread Arith) = ⟨[], .idle⟩ ∨ ∃ T1' b' lo' hi',
        XMach.act xsys X ⟨l, .idle⟩ = (X, T1', 0) ∧ Reads Z m n r0 tl W T1' b' lo' hi' ∧
          b' + 1 ≤ passSum m n l ∧ (lo' ≤ a + 1 ∧ (a + 1 ≤ hi' ∨ 17 * m + 21 ≤ lo')) := by
    intro l lo hi hok hl
    cases hok with
    | nil => exact .inl rfl
    | @snd _ _ l' j α h1 h2 hz ha hok' =>
      right
      have hw : passSum m n (([j], α) :: l') = passCost m n ([j], α) + passSum m n l' := rfl
      have hg := passCost_ge m n ([j], α)
      by_cases hal : assoc [j] X.agents = some α
      · have hz' : j = 2 → Z ∨ (lo ≤ hi ∧ hi ≤ 17 * m + 6) ∨ 17 * m + 17 ≤ lo := fun e => by
          rcases hz e with z | z | z
          · exact .inl z
          · refine .inr (.inl ⟨?_, z⟩)
            have h22 : ¬ 17 * m + 22 ≤ a + 1 := fun hu => by
              rw [e, hgone2 hu] at hal
              cases hal
            omega
          · exact .inr (.inr z)
        have hα' : j = 2 → α = Arith.zero := fun e => by
          have ha' := ha
          rw [e, sum_zero_agent m n] at ha'
          exact (Option.some.inj ha').symm
        exact ⟨⟨l', .look [j] α⟩, _, _, _, XMach.act_idle_pos (e := ([j], α)) hal,
          .tLook l' lo hi hok' j α h1 h2 hz' hα', by omega, by omega⟩
      · have late : ¬ a + 1 ≤ 17 * m + 21 := fun hu =>
          hal (halive' j α h1 (by omega) hu ha)
        exact ⟨⟨l', .idle⟩, _, _, _, XMach.act_idle_neg (e := ([j], α)) hal,
          .tIdle l' (17 * m + 21) (hi + 3) (hok'.late _ (Nat.le_refl _)), by omega, by omega⟩
    | @top _ _ l' α Hlo Hhi k1 k2 k3 k4 ha hok' =>
      right
      have hw : passSum m n (([n + 3], α) :: l') =
        passCost m n ([n + 3], α) + passSum m n l' := rfl
      have hg := passCost_top m n α
      by_cases hal : assoc [n + 3] X.agents = some α
      · exact ⟨⟨l', .look [n + 3] α⟩, _, _, _, XMach.act_idle_pos (e := ([n + 3], α)) hal,
          .tTop l' lo hi Hlo Hhi k1 k2 k3 k4 hok' α, by omega, by omega⟩
      · have late : ¬ a + 1 ≤ 17 * m + 21 := fun hu =>
          hal (halive' (n + 3) α (by omega) (Nat.le_refl _) hu ha)
        exact ⟨⟨l', .idle⟩, _, _, _, XMach.act_idle_neg (e := ([n + 3], α)) hal,
          .tIdle l' (17 * m + 21) (hi + 3 + Hhi) (hok'.late _ (Nat.le_refl _)),
          by omega, by omega⟩
    | @gone _ _ l' j α hj hok' =>
      right
      have hw : passSum m n (([j], α) :: l') = passCost m n ([j], α) + passSum m n l' := rfl
      have hg := passCost_ge m n ([j], α)
      by_cases hal : assoc [j] X.agents = some α
      · exfalso
        rcases hj with ⟨e1, hl4⟩ | ⟨j1, j2, hd⟩
        · rw [e1, (hgone (by omega)).2] at hal
          cases hal
        · by_cases e1 : j = n + 3 + m + 1
          · rw [e1, (hgone (by omega)).1] at hal
            cases hal
          · rw [hgone' j j1 (by omega) (by omega)] at hal
            cases hal
      · exact ⟨⟨l', .idle⟩, _, _, _, XMach.act_idle_neg (e := ([j], α)) hal,
          .tIdle l' (lo + 1) (hi + 1) hok', by omega, by omega⟩
  cases h with
  | cIdle r hr =>
    cases r with
    | zero =>
      have h0 := tailIdle tl (3 * r0) (3 * r0) RL.names (by omega)
      rw [RL.sum] at h0
      rcases h0 with h0 | ⟨T1', b', lo', hi', k1, k2, k3, k4⟩
      · exact .inl h0
      · exact .inr (.inr ⟨T1', b', lo', hi', k1, k2, by omega, k4⟩)
    | succ r =>
      right
      right
      have hal : assoc [n + 3 + r + 1] X.agents = some Arith.succ :=
        halive (n + 3 + r + 1) (by omega) (by omega) (by omega)
      exact ⟨⟨chainL n r ++ tl, .look [n + 3 + r + 1] .succ⟩, _, _, _,
        XMach.act_idle_pos (e := ([n + 3 + r + 1], Arith.succ)) hal, .cLook r (by omega),
        by omega, by omega⟩
  | cLook r hr =>
    right
    right
    cases hq : assoc (([n + 3 + r + 1], 0) : Port) X.wires with
    | none =>
      exfalso
      obtain ⟨q', e'⟩ := assoc_of_mem (hstart _
        ((sum_princ (m + 1) n (n + 3 + r + 1) (by omega) (by omega)
          ([n + 3 + r + 1 + 1], 1)).2 rfl))
      rw [hq] at e'
      cases e'
    | some q =>
      have hq0 := (F.old (.inl rfl) q).1 (hfin _ (assoc_mem hq))
      have eq := (sum_princ (m + 1) n (n + 3 + r + 1) (by omega) (by omega) q).1 hq0
      subst eq
      exact ⟨⟨_, .seek [n + 3 + r + 1] .succ ([n + 3 + r + 1], 0) ([n + 3 + r + 1 + 1], 1)⟩,
        _, _, _, XMach.act_look hq, .cSeek r hr, by omega, by omega⟩
  | cSeek r hr =>
    right
    right
    cases hq : nextSeg X.wires ([n + 3 + r + 1 + 1], 1) ([n + 3 + r + 1], 0) with
    | none =>
      exact ⟨⟨_, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
        .cIdle r (by omega), by omega, by omega⟩
    | some q =>
      exfalso
      obtain ⟨hmem, hne⟩ := nextSeg_spec hq
      have h3 := hseg (n + 3 + r + 1 + 1) (by omega) (by omega) (by omega) q hmem
      rw [show n + 3 + r + 1 + 1 - 1 = n + 3 + r + 1 by omega, below_pos (by omega)] at h3
      exact hne h3
  | tIdle l lo hi hl =>
    rcases tailIdle l lo hi hl hlo with h0 | ⟨T1', b', lo', hi', k1, k2, k3, k4⟩
    · exact .inl h0
    · exact .inr (.inr ⟨T1', b', lo', hi', k1, k2, k3, k4⟩)
  | tLook l lo hi hl j α h1 h2 hz hα =>
    right
    right
    cases hq : assoc (([j], 0) : Port) X.wires with
    | none =>
      exfalso
      have hex : ∃ q, ((([j], 0), q) : Port × Port) ∈ X.wires := by
        by_cases hj2 : j = 2
        · exact ⟨([n + 4], 1), hstart _ (by rw [hj2]; exact (sum_two m n _).2 rfl)⟩
        · exact ⟨([j + 1], 1), hstart _ ((S.up j (by omega) (by omega) _).2 rfl)⟩
      obtain ⟨q, hm⟩ := hex
      obtain ⟨q', e'⟩ := assoc_of_mem hm
      rw [hq] at e'
      cases e'
    | some q =>
      have hm1 := hfin _ (assoc_mem hq)
      by_cases hj2 : j = 2
      · subst hj2
        have eq := (sum_two m n q).1 ((F.old (.inl rfl) q).1 hm1)
        subst eq
        have hw := passCost_two m n α
        exact ⟨⟨l, .seek [2] α ([2], 0) ([n + 4], 1)⟩, _, _, _, XMach.act_look hq,
          .tTwo l lo hi hl α (hz rfl) (hα rfl), by omega, by omega⟩
      · have eq := (F.up S (by omega) (by omega) q).1 hm1
        subst eq
        have hw : passCost m n ([j], α) = 3 :=
          passCost_ne (by ports_differ) (by ports_differ) (by ports_differ)
        exact ⟨⟨l, .seek [j] α ([j], 0) ([j + 1], 1)⟩, _, _, _, XMach.act_look hq,
          .tSeek l lo hi hl j α (by omega) (by omega), by omega, by omega⟩
  | tSeek l lo hi hl j α h1 h2 =>
    right
    right
    cases hq : nextSeg X.wires ([j + 1], 1) ([j], 0) with
    | none =>
      exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
        .tIdle l (lo + 3) (hi + 3) hl, by omega, by omega⟩
    | some q =>
      exfalso
      obtain ⟨hmem, hne⟩ := nextSeg_spec hq
      exact hne ((F.down S h1 h2 q).1 (hfin _ hmem))
  | tTwo l lo hi hl α hz hα =>
    right
    right
    cases hq : nextSeg X.wires ([n + 4], 1) ([2], 0) with
    | none =>
      exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
        .tIdle l (lo + 3) (hi + 3) hl, by omega, by omega⟩
    | some q =>
      obtain ⟨hmem, hne⟩ := nextSeg_spec hq
      rcases F.low_one q (hfin _ hmem) with e | e
      · exact absurd e hne
      · subst e
        have h10 := hl3 hmem
        rcases hz with z | ⟨z1, z2⟩ | z
        · exact ⟨_, _, _, _, XMach.act_seek_next (seek_aux_none X _ 1 (by decide)) hq,
            .eOne l lo hi (a + 1) hl α hα (by omega) h10 (.inl z), by omega, by omega⟩
        · omega
        · exact ⟨_, _, _, _, XMach.act_seek_next (seek_aux_none X _ 1 (by decide)) hq,
            .eOne l lo hi (a + 1) hl α hα (by omega) h10 (.inr z), by omega, by omega⟩
  | eOne l lo hi lo' hl α hα k1 k2 hz =>
    subst hα
    by_cases hal : a + 1 ≤ 17 * m + 20
    · have hA := hAal (by omega) hal
      rcases hz with z | z
      · exact .inr (.inl ⟨z, by omega, hal, by omega, l,
          XMach.act_seek_found (c := ([0, n + 4], 0)) ((ite_pos' rfl).trans hA)
            ⟨by ports_differ, rfl⟩⟩)
      · omega
    · have hA : assoc [0, n + 4] X.agents = none := hAg (by omega)
      right
      right
      cases hq : nextSeg X.wires ([0, n + 4], 0) ([n + 4], 1) with
      | none =>
        exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop ((ite_pos' rfl).trans hA) hq,
          .tIdle l (17 * m + 21) (hi + 3) (hl.late _ (Nat.le_refl _)), by omega, by omega⟩
      | some q =>
        exfalso
        obtain ⟨hmem, hne⟩ := nextSeg_spec hq
        exact hne (F.adder_zero (by omega) q (hfin _ hmem))
  | tTop l lo hi Hlo Hhi k1 k2 k3 k4 hl α =>
    right
    right
    cases hq : assoc (([n + 3], 0) : Port) X.wires with
    | none =>
      exfalso
      obtain ⟨q', e'⟩ := assoc_of_mem (hstart _ ((S.top ([1], 1)).2 rfl))
      rw [hq] at e'
      cases e'
    | some q =>
      have eq := (F.top_snd S q).1 (hfin _ (assoc_mem hq))
      subst eq
      exact ⟨⟨l, .seek [n + 3] α ([n + 3], 0) ([1], 1)⟩, _, _, _, XMach.act_look hq,
        .w0 l lo hi Hlo Hhi k1 k2 k3 k4 hl α, by omega, by omega⟩
  | w0 l lo hi Hlo Hhi k1 k2 k3 k4 hl α =>
    right
    right
    cases hq : nextSeg X.wires ([1], 1) ([n + 3], 0) with
    | none =>
      by_cases hf : 17 * m + 21 ≤ lo + 2
      · exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
          .tIdle l (17 * m + 21) (hi + 3 + Hhi) (hl.late _ (Nat.le_refl _)),
          by omega, by omega⟩
      · have h16 : ¬ 16 ≤ a + 1 := fun hu =>
          nextSeg_ne_none (htop hu) (by ports_differ) hq
        exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
          .tIdle l (lo + 3 + Hlo) (hi + 3 + Hhi) hl, by omega, by omega⟩
    | some q =>
      obtain ⟨hmem, hne⟩ := nextSeg_spec hq
      rcases (F.one_one S q).1 (hfin _ hmem) with e | e
      · exact absurd e hne
      · subst e
        have nx := Reads.wx (Z := Z) (m := m) (n := n) (r0 := r0) (tl := tl) (W := W) l lo hi
          Hlo Hhi k1 k2 k3 k4 hl α (n + 3 + m + 1) (by omega) (Nat.le_refl _) (.inl (by omega))
        rw [ite_pos' (rfl : n + 3 + m + 1 = n + 3 + m + 1)] at nx
        exact ⟨_, _, _, _, XMach.act_seek_next (seek_aux_none X _ 1 (by decide)) hq, nx,
          by omega, by omega⟩
  | wx l lo hi Hlo Hhi k1 k2 k3 k4 hl α x hx1 hx2 hd =>
    right
    right
    cases hq : nextSeg X.wires ([0, x], 1)
        (if x = n + 3 + m + 1 then ([1], 1) else ([0, x + 1], 1)) with
    | none =>
      by_cases hf : 17 * m + 21 ≤ lo + 2 + (n + 3 + m + 2 - x)
      · exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
          .tIdle l (17 * m + 21) (hi + 3 + Hhi) (hl.late _ (Nat.le_refl _)),
          by omega, by omega⟩
      · have hH : Hlo ≤ n + 3 + m + 2 - x := by
          by_cases hx5 : x = n + 3 + 1
          · omega
          · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
            have h16 : ¬ 16 + 17 * (n + 3 + m + 1 - y) ≤ a + 1 := fun hu =>
              nextSeg_ne_none (hpres y (by omega) (by omega) hu) (by
                split
                · ports_differ
                · ports_differ) hq
            omega
        exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
          .tIdle l (lo + 3 + Hlo) (hi + 3 + Hhi) hl, by omega, by omega⟩
    | some q =>
      obtain ⟨hmem, hne⟩ := nextSeg_spec hq
      rcases (F.adder_one hfr (by omega) hx2 q).1 (hfin _ hmem) with
        ⟨ex, e⟩ | ⟨hx, t, ex, e⟩ | ⟨hx, e⟩ | ⟨ex, e⟩
      · rw [ite_pos' ex] at hne
        exact absurd e hne
      · subst ex
        subst e
        have hd' : n + 3 + m + 2 - t ≤ Hhi ∨
            17 * m + 21 ≤ lo + 2 + (n + 3 + m + 2 - t) := by
          have h17 := habs t (by omega) (by omega) hmem
          omega
        have nx := Reads.wx (Z := Z) (m := m) (n := n) (r0 := r0) (tl := tl) (W := W) l lo hi
          Hlo Hhi k1 k2 k3 k4 hl α t (by omega) (by omega) hd'
        rw [ite_neg' (by omega : ¬ t = n + 3 + m + 1)] at nx
        exact ⟨_, _, _, _, XMach.act_seek_next (seek_aux_none X _ 1 (by decide)) hq, nx,
          by omega, by omega⟩
      · rw [ite_neg' (by omega : ¬ x = n + 3 + m + 1)] at hne
        exact absurd e hne
      · subst e
        subst ex
        exact ⟨_, _, _, _, XMach.act_seek_next (seek_aux_none X _ 1 (by decide)) hq,
          .w2 l (hi + 3 + Hhi) (hl.late _ (Nat.le_refl _)) α, by omega, by omega⟩
  | w2 l hi hl α =>
    right
    right
    cases hq : nextSeg X.wires ([0, n + 3 + 1], 2) ([0, n + 3 + 1], 1) with
    | none =>
      exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 2 (by decide)) hq,
        .tIdle l (17 * m + 21) hi hl, by omega, by omega⟩
    | some q =>
      obtain ⟨hmem, hne⟩ := nextSeg_spec hq
      rcases (F.adder_two hfr (by omega) (by omega) q).1 (hfin _ hmem) with
        ⟨ex, -⟩ | ⟨-, e⟩ | ⟨hx, -⟩ | ⟨-, e⟩
      · exact absurd ex (by omega)
      · subst e
        exact ⟨_, _, _, _, XMach.act_seek_next (seek_aux_none X _ 2 (by decide)) hq,
          .w1 l hi hl α, by omega, by omega⟩
      · exact absurd hx (by omega)
      · exact absurd e hne
  | w1 l hi hl α =>
    right
    right
    cases hq : nextSeg X.wires ([0, 0, n + 3 + 1 + 1], 1) ([0, n + 3 + 1], 2) with
    | none =>
      exact ⟨⟨l, .idle⟩, _, _, _, XMach.act_seek_stop (seek_aux_none X _ 1 (by decide)) hq,
        .tIdle l (17 * m + 21) hi hl, by omega, by omega⟩
    | some q =>
      exfalso
      obtain ⟨hmem, hne⟩ := nextSeg_spec hq
      exact hne ((F.res_one hfr (by omega) (by omega) q).1 (hfin _ hmem))

theorem chainL_length (n : Nat) : ∀ r, (chainL n r).length = r
  | 0 => rfl
  | r + 1 => congrArg (· + 1) (chainL_length n r)

theorem chainL_drop (n r : Nat) : ∀ s, (chainL n (r + s)).drop s = chainL n r
  | 0 => rfl
  | s + 1 => chainL_drop n r s

/-- The `s` top successors of a chain. -/
theorem mem_chain_take (n r : Nat) : ∀ (s : Nat) {e : Id × Arith},
    e ∈ (chainL n (r + s)).take s → ∃ j, n + 3 + r + 1 ≤ j ∧ j ≤ n + 3 + r + s ∧ e.1 = [j]
  | 0, _, h => by cases h
  | s + 1, e, h => by
    have h' : e ∈ ([n + 3 + (r + s) + 1], Arith.succ) :: (chainL n (r + s)).take s := h
    rcases List.mem_cons.1 h' with e1 | h''
    · exact ⟨n + 3 + (r + s) + 1, by omega, by omega, by rw [e1]⟩
    · obtain ⟨j, j1, j2, j3⟩ := mem_chain_take n r s h''
      exact ⟨j, j1, by omega, j3⟩

/-- **The list of agents turned by `s`**: the chain without its `s` top
successors, the rest of the agents, and those successors last. -/
theorem chain_turn (n r s : Nat) (B : List (Id × Arith)) :
    (chainL n (r + s) ++ B).drop s ++ (chainL n (r + s) ++ B).take s =
      chainL n r ++ (B ++ (chainL n (r + s)).take s) := by
  have hl : s ≤ (chainL n (r + s)).length := by
    rw [chainL_length]
    omega
  rw [List.drop_append_of_le_length hl, List.take_append_of_le_length hl, chainL_drop,
    List.append_assoc]

/-- Agents of the second argument below its top, at the head of a list:
three actions for each. -/
theorem tailOk_snd {Z : Prop} {m n : Nat} : ∀ (l₁ : List (Id × Arith)),
    (∀ e ∈ l₁, ∃ j, 3 ≤ j ∧ j ≤ n + 2 ∧ e.1 = [j] ∧
      assoc [j] (sum (m + 1) n).agents = some e.2) →
    ∀ (lo hi : Nat) (l : List (Id × Arith)),
      TailOk Z m n (lo + 3 * l₁.length) (hi + 3 * l₁.length) l → TailOk Z m n lo hi (l₁ ++ l)
  | [], _, _, _, _, h => h
  | (i, α) :: l₁, hs, lo, hi, l, h => by
    obtain ⟨j, h1, h2, ej, ha⟩ := hs (i, α) List.mem_cons_self
    have ej' : i = [j] := ej
    subst ej'
    have h' : TailOk Z m n (lo + 3 + 3 * l₁.length) (hi + 3 + 3 * l₁.length) l := by
      rw [show lo + 3 + 3 * l₁.length = lo + 3 * (l₁.length + 1) by omega,
        show hi + 3 + 3 * l₁.length = hi + 3 * (l₁.length + 1) by omega]
      exact h
    exact .snd j α (by omega) h2 (fun e => by omega) ha
      (tailOk_snd l₁ (fun e he => hs e (List.mem_cons_of_mem _ he)) (lo + 3) (hi + 3) l h')

/-- Successors that the first rounds have taken, at the end of a list: one
action for each. -/
theorem tailOk_gone {Z : Prop} {m n : Nat} : ∀ (l₂ : List (Id × Arith)) (lo hi : Nat),
    (∀ e ∈ l₂, ∃ j, n + 4 ≤ j ∧ j ≤ n + 3 + m + 1 ∧
      17 * (n + 3 + m + 1 - j) + 4 ≤ lo ∧ e.1 = [j]) → TailOk Z m n lo hi l₂
  | [], _, _, _ => .nil
  | (i, α) :: l₂, lo, hi, hs => by
    obtain ⟨j, j1, j2, j3, ej⟩ := hs (i, α) List.mem_cons_self
    have ej' : i = [j] := ej
    subst ej'
    exact .gone j α (.inr ⟨j1, j2, j3⟩)
      (tailOk_gone l₂ (lo + 1) (hi + 1) fun e he => by
        obtain ⟨j', k1, k2, k3, k4⟩ := hs e (List.mem_cons_of_mem _ he)
        exact ⟨j', k1, k2, by omega, k4⟩)

/-- The end of the list of the thread numbered `t + 1`: the zero of the
second argument and the `t + 1` top successors. -/
theorem tailOk_end {Z : Prop} (m n t : Nat) (hm : t + 4 ≤ m) {lo hi : Nat}
    (hlo : 17 * t + 1 ≤ lo) (hhi : n = 0 → hi + 4 ≤ 16 * m) :
    TailOk Z m n lo hi (([3], .zero) :: (chainL n (m - t + (t + 1))).take (t + 1)) := by
  have ha : assoc [3] (sum (m + 1) n).agents = some Arith.zero :=
    sum_assoc_base m n (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tops : ∀ lo' hi', lo + 3 ≤ lo' →
      TailOk Z m n lo' hi' ((chainL n (m - t + (t + 1))).take (t + 1)) := fun lo' hi' hl =>
    tailOk_gone _ lo' hi' fun e he => by
      obtain ⟨j, j1, j2, j3⟩ := mem_chain_take n (m - t) (t + 1) he
      exact ⟨j, by omega, by omega, by omega, j3⟩
  cases n with
  | zero =>
    exact .top .zero 0 m (by omega) (hhi rfl) (by omega) (Nat.le_refl _) ha
      (tops _ _ (by omega))
  | succ k =>
    exact .snd 3 .zero (by omega) (by omega) (fun e => absurd e (by decide)) ha
      (tops _ _ (by omega))

/-- **The list of the thread numbered `t + 1`** can be read while the first
thread works: the chain without its `t + 1` top successors, then the second
argument, the adder, the zeros, and those successors.  The thread makes
three actions on each of the `m - t` successors of its chain, a walk from
the top of the second argument that is as long as the rounds written when
it gets there, `(3 * (m - t) + 3) / 16` hops or one more, three actions on
each other agent of the second argument and one on the first adder.  So it
comes to the zero of the first argument after
`3 * (m - t) + 3 * n + 1 + (3 * (m - t) + 3) / 16` actions or one more:
early enough to pass it before the segment to the last adder is written,
or late enough to find the last adder gone, or else `Z` is needed.  And it
comes to the top
successors after their rounds: the round on the last of them has taken it
after `17 * t + 5` actions of the first thread. -/
theorem readList_turn {Z : Prop} (m n t : Nat) (hm : t + 4 ≤ m)
    (ht : 20 * t ≤ 3 * m + 3 * n + 2)
    (h2 : Z ∨ 3 * (m - t) + 3 * n + 2 + (3 * (m - t) + 3) / 16 ≤ 17 * m + 6 ∨
      17 * m + 17 ≤ 3 * (m - t) + 3 * n + 1 + (3 * (m - t) + 3) / 16) :
    ReadList Z m n (m - t) (sndBase n ++ (chainL n (m - t + (t + 1))).take (t + 1))
      (m + 3 * n + 12 + 3 * (t + 1)) := by
  have hlen : ((chainL n (m - t + (t + 1))).take (t + 1)).length = t + 1 := by
    rw [List.length_take, chainL_length]
    omega
  have two : ∀ lo hi, hi ≤ 3 * (m - t) + 3 * n + 2 + (3 * (m - t) + 3) / 16 →
      (n = 0 → hi ≤ 3 * (m - t) + 1) → 3 * (m - t) + 1 ≤ lo →
      (1 ≤ n → 3 * (m - t) + 3 * n + 1 + (3 * (m - t) + 3) / 16 ≤ lo) →
      TailOk Z m n lo hi
        (([2], .zero) :: ([3], .zero) :: (chainL n (m - t + (t + 1))).take (t + 1)) := by
    intro lo hi hh hh0 hl0 hl1
    refine .snd 2 .zero (by omega) (by omega) (fun _ => ?_)
      (sum_assoc_base m n (e := ([2], Arith.zero))
        (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (tailOk_end m n t hm (by omega) (fun e => by
        have := hh0 e
        omega))
    rcases h2 with z | z | z
    · exact .inl z
    · exact .inr (.inl (by omega))
    · exact .inr (.inr (by omega))
  refine ⟨by omega, by omega, ?_, ?_, by omega, by omega⟩
  · show TailOk Z m n (3 * (m - t)) (3 * (m - t))
      ((sndL n ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]) ++
        (chainL n (m - t + (t + 1))).take (t + 1))
    rw [List.append_assoc]
    cases n with
    | zero =>
      exact .gone 1 .add (.inl ⟨rfl, by omega⟩)
        (two _ _ (by omega) (fun _ => by omega) (by omega) (fun h => by omega))
    | succ k =>
      show TailOk Z m (k + 1) (3 * (m - t)) (3 * (m - t))
        (([k + 1 + 3], Arith.succ) :: (sndL k ++
          ([([1], Arith.add), ([2], .zero), ([3], .zero)] ++
            (chainL (k + 1) (m - t + (t + 1))).take (t + 1))))
      refine .top .succ ((3 * (m - t) + 3) / 16) ((3 * (m - t) + 3) / 16 + 1) (by omega)
        (by omega) (by omega) (by omega) ?_ ?_
      · exact sum_assoc_base m (k + 1) (e := ([k + 1 + 3], Arith.succ))
          (List.mem_append_left _
            (show (([k + 1 + 3], Arith.succ) : Id × Arith) ∈ sndL (k + 1) from
              List.mem_cons_self))
      · refine tailOk_snd (sndL k) (fun e he => ?_) _ _ _ ?_
        · obtain ⟨-, j, j1, j2, j3⟩ := mem_sndL he
          have h := sum_assoc_base m (k + 1) (e := e)
            (List.mem_append_left _ (List.mem_cons_of_mem _ he))
          rw [j3] at h
          exact ⟨j, by omega, by omega, j3, h⟩
        · rw [sndL_length]
          exact .gone 1 .add (.inl ⟨rfl, by omega⟩)
            (two _ _ (by omega) (fun h => by omega) (by omega) (fun _ => by omega))
  · rw [passSum_append, passSum_sndBase, passSum_three, hlen]
    intro e he
    obtain ⟨j, j1, j2, j3⟩ := mem_chain_take n (m - t) (t + 1) he
    rw [j3]
    exact ⟨by ports_differ, by ports_differ, by ports_differ⟩

/-- **A thread with such a list only reads, until it is ready to take the
zero of the first argument**: at every moment of the run of the first
thread on the net for `(m + 1) + n`, a thread that acts after each action
of the first is in one of the states of `Reads`, with its count of actions
inside its allowance and between its two bounds; or else, and only when
`Z` allows it, it has got ready to take the zero of the first argument
and the last adder, after only reading, at one of the actions
`17 * m + 11` to `17 * m + 20`. -/
theorem rr_reads {Z : Prop} {m n r0 : Nat} {tl : List (Id × Arith)} {W : Nat}
    (RL : ReadList Z m n r0 tl W) : ∀ a,
    (∃ b lo hi, Reads Z m n r0 tl W (XMach.reader xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ ⟨chainL n r0 ++ tl, .idle⟩ a) b lo hi ∧
      (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
          ⟨chainL n r0 ++ tl, .idle⟩ a = ⟨[], .idle⟩ ∨
        a + b ≤ 4 * m + 3 * n + 15 ∧ (lo ≤ a ∧ (a ≤ hi ∨ 17 * m + 21 ≤ lo)))) ∨
    (Z ∧ ∃ aE l, aE ≤ a ∧ 17 * m + 11 ≤ aE ∧ aE ≤ 17 * m + 20 ∧
      XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        ⟨chainL n r0 ++ tl, .idle⟩ aE = ⟨l, .ready [2] [0, n + 4] .zero .add⟩)
  | 0 => .inl ⟨_, _, _, .cIdle r0 (Nat.le_refl _), .inr ⟨by have := RL.fits; omega, by omega⟩⟩
  | a + 1 => by
    have h4 := RL.four
    have hle := RL.le
    have unf : XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        ⟨chainL n r0 ++ tl, .idle⟩ (a + 1) = (XMach.act xsys
          (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
            ⟨chainL n r0 ++ tl, .idle⟩ a)).2.1 := rfl
    rcases rr_reads RL a with ⟨b, lo, hi, hR, hc⟩ | ⟨z, aE, l, k1, k2, k3, k4⟩
    · obtain ⟨Xf, F, hfin⟩ := solo_fin m n
      rcases hc with hrest | ⟨hb, hlo⟩
      · refine .inl ?_
        rw [unf, hrest]
        exact ⟨_, _, _, .tIdle [] 0 0 .nil, .inl rfl⟩
      · rcases Reads.step RL F (a := a)
          (X := (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1)
          (fun e he => hfin (a + 1) e he)
          (fun t h1 h2 hu q hq => solo_seg m n h1 h2 hu q hq)
          (fun h5 => solo_gone5 m n h5)
          (fun j j1 j2 hu => by
            have hg := solo_gone_succ m n (d := n + 3 + m + 1 - j) (by omega) (by omega)
              (u := a + 1) hu
            rw [show n + 3 + m + 1 - (n + 3 + m + 1 - j) = j by omega] at hg
            exact hg)
          (fun t t1 t2 hu => solo_alive m n (n + 3 + m - t) (by omega) t .succ (a + 1)
            (by omega) (by omega) (by omega) ((start_sum m n).chain.live t t1 (by omega)))
          (fun j α j1 j2 hu hx => solo_alive_zero m n j1 j2 hu hx)
          (fun hu => solo_gone_zero m n hu)
          (fun hq => solo_no_link3 m n (by omega) hq)
          (fun hu => solo_gone_adder m n hu)
          (fun hu1 hu2 => solo_adder_alive m n (by omega) (by omega) hu2)
          (fun hu => solo_link_top m n hu)
          (fun t t1 t2 hu => solo_link m n t1 t2 hu)
          (fun t t1 t2 hq => solo_no_link m n t1 t2 hq)
          (fun e he => by
            have hw := XMach.solo_wires_mono xsys (sum (m + 1) n)
              ⟨(sum (m + 1) n).agents, .idle⟩ 0 (a + 1) e he
            rw [Nat.zero_add] at hw
            exact hw)
          hR hb hlo with
          h0 | ⟨z, t1, t2, -, l, hact⟩ | ⟨T1', b', lo', hi', hact, hR', hb', hlo'⟩
        · refine .inl ?_
          rw [unf, h0]
          exact ⟨_, _, _, .tIdle [] 0 0 .nil, .inl rfl⟩
        · refine .inr ⟨z, a + 1, l, Nat.le_refl _, by omega, by omega, ?_⟩
          rw [unf, hact]
        · refine .inl ?_
          rw [unf, hact]
          exact ⟨b', lo', hi', hR', .inr ⟨by omega, hlo'⟩⟩
    · exact .inr ⟨z, aE, l, by omega, k2, k3, k4⟩

/-- Each of those actions leaves the memory as it is and makes no claim,
the one that gets the thread ready included, and the thread is at rest from
its `4 * m + 3 * n + 15`-th action on: as long as it has not got ready to
take the zero before. -/
theorem rr_quiet {Z : Prop} {m n r0 : Nat} {tl : List (Id × Arith)} {W : Nat}
    (RL : ReadList Z m n r0 tl W) (a : Nat)
    (hne : ¬ (Z ∧ ∃ aE l, aE ≤ a ∧ 17 * m + 11 ≤ aE ∧ aE ≤ 17 * m + 20 ∧
      XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        ⟨chainL n r0 ++ tl, .idle⟩ aE = ⟨l, .ready [2] [0, n + 4] .zero .add⟩)) :
    (XMach.act xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
          ⟨chainL n r0 ++ tl, .idle⟩ a)).1 =
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1 ∧
    (XMach.act xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
          ⟨chainL n r0 ++ tl, .idle⟩ a)).2.2 = 0 ∧
    (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        ⟨chainL n r0 ++ tl, .idle⟩ a ≠ ⟨[], .idle⟩ → a < 4 * m + 3 * n + 15) := by
  have h4 := RL.four
  have hle := RL.le
  rcases rr_reads RL a with ⟨b, lo, hi, hR, hc⟩ | h
  · rcases hc with hrest | ⟨hb, hlo⟩
    · rw [hrest]
      exact ⟨rfl, rfl, fun h => absurd rfl h⟩
    · obtain ⟨Xf, F, hfin⟩ := solo_fin m n
      rcases Reads.step RL F (a := a)
          (X := (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1)
          (fun e he => hfin (a + 1) e he)
          (fun t h1 h2 hu q hq => solo_seg m n h1 h2 hu q hq)
          (fun h5 => solo_gone5 m n h5)
          (fun j j1 j2 hu => by
            have hg := solo_gone_succ m n (d := n + 3 + m + 1 - j) (by omega) (by omega)
              (u := a + 1) hu
            rw [show n + 3 + m + 1 - (n + 3 + m + 1 - j) = j by omega] at hg
            exact hg)
          (fun t t1 t2 hu => solo_alive m n (n + 3 + m - t) (by omega) t .succ (a + 1)
            (by omega) (by omega) (by omega) ((start_sum m n).chain.live t t1 (by omega)))
          (fun j α j1 j2 hu hx => solo_alive_zero m n j1 j2 hu hx)
          (fun hu => solo_gone_zero m n hu)
          (fun hq => solo_no_link3 m n (by omega) hq)
          (fun hu => solo_gone_adder m n hu)
          (fun hu1 hu2 => solo_adder_alive m n (by omega) (by omega) hu2)
          (fun hu => solo_link_top m n hu)
          (fun t t1 t2 hu => solo_link m n t1 t2 hu)
          (fun t t1 t2 hq => solo_no_link m n t1 t2 hq)
          (fun e he => by
            have hw := XMach.solo_wires_mono xsys (sum (m + 1) n)
              ⟨(sum (m + 1) n).agents, .idle⟩ 0 (a + 1) e he
            rw [Nat.zero_add] at hw
            exact hw)
          hR hb hlo with
          h0 | ⟨-, -, -, t3, l, hact⟩ | ⟨T1', b', lo', hi', hact, hR', hb', hlo'⟩
      · rw [h0]
        exact ⟨rfl, rfl, fun h => absurd rfl h⟩
      · rw [hact]
        exact ⟨rfl, rfl, fun _ => by omega⟩
      · rw [hact]
        exact ⟨rfl, rfl, fun _ => by omega⟩
  · exact absurd h hne

/-- While it reads, the list of the thread is an end of its first list. -/
theorem rr_suffix {Z : Prop} {m n r0 : Nat} {tl : List (Id × Arith)} {W : Nat}
    (RL : ReadList Z m n r0 tl W) : ∀ a,
    (Z → a + 1 ≤ 17 * m) →
    ∃ pre, pre ++ (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
      ⟨chainL n r0 ++ tl, .idle⟩ a).todo = chainL n r0 ++ tl
  | 0, _ => ⟨[], rfl⟩
  | a + 1, ha => by
    have ha' : Z → a + 1 ≤ 17 * m := fun z => by
      have := ha z
      omega
    obtain ⟨pre, hp⟩ := rr_suffix RL a ha'
    rcases rr_reads RL a with ⟨b, lo, hi, hR, -⟩ | ⟨z, aE, l, k1, k2, -, -⟩
    · obtain ⟨pre', hp'⟩ := XMach.act_todo_suffix xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1 hR.reading
      refine ⟨pre ++ pre', ?_⟩
      show (pre ++ pre') ++ (XMach.act xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
          ⟨chainL n r0 ++ tl, .idle⟩ a)).2.1.todo = _
      rw [List.append_assoc, hp', hp]
    · exact absurd (ha z) (by omega)

/-- While it reads, and when it gets ready, the entry the thread has in
hand and its list are an end of its first list. -/
theorem rr_pend {Z : Prop} {m n r0 : Nat} {tl : List (Id × Arith)} {W : Nat}
    (RL : ReadList Z m n r0 tl W) : ∀ a,
    (∀ a', a' < a → ¬ (Z ∧ ∃ aE l, aE ≤ a' ∧ 17 * m + 11 ≤ aE ∧ aE ≤ 17 * m + 20 ∧
      XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        ⟨chainL n r0 ++ tl, .idle⟩ aE = ⟨l, .ready [2] [0, n + 4] .zero .add⟩)) →
    ∃ pre, pre ++ (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
      ⟨chainL n r0 ++ tl, .idle⟩ a).pend = chainL n r0 ++ tl
  | 0, _ => ⟨[], rfl⟩
  | a + 1, h => by
    obtain ⟨pre, hp⟩ := rr_pend RL a (fun a' ha' => h a' (by omega))
    rcases rr_reads RL a with ⟨b, lo, hi, hR, -⟩ | hE
    · obtain ⟨pre', hp'⟩ := XMach.act_pend xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1 hR.reading
      refine ⟨pre ++ pre', ?_⟩
      show (pre ++ pre') ++ (XMach.act xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
          ⟨chainL n r0 ++ tl, .idle⟩ a)).2.1.pend = _
      rw [List.append_assoc, hp', hp]
    · exact absurd hE (h a (Nat.lt_succ_self a))

theorem soloWork_succ (m n : Nat) : soloWork (m + 1) n = 22 * (m + 1) + 3 * n + 13 := by
  unfold soloWork
  rw [ite_neg' (by omega)]

/-- The list of the thread numbered `t + 1` on the net for `(m + 1) + n`. -/
theorem turn_list (m n t : Nat) (ht : t ≤ m) :
    (sum (m + 1) n).agents.drop (t + 1) ++ (sum (m + 1) n).agents.take (t + 1) =
      chainL n (m - t) ++ (sndBase n ++ (chainL n (m - t + (t + 1))).take (t + 1)) := by
  have e : m + 1 = m - t + (t + 1) := by omega
  rw [sum_agents]
  show (chainL n (m + 1) ++ sndBase n).drop (t + 1) ++
    (chainL n (m + 1) ++ sndBase n).take (t + 1) = _
  rw [e]
  exact chain_turn n (m - t) (t + 1) (sndBase n)

/-- Each of the `k` threads after the first has a list that can be
read. -/
theorem turn_readList (m n k : Nat) (hm : k + 3 ≤ m) (hk : 20 * k ≤ 3 * m + 3 * n + 22)
    {T : XThread Arith}
    (hT : T ∈ (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)) :
    ∃ t, t < k ∧
      T = ⟨chainL n (m - t) ++
        (sndBase n ++ (chainL n (m - t + (t + 1))).take (t + 1)), .idle⟩ ∧
      ReadList True m n (m - t) (sndBase n ++ (chainL n (m - t + (t + 1))).take (t + 1))
        (m + 3 * n + 12 + 3 * (t + 1)) ∧
      (sum (m + 1) n).agents.drop (t + 1) ++ (sum (m + 1) n).agents.take (t + 1) =
        chainL n (m - t) ++ (sndBase n ++ (chainL n (m - t + (t + 1))).take (t + 1)) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT
  have ht' := List.mem_range.1 ht
  have el := turn_list m n t (by omega)
  exact ⟨t, ht', by rw [el], readList_turn m n t (by omega) (by omega) (.inl trivial), el⟩

/-- **Each of the `k` threads after the first only reads, to the end**,
when the second argument is short or long: an action of it at any moment
of the run of the first thread leaves the memory as it is and makes no
claim, and it is at rest from its `4 * m + 3 * n + 15`-th action on.  With
a short second argument it passes the zero of the first argument before
the segment from there to the last adder is written; with a long one it
finds that zero gone, or finds it and then the last adder gone.  The count
of its actions is exact up to one, so the two cases leave out about
`k + 3` values of `n` only. -/
theorem turn_quiet (m n k : Nat) (hm : k + 3 ≤ m) (hk : 20 * k ≤ 3 * m + 3 * n + 22)
    (hn : 48 * n ≤ 221 * m + 61 ∨ 221 * m + 51 * k + 217 ≤ 48 * n) {T : XThread Arith}
    (hT : T ∈ (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)) (a : Nat) :
    (XMach.act xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).1 =
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1 ∧
    (XMach.act xsys
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).2.2 = 0 ∧
    (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a ≠
      ⟨[], .idle⟩ → a < 4 * m + 3 * n + 15) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT
  have ht' := List.mem_range.1 ht
  rw [turn_list m n t (by omega)]
  exact rr_quiet (Z := False) (readList_turn m n t (by omega) (by omega) (.inr (by omega))) a
    (fun h => h.1.elim)

/-- **Threads in turn add in linear work.**  On the net for `(m + 1) + n`
take `k + 1` threads that act in turn, with `k + 3 ≤ m` and
`20 * k ≤ 3 * m + 3 * n + 22`, and a second argument that is short,
`48 * n ≤ 221 * m + 61`, or long, `221 * m + 51 * k + 217 ≤ 48 * n`.  They
never do more than the work of one thread alone and `4 * m + 3 * n + 15`
more for each of the `k` others: those make no claim and change nothing;
each reads the agents of its list once and comes to rest.  And they do no
less than one thread alone.  The sizes left out are those where a thread
can find the zero of the first argument and the last adder both in memory
with the segment between them written, and so take them. -/
theorem threads_round_robin (m n k : Nat) (hm : k + 3 ≤ m)
    (hk : 20 * k ≤ 3 * m + 3 * n + 22)
    (hn : 48 * n ≤ 221 * m + 61 ∨ 221 * m + 51 * k + 217 ≤ 48 * n) :
    (∀ i, (XMach.init (sum (m + 1) n) (k + 1)).work xsys (fun i => i % (k + 1)) i ≤
      soloWork (m + 1) n + k * (4 * m + 3 * n + 15)) ∧
    ∀ i, (k + 1) * soloWork (m + 1) n ≤ i →
      soloWork (m + 1) n ≤
        (XMach.init (sum (m + 1) n) (k + 1)).work xsys (fun i => i % (k + 1)) i := by
  rw [XMach.init_succ]
  have hl : ((List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)).length = k := by
    rw [List.length_map, List.length_range]
  have hq := fun (T : XThread Arith)
      (hT : T ∈ (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
        (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)) (a : Nat) =>
    turn_quiet m n k hm hk hn hT a
  constructor
  · intro i
    have h := XMach.work_readers (xs := xsys) (X := sum (m + 1) n)
      (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩)
      (Ts := (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
        (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith))
      (B := 4 * m + 3 * n + 15) (fun T hT a => ⟨(hq T hT a).1, (hq T hT a).2.1⟩)
      (fun T hT a => (hq T hT a).2.2) i
    rw [hl] at h
    have h1 := solo_work_all (m + 1) n i
    rw [XMach.init_one] at h1
    omega
  · intro i hi
    have h := XMach.work_readers_ge (xs := xsys) (X := sum (m + 1) n)
      (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩)
      (Ts := (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
        (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith))
      (fun T hT a => ⟨(hq T hT a).1, (hq T hT a).2.1⟩) (soloWork (m + 1) n)
    rw [hl] at h
    have h1 := (solo_work (m + 1) n).2.1
    rw [XMach.init_one] at h1
    have h2 := XMach.work_mono (xs := xsys) (fun i => i % (k + 1))
      (⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ ::
        (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
          (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)⟩ : XMach Arith) hi
    omega

/-- **And they come to rest**: when each thread has had the number of
actions that one thread needs alone, the first has finished the addition
and the others have read their lists. -/
theorem threads_rest (m n k : Nat) (hm : k + 3 ≤ m) (hk : 20 * k ≤ 3 * m + 3 * n + 22)
    (hn : 48 * n ≤ 221 * m + 61 ∨ 221 * m + 51 * k + 217 ≤ 48 * n) :
    ((XMach.init (sum (m + 1) n) (k + 1)).trace xsys (fun i => i % (k + 1))
      ((k + 1) * soloWork (m + 1) n)).1.resting = true := by
  rw [XMach.init_succ]
  have hl : ((List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)).length = k := by
    rw [List.length_map, List.length_range]
  have tr := XMach.trace_readers (xs := xsys) (X := sum (m + 1) n)
    (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩)
    (Ts := (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith))
    (A := soloWork (m + 1) n)
    (fun T hT a _ => by
      have h := turn_quiet m n k hm hk hn hT a
      exact ⟨h.1, h.2.1⟩) (soloWork (m + 1) n) (Nat.le_refl _)
  rw [hl] at tr
  rw [tr]
  obtain ⟨Xf, c, r⟩ := solo_run (m + 1) n
  have e1 := r.works.solo.1
  show (((XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
      (soloWork (m + 1) n)).2 :: ((List.range k).map fun t =>
        (⟨(sum (m + 1) n).agents.drop (t + 1) ++ (sum (m + 1) n).agents.take (t + 1),
          .idle⟩ : XThread Arith)).map fun T => XMach.reader xsys (sum (m + 1) n)
          ⟨(sum (m + 1) n).agents, .idle⟩ T (soloWork (m + 1) n)).all
    fun T => T.todo.isEmpty && T.st.isIdle) = true
  rw [List.all_eq_true]
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · rw [e1]
    rfl
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
    have e2 : XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T
        (soloWork (m + 1) n) = ⟨[], .idle⟩ := by
      by_cases h : XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T
          (soloWork (m + 1) n) = ⟨[], .idle⟩
      · exact h
      · have h3 := (turn_quiet m n k hm hk hn hT (soloWork (m + 1) n)).2.2 h
        have e := soloWork_succ m n
        omega
    rw [e2]
    rfl

/-- **Threads in turn add in linear work, whatever the second argument.**
On the net for `(m + 1) + n` take `k + 1` threads, with `k + 3 ≤ m` and
`20 * k ≤ 3 * m + 3 * n + 22`.  Let them act in turn for the first
`(k + 1) * (17 * m - 1)` actions, and in any order after that.  Then at
most `116 * m + 33 * n + 267` and `48 * m + 15 * n + 85` for each of the
`k` others of their actions are not rests.  Until then the others have
only read, and the first has made all its claims but two; from then on the
measure of the general bound pays for a pass of the first thread, two for
each other, and two claims. -/
theorem threads_any_second (m n k : Nat) (hm : k + 3 ≤ m)
    (hk : 20 * k ≤ 3 * m + 3 * n + 22) (σ : Nat → Nat)
        (hσ : ∀ j, j < (k + 1) * (17 * m - 1) → σ j = j % (k + 1)) (i : Nat) :
    (XMach.init (sum (m + 1) n) (k + 1)).work xsys σ i ≤
      116 * m + 33 * n + 267 + k * (48 * m + 15 * n + 85) := by
  have g := good_sum (m + 1) n
  obtain ⟨N', hs, hn', -⟩ := add_correct g.config
  have ha := sum_agents_length_le (m + 1) n
  have hw := sum_wires_length_le (m + 1) n
  have hl : ((List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)).length = k := by
    rw [List.length_map, List.length_range]
  have cg : (XMach.init (sum (m + 1) n) (k + 1)).trace xsys σ ((k + 1) * (17 * m - 1)) =
      (XMach.init (sum (m + 1) n) (k + 1)).trace xsys (fun i => i % (k + 1))
        ((k + 1) * (17 * m - 1)) :=
    XMach.trace_congr xsys _ _ fun j hj => hσ j hj
  obtain ⟨Xm, w, -⟩ := solo_steady m n (m - 1) (n + 4) (by omega) (by omega)
  rw [show 16 + 17 * (m - 1) = 17 * m - 1 by omega, show 1 + (m - 1) = m by omega] at w
  have es := w.solo.1
  have tr1 := w.trace_at [⟨(sum (m + 1) n).agents, .idle⟩] 0 rfl
  have tr := XMach.trace_readers (xs := xsys) (X := sum (m + 1) n)
    (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩)
    (Ts := (List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith))
    (A := 17 * m - 1)
    (fun T hT a ha => by
      obtain ⟨t, ht, rfl, RL, -⟩ := turn_readList m n k hm hk hT
      have h := rr_quiet RL a (fun h => by
        obtain ⟨-, aE, -, h1, h2, -, -⟩ := h
        omega)
      exact ⟨h.1, h.2.1⟩) (17 * m - 1) (Nat.le_refl _)
  rw [hl, es, tr1] at tr
  have hst : ((XMach.init (sum (m + 1) n) (k + 1)).trace xsys σ
      ((k + 1) * (17 * m - 1))).1 = ⟨Xm, ⟨Xm.agents, .idle⟩ ::
        ((List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
          (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)).map
          fun T => XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T
            (17 * m - 1)⟩ := by
    rw [cg, XMach.init_succ, tr]
  have hcl : ((XMach.init (sum (m + 1) n) (k + 1)).trace xsys σ
      ((k + 1) * (17 * m - 1))).2 = m := by
    rw [cg, XMach.init_succ, tr]
  have h := XMach.work_after_reading (xs := xsys) g.ok.1 (sum_nodup (m + 1) n) (nt := k + 1)
    (Nat.succ_pos k) xsys_bounded hs hn' σ hst hcl
    (fun R hRm => by
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hRm
      obtain ⟨t, ht, rfl, RL, el⟩ := turn_readList m n k hm hk hT
      obtain ⟨pre, hp⟩ := rr_suffix RL (17 * m - 1) (fun _ => by omega)
      rcases rr_reads RL (17 * m - 1) with ⟨b, lo, hi, hR, -⟩ | ⟨-, aE, -, h1, h2, -, -⟩
      · exact ⟨hR.reading, pre, t + 1, by rw [hp, el]⟩
      · exact absurd h1 (by omega)) i
  rw [List.length_map, hl, show m + 1 + 1 - m = 2 by omega] at h
  have e1 : (k + 1) * (17 * m - 1) = k * (17 * m - 1) + (17 * m - 1) := Nat.succ_mul _ _
  have e2 : k * (7 * (sum (m + 1) n).agents.length +
      ((sum (m + 1) n).wires.length + 8 * (m + 1 + 1)) +
      ((sum (m + 1) n).wires.length + 8 * (m + 1 + 1)) + 6) ≤
      k * (31 * m + 15 * n + 86) := Nat.mul_le_mul_left k (by omega)
  have e3 : k * (17 * m - 1) + k * (31 * m + 15 * n + 86) =
      k * (48 * m + 15 * n + 85) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

/-- Two threads: at most one thread's work and `4 * m + 3 * n + 15`
more. -/
theorem two_threads_round_robin (m n : Nat) (hm : 4 ≤ m) (hn : 3 * n + 16 ≤ 13 * m) :
    (∀ i, (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤
      soloWork (m + 1) n + (4 * m + 3 * n + 15)) ∧
    ∀ i, 2 * soloWork (m + 1) n ≤ i →
      soloWork (m + 1) n ≤ (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i := by
  have h := threads_round_robin m n 1 (by omega) (by omega) (.inl (by omega))
  refine ⟨fun i => ?_, fun i hi => h.2 i (by omega)⟩
  have h1 := h.1 i
  show (XMach.init (sum (m + 1) n) (1 + 1)).work xsys (fun i => i % (1 + 1)) i ≤ _
  omega

/-- In numbers: at most `26 * m + 6 * n + 50` actions that are not
rests. -/
theorem two_threads_linear (m n : Nat) (hm : 4 ≤ m) (hn : 3 * n + 16 ≤ 13 * m) (i : Nat) :
    (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤ 26 * m + 6 * n + 50 := by
  have h := (two_threads_round_robin m n hm hn).1 i
  have e := soloWork_succ m n
  omega

theorem two_threads_rest (m n : Nat) (hm : 4 ≤ m) (hn : 3 * n + 16 ≤ 13 * m) :
    ((XMach.init (sum (m + 1) n) 2).trace xsys (fun i => i % 2)
      (2 * soloWork (m + 1) n)).1.resting = true :=
  threads_rest m n 1 (by omega) (by omega) (.inl (by omega))

/-- **The order of the actions decides between linear and quadratic.**  On
the same net, with the same two threads, acting in turn costs less than
the schedule where the threads claim in turn, as soon as the first
argument has eleven successors. -/
theorem round_robin_beats_turns (m n : Nat) (hm : 9 ≤ m) (hn : n ≤ m) (i : Nat) :
    (XMach.init (sum (m + 2) n) 2).work xsys (fun i => i % 2) i <
      (XMach.init (sum (m + 2) n) 2).work xsys (altSched m) (2 * (m * m) + 21 * m + 33) := by
  have h : (XMach.init (sum (m + 2) n) 2).work xsys (fun i => i % 2) i ≤
      26 * (m + 1) + 6 * n + 50 := two_threads_linear (m + 1) n (by omega) (by omega) i
  have hq := (two_threads_quadratic m n).1
  have hmm := Nat.mul_le_mul_right m hm
  omega

theorem Checks.Arith.TwoThreads.c1
    (i : Nat) : (XMach.init (sum 101 100) 2).work xsys (fun i => i % 2) i ≤ 3250 :=
  two_threads_linear 100 100 (by decide) (by decide) i

/-- Two threads, whatever the second argument: at most
`164 * m + 48 * n + 352`, with any schedule after the first `34 * m - 2`
actions. -/
theorem two_threads_any_second (m n : Nat) (hm : 4 ≤ m) (σ : Nat → Nat)
    (hσ : ∀ j, j < 34 * m - 2 → σ j = j % 2) (i : Nat) :
    (XMach.init (sum (m + 1) n) 2).work xsys σ i ≤ 164 * m + 48 * n + 352 := by
  have h := threads_any_second m n 1 (by omega) (by omega) σ (fun j hj => hσ j (by omega)) i
  show (XMach.init (sum (m + 1) n) (1 + 1)).work xsys σ i ≤ _
  omega

theorem two_threads_linear_any (m n : Nat) (hm : 4 ≤ m) (i : Nat) :
    (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤ 164 * m + 48 * n + 352 :=
  two_threads_any_second m n hm (fun i => i % 2) (fun _ _ => rfl) i

/-- Three threads: at most one thread's work and `4 * m + 3 * n + 15` more
for each of the two others. -/
theorem three_threads_round_robin (m n : Nat) (hm : 6 ≤ m) (hn : 3 * n + 16 ≤ 13 * m) :
    (∀ i, (XMach.init (sum (m + 1) n) 3).work xsys (fun i => i % 3) i ≤
      soloWork (m + 1) n + 2 * (4 * m + 3 * n + 15)) ∧
    ∀ i, 3 * soloWork (m + 1) n ≤ i →
      soloWork (m + 1) n ≤ (XMach.init (sum (m + 1) n) 3).work xsys (fun i => i % 3) i := by
  have h := threads_round_robin m n 2 (by omega) (by omega) (.inl (by omega))
  exact ⟨fun i => h.1 i, fun i hi => h.2 i (by omega)⟩

theorem three_threads_linear (m n : Nat) (hm : 6 ≤ m) (hn : 3 * n + 16 ≤ 13 * m) (i : Nat) :
    (XMach.init (sum (m + 1) n) 3).work xsys (fun i => i % 3) i ≤ 30 * m + 9 * n + 65 := by
  have h := (three_threads_round_robin m n hm hn).1 i
  have e := soloWork_succ m n
  omega

/-- Three threads, whatever the second argument: at most
`212 * m + 63 * n + 437`, with any schedule after the first `51 * m - 3`
actions. -/
theorem three_threads_any_second (m n : Nat) (hm : 6 ≤ m) (σ : Nat → Nat)
    (hσ : ∀ j, j < 51 * m - 3 → σ j = j % 3) (i : Nat) :
    (XMach.init (sum (m + 1) n) 3).work xsys σ i ≤ 212 * m + 63 * n + 437 := by
  have h := threads_any_second m n 2 (by omega) (by omega) σ (fun j hj => hσ j (by omega)) i
  show (XMach.init (sum (m + 1) n) (2 + 1)).work xsys σ i ≤ _
  omega

theorem three_threads_linear_any (m n : Nat) (hm : 6 ≤ m) (i : Nat) :
    (XMach.init (sum (m + 1) n) 3).work xsys (fun i => i % 3) i ≤ 212 * m + 63 * n + 437 :=
  three_threads_any_second m n hm (fun i => i % 3) (fun _ _ => rfl) i

/-- Ten threads add `400` and `100` in turn in at most 26,312 actions that
are not rests; one thread needs 9,113. -/
theorem Checks.Arith.TwoThreads.c2
    (i : Nat) : (XMach.init (sum 400 100) 10).work xsys (fun i => i % 10) i ≤ 26312 :=
  Nat.le_trans ((threads_round_robin 399 100 9 (by decide) (by decide) (.inl (by decide))).1 i)
    (by decide)

/-- With a long second argument few successors are needed: ten threads add
`13` and `44` in turn in at most 2,186 actions that are not rests; one
thread needs 431. -/
theorem Checks.Arith.TwoThreads.c3
    (i : Nat) : (XMach.init (sum 13 44) 10).work xsys (fun i => i % 10) i ≤ 2186 :=
  Nat.le_trans ((threads_round_robin 12 44 9 (by decide) (by decide) (.inl (by decide))).1 i)
    (by decide)

/-- Two threads and a long second argument: for `14 * m + 21 ≤ 3 * n` the
same bound as for a short one. -/
theorem two_threads_long (m n : Nat) (hm : 4 ≤ m) (hn : 14 * m + 21 ≤ 3 * n) (i : Nat) :
    (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤ 26 * m + 6 * n + 50 := by
  have h := (threads_round_robin m n 1 (by omega) (by omega) (.inr (by omega))).1 i
  have e := soloWork_succ m n
  have h' : (XMach.init (sum (m + 1) n) (1 + 1)).work xsys (fun i => i % (1 + 1)) i ≤
      soloWork (m + 1) n + 1 * (4 * m + 3 * n + 15) := h
  show (XMach.init (sum (m + 1) n) (1 + 1)).work xsys (fun i => i % (1 + 1)) i ≤ _
  omega

/-- **Two threads, all second arguments but five at most for each first
one**: the bound `26 * m + 6 * n + 50` holds unless `48 * n` lies strictly
between `221 * m + 61` and `221 * m + 268`. -/
theorem two_threads_narrow (m n : Nat) (hm : 4 ≤ m)
    (hn : 48 * n ≤ 221 * m + 61 ∨ 221 * m + 268 ≤ 48 * n) (i : Nat) :
    (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤ 26 * m + 6 * n + 50 := by
  have h := (threads_round_robin m n 1 (by omega) (by omega) (by omega)).1 i
  have e := soloWork_succ m n
  have h' : (XMach.init (sum (m + 1) n) (1 + 1)).work xsys (fun i => i % (1 + 1)) i ≤
      soloWork (m + 1) n + 1 * (4 * m + 3 * n + 15) := h
  show (XMach.init (sum (m + 1) n) (1 + 1)).work xsys (fun i => i % (1 + 1)) i ≤ _
  omega

/-- With a long second argument: three threads add `23` and `120` in turn
in at most 1,805 actions that are not rests; one thread needs 879. -/
theorem Checks.Arith.TwoThreads.c4
    (i : Nat) : (XMach.init (sum 23 120) 3).work xsys (fun i => i % 3) i ≤ 1805 :=
  Nat.le_trans ((threads_round_robin 22 120 2 (by decide) (by decide) (.inr (by decide))).1 i)
    (by decide)

/-- At the edge of the short case: ten threads add `13` and `56` in turn
in at most 2,546 actions that are not rests; one thread needs 467. -/
theorem Checks.Arith.TwoThreads.c5
    (i : Nat) : (XMach.init (sum 13 56) 10).work xsys (fun i => i % 10) i ≤ 2546 :=
  Nat.le_trans ((threads_round_robin 12 56 9 (by decide) (by decide) (.inl (by decide))).1 i)
    (by decide)

/-- Two threads on `21 + 93` and on `21 + 98`, on either side of the four
second arguments left out. -/
theorem Checks.Arith.TwoThreads.c6
    (i : Nat) : (XMach.init (sum 21 93) 2).work xsys (fun i => i % 2) i ≤ 1128 :=
  Nat.le_trans (two_threads_narrow 20 93 (by decide) (.inl (by decide)) i) (by decide)

theorem Checks.Arith.TwoThreads.c7
    (i : Nat) : (XMach.init (sum 21 98) 2).work xsys (fun i => i % 2) i ≤ 1158 :=
  Nat.le_trans (two_threads_narrow 20 98 (by decide) (.inr (by decide)) i) (by decide)

/-- **Two threads in turn: the second only reads, or gets ready to take the
last pair.**  On the net for `(m + 1) + n`, with `m` from four on and any
second argument: either the second thread never does anything but read,
and the work is that of one thread and at most `4 * m + 3 * n + 15` more;
or there is a moment, when each thread has made `aE` actions with `aE`
from `17 * m + 11` to `17 * m + 20`, at which the memory and the first
thread are exactly those of one thread alone and the second thread is
ready to take the zero of the first argument and then the last adder,
with the zero of the second argument and the top successor left in its
list. -/
theorem two_threads_entry (m n : Nat) (hm : 4 ≤ m) :
    (∀ i, (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤
      soloWork (m + 1) n + (4 * m + 3 * n + 15)) ∨
    ∃ aE c, 17 * m + 11 ≤ aE ∧ aE ≤ 17 * m + 20 ∧
      (XMach.init (sum (m + 1) n) 2).trace xsys (fun i => i % 2) (2 * aE) =
        (⟨(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE).1,
          [(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE).2,
            ⟨[([3], .zero), ([n + 3 + m + 1], .succ)],
              .ready [2] [0, n + 4] .zero .add⟩]⟩, c) := by
  have RL : ReadList True m n (m - 0)
      (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1))
      (m + 3 * n + 12 + 3 * (0 + 1)) :=
    readList_turn m n 0 (by omega) (by omega) (.inl trivial)
  have hinit : XMach.init (sum (m + 1) n) 2 = ⟨sum (m + 1) n,
      [⟨(sum (m + 1) n).agents, .idle⟩, ⟨chainL n (m - 0) ++
          (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1)), .idle⟩]⟩ := by
    rw [show (2 : Nat) = 1 + 1 from rfl, XMach.init_succ, ← turn_list m n 0 (by omega)]
    rfl
  rw [hinit]
  by_cases hE : ∃ a l, XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
      ⟨chainL n (m - 0) ++ (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1)), .idle⟩ a =
      ⟨l, .ready [2] [0, n + 4] .zero .add⟩
  · right
    obtain ⟨a0, l0, h0⟩ := hE
    obtain ⟨aE, ⟨l, hl⟩, hmin⟩ := least_of_exists
      (P := fun a => ∃ l, XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
      ⟨chainL n (m - 0) ++ (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1)), .idle⟩ a =
        ⟨l, .ready [2] [0, n + 4] .zero .add⟩) a0 ⟨a0, Nat.le_refl _, l0, h0⟩
    have hb : 17 * m + 11 ≤ aE ∧ aE ≤ 17 * m + 20 := by
      rcases rr_reads RL aE with ⟨b, lo, hi, hR, -⟩ | ⟨-, aE', l', k1, k2, k3, k4⟩
      · rw [hl] at hR
        cases hR
      · have e : aE' = aE := by
          by_cases h : aE' < aE
          · exact absurd ⟨l', k4⟩ (hmin aE' h)
          · omega
        omega
    have tr := XMach.trace_readers (xs := xsys) (X := sum (m + 1) n)
      (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩)
      (Ts := [⟨chainL n (m - 0) ++ (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1)),
          .idle⟩])
      (A := aE)
      (fun T hT a ha => by
        rw [List.mem_singleton.1 hT]
        have h := rr_quiet RL a (fun h => by
          obtain ⟨-, aE', l', k1, -, -, k4⟩ := h
          exact hmin aE' (by omega) ⟨l', k4⟩)
        exact ⟨h.1, h.2.1⟩) aE (Nat.le_refl _)
    obtain ⟨pre, hp⟩ := rr_pend RL aE (fun a' ha' h => by
      obtain ⟨-, aE', l', k1, -, -, k4⟩ := h
      exact hmin aE' (by omega) ⟨l', k4⟩)
    rw [hl] at hp
    have hp' : pre ++ ([2], Arith.zero) :: l =
        (chainL n (m - 0) ++ (sndL n ++ [([1], Arith.add)])) ++
          (([2], Arith.zero) :: ([([3], Arith.zero)] ++
            (chainL n (m - 0 + (0 + 1))).take (0 + 1))) := by
      rw [← append_split3]
      exact hp
    have hl2 : l = [([3], Arith.zero)] ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1) :=
      split_unique (fun hm => by
        rcases List.mem_append.1 hm with h | h
        · obtain ⟨-, j, j1, -, j3⟩ := mem_chainL h
          have j3' : ([2] : Id) = [j] := j3
          injection j3' with e1
          omega
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨-, j, j1, -, j3⟩ := mem_sndL h
            have j3' : ([2] : Id) = [j] := j3
            injection j3' with e1
            omega
          · rcases List.mem_cons.1 h with h | h
            · injection h with h1
              injection h1 with h2
              exact absurd h2 (by decide)
            · cases h) (fun hm => by
        rcases List.mem_cons.1 hm with h | h
        · injection h with h1
          injection h1 with h2
          exact absurd h2 (by decide)
        · obtain ⟨j, j1, -, j3⟩ := mem_chain_take n (m - 0) (0 + 1) h
          have j3' : ([2] : Id) = [j] := j3
          injection j3' with e1
          omega) hp'
    subst hl2
    have hl' : XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
      ⟨chainL n (m - 0) ++ (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1)), .idle⟩ aE =
        ⟨[([3], .zero), ([n + 3 + m + 1], .succ)], .ready [2] [0, n + 4] .zero .add⟩ := hl
    exact ⟨aE, _, hb.1, hb.2, by
      rw [← hl']
      exact tr⟩
  · left
    intro i
    have hq := fun a => rr_quiet RL a (fun h => by
      obtain ⟨-, aE, l, -, -, -, k4⟩ := h
      exact hE ⟨aE, l, k4⟩)
    have h := XMach.work_readers (xs := xsys) (X := sum (m + 1) n)
      (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩)
      (Ts := [⟨chainL n (m - 0) ++ (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1)),
          .idle⟩])
      (B := 4 * m + 3 * n + 15)
      (fun T hT a => by
        rw [List.mem_singleton.1 hT]
        exact ⟨(hq a).1, (hq a).2.1⟩)
      (fun T hT a => by
        rw [List.mem_singleton.1 hT]
        exact (hq a).2.2) i
    have h1 := solo_work_all (m + 1) n i
    rw [XMach.init_one] at h1
    have h' : (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩,
        ⟨chainL n (m - 0) ++ (sndBase n ++ (chainL n (m - 0 + (0 + 1))).take (0 + 1)), .idle⟩]⟩ :
        XMach Arith).work xsys (fun i => i % 2) i ≤
        (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩]⟩ : XMach Arith).work xsys
          (fun _ => 0) i + 1 * (4 * m + 3 * n + 15) := h
    omega

theorem newAgents_zero_swap (z a : Id) : addZero.swap.toX.newAgents z a = [] := rfl

theorem newLinks_zero_swap (z a : Id) : addZero.swap.toX.newLinks ar z a .zero .add =
    [((a, 1), (a, 2)), ((a, 2), (a, 1))] := rfl

/-- **A thread that is ready takes the zero of the first argument and then
the last adder, writes the two segments and starts over**, in five actions,
whatever the first thread does in between, provided the zero is still in
memory after the first thread's next action and the adder after the one
that follows. -/
theorem race_reader_wins {n : Nat} {Y0 Y0' Y1' Y2' Y3' Y4' : XNet Arith}
    {F0 F1 F2 F3 F4 F5 : XThread Arith} {c0 c1 c2 c3 c4 : Nat} {l : List (Id × Arith)}
    (f0 : XMach.act xsys Y0 F0 = (Y0', F1, c0))
    (hZ : assoc [2] Y0'.agents = some .zero)
    (f1 : XMach.act xsys (Y0'.takeAgent [2]) F1 = (Y1', F2, c1))
    (hA : assoc [0, n + 4] Y1'.agents = some .add)
    (f2 : XMach.act xsys (Y1'.takeAgent [0, n + 4]) F2 = (Y2', F3, c2))
    (f3 : XMach.act xsys (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2)) F3 = (Y3', F4, c3))
    (f4 : XMach.act xsys (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1)) F4 = (Y4', F5, c4)) :
    Sweeps xsys ⟨Y0, [F0, ⟨l, .ready [2] [0, n + 4] .zero .add⟩]⟩
      ⟨Y4', [F5, ⟨Y4'.agents, .idle⟩]⟩ 5 := by
  have r0 : XMach.act xsys Y0' ⟨l, .ready [2] [0, n + 4] .zero .add⟩ =
      (Y0'.takeAgent [2], ⟨l, .half [2] [0, n + 4] .zero .add⟩, 0) := XMach.act_ready hZ
  have r1 : XMach.act xsys Y1' ⟨l, .half [2] [0, n + 4] .zero .add⟩ =
      (Y1'.takeAgent [0, n + 4], ⟨l, .write []
        [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩, 1) :=
    XMach.act_half (R := addZero.swap.toX) (by
      rw [ite_pos' (show assoc [0, n + 4] Y1'.agents = some Arith.add ∧
        ([2] : Id) ≠ [0, n + 4] from ⟨hA, by ports_differ⟩)]
      rfl)
  have r2 : XMach.act xsys Y2' ⟨l, .write []
      [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2),
        ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩, 0) := rfl
  have r3 : XMach.act xsys Y3' ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1), ⟨l, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys Y4' ⟨l, .write [] []⟩ = (Y4', ⟨Y4'.agents, .idle⟩, 0) := rfl
  exact .step f0 r0 (.step f1 r1 (.step f2 r2 (.step f3 r3 (.step f4 r4 (.refl _)))))

/-- **A memory with the agents the rounds leave, and the segments of the
memory before the last round and those the last round writes, is one the
rounds leave**: the order in which the segments were written is of no
account. -/
theorem final_of {m n : Nat} {X16 Y : XNet Arith}
    (H : Hist n (sum (m + 1) n) X16 (n + 3 + m + 1) 0 m)
    (hA : Y.agents = resL (n + 3) m ++ (sndL n ++ [([3], .zero)]))
    (hW : ∀ e, e ∈ Y.wires ↔ e ∈ X16.wires ∨ e ∈ linksZ (n + 3 + 1)) :
    Final n (sum (m + 1) n) Y (n + 3 + m + 1) m := by
  refine ⟨rfl, hA, fun e => ?_⟩
  rw [hW, H.wires]
  constructor
  · rintro ((h | h | ⟨t, t1, t2, h⟩) | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨t, by omega, t2, h⟩))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | ⟨t, t1, t2, h⟩ | h)
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr ⟨t, by omega, t2, h⟩))
    · exact .inr h

/-- The zero of the first argument is not in the memory the rounds leave. -/
theorem Final.no_two {n : Nat} {X0 X : XNet Arith} {T d : Nat} (F : Final n X0 X T d) :
    assoc [2] X.agents = none := by
  rw [F.agents]
  refine assoc_none_of_forall fun e he e' => ?_
  rcases List.mem_append.1 he with h | h
  · exact res_ne_single h 2 e'
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨-, j, h2, -, h3⟩ := mem_sndL h
      rw [h3] at e'
      injection e' with e1
      omega
    · rcases List.mem_cons.1 h with rfl | h
      · injection e' with e1
        exact absurd e1 (by decide)
      · cases h

/-- The last pass from any successor of the result on, as a run that only
reads. -/
theorem Final.pass_from {n : Nat} {X0 X : XNet Arith} {T d : Nat} (F : Final n X0 X T d)
    (S : Snd n X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    (d' h : Nat) (hh : n + 3 ≤ h) (hT : h + d' + 1 = T)
    (hm : ∀ e ∈ resL h d', e ∈ X.agents) :
    Stays xsys X ⟨resL h d' ++ (sndL n ++ [([3], .zero)]), .idle⟩ ⟨[], .idle⟩
      (4 * (d' + 1) + (d + 3 + 1 + 2) + 3 * n) := by
  obtain ⟨γ, low, hsplit, hlen, hlow⟩ := snd_split n
  have hmem : ∀ e ∈ ([n + 3], γ) :: low, e ∈ X.agents := fun e he => by
    rw [F.agents, hsplit]
    exact List.mem_append_right _ he
  rw [hsplit]
  have w₁ := F.pass_res_stays S hfr (([n + 3], γ) :: low) d' h hh hT hm
  have h₁ : assoc [n + 3] X.agents = some γ := F.agent (hmem _ List.mem_cons_self)
  have h₂ : assoc (([n + 3], 0) : Port) X.wires = some ([1], 1) :=
    assoc_eq_of_unique ((F.top_snd S _).2 rfl) (fun q' hq => (F.top_snd S q').1 hq)
  have w₂ : Stays xsys X ⟨([n + 3], γ) :: low, .idle⟩ ⟨low, .idle⟩ (d + 3 + 1 + 2) :=
    Stays.dead (xs := xsys) (e := ([n + 3], γ)) _ h₁ h₂ (F.dead_top S hfr)
  have w₃ := Stays.inert_pass (xs := xsys) (X := X) [] low (fun e he => by
    obtain ⟨j, h1, h2, h3⟩ := hlow e he
    exact F.inert S (hmem e (List.mem_cons_of_mem _ he)) h1 h2 h3)
  rw [List.append_nil, hlen] at w₃
  exact (w₁.trans w₂).trans w₃

/-- The same pass over a list that still has the zero of the first
argument: one action more, to find it gone. -/
theorem Final.pass_from_two {n' : Nat} {X0 X : XNet Arith} {T d : Nat}
    (F : Final (n' + 1) X0 X T d) (S : Snd (n' + 1) X0)
    (hfr : ∀ (i : Id) (k : Nat) (q : Port), (((i, k), q) : Port × Port) ∈ X0.wires →
      ∃ j, i = [j])
    (d' h : Nat) (hh : n' + 1 + 3 ≤ h) (hT : h + d' + 1 = T)
    (hm : ∀ e ∈ resL h d', e ∈ X.agents) :
    Stays xsys X ⟨resL h d' ++ tailA (n' + 1), .idle⟩ ⟨[], .idle⟩
      (4 * (d' + 1) + (d + 3 + 1 + 2) + 3 * n' + 1 + 3) := by
  have hsnd : ∀ e ∈ sndL (n' + 1) ++ [([3], Arith.zero)], e ∈ X.agents := fun e he => by
    rw [F.agents]
    exact List.mem_append_right _ he
  have w₁ := F.pass_res_stays S hfr (tailA (n' + 1)) d' h hh hT hm
  have h₁ : assoc [n' + 1 + 3] X.agents = some .succ :=
    F.agent (e := ([n' + 1 + 3], Arith.succ)) (hsnd _ (List.mem_append_left _ List.mem_cons_self))
  have h₂ : assoc (([n' + 1 + 3], 0) : Port) X.wires = some ([1], 1) :=
    assoc_eq_of_unique ((F.top_snd S _).2 rfl) (fun q' hq => (F.top_snd S q').1 hq)
  have w₂ : Stays xsys X
      ⟨([n' + 1 + 3], .succ) :: (sndL n' ++ [([2], .zero), ([3], .zero)]), .idle⟩
      ⟨sndL n' ++ [([2], .zero), ([3], .zero)], .idle⟩ (d + 3 + 1 + 2) :=
    Stays.dead (xs := xsys) (e := ([n' + 1 + 3], Arith.succ)) _ h₁ h₂ (F.dead_top S hfr)
  have w₃ := Stays.inert_pass (xs := xsys) (X := X) [([2], Arith.zero), ([3], .zero)] (sndL n')
    (fun e he => by
      obtain ⟨-, j, h1, h2, h3⟩ := mem_sndL he
      exact F.inert S (hsnd e (List.mem_append_left _ (List.mem_cons_of_mem _ he))) (by omega)
        (by omega) h3)
  rw [sndL_length] at w₃
  have w₄ : Stays xsys X ⟨[([2], .zero), ([3], .zero)], .idle⟩ ⟨[([3], .zero)], .idle⟩ 1 :=
    Stays.absent (xs := xsys) (e := ([2], Arith.zero)) _ (by
      show ¬ assoc [2] X.agents = some Arith.zero
      rw [F.no_two]
      exact fun h => by cases h)
  have w₅ : Stays xsys X ⟨[([3], .zero)], .idle⟩ ⟨[], .idle⟩ 3 :=
    Stays.inert (xs := xsys) [] (F.inert S (e := ([3], Arith.zero))
      (hsnd _ (List.mem_append_right _ List.mem_cons_self)) (j := 3) (by omega) (by omega) rfl)
  exact (((w₁.trans w₂).trans w₃).trans w₄).trans w₅

theorem assoc_cons_ne {A B : Type} [DecidableEq A] {p k : A} {q : B} (l : List (A × B))
    (h : p ≠ k) : assoc k ((p, q) :: l) = assoc k l := by
  show (if p = k then some q else assoc k l) = _
  rw [ite_neg' h]

theorem nextSeg_cons_ne {p c : Port} (q p' : Port) (ws : List (Port × Port)) (h : p ≠ c) :
    nextSeg ((p, q) :: ws) c p' = nextSeg ws c p' := by
  show (if p = c ∧ q ≠ p' then some q else nextSeg ws c p') = _
  rw [ite_neg' (fun h' => h h'.1)]

theorem filter_ne_comm (l : List (Id × Arith)) (a b : Id) :
    (l.filter fun e => decide (e.1 ≠ a)).filter (fun e => decide (e.1 ≠ b)) =
      (l.filter fun e => decide (e.1 ≠ b)).filter (fun e => decide (e.1 ≠ a)) := by
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext e
  exact Bool.and_comm _ _

/-- **The memory before the last round**, with what the race needs of it:
the last adder first in the list, one point away from the zero of the
first argument, and no other segment at that zero. -/
structure RaceBase (m n : Nat) (X : XNet Arith) (rest : List (Id × Arith)) : Prop where
  solo : XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (16 + 17 * m) =
    (X, ⟨X.agents, .idle⟩)
  hist : Hist n (sum (m + 1) n) X (n + 3 + m + 1) 0 m
  agents : X.agents = ([0, n + 4], .add) :: rest
  rest : rest = resL (n + 3) m ++ tailA n
  zero : assoc [2] X.agents = some .zero
  adder : assoc [0, n + 4] X.agents = some .add
  look : assoc (([0, n + 4], 0) : Port) X.wires = some ([n + 4], 1)
  seek : nextSeg X.wires ([n + 4], 1) ([0, n + 4], 0) = some ([2], 0)
  stop : nextSeg X.wires ([2], 0) ([n + 4], 1) = none

theorem race_base (m n : Nat) : ∃ X rest, RaceBase m n X rest := by
  obtain ⟨X, w, st, H⟩ := solo_hist m n m 0 (by omega)
  have st' : Steady n X (n + 3) := st
  have hz := solo_alive_snd m n (j := 2) (by omega) (by omega) (Nat.le_refl (16 + 17 * m))
    (sum_zero_agent m n)
  rw [w.solo.1] at hz
  obtain ⟨rest, hA, h₁, h₂, h₂', -, -⟩ := st'.zero_pair hz
  have hr : rest = resL (n + 3) m ++ tailA n := by
    have h := H.agents
    rw [hA] at h
    exact (List.cons.inj h).2
  exact ⟨X, rest, w.solo.1, H, hA, hr, hz, h₁, h₂, h₂',
    nextSeg_none fun q hq => (sum_two m n q).1 ((H.old 2 q).1 hq)⟩

/-- The memory once the second thread has taken the pair and written the
two segments is one the rounds leave. -/
theorem RaceBase.final {m n : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase m n X rest) {Y : XNet Arith}
    (hA : Y.agents = (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      (fun e => decide (e.1 ≠ [0, n + 4])))
    (hW : Y.wires = (([0, n + 4], 2), ([0, n + 4], 1)) ::
      (([0, n + 4], 1), ([0, n + 4], 2)) :: X.wires) :
    Final n (sum (m + 1) n) Y (n + 3 + m + 1) m := by
  refine final_of B.hist ?_ fun e => ?_
  · rw [hA, filter_ne_comm]
    exact B.hist.final.agents
  · rw [hW, show linksZ (n + 3 + 1) = [(([0, n + 4], 1), ([0, n + 4], 2)),
      (([0, n + 4], 2), ([0, n + 4], 1))] from rfl]
    constructor
    · intro h
      rcases List.mem_cons.1 h with rfl | h
      · exact .inr (List.mem_cons_of_mem _ List.mem_cons_self)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inr List.mem_cons_self
        · exact .inl h
    · rintro (h | h)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.1 h with rfl | h
          · exact List.mem_cons_self
          · cases h

/-- **The first successor of the result, in a memory the rounds leave**:
a thread passes it in four actions, and what is left of them from each
state on the way. -/
theorem Final.first_res {m' n : Nat} {Y : XNet Arith}
    (F : Final n (sum (m' + 1 + 1) n) Y (n + 3 + (m' + 1) + 1) (m' + 1))
    (rest : List (Id × Arith)) :
    assoc [0, 0, n + 3 + 2] Y.agents = some .succ ∧
    assoc (([0, 0, n + 3 + 2], 0) : Port) Y.wires = some ([0, n + 3 + 2], 2) ∧
    Stays xsys Y ⟨rest, .seek [0, 0, n + 3 + 2] .succ ([0, 0, n + 3 + 2], 0)
      ([0, n + 3 + 2], 2)⟩ ⟨rest, .idle⟩ 2 ∧
    ∃ q, XMach.act xsys Y ⟨rest, .seek [0, 0, n + 3 + 2] .succ ([0, 0, n + 3 + 2], 0)
        ([0, n + 3 + 2], 2)⟩ =
        (Y, ⟨rest, .seek [0, 0, n + 3 + 2] .succ ([0, n + 3 + 2], 2) q⟩, 0) ∧
      Stays xsys Y ⟨rest, .seek [0, 0, n + 3 + 2] .succ ([0, n + 3 + 2], 2) q⟩
        ⟨rest, .idle⟩ 1 := by
  have hfr := sum_fresh (m' + 1 + 1) n
  have h₁ : assoc [0, 0, n + 3 + 2] Y.agents = some Arith.succ :=
    F.agent (e := ([0, 0, n + 3 + 2], Arith.succ)) (by
      rw [F.agents]
      exact List.mem_append_left _ List.mem_cons_self)
  have h₂ : assoc (([0, 0, n + 3 + 2], 0) : Port) Y.wires = some ([0, n + 3 + 2], 2) :=
    assoc_eq_of_unique ((F.res_zero hfr (t := n + 3 + 1) (by omega) (by omega) _).2 rfl)
      (fun q' hq => (F.res_zero hfr (t := n + 3 + 1) (by omega) (by omega) q').1 hq)
  have hd : Y.Dead ([0, 0, n + 3 + 2], 0) ([0, n + 3 + 2], 2) 2 :=
    F.dead_two hfr (x := n + 3 + 2) (by omega) (by omega) (.inl ⟨rfl, by omega⟩)
  refine ⟨h₁, h₂, Stays.seek_dead hd, ?_⟩
  cases hd with
  | step k1 k2 hd' =>
    exact ⟨_, XMach.act_seek_next k1 k2, Stays.seek_dead hd'⟩

section RaceFacts

variable {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}

theorem RaceBase.adder1 (B : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc [0, n' + 1 + 4] (X.takeAgent [2]).agents = some .add := by
  show assoc [0, n' + 1 + 4] (X.agents.filter fun e => decide (e.1 ≠ [2])) = _
  rw [assoc_filter_ne, ite_neg' (by ports_differ)]
  exact B.adder

theorem RaceBase.zero1 (_ : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc [2] (X.takeAgent [2]).agents = none := by
  show assoc [2] (X.agents.filter fun e => decide (e.1 ≠ [2])) = none
  rw [assoc_filter_ne, ite_pos' rfl]

theorem RaceBase.zero2 (_ : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc [2] ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
  show assoc [2] ((X.agents.filter fun e => decide (e.1 ≠ [2])).filter
    fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
  rw [assoc_filter_ne, ite_neg' (by ports_differ), assoc_filter_ne, ite_pos' rfl]

theorem RaceBase.res2 (B : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc [0, 0, n' + 1 + 3 + 2] ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents =
      some .succ := by
  show assoc [0, 0, n' + 1 + 3 + 2] ((X.agents.filter fun e => decide (e.1 ≠ [2])).filter
    fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = _
  rw [assoc_filter_ne, ite_neg' (by ports_differ), assoc_filter_ne, ite_neg' (by ports_differ)]
  exact B.hist.agent_res (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) List.mem_cons_self

/-- The memory once the second thread has won. -/
theorem RaceBase.final_read (B : RaceBase (m' + 1) (n' + 1) X rest) :
    Final (n' + 1) (sum (m' + 1 + 1) (n' + 1))
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
        ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl

theorem RaceBase.look_res (B : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port) X.wires = some ([0, n' + 1 + 3 + 2], 2) := by
  have F := B.final_read
  refine assoc_eq_of_unique ((B.hist.wires _).2 (.inr (.inr ⟨n' + 1 + 3 + 1, by omega, by omega,
    (mem_linksA _ _ _).2 (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩))) (fun q' hq => ?_)
  exact (F.res_zero (sum_fresh (m' + 1 + 1) (n' + 1)) (t := n' + 1 + 3 + 1) (by omega) (by omega)
    q').1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))

/-- What is left of the pass of the first thread, when its list still has
the zero of the first argument, after the first successor of the result. -/
theorem RaceBase.pass_two (B : RaceBase (m' + 1) (n' + 1) X rest) :
    Stays xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
        ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .idle⟩ ⟨[], .idle⟩
      (4 * (m' + 1) + (m' + 1 + 3 + 1 + 2) + 3 * n' + 1 + 3) := by
  have F := B.final_read
  refine F.pass_from_two (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1)) m'
    (n' + 1 + 3 + 1) (by omega) (by omega) fun e he => ?_
  rw [F.agents]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ he)

end RaceFacts

/-- **The second thread takes the pair while the first has just come to the
last adder**: when the first thread is about to pop the adder.  The second
takes the zero, the first reads on to the zero and finds it gone, and both
then pass over the agents the rounds leave. -/
theorem race_d5 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    (⟨X, [⟨X.agents, .idle⟩, ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 30) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  have f0 : XMach.act xsys X ⟨X.agents, .idle⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩, 0) := by
    rw [B.agents]
    exact XMach.act_idle_pos (e := ([0, n' + 1 + 4], Arith.add)) B.adder
  have f1 : XMach.act xsys (X.takeAgent [2])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (X.takeAgent [2], ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
        .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
        .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4],
        ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
          .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
        .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2),
        ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) (by
      show nextSeg ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([2], 0)
        ([n' + 1 + 4], 1) = none
      rw [nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.stop)
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
        ([0, n' + 1 + 4], 1))
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
        ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
        ([0, n' + 1 + 4], 1),
        ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 f4
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans B.pass_two
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

/-- The last pass after the first successor of the result, over a list
that still has the zero of the first argument, in any memory the rounds
leave. -/
theorem Final.pass_two_tail {m' n' : Nat} {Y : XNet Arith}
    (F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) Y (n' + 1 + 3 + (m' + 1) + 1) (m' + 1)) :
    Stays xsys Y ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .idle⟩ ⟨[], .idle⟩
      (4 * (m' + 1) + (m' + 1 + 3 + 1 + 2) + 3 * n' + 1 + 3) := by
  refine F.pass_from_two (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1)) m'
    (n' + 1 + 3 + 1) (by omega) (by omega) fun e he => ?_
  rw [F.agents]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ he)

/-- **The second thread takes the zero while the first reads the segment
of the last adder.**  The first reads on to the zero and finds it gone. -/
theorem race_d6 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    (⟨X, [⟨rest, .look [0, n' + 1 + 4] .add⟩, ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 29) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look
      [0, n' + 1 + 4] .add⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add
          ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek
      [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add
          ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1)
      ([2], 0)⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]),
          ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) B.stop
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
      .idle⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look
          [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)),
          ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ
          ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 f4
  have sF := sE2.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

/-- **The second thread takes the zero while the first is on its way from
the last adder to it.**  The first finds the zero gone at once. -/
theorem race_d7 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    (⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 28) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek
      [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add
          ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek
      [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero1) B.stop
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]),
          ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look
      [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek
          [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port)
          ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 k3
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

theorem filter_ne_idem (l : List (Id × Arith)) (a : Id) :
    (l.filter fun e => decide (e.1 ≠ a)).filter (fun e => decide (e.1 ≠ a)) =
      l.filter fun e => decide (e.1 ≠ a) := by
  rw [List.filter_filter]
  congr 1
  funext e
  exact Bool.and_self _

/-- **Each thread takes one agent of the pair in the same round**: the
first thread the adder, then the second the zero.  The first does not find
the zero and puts the adder back; the second finds the adder and takes
it. -/
theorem race_d9 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) :
    (⟨X, [⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 28) := by
  have hr := B.rest
  subst hr
  have hA9 : ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent
      [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
      ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents =
      (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) := by
    show List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) (([0, n' + 1 + 4], Arith.add) ::
      (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter
          (fun e => decide (e.1 ≠ [2]))) = _
    rw [List.filter_cons_of_neg (by simp),
      filter_ne_comm (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) [2] [0, n' + 1 + 4],
      filter_ne_idem, filter_ne_comm]
  have F := B.final hA9 rfl
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .ready [0, n' + 1 + 4]
      [2] .add .zero⟩ =
      ((X.takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half
          [0, n' + 1 + 4] [2] .add .zero⟩, 0) :=
    XMach.act_ready B.adder
  have hZ : assoc [2] (X.takeAgent [0, n' + 1 + 4]).agents = some .zero := by
    show assoc [2] (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = some .zero
    rw [assoc_filter_ne, ite_neg' (by ports_differ)]
    exact B.zero
  have gz : assoc [2] ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).agents = none := by
    show assoc [2] ((X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter fun e => decide
        (e.1 ≠ [2])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f1 : XMach.act xsys ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add),
          ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gz] at h1
      cases h1)
  have hA : assoc [0, n' + 1 + 4] (((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent
      [0, n' + 1 + 4] .add).agents = some .add := by
    show (if ([0, n' + 1 + 4] : Id) = [0, n' + 1 + 4] then some Arith.add else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent
      [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent
          [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look
          [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) (by
      show assoc [0, 0, n' + 1 + 3 + 2] (List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4]))
          (([0, n' + 1 + 4], Arith.add) ::
        (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter
            (fun e => decide (e.1 ≠ [2])))) = some .succ
      rw [assoc_filter_ne, ite_neg' (by ports_differ), assoc_cons_ne _ (by ports_differ),
        assoc_filter_ne, ite_neg' (by ports_differ), assoc_filter_ne,
        ite_neg' (by ports_differ)]
      exact B.hist.agent_res (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) List.mem_cons_self)
  have f3 : XMach.act xsys (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent
      [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
      ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look
      [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent
          [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)),
          ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ
          ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port)
          ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sw := race_reader_wins (l := l) f0 hZ f1 hA f2 f3 k3
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

/-- Without the zero of the first argument, the list of agents after the
last adder is the list the rounds leave. -/
theorem rest_filter_two (n d : Nat) :
    (resL (n + 3) d ++ tailA n).filter (fun e => decide (e.1 ≠ [2])) =
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

/-- The last pass after the first successor of the result, in any memory
the rounds leave. -/
theorem Final.pass_fin_tail {m' n' : Nat} {Y : XNet Arith}
    (F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) Y (n' + 1 + 3 + (m' + 1) + 1) (m' + 1)) :
    Stays xsys Y ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ ⟨[], .idle⟩
      (4 * (m' + 1) + (m' + 1 + 3 + 1 + 2) + 3 * (n' + 1)) := by
  refine F.pass_from (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1)) m'
    (n' + 1 + 3 + 1) (by omega) (by omega) fun e he => ?_
  rw [F.agents]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ he)

/-- **The second thread takes the zero as the first starts over after its
round on the lowest successor.**  The first pops the last adder, reads on
to the zero and finds it gone. -/
theorem race_d4 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (todo l : List (Id × Arith)) :
    (⟨X, [⟨todo, .write [] []⟩, ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 31) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨todo, .write [] []⟩ =
      (X, ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩,
          0) := by
    rw [← B.agents]
    rfl
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨([0, n' + 1 + 4], .add) ::
      (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look
          [0, n' + 1 + 4] .add⟩, 0) :=
    XMach.act_idle_pos (e := ([0, n' + 1 + 4], Arith.add)) B.adder1
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4])
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]),
          ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add
          ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1),
      .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek
          [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl (by
      show nextSeg ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 0) = _
      rw [nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.seek)
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1)
      ([2], 0)⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)),
          ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) (by
      show nextSeg ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) ::
          (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([2], 0)
        ([n' + 1 + 4], 1) = none
      rw [nextSeg_cons_ne _ _ _ (by ports_differ), nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.stop)
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 f4
  have sF := (Stays.step (fun h => by cases h)
    (XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1)
    (Stays.step (fun h => by
      injection h with _ h2
      cases h2) (XMach.act_look k2) sE2)).trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

/-- **The second thread takes the zero as the first writes the last segment
of its round.**  The first starts over with the last adder in its list,
which the second has taken by then. -/
theorem race_d3 {m' n' : Nat} {V : XNet Arith} {p8 q8 : Port} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (V.putLink p8 q8) rest) (todo l : List (Id × Arith)) :
    (⟨V, [⟨todo, .write [] [(p8, q8)]⟩, ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 28) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++
      (sndL (n' + 1) ++ [([3], .zero)]))
  have hM1 : ((V.putLink p8 q8).takeAgent [2]).agents = ([0, n' + 1 + 4], .add) ::
      (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])) := by
    show List.filter (fun e => decide (e.1 ≠ [2])) (V.putLink p8 q8).agents = _
    rw [B.agents, List.filter_cons_of_pos (by simp), rest_filter_two]
  have gA : assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent
      [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] (((V.putLink p8 q8).agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p8, q8)]⟩ =
      ((V.putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p8 q8).takeAgent [2]) ⟨todo, .write [] []⟩ =
      (((V.putLink p8 q8).takeAgent [2]), ⟨([0, n' + 1 + 4], .add) ::
          (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])), .idle⟩, 0) := by
    rw [← hM1]
    rfl
  have f2 : XMach.act xsys (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4])
      ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])),
      .idle⟩ =
      ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]),
          ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([0, n' + 1 + 4], Arith.add)) (by
      show ¬ assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent
          [0, n' + 1 + 4]).agents = some Arith.add
      rw [gA]
      exact fun h => by cases h)
  have f3 : XMach.act xsys ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++
      (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]),
          .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look
      [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)),
          ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .seek
          [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 f4
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

/-- **The second thread takes the zero as the first writes the last
segment but one of its round.**  When the first starts over, both agents
of the pair are gone from its list. -/
theorem race_d2 {m' n' : Nat} {V : XNet Arith} {p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((V.putLink p7 q7).putLink p8 q8) rest)
        (todo l : List (Id × Arith)) :
    (⟨V, [⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 28) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1))
      ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++
      (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent
      [0, n' + 1 + 4]).agents = resL (n' + 1 + 3) (m' + 1) ++
      (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((V.putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p7 q7).takeAgent [2]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent
      [0, n' + 1 + 4]) ⟨todo, .write [] []⟩ =
      (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]),
          ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f3 : XMach.act xsys (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent
      [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++
          (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent
      [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
      ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++
      (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]),
          .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩,
          0) :=
    XMach.act_look k2
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 f4
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

/-- **The second thread takes the zero two segments earlier still.** -/
theorem race_d1 {m' n' : Nat} {V : XNet Arith} {p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (((V.putLink p6 q6).putLink p7 q7).putLink p8 q8) rest)
        (todo l : List (Id × Arith)) :
    (⟨V, [⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩,
        ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 29) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1))
      (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
      [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
      ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++
      (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
      [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1)
      ([0, n' + 1 + 4], 2)).agents = resL (n' + 1 + 3) (m' + 1) ++
      (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((V.putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p6 q6).takeAgent [2])
      ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
      [0, n' + 1 + 4]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
          [0, n' + 1 + 4]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
      [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ⟨todo, .write [] []⟩ =
      (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
          [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)),
          ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f4 : XMach.act xsys (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
      [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
      ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3) (m' + 1) ++
      (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent
          [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
          ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++
          (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 f4
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sF sR (by omega) (by omega) (by omega)

/-- **The second thread takes the zero three segments earlier still**, at
the first moment it can.  Its two segments and the last of the first
thread are written in turn, and both threads start over on the same list
in the same memory. -/
theorem race_d0 {m' n' : Nat} {V : XNet Arith} {p5 q5 p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1)
        ((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8) rest)
        (todo l : List (Id × Arith)) :
    (⟨V, [⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩,
        ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (10 * (m' + 1) + 6 * (n' + 1) + 30) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1))
      ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
      [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1)
      ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := by
    refine final_of B.hist ?_ fun e => ?_
    · rw [show ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
          [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)).agents =
          (((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents.filter
              fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) from rfl, filter_ne_comm]
      exact B.hist.final.agents
    · show e ∈ (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (p8, q8) ::
          (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) ::
          (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ↔
        e ∈ (p8, q8) :: (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ∨
          e ∈ [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)),
              (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]
      constructor
      · intro h
        rcases List.mem_cons.1 h with rfl | h
        · exact .inr (List.mem_cons_of_mem _ List.mem_cons_self)
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl List.mem_cons_self
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inr List.mem_cons_self
            · exact .inl (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        · rcases List.mem_cons.1 h with rfl | h
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          · rcases List.mem_cons.1 h with rfl | h
            · exact List.mem_cons_self
            · cases h
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((V.putLink p5 q5), ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p5 q5).takeAgent [2])
      ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩,
          0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
      [0, n' + 1 + 4]) ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
          [0, n' + 1 + 4]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
      [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
          [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f4 : XMach.act xsys ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
      [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1)
      ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      ⟨todo, .write [] []⟩ =
      (((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
          [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)),
          ⟨((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent
          [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1)
          ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have sw := race_reader_wins (l := l) f0 B.zero f1 B.adder1 f2 f3 f4
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl sR sR (by omega) (by omega) (by omega)

/-- No agent of the first argument is in the memory the rounds leave. -/
theorem Final.no_top {n : Nat} {X0 X : XNet Arith} {T d : Nat} (F : Final n X0 X T d)
    {t : Nat} (ht : n + 3 < t) : assoc [t] X.agents = none := by
  rw [F.agents]
  refine assoc_none_of_forall fun e he e' => ?_
  rcases List.mem_append.1 he with h | h
  · exact res_ne_single h t e'
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨-, j, -, h2, h3⟩ := mem_sndL h
      rw [h3] at e'
      injection e' with e1
      omega
    · rcases List.mem_cons.1 h with rfl | h
      · injection e' with e1
        omega
      · cases h

/-- **The one alignment in which the first thread keeps the last pair**:
the second thread is ready to take the zero as the first comes to it from
the last adder.  The second takes the zero, the first the adder; the second
does not find the adder and puts the zero back, and the first takes it.
The second thread then passes the zero of the second argument and finds
the top successor gone, while the first writes its two segments. -/
theorem race_d8 {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (t : Nat) (ht : n' + 1 + 3 < t) :
    (⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩,
      ⟨[([3], .zero), ([t], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Ends xsys (5 * (m' + 1) + 3 * (n' + 1) + 22) := by
  have hA8 : ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent
      [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
      ([0, n' + 1 + 4], 1)).agents =
      (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) := by
    show List.filter (fun e => decide (e.1 ≠ [2])) (([2], Arith.zero) ::
      (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4]))) = _
    rw [List.filter_cons_of_neg (by simp),
      filter_ne_comm (X.agents.filter fun e => decide (e.1 ≠ [2])) [0, n' + 1 + 4] [2],
      filter_ne_idem]
  have F8 := B.final hA8 rfl
  have S := snd_sum (m' + 1 + 1) (n' + 1)
  have f0 : XMach.act xsys X ⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (X, ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩, 0) :=
    XMach.act_seek_found (c := ([2], 0)) ((ite_pos' rfl).trans B.zero) ⟨by ports_differ, rfl⟩
  have r0 : XMach.act xsys X ⟨[([3], .zero), ([t], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((X.takeAgent [2]), ⟨[([3], .zero), ([t], .succ)], .half [2] [0, n' + 1 + 4] .zero .add⟩,
          0) := XMach.act_ready B.zero
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩,
          0) := XMach.act_ready B.adder1
  have gA : assoc [0, n' + 1 + 4] ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] ((X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have r1 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4])
      ⟨[([3], .zero), ([t], .succ)], .half [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero),
          ⟨[([3], .zero), ([t], .succ)], .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gA] at h1
      cases h1)
  have hZ3 : assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).agents = some Arith.zero := by
    show (if ([2] : Id) = [2] then some Arith.zero else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero)
      ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]),
          ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)),
          (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 1) :=
    XMach.act_half (R := addZero.toX) (by
      rw [ite_pos' (show assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
          [2] .zero).agents = some Arith.zero ∧
        ([0, n' + 1 + 4] : Id) ≠ [2] from ⟨hZ3, by ports_differ⟩)]
      rfl)
  have h3 : assoc [3] ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent
      [2]).agents = some Arith.zero :=
    F8.agent (e := ([3], Arith.zero)) (by
      rw [F8.agents]
      exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self))
  have r2 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).takeAgent [2]) ⟨[([3], .zero), ([t], .succ)], .idle⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]),
          ⟨[([t], .succ)], .look [3] .zero⟩, 0) := XMach.act_idle_pos (e := ([3], Arith.zero)) h3
  have f3 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).takeAgent [2]) ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)),
      (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨rest, .write []
          [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 0) := rfl
  have hl6 : assoc (([3], 0) : Port) ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) ::
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
      ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).wires) = some ([4], 1) :=
    assoc_eq_of_unique ((F8.up S (j := 3) (by omega) (by omega) _).2 rfl)
      (fun q' hq => (F8.up S (j := 3) (by omega) (by omega) q').1 hq)
  rw [assoc_cons_ne _ (by ports_differ)] at hl6
  have r3 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ⟨[([t], .succ)], .look [3] .zero⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨[([t], .succ)], .seek [3] .zero ([3], 0)
          ([4], 1)⟩, 0) := XMach.act_look hl6
  have f4 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2))
      ⟨rest, .write [] [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)), ⟨rest, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
      ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t], .succ)], .seek [3] .zero ([3], 0)
      ([4], 1)⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)), ⟨[([t], .succ)], .idle⟩, 0) :=
    XMach.act_seek_stop rfl (nextSeg_none fun q hq =>
      (F8.down S (j := 3) (by omega) (by omega) q).1 hq)
  have f5 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
      ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨rest, .write [] []⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)), ⟨((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
          [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
          ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have r5 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
      [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
      ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t], .succ)], .idle⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)), ⟨[], .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([t], Arith.succ)) (by
      show ¬ assoc [t] ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent
          [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink
          ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = some Arith.succ
      rw [F8.no_top ht]
      exact fun h => by cases h)
  have sw : Sweeps xsys ⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩,
      ⟨[([3], .zero), ([t], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩
      ⟨((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink
          ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2)
          ([0, n' + 1 + 4], 1)), [⟨rest, .write [] []⟩, ⟨[([t], .succ)], .idle⟩]⟩ 5 :=
    .step f0 r0 (.step f1 r1 (.step f2 r2 (.step f3 r3 (.step f4 r4 (.refl _)))))
  have sF := F8.pass_stays S (sum_fresh (m' + 1 + 1) (n' + 1))
  exact XMach.ends_sweeps sw rfl
    (Stays.step (fun h => by
      injection h with _ h2
      cases h2) f5 sF)
    (Stays.step (fun h => by cases h) r5 (Stays.refl _)) (by omega) (by omega) (by omega)

/-- **The first thread alone through the last round**: from the moment it
is about to pop the last adder to the moment it is ready to take it. -/
theorem RaceBase.states {m n : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase m n X rest) :
    XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 16) =
        (X, ⟨X.agents, .idle⟩) ∧
    XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 17) =
        (X, ⟨rest, .look [0, n + 4] .add⟩) ∧
    XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 18) =
      (X, ⟨rest, .seek [0, n + 4] .add ([0, n + 4], 0) ([n + 4], 1)⟩) ∧
    XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 19) =
      (X, ⟨rest, .seek [0, n + 4] .add ([n + 4], 1) ([2], 0)⟩) ∧
    XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 20) =
        (X, ⟨rest, .ready [0, n + 4] [2] .add .zero⟩) := by
  have f0 : XMach.act xsys X ⟨X.agents, .idle⟩ = (X, ⟨rest, .look [0, n + 4] .add⟩, 0) := by
    rw [B.agents]
    exact XMach.act_idle_pos (e := ([0, n + 4], Arith.add)) B.adder
  have f1 : XMach.act xsys X ⟨rest, .look [0, n + 4] .add⟩ =
      (X, ⟨rest, .seek [0, n + 4] .add ([0, n + 4], 0) ([n + 4], 1)⟩, 0) := XMach.act_look B.look
  have f2 : XMach.act xsys X ⟨rest, .seek [0, n + 4] .add ([0, n + 4], 0) ([n + 4], 1)⟩ =
      (X, ⟨rest, .seek [0, n + 4] .add ([n + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f3 : XMach.act xsys X ⟨rest, .seek [0, n + 4] .add ([n + 4], 1) ([2], 0)⟩ =
      (X, ⟨rest, .ready [0, n + 4] [2] .add .zero⟩, 0) :=
    XMach.act_seek_found (c := ([2], 0)) ((ite_pos' rfl).trans B.zero) ⟨by ports_differ, rfl⟩
  have e : ∀ j k, k = 16 + 17 * m + j →
      XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ k = XMach.solo xsys X
          ⟨X.agents, .idle⟩ j := fun j k hk => by
    subst hk
    rw [XMach.solo_add, B.solo]
  exact ⟨e 0 _ (by omega),
    (e 1 _ (by omega)).trans (XMach.solo_step f0 0),
    (e 2 _ (by omega)).trans ((XMach.solo_step f0 1).trans (XMach.solo_step f1 0)),
    (e 3 _ (by omega)).trans ((XMach.solo_step f0 2).trans
      ((XMach.solo_step f1 1).trans (XMach.solo_step f2 0))),
    (e 4 _ (by omega)).trans ((XMach.solo_step f0 3).trans
      ((XMach.solo_step f1 2).trans ((XMach.solo_step f2 1).trans (XMach.solo_step f3 0))))⟩

/-- **The first thread alone while it writes the last four segments of its
round on the lowest successor**: the five moments, and the memory before
the last round that the four segments complete. -/
theorem race_write (m n : Nat) (hm : 1 ≤ m) :
    ∃ (V : XNet Arith) (todo rest : List (Id × Arith)) (p5 q5 p6 q6 p7 q7 p8 q8 : Port),
      RaceBase m n ((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8) rest ∧
      XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 11) =
        (V, ⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩) ∧
      XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 12) =
        (V.putLink p5 q5, ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩) ∧
      XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 13) =
        ((V.putLink p5 q5).putLink p6 q6, ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩) ∧
      XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 14) =
        (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7, ⟨todo, .write [] [(p8, q8)]⟩) ∧
      XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 15) =
        ((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8,
          ⟨todo, .write [] []⟩) := by
  obtain ⟨X, w, st, -⟩ := solo_hist m n (m - 1) 1 (by omega)
  obtain ⟨rest0, hA, k₁, k₂, k₂', k₃, hne, k₄⟩ := st.round_pair (h := n + 3) (by omega)
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w1 := Works.via_start (xs := xsys) (c := ([n + 3 + 1 + 1], 1)) rest0 k₁ k₂ rfl k₂' k₃
    hne k₄ hR
  rw [← hA, newAgents_add hne,
    show addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + 1 + 1] [n + 3 + 1] .add .succ = _ from
      newLinks_add _ _] at w1
  have w2 := (w1.trans (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_agent (xs := xsys) _ _ _ _ _ _)
  have w3 := (((w2.trans (Works.write_link (xs := xsys) _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)
  have w4 := w3.trans (Works.write_link (xs := xsys) _ _ _ _ _)
  have w5 := w4.trans (Works.write_link (xs := xsys) _ _ _ _ _)
  have w6 := w5.trans (Works.write_link (xs := xsys) _ _ _ _ _)
  have w7 := w6.trans (Works.write_link (xs := xsys) _ _ _ _ _)
  have s11 := (w.trans w3).solo_at (17 * m + 11) (by omega)
  have s12 := (w.trans w4).solo_at (17 * m + 12) (by omega)
  have s13 := (w.trans w5).solo_at (17 * m + 13) (by omega)
  have s14 := (w.trans w6).solo_at (17 * m + 14) (by omega)
  have s15 := (w.trans w7).solo_at (17 * m + 15) (by omega)
  obtain ⟨X16, rest, B⟩ := race_base m n
  have e16 := B.solo
  have e : 16 + 17 * m = 17 * m + 15 + 1 := by omega
  rw [e, XMach.solo_add, s15] at e16
  have eX : _ = X16 := congrArg Prod.fst e16
  subst eX
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, B, s11, s12, s13, s14, s15⟩

/-- One thread alone, at a moment written in another way. -/
theorem solo_at {m n k k' : Nat} {v : XNet Arith × XThread Arith}
    (h : XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ k = v) (e : k' = k) :
    XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ k' = v := by
  subst e
  exact h

/-- From the entry to the race to the end of the run. -/
theorem race_close {m n aE c W : Nat} {X : XNet Arith} {T R : XThread Arith}
    (htr : (XMach.init (sum (m + 1) n) 2).trace xsys (fun i => i % 2) (2 * aE) =
      (⟨(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE).1,
          [(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE).2, R]⟩, c))
    (hs : XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ aE = (X, T))
    (hE : (⟨X, [T, R]⟩ : XMach Arith).Ends xsys W) :
    (XMach.init (sum (m + 1) n) 2).Total xsys (fun i => i % 2) (2 * aE + W) := by
  rw [hs] at htr
  exact (hE.after (congrArg Prod.fst htr) rfl).total

/-- **What two threads in turn do in all on the net for `(m + 1) + n`** when
the second is ready to take the zero of the first argument after
`17 * m + 11 + d` actions of each.  For `d = 8` the first thread takes the
last pair and the second has two entries left to pass; otherwise the second
takes it and both pass over all the agents that are left. -/
def raceWork (m n : Nat) : Nat → Nat
  | 0 => 44 * m + 6 * n + 52
  | 1 => 44 * m + 6 * n + 53
  | 2 => 44 * m + 6 * n + 54
  | 3 => 44 * m + 6 * n + 56
  | 4 => 44 * m + 6 * n + 61
  | 5 => 44 * m + 6 * n + 62
  | 6 => 44 * m + 6 * n + 63
  | 7 => 44 * m + 6 * n + 64
  | 8 => 39 * m + 3 * n + 60
  | _ => 44 * m + 6 * n + 68

theorem raceWork_le (m n d : Nat) : raceWork m n d ≤ 44 * m + 6 * n + 68 := by
  unfold raceWork
  split <;> omega

/-- **Two threads in turn, every second argument, to the action.**  On the
net for `(m + 1) + n`, with `m` from four on: either the second thread only
reads, and the work is that of one thread and at most `4 * m + 3 * n + 15`
more; or it is ready to take the zero of the first argument when each
thread has made `17 * m + 11 + d` actions, for some `d` up to nine, and
then the work of the whole run is exactly `raceWork m n d`. -/
theorem two_threads_exact (m n : Nat) (hm : 4 ≤ m) :
    (∀ i, (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤
      soloWork (m + 1) n + (4 * m + 3 * n + 15)) ∨
    ∃ d c, d ≤ 9 ∧
      (XMach.init (sum (m + 1) n) 2).trace xsys (fun i => i % 2) (2 * (17 * m + 11 + d)) =
        (⟨(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 11 + d)).1,
          [(XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 11 + d)).2,
            ⟨[([3], .zero), ([n + 3 + m + 1], .succ)], .ready [2] [0, n + 4] .zero .add⟩]⟩, c) ∧
      (XMach.init (sum (m + 1) n) 2).Total xsys (fun i => i % 2) (raceWork m n d) := by
  cases n with
  | zero =>
    refine .inl fun i => ?_
    have h := two_threads_narrow m 0 hm (.inl (by omega)) i
    rw [soloWork_succ]
    omega
  | succ n' =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases two_threads_entry (m' + 1) (n' + 1) hm with h | ⟨aE, c, h1, h2, htr⟩
    · exact .inl h
    · obtain ⟨V, todo, rest, p5, q5, p6, q6, p7, q7, p8, q8, B, s11, s12, s13, s14, s15⟩ :=
        race_write (m' + 1) (n' + 1) (by omega)
      obtain ⟨s16, s17, s18, s19, s20⟩ := B.states
      obtain ⟨d, rfl⟩ : ∃ d, aE = 17 * (m' + 1) + 11 + d :=
        ⟨aE - (17 * (m' + 1) + 11), by omega⟩
      refine .inr ⟨d, c, by omega, htr, ?_⟩
      have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
          d = 9 := by omega
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (race_close htr (solo_at s11 (by omega)) (race_d0 B todo _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 52
          omega)
      · exact (race_close htr (solo_at s12 (by omega)) (race_d1 B todo _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 53
          omega)
      · exact (race_close htr (solo_at s13 (by omega)) (race_d2 B todo _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 54
          omega)
      · exact (race_close htr (solo_at s14 (by omega)) (race_d3 B todo _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 56
          omega)
      · exact (race_close htr (solo_at s15 (by omega)) (race_d4 B todo _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 61
          omega)
      · exact (race_close htr (solo_at s16 (by omega)) (race_d5 B _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 62
          omega)
      · exact (race_close htr (solo_at s17 (by omega)) (race_d6 B _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 63
          omega)
      · exact (race_close htr (solo_at s18 (by omega)) (race_d7 B _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 64
          omega)
      · exact (race_close htr (solo_at s19 (by omega)) (race_d8 B _ (by omega))).cast (by
          show _ = 39 * (m' + 1) + 3 * (n' + 1) + 60
          omega)
      · exact (race_close htr (solo_at s20 (by omega)) (race_d9 B _)).cast (by
          show _ = 44 * (m' + 1) + 6 * (n' + 1) + 68
          omega)

/-- **Two threads in turn, every second argument**: at most
`44 * m + 6 * n + 68` busy actions on the net for `(m + 1) + n`, with `m`
from four on. -/
theorem two_threads_race (m n : Nat) (hm : 4 ≤ m) (i : Nat) :
    (XMach.init (sum (m + 1) n) 2).work xsys (fun i => i % 2) i ≤ 44 * m + 6 * n + 68 := by
  rcases two_threads_exact m n hm with h | ⟨d, c, -, -, tot⟩
  · have h' := h i
    rw [soloWork_succ] at h'
    omega
  · have h1 := tot.le i
    have h2 := raceWork_le m n d
    omega

theorem Checks.Arith.TwoThreads.c8
    (i : Nat) : (XMach.init (sum 21 94) 2).work xsys (fun i => i % 2) i ≤ 1512 :=
  two_threads_race 20 94 (by decide) i

theorem Checks.Arith.TwoThreads.c9
    (i : Nat) : (XMach.init (sum 21 97) 2).work xsys (fun i => i % 2) i ≤ 1530 :=
  two_threads_race 20 97 (by decide) i

end Arith

end INet
