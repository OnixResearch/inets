import InteractionNets.Arith.TwoThreads

/-! ### Threads in turn on an addition: where each reader is, action by action -/

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

namespace Arith

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

variable {j m n : Nat}

local macro "ports_differ" : tactic =>
  `(tactic| first | (intro e; simp at e; done) | (intro e; simp at e; omega))

/-- **The segment from the first adder to the one the first round makes is
written by the ninth action** of the first thread. -/
theorem solo_link_top9 (m n : Nat) {u : Nat} (hu : 9 ≤ u) :
    ((([1], 1), ([0, n + 3 + m + 1], 1)) : Port × Port) ∈
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires := by
  have st := start_sum m n
  obtain ⟨rest, hA, h₁, h₂, hne, h₄⟩ := st.pair
  have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
  have w := XMach.solo_claim_start (xs := xsys) rest h₁ h₂ st.adder hne h₄ hR
  rw [← hA] at w
  have e5 := w.2
  rw [newAgents_swap (a := [1]) (s := [m + n + 3 + 1]) (fun e => hne e.symm),
    show addSucc.swap.toX.newLinks xsys.sys.ar [m + n + 3 + 1] [1] .succ .add = _ from
      newLinks_swap _ _] at e5
  have e9 := XMach.solo_add xsys 5 (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ 4
  rw [e5] at e9
  have h9 : ((([1], 1), ([0, m + n + 3 + 1], 1)) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (5 + 4)).1.wires := by
    rw [e9]
    exact List.mem_cons_self
  have hw := XMach.solo_wires_mono xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
    (5 + 4) (u - 9) _ h9
  rw [show 5 + 4 + (u - 9) = u by omega] at hw
  rw [show n + 3 + m + 1 = m + n + 3 + 1 by omega]
  exact hw

/-- **The segment from an adder to the next is the first that its round
writes**: the round on the successor `[t]`, which is `d` below the top,
writes it at its ninth action, so it is in memory once the first thread has
made `17 * d + 8` actions. -/
theorem solo_link8 (m n : Nat) {t u : Nat} (h1 : n + 4 ≤ t) (h2 : t < n + 3 + m + 1)
    (hu : 17 * (n + 3 + m + 1 - t) + 8 ≤ u) :
    ((([0, t + 1], 1), ([0, t], 1)) : Port × Port) ∈
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires := by
  obtain ⟨r, rfl⟩ : ∃ r, t = n + 3 + r + 1 := ⟨t - (n + 4), by omega⟩
  obtain ⟨X, w, st, -⟩ := solo_hist m n (m - r - 1) (r + 1) (by omega)
  have st' : Steady n X (n + 3 + r + 1) := st
  obtain ⟨rest0, hA, k₁, k₂, k₂', k₃, hne, k₄⟩ := st'.round_pair (h := n + 3 + r) (by omega)
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w1 := Works.via_start (xs := xsys) (c := ([n + 3 + r + 1 + 1], 1)) rest0 k₁ k₂ rfl k₂' k₃
    hne k₄ hR
  rw [← hA, newAgents_add hne,
    show addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + r + 1 + 1] [n + 3 + r + 1] .add .succ = _
      from newLinks_add _ _] at w1
  have w3 := ((w1.trans (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)
  have e := (w.trans w3).solo_at (17 * (m - r) + 8) (by omega)
  have h0 : ((([0, n + 3 + r + 1 + 1], 1), ([0, n + 3 + r + 1], 1)) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
          (17 * (m - r) + 8)).1.wires := by
    rw [e]
    exact List.mem_cons_self
  have hw := XMach.solo_wires_mono xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
    (17 * (m - r) + 8) (u - (17 * (m - r) + 8)) _ h0
  rw [show 17 * (m - r) + 8 + (u - (17 * (m - r) + 8)) = u by omega] at hw
  exact hw

/-- **And it is not in memory before that action.** -/
theorem solo_no_link8 (m n : Nat) {t u : Nat} (h1 : n + 4 ≤ t) (h2 : t < n + 3 + m + 1)
    (hq : ((([0, t + 1], 1), ([0, t], 1)) : Port × Port) ∈
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires) :
    17 * (n + 3 + m + 1 - t) + 8 ≤ u := by
  obtain ⟨r, rfl⟩ : ∃ r, t = n + 3 + r + 1 := ⟨t - (n + 4), by omega⟩
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨X, w, st, H⟩ := solo_hist m n (m - r - 1) (r + 1) (by omega)
  have st' : Steady n X (n + 3 + r + 1) := st
  obtain ⟨rest0, hA, k₁, k₂, k₂', k₃, hne, k₄⟩ := st'.round_pair (h := n + 3 + r) (by omega)
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w1 := Works.via_start (xs := xsys) (c := ([n + 3 + r + 1 + 1], 1)) rest0 k₁ k₂ rfl k₂' k₃
    hne k₄ hR
  rw [← hA, newAgents_add hne] at w1
  have w2 := (w1.trans (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_agent (xs := xsys) _ _ _ _ _ _)
  have e := (w.trans w2).solo_at (17 * (m - r) + 7) (by omega)
  have h3 := XMach.solo_wires_mono xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u
    (17 * (m - r) + 7 - u) _ hq
  rw [show u + (17 * (m - r) + 7 - u) = 17 * (m - r) + 7 by omega, e] at h3
  have h3' : ((([0, n + 3 + r + 1 + 1], 1), ([0, n + 3 + r + 1], 1)) : Port × Port) ∈ X.wires := h3
  rcases (H.wires _).1 h3' with h | h | ⟨t', t1, t2, h⟩
  · obtain ⟨j, ej⟩ := sum_fresh (m + 1) n _ _ _ h
    injection ej with _ e2
    cases e2
  · rcases (mem_linksS _ _ _).1 h with h | h | h | h | h | h | h | h <;>
      first | (simp at h; done) | (simp at h; omega)
  · rcases (mem_linksA _ _ _).1 h with h | h | h | h | h | h | h | h <;>
      first | (simp at h; done) | (simp at h; omega)

/-- **The segment from the lowest successor to the last adder** is in
memory once the first thread has made `17 * m + 10` actions. -/
theorem solo_link3 (m n : Nat) (hm : 1 ≤ m) {u : Nat} (hu : 17 * m + 10 ≤ u) :
    ((([n + 3 + 1], 1), ([0, n + 3 + 1], 0)) : Port × Port) ∈
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires := by
  obtain ⟨X, w, st, -⟩ := solo_hist m n (m - 1) 1 (by omega)
  obtain ⟨rest0, hA, k₁, k₂, k₂', k₃, hne, k₄⟩ := st.round_pair (h := n + 3) (by omega)
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  have w1 := Works.via_start (xs := xsys) (c := ([n + 3 + 1 + 1], 1)) rest0 k₁ k₂ rfl k₂' k₃
    hne k₄ hR
  rw [← hA, newAgents_add hne,
    show addSucc.toX.newLinks xsys.sys.ar [0, n + 3 + 1 + 1] [n + 3 + 1] .add .succ = _
      from newLinks_add _ _] at w1
  have w3 := ((((w1.trans (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_agent (xs := xsys) _ _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)).trans
    (Works.write_link (xs := xsys) _ _ _ _ _)
  have e := (w.trans w3).solo_at (17 * m + 10) (by omega)
  have h0 : ((([n + 3 + 1], 1), ([0, n + 3 + 1], 0)) : Port × Port) ∈
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (17 * m + 10)).1.wires := by
    rw [e]
    exact List.mem_cons_self
  have hw := XMach.solo_wires_mono xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
    (17 * m + 10) (u - (17 * m + 10)) _ h0
  rw [show 17 * m + 10 + (u - (17 * m + 10)) = u by omega] at hw
  exact hw

/-- The segments of the net at the start stay in memory. -/
theorem solo_start_wire (m n u : Nat) {e : Port × Port} (he : e ∈ (sum (m + 1) n).wires) :
    e ∈ (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires := by
  have hw := XMach.solo_wires_mono xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ 0 u e he
  rw [Nat.zero_add] at hw
  exact hw

/-- What a thread reads at the principal port of a successor of the chain,
at any moment. -/
theorem solo_look_chain (m n : Nat) {t : Nat} (h1 : n + 4 ≤ t) (h2 : t ≤ n + 3 + m)
    (u : Nat) : assoc (([t], 0) : Port) (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires = some ([t + 1], 1) := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  exact assoc_eq_of_unique
    (solo_start_wire m n u ((sum_princ (m + 1) n t h1 (by omega) _).2 rfl))
    fun q' hq => (sum_princ (m + 1) n t h1 (by omega) q').1
      ((F.old (.inl rfl) q').1 (hfin u _ hq))

/-- No second segment at the point above a successor of the chain, while
the round on the successor above is not yet written. -/
theorem solo_stop_chain (m n : Nat) {t u : Nat} (h1 : n + 4 ≤ t) (h2 : t ≤ n + 3 + m)
    (hu : t + 1 = n + 3 + m + 1 ∧ u ≤ 3 ∨ u + 17 * (t + 1) + 1 ≤ 17 * (n + 3 + m + 1)) :
    nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires ([t + 1], 1)
        ([t], 0) = none :=
  nextSeg_none fun q hq => by
    have h := solo_seg m n (t := t + 1) (by omega) (by omega) hu q hq
    rw [show t + 1 - 1 = t by omega, below_pos h1] at h
    exact h

/-- What a thread reads at the top of the second argument. -/
theorem solo_look_top (m n u : Nat) :
    assoc (([n + 3], 0) : Port) (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires = some ([1], 1) := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  have S := snd_sum (m + 1) n
  exact assoc_eq_of_unique (solo_start_wire m n u ((S.top _).2 rfl))
    fun q' hq => (F.top_snd S q').1 (hfin u _ hq)

/-- From the second argument of the first adder a thread goes on to the
adder that the first round made, once that round has written the
segment. -/
theorem solo_hop_top (m n : Nat) {u : Nat} (hu : 9 ≤ u) :
    nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires ([1], 1)
        ([n + 3], 0) = some ([0, n + 3 + m + 1], 1) := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  have S := snd_sum (m + 1) n
  refine nextSeg_some (solo_link_top9 m n hu) (by ports_differ) fun q hq hne => ?_
  rcases (F.one_one S q).1 (hfin u _ hq) with e | e
  · exact absurd e hne
  · exact e

/-- The point a thread comes from when it is at the adder `[0, x]` on its
walk along the adders. -/
def wprev (m n x : Nat) : Port := if x = n + 3 + m + 1 then ([1], 1) else ([0, x + 1], 1)

/-- **A hop of the walk**: from the adder `[0, t + 1]` on to `[0, t]`, once
the round on `[t]` has written the segment. -/
theorem solo_hop (m n : Nat) {t u : Nat} (h1 : n + 4 ≤ t) (h2 : t < n + 3 + m + 1)
    (hu : 17 * (n + 3 + m + 1 - t) + 8 ≤ u) :
    nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires
        ([0, t + 1], 1) (wprev m n (t + 1)) = some ([0, t], 1) := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  have hfr := sum_fresh (m + 1) n
  have hp : (([0, t], 1) : Port) ≠ wprev m n (t + 1) := by
    unfold wprev
    split
    · ports_differ
    · ports_differ
  refine nextSeg_some (solo_link8 m n h1 h2 hu) hp fun q hq hne => ?_
  rcases (F.adder_one hfr (x := t + 1) (by omega) (by omega) q).1 (hfin u _ hq) with
    ⟨ex, e⟩ | ⟨hx, t', ex, e⟩ | ⟨hx, e⟩ | ⟨ex, e⟩
  · exfalso
    apply hne
    unfold wprev
    rw [ite_pos' ex]
    exact e
  · have et : t' = t := by omega
    rw [et] at e
    exact e
  · exfalso
    apply hne
    unfold wprev
    rw [ite_neg' (by omega)]
    exact e
  · exact absurd ex (by omega)

/-- **The end of the walk**: at the adder `[0, x]` there is no way on while
the round on the successor below has not written the segment. -/
theorem solo_walk_stop (m n : Nat) {x u : Nat} (h1 : n + 5 ≤ x) (h2 : x ≤ n + 3 + m + 1)
    (hu : u < 17 * (n + 3 + m + 2 - x) + 8) :
    nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires ([0, x], 1)
        (wprev m n x) = none := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  have hfr := sum_fresh (m + 1) n
  refine nextSeg_none fun q hq => ?_
  rcases (F.adder_one hfr (x := x) (by omega) h2 q).1 (hfin u _ hq) with
    ⟨ex, e⟩ | ⟨hx, t', ex, e⟩ | ⟨hx, e⟩ | ⟨ex, e⟩
  · unfold wprev
    rw [ite_pos' ex]
    exact e
  · exfalso
    subst ex
    subst e
    have h := solo_no_link8 m n (t := t') (by omega) (by omega) hq
    omega
  · unfold wprev
    rw [ite_neg' (by omega)]
    exact e
  · exact absurd ex (by omega)

/-- What a thread reads at an agent of the second argument below its top,
and that there is no second segment at the point above it. -/
theorem solo_look_snd (m n : Nat) {j : Nat} (h1 : 3 ≤ j) (h2 : j ≤ n + 2) (u : Nat) :
    assoc (([j], 0) : Port) (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires = some ([j + 1], 1) ∧
      nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires
          ([j + 1], 1) ([j], 0) = none := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  have S := snd_sum (m + 1) n
  exact ⟨assoc_eq_of_unique (solo_start_wire m n u ((S.up j h1 h2 _).2 rfl))
      fun q' hq => (F.up S h1 h2 q').1 (hfin u _ hq),
    nextSeg_none fun q hq => (F.down S h1 h2 q).1 (hfin u _ hq)⟩

/-- What a thread reads at the zero of the first argument. -/
theorem solo_look_two (m n u : Nat) :
    assoc (([2], 0) : Port) (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires = some ([n + 4], 1) := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  exact assoc_eq_of_unique (solo_start_wire m n u ((sum_two m n _).2 rfl))
    fun q' hq => (sum_two m n q').1 ((F.old (.inl rfl) q').1 (hfin u _ hq))

/-- From the zero of the first argument a thread comes to the last adder
once the first thread has made `17 * m + 10` actions, and not before. -/
theorem solo_seek_two (m n : Nat) (hm : 1 ≤ m) (u : Nat) :
    (17 * m + 10 ≤ u →
      nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires
          ([n + 4], 1) ([2], 0) = some ([0, n + 4], 0)) ∧
    (u < 17 * m + 10 → nextSeg (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires ([n + 4], 1) ([2], 0) = none) := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  constructor
  · intro hu
    refine nextSeg_some (solo_link3 m n hm hu) (by ports_differ) fun q hq hne => ?_
    rcases F.low_one q (hfin u _ hq) with e | e
    · exact absurd e hne
    · exact e
  · intro hu
    refine nextSeg_none fun q hq => ?_
    rcases F.low_one q (hfin u _ hq) with e | e
    · exact e
    · exfalso
      subst e
      have h := solo_no_link3 m n hm hq
      omega

/-- An agent of the second argument is in a list of the second
argument that is long enough. -/
theorem sndL_mem : ∀ (n k : Nat), k < n → (([k + 4], Arith.succ) : Id × Arith) ∈ sndL n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    by_cases e : k = n
    · subst e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sndL_mem n k (by omega))

/-- At the principal port of the last adder there is only the segment
from the lowest successor. -/
theorem solo_stop_adder (m n : Nat) (hm : 1 ≤ m) (u : Nat) :
    nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.wires
        ([0, n + 4], 0) ([n + 4], 1) = none := by
  obtain ⟨Xf, F, hfin⟩ := solo_fin m n
  exact nextSeg_none fun q hq => F.adder_zero hm q (hfin u _ hq)

/-- **The second argument stays**: each of its agents is in memory after
every action of the first thread, to the end of the run. -/
theorem solo_snd_forever (m n : Nat) {j : Nat} {γ : Arith} (hj3 : 3 ≤ j) (hj : j ≤ n + 3)
    (hx : assoc [j] (sum (m + 1) n).agents = some γ) (u : Nat) :
    assoc [j] (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents,
        .idle⟩ u).1.agents = some γ := by
  by_cases hu : u ≤ 17 * m + 21
  · exact solo_alive_zero m n (by omega) hj hu hx
  · obtain ⟨X, rest, B⟩ := race_base m n
    obtain ⟨-, -, -, -, s20⟩ := B.states
    have h16 := solo_alive_snd m n (j := j) (γ := γ) (by omega) hj (Nat.le_refl (16 + 17 * m)) hx
    rw [B.solo] at h16
    have f0 : XMach.act xsys X ⟨rest, .ready [0, n + 4] [2] .add .zero⟩ =
        (X.takeAgent [0, n + 4], ⟨rest, .half [0, n + 4] [2] .add .zero⟩, 0) :=
      XMach.act_ready B.adder
    have hz : assoc [2] (X.takeAgent [0, n + 4]).agents = some Arith.zero := by
      show assoc [2] (X.agents.filter fun e => decide (e.1 ≠ [0, n + 4])) = some Arith.zero
      rw [assoc_filter_ne, ite_neg' (by ports_differ)]
      exact B.zero
    have f1 : XMach.act xsys (X.takeAgent [0, n + 4]) ⟨rest, .half [0, n + 4] [2] .add .zero⟩ =
        ((X.takeAgent [0, n + 4]).takeAgent [2], ⟨rest, .write []
          [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩, 1) :=
      XMach.act_half (R := addZero.toX) (by
        rw [ite_pos' (show assoc [2] (X.takeAgent [0, n + 4]).agents = some Arith.zero ∧
          ([0, n + 4] : Id) ≠ [2] from ⟨hz, by ports_differ⟩)]
        rfl)
    have e2 : ∀ k, XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (17 * m + 22 + k) =
        XMach.solo xsys ((X.takeAgent [0, n + 4]).takeAgent [2]) ⟨rest, .write []
          [(([0, n + 4], 1), ([0, n + 4], 2)), (([0, n + 4], 2), ([0, n + 4], 1))]⟩ k :=
      fun k => by
        rw [show 17 * m + 22 + k = 17 * m + 20 + (k + 1 + 1) by omega, XMach.solo_add, s20]
        exact (XMach.solo_step f0 (k + 1)).trans (XMach.solo_step f1 k)
    have key : ∀ k, k ≤ 3 → (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (17 * m + 22 + k)).1.agents =
        ((X.takeAgent [0, n + 4]).takeAgent [2]).agents := by
      intro k hk
      rw [e2 k]
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> rfl
    have all : (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents =
        ((X.takeAgent [0, n + 4]).takeAgent [2]).agents := by
      by_cases h25 : 17 * m + 25 ≤ u
      · obtain ⟨Xf, -, hf⟩ := solo_final_mem m n
        rw [hf u h25, ← hf (17 * m + 25) (Nat.le_refl _)]
        exact key 3 (Nat.le_refl _)
      · obtain ⟨k, rfl⟩ : ∃ k, u = 17 * m + 22 + k := ⟨u - (17 * m + 22), by omega⟩
        exact key k (by omega)
    rw [all]
    show assoc [j] ((X.agents.filter fun e => decide (e.1 ≠ [0, n + 4])).filter
      fun e => decide (e.1 ≠ [2])) = some γ
    rw [assoc_filter_ne, ite_neg' (by ports_differ), assoc_filter_ne, ite_neg' (by ports_differ)]
    exact h16

/-- `RdAt m n T0 a T`: beside the first thread on the net for `(m + 1) + n`,
a thread that starts as `T0` and acts after each action of the first has
only read for its first `a` actions, and is then `T`. -/
def RdAt (m n : Nat) (T0 : XThread Arith) (a : Nat) (T : XThread Arith) : Prop :=
  XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a = T ∧
  ∀ a', a' < a →
    (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a')).1 =
        (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1 ∧
    (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a' + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a')).2.2 = 0

theorem RdAt.start (m n : Nat) (T0 : XThread Arith) : RdAt m n T0 0 T0 :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- One more action that reads. -/
theorem RdAt.step {m n : Nat} {T0 T T' : XThread Arith} {a : Nat} (h : RdAt m n T0 a T)
    (hact : XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (a + 1)).1 T = ((XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1,
        T', 0)) :
    RdAt m n T0 (a + 1) T' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun a' ha' => ?_⟩
  · show (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a)).2.1 = T'
    rw [h1, hact]
  · by_cases e : a' = a
    · rw [e, h1, hact]
      exact ⟨rfl, rfl⟩
    · exact h2 a' (by omega)

theorem RdAt.cast {m n : Nat} {T0 T : XThread Arith} {a a' : Nat} (h : RdAt m n T0 a T)
    (e : a = a') : RdAt m n T0 a' T := by
  subst e
  exact h

/-- **An agent that leads nowhere costs three actions**: the thread pops
it, reads its segment, and finds no second segment at the other end. -/
theorem RdAt.pass3 {m n : Nat} {T0 : XThread Arith} {a : Nat} {i : Id} {α : Arith}
    {l : List (Id × Arith)} {q : Port} (h : RdAt m n T0 a ⟨(i, α) :: l, .idle⟩)
    (hal : assoc i (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (a + 1)).1.agents = some α)
    (hlook : assoc ((i, 0) : Port) (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (a + 2)).1.wires = some q)
    (hq : ¬ q.2 = 0)
    (hstop : nextSeg (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (a + 3)).1.wires q (i, 0) = none) :
    RdAt m n T0 (a + 3) ⟨l, .idle⟩ :=
  ((h.step (XMach.act_idle_pos (e := (i, α)) hal)).step (XMach.act_look hlook)).step
    (XMach.act_seek_stop (ite_neg' hq) hstop)

/-- **An agent that is gone costs one action.** -/
theorem RdAt.gone {m n : Nat} {T0 : XThread Arith} {a : Nat} {i : Id} {α : Arith}
    {l : List (Id × Arith)} (h : RdAt m n T0 a ⟨(i, α) :: l, .idle⟩)
    (hg : assoc i (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (a + 1)).1.agents = none) : RdAt m n T0 (a + 1) ⟨l, .idle⟩ :=
  h.step (XMach.act_idle_neg (e := (i, α)) fun h' => by
    have h'' : assoc i (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩
        (a + 1)).1.agents = some α := h'
    rw [hg] at h''
    cases h'')

/-- **The chain, three actions for each successor**: the thread is ahead of
the first, and finds each successor in memory with nothing written above
it. -/
theorem RdAt.chain {m n : Nat} {T0 : XThread Arith} {tl : List (Id × Arith)} :
    ∀ r, r ≤ m → RdAt m n T0 (3 * (m - r)) ⟨chainL n r ++ tl, .idle⟩ →
      RdAt m n T0 (3 * m) ⟨tl, .idle⟩
  | 0, _, h => h
  | r + 1, hr, h => by
    have h' : RdAt m n T0 (3 * (m - (r + 1)))
        ⟨([n + 3 + r + 1], .succ) :: (chainL n r ++ tl), .idle⟩ := h
    have hal := solo_alive m n (m - (r + 1)) (by omega) (n + 3 + r + 1) .succ
      (3 * (m - (r + 1)) + 1) (by omega) (by omega) (by omega)
      ((start_sum m n).chain.live (n + 3 + r + 1) (by omega) (by omega))
    have h3 := h'.pass3 hal (solo_look_chain m n (by omega) (by omega) _)
      (show ¬ (1 : Nat) = 0 by decide)
      (solo_stop_chain m n (by omega) (by omega) (by omega))
    exact RdAt.chain r (by omega) (h3.cast (by omega))

/-- **The top of the second argument and the walk along the adders.**  A
thread that comes to it after `a0` actions reads on to the first adder,
which is gone, and from there along the adders that the first thread has
made, one hop for each round whose first segment is written when the thread
gets there: `K + 1` hops when `16 * K + 5 ≤ a0 < 16 * K + 21`.  Then it
stops: `4 + K` actions in all. -/
theorem RdAt.walk {m n : Nat} {T0 : XThread Arith} {α : Arith} {l : List (Id × Arith)}
    {K a0 : Nat} (h6 : 6 ≤ a0) (hK1 : 16 * K + 5 ≤ a0) (hK2 : a0 < 16 * K + 21)
    (hKm : K + 1 ≤ m) (hx : assoc [n + 3] (sum (m + 1) n).agents = some α)
    (h : RdAt m n T0 a0 ⟨([n + 3], α) :: l, .idle⟩) :
    RdAt m n T0 (a0 + 4 + K) ⟨l, .idle⟩ := by
  have hal := solo_snd_forever m n (j := n + 3) (by omega) (Nat.le_refl _) hx (a0 + 1)
  have h1 := h.step (XMach.act_idle_pos (e := ([n + 3], α)) hal)
  have h2 := h1.step (XMach.act_look (solo_look_top m n _))
  have h3 := h2.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide))
    (solo_hop_top m n (by omega)))
  have walk : ∀ d, d ≤ K → ∀ x, x + d = n + 3 + m + 1 →
      RdAt m n T0 (a0 + 3 + d)
        ⟨l, .seek [n + 3] α (wprev m n x) ([0, x], 1)⟩ := by
    intro d
    induction d with
    | zero =>
      intro _ x hx'
      have e : x = n + 3 + m + 1 := by omega
      subst e
      have ew : wprev m n (n + 3 + m + 1) = ([1], 1) := by
        unfold wprev
        exact ite_pos' rfl
      rw [ew]
      exact h3.cast (by omega)
    | succ d ih =>
      intro hd x hx'
      have hp := ih (by omega) (x + 1) (by omega)
      have hop := solo_hop m n (t := x) (u := a0 + 3 + d + 1) (by omega) (by omega)
        (by omega)
      have h4 := hp.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide)) hop)
      have ew : wprev m n x = ([0, x + 1], 1) := by
        unfold wprev
        exact ite_neg' (by omega)
      rw [ew]
      exact h4.cast (by omega)
  have hw := walk K (Nat.le_refl _) (n + 3 + m + 1 - K) (by omega)
  have hs := solo_walk_stop m n (x := n + 3 + m + 1 - K) (u := a0 + 3 + K + 1) (by omega)
    (by omega) (by omega)
  exact (hw.step (XMach.act_seek_stop (seek_aux_none _ _ 1 (by decide)) hs)).cast (by omega)

/-- **The rest of the second argument, three actions for each agent**, at
any moment of the run. -/
theorem RdAt.snd {m n : Nat} {T0 : XThread Arith} {l : List (Id × Arith)} :
    ∀ (k a : Nat), k + 1 ≤ n →
      RdAt m n T0 a ⟨sndL k ++ l, .idle⟩ → RdAt m n T0 (a + 3 * k) ⟨l, .idle⟩
  | 0, _, _, h => h
  | k + 1, a, hk, h => by
    have h' : RdAt m n T0 a ⟨([k + 4], .succ) :: (sndL k ++ l), .idle⟩ := h
    have hx : assoc [k + 4] (sum (m + 1) n).agents = some Arith.succ :=
      sum_assoc_base m n (e := ([k + 4], Arith.succ))
        (List.mem_append_left _ (sndL_mem n k (by omega)))
    have hal := solo_snd_forever m n (j := k + 4) (by omega) (by omega) hx (a + 1)
    have h3 := h'.pass3 hal (solo_look_snd m n (j := k + 4) (by omega) (by omega) _).1
      (show ¬ (1 : Nat) = 0 by decide) (solo_look_snd m n (j := k + 4) (by omega) (by omega) _).2
    exact (RdAt.snd k (a + 3) (by omega) h3).cast (by omega)

/-- The list of the second of two threads on the net for `(m + 1) + n`,
`n` not zero. -/
theorem two_list (m n' : Nat) :
    (sum (m + 1) (n' + 1)).agents.drop (0 + 1) ++ (sum (m + 1) (n' + 1)).agents.take (0 + 1) =
      chainL (n' + 1) m ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        [([1], .add), ([2], .zero), ([3], .zero), ([n' + 1 + 3 + m + 1], .succ)])) := by
  rw [turn_list m (n' + 1) 0 (by omega)]
  show chainL (n' + 1) m ++ (([n' + 1 + 3], Arith.succ) :: ((sndL n' ++
    [([1], Arith.add), ([2], .zero), ([3], .zero)]) ++ [([n' + 1 + 3 + m + 1], .succ)])) =
    chainL (n' + 1) m ++ (([n' + 1 + 3], Arith.succ) :: (sndL n' ++
      ([([1], Arith.add), ([2], .zero), ([3], .zero)] ++ [([n' + 1 + 3 + m + 1], .succ)])))
  rw [List.append_assoc]

/-- **The second of two threads comes to the zero of the first argument
after exactly `3 * m + 3 * n' + 5 + K` actions**, all of which read, on the
net for `(m + 1) + (n' + 1)`, when `16 * K + 5 ≤ 3 * m < 16 * K + 21`:
three actions for each successor of its chain, `4 + K` for the top of the second argument and the
walk, three for each agent below it, one for the first adder. -/
theorem two_reader_at_zero (m n' K : Nat) (hm : 4 ≤ m) (hK1 : 16 * K + 5 ≤ 3 * m)
    (hK2 : 3 * m < 16 * K + 21) :
    RdAt m (n' + 1) ⟨chainL (n' + 1) m ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        [([1], .add), ([2], .zero), ([3], .zero), ([n' + 1 + 3 + m + 1], .succ)])), .idle⟩
      (3 * m + 3 * n' + 5 + K)
      ⟨[([2], .zero), ([3], .zero), ([n' + 1 + 3 + m + 1], .succ)], .idle⟩ := by
  have h0 := RdAt.start m (n' + 1) ⟨chainL (n' + 1) m ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
    [([1], .add), ([2], .zero), ([3], .zero), ([n' + 1 + 3 + m + 1], .succ)])), .idle⟩
  have h1 := RdAt.chain m (Nat.le_refl _) (h0.cast (by omega))
  have hx : assoc [n' + 1 + 3] (sum (m + 1) (n' + 1)).agents = some Arith.succ :=
    sum_assoc_base m (n' + 1) (e := ([n' + 1 + 3], Arith.succ))
      (List.mem_append_left _ (sndL_mem (n' + 1) n' (by omega)))
  have h2 := RdAt.walk (by omega) hK1 hK2 (by omega) hx h1
  have h3 := RdAt.snd n' (3 * m + 4 + K) (by omega) h2
  have h4 := h3.gone (solo_gone5 m (n' + 1) (u := 3 * m + 4 + K + 3 * n' + 1) (by omega)).2
  exact h4.cast (by omega)

/-- **And it is ready to take that zero four actions later**, when it finds
the segment to the last adder written and the adder in memory: when it
comes to the zero after `17 * m + 7` actions at least and `17 * m + 16` at
most. -/
theorem two_reader_ready (m n' K : Nat) (hm : 4 ≤ m) (hK1 : 16 * K + 5 ≤ 3 * m)
    (hK2 : 3 * m < 16 * K + 21) (h1 : 17 * m + 7 ≤ 3 * m + 3 * n' + 5 + K)
    (h2 : 3 * m + 3 * n' + 5 + K ≤ 17 * m + 16) :
    RdAt m (n' + 1) ⟨chainL (n' + 1) m ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        [([1], .add), ([2], .zero), ([3], .zero), ([n' + 1 + 3 + m + 1], .succ)])), .idle⟩
      (3 * m + 3 * n' + 5 + K + 4)
      ⟨[([3], .zero), ([n' + 1 + 3 + m + 1], .succ)],
        .ready [2] [0, n' + 1 + 4] .zero .add⟩ := by
  have h := two_reader_at_zero m n' K hm hK1 hK2
  have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * m + 3 * n' + 5 + K + 1) (by omega)
    (by omega) (by omega) (sum_zero_agent m (n' + 1))
  have s1 := h.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
  have s2 := s1.step (XMach.act_look (solo_look_two m (n' + 1) _))
  have s3 := s2.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide))
    ((solo_seek_two m (n' + 1) (by omega) _).1 (by omega)))
  have hA := solo_adder_alive m (n' + 1) (by omega)
    (u := 3 * m + 3 * n' + 5 + K + 1 + 1 + 1 + 1) (by omega) (by omega)
  exact s3.step (XMach.act_seek_found (c := ([0, n' + 1 + 4], 0)) ((ite_pos' rfl).trans hA)
    ⟨by ports_differ, rfl⟩)

/-- **The action after which the second of two threads in turn comes to the
zero of the first argument**, on the net for `(m + 1) + n` with `n` not
zero: three actions for each of the `m` successors of its chain, three and
a walk of `(3 * m + 11) / 16` hops from the top of the second argument,
three for each other agent of the second argument, one for the first
adder. -/
def twoAt (m n : Nat) : Nat := 3 * m + 3 * n + 1 + (3 * m + 11) / 16

/-- The two threads at the start, `n` not zero. -/
theorem two_init (m n' : Nat) :
    XMach.init (sum (m + 1) (n' + 1)) 2 = ⟨sum (m + 1) (n' + 1),
      [⟨(sum (m + 1) (n' + 1)).agents, .idle⟩, ⟨chainL (n' + 1) m ++
          (([n' + 1 + 3], .succ) :: (sndL n' ++
        [([1], .add), ([2], .zero), ([3], .zero), ([n' + 1 + 3 + m + 1], .succ)])), .idle⟩]⟩ :=
  (XMach.init_succ (sum (m + 1) (n' + 1)) 1).trans (by
    rw [← two_list m n']
    rfl)

/-- **The way into the race, to the action.**  When the second thread
comes to the zero of the first argument after `17 * m + 7` actions at least
and `17 * m + 16` at most, then four actions later the memory and the first
thread are those of one thread alone, and the second thread is ready to
take that zero and the last adder. -/
theorem two_entry_exact (m n' K : Nat) (hm : 4 ≤ m) (hK1 : 16 * K + 5 ≤ 3 * m)
    (hK2 : 3 * m < 16 * K + 21) (h1 : 17 * m + 7 ≤ 3 * m + 3 * n' + 5 + K)
    (h2 : 3 * m + 3 * n' + 5 + K ≤ 17 * m + 16) :
    ∃ c, (XMach.init (sum (m + 1) (n' + 1)) 2).trace xsys (fun i => i % 2)
        (2 * (3 * m + 3 * n' + 5 + K + 4)) =
      (⟨(XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩
          (3 * m + 3 * n' + 5 + K + 4)).1,
        [(XMach.solo xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩
            (3 * m + 3 * n' + 5 + K + 4)).2,
          ⟨[([3], .zero), ([n' + 1 + 3 + m + 1], .succ)],
            .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩, c) := by
  have R := two_reader_ready m n' K hm hK1 hK2 h1 h2
  have tr := XMach.trace_readers (xs := xsys) (X := sum (m + 1) (n' + 1))
    (T₀ := ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩)
    (Ts := [⟨chainL (n' + 1) m ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        [([1], .add), ([2], .zero), ([3], .zero), ([n' + 1 + 3 + m + 1], .succ)])), .idle⟩])
    (A := 3 * m + 3 * n' + 5 + K + 4)
    (fun T hT a ha => by
      rw [List.mem_singleton.1 hT]
      exact R.2 a ha) (3 * m + 3 * n' + 5 + K + 4) (Nat.le_refl _)
  rw [two_init]
  exact ⟨_, by
    rw [← R.1]
    exact tr⟩

/-- **Two threads in turn, a size in the race, to the action.**  On the net
for `(m + 1) + n`, with `m` from four on: when the second thread comes to
the zero of the first argument after `17 * m + 7 + d` actions, `d` up to
nine, it takes part in the race for the last pair, and the work of the
whole run is exactly `raceWork m n d`. -/
theorem two_threads_race_at (m n : Nat) (hm : 4 ≤ m) (h1 : 17 * m + 7 ≤ twoAt m n)
    (h2 : twoAt m n ≤ 17 * m + 16) :
    (XMach.init (sum (m + 1) n) 2).Total xsys (fun i => i % 2)
      (raceWork m n (twoAt m n - (17 * m + 7))) := by
  unfold twoAt at h1 h2 ⊢
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, (3 * (m' + 1) + 11) / 16 = K + 1 :=
    ⟨(3 * (m' + 1) + 11) / 16 - 1, by omega⟩
  rw [hK] at h1 h2 ⊢
  obtain ⟨c, htr⟩ := two_entry_exact (m' + 1) n' K hm (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨V, todo, rest, p5, q5, p6, q6, p7, q7, p8, q8, B, s11, s12, s13, s14, s15⟩ :=
    race_write (m' + 1) (n' + 1) (by omega)
  obtain ⟨s16, s17, s18, s19, s20⟩ := B.states
  obtain ⟨d, hd⟩ : ∃ d, 3 * (m' + 1) + 3 * n' + 5 + K = 17 * (m' + 1) + 7 + d :=
    ⟨3 * (m' + 1) + 3 * n' + 5 + K - (17 * (m' + 1) + 7), by omega⟩
  have e0 : 3 * (m' + 1) + 3 * (n' + 1) + 1 + (K + 1) - (17 * (m' + 1) + 7) = d := by omega
  rw [e0]
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
      d = 9 := by omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- A thread that is at rest beside the first stays at rest. -/
theorem reader_rest {X : XNet Arith} {F0 T0 : XThread Arith} {a : Nat}
    (h : XMach.reader xsys X F0 T0 a = ⟨[], .idle⟩) :
    ∀ k, XMach.reader xsys X F0 T0 (a + k) = ⟨[], .idle⟩
  | 0 => h
  | k + 1 =>
    (congrArg (fun T => (XMach.act xsys (XMach.solo xsys X F0 (a + k + 1)).1 T).2.1)
      (reader_rest h k)).trans rfl

/-- And its actions read. -/
theorem RdAt.rest {m n : Nat} {T0 : XThread Arith} {a : Nat}
    (h : RdAt m n T0 a ⟨[], .idle⟩) : ∀ b, RdAt m n T0 (a + b) ⟨[], .idle⟩
  | 0 => h
  | b + 1 => (RdAt.rest h b).step rfl

/-- What a sequence of states comes to at a rate that is one for the first
`B` of them and zero from then on. -/
theorem seqTally_exact {κ : XThread Arith → Nat} {R : Nat → XThread Arith} {B : Nat}
    (h1 : ∀ j, j < B → κ (R j) = 1) (h0 : ∀ j, B ≤ j → κ (R j) = 0) :
    ∀ a, (a ≤ B → seqTally κ R a = a) ∧ (B ≤ a → seqTally κ R a = B)
  | 0 => ⟨fun _ => rfl, fun h => by
      have e : B = 0 := by omega
      subst e
      rfl⟩
  | a + 1 => by
    obtain ⟨i1, i2⟩ := seqTally_exact h1 h0 a
    constructor
    · intro h
      show seqTally κ R a + κ (R a) = a + 1
      rw [i1 (by omega), h1 a (by omega)]
    · intro h
      show seqTally κ R a + κ (R a) = B
      by_cases hlt : a < B
      · rw [i1 (by omega), h1 a hlt]
        omega
      · rw [i2 (by omega), h0 a (by omega)]
        rfl

/-- **A second thread that only reads and comes to rest: the two threads in
turn do exactly the work of the first alone and the actions of the
second.**  On the net for `(m + 1) + n`, if the second thread only reads,
is at rest after `b + 1` actions and not after `b`, the work of the whole
run is `soloWork (m + 1) n + (b + 1)`. -/
theorem quiet_total {m n : Nat} {T0 : XThread Arith} {B b : Nat}
    (h : RdAt m n T0 B ⟨[], .idle⟩) (hB : B = b + 1)
    (hb : XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 b ≠ ⟨[], .idle⟩) :
    (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T0]⟩ : XMach Arith).Total xsys
        (fun i => i % 2)
      (soloWork (m + 1) n + B) := by
  have hbusy : ∀ a, a < B → XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a ≠
      ⟨[], .idle⟩ := fun a ha e => by
    have h' := reader_rest e (b - a)
    rw [show a + (b - a) = b by omega] at h'
    exact hb h'
  have hall : ∀ T, T ∈ [T0] → ∀ a,
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).1 =
          (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1 ∧
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).2.2 = 0 := by
    intro T hT a
    rw [List.mem_singleton.1 hT]
    by_cases ha : a < B
    · exact h.2 a ha
    · obtain ⟨d, rfl⟩ : ∃ d, a = B + d := ⟨a - B, by omega⟩
      exact (h.rest (d + 1)).2 (B + d) (by omega)
  have even : ∀ a, soloWork (m + 1) n + B ≤ a →
      (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T0]⟩ : XMach Arith).work xsys
          (fun i => i % 2) (2 * a) = soloWork (m + 1) n + B := by
    intro a ha
    have ht := XMach.tally_readers XThread.busy (xs := xsys) (X := sum (m + 1) n)
      (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩) (Ts := [T0]) (A := a)
      (fun T hT a' _ => hall T hT a') a (Nat.le_refl a)
    have e1 : seqTally XThread.busy (fun j => (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ j).2) a = soloWork (m + 1) n := by
      rw [← XMach.tally_one XThread.busy xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ a]
      obtain ⟨hr, hw, -⟩ := solo_work (m + 1) n
      rw [XMach.init_one] at hr hw
      obtain ⟨d, rfl⟩ : ∃ d, a = soloWork (m + 1) n + d := ⟨a - soloWork (m + 1) n, by omega⟩
      exact (XMach.work_rest (fun _ => 0) hr d).trans hw
    have e2 : seqTally XThread.busy (XMach.reader xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ T0) a = B :=
      (seqTally_exact (fun j hj => XThread.busy_of_ne_rest (hbusy j hj)) (fun j hj => by
        obtain ⟨d, rfl⟩ : ∃ d, j = B + d := ⟨j - B, by omega⟩
        exact (congrArg XThread.busy (h.rest d).1).trans rfl) a).2 (by omega)
    have ht' : (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩,
        T0]⟩ : XMach Arith).tally XThread.busy xsys (fun i => i % 2) (2 * a) =
        seqTally XThread.busy (fun j => (XMach.solo xsys (sum (m + 1) n)
            ⟨(sum (m + 1) n).agents, .idle⟩ j).2) a +
          seqTally XThread.busy (XMach.reader xsys (sum (m + 1) n)
              ⟨(sum (m + 1) n).agents, .idle⟩ T0) a := ht
    show (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩,
        T0]⟩ : XMach Arith).tally XThread.busy xsys (fun i => i % 2) (2 * a) = _
    rw [ht', e1, e2]
  refine ⟨2 * (soloWork (m + 1) n + B), fun i hi => ?_⟩
  have lo := XMach.work_mono (xs := xsys) (fun i => i % 2)
      (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T0]⟩ : XMach Arith)
    (show 2 * (i / 2) ≤ i by omega)
  have up := XMach.work_mono (xs := xsys) (fun i => i % 2)
      (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T0]⟩ : XMach Arith)
    (show i ≤ 2 * (i / 2 + 1) by omega)
  rw [even (i / 2) (by omega)] at lo
  rw [even (i / 2 + 1) (by omega)] at up
  omega

/-- **Two threads in turn, a short second argument, to the action.**  When
the second thread comes to the zero of the first argument after
`17 * m + 6` actions at most, it passes it before the segment to the last
adder is written, reads the zero of the second argument, finds the top
successor gone and rests: seven actions more.  The work of the whole run
is exactly that of one thread and those actions. -/
theorem two_threads_early (m n : Nat) (hm : 4 ≤ m) (hn : 1 ≤ n)
    (h : twoAt m n ≤ 17 * m + 6) :
    (XMach.init (sum (m + 1) n) 2).Total xsys (fun i => i % 2)
      (soloWork (m + 1) n + (twoAt m n + 7)) := by
  unfold twoAt at h ⊢
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, (3 * m + 11) / 16 = K + 1 := ⟨(3 * m + 11) / 16 - 1, by omega⟩
  rw [hK] at h ⊢
  have r0 := two_reader_at_zero m n' K hm (by omega) (by omega)
  have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * m + 3 * n' + 5 + K + 1) (by omega)
    (by omega) (by omega) (sum_zero_agent m (n' + 1))
  have r1 := r0.pass3 hal (solo_look_two m (n' + 1) _) (show ¬ (1 : Nat) = 0 by decide)
    ((solo_seek_two m (n' + 1) (by omega) _).2 (by omega))
  have hx3 : assoc [3] (sum (m + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base m (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hal3 := solo_alive_zero m (n' + 1) (j := 3) (u := 3 * m + 3 * n' + 5 + K + 3 + 1) (by omega)
    (by omega) (by omega) hx3
  have r2 := r1.pass3 hal3 (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).1
    (show ¬ (1 : Nat) = 0 by decide)
    (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).2
  have r3 := r2.gone (solo_gone5 m (n' + 1) (u := 3 * m + 3 * n' + 5 + K + 3 + 3 + 1) (by omega)).1
  rw [two_init]
  exact (quiet_total r3 rfl (fun e => by
    rw [r2.1] at e
    cases e)).cast (by omega)

/-- **Two threads in turn, a second argument just past the race, to the
action.**  When the second thread comes to the zero of the first argument
after `17 * m + 17` actions at least and `17 * m + 20` at most, it finds
it, reads on to the last adder and finds that gone: four actions.  Then the
zero of the second argument and the top successor: eight actions in all
before it rests. -/
theorem two_threads_late (m n : Nat) (hm : 4 ≤ m) (hn : 1 ≤ n)
    (h1 : 17 * m + 17 ≤ twoAt m n) (h2 : twoAt m n ≤ 17 * m + 20) :
    (XMach.init (sum (m + 1) n) 2).Total xsys (fun i => i % 2)
      (soloWork (m + 1) n + (twoAt m n + 8)) := by
  unfold twoAt at h1 h2 ⊢
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, (3 * m + 11) / 16 = K + 1 := ⟨(3 * m + 11) / 16 - 1, by omega⟩
  rw [hK] at h1 h2 ⊢
  have r0 := two_reader_at_zero m n' K hm (by omega) (by omega)
  have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * m + 3 * n' + 5 + K + 1) (by omega)
    (by omega) (by omega) (sum_zero_agent m (n' + 1))
  have s1 := r0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
  have s2 := s1.step (XMach.act_look (solo_look_two m (n' + 1) _))
  have s3 := s2.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide))
    ((solo_seek_two m (n' + 1) (by omega) _).1 (by omega)))
  have hg := solo_gone_adder m (n' + 1) (u := 3 * m + 3 * n' + 5 + K + 1 + 1 + 1 + 1) (by omega)
  have s4 := s3.step (XMach.act_seek_stop ((ite_pos' rfl).trans hg)
    (solo_stop_adder m (n' + 1) (by omega) _))
  have hx3 : assoc [3] (sum (m + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base m (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have r2 := s4.pass3 (solo_snd_forever m (n' + 1) (j := 3) (by omega) (by omega) hx3 _)
    (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).1
    (show ¬ (1 : Nat) = 0 by decide)
    (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).2
  have r3 := r2.gone (solo_gone5 m (n' + 1) (by omega)).1
  rw [two_init]
  exact (quiet_total r3 rfl (fun e => by
    rw [r2.1] at e
    cases e)).cast (by omega)

/-- **Two threads in turn, a long second argument, to the action.**  When
the second thread comes to the zero of the first argument after
`17 * m + 21` actions or more, the first thread has taken it: one action.
Then the zero of the second argument and the top successor: five actions in
all before it rests. -/
theorem two_threads_after (m n : Nat) (hm : 4 ≤ m) (hn : 1 ≤ n)
    (h : 17 * m + 21 ≤ twoAt m n) :
    (XMach.init (sum (m + 1) n) 2).Total xsys (fun i => i % 2)
      (soloWork (m + 1) n + (twoAt m n + 5)) := by
  unfold twoAt at h ⊢
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, (3 * m + 11) / 16 = K + 1 := ⟨(3 * m + 11) / 16 - 1, by omega⟩
  rw [hK] at h ⊢
  have r0 := two_reader_at_zero m n' K hm (by omega) (by omega)
  have r1 := r0.gone (solo_gone_zero m (n' + 1) (by omega))
  have hx3 : assoc [3] (sum (m + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base m (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have r2 := r1.pass3 (solo_snd_forever m (n' + 1) (j := 3) (by omega) (by omega) hx3 _)
    (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).1
    (show ¬ (1 : Nat) = 0 by decide)
    (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).2
  have r3 := r2.gone (solo_gone5 m (n' + 1) (by omega)).1
  rw [two_init]
  exact (quiet_total r3 rfl (fun e => by
    rw [r2.1] at e
    cases e)).cast (by omega)

/-- The two threads at the start when the second argument is zero. -/
theorem two_init_zero (m : Nat) :
    XMach.init (sum (m + 1) 0) 2 = ⟨sum (m + 1) 0,
      [⟨(sum (m + 1) 0).agents, .idle⟩, ⟨chainL 0 m ++
        [([1], .add), ([2], .zero), ([0 + 3], .zero), ([0 + 3 + m + 1], .succ)], .idle⟩]⟩ :=
  (XMach.init_succ (sum (m + 1) 0) 1).trans (by
    have e : (sum (m + 1) 0).agents.drop (0 + 1) ++ (sum (m + 1) 0).agents.take (0 + 1) =
        chainL 0 m ++
          [([1], .add), ([2], .zero), ([0 + 3], .zero), ([0 + 3 + m + 1], .succ)] :=
      (turn_list m 0 0 (by omega)).trans rfl
    rw [← e]
    rfl)

/-- **Two threads in turn, second argument zero, to the action.**  The
second thread finds the first adder gone, passes the zero of the first
argument, and walks along the adders from the zero of the second:
`3 * m + 8 + (3 * m + 15) / 16` actions before it rests. -/
theorem two_threads_zero (m : Nat) (hm : 4 ≤ m) :
    (XMach.init (sum (m + 1) 0) 2).Total xsys (fun i => i % 2)
      (soloWork (m + 1) 0 + (3 * m + 8 + (3 * m + 15) / 16)) := by
  obtain ⟨K, hK⟩ : ∃ K, (3 * m + 15) / 16 = K + 1 := ⟨(3 * m + 15) / 16 - 1, by omega⟩
  rw [hK]
  have h0 := RdAt.start m 0 ⟨chainL 0 m ++
    [([1], .add), ([2], .zero), ([0 + 3], .zero), ([0 + 3 + m + 1], .succ)], .idle⟩
  have h1 := RdAt.chain m (Nat.le_refl _) (h0.cast (by omega))
  have h2 := h1.gone (solo_gone5 m 0 (by omega)).2
  have hal := solo_alive_zero m 0 (j := 2) (u := 3 * m + 1 + 1) (by omega) (by omega)
    (by omega) (sum_zero_agent m 0)
  have h3 := h2.pass3 hal (solo_look_two m 0 _) (show ¬ (1 : Nat) = 0 by decide)
    ((solo_seek_two m 0 (by omega) _).2 (by omega))
  have hx3 : assoc [0 + 3] (sum (m + 1) 0).agents = some Arith.zero :=
    sum_assoc_base m 0 (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h4 := RdAt.walk (K := K) (by omega) (by omega) (by omega) (by omega) hx3 h3
  have h5 := h4.gone (solo_gone5 m 0 (by omega)).1
  rw [two_init_zero]
  exact (quiet_total h5 rfl (fun e => by
    rw [h4.1] at e
    cases e)).cast (by omega)

/-- **The work of two threads in turn on the net for `(m + 1) + n`.**  It
is that of one thread and the actions of the second before it rests,
unless the second comes to the zero of the first argument at one of the
ten moments of the race. -/
def twoWork (m n : Nat) : Nat :=
  if n = 0 then soloWork (m + 1) 0 + (3 * m + 8 + (3 * m + 15) / 16)
  else if twoAt m n ≤ 17 * m + 6 then soloWork (m + 1) n + (twoAt m n + 7)
  else if twoAt m n ≤ 17 * m + 16 then raceWork m n (twoAt m n - (17 * m + 7))
  else if twoAt m n ≤ 17 * m + 20 then soloWork (m + 1) n + (twoAt m n + 8)
  else soloWork (m + 1) n + (twoAt m n + 5)

/-- **Two threads in turn add in exactly `twoWork m n` actions that are
not rests, for every size with `m` from four on.** -/
theorem two_threads_total (m n : Nat) (hm : 4 ≤ m) :
    (XMach.init (sum (m + 1) n) 2).Total xsys (fun i => i % 2) (twoWork m n) := by
  unfold twoWork
  split
  · rename_i h0
    subst h0
    exact two_threads_zero m hm
  · rename_i hn
    split
    · rename_i h
      exact two_threads_early m n hm (by omega) h
    · rename_i h1
      split
      · rename_i h2
        exact two_threads_race_at m n hm (by omega) h2
      · rename_i h2
        split
        · rename_i h3
          exact two_threads_late m n hm (by omega) (by omega) h3
        · rename_i h3
          exact two_threads_after m n hm (by omega) (by omega)

example : (XMach.init (sum 21 94) 2).Total xsys (fun i => i % 2) 1496 :=
  (two_threads_total 20 94 (by decide)).cast (by decide)

example : (XMach.init (sum 21 97) 2).Total xsys (fun i => i % 2) 1530 :=
  (two_threads_total 20 97 (by decide)).cast (by decide)

example : (XMach.init (sum 5 23) 2).Total xsys (fun i => i % 2) 285 :=
  (two_threads_total 4 23 (by decide)).cast (by decide)

example : (XMach.init (sum 21 93) 2).Total xsys (fun i => i % 2) 1105 :=
  (two_threads_total 20 93 (by decide)).cast (by decide)

example : (XMach.init (sum 21 98) 2).Total xsys (fun i => i % 2) 1136 :=
  (two_threads_total 20 98 (by decide)).cast (by decide)

example : (XMach.init (sum 5 0) 2).Total xsys (fun i => i % 2) 144 :=
  (two_threads_total 4 0 (by decide)).cast (by decide)

example (i : Nat) : (XMach.init (sum 21 94) 2).work xsys (fun i => i % 2) i ≤ 1496 :=
  ((two_threads_total 20 94 (by decide)).cast (by decide)).le i

/-- **The chain of the thread numbered `t + 1`**, which starts `t + 1`
successors below the top: three actions for each successor. -/
theorem RdAt.chain_turn {m n t : Nat} {T0 : XThread Arith} {tl : List (Id × Arith)} :
    ∀ r, r + t ≤ m → RdAt m n T0 (3 * (m - t - r)) ⟨chainL n r ++ tl, .idle⟩ →
      RdAt m n T0 (3 * (m - t)) ⟨tl, .idle⟩
  | 0, _, h => h
  | r + 1, hr, h => by
    have h' : RdAt m n T0 (3 * (m - t - (r + 1)))
        ⟨([n + 3 + r + 1], .succ) :: (chainL n r ++ tl), .idle⟩ := h
    have hal := solo_alive m n (m - (r + 1)) (by omega) (n + 3 + r + 1) .succ
      (3 * (m - t - (r + 1)) + 1) (by omega) (by omega) (by omega)
      ((start_sum m n).chain.live (n + 3 + r + 1) (by omega) (by omega))
    have h3 := h'.pass3 hal (solo_look_chain m n (by omega) (by omega) _)
      (show ¬ (1 : Nat) = 0 by decide)
      (solo_stop_chain m n (by omega) (by omega) (by omega))
    exact RdAt.chain_turn r (by omega) (h3.cast (by omega))

/-- A successor of the chain is gone once its round has taken it. -/
theorem solo_gone_top (m n : Nat) {q u : Nat} (hq : q ≤ m) (hu : 17 * (m - q) + 5 ≤ u) :
    assoc [n + 3 + q + 1] (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ u).1.agents = none := by
  by_cases e : q = m
  · subst e
    exact (solo_gone5 q n (by omega)).1
  · have hg := solo_gone_succ m n (d := m - q) (by omega) (by omega) hu
    rw [show n + 3 + m + 1 - (m - q) = n + 3 + q + 1 by omega] at hg
    exact hg

/-- **The top successors at the end of a list, one action for each**: a
thread that comes to them after their rounds finds them gone, and is at
rest after the last. -/
theorem RdAt.tops {m n r : Nat} {T0 : XThread Arith} :
    ∀ (s a : Nat), r + s ≤ m → 17 * (m - r) + 4 ≤ a →
      RdAt m n T0 a ⟨(chainL n (r + (s + 1))).take (s + 1), .idle⟩ →
      RdAt m n T0 (a + (s + 1)) ⟨[], .idle⟩ ∧ XMach.reader xsys (sum (m + 1) n)
          ⟨(sum (m + 1) n).agents, .idle⟩ T0 (a + s) ≠ ⟨[], .idle⟩
  | 0, a, hs, ha, h => by
    have h' : RdAt m n T0 a ⟨[([n + 3 + r + 1], .succ)], .idle⟩ := h
    refine ⟨h'.gone (solo_gone_top m n (by omega) (by omega)), fun e => ?_⟩
    have e' : XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T0 a =
        ⟨[], .idle⟩ := e
    rw [h'.1] at e'
    cases e'
  | s + 1, a, hs, ha, h => by
    have h' : RdAt m n T0 a
        ⟨([n + 3 + (r + (s + 1)) + 1], .succ) :: (chainL n (r + (s + 1))).take (s + 1),
          .idle⟩ := h
    have h1 := h'.gone (solo_gone_top m n (by omega) (by omega))
    obtain ⟨k1, k2⟩ := RdAt.tops s (a + 1) (by omega) (by omega) h1
    refine ⟨k1.cast (by omega), ?_⟩
    rw [show a + (s + 1) = a + 1 + s by omega]
    exact k2

/-- The list of the thread numbered `t + 1` on the net for `(m + 1) + n`,
`n` not zero. -/
theorem turn_list_succ (m n' t : Nat) (ht : t ≤ m) :
    (sum (m + 1) (n' + 1)).agents.drop (t + 1) ++ (sum (m + 1) (n' + 1)).agents.take (t + 1) =
      chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))) := by
  rw [turn_list m (n' + 1) t ht]
  show chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], Arith.succ) :: ((sndL n' ++
    [([1], Arith.add), ([2], .zero), ([3], .zero)]) ++ (chainL (n' + 1) (m - t + (t + 1))).take
        (t + 1))) =
    chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], Arith.succ) :: (sndL n' ++
      ([([1], Arith.add), ([2], .zero), ([3], .zero)] ++ (chainL (n' + 1) (m - t + (t + 1))).take
          (t + 1))))
  rw [List.append_assoc]

/-- The same when the second argument is zero. -/
theorem turn_list_zero (m t : Nat) (ht : t ≤ m) :
    (sum (m + 1) 0).agents.drop (t + 1) ++ (sum (m + 1) 0).agents.take (t + 1) =
      chainL 0 (m - t) ++ (([1], .add) :: ([2], .zero) :: ([0 + 3], .zero) ::
        (chainL 0 (m - t + (t + 1))).take (t + 1)) :=
  (turn_list m 0 t ht).trans rfl

/-- **The action after which the thread numbered `t + 1` comes to the zero
of the first argument**, on the net for `(m + 1) + n` with `n` not zero. -/
def turnAt (m n t : Nat) : Nat := 3 * (m - t) + 3 * n + 1 + (3 * (m - t) + 11) / 16

/-- What the zero of the first argument costs a thread that comes to it
after `A` actions, outside the race: three actions when it passes it before
the segment to the last adder is written, four when it reads on to the last
adder and finds it gone, one when the zero itself is gone. -/
def zeroCost (m A : Nat) : Nat := if A ≤ 17 * m + 6 then 3 else if A ≤ 17 * m + 20 then 4 else 1

/-- **The actions of the thread numbered `t + 1` before it rests**, when it
only reads. -/
def turnRest (m : Nat) : Nat → Nat → Nat
  | 0, t => 3 * (m - t) + 8 + (3 * (m - t) + 15) / 16 + t
  | n + 1, t => turnAt m (n + 1) t + zeroCost m (turnAt m (n + 1) t) + 3 + (t + 1)

/-- Those of the `k` threads after the first. -/
def turnSum (m n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => turnSum m n k + turnRest m n k

/-- **The thread numbered `t + 1` comes to the zero of the first argument
after exactly `3 * (m - t) + 3 * n' + 5 + K` actions**, all of which
read. -/
theorem turn_reader_at_zero (m n' t K : Nat) (ht : t + 2 ≤ m)
    (hK1 : 16 * K + 5 ≤ 3 * (m - t)) (hK2 : 3 * (m - t) < 16 * K + 21) :
    RdAt m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩
      (3 * (m - t) + 3 * n' + 5 + K)
      ⟨([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take (t + 1),
          .idle⟩ := by
  have h0 := RdAt.start m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩
  have h1 := RdAt.chain_turn (t := t) (m - t) (by omega) (h0.cast (by omega))
  have hx : assoc [n' + 1 + 3] (sum (m + 1) (n' + 1)).agents = some Arith.succ :=
    sum_assoc_base m (n' + 1) (e := ([n' + 1 + 3], Arith.succ))
      (List.mem_append_left _ (sndL_mem (n' + 1) n' (by omega)))
  have h2 := RdAt.walk (by omega) hK1 hK2 (by omega) hx h1
  have h3 := RdAt.snd n' (3 * (m - t) + 4 + K) (by omega) h2
  have h4 := h3.gone (solo_gone5 m (n' + 1) (u := 3 * (m - t) + 4 + K + 3 * n' + 1)
    (by omega)).2
  exact h4.cast (by omega)

/-- **The thread numbered `t + 1` only reads and comes to rest after
exactly `turnRest m n t` actions**, when it does not come to the zero of the
first argument at one of the ten moments of the race, and comes to its top
successors after their rounds. -/
theorem turn_reader_quiet (m n' t : Nat) (ht : t + 2 ≤ m)
    (hw : turnAt m (n' + 1) t ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m (n' + 1) t)
    (htop : 17 * t ≤ turnAt m (n' + 1) t) :
    ∃ b, turnRest m (n' + 1) t = b + 1 ∧
      RdAt m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩ (b + 1) ⟨[], .idle⟩ ∧
      XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩
          ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩ b ≠ ⟨[], .idle⟩ := by
  obtain ⟨K, hK⟩ : ∃ K, (3 * (m - t) + 11) / 16 = K + 1 :=
    ⟨(3 * (m - t) + 11) / 16 - 1, by omega⟩
  have eA : turnAt m (n' + 1) t = 3 * (m - t) + 3 * n' + 5 + K := by
    unfold turnAt
    omega
  rw [eA] at hw htop
  have hrest : turnRest m (n' + 1) t =
      turnAt m (n' + 1) t + zeroCost m (turnAt m (n' + 1) t) + 3 + (t + 1) := rfl
  have r0 := turn_reader_at_zero m n' t K ht (by omega) (by omega)
  have hx3 : assoc [3] (sum (m + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base m (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tail : ∀ a, 17 * t + 1 ≤ a →
      RdAt m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩ a
        ⟨([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take (t + 1), .idle⟩ →
      RdAt m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩ (a + 3 + (t + 1)) ⟨[], .idle⟩ ∧
        XMach.reader xsys (sum (m + 1) (n' + 1)) ⟨(sum (m + 1) (n' + 1)).agents, .idle⟩
            ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩ (a + 3 + t) ≠ ⟨[], .idle⟩ := fun a ha h => by
    have r2 := h.pass3 (solo_snd_forever m (n' + 1) (j := 3) (by omega) (by omega) hx3 _)
      (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).1
      (show ¬ (1 : Nat) = 0 by decide)
      (solo_look_snd m (n' + 1) (j := 3) (by omega) (by omega) _).2
    exact RdAt.tops (r := m - t) t (a + 3) (by omega) (by omega) r2
  by_cases h1 : 3 * (m - t) + 3 * n' + 5 + K ≤ 17 * m + 6
  · have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * (m - t) + 3 * n' + 5 + K + 1)
        (by omega) (by omega)
      (by omega) (sum_zero_agent m (n' + 1))
    have r1 := r0.pass3 hal (solo_look_two m (n' + 1) _) (show ¬ (1 : Nat) = 0 by decide)
      ((solo_seek_two m (n' + 1) (by omega) _).2 (by omega))
    obtain ⟨t1, t2⟩ := tail _ (by omega) r1
    have ez : zeroCost m (turnAt m (n' + 1) t) = 3 := by
      rw [eA]
      unfold zeroCost
      exact ite_pos' h1
    exact ⟨3 * (m - t) + 3 * n' + 5 + K + 3 + 3 + t, by omega, t1, t2⟩
  · by_cases h2 : 3 * (m - t) + 3 * n' + 5 + K ≤ 17 * m + 20
    · have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * (m - t) + 3 * n' + 5 + K + 1)
          (by omega) (by omega)
        (by omega) (sum_zero_agent m (n' + 1))
      have s1 := r0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
      have s2 := s1.step (XMach.act_look (solo_look_two m (n' + 1) _))
      have s3 := s2.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide))
        ((solo_seek_two m (n' + 1) (by omega) _).1 (by omega)))
      have hg := solo_gone_adder m (n' + 1) (u := 3 * (m - t) + 3 * n' + 5 + K + 1 + 1 + 1 + 1)
          (by omega)
      have s4 := s3.step (XMach.act_seek_stop ((ite_pos' rfl).trans hg)
        (solo_stop_adder m (n' + 1) (by omega) _))
      obtain ⟨t1, t2⟩ := tail _ (by omega) s4
      have ez : zeroCost m (turnAt m (n' + 1) t) = 4 := by
        rw [eA]
        unfold zeroCost
        exact (ite_neg' h1).trans (ite_pos' h2)
      exact ⟨3 * (m - t) + 3 * n' + 5 + K + 1 + 1 + 1 + 1 + 3 + t, by omega, t1, t2⟩
    · have r1 := r0.gone (solo_gone_zero m (n' + 1) (by omega))
      obtain ⟨t1, t2⟩ := tail _ (by omega) r1
      have ez : zeroCost m (turnAt m (n' + 1) t) = 1 := by
        rw [eA]
        unfold zeroCost
        exact (ite_neg' h1).trans (ite_neg' h2)
      exact ⟨3 * (m - t) + 3 * n' + 5 + K + 1 + 3 + t, by omega, t1, t2⟩

/-- The same when the second argument is zero: the thread finds the first
adder gone, passes the zero of the first argument, walks along the adders
from the zero of the second, and finds its top successors gone. -/
theorem turn_reader_zero (m t : Nat) (ht : t + 2 ≤ m) (htop : 20 * t ≤ 3 * m + 4) :
    ∃ b, turnRest m 0 t = b + 1 ∧
      RdAt m 0 ⟨chainL 0 (m - t) ++ (([1], .add) :: ([2], .zero) :: ([0 + 3], .zero) ::
        (chainL 0 (m - t + (t + 1))).take (t + 1)), .idle⟩ (b + 1) ⟨[], .idle⟩ ∧
      XMach.reader xsys (sum (m + 1) (0)) ⟨(sum (m + 1) (0)).agents, .idle⟩
          ⟨chainL 0 (m - t) ++ (([1], .add) :: ([2], .zero) :: ([0 + 3], .zero) ::
        (chainL 0 (m - t + (t + 1))).take (t + 1)), .idle⟩ b ≠ ⟨[], .idle⟩ := by
  obtain ⟨K, hK⟩ : ∃ K, (3 * (m - t) + 15) / 16 = K + 1 :=
    ⟨(3 * (m - t) + 15) / 16 - 1, by omega⟩
  have h0 := RdAt.start m 0 ⟨chainL 0 (m - t) ++ (([1], .add) :: ([2], .zero) :: ([0 + 3], .zero) ::
        (chainL 0 (m - t + (t + 1))).take (t + 1)), .idle⟩
  have h1 := RdAt.chain_turn (t := t) (m - t) (by omega) (h0.cast (by omega))
  have h2 := h1.gone (solo_gone5 m 0 (by omega)).2
  have hal := solo_alive_zero m 0 (j := 2) (u := 3 * (m - t) + 1 + 1) (by omega) (by omega)
    (by omega) (sum_zero_agent m 0)
  have h3 := h2.pass3 hal (solo_look_two m 0 _) (show ¬ (1 : Nat) = 0 by decide)
    ((solo_seek_two m 0 (by omega) _).2 (by omega))
  have hx3 : assoc [0 + 3] (sum (m + 1) 0).agents = some Arith.zero :=
    sum_assoc_base m 0 (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h4 := RdAt.walk (K := K) (by omega) (by omega) (by omega) (by omega) hx3 h3
  obtain ⟨t1, t2⟩ := RdAt.tops (r := m - t) t _ (by omega) (by omega) h4
  exact ⟨3 * (m - t) + 1 + 3 + 4 + K + t, by
    show 3 * (m - t) + 8 + (3 * (m - t) + 15) / 16 + t = _
    omega, t1, t2⟩

/-- `Quiet m n Ts W`: beside the first thread on the net for `(m + 1) + n`,
each of the threads `Ts` only reads and comes to rest, and `W` is the
number of their actions before they rest. -/
inductive Quiet (m n : Nat) : List (XThread Arith) → Nat → Prop
  | nil : Quiet m n [] 0
  | cons {T : XThread Arith} {Ts : List (XThread Arith)} {b W W' : Nat} :
      RdAt m n T (b + 1) ⟨[], .idle⟩ → XMach.reader xsys (sum (m + 1) n)
          ⟨(sum (m + 1) n).agents, .idle⟩ T b ≠ ⟨[], .idle⟩ →
      Quiet m n Ts W → W' = b + 1 + W → Quiet m n (T :: Ts) W'

theorem Quiet.snoc {m n : Nat} {Ts : List (XThread Arith)} {W : Nat} {T : XThread Arith}
    {b : Nat} (h : Quiet m n Ts W) (h1 : RdAt m n T (b + 1) ⟨[], .idle⟩)
    (h2 : XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T b ≠
        ⟨[], .idle⟩) : Quiet m n (Ts ++ [T]) (W + (b + 1)) := by
  induction h with
  | nil => exact .cons h1 h2 .nil (by omega)
  | cons k1 k2 _ e ih => exact .cons k1 k2 ih (by omega)

/-- Each of these threads reads at every action. -/
theorem Quiet.reads {m n : Nat} {Ts : List (XThread Arith)} {W : Nat} (h : Quiet m n Ts W) :
    ∀ T, T ∈ Ts → ∀ a,
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).1 =
          (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1 ∧
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ (a + 1)).1
          (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T a)).2.2 = 0 := by
  induction h with
  | nil =>
    intro T hT
    cases hT
  | @cons T' Ts' b W W' k1 _ _ _ ih =>
    intro T hT a
    rcases List.mem_cons.1 hT with e | hT'
    · rw [e]
      by_cases ha : a < b + 1
      · exact k1.2 a ha
      · obtain ⟨d, rfl⟩ : ∃ d, a = b + 1 + d := ⟨a - (b + 1), by omega⟩
        exact (k1.rest (d + 1)).2 (b + 1 + d) (by omega)
    · exact ih T hT' a

/-- And their busy actions come to `W`. -/
theorem Quiet.tally {m n : Nat} {Ts : List (XThread Arith)} {W : Nat} (h : Quiet m n Ts W) :
    ∀ a, W ≤ a → total (fun T => seqTally XThread.busy
        (XMach.reader xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ T) a) Ts = W := by
  induction h with
  | nil =>
    intro a _
    rfl
  | @cons T' Ts' b W W' k1 k2 _ e ih =>
    intro a ha
    have hbusy : ∀ j, j < b + 1 → XMach.reader xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ T' j ≠ ⟨[], .idle⟩ := fun j hj e' => by
      have h' := reader_rest e' (b - j)
      rw [show j + (b - j) = b by omega] at h'
      exact k2 h'
    have e2 : seqTally XThread.busy (XMach.reader xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ T') a = b + 1 :=
      (seqTally_exact (B := b + 1) (fun j hj => XThread.busy_of_ne_rest (hbusy j hj))
        (fun j hj => by
          obtain ⟨d, rfl⟩ : ∃ d, j = b + 1 + d := ⟨j - (b + 1), by omega⟩
          exact (congrArg XThread.busy (k1.rest d).1).trans rfl) a).2 (by omega)
    show seqTally XThread.busy (XMach.reader xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ T') a +
      total (fun T => seqTally XThread.busy (XMach.reader xsys (sum (m + 1) n)
          ⟨(sum (m + 1) n).agents, .idle⟩ T) a) Ts' = W'
    rw [e2, ih a (by omega), e]

/-- **Threads that only read beside the first and come to rest: all of them
in turn do exactly the work of the first alone and the actions of the
others before they rest.** -/
theorem quiet_total_all {m n : Nat} {Ts : List (XThread Arith)} {W : Nat}
    (h : Quiet m n Ts W) :
    (⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith).Total xsys
        (fun i => i % (Ts.length + 1))
      (soloWork (m + 1) n + W) := by
  have even : ∀ a, soloWork (m + 1) n + W ≤ a →
      (⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith).work xsys
          (fun i => i % (Ts.length + 1))
        ((Ts.length + 1) * a) = soloWork (m + 1) n + W := by
    intro a ha
    have ht := XMach.tally_readers XThread.busy (xs := xsys) (X := sum (m + 1) n)
      (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩) (Ts := Ts) (A := a)
      (fun T hT a' _ => h.reads T hT a') a (Nat.le_refl a)
    have e1 : seqTally XThread.busy (fun j => (XMach.solo xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ j).2) a = soloWork (m + 1) n := by
      rw [← XMach.tally_one XThread.busy xsys (sum (m + 1) n)
        ⟨(sum (m + 1) n).agents, .idle⟩ a]
      obtain ⟨hr, hw, -⟩ := solo_work (m + 1) n
      rw [XMach.init_one] at hr hw
      obtain ⟨d, rfl⟩ : ∃ d, a = soloWork (m + 1) n + d := ⟨a - soloWork (m + 1) n, by omega⟩
      exact (XMach.work_rest (fun _ => 0) hr d).trans hw
    show (⟨sum (m + 1) n,
        ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith).tally XThread.busy xsys
        (fun i => i % (Ts.length + 1))
      ((Ts.length + 1) * a) = _
    rw [ht, e1, h.tally a (by omega)]
  refine ⟨(Ts.length + 1) * (soloWork (m + 1) n + W), fun i hi => ?_⟩
  have hc : 0 < Ts.length + 1 := Nat.succ_pos _
  have lo := XMach.work_mono (xs := xsys) (fun i => i % (Ts.length + 1))
      (⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith)
    (Nat.mul_div_le i (Ts.length + 1))
  have up := XMach.work_mono (xs := xsys) (fun i => i % (Ts.length + 1))
      (⟨sum (m + 1) n, ⟨(sum (m + 1) n).agents, .idle⟩ :: Ts⟩ : XMach Arith)
    (Nat.le_of_lt (Nat.lt_mul_div_succ i hc))
  have hd : soloWork (m + 1) n + W ≤ i / (Ts.length + 1) :=
    (Nat.le_div_iff_mul_le hc).2 (by
      rw [Nat.mul_comm]
      exact hi)
  rw [even (i / (Ts.length + 1)) hd] at lo
  rw [even (i / (Ts.length + 1) + 1) (by omega)] at up
  omega

/-- The `k` threads after the first, `n` not zero. -/
theorem quiet_turns (m n' : Nat) : ∀ k,
    (∀ t, t < k → t + 2 ≤ m ∧
      (turnAt m (n' + 1) t ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m (n' + 1) t) ∧
      17 * t ≤ turnAt m (n' + 1) t) →
    Quiet m (n' + 1) ((List.range k).map fun t => (⟨(sum (m + 1) (n' + 1)).agents.drop (t + 1) ++
      (sum (m + 1) (n' + 1)).agents.take (t + 1), .idle⟩ : XThread Arith))
      (turnSum m (n' + 1) k)
  | 0, _ => .nil
  | k + 1, h => by
    have ih := quiet_turns m n' k (fun t ht => h t (by omega))
    obtain ⟨h1, h2, h3⟩ := h k (Nat.lt_succ_self k)
    obtain ⟨b, eb, r, hb⟩ := turn_reader_quiet m n' k h1 h2 h3
    rw [List.range_succ, List.map_append]
    show Quiet m (n' + 1) (_ ++ [(⟨(sum (m + 1) (n' + 1)).agents.drop (k + 1) ++
      (sum (m + 1) (n' + 1)).agents.take (k + 1), .idle⟩ : XThread Arith)])
      (turnSum m (n' + 1) k + turnRest m (n' + 1) k)
    rw [turn_list_succ m n' k (by omega), eb]
    exact ih.snoc r hb

/-- The same when the second argument is zero. -/
theorem quiet_turns_zero (m : Nat) : ∀ k,
    (∀ t, t < k → t + 2 ≤ m ∧ 20 * t ≤ 3 * m + 4) →
    Quiet m 0 ((List.range k).map fun t => (⟨(sum (m + 1) (0)).agents.drop (t + 1) ++
      (sum (m + 1) (0)).agents.take (t + 1), .idle⟩ : XThread Arith))
      (turnSum m 0 k)
  | 0, _ => .nil
  | k + 1, h => by
    have ih := quiet_turns_zero m k (fun t ht => h t (by omega))
    obtain ⟨h1, h2⟩ := h k (Nat.lt_succ_self k)
    obtain ⟨b, eb, r, hb⟩ := turn_reader_zero m k h1 h2
    rw [List.range_succ, List.map_append]
    show Quiet m 0 (_ ++ [(⟨(sum (m + 1) 0).agents.drop (k + 1) ++
      (sum (m + 1) 0).agents.take (k + 1), .idle⟩ : XThread Arith)])
      (turnSum m 0 k + turnRest m 0 k)
    rw [turn_list_zero m k (by omega), eb]
    exact ih.snoc r hb

/-- **Threads in turn, to the action, outside the race.**  On the net for
`(m + 1) + n` take `k + 1` threads that act in turn, with `k + 1 ≤ m` and
`20 * k ≤ 3 * m + 3 * n + 21`.  If none of the `k` threads after the first
comes to the zero of the first argument at one of the ten moments of the
race, that is after `17 * m + 7` to `17 * m + 16` actions, then each of
them only reads, and the work of the whole run is exactly that of one
thread and `turnRest m n t` for the thread numbered `t + 1`. -/
theorem threads_total (m n k : Nat) (hm : k + 1 ≤ m) (hk : 20 * k ≤ 3 * m + 3 * n + 21)
    (hw : ∀ t, t < k → turnAt m n t ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n t) :
    (XMach.init (sum (m + 1) n) (k + 1)).Total xsys (fun i => i % (k + 1))
      (soloWork (m + 1) n + turnSum m n k) := by
  rw [XMach.init_succ]
  have q : Quiet m n ((List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)) (turnSum m n k) := by
    cases n with
    | zero => exact quiet_turns_zero m k (fun t ht => ⟨by omega, by omega⟩)
    | succ n' =>
      exact quiet_turns m n' k (fun t ht => ⟨by omega, hw t ht, by
        unfold turnAt
        omega⟩)
  have tt := quiet_total_all q
  have hl : ((List.range k).map fun t => (⟨(sum (m + 1) n).agents.drop (t + 1) ++
      (sum (m + 1) n).agents.take (t + 1), .idle⟩ : XThread Arith)).length = k := by
    rw [List.length_map, List.length_range]
  rw [hl] at tt
  exact tt

example : (XMach.init (sum 7 9) 3).Total xsys (fun i => i % 3) 300 :=
  (threads_total 6 9 2 (by decide) (by decide) (fun t ht => by
    have h : t = 0 ∨ t = 1 := by omega
    rcases h with rfl | rfl <;> decide)).cast (by decide)

example : (XMach.init (sum 6 31) 4).Total xsys (fun i => i % 4) 580 :=
  (threads_total 5 31 3 (by decide) (by decide) (fun t ht => by
    have h : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide)).cast (by decide)

/-- A run of threads in turn, in two parts. -/
theorem work_mod_add (c : Nat) (M : XMach Arith) (w j : Nat) :
    M.work xsys (fun i => i % c) (c * w + j) = M.work xsys (fun i => i % c) (c * w) +
      (M.trace xsys (fun i => i % c) (c * w)).1.work xsys (fun i => i % c) j := by
  have h0 := XMach.work_add xsys (fun i => i % c) M (c * w) j
  have e : (M.trace xsys (fun i => i % c) (c * w)).1.work xsys (fun k => (c * w + k) % c) j =
      (M.trace xsys (fun i => i % c) (c * w)).1.work xsys (fun i => i % c) j :=
    XMach.tally_congr XThread.busy xsys _ j fun k _ => Nat.mul_add_mod c w k
  exact h0.trans (congrArg (M.work xsys (fun i => i % c) (c * w) + ·) e)

/-- A run of three threads in turn, in two parts. -/
theorem trace_triple_add (M : XMach Arith) (w w' : Nat) :
    (M.trace xsys (fun i => i % 3) (3 * (w + w'))).1 =
      ((M.trace xsys (fun i => i % 3) (3 * w)).1.trace xsys (fun i => i % 3) (3 * w')).1 := by
  rw [Nat.mul_add, XMach.trace_add xsys (fun i => i % 3) M (3 * w) (3 * w')]
  show ((M.trace xsys (fun i => i % 3) (3 * w)).1.trace xsys
    (fun i => (3 * w + i) % 3) (3 * w')).1 = _
  rw [XMach.trace_congr xsys _ (σ' := fun i => i % 3) (3 * w') fun j _ => by
    show (3 * w + j) % 3 = j % 3
    omega]

/-- One action of each of two threads in turn, with the work. -/
theorem sweep2_one {Y Y₁ Y₂ : XNet Arith} {a a' b b' : XThread Arith} {c₁ c₂ : Nat}
    (a₁ : XMach.act xsys Y a = (Y₁, a', c₁)) (a₂ : XMach.act xsys Y₁ b = (Y₂, b', c₂)) :
    ((⟨Y, [a, b]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * 1)).1 = ⟨Y₂, [a', b']⟩ ∧
      (⟨Y, [a, b]⟩ : XMach Arith).work xsys (fun i => i % 2) (2 * 1) = a.busy + b.busy := by
  have e₁ : XMach.step xsys ⟨Y, [a, b]⟩ 0 = (⟨Y₁, [a', b]⟩, c₁) :=
    XMach.step_eq (M := ⟨Y, [a, b]⟩) (t := 0) rfl a₁
  refine ⟨XMach.trace_pair a₁ a₂, ?_⟩
  show 0 + (⟨Y, [a, b]⟩ : XMach Arith).stepTally XThread.busy 0 +
    (XMach.step xsys ⟨Y, [a, b]⟩ 0).1.stepTally XThread.busy 1 = _
  rw [e₁]
  show 0 + a.busy + b.busy = a.busy + b.busy
  omega

/-- One action of each of three threads in turn, with the work. -/
theorem sweep3_one {Y Y₁ Y₂ Y₃ : XNet Arith} {a a' b b' q q' : XThread Arith}
    {c₁ c₂ c₃ : Nat} (a₁ : XMach.act xsys Y a = (Y₁, a', c₁))
    (a₂ : XMach.act xsys Y₁ b = (Y₂, b', c₂)) (a₃ : XMach.act xsys Y₂ q = (Y₃, q', c₃)) :
    ((⟨Y, [a, b, q]⟩ : XMach Arith).trace xsys (fun i => i % 3) (3 * 1)).1 =
        ⟨Y₃, [a', b', q']⟩ ∧
      (⟨Y, [a, b, q]⟩ : XMach Arith).work xsys (fun i => i % 3) (3 * 1) =
        a.busy + b.busy + q.busy := by
  have e₁ : XMach.step xsys ⟨Y, [a, b, q]⟩ 0 = (⟨Y₁, [a', b, q]⟩, c₁) :=
    XMach.step_eq (M := ⟨Y, [a, b, q]⟩) (t := 0) rfl a₁
  have e₂ : XMach.step xsys ⟨Y₁, [a', b, q]⟩ 1 = (⟨Y₂, [a', b', q]⟩, c₂) :=
    XMach.step_eq (M := ⟨Y₁, [a', b, q]⟩) (t := 1) rfl a₂
  have e₃ : XMach.step xsys ⟨Y₂, [a', b', q]⟩ 2 = (⟨Y₃, [a', b', q']⟩, c₃) :=
    XMach.step_eq (M := ⟨Y₂, [a', b', q]⟩) (t := 2) rfl a₃
  constructor
  · show (XMach.step xsys (XMach.step xsys (XMach.step xsys ⟨Y, [a, b, q]⟩ 0).1 1).1 2).1 = _
    rw [e₁, e₂, e₃]
  · show 0 + (⟨Y, [a, b, q]⟩ : XMach Arith).stepTally XThread.busy 0 +
      (XMach.step xsys ⟨Y, [a, b, q]⟩ 0).1.stepTally XThread.busy 1 +
      (XMach.step xsys (XMach.step xsys ⟨Y, [a, b, q]⟩ 0).1 1).1.stepTally XThread.busy 2 = _
    rw [e₁, e₂]
    show 0 + a.busy + b.busy + q.busy = a.busy + b.busy + q.busy
    omega

/-- **A third thread that only reads does not disturb two threads in
turn.**  If its actions, each after an action of each of the two, leave the
memory as it is and take it through the states `s`, the run of the three is
the run of the two with that thread beside it, and its work is theirs and
the busy actions of the third. -/
theorem third_quiet {X : XNet Arith} {T0 T1 : XThread Arith} (s : Nat → XThread Arith)
    (hs : ∀ w, XMach.act xsys
        ((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * (w + 1))).1.mem (s w) =
      (((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * (w + 1))).1.mem,
        s (w + 1), 0)) :
    ∀ w, ((⟨X, [T0, T1, s 0]⟩ : XMach Arith).trace xsys (fun i => i % 3) (3 * w)).1 =
        ⟨((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * w)).1.mem,
          ((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * w)).1.ths ++ [s w]⟩ ∧
      (⟨X, [T0, T1, s 0]⟩ : XMach Arith).work xsys (fun i => i % 3) (3 * w) =
        (⟨X, [T0, T1]⟩ : XMach Arith).work xsys (fun i => i % 2) (2 * w) +
          seqTally XThread.busy s w
  | 0 => ⟨rfl, rfl⟩
  | w + 1 => by
    obtain ⟨ih1, ih2⟩ := third_quiet s hs w
    have hlen := XMach.trace_length xsys (fun i => i % 2) (⟨X, [T0, T1]⟩ : XMach Arith) (2 * w)
    have p2 := XMach.trace_pair_add xsys (⟨X, [T0, T1]⟩ : XMach Arith) w 1
    have hq := hs w
    rw [p2] at hq
    have w2' := work_mod_add 2 (⟨X, [T0, T1]⟩ : XMach Arith) w (2 * 1)
    generalize hN : ((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * w)).1 = N
      at ih1 hlen p2 hq w2'
    obtain ⟨Y, ths⟩ := N
    have hlen' : ths.length = 2 := hlen
    obtain ⟨a, b, rfl⟩ : ∃ a b, ths = [a, b] := by
      match ths, hlen' with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨t2, w2⟩ := sweep2_one (Y := Y) (a := a) (b := b)
      (Y₁ := (XMach.act xsys Y a).1) (a' := (XMach.act xsys Y a).2.1)
      (c₁ := (XMach.act xsys Y a).2.2)
      (Y₂ := (XMach.act xsys (XMach.act xsys Y a).1 b).1)
      (b' := (XMach.act xsys (XMach.act xsys Y a).1 b).2.1)
      (c₂ := (XMach.act xsys (XMach.act xsys Y a).1 b).2.2) rfl rfl
    rw [t2] at hq p2
    obtain ⟨t3, w3⟩ := sweep3_one (Y := Y) (a := a) (b := b) (q := s w)
      (Y₁ := (XMach.act xsys Y a).1) (a' := (XMach.act xsys Y a).2.1)
      (c₁ := (XMach.act xsys Y a).2.2)
      (Y₂ := (XMach.act xsys (XMach.act xsys Y a).1 b).1)
      (b' := (XMach.act xsys (XMach.act xsys Y a).1 b).2.1)
      (c₂ := (XMach.act xsys (XMach.act xsys Y a).1 b).2.2) rfl rfl hq
    have ih1' : ((⟨X, [T0, T1, s 0]⟩ : XMach Arith).trace xsys (fun i => i % 3) (3 * w)).1 =
        ⟨Y, [a, b, s w]⟩ := ih1
    have p3 := trace_triple_add (⟨X, [T0, T1, s 0]⟩ : XMach Arith) w 1
    have w3' := work_mod_add 3 (⟨X, [T0, T1, s 0]⟩ : XMach Arith) w (3 * 1)
    rw [ih1'] at p3 w3'
    rw [w3] at w3'
    rw [w2] at w2'
    constructor
    · rw [p3, p2]
      exact t3
    · rw [Nat.mul_add 3 w 1, Nat.mul_add 2 w 1, w3', w2', ih2]
      show _ = _ + (seqTally XThread.busy s w + XThread.busy (s w))
      omega

/-- A thread, and then rest. -/
def thenRest (T : XThread Arith) : Nat → XThread Arith
  | 0 => T
  | _ + 1 => ⟨[], .idle⟩

theorem seqTally_thenRest (T : XThread Arith) :
    ∀ w, seqTally XThread.busy (thenRest T) (w + 1) = T.busy
  | 0 => Nat.zero_add _
  | w + 1 => by
    show seqTally XThread.busy (thenRest T) (w + 1) + XThread.busy ⟨[], .idle⟩ = T.busy
    rw [seqTally_thenRest T w]
    rfl

/-- **A third thread that is at rest, or has one agent left that is gone
for good, adds its one action at most to the work of the two others in
turn.** -/
theorem third_total {X : XNet Arith} {T0 T1 T2 : XThread Arith} {W : Nat}
    (tot : (⟨X, [T0, T1]⟩ : XMach Arith).Total xsys (fun i => i % 2) W)
    (h : T2 = ⟨[], .idle⟩ ∨ ∃ j γ, j ≠ 0 ∧ T2 = ⟨[([j], γ)], .idle⟩ ∧
      assoc [j] X.agents = none ∧ T0.st.Clear [j] ∧ T1.st.Clear [j]) :
    (⟨X, [T0, T1, T2]⟩ : XMach Arith).Total xsys (fun i => i % 3) (W + T2.busy) := by
  have hstep : XMach.act xsys
      ((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * (0 + 1))).1.mem T2 =
      (((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * (0 + 1))).1.mem,
        ⟨[], .idle⟩, 0) := by
    rcases h with e | ⟨j, γ, hj, e, hg, c0, c1⟩
    · rw [e]
      rfl
    · rw [e]
      obtain ⟨t2, -⟩ := sweep2_one (Y := X) (a := T0) (b := T1)
        (Y₁ := (XMach.act xsys X T0).1) (a' := (XMach.act xsys X T0).2.1)
        (c₁ := (XMach.act xsys X T0).2.2)
        (Y₂ := (XMach.act xsys (XMach.act xsys X T0).1 T1).1)
        (b' := (XMach.act xsys (XMach.act xsys X T0).1 T1).2.1)
        (c₂ := (XMach.act xsys (XMach.act xsys X T0).1 T1).2.2) rfl rfl
      have t2' : ((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * (0 + 1))).1 =
          ⟨(XMach.act xsys (XMach.act xsys X T0).1 T1).1,
            [(XMach.act xsys X T0).2.1, (XMach.act xsys (XMach.act xsys X T0).1 T1).2.1]⟩ := t2
      rw [t2']
      have g1 := XMach.act_gone (xs := xsys) (x := [j])
        (fun hR he => single_ne_new hj (new_head hR he)) hg c0
      have g2 := XMach.act_gone (xs := xsys) (x := [j])
        (fun hR he => single_ne_new hj (new_head hR he)) g1.1 c1
      exact XMach.act_idle_neg (e := ([j], γ)) fun h' => by
        have h'' : assoc [j] (XMach.act xsys (XMach.act xsys X T0).1 T1).1.agents = some γ := h'
        rw [g2.1] at h''
        cases h''
  have hs : ∀ w, XMach.act xsys
      ((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * (w + 1))).1.mem
        (thenRest T2 w) =
      (((⟨X, [T0, T1]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * (w + 1))).1.mem,
        thenRest T2 (w + 1), 0)
    | 0 => hstep
    | _ + 1 => rfl
  have q := third_quiet (thenRest T2) hs
  obtain ⟨N, hN⟩ := tot
  refine ⟨3 * (N + 1), fun i hi => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, i / 3 = v + 1 := ⟨i / 3 - 1, by omega⟩
  have q1 : (⟨X, [T0, T1, T2]⟩ : XMach Arith).work xsys (fun i => i % 3) (3 * (v + 1)) =
      (⟨X, [T0, T1]⟩ : XMach Arith).work xsys (fun i => i % 2) (2 * (v + 1)) +
        seqTally XThread.busy (thenRest T2) (v + 1) := (q (v + 1)).2
  have q2 : (⟨X, [T0, T1, T2]⟩ : XMach Arith).work xsys (fun i => i % 3) (3 * (v + 1 + 1)) =
      (⟨X, [T0, T1]⟩ : XMach Arith).work xsys (fun i => i % 2) (2 * (v + 1 + 1)) +
        seqTally XThread.busy (thenRest T2) (v + 1 + 1) := (q (v + 1 + 1)).2
  rw [seqTally_thenRest, hN _ (by omega)] at q1 q2
  have lo := XMach.work_mono (xs := xsys) (fun i => i % 3) (⟨X, [T0, T1, T2]⟩ : XMach Arith)
    (show 3 * (v + 1) ≤ i by omega)
  have up := XMach.work_mono (xs := xsys) (fun i => i % 3) (⟨X, [T0, T1, T2]⟩ : XMach Arith)
    (show i ≤ 3 * (v + 1 + 1) by omega)
  omega

/-- A thread running alone that is not at rest was not at rest before. -/
theorem solo_busy_before {X : XNet Arith} {T : XThread Arith} {E : Nat}
    (h : (XMach.solo xsys X T E).2 ≠ ⟨[], .idle⟩) :
    ∀ j, j < E → (XMach.solo xsys X T j).2 ≠ ⟨[], .idle⟩ := by
  intro j hj e
  apply h
  obtain ⟨d, rfl⟩ : ∃ d, E = j + d := ⟨E - j, by omega⟩
  have h1 := XMach.solo_add xsys j X T d
  rw [e, XMach.solo_rest] at h1
  exact congrArg Prod.snd h1

/-- Nor was a thread beside the first. -/
theorem reader_busy_upto {X : XNet Arith} {F0 T0 : XThread Arith} {b : Nat}
    (h : XMach.reader xsys X F0 T0 b ≠ ⟨[], .idle⟩) :
    ∀ a, a ≤ b → XMach.reader xsys X F0 T0 a ≠ ⟨[], .idle⟩ := by
  intro a ha e
  have h' := reader_rest e (b - a)
  rw [show a + (b - a) = b by omega] at h'
  exact h h'

theorem seqTally_full {κ : XThread Arith → Nat} {R : Nat → XThread Arith} :
    ∀ a, (∀ j, j < a → κ (R j) = 1) → seqTally κ R a = a
  | 0, _ => rfl
  | a + 1, h => by
    show seqTally κ R a + κ (R a) = a + 1
    rw [seqTally_full a (fun j hj => h j (by omega)), h a (Nat.lt_succ_self a)]

/-- **Three threads in turn while the second and the third only read**:
after each has acted `E` times the memory and the first thread are those of
one thread alone, the others are where their own actions took them, and
every action so far was work if none of the three was at rest before. -/
theorem three_entry {m n : Nat} {T1 T2 S1 S2 : XThread Arith} {E : Nat}
    (h1 : RdAt m n T1 E S1) (h2 : RdAt m n T2 E S2)
    (hb0 : (XMach.solo xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩ E).2 ≠ ⟨[], .idle⟩)
    (hb1 : ∀ a, a < E → XMach.reader xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩ T1 a ≠
        ⟨[], .idle⟩)
    (hb2 : ∀ a, a < E → XMach.reader xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩ T2 a ≠
        ⟨[], .idle⟩) :
    ((⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T1, T2]⟩ : XMach Arith).trace xsys
        (fun i => i % 3) (3 * E)).1 = ⟨(XMach.solo xsys (sum (m + 1) (n))
            ⟨(sum (m + 1) (n)).agents, .idle⟩ E).1, [(XMach.solo xsys (sum (m + 1) (n))
            ⟨(sum (m + 1) (n)).agents, .idle⟩ E).2, S1, S2]⟩ ∧
      (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T1, T2]⟩ : XMach Arith).work xsys
        (fun i => i % 3) (3 * E) = 3 * E := by
  have hall : ∀ T, T ∈ [T1, T2] → ∀ a, a < E →
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩
          (a + 1)).1 (XMach.reader xsys (sum (m + 1) (n))
          ⟨(sum (m + 1) (n)).agents, .idle⟩ T a)).1 = (XMach.solo xsys (sum (m + 1) (n))
          ⟨(sum (m + 1) (n)).agents, .idle⟩ (a + 1)).1 ∧
      (XMach.act xsys (XMach.solo xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩
          (a + 1)).1 (XMach.reader xsys (sum (m + 1) (n))
          ⟨(sum (m + 1) (n)).agents, .idle⟩ T a)).2.2 = 0 := by
    intro T hT a ha
    rcases List.mem_cons.1 hT with e | hT
    · rw [e]
      exact h1.2 a ha
    · rcases List.mem_cons.1 hT with e | hT
      · rw [e]
        exact h2.2 a ha
      · cases hT
  have tr := XMach.trace_readers (xs := xsys) (X := sum (m + 1) n)
    (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩) (Ts := [T1, T2]) (A := E) hall E (Nat.le_refl _)
  have ht := XMach.tally_readers XThread.busy (xs := xsys) (X := sum (m + 1) n)
    (T₀ := ⟨(sum (m + 1) n).agents, .idle⟩) (Ts := [T1, T2]) (A := E) hall E (Nat.le_refl _)
  constructor
  · have e' : ((⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T1, T2]⟩ :
        XMach Arith).trace xsys (fun i => i % 3) (3 * E)).1 =
        ⟨(XMach.solo xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩ E).1,
            [(XMach.solo xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩ E).2,
            XMach.reader xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents, .idle⟩ T1 E,
            XMach.reader xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents,
            .idle⟩ T2 E]⟩ := congrArg Prod.fst tr
    rw [h1.1, h2.1] at e'
    exact e'
  · have ht' : (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T1, T2]⟩ :
        XMach Arith).tally XThread.busy xsys (fun i => i % 3) (3 * E) =
        seqTally XThread.busy (fun j => (XMach.solo xsys (sum (m + 1) (n))
            ⟨(sum (m + 1) (n)).agents, .idle⟩ j).2) E +
          (seqTally XThread.busy (XMach.reader xsys (sum (m + 1) (n))
              ⟨(sum (m + 1) (n)).agents, .idle⟩ T1) E + (seqTally XThread.busy
              (XMach.reader xsys (sum (m + 1) (n)) ⟨(sum (m + 1) (n)).agents,
              .idle⟩ T2) E + 0)) := ht
    show (⟨sum (m + 1) n, [⟨(sum (m + 1) n).agents, .idle⟩, T1, T2]⟩ :
      XMach Arith).tally XThread.busy xsys (fun i => i % 3) (3 * E) = 3 * E
    rw [ht', seqTally_full E (fun j hj => XThread.busy_of_ne_rest (solo_busy_before hb0 j hj)),
      seqTally_full E (fun j hj => XThread.busy_of_ne_rest (hb1 j hj)),
      seqTally_full E (fun j hj => XThread.busy_of_ne_rest (hb2 j hj))]
    omega

/-- The work of a run of three threads in turn, from a later state on. -/
theorem total_after3 {M M' : XMach Arith} {E W : Nat}
    (h : (M.trace xsys (fun i => i % 3) (3 * E)).1 = M')
    (hw : M.work xsys (fun i => i % 3) (3 * E) = 3 * E)
    (tot : M'.Total xsys (fun i => i % 3) W) : M.Total xsys (fun i => i % 3) (3 * E + W) := by
  subst h
  obtain ⟨N, hN⟩ := tot
  refine ⟨3 * E + N, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = 3 * E + k := ⟨i - 3 * E, by omega⟩
  rw [work_mod_add 3 M E k, hw, hN k (by omega)]

/-- The top successors at the end of a list, down to the last. -/
theorem RdAt.tops_last {m n r : Nat} {T0 : XThread Arith} :
    ∀ (s a : Nat), r + s ≤ m → 17 * (m - r) + 4 ≤ a →
      RdAt m n T0 a ⟨(chainL n (r + (s + 1))).take (s + 1), .idle⟩ →
      RdAt m n T0 (a + s) ⟨[([n + 3 + r + 1], .succ)], .idle⟩
  | 0, _, _, _, h => h
  | s + 1, a, hs, ha, h => by
    have h' : RdAt m n T0 a
        ⟨([n + 3 + (r + (s + 1)) + 1], .succ) :: (chainL n (r + (s + 1))).take (s + 1),
          .idle⟩ := h
    have h1 := h'.gone (solo_gone_top m n (by omega) (by omega))
    exact (RdAt.tops_last s (a + 1) (by omega) (by omega) h1).cast (by omega)

/-- **The thread numbered `t + 1` is ready to take the zero of the first
argument four actions after it comes to it**, when it comes to it after
`17 * m + 7` actions at least and `17 * m + 16` at most. -/
theorem turn_reader_ready (m n' t K : Nat) (ht : t + 2 ≤ m)
    (hK1 : 16 * K + 5 ≤ 3 * (m - t)) (hK2 : 3 * (m - t) < 16 * K + 21)
    (h1 : 17 * m + 7 ≤ 3 * (m - t) + 3 * n' + 5 + K)
        (h2 : 3 * (m - t) + 3 * n' + 5 + K ≤ 17 * m + 16) :
    RdAt m (n' + 1) ⟨chainL (n' + 1) (m - t) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take
            (t + 1)))), .idle⟩
      (3 * (m - t) + 3 * n' + 5 + K + 4)
      ⟨([3], .zero) :: (chainL (n' + 1) (m - t + (t + 1))).take (t + 1), .ready [2]
          [0, n' + 1 + 4] .zero .add⟩ := by
  have h := turn_reader_at_zero m n' t K ht hK1 hK2
  have hal := solo_alive_zero m (n' + 1) (j := 2) (u := 3 * (m - t) + 3 * n' + 5 + K + 1) (by omega)
      (by omega)
    (by omega) (sum_zero_agent m (n' + 1))
  have s1 := h.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
  have s2 := s1.step (XMach.act_look (solo_look_two m (n' + 1) _))
  have s3 := s2.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide))
    ((solo_seek_two m (n' + 1) (by omega) _).1 (by omega)))
  have hA := solo_adder_alive m (n' + 1) (by omega)
      (u := 3 * (m - t) + 3 * n' + 5 + K + 1 + 1 + 1 + 1) (by omega)
    (by omega)
  exact s3.step (XMach.act_seek_found (c := ([0, n' + 1 + 4], 0)) ((ite_pos' rfl).trans hA)
    ⟨by ports_differ, rfl⟩)

/-- The two threads of the race at its first four moments: the first as
one thread alone, with what the two do from there in all. -/
theorem race_entry_total (m' n' d : Nat) (hd : d ≤ 3) (l : List (Id × Arith)) (x : Id) :
    ∃ X T W, XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩
        (17 * (m' + 1) + 11 + d) = (X, T) ∧ T ≠ ⟨[], .idle⟩ ∧ T.st.Clear x ∧
      (⟨X, [T, ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys
        (fun i => i % 2) W ∧
      2 * (17 * (m' + 1) + 11 + d) + W = raceWork (m' + 1) (n' + 1) d := by
  obtain ⟨V, todo, rest, p5, q5, p6, q6, p7, q7, p8, q8, B, s11, s12, s13, s14, -⟩ :=
    race_write (m' + 1) (n' + 1) (by omega)
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hd' with rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, solo_at s11 (by omega), (fun h => by
      injection h with _ h2
      cases h2), (fun e he => by cases he), (race_d0 B todo l).total, by
      show _ = 44 * (m' + 1) + 6 * (n' + 1) + 52
      omega⟩
  · exact ⟨_, _, _, solo_at s12 (by omega), (fun h => by
      injection h with _ h2
      cases h2), (fun e he => by cases he), (race_d1 B todo l).total, by
      show _ = 44 * (m' + 1) + 6 * (n' + 1) + 53
      omega⟩
  · exact ⟨_, _, _, solo_at s13 (by omega), (fun h => by
      injection h with _ h2
      cases h2), (fun e he => by cases he), (race_d2 B todo l).total, by
      show _ = 44 * (m' + 1) + 6 * (n' + 1) + 54
      omega⟩
  · exact ⟨_, _, _, solo_at s14 (by omega), (fun h => by
      injection h with _ h2
      cases h2), (fun e he => by cases he), (race_d3 B todo l).total, by
      show _ = 44 * (m' + 1) + 6 * (n' + 1) + 56
      omega⟩

/-- **Three threads in turn, the second in the race and the third already
past the zero of the first argument, to the action.**  On the net for
`(m + 1) + n`, with `m` from four on: when the second thread comes to that
zero at one of the ten moments of the race and the third has passed it
before the segment to the last adder was written, the third thread only
reads, and the work of the whole run is exactly that of the race of two
threads and the actions of the third before it rests. -/
theorem three_threads_race_first (m n : Nat) (hm : 4 ≤ m)
    (h1 : 17 * m + 7 ≤ turnAt m n 0) (h2 : turnAt m n 1 ≤ 17 * m + 6) :
    (XMach.init (sum (m + 1) n) 3).Total xsys (fun i => i % 3)
      (raceWork m n (turnAt m n 0 - (17 * m + 7)) + turnRest m n 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
    unfold turnAt at h1
    omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K1, hK1⟩ : ∃ K, (3 * (m' + 1 - 0) + 11) / 16 = K + 1 :=
    ⟨(3 * (m' + 1 - 0) + 11) / 16 - 1, by omega⟩
  obtain ⟨K2, hK2⟩ : ∃ K, (3 * (m' + 1 - 1) + 11) / 16 = K + 1 :=
    ⟨(3 * (m' + 1 - 1) + 11) / 16 - 1, by omega⟩
  have eA1 : turnAt (m' + 1) (n' + 1) 0 = 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 := by
    unfold turnAt
    omega
  have eA2 : turnAt (m' + 1) (n' + 1) 1 = 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 := by
    unfold turnAt
    omega
  have hrest : turnRest (m' + 1) (n' + 1) 1 = turnAt (m' + 1) (n' + 1) 1 +
      zeroCost (m' + 1) (turnAt (m' + 1) (n' + 1) 1) + 3 + (1 + 1) := rfl
  have ez : zeroCost (m' + 1) (turnAt (m' + 1) (n' + 1) 1) = 3 := by
    rw [eA2] at h2 ⊢
    unfold zeroCost
    exact ite_pos' h2
  rw [eA1] at h1
  rw [eA2] at h2
  obtain ⟨d, hd⟩ : ∃ d, 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 7 + d :=
    ⟨3 * (m' + 1 - 0) + 3 * n' + 5 + K1 - (17 * (m' + 1) + 7), by omega⟩
  have e0 : turnAt (m' + 1) (n' + 1) 0 - (17 * (m' + 1) + 7) = d := by omega
  rw [e0]
  have r1 := turn_reader_ready (m' + 1) n' 0 K1 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have q0 := turn_reader_at_zero (m' + 1) n' 1 K2 (by omega) (by omega) (by omega)
  have hal := solo_alive_zero (m' + 1) (n' + 1) (j := 2)
      (u := 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 1) (by omega) (by omega)
    (by omega) (sum_zero_agent (m' + 1) (n' + 1))
  have q1 := q0.pass3 hal (solo_look_two (m' + 1) (n' + 1) _) (show ¬ (1 : Nat) = 0 by decide)
    ((solo_seek_two (m' + 1) (n' + 1) (by omega) _).2 (by omega))
  have hx3 : assoc [3] (sum (m' + 1 + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base (m' + 1) (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have q2 := q1.pass3 (solo_snd_forever (m' + 1) (n' + 1) (j := 3) (by omega) (by omega) hx3 _)
    (solo_look_snd (m' + 1) (n' + 1) (j := 3) (by omega) (by omega) _).1
    (show ¬ (1 : Nat) = 0 by decide)
    (solo_look_snd (m' + 1) (n' + 1) (j := 3) (by omega) (by omega) _).2
  have q3 := RdAt.tops_last (r := m' + 1 - 1) 1 (3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 3 + 3)
      (by omega) (by omega) q2
  have q4 := q3.gone (solo_gone_top (m' + 1) (n' + 1) (q := m' + 1 - 1) (by omega) (by omega))
  obtain ⟨X, T, W, hs, hT, hc, tot2, hW⟩ := race_entry_total m' n' d (by omega)
    (([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1))
        [n' + 1 + 3 + (m' + 1 - 1) + 1]
  have hinit : XMach.init (sum (m' + 1 + 1) (n' + 1)) 3 =
      ⟨sum (m' + 1 + 1) (n' + 1), [⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩,
      ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
            (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩,
      ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
            (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩]⟩ :=
    (XMach.init_succ (sum (m' + 1 + 1) (n' + 1)) 2).trans (by
      rw [← turn_list_succ (m' + 1) n' 0 (by omega), ← turn_list_succ (m' + 1) n' 1 (by omega)]
      rfl)
  rw [hinit]
  have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1))
      ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + d)).2 ≠ ⟨[], .idle⟩ := by
    rw [hs]
    exact hT
  have r1' := r1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 4 = 17 *
      (m' + 1) + 11 + d by omega)
  have hb1 := reader_busy_upto (X := sum (m' + 1 + 1) (n' + 1))
      (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + d)
    (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
            (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
      rw [r1'.1] at e
      injection e with _ e2
      cases e2)
  have hK : K1 = K2 ∨ K1 = K2 + 1 := by omega
  rcases hK with hK | hK
  · have q3' := q3.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 3 + 3 + 1 = 17 *
        (m' + 1) + 11 + d by omega)
    have hb2 := reader_busy_upto (X := sum (m' + 1 + 1) (n' + 1))
        (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + d)
      (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
            (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
        rw [q3'.1] at e
        cases e)
    obtain ⟨tr, wk⟩ := three_entry r1' q3' hb0 (fun a ha => hb1 a (by omega))
      (fun a ha => hb2 a (by omega))
    rw [hs] at tr
    have hg := solo_gone_top (m' + 1) (n' + 1) (q := m' + 1 - 1) (u := 17 * (m' + 1) + 11 + d)
      (by omega) (by omega)
    rw [hs] at hg
    have t3 := third_total tot2 (T2 := ⟨[([n' + 1 + 3 + (m' + 1 - 1) + 1], .succ)], .idle⟩)
      (.inr ⟨_, _, by omega, rfl, hg, hc, trivial⟩)
    have b1 : (⟨[([n' + 1 + 3 + (m' + 1 - 1) + 1], Arith.succ)],
        .idle⟩ : XThread Arith).busy = 1 := rfl
    exact (total_after3 tr wk t3).cast (by omega)
  · have q4' := q4.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 3 + 3 + 1 + 1 = 17 *
        (m' + 1) + 11 + d by omega)
    have hb2 : ∀ a, a < 17 * (m' + 1) + 11 + d →
        XMach.reader xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩
            ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
            (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩ a ≠
            ⟨[], .idle⟩ := fun a ha =>
      reader_busy_upto (X := sum (m' + 1 + 1) (n' + 1))
          (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩)
          (b := 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 3 + 3 + 1)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
            (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [q3.1] at e
          cases e) a (by omega)
    obtain ⟨tr, wk⟩ := three_entry r1' q4' hb0 (fun a ha => hb1 a (by omega)) hb2
    rw [hs] at tr
    have t3 := third_total tot2 (T2 := ⟨[], .idle⟩) (.inl rfl)
    have b0 : (⟨[], .idle⟩ : XThread Arith).busy = 0 := rfl
    exact (total_after3 tr wk t3).cast (by omega)

example : (XMach.init (sum 7 30) 3).Total xsys (fun i => i % 3) 612 :=
  (three_threads_race_first 6 30 (by decide) (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 8 35) 3).Total xsys (fun i => i % 3) 707 :=
  (three_threads_race_first 7 35 (by decide) (by decide) (by decide)).cast (by decide)

end Arith

end INet
