import InteractionNets.Arith.TwoSums

/-! ### Two threads on two additions that do not meet: the rounds, exactly -/

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

namespace Arith

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

variable {j m n : Nat}

local macro "ports_differ" : tactic =>
  `(tactic| first | (intro e; simp at e; done) | (intro e; simp at e; omega))

local macro "under_wires" : tactic =>
  `(tactic| repeat (first | rw [wires_takeAgent] | rw [wires_putAgent] |
      rw [assoc_wires_putLink (by ports_differ)] | rw [nextSeg_putLink (by ports_differ)]))

local macro "under_agents" : tactic =>
  `(tactic| repeat (first | rw [agents_putLink] | rw [assoc_takeAgent_ne (by ports_differ)] |
      rw [assoc_putAgent_ne (by ports_differ)]))

theorem stays_inv {X : XNet Arith} {S T' : XThread Arith} {K : Nat}
    (st : Stays xsys X S T' (K + 1)) :
    S ≠ ⟨[], .idle⟩ ∧ ∃ S1, XMach.act xsys X S = (X, S1, 0) ∧ Stays xsys X S1 T' K := by
  cases st with
  | step hT h st' => exact ⟨hT, _, h, st'⟩

/-- **A thread that reads on a net reads in the same way inside a larger
memory, whatever is done to the other cells between its actions.**  One
action: the thread on `X` reads, is not at rest, and has `K` more actions
of reading before it is; on any memory `Z` whose cells tagged `c` are `X`,
the thread with its names tagged does the same, and `Z` is as it was. -/
theorem stays_act {c : Nat} {X Z : XNet Arith} {S : XThread Arith} {K : Nat} (hS : Scans S.st)
    (st : Stays xsys X S ⟨[], .idle⟩ (K + 1)) (hL : Looks c X Z) (r : List (Id × Arith)) :
    ∃ S1, XMach.act xsys Z (tagTh c r S) = (Z, tagTh c r S1, 0) ∧ Scans S1.st ∧
      Stays xsys X S1 ⟨[], .idle⟩ K := by
  obtain ⟨hne, S1, h, st'⟩ := stays_inv st
  obtain ⟨todo, s⟩ := S
  have hw : s ≠ .write [] [] := fun e => by
    rw [e] at hS
    exact hS
  obtain ⟨X', Y', l', st1, k, aX, aY, -, -, -, hsc⟩ :=
    hL.act todo [] r s (fun e hl => hne (by rw [e, hl])) hw
  rw [List.append_nil, List.append_nil] at aX
  have e := aX.symm.trans h
  injection e with e1 e2
  injection e2 with e3 e4
  subst e1
  subst e3
  subst e4
  obtain ⟨eY, hS1⟩ := hsc hS rfl
  subst eY
  exact ⟨⟨l', st1⟩, aY, hS1, st'⟩

/-- A round of two threads, the first of them reading on its net. -/
theorem read_round {c : Nat} {X W W' : XNet Arith} {S Q Q' : XThread Arith} {K k2 : Nat}
    (hS : Scans S.st) (st : Stays xsys X S ⟨[], .idle⟩ (K + 1)) (hL : Looks c X W)
    (r : List (Id × Arith)) (a2 : XMach.act xsys W Q = (W', Q', k2)) :
    ∃ S1, ((⟨W, [tagTh c r S, Q]⟩ : XMach Arith).trace xsys (fun i => i % 2) (2 * 1)).1 =
        ⟨W', [tagTh c r S1, Q']⟩ ∧ Scans S1.st ∧ Stays xsys X S1 ⟨[], .idle⟩ K := by
  obtain ⟨S1, a1, hS1, st1⟩ := stays_act hS st hL r
  exact ⟨S1, round_two a1 a2, hS1, st1⟩

/-- **Five rounds: the second thread claims the first pair of an addition
while the first thread reads.** -/
theorem claim_rounds_read {n' hi : Nat} {XA XB W : XNet Arith} {S : XThread Arith} {K : Nat}
    (stB : Start n' XB hi) (hA : Looks 0 XA W) (hB : Looks 1 XB W) (hS : Scans S.st)
    (st : Stays xsys XA S ⟨[], .idle⟩ (K + 5)) (r rest : List (Id × Arith)) :
    ∃ S5, ((⟨W, [tagTh 0 r S, ⟨([hi + 1] ++ [1], .succ) :: rest, .idle⟩]⟩ : XMach Arith).trace
          xsys (fun i => i % 2) (2 * 5)).1 =
        ⟨(W.takeAgent ([hi + 1] ++ [1])).takeAgent ([1] ++ [1]),
          [tagTh 0 r S5, ⟨rest, .write ((addSucc.swap.toX.newAgents [hi + 1] [1]).map (tagA 1))
            ((addSucc.swap.toX.newLinks ar [hi + 1] [1] .succ .add).map (tagL 1))⟩]⟩ ∧
      Scans S5.st ∧ Stays xsys XA S5 ⟨[], .idle⟩ K := by
  have hB4 : Looks 1 (XB.takeAgent [hi + 1]) (W.takeAgent ([hi + 1] ++ [1])) :=
    hB.take [hi + 1]
  have hA4 : Looks 0 XA (W.takeAgent ([hi + 1] ++ [1])) := hA.take_other (by decide) [hi + 1]
  obtain ⟨q0, q1, q2, q3, q4⟩ := Looks.claim_acts stB rest hB hB hB hB hB4
  obtain ⟨S1, t1, h1, s1⟩ := read_round hS st hA r q0
  obtain ⟨S2, t2, h2, s2⟩ := read_round h1 s1 hA r q1
  obtain ⟨S3, t3, h3, s3⟩ := read_round h2 s2 hA r q2
  obtain ⟨S4, t4, h4, s4⟩ := read_round h3 s3 hA r q3
  obtain ⟨S5, t5, h5, s5⟩ := read_round h4 s4 hA4 r q4
  refine ⟨S5, ?_, h5, s5⟩
  rw [show (2 * 5 : Nat) = 2 * (1 + 4) from rfl, trace_mod_add, t1,
    show (2 * 4 : Nat) = 2 * (1 + 3) from rfl, trace_mod_add, t2,
    show (2 * 3 : Nat) = 2 * (1 + 2) from rfl, trace_mod_add, t3,
    show (2 * 2 : Nat) = 2 * (1 + 1) from rfl, trace_mod_add, t4, t5]

/-- **The second thread writes its segments and reloads while the first
thread reads.** -/
theorem links_rounds_read {c d : Nat} (hcd : d ≠ c) {X : XNet Arith} :
    ∀ (ls : List (Port × Port)) (W : XNet Arith) (S : XThread Arith) (K : Nat)
      (l r : List (Id × Arith)), Scans S.st →
      Stays xsys X S ⟨[], .idle⟩ (K + (ls.length + 1)) → Looks c X W →
      ∃ S', ((⟨W, [tagTh c r S, ⟨l, .write [] (ls.map (tagL d))⟩]⟩ : XMach Arith).trace xsys
            (fun i => i % 2) (2 * (ls.length + 1))).1 =
          ⟨W.putLinks (ls.map (tagL d)),
            [tagTh c r S', ⟨(W.putLinks (ls.map (tagL d))).agents, .idle⟩]⟩ ∧
        Scans S'.st ∧ Stays xsys X S' ⟨[], .idle⟩ K ∧ Looks c X (W.putLinks (ls.map (tagL d)))
  | [], W, S, K, l, r, hS, st, hL => by
    have a2 : XMach.act xsys W ⟨l, .write [] []⟩ = (W, ⟨W.agents, .idle⟩, 0) := rfl
    obtain ⟨S1, t1, h1, s1⟩ := read_round hS st hL r a2
    exact ⟨S1, t1, h1, s1, hL⟩
  | (p, q) :: ls, W, S, K, l, r, hS, st, hL => by
    have a2 : XMach.act xsys W ⟨l, .write [] (((p, q) :: ls).map (tagL d))⟩ =
        (W.putLink (tagPort d p) (tagPort d q), ⟨l, .write [] (ls.map (tagL d))⟩, 0) := rfl
    have st' : Stays xsys X S ⟨[], .idle⟩ (K + (ls.length + 1) + 1) := st
    obtain ⟨S1, t1, h1, s1⟩ := read_round hS st' hL r a2
    obtain ⟨S', t', h', s', hL'⟩ := links_rounds_read hcd ls
      (W.putLink (tagPort d p) (tagPort d q)) S1 K l r h1 s1 (hL.link_other hcd p q)
    refine ⟨S', ?_, h', s', hL'⟩
    have e : 2 * (((p, q) :: ls).length + 1) = 2 * (1 + (ls.length + 1)) := by
      rw [List.length_cons]
      omega
    rw [e, trace_mod_add, t1]
    exact t'

/-- **The second thread writes what its rule makes and reloads while the
first thread reads**: one round for each agent, each segment, and the
reload; the first thread has read as many times. -/
theorem write_rounds_read {c d : Nat} (hcd : d ≠ c) {X : XNet Arith} :
    ∀ (as : List (Id × Arith)) (ls : List (Port × Port)) (W : XNet Arith) (S : XThread Arith)
      (K : Nat) (l r : List (Id × Arith)), Scans S.st →
      Stays xsys X S ⟨[], .idle⟩ (K + (as.length + ls.length + 1)) → Looks c X W →
      ∃ S', ((⟨W, [tagTh c r S, ⟨l, .write (as.map (tagA d)) (ls.map (tagL d))⟩]⟩ :
            XMach Arith).trace xsys (fun i => i % 2) (2 * (as.length + ls.length + 1))).1 =
          ⟨(W.putAgents (as.map (tagA d))).putLinks (ls.map (tagL d)),
            [tagTh c r S',
              ⟨((W.putAgents (as.map (tagA d))).putLinks (ls.map (tagL d))).agents, .idle⟩]⟩ ∧
        Scans S'.st ∧ Stays xsys X S' ⟨[], .idle⟩ K ∧
        Looks c X ((W.putAgents (as.map (tagA d))).putLinks (ls.map (tagL d)))
  | [], ls, W, S, K, l, r, hS, st, hL => by
    have e : ([] : List (Id × Arith)).length + ls.length + 1 = ls.length + 1 := by
      rw [List.length_nil]
      omega
    rw [e] at st ⊢
    exact links_rounds_read hcd ls W S K l r hS st hL
  | (i, γ) :: as, ls, W, S, K, l, r, hS, st, hL => by
    have a2 : XMach.act xsys W ⟨l, .write (((i, γ) :: as).map (tagA d)) (ls.map (tagL d))⟩ =
        (W.putAgent (i ++ [d]) γ, ⟨l, .write (as.map (tagA d)) (ls.map (tagL d))⟩, 0) := rfl
    have e0 : ((i, γ) :: as).length + ls.length + 1 = as.length + ls.length + 1 + 1 := by
      rw [List.length_cons]
      omega
    rw [e0] at st
    have st' : Stays xsys X S ⟨[], .idle⟩ (K + (as.length + ls.length + 1) + 1) := st
    obtain ⟨S1, t1, h1, s1⟩ := read_round hS st' hL r a2
    obtain ⟨S', t', h', s', hL'⟩ := write_rounds_read hcd as ls (W.putAgent (i ++ [d]) γ) S1 K
      l r h1 s1 (hL.put_other hcd i γ)
    refine ⟨S', ?_, h', s', hL'⟩
    have e : 2 * (((i, γ) :: as).length + ls.length + 1) =
        2 * (1 + (as.length + ls.length + 1)) := by
      rw [List.length_cons]
      omega
    rw [e, trace_mod_add, t1]
    exact t'

/-- **The six actions that claim the last pair of an addition inside a
larger memory**: the adder and the zero of the first argument. -/
theorem Looks.zero_acts {c n : Nat} {X : XNet Arith} (st : Steady n X (n + 3))
    (hz : assoc [2] X.agents = some .zero) (rest : List (Id × Arith))
    {Z0 Z1 Z2 Z3 Z4 Z5 : XNet Arith} (h0 : Looks c X Z0) (h1 : Looks c X Z1)
    (h2 : Looks c X Z2) (h3 : Looks c X Z3) (h4 : Looks c X Z4)
    (h5 : Looks c (X.takeAgent [0, n + 3 + 1]) Z5) :
    XMach.act xsys Z0 ⟨([0, n + 3 + 1] ++ [c], .add) :: rest, .idle⟩ =
        (Z0, ⟨rest, .look ([0, n + 3 + 1] ++ [c]) .add⟩, 0) ∧
      XMach.act xsys Z1 ⟨rest, .look ([0, n + 3 + 1] ++ [c]) .add⟩ =
        (Z1, ⟨rest, .seek ([0, n + 3 + 1] ++ [c]) .add ([0, n + 3 + 1] ++ [c], 0)
          ([n + 3 + 1] ++ [c], 1)⟩, 0) ∧
      XMach.act xsys Z2 ⟨rest, .seek ([0, n + 3 + 1] ++ [c]) .add ([0, n + 3 + 1] ++ [c], 0)
          ([n + 3 + 1] ++ [c], 1)⟩ =
        (Z2, ⟨rest, .seek ([0, n + 3 + 1] ++ [c]) .add ([n + 3 + 1] ++ [c], 1)
          ([2] ++ [c], 0)⟩, 0) ∧
      XMach.act xsys Z3 ⟨rest, .seek ([0, n + 3 + 1] ++ [c]) .add ([n + 3 + 1] ++ [c], 1)
          ([2] ++ [c], 0)⟩ =
        (Z3, ⟨rest, .ready ([0, n + 3 + 1] ++ [c]) ([2] ++ [c]) .add .zero⟩, 0) ∧
      XMach.act xsys Z4 ⟨rest, .ready ([0, n + 3 + 1] ++ [c]) ([2] ++ [c]) .add .zero⟩ =
        (Z4.takeAgent ([0, n + 3 + 1] ++ [c]),
          ⟨rest, .half ([0, n + 3 + 1] ++ [c]) ([2] ++ [c]) .add .zero⟩, 0) ∧
      XMach.act xsys Z5 ⟨rest, .half ([0, n + 3 + 1] ++ [c]) ([2] ++ [c]) .add .zero⟩ =
        (Z5.takeAgent ([2] ++ [c]),
          ⟨rest, .write []
            ((addZero.toX.newLinks ar [0, n + 3 + 1] [2] .add .zero).map (tagL c))⟩, 1) := by
  obtain ⟨-, -, h₁, h₂, h₂', hne, h₄⟩ := st.zero_pair hz
  have gne : ([0, n + 3 + 1] ++ [c] : Id) ≠ [2] ++ [c] := fun e =>
    hne (List.append_cancel_right e)
  have hR : xsys.rule .add .zero = some addZero.toX := rfl
  refine ⟨XMach.act_idle_pos (xs := xsys) (e := ([0, n + 3 + 1] ++ [c], Arith.add))
      ((h0.agent _).trans h₁),
    XMach.act_look (xs := xsys)
      ((h1.wire ([0, n + 3 + 1], 0)).trans (congrArg (Option.map (tagPort c)) h₂)),
    XMach.act_seek_next (xs := xsys) (c := ([n + 3 + 1] ++ [c], 1))
      (ite_neg' (show ¬ (1 : Nat) = 0 by decide))
      ((h2.next ([n + 3 + 1], 1) ([0, n + 3 + 1], 0)).trans
        (congrArg (Option.map (tagPort c)) h₂')),
    XMach.act_seek_found (xs := xsys) (c := ([2] ++ [c], 0))
      ((ite_pos' rfl).trans ((h3.agent [2]).trans hz)) ⟨gne, rfl⟩,
    XMach.act_ready (xs := xsys) ((h4.agent _).trans h₁), ?_⟩
  have aY := XMach.act_half (xs := xsys) (X := Z5) (todo := rest)
    (a := [0, n + 3 + 1] ++ [c]) (b := [2] ++ [c]) (α := .add) (β := .zero)
    (R := addZero.toX) ((ite_pos' ⟨(h5.agent [2]).trans h₄, gne⟩).trans hR)
  rw [(rule_tag c hR hne).2] at aY
  exact aY

/-- **Nine rounds: the second thread makes the last interaction of an
addition while the first thread reads.** -/
theorem zero_rounds_read {n : Nat} {XA XB W : XNet Arith} {S : XThread Arith} {K : Nat}
    (stB : Steady n XB (n + 3)) (hz : assoc [2] XB.agents = some .zero) (hA : Looks 0 XA W)
    (hB : Looks 1 XB W) (hS : Scans S.st) (st : Stays xsys XA S ⟨[], .idle⟩ (K + 9))
    (r rest : List (Id × Arith)) :
    ∃ S9, ((⟨W, [tagTh 0 r S, ⟨([0, n + 3 + 1] ++ [1], .add) :: rest, .idle⟩]⟩ :
          XMach Arith).trace xsys (fun i => i % 2) (2 * 9)).1 =
        ⟨stepZ W ([0, n + 3 + 1] ++ [1]) ([2] ++ [1]),
          [tagTh 0 r S9, ⟨(stepZ W ([0, n + 3 + 1] ++ [1]) ([2] ++ [1])).agents, .idle⟩]⟩ ∧
      Scans S9.st ∧ Stays xsys XA S9 ⟨[], .idle⟩ K ∧
      Looks 0 XA (stepZ W ([0, n + 3 + 1] ++ [1]) ([2] ++ [1])) := by
  have hB5 : Looks 1 (XB.takeAgent [0, n + 3 + 1]) (W.takeAgent ([0, n + 3 + 1] ++ [1])) :=
    hB.take [0, n + 3 + 1]
  have hA5 : Looks 0 XA (W.takeAgent ([0, n + 3 + 1] ++ [1])) :=
    hA.take_other (by decide) [0, n + 3 + 1]
  have hA6 : Looks 0 XA ((W.takeAgent ([0, n + 3 + 1] ++ [1])).takeAgent ([2] ++ [1])) :=
    hA5.take_other (by decide) [2]
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := Looks.zero_acts stB hz rest hB hB hB hB hB hB5
  obtain ⟨S1, t1, h1, s1⟩ := read_round hS st hA r q0
  obtain ⟨S2, t2, h2, s2⟩ := read_round h1 s1 hA r q1
  obtain ⟨S3, t3, h3, s3⟩ := read_round h2 s2 hA r q2
  obtain ⟨S4, t4, h4, s4⟩ := read_round h3 s3 hA r q3
  obtain ⟨S5, t5, h5, s5⟩ := read_round h4 s4 hA r q4
  obtain ⟨S6, t6, h6, s6⟩ := read_round h5 s5 hA5 r q5
  have e3 : (addZero.toX.newLinks ar [0, n + 3 + 1] [2] .add .zero).length + 1 = 3 := by
    rw [newLinks_zero]
    rfl
  have s6' : Stays xsys XA S6 ⟨[], .idle⟩
      (K + ((addZero.toX.newLinks ar [0, n + 3 + 1] [2] .add .zero).length + 1)) := by
    rw [e3]
    exact s6
  obtain ⟨S9, t9, h9, s9, hA9⟩ := links_rounds_read (c := 0) (d := 1) (by decide)
    (addZero.toX.newLinks ar [0, n + 3 + 1] [2] .add .zero)
    ((W.takeAgent ([0, n + 3 + 1] ++ [1])).takeAgent ([2] ++ [1])) S6 K rest r h6 s6' hA6
  rw [e3] at t9
  have eW : stepZ W ([0, n + 3 + 1] ++ [1]) ([2] ++ [1]) =
      ((W.takeAgent ([0, n + 3 + 1] ++ [1])).takeAgent ([2] ++ [1])).putLinks
        ((addZero.toX.newLinks ar [0, n + 3 + 1] [2] .add .zero).map (tagL 1)) := by
    rw [stepZ_tag 1 W]
    rfl
  rw [eW]
  refine ⟨S9, ?_, h9, s9, hA9⟩
  rw [show (2 * 9 : Nat) = 2 * (1 + 8) from rfl, trace_mod_add, t1,
    show (2 * 8 : Nat) = 2 * (1 + 7) from rfl, trace_mod_add, t2,
    show (2 * 7 : Nat) = 2 * (1 + 6) from rfl, trace_mod_add, t3,
    show (2 * 6 : Nat) = 2 * (1 + 5) from rfl, trace_mod_add, t4,
    show (2 * 5 : Nat) = 2 * (1 + 4) from rfl, trace_mod_add, t5,
    show (2 * 4 : Nat) = 2 * (1 + 3) from rfl, trace_mod_add, t6]
  exact t9

/-- The first three actions of one thread on an addition only read. -/
theorem solo_three (m n : Nat) :
    (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ 3).1 = sum (m + 1) n := by
  have st := sum_start m n
  obtain ⟨rest, hhead, h₁, h₂, hne, -⟩ := st.pair
  have a1 : XMach.act xsys (sum (m + 1) n) ⟨([n + 3 + m + 1], .succ) :: rest, .idle⟩ =
      (sum (m + 1) n, ⟨rest, .look [n + 3 + m + 1] .succ⟩, 0) :=
    XMach.act_idle_pos (xs := xsys) (e := ([n + 3 + m + 1], Arith.succ)) h₁
  have a2 : XMach.act xsys (sum (m + 1) n) ⟨rest, .look [n + 3 + m + 1] .succ⟩ =
      (sum (m + 1) n, ⟨rest, .seek [n + 3 + m + 1] .succ ([n + 3 + m + 1], 0) ([1], 0)⟩, 0) :=
    XMach.act_look (xs := xsys) h₂
  have a3 : XMach.act xsys (sum (m + 1) n)
      ⟨rest, .seek [n + 3 + m + 1] .succ ([n + 3 + m + 1], 0) ([1], 0)⟩ =
      (sum (m + 1) n, ⟨rest, .ready [n + 3 + m + 1] [1] .succ .add⟩, 0) :=
    XMach.act_seek_found (xs := xsys) (c := ([1], 0)) ((ite_pos' rfl).trans st.adder)
      ⟨hne, rfl⟩
  rw [hhead]
  show (XMach.solo xsys
    (XMach.act xsys (sum (m + 1) n) ⟨([n + 3 + m + 1], .succ) :: rest, .idle⟩).1
    (XMach.act xsys (sum (m + 1) n) ⟨([n + 3 + m + 1], .succ) :: rest, .idle⟩).2.1 2).1 = _
  rw [a1]
  show (XMach.solo xsys
    (XMach.act xsys (sum (m + 1) n) ⟨rest, .look [n + 3 + m + 1] .succ⟩).1
    (XMach.act xsys (sum (m + 1) n) ⟨rest, .look [n + 3 + m + 1] .succ⟩).2.1 1).1 = _
  rw [a2]
  show (XMach.solo xsys
    (XMach.act xsys (sum (m + 1) n)
      ⟨rest, .seek [n + 3 + m + 1] .succ ([n + 3 + m + 1], 0) ([1], 0)⟩).1
    (XMach.act xsys (sum (m + 1) n)
      ⟨rest, .seek [n + 3 + m + 1] .succ ([n + 3 + m + 1], 0) ([1], 0)⟩).2.1 0).1 = _
  rw [a3]
  rfl

/-- **The second thread on `1 + (k + 1)`, `k` at least six.**  Beside the
first thread it only reads: three actions for each successor of the
second argument, one for the adder and one for the zero of the first
argument, which are gone when it comes to them, three for the other zero.
After `3 * k + 8` actions the top successor alone is left in its list. -/
theorem reader_ones (k : Nat) (hk : 6 ≤ k) :
    RdAt 0 (k + 1) ⟨(sum (0 + 1) (k + 1)).agents.drop (0 + 1) ++
        (sum (0 + 1) (k + 1)).agents.take (0 + 1), .idle⟩ (3 * k + 8)
      ⟨[([k + 1 + 3 + 0 + 1], .succ)], .idle⟩ := by
  rw [turn_list_succ 0 k 0 (Nat.le_refl 0)]
  have h0 : RdAt 0 (k + 1) ⟨chainL (k + 1) (0 - 0) ++ (([k + 1 + 3], .succ) :: (sndL k ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (k + 1) (0 - 0 + (0 + 1))).take
            (0 + 1)))), .idle⟩ 0
      ⟨([k + 1 + 3], .succ) :: (sndL k ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (k + 1) (0 - 0 + (0 + 1))).take
            (0 + 1))), .idle⟩ :=
    RdAt.start 0 (k + 1) _
  have hx : assoc [k + 1 + 3] (sum (0 + 1) (k + 1)).agents = some Arith.succ :=
    sum_assoc_base 0 (k + 1) (e := ([k + 1 + 3], Arith.succ))
      (List.mem_append_left _ (sndL_mem (k + 1) k (by omega)))
  have hx3 : assoc [3] (sum (0 + 1) (k + 1)).agents = some Arith.zero :=
    sum_assoc_base 0 (k + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hstop : nextSeg (XMach.solo xsys (sum (0 + 1) (k + 1))
      ⟨(sum (0 + 1) (k + 1)).agents, .idle⟩ (0 + 3)).1.wires ([1], 1) ([k + 1 + 3], 0) = none := by
    show nextSeg (XMach.solo xsys (sum (0 + 1) (k + 1))
      ⟨(sum (0 + 1) (k + 1)).agents, .idle⟩ 3).1.wires ([1], 1) ([k + 1 + 3], 0) = none
    rw [solo_three 0 (k + 1)]
    exact nextSeg_none fun q hq => ((snd_sum (0 + 1) (k + 1)).one q).1 hq
  have h1 := h0.pass3 (solo_snd_forever 0 (k + 1) (j := k + 1 + 3) (by omega) (Nat.le_refl _) hx _)
    (solo_look_top 0 (k + 1) _) (show ¬ (1 : Nat) = 0 by decide) hstop
  have h2 := RdAt.snd k (0 + 3) (by omega) h1
  have h3 := h2.gone (solo_gone5 0 (k + 1) (u := 0 + 3 + 3 * k + 1) (by omega)).2
  have h4 := h3.gone (solo_gone_zero 0 (k + 1) (u := 0 + 3 + 3 * k + 1 + 1) (by omega))
  have h5 := h4.pass3 (solo_snd_forever 0 (k + 1) (j := 3) (by omega) (by omega) hx3 _)
    (solo_look_snd 0 (k + 1) (j := 3) (by omega) (by omega) _).1
    (show ¬ (1 : Nat) = 0 by decide)
    (solo_look_snd 0 (k + 1) (j := 3) (by omega) (by omega) _).2
  exact h5.cast (by omega)

/-- A thread that reads on to rest: where it is after `d` of its
actions. -/
theorem stays_split {X : XNet Arith} : ∀ (d : Nat) {T : XThread Arith} {K : Nat},
    Stays xsys X T ⟨[], .idle⟩ K → d ≤ K → Scans T.st →
      (XMach.solo xsys X T d).1 = X ∧ Scans (XMach.solo xsys X T d).2.st ∧
        Stays xsys X (XMach.solo xsys X T d).2 ⟨[], .idle⟩ (K - d)
  | 0, _, _, st, _, hS => ⟨rfl, hS, st⟩
  | d + 1, T, K, st, hd, hS => by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    obtain ⟨-, T1, h, st'⟩ := stays_inv st
    have hX : (XMach.act xsys X T).1 = X := by rw [h]
    have hS1 := (act_scan hS hX).1
    rw [h] at hS1
    have ih := stays_split d st' (by omega) hS1
    have e : XMach.solo xsys X T (d + 1) = XMach.solo xsys X T1 d := by
      show XMach.solo xsys (XMach.act xsys X T).1 (XMach.act xsys X T).2.1 d = _
      rw [h]
    rw [e]
    have e2 : K' + 1 - (d + 1) = K' - d := by omega
    rw [e2]
    exact ih

/-- **The first thread on `1 + (k + 1)` after `3 * k + 8` actions**: the
addition is done, the memory is final, and the thread has thirty actions
of reading left before it has passed it. -/
theorem ones_first_reads (k : Nat) (hk : 6 ≤ k) :
    ∃ Xf, Final (k + 1) (sum (0 + 1) (k + 1)) Xf (k + 1 + 3 + 0 + 1) 0 ∧
      (XMach.solo xsys (sum (0 + 1) (k + 1)) ⟨(sum (0 + 1) (k + 1)).agents, .idle⟩
        (3 * k + 8)).1 = Xf ∧
      Scans (XMach.solo xsys (sum (0 + 1) (k + 1)) ⟨(sum (0 + 1) (k + 1)).agents, .idle⟩
        (3 * k + 8)).2.st ∧
      Stays xsys Xf (XMach.solo xsys (sum (0 + 1) (k + 1))
        ⟨(sum (0 + 1) (k + 1)).agents, .idle⟩ (3 * k + 8)).2 ⟨[], .idle⟩ 30 := by
  obtain ⟨Xf, F, hf⟩ := solo_final_mem 0 (k + 1)
  obtain ⟨Xf', run, -⟩ := solo_rounds 0 (k + 1)
  have s25 := run.works.solo.1
  have e25 : Xf' = Xf := by
    have h := hf (17 * 0 + 25) (Nat.le_refl _)
    rw [s25] at h
    exact h
  subst e25
  have sA := F.pass_stays (snd_sum (0 + 1) (k + 1)) (sum_fresh (0 + 1) (k + 1))
  obtain ⟨m1, m2, m3⟩ := stays_split (3 * k - 17) sA (by omega) trivial
  have es : XMach.solo xsys (sum (0 + 1) (k + 1)) ⟨(sum (0 + 1) (k + 1)).agents, .idle⟩
      (3 * k + 8) = XMach.solo xsys Xf' ⟨Xf'.agents, .idle⟩ (3 * k - 17) := by
    have e : 3 * k + 8 = 17 * 0 + 25 + (3 * k - 17) := by omega
    rw [e, XMach.solo_add, s25]
  rw [es]
  have e30 : 5 * 0 + 3 * (k + 1) + 10 - (3 * k - 17) = 30 := by omega
  rw [e30] at m3
  exact ⟨Xf', F, m1, m2, m3⟩

/-- In the final memory of an addition the top successor of the first
argument, the first adder and the zero of the first argument are gone. -/
theorem final_gone {n : Nat} {X0 X : XNet Arith} {T d : Nat} (F : Final n X0 X T d) (j : Nat)
    (hj : j = 1 ∨ j = 2 ∨ n + 4 ≤ j) : assoc [j] X.agents = none := by
  rw [F.agents, assoc_append_skip _ (fun e he => res_ne_single he j),
    assoc_append_skip _ (fun e he e' => by
      obtain ⟨-, i, h1, h2, h3⟩ := mem_sndL he
      rw [h3] at e'
      injection e' with e1
      omega)]
  show (if ([3] : Id) = [j] then some Arith.zero else none) = none
  exact ite_neg' fun e => by
    injection e with e1
    omega

theorem twoSolo_ones (n n' : Nat) : twoSolo 1 n 1 n' = 6 * n + 3 * n' + 80 := by
  have e1 := soloWork_succ 0 n
  have e2 := soloWork_succ 0 n'
  show soloWork (0 + 1) n + soloWork (0 + 1) n' + (5 * 1 + 3 * n + 5) = _
  omega

theorem trace_then {M M1 M2 : XMach Arith} {w w' : Nat}
    (h1 : (M.trace xsys (fun i => i % 2) (2 * w)).1 = M1)
    (h2 : (M1.trace xsys (fun i => i % 2) (2 * w')).1 = M2) :
    (M.trace xsys (fun i => i % 2) (2 * (w + w'))).1 = M2 := by
  rw [trace_mod_add, h1]
  exact h2

theorem ones_two_threads_aux (k n' : Nat) (hk : 6 ≤ k) :
    Rounds 2 (XMach.init (twoSums 1 (k + 1) 1 n') 2)
      (3 * k + 8 + 5 + 11 + 9 + (5 * 0 + 3 * (k + 1) + 10 + (5 * 0 + 3 * n' + 10))) := by
  -- the first addition, each thread beside the other
  have rd := reader_ones k hk
  obtain ⟨restA, hAa⟩ := (sum_start 0 (k + 1)).head
  have e : (sum (0 + 1) (k + 1)).agents.drop (0 + 1) ++
      (sum (0 + 1) (k + 1)).agents.take (0 + 1) = restA ++ [([k + 1 + 3 + 0 + 1], .succ)] := by
    rw [hAa]
    rfl
  rw [e] at rd
  have hsw := soloWork_succ 0 (k + 1)
  obtain ⟨Yb, tr, hI, mv⟩ := beside_stretch (sum (0 + 1) n') hAa (3 * k + 8)
    (fun a ha => rd.2 a ha) rd.1 (fun j hj => sum_busy 0 (k + 1) j (by omega))
  obtain ⟨XAf, FA, eXA, hS0, st0⟩ := ones_first_reads k hk
  rw [eXA] at hI
  have hA0 : Looks 0 XAf Yb := hI.looks
  have hB0 : Looks 1 (sum (0 + 1) n') Yb := mv.other 1 _ (by decide) (looks_right _ _)
  have tg0 : ∀ e, e ∈ Yb.agents → tagged 0 e.1 = true ∨ tagged 1 e.1 = true :=
    mv.tags (fun i => tagged 0 i = true ∨ tagged 1 i = true) (fun i => .inl (tagged_self 0 i))
      (fun e he => by
        have he' : e ∈ (sum (0 + 1) (k + 1)).agents.map (tagA 0) ++
            (sum (0 + 1) n').agents.map (tagA 1) := he
        rcases List.mem_append.1 he' with h | h
        · exact .inl (mem_tag_self h)
        · exact .inr (mem_tag_self h))
  -- the second addition alone
  have stB := sum_start 0 n'
  obtain ⟨restB, hBa⟩ := stB.head
  have eB : ((([n' + 3 + 0 + 1], Arith.succ) :: restB : List (Id × Arith))) =
      ([n' + 3 + 0 + 1], Arith.succ) ::
        (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]) :=
    hBa.symm.trans (sum_agents (0 + 1) n')
  have eR := (List.cons.inj eB).2
  subst eR
  obtain ⟨-, -, -, -, hneB, -⟩ := stB.pair
  have hneB' : ([1] : Id) ≠ [n' + 3 + 0 + 1] := fun e => hneB e.symm
  obtain ⟨-, stB1⟩ := Start.round_exact stB
  have stB1' : Steady n' (stepS (sum (0 + 1) n') [n' + 3 + 0 + 1] [1]) (n' + 3) := stB1
  have H0 : Hist n' (sum (0 + 1) n') (stepS (sum (0 + 1) n') [n' + 3 + 0 + 1] [1])
      (n' + 3 + 0 + 1) 0 0 := hist_start (n := n') (r := 0) (sum_agents (0 + 1) n')
  have hz : assoc [2] (stepS (sum (0 + 1) n') [n' + 3 + 0 + 1] [1]).agents = some .zero := by
    rw [H0.agents]
    show (if ([0, n' + 3 + 0 + 1] : Id) = [2] then some Arith.add
      else assoc [2] (resL (n' + 3 + 0) 0 ++
        (sndL n' ++ [([2], Arith.zero), ([3], .zero)]))) = _
    rw [ite_neg' (fun e => by injection e with _ e2; cases e2),
      assoc_append_skip _ (fun e he => res_ne_single he 2),
      assoc_append_skip _ (fun e he e' => by
        obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
        rw [h3] at e'
        injection e' with e1
        omega)]
    rfl
  have FB := H0.final
  -- the machine after the first stretch
  rw [hBa] at tr
  have tr' : ((XMach.init (twoSums 1 (k + 1) 1 n') 2).trace xsys (fun i => i % 2)
      (2 * (3 * k + 8))).1 =
      ⟨Yb, [tagTh 0 ((([n' + 3 + 0 + 1], Arith.succ) ::
            (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1))
          (XMach.solo xsys (sum (0 + 1) (k + 1)) ⟨(sum (0 + 1) (k + 1)).agents, .idle⟩
            (3 * k + 8)).2,
        ⟨([n' + 3 + 0 + 1] ++ [1], .succ) ::
          ((sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]).map (tagA 1) ++
            [tagA 0 ([k + 1 + 3 + 0 + 1], .succ)]), .idle⟩]⟩ := tr
  -- the second thread claims the first pair of the second addition
  obtain ⟨S5, t5, h5, s5⟩ := claim_rounds_read (K := 25) stB hA0 hB0 hS0 st0
    ((([n' + 3 + 0 + 1], Arith.succ) ::
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1))
    ((sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]).map (tagA 1) ++
      [tagA 0 ([k + 1 + 3 + 0 + 1], .succ)])
  have E2 := trace_then tr' t5
  -- and writes what the rule makes of it
  have hlen : (addSucc.swap.toX.newAgents [n' + 3 + 0 + 1] [1]).length +
      (addSucc.swap.toX.newLinks ar [n' + 3 + 0 + 1] [1] .succ .add).length + 1 = 11 := by
    rw [newAgents_swap hneB', newLinks_swap]
    rfl
  have s5' : Stays xsys XAf S5 ⟨[], .idle⟩
      (14 + ((addSucc.swap.toX.newAgents [n' + 3 + 0 + 1] [1]).length +
        (addSucc.swap.toX.newLinks ar [n' + 3 + 0 + 1] [1] .succ .add).length + 1)) := by
    rw [hlen]
    exact s5
  have hA5 : Looks 0 XAf ((Yb.takeAgent ([n' + 3 + 0 + 1] ++ [1])).takeAgent ([1] ++ [1])) :=
    (hA0.take_other (by decide) [n' + 3 + 0 + 1]).take_other (by decide) [1]
  obtain ⟨S16, t16, h16, s16, hA16⟩ := write_rounds_read (c := 0) (d := 1) (by decide)
    (addSucc.swap.toX.newAgents [n' + 3 + 0 + 1] [1])
    (addSucc.swap.toX.newLinks ar [n' + 3 + 0 + 1] [1] .succ .add)
    ((Yb.takeAgent ([n' + 3 + 0 + 1] ++ [1])).takeAgent ([1] ++ [1])) S5 14
    ((sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]).map (tagA 1) ++
      [tagA 0 ([k + 1 + 3 + 0 + 1], .succ)])
    ((([n' + 3 + 0 + 1], Arith.succ) ::
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1)) h5 s5' hA5
  rw [hlen] at t16
  have eW : stepS Yb ([n' + 3 + 0 + 1] ++ [1]) ([1] ++ [1]) =
      (((Yb.takeAgent ([n' + 3 + 0 + 1] ++ [1])).takeAgent ([1] ++ [1])).putAgents
        ((addSucc.swap.toX.newAgents [n' + 3 + 0 + 1] [1]).map (tagA 1))).putLinks
        ((addSucc.swap.toX.newLinks ar [n' + 3 + 0 + 1] [1] .succ .add).map (tagL 1)) := by
    rw [stepS_tag 1 Yb hneB']
    rfl
  rw [← eW] at t16 hA16
  have hB16 : Looks 1 (stepS (sum (0 + 1) n') [n' + 3 + 0 + 1] [1])
      (stepS Yb ([n' + 3 + 0 + 1] ++ [1]) ([1] ++ [1])) := hB0.afterS hneB'
  obtain ⟨ry, hry⟩ := stepS_head 1 Yb hneB'
  have hry' : (stepS Yb ([n' + 3 + 0 + 1] ++ [1]) ([1] ++ [1])).agents =
      ([0, n' + 3 + 1] ++ [1], Arith.add) :: ry := hry
  rw [hry'] at t16
  have E3 := trace_then E2 t16
  -- the second thread makes the last interaction of the second addition
  obtain ⟨S25, t25, h25, s25, hA25⟩ := zero_rounds_read (K := 5) stB1' hz hA16 hB16 h16 s16
    ((([n' + 3 + 0 + 1], Arith.succ) ::
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1)) ry
  have E4 := trace_then E3 t25
  have hBf : Looks 1 (stepZ (stepS (sum (0 + 1) n') [n' + 3 + 0 + 1] [1]) [0, n' + 3 + 1] [2])
      (stepZ (stepS Yb ([n' + 3 + 0 + 1] ++ [1]) ([1] ++ [1])) ([0, n' + 3 + 1] ++ [1])
        ([2] ++ [1])) := hB16.afterZ [0, n' + 3 + 1] [2]
  have tgf : ∀ e, e ∈ (stepZ (stepS Yb ([n' + 3 + 0 + 1] ++ [1]) ([1] ++ [1]))
      ([0, n' + 3 + 1] ++ [1]) ([2] ++ [1])).agents →
      tagged 0 e.1 = true ∨ tagged 1 e.1 = true :=
    (Moves.afterZ 1 (stepS Yb ([n' + 3 + 0 + 1] ++ [1]) ([1] ++ [1])) [0, n' + 3 + 1] [2]).tags
      (fun i => tagged 0 i = true ∨ tagged 1 i = true) (fun i => .inr (tagged_self 1 i))
      ((Moves.afterS 1 Yb hneB').tags (fun i => tagged 0 i = true ∨ tagged 1 i = true)
        (fun i => .inr (tagged_self 1 i)) tg0)
  -- the memory is final: both threads read on
  generalize hYf : stepZ (stepS Yb ([n' + 3 + 0 + 1] ++ [1]) ([1] ++ [1]))
    ([0, n' + 3 + 1] ++ [1]) ([2] ++ [1]) = Yf at E4 hA25 hBf tgf
  generalize hXBf : stepZ (stepS (sum (0 + 1) n') [n' + 3 + 0 + 1] [1]) [0, n' + 3 + 1] [2] =
    XBf at FB hBf
  have sA := FA.pass_stays (snd_sum (0 + 1) (k + 1)) (sum_fresh (0 + 1) (k + 1))
  have sB := FB.pass_stays (snd_sum (0 + 1) n') (sum_fresh (0 + 1) n')
  have pQ := pass_two hA25 hBf Yf.agents XAf.agents XBf.agents _ _ tgf hA25.agents
    hBf.agents sA sB
  -- the first thread: five more actions on the first addition
  obtain ⟨k1, k2, hk12, sP1, sP2⟩ := hA25.pass s25 rfl h25 S25.todo []
    ((([n' + 3 + 0 + 1], Arith.succ) ::
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1))
    (List.append_nil _).symm
  have ek2 := stays_rest_zero sP2
  -- then the cells the second addition had at the start
  have sB' : Stays xsys XBf ⟨resL (n' + 3) 0 ++ (sndL n' ++ [([3], Arith.zero)]), .idle⟩
      ⟨[], .idle⟩ (5 * 0 + 3 * n' + 10) := by
    rw [← FB.agents]
    exact sB
  obtain ⟨j1, j2, hj12, -, sB2⟩ := hBf.pass sB' rfl trivial (resL (n' + 3) 0)
    (sndL n' ++ [([3], Arith.zero)]) [] rfl
  obtain ⟨j3, j4, hj34, sY3, sB4⟩ := hBf.pass sB2 rfl trivial (sndL n') [([3], Arith.zero)]
    [([1] ++ [1], Arith.add), ([2] ++ [1], .zero), ([3] ++ [1], .zero)] rfl
  obtain ⟨j5, j6, hj56, sY5, sB6⟩ := hBf.pass sB4 rfl trivial [([3], Arith.zero)] [] [] rfl
  have ej6 := stays_rest_zero sB6
  have g_top : ¬ assoc ([n' + 3 + 0 + 1] ++ [1]) Yf.agents = some Arith.succ := fun hh => by
    rw [hBf.agent, final_gone FB (n' + 3 + 0 + 1) (by omega)] at hh
    cases hh
  have g_add : ¬ assoc ([1] ++ [1]) Yf.agents = some Arith.add := fun hh => by
    rw [hBf.agent, final_gone FB 1 (.inl rfl)] at hh
    cases hh
  have g_zero : ¬ assoc ([2] ++ [1]) Yf.agents = some Arith.zero := fun hh => by
    rw [hBf.agent, final_gone FB 2 (.inr (.inl rfl))] at hh
    cases hh
  have sT : Stays xsys Yf
      ⟨([n' + 3 + 0 + 1] ++ [1], Arith.succ) :: ((sndL n').map (tagA 1) ++
        [([1] ++ [1], Arith.add), ([2] ++ [1], .zero), ([3] ++ [1], .zero)]), .idle⟩
      ⟨[], .idle⟩ (j3 + (j5 + 1 + 1) + 1) :=
    .step (fun e => List.cons_ne_nil _ _ (congrArg XThread.todo e))
      (XMach.act_idle_neg (xs := xsys) (e := ([n' + 3 + 0 + 1] ++ [1], Arith.succ)) g_top)
      (sY3.trans (.step (fun e => List.cons_ne_nil _ _ (congrArg XThread.todo e))
        (XMach.act_idle_neg (xs := xsys) (e := ([1] ++ [1], Arith.add)) g_add)
        (.step (fun e => List.cons_ne_nil _ _ (congrArg XThread.todo e))
          (XMach.act_idle_neg (xs := xsys) (e := ([2] ++ [1], Arith.zero)) g_zero) sY5)))
  have er : ((([n' + 3 + 0 + 1], Arith.succ) ::
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1)) =
      ([n' + 3 + 0 + 1] ++ [1], Arith.succ) :: ((sndL n').map (tagA 1) ++
        [([1] ++ [1], Arith.add), ([2] ++ [1], .zero), ([3] ++ [1], .zero)]) := by
    show tagA 1 _ :: (sndL n' ++ _).map (tagA 1) = _
    rw [List.map_append]
    rfl
  rw [← er] at sT
  have sP := sP1.trans sT
  have hR : Rounds 2 ⟨Yf, [tagTh 0 ((([n' + 3 + 0 + 1], Arith.succ) ::
        (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1)) S25,
      ⟨Yf.agents, .idle⟩]⟩ (5 * 0 + 3 * (k + 1) + 10 + (5 * 0 + 3 * n' + 10)) :=
    rounds_stays (Ts := [tagTh 0 ((([n' + 3 + 0 + 1], Arith.succ) ::
        (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1)) S25,
      ⟨Yf.agents, .idle⟩])
      (fun T hT => by
        rcases List.mem_cons.1 hT with rfl | hT
        · exact ⟨_, by omega, sP⟩
        · rcases List.mem_cons.1 hT with rfl | hT
          · exact ⟨_, Nat.le_refl _, pQ⟩
          · cases hT)
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, pQ⟩
  exact rounds_after 2 E4 hR (by omega)

/-- **Two threads on `1 + n` beside `1 + n'`, `n` at least seven: exactly
`6 * n + 3 * n' + 50` rounds.**  The first thread makes the two
interactions of the first addition and reads on.  The second reads its
way past the first addition, which is done when it comes to the adder and
the zero, makes the two interactions of the second addition, and passes
the whole memory.  The threads never go for the same pair. -/
theorem ones_two_threads (n n' : Nat) (hn : 7 ≤ n) :
    Rounds 2 (XMach.init (twoSums 1 n 1 n') 2) (6 * n + 3 * n' + 50) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (ones_two_threads_aux k n' (by omega)).cast (by omega)

/-- **Two threads save thirty rounds, for every such size.**  On `1 + n`
beside `1 + n'` with `n` at least seven, one thread takes
`6 * n + 3 * n' + 80` rounds and two threads take thirty fewer. -/
theorem ones_saving (n n' : Nat) (hn : 7 ≤ n) :
    Rounds 1 (XMach.init (twoSums 1 n 1 n') 1) (twoSolo 1 n 1 n') ∧
      Rounds 2 (XMach.init (twoSums 1 n 1 n') 2) (twoSolo 1 n 1 n' - 30) := by
  refine ⟨two_sums_solo 0 n 0 n', (ones_two_threads n n' hn).cast ?_⟩
  rw [twoSolo_ones]
  omega

/-- `1 + 12` beside `1 + 3`: 161 rounds for one thread, 131 for two. -/
theorem Checks.Arith.Apart.c1 : Rounds 1 (XMach.init (twoSums 1 12 1 3) 1) 161 ∧
    Rounds 2 (XMach.init (twoSums 1 12 1 3) 2) 131 :=
  ⟨(ones_saving 12 3 (by decide)).1.cast (by decide), ones_two_threads 12 3 (by decide)⟩

/-- **The first thread after the rounds of its addition**: from its
action `17 * m + 25` on the memory is final and the thread only reads,
until it has passed it with its action `22 * m + 3 * n + 35`. -/
theorem first_reads (m n b : Nat) (h1 : 17 * m + 25 ≤ b) (h2 : b ≤ 22 * m + 3 * n + 35) :
    ∃ Xf, Final n (sum (m + 1) n) Xf (n + 3 + m + 1) m ∧
      (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).1 = Xf ∧
      Scans (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).2.st ∧
      Stays xsys Xf (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).2
        ⟨[], .idle⟩ (22 * m + 3 * n + 35 - b) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = 17 * m + 25 + d := ⟨b - (17 * m + 25), by omega⟩
  obtain ⟨Xf, F, hf⟩ := solo_final_mem m n
  obtain ⟨Xf', run, -⟩ := solo_rounds m n
  have s25 := run.works.solo.1
  have e25 : Xf' = Xf := by
    have h := hf (17 * m + 25) (Nat.le_refl _)
    rw [s25] at h
    exact h
  subst e25
  have sA := F.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
  obtain ⟨m1, m2, m3⟩ := stays_split d sA (by omega) trivial
  rw [XMach.solo_add, s25]
  have e30 : 22 * m + 3 * n + 35 - (17 * m + 25 + d) = 5 * m + 3 * n + 10 - d := by omega
  rw [e30]
  exact ⟨Xf', F, m1, m2, m3⟩

theorem turnRest_le (m n : Nat) : turnRest m n 0 ≤ 4 * m + 3 * n + 13 := by
  cases n with
  | zero =>
    show 3 * (m - 0) + 8 + (3 * (m - 0) + 15) / 16 + 0 ≤ _
    omega
  | succ n' =>
    have hz := zeroCost_le m (turnAt m (n' + 1) 0)
    have ht : turnAt m (n' + 1) 0 = 3 * (m - 0) + 3 * (n' + 1) + 1 + (3 * (m - 0) + 11) / 16 := rfl
    show turnAt m (n' + 1) 0 + zeroCost m (turnAt m (n' + 1) 0) + 3 + (0 + 1) ≤ _
    omega

/-- **The six actions that claim a later pair of an addition inside a
larger memory**: the adder and the next successor of the first
argument. -/
theorem Looks.later_acts {c n hh : Nat} {X : XNet Arith} (st : Steady n X (hh + 1))
    (hn : n + 4 ≤ hh + 1) (rest : List (Id × Arith)) {Z0 Z1 Z2 Z3 Z4 Z5 : XNet Arith}
    (h0 : Looks c X Z0) (h1 : Looks c X Z1) (h2 : Looks c X Z2) (h3 : Looks c X Z3)
    (h4 : Looks c X Z4) (h5 : Looks c (X.takeAgent [0, hh + 1 + 1]) Z5) :
    XMach.act xsys Z0 ⟨([0, hh + 1 + 1] ++ [c], .add) :: rest, .idle⟩ =
        (Z0, ⟨rest, .look ([0, hh + 1 + 1] ++ [c]) .add⟩, 0) ∧
      XMach.act xsys Z1 ⟨rest, .look ([0, hh + 1 + 1] ++ [c]) .add⟩ =
        (Z1, ⟨rest, .seek ([0, hh + 1 + 1] ++ [c]) .add ([0, hh + 1 + 1] ++ [c], 0)
          ([hh + 1 + 1] ++ [c], 1)⟩, 0) ∧
      XMach.act xsys Z2 ⟨rest, .seek ([0, hh + 1 + 1] ++ [c]) .add ([0, hh + 1 + 1] ++ [c], 0)
          ([hh + 1 + 1] ++ [c], 1)⟩ =
        (Z2, ⟨rest, .seek ([0, hh + 1 + 1] ++ [c]) .add ([hh + 1 + 1] ++ [c], 1)
          ([hh + 1] ++ [c], 0)⟩, 0) ∧
      XMach.act xsys Z3 ⟨rest, .seek ([0, hh + 1 + 1] ++ [c]) .add ([hh + 1 + 1] ++ [c], 1)
          ([hh + 1] ++ [c], 0)⟩ =
        (Z3, ⟨rest, .ready ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c]) .add .succ⟩, 0) ∧
      XMach.act xsys Z4 ⟨rest, .ready ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c]) .add .succ⟩ =
        (Z4.takeAgent ([0, hh + 1 + 1] ++ [c]),
          ⟨rest, .half ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c]) .add .succ⟩, 0) ∧
      XMach.act xsys Z5 ⟨rest, .half ([0, hh + 1 + 1] ++ [c]) ([hh + 1] ++ [c]) .add .succ⟩ =
        (Z5.takeAgent ([hh + 1] ++ [c]),
          ⟨rest, .write ((addSucc.toX.newAgents [0, hh + 1 + 1] [hh + 1]).map (tagA c))
            ((addSucc.toX.newLinks ar [0, hh + 1 + 1] [hh + 1] .add .succ).map (tagL c))⟩,
          1) := by
  obtain ⟨-, -, k₁, k₂, k₂', k₃, hne, k₄⟩ := st.round_pair hn
  have gne : ([0, hh + 1 + 1] ++ [c] : Id) ≠ [hh + 1] ++ [c] := fun e =>
    hne (List.append_cancel_right e)
  have hR : xsys.rule .add .succ = some addSucc.toX := rfl
  refine ⟨XMach.act_idle_pos (xs := xsys) (e := ([0, hh + 1 + 1] ++ [c], Arith.add))
      ((h0.agent _).trans k₁),
    XMach.act_look (xs := xsys)
      ((h1.wire ([0, hh + 1 + 1], 0)).trans (congrArg (Option.map (tagPort c)) k₂)),
    XMach.act_seek_next (xs := xsys) (c := ([hh + 1 + 1] ++ [c], 1))
      (ite_neg' (show ¬ (1 : Nat) = 0 by decide))
      ((h2.next ([hh + 1 + 1], 1) ([0, hh + 1 + 1], 0)).trans
        (congrArg (Option.map (tagPort c)) k₂')),
    XMach.act_seek_found (xs := xsys) (c := ([hh + 1] ++ [c], 0))
      ((ite_pos' rfl).trans ((h3.agent [hh + 1]).trans k₃)) ⟨gne, rfl⟩,
    XMach.act_ready (xs := xsys) ((h4.agent _).trans k₁), ?_⟩
  have aY := XMach.act_half (xs := xsys) (X := Z5) (todo := rest)
    (a := [0, hh + 1 + 1] ++ [c]) (b := [hh + 1] ++ [c]) (α := .add) (β := .succ)
    (R := addSucc.toX) ((ite_pos' ⟨(h5.agent [hh + 1]).trans k₄, gne⟩).trans hR)
  rw [(rule_tag c hR hne).1, (rule_tag c hR hne).2] at aY
  exact aY

/-- **Seventeen rounds: the second thread makes a later interaction of an
addition while the first thread reads.** -/
theorem later_rounds_read {n hh : Nat} {XA XB W : XNet Arith} {S : XThread Arith} {K : Nat}
    (stB : Steady n XB (hh + 1)) (hn : n + 4 ≤ hh + 1) (hA : Looks 0 XA W)
    (hB : Looks 1 XB W) (hS : Scans S.st) (st : Stays xsys XA S ⟨[], .idle⟩ (K + 17))
    (r rest : List (Id × Arith)) :
    ∃ S', ((⟨W, [tagTh 0 r S, ⟨([0, hh + 1 + 1] ++ [1], .add) :: rest, .idle⟩]⟩ :
          XMach Arith).trace xsys (fun i => i % 2) (2 * 17)).1 =
        ⟨stepA W ([0, hh + 1 + 1] ++ [1]) ([hh + 1] ++ [1]),
          [tagTh 0 r S', ⟨(stepA W ([0, hh + 1 + 1] ++ [1]) ([hh + 1] ++ [1])).agents,
            .idle⟩]⟩ ∧
      Scans S'.st ∧ Stays xsys XA S' ⟨[], .idle⟩ K ∧
      Looks 0 XA (stepA W ([0, hh + 1 + 1] ++ [1]) ([hh + 1] ++ [1])) := by
  obtain ⟨-, -, -, -, -, -, hne, -⟩ := stB.round_pair hn
  have hB5 : Looks 1 (XB.takeAgent [0, hh + 1 + 1]) (W.takeAgent ([0, hh + 1 + 1] ++ [1])) :=
    hB.take [0, hh + 1 + 1]
  have hA5 : Looks 0 XA (W.takeAgent ([0, hh + 1 + 1] ++ [1])) :=
    hA.take_other (by decide) [0, hh + 1 + 1]
  have hA6 : Looks 0 XA ((W.takeAgent ([0, hh + 1 + 1] ++ [1])).takeAgent ([hh + 1] ++ [1])) :=
    hA5.take_other (by decide) [hh + 1]
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := Looks.later_acts stB hn rest hB hB hB hB hB hB5
  have st' : Stays xsys XA S ⟨[], .idle⟩ (K + 11 + 6) := st
  obtain ⟨S1, t1, h1, s1⟩ := read_round hS st' hA r q0
  obtain ⟨S2, t2, h2, s2⟩ := read_round h1 s1 hA r q1
  obtain ⟨S3, t3, h3, s3⟩ := read_round h2 s2 hA r q2
  obtain ⟨S4, t4, h4, s4⟩ := read_round h3 s3 hA r q3
  obtain ⟨S5, t5, h5, s5⟩ := read_round h4 s4 hA r q4
  obtain ⟨S6, t6, h6, s6⟩ := read_round h5 s5 hA5 r q5
  have hlen : (addSucc.toX.newAgents [0, hh + 1 + 1] [hh + 1]).length +
      (addSucc.toX.newLinks ar [0, hh + 1 + 1] [hh + 1] .add .succ).length + 1 = 11 := by
    rw [newAgents_add hne, newLinks_add]
    rfl
  have s6' : Stays xsys XA S6 ⟨[], .idle⟩
      (K + ((addSucc.toX.newAgents [0, hh + 1 + 1] [hh + 1]).length +
        (addSucc.toX.newLinks ar [0, hh + 1 + 1] [hh + 1] .add .succ).length + 1)) := by
    rw [hlen]
    exact s6
  obtain ⟨S', t', h', s', hA'⟩ := write_rounds_read (c := 0) (d := 1) (by decide)
    (addSucc.toX.newAgents [0, hh + 1 + 1] [hh + 1])
    (addSucc.toX.newLinks ar [0, hh + 1 + 1] [hh + 1] .add .succ)
    ((W.takeAgent ([0, hh + 1 + 1] ++ [1])).takeAgent ([hh + 1] ++ [1])) S6 K rest r h6 s6' hA6
  rw [hlen] at t'
  have eW : stepA W ([0, hh + 1 + 1] ++ [1]) ([hh + 1] ++ [1]) =
      (((W.takeAgent ([0, hh + 1 + 1] ++ [1])).takeAgent ([hh + 1] ++ [1])).putAgents
        ((addSucc.toX.newAgents [0, hh + 1 + 1] [hh + 1]).map (tagA 1))).putLinks
        ((addSucc.toX.newLinks ar [0, hh + 1 + 1] [hh + 1] .add .succ).map (tagL 1)) := by
    rw [stepA_tag 1 W hne]
    rfl
  rw [eW]
  refine ⟨S', ?_, h', s', hA'⟩
  rw [show (2 * 17 : Nat) = 2 * (1 + 16) from rfl, trace_mod_add, t1,
    show (2 * 16 : Nat) = 2 * (1 + 15) from rfl, trace_mod_add, t2,
    show (2 * 15 : Nat) = 2 * (1 + 14) from rfl, trace_mod_add, t3,
    show (2 * 14 : Nat) = 2 * (1 + 13) from rfl, trace_mod_add, t4,
    show (2 * 13 : Nat) = 2 * (1 + 12) from rfl, trace_mod_add, t5,
    show (2 * 12 : Nat) = 2 * (1 + 11) from rfl, trace_mod_add, t6]
  exact t'

/-- **The later rounds of an addition, made by the second thread while the
first reads**: `r` rounds of seventeen. -/
theorem later_many_read {n : Nat} {XA X0 : XNet Arith} {T : Nat} (rr : List (Id × Arith)) :
    ∀ (r : Nat) {XB W : XNet Arith} {d : Nat} {S : XThread Arith} {K : Nat},
      Steady n XB (n + 3 + r) → Hist n X0 XB T r d → Looks 1 XB W → Looks 0 XA W →
      (∃ ry, W.agents = ([0, n + 3 + r + 1] ++ [1], Arith.add) :: ry) → Scans S.st →
      Stays xsys XA S ⟨[], .idle⟩ (K + 17 * r) →
      ∃ XB' W' S', ((⟨W, [tagTh 0 rr S, ⟨W.agents, .idle⟩]⟩ : XMach Arith).trace xsys
            (fun i => i % 2) (2 * (17 * r))).1 =
          ⟨W', [tagTh 0 rr S', ⟨W'.agents, .idle⟩]⟩ ∧
        Steady n XB' (n + 3) ∧ Hist n X0 XB' T 0 (d + r) ∧ Looks 1 XB' W' ∧ Looks 0 XA W' ∧
        Moves 1 W W' ∧ (∃ ry, W'.agents = ([0, n + 3 + 1] ++ [1], Arith.add) :: ry) ∧
        Scans S'.st ∧ Stays xsys XA S' ⟨[], .idle⟩ K
  | 0, XB, W, _, S, _, st, H, hB, hA, hd, hS, sS =>
    ⟨XB, W, S, rfl, st, H, hB, hA, Moves.refl 1 W, hd, hS, sS⟩
  | r + 1, XB, W, d, S, K, st, H, hB, hA, hd, hS, sS => by
    have st' : Steady n XB (n + 3 + r + 1) := st
    obtain ⟨-, st1⟩ := Steady.round_exact st' (by omega)
    obtain ⟨ry, hy⟩ := hd
    have hne : ([0, n + 3 + r + 1 + 1] : Id) ≠ [n + 3 + r + 1] := fun e => by
      injection e with _ e2
      cases e2
    have sS' : Stays xsys XA S ⟨[], .idle⟩ (K + 17 * r + 17) := sS
    obtain ⟨S1, t1, h1, s1, hA1⟩ := later_rounds_read st' (by omega) hA hB hS sS' rr ry
    have t1' : ((⟨W, [tagTh 0 rr S, ⟨W.agents, .idle⟩]⟩ : XMach Arith).trace xsys
        (fun i => i % 2) (2 * 17)).1 =
        ⟨stepA W ([0, n + 3 + r + 1 + 1] ++ [1]) ([n + 3 + r + 1] ++ [1]),
          [tagTh 0 rr S1, ⟨(stepA W ([0, n + 3 + r + 1 + 1] ++ [1])
            ([n + 3 + r + 1] ++ [1])).agents, .idle⟩]⟩ := by
      rw [hy]
      exact t1
    obtain ⟨XB', W', S', t', st2, H2, hB2, hA2, mv2, hd2, hS2, sS2⟩ :=
      later_many_read rr r st1 H.step (hB.afterA hne) hA1 (stepA_head 1 W hne) h1 s1
    refine ⟨XB', W', S', ?_, st2, ?_, hB2, hA2, (Moves.afterA 1 W hne).trans mv2, hd2, hS2,
      sS2⟩
    · have e : 2 * (17 * (r + 1)) = 2 * (17 + 17 * r) := by omega
      rw [e]
      exact trace_then t1' t'
    · have e : d + 1 + r = d + (r + 1) := by omega
      rw [← e]
      exact H2

/-- A thread passes entries whose agents are gone in one action each. -/
theorem gone_chain {c : Nat} {XB Yf : XNet Arith} (hB : Looks c XB Yf) (n : Nat)
    (hg : ∀ j, n + 4 ≤ j → assoc [j] XB.agents = none) :
    ∀ (r : Nat) (rest : List (Id × Arith)),
      Stays xsys Yf ⟨(chainL n r).map (tagA c) ++ rest, .idle⟩ ⟨rest, .idle⟩ r
  | 0, _ => .refl _
  | r + 1, rest =>
    .step (fun e => List.cons_ne_nil _ _ (congrArg XThread.todo e))
      (XMach.act_idle_neg (xs := xsys) (e := ([n + 3 + r + 1] ++ [c], Arith.succ))
        (rest := (chainL n r).map (tagA c) ++ rest) (fun hh => by
          rw [hB.agent, hg (n + 3 + r + 1) (by omega)] at hh
          cases hh))
      (gone_chain hB n hg r rest)

/-- The first six actions of one thread on an addition write no
segment. -/
theorem solo_six_wires (m n : Nat) :
    (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ 6).1.wires =
      (sum (m + 1) n).wires := by
  have st := sum_start m n
  obtain ⟨rest, hA, h₁, h₂, hne, h₄⟩ := st.pair
  have hR : xsys.rule .succ .add = some addSucc.swap.toX := rfl
  have w := XMach.solo_claim_start (xs := xsys) rest h₁ h₂ st.adder hne h₄ hR
  rw [← hA] at w
  have e5 := w.2
  rw [newAgents_swap (a := [1]) (s := [n + 3 + m + 1]) (fun e => hne e.symm)] at e5
  have e6 := XMach.solo_add xsys 5 (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ 1
  rw [e5] at e6
  rw [show (6 : Nat) = 5 + 1 from rfl, e6]
  rfl

/-- **The second thread before the top successor, first argument two.**
On the net for `2 + (n' + 1)` with `n'` at least ten, beside the first
thread, the second thread only reads: three actions for the lower
successor of the first argument, three for each successor of the second,
one for the adder, which is gone, four or one for the zero of the first
argument, three for the other zero. -/
theorem reader_two (n' : Nat) (hn : 10 ≤ n') :
    ∃ b, turnRest 1 (n' + 1) 0 = b + 1 ∧
      RdAt 1 (n' + 1) ⟨(sum (1 + 1) (n' + 1)).agents.drop (0 + 1) ++
        (sum (1 + 1) (n' + 1)).agents.take (0 + 1), .idle⟩ b
        ⟨[([n' + 1 + 3 + 1 + 1], .succ)], .idle⟩ := by
  rw [turn_list_succ 1 n' 0 (by omega)]
  have h0 := RdAt.start 1 (n' + 1) ⟨chainL (n' + 1) (1 - 0) ++ (([n' + 1 + 3], .succ) ::
    (sndL n' ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
      (chainL (n' + 1) (1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩
  have h1 := RdAt.chain_turn (t := 0) (1 - 0) (by omega) (h0.cast (by omega))
  have hx : assoc [n' + 1 + 3] (sum (1 + 1) (n' + 1)).agents = some Arith.succ :=
    sum_assoc_base 1 (n' + 1) (e := ([n' + 1 + 3], Arith.succ))
      (List.mem_append_left _ (sndL_mem (n' + 1) n' (by omega)))
  have hx3 : assoc [3] (sum (1 + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base 1 (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hstop : nextSeg (XMach.solo xsys (sum (1 + 1) (n' + 1))
      ⟨(sum (1 + 1) (n' + 1)).agents, .idle⟩ (3 + 3)).1.wires ([1], 1) ([n' + 1 + 3], 0) =
      none := by
    show nextSeg (XMach.solo xsys (sum (1 + 1) (n' + 1))
      ⟨(sum (1 + 1) (n' + 1)).agents, .idle⟩ 6).1.wires ([1], 1) ([n' + 1 + 3], 0) = none
    rw [solo_six_wires 1 (n' + 1)]
    exact nextSeg_none fun q hq => ((snd_sum (1 + 1) (n' + 1)).one q).1 hq
  have h2 := (h1.cast (show 3 * (1 - 0) = 3 from rfl)).pass3
    (solo_snd_forever 1 (n' + 1) (j := n' + 1 + 3) (by omega) (Nat.le_refl _) hx _)
    (solo_look_top 1 (n' + 1) _) (show ¬ (1 : Nat) = 0 by decide) hstop
  have h3 := RdAt.snd n' (3 + 3) (by omega) h2
  have h4 := h3.gone (solo_gone5 1 (n' + 1) (u := 3 + 3 + 3 * n' + 1) (by omega)).2
  have tail : ∀ a,
      RdAt 1 (n' + 1) ⟨chainL (n' + 1) (1 - 0) ++ (([n' + 1 + 3], .succ) ::
        (sndL n' ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
          (chainL (n' + 1) (1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩ a
        ⟨([3], .zero) :: (chainL (n' + 1) (1 - 0 + (0 + 1))).take (0 + 1), .idle⟩ →
      RdAt 1 (n' + 1) ⟨chainL (n' + 1) (1 - 0) ++ (([n' + 1 + 3], .succ) ::
        (sndL n' ++ (([1], .add) :: ([2], .zero) :: ([3], .zero) ::
          (chainL (n' + 1) (1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩ (a + 3)
        ⟨(chainL (n' + 1) (1 - 0 + (0 + 1))).take (0 + 1), .idle⟩ := fun a h =>
    h.pass3 (solo_snd_forever 1 (n' + 1) (j := 3) (by omega) (by omega) hx3 _)
      (solo_look_snd 1 (n' + 1) (j := 3) (by omega) (by omega) _).1
      (show ¬ (1 : Nat) = 0 by decide)
      (solo_look_snd 1 (n' + 1) (j := 3) (by omega) (by omega) _).2
  have hrest : turnRest 1 (n' + 1) 0 =
      turnAt 1 (n' + 1) 0 + zeroCost 1 (turnAt 1 (n' + 1) 0) + 3 + (0 + 1) := rfl
  have eA : turnAt 1 (n' + 1) 0 = 3 + 3 + 3 * n' + 1 := by
    unfold turnAt
    omega
  by_cases h2c : 3 + 3 + 3 * n' + 1 ≤ 17 * 1 + 20
  · have hal := solo_alive_zero 1 (n' + 1) (j := 2) (u := 3 + 3 + 3 * n' + 1 + 1) (by omega)
      (by omega) (by omega) (sum_zero_agent 1 (n' + 1))
    have s1 := h4.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
    have s2 := s1.step (XMach.act_look (solo_look_two 1 (n' + 1) _))
    have s3 := s2.step (XMach.act_seek_next (seek_aux_none _ _ 1 (by decide))
      ((solo_seek_two 1 (n' + 1) (by omega) _).1 (by omega)))
    have hg := solo_gone_adder 1 (n' + 1) (u := 3 + 3 + 3 * n' + 1 + 1 + 1 + 1 + 1) (by omega)
    have s4 := s3.step (XMach.act_seek_stop ((ite_pos' rfl).trans hg)
      (solo_stop_adder 1 (n' + 1) (by omega) _))
    have ez : zeroCost 1 (turnAt 1 (n' + 1) 0) = 4 := by
      rw [eA]
      unfold zeroCost
      exact (ite_neg' (by omega)).trans (ite_pos' h2c)
    exact ⟨3 + 3 + 3 * n' + 1 + 1 + 1 + 1 + 1 + 3, by omega, tail _ s4⟩
  · have r1 := h4.gone (solo_gone_zero 1 (n' + 1) (by omega))
    have ez : zeroCost 1 (turnAt 1 (n' + 1) 0) = 1 := by
      rw [eA]
      unfold zeroCost
      exact (ite_neg' (by omega)).trans (ite_neg' h2c)
    exact ⟨3 + 3 + 3 * n' + 1 + 1 + 3, by omega, tail _ r1⟩

/-- **The second thread before the top successor, when it comes to it
after the rounds of the first addition**: for every first argument of two
or more. -/
theorem reader_late (m n : Nat) (hm : 1 ≤ m) (hl : 17 * m + 26 ≤ turnRest m n 0) :
    ∃ b, turnRest m n 0 = b + 1 ∧
      RdAt m n ⟨(sum (m + 1) n).agents.drop (0 + 1) ++ (sum (m + 1) n).agents.take (0 + 1),
        .idle⟩ b ⟨[([n + 3 + m + 1], .succ)], .idle⟩ := by
  by_cases h2 : 2 ≤ m
  · have hw : turnAt m n 0 ≤ 17 * m + 6 ∨ 17 * m + 17 ≤ turnAt m n 0 := by
      cases n with
      | zero =>
        refine .inl ?_
        show 3 * (m - 0) + 3 * 0 + 1 + (3 * (m - 0) + 11) / 16 ≤ _
        omega
      | succ n' =>
        have hz := zeroCost_le m (turnAt m (n' + 1) 0)
        have hrest : turnRest m (n' + 1) 0 =
            turnAt m (n' + 1) 0 + zeroCost m (turnAt m (n' + 1) 0) + 3 + (0 + 1) := rfl
        exact .inr (by omega)
    exact reader_top m n h2 hw
  · obtain rfl : m = 1 := by omega
    cases n with
    | zero => exact absurd hl (by decide)
    | succ n' =>
      have hz := zeroCost_le 1 (turnAt 1 (n' + 1) 0)
      have hrest : turnRest 1 (n' + 1) 0 =
          turnAt 1 (n' + 1) 0 + zeroCost 1 (turnAt 1 (n' + 1) 0) + 3 + (0 + 1) := rfl
      have ht : turnAt 1 (n' + 1) 0 =
          3 * (1 - 0) + 3 * (n' + 1) + 1 + (3 * (1 - 0) + 11) / 16 := rfl
      exact reader_two n' (by omega)

/-- **`turnRest` in closed form when the second argument is long.** -/
theorem turnRest_far (m n : Nat) (hn : 5 * m + 7 ≤ n) :
    turnRest m n 0 = 3 * m + 3 * n + 6 + (3 * m + 11) / 16 := by
  obtain ⟨n0, rfl⟩ : ∃ n0, n = n0 + 1 := ⟨n - 1, by omega⟩
  have ht : turnAt m (n0 + 1) 0 =
      3 * (m - 0) + 3 * (n0 + 1) + 1 + (3 * (m - 0) + 11) / 16 := rfl
  have ez : zeroCost m (turnAt m (n0 + 1) 0) = 1 := by
    rw [ht]
    unfold zeroCost
    exact (ite_neg' (by omega)).trans (ite_neg' (by omega))
  show turnAt m (n0 + 1) 0 + zeroCost m (turnAt m (n0 + 1) 0) + 3 + (0 + 1) = _
  rw [ez, ht]
  omega

/-- Before its last round an addition still has the zero of its first
argument. -/
theorem Hist.zero {n : Nat} {X0 X : XNet Arith} {T d : Nat} (H : Hist n X0 X T 0 d) :
    assoc [2] X.agents = some .zero := by
  rw [H.agents]
  show (if ([0, n + 3 + 0 + 1] : Id) = [2] then some Arith.add
    else assoc [2] (resL (n + 3 + 0) d ++
      (sndL n ++ [([2], Arith.zero), ([3], .zero)]))) = _
  rw [ite_neg' (fun e => by injection e with _ e2; cases e2),
    assoc_append_skip _ (fun e he => res_ne_single he 2),
    assoc_append_skip _ (fun e he e' => by
      obtain ⟨-, j, h1, -, h3⟩ := mem_sndL he
      rw [h3] at e'
      injection e' with e1
      omega)]
  rfl

/-- **When each addition is done before the other thread comes to it.**
On `(m + 1) + n` beside `(m' + 1) + n'`, let the second thread read its
way past the first addition in `b` actions, as it does beside the first
thread on that addition alone; let `b` be at least the `17 * m + 25`
rounds of the first addition, and let the `17 * m' + 25` rounds of the
second end before the first thread has read what the first addition
left.  Then the threads never go for the same pair: the second makes
every interaction of the second addition while the first only reads, and
the run ends when the second thread has passed the whole memory. -/
theorem apart_second (m n m' n' b : Nat)
    (rd : RdAt m n ⟨(sum (m + 1) n).agents.drop (0 + 1) ++ (sum (m + 1) n).agents.take (0 + 1),
      .idle⟩ b ⟨[([n + 3 + m + 1], .succ)], .idle⟩)
    (hb : 17 * m + 25 ≤ b) (hb2 : b + 17 * m' + 25 ≤ 22 * m + 3 * n + 35) :
    Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2)
      (b + 5 + 11 + 17 * m' + 9 + (5 * m + 3 * n + 10 + (5 * m' + 3 * n' + 10))) := by
  -- the first addition, each thread beside the other
  obtain ⟨restA, hAa⟩ := (sum_start m n).head
  have e : (sum (m + 1) n).agents.drop (0 + 1) ++
      (sum (m + 1) n).agents.take (0 + 1) = restA ++ [([n + 3 + m + 1], .succ)] := by
    rw [hAa]
    rfl
  rw [e] at rd
  have hsw := soloWork_succ m n
  obtain ⟨Yb, tr, hI, mv⟩ := beside_stretch (sum (m' + 1) n') hAa b
    (fun a ha => rd.2 a ha) rd.1 (fun j hj => sum_busy m n j (by omega))
  obtain ⟨XAf, FA, eXA, hS0, st0⟩ := first_reads m n b hb (by omega)
  obtain ⟨K, hK⟩ : ∃ K, 22 * m + 3 * n + 35 - b = K + 9 + 17 * m' + 11 + 5 :=
    ⟨22 * m + 3 * n + 35 - b - (17 * m' + 25), by omega⟩
  rw [hK] at st0
  rw [eXA] at hI
  have hA0 : Looks 0 XAf Yb := hI.looks
  have hB0 : Looks 1 (sum (m' + 1) n') Yb := mv.other 1 _ (by decide) (looks_right _ _)
  have tg0 : ∀ e, e ∈ Yb.agents → tagged 0 e.1 = true ∨ tagged 1 e.1 = true :=
    mv.tags (fun i => tagged 0 i = true ∨ tagged 1 i = true) (fun i => .inl (tagged_self 0 i))
      (fun e he => by
        have he' : e ∈ (sum (m + 1) n).agents.map (tagA 0) ++
            (sum (m' + 1) n').agents.map (tagA 1) := he
        rcases List.mem_append.1 he' with h | h
        · exact .inl (mem_tag_self h)
        · exact .inr (mem_tag_self h))
  -- the second addition alone
  have stB := sum_start m' n'
  obtain ⟨restB, hBa⟩ := stB.head
  have eB : ((([n' + 3 + m' + 1], Arith.succ) :: restB : List (Id × Arith))) =
      ([n' + 3 + m' + 1], Arith.succ) ::
        (chainL n' m' ++ (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])) :=
    hBa.symm.trans (sum_agents (m' + 1) n')
  have eR := (List.cons.inj eB).2
  subst eR
  obtain ⟨-, -, -, -, hneB, -⟩ := stB.pair
  have hneB' : ([1] : Id) ≠ [n' + 3 + m' + 1] := fun e => hneB e.symm
  obtain ⟨-, stB1⟩ := Start.round_exact stB
  have H0 : Hist n' (sum (m' + 1) n') (stepS (sum (m' + 1) n') [n' + 3 + m' + 1] [1])
      (n' + 3 + m' + 1) m' 0 := hist_start (n := n') (r := m') (sum_agents (m' + 1) n')
  -- the machine after the first stretch
  rw [hBa] at tr
  have tr' : ((XMach.init (twoSums (m + 1) n (m' + 1) n') 2).trace xsys (fun i => i % 2)
      (2 * b)).1 =
      ⟨Yb, [tagTh 0 ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
            (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1))
          (XMach.solo xsys (sum (m + 1) n) ⟨(sum (m + 1) n).agents, .idle⟩ b).2,
        ⟨([n' + 3 + m' + 1] ++ [1], .succ) ::
          ((chainL n' m' ++
            (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1) ++
            [tagA 0 ([n + 3 + m + 1], .succ)]), .idle⟩]⟩ := tr
  -- the second thread claims the first pair of the second addition
  obtain ⟨S5, t5, h5, s5⟩ := claim_rounds_read (K := K + 9 + 17 * m' + 11) stB hA0 hB0 hS0 st0
    ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1))
    ((chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1) ++
      [tagA 0 ([n + 3 + m + 1], .succ)])
  have E2 := trace_then tr' t5
  -- and writes what the rule makes of it
  have hlen : (addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).length +
      (addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).length + 1 = 11 := by
    rw [newAgents_swap hneB', newLinks_swap]
    rfl
  have s5' : Stays xsys XAf S5 ⟨[], .idle⟩
      (K + 9 + 17 * m' + ((addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).length +
        (addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).length + 1)) := by
    rw [hlen]
    exact s5
  have hA5 : Looks 0 XAf ((Yb.takeAgent ([n' + 3 + m' + 1] ++ [1])).takeAgent ([1] ++ [1])) :=
    (hA0.take_other (by decide) [n' + 3 + m' + 1]).take_other (by decide) [1]
  obtain ⟨S16, t16, h16, s16, hA16⟩ := write_rounds_read (c := 0) (d := 1) (by decide)
    (addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1])
    (addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add)
    ((Yb.takeAgent ([n' + 3 + m' + 1] ++ [1])).takeAgent ([1] ++ [1])) S5 (K + 9 + 17 * m')
    ((chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)])).map (tagA 1) ++
      [tagA 0 ([n + 3 + m + 1], .succ)])
    ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1)) h5 s5' hA5
  rw [hlen] at t16
  have eW : stepS Yb ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1]) =
      (((Yb.takeAgent ([n' + 3 + m' + 1] ++ [1])).takeAgent ([1] ++ [1])).putAgents
        ((addSucc.swap.toX.newAgents [n' + 3 + m' + 1] [1]).map (tagA 1))).putLinks
        ((addSucc.swap.toX.newLinks ar [n' + 3 + m' + 1] [1] .succ .add).map (tagL 1)) := by
    rw [stepS_tag 1 Yb hneB']
    rfl
  rw [← eW] at t16 hA16
  have hB16 : Looks 1 (stepS (sum (m' + 1) n') [n' + 3 + m' + 1] [1])
      (stepS Yb ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1])) := hB0.afterS hneB'
  obtain ⟨ry, hry⟩ := stepS_head 1 Yb hneB'
  have hry' : (stepS Yb ([n' + 3 + m' + 1] ++ [1]) ([1] ++ [1])).agents =
      ([0, n' + 3 + m' + 1] ++ [1], Arith.add) :: ry := hry
  have E3 := trace_then E2 t16
  -- then the other successor interactions of the second addition
  obtain ⟨XB', W', S', tM, st2, H2, hB2, hA2, mv2, ⟨ry2, hry2⟩, hS2, sS2⟩ :=
    later_many_read ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1))
      m' stB1 H0 hB16 hA16 ⟨ry, hry'⟩ h16 s16
  have E3b := trace_then E3 tM
  rw [hry2] at E3b
  rw [Nat.zero_add] at H2
  -- and the last interaction of the second addition
  obtain ⟨S25, t25, h25, s25, hA25⟩ := zero_rounds_read (K := K) st2 H2.zero hA2 hB2 hS2 sS2
    ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1)) ry2
  have E4 := trace_then E3b t25
  have hBf : Looks 1 (stepZ XB' [0, n' + 3 + 1] [2])
      (stepZ W' ([0, n' + 3 + 1] ++ [1]) ([2] ++ [1])) := hB2.afterZ [0, n' + 3 + 1] [2]
  have tgf : ∀ e, e ∈ (stepZ W' ([0, n' + 3 + 1] ++ [1]) ([2] ++ [1])).agents →
      tagged 0 e.1 = true ∨ tagged 1 e.1 = true :=
    (Moves.afterZ 1 W' [0, n' + 3 + 1] [2]).tags
      (fun i => tagged 0 i = true ∨ tagged 1 i = true) (fun i => .inr (tagged_self 1 i))
      (mv2.tags (fun i => tagged 0 i = true ∨ tagged 1 i = true)
        (fun i => .inr (tagged_self 1 i))
        ((Moves.afterS 1 Yb hneB').tags (fun i => tagged 0 i = true ∨ tagged 1 i = true)
          (fun i => .inr (tagged_self 1 i)) tg0))
  have FB := H2.final
  -- the memory is final: both threads read on
  generalize hYf : stepZ W' ([0, n' + 3 + 1] ++ [1]) ([2] ++ [1]) = Yf at E4 hA25 hBf tgf
  generalize hXBf : stepZ XB' [0, n' + 3 + 1] [2] = XBf at FB hBf
  have sA := FA.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
  have sB := FB.pass_stays (snd_sum (m' + 1) n') (sum_fresh (m' + 1) n')
  have pQ := pass_two hA25 hBf Yf.agents XAf.agents XBf.agents _ _ tgf hA25.agents
    hBf.agents sA sB
  -- the first thread: what is left of its pass over the first addition
  obtain ⟨k1, k2, hk12, sP1, sP2⟩ := hA25.pass s25 rfl h25 S25.todo []
    ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1))
    (List.append_nil _).symm
  have ek2 := stays_rest_zero sP2
  -- then the cells the second addition had at the start
  have sB' : Stays xsys XBf ⟨resL (n' + 3) m' ++ (sndL n' ++ [([3], Arith.zero)]), .idle⟩
      ⟨[], .idle⟩ (5 * m' + 3 * n' + 10) := by
    rw [← FB.agents]
    exact sB
  obtain ⟨j1, j2, hj12, -, sB2⟩ := hBf.pass sB' rfl trivial (resL (n' + 3) m')
    (sndL n' ++ [([3], Arith.zero)]) [] rfl
  obtain ⟨j3, j4, hj34, sY3, sB4⟩ := hBf.pass sB2 rfl trivial (sndL n') [([3], Arith.zero)]
    [([1] ++ [1], Arith.add), ([2] ++ [1], .zero), ([3] ++ [1], .zero)] rfl
  obtain ⟨j5, j6, hj56, sY5, sB6⟩ := hBf.pass sB4 rfl trivial [([3], Arith.zero)] [] [] rfl
  have ej6 := stays_rest_zero sB6
  have g_add : ¬ assoc ([1] ++ [1]) Yf.agents = some Arith.add := fun hh => by
    rw [hBf.agent, final_gone FB 1 (.inl rfl)] at hh
    cases hh
  have g_zero : ¬ assoc ([2] ++ [1]) Yf.agents = some Arith.zero := fun hh => by
    rw [hBf.agent, final_gone FB 2 (.inr (.inl rfl))] at hh
    cases hh
  have sT : Stays xsys Yf
      ⟨(chainL n' (m' + 1)).map (tagA 1) ++ ((sndL n').map (tagA 1) ++
        [([1] ++ [1], Arith.add), ([2] ++ [1], .zero), ([3] ++ [1], .zero)]), .idle⟩
      ⟨[], .idle⟩ (m' + 1 + (j3 + (j5 + 1 + 1))) :=
    (gone_chain hBf n' (fun j hj => final_gone FB j (.inr (.inr hj))) (m' + 1) _).trans
      (sY3.trans (.step (fun e => List.cons_ne_nil _ _ (congrArg XThread.todo e))
        (XMach.act_idle_neg (xs := xsys) (e := ([1] ++ [1], Arith.add)) g_add)
        (.step (fun e => List.cons_ne_nil _ _ (congrArg XThread.todo e))
          (XMach.act_idle_neg (xs := xsys) (e := ([2] ++ [1], Arith.zero)) g_zero) sY5)))
  have er : ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
      (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1)) =
      (chainL n' (m' + 1)).map (tagA 1) ++ ((sndL n').map (tagA 1) ++
        [([1] ++ [1], Arith.add), ([2] ++ [1], .zero), ([3] ++ [1], .zero)]) := by
    show (chainL n' (m' + 1) ++ (sndL n' ++ _)).map (tagA 1) = _
    rw [List.map_append, List.map_append]
    rfl
  rw [← er] at sT
  have sP := sP1.trans sT
  have hR : Rounds 2 ⟨Yf, [tagTh 0 ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
        (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1)) S25,
      ⟨Yf.agents, .idle⟩]⟩ (5 * m + 3 * n + 10 + (5 * m' + 3 * n' + 10)) :=
    rounds_stays (Ts := [tagTh 0 ((([n' + 3 + m' + 1], Arith.succ) :: (chainL n' m' ++
        (sndL n' ++ [([1], Arith.add), ([2], .zero), ([3], .zero)]))).map (tagA 1)) S25,
      ⟨Yf.agents, .idle⟩])
      (fun T hT => by
        rcases List.mem_cons.1 hT with rfl | hT
        · exact ⟨_, by omega, sP⟩
        · rcases List.mem_cons.1 hT with rfl | hT
          · exact ⟨_, Nat.le_refl _, pQ⟩
          · cases hT)
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, pQ⟩
  exact rounds_after 2 E4 hR (by omega)

theorem turnRest_ge (m n : Nat) : 3 * m + 3 * (n + 1) + 5 ≤ turnRest m (n + 1) 0 := by
  have ht : turnAt m (n + 1) 0 = 3 * (m - 0) + 3 * (n + 1) + 1 + (3 * (m - 0) + 11) / 16 := rfl
  show _ ≤ turnAt m (n + 1) 0 + zeroCost m (turnAt m (n + 1) 0) + 3 + (0 + 1)
  omega

theorem twoSolo_apart (m n m' n' : Nat) :
    twoSolo (m + 1) n (m' + 1) n' = 27 * m + 6 * n + 22 * m' + 3 * n' + 80 := by
  have e1 := soloWork_succ m n
  have e2 := soloWork_succ m' n'
  show soloWork (m + 1) n + soloWork (m' + 1) n' + (5 * (m + 1) + 3 * n + 5) = _
  omega

/-- **Two threads on `(m + 1) + n` beside `(m' + 1) + n'`, when each
addition is done before the other thread comes to it**: with `m` at least
one, `turnRest m n 0` at least `17 * m + 26` and
`turnRest m n 0 + 17 * m' + 24` at most `22 * m + 3 * n + 35`, the run
takes exactly `turnRest m n 0 + 5 * m + 3 * n + 22 * m' + 3 * n' + 44`
rounds. -/
theorem apart_two_threads (m n m' n' : Nat) (hm : 1 ≤ m) (hl : 17 * m + 26 ≤ turnRest m n 0)
    (hr : turnRest m n 0 + 17 * m' + 24 ≤ 22 * m + 3 * n + 35) :
    Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2)
      (turnRest m n 0 + 5 * m + 3 * n + 22 * m' + 3 * n' + 44) := by
  obtain ⟨b, eb, rd⟩ := reader_late m n hm hl
  exact (apart_second m n m' n' b rd (by omega) (by omega)).cast (by omega)

/-- **The saving**: `22 * m + 3 * n + 36 - turnRest m n 0` rounds, which
is at least `18 * m + 23` and at least `17 * m' + 25`. -/
theorem apart_saving (m n m' n' : Nat) (hm : 1 ≤ m) (hl : 17 * m + 26 ≤ turnRest m n 0)
    (hr : turnRest m n 0 + 17 * m' + 24 ≤ 22 * m + 3 * n + 35) :
    Rounds 1 (XMach.init (twoSums (m + 1) n (m' + 1) n') 1) (twoSolo (m + 1) n (m' + 1) n') ∧
      Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2)
        (turnRest m n 0 + 5 * m + 3 * n + 22 * m' + 3 * n' + 44) ∧
      turnRest m n 0 + 5 * m + 3 * n + 22 * m' + 3 * n' + 44 +
          (22 * m + 3 * n + 36 - turnRest m n 0) = twoSolo (m + 1) n (m' + 1) n' ∧
      18 * m + 23 ≤ 22 * m + 3 * n + 36 - turnRest m n 0 ∧
      17 * m' + 25 ≤ 22 * m + 3 * n + 36 - turnRest m n 0 := by
  have hle := turnRest_le m n
  refine ⟨two_sums_solo m n m' n', apart_two_threads m n m' n' hm hl hr, ?_, by omega,
    by omega⟩
  rw [twoSolo_apart]
  omega

/-- **A family of sizes where two threads save, with the rounds in closed
form.**  On `(m + 1) + n` beside `(m' + 1) + n'`, whenever the second
argument of the first addition is at least `5 * m + 7` and the first
argument of the second addition is no longer than that of the first: one
thread takes `27 * m + 6 * n + 22 * m' + 3 * n' + 80` rounds, two threads
take `8 * m + 6 * n + 22 * m' + 3 * n' + 50 + (3 * m + 11) / 16`, which is
at least `18 * m + 29` fewer. -/
theorem apart_family (m n m' n' : Nat) (hm' : m' ≤ m) (hn : 5 * m + 7 ≤ n) :
    Rounds 1 (XMach.init (twoSums (m + 1) n (m' + 1) n') 1)
        (27 * m + 6 * n + 22 * m' + 3 * n' + 80) ∧
      Rounds 2 (XMach.init (twoSums (m + 1) n (m' + 1) n') 2)
        (8 * m + 6 * n + 22 * m' + 3 * n' + 50 + (3 * m + 11) / 16) ∧
      8 * m + 6 * n + 22 * m' + 3 * n' + 50 + (3 * m + 11) / 16 + (18 * m + 29) ≤
        27 * m + 6 * n + 22 * m' + 3 * n' + 80 := by
  have h1 := two_sums_solo m n m' n'
  rw [twoSolo_apart] at h1
  refine ⟨h1, ?_, by omega⟩
  by_cases hm : 1 ≤ m
  · have hf := turnRest_far m n hn
    exact (apart_two_threads m n m' n' hm (by omega) (by omega)).cast (by omega)
  · obtain rfl : m = 0 := by omega
    obtain rfl : m' = 0 := by omega
    exact (ones_two_threads n n' (by omega)).cast (by omega)

/-- **The same addition twice**: `(m + 1) + n` beside itself, `n` at least
`5 * m + 7`. -/
theorem twice_family (m n : Nat) (hn : 5 * m + 7 ≤ n) :
    Rounds 1 (XMach.init (twoSums (m + 1) n (m + 1) n) 1) (49 * m + 9 * n + 80) ∧
      Rounds 2 (XMach.init (twoSums (m + 1) n (m + 1) n) 2)
        (30 * m + 9 * n + 50 + (3 * m + 11) / 16) := by
  obtain ⟨h1, h2, -⟩ := apart_family m n m n (Nat.le_refl m) hn
  exact ⟨h1.cast (by omega), h2.cast (by omega)⟩

/-- `6 + 31` beside `1 + 2`: 407 rounds for one thread, 283 for two. -/
theorem Checks.Arith.Apart.c2 : Rounds 1 (XMach.init (twoSums 6 31 1 2) 1) 407 ∧
    Rounds 2 (XMach.init (twoSums 6 31 1 2) 2) 283 :=
  ⟨(apart_saving 5 31 0 2 (by decide) (by decide) (by decide)).1.cast (by decide),
    (apart_two_threads 5 31 0 2 (by decide) (by decide) (by decide)).cast (by decide)⟩

/-- `6 + 32` twice: 613 rounds for one thread, 489 for two. -/
theorem Checks.Arith.Apart.c3 : Rounds 1 (XMach.init (twoSums 6 32 6 32) 1) 613 ∧
    Rounds 2 (XMach.init (twoSums 6 32 6 32) 2) 489 := twice_family 5 32 (by decide)

/-- `2 + 12` twice: 237 rounds for one thread, 188 for two. -/
theorem Checks.Arith.Apart.c4 : Rounds 1 (XMach.init (twoSums 2 12 2 12) 1) 237 ∧
    Rounds 2 (XMach.init (twoSums 2 12 2 12) 2) 188 := twice_family 1 12 (by decide)

/-- `1 + 7` twice: 143 rounds for one thread, 113 for two. -/
theorem Checks.Arith.Apart.c5 : Rounds 1 (XMach.init (twoSums 1 7 1 7) 1) 143 ∧
    Rounds 2 (XMach.init (twoSums 1 7 1 7) 2) 113 := twice_family 0 7 (by decide)

end Arith

end INet
