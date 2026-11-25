import InteractionNets.Arith.Census

/-! ### What the memory holds at rest: the sums, and nothing else -/

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

/-- **A net within a larger memory**: the segments of `X` are in `Y` with
the tag `c` at the end of every name, and the agents and the free ports
of `Y` with the tag are those of `X`. -/
structure Within (c : Nat) (X Y : XNet Arith) : Prop where
  link : ∀ p q, (p, q) ∈ X.wires → (tagPort c p, tagPort c q) ∈ Y.wires
  agent : ∀ i γ, (i ++ [c], γ) ∈ Y.agents ↔ (i, γ) ∈ X.agents
  free : ∀ p, tagPort c p ∈ Y.free ↔ p ∈ X.free

theorem Within.end_iff {c : Nat} {X Y : XNet Arith} (h : Within c X Y) (p : Port) :
    Y.toNet.End ar (tagPort c p) ↔ X.toNet.End ar p := by
  show (tagPort c p ∈ Y.free ∨ ∃ γ, (p.1 ++ [c], γ) ∈ Y.agents ∧ p.2 ≤ ar γ) ↔
    (p ∈ X.free ∨ ∃ γ, (p.1, γ) ∈ X.agents ∧ p.2 ≤ ar γ)
  exact or_congr (h.free p) (exists_congr fun γ => and_congr (h.agent p.1 γ) Iff.rfl)

/-- A wire of the net is a wire of the memory. -/
theorem Within.walk {c : Nat} {X Y : XNet Arith} (h : Within c X Y) {u v x y : Port}
    (w : Walk X.toNet.link (X.toNet.End ar) u v x y) :
    Walk Y.toNet.link (Y.toNet.End ar) (tagPort c u) (tagPort c v) (tagPort c x)
      (tagPort c y) := by
  induction w with
  | single hl => exact .single (h.link _ _ hl)
  | cons hl hT hne _ ih =>
    exact .cons (h.link _ _ hl) (fun he => hT ((h.end_iff _).1 he))
      (fun e => hne (tagPort_inj e)) ih

theorem Within.paired {c : Nat} {X Y : XNet Arith} (h : Within c X Y) {p q : Port}
    (hp : X.toNet.Paired ar p q) : Y.toNet.Paired ar (tagPort c p) (tagPort c q) := by
  obtain ⟨e1, e2, v, x, w⟩ := hp
  exact ⟨(h.end_iff p).2 e1, (h.end_iff q).2 e2, tagPort c v, tagPort c x, h.walk w⟩

theorem Within.num {c : Nat} {X Y : XNet Arith} (h : Within c X Y) :
    ∀ {k : Nat} {i : Id}, Num X.toNet i k → Num Y.toNet (i ++ [c]) k
  | 0, i, hz => (h.agent i zero).2 hz
  | _ + 1, i, ⟨hs, i', hp, hn⟩ => ⟨(h.agent i succ).2 hs, i' ++ [c], h.paired hp, h.num hn⟩

/-- **A numeral of the net is a numeral of the memory.** -/
theorem Within.isNum {c : Nat} {X Y : XNet Arith} (h : Within c X Y) {p : Port} {k : Nat}
    (hn : IsNum X.toNet p k) : IsNum Y.toNet (tagPort c p) k := by
  obtain ⟨i, hp, hk⟩ := hn
  exact ⟨i ++ [c], h.paired hp, h.num hk⟩

/-- A memory whose cells with the tag are a net with the agents and the
segments of `X` holds `X` within it. -/
theorem Looks.within {c : Nat} {X X' Y : XNet Arith} (h : Looks c X' Y)
    (ha : X.agents = X'.agents) (hw : ∀ e, e ∈ X.wires ↔ e ∈ X'.wires)
    (hf : ∀ p, tagPort c p ∈ Y.free ↔ p ∈ X.free) : Within c X Y where
  link := fun p q hl => by
    have h1 : tagL c (p, q) ∈ X'.wires.map (tagL c) := List.mem_map_of_mem ((hw (p, q)).1 hl)
    rw [← h.wires] at h1
    exact (List.mem_filter.1 h1).1
  agent := fun i γ => by
    rw [ha]
    constructor
    · intro hy
      have h1 : (i ++ [c], γ) ∈ Y.agents.filter (fun e => tagged c e.1) :=
        List.mem_filter.2 ⟨hy, tagged_self c i⟩
      rw [h.agents] at h1
      obtain ⟨e, he, ee⟩ := List.mem_map.1 h1
      have e1 : e.1 ++ [c] = i ++ [c] := congrArg Prod.fst ee
      have e2 : e.2 = γ := congrArg Prod.snd ee
      have e3 : e = (i, γ) := Prod.ext (List.append_cancel_right e1) e2
      rw [← e3]
      exact he
    · intro hx
      have h1 : tagA c (i, γ) ∈ X'.agents.map (tagA c) := List.mem_map_of_mem hx
      rw [← h.agents] at h1
      exact (List.mem_filter.1 h1).1
  free := hf

/-- The free ports are never written. -/
theorem works_free {X X' : XNet Arith} {T T' : XThread Arith} {c k : Nat}
    (w : Works xsys X T X' T' c k) : X'.free = X.free := by
  induction w with
  | refl X T => rfl
  | @step X X₁ X' T T₁ T' c₁ c k hT h _ ih =>
    have e : X₁.free = X.free := by
      have a := XMach.act_free xsys X T
      rw [h] at a
      exact a
    exact ih.trans e

theorem free_tag0 (A B : List Port) (p : Port) :
    tagPort 0 p ∈ A.map (tagPort 0) ++ B.map (tagPort 1) ↔ p ∈ A := by
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨q, hq, e⟩ := List.mem_map.1 h
      rw [← tagPort_inj e]
      exact hq
    · obtain ⟨q, -, e⟩ := List.mem_map.1 h
      have e1 : q.1 ++ [1] = p.1 ++ [0] := congrArg Prod.fst e
      exact absurd (snoc_inj e1).2 (by decide)
  · intro h
    exact List.mem_append_left _ (List.mem_map_of_mem h)

theorem free_tag1 (A B : List Port) (p : Port) :
    tagPort 1 p ∈ A.map (tagPort 0) ++ B.map (tagPort 1) ↔ p ∈ B := by
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨q, -, e⟩ := List.mem_map.1 h
      have e1 : q.1 ++ [0] = p.1 ++ [1] := congrArg Prod.fst e
      exact absurd (snoc_inj e1).2 (by decide)
    · obtain ⟨q, hq, e⟩ := List.mem_map.1 h
      rw [← tagPort_inj e]
      exact hq
  · intro h
    exact List.mem_append_right _ (List.mem_map_of_mem h)

/-- **Runs that end at rest hold the same net**, whatever the numbers of
threads and the schedules. -/
theorem rest_mem_eq {X : XNet Arith} (hX : X.toNet.WF ar) {nt nt' : Nat} (hnt : 0 < nt)
    (hnt' : 0 < nt') (σ σ' : Nat → Nat) {i j : Nat}
    (h1 : ((XMach.init X nt).trace xsys σ i).1.resting = true)
    (h2 : ((XMach.init X nt').trace xsys σ' j).1.resting = true) :
    ((XMach.init X nt).trace xsys σ i).1.mem.toNet =
      ((XMach.init X nt').trace xsys σ' j).1.mem.toNet := by
  have L1 := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  have L2 := XMach.trace_live σ' (XMach.init_live (xs := xsys) hX hnt') j
  obtain ⟨q1, n1⟩ := L1.rest h1
  obtain ⟨q2, n2⟩ := L2.rest h2
  have r1 := XMach.trace_run xsys σ (XMach.init X nt) i
  have r2 := XMach.trace_run xsys σ' (XMach.init X nt') j
  rw [XMach.init_toMach] at r1 r2
  exact (MRun.confluent hX r1 r2 q1 q2 n1 n2).1

/-- **One addition comes out right, whatever the threads do**: with any
number of threads and any schedule, a memory at rest has the numeral
`m + n` on the free port. -/
theorem sum_rest_num (m n : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sum m n) nt).trace xsys σ i).1.resting = true) :
    IsNum ((XMach.init (sum m n) nt).trace xsys σ i).1.mem.toNet ([0], 0) (m + n) := by
  have g := good_sum m n
  obtain ⟨N', hs, hn', hnum⟩ := add_correct g.config
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) g.ok.1 hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (sum m n) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final g.ok.1 r q hn
  obtain ⟨e, -⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (sum m n) nt).trace xsys σ i).1.mem.toNet := e
  rw [← e']
  exact hnum

/-- **The memory one thread leaves on an addition carries the sum**: the
memory described by `Final`, with the free port of the start and the
numeral `(m + 1) + n` on it. -/
theorem solo_final_num (m n : Nat) : ∃ Xf, Final n (sum (m + 1) n) Xf (n + 3 + m + 1) m ∧
    Xf.free = (sum (m + 1) n).free ∧ IsNum Xf.toNet ([0], 0) (m + 1 + n) := by
  obtain ⟨Xf, r, F⟩ := solo_rounds m n
  have p := F.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
  have w := r.works.trans p.works
  have t := w.trace.1
  have h1 : ((XMach.init (sum (m + 1) n) 1).trace xsys (fun _ => 0)
      (17 * m + 25 + (5 * m + 3 * n + 10))).1.resting = true := by
    rw [XMach.init_one, t]
    rfl
  have hnum := sum_rest_num (m + 1) n (Nat.zero_lt_one) (fun _ => 0) h1
  rw [XMach.init_one, t] at hnum
  exact ⟨Xf, F, works_free w, hnum⟩

/-- **One thread on two additions side by side: what it leaves.**  The
memory at rest, and the memories that the rounds on each addition alone
leave, seen in it. -/
theorem two_sums_solo_final (m n m' n' : Nat) : ∃ Yf XAf XBf,
    Works xsys (twoSums (m + 1) n (m' + 1) n')
      ⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩ Yf ⟨[], .idle⟩ (m + m' + 4)
      (twoSolo (m + 1) n (m' + 1) n') ∧
    Final n (sum (m + 1) n) XAf (n + 3 + m + 1) m ∧ Looks 0 XAf Yf ∧
    Final n' (sum (m' + 1) n') XBf (n' + 3 + m' + 1) m' ∧ Looks 1 XBf Yf := by
  have hA0 : Looks 0 (sum (m + 1) n) (twoSums (m + 1) n (m' + 1) n') := looks_left _ _
  have hB0 : Looks 1 (sum (m' + 1) n') (twoSums (m + 1) n (m' + 1) n') := looks_right _ _
  have eY0 : (twoSums (m + 1) n (m' + 1) n').agents =
      (sum (m + 1) n).agents.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1) := rfl
  have stA : Start n (sum (m + 1) n) (n + 3 + m) := by
    have h := start_sum m n
    have e : m + n + 3 = n + 3 + m := by omega
    rw [e] at h
    exact h
  have stB : Start n' (sum (m' + 1) n') (n' + 3 + m') := by
    have h := start_sum m' n'
    have e : m' + n' + 3 = n' + 3 + m' := by omega
    rw [e] at h
    exact h
  obtain ⟨restA, hAa⟩ := stA.head
  obtain ⟨restB, hBa⟩ := stB.head
  obtain ⟨XAf, Y1, wA, FA, hA1, mvA⟩ :=
    hA0.rounds_all (restA.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1))
  have wA' : Works xsys (twoSums (m + 1) n (m' + 1) n')
      ⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩ Y1 ⟨Y1.agents, .idle⟩ (m + 2)
      (17 * m + 25) := by
    rw [eY0, hAa]
    exact wA
  have hB1 : Looks 1 (sum (m' + 1) n') Y1 := mvA.other 1 _ (by decide) hB0
  obtain ⟨N', hN', hNt⟩ := mvA.keep ((sum (m + 1) n).agents.map (tagA 0))
    ((sum (m' + 1) n').agents.map (tagA 1)) eY0 (fun _ he => mem_tag_self he)
    (fun _ he => mem_tag_other (by decide) he)
  have eN : N' = XAf.agents.map (tagA 0) := by
    have f := hA1.agents
    rw [hN', List.filter_append,
      (List.filter_eq_self (p := fun e : Id × Arith => tagged 0 e.1)).2 (fun e he => hNt e he),
      filter_tag_none (by decide), List.append_nil] at f
    exact f
  have eY1 : Y1.agents =
      XAf.agents.map (tagA 0) ++ (sum (m' + 1) n').agents.map (tagA 1) := by
    rw [hN', eN]
  have sA := FA.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
  obtain ⟨k1, k2, hk, sY1, sX1⟩ := hA1.pass sA rfl trivial XAf.agents []
    ((sum (m' + 1) n').agents.map (tagA 1)) (List.append_nil _).symm
  have ek2 := stays_rest_zero sX1
  have pA : Works xsys Y1 ⟨Y1.agents, .idle⟩ Y1
      ⟨(sum (m' + 1) n').agents.map (tagA 1), .idle⟩ 0 (5 * m + 3 * n + 10) := by
    rw [eY1]
    have e : k1 = 5 * m + 3 * n + 10 := by omega
    rw [← e]
    exact sY1.works
  obtain ⟨XBf, Y2, wB, FB, hB2, mvB⟩ := hB1.rounds_all (restB.map (tagA 1))
  have wB' : Works xsys Y1 ⟨(sum (m' + 1) n').agents.map (tagA 1), .idle⟩ Y2
      ⟨Y2.agents, .idle⟩ (m' + 2) (17 * m' + 25) := by
    rw [hBa]
    exact wB
  have hA2 : Looks 0 XAf Y2 := mvB.other 0 _ (by decide) hA1
  have tg1 : ∀ e, e ∈ Y1.agents → tagged 0 e.1 = true ∨ tagged 1 e.1 = true := by
    intro e he
    rw [eY1] at he
    rcases List.mem_append.1 he with he | he
    · exact .inl (mem_tag_self he)
    · exact .inr (mem_tag_self he)
  have tg2 := mvB.tags (fun i => tagged 0 i = true ∨ tagged 1 i = true)
    (fun i => .inr (tagged_self 1 i)) tg1
  have sB := FB.pass_stays (snd_sum (m' + 1) n') (sum_fresh (m' + 1) n')
  have pF := pass_two hA2 hB2 Y2.agents XAf.agents XBf.agents _ _ tg2 hA2.agents hB2.agents
    sA sB
  have w := ((wA'.trans pA).trans wB').trans pF.works
  have e : 17 * m + 25 + (5 * m + 3 * n + 10) + (17 * m' + 25) +
      (5 * m + 3 * n + 10 + (5 * m' + 3 * n' + 10)) = twoSolo (m + 1) n (m' + 1) n' := by
    unfold twoSolo
    rw [soloWork_succ, soloWork_succ]
    omega
  have ec : m + 2 + 0 + (m' + 2) + 0 = m + m' + 4 := by omega
  rw [e, ec] at w
  exact ⟨Y2, XAf, XBf, w, FA, hA2, FB, hB2⟩

/-- **One thread on two additions leaves both sums.** -/
theorem two_sums_solo_num (m n m' n' : Nat) : ∃ Yf,
    Works xsys (twoSums (m + 1) n (m' + 1) n')
      ⟨(twoSums (m + 1) n (m' + 1) n').agents, .idle⟩ Yf ⟨[], .idle⟩ (m + m' + 4)
      (twoSolo (m + 1) n (m' + 1) n') ∧
    IsNum Yf.toNet ([0, 0], 0) (m + 1 + n) ∧ IsNum Yf.toNet ([0, 1], 0) (m' + 1 + n') := by
  obtain ⟨Yf, XAf, XBf, w, FA, hA, FB, hB⟩ := two_sums_solo_final m n m' n'
  obtain ⟨XA, FA', fA, numA⟩ := solo_final_num m n
  obtain ⟨XB, FB', fB, numB⟩ := solo_final_num m' n'
  have hfY : Yf.free = (sum (m + 1) n).free.map (tagPort 0) ++
      (sum (m' + 1) n').free.map (tagPort 1) := works_free w
  have W0 : Within 0 XA Yf := hA.within (FA'.agents.trans FA.agents.symm)
    (fun e => (FA'.wires e).trans (FA.wires e).symm) (fun p => by
      rw [hfY, fA]
      exact free_tag0 _ _ p)
  have W1 : Within 1 XB Yf := hB.within (FB'.agents.trans FB.agents.symm)
    (fun e => (FB'.wires e).trans (FB.wires e).symm) (fun p => by
      rw [hfY, fB]
      exact free_tag1 _ _ p)
  exact ⟨Yf, w, W0.isNum numA, W1.isNum numB⟩

/-- **Two additions side by side come out right, whatever the threads
do.**  With any number of threads and any schedule, a memory at rest has
the numeral `m + n` on the free port of the first net and the numeral
`m' + n'` on the free port of the second. -/
theorem two_sums_rest_num (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true) :
    IsNum ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.toNet
        ([0, 0], 0) (m + 1 + n) ∧
      IsNum ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.toNet
        ([0, 1], 0) (m' + 1 + n') := by
  obtain ⟨Yf, w, hA, hB⟩ := two_sums_solo_num m n m' n'
  have t := w.trace.1
  have h1 : ((XMach.init (twoSums (m + 1) n (m' + 1) n') 1).trace xsys (fun _ => 0)
      (twoSolo (m + 1) n (m' + 1) n')).1.resting = true := by
    rw [XMach.init_one, t]
    rfl
  have e := rest_mem_eq (two_sums_wf (m + 1) n (m' + 1) n') hnt (Nat.zero_lt_one) σ
    (fun _ => 0) hr h1
  rw [XMach.init_one, t] at e
  rw [e]
  exact ⟨hA, hB⟩

/-- **Two additions side by side by threads under a fair schedule.**  With
any number of threads and any unending schedule in which every thread
keeps being scheduled, from some action on every thread is at rest,
`m + m' + 4` claims have been made, and the memory has the numeral
`m + n` on the free port of the first net and `m' + n'` on that of the
second. -/
theorem two_sums_fair (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).2 = m + m' + 4 ∧
      IsNum ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.toNet
        ([0, 0], 0) (m + 1 + n) ∧
      IsNum ((XMach.init (twoSums (m + 1) n (m' + 1) n') nt).trace xsys σ i).1.mem.toNet
        ([0, 1], 0) (m' + 1 + n') := by
  obtain ⟨Yf, w⟩ := two_sums_solo_count m n m' n'
  have t := w.trace.1
  have hX := two_sums_wf (m + 1) n (m' + 1) n'
  have L := XMach.trace_live (fun _ => 0)
    (XMach.init_live (xs := xsys) hX (Nat.zero_lt_one)) (twoSolo (m + 1) n (m' + 1) n')
  have r := XMach.trace_run xsys (fun _ => 0) (XMach.init (twoSums (m + 1) n (m' + 1) n') 1)
    (twoSolo (m + 1) n (m' + 1) n')
  rw [XMach.init_toMach] at r
  have h1 : ((XMach.init (twoSums (m + 1) n (m' + 1) n') 1).trace xsys (fun _ => 0)
      (twoSolo (m + 1) n (m' + 1) n')).1.resting = true := by
    rw [XMach.init_one, t]
    rfl
  obtain ⟨q, hn⟩ := L.rest h1
  have hs := (MRun.final hX r q hn).1
  obtain ⟨i₀, h⟩ := XMach.fair_complete hX hnt hs hn σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, -, -⟩ := h i hi
  obtain ⟨a, b⟩ := two_sums_rest_num m n m' n' hnt σ hr
  exact ⟨hr, two_sums_claims m n m' n' hnt σ hr, a, b⟩

/-- `6 + 32` twice, with any number of threads and any schedule: a memory
at rest has `38` on each of the two free ports. -/
theorem _root_.INet.Checks.Arith.AtRest.c1 {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums 6 32 6 32) nt).trace xsys σ i).1.resting = true) :
    IsNum ((XMach.init (twoSums 6 32 6 32) nt).trace xsys σ i).1.mem.toNet ([0, 0], 0) 38 ∧
      IsNum ((XMach.init (twoSums 6 32 6 32) nt).trace xsys σ i).1.mem.toNet ([0, 1], 0) 38 :=
  two_sums_rest_num 5 32 5 32 hnt σ hr

theorem tagSt_idle {c : Nat} {st : TState Arith} (h : tagSt c st = .idle) : st = .idle := by
  cases st with
  | idle => rfl
  | look a α => cases h
  | seek a α p q => cases h
  | ready a b α β => cases h
  | half a b α β => cases h
  | write as ls => cases h

theorem tagTh_ne_rest {c : Nat} {r : List (Id × Arith)} {T : XThread Arith}
    (h : T ≠ ⟨[], .idle⟩) : tagTh c r T ≠ ⟨[], .idle⟩ := fun e => by
  obtain ⟨todo, st⟩ := T
  have e1 : todo.map (tagA c) ++ r = [] := congrArg XThread.todo e
  have e2 : tagSt c st = .idle := congrArg XThread.st e
  have h1 : todo = [] := List.map_eq_nil_iff.1 (List.append_eq_nil_iff.1 e1).1
  have h2 := tagSt_idle e2
  exact h (by rw [h1, h2])

/-- **The run of one thread on a net that comes first in a larger memory
is its run on the net alone, claim for claim.** -/
theorem Inside.works {c : Nat} {Fr : List (Id × Arith)} {X X' : XNet Arith}
    {T T' : XThread Arith} {cl k : Nat} (w : Works xsys X T X' T' cl k) :
    ∀ {Y : XNet Arith} (r : List (Id × Arith)), Inside c Fr X Y →
      ∃ Y' r', Works xsys Y (tagTh c r T) Y' (tagTh c r' T') cl k ∧ Inside c Fr X' Y' ∧
        Moves c Y Y' ∧ (r' = r ∨ r' = Fr) := by
  induction w with
  | refl X T =>
    intro Y r h
    exact ⟨Y, r, .refl _ _, h, Moves.refl c Y, .inl rfl⟩
  | @step X X₁ X' T T₁ T' c₁ c₂ k hT hact _ ih =>
    intro Y r h
    obtain ⟨Y1, r1, aY, h1, mv1, hr1⟩ := h.act r T hT
    rw [hact] at aY h1
    obtain ⟨Y', r', w', h', mv', hr'⟩ := ih r1 h1
    refine ⟨Y', r', .step (tagTh_ne_rest hT) aY w', h', mv1.trans mv', ?_⟩
    rcases hr' with e | e
    · rcases hr1 with e1 | e1
      · exact .inl (e.trans e1)
      · exact .inr (e.trans e1)
    · exact .inr e

/-- A run of one thread that ends at rest, as a run of the machine. -/
theorem rest_of_works {X Xf : XNet Arith} {c k : Nat}
    (w : Works xsys X ⟨X.agents, .idle⟩ Xf ⟨[], .idle⟩ c k) :
    ((XMach.init X 1).trace xsys (fun _ => 0) k).1.resting = true ∧
      ((XMach.init X 1).trace xsys (fun _ => 0) k).1.mem = Xf := by
  have t := w.trace.1
  rw [XMach.init_one, t]
  exact ⟨rfl, rfl⟩

/-- **A run of one thread that ends idle is a reduction of the net**, as
long as its number of claims. -/
theorem works_steps {X X' : XNet Arith} {l : List (Id × Arith)} {c k : Nat}
    (hX : X.toNet.WF ar) (w : Works xsys X ⟨X.agents, .idle⟩ X' ⟨l, .idle⟩ c k) :
    Steps (Step system) c X.toNet X'.toNet := by
  have t := w.trace.1
  have r := XMach.trace_run xsys (fun _ => 0) (XMach.init X 1) k
  rw [XMach.init_toMach, XMach.init_one, t] at r
  have hq : (⟨X', [⟨l, .idle⟩]⟩ : XMach Arith).toMach.Quiet := by
    intro u
    show threadOf [(⟨l, .idle⟩ : XThread Arith)] u = .idle
    unfold threadOf
    split
    · rename_i T hT
      have hm : T ∈ [(⟨l, .idle⟩ : XThread Arith)] := List.mem_of_getElem? hT
      rw [List.mem_singleton.1 hm]
    · rfl
  exact MRun.quiet hX r hq

/-- A run of one thread that ends at rest leaves a normal form. -/
theorem works_normal {X X' : XNet Arith} {c k : Nat} (hX : X.toNet.WF ar)
    (w : Works xsys X ⟨X.agents, .idle⟩ X' ⟨[], .idle⟩ c k) :
    Normal (Step system) X'.toNet := by
  obtain ⟨h1, e1⟩ := rest_of_works w
  have L := XMach.trace_live (fun _ => 0) (XMach.init_live (xs := xsys) hX Nat.zero_lt_one) k
  have hn := (L.rest h1).2
  rw [e1] at hn
  exact hn

/-- A memory with the cells of the second net moved before those of the
first: the same net, listed in another order. -/
def swapped (A' B Y : XNet Arith) : XNet Arith :=
  ⟨B.agents.map (tagA 1) ++ A'.agents.map (tagA 0), Y.free, Y.wires⟩

theorem swapped_toNet {A' B Y : XNet Arith}
    (h : Y.agents = A'.agents.map (tagA 0) ++ B.agents.map (tagA 1)) :
    (swapped A' B Y).toNet = Y.toNet := by
  apply Net.ext'
  · intro i γ
    show (i, γ) ∈ B.agents.map (tagA 1) ++ A'.agents.map (tagA 0) ↔ (i, γ) ∈ Y.agents
    rw [h, List.mem_append, List.mem_append]
    exact Or.comm
  · exact fun _ _ => Iff.rfl
  · exact fun _ => Iff.rfl

theorem swapped_inside {A' B Y : XNet Arith} (hB : Looks 1 B Y) :
    Inside 1 (A'.agents.map (tagA 0)) B (swapped A' B Y) :=
  ⟨⟨by
      show (B.agents.map (tagA 1) ++ A'.agents.map (tagA 0)).filter (fun e => tagged 1 e.1) =
        B.agents.map (tagA 1)
      rw [List.filter_append, filter_tag_self, filter_tag_none (by decide), List.append_nil],
    hB.wires⟩, rfl, fun _ he => mem_tag_other (by decide) he⟩

theorem swapped_looks {A' B Y : XNet Arith} (hA : Looks 0 A' Y) :
    Looks 0 A' (swapped A' B Y) :=
  ⟨by
    show (B.agents.map (tagA 1) ++ A'.agents.map (tagA 0)).filter (fun e => tagged 0 e.1) =
      A'.agents.map (tagA 0)
    rw [List.filter_append, filter_tag_none (by decide), filter_tag_self, List.nil_append],
  hA.wires⟩

/-- **Two nets side by side reduce as each does alone.**  Let one thread
alone bring the net `A` to rest at `A'`, and `B` at `B'`, and let a new
pass over `A'` only read.  Then the two nets side by side reduce, in as
many steps as the two runs have claims, to a normal form that holds `A'`
under the tag `0` and `B'` under the tag `1`. -/
theorem beside_normal {A B A' B' : XNet Arith} {cA kA cB kB kp : Nat}
    (hY : (beside (tagNet 0 A) (tagNet 1 B)).toNet.WF ar)
    (wA : Works xsys A ⟨A.agents, .idle⟩ A' ⟨[], .idle⟩ cA kA)
    (pA : Stays xsys A' ⟨A'.agents, .idle⟩ ⟨[], .idle⟩ kp)
    (wB : Works xsys B ⟨B.agents, .idle⟩ B' ⟨[], .idle⟩ cB kB) :
    ∃ Z : XNet Arith,
      Steps (Step system) (cA + cB) (beside (tagNet 0 A) (tagNet 1 B)).toNet Z.toNet ∧
        Normal (Step system) Z.toNet ∧ Within 0 A' Z ∧ Within 1 B' Z := by
  -- the thread works on the first net
  have hIn0 : Inside 0 (B.agents.map (tagA 1)) A (beside (tagNet 0 A) (tagNet 1 B)) :=
    ⟨looks_left A B, rfl, fun _ he => mem_tag_other (by decide) he⟩
  obtain ⟨Y1, r1, W1, hIn1, mv1, hr1⟩ := Inside.works wA (B.agents.map (tagA 1)) hIn0
  have er1 : r1 = B.agents.map (tagA 1) := by
    rcases hr1 with e | e <;> exact e
  subst er1
  have W1' : Works xsys (beside (tagNet 0 A) (tagNet 1 B))
      ⟨(beside (tagNet 0 A) (tagNet 1 B)).agents, .idle⟩ Y1
      ⟨B.agents.map (tagA 1), .idle⟩ cA kA := W1
  have s1 := works_steps hY W1'
  -- the same net with the cells of the second net first
  have hB1 : Looks 1 B Y1 := mv1.other 1 _ (by decide) (looks_right A B)
  have eZ : (swapped A' B Y1).toNet = Y1.toNet := swapped_toNet hIn1.agents
  have hZ : (swapped A' B Y1).toNet.WF ar := by
    rw [eZ]
    exact Steps.wf hY s1
  obtain ⟨Z2, r2, W2, hIn2, mv2, hr2⟩ :=
    Inside.works wB (A'.agents.map (tagA 0)) (swapped_inside (A' := A') hB1)
  have er2 : r2 = A'.agents.map (tagA 0) := by
    rcases hr2 with e | e <;> exact e
  subst er2
  -- the last pass, over what the first run left
  have hA2 : Looks 0 A' Z2 := mv2.other 0 _ (by decide) (swapped_looks hIn1.looks)
  obtain ⟨k1, -, -, sY, -⟩ := hA2.pass pA rfl trivial A'.agents [] [] (List.append_nil _).symm
  have p : Works xsys Z2 ⟨A'.agents.map (tagA 0), .idle⟩ Z2 ⟨[], .idle⟩ 0 k1 := by
    have q := sY.works
    rw [List.append_nil] at q
    exact q
  have W2' : Works xsys (swapped A' B Y1) ⟨(swapped A' B Y1).agents, .idle⟩ Z2 ⟨[], .idle⟩
      (cB + 0) (kB + k1) := Works.trans W2 p
  have s2 := works_steps hZ W2'
  have n2 := works_normal hZ W2'
  rw [eZ] at s2
  have s := s1.trans s2
  -- the free ports
  have f1 : Y1.free = (beside (tagNet 0 A) (tagNet 1 B)).free := works_free W1'
  have f2 : Z2.free = (swapped A' B Y1).free := works_free W2'
  have fY : Z2.free = A.free.map (tagPort 0) ++ B.free.map (tagPort 1) := f2.trans f1
  have fA : A'.free = A.free := works_free wA
  have fB : B'.free = B.free := works_free wB
  refine ⟨Z2, s, n2, hA2.within rfl (fun _ => Iff.rfl) (fun p => ?_),
    hIn2.looks.within rfl (fun _ => Iff.rfl) (fun p => ?_)⟩
  · rw [fY, fA]
    exact free_tag0 _ _ p
  · rw [fY, fB]
    exact free_tag1 _ _ p

/-- **The last pass of `0 + n` only reads.** -/
theorem Final0.pass_stays {n : Nat} {X0 X : XNet Arith} (F : Final0 n X0 X) (S : Snd n X0) :
    Stays xsys X ⟨X.agents, .idle⟩ ⟨[], .idle⟩ (3 * n + 5) := by
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
  have w₂ : Stays xsys X ⟨([n + 3], γ) :: low, .idle⟩ ⟨low, .idle⟩ 5 :=
    Stays.dead (xs := xsys) (e := ([n + 3], γ)) (k := 3) _ h₁ h₂ hd
  have w₃ := Stays.inert_pass (xs := xsys) (X := X) [] low (fun e he => by
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
  rw [e] at w
  rw [hA]
  exact w

/-- **The run of one thread on the net for `0 + n`, and the memory it
leaves.** -/
theorem solo_zero_final (n : Nat) :
    Works xsys (sum 0 n) ⟨(sum 0 n).agents, .idle⟩ (stepZ (sumSnd n) [1] [2]) ⟨[], .idle⟩ 1
      (6 * n + 13) := by
  show Works xsys (sumSnd n) ⟨(sumSnd n).agents, .idle⟩ (stepZ (sumSnd n) [1] [2])
    ⟨[], .idle⟩ 1 (6 * n + 13)
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
  rw [e] at w
  rw [hA]
  exact w.works

/-- **One thread on any addition**: its run to rest, with `m + 1` claims,
and a new pass over the memory it leaves, which only reads. -/
theorem sum_solo_pass (m n : Nat) : ∃ (Xf : XNet Arith) (k kp : Nat),
    Works xsys (sum m n) ⟨(sum m n).agents, .idle⟩ Xf ⟨[], .idle⟩ (m + 1) k ∧
      Stays xsys Xf ⟨Xf.agents, .idle⟩ ⟨[], .idle⟩ kp := by
  cases m with
  | zero =>
    exact ⟨stepZ (sumSnd n) [1] [2], _, _, solo_zero_final n,
      (final0_sumSnd n).pass_stays (snd_sumSnd n)⟩
  | succ m =>
    obtain ⟨Xf, r, F⟩ := solo_rounds m n
    have p := F.pass_stays (snd_sum (m + 1) n) (sum_fresh (m + 1) n)
    have w := r.works.trans p.works
    have e : m + 2 + 0 = m + 1 + 1 := by omega
    rw [e] at w
    exact ⟨Xf, _, _, w, p⟩

/-- The memory one thread leaves at rest on an addition has the numeral
on its free port. -/
theorem works_rest_num {m n : Nat} {Xf : XNet Arith} {c k : Nat}
    (w : Works xsys (sum m n) ⟨(sum m n).agents, .idle⟩ Xf ⟨[], .idle⟩ c k) :
    IsNum Xf.toNet ([0], 0) (m + n) := by
  obtain ⟨h1, e1⟩ := rest_of_works w
  have hnum := sum_rest_num m n Nat.zero_lt_one (fun _ => 0) h1
  rw [e1] at hnum
  exact hnum

/-- **Two additions side by side, as nets, for all arguments.**  The net
reduces in `(m + 1) + (m' + 1)` steps to a normal form with the numeral
`m + n` on the free port of the first net and `m' + n'` on that of the
second. -/
theorem two_sums_normal (m n m' n' : Nat) : ∃ N' : Net Arith,
    Steps (Step system) (m + 1 + (m' + 1)) (twoSums m n m' n').toNet N' ∧
      Normal (Step system) N' ∧ IsNum N' ([0, 0], 0) (m + n) ∧
        IsNum N' ([0, 1], 0) (m' + n') := by
  obtain ⟨XA, kA, kp, wA, pA⟩ := sum_solo_pass m n
  obtain ⟨XB, kB, -, wB, -⟩ := sum_solo_pass m' n'
  obtain ⟨Z, s, hn, W0, W1⟩ := beside_normal (two_sums_wf m n m' n') wA pA wB
  exact ⟨Z.toNet, s, hn, W0.isNum (works_rest_num wA), W1.isNum (works_rest_num wB)⟩

/-- **Two additions side by side come out right, whatever the threads do,
for all arguments.**  With any number of threads and any schedule, a run
that ends at rest has made `(m + 1) + (m' + 1)` claims, and the memory
has the numeral `m + n` on the free port of the first net and `m' + n'`
on that of the second. -/
theorem two_sums_rest (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).2 = m + 1 + (m' + 1) ∧
      IsNum ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet
        ([0, 0], 0) (m + n) ∧
      IsNum ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet
        ([0, 1], 0) (m' + n') := by
  obtain ⟨N', hs, hn', hA, hB⟩ := two_sums_normal m n m' n'
  have hX := two_sums_wf m n m' n'
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (twoSums m n m' n') nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e, ek⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet := e
  rw [← e']
  exact ⟨ek.symm, hA, hB⟩

/-- **Two additions side by side under a fair schedule, for all
arguments.**  With any number of threads and any unending schedule in
which every thread keeps being scheduled, from some action on every
thread is at rest, `(m + 1) + (m' + 1)` claims have been made, and the
memory has the two numerals on the two free ports. -/
theorem two_sums_fair_all (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ σ j = u) :
    ∃ i₀, ∀ i, i₀ ≤ i →
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.resting = true ∧
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).2 = m + 1 + (m' + 1) ∧
      IsNum ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet
        ([0, 0], 0) (m + n) ∧
      IsNum ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet
        ([0, 1], 0) (m' + n') := by
  obtain ⟨N', hs, hn', hA, hB⟩ := two_sums_normal m n m' n'
  obtain ⟨i₀, h⟩ := XMach.fair_complete (xs := xsys) (two_sums_wf m n m' n') hnt hs hn' σ hfair
  refine ⟨i₀, fun i hi => ?_⟩
  obtain ⟨hr, hc, e⟩ := h i hi
  rw [e]
  exact ⟨hr, hc, hA, hB⟩

/-- `0 + 7` beside `3 + 0`, with any number of threads and any schedule:
a memory at rest has `7` on the first free port and `3` on the second,
after five claims. -/
theorem _root_.INet.Checks.Arith.AtRest.c2 {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.resting = true) :
    ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).2 = 5 ∧
      IsNum ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.mem.toNet ([0, 0], 0) 7 ∧
      IsNum ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.mem.toNet ([0, 1], 0) 3 :=
  two_sums_rest 0 7 3 0 hnt σ hr

/-- The successors of a second argument are agents of the addition. -/
theorem sum_snd_alive (M n : Nat) {j : Nat} (h4 : 4 ≤ j) (h3 : j ≤ n + 3) :
    assoc [j] (sum M n).agents = some .succ := by
  have hm := sndL_mem n (j - 4) (by omega)
  rw [show j - 4 + 4 = j by omega] at hm
  have hin : (([j], Arith.succ) : Id × Arith) ∈ (sum M n).agents := by
    rw [sum_agents]
    exact List.mem_append_right _ (List.mem_append_left _ hm)
  exact assoc_of_nodup (sum_nodup M n) hin

/-- And each has a segment at its principal port. -/
theorem sum_snd_look (M n : Nat) {j : Nat} (h4 : 4 ≤ j) (h3 : j ≤ n + 3) :
    ∃ q, assoc (([j], 0) : Port) (sum M n).wires = some q := by
  have S := snd_sum M n
  by_cases hj : j = n + 3
  · subst hj
    exact ⟨_, assoc_eq_of_unique ((S.top _).2 rfl) (fun q' hq => (S.top q').1 hq)⟩
  · exact ⟨_, assoc_eq_of_unique ((S.up j (by omega) (by omega) _).2 rfl)
      (fun q' hq => (S.up j (by omega) (by omega) q').1 hq)⟩

/-- **Two additions side by side are a memory in order, for all
arguments.** -/
theorem two_sums_memOk_all (m n m' n' : Nat) :
    MemOk (sideN n n') (n + n') (twoSums m n m' n') where
  kinds := fun e he => by
    have he' : e ∈ (sum m n).agents.map (tagA 0) ++ (sum m' n').agents.map (tagA 1) := he
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_kind m n 0 x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_kind m' n' 1 x hx
  wires := fun e he => by
    have he' : e ∈ (sum m n).wires.map (tagL 0) ++ (sum m' n').wires.map (tagL 1) := he
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_color (sideN n n') 0 n rfl m x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact sum_color (sideN n n') 1 n' rfl m' x hx
  alive := fun s hs => by
    obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape _ hs
    have h3' : j ≤ (if c = 0 then n else if c = 1 then n' else 0) + 3 := h3
    by_cases h0 : c = 0
    · subst h0
      rw [ite_pos' rfl] at h3'
      exact ((looks_left (sum m n) (sum m' n')).agent [j]).trans (sum_snd_alive m n h4 h3')
    · rw [ite_neg' h0] at h3'
      by_cases h1 : c = 1
      · subst h1
        rw [ite_pos' rfl] at h3'
        exact ((looks_right (sum m n) (sum m' n')).agent [j]).trans
          (sum_snd_alive m' n' h4 h3')
      · rw [ite_neg' h1] at h3'
        omega
  look := fun s hs => by
    obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape _ hs
    have h3' : j ≤ (if c = 0 then n else if c = 1 then n' else 0) + 3 := h3
    by_cases h0 : c = 0
    · subst h0
      rw [ite_pos' rfl] at h3'
      obtain ⟨q, hq⟩ := sum_snd_look m n h4 h3'
      exact ⟨tagPort 0 q, ((looks_left (sum m n) (sum m' n')).wire ([j], 0)).trans
        (congrArg (Option.map (tagPort 0)) hq)⟩
    · rw [ite_neg' h0] at h3'
      by_cases h1 : c = 1
      · subst h1
        rw [ite_pos' rfl] at h3'
        obtain ⟨q, hq⟩ := sum_snd_look m' n' h4 h3'
        exact ⟨tagPort 1 q, ((looks_right (sum m n) (sum m' n')).wire ([j], 0)).trans
          (congrArg (Option.map (tagPort 1)) hq)⟩
      · rw [ite_neg' h1] at h3'
        omega
  count := by
    show n + n' ≤ sndCnt (sideN n n') ((sum m n).agents.map (tagA 0) ++
      (sum m' n').agents.map (tagA 1))
    rw [sndCnt_append]
    have h1 := sum_sndCnt (sideN n n') 0 n rfl m
    have h2 := sum_sndCnt (sideN n n') 1 n' rfl m'
    omega

/-- **At rest every cell of a first argument has been used**, for all
arguments, with any number of threads and any schedule. -/
theorem two_sums_first_all (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.resting = true) :
    fcnt (sideN n n')
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents = 0 := by
  have F := trace_first σ (init_ok (two_sums_memOk_all m n m' n') nt) i
  have z := total_init (heldFT (sideN n n')) (fun _ => rfl) (twoSums m n m' n') nt
  have e0 : (XMach.init (twoSums m n m' n') nt).mem =
      twoSums m n m' n' := rfl
  rw [z, e0, (two_sums_rest m n m' n' hnt σ hr).1] at F
  have f : fcnt (sideN n n') (twoSums m n m' n').agents ≤ m + 1 + (m' + 1) := by
    show fcnt (sideN n n') ((sum m n).agents.map (tagA 0) ++
      (sum m' n').agents.map (tagA 1)) ≤ m + 1 + (m' + 1)
    rw [fcnt_append]
    have a := sum_fcnt_le (sideN n n') 0 n rfl m
    have b := sum_fcnt_le (sideN n n') 1 n' rfl m'
    omega
  omega

/-- **At rest no adder is left**, for all arguments, with any number of
threads and any schedule. -/
theorem two_sums_adders_all (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat}
    (hr : ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.resting = true) :
    adders ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents = 0 := by
  have Z := trace_zf (two_sums_wf m n m' n') (two_sums_nodup m n m' n')
    (two_sums_memOk_all m n m' n') hnt σ i
  have hf := two_sums_first_all m n m' n' hnt σ hr
  have hz := zcnt_le_fcnt (sideN n n')
    ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents
  have z1 : total heldAddT
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.ths = 0 :=
    total_rest heldAddT rfl _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z2 : total heldZT
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.ths = 0 :=
    total_rest heldZT rfl _ fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have a := adders_two_sums m n m' n'
  have b := zcnt_two_sums_ge m n m' n'
  omega

/-- **Two additions side by side come out whole, whatever the threads
do, for all arguments.**  With any number of threads and any schedule, a memory at rest
holds no adder; it holds the `m + n` and `m' + n'` successors of the two
results, those of the second addition in the second net; it holds two
zeros, one in each net; and it holds nothing else. -/
theorem two_sums_census (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat}
    (hr : ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.resting = true) :
    adders ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents = 0 ∧
      succs ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents =
        m + n + (m' + n') ∧
      succs1 ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents =
        m' + n' ∧
      zeros ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents = 2 ∧
      zeros1 ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents = 1 ∧
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents.length =
        m + n + (m' + n') + 2 := by
  have A := two_sums_adders_all m n m' n' hnt σ hr
  obtain ⟨S1, S⟩ := two_sums_succs_each m n m' n' hnt σ i
  have C0 := trace_census (fun _ => true) (two_sums_wf m n m' n')
    (two_sums_nodup m n m' n') (two_sums_memT m n m' n') hnt σ i
  have C1 := trace_census (fun b => b) (two_sums_wf m n m' n')
    (two_sums_nodup m n m' n') (two_sums_memT m n m' n') hnt σ i
  have hrest : ∀ T, T ∈ ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.ths →
      T = ⟨[], .idle⟩ := fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z1 := total_rest (heldWT (fun _ => true) isZero) rfl _ hrest
  have z2 := total_rest (heldWT (fun _ => true) isAdd) rfl _ hrest
  have z3 := total_rest (heldWT (fun b => b) isZero) rfl _ hrest
  have z4 := total_rest (heldWT (fun b => b) isAdd) rfl _ hrest
  have z5 := total_rest held1T rfl _ hrest
  have z6 := total_rest held rfl _ hrest
  have a0 := wIn_adders
    ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents
  have a1 := wIn_le (fun b => b) isAdd
    ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents
  have x0 := zeros_two_sums m n m' n'
  have x1 : wIn (fun _ => true) isAdd (twoSums m n m' n').agents = 2 :=
    (wIn_adders _).trans (adders_two_sums m n m' n')
  have x2 := zeros1_two_sums m n m' n'
  have x3 := adders1_two_sums m n m' n'
  have L := length_census
    ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents
  have Z0 : wIn (fun _ => true) isZero
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents = 2 := by
    omega
  have Z1 : wIn (fun b => b) isZero
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents = 1 := by
    omega
  exact ⟨A, by omega, by omega, Z0, Z1, by omega⟩

/-- `0 + 7` beside `3 + 0`, with any number of threads and any schedule:
a memory at rest holds ten successors, three of them in the second net,
and two zeros, twelve agents in all. -/
theorem _root_.INet.Checks.Arith.AtRest.c3 {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.resting = true) :
    succs ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.mem.agents = 10 ∧
      succs1 ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.mem.agents = 3 ∧
      ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.mem.agents.length = 12 := by
  obtain ⟨-, h1, h2, -, -, h3⟩ := two_sums_census 0 7 3 0 hnt σ hr
  exact ⟨h1, h2, h3⟩

/-- **A list without repeats, inside a list that is no longer, holds all
the members of that list.** -/
theorem nodup_cover {α : Type} [DecidableEq α] : ∀ (L M : List α), L.Nodup →
    (∀ a, a ∈ L → a ∈ M) → M.length ≤ L.length → ∀ b, b ∈ M → b ∈ L
  | [], M, _, _, hlen, b, hb => by
    cases M with
    | nil => cases hb
    | cons x M' => exact absurd hlen (Nat.not_succ_le_zero _)
  | a :: L, M, hnd, hsub, hlen, b, hb => by
    obtain ⟨ha, hL⟩ := List.nodup_cons.1 hnd
    have haM := hsub a List.mem_cons_self
    by_cases e : b = a
    · rw [e]
      exact List.mem_cons_self
    · have hsub' : ∀ c, c ∈ L → c ∈ M.erase a := fun c hc => by
        have hca : c ≠ a := fun h => by
          rw [h] at hc
          exact ha hc
        exact (List.mem_erase_of_ne hca).2 (hsub c (List.mem_cons_of_mem _ hc))
      have hlen' : (M.erase a).length ≤ L.length := by
        rw [List.length_erase_of_mem haM]
        have h : M.length ≤ L.length + 1 := hlen
        omega
      exact List.mem_cons_of_mem _
        (nodup_cover L (M.erase a) hL hsub' hlen' b ((List.mem_erase_of_ne e).2 hb))

/-- **The agents of a numeral**, from its head down: successors, each
with the next agent on its auxiliary port, and a zero last. -/
inductive NumList (N : Net Arith) : Id → List Id → Prop
  | last {i : Id} : N.agent i Arith.zero → NumList N i [i]
  | next {i i' : Id} {l : List Id} : N.agent i Arith.succ → N.Paired ar (i, 1) (i', 0) →
      NumList N i' l → NumList N i (i :: l)

/-- The numeral `k` has `k + 1` agents. -/
theorem Num.list {N : Net Arith} : ∀ {k : Nat} {i : Id}, Num N i k →
    ∃ l, NumList N i l ∧ l.length = k + 1
  | 0, _, h => ⟨_, .last h, rfl⟩
  | _ + 1, _, ⟨hs, _, hp, hn⟩ => by
    obtain ⟨l, hl, e⟩ := Num.list hn
    exact ⟨_ :: l, .next hs hp hl, by rw [List.length_cons, e]⟩

/-- A list of `k + 1` agents of a numeral is the numeral `k`. -/
theorem NumList.num {N : Net Arith} {i : Id} {l : List Id} (h : NumList N i l) :
    ∃ k, l.length = k + 1 ∧ Num N i k := by
  induction h with
  | last hz => exact ⟨0, rfl, hz⟩
  | next hs hp _ ih =>
    obtain ⟨k, e, hn⟩ := ih
    exact ⟨k + 1, by rw [List.length_cons, e], ⟨hs, _, hp, hn⟩⟩

theorem NumList.agent {N : Net Arith} {i : Id} {l : List Id} (h : NumList N i l) :
    ∀ a, a ∈ l → ∃ γ, N.agent a γ := by
  induction h with
  | last hz =>
    intro a ha
    rw [List.mem_singleton.1 ha]
    exact ⟨_, hz⟩
  | next hs _ _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, hs⟩
    · exact ih a ha'

/-- A numeral starts at each of its agents. -/
theorem NumList.sub {N : Net Arith} {i : Id} {l : List Id} (h : NumList N i l) :
    ∀ a, a ∈ l → ∃ l', NumList N a l' ∧ l'.length ≤ l.length := by
  induction h with
  | last hz =>
    intro a ha
    rw [List.mem_singleton.1 ha]
    exact ⟨_, .last hz, Nat.le_refl _⟩
  | next hs hp hl ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, .next hs hp hl, Nat.le_refl _⟩
    · obtain ⟨l', h', hle⟩ := ih a ha'
      exact ⟨l', h', Nat.le_succ_of_le hle⟩

/-- The agents of a numeral are fixed by its head. -/
theorem NumList.det {N : Net Arith} (hN : N.WF ar) {i : Id} {l₁ : List Id}
    (h₁ : NumList N i l₁) : ∀ {l₂ : List Id}, NumList N i l₂ → l₁ = l₂ := by
  induction h₁ with
  | last hz =>
    intro l₂ h₂
    cases h₂ with
    | last _ => rfl
    | next hs _ _ => exact absurd (hN.agent_fun hz hs) (by decide)
  | @next i i' l hs hp _ ih =>
    intro l₂ h₂
    cases h₂ with
    | last hz => exact absurd (hN.agent_fun hz hs) (by decide)
    | @next _ i'' l'' _ hp' hl' =>
      have e : i' = i'' :=
        congrArg Prod.fst (Net.Conn.det hN hp.1 hp.2.1 hp'.2.1 hp.2.2 hp'.2.2)
      subst e
      rw [ih hl']

/-- **No agent is twice in a numeral.** -/
theorem NumList.nodup {N : Net Arith} (hN : N.WF ar) {i : Id} {l : List Id}
    (h : NumList N i l) : l.Nodup := by
  induction h with
  | last _ => exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | @next i i' l hs hp hl ih =>
    refine List.nodup_cons.2 ⟨fun hi => ?_, ih⟩
    obtain ⟨l', h', hle⟩ := hl.sub i hi
    have e := (NumList.next hs hp hl).det hN h'
    rw [← e] at hle
    exact Nat.not_succ_le_self _ hle

/-- A wire of a memory whose segments stay in one net stays in one net. -/
theorem walk_tag {N : Net Arith} (hT : ∀ p q, N.link p q → tagged 1 p.1 = tagged 1 q.1)
    {u v x y : Port} (w : Walk N.link (N.End ar) u v x y) : tagged 1 u.1 = tagged 1 y.1 := by
  induction w with
  | single hl => exact hT _ _ hl
  | cons hl _ _ _ ih => exact (hT _ _ hl).trans ih

theorem paired_tag {N : Net Arith} (hT : ∀ p q, N.link p q → tagged 1 p.1 = tagged 1 q.1)
    {p q : Port} (h : N.Paired ar p q) : tagged 1 p.1 = tagged 1 q.1 := by
  obtain ⟨-, -, v, x, w⟩ := h
  exact walk_tag hT w

/-- The agents of a numeral are in the net of its head. -/
theorem NumList.tag {N : Net Arith} (hT : ∀ p q, N.link p q → tagged 1 p.1 = tagged 1 q.1)
    {i : Id} {l : List Id} (h : NumList N i l) : ∀ a, a ∈ l → tagged 1 a = tagged 1 i := by
  induction h with
  | last _ =>
    intro a ha
    rw [List.mem_singleton.1 ha]
  | next _ hp _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha'
    · rfl
    · exact (ih a ha').trans (paired_tag hT hp).symm

/-- **A memory with two numerals and no more agents than they have is
those two numerals.**  Let no segment join the two nets, let the two
free ports carry the numerals `k₀` and `k₁`, and let the memory hold at
most `(k₀ + 1) + (k₁ + 1)` agents.  Then every agent of the memory is one
of the `k₀ + 1` agents of the first numeral, which are in the first net,
or one of the `k₁ + 1` agents of the second, which are in the second. -/
theorem numerals_cover {M : XNet Arith} {k₀ k₁ : Nat} (hN : M.toNet.WF ar)
    (hT : ∀ e, e ∈ M.wires → tagged 1 e.1.1 = tagged 1 e.2.1)
    (h0 : IsNum M.toNet ([0, 0], 0) k₀) (h1 : IsNum M.toNet ([0, 1], 0) k₁)
    (hlen : M.agents.length ≤ k₀ + 1 + (k₁ + 1)) :
    ∃ (i₀ i₁ : Id) (l₀ l₁ : List Id),
      M.toNet.Paired ar ([0, 0], 0) (i₀, 0) ∧ NumList M.toNet i₀ l₀ ∧ l₀.length = k₀ + 1 ∧
      M.toNet.Paired ar ([0, 1], 0) (i₁, 0) ∧ NumList M.toNet i₁ l₁ ∧ l₁.length = k₁ + 1 ∧
      (∀ a, a ∈ l₀ → tagged 1 a = false) ∧ (∀ a, a ∈ l₁ → tagged 1 a = true) ∧
      ∀ e, e ∈ M.agents → e.1 ∈ l₀ ∨ e.1 ∈ l₁ := by
  have hT' : ∀ p q, M.toNet.link p q → tagged 1 p.1 = tagged 1 q.1 := fun p q h => hT (p, q) h
  obtain ⟨i₀, p0, n0⟩ := h0
  obtain ⟨i₁, p1, n1⟩ := h1
  obtain ⟨l₀, L0, e0⟩ := Num.list n0
  obtain ⟨l₁, L1, e1⟩ := Num.list n1
  have z0 : tagged 1 ([0, 0] : Id) = false := rfl
  have z1 : tagged 1 ([0, 1] : Id) = true := rfl
  have t0 : ∀ a, a ∈ l₀ → tagged 1 a = false := fun a ha =>
    ((L0.tag hT' a ha).trans (paired_tag hT' p0).symm).trans z0
  have t1 : ∀ a, a ∈ l₁ → tagged 1 a = true := fun a ha =>
    ((L1.tag hT' a ha).trans (paired_tag hT' p1).symm).trans z1
  have hnd : (l₀ ++ l₁).Nodup :=
    List.nodup_append.2 ⟨L0.nodup hN, L1.nodup hN, fun a ha b hb e => by
      have h := t0 a ha
      rw [e, t1 b hb] at h
      cases h⟩
  have hsub : ∀ a, a ∈ l₀ ++ l₁ → a ∈ M.agents.map Prod.fst := fun a ha => by
    have hag : ∃ γ, M.toNet.agent a γ := by
      rcases List.mem_append.1 ha with h | h
      · exact L0.agent a h
      · exact L1.agent a h
    obtain ⟨γ, hγ⟩ := hag
    exact List.mem_map.2 ⟨(a, γ), hγ, rfl⟩
  have hlen' : (M.agents.map Prod.fst).length ≤ (l₀ ++ l₁).length := by
    rw [List.length_map, List.length_append, e0, e1]
    exact hlen
  have cov := nodup_cover (l₀ ++ l₁) (M.agents.map Prod.fst) hnd hsub hlen'
  refine ⟨i₀, i₁, l₀, l₁, p0, L0, e0, p1, L1, e1, t0, t1, fun e he => ?_⟩
  exact List.mem_append.1 (cov e.1 (List.mem_map_of_mem he))

/-- **Two additions side by side at rest are their two sums and nothing
else**, for all arguments, with any number of threads and any schedule.
The free port of the first net is wired to a numeral of `m + n + 1`
agents, all in the first net; the free port of the second to a numeral
of `m' + n' + 1` agents, all in the second; and every agent in memory is
one of them. -/
theorem two_sums_exact (m n m' n' : Nat) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.resting = true) :
    ∃ (i₀ i₁ : Id) (l₀ l₁ : List Id),
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet.Paired ar
        ([0, 0], 0) (i₀, 0) ∧
      NumList ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet i₀ l₀ ∧
      l₀.length = m + n + 1 ∧
      ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet.Paired ar
        ([0, 1], 0) (i₁, 0) ∧
      NumList ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet i₁ l₁ ∧
      l₁.length = m' + n' + 1 ∧
      (∀ a, a ∈ l₀ → tagged 1 a = false) ∧ (∀ a, a ∈ l₁ → tagged 1 a = true) ∧
      ∀ e, e ∈ ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.agents →
        e.1 ∈ l₀ ∨ e.1 ∈ l₁ := by
  obtain ⟨-, h0, h1⟩ := two_sums_rest m n m' n' hnt σ hr
  obtain ⟨-, -, -, -, -, hlen⟩ := two_sums_census m n m' n' hnt σ hr
  have hX := two_sums_wf m n m' n'
  have L := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, -⟩ := L.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (twoSums m n m' n') nt) i
  rw [XMach.init_toMach] at r
  have hN : ((XMach.init (twoSums m n m' n') nt).trace xsys σ i).1.mem.toNet.WF ar :=
    Steps.wf hX (MRun.quiet hX r q)
  exact numerals_cover hN (two_sums_apart m n m' n' nt σ i) h0 h1 (by omega)

/-- `0 + 7` beside `3 + 0`, with any number of threads and any schedule:
at rest every agent in memory is one of the eight of the first numeral
or one of the four of the second. -/
theorem _root_.INet.Checks.Arith.AtRest.c4 {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.resting = true) :
    ∃ l₀ l₁ : List Id, l₀.length = 8 ∧ l₁.length = 4 ∧
      ∀ e, e ∈ ((XMach.init (twoSums 0 7 3 0) nt).trace xsys σ i).1.mem.agents →
        e.1 ∈ l₀ ∨ e.1 ∈ l₁ := by
  obtain ⟨-, -, l₀, l₁, -, -, e0, -, -, e1, -, -, h⟩ := two_sums_exact 0 7 3 0 hnt σ hr
  exact ⟨l₀, l₁, e0, e1, h⟩

end Arith

end INet
