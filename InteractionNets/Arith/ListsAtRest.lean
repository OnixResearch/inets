import InteractionNets.Arith.Lists

/-! ### Any number of additions at rest: the count of the agents, and nothing else -/

namespace INet

namespace Arith

/-- A name has one tag. -/
theorem tagged_unique {c d : Nat} : ∀ {a : Id}, tagged c a = true → tagged d a = true → c = d
  | [], h, _ => by cases h
  | [x], h, h' => by
    have e1 : x = c := beq_iff_eq.1 h
    have e2 : x = d := beq_iff_eq.1 h'
    rw [← e1, ← e2]
  | _ :: y :: l, h, h' => tagged_unique (a := y :: l) h h'

/-- In a memory that holds nets side by side, a segment that starts in
one of the nets ends in it. -/
theorem Holds.link_tag {L : List (Nat × XNet Arith)} {M : XNet Arith} (h : Holds L M)
    {e : Nat × XNet Arith} (he : e ∈ L) {p q : Port} (hl : (p, q) ∈ M.wires)
    (hp : tagged e.1 p.1 = true) : tagged e.1 q.1 = true := by
  have hf : (p, q) ∈ M.wires.filter (fun w => tagged e.1 w.1.1) := List.mem_filter.2 ⟨hl, hp⟩
  rw [h.wires e he] at hf
  obtain ⟨x, -, ex⟩ := List.mem_map.1 hf
  have e2 : tagPort e.1 x.2 = q := congrArg Prod.snd ex
  rw [← e2]
  exact tagged_self e.1 x.2.1

/-- A wire that starts in a net whose segments stay in it ends in it. -/
theorem walk_tagc {N : Net Arith} {c : Nat}
    (hT : ∀ p q, N.link p q → tagged c p.1 = true → tagged c q.1 = true) {u v x y : Port}
    (w : Walk N.link (N.End ar) u v x y) : tagged c u.1 = true → tagged c y.1 = true := by
  induction w with
  | single hl => exact hT _ _ hl
  | cons hl _ _ _ ih => exact fun h => ih (hT _ _ hl h)

theorem paired_tagc {N : Net Arith} {c : Nat}
    (hT : ∀ p q, N.link p q → tagged c p.1 = true → tagged c q.1 = true) {p q : Port}
    (h : N.Paired ar p q) (hp : tagged c p.1 = true) : tagged c q.1 = true := by
  obtain ⟨-, -, v, x, w⟩ := h
  exact walk_tagc hT w hp

/-- The agents of a numeral whose head is in such a net are all in it. -/
theorem NumList.tagc {N : Net Arith} {c : Nat}
    (hT : ∀ p q, N.link p q → tagged c p.1 = true → tagged c q.1 = true) {i : Id}
    {l : List Id} (h : NumList N i l) : tagged c i = true → ∀ a, a ∈ l → tagged c a = true := by
  induction h with
  | last _ =>
    intro hi a ha
    rw [List.mem_singleton.1 ha]
    exact hi
  | next _ hp _ ih =>
    intro hi a ha
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact hi
    · exact ih (paired_tagc hT hp hi) a ha'

/-- The agents of the numerals of a list of additions: `m + n + 1` for
each addition `m + n`. -/
def agentsSum : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => e.1 + e.2 + 1 + agentsSum l

/-- **The agents of the numerals of a list of additions, all together.**
In a well-formed net that has the numeral `m + n` of the `j`-th addition
on the free port tagged `t + j`, and whose segments stay in the net they
start in, the agents of those numerals make a list without repeats, of
`m + n + 1` agents for each addition; each is an agent of the net, and
is on the numeral of one of the additions. -/
theorem numerals_all {N : Net Arith} (hN : N.WF ar) :
    ∀ (l : List (Nat × Nat)) (t : Nat),
      (∀ j m n, l[j]? = some (m, n) → IsNum N ([0, t + j], 0) (m + n) ∧
        ∀ p q, N.link p q → tagged (t + j) p.1 = true → tagged (t + j) q.1 = true) →
      ∃ A : List Id, A.Nodup ∧ A.length = agentsSum l ∧
        ∀ a, a ∈ A → (∃ γ, N.agent a γ) ∧ (∃ j, tagged (t + j) a = true) ∧
          ∃ j m n i₀ L, l[j]? = some (m, n) ∧ N.Paired ar ([0, t + j], 0) (i₀, 0) ∧
            NumList N i₀ L ∧ L.length = m + n + 1 ∧ a ∈ L
  | [], _, _ => ⟨[], List.nodup_nil, rfl, fun _ ha => absurd ha List.not_mem_nil⟩
  | (m₀, n₀) :: l, t, h => by
    obtain ⟨hnum, hT0⟩ := h 0 m₀ n₀ List.getElem?_cons_zero
    obtain ⟨i₀, hp, hn⟩ := hnum
    obtain ⟨L, hL, eL⟩ := Num.list hn
    have ti : tagged (t + 0) i₀ = true := paired_tagc hT0 hp (tagged_self (t + 0) [0])
    have tL := hL.tagc hT0 ti
    have h' : ∀ j m n, l[j]? = some (m, n) → IsNum N ([0, t + 1 + j], 0) (m + n) ∧
        ∀ p q, N.link p q → tagged (t + 1 + j) p.1 = true → tagged (t + 1 + j) q.1 = true := by
      intro j m n hj
      have e : t + (j + 1) = t + 1 + j := by omega
      have hh := h (j + 1) m n (by
        rw [List.getElem?_cons_succ]
        exact hj)
      rw [e] at hh
      exact hh
    obtain ⟨A, hA1, hA2, hA3⟩ := numerals_all hN l (t + 1) h'
    refine ⟨L ++ A, List.nodup_append.2 ⟨hL.nodup hN, hA1, fun a ha b hb e => ?_⟩, ?_,
      fun a ha => ?_⟩
    · obtain ⟨-, ⟨j, hj⟩, -⟩ := hA3 b hb
      rw [← e] at hj
      have := tagged_unique (tL a ha) hj
      omega
    · rw [List.length_append, eL, hA2]
      rfl
    · rcases List.mem_append.1 ha with h1 | h1
      · exact ⟨hL.agent a h1, ⟨0, tL a h1⟩,
          0, m₀, n₀, i₀, L, List.getElem?_cons_zero, hp, hL, eL, h1⟩
      · obtain ⟨hag, ⟨j, hj⟩, j', m, n, i, L', hl', hp', hL', eL', ha'⟩ := hA3 a h1
        refine ⟨hag, ⟨j + 1, ?_⟩, j' + 1, m, n, i, L', ?_, ?_, hL', eL', ha'⟩
        · rw [show t + (j + 1) = t + 1 + j by omega]
          exact hj
        · rw [List.getElem?_cons_succ]
          exact hl'
        · rw [show t + (j' + 1) = t + 1 + j' by omega]
          exact hp'

/-- An entry of a list of additions is one of the nets side by side. -/
theorem mem_sumsFrom : ∀ {l : List (Nat × Nat)} {t j m n : Nat}, l[j]? = some (m, n) →
    (t + j, sum m n) ∈ sumsFrom t l
  | [], _, _, _, _, h => by
    rw [List.getElem?_nil] at h
    cases h
  | e :: l, t, j, m, n, h => by
    cases j with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      have e' : e = (m, n) := Option.some.inj h
      rw [e']
      exact List.mem_cons_self
    | succ j =>
      rw [List.getElem?_cons_succ] at h
      have hm := mem_sumsFrom (t := t + 1) h
      rw [show t + (j + 1) = t + 1 + j by omega]
      exact List.mem_cons_of_mem _ hm

/-- And each of the nets side by side is an entry of the list. -/
theorem sumsFrom_mem : ∀ {l : List (Nat × Nat)} {t : Nat} {e : Nat × XNet Arith},
    e ∈ sumsFrom t l → ∃ j m n, l[j]? = some (m, n) ∧ e = (t + j, sum m n)
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: l, t, e, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨0, x.1, x.2, List.getElem?_cons_zero, rfl⟩
    · obtain ⟨j, m, n, hj, he⟩ := sumsFrom_mem h'
      refine ⟨j + 1, m, n, ?_, ?_⟩
      · rw [List.getElem?_cons_succ]
        exact hj
      · rw [he, show t + (j + 1) = t + 1 + j by omega]

/-- The size of the second argument of the addition with a given tag. -/
def sndSize (l : List (Nat × Nat)) (c : Nat) : Nat :=
  match l[c]? with
  | some e => e.2
  | none => 0

theorem sndSize_at {l : List (Nat × Nat)} {j m n : Nat} (h : l[j]? = some (m, n)) :
    sndSize l (0 + j) = n := by
  unfold sndSize
  rw [Nat.zero_add, h]

/-- The successors of the second arguments of a list of additions. -/
def sndSum : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => e.2 + sndSum l

/-- The successors of a list of additions. -/
def succSum : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => e.1 + e.2 + succSum l

theorem agentsSum_eq : ∀ l : List (Nat × Nat), agentsSum l = succSum l + l.length
  | [] => rfl
  | e :: l => by
    have ih := agentsSum_eq l
    show e.1 + e.2 + 1 + agentsSum l = e.1 + e.2 + succSum l + (l.length + 1)
    omega

theorem sums_adders : ∀ (l : List (Nat × Nat)) (t : Nat),
    adders (flatA (sumsFrom t l)) = l.length
  | [], _ => rfl
  | e :: l, t => by
    show adders ((sum e.1 e.2).agents.map (tagA t) ++ flatA (sumsFrom (t + 1) l)) =
      l.length + 1
    rw [adders_append, adders_tag, adders_sum, sums_adders l (t + 1)]
    omega

theorem sums_succs : ∀ (l : List (Nat × Nat)) (t : Nat),
    succs (flatA (sumsFrom t l)) = succSum l
  | [], _ => rfl
  | e :: l, t => by
    show succs ((sum e.1 e.2).agents.map (tagA t) ++ flatA (sumsFrom (t + 1) l)) =
      e.1 + e.2 + succSum l
    rw [succs_append, succs_tag, succs_sum, sums_succs l (t + 1)]

theorem sums_zeros : ∀ (l : List (Nat × Nat)) (t : Nat),
    wIn (fun _ => true) isZero (flatA (sumsFrom t l)) = 2 * l.length
  | [], _ => rfl
  | e :: l, t => by
    show wIn (fun _ => true) isZero
      ((sum e.1 e.2).agents.map (tagA t) ++ flatA (sumsFrom (t + 1) l)) = 2 * (l.length + 1)
    rw [wIn_append, wIn_tag, zeros_sum, sums_zeros l (t + 1)]
    omega

theorem sums_zcnt : ∀ (l : List (Nat × Nat)) (t : Nat),
    l.length ≤ zcnt (flatA (sumsFrom t l))
  | [], _ => Nat.le_refl 0
  | e :: l, t => by
    show l.length + 1 ≤
      zcnt ((sum e.1 e.2).agents.map (tagA t) ++ flatA (sumsFrom (t + 1) l))
    rw [zcnt_append]
    have a := sum_zcnt_ge e.1 e.2 t
    have b := sums_zcnt l (t + 1)
    omega

theorem sums_fcnt (N : Nat → Nat) : ∀ (l : List (Nat × Nat)) (t : Nat),
    (∀ j m n, l[j]? = some (m, n) → N (t + j) = n) →
      fcnt N (flatA (sumsFrom t l)) ≤ claimsSum l
  | [], _, _ => Nat.le_refl 0
  | e :: l, t, h => by
    show fcnt N ((sum e.1 e.2).agents.map (tagA t) ++ flatA (sumsFrom (t + 1) l)) ≤
      e.1 + 1 + claimsSum l
    rw [fcnt_append]
    have a := sum_fcnt_le N t e.2 (h 0 e.1 e.2 List.getElem?_cons_zero) e.1
    have b := sums_fcnt N l (t + 1) (fun j m n hj => by
      have hh := h (j + 1) m n (by
        rw [List.getElem?_cons_succ]
        exact hj)
      rw [show t + (j + 1) = t + 1 + j by omega] at hh
      exact hh)
    omega

theorem sums_sndCnt (N : Nat → Nat) : ∀ (l : List (Nat × Nat)) (t : Nat),
    (∀ j m n, l[j]? = some (m, n) → N (t + j) = n) →
      sndSum l ≤ sndCnt N (flatA (sumsFrom t l))
  | [], _, _ => Nat.le_refl 0
  | e :: l, t, h => by
    show e.2 + sndSum l ≤
      sndCnt N ((sum e.1 e.2).agents.map (tagA t) ++ flatA (sumsFrom (t + 1) l))
    rw [sndCnt_append]
    have a := sum_sndCnt N t e.2 (h 0 e.1 e.2 List.getElem?_cons_zero) e.1
    have b := sums_sndCnt N l (t + 1) (fun j m n hj => by
      have hh := h (j + 1) m n (by
        rw [List.getElem?_cons_succ]
        exact hj)
      rw [show t + (j + 1) = t + 1 + j by omega] at hh
      exact hh)
    omega

/-- No agent is listed twice in nets side by side under different tags,
when none is listed twice in one of them. -/
theorem flatA_nodup : ∀ {L : List (Nat × XNet Arith)}, (L.map Prod.fst).Nodup →
    (∀ e, e ∈ L → (e.2.agents.map Prod.fst).Nodup) → ((flatA L).map Prod.fst).Nodup
  | [], _, _ => List.nodup_nil
  | e :: L, hnd, h => by
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.1 hnd
    show ((e.2.agents.map (tagA e.1) ++ flatA L).map Prod.fst).Nodup
    rw [List.map_append, map_fst_tag]
    refine List.nodup_append.2 ⟨nodup_snoc e.1 _ (h e List.mem_cons_self),
      flatA_nodup hnd' (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      fun a ha b hb eab => ?_⟩
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    obtain ⟨e', he', hy'⟩ := mem_flatG.1 hy
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy'
    have eab' : x ++ [e.1] = z.1 ++ [e'.1] := eab
    have ec : e.1 = e'.1 := (snoc_inj eab').2
    exact hn (by
      rw [ec]
      exact List.mem_map_of_mem (f := Prod.fst) he')

theorem sums_nodup (l : List (Nat × Nat)) : ((sums l).agents.map Prod.fst).Nodup :=
  flatA_nodup (sumsFrom_tags l 0).2 (fun e he => by
    obtain ⟨j, m, n, -, rfl⟩ := sumsFrom_mem he
    exact sum_nodup m n)

/-- Nets side by side start with no segment between two of them. -/
theorem besides_memT (L : List (Nat × XNet Arith)) : MemT (besides L) := fun e he => by
  obtain ⟨b, -, hx⟩ := mem_flatG.1 (show e ∈ flatW L from he)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hx
  show tagged 1 (x.1.1 ++ [b.1]) = tagged 1 (x.2.1 ++ [b.1])
  rw [tagged_append, tagged_append]

/-- **Any number of additions side by side are a memory in order.** -/
theorem sums_memOk (l : List (Nat × Nat)) : MemOk (sndSize l) (sndSum l) (sums l) where
  kinds := fun e he => by
    obtain ⟨b, hb, hx⟩ := mem_flatG.1 (show e ∈ flatA (sumsFrom 0 l) from he)
    obtain ⟨j, m, n, -, rfl⟩ := sumsFrom_mem hb
    obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hx
    exact sum_kind m n (0 + j) x hx'
  wires := fun e he => by
    obtain ⟨b, hb, hx⟩ := mem_flatG.1 (show e ∈ flatW (sumsFrom 0 l) from he)
    obtain ⟨j, m, n, hj, rfl⟩ := sumsFrom_mem hb
    obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hx
    exact sum_color (sndSize l) (0 + j) n (sndSize_at hj) m x hx'
  alive := fun s hs => by
    obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape _ hs
    cases hc : l[c]? with
    | none =>
      have e0 : sndSize l c = 0 := by
        unfold sndSize
        rw [hc]
      omega
    | some e =>
      obtain ⟨m, n⟩ := e
      have en : sndSize l c = n := by
        unfold sndSize
        rw [hc]
      have hm : (c, sum m n) ∈ sumsFrom 0 l := by
        have := mem_sumsFrom (t := 0) hc
        rw [Nat.zero_add] at this
        exact this
      have hl := (holds_besides (sumsFrom_tags l 0).2).looks hm
      exact (hl.agent [j]).trans (sum_snd_alive m n h4 (by omega))
  look := fun s hs => by
    obtain ⟨j, c, rfl, h4, h3⟩ := snd_shape _ hs
    cases hc : l[c]? with
    | none =>
      have e0 : sndSize l c = 0 := by
        unfold sndSize
        rw [hc]
      omega
    | some e =>
      obtain ⟨m, n⟩ := e
      have en : sndSize l c = n := by
        unfold sndSize
        rw [hc]
      have hm : (c, sum m n) ∈ sumsFrom 0 l := by
        have := mem_sumsFrom (t := 0) hc
        rw [Nat.zero_add] at this
        exact this
      have hl := (holds_besides (sumsFrom_tags l 0).2).looks hm
      obtain ⟨q, hq⟩ := sum_snd_look m n h4 (show j ≤ n + 3 by omega)
      exact ⟨tagPort c q, (hl.wire ([j], 0)).trans (congrArg (Option.map (tagPort c)) hq)⟩
  count := sums_sndCnt (sndSize l) l 0 (fun _ _ _ h => sndSize_at h)

/-- **At rest every cell of a first argument has been used**, for any
number of additions, with any number of threads and any schedule. -/
theorem sums_rest_first (l : List (Nat × Nat)) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat} (hr : ((XMach.init (sums l) nt).trace xsys σ i).1.resting = true) :
    fcnt (sndSize l) ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents = 0 := by
  have F := trace_first σ (init_ok (sums_memOk l) nt) i
  have z := total_init (heldFT (sndSize l)) (fun _ => rfl) (sums l) nt
  have e0 : (XMach.init (sums l) nt).mem = sums l := rfl
  rw [z, e0, (sums_rest l hnt σ hr).1] at F
  have f : fcnt (sndSize l) (sums l).agents ≤ claimsSum l :=
    sums_fcnt (sndSize l) l 0 (fun _ _ _ h => sndSize_at h)
  omega

/-- **At rest no adder is left**, for any number of additions. -/
theorem sums_rest_adders (l : List (Nat × Nat)) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat} (hr : ((XMach.init (sums l) nt).trace xsys σ i).1.resting = true) :
    adders ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents = 0 := by
  have Z := trace_zf (sums_wf l) (sums_nodup l) (sums_memOk l) hnt σ i
  have hf := sums_rest_first l hnt σ hr
  have hz := zcnt_le_fcnt (sndSize l) ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents
  have hrest : ∀ T, T ∈ ((XMach.init (sums l) nt).trace xsys σ i).1.ths → T = ⟨[], .idle⟩ :=
    fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z1 := total_rest heldAddT rfl _ hrest
  have z2 := total_rest heldZT rfl _ hrest
  have a : adders (sums l).agents = l.length := sums_adders l 0
  have b : l.length ≤ zcnt (sums l).agents := sums_zcnt l 0
  omega

/-- **What the memory holds at rest, for any number of additions.**  With
any number of threads and any schedule, a memory at rest holds no adder,
the `m + n` successors of every sum, one zero for each addition, and
nothing else. -/
theorem sums_census (l : List (Nat × Nat)) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat)
    {i : Nat} (hr : ((XMach.init (sums l) nt).trace xsys σ i).1.resting = true) :
    adders ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents = 0 ∧
      succs ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents = succSum l ∧
      zeros ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents = l.length ∧
      ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents.length = agentsSum l := by
  have A := sums_rest_adders l hnt σ hr
  obtain ⟨-, R, -⟩ := trace_read (sums_wf l) (sums_nodup l) hnt σ i
  have C0 := trace_census (fun _ => true) (sums_wf l) (sums_nodup l) (besides_memT _) hnt σ i
  have hrest : ∀ T, T ∈ ((XMach.init (sums l) nt).trace xsys σ i).1.ths → T = ⟨[], .idle⟩ :=
    fun T hT => XThread.eq_rest (List.all_eq_true.1 hr T hT)
  have z1 := total_rest (heldWT (fun _ => true) isZero) rfl _ hrest
  have z2 := total_rest (heldWT (fun _ => true) isAdd) rfl _ hrest
  have z3 := total_rest held rfl _ hrest
  have a0 := wIn_adders ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents
  have x0 : wIn (fun _ => true) isZero (sums l).agents = 2 * l.length := sums_zeros l 0
  have x1 : wIn (fun _ => true) isAdd (sums l).agents = l.length :=
    (wIn_adders _).trans (sums_adders l 0)
  have x2 : succs (sums l).agents = succSum l := sums_succs l 0
  have L := length_census ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents
  have e := agentsSum_eq l
  have Z0 : wIn (fun _ => true) isZero
      ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents = l.length := by
    omega
  exact ⟨A, by omega, Z0, by omega⟩

/-- **Any number of additions side by side, as a net, with its tags.**
The normal form of `Arith.sums_normal`, in which also every segment that
starts in the net of one of the additions ends in it. -/
theorem sums_normal_tags (l : List (Nat × Nat)) : ∃ N' : Net Arith,
    Steps (Step system) (claimsSum l) (sums l).toNet N' ∧ Normal (Step system) N' ∧
      (∀ i m n, l[i]? = some (m, n) → IsNum N' ([0, i], 0) (m + n)) ∧
      ∀ i m n, l[i]? = some (m, n) →
        ∀ p q, N'.link p q → tagged i p.1 = true → tagged i q.1 = true := by
  obtain ⟨P, e1, e2, hR, hI⟩ := sum_parts l 0
  have hT : ((partNets P).map Prod.fst).Nodup := by
    rw [e1]
    exact (sumsFrom_tags l 0).2
  have hY : (besides (partNets P)).toNet.WF ar := by
    rw [e1]
    exact sums_wf l
  obtain ⟨Z, s, hn, hH, hf⟩ := besides_holds P hT hY (fun p hp => (hR p hp).1)
    (fun p hp => (hR p hp).2)
  rw [e1, e2] at s
  refine ⟨Z.toNet, s, hn, fun i m n h => ?_, fun i m n h p q hl hp => ?_⟩
  · obtain ⟨pt, hpt, ht, hnet⟩ := hI i m n h
    obtain ⟨k, w⟩ := (hR pt hpt).1
    rw [hnet] at w
    have num := (hH.within_left hT hf hpt (hR pt hpt).1).isNum (works_rest_num w)
    rw [ht, Nat.zero_add] at num
    exact num
  · obtain ⟨pt, hpt, ht, -⟩ := hI i m n h
    have hm : (pt.tag, pt.left) ∈ partLefts P := List.mem_map.2 ⟨pt, hpt, rfl⟩
    have ht' : pt.tag = i := by
      rw [ht, Nat.zero_add]
    have hq := hH.link_tag hm (p := p) (q := q) hl (by
      show tagged pt.tag p.1 = true
      rw [ht']
      exact hp)
    have hq' : tagged pt.tag q.1 = true := hq
    rw [ht'] at hq'
    exact hq'

/-- **Any number of additions at rest are their sums and nothing else.**
With any number of threads and any schedule, every agent in a memory at
rest is one of the `m + n + 1` agents of the numeral on the free port of
one of the additions `m + n`. -/
theorem sums_exact (l : List (Nat × Nat)) {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sums l) nt).trace xsys σ i).1.resting = true) :
    ∀ e, e ∈ ((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents →
      ∃ j m n i₀ L, l[j]? = some (m, n) ∧
        ((XMach.init (sums l) nt).trace xsys σ i).1.mem.toNet.Paired ar ([0, j], 0) (i₀, 0) ∧
        NumList ((XMach.init (sums l) nt).trace xsys σ i).1.mem.toNet i₀ L ∧
        L.length = m + n + 1 ∧ e.1 ∈ L := by
  obtain ⟨N', hs, hn', hA, hTg⟩ := sums_normal_tags l
  have hX := sums_wf l
  have Lv := XMach.trace_live σ (XMach.init_live (xs := xsys) hX hnt) i
  obtain ⟨q, hn⟩ := Lv.rest hr
  have r := XMach.trace_run xsys σ (XMach.init (sums l) nt) i
  rw [XMach.init_toMach] at r
  obtain ⟨-, hu⟩ := MRun.final hX r q hn
  obtain ⟨e, -⟩ := (hu hs).2 hn'
  have e' : N' = ((XMach.init (sums l) nt).trace xsys σ i).1.mem.toNet := e
  subst e'
  have hN := Steps.wf hX hs
  obtain ⟨A, hnd, hlen, hall⟩ := numerals_all hN l 0 (fun j m n h => by
    rw [Nat.zero_add]
    exact ⟨hA j m n h, hTg j m n h⟩)
  obtain ⟨-, -, -, hL⟩ := sums_census l hnt σ hr
  have cov := nodup_cover A
    (((XMach.init (sums l) nt).trace xsys σ i).1.mem.agents.map Prod.fst) hnd
    (fun a ha => by
      obtain ⟨⟨γ, hγ⟩, -, -⟩ := hall a ha
      exact List.mem_map.2 ⟨(a, γ), hγ, rfl⟩)
    (by
      rw [List.length_map, hlen, hL]
      exact Nat.le_refl _)
  intro x hx
  obtain ⟨-, -, j, m, n, i₀, L, h1, h2, h3, h4, h5⟩ := hall x.1 (cov x.1 (List.mem_map_of_mem hx))
  rw [Nat.zero_add] at h2
  exact ⟨j, m, n, i₀, L, h1, h2, h3, h4, h5⟩

/-- `0 + 7`, `3 + 0` and `2 + 2` side by side, with any number of threads
and any schedule: a memory at rest holds no adder, the fourteen
successors of `7`, `3` and `4`, and seventeen agents in all. -/
theorem _root_.INet.Checks.Arith.ListsAtRest.c1 {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) {i : Nat}
    (hr : ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.resting = true) :
    adders ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.mem.agents = 0 ∧
      succs ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.mem.agents = 14 ∧
      ((XMach.init (sums [(0, 7), (3, 0), (2, 2)]) nt).trace xsys σ i).1.mem.agents.length =
        17 := by
  obtain ⟨h1, h2, -, h3⟩ := sums_census [(0, 7), (3, 0), (2, 2)] hnt σ hr
  exact ⟨h1, h2, h3⟩

end Arith

end INet
