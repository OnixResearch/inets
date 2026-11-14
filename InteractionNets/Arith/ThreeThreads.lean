import InteractionNets.Arith.Readers

/-! ### Three threads in turn on an addition -/

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

namespace Arith

variable {N M : Net Arith} {a s u : Id} {p q r : Port} {σ : Arith}

variable {j m n : Nat}

local macro "ports_differ" : tactic =>
  `(tactic| first | (intro e; simp at e; done) | (intro e; simp at e; omega))

/-- `Sweeps3 M M' w`: `w` times, each of three threads acts in turn, and
that takes the machine `M` to `M'`. -/
inductive Sweeps3 : XMach Arith → XMach Arith → Nat → Prop
  | refl (M : XMach Arith) : Sweeps3 M M 0
  | step {X X₁ X₂ X₃ : XNet Arith} {T₀ T₀' T₁ T₁' T₂ T₂' : XThread Arith} {c₁ c₂ c₃ : Nat}
      {M' : XMach Arith} {w : Nat} : XMach.act xsys X T₀ = (X₁, T₀', c₁) →
      XMach.act xsys X₁ T₁ = (X₂, T₁', c₂) → XMach.act xsys X₂ T₂ = (X₃, T₂', c₃) →
      Sweeps3 ⟨X₃, [T₀', T₁', T₂']⟩ M' w → Sweeps3 ⟨X, [T₀, T₁, T₂]⟩ M' (w + 1)

theorem Sweeps3.trace {M M' : XMach Arith} {w : Nat} (s : Sweeps3 M M' w) :
    (M.trace xsys (fun i => i % 3) (3 * w)).1 = M' := by
  induction s with
  | refl M => rfl
  | @step X X₁ X₂ X₃ T₀ T₀' T₁ T₁' T₂ T₂' c₁ c₂ c₃ M' w a₁ a₂ a₃ _ ih =>
    rw [show w + 1 = 1 + w from Nat.add_comm _ _, trace_triple_add, (sweep3_one a₁ a₂ a₃).1]
    exact ih

/-- When three threads act in turn, each has had `w` actions after
`3 * w`. -/
theorem hits_alt3 : ∀ w, hits (fun i => i % 3) 0 (3 * w) = w ∧
    hits (fun i => i % 3) 1 (3 * w) = w ∧ hits (fun i => i % 3) 2 (3 * w) = w
  | 0 => ⟨rfl, rfl, rfl⟩
  | w + 1 => by
    obtain ⟨h0, h1, h2⟩ := hits_alt3 w
    rw [Nat.mul_succ]
    refine ⟨?_, ?_, ?_⟩
    · show hits (fun i => i % 3) 0 (3 * w) + (if (3 * w) % 3 = 0 then 1 else 0) +
        (if (3 * w + 1) % 3 = 0 then 1 else 0) + (if (3 * w + 2) % 3 = 0 then 1 else 0) = w + 1
      rw [h0, ite_pos' (by omega), ite_neg' (by omega), ite_neg' (by omega)]
    · show hits (fun i => i % 3) 1 (3 * w) + (if (3 * w) % 3 = 1 then 1 else 0) +
        (if (3 * w + 1) % 3 = 1 then 1 else 0) + (if (3 * w + 2) % 3 = 1 then 1 else 0) = w + 1
      rw [h1, ite_neg' (by omega), ite_pos' (by omega), ite_neg' (by omega)]
    · show hits (fun i => i % 3) 2 (3 * w) + (if (3 * w) % 3 = 2 then 1 else 0) +
        (if (3 * w + 1) % 3 = 2 then 1 else 0) + (if (3 * w + 2) % 3 = 2 then 1 else 0) = w + 1
      rw [h2, ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]

/-- **Three threads that only read, in turn, do exactly the work of
each.** -/
theorem total_three_stays {X : XNet Arith} {P Q R : XThread Arith} {kP kQ kR : Nat}
    (sP : Stays xsys X P ⟨[], .idle⟩ kP) (sQ : Stays xsys X Q ⟨[], .idle⟩ kQ)
    (sR : Stays xsys X R ⟨[], .idle⟩ kR) :
    (⟨X, [P, Q, R]⟩ : XMach Arith).Total xsys (fun i => i % 3) (kP + kQ + kR) := by
  have hR : ∀ T, T ∈ (⟨X, [P, Q, R]⟩ : XMach Arith).ths →
      T.Reads xsys (⟨X, [P, Q, R]⟩ : XMach Arith).mem := by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (sP.after rfl).1
    · rcases List.mem_cons.1 hT with rfl | hT
      · exact (sQ.after rfl).1
      · rcases List.mem_cons.1 hT with rfl | hT
        · exact (sR.after rfl).1
        · cases hT
  have key : ∀ i, (⟨X, [P, Q, R]⟩ : XMach Arith).work xsys (fun i => i % 3) i =
      P.tally XThread.busy xsys X (hits (fun i => i % 3) 0 i) +
        Q.tally XThread.busy xsys X (hits (fun i => i % 3) 1 i) +
        R.tally XThread.busy xsys X (hits (fun i => i % 3) 2 i) := by
    intro i
    have e := XMach.tally_reads XThread.busy (fun i => i % 3) hR i
    show (⟨X, [P, Q, R]⟩ : XMach Arith).tally XThread.busy xsys (fun i => i % 3) i = _
    rw [e]
    show 0 + P.tally XThread.busy xsys X (hits (fun i => i % 3) 0 i) +
      Q.tally XThread.busy xsys X (hits (fun i => i % 3) 1 i) +
      R.tally XThread.busy xsys X (hits (fun i => i % 3) 2 i) = _
    omega
  obtain ⟨h0, h1, h2⟩ := hits_alt3 (kP + kQ + kR)
  refine ⟨3 * (kP + kQ + kR), fun i hi => ?_⟩
  have up := key i
  have u1 := sP.tally_le rfl (hits (fun i => i % 3) 0 i)
  have u2 := sQ.tally_le rfl (hits (fun i => i % 3) 1 i)
  have u3 := sR.tally_le rfl (hits (fun i => i % 3) 2 i)
  have at0 := key (3 * (kP + kQ + kR))
  rw [h0, h1, h2, sP.tally_eq rfl _ (by omega), sQ.tally_eq rfl _ (by omega),
    sR.tally_eq rfl _ (by omega)] at at0
  have lo := XMach.work_mono (xs := xsys) (fun i => i % 3) (⟨X, [P, Q, R]⟩ : XMach Arith) hi
  omega

/-- **Three threads in turn, to the end of the run**: `w` actions of each,
then each only reads; the work is all of these. -/
theorem total3_sweeps {M : XMach Arith} {Y : XNet Arith} {P Q R : XThread Arith}
    {w kP kQ kR W : Nat} (s : Sweeps3 M ⟨Y, [P, Q, R]⟩ w) (hlen : M.ths.length = 3)
    (sP : Stays xsys Y P ⟨[], .idle⟩ kP) (sQ : Stays xsys Y Q ⟨[], .idle⟩ kQ)
    (sR : Stays xsys Y R ⟨[], .idle⟩ kR) (hP : 1 ≤ kP) (hQ : 1 ≤ kQ) (hR : 1 ≤ kR)
    (hW : W = 3 * w + (kP + kQ + kR)) : M.Total xsys (fun i => i % 3) W := by
  subst hW
  have hb : ∀ (t : Nat) (T : XThread Arith),
      (M.trace xsys (fun i => i % 3) (3 * w)).1.ths[t]? = some T → T ≠ ⟨[], .idle⟩ := by
    rw [s.trace]
    intro t T hT
    cases t with
    | zero =>
      have e : P = T := Option.some.inj hT
      subst e
      exact sP.ne_rest hP
    | succ t =>
      cases t with
      | zero =>
        have e : Q = T := Option.some.inj hT
        subst e
        exact sQ.ne_rest hQ
      | succ t =>
        cases t with
        | zero =>
          have e : R = T := Option.some.inj hT
          subst e
          exact sR.ne_rest hR
        | succ t => exact absurd hT (by simp)
  have full := XMach.work_full (xs := xsys) (M := M) (σ := fun i => i % 3) (N := 3 * w) hb
    (fun i => by
      show i % 3 < M.ths.length
      rw [hlen]
      exact Nat.mod_lt _ (by omega)) (3 * w) (Nat.le_refl _)
  exact total_after3 s.trace full (total_three_stays sP sQ sR)

theorem assoc_wires_putLink {X : XNet Arith} {p q k : Port} (h : p ≠ k) :
    assoc k (X.putLink p q).wires = assoc k X.wires := assoc_cons_ne _ h

theorem nextSeg_putLink {X : XNet Arith} {p q c p' : Port} (h : p ≠ c) :
    nextSeg (X.putLink p q).wires c p' = nextSeg X.wires c p' := nextSeg_cons_ne _ _ _ h

theorem wires_takeAgent (X : XNet Arith) (a : Id) : (X.takeAgent a).wires = X.wires := rfl

theorem wires_putAgent (X : XNet Arith) (a : Id) (α : Arith) :
    (X.putAgent a α).wires = X.wires := rfl

theorem agents_putLink (X : XNet Arith) (p q : Port) : (X.putLink p q).agents = X.agents := rfl

theorem assoc_takeAgent_ne {X : XNet Arith} {a k : Id} (h : a ≠ k) :
    assoc k (X.takeAgent a).agents = assoc k X.agents := by
  show assoc k (X.agents.filter fun e => decide (e.1 ≠ a)) = _
  rw [assoc_filter_ne, ite_neg' h]

theorem assoc_putAgent_ne {X : XNet Arith} {a k : Id} {α : Arith} (h : a ≠ k) :
    assoc k (X.putAgent a α).agents = assoc k X.agents := assoc_cons_ne _ h

theorem assoc_takeAgent_self (X : XNet Arith) (a : Id) :
    assoc a (X.takeAgent a).agents = none := by
  show assoc a (X.agents.filter fun e => decide (e.1 ≠ a)) = none
  rw [assoc_filter_ne, ite_pos' rfl]

/-- Reduce a question about the segments of a memory written with takes
and puts to the same question about the memory underneath. -/
local macro "under_wires" : tactic =>
  `(tactic| repeat (first | rw [wires_takeAgent] | rw [wires_putAgent] |
      rw [assoc_wires_putLink (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))] | rw [nextSeg_putLink (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))]))

/-- The same for its agents. -/
local macro "under_agents" : tactic =>
  `(tactic| repeat (first | rw [agents_putLink] | rw [assoc_takeAgent_ne (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))] |
      rw [assoc_putAgent_ne (by first | (intro e; simp at e; done) | (intro e; simp at e; omega))]))

section Bystander

variable {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}

theorem RaceBase.by_look2 (B : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc (([2], 0) : Port) X.wires = some ([n' + 1 + 4], 1) := by
  have h := solo_look_two (m' + 1) (n' + 1) (16 + 17 * (m' + 1))
  rw [B.solo] at h
  exact h

theorem RaceBase.by_seek2 (B : RaceBase (m' + 1) (n' + 1) X rest) :
    nextSeg X.wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0) := by
  have h := (solo_seek_two (m' + 1) (n' + 1) (by omega) (16 + 17 * (m' + 1))).1 (by omega)
  rw [B.solo] at h
  exact h

theorem RaceBase.by_stopA (B : RaceBase (m' + 1) (n' + 1) X rest) :
    nextSeg X.wires ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1) = none := by
  have h := solo_stop_adder (m' + 1) (n' + 1) (by omega) (16 + 17 * (m' + 1))
  rw [B.solo] at h
  exact h

theorem RaceBase.by_three (B : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc [3] X.agents = some Arith.zero := by
  have hx3 : assoc [3] (sum (m' + 1 + 1) (n' + 1)).agents = some Arith.zero :=
    sum_assoc_base (m' + 1) (n' + 1) (e := ([3], Arith.zero))
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h := solo_snd_forever (m' + 1) (n' + 1) (j := 3) (by omega) (by omega) hx3
    (16 + 17 * (m' + 1))
  rw [B.solo] at h
  exact h

theorem RaceBase.by_look3 (B : RaceBase (m' + 1) (n' + 1) X rest) :
    assoc (([3], 0) : Port) X.wires = some ([4], 1) := by
  have h := (solo_look_snd (m' + 1) (n' + 1) (j := 3) (by omega) (by omega)
    (16 + 17 * (m' + 1))).1
  rw [B.solo] at h
  exact h

end Bystander

/-- What is left to a thread that has read the segment of the zero of the
second argument, in a memory the rounds leave: it finds no second segment,
then its last agent gone. -/
theorem Final.bystander_a {m n : Nat} {Y : XNet Arith}
    (F : Final n (sum (m + 1) n) Y (n + 3 + m + 1) m) (hn : 1 ≤ n) {j : Nat} (hj : n + 3 < j)
    (γ : Arith) :
    Stays xsys Y ⟨[([j], γ)], .seek [3] .zero ([3], 0) ([4], 1)⟩ ⟨[], .idle⟩ 2 := by
  have S := snd_sum (m + 1) n
  have s1 : XMach.act xsys Y ⟨[([j], γ)], .seek [3] .zero ([3], 0) ([4], 1)⟩ =
      (Y, ⟨[([j], γ)], .idle⟩, 0) :=
    XMach.act_seek_stop (seek_aux_none Y _ 1 (by decide)) (nextSeg_none fun q hq =>
      (F.down S (j := 3) (by omega) (by omega) q).1 hq)
  have s2 : XMach.act xsys Y ⟨[([j], γ)], .idle⟩ = (Y, ⟨[], .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([j], γ)) (by
      show ¬ assoc [j] Y.agents = some γ
      rw [F.no_top hj]
      exact fun h => by cases h)
  exact .step (k := 1) (fun h => by
    injection h with _ h2
    cases h2) s1 (.step (k := 0) (fun h => by cases h) s2 (.refl _))

/-- The same from the moment it has popped that zero. -/
theorem Final.bystander_b {m n : Nat} {Y : XNet Arith}
    (F : Final n (sum (m + 1) n) Y (n + 3 + m + 1) m) (hn : 1 ≤ n) {j : Nat} (hj : n + 3 < j)
    (γ : Arith) :
    Stays xsys Y ⟨[([j], γ)], .look [3] .zero⟩ ⟨[], .idle⟩ 3 := by
  have S := snd_sum (m + 1) n
  have hl : assoc (([3], 0) : Port) Y.wires = some ([4], 1) :=
    assoc_eq_of_unique ((F.up S (j := 3) (by omega) (by omega) _).2 rfl)
      (fun q' hq => (F.up S (j := 3) (by omega) (by omega) q').1 hq)
  exact .step (k := 2) (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look hl) (F.bystander_a hn hj γ)

/-- **The race for the last pair with a thread that reads between the two**:
the third thread takes the zero and the last adder, writes the two segments
and starts over, in five actions, while the second, which has read the
segment of that zero, reads on to the last adder, finds it gone and goes on
to the zero of the second argument. -/
theorem race_wins3_a {n : Nat} {Y0 Y0' Y1' Y2' Y3' Y4' : XNet Arith}
    {F0 F1 F2 F3 F4 F5 : XThread Arith} {c0 c1 c2 c3 c4 : Nat} {l tq : List (Id × Arith)}
    (f0 : XMach.act xsys Y0 F0 = (Y0', F1, c0))
    (hZ : assoc [2] Y0'.agents = some .zero)
    (f1 : XMach.act xsys (Y0'.takeAgent [2]) F1 = (Y1', F2, c1))
    (hA : assoc [0, n + 4] Y1'.agents = some .add)
    (f2 : XMach.act xsys (Y1'.takeAgent [0, n + 4]) F2 = (Y2', F3, c2))
    (f3 : XMach.act xsys (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2)) F3 = (Y3', F4, c3))
    (f4 : XMach.act xsys (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1)) F4 = (Y4', F5, c4))
    (k0 : assoc (([2], 0) : Port) Y0'.wires = some ([n + 4], 1))
    (k1 : nextSeg Y1'.wires ([n + 4], 1) ([2], 0) = some ([0, n + 4], 0))
    (k2a : assoc [0, n + 4] Y2'.agents = none)
    (k2b : nextSeg Y2'.wires ([0, n + 4], 0) ([n + 4], 1) = none)
    (k3 : assoc [3] Y3'.agents = some Arith.zero)
    (k4 : assoc (([3], 0) : Port) Y4'.wires = some ([4], 1)) :
    Sweeps3 ⟨Y0, [F0, ⟨([3], .zero) :: tq, .look [2] .zero⟩,
        ⟨l, .ready [2] [0, n + 4] .zero .add⟩]⟩
      ⟨Y4', [F5, ⟨tq, .seek [3] .zero ([3], 0) ([4], 1)⟩, ⟨Y4'.agents, .idle⟩]⟩ 5 := by
  have g0 : XMach.act xsys Y0' ⟨([3], .zero) :: tq, .look [2] .zero⟩ =
      (Y0', ⟨([3], .zero) :: tq, .seek [2] .zero ([2], 0) ([n + 4], 1)⟩, 0) :=
    XMach.act_look k0
  have g1 : XMach.act xsys Y1' ⟨([3], .zero) :: tq, .seek [2] .zero ([2], 0) ([n + 4], 1)⟩ =
      (Y1', ⟨([3], .zero) :: tq, .seek [2] .zero ([n + 4], 1) ([0, n + 4], 0)⟩, 0) :=
    XMach.act_seek_next (seek_aux_none _ _ 1 (by decide)) k1
  have g2 : XMach.act xsys Y2' ⟨([3], .zero) :: tq, .seek [2] .zero ([n + 4], 1) ([0, n + 4], 0)⟩ =
      (Y2', ⟨([3], .zero) :: tq, .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans k2a) k2b
  have g3 : XMach.act xsys Y3' ⟨([3], .zero) :: tq, .idle⟩ =
      (Y3', ⟨tq, .look [3] .zero⟩, 0) := XMach.act_idle_pos (e := ([3], Arith.zero)) k3
  have g4 : XMach.act xsys Y4' ⟨tq, .look [3] .zero⟩ =
      (Y4', ⟨tq, .seek [3] .zero ([3], 0) ([4], 1)⟩, 0) := XMach.act_look k4
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
      (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2), ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩, 0) := rfl
  have r3 : XMach.act xsys Y3' ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1), ⟨l, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys Y4' ⟨l, .write [] []⟩ = (Y4', ⟨Y4'.agents, .idle⟩, 0) := rfl
  exact .step f0 g0 r0 (.step f1 g1 r1 (.step f2 g2 r2 (.step f3 g3 r3
    (.step f4 g4 r4 (.refl _)))))

/-- The same when the second thread is about to pop that zero as the third
takes it. -/
theorem race_wins3_b {n : Nat} {Y0 Y0' Y1' Y2' Y3' Y4' : XNet Arith}
    {F0 F1 F2 F3 F4 F5 : XThread Arith} {c0 c1 c2 c3 c4 : Nat} {l tq : List (Id × Arith)}
    (f0 : XMach.act xsys Y0 F0 = (Y0', F1, c0))
    (hZ : assoc [2] Y0'.agents = some .zero)
    (f1 : XMach.act xsys (Y0'.takeAgent [2]) F1 = (Y1', F2, c1))
    (hA : assoc [0, n + 4] Y1'.agents = some .add)
    (f2 : XMach.act xsys (Y1'.takeAgent [0, n + 4]) F2 = (Y2', F3, c2))
    (f3 : XMach.act xsys (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2)) F3 = (Y3', F4, c3))
    (f4 : XMach.act xsys (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1)) F4 = (Y4', F5, c4))
    (k1 : assoc (([2], 0) : Port) Y1'.wires = some ([n + 4], 1))
    (k2 : nextSeg Y2'.wires ([n + 4], 1) ([2], 0) = some ([0, n + 4], 0))
    (k3a : assoc [0, n + 4] Y3'.agents = none)
    (k3b : nextSeg Y3'.wires ([0, n + 4], 0) ([n + 4], 1) = none)
    (k4 : assoc [3] Y4'.agents = some Arith.zero) :
    Sweeps3 ⟨Y0, [F0, ⟨([2], .zero) :: ([3], .zero) :: tq, .idle⟩,
        ⟨l, .ready [2] [0, n + 4] .zero .add⟩]⟩
      ⟨Y4', [F5, ⟨tq, .look [3] .zero⟩, ⟨Y4'.agents, .idle⟩]⟩ 5 := by
  have g0 : XMach.act xsys Y0' ⟨([2], .zero) :: ([3], .zero) :: tq, .idle⟩ =
      (Y0', ⟨([3], .zero) :: tq, .look [2] .zero⟩, 0) :=
    XMach.act_idle_pos (e := ([2], Arith.zero)) hZ
  have g1 : XMach.act xsys Y1' ⟨([3], .zero) :: tq, .look [2] .zero⟩ =
      (Y1', ⟨([3], .zero) :: tq, .seek [2] .zero ([2], 0) ([n + 4], 1)⟩, 0) :=
    XMach.act_look k1
  have g2 : XMach.act xsys Y2' ⟨([3], .zero) :: tq, .seek [2] .zero ([2], 0) ([n + 4], 1)⟩ =
      (Y2', ⟨([3], .zero) :: tq, .seek [2] .zero ([n + 4], 1) ([0, n + 4], 0)⟩, 0) :=
    XMach.act_seek_next (seek_aux_none _ _ 1 (by decide)) k2
  have g3 : XMach.act xsys Y3' ⟨([3], .zero) :: tq, .seek [2] .zero ([n + 4], 1) ([0, n + 4], 0)⟩ =
      (Y3', ⟨([3], .zero) :: tq, .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans k3a) k3b
  have g4 : XMach.act xsys Y4' ⟨([3], .zero) :: tq, .idle⟩ =
      (Y4', ⟨tq, .look [3] .zero⟩, 0) := XMach.act_idle_pos (e := ([3], Arith.zero)) k4
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
      (Y2'.putLink ([0, n + 4], 1) ([0, n + 4], 2), ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩, 0) := rfl
  have r3 : XMach.act xsys Y3' ⟨l, .write [] [(([0, n + 4], 2), ([0, n + 4], 1))]⟩ =
      (Y3'.putLink ([0, n + 4], 2) ([0, n + 4], 1), ⟨l, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys Y4' ⟨l, .write [] []⟩ = (Y4', ⟨Y4'.agents, .idle⟩, 0) := rfl
  exact .step f0 g0 r0 (.step f1 g1 r1 (.step f2 g2 r2 (.step f3 g3 r3
    (.step f4 g4 r4 (.refl _)))))

/-- **The third thread takes the zero while the first reads the segment of the
last adder**, and the second, which has read the segment of that
zero, reads on to the last adder and finds it gone.  Three threads in turn, to the end of the run. -/
theorem race3_d6_a {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨rest, .look [0, n' + 1 + 4] .add⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 29 + 7) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) B.stop
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2) (by
      under_wires
      exact B.by_seek2) (by
      under_agents
      exact assoc_takeAgent_self _ _) (by
      under_wires
      exact B.by_stopA) (by
      under_agents
      exact B.by_three) (by
      under_wires
      exact B.by_look3)
  have sF := sE2.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero while the first reads the segment of the
last adder**, and the second, about to pop that zero, pops it, reads on
to the last adder and finds it gone.  Three threads in turn, to the end of the run. -/
theorem race3_d6_b {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨rest, .look [0, n' + 1 + 4] .add⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 29 + 8) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) B.stop
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2) (by
      under_wires
      exact B.by_seek2) (by
      under_agents
      exact assoc_takeAgent_self _ _) (by
      under_wires
      exact B.by_stopA) (by
      under_agents
      exact B.by_three)
  have sF := sE2.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero while the first is on its way from the
last adder to it**, and the second, which has read the segment of that
zero, reads on to the last adder and finds it gone.  Three threads in turn, to the end of the run. -/
theorem race3_d7_a {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 7) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero1) B.stop
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port) ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 k3
    (by
      under_wires
      exact B.by_look2) (by
      under_wires
      exact B.by_seek2) (by
      under_agents
      exact assoc_takeAgent_self _ _) (by
      under_wires
      exact B.by_stopA) (by
      under_agents
      exact B.by_three) (by
      under_wires
      exact B.by_look3)
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero while the first is on its way from the
last adder to it**, and the second, about to pop that zero, pops it, reads on
to the last adder and finds it gone.  Three threads in turn, to the end of the run. -/
theorem race3_d7_b {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 8) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      (X, ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl B.seek
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero1) B.stop
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port) ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 k3
    (by
      under_wires
      exact B.by_look2) (by
      under_wires
      exact B.by_seek2) (by
      under_agents
      exact assoc_takeAgent_self _ _) (by
      under_wires
      exact B.by_stopA) (by
      under_agents
      exact B.by_three)
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The first and the third thread take one agent of the last pair each in
the same round**, and the second, which has read the segment of that
zero, reads on to the last adder and finds it gone.  Three threads in turn, to the end of the run. -/
theorem race3_d9_a {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 7) := by
  have hr := B.rest
  subst hr
  have hA9 : ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) := by
    show List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) (([0, n' + 1 + 4], Arith.add) ::
      (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter (fun e => decide (e.1 ≠ [2]))) = _
    rw [List.filter_cons_of_neg (by simp),
      filter_ne_comm (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) [2] [0, n' + 1 + 4],
      filter_ne_idem, filter_ne_comm]
  have F := B.final hA9 rfl
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .ready [0, n' + 1 + 4] [2] .add .zero⟩ =
      ((X.takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half [0, n' + 1 + 4] [2] .add .zero⟩, 0) :=
    XMach.act_ready B.adder
  have hZ : assoc [2] (X.takeAgent [0, n' + 1 + 4]).agents = some .zero := by
    show assoc [2] (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = some .zero
    rw [assoc_filter_ne, ite_neg' (by ports_differ)]
    exact B.zero
  have gz : assoc [2] ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).agents = none := by
    show assoc [2] ((X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter fun e => decide (e.1 ≠ [2])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f1 : XMach.act xsys ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gz] at h1
      cases h1)
  have hA : assoc [0, n' + 1 + 4] (((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).agents = some .add := by
    show (if ([0, n' + 1 + 4] : Id) = [0, n' + 1 + 4] then some Arith.add else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) (by
      show assoc [0, 0, n' + 1 + 3 + 2] (List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) (([0, n' + 1 + 4], Arith.add) ::
        (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter (fun e => decide (e.1 ≠ [2])))) = some .succ
      rw [assoc_filter_ne, ite_neg' (by ports_differ), assoc_cons_ne _ (by ports_differ),
        assoc_filter_ne, ite_neg' (by ports_differ), assoc_filter_ne,
        ite_neg' (by ports_differ)]
      exact B.hist.agent_res (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) List.mem_cons_self)
  have f3 : XMach.act xsys (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port) ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 hZ f1 hA f2 f3 k3
    (by
      under_wires
      exact B.by_look2) (by
      under_wires
      exact B.by_seek2) (by
      under_agents
      exact assoc_takeAgent_self _ _) (by
      under_wires
      exact B.by_stopA) (by
      under_agents
      exact B.by_three) (by
      under_wires
      exact B.by_look3)
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The first and the third thread take one agent of the last pair each in
the same round**, and the second, about to pop that zero, pops it, reads on
to the last adder and finds it gone.  Three threads in turn, to the end of the run. -/
theorem race3_d9_b {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 8) := by
  have hr := B.rest
  subst hr
  have hA9 : ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = (X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) := by
    show List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) (([0, n' + 1 + 4], Arith.add) ::
      (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter (fun e => decide (e.1 ≠ [2]))) = _
    rw [List.filter_cons_of_neg (by simp),
      filter_ne_comm (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) [2] [0, n' + 1 + 4],
      filter_ne_idem, filter_ne_comm]
  have F := B.final hA9 rfl
  obtain ⟨-, -, -, q, k3, sE3⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .ready [0, n' + 1 + 4] [2] .add .zero⟩ =
      ((X.takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half [0, n' + 1 + 4] [2] .add .zero⟩, 0) :=
    XMach.act_ready B.adder
  have hZ : assoc [2] (X.takeAgent [0, n' + 1 + 4]).agents = some .zero := by
    show assoc [2] (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = some .zero
    rw [assoc_filter_ne, ite_neg' (by ports_differ)]
    exact B.zero
  have gz : assoc [2] ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).agents = none := by
    show assoc [2] ((X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter fun e => decide (e.1 ≠ [2])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f1 : XMach.act xsys ((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gz] at h1
      cases h1)
  have hA : assoc [0, n' + 1 + 4] (((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).agents = some .add := by
    show (if ([0, n' + 1 + 4] : Id) = [0, n' + 1 + 4] then some Arith.add else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys ((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩ =
      (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) (by
      show assoc [0, 0, n' + 1 + 3 + 2] (List.filter (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) (([0, n' + 1 + 4], Arith.add) ::
        (X.agents.filter fun e => decide (e.1 ≠ [0, n' + 1 + 4])).filter (fun e => decide (e.1 ≠ [2])))) = some .succ
      rw [assoc_filter_ne, ite_neg' (by ports_differ), assoc_cons_ne _ (by ports_differ),
        assoc_filter_ne, ite_neg' (by ports_differ), assoc_filter_ne,
        ite_neg' (by ports_differ)]
      exact B.hist.agent_res (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) List.mem_cons_self)
  have f3 : XMach.act xsys (((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((X.takeAgent [0, n' + 1 + 4]).takeAgent [2]).putAgent [0, n' + 1 + 4] .add).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look (by
      show assoc (([0, 0, n' + 1 + 3 + 2], 0) : Port) ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) = _
      rw [assoc_cons_ne _ (by ports_differ)]
      exact B.look_res)
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 hZ f1 hA f2 f3 k3
    (by
      under_wires
      exact B.by_look2) (by
      under_wires
      exact B.by_seek2) (by
      under_agents
      exact assoc_takeAgent_self _ _) (by
      under_wires
      exact B.by_stopA) (by
      under_agents
      exact B.by_three)
  have sF := sE3.trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The one alignment in which the first thread keeps the last pair, with
a thread reading between the two**: the third thread takes the zero, the
first the adder; the third does not find the adder and puts the zero back,
and the first takes it.  The second thread, which has read the segment of that zero,
reads on to the last adder and finds it gone.  Three threads in turn, to the
end of the run. -/
theorem race3_d8_a {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) {j t1 t2 : Nat} (hj : n' + 1 + 3 < j)
    (ht1 : n' + 1 + 3 < t1) (ht2 : n' + 1 + 3 < t2) (γ : Arith) :
    (⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (5 * (m' + 1) + 3 * (n' + 1) + 22 + 8) := by
  have hA8 : ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents =
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
  have r0 : XMach.act xsys X ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((X.takeAgent [2]), ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .half [2] [0, n' + 1 + 4] .zero .add⟩, 0) := XMach.act_ready B.zero
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩, 0) := XMach.act_ready B.adder1
  have gA : assoc [0, n' + 1 + 4] ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] ((X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have r1 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .half [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero), ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gA] at h1
      cases h1)
  have hZ3 : assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).agents = some Arith.zero := by
    show (if ([2] : Id) = [2] then some Arith.zero else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero) ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 1) :=
    XMach.act_half (R := addZero.toX) (by
      rw [ite_pos' (show assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).agents = some Arith.zero ∧
        ([0, n' + 1 + 4] : Id) ≠ [2] from ⟨hZ3, by ports_differ⟩)]
      rfl)
  have h3 : assoc [3] ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).agents = some Arith.zero :=
    F8.agent (e := ([3], Arith.zero)) (by
      rw [F8.agents]
      exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self))
  have r2 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .idle⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨[([t1], .succ), ([t2], .succ)], .look [3] .zero⟩, 0) := XMach.act_idle_pos (e := ([3], Arith.zero)) h3
  have f3 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨rest, .write [] [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 0) := rfl
  have hl6 : assoc (([3], 0) : Port) ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).wires) = some ([4], 1) :=
    assoc_eq_of_unique ((F8.up S (j := 3) (by omega) (by omega) _).2 rfl)
      (fun q' hq => (F8.up S (j := 3) (by omega) (by omega) q').1 hq)
  rw [assoc_cons_ne _ (by ports_differ)] at hl6
  have r3 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨[([t1], .succ), ([t2], .succ)], .look [3] .zero⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨[([t1], .succ), ([t2], .succ)], .seek [3] .zero ([3], 0) ([4], 1)⟩, 0) := XMach.act_look hl6
  have f4 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨rest, .write [] [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨rest, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t1], .succ), ([t2], .succ)], .seek [3] .zero ([3], 0) ([4], 1)⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[([t1], .succ), ([t2], .succ)], .idle⟩, 0) :=
    XMach.act_seek_stop rfl (nextSeg_none fun q hq =>
      (F8.down S (j := 3) (by omega) (by omega) q).1 hq)
  have f5 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨rest, .write [] []⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have r5 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t1], .succ), ([t2], .succ)], .idle⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[([t2], .succ)], .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([t1], Arith.succ)) (by
      show ¬ assoc [t1] ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = some Arith.succ
      rw [F8.no_top ht1]
      exact fun h => by cases h)
  have r6 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t2], .succ)], .idle⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[], .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([t2], Arith.succ)) (by
      show ¬ assoc [t2] ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = some Arith.succ
      rw [F8.no_top ht2]
      exact fun h => by cases h)
  have g0 : XMach.act xsys X ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩ =
      (X, ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([2], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look (by
      under_wires
      exact B.by_look2)
  have g1 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([2], 0) ([n' + 1 + 4], 1)⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([n' + 1 + 4], 1) ([0, n' + 1 + 4], 0)⟩, 0) :=
    XMach.act_seek_next (seek_aux_none _ _ 1 (by decide)) (by
      under_wires
      exact B.by_seek2)
  have g2 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([n' + 1 + 4], 1) ([0, n' + 1 + 4], 0)⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨([3], .zero) :: [([j], γ)], .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans (by
      under_agents
      exact assoc_takeAgent_self _ _)) (by
      under_wires
      exact B.by_stopA)
  have g3 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨([3], .zero) :: [([j], γ)], .idle⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨[([j], γ)], .look [3] .zero⟩, 0) :=
    XMach.act_idle_pos (e := ([3], Arith.zero)) (by
      under_agents
      exact B.by_three)
  have g4 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([j], γ)], .look [3] .zero⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[([j], γ)], .seek [3] .zero ([3], 0) ([4], 1)⟩, 0) :=
    XMach.act_look (by
      under_wires
      exact B.by_look3)
  have sw : Sweeps3 ⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩, ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩
      ⟨((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), [⟨rest, .write [] []⟩, ⟨[([j], γ)], .seek [3] .zero ([3], 0) ([4], 1)⟩, ⟨[([t1], .succ), ([t2], .succ)], .idle⟩]⟩ 5 :=
    .step f0 g0 r0 (.step f1 g1 r1 (.step f2 g2 r2 (.step f3 g3 r3 (.step f4 g4 r4 (.refl _)))))
  have sF := F8.pass_stays S (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl
    (Stays.step (fun h => by
      injection h with _ h2
      cases h2) f5 sF)
    (F8.bystander_a (by omega) hj γ)
    (Stays.step (fun h => by cases h) r5 (Stays.step (fun h => by cases h) r6 (Stays.refl _)))
    (by omega) (by omega) (by omega) (by omega)

/-- **The one alignment in which the first thread keeps the last pair, with
a thread reading between the two**: the third thread takes the zero, the
first the adder; the third does not find the adder and puts the zero back,
and the first takes it.  The second thread, about to pop that zero,
reads on to the last adder and finds it gone.  Three threads in turn, to the
end of the run. -/
theorem race3_d8_b {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) {j t1 t2 : Nat} (hj : n' + 1 + 3 < j)
    (ht1 : n' + 1 + 3 < t1) (ht2 : n' + 1 + 3 < t2) (γ : Arith) :
    (⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ : XMach Arith).Total xsys (fun i => i % 3)
      (5 * (m' + 1) + 3 * (n' + 1) + 22 + 9) := by
  have hA8 : ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents =
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
  have r0 : XMach.act xsys X ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((X.takeAgent [2]), ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .half [2] [0, n' + 1 + 4] .zero .add⟩, 0) := XMach.act_ready B.zero
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩, 0) := XMach.act_ready B.adder1
  have gA : assoc [0, n' + 1 + 4] ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] ((X.agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have r1 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .half [2] [0, n' + 1 + 4] .zero .add⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero), ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .idle⟩, 0) :=
    XMach.act_half_none (ite_neg' fun h => by
      have h1 := h.1
      rw [gA] at h1
      cases h1)
  have hZ3 : assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).agents = some Arith.zero := by
    show (if ([2] : Id) = [2] then some Arith.zero else _) = _
    rw [ite_pos' rfl]
  have f2 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero) ⟨rest, .half [0, n' + 1 + 4] [2] .add .zero⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 1) :=
    XMach.act_half (R := addZero.toX) (by
      rw [ite_pos' (show assoc [2] (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).agents = some Arith.zero ∧
        ([0, n' + 1 + 4] : Id) ≠ [2] from ⟨hZ3, by ports_differ⟩)]
      rfl)
  have h3 : assoc [3] ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).agents = some Arith.zero :=
    F8.agent (e := ([3], Arith.zero)) (by
      rw [F8.agents]
      exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self))
  have r2 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .idle⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨[([t1], .succ), ([t2], .succ)], .look [3] .zero⟩, 0) := XMach.act_idle_pos (e := ([3], Arith.zero)) h3
  have f3 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨rest, .write [] [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨rest, .write [] [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩, 0) := rfl
  have hl6 : assoc (([3], 0) : Port) ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).wires) = some ([4], 1) :=
    assoc_eq_of_unique ((F8.up S (j := 3) (by omega) (by omega) _).2 rfl)
      (fun q' hq => (F8.up S (j := 3) (by omega) (by omega) q').1 hq)
  rw [assoc_cons_ne _ (by ports_differ)] at hl6
  have r3 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨[([t1], .succ), ([t2], .succ)], .look [3] .zero⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨[([t1], .succ), ([t2], .succ)], .seek [3] .zero ([3], 0) ([4], 1)⟩, 0) := XMach.act_look hl6
  have f4 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨rest, .write [] [(([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨rest, .write [] []⟩, 0) := rfl
  have r4 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t1], .succ), ([t2], .succ)], .seek [3] .zero ([3], 0) ([4], 1)⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[([t1], .succ), ([t2], .succ)], .idle⟩, 0) :=
    XMach.act_seek_stop rfl (nextSeg_none fun q hq =>
      (F8.down S (j := 3) (by omega) (by omega) q).1 hq)
  have f5 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨rest, .write [] []⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have r5 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t1], .succ), ([t2], .succ)], .idle⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[([t2], .succ)], .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([t1], Arith.succ)) (by
      show ¬ assoc [t1] ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = some Arith.succ
      rw [F8.no_top ht1]
      exact fun h => by cases h)
  have r6 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨[([t2], .succ)], .idle⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[], .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([t2], Arith.succ)) (by
      show ¬ assoc [t2] ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = some Arith.succ
      rw [F8.no_top ht2]
      exact fun h => by cases h)
  have g0 : XMach.act xsys X ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩ =
      (X, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩, 0) :=
    XMach.act_idle_pos (e := ([2], Arith.zero)) B.zero
  have g1 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([2], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look (by
      under_wires
      exact B.by_look2)
  have g2 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]) ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([2], 0) ([n' + 1 + 4], 1)⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]), ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([n' + 1 + 4], 1) ([0, n' + 1 + 4], 0)⟩, 0) :=
    XMach.act_seek_next (seek_aux_none _ _ 1 (by decide)) (by
      under_wires
      exact B.by_seek2)
  have g3 : XMach.act xsys (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨([3], .zero) :: [([j], γ)], .seek [2] .zero ([n' + 1 + 4], 1) ([0, n' + 1 + 4], 0)⟩ =
      ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨([3], .zero) :: [([j], γ)], .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans (by
      under_agents
      exact assoc_takeAgent_self _ _)) (by
      under_wires
      exact B.by_stopA)
  have g4 : XMach.act xsys ((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨([3], .zero) :: [([j], γ)], .idle⟩ =
      (((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨[([j], γ)], .look [3] .zero⟩, 0) :=
    XMach.act_idle_pos (e := ([3], Arith.zero)) (by
      under_agents
      exact B.by_three)
  have sw : Sweeps3 ⟨X, [⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩, ⟨[([3], .zero), ([t1], .succ), ([t2], .succ)], .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩
      ⟨((((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putAgent [2] .zero).takeAgent [2]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), [⟨rest, .write [] []⟩, ⟨[([j], γ)], .look [3] .zero⟩, ⟨[([t1], .succ), ([t2], .succ)], .idle⟩]⟩ 5 :=
    .step f0 g0 r0 (.step f1 g1 r1 (.step f2 g2 r2 (.step f3 g3 r3 (.step f4 g4 r4 (.refl _)))))
  have sF := F8.pass_stays S (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl
    (Stays.step (fun h => by
      injection h with _ h2
      cases h2) f5 sF)
    (F8.bystander_b (by omega) hj γ)
    (Stays.step (fun h => by cases h) r5 (Stays.step (fun h => by cases h) r6 (Stays.refl _)))
    (by omega) (by omega) (by omega) (by omega)

/-- **Three threads in turn, the third in the race and the second past the
first thread's last round, to the action.**  On the net for `(m + 1) + n`,
with `m` from four on: when the third thread comes to the zero of the first
argument at one of the ten moments of the race and the second comes to it
after them, the second is three or four actions behind the third; it reads
on to the last adder, finds it gone, and goes on reading to the end of its
list, eight actions after it came to that zero.  The work of the whole run
is exactly that of the race of the first and the third thread and the
actions of the second, and one more when the first thread keeps the
pair. -/
theorem three_threads_race_third (m n : Nat) (hm : 4 ≤ m)
    (h1 : turnAt m n 1 ≤ 17 * m + 16) (h2 : 17 * m + 17 ≤ turnAt m n 0) :
    (XMach.init (sum (m + 1) n) 3).Total xsys (fun i => i % 3)
      (raceWork m n (turnAt m n 1 - (17 * m + 7)) +
        (if turnAt m n 1 = 17 * m + 15 then 1 else 0) + (turnAt m n 0 + 8)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
    unfold turnAt at h2
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
  rw [eA1] at h2 ⊢
  rw [eA2] at h1 ⊢
  obtain ⟨d, hd⟩ : ∃ d, 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 = 17 * (m' + 1) + 7 + d :=
    ⟨3 * (m' + 1 - 1) + 3 * n' + 5 + K2 - (17 * (m' + 1) + 7), by omega⟩
  have e0 : 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 - (17 * (m' + 1) + 7) = d := by omega
  rw [e0]
  have r1 := turn_reader_ready (m' + 1) n' 1 K2 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have q0 := turn_reader_at_zero (m' + 1) n' 0 K1 (by omega) (by omega) (by omega)
  obtain ⟨X, rest, B⟩ := race_base (m' + 1) (n' + 1)
  obtain ⟨-, s17, s18, s19, s20⟩ := B.states
  have hinit : XMach.init (sum (m' + 1 + 1) (n' + 1)) 3 = ⟨(sum (m' + 1 + 1) (n' + 1)), [⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩,
      ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩,
      ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩]⟩ :=
    (XMach.init_succ (sum (m' + 1 + 1) (n' + 1)) 2).trans (by
      rw [← turn_list_succ (m' + 1) n' 0 (by omega), ← turn_list_succ (m' + 1) n' 1 (by omega)]
      rfl)
  rw [hinit]
  have hK : K1 = K2 ∨ K1 = K2 + 1 := by omega
  rcases hK with hK | hK
  · have hal := solo_alive_zero (m' + 1) (n' + 1) (j := 2) (u := 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1) (by omega) (by omega)
      (by omega) (sum_zero_agent (m' + 1) (n' + 1))
    have q1 := q0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
    have hd' : d = 7 ∨ d = 8 ∨ d = 9 := by omega
    rcases hd' with rfl | rfl | rfl
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 7 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 7 by omega)
      have es := solo_at s18 (show 17 * (m' + 1) + 11 + 7 = 17 * (m' + 1) + 18 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 7)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 7)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 7)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 7 = 44 * (m' + 1) + 6 * (n' + 1) + 64 := rfl
      exact (total_after3 tr wk (race3_d7_a B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR, ite_neg' (by omega)]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 8 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 8 by omega)
      have es := solo_at s19 (show 17 * (m' + 1) + 11 + 8 = 17 * (m' + 1) + 19 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 8)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 8)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 8)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 8 = 39 * (m' + 1) + 3 * (n' + 1) + 60 := rfl
      exact (total_after3 tr wk (race3_d8_a B (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (t1 := n' + 1 + 3 + (m' + 1 - 1 + 1) + 1) (t2 := n' + 1 + 3 + (m' + 1 - 1) + 1) (by omega) (by omega) (by omega) .succ)).cast (by
        rw [eR, ite_pos' (by omega)]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 9 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 9 by omega)
      have es := solo_at s20 (show 17 * (m' + 1) + 11 + 9 = 17 * (m' + 1) + 20 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 9)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 9)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 9)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 9 = 44 * (m' + 1) + 6 * (n' + 1) + 68 := rfl
      exact (total_after3 tr wk (race3_d9_a B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR, ite_neg' (by omega)]
        omega)
  · have hd' : d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
    rcases hd' with rfl | rfl | rfl | rfl
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 6 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 6 by omega)
      have es := solo_at s17 (show 17 * (m' + 1) + 11 + 6 = 17 * (m' + 1) + 17 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 6)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .look [0, n' + 1 + 4] .add⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 6)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 6)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 6 = 44 * (m' + 1) + 6 * (n' + 1) + 63 := rfl
      exact (total_after3 tr wk (race3_d6_b B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR, ite_neg' (by omega)]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 7 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 7 by omega)
      have es := solo_at s18 (show 17 * (m' + 1) + 11 + 7 = 17 * (m' + 1) + 18 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 7)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 7)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 7)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 7 = 44 * (m' + 1) + 6 * (n' + 1) + 64 := rfl
      exact (total_after3 tr wk (race3_d7_b B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR, ite_neg' (by omega)]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 8 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 8 by omega)
      have es := solo_at s19 (show 17 * (m' + 1) + 11 + 8 = 17 * (m' + 1) + 19 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 8)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 8)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 8)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 8 = 39 * (m' + 1) + 3 * (n' + 1) + 60 := rfl
      exact (total_after3 tr wk (race3_d8_b B (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (t1 := n' + 1 + 3 + (m' + 1 - 1 + 1) + 1) (t2 := n' + 1 + 3 + (m' + 1 - 1) + 1) (by omega) (by omega) (by omega) .succ)).cast (by
        rw [eR, ite_pos' (by omega)]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 9 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 9 by omega)
      have es := solo_at s20 (show 17 * (m' + 1) + 11 + 9 = 17 * (m' + 1) + 20 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 9)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .ready [0, n' + 1 + 4] [2] .add .zero⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 9)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 9)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 9 = 44 * (m' + 1) + 6 * (n' + 1) + 68 := rfl
      exact (total_after3 tr wk (race3_d9_b B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR, ite_neg' (by omega)]
        omega)

example : (XMach.init (sum 7 33) 3).Total xsys (fun i => i % 3) 653 :=
  (three_threads_race_third 6 33 (by decide) (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 8 38) 3).Total xsys (fun i => i % 3) 594 :=
  (three_threads_race_third 7 38 (by decide) (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 5 24) 3).Total xsys (fun i => i % 3) 383 :=
  (three_threads_race_third 4 24 (by decide) (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 14 66) 3).Total xsys (fun i => i % 3) 1285 :=
  (three_threads_race_third 13 66 (by decide) (by decide) (by decide)).cast (by decide)

/-- A search that finds no segment finds none among fewer segments. -/
theorem nextSeg_none_mem {ws : List (Port × Port)} {c p : Port} (h : nextSeg ws c p = none)
    (q : Port) (hq : (c, q) ∈ ws) : q = p := by
  by_cases e : q = p
  · exact e
  · exact absurd h (nextSeg_ne_none hq e)

theorem nextSeg_none_sub {l l' : List (Port × Port)} {c p : Port} (h : nextSeg l c p = none)
    (hs : ∀ q, (c, q) ∈ l' → (c, q) ∈ l) : nextSeg l' c p = none :=
  nextSeg_none fun q hq => nextSeg_none_mem h q (hs q hq)

/-- The segment of the zero of the second argument, in a memory the rounds
leave. -/
theorem Final.look3 {m n : Nat} {Y : XNet Arith}
    (F : Final n (sum (m + 1) n) Y (n + 3 + m + 1) m) (hn : 1 ≤ n) :
    assoc (([3], 0) : Port) Y.wires = some ([4], 1) :=
  assoc_eq_of_unique ((F.up (snd_sum (m + 1) n) (j := 3) (by omega) (by omega) _).2 rfl)
    (fun q' hq => (F.up (snd_sum (m + 1) n) (j := 3) (by omega) (by omega) q').1 hq)

/-- **The third thread takes the zero at the first moment it can, three
segments before the end of the round of the first**, with the second thread, which has read the segment of that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d0_a {m' n' : Nat} {V : XNet Arith} {p5 q5 p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith)
    (h0 : assoc (([2], 0) : Port) (V.putLink p5 q5).wires = some ([n' + 1 + 4], 1))
    (h1 : nextSeg ((V.putLink p5 q5).putLink p6 q6).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0)) :
    (⟨V, [⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 30 + 7) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := by
    refine final_of B.hist ?_ fun e => ?_
    · rw [show ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = (((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents.filter fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) from rfl, filter_ne_comm]
      exact B.hist.final.agents
    · show e ∈ (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (p8, q8) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) ::
          (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ↔
        e ∈ (p8, q8) :: (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ∨
          e ∈ [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]
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
      ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f4 : XMach.act xsys ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨todo, .write [] []⟩ =
      (((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    h0
    h1
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (nextSeg_none_sub B.by_stopA fun q hq => List.mem_cons_of_mem _ hq)
    (by
      under_agents
      exact B.by_three)
    (F.look3 (by omega))
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sR (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero at the first moment it can, three
segments before the end of the round of the first**, with the second thread, about to pop that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d0_b {m' n' : Nat} {V : XNet Arith} {p5 q5 p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith)
    (h1 : assoc (([2], 0) : Port) ((V.putLink p5 q5).putLink p6 q6).wires = some ([n' + 1 + 4], 1))
    (h2 : nextSeg (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0)) :
    (⟨V, [⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 30 + 8) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := by
    refine final_of B.hist ?_ fun e => ?_
    · rw [show ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents = (((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents.filter fun e => decide (e.1 ≠ [2])).filter
        (fun e => decide (e.1 ≠ [0, n' + 1 + 4])) from rfl, filter_ne_comm]
      exact B.hist.final.agents
    · show e ∈ (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (p8, q8) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) ::
          (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ↔
        e ∈ (p8, q8) :: (p7, q7) :: (p6, q6) :: (V.putLink p5 q5).wires ∨
          e ∈ [(([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)), (([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1))]
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
      ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f4 : XMach.act xsys ((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨todo, .write [] []⟩ =
      (((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨((((((((V.putLink p5 q5).takeAgent [2]).putLink p6 q6).takeAgent [0, n' + 1 + 4]).putLink p7 q7).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink p8 q8).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)).agents, .idle⟩, 0) := rfl
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    h1
    h2
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (nextSeg_none_sub B.by_stopA fun q hq => by
      have hq' : (([0, n' + 1 + 4], 0), q) ∈ (p8, q8) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).wires := hq
      show (([0, n' + 1 + 4], 0), q) ∈ (p8, q8) :: (((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).wires
      rcases List.mem_cons.1 hq' with e | hq'
      · rw [e]
        exact List.mem_cons_self
      · rcases List.mem_cons.1 hq' with e | hq'
        · simp at e
        · exact List.mem_cons_of_mem _ hq')
    (by
      under_agents
      exact B.by_three)
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sR (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero two segments before the end of the round
of the first**, with the second thread, which has read the segment of that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d1_a {m' n' : Nat} {V : XNet Arith} {p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (((V.putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith)
    (h0 : assoc (([2], 0) : Port) (V.putLink p6 q6).wires = some ([n' + 1 + 4], 1))
    (h1 : nextSeg ((V.putLink p6 q6).putLink p7 q7).wires ([n' + 1 + 4], 1) ([2], 0) = some ([0, n' + 1 + 4], 0)) :
    (⟨V, [⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 29 + 7) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).agents = resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((V.putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p6 q6).takeAgent [2]) ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨todo, .write [] []⟩ =
      (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f4 : XMach.act xsys (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    h0
    h1
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
    (F.look3 (by omega))
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero two segments before the end of the round
of the first**, with the second thread, about to pop that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d1_b {m' n' : Nat} {V : XNet Arith} {p6 q6 p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (((V.putLink p6 q6).putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith)
    (h1 : assoc (([2], 0) : Port) ((V.putLink p6 q6).putLink p7 q7).wires = some ([n' + 1 + 4], 1)) :
    (⟨V, [⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 29 + 8) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).agents = resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ =
      ((V.putLink p6 q6), ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p6 q6).takeAgent [2]) ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f3 : XMach.act xsys ((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨todo, .write [] []⟩ =
      (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f4 : XMach.act xsys (((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((((V.putLink p6 q6).takeAgent [2]).putLink p7 q7).takeAgent [0, n' + 1 + 4]).putLink p8 q8).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    h1
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first writes the last segment but
one of its round**, with the second thread, which has read the segment of that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d2_a {m' n' : Nat} {V : XNet Arith} {p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((V.putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith)
    (h0 : assoc (([2], 0) : Port) (V.putLink p7 q7).wires = some ([n' + 1 + 4], 1)) :
    (⟨V, [⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 7) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).agents = resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((V.putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p7 q7).takeAgent [2]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] []⟩ =
      (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f3 : XMach.act xsys (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    h0
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
    (F.look3 (by omega))
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first writes the last segment but
one of its round**, with the second thread, about to pop that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d2_b {m' n' : Nat} {V : XNet Arith} {p7 q7 p8 q8 : Port}
    {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) ((V.putLink p7 q7).putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨V, [⟨todo, .write [] [(p7, q7), (p8, q8)]⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 8) := by
  have F : Final (n' + 1) (sum (m' + 1 + 1) (n' + 1)) ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1))
      (n' + 1 + 3 + (m' + 1) + 1) (m' + 1) := B.final rfl rfl
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hfin : ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).agents = resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]) := F.agents
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ =
      ((V.putLink p7 q7), ⟨todo, .write [] [(p8, q8)]⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p7 q7).takeAgent [2]) ⟨todo, .write [] [(p8, q8)]⟩ =
      ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f2 : XMach.act xsys ((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]) ⟨todo, .write [] []⟩ =
      (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) := by
    rw [← hfin]
    rfl
  have f3 : XMach.act xsys (((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys ((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      (((((((V.putLink p7 q7).takeAgent [2]).putLink p8 q8).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2)
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first writes the last segment of
its round**, with the second thread, which has read the segment of that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d3_a {m' n' : Nat} {V : XNet Arith} {p8 q8 : Port} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (V.putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨V, [⟨todo, .write [] [(p8, q8)]⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 7) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hM1 : ((V.putLink p8 q8).takeAgent [2]).agents = ([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])) := by
    show List.filter (fun e => decide (e.1 ≠ [2])) (V.putLink p8 q8).agents = _
    rw [B.agents, List.filter_cons_of_pos (by simp), rest_filter_two]
  have gA : assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] (((V.putLink p8 q8).agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p8, q8)]⟩ =
      ((V.putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p8 q8).takeAgent [2]) ⟨todo, .write [] []⟩ =
      (((V.putLink p8 q8).takeAgent [2]), ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])), .idle⟩, 0) := by
    rw [← hM1]
    rfl
  have f2 : XMach.act xsys (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])), .idle⟩ =
      ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([0, n' + 1 + 4], Arith.add)) (by
      show ¬ assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = some Arith.add
      rw [gA]
      exact fun h => by cases h)
  have f3 : XMach.act xsys ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2)
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
    (F.look3 (by omega))
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first writes the last segment of
its round**, with the second thread, about to pop that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d3_b {m' n' : Nat} {V : XNet Arith} {p8 q8 : Port} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) (V.putLink p8 q8) rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨V, [⟨todo, .write [] [(p8, q8)]⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 28 + 8) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]))
  have hM1 : ((V.putLink p8 q8).takeAgent [2]).agents = ([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])) := by
    show List.filter (fun e => decide (e.1 ≠ [2])) (V.putLink p8 q8).agents = _
    rw [B.agents, List.filter_cons_of_pos (by simp), rest_filter_two]
  have gA : assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = none := by
    show assoc [0, n' + 1 + 4] (((V.putLink p8 q8).agents.filter fun e => decide (e.1 ≠ [2])).filter
      fun e => decide (e.1 ≠ [0, n' + 1 + 4])) = none
    rw [assoc_filter_ne, ite_pos' rfl]
  have f0 : XMach.act xsys V ⟨todo, .write [] [(p8, q8)]⟩ =
      ((V.putLink p8 q8), ⟨todo, .write [] []⟩, 0) := rfl
  have f1 : XMach.act xsys ((V.putLink p8 q8).takeAgent [2]) ⟨todo, .write [] []⟩ =
      (((V.putLink p8 q8).takeAgent [2]), ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])), .idle⟩, 0) := by
    rw [← hM1]
    rfl
  have f2 : XMach.act xsys (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)])), .idle⟩ =
      ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩, 0) :=
    XMach.act_idle_neg (e := ([0, n' + 1 + 4], Arith.add)) (by
      show ¬ assoc [0, n' + 1 + 4] (((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).agents = some Arith.add
      rw [gA]
      exact fun h => by cases h)
  have f3 : XMach.act xsys ((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ (sndL (n' + 1) ++ [([3], .zero)]), .idle⟩ =
      (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩, 0) :=
    XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) B.res2
  have f4 : XMach.act xsys (((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .look [0, 0, n' + 1 + 3 + 2] .succ⟩ =
      ((((((V.putLink p8 q8).takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3 + 1) m' ++ (sndL (n' + 1) ++ [([3], .zero)]), .seek [0, 0, n' + 1 + 3 + 2] .succ ([0, 0, n' + 1 + 3 + 2], 0) ([0, n' + 1 + 3 + 2], 2)⟩, 0) :=
    XMach.act_look k2
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2)
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
  have sF := sE2.trans F.pass_fin_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first starts over after its round
on the lowest successor**, with the second thread, which has read the segment of that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d4_a {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨todo, .write [] []⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 31 + 7) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨todo, .write [] []⟩ =
      (X, ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩, 0) := by
    rw [← B.agents]
    rfl
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩, 0) :=
    XMach.act_idle_pos (e := ([0, n' + 1 + 4], Arith.add)) B.adder1
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl (by
      show nextSeg ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([n' + 1 + 4], 1) ([0, n' + 1 + 4], 0) = _
      rw [nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.seek)
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) (by
      show nextSeg ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([2], 0)
        ([n' + 1 + 4], 1) = none
      rw [nextSeg_cons_ne _ _ _ (by ports_differ), nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.stop)
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2)
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
    (F.look3 (by omega))
  have sF := (Stays.step (fun h => by cases h)
    (XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1)
    (Stays.step (fun h => by
      injection h with _ h2
      cases h2) (XMach.act_look k2) sE2)).trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first starts over after its round
on the lowest successor**, with the second thread, about to pop that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d4_b {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (todo l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨todo, .write [] []⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 31 + 8) := by
  have hr := B.rest
  subst hr
  have F := B.final_read
  obtain ⟨k1, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have f0 : XMach.act xsys X ⟨todo, .write [] []⟩ =
      (X, ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩, 0) := by
    rw [← B.agents]
    rfl
  have f1 : XMach.act xsys (X.takeAgent [2]) ⟨([0, n' + 1 + 4], .add) :: (resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1)), .idle⟩ =
      ((X.takeAgent [2]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩, 0) :=
    XMach.act_idle_pos (e := ([0, n' + 1 + 4], Arith.add)) B.adder1
  have f2 : XMach.act xsys ((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .look [0, n' + 1 + 4] .add⟩ =
      (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩, 0) :=
    XMach.act_look B.look
  have f3 : XMach.act xsys (((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([0, n' + 1 + 4], 0) ([n' + 1 + 4], 1)⟩ =
      ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩, 0) :=
    XMach.act_seek_next rfl (by
      show nextSeg ((([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([n' + 1 + 4], 1) ([0, n' + 1 + 4], 0) = _
      rw [nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.seek)
  have f4 : XMach.act xsys ((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)) ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .seek [0, n' + 1 + 4] .add ([n' + 1 + 4], 1) ([2], 0)⟩ =
      (((((X.takeAgent [2]).takeAgent [0, n' + 1 + 4]).putLink ([0, n' + 1 + 4], 1) ([0, n' + 1 + 4], 2)).putLink ([0, n' + 1 + 4], 2) ([0, n' + 1 + 4], 1)), ⟨resL (n' + 1 + 3) (m' + 1) ++ tailA (n' + 1), .idle⟩, 0) :=
    XMach.act_seek_stop ((ite_pos' rfl).trans B.zero2) (by
      show nextSeg ((([0, n' + 1 + 4], 2), ([0, n' + 1 + 4], 1)) :: (([0, n' + 1 + 4], 1), ([0, n' + 1 + 4], 2)) :: X.wires) ([2], 0)
        ([n' + 1 + 4], 1) = none
      rw [nextSeg_cons_ne _ _ _ (by ports_differ), nextSeg_cons_ne _ _ _ (by ports_differ)]
      exact B.stop)
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2)
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
  have sF := (Stays.step (fun h => by cases h)
    (XMach.act_idle_pos (e := ([0, 0, n' + 1 + 3 + 2], Arith.succ)) k1)
    (Stays.step (fun h => by
      injection h with _ h2
      cases h2) (XMach.act_look k2) sE2)).trans F.pass_two_tail
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first is about to pop the last
adder**, with the second thread, which has read the segment of that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d5_a {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨X.agents, .idle⟩, ⟨([3], .zero) :: [([j], γ)], .look [2] .zero⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 30 + 7) := by
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
  have sw := race_wins3_a (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2)
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
    (F.look3 (by omega))
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans B.pass_two
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_a (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **The third thread takes the zero as the first is about to pop the last
adder**, with the second thread, about to pop that zero,
reading between the two: it reads on to the last adder and finds it gone.
Three threads in turn, to the end of the run. -/
theorem race3_d5_b {m' n' : Nat} {X : XNet Arith} {rest : List (Id × Arith)}
    (B : RaceBase (m' + 1) (n' + 1) X rest) (l : List (Id × Arith)) {j : Nat}
    (hj : n' + 1 + 3 < j) (γ : Arith) :
    (⟨X, [⟨X.agents, .idle⟩, ⟨([2], .zero) :: ([3], .zero) :: [([j], γ)], .idle⟩,
      ⟨l, .ready [2] [0, n' + 1 + 4] .zero .add⟩]⟩ :
      XMach Arith).Total xsys (fun i => i % 3)
      (10 * (m' + 1) + 6 * (n' + 1) + 30 + 8) := by
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
  have sw := race_wins3_b (l := l) (tq := [([j], γ)]) f0 B.zero f1 B.adder1 f2 f3 f4
    (by
      under_wires
      exact B.by_look2)
    (by
      under_wires
      exact B.by_seek2)
    (by
      under_agents
      exact assoc_takeAgent_self _ _)
    (by
      under_wires
      exact B.by_stopA)
    (by
      under_agents
      exact B.by_three)
  obtain ⟨-, k2, sE2, -⟩ := F.first_res (resL (n' + 1 + 3 + 1) m' ++ tailA (n' + 1))
  have sF := (Stays.step (fun h => by
    injection h with _ h2
    cases h2) (XMach.act_look k2) sE2).trans B.pass_two
  have sR := F.pass_stays (snd_sum (m' + 1 + 1) (n' + 1)) (sum_fresh (m' + 1 + 1) (n' + 1))
  exact total3_sweeps sw rfl sF (F.bystander_b (by omega) hj γ) sR (by omega) (by omega) (by omega)
    (by omega)

/-- **Three threads in turn, the second and the third both at the zero of the
first argument during the ten moments of the race, to the action.**  On the
net for `(m + 1) + n`, with `m` from four on: the third thread is ready to
take that zero when the second, three or four actions behind it, has just
popped it or is about to.  The third takes the pair; the second reads on to
the last adder, finds it gone, and reads to the end of its list, eight
actions after it came to that zero.  The work of the whole run is exactly
that of the race of the first and the third thread and the actions of the
second. -/
theorem three_threads_race_both (m n : Nat) (hm : 4 ≤ m)
    (h1 : 17 * m + 7 ≤ turnAt m n 1) (h2 : turnAt m n 0 ≤ 17 * m + 16) :
    (XMach.init (sum (m + 1) n) 3).Total xsys (fun i => i % 3)
      (raceWork m n (turnAt m n 1 - (17 * m + 7)) + (turnAt m n 0 + 8)) := by
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
  rw [eA1] at h2 ⊢
  rw [eA2] at h1 ⊢
  obtain ⟨d, hd⟩ : ∃ d, 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 = 17 * (m' + 1) + 7 + d :=
    ⟨3 * (m' + 1 - 1) + 3 * n' + 5 + K2 - (17 * (m' + 1) + 7), by omega⟩
  have e0 : 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 - (17 * (m' + 1) + 7) = d := by omega
  rw [e0]
  have r1 := turn_reader_ready (m' + 1) n' 1 K2 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have q0 := turn_reader_at_zero (m' + 1) n' 0 K1 (by omega) (by omega) (by omega)
  obtain ⟨V, todo, rest, p5, q5, p6, q6, p7, q7, p8, q8, B, s11, s12, s13, s14, s15⟩ :=
    race_write (m' + 1) (n' + 1) (by omega)
  obtain ⟨s16, s17, -, -, -⟩ := B.states
  have lk12 := solo_look_two (m' + 1) (n' + 1) (17 * (m' + 1) + 12)
  rw [s12] at lk12
  have lk13 := solo_look_two (m' + 1) (n' + 1) (17 * (m' + 1) + 13)
  rw [s13] at lk13
  have lk14 := solo_look_two (m' + 1) (n' + 1) (17 * (m' + 1) + 14)
  rw [s14] at lk14
  have sk13 := (solo_seek_two (m' + 1) (n' + 1) (by omega) (17 * (m' + 1) + 13)).1 (by omega)
  rw [s13] at sk13
  have sk14 := (solo_seek_two (m' + 1) (n' + 1) (by omega) (17 * (m' + 1) + 14)).1 (by omega)
  rw [s14] at sk14
  have hinit : XMach.init (sum (m' + 1 + 1) (n' + 1)) 3 = ⟨(sum (m' + 1 + 1) (n' + 1)), [⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩,
      ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩,
      ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
        (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩]⟩ :=
    (XMach.init_succ (sum (m' + 1 + 1) (n' + 1)) 2).trans (by
      rw [← turn_list_succ (m' + 1) n' 0 (by omega), ← turn_list_succ (m' + 1) n' 1 (by omega)]
      rfl)
  rw [hinit]
  have hK : K1 = K2 ∨ K1 = K2 + 1 := by omega
  rcases hK with hK | hK
  · have hal := solo_alive_zero (m' + 1) (n' + 1) (j := 2) (u := 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1) (by omega) (by omega)
      (by omega) (sum_zero_agent (m' + 1) (n' + 1))
    have q1 := q0.step (XMach.act_idle_pos (e := ([2], Arith.zero)) hal)
    have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 0 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 0 by omega)
      have es := solo_at s11 (show 17 * (m' + 1) + 11 + 0 = 17 * (m' + 1) + 11 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 0)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 0)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 0)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 0 = 44 * (m' + 1) + 6 * (n' + 1) + 52 := rfl
      exact (total_after3 tr wk (race3_d0_a B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ lk12 sk13)).cast (by
        rw [eR]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 1 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 1 by omega)
      have es := solo_at s12 (show 17 * (m' + 1) + 11 + 1 = 17 * (m' + 1) + 12 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 1)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 1)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 1)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 1 = 44 * (m' + 1) + 6 * (n' + 1) + 53 := rfl
      exact (total_after3 tr wk (race3_d1_a B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ lk13 sk14)).cast (by
        rw [eR]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 2 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 2 by omega)
      have es := solo_at s13 (show 17 * (m' + 1) + 11 + 2 = 17 * (m' + 1) + 13 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 2)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 2)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 2)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 2 = 44 * (m' + 1) + 6 * (n' + 1) + 54 := rfl
      exact (total_after3 tr wk (race3_d2_a B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ lk14)).cast (by
        rw [eR]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 3 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 3 by omega)
      have es := solo_at s14 (show 17 * (m' + 1) + 11 + 3 = 17 * (m' + 1) + 14 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 3)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 3)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 3)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 3 = 44 * (m' + 1) + 6 * (n' + 1) + 56 := rfl
      exact (total_after3 tr wk (race3_d3_a B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 4 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 4 by omega)
      have es := solo_at s15 (show 17 * (m' + 1) + 11 + 4 = 17 * (m' + 1) + 15 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 4)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] []⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 4)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 4)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 4 = 44 * (m' + 1) + 6 * (n' + 1) + 61 := rfl
      exact (total_after3 tr wk (race3_d4_a B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 5 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 5 by omega)
      have es := solo_at s16 (show 17 * (m' + 1) + 11 + 5 = 17 * (m' + 1) + 16 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 5)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents, .idle⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        rw [B.agents]
        exact fun h => by cases h
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 5)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 5)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 5 = 44 * (m' + 1) + 6 * (n' + 1) + 62 := rfl
      exact (total_after3 tr wk (race3_d5_a B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)
    · have q' := q1.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 + 1 = 17 * (m' + 1) + 11 + 6 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 6 by omega)
      have es := solo_at s17 (show 17 * (m' + 1) + 11 + 6 = 17 * (m' + 1) + 17 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 6)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨rest, .look [0, n' + 1 + 4] .add⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 6)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          injection e with _ e2
          cases e2)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 6)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 6 = 44 * (m' + 1) + 6 * (n' + 1) + 63 := rfl
      exact (total_after3 tr wk (race3_d6_a B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)
  · have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 0 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 0 by omega)
      have es := solo_at s11 (show 17 * (m' + 1) + 11 + 0 = 17 * (m' + 1) + 11 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 0)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p5, q5), (p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 0)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 0)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 0 = 44 * (m' + 1) + 6 * (n' + 1) + 52 := rfl
      exact (total_after3 tr wk (race3_d0_b B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ lk13 sk14)).cast (by
        rw [eR]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 1 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 1 by omega)
      have es := solo_at s12 (show 17 * (m' + 1) + 11 + 1 = 17 * (m' + 1) + 12 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 1)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p6, q6), (p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 1)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 1)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 1 = 44 * (m' + 1) + 6 * (n' + 1) + 53 := rfl
      exact (total_after3 tr wk (race3_d1_b B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ lk14)).cast (by
        rw [eR]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 2 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 2 by omega)
      have es := solo_at s13 (show 17 * (m' + 1) + 11 + 2 = 17 * (m' + 1) + 13 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 2)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p7, q7), (p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 2)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 2)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 2 = 44 * (m' + 1) + 6 * (n' + 1) + 54 := rfl
      exact (total_after3 tr wk (race3_d2_b B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 3 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 3 by omega)
      have es := solo_at s14 (show 17 * (m' + 1) + 11 + 3 = 17 * (m' + 1) + 14 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 3)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] [(p8, q8)]⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 3)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 3)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 3 = 44 * (m' + 1) + 6 * (n' + 1) + 56 := rfl
      exact (total_after3 tr wk (race3_d3_b B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 4 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 4 by omega)
      have es := solo_at s15 (show 17 * (m' + 1) + 11 + 4 = 17 * (m' + 1) + 15 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 4)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨todo, .write [] []⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        exact fun h => by
          injection h with _ h2
          cases h2
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 4)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 4)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 4 = 44 * (m' + 1) + 6 * (n' + 1) + 61 := rfl
      exact (total_after3 tr wk (race3_d4_b B todo _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)
    · have q' := q0.cast (show 3 * (m' + 1 - 0) + 3 * n' + 5 + K1 = 17 * (m' + 1) + 11 + 5 by omega)
      have r' := r1.cast (show 3 * (m' + 1 - 1) + 3 * n' + 5 + K2 + 4 = 17 * (m' + 1) + 11 + 5 by omega)
      have es := solo_at s16 (show 17 * (m' + 1) + 11 + 5 = 17 * (m' + 1) + 16 by omega)
      have hb0 : (XMach.solo xsys (sum (m' + 1 + 1) (n' + 1)) ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩ (17 * (m' + 1) + 11 + 5)).2 ≠ ⟨[], .idle⟩ := by
        rw [es]
        show (⟨((((V.putLink p5 q5).putLink p6 q6).putLink p7 q7).putLink p8 q8).agents, .idle⟩ : XThread Arith) ≠ ⟨[], .idle⟩
        rw [B.agents]
        exact fun h => by cases h
      have hb1 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 5)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 0) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 0 + (0 + 1))).take (0 + 1)))), .idle⟩) (fun e => by
          rw [q'.1] at e
          cases e)
      have hb2 := reader_busy_upto (X := (sum (m' + 1 + 1) (n' + 1))) (F0 := ⟨(sum (m' + 1 + 1) (n' + 1)).agents, .idle⟩) (b := 17 * (m' + 1) + 11 + 5)
        (T0 := ⟨chainL (n' + 1) (m' + 1 - 1) ++ (([n' + 1 + 3], .succ) :: (sndL n' ++
              (([1], .add) :: ([2], .zero) :: ([3], .zero) :: (chainL (n' + 1) (m' + 1 - 1 + (1 + 1))).take (1 + 1)))), .idle⟩) (fun e => by
          rw [r'.1] at e
          injection e with _ e2
          cases e2)
      obtain ⟨tr, wk⟩ := three_entry q' r' hb0 (fun a ha => hb1 a (by omega))
        (fun a ha => hb2 a (by omega))
      rw [es] at tr
      have eR : raceWork (m' + 1) (n' + 1) 5 = 44 * (m' + 1) + 6 * (n' + 1) + 62 := rfl
      exact (total_after3 tr wk (race3_d5_b B _ (j := n' + 1 + 3 + (m' + 1 - 0) + 1) (by omega) .succ)).cast (by
        rw [eR]
        omega)

/-- **Three threads in turn with the third in the race, to the action.**
On the net for `(m + 1) + n`, with `m` from four on, when the third thread
comes to the zero of the first argument after `17 * m + 7 + d` actions,
`d` up to nine: the second thread, three or four actions behind it, takes
nothing, and the work of the whole run is exactly `raceWork m n d` for the
first and the third thread and `turnAt m n 0 + 8` for the second, and one
more when the first thread keeps the pair. -/
theorem three_threads_race_late (m n : Nat) (hm : 4 ≤ m)
    (h1 : 17 * m + 7 ≤ turnAt m n 1) (h2 : turnAt m n 1 ≤ 17 * m + 16) :
    (XMach.init (sum (m + 1) n) 3).Total xsys (fun i => i % 3)
      (raceWork m n (turnAt m n 1 - (17 * m + 7)) +
        (if turnAt m n 1 = 17 * m + 15 then 1 else 0) + (turnAt m n 0 + 8)) := by
  by_cases h : turnAt m n 0 ≤ 17 * m + 16
  · have hne : ¬ turnAt m n 1 = 17 * m + 15 := by
      intro e
      unfold turnAt at h e
      omega
    rw [ite_neg' hne]
    exact (three_threads_race_both m n hm h1 h).cast (by omega)
  · exact three_threads_race_third m n hm h2 (by omega)

/-- **What three threads in turn do in all on the net for `(m + 1) + n`**:
the race of the first and the third thread with the second reading beside
them, the race of the first and the second with the third reading, or the
work of one thread and the actions of two readers. -/
def threeWork (m n : Nat) : Nat :=
  if 17 * m + 7 ≤ turnAt m n 1 ∧ turnAt m n 1 ≤ 17 * m + 16 then
    raceWork m n (turnAt m n 1 - (17 * m + 7)) +
      (if turnAt m n 1 = 17 * m + 15 then 1 else 0) + (turnAt m n 0 + 8)
  else if 17 * m + 7 ≤ turnAt m n 0 ∧ turnAt m n 0 ≤ 17 * m + 16 then
    raceWork m n (turnAt m n 0 - (17 * m + 7)) + turnRest m n 1
  else soloWork (m + 1) n + turnSum m n 2

/-- **Three threads in turn, every size, to the action.**  On the net for
`(m + 1) + n`, with `m` from four on and `19 ≤ 3 * m + 3 * n`, three
threads acting in turn make exactly `threeWork m n` actions that are not
rests. -/
theorem three_threads_total (m n : Nat) (hm : 4 ≤ m) (hn : 19 ≤ 3 * m + 3 * n) :
    (XMach.init (sum (m + 1) n) 3).Total xsys (fun i => i % 3) (threeWork m n) := by
  unfold threeWork
  by_cases c1 : 17 * m + 7 ≤ turnAt m n 1 ∧ turnAt m n 1 ≤ 17 * m + 16
  · rw [ite_pos' c1]
    exact three_threads_race_late m n hm c1.1 c1.2
  · rw [ite_neg' c1]
    by_cases c0 : 17 * m + 7 ≤ turnAt m n 0 ∧ turnAt m n 0 ≤ 17 * m + 16
    · rw [ite_pos' c0]
      exact three_threads_race_first m n hm c0.1 (by
        have c2 := c0.2
        unfold turnAt at c1 c2 ⊢
        omega)
    · rw [ite_neg' c0]
      exact threads_total m n 2 (by omega) (by omega) (fun t ht => by
        have h : t = 0 ∨ t = 1 := by omega
        rcases h with rfl | rfl
        · omega
        · omega)

example : (XMach.init (sum 7 31) 3).Total xsys (fun i => i % 3) 624 :=
  (three_threads_total 6 31 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 32) 3).Total xsys (fun i => i % 3) 641 :=
  (three_threads_total 6 32 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 8 36) 3).Total xsys (fun i => i % 3) 718 :=
  (three_threads_total 7 36 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 33) 3).Total xsys (fun i => i % 3) 653 :=
  (three_threads_total 6 33 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 30) 3).Total xsys (fun i => i % 3) 612 :=
  (three_threads_total 6 30 (by decide) (by decide)).cast (by decide)

example : (XMach.init (sum 7 9) 3).Total xsys (fun i => i % 3) 300 :=
  (three_threads_total 6 9 (by decide) (by decide)).cast (by decide)

end Arith

end INet
