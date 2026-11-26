import InteractionNets.Reducer

/-! # Firing every active pair in each round is optimal

A parallel round fires some active pairs that share no agent, all at once.
`XNet.parStep` fires all of them.  Here it is proved that no schedule of
rounds reaches a normal form in fewer rounds than `XNet.parRun`
(`XNet.parRun_optimal`), and that a net some pairs ahead of another needs
no more rounds than it (`XNet.parRun_ahead`): firing a pair early never
costs a round.

The key fact is `par_absorb`: fire any independent pairs `rs` of a net, and the
net reached by firing all its active pairs is one round further on, by the
pairs of the full round that share no agent with `rs`.  Rounds are counted,
not the work of finding the pairs. -/

namespace INet

variable {S : Type} {sys : System S} {N C : Net S}

/-- One round of a parallel schedule on nets without history: fire some
independent active pairs together, then compact. -/
def PStep (sys : System S) (C C' : Net S) : Prop :=
  ∃ rs, Indep sys C rs ∧ C' = (C.fireAll rs).compact sys.ar

/-- The pairs of a list meet every active pair of the net. -/
def MeetsAll (sys : System S) (C : Net S) (ts : List (Id × Id × Rhs S)) : Prop :=
  ∀ {a b : Id} {α β : S} {R : Rhs S}, Redex sys C a b α β R → ∃ t ∈ ts, a = t.1 ∨ a = t.2.1

/-- Two pairs on the same two agents, in either order. -/
def SameAgents (r r' : Id × Id × Rhs S) : Prop :=
  (r.1 = r'.1 ∧ r.2.1 = r'.2.1) ∨ (r.1 = r'.2.1 ∧ r.2.1 = r'.1)

/-- Two pairs that share no agent. -/
def PairApart (r r' : Id × Id × Rhs S) : Prop :=
  r.1 ≠ r'.1 ∧ r.1 ≠ r'.2.1 ∧ r.2.1 ≠ r'.1 ∧ r.2.1 ≠ r'.2.1

instance (r r' : Id × Id × Rhs S) : Decidable (PairApart r r') := by
  unfold PairApart; infer_instance

theorem PairApart.symm {r r' : Id × Id × Rhs S} (h : PairApart r r') : PairApart r' r :=
  ⟨Ne.symm h.1, Ne.symm h.2.2.1, Ne.symm h.2.1, Ne.symm h.2.2.2⟩

/-- Pairs on the same agents as a third are not apart. -/
theorem SameAgents.not_apart {r x x' : Id × Id × Rhs S} (h : SameAgents r x')
    (h' : SameAgents x x') (d : PairApart r x) : False := by
  obtain ⟨d₁, d₂, d₃, d₄⟩ := d
  rcases h with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rcases h' with ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩
  · exact d₁ (e₁.trans f₁.symm)
  · exact d₂ (e₁.trans f₂.symm)
  · exact d₂ (e₁.trans f₂.symm)
  · exact d₁ (e₁.trans f₁.symm)

/-- Two active pairs sharing an agent are on the same two agents. -/
theorem Redex.same_of_share {a b c d : Id} {α β γ δ : S} {R R' : Rhs S}
    (r : Redex sys N a b α β R) (r' : Redex sys N c d γ δ R') (hN : N.WF sys.ar)
    (h : a = c ∨ a = d ∨ b = c ∨ b = d) : SameAgents (a, b, R) (c, d, R') := by
  obtain ⟨Rf, rf, -⟩ := r.flip hN
  obtain ⟨Rf', rf', -⟩ := r'.flip hN
  rcases h with rfl | rfl | rfl | rfl
  · exact .inl ⟨rfl, r.partner_unique r' hN⟩
  · exact .inr ⟨rfl, r.partner_unique rf' hN⟩
  · exact .inr ⟨rf.partner_unique r' hN, rfl⟩
  · exact .inl ⟨rf.partner_unique rf' hN, rfl⟩

/-- Two active pairs on the same agents fire to the same net. -/
theorem Redex.fire_same {a b c d : Id} {α β γ δ : S} {R R' : Rhs S}
    (r : Redex sys N a b α β R) (r' : Redex sys N c d γ δ R') (hN : N.WF sys.ar)
    (h : SameAgents (a, b, R) (c, d, R')) : N.fire a b R = N.fire c d R' := by
  rcases h with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · dsimp only at e₁ e₂
    subst e₁ e₂
    exact r.fire_eq r' hN
  · dsimp only at e₁ e₂
    subst e₁ e₂
    obtain ⟨R₂, r₂, e⟩ := r.flip hN
    exact e.trans (r₂.fire_eq r' hN)

theorem Net.fireSeq_append (N : Net S) (rs us : List (Id × Id × Rhs S)) :
    N.fireSeq (rs ++ us) = (N.fireSeq rs).fireSeq us := by
  induction rs generalizing N with
  | nil => rfl
  | cons r rs ih => exact ih _

namespace Indep

variable {rs rs' : List (Id × Id × Rhs S)}

theorem mem_redex (h : Indep sys N rs) {r : Id × Id × Rhs S} (hr : r ∈ rs) :
    ∃ α β, Redex sys N r.1 r.2.1 α β r.2.2 :=
  h.redex r hr

/-- An active pair apart from independent pairs survives their firing. -/
theorem redex_fireSeq (hN : N.WF sys.ar) (h : Indep sys N rs) {c d : Id} {γ δ : S}
    {R' : Rhs S} (rx : Redex sys N c d γ δ R') (hd : ∀ r ∈ rs, PairApart (c, d, R') r) :
    Redex sys (N.fireSeq rs) c d γ δ R' := by
  induction rs generalizing N with
  | nil => exact rx
  | cons r rs ih =>
    obtain ⟨α, β, rr⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
    obtain ⟨d₁, d₂, d₃, d₄⟩ := hd r (List.mem_cons.2 (.inl rfl))
    exact ih (Step.wf hN h.step) (h.tail hN) (rr.fire rx hN d₁ d₂ d₃ d₄)
      (fun r' hr' => hd r' (List.mem_cons.2 (.inr hr')))

/-- Independence does not depend on the order of the list. -/
theorem perm (h : Indep sys N rs) (hp : rs.Perm rs') : Indep sys N rs' :=
  ⟨fun r hr => h.redex r (hp.mem_iff.2 hr),
    h.disjoint.perm hp fun e => PairApart.symm e⟩

/-- **Two lists of independent pairs on the same agents fire to the same
net**, whatever the order of the lists and of the two agents of each pair. -/
theorem fireSeq_same (hN : N.WF sys.ar) (h : Indep sys N rs) (h' : Indep sys N rs')
    (hm : ∀ r ∈ rs, ∃ r' ∈ rs', SameAgents r r')
    (hm' : ∀ r' ∈ rs', ∃ r ∈ rs, SameAgents r r') : N.fireSeq rs = N.fireSeq rs' := by
  induction rs generalizing N rs' with
  | nil =>
    cases rs' with
    | nil => rfl
    | cons r' _ =>
      obtain ⟨r, hr, -⟩ := hm' r' (List.mem_cons.2 (.inl rfl))
      exact absurd hr List.not_mem_nil
  | cons r rest ih =>
    obtain ⟨r', hr', hs⟩ := hm r (List.mem_cons.2 (.inl rfl))
    obtain ⟨s₁, s₂, rfl⟩ := List.append_of_mem hr'
    have hp : (s₁ ++ r' :: s₂).Perm (r' :: (s₁ ++ s₂)) := List.perm_middle
    have h₂ : Indep sys N (r' :: (s₁ ++ s₂)) := h'.perm hp
    rw [h'.fireSeq_perm hN h₂ (fun x => hp.mem_iff)]
    obtain ⟨α, β, rr⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
    obtain ⟨γ, δ, rr'⟩ := h₂.redex r' (List.mem_cons.2 (.inl rfl))
    have e : N.fire r.1 r.2.1 r.2.2 = N.fire r'.1 r'.2.1 r'.2.2 := rr.fire_same rr' hN hs
    show (N.fire r.1 r.2.1 r.2.2).fireSeq rest = (N.fire r'.1 r'.2.1 r'.2.2).fireSeq _
    rw [← e]
    have ht : Indep sys (N.fire r.1 r.2.1 r.2.2) (s₁ ++ s₂) := by
      have := h₂.tail hN
      rwa [← e] at this
    obtain ⟨hd, -⟩ := List.pairwise_cons.1 h.disjoint
    obtain ⟨hd', -⟩ := List.pairwise_cons.1 h₂.disjoint
    refine ih (Step.wf hN h.step) (h.tail hN) ht (fun x hx => ?_) (fun y' hy' => ?_)
    · obtain ⟨x', hx', hxs⟩ := hm x (List.mem_cons.2 (.inr hx))
      refine ⟨x', ?_, hxs⟩
      rcases List.mem_append.1 hx' with hx' | hx'
      · exact List.mem_append.2 (.inl hx')
      rcases List.mem_cons.1 hx' with rfl | hx'
      · exact absurd (hd x hx) fun d => hs.not_apart hxs d
      · exact List.mem_append.2 (.inr hx')
    · have hy'' : y' ∈ s₁ ++ r' :: s₂ := by
        rcases List.mem_append.1 hy' with h | h
        · exact List.mem_append.2 (.inl h)
        · exact List.mem_append.2 (.inr (List.mem_cons.2 (.inr h)))
      obtain ⟨y, hy, hys⟩ := hm' y' hy''
      refine ⟨y, ?_, hys⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd (hd' y' hy') fun d => by
          rcases hs with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rcases hys with ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩
          · exact d.1 (e₁.symm.trans f₁)
          · exact d.2.1 (e₁.symm.trans f₁)
          · exact d.2.2.1 (e₁.symm.trans f₁)
          · exact d.2.2.2 (e₁.symm.trans f₁)
      · exact hy

end Indep

/-- A net with no step has no independent active pairs but the empty list. -/
theorem Indep.eq_nil_of_normal {rs : List (Id × Id × Rhs S)} (h : Indep sys C rs)
    (hn : Normal (CStep sys) C) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r _ =>
    exact absurd ⟨_, h.step, rfl⟩ (hn _)

/-- **Absorption.**  Fire any independent pairs `rs` of a net; the net
reached by firing a list `ts` that meets every active pair is one round
further on, by the pairs of `ts` apart from `rs`. -/
theorem par_absorb (hC : C.WF sys.ar) {rs ts : List (Id × Id × Rhs S)}
    (hr : Indep sys C rs) (ht : Indep sys C ts) (cov : MeetsAll sys C ts) :
    PStep sys ((C.fireAll rs).compact sys.ar) ((C.fireAll ts).compact sys.ar) := by
  let us := ts.filter fun t => rs.all fun r => decide (PairApart r t)
  have hus : ∀ u ∈ us, u ∈ ts ∧ ∀ r ∈ rs, PairApart r u := by
    intro u hu
    obtain ⟨hu, ha⟩ := List.mem_filter.1 hu
    exact ⟨hu, fun r hr => of_decide_eq_true (List.all_eq_true.1 ha r hr)⟩
  have hN₁ : (C.fireSeq rs).WF sys.ar := Steps.wf hC (hr.steps hC)
  have hu₁ : Indep sys (C.fireSeq rs) us := by
    refine ⟨fun u hu => ?_, ht.disjoint.sublist List.filter_sublist⟩
    obtain ⟨hu, hap⟩ := hus u hu
    obtain ⟨α, β, rx⟩ := ht.redex u hu
    exact ⟨α, β, hr.redex_fireSeq hC rx fun r hr => (hap r hr).symm⟩
  have hru : Indep sys C (rs ++ us) := by
    refine ⟨fun x hx => ?_, List.pairwise_append.2 ⟨hr.disjoint,
      ht.disjoint.sublist List.filter_sublist, fun r hr u hu => (hus u hu).2 r hr⟩⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hr.redex x hx
    · exact ht.redex x (hus x hx).1
  refine ⟨us, ?_, ?_⟩
  · rw [← hr.fireSeq_eq hC]
    exact hu₁.obsEq (Net.compact_obs sys.ar _)
  · rw [← hr.fireSeq_eq hC, ← hu₁.compact_fireAll hN₁, ← hu₁.fireSeq_eq hN₁,
      ← Net.fireSeq_append, ← ht.fireSeq_eq hC, hru.fireSeq_same hC ht]
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨α, β, rx⟩ := hr.redex x hx
        obtain ⟨t, htm, hat⟩ := cov rx
        obtain ⟨γ, δ, rt⟩ := ht.redex t htm
        refine ⟨t, htm, rx.same_of_share rt hC ?_⟩
        rcases hat with e | e
        · exact .inl e
        · exact .inr (.inl e)
      · exact ⟨x, (hus x hx).1, .inl ⟨rfl, rfl⟩⟩
    · intro t htm
      by_cases hall : ∀ r ∈ rs, PairApart r t
      · refine ⟨t, List.mem_append.2 (.inr ?_), .inl ⟨rfl, rfl⟩⟩
        exact List.mem_filter.2 ⟨htm, List.all_eq_true.2 fun r hr => decide_eq_true (hall r hr)⟩
      · obtain ⟨r, hrm, hn⟩ : ∃ r ∈ rs, ¬ PairApart r t := by
          simp only [Classical.not_forall] at hall
          obtain ⟨r, hr, hn⟩ := hall
          exact ⟨r, hr, hn⟩
        obtain ⟨α, β, rx⟩ := hr.redex r hrm
        obtain ⟨γ, δ, rt⟩ := ht.redex t htm
        refine ⟨r, List.mem_append.2 (.inl hrm), rx.same_of_share rt hC ?_⟩
        by_cases h₁ : r.1 = t.1
        · exact .inl h₁
        by_cases h₂ : r.1 = t.2.1
        · exact .inr (.inl h₂)
        by_cases h₃ : r.2.1 = t.1
        · exact .inr (.inr (.inl h₃))
        by_cases h₄ : r.2.1 = t.2.1
        · exact .inr (.inr (.inr h₄))
        exact absurd ⟨h₁, h₂, h₃, h₄⟩ hn

/-! ### The parallel reducer -/

variable {xs : XSys S} {X Y : XNet S}

/-- The pairs fired by a round of `XNet.parStep`. -/
abbrev XNet.parSel (xs : XSys S) (X : XNet S) : List (Id × Id × Rhs S) :=
  (selectIndep [] (X.redexes xs)).map XRedex.abs

/-- **A round of `XNet.parStep` meets every active pair.** -/
theorem XNet.parSel_covers (hX : X.Ok xs.sys.ar) : MeetsAll xs.sys X.toNet (X.parSel xs) := by
  intro a b α β R r
  cases ht : X.redexAt xs a α with
  | none => exact absurd ht (XNet.redexAt_complete hX r)
  | some t =>
    have hmem : t ∈ X.redexes xs := List.mem_filterMap.2 ⟨(a, α), r.ha, ht⟩
    have hfst := XNet.redexAt_fst ht
    obtain ⟨a', b', α', β', R'⟩ := t
    have hfst' : a' = a := hfst
    subst hfst'
    obtain ⟨rt, -⟩ := XNet.redexAt_sound ht r.ha
    obtain ⟨⟨c, d, γ', δ', R''⟩, hr', hc⟩ := selectIndep_covers (X.redexes xs) [] _ hmem
    obtain ⟨rx', -⟩ := (XNet.redexes_indep xs X).redex _ hr'
    refine ⟨(c, d, R''.toRhs), List.mem_map.2 ⟨_, hr', rfl⟩, ?_⟩
    rcases hc with e' | hc
    · exact .inl (congrArg (·.1) e').symm
    · by_cases h₁ : a' = c
      · exact .inl h₁
      by_cases h₂ : a' = d
      · exact .inr h₂
      by_cases h₃ : b' = c
      · subst h₃
        obtain ⟨R₂, rt', -⟩ := rt.flip hX.1
        exact .inr (rt'.partner_unique rx' hX.1)
      by_cases h₄ : b' = d
      · subst h₄
        obtain ⟨R₂, rt', -⟩ := rt.flip hX.1
        obtain ⟨R₃, rx'', -⟩ := rx'.flip hX.1
        exact .inl (rt'.partner_unique rx'' hX.1)
      exact absurd ⟨h₁, h₂, h₃, h₄⟩ hc

theorem XNet.parStep_toNet (hX : X.Ok xs.sys.ar) :
    (X.parStep xs).1.toNet = (X.toNet.fireAll (X.parSel xs)).compact xs.sys.ar :=
  (XNet.fireList_toNet hX (XNet.redexes_indep xs X)).1

/-- A round from a net with no step changes nothing. -/
theorem XNet.pstep_normal (hX : X.Ok xs.sys.ar) (h : X.step xs = none)
    (hp : PStep xs.sys X.toNet Y.toNet) : Y.toNet = X.toNet := by
  obtain ⟨ps, hps, e⟩ := hp
  rw [e, hps.eq_nil_of_normal (XNet.step_complete hX h), Net.fireAll_nil, hX.2]

/-- **A net ahead needs no more rounds**: if `Y` is one round of any
independent pairs on from `X`, and `k` rounds of `XNet.parStep` bring `X`
to a normal form, then `k` rounds bring `Y` to one.  Firing pairs early
never costs a round. -/
theorem XNet.parRun_ahead (hX : X.Ok xs.sys.ar) (hY : Y.Ok xs.sys.ar)
    (hp : PStep xs.sys X.toNet Y.toNet) (k : Nat) (h : (X.parRun xs k).1.step xs = none) :
    (Y.parRun xs k).1.step xs = none := by
  induction k generalizing X Y with
  | zero =>
    have e := XNet.pstep_normal hX h hp
    exact XNet.step_none_of_normal hY (e ▸ XNet.step_complete hX h)
  | succ k ih =>
    unfold XNet.parRun
    split
    · exact XNet.parStep_zero_iff.1 (by assumption)
    · rename_i hy
      unfold XNet.parRun at h
      split at h
      · have e := XNet.pstep_normal hX h hp
        exact absurd (XNet.parStep_zero_iff.2
          (XNet.step_none_of_normal hY (e ▸ XNet.step_complete hX h))) hy
      · obtain ⟨-, hX'⟩ := XNet.parStep_spec (xs := xs) hX
        obtain ⟨-, hY'⟩ := XNet.parStep_spec (xs := xs) hY
        refine ih hX' hY' ?_ h
        obtain ⟨ps, hps, eY⟩ := hp
        have hI := (XNet.redexes_indep xs X).abs
        obtain ⟨us, hus, eX'⟩ := par_absorb hX.1 hps hI (XNet.parSel_covers hX)
        rw [← eY, ← XNet.parStep_toNet hX] at eX'
        rw [← eY] at hus
        have hJ := (XNet.redexes_indep xs Y).abs
        have := par_absorb hY.1 hus hJ (XNet.parSel_covers hY)
        rwa [← eX', ← XNet.parStep_toNet hY] at this

/-- A schedule of `r` parallel rounds from one net to another: each round
fires a list of independent active pairs. -/
inductive XNet.Sched (xs : XSys S) : Nat → XNet S → XNet S → Prop
  | refl (X : XNet S) : XNet.Sched xs 0 X X
  | round {X Y : XNet S} {r : Nat} (rs : List (XRedex S)) (h : X.Indep xs rs)
      (rest : XNet.Sched xs r (X.fireList xs.sys.ar rs) Y) : XNet.Sched xs (r + 1) X Y

/-- **Firing every active pair in each round is optimal**: if some schedule
of `r` parallel rounds brings a net to a normal form, then `r` rounds of
`XNet.parStep` bring it to a normal form too. -/
theorem XNet.parRun_optimal {r : Nat} (hX : X.Ok xs.sys.ar) (hs : XNet.Sched xs r X Y)
    (hn : Y.step xs = none) : (X.parRun xs r).1.step xs = none := by
  induction hs with
  | refl => exact hn
  | @round X Y r rs hI rest ih =>
    obtain ⟨e₁, hX₁⟩ := XNet.fireList_toNet hX hI
    have ih := ih hX₁ hn
    unfold XNet.parRun
    split
    · exact XNet.parStep_zero_iff.1 (by assumption)
    · obtain ⟨-, hY⟩ := XNet.parStep_spec (xs := xs) hX
      refine XNet.parRun_ahead hX₁ hY ?_ r ih
      rw [e₁, XNet.parStep_toNet hX]
      exact par_absorb hX.1 hI.abs (XNet.redexes_indep xs X).abs (XNet.parSel_covers hX)

/-- A schedule may stand still: a round can fire no pair. -/
theorem XNet.Sched.stay (xs : XSys S) (X : XNet S) : ∀ r, XNet.Sched xs r X X
  | 0 => .refl X
  | r + 1 => .round [] ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
      (XNet.Sched.stay xs X r)

/-- The parallel reducer is itself a schedule, of as many rounds as it is
given. -/
theorem XNet.parRun_sched (xs : XSys S) : ∀ (r : Nat) (X : XNet S),
    XNet.Sched xs r X (X.parRun xs r).1
  | 0, X => .refl X
  | r + 1, X => by
    unfold XNet.parRun
    split
    · exact XNet.Sched.stay xs X (r + 1)
    · exact .round _ (XNet.redexes_indep xs X) (XNet.parRun_sched xs r (X.parStep xs).1)

/-- **The fewest rounds**: a schedule of `r` parallel rounds can bring the
net to a normal form exactly when `r` rounds of `XNet.parStep` do. -/
theorem XNet.parRun_optimal_iff {r : Nat} (hX : X.Ok xs.sys.ar) :
    (X.parRun xs r).1.step xs = none ↔ ∃ Y, XNet.Sched xs r X Y ∧ Y.step xs = none :=
  ⟨fun h => ⟨_, XNet.parRun_sched xs r X, h⟩,
    fun ⟨_, hs, hn⟩ => XNet.parRun_optimal hX hs hn⟩

end INet
