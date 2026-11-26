import InteractionNets.Reducer

/-! # Firing every active pair in each round is optimal

A parallel round fires some active pairs that share no agent, all at once.
`XNet.parStep` fires all of them.  Here it is proved that no schedule of
rounds reaches a normal form in fewer rounds than `XNet.parRun`
(`XNet.parRun_optimal`), and that a net some pairs ahead of another needs
no more rounds than it (`XNet.parRun_ahead`): firing a pair early never
costs a round.  With room for at most `p` pairs a round, `W / p + D`
rounds are enough, `W` the steps and `D` the rounds of `XNet.parRun`
(`XNet.parRunP_bound`), at most twice the rounds of any schedule of at
most `p` pairs a round (`XNet.parRunP_twice`).

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

/-! ### A bounded number of firing units

With room for at most `p` pairs in a round, the rounds needed are at most
the pairs fired divided by `p`, plus the rounds of `XNet.parStep` (Brent's
bound).  The policy is the plainest one: fire the first `p` pairs that
`XNet.parStep` would fire. -/

/-- A round that fires at most `p` active pairs: the first `p` of those
that `XNet.parStep` fires.  Returns the net reached and the pairs fired. -/
def XNet.parStepP (xs : XSys S) (p : Nat) (X : XNet S) : XNet S × Nat :=
  (X.fireList xs.sys.ar ((selectIndep [] (X.redexes xs)).take p),
    ((selectIndep [] (X.redexes xs)).take p).length)

/-- Repeat `XNet.parStepP` for at most `n` rounds.  Returns the net reached
and the total number of pairs fired. -/
def XNet.parRunP (xs : XSys S) (p : Nat) : Nat → XNet S → XNet S × Nat
  | 0, X => (X, 0)
  | n + 1, X =>
    if (X.parStepP xs p).2 = 0 then (X, 0)
    else ((XNet.parRunP xs p n (X.parStepP xs p).1).1,
      (X.parStepP xs p).2 + (XNet.parRunP xs p n (X.parStepP xs p).1).2)

theorem XNet.Indep.sublist {rs rs' : List (XRedex S)} (h : X.Indep xs rs) (hs : rs'.Sublist rs) :
    X.Indep xs rs' :=
  ⟨fun r hr => h.redex r (hs.subset hr), h.disjoint.sublist hs⟩

/-- Firing a list of independent pairs is a reduction with one step per
pair, and preserves the invariant. -/
theorem XNet.fireList_steps {rs : List (XRedex S)} (hX : X.Ok xs.sys.ar) (h : X.Indep xs rs) :
    Steps (CStep xs.sys) rs.length X.toNet (X.fireList xs.sys.ar rs).toNet ∧
      (X.fireList xs.sys.ar rs).Ok xs.sys.ar := by
  obtain ⟨e, hok⟩ := XNet.fireList_toNet hX h
  refine ⟨?_, hok⟩
  have sts := Steps.cstep hX.1 (h.abs.fireAll_steps hX.1)
  rw [hX.2, List.length_map] at sts
  rw [e]
  exact sts

/-- **Brent's bound for interaction nets.**  If the net reaches a normal
form in `W` steps, and `D` rounds of `XNet.parStep` bring it to a normal
form, then rounds of at most `p` pairs bring it to a normal form within
`W / p + D` rounds. -/
theorem XNet.parRunP_bound {p : Nat} (hp : 0 < p) :
    ∀ (n : Nat) {X : XNet S} {W D : Nat} {C : Net S}, X.Ok xs.sys.ar →
      Steps (CStep xs.sys) W X.toNet C → Normal (CStep xs.sys) C →
      (X.parRun xs D).1.step xs = none → W / p + D ≤ n →
      (X.parRunP xs p n).1.step xs = none := by
  intro n
  induction n with
  | zero =>
    intro X W D C hX _ _ hD hn
    obtain rfl : D = 0 := by have := Nat.zero_le (W / p); omega
    exact hD
  | succ n ih =>
    intro X W D C hX hW hC hD hn
    have hI := XNet.redexes_indep xs X
    have hT : X.Indep xs ((selectIndep [] (X.redexes xs)).take p) :=
      hI.sublist (List.take_sublist _ _)
    unfold XNet.parRunP
    split
    · rename_i h0
      have h0' : ((selectIndep [] (X.redexes xs)).take p).length = 0 := h0
      rw [List.length_take] at h0'
      have hl : (selectIndep [] (X.redexes xs)).length = 0 := by omega
      exact XNet.parStep_zero_iff.1 hl
    · rename_i h0
      obtain ⟨sts, hY⟩ := XNet.fireList_steps hX hT
      obtain ⟨hle, rest⟩ := (cstrongConfluent xs.sys).bounded hX.1 hW hC sts
      by_cases hsel : (selectIndep [] (X.redexes xs)).length ≤ p
      · -- the round fires every active pair: it is a round of `parStep`
        have et : (selectIndep [] (X.redexes xs)).take p = selectIndep [] (X.redexes xs) :=
          List.take_of_length_le hsel
        have hz : ¬ (X.parStep xs).2 = 0 := by
          intro hz
          exact h0 (by
            show ((selectIndep [] (X.redexes xs)).take p).length = 0
            rw [et]
            exact hz)
        cases D with
        | zero => exact absurd (XNet.parStep_zero_iff.2 hD) hz
        | succ d =>
          unfold XNet.parRun at hD
          split at hD
          · exact absurd (by assumption) hz
          rw [et] at hY rest hle
          show (XNet.parRunP xs p n
            (X.fireList xs.sys.ar ((selectIndep [] (X.redexes xs)).take p))).1.step xs = none
          rw [et]
          refine ih hY rest hC hD ?_
          have := Nat.div_le_div_right (c := p) (Nat.sub_le W
            (selectIndep [] (X.redexes xs)).length)
          omega
      · -- the round fires `p` pairs: it is ahead of `X`
        have hlen : ((selectIndep [] (X.redexes xs)).take p).length = p := by
          rw [List.length_take]
          omega
        have hD' := XNet.parRun_ahead hX hY ?_ D hD
        · refine ih (W := W - _) hY rest hC hD' ?_
          rw [hlen] at hle ⊢
          have := Nat.div_eq_sub_div hp hle
          omega
        · obtain ⟨e, -⟩ := XNet.fireList_toNet hX hT
          exact ⟨_, hT.abs, e⟩

/-- A schedule of `r` rounds, each firing at most `p` independent active
pairs. -/
inductive XNet.SchedP (xs : XSys S) (p : Nat) : Nat → XNet S → XNet S → Prop
  | refl (X : XNet S) : XNet.SchedP xs p 0 X X
  | round {X Y : XNet S} {r : Nat} (rs : List (XRedex S)) (h : X.Indep xs rs)
      (hp : rs.length ≤ p) (rest : XNet.SchedP xs p r (X.fireList xs.sys.ar rs) Y) :
      XNet.SchedP xs p (r + 1) X Y

theorem XNet.SchedP.sched {p r : Nat} {X Y : XNet S} (h : XNet.SchedP xs p r X Y) :
    XNet.Sched xs r X Y := by
  induction h with
  | refl X => exact .refl X
  | round rs hI _ _ ih => exact .round rs hI ih

/-- A schedule of `r` rounds of at most `p` pairs is a reduction of at most
`p * r` steps. -/
theorem XNet.SchedP.steps {p r : Nat} {X Y : XNet S} (h : XNet.SchedP xs p r X Y)
    (hX : X.Ok xs.sys.ar) :
    ∃ W, W ≤ p * r ∧ Steps (CStep xs.sys) W X.toNet Y.toNet ∧ Y.Ok xs.sys.ar := by
  induction h with
  | refl X => exact ⟨0, Nat.zero_le _, .refl _, hX⟩
  | @round X Y r rs hI hp _ ih =>
    obtain ⟨st, hX₁⟩ := XNet.fireList_steps hX hI
    obtain ⟨W, hW, sts, hY⟩ := ih hX₁
    refine ⟨rs.length + W, ?_, st.trans sts, hY⟩
    rw [Nat.mul_succ]
    omega

/-- **Within twice the best**: if some schedule of `r` rounds of at most
`p` pairs each brings the net to a normal form, then `2 * r` rounds of
`XNet.parStepP` do. -/
theorem XNet.parRunP_twice {p r : Nat} {X Y : XNet S} (hp : 0 < p) (hX : X.Ok xs.sys.ar)
    (h : XNet.SchedP xs p r X Y) (hn : Y.step xs = none) :
    (X.parRunP xs p (2 * r)).1.step xs = none := by
  obtain ⟨W, hW, sts, hY⟩ := h.steps hX
  have hD := XNet.parRun_optimal hX h.sched hn
  refine XNet.parRunP_bound hp (2 * r) hX sts (XNet.step_complete hY hn) hD ?_
  have : W / p ≤ r := Nat.div_le_of_le_mul hW
  omega

end INet
