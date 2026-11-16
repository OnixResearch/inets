import InteractionNets.JoinTotal

/-! # Rules that join several segments

`JMach.rests_log` covers systems whose rules join one segment at most.  The
interaction combinators annihilate by joining two.  Here a rule may join up
to `J` segments, as long as joining is all it does, each interface port on
one joined segment (`XSys.PureJoins`).  The thread walks the joined
segments one after the other, on the net with all of them written; each
walk is a walk of one segment added to the net with the others
(`joined_of_pure`), so `walk_pays_found` pays it with the growth of the
measure from the net before the claim.  The claim pays for its walks with
`J` times that growth, and one thread is at rest after
`O(n + J K log K)` actions (`JMach.rests_multi`).
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- The net with some segments added, in both directions. -/
def Net.addSegs (G : Net S) (L : List (Port × Port)) : Net S where
  agent := G.agent
  link u v := G.link u v ∨ ∃ pq, pq ∈ L ∧ ((u = pq.1 ∧ v = pq.2) ∨ (u = pq.2 ∧ v = pq.1))
  free := G.free

/-- The two ends of each segment of a list. -/
def segEnds (L : List (Port × Port)) : List Port := L.flatMap fun pq => [pq.1, pq.2]

/-- **The joins of a system do nothing else**, rule by rule: firing adds
the joined segments and nothing more, each interface port lies on one of
them at most, and they join points on one segment of the net at most that
are not principal ports. -/
def XSys.PureJoins (xs : XSys S) : Prop :=
  ∀ (G : Net S) (a b : Id) (α β : S) (R : XRhs S), G.WF xs.sys.ar →
    xs.rule α β = some R → Redex xs.sys G a b α β R.toRhs →
    R.joinPairs xs.sys.ar a b α β ≠ [] →
    (∀ u v, (G.fire a b R.toRhs).link u v ↔ (G.addSegs (R.joinPairs xs.sys.ar a b α β)).link u v) ∧
    (∀ x, x ∈ segEnds (R.joinPairs xs.sys.ar a b α β) →
      (∀ y z, G.link x y → G.link x z → y = z) ∧ x.2 ≠ 0) ∧
    (segEnds (R.joinPairs xs.sys.ar a b α β)).Nodup

/-- Every rule joins `J` segments at most. -/
def XSys.JoinsAtMost (xs : XSys S) (J : Nat) : Prop :=
  ∀ α β R a b, xs.rule α β = some R → (R.joinPairs xs.sys.ar a b α β).length ≤ J

theorem pairwise_of_mem {α : Type} {R : α → α → Prop} (hs : ∀ {a b}, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact h.1 b hb'
    · exact hs (h.1 a ha')
    · exact pairwise_of_mem hs h.2 ha' hb' hne

/-- Different segments of a list whose ends are all different share no
end. -/
theorem segEnds_apart {L : List (Port × Port)} (h : (segEnds L).Nodup) {pq pq' : Port × Port}
    (hm : pq ∈ L) (hm' : pq' ∈ L) (hne : pq' ≠ pq) {x : Port}
    (hx : x = pq.1 ∨ x = pq.2) (hx' : x = pq'.1 ∨ x = pq'.2) : False := by
  unfold segEnds List.Nodup at h
  rw [List.pairwise_flatMap] at h
  have := pairwise_of_mem (R := fun a b => ∀ x, x ∈ [a.1, a.2] → ∀ y, y ∈ [b.1, b.2] → x ≠ y)
    (fun h x hx y hy e => h y hy x hx e.symm) h.2 hm' hm hne x
    (by rcases hx' with rfl | rfl <;> simp) x (by rcases hx with rfl | rfl <;> simp)
  exact this rfl

omit [DecidableEq S] in
/-- **Each walk of a rule that only joins is the walk of one segment added
to the net with the others.** -/
theorem joined_of_pure {G N : Net S} {L : List (Port × Port)}
    (hl : ∀ u v, N.link u v ↔ (G.addSegs L).link u v)
    (he : ∀ x, x ∈ segEnds L → (∀ y z, G.link x y → G.link x z → y = z) ∧ x.2 ≠ 0)
    (hnd : (segEnds L).Nodup) {pq : Port × Port} (hm : pq ∈ L) :
    Joined (G.addSegs (L.filter (· ≠ pq))) N pq.1 pq.2 := by
  have e₁ : pq.1 ∈ segEnds L := List.mem_flatMap.2 ⟨pq, hm, by simp⟩
  have e₂ : pq.2 ∈ segEnds L := List.mem_flatMap.2 ⟨pq, hm, by simp⟩
  have endR : ∀ x, (x = pq.1 ∨ x = pq.2) → ∀ y z, (G.addSegs (L.filter (· ≠ pq))).link x y →
      (G.addSegs (L.filter (· ≠ pq))).link x z → y = z := by
    intro x hx y z hy hz
    have hxe : x ∈ segEnds L := by rcases hx with rfl | rfl <;> assumption
    have only : ∀ w, (G.addSegs (L.filter (· ≠ pq))).link x w → G.link x w := by
      rintro w (hw | ⟨pq', hm', hw⟩)
      · exact hw
      · exfalso
        obtain ⟨hm'', hne⟩ := List.mem_filter.1 hm'
        have hne' : pq' ≠ pq := by simpa using hne
        exact segEnds_apart hnd hm hm'' hne' hx (by rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
    exact (he x hxe).1 y z (only y hy) (only z hz)
  refine ⟨fun u v => ?_, endR _ (.inl rfl), endR _ (.inr rfl), (he _ e₁).2, (he _ e₂).2⟩
  rw [hl]
  constructor
  · rintro (h | ⟨pq', hm', h⟩)
    · exact .inl (.inl h)
    · by_cases hq : pq' = pq
      · subst hq
        exact .inr h
      · exact .inl (.inr ⟨pq', List.mem_filter.2 ⟨hm', by simpa using hq⟩, h⟩)
  · rintro ((h | ⟨pq', hm', h⟩) | h)
    · exact .inl h
    · exact .inr ⟨pq', (List.mem_filter.1 hm').1, h⟩
    · exact .inr ⟨pq, hm, h⟩

/-- The joined segments of a rule, as pairs of ports of the right-hand
side. -/
def XRhs.joinPairsL (R : XRhs S) (ar : S → Nat) (α β : S) : List (LPort × LPort) :=
  (ifcPorts ar α β).filterMap fun x =>
    match R.wire x with
    | some y => if !y.isNew && x.rank < y.rank then some (x, y) else none
    | none => none

omit [DecidableEq S] in
theorem XRhs.joinPairs_eq (R : XRhs S) (ar : S → Nat) (a b : Id) (α β : S) :
    R.joinPairs ar a b α β = (R.joinPairsL ar α β).map fun xy => (emb a b xy.1, emb a b xy.2) := by
  unfold XRhs.joinPairs XRhs.joinPairsL
  induction ifcPorts ar α β with
  | nil => rfl
  | cons x L ih =>
    simp only [List.filterMap_cons]
    cases R.wire x with
    | none => exact ih
    | some y =>
      dsimp only
      by_cases hc : (!y.isNew && decide (x.rank < y.rank)) = true
      · rw [ite_pos' hc, ite_pos' hc, List.map_cons, ih]
      · rw [ite_neg' hc, ite_neg' hc]
        exact ih

omit [DecidableEq S] in
theorem XRhs.mem_joinPairsL {R : XRhs S} {ar : S → Nat} {α β : S} {x y : LPort}
    (h : (x, y) ∈ R.joinPairsL ar α β) :
    (∃ s k, x = .ifc s k) ∧ ∃ s k, y = .ifc s k := by
  unfold XRhs.joinPairsL at h
  obtain ⟨x', hx, hf⟩ := List.mem_filterMap.1 h
  obtain ⟨s, k, rfl, -⟩ := mem_ifcPorts.1 hx
  cases hw : R.wire (.ifc s k) with
  | none => rw [hw] at hf; cases hf
  | some y' =>
    rw [hw] at hf
    dsimp only at hf
    split at hf
    · rename_i hc
      cases hf
      refine ⟨⟨s, k, rfl⟩, ?_⟩
      cases y with
      | ifc s' k' => exact ⟨s', k', rfl⟩
      | new o j k' => simp [LPort.isNew] at hc
    · cases hf

omit [DecidableEq S] in
/-- **The joins of a system do nothing else** when every rule that joins
interface ports writes no agent and the ports of its joined segments are
all different. -/
theorem XSys.pureJoins_of
    (hb : ∀ α β R, xs.rule α β = some R → R.joins xs.sys.ar α β = true →
      R.slots = [] ∧ ((R.joinPairsL xs.sys.ar α β).flatMap fun xy => [xy.1, xy.2]).Nodup) :
    xs.PureJoins := by
  intro G a b α β R hG hR rg hne
  have hwf : R.toRhs.WF xs.sys.ar α β := xs.sys.rule_wf (by rw [xs.rule_spec, hR]; rfl)
  obtain ⟨pq₀, hpq₀⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hsl, hndL⟩ := hb α β R hR (XRhs.joins_of_mem hpq₀)
  have nolab : ∀ o j, R.lab o j = none := by
    intro o j
    cases hl : R.lab o j with
    | none => rfl
    | some γ =>
      have := xs.slots_spec hR hl
      rw [hsl] at this
      exact absurd this List.not_mem_nil
  have ifc : ∀ {x y}, R.wire x = some y → ∃ s k, x = .ifc s k ∧ k < xs.sys.ar (sel α β s) := by
    intro x y hw
    have hv := hwf.valid (x := x) (y := y) hw
    cases x with
    | ifc s k => exact ⟨s, k, rfl, hv⟩
    | new o j k =>
      obtain ⟨γ, hγ, -⟩ := hv
      have : R.toRhs.lab o j = none := nolab o j
      rw [this] at hγ
      cases hγ
  have hagent : ∀ s, G.agent (sel a b s) (sel α β s) := by
    intro s
    cases s
    · exact rg.ha
    · exact rg.hb
  refine ⟨fun u v => ⟨fun h => ?_, fun h => ?_⟩, fun x hx => ?_, ?_⟩
  · rcases h with h | ⟨x, y, hxy, rfl, rfl⟩
    · exact .inl h
    · obtain ⟨s₂, k₂, rfl, -⟩ := ifc hxy
      obtain ⟨s₃, k₃, rfl, -⟩ := ifc (hwf.symm (x := .ifc s₂ k₂) (y := y) hxy)
      rcases XRhs.joinPairs_of_wire (a := a) (b := b) hwf hxy with hm | hm
      · exact .inr ⟨_, hm, .inl ⟨rfl, rfl⟩⟩
      · exact .inr ⟨_, hm, .inr ⟨rfl, rfl⟩⟩
  · rcases h with h | ⟨pq, hm, h⟩
    · exact .inl h
    · obtain ⟨s, k, s', k', hw, -, e₁, e₂⟩ := XRhs.mem_joinPairs hm
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr ⟨_, _, hw, e₁, e₂⟩
      · exact .inr ⟨_, _, hwf.symm (x := .ifc s k) (y := .ifc s' k') hw, e₂, e₁⟩
  · obtain ⟨pq, hm, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨s, k, s', k', hw, -, e₁, e₂⟩ := XRhs.mem_joinPairs hm
    obtain ⟨s₀, k₀, e₀, hk⟩ := ifc hw
    obtain ⟨s₀', k₀', e₀', hk'⟩ := ifc (hwf.symm (x := .ifc s k) (y := .ifc s' k') hw)
    cases e₀
    cases e₀'
    have key : ∀ s k, k < xs.sys.ar (sel α β s) →
        (∀ y z, G.link (emb a b (.ifc s k)) y → G.link (emb a b (.ifc s k)) z → y = z) ∧
          (emb a b (.ifc s k)).2 ≠ 0 :=
      fun s k hk => ⟨fun y z hy hz => hG.end_unique
        (.inr ⟨sel α β s, hagent s, by simp only [emb]; omega⟩) hy hz, by simp [emb]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [e₁]
      exact key s k hk
    · rw [e₂]
      exact key s' k' hk'
  · -- the ends are all different: `emb` keeps the ports of the pair apart
    rw [XRhs.joinPairs_eq]
    unfold segEnds
    rw [List.flatMap_map]
    have hinj : ∀ x y, (∃ s k, x = LPort.ifc s k) → (∃ s k, y = LPort.ifc s k) →
        emb a b x = emb a b y → x = y := by
      rintro x y ⟨s, k, rfl⟩ ⟨s', k', rfl⟩ e
      simp only [emb, Prod.mk.injEq] at e
      obtain ⟨e₁, e₂⟩ := e
      have hk : k = k' := by omega
      subst hk
      cases s <;> cases s'
      · rfl
      · exact absurd e₁ rg.ne
      · exact absurd e₁.symm rg.ne
      · rfl
    have hifc : ∀ z, z ∈ (R.joinPairsL xs.sys.ar α β).flatMap (fun xy => [xy.1, xy.2]) →
        ∃ s k, z = LPort.ifc s k := by
      intro z hz
      obtain ⟨⟨x, y⟩, hm, hz⟩ := List.mem_flatMap.1 hz
      obtain ⟨hx, hy⟩ := XRhs.mem_joinPairsL hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have e : ((R.joinPairsL xs.sys.ar α β).flatMap fun xy =>
        [(emb a b xy.1, emb a b xy.2).1, (emb a b xy.1, emb a b xy.2).2]) =
        ((R.joinPairsL xs.sys.ar α β).flatMap fun xy => [xy.1, xy.2]).map (emb a b) := by
      rw [List.map_flatMap]
      rfl
    rw [e]
    unfold List.Nodup
    rw [List.pairwise_map]
    exact hndL.imp_of_mem fun hx hy hne e => hne (hinj _ _ (hifc _ hx) (hifc _ hy) e)

omit [DecidableEq S] in
/-- `J` joins at most, checked on one pair of names. -/
theorem XSys.joinsAtMost_of {J : Nat}
    (h : ∀ α β R, xs.rule α β = some R → (R.joinPairs xs.sys.ar [] [] α β).length ≤ J) :
    xs.JoinsAtMost J := fun α β R a b hR => by
  rw [XRhs.joinPairs_length R xs.sys.ar a b [] [] α β]
  exact h α β R hR

/-- What the walks of a list of joined segments cost on a memory holding
`G`, one after the other, within `b` actions. -/
def JoinsOwe (H : Net S) (K : Nat) (G : Net S) : List (Port × Port) → Nat → Prop
  | [], _ => True
  | (p, q) :: js, b => ∃ c, c ≤ b ∧ (∀ X : XNet S, X.Like G → ∃ n v, 1 ≤ n ∧
      (JWalk.iter X n (JWalk.start p q)).found = some v ∧ n + 1 + pushCost H K v ≤ c) ∧
      JoinsOwe H K G js (b - c)

omit [DecidableEq S] in
theorem JoinsOwe.mono {H : Net S} {K : Nat} {G : Net S} :
    ∀ {js : List (Port × Port)} {b b' : Nat}, JoinsOwe H K G js b → b ≤ b' → JoinsOwe H K G js b'
  | [], _, _, _, _ => trivial
  | (_, _) :: _, _, _, ⟨c, hc, hw, hr⟩, hle =>
    ⟨c, Nat.le_trans hc hle, hw, JoinsOwe.mono hr (Nat.sub_le_sub_right hle c)⟩

omit [DecidableEq S] in
theorem JoinsOwe.of_each {H : Net S} {K : Nat} {G : Net S} {c : Nat} :
    ∀ {js : List (Port × Port)}, (∀ pq, pq ∈ js → ∀ X : XNet S, X.Like G → ∃ n v, 1 ≤ n ∧
      (JWalk.iter X n (JWalk.start pq.1 pq.2)).found = some v ∧ n + 1 + pushCost H K v ≤ c) →
      JoinsOwe H K G js (js.length * c)
  | [], _ => trivial
  | (p, q) :: js, h => ⟨c, by simp [Nat.succ_mul], h (p, q) List.mem_cons_self, by
      have e : (js.length + 1) * c - c = js.length * c := by rw [Nat.succ_mul]; omega
      simp only [List.length_cons]
      rw [e]
      exact JoinsOwe.of_each fun pq hm => h pq (List.mem_cons_of_mem _ hm)⟩

/-- What the only thread owes to its walks: the walk under way, then the
segments still to walk. -/
def JMach.OwesM (H : Net S) (K : Nat) (M : JMach S) (b : Nat) : Prop :=
  ∀ T, M.ths[0]? = some T →
    (∀ w, T.walk = some w → ∃ c, c ≤ b ∧
      (∃ n v, 1 ≤ n ∧ (JWalk.iter M.mem n w).found = some v ∧ n + pushCost H K v ≤ c) ∧
      JoinsOwe H K M.toMach.goal T.joins (b - c)) ∧
    (T.walk = none → JoinsOwe H K M.toMach.goal T.joins b)

/-- **One action of the only thread, when a rule may join `J` segments**:
at rest it does nothing; otherwise it lowers the measure of the thread plus
what it owes to walks by one at least, after adding at a claim what the
claim writes, `C + D + 1 + 9 J`, and `J` times the growth of `payΦ`. -/
theorem JMach.total_step_multi {J : Nat} (hJ : xs.JoinsAtMost J) (hP : xs.PureJoins)
    {M : JMach S} (hL : M.Live xs)
    {T : JThread S} (h1 : M.ths = [T]) (hnd : (M.mem.agents.map Prod.fst).Nodup)
    {C D : Nat} (hb : xs.Bounded C D) {H : Net S} {K A : Nat} (hH : H.Sized K)
    (hM : M.toW.toX.Ahead H) (hM' : (M.step xs 0).1.toW.toX.Ahead H) (hA : M.toW.heads ≤ A)
    {W : List (Port × Port)} {l : List Id} (hWK : W.length ≤ K)
    (hok : PayOk xs.sys.ar W l M.toMach.goal)
    (hok' : PayOk xs.sys.ar W l (M.step xs 0).1.toMach.goal) {b : Nat}
    (hb' : M.OwesM H K b) :
    (T.todo = [] ∧ T.st = .idle) ∨
      ∃ b', (M.step xs 0).1.OwesM H K b' ∧
        1 + potV H K A ((JMach.act xs M.mem T).2.1) + b' + J * payΦ K W l M.toMach.goal ≤
          potV H K A T + b + J * payΦ K W l (M.step xs 0).1.toMach.goal +
            (M.step xs 0).2 * (C + D + 1 + 9 * J) + H.scan K (JMach.stepKids xs M 0) := by
  have ht : M.ths[0]? = some T := by rw [h1]; rfl
  obtain ⟨hbw, hbj⟩ := hb' T ht
  have es := JMach.step_eq (X₁ := (JMach.act xs M.mem T).1) (T₁ := (JMach.act xs M.mem T).2.1)
    (c := (JMach.act xs M.mem T).2.2) ht rfl
  have hset : M.ths.set 0 (JMach.act xs M.mem T).2.1 = [(JMach.act xs M.mem T).2.1] := by
    rw [h1]; rfl
  rw [hset] at es
  have ht' : (M.step xs 0).1.ths[0]? = some (JMach.act xs M.mem T).2.1 := by rw [es]; rfl
  have hm' : (M.step xs 0).1.mem = (JMach.act xs M.mem T).1 := by rw [es]
  have hc' : (M.step xs 0).2 = (JMach.act xs M.mem T).2.2 := by rw [es]
  have hk : JMach.stepKids xs M 0 = WMach.actKids xs M.mem T.toW := by
    unfold JMach.stepKids
    rw [ht]
  have mk : ∀ b', ((JMach.act xs M.mem T).2.1.walk = none →
      JoinsOwe H K (M.step xs 0).1.toMach.goal (JMach.act xs M.mem T).2.1.joins b') →
      (∀ w, (JMach.act xs M.mem T).2.1.walk = some w → ∃ c, c ≤ b' ∧
        (∃ n v, 1 ≤ n ∧ (JWalk.iter (JMach.act xs M.mem T).1 n w).found = some v ∧
          n + pushCost H K v ≤ c) ∧
        JoinsOwe H K (M.step xs 0).1.toMach.goal (JMach.act xs M.mem T).2.1.joins (b' - c)) →
      (M.step xs 0).1.OwesM H K b' := by
    intro b' hj hw T' hT'
    rw [ht'] at hT'
    cases hT'
    exact ⟨fun w h => by rw [← hm'] at hw; exact hw w h, hj⟩
  by_cases hw : T.st = .write [] [] ∧ T.again = true
  · refine .inr ?_
    have h0 : (M.step xs 0).2 = 0 := by
      rcases JMach.act_wr (xs := xs) M.mem T hw.1 hw.2 with ⟨_, _, _, h⟩ |
        ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
      · rw [hc', h]
    have eg := JMach.goal_of_zero hL h0
    have hk0 : JMach.stepKids xs M 0 = [] := by
      rw [hk]
      unfold WMach.actKids
      show (match T.st with
        | .half a b α β =>
          match (if assoc b M.mem.agents = some β ∧ a ≠ b then xs.rule α β else none) with
          | some R => R.newAgents a b
          | none => []
        | _ => []) = []
      rw [hw.1]
    rw [h0, eg, hk0, Nat.zero_mul, Nat.add_zero]
    have hsc : H.scan K ([] : List (Id × S)) = 0 := rfl
    rw [hsc, Nat.add_zero]
    obtain ⟨todo, st, again, joins, walk⟩ := T
    obtain ⟨hst, hag⟩ := hw
    dsimp only at hst hag
    subst hst hag
    have pvT : ∀ (js : List (Port × Port)) (wk : Option (JWalk S)) (todo' : List (Id × S)),
        potV H K A ⟨todo', .write [] [], true, js, wk⟩ = H.scan K todo' + (0 + 0 + 1) :=
      fun _ _ _ => rfl
    cases walk with
    | some w =>
      obtain ⟨c, hcb, ⟨n, v, hn1, hfn, hnc⟩, hrest⟩ := hbw w rfl
      cases hf : (w.advance M.mem).found with
      | none =>
        have hn2 : 2 ≤ n := by
          rcases Nat.lt_or_ge n 2 with h | h
          · obtain rfl : n = 1 := by omega
            change (w.advance M.mem).found = some v at hfn
            rw [hf] at hfn
            cases hfn
          · exact h
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, joins, some w⟩ =
            (M.mem, ⟨todo, .write [] [], true, joins, some (w.advance M.mem)⟩, 0) := by
          unfold JMach.act
          dsimp only
          rw [hf]
          rfl
        refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), ?_⟩
        · rw [hact] at h ⊢
          cases h
          refine ⟨c - 1, by omega, ⟨n - 1, v, by omega, ?_, by omega⟩, ?_⟩
          · have e : JWalk.iter M.mem n w = JWalk.iter M.mem (n - 1) (w.advance M.mem) := by
              obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              rfl
            rw [← e]
            exact hfn
          · rw [eg]
            exact hrest.mono (by omega)
        · rw [hact, pvT, pvT]
          omega
      | some v' =>
        have hvv := JWalk.found_eq M.mem hn1 hfn hf
        subst hvv
        have hact := JMach.act_end (xs := xs) M.mem ⟨todo, .write [] [], true, joins, some w⟩ rfl
          rfl rfl hf
        refine ⟨b - c, mk _ (fun _ => ?_) (fun w' h => by rw [hact] at h; cases h), ?_⟩
        · rw [hact, eg]
          exact hrest
        · rw [hact, pvT, pvT, scan_foundList]
          dsimp only
          omega
    | none =>
      cases joins with
      | cons pq js =>
        obtain ⟨p, q⟩ := pq
        obtain ⟨c, hcb, hX, hrest⟩ := hbj rfl
        obtain ⟨n, v, hn1, hfn, hnc⟩ := hX M.mem (JMach.like_goal h1 rfl)
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, (p, q) :: js, none⟩ =
            (M.mem, ⟨todo, .write [] [], true, js, some (JWalk.start p q)⟩, 0) := rfl
        refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), ?_⟩
        · rw [hact] at h ⊢
          cases h
          refine ⟨c - 1, by omega, ⟨n, v, hn1, hfn, by omega⟩, ?_⟩
          rw [eg]
          exact hrest.mono (by omega)
        · rw [hact, pvT, pvT]
          omega
      | nil =>
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, [], none⟩ =
            (M.mem, ⟨todo, .idle, false, [], none⟩, 0) := rfl
        refine ⟨b, mk _ (fun _ => by rw [hact]; trivial)
          (fun w' h => by rw [hact] at h; cases h), ?_⟩
        rw [hact, pvT]
        show 1 + H.scan K todo + b + _ ≤ _
        omega
  · -- not walking
    have hwn : T.walk = none := by
      cases hwk : T.walk with
      | none => rfl
      | some w =>
        have hs := hL.wst 0 T w ht hwk
        cases ha : T.again
        · rw [(hL.nojoin 0 T ht ha).2] at hwk
          cases hwk
        · exact absurd ⟨hs, ha⟩ hw
    have hcnt := JMach.act_count_eq (xs := xs) M.mem T
    rcases JMach.act_potV hL hnd hb hH hM hA ht hw with ⟨-, hto, hst⟩ | ⟨h1c, hle⟩ | ⟨h0, hlt⟩
    · exact .inl ⟨hto, hst⟩
    · -- a claim
      refine .inr ?_
      rcases WMach.act_count (xs := xs) M.mem T.toW with h0 | ⟨a, b₀, α, β, R, hs, hh⟩
      · rw [hcnt, h0] at h1c
        cases h1c
      change T.st = _ at hs
      have hact := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
      obtain ⟨hR, rg, eg⟩ := JMach.claim_goal hL ht hs hh
      have hc1 : (M.step xs 0).2 = 1 := by rw [hc', hact]
      rw [hc1, Nat.one_mul, eg]
      rw [eg] at hok'
      have hmono : payΦ K W l M.toMach.goal ≤ payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) :=
        payΦ_mono fun h => .inl h
      have hHG : ∀ {u v}, (M.toMach.goal.fire a b₀ R.toRhs).link u v → H.link u v :=
        fun {u v} h => hM'.link (show (M.step xs 0).1.toMach.goal.link u v by rw [eg]; exact h)
      have hpr : ∀ k γ q, (M.toMach.goal.fire a b₀ R.toRhs).agent k γ → H.link (k, 0) q →
          (M.toMach.goal.fire a b₀ R.toRhs).link (k, 0) q := by
        intro k γ q hk hq
        have hu : (M.step xs 0).1.toMach.goal.Used k := by
          rw [eg]
          exact .inl ⟨γ, hk⟩
        have := hM'.principal hu hq
        change (M.step xs 0).1.toMach.goal.link (k, 0) q at this
        rw [eg] at this
        exact this
      let c₁ := 9 + payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) - payΦ K W l M.toMach.goal
      have hjl := hJ α β R a b₀ hR
      refine ⟨J * c₁, mk _ (fun _ => ?_) (fun w h => by rw [hact] at h; cases h), ?_⟩
      · rw [hact, eg]
        show JoinsOwe H K _ (R.joinPairs xs.sys.ar a b₀ α β) _
        refine JoinsOwe.mono (JoinsOwe.of_each fun pq hm X hX => ?_) (Nat.mul_le_mul_right _ hjl)
        have hne : R.joinPairs xs.sys.ar a b₀ α β ≠ [] := fun e => by rw [e] at hm; cases hm
        obtain ⟨hl', he, hnd'⟩ := hP _ a b₀ α β R hok.1 hR rg hne
        have hJn := joined_of_pure hl' he hnd' hm
        obtain ⟨n, v, hn1, hfn, hle'⟩ := walk_pays_found hok'.1 hJn hX
          (fun h => hok'.2.1 _ _ h) hWK hok'.2.2 hH.deg hHG hpr
        have hm2 : payΦ K W l M.toMach.goal ≤
            payΦ K W l (M.toMach.goal.addSegs ((R.joinPairs xs.sys.ar a b₀ α β).filter (· ≠ pq))) :=
          payΦ_mono fun h => .inl h
        exact ⟨n, v, hn1, hfn, by omega⟩
      · rw [hk]
        have e : J * c₁ + J * payΦ K W l M.toMach.goal =
            J * 9 + J * payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) := by
          rw [← Nat.mul_add, ← Nat.mul_add]
          congr 1
          omega
        omega
    · -- a step that lowers the measure, without a claim
      refine .inr ?_
      have h0' : (M.step xs 0).2 = 0 := by rw [hc', h0]
      have eg := JMach.goal_of_zero hL h0'
      rw [h0', eg, Nat.zero_mul, Nat.add_zero]
      refine ⟨b, ?_, by omega⟩
      have hw' : ¬ (T.st = .write [] [] ∧ T.again = true) := hw
      rcases (JMach.act_shape (xs := xs) M.mem T hw').2.2.2 with ⟨ej, ew⟩ | ⟨ej, ew⟩ |
        ⟨a, b₀, α, β, R, hs, hh, -, -⟩
      · refine mk _ (fun _ => ?_) (fun w h => by rw [ew, hwn] at h; cases h)
        rw [ej, eg]
        exact hbj hwn
      · exact mk _ (fun _ => by rw [ej]; trivial) (fun w h => by rw [ew] at h; cases h)
      · have h1' := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
        rw [hcnt] at h0
        have : (JMach.act xs M.mem T).2.2 = 1 := by rw [h1']
        rw [hcnt] at this
        rw [h0] at this
        cases this

/-- **One thread is at rest after `O(n + J K log K)` actions when rules
may join up to `J` segments**: at most
`7 |agents| + 2 K + J (4 K log (K + 1) + 6 K) + n (C + D + 1 + 9 J) + 7 C n`,
where `n` is the number of steps to the normal form and `K = |wires| + D n`,
for a system whose rules write at most `C` agents and `D` segments and join
at most `J` segments, doing nothing else when they join. -/
theorem JMach.rests_multi {J : Nat} (hJ : xs.JoinsAtMost J) (hP : xs.PureJoins) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') :
    ∀ i, 7 * X.agents.length + 2 * (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) + 7 * (C * n) < i →
      ((JMach.init X 1).trace xs (fun _ => 0) i).1.resting = true := by
  classical
  have live := JMach.trace_live (xs := xs) (fun _ => 0) (JMach.init_live hX Nat.one_pos)
  have run : ∀ i, MRun xs.sys ((JMach.init X 1).trace xs (fun _ => 0) i).2 (Mach.init X.toNet)
      ((JMach.init X 1).trace xs (fun _ => 0) i).1.toMach := by
    intro i
    have h := JMach.trace_run xs (fun _ => 0) (JMach.init X 1) i
    rw [JMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((JMach.init X 1).trace xs (fun _ => 0) i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  have one : ∀ i, ∃ T, ((JMach.init X 1).trace xs (fun _ => 0) i).1.ths = [T] := by
    intro i
    apply JMach.one_thread
    rw [JMach.trace_length]
    simp [JMach.init]
  have hA : ∀ i, ((JMach.init X 1).trace xs (fun _ => 0) i).1.toW.heads ≤
      X.agents.length + (C - 2) * n := by
    intro i
    have h := (JMach.trace_sizes (fun _ => 0) (JMach.init X 1) hb i).2
    rw [JMach.init_toW, WMach.init_heads] at h
    exact Nat.le_trans h (Nat.add_le_add_left (Nat.mul_le_mul_left (C - 2) (bound i)) _)
  have nd : ∀ i, (((JMach.init X 1).trace xs (fun _ => 0) i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact JMach.step_nodup (live i) ih 0
  have ahead : ∀ i, ((JMach.init X 1).trace xs (fun _ => 0) i).1.toW.toX.Ahead N' :=
    fun i => XMach.ahead_of_run (M := ((JMach.init X 1).trace xs (fun _ => 0) i).1.toW.toX)
      (live i).inv hX (run i) hs hn
  have born := JMach.born_inv hb live ahead
  have hN' := Steps.wf hX hs
  have hH := XNet.normal_sized hX hb hs hn
  generalize hK : X.wires.length + D * n = K at hH
  generalize hAA : X.agents.length + (C - 2) * n = A at hA
  have hR : ∀ i, N'.scan K (JMach.born xs (fun _ => 0) (JMach.init X 1) i) ≤ 7 * (C * n) + K := by
    intro i
    obtain ⟨h₁, -, h₃, h₄⟩ := born i
    have := Net.scan_le hH _ h₁ h₃
    have h5 : C * ((JMach.init X 1).trace xs (fun _ => 0) i).2 ≤ C * n :=
      Nat.mul_le_mul_left C (bound i)
    omega
  obtain ⟨W, hWK, hWl⟩ := hH.fin
  let l : List Id := (dedupList (W.map fun e => e.1.1)).filter
    fun k => decide (∀ x y, N'.link (k, 0) x → N'.link (k, 0) y → x = y)
  have hlnd : l.Nodup := (dedupList_nodup _).filter _
  have hok : ∀ j, PayOk xs.sys.ar W l ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal := by
    intro j
    have hG := (live j).inv.wf
    refine ⟨hG, fun u v h => hWl ((ahead j).link h), fun k γ hk => ?_⟩
    have hE : ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal.End xs.sys.ar (k, 0) :=
      .inr ⟨γ, hk, Nat.zero_le _⟩
    obtain ⟨q, hq⟩ := hG.end_wired hE
    refine List.mem_filter.2 ⟨mem_dedupList.2 (List.mem_map.2 ⟨_, hWl ((ahead j).link hq), rfl⟩),
      decide_eq_true fun x y hx hy => ?_⟩
    have hu : ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal.Used k := .inl ⟨γ, hk⟩
    exact hG.end_unique hE ((ahead j).principal hu hx) ((ahead j).principal hu hy)
  -- the measure at the end of the run, and at the start
  have hΦ : ∀ j, payΦ K W l ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal ≤
      4 * (K * Nat.log2 (K + 1)) + 6 * K := by
    intro j
    have hmono : payΦ K W l ((JMach.init X 1).trace xs (fun _ => 0) j).1.toMach.goal ≤
        payΦ K W l N' := payΦ_mono fun h => (ahead j).link h
    have hle := payΦ_le_ends (K := K) hN'.symm hN'.deg (fun h => hWl h) hlnd
      (fun k hk x y hx hy => of_decide_eq_true (List.mem_filter.1 hk).2 x y hx hy)
    have hllen : l.length ≤ W.length :=
      Nat.le_trans (List.length_filter_le _ _)
        (Nat.le_trans (dedupList_length _) (Nat.le_of_eq (List.length_map _)))
    have hmul₁ : W.length * Nat.log2 (K + 1) ≤ K * Nat.log2 (K + 1) := Nat.mul_le_mul_right _ hWK
    omega
  have h0 : JMach.potV0 N' K A (JMach.init X 1) ≤ 7 * X.agents.length + K := by
    obtain ⟨-, pr⟩ := Steps.links hX hs
    have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
    have hscan : N'.scan K X.agents ≤ 7 * X.agents.length + K :=
      Net.scan_le hH X.agents hnd fun e he q q' h h' =>
        hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
          (pr (.inl ⟨e.2, hag e he⟩) h')
    show N'.scan K (X.agents.drop 0 ++ X.agents.take 0) ≤ _
    simpa using hscan
  -- while no action has been at rest, each lowers the measure
  have key : ∀ i, (∀ j, j < i → ¬ ((JMach.init X 1).trace xs (fun _ => 0) j).1.AtRest 0) →
      ∃ b, ((JMach.init X 1).trace xs (fun _ => 0) i).1.OwesM N' K b ∧
        i + JMach.potV0 N' K A ((JMach.init X 1).trace xs (fun _ => 0) i).1 + b +
            J * payΦ K W l X.toNet ≤
          JMach.potV0 N' K A (JMach.init X 1) +
            J * payΦ K W l ((JMach.init X 1).trace xs (fun _ => 0) i).1.toMach.goal +
            ((JMach.init X 1).trace xs (fun _ => 0) i).2 * (C + D + 1 + 9 * J) +
            N'.scan K (JMach.born xs (fun _ => 0) (JMach.init X 1) i) := by
    intro i
    induction i with
    | zero =>
      intro _
      have eg : (JMach.init X 1).toMach.goal = X.toNet := by
        rw [JMach.init_toMach X 1]
        exact congrArg CState.goal (Mach.init_quiet X.toNet).abs
      refine ⟨0, fun T hT => ?_, ?_⟩
      · change (JMach.init X 1).ths[0]? = some T at hT
        simp only [JMach.init, List.range_one, List.map_cons, List.map_nil,
          List.getElem?_cons_zero, Option.some.injEq] at hT
        subst hT
        refine ⟨fun w h => ?_, fun _ => trivial⟩
        cases h
      · show 0 + JMach.potV0 N' K A (JMach.init X 1) + 0 + _ ≤ _ +
          J * payΦ K W l (JMach.init X 1).toMach.goal + 0 * (C + D + 1 + 9 * J) + N'.scan K []
        rw [eg]
        have : N'.scan K ([] : List (Id × S)) = 0 := rfl
        omega
    | succ i ih =>
      intro hno
      obtain ⟨b, hb', hle⟩ := ih fun j hj => hno j (by omega)
      obtain ⟨T, h1⟩ := one i
      have ht : ((JMach.init X 1).trace xs (fun _ => 0) i).1.ths[0]? = some T := by
        rw [h1]; rfl
      have hsucc : ((JMach.init X 1).trace xs (fun _ => 0) (i + 1)) =
          ((((JMach.init X 1).trace xs (fun _ => 0) i).1.step xs 0).1,
          ((JMach.init X 1).trace xs (fun _ => 0) i).2 +
            (((JMach.init X 1).trace xs (fun _ => 0) i).1.step xs 0).2) := rfl
      have hbs : JMach.born xs (fun _ => 0) (JMach.init X 1) (i + 1) =
          JMach.born xs (fun _ => 0) (JMach.init X 1) i ++
            JMach.stepKids xs ((JMach.init X 1).trace xs (fun _ => 0) i).1 0 := rfl
      have hok' := hok (i + 1)
      have hM' := ahead (i + 1)
      rw [hsucc] at hok' hM'
      rcases JMach.total_step_multi hJ hP (live i) h1 (nd i) hb hH (ahead i) hM' (hA i) hWK
          (hok i) hok' hb' with ⟨hto, hst⟩ | ⟨b', hb'', hstep⟩
      · exfalso
        obtain ⟨todo, st, g, js, wk⟩ := T
        dsimp only at hto hst
        subst hto hst
        exact hno i (by omega) ⟨g, js, wk, ht⟩
      · refine ⟨b', ?_, ?_⟩
        · rw [hsucc]
          exact hb''
        · have hp : JMach.potV0 N' K A ((JMach.init X 1).trace xs (fun _ => 0) (i + 1)).1 =
              potV N' K A
                (JMach.act xs ((JMach.init X 1).trace xs (fun _ => 0) i).1.mem T).2.1 := by
            rw [hsucc]
            unfold JMach.potV0
            have es := JMach.step_eq
              (X₁ := (JMach.act xs ((JMach.init X 1).trace xs (fun _ => 0) i).1.mem T).1)
              (T₁ := (JMach.act xs ((JMach.init X 1).trace xs (fun _ => 0) i).1.mem T).2.1)
              (c := (JMach.act xs ((JMach.init X 1).trace xs (fun _ => 0) i).1.mem T).2.2) ht rfl
            rw [es, h1]
            rfl
          have hp0 : JMach.potV0 N' K A ((JMach.init X 1).trace xs (fun _ => 0) i).1 =
              potV N' K A T := by
            unfold JMach.potV0
            rw [ht]
          rw [hp, hbs, Net.scan_append, hsucc]
          rw [hp0] at hle
          dsimp only
          rw [Nat.add_mul]
          omega
  intro i hi
  -- some action before was at rest, and a thread at rest stays at rest
  have hrest : ∃ j, j ≤ i ∧ ((JMach.init X 1).trace xs (fun _ => 0) j).1.AtRest 0 := by
    refine Classical.byContradiction fun hno => ?_
    obtain ⟨b, -, hle⟩ := key i fun j hj h => hno ⟨j, by omega, h⟩
    have := Nat.mul_le_mul_left J (hΦ i)
    have := hR i
    have hc : ((JMach.init X 1).trace xs (fun _ => 0) i).2 * (C + D + 1 + 9 * J) ≤
        n * (C + D + 1 + 9 * J) :=
      Nat.mul_le_mul_right _ (bound i)
    omega
  obtain ⟨j, hj, g, js, wk, hT⟩ := hrest
  have stay : ∀ k, j ≤ k →
      ((JMach.init X 1).trace xs (fun _ => 0) k).1.ths[0]? = some ⟨[], .idle, g, js, wk⟩ := by
    intro k hk
    induction k with
    | zero =>
      obtain rfl : j = 0 := by omega
      exact hT
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact JMach.step_rest _ 0 (ih (by omega))
      · obtain rfl : j = k + 1 := by omega
        exact hT
  obtain ⟨T, h1⟩ := one i
  have := stay i hj
  rw [h1] at this
  obtain rfl : T = ⟨[], .idle, g, js, wk⟩ := Option.some.inj this
  unfold JMach.resting
  rw [h1]
  rfl

/-- **At rest, the thread has made all the claims and the memory holds the
normal form.** -/
theorem JMach.rests_multi_final {J : Nat} (hJ : xs.JoinsAtMost J) (hP : xs.PureJoins)
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (i : Nat)
    (hi : 7 * X.agents.length + 2 * (X.wires.length + D * n) +
        J * (4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
          6 * (X.wires.length + D * n)) + n * (C + D + 1 + 9 * J) + 7 * (C * n) < i) :
    ((JMach.init X 1).trace xs (fun _ => 0) i).1.resting = true ∧
      ((JMach.init X 1).trace xs (fun _ => 0) i).2 = n ∧
      ((JMach.init X 1).trace xs (fun _ => 0) i).1.mem.toNet = N' := by
  have hrest := JMach.rests_multi hJ hP hX hnd hb hs hn i hi
  have live := JMach.trace_live (xs := xs) (fun _ => 0) (JMach.init_live hX Nat.one_pos)
  have run := JMach.trace_run xs (fun _ => 0) (JMach.init X 1) i
  rw [JMach.init_toMach] at run
  obtain ⟨hq, hnorm⟩ := (live i).rest hrest
  obtain ⟨-, hu⟩ := run.final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨hrest, e₂.symm, e₁.symm⟩

theorem Comb.dsystem_joinsAtMost : Comb.dsystem.JoinsAtMost 2 :=
  XSys.joinsAtMost_of fun α β R h => by
    cases α <;> cases β <;> cases h <;> decide

theorem Comb.dsystem_pureJoins : Comb.dsystem.PureJoins :=
  XSys.pureJoins_of fun α β R h hj => by
    cases α <;> cases β <;> cases h <;> revert hj <;> decide

theorem Comb.dsystem_bounded : Comb.dsystem.Bounded 4 16 := by
  intro α β R h
  cases α <;> cases β <;> cases h <;> decide

/-- **One thread of the interaction combinators reaches the normal form
after `O(n + K log K)` actions**, `K = |wires| + 16 n`. -/
theorem Comb.rests_multi {X : XNet Comb} (hX : X.toNet.WF Comb.dsystem.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {n : Nat} {N' : Net Comb}
    (hs : Steps (Step Comb.dsystem.sys) n X.toNet N') (hn : Normal (Step Comb.dsystem.sys) N')
    (i : Nat)
    (hi : 7 * X.agents.length + 2 * (X.wires.length + 16 * n) +
        2 * (4 * ((X.wires.length + 16 * n) * Nat.log2 (X.wires.length + 16 * n + 1)) +
          6 * (X.wires.length + 16 * n)) + n * (4 + 16 + 1 + 9 * 2) + 7 * (4 * n) < i) :
    ((JMach.init X 1).trace Comb.dsystem (fun _ => 0) i).1.resting = true ∧
      ((JMach.init X 1).trace Comb.dsystem (fun _ => 0) i).2 = n ∧
      ((JMach.init X 1).trace Comb.dsystem (fun _ => 0) i).1.mem.toNet = N' :=
  JMach.rests_multi_final Comb.dsystem_joinsAtMost Comb.dsystem_pureJoins hX hnd
    Comb.dsystem_bounded hs hn i hi

end INet
