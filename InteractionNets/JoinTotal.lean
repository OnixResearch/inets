import InteractionNets.JoinSystems

/-! # All the actions of one thread

`JMach.walked_log` bounds the actions of walks.  The other actions are
bounded by a measure of the thread that does not count walks (`potV`): it
is the measure of `WorkBound` (`potW`) without the charge of `7 A + K` that
`WMach` needs to scan the whole memory again after a rule that joins; the
program of `JoinWalk` walks instead.  An action that is not part of a walk
lowers it by one at least, except a claim, which raises it by what it
writes; a walk leaves it as it is, except that a walk that finds a pair
puts one agent in the list of the thread.
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- The measure of a thread of `WMach` without the charge for scanning the
memory again. -/
noncomputable def potVw (H : Net S) (K A : Nat) (T : WThread S) : Nat :=
  match T.st with
  | .write as ls => H.scan K T.todo + (as.length + ls.length + 1)
  | _ => potIn H K A T.toX

/-- The charge for scanning the memory again. -/
def againCharge (K A : Nat) (T : WThread S) : Nat :=
  match T.st with
  | .write _ _ => if T.again then 7 * A + K else 0
  | _ => 0

omit [DecidableEq S] in
theorem potW_split (H : Net S) (K A : Nat) (T : WThread S) :
    potW H K A T = potVw H K A T + againCharge K A T := by
  obtain ⟨todo, st, again⟩ := T
  cases st <;> simp [potW, potVw, againCharge]

/-- **The measure of a thread of `JMach` that does not count walks.** -/
noncomputable def potV (H : Net S) (K A : Nat) (T : JThread S) : Nat := potVw H K A T.toW

/-- **An action that is not part of a walk lowers the measure, or is a
claim, which raises it by what it writes at most, or changes nothing at
rest.** -/
theorem JMach.act_potV {M : JMach S} (hL : M.Live xs) (hnd : (M.mem.agents.map Prod.fst).Nodup)
    {C D : Nat} (hb : xs.Bounded C D) {H : Net S} {K A : Nat} (hH : H.Sized K)
    (hM : M.toW.toX.Ahead H) (hA : M.toW.heads ≤ A) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) (hw : ¬ (T.st = .write [] [] ∧ T.again = true)) :
    (JMach.act xs M.mem T = (M.mem, T, 0) ∧ T.todo = [] ∧ T.st = .idle) ∨
      ((JMach.act xs M.mem T).2.2 = 1 ∧
        potV H K A (JMach.act xs M.mem T).2.1 ≤ potV H K A T + (C + D) +
          H.scan K (WMach.actKids xs M.mem T.toW)) ∨
      ((JMach.act xs M.mem T).2.2 = 0 ∧
        potV H K A (JMach.act xs M.mem T).2.1 < potV H K A T) := by
  obtain ⟨e₁, e₂, e₃, -⟩ := JMach.act_shape (xs := xs) M.mem T hw
  have hpv : potV H K A (JMach.act xs M.mem T).2.1 =
      potVw H K A (WMach.act xs M.mem T.toW).2.1 := by
    unfold potV
    rw [e₂]
  by_cases hwr : ∃ as ls, T.st = .write as ls
  · -- writing: one agent or one segment less, or done
    obtain ⟨as, ls, hs⟩ := hwr
    obtain ⟨todo, st, again, js, wk⟩ := T
    change st = _ at hs
    subst hs
    refine .inr (.inr ⟨?_, ?_⟩)
    · rw [e₃]
      cases ls with
      | cons e ls => rfl
      | nil =>
        cases as with
        | cons e as => rfl
        | nil =>
          show (WMach.act xs M.mem ⟨todo, .write [] [], again⟩).2.2 = 0
          unfold WMach.act
          dsimp only
          split <;> rfl
    · rw [hpv]
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        show H.scan K todo + (as.length + ls.length + 1) <
          H.scan K todo + (as.length + (ls.length + 1) + 1)
        omega
      | nil =>
        cases as with
        | cons e as =>
          obtain ⟨i, γ⟩ := e
          show H.scan K todo + (as.length + 0 + 1) < H.scan K todo + ((as.length + 1) + 0 + 1)
          omega
        | nil =>
          cases hag : again with
          | true => exact absurd ⟨rfl, hag⟩ hw
          | false =>
            show H.scan K todo < H.scan K todo + (0 + 0 + 1)
            omega
  · have hnw : ∀ as ls, T.toW.st ≠ .write as ls := fun as ls h => hwr ⟨as, ls, h⟩
    have hag0 : againCharge K A T.toW = 0 := by
      unfold againCharge
      split
      · rename_i as ls h
        exact absurd h (hnw as ls)
      · rfl
    have hT : potW H K A T.toW = potV H K A T := by
      rw [potW_split, hag0, Nat.add_zero]
      rfl
    rcases WMach.act_pot (M := M.toW) hL.inv.wf hnd hb hH hM hA (T := T.toW)
        (hL.sane t T ht) with ⟨e, hto, hst⟩ | ⟨h1, hle⟩ | ⟨h0, hlt⟩
    · obtain ⟨todo, st, again, js, wk⟩ := T
      change todo = [] at hto
      change st = .idle at hst
      subst hto hst
      exact .inl ⟨rfl, rfl, rfl⟩
    · change (WMach.act xs M.mem T.toW).2.2 = 1 at h1
      change potW H K A (WMach.act xs M.mem T.toW).2.1 ≤ potW H K A T.toW + (C + D) +
        H.scan K (WMach.actKids xs M.mem T.toW) +
        (if WMach.actJoins xs M.mem T.toW then 7 * A + K else 0) at hle
      refine .inr (.inl ⟨by rw [e₃]; exact h1, ?_⟩)
      rw [hpv, ← hT]
      -- the claim: its charge for scanning again is the one it is allowed
      rcases WMach.act_count (xs := xs) M.mem T.toW with h0 | ⟨a, b, α, β, R, hs, hh⟩
      · rw [h0] at h1
        cases h1
      have hact := WMach.act_half_some (xs := xs) (X := M.mem) (T := T.toW) hs hh
      have ej : WMach.actJoins xs M.mem T.toW = R.joins xs.sys.ar α β := by
        unfold WMach.actJoins
        rw [hs]
        dsimp only
        rw [hh]
      have hag' : againCharge K A (WMach.act xs M.mem T.toW).2.1 =
          if R.joins xs.sys.ar α β then 7 * A + K else 0 := by
        rw [hact]
        rfl
      rw [potW_split, hag', ej] at hle
      omega
    · change (WMach.act xs M.mem T.toW).2.2 = 0 at h0
      change potW H K A (WMach.act xs M.mem T.toW).2.1 < potW H K A T.toW at hlt
      refine .inr (.inr ⟨by rw [e₃]; exact h0, ?_⟩)
      rw [hpv, ← hT]
      rw [potW_split (T := (WMach.act xs M.mem T.toW).2.1)] at hlt
      omega

omit [DecidableEq S] in
/-- **What a walk has found stays found.** -/
theorem JWalk.found_advance (X : XNet S) {w : JWalk S} {v : Option (Id × S)}
    (h : w.found = some v) : (w.advance X).found = some v := by
  obtain ⟨s₁, s₂, c₁, c₂, t⟩ := w
  unfold JWalk.advance
  dsimp only
  cases c₁ with
  | stop =>
    simp only [JWalk.found] at h
    cases h
    simp [JCur.going, JWalk.found]
  | prin i γ =>
    cases c₂ with
    | go _ _ => simp [JWalk.found] at h
    | stop =>
      simp only [JWalk.found] at h
      cases h
      simp [JCur.going, JWalk.found, JCur.next]
    | prin i' γ' =>
      simp only [JWalk.found] at h
      cases h
      simp [JCur.going, JWalk.found, JCur.next]
  | go a b =>
    cases c₂ with
    | go _ _ => simp [JWalk.found] at h
    | prin _ _ => simp [JWalk.found] at h
    | stop =>
      simp only [JWalk.found] at h
      cases h
      simp only [JCur.going, Bool.true_and, Bool.not_false, Bool.or_true, ite_true]
      cases JCur.next X s₂ (.go a b) <;> rfl

omit [DecidableEq S] in
theorem JWalk.found_iter (X : XNet S) {w : JWalk S} {v : Option (Id × S)}
    (h : w.found = some v) : ∀ n, (JWalk.iter X n w).found = some v
  | 0 => h
  | n + 1 => by
    rw [JWalk.iter_succ]
    exact JWalk.found_advance X (JWalk.found_iter X h n)

omit [DecidableEq S] in
/-- Once a walk has found something within `n` advances, what it found
after one advance is the same. -/
theorem JWalk.found_eq (X : XNet S) {w : JWalk S} {n : Nat} {v v' : Option (Id × S)}
    (hn : 1 ≤ n) (h : (JWalk.iter X n w).found = some v) (h' : (w.advance X).found = some v') :
    v = v' := by
  have e : JWalk.iter X n w = JWalk.iter X (n - 1) (w.advance X) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl
  rw [e, JWalk.found_iter X h'] at h
  exact (Option.some.inj h).symm

omit [DecidableEq S] in
/-- **A path that a trail cannot leave stays one in a larger wiring** when
its two ends gain no segment and a point lies on two segments at most. -/
theorem IsPath.extend {V : Type} {L L' : V → V → Prop} {f : Nat → V} {t : Nat}
    (P : IsPath L f t) (hs : ∀ {u v}, L u v → L v u) (hLL : ∀ {u v}, L u v → L' u v)
    (hd : ∀ {p x y z}, L' p x → L' p y → L' p z → x = y ∨ x = z ∨ y = z)
    (h0 : ∀ x, L' (f 0) x → L (f 0) x) (ht : ∀ x, L' (f t) x → L (f t) x) :
    IsPath L' f t := by
  refine ⟨fun i hi => hLL (P.link i hi), P.inj, fun i q hi hq => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact P.nb 0 q hi (h0 q hq)
  by_cases hit : i = t
  · subst hit
    exact P.nb i q hi (ht q hq)
  have hA : L' (f i) (f (i - 1)) := by
    have := P.link (i - 1) (by omega)
    rw [Nat.sub_add_cancel hpos] at this
    exact hLL (hs this)
  have hB : L' (f i) (f (i + 1)) := hLL (P.link i (by omega))
  rcases hd hA hB hq with e | e | e
  · exact absurd (P.inj _ _ (by omega) (by omega) e) (by omega)
  · exact .inl ⟨hpos, e.symm⟩
  · exact .inr ⟨by omega, e.symm⟩

section Wire

variable {ar : S → Nat} {N : Net S} {X : XNet S} {p o : Port}

omit [DecidableEq S] in
/-- **A walk whose two sides both end without a loop runs along a path
that a trail cannot leave**: the first side backwards, then the second. -/
theorem walk_isPath (hN : N.WF ar) (hX : X.Like N) (hpo : N.link p o) {r₁ r₂ : Nat}
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (h₁ : ∀ i, (JCur.iter X o i (.go o p)).going = true ↔ i < r₁)
    (h₂ : ∀ i, (JCur.iter X p i (.go p o)).going = true ↔ i < r₂)
    (e₁ : ∀ n, N.link (sidePt X o p (r₁ - 1)) n → n = sidePrev X o p (r₁ - 1))
    (e₂ : ∀ n, N.link (sidePt X p o (r₂ - 1)) n → n = sidePrev X p o (r₂ - 1)) :
    IsPath N.link (fun k => if k ≤ r₁ - 1 then sidePt X o p (r₁ - 1 - k)
      else sidePt X p o (k - r₁)) (r₁ + r₂ - 1) := by
  have hop : N.link o p := hN.symm hpo
  obtain ⟨-, l₁, i₁, -⟩ := side_go hN hX hpo (r₁ - 1) ((h₁ _).2 (by omega))
  obtain ⟨-, l₂, i₂, -⟩ := side_go hN hX hop (r₂ - 1) ((h₂ _).2 (by omega))
  have nb₁ := side_nb hN hX hpo hr₁ h₁ e₁
  have nb₂ := side_nb hN hX hop hr₂ h₂ e₂
  have ap : ∀ l k, l ≤ r₂ - 1 → k ≤ r₁ - 1 → sidePt X p o l ≠ sidePt X o p k :=
    fun l k hl hk => sides_apart hN hX hpo hr₁ h₁ h₂ e₁ l (by omega) k hk
  have g0 : sidePt X p o 0 = o := rfl
  have f0 : sidePt X o p 0 = p := rfl
  refine ⟨fun k hk => ?_, fun a b ha hb e => ?_, fun k n hk hn => ?_⟩
  · -- links
    by_cases h₁' : k + 1 ≤ r₁ - 1
    · rw [ite_pos' (by omega), ite_pos' h₁']
      have := l₁ (r₁ - 1 - (k + 1)) (by omega)
      have e : r₁ - 1 - (k + 1) + 1 = r₁ - 1 - k := by omega
      rw [e] at this
      exact hN.symm this
    · by_cases h₂' : k ≤ r₁ - 1
      · obtain rfl : k = r₁ - 1 := by omega
        rw [ite_pos' (Nat.le_refl _), ite_neg' (by omega), Nat.sub_self]
        have e : r₁ - 1 + 1 - r₁ = 0 := by omega
        rw [e, f0, g0]
        exact hpo
      · rw [ite_neg' h₂', ite_neg' (by omega)]
        have := l₂ (k - r₁) (by omega)
        have e : k - r₁ + 1 = k + 1 - r₁ := by omega
        rwa [e] at this
  · -- different points
    split at e <;> split at e
    · have := i₁ _ _ (by omega) (by omega) e
      omega
    · exact absurd e.symm (ap _ _ (by omega) (by omega))
    · exact absurd e (ap _ _ (by omega) (by omega))
    · have := i₂ _ _ (by omega) (by omega) e
      omega
  · -- every point linked to one of them is the one before or after
    split at hn
    · rename_i hk₁
      rcases nb₁ (r₁ - 1 - k) n (by omega) hn with e | ⟨hlt, e⟩
      · unfold sidePrev at e
        split at e
        · rename_i h0
          -- the start of the first side: the next point is the start of the second
          refine .inr ⟨by omega, ?_⟩
          rw [ite_neg' (by omega)]
          have e' : k + 1 - r₁ = 0 := by omega
          rw [e', g0]
          exact e
        · refine .inr ⟨by omega, ?_⟩
          rw [ite_pos' (by omega)]
          rw [e]
          congr 1
      · refine .inl ⟨by omega, ?_⟩
        rw [ite_pos' (by omega), e]
        congr 1
        omega
    · rename_i hk₁
      rcases nb₂ (k - r₁) n (by omega) hn with e | ⟨hlt, e⟩
      · unfold sidePrev at e
        split at e
        · rename_i h0
          refine .inl ⟨by omega, ?_⟩
          rw [ite_pos' (by omega)]
          have e' : r₁ - 1 - (k - 1) = 0 := by omega
          rw [e', f0]
          exact e
        · refine .inl ⟨by omega, ?_⟩
          rw [ite_neg' (by omega), e]
          congr 1
          omega
      · refine .inr ⟨by omega, ?_⟩
        rw [ite_neg' (by omega), e]
        congr 1
        omega

/-- What it costs to take on the agent a walk has found, if any: one scan
of its wire. -/
noncomputable def pushCost (H : Net S) (K : Nat) : Option (Id × S) → Nat
  | some e => H.scan K [e]
  | none => 0

omit [DecidableEq S] in
/-- **The walk of a joined segment, and the scan of the agent it finds,
are paid for by the growth of the measure**, with nine to spare.  `H` is a
wiring ahead of `N` that adds no segment at a principal port of `N`. -/
theorem walk_pays_found {G : Net S} (hN : N.WF ar) (hJ : Joined G N p o) (hX : X.Like N)
    {K : Nat} {W : List (Port × Port)} {l : List Id} (hW : ∀ {u v}, N.link u v → (u, v) ∈ W)
    (hWK : W.length ≤ K) (hl : ∀ i γ, N.agent i γ → i ∈ l) {H : Net S}
    (hHd : ∀ {p x y z}, H.link p x → H.link p y → H.link p z → x = y ∨ x = z ∨ y = z)
    (hNH : ∀ {u v}, N.link u v → H.link u v)
    (hprin : ∀ k γ q, N.agent k γ → H.link (k, 0) q → N.link (k, 0) q) :
    ∃ n v, 1 ≤ n ∧ (JWalk.iter X n (JWalk.start p o)).found = some v ∧
      n + 1 + pushCost H K v + payΦ K W l G ≤ 9 + payΦ K W l N := by
  obtain ⟨r₁, hr₁, -, h₁⟩ := side_len hN hX hJ.pair hW
  obtain ⟨r₂, hr₂, -, h₂⟩ := side_len hN hX (hN.symm hJ.pair) hW
  have ng₁ : (JCur.iter X o r₁ (.go o p)).going = false := by
    cases hg : (JCur.iter X o r₁ (.go o p)).going
    · rfl
    · exact absurd ((h₁ _).1 hg) (Nat.lt_irrefl _)
  have ng₂ : (JCur.iter X p r₂ (.go p o)).going = false := by
    cases hg : (JCur.iter X p r₂ (.go p o)).going
    · rfl
    · exact absurd ((h₂ _).1 hg) (Nat.lt_irrefl _)
  -- after `r₁ + r₂` advances, both sides are done
  have hend : JWalk.iter X (r₁ + r₂) (JWalk.start p o) =
      ⟨p, o, JCur.iter X o r₁ (.go o p), JCur.iter X p r₂ (.go p o),
        (JWalk.iter X (r₁ + r₂) (JWalk.start p o)).turn⟩ := by
    obtain ⟨a, b, t, e, hab, ha, hb⟩ := JWalk.iter_shape X (JWalk.start p o) h₁ h₂ (r₁ + r₂)
    have hab' : a = r₁ ∧ b ≥ r₂ := by omega
    obtain ⟨rfl, hb'⟩ := hab'
    have eb : JCur.iter X p b (.go p o) = JCur.iter X p r₂ (.go p o) := JCur.iter_rest ng₂ b hb'
    rw [e]
    show (⟨p, o, _, JCur.iter X p b (.go p o), t⟩ : JWalk S) = _
    rw [eb]
    rfl
  -- what the prin case costs, both sides reaching principal ports
  have prinCase : ∀ (r r' : Nat), r + r' = r₁ + r₂ →
      2 * r + 2 * r' + payΦ K W l G ≤ 2 + payΦ K W l N →
      ∃ n v, 1 ≤ n ∧ (JWalk.iter X n (JWalk.start p o)).found = some v ∧
        n + 1 + pushCost H K v + payΦ K W l G ≤ 9 + payΦ K W l N := by
    intro r r' hrr hgain
    refine ⟨r₁ + r₂, (JWalk.iter X (r₁ + r₂) (JWalk.start p o)).found.getD none, by omega, ?_, ?_⟩
    · have := JWalk.found_rest (w := JWalk.iter X (r₁ + r₂) (JWalk.start p o))
        (by rw [hend]; exact ng₁) (by rw [hend]; exact ng₂)
      cases hf : (JWalk.iter X (r₁ + r₂) (JWalk.start p o)).found with
      | none => exact absurd hf this
      | some v => rfl
    · rw [hend]
      rcases JCur.rest_cases ng₁ with hs₁ | ⟨i, γ, hp₁⟩
      · rw [hs₁]
        show r₁ + r₂ + 1 + 0 + _ ≤ _
        omega
      rcases JCur.rest_cases ng₂ with hs₂ | ⟨i', γ', hp₂⟩
      · rw [hs₂]
        show r₁ + r₂ + 1 + pushCost H K ((JWalk.found ⟨p, o, _, .stop, _⟩).getD none) + _ ≤ _
        cases JCur.iter X o r₁ (.go o p) <;> (simp only [JWalk.found, Option.getD_some]; try
          simp only [pushCost]) <;> omega
      rw [hp₁, hp₂]
      show r₁ + r₂ + 1 + H.scan K [(i, γ)] + _ ≤ _
      -- both sides end at principal ports: the wire between them is a path of `H`
      rcases side_end hN hX hJ.pair hr₁ h₁ with ⟨-, -, hst⟩ | ⟨e₁, hfin₁⟩
      · rw [hst] at hp₁
        cases hp₁
      rcases side_end hN hX (hN.symm hJ.pair) hr₂ h₂ with ⟨-, -, hst⟩ | ⟨e₂, hfin₂⟩
      · rw [hst] at hp₂
        cases hp₂
      obtain ⟨γ₁, hq₁, h0₁, ha₁⟩ : ∃ γ₁, JCur.iter X o r₁ (.go o p) =
          .prin (sidePt X o p (r₁ - 1)).1 γ₁ ∧ (sidePt X o p (r₁ - 1)).2 = 0 ∧
          N.agent (sidePt X o p (r₁ - 1)).1 γ₁ := by
        rcases hfin₁ with h | h
        · rw [h] at hp₁
          cases hp₁
        · exact h
      obtain ⟨γ₂, -, h0₂, ha₂⟩ : ∃ γ₂, JCur.iter X p r₂ (.go p o) =
          .prin (sidePt X p o (r₂ - 1)).1 γ₂ ∧ (sidePt X p o (r₂ - 1)).2 = 0 ∧
          N.agent (sidePt X p o (r₂ - 1)).1 γ₂ := by
        rcases hfin₂ with h | h
        · rw [h] at hp₂
          cases hp₂
        · exact h
      rw [hq₁] at hp₁
      obtain ⟨rfl, -⟩ : (sidePt X o p (r₁ - 1)).1 = i ∧ γ₁ = γ := by
        cases hp₁
        exact ⟨rfl, rfl⟩
      have P := walk_isPath hN hX hJ.pair hr₁ hr₂ h₁ h₂ e₁ e₂
      have hpt₁ : sidePt X o p (r₁ - 1) = ((sidePt X o p (r₁ - 1)).1, 0) := Prod.ext rfl h0₁
      have hpt₂ : sidePt X p o (r₂ - 1) = ((sidePt X p o (r₂ - 1)).1, 0) := Prod.ext rfl h0₂
      have PH := P.extend hN.symm hNH hHd (fun x hx => by
          simp only [ite_pos' (Nat.zero_le (r₁ - 1)), Nat.sub_zero] at hx ⊢
          rw [hpt₁] at hx ⊢
          exact hprin _ _ x ha₁ hx)
        (fun x hx => by
          simp only [ite_neg' (show ¬ r₁ + r₂ - 1 ≤ r₁ - 1 by omega)] at hx ⊢
          have e : r₁ + r₂ - 1 - r₁ = r₂ - 1 := by omega
          rw [e] at hx ⊢
          rw [hpt₂] at hx ⊢
          exact hprin _ _ x ha₂ hx)
      have hfar := PH.lfar_le (j := 0) (Nat.zero_le _) K
      simp only [ite_pos' (Nat.zero_le (r₁ - 1)), Nat.sub_zero] at hfar
      have hmax : max (0 + 1) (r₁ + r₂ - 1 + 1) = r₁ + r₂ := by
        simp only [Nat.max_def]
        split <;> omega
      rw [hmax] at hfar
      show r₁ + r₂ + 1 + (H.far K ((sidePt X o p (r₁ - 1)).1, 0) + 6 + 0) + _ ≤ _
      rw [← hpt₁, Net.far_eq_lfar]
      omega
  rcases Nat.lt_or_ge r₂ r₁ with hlt | hle
  · obtain ⟨gs, gp⟩ := side_gain hN hJ.swap hX hW hWK hl hr₂ h₂ h₁ (by omega)
    rcases JCur.rest_cases ng₂ with hs | ⟨i, γ, hp⟩
    · have := gs hs
      refine ⟨2 * r₂, none, by omega, ?_, by show 2 * r₂ + 1 + 0 + _ ≤ _; omega⟩
      rw [JWalk.iter_both X (JWalk.start p o) rfl h₁ h₂ _ (fun m hm => ⟨by omega, by omega⟩)]
      have e : 2 * r₂ / 2 = r₂ := by omega
      show JWalk.found ⟨p, o, _, JCur.iter X p (2 * r₂ / 2) (.go p o), _⟩ = _
      rw [e, hs]
      generalize JCur.iter X (JWalk.start p o).s₂ ((2 * r₂ + 1) / 2) (JWalk.start p o).c₁ = c
      cases c <;> rfl
    · exact prinCase r₂ r₁ (by omega) (gp i γ hp)
  · obtain ⟨gs, gp⟩ := side_gain hN hJ hX hW hWK hl hr₁ h₁ h₂ hle
    rcases JCur.rest_cases ng₁ with hs | ⟨i, γ, hp⟩
    · have := gs hs
      refine ⟨2 * r₁ - 1, none, by omega, ?_, by show 2 * r₁ - 1 + 1 + 0 + _ ≤ _; omega⟩
      rw [JWalk.iter_both X (JWalk.start p o) rfl h₁ h₂ _ (fun m hm => ⟨by omega, by omega⟩)]
      have e : (2 * r₁ - 1 + 1) / 2 = r₁ := by omega
      show JWalk.found ⟨p, o, JCur.iter X o ((2 * r₁ - 1 + 1) / 2) (.go o p), _, _⟩ = _
      rw [e, hs]
      rfl
    · exact prinCase r₁ r₂ (by omega) (gp i γ hp)

end Wire

/-- The agent a walk found, if any, as a list. -/
def foundList : Option (Id × S) → List (Id × S)
  | some e => [e]
  | none => []

omit [DecidableEq S] in
theorem scan_foundList (H : Net S) (K : Nat) (v : Option (Id × S)) (l : List (Id × S)) :
    H.scan K (foundList v ++ l) = pushCost H K v + H.scan K l := by
  rw [Net.scan_append]
  cases v <;> rfl

/-- The end of a walk: the thread takes on the agent found, if any. -/
theorem JMach.act_end (X : XNet S) (T : JThread S) (hs : T.st = .write [] [])
    (ha : T.again = true) {w : JWalk S} (hw : T.walk = some w) {v : Option (Id × S)}
    (hf : (JWalk.advance X w).found = some v) :
    JMach.act xs X T = (X, ⟨foundList v ++ T.todo, T.st, true, T.joins, none⟩, 0) := by
  obtain ⟨todo, st, again, joins, walk⟩ := T
  dsimp only at hs ha hw
  subst hs ha hw
  unfold JMach.act
  cases v with
  | none => simp only [hf]; rfl
  | some e => simp only [hf]; rfl

/-- What the only thread owes to its walks, scans of agents found
included. -/
def JMach.OwesC (H : Net S) (K : Nat) (M : JMach S) (b : Nat) : Prop :=
  ∀ T, M.ths[0]? = some T →
    (∀ w, T.walk = some w → T.joins = [] ∧
      ∃ n v, 1 ≤ n ∧ (JWalk.iter M.mem n w).found = some v ∧ n + pushCost H K v ≤ b) ∧
    (T.walk = none → ∀ p q js, T.joins = (p, q) :: js → js = [] ∧
      ∀ X : XNet S, X.Like M.toMach.goal → ∃ n v, 1 ≤ n ∧
        (JWalk.iter X n (JWalk.start p q)).found = some v ∧ n + 1 + pushCost H K v ≤ b)

/-- **One action of the only thread**: at rest it does nothing; otherwise
it lowers the measure of the thread plus what it owes to walks by one at
least, after adding at a claim what the claim writes, `C + D + 10`, and
the growth of `payΦ`. -/
theorem JMach.total_step (hJ : xs.OneJoin) (hP : xs.PureJoin) {M : JMach S} (hL : M.Live xs)
    {T : JThread S} (h1 : M.ths = [T]) (hnd : (M.mem.agents.map Prod.fst).Nodup)
    {C D : Nat} (hb : xs.Bounded C D) {H : Net S} {K A : Nat} (hH : H.Sized K)
    (hM : M.toW.toX.Ahead H) (hM' : (M.step xs 0).1.toW.toX.Ahead H) (hA : M.toW.heads ≤ A)
    {W : List (Port × Port)} {l : List Id} (hWK : W.length ≤ K)
    (hok : PayOk xs.sys.ar W l M.toMach.goal)
    (hok' : PayOk xs.sys.ar W l (M.step xs 0).1.toMach.goal) {b : Nat}
    (hb' : M.OwesC H K b) :
    (T.todo = [] ∧ T.st = .idle) ∨
      ∃ b', (M.step xs 0).1.OwesC H K b' ∧
        1 + potV H K A ((JMach.act xs M.mem T).2.1) + b' + payΦ K W l M.toMach.goal ≤
          potV H K A T + b + payΦ K W l (M.step xs 0).1.toMach.goal +
            (M.step xs 0).2 * (C + D + 10) + H.scan K (JMach.stepKids xs M 0) := by
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
      ∀ p q js, (JMach.act xs M.mem T).2.1.joins = (p, q) :: js → js = [] ∧
        ∀ X : XNet S, X.Like (M.step xs 0).1.toMach.goal → ∃ n v, 1 ≤ n ∧
          (JWalk.iter X n (JWalk.start p q)).found = some v ∧ n + 1 + pushCost H K v ≤ b') →
      (∀ w, (JMach.act xs M.mem T).2.1.walk = some w → (JMach.act xs M.mem T).2.1.joins = [] ∧
        ∃ n v, 1 ≤ n ∧ (JWalk.iter (JMach.act xs M.mem T).1 n w).found = some v ∧
          n + pushCost H K v ≤ b') →
      (M.step xs 0).1.OwesC H K b' := by
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
    have pv : ∀ todo', potV H K A ⟨todo', .write [] [], true, [], none⟩ =
        H.scan K todo' + (0 + 0 + 1) := fun _ => rfl
    obtain ⟨todo, st, again, joins, walk⟩ := T
    obtain ⟨hst, hag⟩ := hw
    dsimp only at hst hag
    subst hst hag
    have pvT : ∀ (js : List (Port × Port)) (wk : Option (JWalk S)) (todo' : List (Id × S)),
        potV H K A ⟨todo', .write [] [], true, js, wk⟩ = H.scan K todo' + (0 + 0 + 1) :=
      fun _ _ _ => rfl
    cases walk with
    | some w =>
      obtain ⟨hjn, n, v, hn1, hfn, hnb⟩ := hbw w rfl
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
          refine ⟨hjn, n - 1, v, by omega, ?_, by omega⟩
          have e : JWalk.iter M.mem n w = JWalk.iter M.mem (n - 1) (w.advance M.mem) := by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rfl
          rw [← e]
          exact hfn
        · rw [hact, pvT, pvT]
          have := Nat.le_trans (Nat.le_add_right n (pushCost H K v)) hnb
          omega
      | some v' =>
        have hvv := JWalk.found_eq M.mem hn1 hfn hf
        subst hvv
        have hact := JMach.act_end (xs := xs) M.mem ⟨todo, .write [] [], true, joins, some w⟩ rfl
          rfl rfl hf
        refine ⟨b - 1 - pushCost H K v, mk _ (fun _ p q js h => ?_) (fun w' h => ?_), ?_⟩
        · rw [hact, hjn] at h
          cases h
        · rw [hact] at h
          cases h
        · rw [hact, pvT, pvT]
          rw [scan_foundList]
          dsimp only
          omega
    | none =>
      cases joins with
      | cons pq js =>
        obtain ⟨p, q⟩ := pq
        obtain ⟨hjs, hX⟩ := hbj rfl p q js rfl
        subst hjs
        obtain ⟨n, v, hn1, hfn, hnb⟩ := hX M.mem (JMach.like_goal h1 rfl)
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, [(p, q)], none⟩ =
            (M.mem, ⟨todo, .write [] [], true, [], some (JWalk.start p q)⟩, 0) := rfl
        refine ⟨b - 1, mk _ (fun h => by rw [hact] at h; cases h) (fun w' h => ?_), ?_⟩
        · rw [hact] at h ⊢
          cases h
          exact ⟨rfl, n, v, hn1, hfn, by omega⟩
        · rw [hact, pvT, pvT]
          omega
      | nil =>
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, [], none⟩ =
            (M.mem, ⟨todo, .idle, false, [], none⟩, 0) := rfl
        refine ⟨b, mk _ (fun _ p q js h => by rw [hact] at h; cases h)
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
      refine ⟨9 + payΦ K W l (M.toMach.goal.fire a b₀ R.toRhs) - payΦ K W l M.toMach.goal,
        mk _ (fun _ p q js hj => ?_) (fun w h => by rw [hact] at h; cases h), ?_⟩
      · rw [hact] at hj
        have hl := hJ α β R a b₀ hR
        change R.joinPairs xs.sys.ar a b₀ α β = (p, q) :: js at hj
        rw [hj] at hl
        have hjs : js = [] := by
          cases js with
          | nil => rfl
          | cons _ _ => simp at hl
        subst hjs
        refine ⟨rfl, fun X hX => ?_⟩
        rw [eg] at hX
        have hJn := hP _ a b₀ α β R p q hok.1 hR rg hj
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
        obtain ⟨n, v, hn1, hfn, hle'⟩ := walk_pays_found hok'.1 hJn hX
          (fun h => hok'.2.1 _ _ h) hWK hok'.2.2 hH.deg hHG hpr
        exact ⟨n, v, hn1, hfn, by omega⟩
      · rw [hk]
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
      · refine mk _ (fun h p q js hj => ?_) (fun w h => by rw [ew, hwn] at h; cases h)
        rw [ej] at hj
        rw [eg]
        exact hbj hwn p q js hj
      · exact mk _ (fun _ p q js h => by rw [ej] at h; cases h)
          (fun w h => by rw [ew] at h; cases h)
      · have h1' := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
        rw [hcnt] at h0
        have : (JMach.act xs M.mem T).2.2 = 1 := by rw [h1']
        rw [hcnt] at this
        rw [h0] at this
        cases this

/-- The measure of the thread numbered `0`. -/
noncomputable def JMach.potV0 (H : Net S) (K A : Nat) (M : JMach S) : Nat :=
  match M.ths[0]? with
  | some T => potV H K A T
  | none => 0

/-- **One thread of the program that walks the joined wires is at rest
after `O(n + K log K)` actions**: at most
`7 |agents| + 2 K + 4 K log (K + 1) + 6 K + n (C + D + 10) + 7 C n`, where
`n` is the number of steps to the normal form and `K = |wires| + D n`, for
a system whose rules write at most `C` agents and `D` segments and join one
segment at most, doing nothing else when they join. -/
theorem JMach.rests_log (hJ : xs.OneJoin) (hP : xs.PureJoin) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') :
    ∀ i, 7 * X.agents.length + 2 * (X.wires.length + D * n) +
        4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        6 * (X.wires.length + D * n) + n * (C + D + 10) + 7 * (C * n) < i →
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
      ∃ b, ((JMach.init X 1).trace xs (fun _ => 0) i).1.OwesC N' K b ∧
        i + JMach.potV0 N' K A ((JMach.init X 1).trace xs (fun _ => 0) i).1 + b +
            payΦ K W l X.toNet ≤
          JMach.potV0 N' K A (JMach.init X 1) +
            payΦ K W l ((JMach.init X 1).trace xs (fun _ => 0) i).1.toMach.goal +
            ((JMach.init X 1).trace xs (fun _ => 0) i).2 * (C + D + 10) +
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
        refine ⟨fun w h => ?_, fun _ p q js h => ?_⟩
        · cases h
        · cases h
      · show 0 + JMach.potV0 N' K A (JMach.init X 1) + 0 + _ ≤ _ +
          payΦ K W l (JMach.init X 1).toMach.goal + 0 * (C + D + 10) + N'.scan K []
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
      rcases JMach.total_step hJ hP (live i) h1 (nd i) hb hH (ahead i) hM' (hA i) hWK (hok i) hok'
          hb' with ⟨hto, hst⟩ | ⟨b', hb'', hstep⟩
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
    have := hΦ i
    have := hR i
    have hc : ((JMach.init X 1).trace xs (fun _ => 0) i).2 * (C + D + 10) ≤ n * (C + D + 10) :=
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

/-- **At rest, after `O(n + K log K)` actions, the thread has made all the
claims and the memory holds the normal form.** -/
theorem JMach.rests_log_final (hJ : xs.OneJoin) (hP : xs.PureJoin) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (i : Nat)
    (hi : 7 * X.agents.length + 2 * (X.wires.length + D * n) +
        4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        6 * (X.wires.length + D * n) + n * (C + D + 10) + 7 * (C * n) < i) :
    ((JMach.init X 1).trace xs (fun _ => 0) i).1.resting = true ∧
      ((JMach.init X 1).trace xs (fun _ => 0) i).2 = n ∧
      ((JMach.init X 1).trace xs (fun _ => 0) i).1.mem.toNet = N' := by
  have hrest := JMach.rests_log hJ hP hX hnd hb hs hn i hi
  have live := JMach.trace_live (xs := xs) (fun _ => 0) (JMach.init_live hX Nat.one_pos)
  have run := JMach.trace_run xs (fun _ => 0) (JMach.init X 1) i
  rw [JMach.init_toMach] at run
  obtain ⟨hq, hnorm⟩ := (live i).rest hrest
  obtain ⟨-, hu⟩ := run.final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨hrest, e₂.symm, e₁.symm⟩

/-- **One thread returns the numeral of the normal form after
`O(n + K log K)` actions**: given more actions than the bound of
`JMach.rests_log`, and at least the value plus one. -/
theorem XNet.jrunRead_log (hJ : xs.OneJoin) (hP : xs.PureJoin) {zero succ : S}
    (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {C D : Nat} (hb : xs.Bounded C D) {n : Nat}
    {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N')
    {p : Port} {v₀ : Nat} (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) (s : Nat)
    (h₁ : 7 * X.agents.length + 2 * (X.wires.length + D * n) +
        4 * ((X.wires.length + D * n) * Nat.log2 (X.wires.length + D * n + 1)) +
        6 * (X.wires.length + D * n) + n * (C + D + 10) + 7 * (C * n) < s)
    (h₃ : v₀ + 1 ≤ s) :
    XNet.jrunRead xs zero succ X p 1 s = some v₀ := by
  have hσ : (fun j => j % 1) = fun _ => 0 := funext fun j => Nat.mod_one j
  obtain ⟨hr, -, e⟩ := JMach.rests_log_final hJ hP hX hnd hb hs hn s h₁
  have hW : ((JMach.init X 1).trace xs (fun _ => 0) s).1.mem.toNet.WF xs.sys.ar := by
    rw [e]
    exact Steps.wf hX hs
  have hnum' : Addition.IsNum xs.sys.ar zero succ
      ((JMach.init X 1).trace xs (fun _ => 0) s).1.mem.toNet p v₀ := by
    rw [e]
    exact hnum
  have hread := XNet.readNum_bounded hzs hW v₀ p hnum'
  have hwl := JMach.trace_wires_le hX hb hs hn 1 (fun _ => 0) s
  unfold XNet.jrunRead
  rw [hσ, ite_pos' hr]
  exact XNet.readNum_mono (by omega) hread h₃

/-- **One thread of arithmetic is at rest after `O(n + K log K)`
actions**, `K = |wires| + 8 n`. -/
theorem Arith.rests_log {X : XNet Arith} (hX : X.toNet.WF Arith.xsys.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {n : Nat} {N' : Net Arith}
    (hs : Steps (Step Arith.xsys.sys) n X.toNet N') (hn : Normal (Step Arith.xsys.sys) N') :
    ∀ i, 7 * X.agents.length + 2 * (X.wires.length + 8 * n) +
        4 * ((X.wires.length + 8 * n) * Nat.log2 (X.wires.length + 8 * n + 1)) +
        6 * (X.wires.length + 8 * n) + n * (2 + 8 + 10) + 7 * (2 * n) < i →
      ((JMach.init X 1).trace Arith.xsys (fun _ => 0) i).1.resting = true :=
  JMach.rests_log Arith.xsys_oneJoin Arith.xsys_pureJoin hX hnd Arith.xsys_bounded hs hn

end INet
