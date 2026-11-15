import InteractionNets.JoinRun
import InteractionNets.WorkBound
import InteractionNets.WorkRun
import InteractionNets.WorkCount

/-! # How many actions the program that walks the joined wires takes

The measure of a thread of `JMach` is the measure `potW` of the thread of
`WMach` it agrees with, and a budget for its walks: for each joined segment
still to walk, two sides and the agent a walk may put in front of the list,
and for the walk under way what each side can still cover in a net ahead of
the goal, as `potIn` measures a thread that follows a wire.  A claim of a
rule that joins pays for its joined segments, at most `D` of them, and
`potW` still charges it a pass, which a walker no longer takes; so the
bound is that of `WMach.fair_bound` with more for each claim that joins,
and the same for a system whose rules join nothing.
-/

namespace INet

variable {S : Type}

/-- The lengths of the trails of `H` from `u` whose last step goes from
`p` to `c`. -/
def TrailFrom (H : Net S) (u p c : Port) (n : Nat) : Prop :=
  ∃ vs, Trail H.link u (c :: p :: vs) ∧ vs.length + 2 = n

theorem Net.trailFrom_le_far (H : Net S) (K : Nat) (u p c : Port) :
    supBelow (TrailFrom H u p c) (K + 1) ≤ H.far K u :=
  supBelow_mono (fun _ ⟨vs, t, e⟩ => ⟨c :: p :: vs, t, e⟩) (K + 1)

/-- What one side of a walk can still cover, and one more for the action
that stops it. -/
noncomputable def JCur.left (H : Net S) (K : Nat) (u : Port) : JCur S → Nat
  | .go p c => H.far K u - supBelow (TrailFrom H u p c) (K + 1) + 1
  | _ => 0

/-- The budget of a thread for its walks. -/
noncomputable def JThread.walkLeft (H : Net S) (K : Nat) (T : JThread S) : Nat :=
  T.joins.length * (3 * K + 12) +
    match T.walk with
    | some w => w.c₁.left H K w.s₂ + w.c₂.left H K w.s₁ + (K + 7)
    | none => 0

/-- **The measure of a thread.** -/
noncomputable def potJ (H : Net S) (K A : Nat) (T : JThread S) : Nat :=
  potW H K A T.toW + T.walkLeft H K

theorem Net.far_le (H : Net S) (K : Nat) (u : Port) : H.far K u ≤ K + 1 :=
  supBelow_le _ _

/-- **A side that moves on along a wire can cover less.** -/
theorem JCur.left_go {H : Net S} {K : Nat} (hH : H.Sized K) {u prev cur n : Port}
    (hl : H.link cur n) (hn : n ≠ prev) (hnu : n ≠ u) {vs' : List Port}
    (tr' : Trail H.link u (n :: cur :: vs')) :
    (JCur.go cur n : JCur S).left H K u < (JCur.go prev cur : JCur S).left H K u := by
  obtain ⟨W, hWK, hW⟩ := hH.fin
  have hlen : ∀ {vs : List Port}, Trail H.link u vs → vs.length ≤ K + 1 := by
    intro vs tr
    have h := tr.length_le W hW
    omega
  have hle' := H.trailFrom_le_far K u cur n
  show H.far K u - supBelow (TrailFrom H u cur n) (K + 1) + 1 <
    H.far K u - supBelow (TrailFrom H u prev cur) (K + 1) + 1
  rcases supBelow_spec (TrailFrom H u prev cur) (K + 1) with h0 | ⟨vs, tr, hvs⟩
  · have hb := hlen tr'
    have hs : vs'.length + 2 ≤ supBelow (TrailFrom H u cur n) (K + 1) :=
      le_supBelow ⟨vs', tr', rfl⟩ (by simp only [List.length_cons] at hb; omega)
    omega
  · have hfr : n ∉ cur :: prev :: vs := by
      rcases Trail.fresh' hH.symm hH.irrefl hH.deg tr hl hn with h | h
      · exact h
      · exact absurd h hnu
    have tr₂ : Trail H.link u (n :: cur :: prev :: vs) := .step tr hl hfr
    have hb := hlen tr₂
    have hs : (prev :: vs).length + 2 ≤ supBelow (TrailFrom H u cur n) (K + 1) :=
      le_supBelow ⟨prev :: vs, tr₂, rfl⟩ (by simp only [List.length_cons] at hb ⊢; omega)
    simp only [List.length_cons] at hs
    omega

section JBound

variable [DecidableEq S] {xs : XSys S}

omit [DecidableEq S] in
/-- A side of a walk still going, or one more for a walk with a side going. -/
theorem JCur.left_pos {H : Net S} {K : Nat} {u : Port} {c : JCur S} (h : c.going = true) :
    0 < c.left H K u := by
  cases c with
  | go p c' => exact Nat.succ_pos _
  | prin i γ => cases h
  | stop => cases h

omit [DecidableEq S] in
/-- **One step of a side that is going can cover less.** -/
theorem JMach.Live.left_next {M : JMach S} (hL : M.Live xs) {H : Net S} {K : Nat}
    (hH : H.Sized K) (hM : ∀ {p q}, M.toMach.goal.link p q → H.link p q) {u v : Port}
    {c : JCur S} (hc : JCur.Ok xs.sys.ar M.toMach.goal u v c) (hgo : c.going = true) :
    (c.next M.mem u).left H K u < c.left H K u := by
  cases c with
  | prin i γ => cases hgo
  | stop => cases hgo
  | go prev cur =>
    cases hnx : JCur.next M.mem u (.go prev cur) with
    | prin i γ => exact JCur.left_pos rfl
    | stop => exact JCur.left_pos rfl
    | go cur' n =>
      have hok := hL.cur_next hc (by rw [hnx]; exact fun h => by cases h)
      rw [hnx] at hok
      obtain ⟨-, hnu, -, vs', tr', -⟩ := hok
      unfold JCur.next at hnx
      dsimp only at hnx
      cases hns : nextSeg M.mem.wires cur prev with
      | none =>
        rw [hns] at hnx
        dsimp only at hnx
        split at hnx
        · split at hnx <;> cases hnx
        · cases hnx
      | some n' =>
        rw [hns] at hnx
        dsimp only at hnx
        split at hnx
        · cases hnx
        · obtain ⟨rfl, rfl⟩ := JCur.go.inj hnx
          obtain ⟨hl, hnp⟩ := nextSeg_spec hns
          exact JCur.left_go hH (hM (.inl hl)) hnp hnu (tr'.mono hM)

omit [DecidableEq S] in
/-- A walk under way has a side still going. -/
theorem JWalk.Ok.going {ar : S → Nat} {G : Net S} {w : JWalk S} (h : JWalk.Ok ar G w) :
    w.c₁.going = true ∨ w.c₂.going = true := by
  obtain ⟨-, -, -, h₁, h₂, hf⟩ := h
  unfold JWalk.found at hf
  cases hc₁ : w.c₁ with
  | go p c => exact .inl rfl
  | stop =>
    rw [hc₁] at h₁
    exact False.elim h₁
  | prin i γ =>
    cases hc₂ : w.c₂ with
    | go p c => exact .inr rfl
    | stop =>
      rw [hc₂] at h₂
      exact False.elim h₂
    | prin j δ =>
      rw [hc₁, hc₂] at hf
      cases hf

omit [DecidableEq S] in
/-- **One step of a walk can cover less.** -/
theorem JMach.Live.advance_left {M : JMach S} (hL : M.Live xs) {H : Net S} {K : Nat}
    (hH : H.Sized K) (hM : ∀ {p q}, M.toMach.goal.link p q → H.link p q) {w : JWalk S}
    (hw : JWalk.Ok xs.sys.ar M.toMach.goal w) :
    (w.advance M.mem).c₁.left H K w.s₂ + (w.advance M.mem).c₂.left H K w.s₁ <
      w.c₁.left H K w.s₂ + w.c₂.left H K w.s₁ := by
  have hg := hw.going
  obtain ⟨-, -, -, h₁, h₂, -⟩ := hw
  unfold JWalk.advance
  split
  · rename_i hcond
    have hgo : w.c₁.going = true := by
      simp only [Bool.and_eq_true] at hcond
      exact hcond.1
    have := hL.left_next hH hM h₁ hgo
    show (w.c₁.next M.mem w.s₂).left H K w.s₂ + w.c₂.left H K w.s₁ < _
    omega
  · rename_i hcond
    have hgo : w.c₂.going = true := by
      rcases hg with h | h
      · cases h2 : w.c₂.going
        · exfalso
          apply hcond
          rw [h, h2]
          simp
        · rfl
      · exact h
    have := hL.left_next hH hM h₂ hgo
    show w.c₁.left H K w.s₂ + (w.c₂.next M.mem w.s₁).left H K w.s₁ < _
    omega

/-- **Away from the end of a rule that joins, an action of `JMach` is the
action of `WMach`**, and keeps the joined segments and the walk of the
thread, empties them, or, for a claim, sets the joined segments of the
rule. -/
theorem JMach.act_shape (X : XNet S) (T : JThread S)
    (hT : ¬ (T.st = .write [] [] ∧ T.again = true)) :
    (JMach.act xs X T).1 = (WMach.act xs X T.toW).1 ∧
      (JMach.act xs X T).2.1.toW = (WMach.act xs X T.toW).2.1 ∧
      (JMach.act xs X T).2.2 = (WMach.act xs X T.toW).2.2 ∧
      (((JMach.act xs X T).2.1.joins = T.joins ∧ (JMach.act xs X T).2.1.walk = T.walk) ∨
        ((JMach.act xs X T).2.1.joins = [] ∧ (JMach.act xs X T).2.1.walk = none) ∨
        ∃ a b α β R, T.st = .half a b α β ∧
          (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) = some R ∧
          (JMach.act xs X T).2.1.joins = R.joinPairs xs.sys.ar a b α β ∧
          (JMach.act xs X T).2.1.walk = none) := by
  obtain ⟨todo, st, again, js, wk⟩ := T
  cases st with
  | idle => exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  | look a α => exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  | seek a α p c => exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  | ready a b α β => exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  | half a b α β =>
    cases hh : (if assoc b X.agents = some β ∧ a ≠ b then xs.rule α β else none) with
    | some R =>
      have e₁ := JMach.act_half_some (xs := xs) (X := X) (T := ⟨todo, .half a b α β, again, js, wk⟩)
        rfl hh
      have e₂ := WMach.act_half_some (xs := xs) (X := X) (T := ⟨todo, .half a b α β, again⟩) rfl hh
      rw [e₁, show JThread.toW ⟨todo, .half a b α β, again, js, wk⟩ =
        ⟨todo, .half a b α β, again⟩ from rfl, e₂]
      exact ⟨rfl, rfl, rfl, .inr (.inr ⟨a, b, α, β, R, rfl, hh, rfl, rfl⟩)⟩
    | none =>
      unfold JMach.act WMach.act
      dsimp only [JThread.toW]
      rw [hh]
      exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  | write as ls =>
    cases as with
    | cons e as =>
      cases ls with
      | cons l ls => exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
      | nil => exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
    | nil =>
      cases ls with
      | cons l ls => exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
      | nil =>
        cases again with
        | false => exact ⟨rfl, rfl, rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
        | true => exact absurd ⟨rfl, rfl⟩ hT

omit [DecidableEq S] in
theorem filterMap_length_mono {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (h : ∀ x, (f x).isSome = true → (g x).isSome = true) :
    ∀ l : List α, (l.filterMap f).length ≤ (l.filterMap g).length
  | [] => Nat.le_refl _
  | x :: l => by
    have ih := filterMap_length_mono f g h l
    simp only [List.filterMap_cons]
    cases hf : f x with
    | none =>
      cases hg : g x with
      | none => exact ih
      | some _ =>
        simp only [List.length_cons]
        omega
    | some _ =>
      have hgs := h x (by rw [hf]; rfl)
      cases hg : g x with
      | none =>
        rw [hg] at hgs
        cases hgs
      | some _ =>
        simp only [List.length_cons]
        omega

omit [DecidableEq S] in
theorem XRhs.joinPairs_length_le {R : XRhs S} {ar : S → Nat} {a b : Id} {α β : S} :
    (R.joinPairs ar a b α β).length ≤ (R.newLinks ar a b α β).length := by
  unfold XRhs.joinPairs XRhs.newLinks XRhs.wiresFrom
  rw [List.filterMap_append, List.length_append]
  have := filterMap_length_mono
    (fun x => match R.wire x with
      | some y => if (!y.isNew && decide (x.rank < y.rank)) = true then
          some (emb a b x, emb a b y) else none
      | none => none)
    (fun x => match R.wire x with
      | some y => if (fun _ => true) y = true then some (emb a b x, emb a b y) else none
      | none => none)
    (fun x h => by
      revert h
      cases R.wire x with
      | none => exact fun h => h
      | some y => exact fun _ => rfl) (ifcPorts ar α β)
  exact Nat.le_trans this (Nat.le_add_right _ _)

omit [DecidableEq S] in
theorem JThread.walkLeft_congr {H : Net S} {K : Nat} {T T' : JThread S} (hj : T'.joins = T.joins)
    (hw : T'.walk = T.walk) : T'.walkLeft H K = T.walkLeft H K := by
  unfold JThread.walkLeft
  rw [hj, hw]

/-- **Every action of a thread is a rest, a claim, or brings its share
down.**  A claim raises the share by the writes of one rule, the trails of
the agents it writes, and, if its rule joins interface ports, a pass and
the walks of its joined segments. -/
theorem JMach.act_pot {M : JMach S} (hL : M.Live xs) (hnd : (M.mem.agents.map Prod.fst).Nodup)
    {C D : Nat} (hb : xs.Bounded C D) {H : Net S} {K A : Nat} (hH : H.Sized K)
    (hM : M.toW.toX.Ahead H) (hA : M.toW.heads ≤ A) {t : Nat} {T : JThread S}
    (ht : M.ths[t]? = some T) :
    (JMach.act xs M.mem T = (M.mem, T, 0) ∧ T.todo = [] ∧ T.st = .idle) ∨
      ((JMach.act xs M.mem T).2.2 = 1 ∧
        potJ H K A (JMach.act xs M.mem T).2.1 ≤ potJ H K A T + (C + D) +
          H.scan K (WMach.actKids xs M.mem T.toW) +
          (if WMach.actJoins xs M.mem T.toW then 7 * A + K + D * (3 * K + 12) else 0)) ∨
      ((JMach.act xs M.mem T).2.2 = 0 ∧
        potJ H K A (JMach.act xs M.mem T).2.1 < potJ H K A T) := by
  have hML : ∀ {p q}, M.toMach.goal.link p q → H.link p q := fun h => hM.link h
  by_cases hw : T.st = .write [] [] ∧ T.again = true
  · obtain ⟨todo, st, again, js, wk⟩ := T
    obtain ⟨hst, hag⟩ := hw
    dsimp only at hst hag
    subst hst hag
    have pw : ∀ todo' : List (Id × S),
        potW H K A ⟨todo', .write [] [], true⟩ = H.scan K todo' + (0 + 0 + 1) + (7 * A + K) :=
      fun _ => rfl
    refine .inr (.inr ?_)
    cases wk with
    | none =>
      cases js with
      | nil =>
        refine ⟨rfl, ?_⟩
        show potW H K A ⟨todo, .idle, false⟩ + JThread.walkLeft H K ⟨todo, .idle, false, [], none⟩ <
          potW H K A ⟨todo, .write [] [], true⟩ +
            JThread.walkLeft H K ⟨todo, .write [] [], true, [], none⟩
        rw [pw]
        show H.scan K todo + (0 * (3 * K + 12) + 0) <
          H.scan K todo + (0 + 0 + 1) + (7 * A + K) + (0 * (3 * K + 12) + 0)
        omega
      | cons pq js =>
        obtain ⟨p, q⟩ := pq
        refine ⟨rfl, ?_⟩
        show potW H K A ⟨todo, .write [] [], true⟩ + (js.length * (3 * K + 12) +
            ((JCur.go q p : JCur S).left H K q + (JCur.go p q : JCur S).left H K p + (K + 7))) <
          potW H K A ⟨todo, .write [] [], true⟩ + ((js.length + 1) * (3 * K + 12) + 0)
        have h₁ : (JCur.go q p : JCur S).left H K q ≤ K + 2 := by
          show H.far K q - _ + 1 ≤ _
          have := H.far_le K q
          omega
        have h₂ : (JCur.go p q : JCur S).left H K p ≤ K + 2 := by
          show H.far K p - _ + 1 ≤ _
          have := H.far_le K p
          omega
        rw [Nat.add_mul]
        omega
    | some w =>
      have hwk := hL.wok t _ w ht rfl
      obtain ⟨e₁, e₂, -, -⟩ := JWalk.advance_cases w M.mem
      have hdec := hL.advance_left hH hML hwk
      have hpos : 0 < w.c₁.left H K w.s₂ + w.c₂.left H K w.s₁ := by
        rcases hwk.going with h | h
        · have := JCur.left_pos (H := H) (K := K) (u := w.s₂) h
          omega
        · have := JCur.left_pos (H := H) (K := K) (u := w.s₁) h
          omega
      cases hf : (w.advance M.mem).found with
      | none =>
        have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, js, some w⟩ =
            (M.mem, ⟨todo, .write [] [], true, js, some (w.advance M.mem)⟩, 0) := by
          unfold JMach.act
          dsimp only
          rw [hf]
          rfl
        rw [hact]
        refine ⟨rfl, ?_⟩
        show potW H K A ⟨todo, .write [] [], true⟩ + (js.length * (3 * K + 12) +
            ((w.advance M.mem).c₁.left H K (w.advance M.mem).s₂ +
              (w.advance M.mem).c₂.left H K (w.advance M.mem).s₁ + (K + 7))) <
          potW H K A ⟨todo, .write [] [], true⟩ + (js.length * (3 * K + 12) +
            (w.c₁.left H K w.s₂ + w.c₂.left H K w.s₁ + (K + 7)))
        rw [e₁, e₂]
        omega
      | some o =>
        cases o with
        | none =>
          have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, js, some w⟩ =
              (M.mem, ⟨todo, .write [] [], true, js, none⟩, 0) := by
            unfold JMach.act
            dsimp only
            rw [hf]
            rfl
          rw [hact]
          refine ⟨rfl, ?_⟩
          show potW H K A ⟨todo, .write [] [], true⟩ + (js.length * (3 * K + 12) + 0) <
            potW H K A ⟨todo, .write [] [], true⟩ + (js.length * (3 * K + 12) +
              (w.c₁.left H K w.s₂ + w.c₂.left H K w.s₁ + (K + 7)))
          omega
        | some e =>
          have hact : JMach.act xs M.mem ⟨todo, .write [] [], true, js, some w⟩ =
              (M.mem, ⟨e :: todo, .write [] [], true, js, none⟩, 0) := by
            unfold JMach.act
            dsimp only
            rw [hf]
            rfl
          rw [hact]
          refine ⟨rfl, ?_⟩
          show potW H K A ⟨e :: todo, .write [] [], true⟩ + (js.length * (3 * K + 12) + 0) <
            potW H K A ⟨todo, .write [] [], true⟩ + (js.length * (3 * K + 12) +
              (w.c₁.left H K w.s₂ + w.c₂.left H K w.s₁ + (K + 7)))
          rw [pw, pw]
          show H.far K (e.1, 0) + 6 + H.scan K todo + (0 + 0 + 1) + (7 * A + K) +
              (js.length * (3 * K + 12) + 0) < _
          have := H.far_le K (e.1, 0)
          omega
  · obtain ⟨e₁, e₂, e₃, hjw⟩ := JMach.act_shape (xs := xs) M.mem T hw
    have hpj : potJ H K A (JMach.act xs M.mem T).2.1 =
        potW H K A (WMach.act xs M.mem T.toW).2.1 + (JMach.act xs M.mem T).2.1.walkLeft H K := by
      unfold potJ
      rw [e₂]
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
      rw [hpj]
      have hwl : (JMach.act xs M.mem T).2.1.walkLeft H K ≤ T.walkLeft H K +
          (if WMach.actJoins xs M.mem T.toW then D * (3 * K + 12) else 0) := by
        rcases hjw with ⟨hj, hw'⟩ | ⟨hj, hw'⟩ | ⟨a, b, α, β, R, hs, hh, hj, hw'⟩
        · rw [JThread.walkLeft_congr hj hw']
          omega
        · show (JMach.act xs M.mem T).2.1.joins.length * (3 * K + 12) + _ ≤ _
          rw [hj, hw']
          simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
          omega
        · show (JMach.act xs M.mem T).2.1.joins.length * (3 * K + 12) + _ ≤ _
          rw [hj, hw']
          have ej : WMach.actJoins xs M.mem T.toW = R.joins xs.sys.ar α β := by
            obtain ⟨todo, st, again, js, wk⟩ := T
            change st = _ at hs
            subst hs
            unfold WMach.actJoins
            dsimp only [JThread.toW]
            rw [hh]
          have hc : assoc b M.mem.agents = some β ∧ a ≠ b := by
            split at hh
            · rename_i hc
              exact hc
            · cases hh
          have hR : xs.rule α β = some R := by
            rw [ite_pos' hc] at hh
            exact hh
          obtain ⟨-, hD⟩ := hb α β R hR
          have hl := Nat.le_trans (Nat.le_trans XRhs.joinPairs_length_le
            (R.newLinks_length xs.sys.ar a b α β)) hD
          rw [ej]
          cases hjo : R.joins xs.sys.ar α β with
          | true =>
            simp only [ite_true, Nat.add_zero]
            have := Nat.mul_le_mul_right (3 * K + 12) hl
            omega
          | false =>
            cases hjp : R.joinPairs xs.sys.ar a b α β with
            | nil => simp
            | cons pq rest =>
              have := XRhs.joins_of_mem (pq := pq) (by rw [hjp]; exact List.mem_cons_self)
              rw [hjo] at this
              cases this
      unfold potJ
      cases hJ : WMach.actJoins xs M.mem T.toW with
      | true =>
        rw [hJ] at hle hwl
        simp only [ite_true] at hle hwl ⊢
        omega
      | false =>
        rw [hJ] at hle hwl
        simp only [Bool.false_eq_true, ite_false] at hle hwl ⊢
        omega
    · change (WMach.act xs M.mem T.toW).2.2 = 0 at h0
      change potW H K A (WMach.act xs M.mem T.toW).2.1 < potW H K A T.toW at hlt
      refine .inr (.inr ⟨by rw [e₃]; exact h0, ?_⟩)
      rw [hpj]
      have hwl : (JMach.act xs M.mem T).2.1.walkLeft H K ≤ T.walkLeft H K := by
        rcases hjw with ⟨hj, hw'⟩ | ⟨hj, hw'⟩ | ⟨a, b, α, β, R, hs, hh, -, -⟩
        · rw [JThread.walkLeft_congr hj hw']
          exact Nat.le_refl _
        · show (JMach.act xs M.mem T).2.1.joins.length * (3 * K + 12) + _ ≤ _
          rw [hj, hw']
          simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
          omega
        · exfalso
          have := JMach.act_half_some (xs := xs) (X := M.mem) hs hh
          rw [this] at e₃
          rw [← e₃] at h0
          cases h0
      unfold potJ
      omega

omit [DecidableEq S] in
theorem XThread.pendLen_st {T T' : XThread S} (h : T.st = T'.st) : T.pendLen = T'.pendLen := by
  unfold XThread.pendLen
  rw [h]

omit [DecidableEq S] in
theorem XThread.owes_st {T T' : XThread S} (h : T.st = T'.st) : T.owes = T'.owes := by
  unfold XThread.owes
  rw [h]

/-- An action adds at most `D` segments and `C - 2` agents to what is
written and still to write, and only when it is a claim. -/
theorem JMach.act_sizes {C D : Nat} (hb : xs.Bounded C D) (X : XNet S) (T : JThread S) :
    (JMach.act xs X T).1.wires.length + (JMach.act xs X T).2.1.toW.toX.pendLen ≤
        X.wires.length + T.toW.toX.pendLen + D * (JMach.act xs X T).2.2 ∧
      (JMach.act xs X T).1.agents.length + (JMach.act xs X T).2.1.toW.toX.owes ≤
        X.agents.length + T.toW.toX.owes + (C - 2) * (JMach.act xs X T).2.2 := by
  rcases JMach.act_agree xs X T with ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₃⟩
  · have h := WMach.act_sizes hb X T.toW
    rw [e₁, e₃, XThread.pendLen_st (T' := (WMach.act xs X T.toW).2.1.toX) e₂,
      XThread.owes_st (T' := (WMach.act xs X T.toW).2.1.toX) e₂]
    exact h
  · rw [e₁, e₃, XThread.pendLen_st (T' := T.toW.toX) e₂, XThread.owes_st (T' := T.toW.toX) e₂]
    omega

theorem JMach.step_length (xs : XSys S) (M : JMach S) (t : Nat) :
    (M.step xs t).1.ths.length = M.ths.length := by
  unfold JMach.step
  split
  · exact List.length_set
  · rfl

theorem JMach.trace_length (xs : XSys S) (σ : Nat → Nat) (M : JMach S) :
    ∀ i, (M.trace xs σ i).1.ths.length = M.ths.length
  | 0 => rfl
  | i + 1 => (JMach.step_length xs _ _).trans (JMach.trace_length xs σ M i)

/-- An action adds at most `D` segments and `C - 2` agents, and only when it
is a claim. -/
theorem JMach.step_sizes {C D : Nat} (hb : xs.Bounded C D) (M : JMach S) (t : Nat) :
    (M.step xs t).1.toW.segs ≤ M.toW.segs + D * (M.step xs t).2 ∧
      (M.step xs t).1.toW.heads ≤ M.toW.heads + (C - 2) * (M.step xs t).2 := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold JMach.step
      rw [ht]
    rw [e]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | some T =>
    have e := JMach.step_eq (xs := xs) ht (rfl : JMach.act xs M.mem T =
      ((JMach.act xs M.mem T).1, (JMach.act xs M.mem T).2.1, (JMach.act xs M.mem T).2.2))
    rw [e]
    obtain ⟨h₁, h₂⟩ := JMach.act_sizes hb M.mem T
    have hw : (M.ths.map JThread.toW)[t]? = some T.toW := JMach.toW_get ht
    have hset : (M.ths.set t (JMach.act xs M.mem T).2.1).map JThread.toW =
        (M.ths.map JThread.toW).set t (JMach.act xs M.mem T).2.1.toW := by
      rw [List.map_set]
    have tp := total_map_set XThread.pendLen (M.ths.map JThread.toW) t T.toW
      (JMach.act xs M.mem T).2.1.toW hw
    have to := total_map_set XThread.owes (M.ths.map JThread.toW) t T.toW
      (JMach.act xs M.mem T).2.1.toW hw
    constructor
    · show (JMach.act xs M.mem T).1.wires.length + total XThread.pendLen
          (((M.ths.set t (JMach.act xs M.mem T).2.1).map JThread.toW).map WThread.toX) ≤
        M.mem.wires.length + total XThread.pendLen ((M.ths.map JThread.toW).map WThread.toX) +
          D * (JMach.act xs M.mem T).2.2
      rw [hset]
      omega
    · show (JMach.act xs M.mem T).1.agents.length + total XThread.owes
          (((M.ths.set t (JMach.act xs M.mem T).2.1).map JThread.toW).map WThread.toX) ≤
        M.mem.agents.length + total XThread.owes ((M.ths.map JThread.toW).map WThread.toX) +
          (C - 2) * (JMach.act xs M.mem T).2.2
      rw [hset]
      omega

/-- Along a run, every claim adds at most `D` segments and `C - 2` agents. -/
theorem JMach.trace_sizes (σ : Nat → Nat) (M : JMach S) {C D : Nat} (hb : xs.Bounded C D) :
    ∀ i, (M.trace xs σ i).1.toW.segs ≤ M.toW.segs + D * (M.trace xs σ i).2 ∧
      (M.trace xs σ i).1.toW.heads ≤ M.toW.heads + (C - 2) * (M.trace xs σ i).2
  | 0 => ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | i + 1 => by
    obtain ⟨h₁, h₂⟩ := JMach.trace_sizes σ M hb i
    obtain ⟨s₁, s₂⟩ := JMach.step_sizes hb (M.trace xs σ i).1 (σ i)
    show ((M.trace xs σ i).1.step xs (σ i)).1.toW.segs ≤
        M.toW.segs + D * ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2) ∧
      ((M.trace xs σ i).1.step xs (σ i)).1.toW.heads ≤
        M.toW.heads + (C - 2) * ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2)
    rw [Nat.mul_add, Nat.mul_add]
    omega

/-- No agent is in memory twice, if none was at the start. -/
theorem JMach.step_nodup {M : JMach S} (hL : M.Live xs)
    (h : (M.mem.agents.map Prod.fst).Nodup) (t : Nat) :
    ((M.step xs t).1.mem.agents.map Prod.fst).Nodup := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold JMach.step
      rw [ht]
    rw [e]
    exact h
  | some T =>
    have e : (M.step xs t).1.mem = (JMach.act xs M.mem T).1 := by
      unfold JMach.step
      rw [ht]
    rw [e]
    have hok := hL.ok ht
    have fresh : ∀ {i : Id} {γ : S}, (∀ δ, ¬ M.mem.toNet.agent i δ) →
        ((M.mem.putAgent i γ).agents.map Prod.fst).Nodup := by
      intro i γ hi
      show (i :: M.mem.agents.map Prod.fst).Nodup
      refine List.nodup_cons.2 ⟨fun hm => ?_, h⟩
      obtain ⟨e', he', ee⟩ := List.mem_map.1 hm
      have hm' : (i, e'.2) ∈ M.mem.agents := by
        rw [← ee]
        exact he'
      exact hi e'.2 hm'
    rcases JMach.act_agree xs M.mem T with ⟨e₁, -, -⟩ | ⟨e₁, -, -⟩
    · rw [e₁]
      rcases WMach.act_agents (xs := xs) M.mem T.toW with e₂ | ⟨a, e₂⟩ |
        ⟨a, b, α, β, es, e₂⟩ | ⟨i, γ, as, es, e₂⟩
      · rw [e₂]
        exact h
      · rw [e₂]
        exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) h
      · rw [e₂]
        change T.st = _ at es
        rw [es] at hok
        exact fresh hok.2
      · rw [e₂]
        refine fresh fun δ hδ => ?_
        have hp : (M.toMach.th t).pendA i γ := by
          show (threadOf ((M.ths.map JThread.toW).map WThread.toX) t).pendA i γ
          rw [threadOf_mapJ_eq ht]
          change T.st = _ at es
          rw [es]
          exact List.mem_cons_self
        exact hL.inv.pend_fresh δ hp (.inl hδ)
    · rw [e₁]
      exact h

/-- The agents written by the action of thread `t`, if it is a claim. -/
def JMach.stepKids (xs : XSys S) (M : JMach S) (t : Nat) : List (Id × S) :=
  match M.ths[t]? with
  | some T => WMach.actKids xs M.mem T.toW
  | none => []

/-- `1` if the action of thread `t` claims by a rule that joins interface
ports. -/
def JMach.stepJoins (xs : XSys S) (M : JMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => if WMach.actJoins xs M.mem T.toW then 1 else 0
  | none => 0

/-- **What an action does to the goal**: nothing, or it fires the pair its
thread claims, and the agents it writes are the children of that firing. -/
theorem JMach.step_goal {M : JMach S} (hL : M.Live xs) (t : Nat) :
    ((M.step xs t).2 = 0 ∧ (M.step xs t).1.toMach.goal = M.toMach.goal ∧
        JMach.stepKids xs M t = [] ∧ JMach.stepJoins xs M t = 0) ∨
      ∃ (a b : Id) (α β : S) (R : XRhs S), xs.rule α β = some R ∧ (M.step xs t).2 = 1 ∧
        Redex xs.sys M.toMach.goal a b α β R.toRhs ∧
        (M.step xs t).1.toMach.goal = M.toMach.goal.fire a b R.toRhs ∧
        Writes a b R.toRhs (R.newAgents a b) (R.newLinks xs.sys.ar a b α β) ∧
        JMach.stepKids xs M t = R.newAgents a b ∧
        JMach.stepJoins xs M t = if R.joins xs.sys.ar α β then 1 else 0 := by
  cases ht : M.ths[t]? with
  | none =>
    have e : M.step xs t = (M, 0) := by
      unfold JMach.step
      rw [ht]
    refine .inl ⟨by rw [e], by rw [e], ?_, ?_⟩
    · unfold JMach.stepKids
      rw [ht]
    · unfold JMach.stepJoins
      rw [ht]
  | some T =>
    have es := JMach.step_eq (xs := xs) ht (rfl : JMach.act xs M.mem T =
      ((JMach.act xs M.mem T).1, (JMach.act xs M.mem T).2.1, (JMach.act xs M.mem T).2.2))
    have hcnt : (JMach.act xs M.mem T).2.2 = (WMach.act xs M.mem T.toW).2.2 := by
      rcases JMach.act_agree xs M.mem T with ⟨-, -, e₃⟩ | ⟨-, -, e₃⟩
      · exact e₃
      · rw [e₃]
        rcases WMach.act_count (xs := xs) M.mem T.toW with h0 | ⟨a, b, α, β, R, hs, hh⟩
        · exact h0.symm
        · exfalso
          have h1 := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
          rw [h1] at e₃
          cases e₃
    rcases WMach.act_count (xs := xs) M.mem T.toW with h0 | ⟨a₀, b₀, α₀, β₀, R, hs, hh⟩
    · obtain ⟨k0, j0⟩ := WMach.act_zero_kids h0
      have hc : (M.step xs t).2 = 0 := by
        rw [es]
        exact hcnt.trans h0
      refine .inl ⟨hc, ?_, ?_, ?_⟩
      · rcases JMach.step_sim xs M t with ⟨e₁, -⟩ | hs'
        · rw [e₁]
        · rw [hc] at hs'
          exact (MStep.sim hL.inv hs').2.goal_zero rfl
      · unfold JMach.stepKids
        rw [ht]
        exact k0
      · unfold JMach.stepJoins
        rw [ht]
        dsimp only
        rw [j0]
        rfl
    · change T.st = _ at hs
      have hact := JMach.act_half_some (xs := xs) (X := M.mem) (T := T) hs hh
      have hc : assoc b₀ M.mem.agents = some β₀ ∧ a₀ ≠ b₀ := by
        split at hh
        · rename_i hc
          exact hc
        · cases hh
      have hR : xs.rule α₀ β₀ = some R := by
        rw [ite_pos' hc] at hh
        exact hh
      obtain ⟨hsys, hw⟩ := xs.writes hc.2 hR
      have e : M.toMach.th t = .half a₀ b₀ α₀ β₀ := by
        rw [← hs]
        exact threadOf_mapJ_eq ht
      obtain ⟨rg, eg⟩ := hL.inv.cas₂_goal e (assoc_mem hc.1) hc.2 hsys hw
      have es' := JMach.step_eq ht hact
      have hmx : ((M.ths.map JThread.toW).map WThread.toX)[t]? = some T.toW.toX := by
        rw [List.getElem?_map, List.getElem?_map, ht]
        rfl
      refine .inr ⟨a₀, b₀, α₀, β₀, R, hR, by rw [es'], rg, ?_, hw, ?_, ?_⟩
      · rw [es']
        show Mach.goal ⟨(M.mem.takeAgent b₀).toNet,
          threadOf (((M.ths.set t _).map JThread.toW).map WThread.toX)⟩ = _
        rw [List.map_set, List.map_set, threadOf_set hmx, XNet.takeAgent_toNet]
        exact eg
      · unfold JMach.stepKids WMach.actKids
        rw [ht]
        dsimp only
        change (match T.st with
          | .half a b α β =>
            match (if assoc b M.mem.agents = some β ∧ a ≠ b then xs.rule α β else none) with
            | some R => R.newAgents a b
            | none => []
          | _ => []) = _
        rw [hs]
        dsimp only
        rw [hh]
      · unfold JMach.stepJoins WMach.actJoins
        rw [ht]
        dsimp only
        change (if (match T.st with
          | .half a b α β =>
            match (if assoc b M.mem.agents = some β ∧ a ≠ b then xs.rule α β else none) with
            | some R => R.joins xs.sys.ar α β
            | none => false
          | _ => false) = true then 1 else 0) = _
        rw [hs]
        dsimp only
        simp only [hh]

theorem JMach.act_count_eq (X : XNet S) (T : JThread S) :
    (JMach.act xs X T).2.2 = (WMach.act xs X T.toW).2.2 := by
  rcases JMach.act_agree xs X T with ⟨-, -, e₃⟩ | ⟨-, -, e₃⟩
  · exact e₃
  · rw [e₃]
    rcases WMach.act_count (xs := xs) X T.toW with h0 | ⟨a, b, α, β, R, hs, hh⟩
    · exact h0.symm
    · exfalso
      have h1 := JMach.act_half_some (xs := xs) (X := X) (T := T) hs hh
      rw [h1] at e₃
      cases e₃

/-- The agents written so far along a run, by the claims that wrote them. -/
def JMach.born (xs : XSys S) (σ : Nat → Nat) (M : JMach S) : Nat → List (Id × S)
  | 0 => []
  | i + 1 => JMach.born xs σ M i ++ JMach.stepKids xs (M.trace xs σ i).1 (σ i)

/-- The claims so far along a run of rules that join interface ports. -/
def JMach.joined (xs : XSys S) (σ : Nat → Nat) (M : JMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => JMach.joined xs σ M i + JMach.stepJoins xs (M.trace xs σ i).1 (σ i)

/-- **The agents written along a run have different names**, all in use in
the goal, and each has one segment at its principal port in a net ahead of
every goal of the run; a claim writes at most `C` of them. -/
theorem JMach.born_inv {X : XNet S} {nt : Nat} {σ : Nat → Nat} {C D : Nat}
    (hb : xs.Bounded C D) {H : Net S}
    (live : ∀ i, ((JMach.init X nt).trace xs σ i).1.Live xs)
    (ahead : ∀ i, ((JMach.init X nt).trace xs σ i).1.toW.toX.Ahead H) :
    ∀ i, ((JMach.born xs σ (JMach.init X nt) i).map Prod.fst).Nodup ∧
      (∀ e, e ∈ JMach.born xs σ (JMach.init X nt) i →
        ((JMach.init X nt).trace xs σ i).1.toMach.goal.Used e.1) ∧
      (∀ e, e ∈ JMach.born xs σ (JMach.init X nt) i → ∀ q q',
        H.link (e.1, 0) q → H.link (e.1, 0) q' → q = q') ∧
      (JMach.born xs σ (JMach.init X nt) i).length ≤ C * ((JMach.init X nt).trace xs σ i).2
  | 0 => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  | i + 1 => by
    obtain ⟨hnd, hu, hl, hlen⟩ := JMach.born_inv hb live ahead i
    have hsucc : ((JMach.init X nt).trace xs σ (i + 1)) =
        ((((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1,
          ((JMach.init X nt).trace xs σ i).2 +
            (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).2) := rfl
    have hbs : JMach.born xs σ (JMach.init X nt) (i + 1) = JMach.born xs σ (JMach.init X nt) i ++
        JMach.stepKids xs ((JMach.init X nt).trace xs σ i).1 (σ i) := rfl
    have hG' := (live (i + 1)).inv.wf
    have hA' := ahead (i + 1)
    rw [hsucc] at hG' hA'
    rw [hbs, hsucc]
    rcases JMach.step_goal (live i) (σ i) with ⟨h0, eg, ek, -⟩ |
      ⟨a, b, α, β, R, hR, h1, rg, eg, hw, ek, -⟩
    · rw [ek, List.append_nil, h0, Nat.add_zero]
      refine ⟨hnd, fun e he => ?_, hl, hlen⟩
      show (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toMach.goal.Used e.1
      rw [eg]
      exact hu e he
    · have hG := (live i).inv.wf
      have site := rg.site hG
      rw [ek, h1]
      have kid : ∀ e, e ∈ R.newAgents a b →
          (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toMach.goal.agent e.1 e.2 ∧
            ∃ o j, e.1 = child a b o j := by
        intro e he
        obtain ⟨o, j, ei, hlab⟩ := hw.agent.1 he
        refine ⟨?_, o, j, ei⟩
        rw [eg]
        exact .inr ⟨o, j, ei, hlab⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.map_append]
        refine List.nodup_append.2 ⟨hnd, hw.nodup, ?_⟩
        intro x hx y hy hxy
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 hy
        obtain ⟨-, o, j, ej⟩ := kid e' he'
        exact site.not_used_child o j (by rw [← ej, ← hxy]; exact hu e he)
      · intro e he
        rcases List.mem_append.1 he with he | he
        · rw [eg]
          exact site.used_fire_mono R.toRhs (hu e he)
        · exact .inl ⟨e.2, (kid e he).1⟩
      · intro e he q q' h h'
        rcases List.mem_append.1 he with he | he
        · exact hl e he q q' h h'
        · have hag := (kid e he).1
          have hU : (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1.toMach.goal.Used e.1 :=
            .inl ⟨e.2, hag⟩
          exact hG'.end_unique (.inr ⟨e.2, hag, Nat.zero_le _⟩) (hA'.principal hU h)
            (hA'.principal hU h')
      · rw [List.length_append]
        have hk : (R.newAgents a b).length ≤ C := by
          obtain ⟨hC, -⟩ := hb α β R hR
          exact Nat.le_trans (R.newAgents_length a b) hC
        rw [Nat.mul_add, Nat.mul_one]
        omega

theorem JMach.step_other (M : JMach S) {s t : Nat} (h : s ≠ t) :
    (M.step xs s).1.ths[t]? = M.ths[t]? := by
  unfold JMach.step
  split
  · exact List.getElem?_set_ne h
  · rfl

theorem JMach.rest_act (X : XNet S) (g : Bool) (js : List (Port × Port))
    (wk : Option (JWalk S)) :
    JMach.act xs X ⟨[], .idle, g, js, wk⟩ = (X, ⟨[], .idle, g, js, wk⟩, 0) := rfl

/-- A thread at rest stays at rest, whoever acts. -/
theorem JMach.step_rest (M : JMach S) (s : Nat) {t : Nat} {g : Bool}
    {js : List (Port × Port)} {wk : Option (JWalk S)}
    (h : M.ths[t]? = some ⟨[], .idle, g, js, wk⟩) :
    (M.step xs s).1.ths[t]? = some ⟨[], .idle, g, js, wk⟩ := by
  by_cases e : s = t
  · subst e
    rw [JMach.step_eq h (JMach.rest_act M.mem g js wk), set_self M.ths s _ h]
    exact h
  · rw [JMach.step_other M e]
    exact h

/-- The share of thread `t`. -/
noncomputable def JMach.potAt (M : JMach S) (H : Net S) (K A t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => potJ H K A T
  | none => 0

omit [DecidableEq S] in
theorem JMach.potAt_eq {M : JMach S} {t : Nat} {T : JThread S} (ht : M.ths[t]? = some T)
    (H : Net S) (K A : Nat) : M.potAt H K A t = potJ H K A T := by
  unfold JMach.potAt
  rw [ht]

/-- The thread is idle with nothing left to try. -/
def JMach.AtRest (M : JMach S) (t : Nat) : Prop :=
  ∃ g js wk, M.ths[t]? = some ⟨[], .idle, g, js, wk⟩

/-- **A bound on the length of a fair run of the program that walks the
joined wires.**  Take a well-formed net with no name twice, whose
normal form is `n` steps away, a system whose rules write at most `C`
agents and `D` segments, and a schedule in which every thread acts in every
window of `F` actions.  If at most `m` of the claims along the run are of
rules that join interface ports, the run is at rest with the normal form
after `F * (B + 1)` actions, where `B` is one pass over the agents at the
start, the writes of each claim, a pass and the walks of its joined
segments for each claim that joins, and one pass over all the agents the
claims can write. -/
theorem JMach.fair_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F m : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u)
    (hm : ∀ i, JMach.joined xs σ (JMach.init X nt) i ≤ m) :
    ∀ i, F * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
          m * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) +
            D * (3 * (X.wires.length + D * n) + 12)) +
          (7 * (C * n) + (X.wires.length + D * n)) + 1) ≤ i →
      ((JMach.init X nt).trace xs σ i).1.resting = true ∧
      ((JMach.init X nt).trace xs σ i).2 = n ∧
      ((JMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  -- the run and what holds along it
  have live := JMach.trace_live (xs := xs) σ (JMach.init_live hX hnt)
  have run : ∀ i, MRun xs.sys ((JMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((JMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := JMach.trace_run xs σ (JMach.init X nt) i
    rw [JMach.init_toMach] at h
    exact h
  have bound : ∀ i, ((JMach.init X nt).trace xs σ i).2 ≤ n :=
    fun i => (run i).claims_le hX hs hn
  have len : ∀ i, ((JMach.init X nt).trace xs σ i).1.ths.length = nt := by
    intro i
    rw [JMach.trace_length]
    show ((List.range nt).map _).length = nt
    rw [List.length_map, List.length_range]
  have hA : ∀ i, ((JMach.init X nt).trace xs σ i).1.toW.heads ≤ X.agents.length + (C - 2) * n := by
    intro i
    have h := (JMach.trace_sizes σ (JMach.init X nt) hb i).2
    rw [JMach.init_toW, WMach.init_heads] at h
    exact Nat.le_trans h (Nat.add_le_add_left (Nat.mul_le_mul_left (C - 2) (bound i)) _)
  have nd : ∀ i, (((JMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
    intro i
    induction i with
    | zero => exact hnd
    | succ i ih => exact JMach.step_nodup (live i) ih (σ i)
  have hH := XNet.normal_sized hX hb hs hn
  have ahead : ∀ i, ((JMach.init X nt).trace xs σ i).1.toW.toX.Ahead N' :=
    fun i => XMach.ahead_of_run (M := ((JMach.init X nt).trace xs σ i).1.toW.toX) (live i).inv hX
      (run i) hs hn
  have born := JMach.born_inv hb live ahead
  -- names for the quantities
  generalize hK : X.wires.length + D * n = K at hH
  generalize hAA : X.agents.length + (C - 2) * n = A at hA
  have hR : ∀ i, N'.scan K (JMach.born xs σ (JMach.init X nt) i) ≤ 7 * (C * n) + K := by
    intro i
    obtain ⟨h₁, -, h₃, h₄⟩ := born i
    have := Net.scan_le hH _ h₁ h₃
    have h5 : C * ((JMach.init X nt).trace xs σ i).2 ≤ C * n :=
      Nat.mul_le_mul_left C (bound i)
    omega
  let Ψ : Nat → Nat → Nat := fun t i =>
    ((JMach.init X nt).trace xs σ i).1.potAt N' K A t +
      (n - ((JMach.init X nt).trace xs σ i).2) * (C + D + 1) +
      (m - JMach.joined xs σ (JMach.init X nt) i) * (7 * A + K + D * (3 * K + 12)) +
      (7 * (C * n) + K - N'.scan K (JMach.born xs σ (JMach.init X nt) i))
  have each : ∀ t, t < nt → ∀ i,
      F * ((7 * X.agents.length + K) + n * (C + D + 1) + m * (7 * A + K + D * (3 * K + 12)) +
        (7 * (C * n) + K) + 1) ≤ i → ((JMach.init X nt).trace xs σ i).1.AtRest t := by
    intro t ht
    have h0 : Ψ t 0 ≤ (7 * X.agents.length + K) + n * (C + D + 1) +
        m * (7 * A + K + D * (3 * K + 12)) +
        (7 * (C * n) + K) := by
      have hT := JMach.init_thread X ht
      have ep : ((JMach.init X nt).trace xs σ 0).1.potAt N' K A t = N'.scan K X.agents := by
        show (JMach.init X nt).potAt N' K A t = _
        rw [JMach.potAt_eq hT]
        show N'.scan K (X.agents.drop t ++ X.agents.take t) + (0 * (3 * K + 12) + 0) = _
        rw [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
        have e : N'.scan K X.agents = N'.scan K (X.agents.take t) +
            N'.scan K (X.agents.drop t) := by
          rw [← Net.scan_append, List.take_append_drop]
        rw [Net.scan_append, e]
        exact Nat.add_comm _ _
      obtain ⟨-, pr⟩ := Steps.links hX hs
      have hag : ∀ e : Id × S, e ∈ X.agents → X.toNet.agent e.1 e.2 := fun _ he => he
      have hscan : N'.scan K X.agents ≤ 7 * X.agents.length + K :=
        Net.scan_le hH X.agents hnd fun e he q q' h h' =>
          hX.end_unique (.inr ⟨e.2, hag e he, Nat.zero_le _⟩) (pr (.inl ⟨e.2, hag e he⟩) h)
            (pr (.inl ⟨e.2, hag e he⟩) h')
      show ((JMach.init X nt).trace xs σ 0).1.potAt N' K A t + (n - 0) * (C + D + 1) +
        (m - 0) * (7 * A + K + D * (3 * K + 12)) +
        (7 * (C * n) + K - N'.scan K []) ≤ _
      rw [ep, Nat.sub_zero, Nat.sub_zero]
      have : N'.scan K ([] : List (Id × S)) = 0 := rfl
      omega
    intro i hi
    refine window_settles (Ψ t) (fun i => σ i ≠ t ∨ ((JMach.init X nt).trace xs σ i).1.AtRest t)
      (fun i => ((JMach.init X nt).trace xs σ i).1.AtRest t) F ?_ ?_ ?_ i
      (Nat.le_trans (Nat.mul_le_mul_left F (Nat.succ_le_succ h0)) hi)
    · intro i
      have hsucc : ((JMach.init X nt).trace xs σ (i + 1)) =
          ((((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1,
          ((JMach.init X nt).trace xs σ i).2 +
            (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).2) := rfl
      have hbs : JMach.born xs σ (JMach.init X nt) (i + 1) =
          JMach.born xs σ (JMach.init X nt) i ++
            JMach.stepKids xs ((JMach.init X nt).trace xs σ i).1 (σ i) := rfl
      have hjs : JMach.joined xs σ (JMach.init X nt) (i + 1) =
          JMach.joined xs σ (JMach.init X nt) i +
            JMach.stepJoins xs ((JMach.init X nt).trace xs σ i).1 (σ i) := rfl
      have hb1 := bound (i + 1)
      have hm1 := hm (i + 1)
      have hR1 := hR (i + 1)
      rw [hsucc] at hb1
      rw [hjs] at hm1
      rw [hbs] at hR1
      dsimp only at hb1
      rw [Net.scan_append] at hR1
      show (_ ∧ Ψ t (i + 1) = Ψ t i) ∨ Ψ t (i + 1) < Ψ t i
      simp only [Ψ]
      rw [hbs, hjs, Net.scan_append, hsucc]
      dsimp only
      have hlt : t < ((JMach.init X nt).trace xs σ i).1.ths.length := by
        rw [len i]
        exact ht
      obtain ⟨T, hT⟩ : ∃ T, ((JMach.init X nt).trace xs σ i).1.ths[t]? = some T :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      by_cases hst : σ i = t
      · rw [hst] at hb1 hm1 hR1 ⊢
        have es := JMach.step_eq (xs := xs) hT
          (rfl : JMach.act xs ((JMach.init X nt).trace xs σ i).1.mem T =
          ((JMach.act xs ((JMach.init X nt).trace xs σ i).1.mem T).1,
            (JMach.act xs ((JMach.init X nt).trace xs σ i).1.mem T).2.1,
            (JMach.act xs ((JMach.init X nt).trace xs σ i).1.mem T).2.2))
        have hk : JMach.stepKids xs ((JMach.init X nt).trace xs σ i).1 t =
            WMach.actKids xs ((JMach.init X nt).trace xs σ i).1.mem T.toW := by
          unfold JMach.stepKids
          rw [hT]
        have hj : JMach.stepJoins xs ((JMach.init X nt).trace xs σ i).1 t =
            if WMach.actJoins xs ((JMach.init X nt).trace xs σ i).1.mem T.toW then 1 else 0 := by
          unfold JMach.stepJoins
          rw [hT]
        have hp1 : (((JMach.init X nt).trace xs σ i).1.step xs t).1.potAt N' K A t =
            potJ N' K A (JMach.act xs ((JMach.init X nt).trace xs σ i).1.mem T).2.1 := by
          rw [es]
          exact JMach.potAt_eq (List.getElem?_set_self hlt) N' K A
        have hc2 : (((JMach.init X nt).trace xs σ i).1.step xs t).2 =
            (JMach.act xs ((JMach.init X nt).trace xs σ i).1.mem T).2.2 :=
          congrArg Prod.snd es
        rw [hk, hj, hp1, hc2, JMach.potAt_eq hT]
        rw [hc2] at hb1
        rw [hj] at hm1
        rw [hk] at hR1
        rcases JMach.act_pot (live i) (nd i) hb hH (ahead i) (hA i) hT with
          ⟨e, hto, hsto⟩ | ⟨h1, hle⟩ | ⟨h0', hlt'⟩
        · obtain ⟨todo, st, g, js, wk⟩ := T
          dsimp only at hto hsto
          subst hto hsto
          refine .inl ⟨.inr ⟨g, js, wk, hT⟩, ?_⟩
          rw [e]
          have k0 := WMach.act_zero_kids (xs := xs) (X := ((JMach.init X nt).trace xs σ i).1.mem)
            (T := JThread.toW ⟨[], .idle, g, js, wk⟩) rfl
          rw [k0.1, k0.2]
          rfl
        · refine .inr ?_
          rw [h1]
          rw [h1] at hb1
          cases hJ : WMach.actJoins xs ((JMach.init X nt).trace xs σ i).1.mem T.toW with
          | true =>
            rw [hJ] at hle hm1
            simp only [ite_true] at hle hm1 ⊢
            have e1 : n - ((JMach.init X nt).trace xs σ i).2 =
                (n - (((JMach.init X nt).trace xs σ i).2 + 1)) + 1 := by omega
            have e2 : m - JMach.joined xs σ (JMach.init X nt) i =
                (m - (JMach.joined xs σ (JMach.init X nt) i + 1)) + 1 := by omega
            rw [e1, e2, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
            omega
          | false =>
            rw [hJ] at hle hm1
            simp only [Bool.false_eq_true, ite_false] at hle hm1 ⊢
            have e1 : n - ((JMach.init X nt).trace xs σ i).2 =
                (n - (((JMach.init X nt).trace xs σ i).2 + 1)) + 1 := by omega
            rw [e1, Nat.add_mul, Nat.one_mul]
            simp only [Nat.add_zero] at hle ⊢
            omega
        · refine .inr ?_
          obtain ⟨k0, j0⟩ := WMach.act_zero_kids ((JMach.act_count_eq _ _).symm.trans h0')
          rw [h0', k0, j0]
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          have : N'.scan K ([] : List (Id × S)) = 0 := rfl
          omega
      · have hpo : (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1.potAt N' K A t =
            ((JMach.init X nt).trace xs σ i).1.potAt N' K A t := by
          unfold JMach.potAt
          rw [JMach.step_other _ hst]
        rw [hpo]
        rcases JMach.step_goal (live i) (σ i) with ⟨h0', -, k0, j0⟩ |
            ⟨a, b, α, β, R, -, h1, -⟩
        · refine .inl ⟨.inl hst, ?_⟩
          rw [h0', k0, j0]
          simp only [Nat.add_zero]
          have : N'.scan K ([] : List (Id × S)) = 0 := rfl
          omega
        · refine .inr ?_
          rw [h1] at hb1 ⊢
          have e1 : n - ((JMach.init X nt).trace xs σ i).2 =
              (n - (((JMach.init X nt).trace xs σ i).2 + 1)) + 1 := by omega
          rw [e1, Nat.add_mul, Nat.one_mul]
          have hj2 : m - (JMach.joined xs σ (JMach.init X nt) i +
              JMach.stepJoins xs ((JMach.init X nt).trace xs σ i).1 (σ i)) ≤
                m - JMach.joined xs σ (JMach.init X nt) i :=
            by omega
          have hj3 := Nat.mul_le_mul_right (7 * A + K + D * (3 * K + 12)) hj2
          omega
    · intro i hall
      have same : ∀ d, d ≤ F → ((JMach.init X nt).trace xs σ (i + d)).1.ths[t]? =
          ((JMach.init X nt).trace xs σ i).1.ths[t]? := by
        intro d
        induction d with
        | zero => exact fun _ => rfl
        | succ d ih =>
          intro hd
          have ih' := ih (by omega)
          show (((JMach.init X nt).trace xs σ (i + d)).1.step xs (σ (i + d))).1.ths[t]? =
            ((JMach.init X nt).trace xs σ i).1.ths[t]?
          rcases hall (i + d) (by omega) (by omega) with hne | ⟨g, js, wk, hr⟩
          · rw [JMach.step_other _ hne]
            exact ih'
          · rw [JMach.step_rest _ _ hr, ← ih', hr]
      obtain ⟨j, hj₁, hj₂, hju⟩ := hfair t ht i
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
      rcases hall (i + d) hj₁ hj₂ with hne | ⟨g, js, wk, hr⟩
      · exact absurd hju hne
      · exact ⟨g, js, wk, by rw [← same d (by omega)]; exact hr⟩
    · intro i ⟨g, js, wk, h⟩
      exact ⟨g, js, wk, JMach.step_rest _ _ h⟩
  intro i hi
  have hrest : ((JMach.init X nt).trace xs σ i).1.resting = true := by
    refine List.all_eq_true.2 fun T hT => ?_
    obtain ⟨u, hu⟩ := List.getElem?_of_mem hT
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hu
    rw [len i] at hlt
    obtain ⟨g, js, wk, h⟩ := each u hlt i hi
    rw [hu] at h
    rw [Option.some.inj h]
    rfl
  obtain ⟨hq, hnorm⟩ := (live i).rest hrest
  obtain ⟨-, hu⟩ := (run i).final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨hrest, e₂.symm, e₁.symm⟩


/-- In a system none of whose rules joins interface ports, no claim does. -/
theorem JMach.joined_zero (hj : xs.NoJoins) (σ : Nat → Nat) (M : JMach S) :
    ∀ i, JMach.joined xs σ M i = 0
  | 0 => rfl
  | i + 1 => by
    show JMach.joined xs σ M i + JMach.stepJoins xs (M.trace xs σ i).1 (σ i) = 0
    rw [JMach.joined_zero hj σ M i, Nat.zero_add]
    unfold JMach.stepJoins
    split
    · rename_i T _
      rcases WMach.act_count (xs := xs) (M.trace xs σ i).1.mem T.toW with
          h0 | ⟨a, b, α, β, R, hs, hh⟩
      · rw [(WMach.act_zero_kids h0).2]
        rfl
      · have hc : assoc b (M.trace xs σ i).1.mem.agents = some β ∧ a ≠ b := by
          split at hh
          · rename_i hc
            exact hc
          · cases hh
        have hR : xs.rule α β = some R := by
          rw [ite_pos' hc] at hh
          exact hh
        have ej : WMach.actJoins xs (M.trace xs σ i).1.mem T.toW = R.joins xs.sys.ar α β := by
          unfold WMach.actJoins
          rw [hs]
          dsimp only
          rw [hh]
        rw [ej, hj α β R hR]
        rfl
    · rfl

/-- Claims that join interface ports are claims. -/
theorem JMach.joined_le (σ : Nat → Nat) (M : JMach S) :
    ∀ i, JMach.joined xs σ M i ≤ (M.trace xs σ i).2
  | 0 => Nat.le_refl _
  | i + 1 => by
    show JMach.joined xs σ M i + JMach.stepJoins xs (M.trace xs σ i).1 (σ i) ≤
      (M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2
    have ih := JMach.joined_le σ M i
    have h : JMach.stepJoins xs (M.trace xs σ i).1 (σ i) ≤
        ((M.trace xs σ i).1.step xs (σ i)).2 := by
      unfold JMach.stepJoins
      split
      · rename_i T ht
        rcases WMach.act_count (xs := xs) (M.trace xs σ i).1.mem T.toW with
          h0 | ⟨a, b, α, β, R, hs, hh⟩
        · rw [(WMach.act_zero_kids h0).2]
          exact Nat.zero_le _
        · have e := JMach.step_eq (xs := xs) ht (JMach.act_half_some hs hh)
          rw [e]
          have h1 : (if WMach.actJoins xs (M.trace xs σ i).1.mem T.toW then 1 else 0) ≤ 1 := by
            split <;> omega
          exact h1
      · exact Nat.zero_le _
    omega

/-- **A bound linear in the steps, for systems whose rules join no
interface ports**: a fair run is at rest with the normal form after
`F * (B + 1)` actions, where `B` is two passes over the start and the writes
of each claim with seven actions for each agent it writes.  No trail
length enters: the agents written along the run have different names, so
their trails share no segment. -/
theorem JMach.fair_bound_nojoin {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) (hj : xs.NoJoins) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    {F : Nat} (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * (7 * X.agents.length + 2 * (X.wires.length + D * n) +
          n * (8 * C + D + 1) + 1) ≤ i →
      ((JMach.init X nt).trace xs σ i).1.resting = true ∧
      ((JMach.init X nt).trace xs σ i).2 = n ∧
      ((JMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  intro i hi
  refine JMach.fair_bound hX hnd hnt hb hs hn σ (m := 0) hfair
    (fun i => Nat.le_of_eq (JMach.joined_zero hj σ _ i)) i (Nat.le_trans ?_ hi)
  apply Nat.mul_le_mul_left
  have h1 : n * (8 * C + D + 1) = 8 * (C * n) + D * n + n := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_comm n C,
      Nat.mul_comm n D]
  have h2 : n * (C + D + 1) = C * n + D * n + n := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm n C, Nat.mul_comm n D]
  rw [Nat.zero_mul, h1, h2]
  omega


/-- **Every fair run comes to rest with the normal form**: at most every
claim joins. -/
theorem JMach.fair_bound_all {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {F : Nat}
    (hfair : ∀ u, u < nt → ∀ i, ∃ j, i ≤ j ∧ j < i + F ∧ σ j = u) :
    ∀ i, F * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
          n * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) +
            D * (3 * (X.wires.length + D * n) + 12)) +
          (7 * (C * n) + (X.wires.length + D * n)) + 1) ≤ i →
      ((JMach.init X nt).trace xs σ i).1.resting = true ∧
      ((JMach.init X nt).trace xs σ i).2 = n ∧
      ((JMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  have run : ∀ i, MRun xs.sys ((JMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((JMach.init X nt).trace xs σ i).1.toMach := by
    intro i
    have h := JMach.trace_run xs σ (JMach.init X nt) i
    rw [JMach.init_toMach] at h
    exact h
  exact JMach.fair_bound hX hnd hnt hb hs hn σ hfair
    fun i => Nat.le_trans (JMach.joined_le σ _ i) ((run i).claims_le hX hs hn)

/-- **Along a run the memory holds at most the segments of the net and
`D` for each step to the normal form.** -/
theorem JMach.trace_wires_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (nt : Nat) (σ : Nat → Nat) (i : Nat) :
    ((JMach.init X nt).trace xs σ i).1.mem.wires.length ≤ X.wires.length + D * n := by
  have run : MRun xs.sys ((JMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((JMach.init X nt).trace xs σ i).1.toMach := by
    have h := JMach.trace_run xs σ (JMach.init X nt) i
    rw [JMach.init_toMach] at h
    exact h
  have hc := run.claims_le hX hs hn
  have h := (JMach.trace_sizes σ (JMach.init X nt) hb i).1
  rw [JMach.init_toW, WMach.init_segs] at h
  have h1 : ((JMach.init X nt).trace xs σ i).1.mem.wires.length ≤
      ((JMach.init X nt).trace xs σ i).1.toW.segs := Nat.le_add_right _ _
  have h2 := Nat.mul_le_mul_left D hc
  omega

/-- The agents of symbol `κ` in the goal: in memory, held, or still to be
written. -/
def JMach.census (κ : S) (M : JMach S) : Nat := M.toW.census κ

/-- An action changes the agents of `κ` in the goal only by a claim of a
rule that joins interface ports, as for `WMach`. -/
theorem JMach.act_census {κ : S}
    (hk : ∀ α β R a b, a ≠ b → xs.rule α β = some R →
      (R.newAgents a b).countP (fun e => decide (e.2 = κ)) +
        (if R.joins xs.sys.ar α β then 1 else 0) =
        (if α = κ then 1 else 0) + (if β = κ then 1 else 0))
    {X : XNet S} (hnd : (X.agents.map Prod.fst).Nodup) (T : JThread S) :
    (JMach.act xs X T).1.agents.countP (fun e => decide (e.2 = κ)) +
        (JMach.act xs X T).2.1.st.kc κ + (if WMach.actJoins xs X T.toW then 1 else 0) =
      X.agents.countP (fun e => decide (e.2 = κ)) + T.st.kc κ := by
  rcases JMach.act_agree xs X T with ⟨e₁, e₂, -⟩ | ⟨e₁, e₂, e₃⟩
  · rw [e₁, e₂]
    exact WMach.act_census hk hnd T.toW
  · rw [e₁, e₂, (WMach.act_zero_kids ((JMach.act_count_eq X T).symm.trans e₃)).2]
    simp

/-- **The joining claims plus the agents of `κ` in the goal stay as many as
the agents of `κ` at the start.** -/
theorem JMach.trace_census {κ : S}
    (hk : ∀ α β R a b, a ≠ b → xs.rule α β = some R →
      (R.newAgents a b).countP (fun e => decide (e.2 = κ)) +
        (if R.joins xs.sys.ar α β then 1 else 0) =
        (if α = κ then 1 else 0) + (if β = κ then 1 else 0))
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup)
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) :
    ∀ i, JMach.joined xs σ (JMach.init X nt) i +
        ((JMach.init X nt).trace xs σ i).1.census κ =
      X.agents.countP fun e => decide (e.2 = κ)
  | 0 => by
    have h := WMach.trace_census hk hX hnd hnt σ 0
    show 0 + (JMach.init X nt).toW.census κ = _
    rw [JMach.init_toW]
    exact h
  | i + 1 => by
    have ih := JMach.trace_census hk hX hnd hnt σ i
    have nd : (((JMach.init X nt).trace xs σ i).1.mem.agents.map Prod.fst).Nodup := by
      clear ih
      induction i with
      | zero => exact hnd
      | succ i ih' =>
        exact JMach.step_nodup (JMach.trace_live σ (JMach.init_live hX hnt) i) ih' (σ i)
    show JMach.joined xs σ (JMach.init X nt) i +
        JMach.stepJoins xs ((JMach.init X nt).trace xs σ i).1 (σ i) +
        (((JMach.init X nt).trace xs σ i).1.step xs (σ i)).1.census κ = _
    rw [← ih]
    generalize ((JMach.init X nt).trace xs σ i).1 = M at nd ⊢
    unfold JMach.stepJoins
    cases ht : M.ths[σ i]? with
    | none =>
      have e : M.step xs (σ i) = (M, 0) := by
        unfold JMach.step
        rw [ht]
      rw [e]
      dsimp only
      omega
    | some T =>
      dsimp only
      have es := JMach.step_eq (xs := xs) ht (rfl : JMach.act xs M.mem T =
        ((JMach.act xs M.mem T).1, (JMach.act xs M.mem T).2.1, (JMach.act xs M.mem T).2.2))
      rw [es]
      have ha := JMach.act_census hk nd T
      have hw : (M.ths.map JThread.toW)[σ i]? = some T.toW := JMach.toW_get ht
      have hto := total_map_set (fun T : XThread S => T.st.kc κ) (M.ths.map JThread.toW) (σ i)
        T.toW (JMach.act xs M.mem T).2.1.toW hw
      have hset : (M.ths.set (σ i) (JMach.act xs M.mem T).2.1).map JThread.toW =
          (M.ths.map JThread.toW).set (σ i) (JMach.act xs M.mem T).2.1.toW := by
        rw [List.map_set]
      show (JMach.joined xs σ (JMach.init X nt) i +
          (if WMach.actJoins xs M.mem T.toW then 1 else 0)) +
          ((JMach.act xs M.mem T).1.agents.countP (fun e => decide (e.2 = κ)) +
            total (fun T => T.st.kc κ)
              (((M.ths.set (σ i) (JMach.act xs M.mem T).2.1).map JThread.toW).map
                WThread.toX)) =
        JMach.joined xs σ (JMach.init X nt) i +
          (M.mem.agents.countP (fun e => decide (e.2 = κ)) +
            total (fun T => T.st.kc κ) ((M.ths.map JThread.toW).map WThread.toX))
      rw [hset]
      have e1 : (T.toW.toX).st = T.st := rfl
      have e2 : ((JMach.act xs M.mem T).2.1.toW.toX).st = (JMach.act xs M.mem T).2.1.st := rfl
      simp only [e1, e2] at hto
      omega

/-- **The joining claims are at most the agents of `κ` at the start**, on
every run of `JMach`. -/
theorem JMach.joined_le_census {κ : S}
    (hk : ∀ α β R a b, a ≠ b → xs.rule α β = some R →
      (R.newAgents a b).countP (fun e => decide (e.2 = κ)) +
        (if R.joins xs.sys.ar α β then 1 else 0) =
        (if α = κ then 1 else 0) + (if β = κ then 1 else 0))
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup)
    {nt : Nat} (hnt : 0 < nt) (σ : Nat → Nat) (i : Nat) :
    JMach.joined xs σ (JMach.init X nt) i ≤ X.agents.countP fun e => decide (e.2 = κ) := by
  have := JMach.trace_census hk hX hnd hnt σ i
  omega

section Read

variable {zero succ : S}

/-- **How many actions are enough to run with `JMach` and read.**  As
`XNet.wrunRead_bound`, with the walks of each claim that joins added to
its pass. -/
theorem XNet.jrunRead_bound (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') {p : Port} {v₀ : Nat}
    (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) {m : Nat}
    (hm : ∀ i, JMach.joined xs (fun j => j % nt) (JMach.init X nt) i ≤ m) (s : Nat)
    (h₁ : nt * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
          m * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) +
            D * (3 * (X.wires.length + D * n) + 12)) +
          (7 * (C * n) + (X.wires.length + D * n)) + 1) ≤ s)
    (h₂ : X.wires.length + D * n ≤ s) (h₃ : v₀ + 1 ≤ s) :
    XNet.jrunRead xs zero succ X p nt s = some v₀ := by
  obtain ⟨hr, -, e⟩ := JMach.fair_bound hX hnd hnt hb hs hn (fun j => j % nt)
    roundRobin_fair hm s h₁
  have hW : ((JMach.init X nt).trace xs (fun j => j % nt) s).1.mem.toNet.WF xs.sys.ar := by
    rw [e]
    exact Steps.wf hX hs
  have hnum' : Addition.IsNum xs.sys.ar zero succ
      ((JMach.init X nt).trace xs (fun j => j % nt) s).1.mem.toNet p v₀ := by
    rw [e]
    exact hnum
  have hread := XNet.readNum_bounded hzs hW v₀ p hnum'
  have hwl := JMach.trace_wires_le hX hb hs hn nt (fun j => j % nt) s
  unfold XNet.jrunRead
  rw [ite_pos' hr]
  exact XNet.readNum_mono (by omega) hread h₃

/-- **Given enough actions, the run with `JMach` returns the numeral of
the normal form.** -/
theorem XNet.jrunRead_complete (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') {p : Port} {v₀ : Nat}
    (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) :
    ∃ s₀, ∀ s, s₀ ≤ s → XNet.jrunRead xs zero succ X p nt s = some v₀ := by
  have hm : ∀ i, JMach.joined xs (fun j => j % nt) (JMach.init X nt) i ≤ n := by
    intro i
    have run := JMach.trace_run xs (fun j => j % nt) (JMach.init X nt) i
    rw [JMach.init_toMach] at run
    exact Nat.le_trans (JMach.joined_le _ _ i) (run.claims_le hX hs hn)
  refine ⟨nt * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
      n * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n) +
        D * (3 * (X.wires.length + D * n) + 12)) +
      (7 * (C * n) + (X.wires.length + D * n)) + 1) + (X.wires.length + D * n) + (v₀ + 1),
    fun s hs' => ?_⟩
  exact XNet.jrunRead_bound hzs hX hnd hnt hb hs hn hnum hm s (by omega) (by omega) (by omega)

end Read

end JBound

end INet
