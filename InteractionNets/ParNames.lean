import InteractionNets.ParOptimal
import InteractionNets.ShortNames

/-! # Parallel rounds on names of one cell

The names of new agents are built from the names of the agents they
replace, so they grow by a cell at each step.  Hardware has addresses of a
fixed width.  Here a round of `XNet.parStep` is followed by `XNet.short`,
which renames every identifier to one cell, its place in the list of the
identifiers of the net (`XNet.packRun`).

A round commutes with renaming (`XNet.parStep_copy`): copies of a net fire
as many pairs and stay copies.  So the packed run fires the same pairs in
the same rounds as `XNet.parRun`, stops when it does, and ends on a copy of
its result (`XNet.packRun_copy`), and every name it holds is one cell, a
number below the length of the list of identifiers of the net it holds
(`XNet.packRun_names`, `XNet.packRun_short`).  So the width of an address
follows the size of the net at that round, not the history of the run.
The free ports are renamed too, so their names may change from round
to round. -/

namespace INet

variable {S : Type} {sys : System S} {N : Net S}

/-- A pair with its agents renamed. -/
def renPair (f : Id → Id) (r : Id × Id × Rhs S) : Id × Id × Rhs S := (f r.1, f r.2.1, r.2.2)

namespace Indep

variable {rs ts : List (Id × Id × Rhs S)}

theorem sublist (h : Indep sys N rs) (hs : ts.Sublist rs) : Indep sys N ts :=
  ⟨fun r hr => h.redex r (hs.subset hr), h.disjoint.sublist hs⟩

/-- **Firing independent pairs commutes with renaming.** -/
theorem fireSeq_map {f : Id → Id} (hN : N.WF sys.ar) (hf : Renaming f N) (h : Indep sys N rs) :
    ∃ g, Renaming g (N.fireSeq rs) ∧ (∀ i, N.Used i → g i = f i) ∧
      (N.map f).fireSeq (rs.map (renPair f)) = (N.fireSeq rs).map g := by
  induction rs generalizing N f with
  | nil => exact ⟨f, hf, fun _ _ => rfl, rfl⟩
  | cons r rest ih =>
    obtain ⟨α, β, rx⟩ := h.redex r (List.mem_cons.2 (.inl rfl))
    have s := rx.site hN
    have hg₁ := hf.fire s r.2.2
    have e₁ := s.map_fire hf (fun i hu => s.rechild_used f hu) (rechild_child f _ _) r.2.2
    obtain ⟨g, hg, agree, e⟩ := ih (Step.wf hN h.step) hg₁ (h.tail hN)
    have hm : rest.map (renPair (rechild f r.1 r.2.1)) = rest.map (renPair f) := by
      refine List.map_congr_left fun x hx => ?_
      obtain ⟨γ, δ, rx'⟩ := h.redex x (List.mem_cons.2 (.inr hx))
      have e₁ : rechild f r.1 r.2.1 x.1 = f x.1 := s.rechild_used f (.inl ⟨_, rx'.ha⟩)
      have e₂ : rechild f r.1 r.2.1 x.2.1 = f x.2.1 := s.rechild_used f (.inl ⟨_, rx'.hb⟩)
      unfold renPair
      rw [e₁, e₂]
    refine ⟨g, hg, fun i hu => ?_, ?_⟩
    · rw [agree i (s.used_fire_mono r.2.2 hu)]
      exact s.rechild_used f hu
    · show ((N.map f).fire (f r.1) (f r.2.1) r.2.2).fireSeq (rest.map (renPair f)) = _
      rw [← e₁, ← hm]
      exact e

/-- Independent pairs stay independent in a renamed net. -/
theorem map {f : Id → Id} (hN : N.WF sys.ar) (hf : Renaming f N) (h : Indep sys N rs) :
    Indep sys (N.map f) (rs.map (renPair f)) := by
  refine ⟨fun r' hr' => ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    obtain ⟨α, β, rx⟩ := h.redex r hr
    exact ⟨α, β, hf.redex_map hN rx⟩
  · refine List.pairwise_map.2 (h.disjoint.imp_of_mem fun {x y} hx hy d => ?_)
    obtain ⟨α, β, rx⟩ := h.redex x hx
    obtain ⟨γ, δ, ry⟩ := h.redex y hy
    have ux₁ : N.Used x.1 := .inl ⟨_, rx.ha⟩
    have ux₂ : N.Used x.2.1 := .inl ⟨_, rx.hb⟩
    have uy₁ : N.Used y.1 := .inl ⟨_, ry.ha⟩
    have uy₂ : N.Used y.2.1 := .inl ⟨_, ry.hb⟩
    exact ⟨fun e => d.1 (hf.inj ux₁ uy₁ e), fun e => d.2.1 (hf.inj ux₁ uy₂ e),
      fun e => d.2.2.1 (hf.inj ux₂ uy₁ e), fun e => d.2.2.2 (hf.inj ux₂ uy₂ e)⟩

/-- Every pair of an independent list is on the agents of a pair of a list
that meets every active pair. -/
theorem same_of_meets (hN : N.WF sys.ar) (h : Indep sys N rs) (ht : Indep sys N ts)
    (cov : MeetsAll sys N ts) : ∀ r ∈ rs, ∃ t ∈ ts, SameAgents r t := by
  intro x hx
  obtain ⟨α, β, rx⟩ := h.redex x hx
  obtain ⟨t, htm, hat⟩ := cov rx
  obtain ⟨γ, δ, rt⟩ := ht.redex t htm
  refine ⟨t, htm, rx.same_of_share rt hN ?_⟩
  rcases hat with e | e
  · exact .inl e
  · exact .inr (.inl e)

/-- Two lists of independent pairs on the same agents have the same length. -/
theorem length_same (h : Indep sys N rs) (h' : Indep sys N ts)
    (hm : ∀ r ∈ rs, ∃ r' ∈ ts, SameAgents r r')
    (hm' : ∀ r' ∈ ts, ∃ r ∈ rs, SameAgents r r') : rs.length = ts.length := by
  induction rs generalizing ts with
  | nil =>
    cases ts with
    | nil => rfl
    | cons r' _ =>
      obtain ⟨r, hr, -⟩ := hm' r' (List.mem_cons.2 (.inl rfl))
      exact absurd hr List.not_mem_nil
  | cons r rest ih =>
    obtain ⟨r', hr', hs⟩ := hm r (List.mem_cons.2 (.inl rfl))
    obtain ⟨s₁, s₂, rfl⟩ := List.append_of_mem hr'
    have hp : (s₁ ++ r' :: s₂).Perm (r' :: (s₁ ++ s₂)) := List.perm_middle
    have h₂ : Indep sys N (r' :: (s₁ ++ s₂)) := h'.perm hp
    obtain ⟨hd, -⟩ := List.pairwise_cons.1 h.disjoint
    obtain ⟨hd', -⟩ := List.pairwise_cons.1 h₂.disjoint
    have ht : Indep sys N (s₁ ++ s₂) := h₂.sublist (List.sublist_cons_self _ _)
    have hr : Indep sys N rest := h.sublist (List.sublist_cons_self _ _)
    have e := ih hr ht (fun x hx => ?_) (fun y' hy' => ?_)
    · rw [hp.length_eq, List.length_cons, List.length_cons, e]
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

/-- Lists meeting every active pair stay so in a renamed net. -/
theorem MeetsAll.map {f : Id → Id} {ts : List (Id × Id × Rhs S)} (hN : N.WF sys.ar)
    (hf : Renaming f N) (cov : MeetsAll sys N ts) :
    MeetsAll sys (N.map f) (ts.map (renPair f)) := by
  intro a' b' α β R r
  obtain ⟨a, b, rfl, rfl, rx⟩ := hf.redex_of_map hN r
  obtain ⟨t, ht, e⟩ := cov rx
  refine ⟨renPair f t, List.mem_map.2 ⟨t, ht, rfl⟩, ?_⟩
  rcases e with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

/-! ### Rounds on copies -/

variable {xs : XSys S} {X Y : XNet S}

theorem XNet.parStep_snd (X : XNet S) : (X.parStep xs).2 = (X.parSel xs).length :=
  (List.length_map _).symm

/-- **A round commutes with renaming**: rounds of `XNet.parStep` on a net
and on a renamed copy fire as many pairs and reach copies. -/
theorem XNet.parStep_map {f : Id → Id} (hX : X.Ok xs.sys.ar) (hY : Y.Ok xs.sys.ar)
    (hf : Renaming f X.toNet) (e : Y.toNet = X.toNet.map f) :
    (Y.parStep xs).2 = (X.parStep xs).2 ∧
      ∃ g, Renaming g (X.parStep xs).1.toNet ∧ (∀ i, X.toNet.Used i → g i = f i) ∧
        (Y.parStep xs).1.toNet = (X.parStep xs).1.toNet.map g := by
  have hC := hX.1
  have hI := (XNet.redexes_indep xs X).abs
  have hJ := (XNet.redexes_indep xs Y).abs
  have cX : MeetsAll xs.sys X.toNet (X.parSel xs) := XNet.parSel_covers hX
  have cY : MeetsAll xs.sys Y.toNet (Y.parSel xs) := XNet.parSel_covers hY
  rw [e] at hJ cY
  have hM := hI.map hC hf
  have cM : MeetsAll xs.sys (X.toNet.map f) ((X.parSel xs).map (renPair f)) := cX.map hC hf
  have hCf : (X.toNet.map f).WF xs.sys.ar := hf.wf_map hC
  have m₁ := hJ.same_of_meets hCf hM cM
  have m₂ := hM.same_of_meets hCf hJ cY
  have m₂' : ∀ r' ∈ (X.parSel xs).map (renPair f), ∃ r ∈ Y.parSel xs, SameAgents r r' := by
    intro r' hr'
    obtain ⟨r, hr, hs⟩ := m₂ r' hr'
    refine ⟨r, hr, ?_⟩
    rcases hs with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact .inl ⟨e₁.symm, e₂.symm⟩
    · exact .inr ⟨e₂.symm, e₁.symm⟩
  refine ⟨?_, ?_⟩
  · rw [XNet.parStep_snd, XNet.parStep_snd, hJ.length_same hM m₁ m₂', List.length_map]
  · obtain ⟨g, hg, agree, eg⟩ := hI.fireSeq_map hC hf
    have hW : (X.toNet.fireSeq (X.parSel xs)).WF xs.sys.ar := Steps.wf hC (hI.steps hC)
    refine ⟨g, ?_, agree, ?_⟩
    · rw [XNet.parStep_toNet hX, ← hI.fireSeq_eq hC]
      exact hg.compact
    · rw [XNet.parStep_toNet hY, XNet.parStep_toNet hX, e, ← hJ.fireSeq_eq hCf,
        hJ.fireSeq_same hCf hM m₁ m₂', eg, ← hI.fireSeq_eq hC, hg.compact_map hW]

/-- An executable net in the invariant is a copy of another exactly when it
is a renaming of it, on the nose. -/
theorem XNet.copy_iff {f : Id → Id} (hX : X.Ok xs.sys.ar) (hY : Y.Ok xs.sys.ar) :
    X.toNet.Iso xs.sys.ar f Y.toNet ↔ Renaming f X.toNet ∧ Y.toNet = X.toNet.map f := by
  constructor
  · intro hi
    refine ⟨hi.ren, ?_⟩
    have e := Net.obsEq_iff_compact_eq.1 hi.obs
    rw [hY.2, hi.ren.compact_map hX.1, hX.2] at e
    exact e.symm
  · rintro ⟨hf, e⟩
    exact ⟨hf, e ▸ Net.ObsEq.refl _⟩

/-- **Copies take the same rounds**: a round of `XNet.parStep` on two
copies fires as many pairs and reaches copies. -/
theorem XNet.parStep_copy (hX : X.Ok xs.sys.ar) (hY : Y.Ok xs.sys.ar)
    (h : X.toNet.Copy xs.sys.ar Y.toNet) :
    (Y.parStep xs).2 = (X.parStep xs).2 ∧
      (X.parStep xs).1.toNet.Copy xs.sys.ar (Y.parStep xs).1.toNet := by
  obtain ⟨f, hi⟩ := h
  obtain ⟨hf, e⟩ := (XNet.copy_iff hX hY).1 hi
  obtain ⟨hn, g, hg, -, eg⟩ := XNet.parStep_map hX hY hf e
  obtain ⟨-, hX'⟩ := XNet.parStep_spec (xs := xs) hX
  obtain ⟨-, hY'⟩ := XNet.parStep_spec (xs := xs) hY
  exact ⟨hn, g, (XNet.copy_iff hX' hY').2 ⟨hg, eg⟩⟩

/-- The short form keeps the invariant. -/
theorem XNet.short_ok (hX : X.Ok xs.sys.ar) : X.short.Ok xs.sys.ar := by
  refine ⟨XNet.short_wf hX.1, ?_⟩
  rw [XNet.short_toNet, (XNet.short_renaming X).compact_map hX.1, hX.2]

/-- The short form is a copy. -/
theorem XNet.short_copy (hX : X.Ok xs.sys.ar) : X.toNet.Copy xs.sys.ar X.short.toNet :=
  ⟨_, (XNet.copy_iff hX (XNet.short_ok hX)).2 ⟨XNet.short_renaming X, XNet.short_toNet X⟩⟩

/-- Rounds of `XNet.parStep`, each followed by renaming every identifier to
one cell.  Returns the net reached and the number of pairs fired. -/
def XNet.packRun (xs : XSys S) : Nat → XNet S → XNet S × Nat
  | 0, X => (X, 0)
  | n + 1, X =>
    if (X.parStep xs).2 = 0 then (X, 0)
    else ((XNet.packRun xs n (X.parStep xs).1.short).1,
      (X.parStep xs).2 + (XNet.packRun xs n (X.parStep xs).1.short).2)

/-- **The packed run is the parallel run up to names**: started on a copy,
it fires as many pairs, stops exactly when `XNet.parRun` does, and ends on
a copy of its result. -/
theorem XNet.packRun_copy (n : Nat) (hX : X.Ok xs.sys.ar) (hY : Y.Ok xs.sys.ar)
    (h : X.toNet.Copy xs.sys.ar Y.toNet) :
    (Y.packRun xs n).2 = (X.parRun xs n).2 ∧ (Y.packRun xs n).1.Ok xs.sys.ar ∧
      ((Y.packRun xs n).1.step xs = none ↔ (X.parRun xs n).1.step xs = none) ∧
      (X.parRun xs n).1.toNet.Copy xs.sys.ar (Y.packRun xs n).1.toNet := by
  induction n generalizing X Y with
  | zero =>
    obtain ⟨e, -⟩ := XNet.parStep_copy hX hY h
    refine ⟨rfl, hY, ?_, h⟩
    show Y.step xs = none ↔ X.step xs = none
    rw [← XNet.parStep_zero_iff, ← XNet.parStep_zero_iff, e]
  | succ n ih =>
    obtain ⟨e, hc⟩ := XNet.parStep_copy hX hY h
    unfold XNet.packRun XNet.parRun
    by_cases h0 : (X.parStep xs).2 = 0
    · have h0' : (Y.parStep xs).2 = 0 := e ▸ h0
      rw [ite_pos' h0, ite_pos' h0']
      refine ⟨rfl, hY, ?_, h⟩
      rw [← XNet.parStep_zero_iff, ← XNet.parStep_zero_iff, h0, h0']
    · have h0' : ¬ (Y.parStep xs).2 = 0 := e ▸ h0
      rw [ite_neg' h0, ite_neg' h0']
      obtain ⟨-, hX'⟩ := XNet.parStep_spec (xs := xs) hX
      obtain ⟨-, hY'⟩ := XNet.parStep_spec (xs := xs) hY
      have hc' := hc.trans (XNet.short_copy hY') hX'.1 hY'.1 hX'.2
      obtain ⟨e', hok, hs, hcopy⟩ := ih hX' (XNet.short_ok hY') hc'
      exact ⟨by rw [e', e], hok, hs, hcopy⟩

/-- A property of nets that every short form has holds of the net the
packed run ends on, if it holds of its input. -/
theorem XNet.packRun_keeps (xs : XSys S) (P : XNet S → Prop) (hP : ∀ Z : XNet S, P Z.short) :
    ∀ (n : Nat) (Y : XNet S), P Y → P (Y.packRun xs n).1
  | 0, _, h => h
  | n + 1, Y, h => by
    unfold XNet.packRun
    split
    · exact h
    · exact XNet.packRun_keeps xs P hP n _ (hP _)

/-- **Small names**: every name of a short form is one cell holding a
number below the length of its list of identifiers. -/
theorem XNet.short_small (X : XNet S) :
    ∀ i ∈ X.short.allIds, ∃ k, i = [k] ∧ k < X.short.allIds.length := by
  intro i hi
  have hl : X.short.allIds = X.allIds.map X.shortName := by
    rw [XNet.short_eq, XNet.allIds_map]
  rw [hl] at hi ⊢
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  obtain ⟨k, ek, hk⟩ := XNet.shortName_of_mem hj
  refine ⟨k, ek, ?_⟩
  rw [List.length_map]
  exact (List.getElem?_eq_some_iff.1 hk).1

/-- **Names of one cell**: if every name of the input is one cell holding
a number below the length of its list of identifiers, so is every name the
packed run holds. -/
theorem XNet.packRun_names (xs : XSys S) (n : Nat) (Y : XNet S)
    (h : ∀ i ∈ Y.allIds, ∃ k, i = [k] ∧ k < Y.allIds.length) :
    ∀ i ∈ (Y.packRun xs n).1.allIds, ∃ k, i = [k] ∧ k < (Y.packRun xs n).1.allIds.length :=
  XNet.packRun_keeps xs (fun Z => ∀ i ∈ Z.allIds, ∃ k, i = [k] ∧ k < Z.allIds.length)
    XNet.short_small n Y h

/-- **The parallel run on names of one cell**: started on the short form
of a net, the packed run fires the pairs of `XNet.parRun` in its rounds,
stops when it does on a copy of its result, and holds only names of one
cell, each a number below the length of the list of identifiers of the net
it ends on. -/
theorem XNet.packRun_short (n : Nat) (hX : X.Ok xs.sys.ar) :
    (X.short.packRun xs n).2 = (X.parRun xs n).2 ∧
      ((X.short.packRun xs n).1.step xs = none ↔ (X.parRun xs n).1.step xs = none) ∧
      (X.parRun xs n).1.toNet.Copy xs.sys.ar (X.short.packRun xs n).1.toNet ∧
      ∀ i ∈ (X.short.packRun xs n).1.allIds,
        ∃ k, i = [k] ∧ k < (X.short.packRun xs n).1.allIds.length := by
  obtain ⟨e, -, hs, hc⟩ := XNet.packRun_copy n hX (XNet.short_ok hX) (XNet.short_copy hX)
  exact ⟨e, hs, hc, XNet.packRun_names xs n _ (XNet.short_small X)⟩

end INet
