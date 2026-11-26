import InteractionNets.ParAlloc

/-! # Both limits at once: `p` firing units and reused names

Rounds of at most `p` pairs (`XNet.parStepP`), each followed by the
allocator of `ParAlloc` (`XNet.reuseRunP`).  From the short form of a net
that reaches its normal form `C` in `W` steps and in `D` rounds of
`XNet.parStep`, the run stops within `W / p + D` rounds, on `C` renamed by
a renaming that is `XNet.shortName` on the free ports; the free ports keep
their names; and every name it holds is one cell, a number below the
longest list of identifiers held (`XNet.reuseRunP_short`,
`XNet.reuseRunP_names`).

A round of at most `p` pairs is not carried along a renaming: which `p`
pairs come first depends on the order of the lists.  What is carried is
the number of steps left (`Steps.cmap`) and the rounds of `XNet.parRun`
left (`XNet.parRun_map_stop`), and those are all the bound needs. -/

namespace INet

variable {S : Type} {sys : System S} {xs : XSys S} {X Y Z : XNet S}

/-- Reduction without history keeps the free ports. -/
theorem Steps.cfree {n : Nat} {C C' : Net S} (h : Steps (CStep sys) n C C') :
    C'.free = C.free := by
  induction h with
  | refl => rfl
  | head h₁ _ ih =>
    obtain ⟨N', s, rfl⟩ := h₁
    have e := Step.free s
    exact ih.trans e

/-- A renamed normal form is normal. -/
theorem Renaming.cnormal_map {C : Net S} {g : Id → Id} (hC : C.WF sys.ar) (hg : Renaming g C)
    (hn : Normal (CStep sys) C) : Normal (CStep sys) (C.map g) := fun _ h => by
  obtain ⟨C', h'⟩ := CStep.of_map hC hg h
  exact hn _ h'

/-- **The rounds of `XNet.parRun` do not depend on names.** -/
theorem XNet.parRun_map_stop (D : Nat) {f : Id → Id} (hX : X.Ok xs.sys.ar)
    (hf : Renaming f X.toNet) (e : Y.toNet = X.toNet.map f)
    (h : (X.parRun xs D).1.step xs = none) : (Y.parRun xs D).1.step xs = none := by
  induction D generalizing X Y f with
  | zero =>
    have hY := XNet.ok_of_map hX hf e
    obtain ⟨hn, -⟩ := XNet.parStep_map hX hY hf e
    show Y.step xs = none
    rw [← XNet.parStep_zero_iff, hn, XNet.parStep_zero_iff]
    exact h
  | succ D ih =>
    have hY := XNet.ok_of_map hX hf e
    obtain ⟨hn, g, hg, -, eg⟩ := XNet.parStep_map hX hY hf e
    unfold XNet.parRun at h ⊢
    by_cases h0 : (X.parStep xs).2 = 0
    · have h0' : (Y.parStep xs).2 = 0 := hn ▸ h0
      rw [ite_pos' h0']
      exact XNet.parStep_zero_iff.1 h0'
    · have h0' : ¬ (Y.parStep xs).2 = 0 := hn ▸ h0
      rw [ite_neg' h0] at h
      rw [ite_neg' h0']
      obtain ⟨-, hX'⟩ := XNet.parStep_spec (xs := xs) hX
      exact ih hX' hg eg h

/-- The allocator keeps names small after any change of the net. -/
theorem XNet.reuse_small_of {P : Nat} (h : X.Small P) (Z : XNet S) :
    (Z.map (X.reuseName Z)).Small (max P Z.allIds.length) := by
  intro i hi
  rw [XNet.allIds_map] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  obtain ⟨k, e, hk⟩ := XNet.reuseName_small (Y := X) hj
  refine ⟨k, e, ?_⟩
  rcases hk with hk | hk
  · omega
  · obtain ⟨k', e', hk'⟩ := h _ hk
    obtain rfl := (List.cons.inj e').1
    omega

/-- The allocator keeps the names of free ports that were small. -/
theorem XNet.reuse_free_of {P : Nat} (h : X.Small P) (hZ : Z.free = X.free) :
    (Z.map (X.reuseName Z)).free = X.free := by
  show (Z.free.map (mapPort _)) = X.free
  rw [hZ]
  refine (List.map_congr_left fun p hp => ?_).trans (List.map_id _)
  have hm : p.1 ∈ X.allIds :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  obtain ⟨k, e, -⟩ := h _ hm
  have hk : X.Kept p.1 := ⟨by rw [e]; rfl, hm⟩
  exact Prod.ext (XNet.reuseName_kept hk) rfl

/-- Rounds of at most `p` pairs, each followed by the allocator. -/
def XNet.reuseRunP (xs : XSys S) (p : Nat) : Nat → XNet S → XNet S × Nat
  | 0, X => (X, 0)
  | n + 1, X =>
    if (X.parStepP xs p).2 = 0 then (X, 0)
    else
      ((XNet.reuseRunP xs p n ((X.parStepP xs p).1.map (X.reuseName (X.parStepP xs p).1))).1,
        (X.parStepP xs p).2 +
          (XNet.reuseRunP xs p n
            ((X.parStepP xs p).1.map (X.reuseName (X.parStepP xs p).1))).2)

/-- The longest list of identifiers held in the run. -/
def XNet.reusePeakP (xs : XSys S) (p : Nat) : Nat → XNet S → Nat
  | 0, X => X.allIds.length
  | n + 1, X =>
    if (X.parStepP xs p).2 = 0 then X.allIds.length
    else max X.allIds.length
      (XNet.reusePeakP xs p n ((X.parStepP xs p).1.map (X.reuseName (X.parStepP xs p).1)))

theorem XNet.reusePeakP_ge (xs : XSys S) (p : Nat) : ∀ (n : Nat) (X : XNet S),
    X.allIds.length ≤ X.reusePeakP xs p n
  | 0, _ => Nat.le_refl _
  | n + 1, X => by
    unfold XNet.reusePeakP
    split
    · exact Nat.le_refl _
    · exact Nat.le_max_left _ _

/-- **Small names**, with at most `p` pairs a round. -/
theorem XNet.reuseRunP_names (xs : XSys S) (p : Nat) :
    ∀ (n : Nat) (X : XNet S) (P : Nat), X.Small P →
      (X.reuseRunP xs p n).1.Small (max P (X.reusePeakP xs p n))
  | 0, X, P, h => h.mono (Nat.le_max_left _ _)
  | n + 1, X, P, h => by
    unfold XNet.reuseRunP XNet.reusePeakP
    split
    · exact h.mono (Nat.le_max_left _ _)
    · have ih := XNet.reuseRunP_names xs p n _ _ (XNet.reuse_small_of h (X.parStepP xs p).1)
      have hge := XNet.reusePeakP_ge xs p n
        ((X.parStepP xs p).1.map (X.reuseName (X.parStepP xs p).1))
      rw [XNet.allIds_map, List.length_map] at hge
      refine ih.mono ?_
      omega

/-- A net with no step reaches its normal form in no step. -/
theorem XNet.final_of_stop {W : Nat} {C : Net S} (hY : Y.Ok xs.sys.ar) (hs : Y.step xs = none)
    (hW : Steps (CStep xs.sys) W Y.toNet C) :
    ∃ g, Renaming g C ∧ (∀ q, C.free q → g q.1 = q.1) ∧ Y.toNet = C.map g := by
  obtain ⟨-, rfl⟩ := Steps.of_normal (XNet.step_complete hY hs) hW
  exact ⟨id, Renaming.id hY.1, fun _ _ => rfl, (Net.map_id _).symm⟩

/-- **Brent's bound on reused names.**  If the net reaches its normal form
`C` in `W` steps and in `D` rounds of `XNet.parStep`, and its names are
small, then rounds of at most `p` pairs, each followed by the allocator,
stop within `W / p + D` rounds, keep the free ports, and end on `C`
renamed by a renaming that keeps the names of the free ports. -/
theorem XNet.reuseRunP_bound {p : Nat} (hp : 0 < p) :
    ∀ (n : Nat) {Y : XNet S} {W D P : Nat} {C : Net S}, Y.Ok xs.sys.ar →
      Steps (CStep xs.sys) W Y.toNet C → Normal (CStep xs.sys) C →
      (Y.parRun xs D).1.step xs = none → Y.Small P → W / p + D ≤ n →
      (Y.reuseRunP xs p n).1.step xs = none ∧ (Y.reuseRunP xs p n).1.free = Y.free ∧
        ∃ g, Renaming g C ∧ (∀ q, C.free q → g q.1 = q.1) ∧
          (Y.reuseRunP xs p n).1.toNet = C.map g := by
  intro n
  induction n with
  | zero =>
    intro Y W D P C hY hW _ hD _ hn
    obtain rfl : D = 0 := by have := Nat.zero_le (W / p); omega
    exact ⟨hD, rfl, XNet.final_of_stop hY hD hW⟩
  | succ n ih =>
    intro Y W D P C hY hW hC hD hs hn
    have hI := XNet.redexes_indep xs Y
    have hT : Y.Indep xs ((selectIndep [] (Y.redexes xs)).take p) :=
      hI.sublist (List.take_sublist _ _)
    unfold XNet.reuseRunP
    split
    · rename_i h0
      have h0' : ((selectIndep [] (Y.redexes xs)).take p).length = 0 := h0
      rw [List.length_take] at h0'
      have hl : (selectIndep [] (Y.redexes xs)).length = 0 := by omega
      have hstop := XNet.parStep_zero_iff.1 hl
      exact ⟨hstop, rfl, XNet.final_of_stop hY hstop hW⟩
    · rename_i h0
      obtain ⟨sts, hY₁⟩ := XNet.fireList_steps hY hT
      obtain ⟨hle, rest⟩ := (cstrongConfluent xs.sys).bounded hY.1 hW hC sts
      -- the rounds of `parRun` left after the round, and the bound
      obtain ⟨D', hD', hnD⟩ : ∃ D', ((Y.parStepP xs p).1.parRun xs D').1.step xs = none ∧
          (W - (Y.parStepP xs p).2) / p + D' ≤ n := by
        by_cases hsel : (selectIndep [] (Y.redexes xs)).length ≤ p
        · have et : (selectIndep [] (Y.redexes xs)).take p = selectIndep [] (Y.redexes xs) :=
            List.take_of_length_le hsel
          have hz : ¬ (Y.parStep xs).2 = 0 := by
            intro hz
            exact h0 (by
              show ((selectIndep [] (Y.redexes xs)).take p).length = 0
              rw [et]
              exact hz)
          have hYeq : (Y.parStepP xs p).1 = (Y.parStep xs).1 := by
            show Y.fireList xs.sys.ar _ = Y.fireList xs.sys.ar _
            rw [et]
          cases D with
          | zero => exact absurd (XNet.parStep_zero_iff.2 hD) hz
          | succ d =>
            unfold XNet.parRun at hD
            split at hD
            · exact absurd (by assumption) hz
            refine ⟨d, hYeq ▸ hD, ?_⟩
            have := Nat.div_le_div_right (c := p) (Nat.sub_le W (Y.parStepP xs p).2)
            omega
        · have hlen : ((selectIndep [] (Y.redexes xs)).take p).length = p := by
            rw [List.length_take]
            omega
          refine ⟨D, XNet.parRun_ahead hY hY₁ ?_ D hD, ?_⟩
          · obtain ⟨e, -⟩ := XNet.fireList_toNet hY hT
            exact ⟨_, hT.abs, e⟩
          · have hle' : p ≤ W := hlen ▸ hle
            have := Nat.div_eq_sub_div hp hle'
            show (W - ((selectIndep [] (Y.redexes xs)).take p).length) / p + D ≤ n
            rw [hlen]
            omega
      -- rename the net reached, and its normal form with it
      have hren := XNet.reuse_renaming Y (Y.parStepP xs p).1
      have e' := XNet.map_toNet (Y.reuseName (Y.parStepP xs p).1) (Y.parStepP xs p).1
      have hY' := XNet.ok_of_map hY₁ hren e'
      have hCw : C.WF xs.sys.ar := (cstrongConfluent xs.sys).inv_steps hY.1 hW
      obtain ⟨g₁, hg₁, agree₁, sts₀⟩ := Steps.cmap hY₁.1 hren rest
      have sts' : Steps (CStep xs.sys) (W - (Y.parStepP xs p).2)
          ((Y.parStepP xs p).1.map (Y.reuseName (Y.parStepP xs p).1)).toNet (C.map g₁) := by
        rw [e']
        exact sts₀
      have hfr₁ : (Y.parStepP xs p).1.free = Y.free := XNet.fireList_free _ _ _
      obtain ⟨hstop, hfree, g₂, hg₂, agree₂, eq₂⟩ :=
        ih hY' sts' (hg₁.cnormal_map hCw hC) (XNet.parRun_map_stop D' hY₁ hren e' hD')
          (XNet.reuse_small_of hs _) hnD
      refine ⟨hstop, hfree.trans (XNet.reuse_free_of hs hfr₁), g₂ ∘ g₁, hg₁.comp hg₂,
        fun q hq => ?_, by rw [eq₂, Net.map_map]⟩
      have h₂ := agree₂ (mapPort g₁ q) ⟨q, rfl, hq⟩
      show g₂ (g₁ q.1) = q.1
      rw [show g₂ (g₁ q.1) = g₁ q.1 from h₂]
      have hq₁ : (Y.parStepP xs p).1.toNet.free q := by
        have := Steps.cfree rest
        rw [this] at hq
        exact hq
      rw [agree₁ q hq₁]
      have hqY : q ∈ Y.free := hfr₁ ▸ hq₁
      have hm : q.1 ∈ Y.allIds :=
        List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨q, hqY, rfl⟩))
      obtain ⟨k, ek, -⟩ := hs _ hm
      exact XNet.reuseName_kept ⟨by rw [ek]; rfl, hm⟩

/-- **Both limits from the short form.**  If a net reaches its normal form
`C` in `W` steps and in `D` rounds of `XNet.parStep`, then from its short
form rounds of at most `p` pairs, each followed by the allocator, stop
within `W / p + D` rounds on `C` renamed by a renaming that is
`XNet.shortName` on the free ports, keep the names of the free ports of
the short form, and hold only names `[k]` with `k` below the longest list
of identifiers held. -/
theorem XNet.reuseRunP_short {p W D : Nat} {C : Net S} (hp : 0 < p) (hX : X.Ok xs.sys.ar)
    (hW : Steps (CStep xs.sys) W X.toNet C) (hC : Normal (CStep xs.sys) C)
    (hD : (X.parRun xs D).1.step xs = none) :
    (X.short.reuseRunP xs p (W / p + D)).1.step xs = none ∧
      (X.short.reuseRunP xs p (W / p + D)).1.free = X.short.free ∧
      (∃ g, Renaming g C ∧ (∀ q, C.free q → g q.1 = X.shortName q.1) ∧
        (X.short.reuseRunP xs p (W / p + D)).1.toNet = C.map g) ∧
      (X.short.reuseRunP xs p (W / p + D)).1.Small
        (X.short.reusePeakP xs p (W / p + D)) := by
  have hs : X.short.Small X.short.allIds.length := XNet.short_small X
  have hCw : C.WF xs.sys.ar := (cstrongConfluent xs.sys).inv_steps hX.1 hW
  obtain ⟨g₀, hg₀, agree₀, sts⟩ := Steps.cmap hX.1 (XNet.short_renaming X) hW
  rw [← XNet.short_toNet] at sts
  obtain ⟨hstop, hfree, g, hg, agree, eq⟩ :=
    XNet.reuseRunP_bound hp (W / p + D) (XNet.short_ok hX) sts (hg₀.cnormal_map hCw hC)
      (XNet.parRun_map_stop D hX (XNet.short_renaming X) (XNet.short_toNet X) hD) hs
      (Nat.le_refl _)
  refine ⟨hstop, hfree, ⟨g ∘ g₀, hg₀.comp hg, fun q hq => ?_, by rw [eq, Net.map_map]⟩, ?_⟩
  · show g (g₀ q.1) = X.shortName q.1
    rw [show g (g₀ q.1) = g₀ q.1 from agree (mapPort g₀ q) ⟨q, rfl, hq⟩]
    exact agree₀ q (Steps.cfree hW ▸ hq)
  · have hn := XNet.reuseRunP_names xs p (W / p + D) _ _ hs
    have hge := XNet.reusePeakP_ge xs p (W / p + D) X.short
    exact hn.mono (by omega)

end INet
