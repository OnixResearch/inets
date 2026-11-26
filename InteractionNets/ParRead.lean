import InteractionNets.ParUnits
import InteractionNets.ReadAgents

/-! # Reading the result of the run with both limits

The run of `ParUnits` ends on the normal form renamed by a renaming that is
`XNet.shortName` on the free ports.  So the agent at a free port of the
normal form is read, by `XNet.readAgent`, at the short name of that port
(`XNet.reuseRunP_read`): whatever is read there is the symbol of the agent
the port is paired with in the normal form, and with enough fuel that
symbol is read. -/

namespace INet

variable {S : Type} {ar : S → Nat}

/-- Reading at a free port of a renamed net, sound: what is read is the
renamed agent the port is paired with. -/
theorem XNet.readAgent_map_sound {Z : XNet S} {C : Net S} {g : Id → Id} (hC : C.WF ar)
    (hg : Renaming g C) (e : Z.toNet = C.map g) {q : Port} (hq : C.free q) {w : Nat} {j : Id}
    {γ : S} (h : Z.readAgent w (mapPort g q) = some (j, γ)) :
    ∃ i, j = g i ∧ C.Paired ar q (i, 0) ∧ C.agent i γ := by
  have hZ : Z.toNet.WF ar := e ▸ hg.wf_map hC
  have hp : Z.toNet.End ar (mapPort g q) := by
    rw [e]
    exact Net.end_map (.inl hq)
  obtain ⟨hpair, hag⟩ := XNet.readAgent_sound hZ hp h
  rw [e] at hpair hag
  obtain ⟨p', q', ep, eq, hpq⟩ := (hg.paired_map hC).1 hpair
  obtain rfl := hg.port_inj (Net.End.used (ar := ar) (.inl hq)) hpq.1.used ep
  obtain ⟨i', rfl, hi'⟩ := hag
  have e₂ : q'.2 = 0 := (Prod.mk.inj eq).2.symm
  have e₁ : g i' = g q'.1 := (Prod.mk.inj eq).1
  obtain rfl := hg.inj (.inl ⟨_, hi'⟩) hpq.2.1.used e₁
  refine ⟨q'.1, rfl, ?_, hi'⟩
  have : q' = (q'.1, 0) := Prod.ext rfl e₂
  rw [← this]
  exact hpq

/-- Reading at a free port of a renamed net, complete. -/
theorem XNet.readAgent_map_complete {Z : XNet S} {C : Net S} {g : Id → Id} (hC : C.WF ar)
    (hg : Renaming g C) (e : Z.toNet = C.map g) {q : Port} {i : Id} {γ : S}
    (hpair : C.Paired ar q (i, 0)) (hag : C.agent i γ) :
    Z.readAgent Z.wires.length (mapPort g q) = some (g i, γ) := by
  have hZ : Z.toNet.WF ar := e ▸ hg.wf_map hC
  refine XNet.readAgent_complete hZ ?_ ?_
  · rw [e]
    exact (hg.paired_map hC).2 ⟨q, (i, 0), rfl, rfl, hpair⟩
  · rw [e]
    exact ⟨i, rfl, hag⟩

variable {xs : XSys S} {X : XNet S}

/-- **The result of the run with both limits, read at the ports.**  Under
the hypotheses of `XNet.reuseRunP_short`, at the short name of a free port
of the input: whatever `XNet.readAgent` returns is the symbol of the agent
the port is paired with in the normal form, and with as much fuel as there
are segments it returns that symbol. -/
theorem XNet.reuseRunP_read {p W D : Nat} {C : Net S} (hp : 0 < p) (hX : X.Ok xs.sys.ar)
    (hW : Steps (CStep xs.sys) W X.toNet C) (hC : Normal (CStep xs.sys) C)
    (hD : (X.parRun xs D).1.step xs = none) {q : Port} (hq : q ∈ X.free) :
    (∀ {w : Nat} {j : Id} {γ : S},
      (X.short.reuseRunP xs p (W / p + D)).1.readAgent w (X.shortName q.1, q.2) = some (j, γ) →
        ∃ i, C.Paired xs.sys.ar q (i, 0) ∧ C.agent i γ) ∧
    (∀ {i : Id} {γ : S}, C.Paired xs.sys.ar q (i, 0) → C.agent i γ →
      ∃ j, (X.short.reuseRunP xs p (W / p + D)).1.readAgent
        (X.short.reuseRunP xs p (W / p + D)).1.wires.length (X.shortName q.1, q.2) =
          some (j, γ)) := by
  obtain ⟨-, -, ⟨g, hg, agree, e⟩, -⟩ := XNet.reuseRunP_short hp hX hW hC hD
  have hCw : C.WF xs.sys.ar := (cstrongConfluent xs.sys).inv_steps hX.1 hW
  have hqC : C.free q := by
    rw [Steps.cfree hW]
    exact hq
  have ep : mapPort g q = (X.shortName q.1, q.2) := Prod.ext (agree q hqC) rfl
  refine ⟨fun h => ?_, fun {i γ} hpair hag => ?_⟩
  · rw [← ep] at h
    obtain ⟨i, -, hpair, hag⟩ := XNet.readAgent_map_sound hCw hg e hqC h
    exact ⟨i, hpair, hag⟩
  · refine ⟨g i, ?_⟩
    rw [← ep]
    exact XNet.readAgent_map_complete hCw hg e hpair hag

end INet
