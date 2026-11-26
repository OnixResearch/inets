import InteractionNets.EndToEnd

/-! # Reading the agents on the free ports, for any system

`IJMach.runRead` reads a unary numeral.  A system whose values are agents
of their own, as an agent carrying a 64-bit number, is read by looking at
the agent at the other end of the wire of each port of its interface.
`XNet.readAgent` does that on lists and `IMem.readAgent` on the maps of the
indexed memory (`IMem.readAgent_eq`).  What it returns is the agent wired
to the port by its principal port (`XNet.readAgent_sound`), and when there
is one, fuel for the segments of the memory finds it
(`XNet.readAgent_complete`).

`IJMach.runReadAgents` runs the indexed program busy-first, and at rest
reads the agents on a list of ports, with the time of the run.  Whatever it
returns names, for each port, the symbol of the agent wired to it in the
normal form (`IJMach.runReadAgents_sound`), and with enough fuel it returns
them, at a time within `2 C + 3 D + 6` times the work bound
(`IJMach.runReadAgents_eq`), for any system whose rules write at most `C`
agents and `D` segments and join at most `J`. -/

namespace INet

variable {S : Type} [DecidableEq S]

/-- The agent whose principal port the wire from `p` reaches, on lists. -/
def XNet.readAgent (X : XNet S) (w : Nat) (p : Port) : Option (Id × S) :=
  match assoc p X.wires with
  | none => none
  | some c =>
    match X.followTo w p c with
    | none => none
    | some i => (assoc i X.agents).map fun γ => (i, γ)

/-- The same, on the maps of the indexed memory. -/
def IMem.readAgent (H : IMem S) (w : Nat) (p : Port) : Option (Id × S) :=
  match (H.nb p).head? with
  | none => none
  | some c =>
    match H.followTo w p c with
    | none => none
    | some i => (H.sym i).map fun γ => (i, γ)

theorem IMem.readAgent_eq {H : IMem S} (h : H.Ok) (w : Nat) (p : Port) :
    H.readAgent w p = H.toX.readAgent w p := by
  unfold IMem.readAgent XNet.readAgent
  rw [h.first p]
  cases assoc p H.toX.wires with
  | none => rfl
  | some c =>
    dsimp only
    rw [IMem.followTo_eq h]
    cases H.toX.followTo w p c with
    | none => rfl
    | some i =>
      dsimp only
      rw [h.sym i]

variable {ar : S → Nat}

omit [DecidableEq S] in
/-- **What `readAgent` returns is the agent wired to the port** by its
principal port. -/
theorem XNet.readAgent_sound {X : XNet S} (hX : X.toNet.WF ar) {w : Nat} {p : Port}
    (hp : X.toNet.End ar p) {i : Id} {γ : S} (h : X.readAgent w p = some (i, γ)) :
    X.toNet.Paired ar p (i, 0) ∧ X.toNet.agent i γ := by
  unfold XNet.readAgent at h
  cases hc : assoc p X.wires with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    dsimp only at h
    cases hf : X.followTo w p c with
    | none => rw [hf] at h; cases h
    | some i' =>
      rw [hf] at h
      dsimp only at h
      cases ha : assoc i' X.agents with
      | none => rw [ha] at h; cases h
      | some γ' =>
        rw [ha] at h
        cases h
        have hag : (i, γ) ∈ X.agents := assoc_mem ha
        obtain ⟨⟨x, wk⟩, -⟩ := XNet.followTo_sound hX w p c i (assoc_mem hc) hf
        exact ⟨⟨hp, .inr ⟨γ, hag, Nat.zero_le _⟩, c, x, wk⟩, hag⟩

omit [DecidableEq S] in
/-- **Fuel for the segments of the memory finds the agent** wired to a
port, when there is one. -/
theorem XNet.readAgent_complete {X : XNet S} (hX : X.toNet.WF ar) {p : Port} {i : Id} {γ : S}
    (hpair : X.toNet.Paired ar p (i, 0)) (hag : X.toNet.agent i γ) :
    X.readAgent X.wires.length p = some (i, γ) := by
  obtain ⟨hp, -, v, x, wk⟩ := hpair
  have hv : assoc p X.wires = some v :=
    assoc_eq_of_unique wk.link_first fun q' hq' => hX.end_unique hp hq' wk.link_first
  obtain ⟨f, hf⟩ := XNet.followTo_complete hX wk hag
  have hf' := XNet.followTo_wires (assoc_mem hv) hf
  have ha : assoc i X.agents = some γ :=
    assoc_eq_of_unique hag fun γ' h' => hX.agent_fun h' hag
  unfold XNet.readAgent
  rw [hv]
  dsimp only
  rw [hf']
  dsimp only
  rw [ha]
  rfl

omit [DecidableEq S] in
/-- Reading on lists with more fuel for the segments finds the same. -/
theorem XNet.readAgent_mono {X : XNet S} {w w' : Nat} (hw : w ≤ w') {p : Port} {i : Id}
    {γ : S} (h : X.readAgent w p = some (i, γ)) : X.readAgent w' p = some (i, γ) := by
  unfold XNet.readAgent at h ⊢
  cases hc : assoc p X.wires with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    dsimp only at h ⊢
    cases hf : X.followTo w p c with
    | none => rw [hf] at h; cases h
    | some i' =>
      rw [hf] at h
      rw [XNet.followTo_mono hf hw]
      exact h

/-- **Run and read the agents on the indexed memory**: the busy-first run
from `X` with `nt` threads within `s` actions and, if every thread is then
at rest, the symbols of the agents wired to the ports `ps`, with the time
of the run. -/
def IJMach.runReadAgents (xs : XSys S) (X : XNet S) (ps : List Port) (nt s : Nat) :
    Option (List S × Nat) :=
  match IJMach.bfLoopS xs nt s 0 0 (IJMach.init X nt) with
  | (_, t, M) =>
    if M.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) then
      (ps.mapM fun p => (M.mem.readAgent s p).map (·.2)).map fun γs => (γs, t)
    else none

variable {xs : XSys S}

/-- Two lists in step, each pair related by `R`. -/
inductive ListRel {A B : Type} (R : A → B → Prop) : List A → List B → Prop
  | nil : ListRel R [] []
  | cons {a b l r} : R a b → ListRel R l r → ListRel R (a :: l) (b :: r)

theorem ListRel.imp_mem {A B : Type} {R R' : A → B → Prop} :
    ∀ {l : List A} {r : List B}, ListRel R l r → (∀ {a b}, a ∈ l → R a b → R' a b) →
      ListRel R' l r
  | _, _, .nil, _ => .nil
  | _, _, .cons hab hlr, h =>
    .cons (h List.mem_cons_self hab)
      (ListRel.imp_mem hlr fun ha hR => h (List.mem_cons_of_mem _ ha) hR)

theorem mapM_some {A B : Type} {f : A → Option B} :
    ∀ {l : List A} {r : List B}, l.mapM f = some r → ListRel (fun a b => f a = some b) l r
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | none => rw [hl] at h; cases h
      | some r' =>
        rw [hl] at h
        cases h
        exact .cons ha (mapM_some hl)

theorem mapM_of_forall {A B : Type} {f : A → Option B} {P : A → B → Prop}
    (hf : ∀ a, (∃ b, P a b) → ∃ b, f a = some b ∧ P a b) :
    ∀ (l : List A), (∀ a ∈ l, ∃ b, P a b) →
      ∃ r, l.mapM f = some r ∧ ListRel P l r
  | [], _ => ⟨[], rfl, .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb, hP⟩ := hf a (h a List.mem_cons_self)
    obtain ⟨r, hr, hR⟩ := mapM_of_forall hf l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    refine ⟨b :: r, ?_, .cons hP hR⟩
    rw [List.mapM_cons, hb, hr]
    rfl

/-- Where the busy-first run stops with every thread at rest, the indexed
memory is right and stands for the normal form, and for the memory of
`JMach` at the same action. -/
theorem IJMach.bfStop {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (s : Nat)
    (hr : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) = true) :
    ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.mem.Ok ∧
    ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.mem.toX = ((JMach.init X nt).trace xs
        (JMach.bfSched xs (JMach.init X nt) nt) (JMach.bfRun xs X nt s).1).1.mem ∧
    ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.mem.toNet = N' := by
  obtain ⟨a, -, ok⟩ := IJMach.init_sim hX hnd hnt (JMach.bfSched xs (JMach.init X nt) nt)
    (JMach.bfRun xs X nt s).1
  have hrest : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.resting = true := by
    rw [← a]
    exact hr
  obtain ⟨hs', hn'⟩ := JMach.rest_steps hX hnt hrest
  exact ⟨ok, congrArg JMach.mem a, (normal_form_unique hX hs' hs hn' hn).1⟩

/-- **Whatever `runReadAgents` returns names, for each port, the symbol of
the agent wired to it in the normal form**, for any fuel. -/
theorem IJMach.runReadAgents_sound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {ps : List Port}
    (hps : ∀ p ∈ ps, X.toNet.free p) {s : Nat} {γs : List S} {t : Nat}
    (h : IJMach.runReadAgents xs X ps nt s = some (γs, t)) :
    ListRel (fun p γ => ∃ i, N'.Paired xs.sys.ar p (i, 0) ∧ N'.agent i γ) ps γs := by
  unfold IJMach.runReadAgents at h
  rw [IJMach.bfLoopS_eq hX hnd hnt s] at h
  dsimp only at h
  by_cases hr : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) = true
  · rw [ite_pos' hr] at h
    obtain ⟨ok, em, e⟩ := IJMach.bfStop hX hnd hnt hs hn s hr
    have hW : N'.WF xs.sys.ar := Steps.wf hX hs
    cases hm : ps.mapM (fun p => (((IJMach.init X nt).trace xs
        (JMach.bfSched xs (JMach.init X nt) nt) (JMach.bfRun xs X nt s).1).1.mem.readAgent
          s p).map (·.2)) with
    | none => rw [hm] at h; cases h
    | some r =>
      rw [hm] at h
      cases h
      have hf := mapM_some hm
      refine ListRel.imp_mem hf fun {p γ} hp hpγ => ?_
      rw [IMem.readAgent_eq ok, em] at hpγ
      cases hra : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
          (JMach.bfRun xs X nt s).1).1.mem.readAgent s p with
      | none => rw [hra] at hpγ; cases hpγ
      | some iγ =>
        rw [hra] at hpγ
        obtain ⟨i, γ'⟩ := iγ
        cases hpγ
        have hfree : N'.free p := by
          rw [Steps.free hs]
          exact hps p hp
        have hp' : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
            (JMach.bfRun xs X nt s).1).1.mem.toNet.End xs.sys.ar p := by
          rw [e]
          exact .inl hfree
        have k := XNet.readAgent_sound (by rw [e]; exact hW) hp' hra
        rw [e] at k
        exact ⟨i, k⟩
  · rw [ite_neg' hr] at h
    cases h

/-- **With enough fuel `runReadAgents` returns the agents wired to the
ports in the normal form, in counted time**: given the work bound and two
actions, and the segments a memory can hold, when each port is wired to an
agent by its principal port in the normal form. -/
theorem IJMach.runReadAgents_eq {J : Nat} (hJ : xs.JoinsAtMost J) {X : XNet S}
    (hX : X.toNet.WF xs.sys.ar) (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt)
    {C D : Nat} (hb : xs.Bounded C D) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {ps : List Port}
    (hps : ∀ p ∈ ps, ∃ i γ, N'.Paired xs.sys.ar p (i, 0) ∧ N'.agent i γ) (s : Nat)
    (h₁ : X.workBound nt C D J n + 2 ≤ s) (h₂ : X.wires.length + D * n ≤ s) :
    ∃ γs t, IJMach.runReadAgents xs X ps nt s = some (γs, t) ∧
      ListRel (fun p γ => ∃ i, N'.Paired xs.sys.ar p (i, 0) ∧ N'.agent i γ) ps γs ∧
      t ≤ (2 * C + 3 * D + 6) * X.workBound nt C D J n := by
  have hk : (JMach.bfRun xs X nt s).1 ≤ X.workBound nt C D J n + 1 :=
    JMach.bfRun_rests hJ hX hnd hnt hb hs hn s
  have spec := JMach.pRun_spec xs (fun M i => M.bfPick nt i) (JMach.init X nt) s
  rw [← JMach.bfSched_eq] at spec
  have hrest := spec.2.2.1 (by
    show (JMach.bfRun xs X nt s).1 < s
    omega)
  obtain ⟨a, -, -⟩ := IJMach.init_sim hX hnd hnt (JMach.bfSched xs (JMach.init X nt) nt)
    (JMach.bfRun xs X nt s).1
  have hr : ((IJMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.ths.all (fun T => T.todo.isEmpty && T.st.isIdle) = true := by
    have : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
        (JMach.bfRun xs X nt s).1).1.resting = true := hrest
    rw [← a] at this
    exact this
  obtain ⟨ok, em, e⟩ := IJMach.bfStop hX hnd hnt hs hn s hr
  have hwl := JMach.trace_wires_le hX hb hs hn nt (JMach.bfSched xs (JMach.init X nt) nt)
    (JMach.bfRun xs X nt s).1
  have hW : ((JMach.init X nt).trace xs (JMach.bfSched xs (JMach.init X nt) nt)
      (JMach.bfRun xs X nt s).1).1.mem.toNet.WF xs.sys.ar := by
    rw [e]
    exact Steps.wf hX hs
  obtain ⟨γs, hm, hR⟩ := mapM_of_forall (f := fun p => (((IJMach.init X nt).trace xs
      (JMach.bfSched xs (JMach.init X nt) nt) (JMach.bfRun xs X nt s).1).1.mem.readAgent
        s p).map (·.2))
    (P := fun p γ => ∃ i, N'.Paired xs.sys.ar p (i, 0) ∧ N'.agent i γ)
    (fun p ⟨γ, i, hpair, hag⟩ => by
      refine ⟨γ, ?_, i, hpair, hag⟩
      rw [IMem.readAgent_eq ok, em]
      have hc := XNet.readAgent_complete hW (by rw [e]; exact hpair) (by rw [e]; exact hag)
      rw [XNet.readAgent_mono (by omega) hc]
      rfl)
    ps (fun p hp => by
      obtain ⟨i, γ, hpair, hag⟩ := hps p hp
      exact ⟨γ, i, hpair, hag⟩)
  refine ⟨γs, (IJMach.init X nt).time xs (JMach.bfSched xs (JMach.init X nt) nt)
    (JMach.bfRun xs X nt s).1, ?_, hR, IJMach.time_bfSched hJ hX hnd hnt hb hs hn _⟩
  unfold IJMach.runReadAgents
  rw [IJMach.bfLoopS_eq hX hnd hnt s]
  dsimp only
  rw [ite_pos' hr, hm]
  rfl

end INet
