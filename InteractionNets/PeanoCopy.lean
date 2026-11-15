import InteractionNets.Peano
import InteractionNets.Keeps

/-! # Erasing and copying a numeral

The two helpers that multiplication needs, in the system `Peano`, with
any other agents in the net.

An eraser on a numeral `n` runs for `n + 1` steps; the eraser and the
agents of the numeral are then gone, nothing new is there, and what was
away from them is as it was (`Peano.erase`).

A copier on a numeral `n`, with its two copies wired to the ports `p₁`
and `p₂`, runs for `n + 1` steps, after which both ports carry the
numeral `n`, and what was away from the copier and the numeral is as it
was (`Peano.copy`).  The ports may be free ports or ports of other
agents.
-/

namespace INet

namespace Peano

open Addition (gone)

/-- The port `p` is wired to the numeral `k`. -/
abbrev IsNum (N : Net Peano) (p : Port) (k : Nat) : Prop := Addition.IsNum ar zero succ N p k

/-- The agents of a numeral, from its head down. -/
abbrev NumList (N : Net Peano) (i : Id) (l : List Id) : Prop :=
  Addition.NumList ar zero succ N i l

/-- Above the port `x` there are `j` successors, the last of which has its
principal port wired to `r`. -/
abbrev Tower (N : Net Peano) (x : Port) (j : Nat) (r : Port) : Prop :=
  Addition.Tower ar succ N x j r

theorem rule_era_zero : system.rule era zero = some eraZero.toX.toRhs := rfl
theorem rule_era_succ : system.rule era succ = some eraSucc.toX.toRhs := rfl
theorem rule_dup_zero : system.rule dup zero = some dupZero.toX.toRhs := rfl
theorem rule_dup_succ : system.rule dup succ = some dupSucc.toX.toRhs := rfl

/-- The rule for erasing a successor makes one agent, the new eraser. -/
theorem eraSucc_lab {o : Option Bool} {j : Nat} {γ : Peano}
    (h : eraSucc.toX.toRhs.lab o j = some γ) : o = some true ∧ j = 0 := by
  have h' : assoc (o, j) eraSucc.agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some true : Option Bool), 0), era)] := assoc_mem h'
  rcases List.mem_cons.1 hm with e | hm'
  · injection e with e1 _
    injection e1 with e3 e4
    exact ⟨e3, e4⟩
  · exact absurd hm' List.not_mem_nil

/-! ### Erasing -/

/-- **Erasing a numeral.**  Let the eraser `e` face the head `h` of a
numeral with the agents `l`.  The net reduces, in as many steps as the
numeral has agents, to a net that has kept everything away from the
eraser and the numeral, and whose agents are those of the start without
the eraser and the numeral. -/
theorem erase : ∀ (l : List Id) {N : Net Peano} {e h : Id}, N.WF ar → N.agent e era →
    N.Paired ar (e, 0) (h, 0) → NumList N h l →
    ∃ N', Steps (Step system) l.length N N' ∧ N.Keeps ar (gone N e l) N' ∧
      ∀ i γ, N'.agent i γ → N.agent i γ ∧ i ≠ e ∧ ¬ i ∈ l
  | [], _, _, _, _, _, _, hl => by cases hl
  | h :: l', N, e, _, hN, he, hp, hl => by
    cases hl with
    | last hz =>
      have hA : Addition.Adder ar era N e h zero := ⟨hN, he, hz, by decide, hp⟩
      have red : Redex system N e h era zero eraZero.toX.toRhs :=
        ⟨he, hz, hA.site.ne, hp.2.2, rule_era_zero⟩
      have st : Step system N (N.fire e h eraZero.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
      refine ⟨_, .single st, (hA.site.keeps _).mono ?_, ?_⟩
      · rintro i (e1 | e1)
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
      · rintro i γ (⟨hi, h1, h2⟩ | ⟨o, j, -, hlab⟩)
        · exact ⟨hi, h1, fun hm => h2 (List.mem_singleton.1 hm)⟩
        · cases hlab
    | @next _ h' _ hs hpi hl' =>
      have hA : Addition.Adder ar era N e h succ := ⟨hN, he, hs, by decide, hp⟩
      have hR : eraSucc.toX.toRhs.WF ar era succ := system.rule_wf rule_era_succ
      have red : Redex system N e h era succ eraSucc.toX.toRhs :=
        ⟨he, hs, hA.site.ne, hp.2.2, rule_era_succ⟩
      have st : Step system N (N.fire e h eraSucc.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
      have hN₁ := Step.wf hN st
      have hh'e : h' ≠ e := by
        rcases hl'.label h' hl'.head_mem with hx | hx
        · exact hA.ne_add hx (by decide)
        · exact hA.ne_add hx (by decide)
      have hh'h : h' ≠ h := hA.not_s hpi (port_ne_snd (by decide))
      -- the new eraser faces the rest of the numeral
      have pe : (N.fire e h eraSucc.toX.toRhs).Paired ar (h', 0) (child e h (some true) 0, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show eraSucc.toX.toRhs.link (.ifc true 0) (.new (some true) 0 0) from rfl)
          (hpi.symm hN) hh'e hh'h
      have hav : ∀ j, j ∈ l' → ¬ (j = e ∨ j = h) := by
        intro j hj hc
        rcases hc with e1 | e1
        · rw [e1] at hj
          rcases hl'.label e hj with hx | hx
          · exact absurd (hN.agent_fun hx he) (by decide)
          · exact absurd (hN.agent_fun hx he) (by decide)
        · rw [e1] at hj
          exact Addition.NumList.not_mem hN hp hl' hpi (port_ne_snd (by decide)) hj
      have hl₁ : NumList (N.fire e h eraSucc.toX.toRhs) h' l' :=
        hl'.keeps (hA.site.keeps _) hav
      have he' : (N.fire e h eraSucc.toX.toRhs).agent (child e h (some true) 0) era :=
        .inr ⟨some true, 0, rfl, rfl⟩
      obtain ⟨N', sts, kp, hag⟩ := erase l' hN₁ he' (pe.symm hN₁) hl₁
      refine ⟨N', .head st sts, ((hA.site.keeps _).trans kp).mono ?_, ?_⟩
      · rintro i ((e1 | e1) | e1 | hm | hu)
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
        · exact .inr (.inr (by
            rw [e1]
            exact hA.site.not_used_child (some true) 0))
        · exact .inr (.inl (List.mem_cons_of_mem _ hm))
        · exact .inr (.inr fun hu' => hu (Net.used_fire hN hu' _ _ _))
      · intro i γ hi
        obtain ⟨hi₁, hne', hnl⟩ := hag i γ hi
        rcases hi₁ with ⟨hi₀, h1, h2⟩ | ⟨o, j, e1, hlab⟩
        · exact ⟨hi₀, h1, fun hm => (List.mem_cons.1 hm).elim h2 hnl⟩
        · obtain ⟨rfl, rfl⟩ := eraSucc_lab hlab
          exact absurd e1 hne'

/-- **Erasing the numeral `n`** takes `n + 1` steps. -/
theorem erase_num {N : Net Peano} {e : Id} {n : Nat} (hN : N.WF ar) (he : N.agent e era)
    (hn : IsNum N (e, 0) n) :
    ∃ N' l, l.length = n + 1 ∧ Steps (Step system) (n + 1) N N' ∧ N.Keeps ar (gone N e l) N' ∧
      ∀ i γ, N'.agent i γ → N.agent i γ ∧ i ≠ e ∧ ¬ i ∈ l := by
  obtain ⟨h, hp, hk⟩ := hn
  obtain ⟨l, hl, el⟩ := Addition.Num.list hk
  obtain ⟨N', sts, kp, hag⟩ := erase l hN he hp hl
  rw [el] at sts
  exact ⟨N', l, el, sts, kp, hag⟩

/-! ### Copying -/

/-- The situation of a copy under way: the copier `d` faces the head `h`
of what is left of the numeral, with the agents `l`; above each of its
two copies there are already `j` successors, up to the ports `p₁` and
`p₂`, which are on names in use that are neither the copier nor agents of
the numeral. -/
structure Copying (N : Net Peano) (d : Id) (j : Nat) (h : Id) (l : List Id) (p₁ p₂ : Port) :
    Prop where
  wf : N.WF ar
  hd : N.agent d dup
  fst : N.Paired ar (d, 0) (h, 0)
  num : NumList N h l
  out₁ : ∃ x, N.Paired ar (d, 1) x ∧ Tower N x j p₁
  out₂ : ∃ x, N.Paired ar (d, 2) x ∧ Tower N x j p₂
  hp₁ : N.Used p₁.1 ∧ p₁.1 ≠ d ∧ ¬ p₁.1 ∈ l
  hp₂ : N.Used p₂.1 ∧ p₂.1 ≠ d ∧ ¬ p₂.1 ∈ l

/-- The copier runs for as many steps as the numeral has agents left,
after which both ports carry the numeral, with the successors already
made, and everything away from the copier and the numeral is kept. -/
theorem Copying.run : ∀ (l : List Id) {N : Net Peano} {d : Id} {j : Nat} {h : Id}
    {p₁ p₂ : Port} {n : Nat}, Copying N d j h l p₁ p₂ → l.length = n + 1 →
    ∃ N', Steps (Step system) l.length N N' ∧ IsNum N' p₁ (j + n) ∧ IsNum N' p₂ (j + n) ∧
      N.Keeps ar (gone N d l) N'
  | [], _, _, _, _, _, _, _, c, _ => by cases c.num
  | h :: l', N, d, j, _, p₁, p₂, n, c, hlen => by
    have hN := c.wf
    obtain ⟨x₁, hpx₁, ht₁⟩ := c.out₁
    obtain ⟨x₂, hpx₂, ht₂⟩ := c.out₂
    have hp₁ := c.hp₁
    have hp₂ := c.hp₂
    have hd := c.hd
    have hfst := c.fst
    have hnum := c.num
    cases hnum with
    | last hz =>
      have hn : n = 0 := Nat.succ.inj hlen.symm
      have hA : Addition.Adder ar dup N d h zero := ⟨hN, hd, hz, by decide, hfst⟩
      have hR : dupZero.toX.toRhs.WF ar dup zero := system.rule_wf rule_dup_zero
      have red : Redex system N d h dup zero dupZero.toX.toRhs :=
        ⟨hd, hz, hA.site.ne, hfst.2.2, rule_dup_zero⟩
      have st : Step system N (N.fire d h dupZero.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
      obtain ⟨hx₁d, hx₁h, ht₁'⟩ := hA.tower_fire' (by decide) dupZero.toX.toRhs hp₁.2.1
        (fun e => hp₁.2.2 (by
          rw [e]
          exact List.mem_cons_self)) ht₁
      obtain ⟨hx₂d, hx₂h, ht₂'⟩ := hA.tower_fire' (by decide) dupZero.toX.toRhs hp₂.2.1
        (fun e => hp₂.2.2 (by
          rw [e]
          exact List.mem_cons_self)) ht₂
      -- a new zero on each copy
      have q₁ : (N.fire d h dupZero.toX.toRhs).Paired ar x₁ (child d h (some false) 0, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show dupZero.toX.toRhs.link (.ifc false 0) (.new (some false) 0 0) from rfl)
          (hpx₁.symm hN) hx₁d hx₁h
      have q₂ : (N.fire d h dupZero.toX.toRhs).Paired ar x₂ (child d h (some true) 0, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show dupZero.toX.toRhs.link (.ifc false 1) (.new (some true) 0 0) from rfl)
          (hpx₂.symm hN) hx₂d hx₂h
      have n₁ : IsNum (N.fire d h dupZero.toX.toRhs) x₁ 0 :=
        ⟨_, q₁, .inr ⟨some false, 0, rfl, rfl⟩⟩
      have n₂ : IsNum (N.fire d h dupZero.toX.toRhs) x₂ 0 :=
        ⟨_, q₂, .inr ⟨some true, 0, rfl, rfl⟩⟩
      refine ⟨_, .single st, ?_, ?_, (hA.site.keeps _).mono ?_⟩
      · rw [hn]
        exact ht₁'.num n₁
      · rw [hn]
        exact ht₂'.num n₂
      · rintro i (e1 | e1)
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
    | @next _ h' _ hs hpi hl' =>
      obtain ⟨k, ek, -⟩ := hl'.num
      have hn : n = k + 1 := by
        have e : l'.length + 1 = n + 1 := hlen
        omega
      have hA : Addition.Adder ar dup N d h succ := ⟨hN, hd, hs, by decide, hfst⟩
      have hR : dupSucc.toX.toRhs.WF ar dup succ := system.rule_wf rule_dup_succ
      have red : Redex system N d h dup succ dupSucc.toX.toRhs :=
        ⟨hd, hs, hA.site.ne, hfst.2.2, rule_dup_succ⟩
      have st : Step system N (N.fire d h dupSucc.toX.toRhs) := ⟨_, _, _, _, _, red, rfl⟩
      have hN₁ := Step.wf hN st
      have hh'd : h' ≠ d := by
        rcases hl'.label h' hl'.head_mem with hx | hx
        · exact hA.ne_add hx (by decide)
        · exact hA.ne_add hx (by decide)
      have hh'h : h' ≠ h := hA.not_s hpi (port_ne_snd (by decide))
      obtain ⟨hx₁d, hx₁h, ht₁'⟩ := hA.tower_fire' (by decide) dupSucc.toX.toRhs hp₁.2.1
        (fun e => hp₁.2.2 (by
          rw [e]
          exact List.mem_cons_self)) ht₁
      obtain ⟨hx₂d, hx₂h, ht₂'⟩ := hA.tower_fire' (by decide) dupSucc.toX.toRhs hp₂.2.1
        (fun e => hp₂.2.2 (by
          rw [e]
          exact List.mem_cons_self)) ht₂
      -- the five wires of the right-hand side
      have q₁ : (N.fire d h dupSucc.toX.toRhs).Paired ar x₁ (child d h (some false) 0, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show dupSucc.toX.toRhs.link (.ifc false 0) (.new (some false) 0 0) from rfl)
          (hpx₁.symm hN) hx₁d hx₁h
      have q₂ : (N.fire d h dupSucc.toX.toRhs).Paired ar x₂ (child d h (some false) 1, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show dupSucc.toX.toRhs.link (.ifc false 1) (.new (some false) 1 0) from rfl)
          (hpx₂.symm hN) hx₂d hx₂h
      have q₃ : (N.fire d h dupSucc.toX.toRhs).Paired ar (child d h (some false) 0, 1)
          (child d h (some true) 0, 1) :=
        Site.paired_fire_new_new hR
          (show dupSucc.toX.toRhs.link (.new (some false) 0 1) (.new (some true) 0 1) from rfl)
      have q₄ : (N.fire d h dupSucc.toX.toRhs).Paired ar (child d h (some false) 1, 1)
          (child d h (some true) 0, 2) :=
        Site.paired_fire_new_new hR
          (show dupSucc.toX.toRhs.link (.new (some false) 1 1) (.new (some true) 0 2) from rfl)
      have q₅ : (N.fire d h dupSucc.toX.toRhs).Paired ar (h', 0) (child d h (some true) 0, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show dupSucc.toX.toRhs.link (.ifc true 0) (.new (some true) 0 0) from rfl)
          (hpi.symm hN) hh'd hh'h
      have hav : ∀ i, i ∈ l' → ¬ (i = d ∨ i = h) := by
        intro i hi hc
        rcases hc with e1 | e1
        · rw [e1] at hi
          rcases hl'.label d hi with hx | hx
          · exact absurd (hN.agent_fun hx hd) (by decide)
          · exact absurd (hN.agent_fun hx hd) (by decide)
        · rw [e1] at hi
          exact Addition.NumList.not_mem hN hfst hl' hpi (port_ne_snd (by decide)) hi
      have c' : Copying (N.fire d h dupSucc.toX.toRhs) (child d h (some true) 0) (j + 1) h' l'
          p₁ p₂ :=
        { wf := hN₁
          hd := .inr ⟨some true, 0, rfl, rfl⟩
          fst := q₅.symm hN₁
          num := hl'.keeps (hA.site.keeps _) hav
          out₁ := ⟨_, q₃.symm hN₁, child d h (some false) 0, x₁, rfl,
            .inr ⟨some false, 0, rfl, rfl⟩, q₁, ht₁'⟩
          out₂ := ⟨_, q₄.symm hN₁, child d h (some false) 1, x₂, rfl,
            .inr ⟨some false, 1, rfl, rfl⟩, q₂, ht₂'⟩
          hp₁ := ⟨Net.used_fire hN hp₁.1 _ _ _, fun e => hA.site.not_used_child (some true) 0 (by
            rw [← e]
            exact hp₁.1), fun hm => hp₁.2.2 (List.mem_cons_of_mem _ hm)⟩
          hp₂ := ⟨Net.used_fire hN hp₂.1 _ _ _, fun e => hA.site.not_used_child (some true) 0 (by
            rw [← e]
            exact hp₂.1), fun hm => hp₂.2.2 (List.mem_cons_of_mem _ hm)⟩ }
      obtain ⟨N', sts, i₁, i₂, kp⟩ := Copying.run l' c' ek
      have e : j + n = j + 1 + k := by omega
      refine ⟨N', .head st sts, ?_, ?_, ((hA.site.keeps _).trans kp).mono ?_⟩
      · rw [e]
        exact i₁
      · rw [e]
        exact i₂
      · rintro i ((e1 | e1) | e1 | hm | hu)
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
        · exact .inr (.inr (by
            rw [e1]
            exact hA.site.not_used_child (some true) 0))
        · exact .inr (.inl (List.mem_cons_of_mem _ hm))
        · exact .inr (.inr fun hu' => hu (Net.used_fire hN hu' _ _ _))

/-- **Copying a numeral.**  Let the copier `d` face the head `h` of the
numeral `n`, with the agents `l`, and let its two copies be wired to the
ports `p₁` and `p₂`, neither on the copier or on an agent of the numeral.
The net reduces, in `n + 1` steps, to a net in which both ports carry the
numeral `n`, and which has kept everything away from the copier and the
numeral. -/
theorem copy {N : Net Peano} {d h : Id} {l : List Id} {p₁ p₂ : Port} {n : Nat}
    (hN : N.WF ar) (hd : N.agent d dup) (hp : N.Paired ar (d, 0) (h, 0)) (hl : NumList N h l)
    (hlen : l.length = n + 1) (h₁ : N.Paired ar (d, 1) p₁) (h₂ : N.Paired ar (d, 2) p₂)
    (hp₁ : p₁.1 ≠ d ∧ ¬ p₁.1 ∈ l) (hp₂ : p₂.1 ≠ d ∧ ¬ p₂.1 ∈ l) :
    ∃ N', Steps (Step system) (n + 1) N N' ∧ IsNum N' p₁ n ∧ IsNum N' p₂ n ∧
      N.Keeps ar (gone N d l) N' := by
  have c : Copying N d 0 h l p₁ p₂ :=
    ⟨hN, hd, hp, hl, ⟨p₁, h₁, rfl⟩, ⟨p₂, h₂, rfl⟩, ⟨Net.End.used h₁.2.1, hp₁⟩,
      ⟨Net.End.used h₂.2.1, hp₂⟩⟩
  obtain ⟨N', sts, i₁, i₂, kp⟩ := Copying.run l c hlen
  rw [hlen] at sts
  rw [Nat.zero_add] at i₁ i₂
  exact ⟨N', sts, i₁, i₂, kp⟩

/-! ### Two small runs -/

/-- An eraser on the numeral `2`, and nothing else. -/
def eraseTwo : XNet Peano :=
  XNet.ofWires [([1], era), ([2], succ), ([3], succ), ([4], zero)] []
    [(([1], 0), ([2], 0)), (([2], 1), ([3], 0)), (([3], 1), ([4], 0))]

/-- The reducer stops after three steps with no agent and no wire. -/
example : (eraseTwo.normalize xsys 20).map
    (fun r => (r.2, r.1.agents.length, r.1.wires.length)) = some (3, 0, 0) := by
  decide +kernel

/-- A copier on the numeral `2`, with its copies on two free ports. -/
def copyTwo : XNet Peano :=
  XNet.ofWires [([1], dup), ([2], succ), ([3], succ), ([4], zero)] [([0], 0), ([5], 0)]
    [(([1], 0), ([2], 0)), (([2], 1), ([3], 0)), (([3], 1), ([4], 0)),
      (([1], 1), ([0], 0)), (([1], 2), ([5], 0))]

/-- The reducer stops after three steps with four successors and two
zeros. -/
example : (copyTwo.normalize xsys 20).map (fun r => (r.2, r.1.agents.map (·.2))) =
    some (3, [succ, succ, succ, succ, zero, zero]) := by
  decide +kernel

end Peano

end INet
