import InteractionNets.Addition

/-! # What a run leaves alone

A reduction that works on one part of a net leaves the rest as it was.
`N.Keeps ar C N'` says so for a set of names `C`: an agent of `N` whose
name is not in `C` is an agent of `N'`, and two ends of `N` joined by a
wire, neither on a name of `C`, are joined in `N'`.  One firing keeps
everything away from the two agents that fire (`Site.keeps`), and runs
compose (`Net.Keeps.trans`).

Numerals are followed through such runs by the list of their agents
(`Addition.NumList`).  A numeral whose agents are not in `C` is kept
(`Addition.NumList.keeps`), and when `C` is closed, the principal port of
a name in `C` being wired to a name in `C`, every numeral held at a port
outside `C` is outside `C` (`Addition.NumList.avoid`,
`Addition.IsNum.keeps`).  The names that a run on a numeral uses up
(`Addition.gone`) are closed in this sense.

The adder is proved here in this setting (`Addition.Adding.run`): the net
may have any other agents, other adders among them, and the result of the
adder may be wired to any port.  The theorem says what the run leaves
alone, and what agents the net has afterwards.
-/

namespace INet

variable {S : Type}

/-- **What a run leaves alone.**  `N'` has the agents of `N` whose names
are not in `C`, and the pairs of ends of `N` that are not on names of
`C`. -/
structure Net.Keeps (ar : S → Nat) (C : Id → Prop) (N N' : Net S) : Prop where
  agent : ∀ {i γ}, N.agent i γ → ¬ C i → N'.agent i γ
  paired : ∀ {p q}, N.Paired ar p q → ¬ C p.1 → ¬ C q.1 → N'.Paired ar p q

variable {ar : S → Nat} {N N₁ N₂ N' : Net S} {C C₁ C₂ : Id → Prop}

theorem Net.Keeps.refl (ar : S → Nat) (C : Id → Prop) (N : Net S) : N.Keeps ar C N :=
  ⟨fun h _ => h, fun h _ _ => h⟩

theorem Net.Keeps.mono (h : N.Keeps ar C N') {C' : Id → Prop} (hC : ∀ i, C i → C' i) :
    N.Keeps ar C' N' :=
  ⟨fun hi hn => h.agent hi fun c => hn (hC _ c),
    fun hp h1 h2 => h.paired hp (fun c => h1 (hC _ c)) fun c => h2 (hC _ c)⟩

/-- Runs compose: what both leave alone is left alone. -/
theorem Net.Keeps.trans (h₁ : N.Keeps ar C₁ N₁) (h₂ : N₁.Keeps ar C₂ N₂) :
    N.Keeps ar (fun i => C₁ i ∨ C₂ i) N₂ :=
  ⟨fun hi hn => h₂.agent (h₁.agent hi fun c => hn (.inl c)) fun c => hn (.inr c),
    fun hp h1 h2 => h₂.paired (h₁.paired hp (fun c => h1 (.inl c)) fun c => h2 (.inl c))
      (fun c => h1 (.inr c)) fun c => h2 (.inr c)⟩

/-- **One firing leaves alone everything away from the two agents.** -/
theorem Site.keeps {a b : Id} {α β : S} (h : Site ar N a b α β) (R : Rhs S) :
    N.Keeps ar (fun i => i = a ∨ i = b) (N.fire a b R) :=
  ⟨fun hi hn => .inl ⟨hi, fun e => hn (.inl e), fun e => hn (.inr e)⟩,
    fun hp h1 h2 => h.paired_fire hp (fun e => h1 (.inl e)) (fun e => h1 (.inr e))
      (fun e => h2 (.inl e)) fun e => h2 (.inr e)⟩

namespace Addition

variable {zero succ add : S} {a s i : Id} {l : List Id} {σ : S}

/-- **The agents of a numeral**, from its head down: successors, each
with the next agent on its auxiliary port, and a zero last. -/
inductive NumList (ar : S → Nat) (zero succ : S) (N : Net S) : Id → List Id → Prop
  | last {i : Id} : N.agent i zero → NumList ar zero succ N i [i]
  | next {i i' : Id} {l : List Id} : N.agent i succ → N.Paired ar (i, 1) (i', 0) →
      NumList ar zero succ N i' l → NumList ar zero succ N i (i :: l)

theorem NumList.head_mem (h : NumList ar zero succ N i l) : i ∈ l := by
  cases h with
  | last _ => exact List.mem_cons_self
  | next _ _ _ => exact List.mem_cons_self

/-- The numeral `k` has `k + 1` agents. -/
theorem Num.list : ∀ {k : Nat} {i : Id}, Num ar zero succ N i k →
    ∃ l, NumList ar zero succ N i l ∧ l.length = k + 1
  | 0, _, h => ⟨_, .last h, rfl⟩
  | _ + 1, _, ⟨hs, _, hp, hn⟩ => by
    obtain ⟨l, hl, e⟩ := Num.list hn
    exact ⟨_, .next hs hp hl, by rw [List.length_cons, e]⟩

theorem NumList.num (h : NumList ar zero succ N i l) :
    ∃ k, l.length = k + 1 ∧ Num ar zero succ N i k := by
  induction h with
  | last hz => exact ⟨0, rfl, hz⟩
  | next hs hp _ ih =>
    obtain ⟨k, e, hn⟩ := ih
    exact ⟨k + 1, by rw [List.length_cons, e], hs, _, hp, hn⟩

/-- The agents of a numeral are zeros and successors. -/
theorem NumList.label (h : NumList ar zero succ N i l) :
    ∀ j, j ∈ l → N.agent j zero ∨ N.agent j succ := by
  induction h with
  | last hz =>
    intro j hj
    rw [List.mem_singleton.1 hj]
    exact .inl hz
  | next hs _ _ ih =>
    intro j hj
    rcases List.mem_cons.1 hj with e | hj'
    · rw [e]
      exact .inr hs
    · exact ih j hj'

/-- An agent whose principal port is wired to the principal port of `a`
is in no numeral that is held at another port. -/
theorem NumList.not_mem (hN : N.WF ar) (hs : N.Paired ar (a, 0) (s, 0))
    (h : NumList ar zero succ N i l) :
    ∀ {p : Port}, N.Paired ar p (i, 0) → p ≠ (a, 0) → ¬ s ∈ l := by
  induction h with
  | @last i hz =>
    intro p hp hne hm
    have e : s = i := List.mem_singleton.1 hm
    rw [← e] at hp
    exact hne (hp.det_left hN hs)
  | @next i i' l hsu hpi _ ih =>
    intro p hp hne hm
    rcases List.mem_cons.1 hm with e | hm'
    · rw [← e] at hp
      exact hne (hp.det_left hN hs)
    · exact ih hpi (port_ne_snd (by decide)) hm'

/-- **A numeral away from `C` is kept.** -/
theorem NumList.keeps (k : N.Keeps ar C N') (h : NumList ar zero succ N i l) :
    (∀ j, j ∈ l → ¬ C j) → NumList ar zero succ N' i l := by
  induction h with
  | last hz => exact fun hC => .last (k.agent hz (hC _ List.mem_cons_self))
  | next hs hp hl ih =>
    exact fun hC => .next (k.agent hs (hC _ List.mem_cons_self))
      (k.paired hp (hC _ List.mem_cons_self) (hC _ (List.mem_cons_of_mem _ hl.head_mem)))
      (ih fun j hj => hC j (List.mem_cons_of_mem _ hj))

/-- `C` is closed: the principal port of a name in `C` is wired to a port
of a name in `C`. -/
def Closed (ar : S → Nat) (C : Id → Prop) (N : Net S) : Prop :=
  ∀ (i : Id) (q : Port), C i → N.Paired ar q (i, 0) → C q.1

/-- **A numeral held outside a closed set is outside it.** -/
theorem NumList.avoid (hC : Closed ar C N) (h : NumList ar zero succ N i l) :
    ∀ {p : Port}, N.Paired ar p (i, 0) → ¬ C p.1 → ∀ j, j ∈ l → ¬ C j := by
  induction h with
  | @last i hz =>
    intro p hp hpC j hj hc
    rw [List.mem_singleton.1 hj] at hc
    exact hpC (hC i p hc hp)
  | @next i i' l hs hpi _ ih =>
    intro p hp hpC j hj hc
    have hi : ¬ C i := fun c => hpC (hC i p c hp)
    rcases List.mem_cons.1 hj with e | hj'
    · rw [e] at hc
      exact hi hc
    · exact ih hpi hi j hj' hc

/-- **A numeral held at a port outside a closed set is kept.** -/
theorem IsNum.keeps (k : N.Keeps ar C N') (hC : Closed ar C N) {p : Port} {n : Nat}
    (h : IsNum ar zero succ N p n) (hp : ¬ C p.1) : IsNum ar zero succ N' p n := by
  obtain ⟨i, hpi, hn⟩ := h
  obtain ⟨l, hl, e⟩ := Num.list hn
  have hav := hl.avoid hC hpi hp
  obtain ⟨n', e', hn'⟩ := (hl.keeps k hav).num
  have en : n' = n := by omega
  rw [en] at hn'
  exact ⟨i, k.paired hpi hp (hav i hl.head_mem), hn'⟩

/-- The names that a run on the numeral `l` from the agent `a` uses up:
`a`, the agents of the numeral, and the names not in use, among which are
those of the agents the run makes. -/
def gone (N : Net S) (a : Id) (l : List Id) : Id → Prop :=
  fun j => j = a ∨ j ∈ l ∨ ¬ N.Used j

/-- The principal port of an agent of a numeral is wired to the port that
holds the numeral or to an agent of the numeral. -/
theorem NumList.partner (hN : N.WF ar) (h : NumList ar zero succ N i l) :
    ∀ {p₀ : Port}, N.Paired ar p₀ (i, 0) → ∀ j, j ∈ l → ∀ q, N.Paired ar q (j, 0) →
      q.1 = p₀.1 ∨ q.1 ∈ l := by
  induction h with
  | @last i hz =>
    intro p₀ hp₀ j hj q hq
    rw [List.mem_singleton.1 hj] at hq
    exact .inl (congrArg Prod.fst (hq.det_left hN hp₀))
  | @next i i' l hs hpi _ ih =>
    intro p₀ hp₀ j hj q hq
    rcases List.mem_cons.1 hj with e | hj'
    · rw [e] at hq
      exact .inl (congrArg Prod.fst (hq.det_left hN hp₀))
    · rcases ih hpi j hj' q hq with e | hm
      · exact .inr (by
          rw [e]
          exact List.mem_cons_self)
      · exact .inr (List.mem_cons_of_mem _ hm)

/-- **The names a run on a numeral uses up are closed.** -/
theorem gone_closed (hN : N.WF ar) (ha : N.Paired ar (a, 0) (i, 0))
    (hl : NumList ar zero succ N i l) : Closed ar (gone N a l) N := by
  intro j q hj hq
  rcases hj with e | hm | hu
  · rw [e] at hq
    have eq : q = (i, 0) := hq.det_left hN (ha.symm hN)
    exact .inr (.inl (by
      rw [eq]
      exact hl.head_mem))
  · rcases hl.partner hN ha j hm q hq with e | hm'
    · exact .inl e
    · exact .inr (.inl hm')
  · exact absurd (Net.End.used hq.2.1) hu

namespace Adder

/-- A tower survives the firing when the port it ends on is on neither
agent. -/
theorem tower_fire' (h : Adder ar add N a s σ) (hsa : succ ≠ add) (R : Rhs S) {r : Port}
    (hra : r.1 ≠ a) (hrs : r.1 ≠ s) : ∀ {j : Nat} {x : Port}, Tower ar succ N x j r →
      x.1 ≠ a ∧ x.1 ≠ s ∧ Tower ar succ (N.fire a s R) x j r
  | 0, x, ht => by
    have e : x = r := ht
    rw [e]
    exact ⟨hra, hrs, rfl⟩
  | j + 1, x, ⟨u, x', e, hu, hp, ht⟩ => by
    subst e
    obtain ⟨hx'a, hx's, ht'⟩ := tower_fire' h hsa R hra hrs ht
    have hua : u ≠ a := h.ne_add hu hsa
    have hus : u ≠ s := h.not_s hp (fun e => hx'a (congrArg Prod.fst e))
    exact ⟨hua, hus, u, x', rfl, .inl ⟨hu, hua, hus⟩,
      h.site.paired_fire hp hx'a hx's hua hus, ht'⟩

/-- The two agents of an active pair are a closed set. -/
theorem closed (h : Adder ar add N a s σ) : Closed ar (fun i => i = a ∨ i = s) N := by
  intro i q hi hq
  rcases hi with e | e
  · rw [e] at hq
    exact .inr (congrArg Prod.fst (hq.det_left h.wf (h.pair.symm h.wf)))
  · rw [e] at hq
    exact .inl (congrArg Prod.fst (hq.det_left h.wf h.pair))

end Adder

/-! ### The adder, with anything else around -/

/-- The new agents of the rule for `succ` are a successor and the adder
of the second side. -/
theorem succ_lab {o : Option Bool} {j : Nat} {γ : S}
    (h : (succData succ add).toX.toRhs.lab o j = some γ) :
    γ = succ ∨ (o = some true ∧ j = 0) := by
  have h' : assoc (o, j) (succData succ add).agents = some γ := h
  have hm : ((o, j), γ) ∈ [(((some false : Option Bool), 0), succ), ((some true, 0), add)] :=
    assoc_mem h'
  rcases List.mem_cons.1 hm with e | hm'
  · injection e with _ e2
    exact .inl e2
  · rcases List.mem_cons.1 hm' with e | hm''
    · injection e with e1 _
      injection e1 with e3 e4
      exact .inr ⟨e3, e4⟩
    · exact absurd hm'' List.not_mem_nil

/-- The situation of an addition under way, with anything else in the
net: the adder `a` faces the head `h` of what is left of its first
argument, with the agents `l`; its second argument is the numeral `n`;
above its result there are already `j` successors, up to the port `x`,
which is on a name in use that is neither the adder nor an agent of the
first argument.  The port `x` need not be free, and the net may have
other adders. -/
structure Adding (ar : S → Nat) (zero succ add : S) (N : Net S) (a : Id) (j : Nat) (h : Id)
    (l : List Id) (n : Nat) (x : Port) : Prop where
  wf : N.WF ar
  ha : N.agent a add
  fst : N.Paired ar (a, 0) (h, 0)
  num : NumList ar zero succ N h l
  snd : IsNum ar zero succ N (a, 1) n
  out : ∃ y, N.Paired ar (a, 2) y ∧ Tower ar succ N y j x
  hx : N.Used x.1 ∧ x.1 ≠ a ∧ ¬ x.1 ∈ l

/-- **The adder adds, with anything else around.**  The adder runs for as
many steps as its first argument has agents left, after which the port
`x` carries the numeral; everything away from the adder and its first
argument is kept, and the agents of the net are successors or agents of
the start other than the adder. -/
theorem Adding.run {sys : System S} (H : Rules sys zero succ add) :
    ∀ (l : List Id) {N : Net S} {a : Id} {j : Nat} {h : Id} {n : Nat} {x : Port} {m : Nat},
      Adding sys.ar zero succ add N a j h l n x → l.length = m + 1 →
      ∃ N', Steps (Step sys) l.length N N' ∧ IsNum sys.ar zero succ N' x (j + m + n) ∧
        N.Keeps sys.ar (gone N a l) N' ∧
        ∀ i γ, N'.agent i γ → γ = succ ∨ (N.agent i γ ∧ i ≠ a)
  | [], _, _, _, _, _, _, _, c, _ => by cases c.num
  | h :: l', N, a, j, _, n, x, m, c, hlen => by
    have hN := c.wf
    have ha := c.ha
    have hfst := c.fst
    have hx := c.hx
    obtain ⟨t, hpt, hnt⟩ := c.snd
    obtain ⟨y, hpy, hty⟩ := c.out
    have hnum := c.num
    cases hnum with
    | last hz =>
      have hm : m = 0 := Nat.succ.inj hlen.symm
      have hA : Adder sys.ar add N a h zero := ⟨hN, ha, hz, H.zero_ne_add, hfst⟩
      have red : Redex sys N a h add zero (zeroData (S := S)).toX.toRhs :=
        ⟨ha, hz, hA.site.ne, hfst.2.2, H.rule_zero⟩
      have st : Step sys N (N.fire a h (zeroData (S := S)).toX.toRhs) :=
        ⟨_, _, _, _, _, red, rfl⟩
      have hN₁ := Step.wf hN st
      have hta : t ≠ a := by
        rcases hnt.label with hx' | hx'
        · exact hA.ne_add hx' H.zero_ne_add
        · exact hA.ne_add hx' H.succ_ne_add
      have hts : t ≠ h := hA.not_s hpt (port_ne_snd (by decide))
      obtain ⟨hya, hyh, hty'⟩ :=
        hA.tower_fire' H.succ_ne_add (zeroData (S := S)).toX.toRhs hx.2.1
          (fun e => hx.2.2 (by
            rw [e]
            exact List.mem_cons_self)) hty
      have hlk : (zeroData (S := S)).toX.toRhs.link (.ifc false 0) (.ifc false 1) := rfl
      have hp : (N.fire a h (zeroData (S := S)).toX.toRhs).Paired sys.ar (t, 0) y :=
        hA.site.paired_fire_ifc_ifc hlk (hpt.symm hN) (hpy.symm hN) hta hts hya hyh
      refine ⟨_, .single st, ?_, (hA.site.keeps _).mono ?_, ?_⟩
      · rw [hm, Nat.add_zero]
        exact hty'.num ⟨t, hp.symm hN₁, hA.num_fire H.zero_ne_add H.succ_ne_add _ hnt hts⟩
      · rintro i (e1 | e1)
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
      · rintro i γ (⟨hi, h1, -⟩ | ⟨o, j', -, hlab⟩)
        · exact .inr ⟨hi, h1⟩
        · cases hlab
    | @next _ h' _ hs hpi hl' =>
      obtain ⟨k, ek, -⟩ := hl'.num
      have hm : m = k + 1 := by
        have e : l'.length + 1 = m + 1 := hlen
        omega
      have hA : Adder sys.ar add N a h succ := ⟨hN, ha, hs, H.succ_ne_add, hfst⟩
      have hR : (succData succ add).toX.toRhs.WF sys.ar add succ := sys.rule_wf H.rule_succ
      have red : Redex sys N a h add succ (succData succ add).toX.toRhs :=
        ⟨ha, hs, hA.site.ne, hfst.2.2, H.rule_succ⟩
      have st : Step sys N (N.fire a h (succData succ add).toX.toRhs) :=
        ⟨_, _, _, _, _, red, rfl⟩
      have hN₁ := Step.wf hN st
      have hta : t ≠ a := by
        rcases hnt.label with hx' | hx'
        · exact hA.ne_add hx' H.zero_ne_add
        · exact hA.ne_add hx' H.succ_ne_add
      have hts : t ≠ h := hA.not_s hpt (port_ne_snd (by decide))
      have hh'a : h' ≠ a := by
        rcases hl'.label h' hl'.head_mem with hx' | hx'
        · exact hA.ne_add hx' H.zero_ne_add
        · exact hA.ne_add hx' H.succ_ne_add
      have hh'h : h' ≠ h := hA.not_s hpi (port_ne_snd (by decide))
      obtain ⟨hya, hyh, hty'⟩ :=
        hA.tower_fire' H.succ_ne_add (succData succ add).toX.toRhs hx.2.1
          (fun e => hx.2.2 (by
            rw [e]
            exact List.mem_cons_self)) hty
      -- the four wires of the right-hand side
      have p₁ : (N.fire a h (succData succ add).toX.toRhs).Paired sys.ar y
          (child a h (some false) 0, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show (succData succ add).toX.toRhs.link (.ifc false 1) (.new (some false) 0 0)
            from rfl)
          (hpy.symm hN) hya hyh
      have p₂ : (N.fire a h (succData succ add).toX.toRhs).Paired sys.ar
          (child a h (some false) 0, 1) (child a h (some true) 0, 2) :=
        Site.paired_fire_new_new hR
          (show (succData succ add).toX.toRhs.link (.new (some false) 0 1)
            (.new (some true) 0 2) from rfl)
      have p₃ : (N.fire a h (succData succ add).toX.toRhs).Paired sys.ar (h', 0)
          (child a h (some true) 0, 0) :=
        hA.site.paired_fire_ifc_new hR
          (show (succData succ add).toX.toRhs.link (.ifc true 0) (.new (some true) 0 0)
            from rfl)
          (hpi.symm hN) hh'a hh'h
      have p₄ : (N.fire a h (succData succ add).toX.toRhs).Paired sys.ar (t, 0)
          (child a h (some true) 0, 1) :=
        hA.site.paired_fire_ifc_new hR
          (show (succData succ add).toX.toRhs.link (.ifc false 0) (.new (some true) 0 1)
            from rfl)
          (hpt.symm hN) hta hts
      have hav : ∀ i, i ∈ l' → ¬ (i = a ∨ i = h) := by
        intro i hi hc
        rcases hc with e1 | e1
        · rw [e1] at hi
          rcases hl'.label a hi with hx' | hx'
          · exact H.zero_ne_add (hN.agent_fun hx' ha)
          · exact H.succ_ne_add (hN.agent_fun hx' ha)
        · rw [e1] at hi
          exact NumList.not_mem hN hfst hl' hpi (port_ne_snd (by decide)) hi
      have c' : Adding sys.ar zero succ add (N.fire a h (succData succ add).toX.toRhs)
          (child a h (some true) 0) (j + 1) h' l' n x :=
        { wf := hN₁
          ha := .inr ⟨some true, 0, rfl, rfl⟩
          fst := p₃.symm hN₁
          num := hl'.keeps (hA.site.keeps _) hav
          snd := ⟨t, p₄.symm hN₁, hA.num_fire H.zero_ne_add H.succ_ne_add _ hnt hts⟩
          out := ⟨_, p₂.symm hN₁, child a h (some false) 0, y, rfl,
            .inr ⟨some false, 0, rfl, rfl⟩, p₁, hty'⟩
          hx := ⟨Net.used_fire hN hx.1 _ _ _, fun e => hA.site.not_used_child (some true) 0 (by
            rw [← e]
            exact hx.1), fun hmem => hx.2.2 (List.mem_cons_of_mem _ hmem)⟩ }
      obtain ⟨N', sts, inum, kp, hag⟩ := Adding.run H l' c' ek
      have e : j + m + n = j + 1 + k + n := by omega
      refine ⟨N', .head st sts, ?_, ((hA.site.keeps _).trans kp).mono ?_, ?_⟩
      · rw [e]
        exact inum
      · rintro i ((e1 | e1) | e1 | hmem | hu)
        · exact .inl e1
        · exact .inr (.inl (by
            rw [e1]
            exact List.mem_cons_self))
        · exact .inr (.inr (by
            rw [e1]
            exact hA.site.not_used_child (some true) 0))
        · exact .inr (.inl (List.mem_cons_of_mem _ hmem))
        · exact .inr (.inr fun hu' => hu (Net.used_fire hN hu' _ _ _))
      · intro i γ hi
        rcases hag i γ hi with hsucc | ⟨hi₁, hne'⟩
        · exact .inl hsucc
        · rcases hi₁ with ⟨hi₀, h1, -⟩ | ⟨o, j', e1, hlab⟩
          · exact .inr ⟨hi₀, h1⟩
          · rcases succ_lab hlab with hsucc | ⟨rfl, rfl⟩
            · exact .inl hsucc
            · exact absurd e1 hne'

end Addition

end INet
