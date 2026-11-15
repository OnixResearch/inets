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

end Adder

end Addition

end INet
