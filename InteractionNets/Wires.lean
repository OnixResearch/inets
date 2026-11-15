import Std.Data.HashMap
import Std.Data.TreeMap
import InteractionNets.Rewriting

namespace INet

universe u v

/-! ## Wires

Wires are studied on their own first, for an arbitrary relation `L` of
segments between points and an arbitrary set `T` of terminals. -/

section Wires

variable {V : Type u} {L L' L₁ L₂ L₁' L₂' : V → V → Prop} {T T' : V → Prop}

/-- `Walk L T u v x y`: a non-backtracking chain of segments whose first
segment is `u — v` and whose last segment is `x — y`, none of whose
intermediate points is a terminal. -/
inductive Walk (L : V → V → Prop) (T : V → Prop) : V → V → V → V → Prop
  | single {u v : V} : L u v → Walk L T u v u v
  | cons {u v w x y : V} :
      L u v → ¬ T v → w ≠ u → Walk L T v w x y → Walk L T u v x y

/-- `p` and `q` are the two extremities of a wire. -/
def Conn (L : V → V → Prop) (T : V → Prop) (p q : V) : Prop :=
  ∃ v x, Walk L T p v x q

/-- Segments are symmetric, a point lies on at most two segments and a
terminal on at most one. -/
structure Wiring (L : V → V → Prop) (T : V → Prop) : Prop where
  symm : ∀ {p q}, L p q → L q p
  deg : ∀ {p x y z}, L p x → L p y → L p z → x = y ∨ x = z ∨ y = z
  term : ∀ {p q r}, T p → L p q → L p r → q = r

/-- Every terminal is joined by a wire to another terminal. -/
def Wired (L : V → V → Prop) (T : V → Prop) : Prop :=
  ∀ t, T t → ∃ t', T t' ∧ t' ≠ t ∧ Conn L T t t'

namespace Walk

theorem link_first {u v x y : V} (w : Walk L T u v x y) : L u v := by
  cases w with
  | single h => exact h
  | cons h _ _ _ => exact h

theorem link_last {u v x y : V} (w : Walk L T u v x y) : L x y := by
  induction w with
  | single h => exact h
  | cons _ _ _ _ ih => exact ih

/-- The point before the last is the starting point or is not a terminal. -/
theorem penult {u v x y : V} (w : Walk L T u v x y) : x = u ∨ ¬ T x := by
  induction w with
  | single _ => exact .inl rfl
  | cons _ hv _ _ ih =>
    rcases ih with rfl | h
    · exact .inr hv
    · exact .inr h

theorem snoc {u v x y z : V} (w : Walk L T u v x y)
    (hy : ¬ T y) (hl : L y z) (hz : z ≠ x) : Walk L T u v y z := by
  induction w with
  | single h => exact .cons h hy hz (.single hl)
  | cons h hv hw _ ih => exact .cons h hv hw (ih hy hl hz)

theorem append {u v x y z x' y' : V} (w₁ : Walk L T u v x y)
    (hy : ¬ T y) (w₂ : Walk L T y z x' y') (hz : z ≠ x) : Walk L T u v x' y' := by
  induction w₁ with
  | single h => exact .cons h hy hz w₂
  | cons h hv hw _ ih => exact .cons h hv hw (ih hy w₂ hz)

theorem rev (hs : ∀ {p q}, L p q → L q p) {u v x y : V}
    (w : Walk L T u v x y) : Walk L T y x v u := by
  induction w with
  | single h => exact .single (hs h)
  | cons h hv hw _ ih => exact ih.snoc hv (hs h) (Ne.symm hw)

/-- A walk survives when segments are added, as long as the points it runs
through do not become terminals. -/
theorem mono (hL : ∀ {p q}, L p q → L' p q) (hT : ∀ {p q}, L p q → ¬ T q → ¬ T' q)
    {u v x y : V} (w : Walk L T u v x y) : Walk L' T' u v x y := by
  induction w with
  | single h => exact .single (hL h)
  | cons h hv hw _ ih => exact .cons (hL h) (hT h hv) hw ih

/-- A walk is determined by its first segment and the fact that it stops at
the first terminal it meets. -/
theorem det (hW : Wiring L T) {u v x y x' y' : V}
    (w : Walk L T u v x y) (w' : Walk L T u v x' y')
    (hy : T y) (hy' : T y') : y = y' := by
  induction w generalizing x' y' with
  | single h =>
    cases w' with
    | single _ => rfl
    | cons _ hv _ _ => exact absurd hy hv
  | cons h hv hw w₁ ih =>
    cases w' with
    | single _ => exact absurd hy' hv
    | cons _ _ hw' w₂ =>
      rcases hW.deg w₁.link_first w₂.link_first (hW.symm h) with e | e | e
      · subst e; exact ih w₂ hy hy'
      · exact absurd e hw
      · exact absurd e hw'

end Walk

theorem Conn.symm (hW : Wiring L T) {p q : V} (h : Conn L T p q) : Conn L T q p := by
  obtain ⟨v, x, w⟩ := h
  exact ⟨x, v, w.rev hW.symm⟩

/-- A wire leaving a terminal has exactly one other extremity. -/
theorem Conn.det (hW : Wiring L T) {p q q' : V} (hp : T p) (hq : T q) (hq' : T q')
    (h : Conn L T p q) (h' : Conn L T p q') : q = q' := by
  obtain ⟨v, x, w⟩ := h
  obtain ⟨v', x', w'⟩ := h'
  obtain rfl := hW.term hp w.link_first w'.link_first
  exact w.det hW w' hq hq'

theorem Wired.congr (hL : ∀ p q, L p q ↔ L' p q) (hT : ∀ p, T p ↔ T' p)
    (h : Wired L T) : Wired L' T' := by
  have e₁ : L = L' := funext fun p => funext fun q => propext (hL p q)
  have e₂ : T = T' := funext fun p => propext (hT p)
  subst e₁ e₂
  exact h

/-- Adding segments between terminals, at most one per terminal, and
demoting their extremities, gives a wiring again. -/
theorem Wiring.add (hW : Wiring L T) {M : V → V → Prop}
    (hs : ∀ {p q}, M p q → M q p) (hf : ∀ {p q r}, M p q → M p r → q = r)
    (hT : ∀ {p q}, M p q → T p) :
    Wiring (fun p q => L p q ∨ M p q) (fun p => T p ∧ ¬ ∃ q, M p q) where
  symm := by
    rintro p q (h | h)
    · exact .inl (hW.symm h)
    · exact .inr (hs h)
  deg := by
    rintro p x y z (hx | hx) (hy | hy) (hz | hz)
    · exact hW.deg hx hy hz
    · exact .inl (hW.term (hT hz) hx hy)
    · exact .inr (.inl (hW.term (hT hy) hx hz))
    · exact .inr (.inr (hf hy hz))
    · exact .inr (.inr (hW.term (hT hx) hy hz))
    · exact .inr (.inl (hf hx hz))
    · exact .inl (hf hx hy)
    · exact .inl (hf hx hy)
  term := by
    rintro p q r ⟨hp, hn⟩ (hq | hq) (hr | hr)
    · exact hW.term hp hq hr
    · exact absurd ⟨_, hr⟩ hn
    · exact absurd ⟨_, hq⟩ hn
    · exact absurd ⟨_, hq⟩ hn

/-- Two wirings on the same terminals in which every terminal is joined to
the same other terminal.  `Wired L T` is the case of a wiring taken twice. -/
def JointWired (L₁ L₂ : V → V → Prop) (T : V → Prop) : Prop :=
  ∀ t, T t → ∃ t', T t' ∧ t' ≠ t ∧ Conn L₁ T t t' ∧ Conn L₂ T t t'

theorem Wired.joint (h : Wired L T) : JointWired L L T := by
  intro t ht
  obtain ⟨t', ht', hne, c⟩ := h t ht
  exact ⟨t', ht', hne, c, c⟩

theorem JointWired.left (h : JointWired L₁ L₂ T) : Wired L₁ T := by
  intro t ht
  obtain ⟨t', ht', hne, c, -⟩ := h t ht
  exact ⟨t', ht', hne, c⟩

theorem JointWired.right (h : JointWired L₁ L₂ T) : Wired L₂ T := by
  intro t ht
  obtain ⟨t', ht', hne, -, c⟩ := h t ht
  exact ⟨t', ht', hne, c⟩

/-- Jointly wired wirings pair their terminals in the same way. -/
theorem JointWired.conn_iff (h : JointWired L₁ L₂ T) (hW₁ : Wiring L₁ T) (hW₂ : Wiring L₂ T)
    {p q : V} (hp : T p) (hq : T q) : Conn L₁ T p q ↔ Conn L₂ T p q := by
  obtain ⟨t', ht', -, c₁, c₂⟩ := h p hp
  constructor
  · intro c
    rw [Conn.det hW₁ hp hq ht' c c₁]
    exact c₂
  · intro c
    rw [Conn.det hW₂ hp hq ht' c c₂]
    exact c₁

theorem JointWired.congr (hL₁ : ∀ p q, L₁ p q ↔ L₁' p q) (hL₂ : ∀ p q, L₂ p q ↔ L₂' p q)
    (hT : ∀ p, T p ↔ T' p) (h : JointWired L₁ L₂ T) : JointWired L₁' L₂' T' := by
  have e₁ : L₁ = L₁' := funext fun p => funext fun q => propext (hL₁ p q)
  have e₂ : L₂ = L₂' := funext fun p => funext fun q => propext (hL₂ p q)
  have e₃ : T = T' := funext fun p => propext (hT p)
  subst e₁ e₂ e₃
  exact h

/-- Two terminals joined by a wire can be retired together. -/
theorem JointWired.retire (hW₁ : Wiring L₁ T) (h : JointWired L₁ L₂ T) {u v : V}
    (hu : T u) (hv : T v) (huv : Conn L₁ T u v) :
    JointWired L₁ L₂ (fun p => T p ∧ p ≠ u ∧ p ≠ v) := by
  rintro t ⟨ht, htu, htv⟩
  obtain ⟨t', ht', hne, c₁, c₂⟩ := h t ht
  have h₁ : t' ≠ u := by
    rintro rfl
    exact htv (Conn.det hW₁ ht' ht hv (c₁.symm hW₁) huv)
  have h₂ : t' ≠ v := by
    rintro rfl
    exact htu (Conn.det hW₁ ht' ht hu (c₁.symm hW₁) (huv.symm hW₁))
  obtain ⟨z₁, x₁, w₁⟩ := c₁
  obtain ⟨z₂, x₂, w₂⟩ := c₂
  exact ⟨t', ⟨ht', h₁, h₂⟩, hne,
    ⟨z₁, x₁, w₁.mono (fun h => h) (fun _ hq hq' => hq hq'.1)⟩,
    ⟨z₂, x₂, w₂.mono (fun h => h) (fun _ hq hq' => hq hq'.1)⟩⟩

/-- A wire that stopped at `x`, a new segment `x — y` and a wire that left
`y` make up one wire. -/
theorem Walk.splice (hW : Wiring L T) {x y : V} (hx : T x) (hy : T y)
    (hL : ∀ {p q}, L p q → L' p q) (hT : ∀ {p}, T' p → T p)
    (hx' : ¬ T' x) (hy' : ¬ T' y) (hl : L' x y)
    {t z u z₂ u₂ t'' : V} (hty : t ≠ y)
    (w : Walk L T t z u x) (w₂ : Walk L T y z₂ u₂ t'') : Conn L' T' t t'' := by
  have h₃ : y ≠ u := by
    rcases w.penult with e | e
    · exact fun e' => hty (e.symm.trans e'.symm)
    · exact fun e' => e (e' ▸ hy)
  have h₄ : z₂ ≠ x := by
    rintro rfl
    exact h₃ (hW.term hx (hW.symm w₂.link_first) (hW.symm w.link_last))
  have mono : ∀ {a b c d : V}, Walk L T a b c d → Walk L' T' a b c d :=
    fun w => w.mono hL (fun _ hq hq' => hq (hT hq'))
  exact ⟨z, u₂, ((mono w).snoc hx' hl h₃).append hy' (mono w₂) h₄⟩

/-- One half of `JointWired.splice`: the wires that used to stop at `x` now
run on through the new segment `x — y` and along the wires that used to
leave `y`. -/
theorem JointWired.splice_aux (hW₁ : Wiring L₁ T) (hW₂ : Wiring L₂ T)
    (h : JointWired L₁ L₂ T) {x y : V} (hx : T x) (hy : T y) (hxy : x ≠ y)
    (hL₁ : ∀ {p q}, L₁ p q → L₁' p q) (hL₂ : ∀ {p q}, L₂ p q → L₂' p q)
    (hT : ∀ {p}, T' p → T p) (hT' : ∀ {p}, T p → p ≠ x → p ≠ y → T' p)
    (hx' : ¬ T' x) (hy' : ¬ T' y) (hl₁ : L₁' x y) (hl₂ : L₂' x y)
    {t : V} (ht : T' t) (c₁ : Conn L₁ T t x) (c₂ : Conn L₂ T t x) :
    ∃ t', T' t' ∧ t' ≠ t ∧ Conn L₁' T' t t' ∧ Conn L₂' T' t t' := by
  have ht₀ : T t := hT ht
  have hty : t ≠ y := fun e => hy' (e ▸ ht)
  obtain ⟨t'', ht'', hne, d₁, d₂⟩ := h y hy
  have h₁ : t'' ≠ x := by
    rintro rfl
    exact hty (Conn.det hW₁ ht'' ht₀ hy (c₁.symm hW₁) (d₁.symm hW₁))
  have h₂ : t'' ≠ t := by
    rintro rfl
    exact hxy (Conn.det hW₁ ht'' hx hy c₁ (d₁.symm hW₁))
  obtain ⟨z, u, w⟩ := c₁
  obtain ⟨z', u', w'⟩ := c₂
  obtain ⟨a, b, v⟩ := d₁
  obtain ⟨a', b', v'⟩ := d₂
  exact ⟨t'', hT' ht'' h₁ hne, h₂,
    Walk.splice hW₁ hx hy hL₁ hT hx' hy' hl₁ hty w v,
    Walk.splice hW₂ hx hy hL₂ hT hx' hy' hl₂ hty w' v'⟩

/-- Joining two terminals by a new segment turns the two wires that ended
there into one. -/
theorem JointWired.splice (hW₁ : Wiring L₁ T) (hW₂ : Wiring L₂ T) (h : JointWired L₁ L₂ T)
    {x y : V} (hx : T x) (hy : T y) (hxy : x ≠ y) :
    JointWired (fun p q => L₁ p q ∨ (p = x ∧ q = y) ∨ (p = y ∧ q = x))
      (fun p q => L₂ p q ∨ (p = x ∧ q = y) ∨ (p = y ∧ q = x))
      (fun p => T p ∧ p ≠ x ∧ p ≠ y) := by
  intro t ht
  obtain ⟨t', ht', hne, c₁, c₂⟩ := h t ht.1
  by_cases e₁ : t' = x
  · subst e₁
    exact JointWired.splice_aux hW₁ hW₂ h hx hy hxy (fun h => .inl h) (fun h => .inl h)
      (fun h => h.1) (fun h h₁ h₂ => ⟨h, h₁, h₂⟩) (fun h => h.2.1 rfl) (fun h => h.2.2 rfl)
      (.inr (.inl ⟨rfl, rfl⟩)) (.inr (.inl ⟨rfl, rfl⟩)) ht c₁ c₂
  by_cases e₂ : t' = y
  · subst e₂
    exact JointWired.splice_aux hW₁ hW₂ h hy hx hxy.symm (fun h => .inl h) (fun h => .inl h)
      (fun h => h.1) (fun h h₁ h₂ => ⟨h, h₂, h₁⟩) (fun h => h.2.2 rfl) (fun h => h.2.1 rfl)
      (.inr (.inr ⟨rfl, rfl⟩)) (.inr (.inr ⟨rfl, rfl⟩)) ht c₁ c₂
  · obtain ⟨z, u, w⟩ := c₁
    obtain ⟨z', u', w'⟩ := c₂
    exact ⟨t', ⟨ht', e₁, e₂⟩, hne,
      ⟨z, u, w.mono (fun h => .inl h) (fun _ hq hq' => hq hq'.1)⟩,
      ⟨z', u', w'.mono (fun h => .inl h) (fun _ hq hq' => hq hq'.1)⟩⟩

/-- Finitely many new segments between terminals, at most one per terminal,
can be added at once: the wires they join merge, in the same way in both
wirings. -/
theorem JointWired.add_matching (hW₁ : Wiring L₁ T) (hW₂ : Wiring L₂ T)
    (h : JointWired L₁ L₂ T) (l : List V) :
    ∀ {M : V → V → Prop}, (∀ {p q}, M p q → M q p) → (∀ {p}, ¬ M p p) →
      (∀ {p q r}, M p q → M p r → q = r) → (∀ {p q}, M p q → T p) →
      (∀ {p q}, M p q → p ∈ l) →
      JointWired (fun p q => L₁ p q ∨ M p q) (fun p q => L₂ p q ∨ M p q)
        (fun p => T p ∧ ¬ ∃ q, M p q) := by
  induction l with
  | nil =>
    intro M hs hi hf hT hl
    have hM : ∀ {p q}, ¬ M p q := fun hpq => List.not_mem_nil (hl hpq)
    have hL : ∀ (L : V → V → Prop) (p q : V), L p q ↔ L p q ∨ M p q :=
      fun L p q => ⟨.inl, fun h' => h'.elim id (fun h'' => (hM h'').elim)⟩
    exact h.congr (hL L₁) (hL L₂)
      (fun p => ⟨fun hp => ⟨hp, fun ⟨q, hq⟩ => hM hq⟩, fun hp => hp.1⟩)
  | cons x₀ l ih =>
    intro M hs hi hf hT hl
    -- the segments that do not touch `x₀`
    have hs₀ : ∀ {p q}, (M p q ∧ p ≠ x₀ ∧ q ≠ x₀) → (M q p ∧ q ≠ x₀ ∧ p ≠ x₀) :=
      fun h => ⟨hs h.1, h.2.2, h.2.1⟩
    have hf₀ : ∀ {p q r}, (M p q ∧ p ≠ x₀ ∧ q ≠ x₀) → (M p r ∧ p ≠ x₀ ∧ r ≠ x₀) → q = r :=
      fun h h' => hf h.1 h'.1
    have hT₀ : ∀ {p q}, (M p q ∧ p ≠ x₀ ∧ q ≠ x₀) → T p := fun h => hT h.1
    have ih' := ih (M := fun p q => M p q ∧ p ≠ x₀ ∧ q ≠ x₀) hs₀ (fun h => hi h.1) hf₀ hT₀
      (fun h => (List.mem_cons.1 (hl h.1)).resolve_left h.2.1)
    have W₁ := hW₁.add (M := fun p q => M p q ∧ p ≠ x₀ ∧ q ≠ x₀) hs₀ hf₀ hT₀
    have W₂ := hW₂.add (M := fun p q => M p q ∧ p ≠ x₀ ∧ q ≠ x₀) hs₀ hf₀ hT₀
    by_cases hx : ∃ y₀, M x₀ y₀
    · obtain ⟨y₀, hxy⟩ := hx
      have hne : x₀ ≠ y₀ := by
        rintro rfl
        exact hi hxy
      have tx : T x₀ ∧ ¬ ∃ q, M x₀ q ∧ x₀ ≠ x₀ ∧ q ≠ x₀ :=
        ⟨hT hxy, fun ⟨q, hq⟩ => hq.2.1 rfl⟩
      have ty : T y₀ ∧ ¬ ∃ q, M y₀ q ∧ y₀ ≠ x₀ ∧ q ≠ x₀ :=
        ⟨hT (hs hxy), fun ⟨q, hq⟩ => hq.2.2 (hf hq.1 (hs hxy))⟩
      have hL : ∀ (L : V → V → Prop) (p q : V),
          ((L p q ∨ M p q ∧ p ≠ x₀ ∧ q ≠ x₀) ∨ (p = x₀ ∧ q = y₀) ∨ (p = y₀ ∧ q = x₀)) ↔
            (L p q ∨ M p q) := by
        intro L p q
        constructor
        · rintro ((h | ⟨h, -, -⟩) | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact .inl h
          · exact .inr h
          · exact .inr hxy
          · exact .inr (hs hxy)
        · rintro (h | h)
          · exact .inl (.inl h)
          · by_cases hp : p = x₀
            · subst hp
              exact .inr (.inl ⟨rfl, hf h hxy⟩)
            · by_cases hq : q = x₀
              · subst hq
                exact .inr (.inr ⟨hf (hs h) hxy, rfl⟩)
              · exact .inl (.inr ⟨h, hp, hq⟩)
      refine (ih'.splice W₁ W₂ tx ty hne).congr (hL L₁) (hL L₂) ?_
      intro p
      constructor
      · rintro ⟨⟨hp, hn⟩, hpx, hpy⟩
        refine ⟨hp, fun ⟨q, hq⟩ => ?_⟩
        by_cases hqx : q = x₀
        · subst hqx
          exact hpy (hf (hs hq) hxy)
        · exact hn ⟨q, hq, hpx, hqx⟩
      · rintro ⟨hp, hn⟩
        refine ⟨⟨hp, fun ⟨q, hq⟩ => hn ⟨q, hq.1⟩⟩, ?_, ?_⟩
        · rintro rfl
          exact hn ⟨y₀, hxy⟩
        · rintro rfl
          exact hn ⟨x₀, hs hxy⟩
    · have hM : ∀ {p q}, M p q → p ≠ x₀ ∧ q ≠ x₀ := by
        intro p q hpq
        constructor
        · rintro rfl
          exact hx ⟨q, hpq⟩
        · rintro rfl
          exact hx ⟨p, hs hpq⟩
      have hL : ∀ (L : V → V → Prop) (p q : V),
          (L p q ∨ M p q ∧ p ≠ x₀ ∧ q ≠ x₀) ↔ (L p q ∨ M p q) :=
        fun L p q => or_congr Iff.rfl ⟨fun h => h.1, fun h => ⟨h, hM h⟩⟩
      refine ih'.congr (hL L₁) (hL L₂) ?_
      intro p
      constructor
      · rintro ⟨hp, hn⟩
        exact ⟨hp, fun ⟨q, hq⟩ => hn ⟨q, hq, hM hq⟩⟩
      · rintro ⟨hp, hn⟩
        exact ⟨hp, fun ⟨q, hq⟩ => hn ⟨q, hq.1⟩⟩

/-- Fresh terminals `F` can be attached by new segments `K`, each new segment
running from a fresh terminal to a fresh terminal or to an old one, which is
thereby demoted. -/
theorem JointWired.attach (hsym₁ : ∀ {p q}, L₁ p q → L₁ q p) (hsym₂ : ∀ {p q}, L₂ p q → L₂ q p)
    (h : JointWired L₁ L₂ T) {K : V → V → Prop} {F : V → Prop}
    (hs : ∀ {p q}, K p q → K q p) (hi : ∀ {p}, ¬ K p p)
    (hf : ∀ {p q r}, K p q → K p r → q = r)
    (hKF : ∀ {p q}, K p q → F p ∨ F q) (hKT : ∀ {p q}, K p q → F p ∨ T p)
    (hFK : ∀ {p}, F p → ∃ q, K p q)
    (hFL₁ : ∀ {p q}, F p → ¬ L₁ p q) (hFL₂ : ∀ {p q}, F p → ¬ L₂ p q)
    (hFT : ∀ {p}, F p → ¬ T p) :
    JointWired (fun p q => L₁ p q ∨ K p q) (fun p q => L₂ p q ∨ K p q)
      (fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p) := by
  -- an old terminal that received a new segment is not a terminal any more
  have dem : ∀ {p q}, T p → K p q → ¬ ((T p ∧ ¬ ∃ q, K p q) ∨ F p) := by
    rintro p q hp hk (⟨-, hn⟩ | hF)
    · exact hn ⟨q, hk⟩
    · exact hFT hF hp
  -- the other extremity of a new segment leaving an old terminal is fresh
  have far : ∀ {p q}, T p → K p q → F q := fun hp hk =>
    (hKF hk).resolve_left (fun hF => hFT hF hp)
  -- the three ways in which an old wire shows up in a new one, for either wiring
  have mono : ∀ (L : V → V → Prop), (∀ {p q}, L p q → L q p) → (∀ {p q}, F p → ¬ L p q) →
      ∀ {a b c d : V}, Walk L T a b c d →
        Walk (fun p q => L p q ∨ K p q) (fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p) a b c d :=
    fun L hsym hFL _ _ _ _ w => w.mono (fun h => .inl h) (fun hl hq hq' =>
      hq'.elim (fun h' => hq h'.1) (fun hF => hFL hF (hsym hl)))
  have ext : ∀ (L : V → V → Prop), (∀ {p q}, L p q → L q p) → (∀ {p q}, F p → ¬ L p q) →
      ∀ {t t' q : V}, T t' → K t' q → Conn L T t t' →
        Conn (fun p q => L p q ∨ K p q) (fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p) t q := by
    rintro L hsym hFL t t' q ht' hq ⟨z, u, w⟩
    refine ⟨z, t', (mono L hsym hFL w).snoc (dem ht' hq) (.inr hq) ?_⟩
    rintro rfl
    exact hFL (far ht' hq) w.link_last
  have pre : ∀ (L : V → V → Prop), (∀ {p q}, L p q → L q p) → (∀ {p q}, F p → ¬ L p q) →
      ∀ {t x t'' : V}, F t → K t x → T x → Conn L T x t'' →
        ∃ u, Walk (fun p q => L p q ∨ K p q) (fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p) t x u t'' ∧
          L u t'' := by
    rintro L hsym hFL t x t'' hF hx hTx ⟨z, u, w⟩
    refine ⟨u, .cons (.inr hx) (dem hTx (hs hx)) ?_ (mono L hsym hFL w), w.link_last⟩
    rintro rfl
    exact hFL hF (hsym w.link_first)
  rintro t (⟨ht, hnk⟩ | hF)
  · obtain ⟨t', ht', hne, c₁, c₂⟩ := h t ht
    by_cases hk : ∃ q, K t' q
    · obtain ⟨q, hq⟩ := hk
      refine ⟨q, .inr (far ht' hq), ?_, ext L₁ hsym₁ hFL₁ ht' hq c₁, ext L₂ hsym₂ hFL₂ ht' hq c₂⟩
      rintro rfl
      exact hFT (far ht' hq) ht
    · obtain ⟨z, u, w⟩ := c₁
      obtain ⟨z', u', w'⟩ := c₂
      exact ⟨t', .inl ⟨ht', hk⟩, hne, ⟨z, u, mono L₁ hsym₁ hFL₁ w⟩, ⟨z', u', mono L₂ hsym₂ hFL₂ w'⟩⟩
  · obtain ⟨x, hx⟩ := hFK hF
    rcases hKT (hs hx) with hFx | hTx
    · refine ⟨x, .inr hFx, ?_, ⟨x, t, .single (.inr hx)⟩, ⟨x, t, .single (.inr hx)⟩⟩
      rintro rfl
      exact hi hx
    · obtain ⟨t'', ht'', hne, c₁, c₂⟩ := h x hTx
      obtain ⟨u₁, w₁, l₁⟩ := pre L₁ hsym₁ hFL₁ hF hx hTx c₁
      obtain ⟨u₂, w₂, l₂⟩ := pre L₂ hsym₂ hFL₂ hF hx hTx c₂
      by_cases hk : ∃ q, K t'' q
      · obtain ⟨q, hq⟩ := hk
        have hFq := far ht'' hq
        refine ⟨q, .inr hFq, ?_, ⟨x, t'', w₁.snoc (dem ht'' hq) (.inr hq) ?_⟩,
          ⟨x, t'', w₂.snoc (dem ht'' hq) (.inr hq) ?_⟩⟩
        · rintro rfl
          exact hne (hf (hs hq) hx)
        · rintro rfl
          exact hFL₁ hFq l₁
        · rintro rfl
          exact hFL₂ hFq l₂
      · refine ⟨t'', .inl ⟨ht'', hk⟩, ?_, ⟨x, u₁, w₁⟩, ⟨x, u₂, w₂⟩⟩
        rintro rfl
        exact hFT hF ht''

end Wires

/-! ## Tables of wires

A finite table that lists, for every terminal of a wiring, the terminal at
the other extremity of its wire.  The three operations on wirings used to
describe a firing are mirrored by three executable operations on tables. -/

section Tables

variable {V : Type u} {L L' : V → V → Prop} {T T' : V → Prop} {W : List (V × V)}

/-- Look a key up in a list of pairs. -/
def assoc {α : Type u} {β : Type v} [DecidableEq α] (p : α) : List (α × β) → Option β
  | [] => none
  | (k, v) :: l => if k = p then some v else assoc p l

theorem assoc_mem {α : Type u} {β : Type v} [DecidableEq α] {p : α} {q : β}
    {l : List (α × β)} (h : assoc p l = some q) : (p, q) ∈ l := by
  induction l with
  | nil => cases h
  | cons e l ih =>
    obtain ⟨k, v⟩ := e
    simp only [assoc] at h
    split at h
    · rename_i hk
      subst hk
      cases h
      exact List.mem_cons.2 (.inl rfl)
    · exact List.mem_cons.2 (.inr (ih h))

theorem assoc_of_mem {α : Type u} {β : Type v} [DecidableEq α] {p : α} {q : β}
    {l : List (α × β)} (h : (p, q) ∈ l) : ∃ q', assoc p l = some q' := by
  induction l with
  | nil => cases h
  | cons e l ih =>
    obtain ⟨k, v⟩ := e
    simp only [assoc]
    split
    · exact ⟨v, rfl⟩
    · rename_i hk
      rcases List.mem_cons.1 h with e | h'
      · exact absurd (Prod.mk.inj e).1.symm hk
      · exact ih h'

/-- `W` lists every terminal together with the other extremity of its wire,
and nothing else. -/
structure Exact (W : List (V × V)) (L : V → V → Prop) (T : V → Prop) : Prop where
  sound : ∀ {p q}, (p, q) ∈ W → T p ∧ T q ∧ p ≠ q ∧ Conn L T p q
  total : ∀ {p}, T p → ∃ q, (p, q) ∈ W

namespace Exact

theorem det (h : Exact W L T) (hW : Wiring L T) {p q q' : V}
    (h₁ : (p, q) ∈ W) (h₂ : (p, q') ∈ W) : q = q' :=
  Conn.det hW (h.sound h₁).1 (h.sound h₁).2.1 (h.sound h₂).2.1
    (h.sound h₁).2.2.2 (h.sound h₂).2.2.2

theorem symm (h : Exact W L T) (hW : Wiring L T) {p q : V} (h₁ : (p, q) ∈ W) : (q, p) ∈ W := by
  obtain ⟨hp, hq, -, c⟩ := h.sound h₁
  obtain ⟨p', h₂⟩ := h.total hq
  have e : p' = p := Conn.det hW hq (h.sound h₂).2.1 hp (h.sound h₂).2.2.2 (c.symm hW)
  exact e ▸ h₂

/-- The table is the pairing of terminals by wires. -/
theorem mem_iff (h : Exact W L T) (hW : Wiring L T) {p q : V} :
    (p, q) ∈ W ↔ T p ∧ T q ∧ Conn L T p q := by
  constructor
  · intro hm
    exact ⟨(h.sound hm).1, (h.sound hm).2.1, (h.sound hm).2.2.2⟩
  · rintro ⟨hp, hq, c⟩
    obtain ⟨q', hm⟩ := h.total hp
    rw [Conn.det hW hp hq (h.sound hm).2.1 c (h.sound hm).2.2.2]
    exact hm

/-- Looking a terminal up in the table gives its partner. -/
theorem assoc_eq [DecidableEq V] (h : Exact W L T) (hW : Wiring L T) {p q : V}
    (hm : (p, q) ∈ W) : assoc p W = some q := by
  obtain ⟨q', e⟩ := assoc_of_mem hm
  rw [e, h.det hW hm (assoc_mem e)]

theorem congr (hL : ∀ p q, L p q ↔ L' p q) (hT : ∀ p, T p ↔ T' p) (h : Exact W L T) :
    Exact W L' T' := by
  have e₁ : L = L' := funext fun p => funext fun q => propext (hL p q)
  have e₂ : T = T' := funext fun p => propext (hT p)
  subst e₁ e₂
  exact h

theorem congr_mem {W' : List (V × V)} (hm : ∀ e, e ∈ W' ↔ e ∈ W) (h : Exact W L T) :
    Exact W' L T :=
  ⟨fun hpq => h.sound ((hm _).1 hpq), fun hp => by
    obtain ⟨q, hq⟩ := h.total hp
    exact ⟨q, (hm _).2 hq⟩⟩

end Exact

/-- Drop the entries of two terminals. -/
def retireTable [DecidableEq V] (W : List (V × V)) (u v : V) : List (V × V) :=
  W.filter fun e => decide (e.1 ≠ u ∧ e.1 ≠ v)

theorem Exact.retire [DecidableEq V] (hW : Wiring L T) (h : Exact W L T) {u v : V}
    (hu : T u) (hv : T v) (huv : Conn L T u v) :
    Exact (retireTable W u v) L (fun p => T p ∧ p ≠ u ∧ p ≠ v) := by
  constructor
  · intro p q hm
    obtain ⟨hm, hk⟩ := List.mem_filter.1 hm
    have hk : p ≠ u ∧ p ≠ v := of_decide_eq_true hk
    obtain ⟨hp, hq, hne, c⟩ := h.sound hm
    have h₁ : q ≠ u := by
      rintro rfl
      exact hk.2 (Conn.det hW hq hp hv (c.symm hW) huv)
    have h₂ : q ≠ v := by
      rintro rfl
      exact hk.1 (Conn.det hW hq hp hu (c.symm hW) (huv.symm hW))
    obtain ⟨z, x, w⟩ := c
    exact ⟨⟨hp, hk⟩, ⟨hq, h₁, h₂⟩, hne, z, x, w.mono (fun h => h) (fun _ hq hq' => hq hq'.1)⟩
  · rintro p ⟨hp, hk⟩
    obtain ⟨q, hm⟩ := h.total hp
    exact ⟨q, List.mem_filter.2 ⟨hm, decide_eq_true hk⟩⟩

theorem Wiring.congr (hL : ∀ p q, L p q ↔ L' p q) (hT : ∀ p, T p ↔ T' p) (h : Wiring L T) :
    Wiring L' T' := by
  have e₁ : L = L' := funext fun p => funext fun q => propext (hL p q)
  have e₂ : T = T' := funext fun p => propext (hT p)
  subst e₁ e₂
  exact h

theorem Wiring.splice (hW : Wiring L T) {x y : V} (hx : T x) (hy : T y) :
    Wiring (fun p q => L p q ∨ (p = x ∧ q = y) ∨ (p = y ∧ q = x))
      (fun p => T p ∧ p ≠ x ∧ p ≠ y) := by
  have h := hW.add (M := fun p q => (p = x ∧ q = y) ∨ (p = y ∧ q = x))
    (by
      rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl ⟨rfl, rfl⟩)
    (by
      rintro p q r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨e, rfl⟩ | ⟨e, rfl⟩)
      · rfl
      · exact e.symm
      · exact e.symm
      · rfl)
    (by
      rintro p q (⟨rfl, -⟩ | ⟨rfl, -⟩)
      · exact hx
      · exact hy)
  refine h.congr (fun _ _ => Iff.rfl) (fun p => and_congr Iff.rfl ⟨?_, ?_⟩)
  · intro hn
    exact ⟨fun e => hn ⟨y, .inl ⟨e, rfl⟩⟩, fun e => hn ⟨x, .inr ⟨e, rfl⟩⟩⟩
  · rintro ⟨h₁, h₂⟩ ⟨q, ⟨e, -⟩ | ⟨e, -⟩⟩
    · exact h₁ e
    · exact h₂ e

/-- Where a wire that used to stop at `x` or at `y` stops once `x` and `y`
are joined. -/
def redirect [DecidableEq V] (W : List (V × V)) (x y q : V) : V :=
  if q = x then (assoc y W).getD y else if q = y then (assoc x W).getD x else q

theorem redirect_left [DecidableEq V] (W : List (V × V)) (x y : V) :
    redirect W x y x = (assoc y W).getD y := by
  simp [redirect]

theorem redirect_right [DecidableEq V] (W : List (V × V)) {x y : V} (h : y ≠ x) :
    redirect W x y y = (assoc x W).getD x := by
  simp [redirect, h]

theorem redirect_other [DecidableEq V] (W : List (V × V)) {x y q : V} (hx : q ≠ x) (hy : q ≠ y) :
    redirect W x y q = q := by
  simp [redirect, hx, hy]

/-- Join the terminals `x` and `y`: their entries go, and the wires that
stopped there are redirected. -/
def spliceTable [DecidableEq V] (W : List (V × V)) (x y : V) : List (V × V) :=
  W.filterMap fun e => if e.1 = x ∨ e.1 = y then none else some (e.1, redirect W x y e.2)

theorem Exact.splice [DecidableEq V] (hW : Wiring L T) (h : Exact W L T) {x y : V}
    (hx : T x) (hy : T y) (hxy : x ≠ y)
    (hL : ∀ {p q}, L p q → L' p q) (hl : L' x y) (hl' : L' y x)
    (hT : ∀ {p}, T' p ↔ T p ∧ p ≠ x ∧ p ≠ y) : Exact (spliceTable W x y) L' T' := by
  obtain ⟨tx, hmx⟩ := h.total hx
  obtain ⟨ty, hmy⟩ := h.total hy
  have ex : (assoc x W).getD x = tx := by rw [h.assoc_eq hW hmx]; rfl
  have ey : (assoc y W).getD y = ty := by rw [h.assoc_eq hW hmy]; rfl
  have hx' : ¬ T' x := fun h' => (hT.1 h').2.1 rfl
  have hy' : ¬ T' y := fun h' => (hT.1 h').2.2 rfl
  have hT₁ : ∀ {p}, T' p → T p := fun h' => (hT.1 h').1
  -- a wire that stopped at `x` now runs on to the partner of `y`
  have key : ∀ {x y ty p : V}, T x → T y → x ≠ y → L' x y → ¬ T' x → ¬ T' y →
      (∀ {p}, T p → p ≠ x → p ≠ y → T' p) → (y, ty) ∈ W → (p, x) ∈ W → p ≠ y →
      T' ty ∧ p ≠ ty ∧ Conn L' T' p ty := by
    intro x y ty p hx hy hxy hl hx' hy' hT₂ hmy hmp hpy
    obtain ⟨-, hty, hne, cy⟩ := h.sound hmy
    obtain ⟨-, -, -, cp⟩ := h.sound hmp
    have h₁ : ty ≠ x := by
      rintro rfl
      exact hpy (h.det hW (h.symm hW hmp) (h.symm hW hmy))
    have h₂ : p ≠ ty := by
      rintro rfl
      exact hxy (h.det hW hmp (h.symm hW hmy))
    obtain ⟨z, u, w⟩ := cp
    obtain ⟨z₂, u₂, w₂⟩ := cy
    exact ⟨hT₂ hty h₁ hne.symm, h₂, Walk.splice hW hx hy hL hT₁ hx' hy' hl hpy w w₂⟩
  constructor
  · intro p q' hm
    obtain ⟨⟨p₀, q⟩, hm₀, he⟩ := List.mem_filterMap.1 hm
    dsimp only at he
    split at he
    · cases he
    · rename_i hk
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      have hpx : p₀ ≠ x := fun e => hk (.inl e)
      have hpy : p₀ ≠ y := fun e => hk (.inr e)
      obtain ⟨hp, hq, hne, c⟩ := h.sound hm₀
      have hp' : T' p₀ := hT.2 ⟨hp, hpx, hpy⟩
      by_cases hqx : q = x
      · subst hqx
        rw [redirect_left, ey]
        obtain ⟨h₁, h₂, h₃⟩ :=
          key hx hy hxy hl hx' hy' (fun a b c => hT.2 ⟨a, b, c⟩) hmy hm₀ hpy
        exact ⟨hp', h₁, h₂, h₃⟩
      · by_cases hqy : q = y
        · subst hqy
          rw [redirect_right W hxy.symm, ex]
          obtain ⟨h₁, h₂, h₃⟩ :=
            key hy hx hxy.symm hl' hy' hx' (fun a b c => hT.2 ⟨a, c, b⟩) hmx hm₀ hpx
          exact ⟨hp', h₁, h₂, h₃⟩
        · rw [redirect_other W hqx hqy]
          obtain ⟨z, u, w⟩ := c
          exact ⟨hp', hT.2 ⟨hq, hqx, hqy⟩, hne, z, u,
            w.mono hL (fun _ hq hq' => hq (hT₁ hq'))⟩
  · intro p hp
    obtain ⟨hp₀, hpx, hpy⟩ := hT.1 hp
    obtain ⟨q, hm⟩ := h.total hp₀
    refine ⟨redirect W x y q, List.mem_filterMap.2 ⟨(p, q), hm, ?_⟩⟩
    simp [hpx, hpy]

/-- Join a list of pairs of terminals, one pair after the other. -/
def spliceAll [DecidableEq V] (W : List (V × V)) : List (V × V) → List (V × V)
  | [] => W
  | (x, y) :: ps => spliceAll (spliceTable W x y) ps

/-- Joining a pair whose members are not terminals does nothing. -/
theorem Exact.spliceTable_mem [DecidableEq V] (h : Exact W L T) {x y : V}
    (hx : ¬ T x) (hy : ¬ T y) (e : V × V) : e ∈ spliceTable W x y ↔ e ∈ W := by
  have keep : ∀ {p q : V}, (p, q) ∈ W →
      (if p = x ∨ p = y then none else some (p, redirect W x y q)) = some (p, q) := by
    intro p q hm
    obtain ⟨hp, hq, -, -⟩ := h.sound hm
    have hpx : p ≠ x := fun e => hx (e ▸ hp)
    have hpy : p ≠ y := fun e => hy (e ▸ hp)
    have hqx : q ≠ x := fun e => hx (e ▸ hq)
    have hqy : q ≠ y := fun e => hy (e ▸ hq)
    simp [hpx, hpy, redirect_other W hqx hqy]
  constructor
  · intro hm
    obtain ⟨⟨p, q⟩, hm₀, he⟩ := List.mem_filterMap.1 hm
    dsimp only at he
    rw [keep hm₀] at he
    cases he
    exact hm₀
  · intro hm
    obtain ⟨p, q⟩ := e
    exact List.mem_filterMap.2 ⟨(p, q), hm, keep hm⟩

/-- Joining the pairs of a matching `M`, in any order and with repetitions:
the table follows the wiring. -/
theorem Exact.spliceAll [DecidableEq V] {M : V → V → Prop}
    (hs : ∀ {p q}, M p q → M q p) (hi : ∀ {p}, ¬ M p p)
    (hf : ∀ {p q r}, M p q → M p r → q = r) (ps : List (V × V)) :
    (∀ e ∈ ps, M e.1 e.2) →
    ∀ {W : List (V × V)} {L : V → V → Prop} {T : V → Prop}, Wiring L T → Exact W L T →
      (∀ {x y}, M x y → (T x ∧ T y) ∨ (L x y ∧ ¬ T x ∧ ¬ T y)) →
      Exact (INet.spliceAll W ps) (fun p q => L p q ∨ (p, q) ∈ ps ∨ (q, p) ∈ ps)
        (fun p => T p ∧ ∀ e ∈ ps, p ≠ e.1 ∧ p ≠ e.2) := by
  induction ps with
  | nil =>
    intro _ W L T _ h _
    exact h.congr
      (fun p q => ⟨.inl, fun h' => h'.elim id (fun h'' =>
        h''.elim (fun m => absurd m List.not_mem_nil) (fun m => absurd m List.not_mem_nil))⟩)
      (fun p => ⟨fun hp => ⟨hp, fun e he => absurd he List.not_mem_nil⟩, fun hp => hp.1⟩)
  | cons e ps ih =>
    obtain ⟨x, y⟩ := e
    intro hps W L T hW h hInv
    have hM : M x y := hps (x, y) (List.mem_cons.2 (.inl rfl))
    have hps' : ∀ e ∈ ps, M e.1 e.2 := fun e he => hps e (List.mem_cons.2 (.inr he))
    rcases hInv hM with ⟨hx, hy⟩ | ⟨hl, hx, hy⟩
    · -- the pair is still pending: join it
      have hxy : x ≠ y := by
        rintro rfl
        exact hi hM
      have h₁ := h.splice (L' := fun p q => L p q ∨ (p = x ∧ q = y) ∨ (p = y ∧ q = x))
        (T' := fun p => T p ∧ p ≠ x ∧ p ≠ y) hW hx hy hxy (fun h => .inl h)
        (.inr (.inl ⟨rfl, rfl⟩)) (.inr (.inr ⟨rfl, rfl⟩)) Iff.rfl
      have W₁ := hW.splice hx hy
      have hInv₁ : ∀ {u v : V}, M u v →
          ((T u ∧ u ≠ x ∧ u ≠ y) ∧ (T v ∧ v ≠ x ∧ v ≠ y)) ∨
            ((L u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∧
              ¬ (T u ∧ u ≠ x ∧ u ≠ y) ∧ ¬ (T v ∧ v ≠ x ∧ v ≠ y)) := by
        intro u v huv
        by_cases hux : u = x
        · subst hux
          obtain rfl := hf huv hM
          exact .inr ⟨.inr (.inl ⟨rfl, rfl⟩), fun h => h.2.1 rfl, fun h => h.2.2 rfl⟩
        by_cases huy : u = y
        · subst huy
          obtain rfl := hf huv (hs hM)
          exact .inr ⟨.inr (.inr ⟨rfl, rfl⟩), fun h => h.2.2 rfl, fun h => h.2.1 rfl⟩
        have hvx : v ≠ x := by
          rintro rfl
          exact huy (hf (hs huv) hM)
        have hvy : v ≠ y := by
          rintro rfl
          exact hux (hf (hs huv) (hs hM))
        rcases hInv huv with ⟨hu, hv⟩ | ⟨hl, hu, hv⟩
        · exact .inl ⟨⟨hu, hux, huy⟩, ⟨hv, hvx, hvy⟩⟩
        · exact .inr ⟨.inl hl, fun h => hu h.1, fun h => hv h.1⟩
      refine (ih hps' W₁ h₁ hInv₁).congr (fun p q => ?_) (fun p => ?_)
      · constructor
        · rintro ((hl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hm | hm)
          · exact .inl hl
          · exact .inr (.inl (List.mem_cons.2 (.inl rfl)))
          · exact .inr (.inr (List.mem_cons.2 (.inl rfl)))
          · exact .inr (.inl (List.mem_cons.2 (.inr hm)))
          · exact .inr (.inr (List.mem_cons.2 (.inr hm)))
        · rintro (hl | hm | hm)
          · exact .inl (.inl hl)
          · rcases List.mem_cons.1 hm with e | hm
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
              exact .inl (.inr (.inl ⟨rfl, rfl⟩))
            · exact .inr (.inl hm)
          · rcases List.mem_cons.1 hm with e | hm
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
              exact .inl (.inr (.inr ⟨rfl, rfl⟩))
            · exact .inr (.inr hm)
      · constructor
        · rintro ⟨⟨hp, hpx, hpy⟩, hall⟩
          refine ⟨hp, fun e he => ?_⟩
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨hpx, hpy⟩
          · exact hall e he
        · rintro ⟨hp, hall⟩
          exact ⟨⟨hp, hall (x, y) (List.mem_cons.2 (.inl rfl))⟩,
            fun e he => hall e (List.mem_cons.2 (.inr he))⟩
    · -- the pair has been joined already
      refine (ih hps' hW (h.congr_mem (h.spliceTable_mem hx hy)) hInv).congr
        (fun p q => ?_) (fun p => ?_)
      · constructor
        · rintro (hl | hm | hm)
          · exact .inl hl
          · exact .inr (.inl (List.mem_cons.2 (.inr hm)))
          · exact .inr (.inr (List.mem_cons.2 (.inr hm)))
        · rintro (hl' | hm | hm)
          · exact .inl hl'
          · rcases List.mem_cons.1 hm with e | hm
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
              exact .inl hl
            · exact .inr (.inl hm)
          · rcases List.mem_cons.1 hm with e | hm
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
              exact .inl (hW.symm hl)
            · exact .inr (.inr hm)
      · constructor
        · rintro ⟨hp, hall⟩
          refine ⟨hp, fun e he => ?_⟩
          rcases List.mem_cons.1 he with rfl | he
          · constructor
            · rintro rfl
              exact hx hp
            · rintro rfl
              exact hy hp
          · exact hall e he
        · rintro ⟨hp, hall⟩
          exact ⟨hp, fun e he => hall e (List.mem_cons.2 (.inr he))⟩

/-- Attach fresh terminals: every old wire keeps its table entry, with each
extremity that received a new segment replaced by the fresh terminal at the
other end of that segment (`e`), and the new segments between two fresh
terminals (`Fp`) are added. -/
theorem Exact.attach (hsym : ∀ {p q}, L p q → L q p) (h : Exact W L T)
    {K : V → V → Prop} {F : V → Prop}
    (hs : ∀ {p q}, K p q → K q p) (hi : ∀ {p}, ¬ K p p)
    (hf : ∀ {p q r}, K p q → K p r → q = r)
    (hKF : ∀ {p q}, K p q → F p ∨ F q) (hKT : ∀ {p q}, K p q → F p ∨ T p)
    (hFK : ∀ {p}, F p → ∃ q, K p q)
    (hFL : ∀ {p q}, F p → ¬ L p q) (hFT : ∀ {p}, F p → ¬ T p)
    (e : V → V) (he : ∀ {p f}, T p → K p f → e p = f)
    (he' : ∀ {p}, T p → (¬ ∃ f, K p f) → e p = p)
    (Fp : List (V × V)) (hFp : ∀ {f g}, (f, g) ∈ Fp ↔ F f ∧ F g ∧ K f g) :
    Exact (W.map (fun w => (e w.1, e w.2)) ++ Fp) (fun p q => L p q ∨ K p q)
      (fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p) := by
  have dem : ∀ {p q}, T p → K p q → ¬ ((T p ∧ ¬ ∃ q, K p q) ∨ F p) := by
    rintro p q hp hk (⟨-, hn⟩ | hF)
    · exact hn ⟨q, hk⟩
    · exact hFT hF hp
  have far : ∀ {p q}, T p → K p q → F q := fun hp hk =>
    (hKF hk).resolve_left (fun hF => hFT hF hp)
  have mono : ∀ {a b c d : V}, Walk L T a b c d →
      Walk (fun p q => L p q ∨ K p q) (fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p) a b c d :=
    fun w => w.mono (fun h => .inl h) (fun hl hq hq' =>
      hq'.elim (fun h' => hq h'.1) (fun hF => hFL hF (hsym hl)))
  -- the image of an old wire `p — q`
  have image : ∀ {p q : V}, T p → T q → p ≠ q → Conn L T p q →
      ((T (e p) ∧ ¬ ∃ r, K (e p) r) ∨ F (e p)) ∧ ((T (e q) ∧ ¬ ∃ r, K (e q) r) ∨ F (e q)) ∧
        e p ≠ e q ∧
        Conn (fun p q => L p q ∨ K p q) (fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p) (e p) (e q) := by
    rintro p q hp hq hne ⟨z, u, w⟩
    by_cases hkp : ∃ f, K p f
    · obtain ⟨f, hpf⟩ := hkp
      have hFf := far hp hpf
      rw [he hp hpf]
      have hz : z ≠ f := by
        rintro rfl
        exact hFL hFf (hsym w.link_first)
      have w' := Walk.cons (T := fun p => (T p ∧ ¬ ∃ q, K p q) ∨ F p)
        (.inr (hs hpf)) (dem hp hpf) hz (mono w)
      by_cases hkq : ∃ g, K q g
      · obtain ⟨g, hqg⟩ := hkq
        have hFg := far hq hqg
        rw [he hq hqg]
        refine ⟨.inr hFf, .inr hFg, ?_, p, q, w'.snoc (dem hq hqg) (.inr hqg) ?_⟩
        · rintro rfl
          exact hne (hf (hs hpf) (hs hqg))
        · rintro rfl
          exact hFL hFg w.link_last
      · rw [he' hq hkq]
        refine ⟨.inr hFf, .inl ⟨hq, hkq⟩, ?_, p, u, w'⟩
        rintro rfl
        exact hFT hFf hq
    · rw [he' hp hkp]
      by_cases hkq : ∃ g, K q g
      · obtain ⟨g, hqg⟩ := hkq
        have hFg := far hq hqg
        rw [he hq hqg]
        refine ⟨.inl ⟨hp, hkp⟩, .inr hFg, ?_, z, q, (mono w).snoc (dem hq hqg) (.inr hqg) ?_⟩
        · rintro rfl
          exact hFT hFg hp
        · rintro rfl
          exact hFL hFg w.link_last
      · rw [he' hq hkq]
        exact ⟨.inl ⟨hp, hkp⟩, .inl ⟨hq, hkq⟩, hne, z, u, mono w⟩
  constructor
  · intro p' q' hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨⟨p, q⟩, hm₀, he₀⟩ := List.mem_map.1 hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he₀
      obtain ⟨hp, hq, hne, c⟩ := h.sound hm₀
      exact image hp hq hne c
    · obtain ⟨hFp', hFq', hk⟩ := hFp.1 hm
      refine ⟨.inr hFp', .inr hFq', ?_, q', p', .single (.inr hk)⟩
      rintro rfl
      exact hi hk
  · rintro t (⟨ht, hnk⟩ | hF)
    · obtain ⟨q, hm⟩ := h.total ht
      refine ⟨e q, List.mem_append.2 (.inl (List.mem_map.2 ⟨(t, q), hm, ?_⟩))⟩
      rw [he' ht hnk]
    · obtain ⟨x, hx⟩ := hFK hF
      rcases hKT (hs hx) with hFx | hTx
      · exact ⟨x, List.mem_append.2 (.inr (hFp.2 ⟨hF, hFx, hx⟩))⟩
      · obtain ⟨q, hm⟩ := h.total hTx
        refine ⟨e q, List.mem_append.2 (.inl (List.mem_map.2 ⟨(x, q), hm, ?_⟩))⟩
        rw [he hTx (hs hx)]

end Tables

end INet
