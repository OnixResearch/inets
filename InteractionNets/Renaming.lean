import InteractionNets.Confluence

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ## Renaming

The names of the agents are arbitrary.  A *renaming* of a net is a map of
identifiers that keeps the identifiers in use apart and keeps the names
reserved for future agents out of use.  Firing does not commute with a
renaming as it stands: the name of a new agent owned by neither side depends
on the order of the names of the two fired agents, and a renaming need not
respect that order.  It commutes with it up to an extension of the renaming
to the new agents (`rechild`).  So a reduction of a renamed net is the
renaming of a reduction, step by step, and normal forms do not depend on
names. -/

section Rename

section WalkImage

variable {V : Type u} {V' : Type v} {L : V → V → Prop} {T : V → Prop}
  {L' : V' → V' → Prop} {T' : V' → Prop}

/-- A walk is carried along a map of points that preserves segments, keeps
the points of the walk apart, and makes no terminal out of a junction. -/
theorem Walk.image (g : V → V') (hL : ∀ {p q}, L p q → L' (g p) (g q))
    (hT : ∀ {p q}, L p q → ¬ T p → ¬ T' (g p))
    (hne : ∀ {p q r}, L p q → L q r → r ≠ p → g r ≠ g p)
    {u v x y : V} (w : Walk L T u v x y) : Walk L' T' (g u) (g v) (g x) (g y) := by
  induction w with
  | single h => exact .single (hL h)
  | cons h hv hw w ih => exact .cons (hL h) (hT w.link_first hv) (hne h w.link_first hw) ih

end WalkImage

/-- Rename a port. -/
def mapPort (f : Id → Id) (p : Port) : Port := (f p.1, p.2)

/-- The image of a net under a renaming of identifiers. -/
def Net.map (f : Id → Id) (N : Net S) : Net S where
  agent i γ := ∃ i', i = f i' ∧ N.agent i' γ
  link p q := ∃ p' q', p = mapPort f p' ∧ q = mapPort f q' ∧ N.link p' q'
  free p := ∃ p', p = mapPort f p' ∧ N.free p'

/-- `f` is a *renaming* of the net `N`: it keeps the identifiers in use
apart, and it keeps the names reserved for the descendants of a live agent
out of use. -/
structure Renaming (f : Id → Id) (N : Net S) : Prop where
  inj : ∀ {i j}, N.Used i → N.Used j → f i = f j → i = j
  fresh : ∀ {a α i} (l : List Nat), N.agent a α → N.Used i → f i = l ++ f a → l = []

theorem Net.End.used {ar : S → Nat} {N : Net S} {p : Port} (h : N.End ar p) : N.Used p.1 := by
  rcases h with hf | ⟨γ, hg, -⟩
  · exact .inr (.inr ⟨p.2, hf⟩)
  · exact .inl ⟨γ, hg⟩

theorem Net.used_link {N : Net S} {p q : Port} (h : N.link p q) : N.Used p.1 :=
  .inr (.inl ⟨p.2, q, h⟩)

theorem Net.used_map {f : Id → Id} {N : Net S} {j : Id} (h : (N.map f).Used j) :
    ∃ i, j = f i ∧ N.Used i := by
  rcases h with ⟨γ, i, rfl, hg⟩ | ⟨k, q, p', q', e, -, hl⟩ | ⟨k, p', e, hfr⟩
  · exact ⟨i, rfl, .inl ⟨γ, hg⟩⟩
  · exact ⟨p'.1, (Prod.mk.inj e).1, Net.used_link hl⟩
  · exact ⟨p'.1, (Prod.mk.inj e).1, .inr (.inr ⟨p'.2, hfr⟩)⟩

theorem Net.end_map {ar : S → Nat} {f : Id → Id} {N : Net S} {p : Port} (h : N.End ar p) :
    (N.map f).End ar (mapPort f p) := by
  rcases h with hfr | ⟨γ, hg, hk⟩
  · exact .inl ⟨p, rfl, hfr⟩
  · exact .inr ⟨γ, ⟨p.1, rfl, hg⟩, hk⟩

theorem Net.end_of_map {ar : S → Nat} {f : Id → Id} {N : Net S} {q : Port}
    (h : (N.map f).End ar q) : ∃ p, q = mapPort f p ∧ N.End ar p := by
  rcases h with ⟨p, rfl, hfr⟩ | ⟨γ, ⟨i, e, hg⟩, hk⟩
  · exact ⟨p, rfl, .inl hfr⟩
  · exact ⟨(i, q.2), Prod.ext e rfl, .inr ⟨γ, hg, hk⟩⟩

variable {N' M M' : Net S} {f : Id → Id}

namespace Renaming

variable {ar : S → Nat}

theorem port_inj (hf : Renaming f N) {p q : Port} (hp : N.Used p.1) (hq : N.Used q.1)
    (e : mapPort f p = mapPort f q) : p = q := by
  have e' : (f p.1, p.2) = (f q.1, q.2) := e
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj e'
  exact Prod.ext (hf.inj hp hq e₁) e₂

/-- A used port is an end of the renamed net exactly when it was an end. -/
theorem end_iff (hf : Renaming f N) {p : Port} (hp : N.Used p.1) :
    (N.map f).End ar (mapPort f p) ↔ N.End ar p := by
  constructor
  · intro h
    obtain ⟨p', e, hE⟩ := Net.end_of_map h
    rw [hf.port_inj hp hE.used e]
    exact hE
  · exact Net.end_map

theorem walk_map (hf : Renaming f N) (hs : ∀ {p q}, N.link p q → N.link q p) {u v x y : Port}
    (w : Walk N.link (N.End ar) u v x y) :
    Walk (N.map f).link ((N.map f).End ar) (mapPort f u) (mapPort f v) (mapPort f x)
      (mapPort f y) := by
  have hL : ∀ {p q : Port}, N.link p q → (N.map f).link (mapPort f p) (mapPort f q) :=
    fun {p q} h => ⟨p, q, rfl, rfl, h⟩
  have hT : ∀ {p q : Port}, N.link p q → ¬ N.End ar p → ¬ (N.map f).End ar (mapPort f p) :=
    fun h hT hE => hT ((hf.end_iff (Net.used_link h)).1 hE)
  have hne : ∀ {p q r : Port}, N.link p q → N.link q r → r ≠ p → mapPort f r ≠ mapPort f p :=
    fun h h' hne e => hne (hf.port_inj (Net.used_link (hs h')) (Net.used_link h) e)
  exact w.image (mapPort f) hL hT hne

/-- Wires are carried along a renaming. -/
theorem conn_map (hf : Renaming f N) (hs : ∀ {p q}, N.link p q → N.link q p) {p q : Port}
    (h : N.Conn ar p q) : (N.map f).Conn ar (mapPort f p) (mapPort f q) := by
  obtain ⟨v, x, w⟩ := h
  exact ⟨_, _, hf.walk_map hs w⟩

/-- **A renamed net is well formed.** -/
theorem wf_map (hf : Renaming f N) (hN : N.WF ar) : (N.map f).WF ar where
  agent_fun := by
    rintro i α β ⟨i₁, rfl, h₁⟩ ⟨i₂, e, h₂⟩
    obtain rfl := hf.inj (.inl ⟨_, h₁⟩) (.inl ⟨_, h₂⟩) e
    exact hN.agent_fun h₁ h₂
  symm := by
    rintro p q ⟨p', q', rfl, rfl, hl⟩
    exact ⟨q', p', rfl, rfl, hN.symm hl⟩
  irrefl := by
    rintro p ⟨p', q', rfl, e, hl⟩
    obtain rfl := hf.port_inj (Net.used_link hl) (Net.used_link (hN.symm hl)) e
    exact hN.irrefl hl
  end_unique := by
    rintro p q r hE ⟨p₁, q₁, rfl, rfl, h₁⟩ ⟨p₂, r₂, e, rfl, h₂⟩
    obtain rfl := hf.port_inj (Net.used_link h₁) (Net.used_link h₂) e
    rw [hN.end_unique ((hf.end_iff (Net.used_link h₁)).1 hE) h₁ h₂]
  end_conn := by
    intro p hE
    obtain ⟨p', rfl, hE'⟩ := Net.end_of_map hE
    obtain ⟨q', hq', hne, hc⟩ := hN.end_conn hE'
    exact ⟨mapPort f q', Net.end_map hq', fun e => hne (hf.port_inj hq'.used hE'.used e),
      hf.conn_map hN.symm hc⟩
  deg := by
    rintro p x y z ⟨p₁, x₁, rfl, rfl, h₁⟩ ⟨p₂, y₂, e₂, rfl, h₂⟩ ⟨p₃, z₃, e₃, rfl, h₃⟩
    obtain rfl := hf.port_inj (Net.used_link h₁) (Net.used_link h₂) e₂
    obtain rfl := hf.port_inj (Net.used_link h₁) (Net.used_link h₃) e₃
    rcases hN.deg h₁ h₂ h₃ with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
  free_agent := by
    rintro i k α ⟨p', e, hfr⟩ ⟨i', rfl, hg⟩
    have e' : (f i', k) = (f p'.1, p'.2) := e
    have hu : N.Used p'.1 := .inr (.inr ⟨p'.2, hfr⟩)
    have ei := hf.inj (.inl ⟨α, hg⟩) hu (Prod.mk.inj e').1
    exact hN.free_agent (i := p'.1) (k := p'.2) hfr (ei ▸ hg)
  fresh := by
    rintro a α l ⟨a', rfl, hg⟩ hu
    obtain ⟨i, e, hi⟩ := Net.used_map hu
    exact hf.fresh l hg hi e.symm

/-- A firing site is carried along a renaming. -/
theorem site_map (hf : Renaming f N) {a b : Id} {α β : S} (h : Site ar N a b α β) :
    Site ar (N.map f) (f a) (f b) α β where
  wf := hf.wf_map h.wf
  ha := ⟨a, rfl, h.ha⟩
  hb := ⟨b, rfl, h.hb⟩
  ne := fun e => h.ne (hf.inj (.inl ⟨_, h.ha⟩) (.inl ⟨_, h.hb⟩) e)
  conn := hf.conn_map h.wf.symm h.conn

end Renaming

/-- Extend a renaming to the agents created when `a` and `b` fire: the new
agent in slot `n` of a fired agent goes to the same slot of its image, or,
for the slots of agents owned by neither side, to that slot of whichever
image comes first. -/
def rechild (f : Id → Id) (a b : Id) : Id → Id
  | [] => f []
  | n :: t =>
    if t = a ∨ t = b then
      if n % 2 = 0 then n :: f t else n :: pick (f a) (f b)
    else f (n :: t)

theorem rechild_child (f : Id → Id) (a b : Id) (o : Option Bool) (j : Nat) :
    rechild f a b (child a b o j) = child (f a) (f b) o j := by
  have h : par a b o = a ∨ par a b o = b := par_eq a b o
  show (if par a b o = a ∨ par a b o = b then
      if slot o j % 2 = 0 then slot o j :: f (par a b o) else slot o j :: pick (f a) (f b)
    else f (slot o j :: par a b o)) = slot o j :: par (f a) (f b) o
  simp only [h, ↓reduceIte]
  cases o with
  | none =>
    have h' : ¬ (2 * j + 1) % 2 = 0 := by omega
    simp only [slot, par, h', ↓reduceIte]
  | some s =>
    have h' : (2 * j) % 2 = 0 := by omega
    simp only [slot, par, h', ↓reduceIte]
    cases s <;> rfl

theorem append_child (l : List Nat) (a b : Id) (o : Option Bool) (j : Nat) :
    l ++ child a b o j = (l ++ [slot o j]) ++ par a b o := by
  simp [child]

namespace Site

variable {ar : S → Nat} {a b : Id} {α β : S}

/-- On the identifiers in use, the extension is the renaming itself. -/
theorem rechild_used (h : Site ar N a b α β) (f : Id → Id) {i : Id} (hu : N.Used i) :
    rechild f a b i = f i := by
  cases i with
  | nil => rfl
  | cons n t =>
    have hn : ¬ (t = a ∨ t = b) := by
      rintro (e | e)
      · exact h.not_used_desc (some false) n [] (e ▸ hu)
      · exact h.not_used_desc (some true) n [] (e ▸ hu)
    show (if t = a ∨ t = b then _ else f (n :: t)) = f (n :: t)
    simp only [hn, ↓reduceIte]

/-- Identifiers stay in use. -/
theorem used_fire_mono (h : Site ar N a b α β) (R : Rhs S) {i : Id} (hu : N.Used i) :
    (N.fire a b R).Used i := by
  rcases hu with ⟨γ, hg⟩ | ⟨k, q, hl⟩ | ⟨k, hf⟩
  · have hE : N.End ar (i, 0) := .inr ⟨γ, hg, Nat.zero_le _⟩
    obtain ⟨q, hl⟩ := h.wf.end_wired hE
    exact .inr (.inl ⟨0, q, .inl hl⟩)
  · exact .inr (.inl ⟨k, q, .inl hl⟩)
  · exact .inr (.inr ⟨k, hf⟩)

/-- **Firing commutes with renaming**: renaming the net and firing the
renamed pair gives the renamed result, for any extension of the renaming
that sends the new agents of one firing to the new agents of the other. -/
theorem map_fire (h : Site ar N a b α β) {f g : Id → Id} (hf : Renaming f N)
    (hg : ∀ i, N.Used i → g i = f i) (hc : ∀ o j, g (child a b o j) = child (f a) (f b) o j)
    (R : Rhs S) : (N.fire a b R).map g = (N.map f).fire (f a) (f b) R := by
  have ha : N.Used a := .inl ⟨_, h.ha⟩
  have hb : N.Used b := .inl ⟨_, h.hb⟩
  have hp : ∀ {p q : Port}, N.link p q → mapPort g p = mapPort f p := fun hl =>
    Prod.ext (hg _ (Net.used_link hl)) rfl
  have he : ∀ x, mapPort g (emb a b x) = emb (f a) (f b) x := by
    intro x
    cases x with
    | ifc s k =>
      cases s
      · exact Prod.ext (hg a ha) rfl
      · exact Prod.ext (hg b hb) rfl
    | new o j k => exact Prod.ext (hc o j) rfl
  apply Net.ext'
  · intro i γ
    constructor
    · rintro ⟨i', rfl, ⟨hag, na, nb⟩ | ⟨o, j, rfl, hl⟩⟩
      · have hu : N.Used i' := .inl ⟨_, hag⟩
        rw [hg i' hu]
        exact .inl ⟨⟨i', rfl, hag⟩, fun e => na (hf.inj hu ha e), fun e => nb (hf.inj hu hb e)⟩
      · exact .inr ⟨o, j, hc o j, hl⟩
    · rintro (⟨⟨i', rfl, hag⟩, na, nb⟩ | ⟨o, j, rfl, hl⟩)
      · exact ⟨i', (hg i' (.inl ⟨_, hag⟩)).symm,
          .inl ⟨hag, fun e => na (congrArg f e), fun e => nb (congrArg f e)⟩⟩
      · exact ⟨child a b o j, (hc o j).symm, .inr ⟨o, j, rfl, hl⟩⟩
  · intro p q
    constructor
    · rintro ⟨p', q', rfl, rfl, hl | ⟨x, y, hxy, rfl, rfl⟩⟩
      · exact .inl ⟨p', q', hp hl, hp (h.wf.symm hl), hl⟩
      · exact .inr ⟨x, y, hxy, he x, he y⟩
    · rintro (⟨p', q', rfl, rfl, hl⟩ | ⟨x, y, hxy, rfl, rfl⟩)
      · exact ⟨p', q', (hp hl).symm, (hp (h.wf.symm hl)).symm, .inl hl⟩
      · exact ⟨emb a b x, emb a b y, (he x).symm, (he y).symm, .inr ⟨x, y, hxy, rfl, rfl⟩⟩
  · intro p
    constructor
    · rintro ⟨p', rfl, hfr⟩
      exact ⟨p', Prod.ext (hg _ (.inr (.inr ⟨p'.2, hfr⟩))) rfl, hfr⟩
    · rintro ⟨p', rfl, hfr⟩
      have e : mapPort g p' = mapPort f p' := Prod.ext (hg _ (.inr (.inr ⟨p'.2, hfr⟩))) rfl
      exact ⟨p', e.symm, hfr⟩

end Site

namespace Renaming

variable {ar : S → Nat} {a b : Id} {α β : S}

/-- **The extended renaming is a renaming of the net after the firing.** -/
theorem fire (hf : Renaming f N) (h : Site ar N a b α β) (R : Rhs S) :
    Renaming (rechild f a b) (N.fire a b R) := by
  have hm := hf.site_map h
  have hg : ∀ {i}, N.Used i → rechild f a b i = f i := fun hu => h.rechild_used f hu
  have hc := rechild_child f a b
  have ha : N.Used a := .inl ⟨_, h.ha⟩
  have hb : N.Used b := .inl ⟨_, h.hb⟩
  -- the image of a new name extends the image of a fired agent
  have hpar : ∀ o, ∃ x δ, N.agent x δ ∧ par (f a) (f b) o = f x := by
    intro o
    rcases par_eq (f a) (f b) o with e | e
    · exact ⟨a, α, h.ha, e⟩
    · exact ⟨b, β, h.hb, e⟩
  constructor
  · intro i j hi hj e
    rcases h.used_fire hi with hi | ⟨o, n, rfl⟩ <;>
      rcases h.used_fire hj with hj | ⟨o', n', rfl⟩
    · rw [hg hi, hg hj] at e
      exact hf.inj hi hj e
    · rw [hg hi, hc] at e
      obtain ⟨x, δ, hx, ex⟩ := hpar o'
      have e' : f i = [slot o' n'] ++ f x := by rw [e, ← ex]; rfl
      exact absurd (hf.fresh _ hx hi e') (by simp)
    · rw [hc, hg hj] at e
      obtain ⟨x, δ, hx, ex⟩ := hpar o
      have e' : f j = [slot o n] ++ f x := by rw [← e, ← ex]; rfl
      exact absurd (hf.fresh _ hx hj e') (by simp)
    · rw [hc, hc] at e
      obtain ⟨rfl, rfl⟩ := hm.child_inj e
      rfl
  · intro c γ i l hcg hi e
    rcases hcg with ⟨hag, na, nb⟩ | ⟨o, n, rfl, -⟩ <;>
      rcases h.used_fire hi with hi | ⟨o', n', rfl⟩
    · rw [hg hi, hg (.inl ⟨_, hag⟩)] at e
      exact hf.fresh l hag hi e
    · rw [hc, hg (.inl ⟨_, hag⟩)] at e
      cases l with
      | nil => rfl
      | cons m l' =>
        have e' : slot o' n' :: par (f a) (f b) o' = m :: (l' ++ f c) := e
        obtain ⟨x, δ, hx, ex⟩ := hpar o'
        have e₂ : f x = l' ++ f c := ex.symm.trans (List.cons.inj e').2
        obtain rfl := hf.fresh l' hag (.inl ⟨_, hx⟩) e₂
        have ec : x = c := hf.inj (.inl ⟨_, hx⟩) (.inl ⟨_, hag⟩) e₂
        subst ec
        rcases par_eq (f a) (f b) o' with e₃ | e₃
        · exact absurd (hf.inj (.inl ⟨_, hx⟩) ha (ex.symm.trans e₃)) na
        · exact absurd (hf.inj (.inl ⟨_, hx⟩) hb (ex.symm.trans e₃)) nb
    · rw [hg hi, hc, append_child] at e
      obtain ⟨x, δ, hx, ex⟩ := hpar o
      rw [ex] at e
      exact absurd (hf.fresh _ hx hi e) (by simp)
    · rw [hc, hc] at e
      cases l with
      | nil => rfl
      | cons m l' =>
        have e' : slot o' n' :: par (f a) (f b) o' = m :: (l' ++ child (f a) (f b) o n) := e
        have e₂ := (List.cons.inj e').2
        rw [append_child] at e₂
        obtain ⟨x, δ, hx, ex⟩ := hpar o
        obtain ⟨x', δ', hx', ex'⟩ := hpar o'
        rw [ex, ex'] at e₂
        exact absurd (hf.fresh _ hx (.inl ⟨_, hx'⟩) e₂) (by simp)

/-- An active pair is carried along a renaming. -/
theorem redex_map (hf : Renaming f N) (hN : N.WF sys.ar) {R : Rhs S}
    (r : Redex sys N a b α β R) : Redex sys (N.map f) (f a) (f b) α β R :=
  have s := hf.site_map (r.site hN)
  ⟨s.ha, s.hb, s.ne, s.conn, r.rule⟩

/-- Every active pair of the renamed net comes from one of the net. -/
theorem redex_of_map (hf : Renaming f N) (hN : N.WF sys.ar) {a' b' : Id} {R : Rhs S}
    (r : Redex sys (N.map f) a' b' α β R) :
    ∃ a b, a' = f a ∧ b' = f b ∧ Redex sys N a b α β R := by
  obtain ⟨a, rfl, ha⟩ := r.ha
  obtain ⟨b, rfl, hb⟩ := r.hb
  have hEa : N.End sys.ar (a, 0) := .inr ⟨α, ha, Nat.zero_le _⟩
  have hEb : N.End sys.ar (b, 0) := .inr ⟨β, hb, Nat.zero_le _⟩
  obtain ⟨q, hq, -, hc⟩ := hN.end_conn hEa
  have e : mapPort f q = mapPort f (b, 0) :=
    Net.Conn.det (hf.wf_map hN) r.end_left (Net.end_map hq) r.end_right
      (hf.conn_map hN.symm hc) r.conn
  obtain rfl := hf.port_inj hq.used hEb.used e
  exact ⟨a, b, rfl, rfl, ha, hb, fun e => r.ne (congrArg f e), hc, r.rule⟩

end Renaming

/-- Identifiers stay in use along a reduction step. -/
theorem Step.used (hN : N.WF sys.ar) (h : Step sys N N') {i : Id} (hu : N.Used i) :
    N'.Used i := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  exact (r.site hN).used_fire_mono R hu

/-- **Reduction commutes with renaming**: a step of a net is a step of the
renamed net, to the result renamed by an extension of the renaming. -/
theorem Step.map (hN : N.WF sys.ar) (hf : Renaming f N) (h : Step sys N N') :
    ∃ g, Renaming g N' ∧ (∀ i, N.Used i → g i = f i) ∧ Step sys (N.map f) (N'.map g) := by
  obtain ⟨a, b, α, β, R, r, rfl⟩ := h
  have s := r.site hN
  exact ⟨rechild f a b, hf.fire s R, fun i hu => s.rechild_used f hu, f a, f b, α, β, R,
    hf.redex_map hN r, s.map_fire hf (fun i hu => s.rechild_used f hu) (rechild_child f a b) R⟩

/-- Conversely, every step of the renamed net is the renaming of a step. -/
theorem Step.of_map (hN : N.WF sys.ar) (hf : Renaming f N) (h : Step sys (N.map f) M') :
    ∃ N' g, Step sys N N' ∧ Renaming g N' ∧ (∀ i, N.Used i → g i = f i) ∧ M' = N'.map g := by
  obtain ⟨a', b', α, β, R, r, rfl⟩ := h
  obtain ⟨a, b, rfl, rfl, r'⟩ := hf.redex_of_map hN r
  have s := r'.site hN
  exact ⟨N.fire a b R, rechild f a b, ⟨a, b, α, β, R, r', rfl⟩, hf.fire s R,
    fun i hu => s.rechild_used f hu,
    (s.map_fire hf (fun i hu => s.rechild_used f hu) (rechild_child f a b) R).symm⟩

/-- A reduction of a net is a reduction of the renamed net, of the same
length. -/
theorem Steps.map {n : Nat} (hN : N.WF sys.ar) (hf : Renaming f N)
    (h : Steps (Step sys) n N N') :
    ∃ g, Renaming g N' ∧ (∀ i, N.Used i → g i = f i) ∧
      Steps (Step sys) n (N.map f) (N'.map g) := by
  induction h generalizing f with
  | refl N => exact ⟨f, hf, fun _ _ => rfl, .refl _⟩
  | head h₁ _ ih =>
    obtain ⟨g₁, hg₁, e₁, s₁⟩ := Step.map hN hf h₁
    obtain ⟨g, hg, e, s⟩ := ih (Step.wf hN h₁) hg₁
    exact ⟨g, hg, fun i hu => (e i (Step.used hN h₁ hu)).trans (e₁ i hu), .head s₁ s⟩

/-- A net and its renamings are normal together. -/
theorem Renaming.normal (hf : Renaming f N) (hN : N.WF sys.ar) :
    Normal (Step sys) N ↔ Normal (Step sys) (N.map f) := by
  constructor
  · intro hn M' s
    obtain ⟨N', g, s', -⟩ := Step.of_map hN hf s
    exact hn N' s'
  · intro hn N' s
    obtain ⟨g, -, -, s'⟩ := Step.map hN hf s
    exact hn _ s'

/-- On the nose: the normal form of a renamed net is a renaming of the
normal form, reached in the same number of steps. -/
theorem Renaming.normal_form {n m : Nat} (hf : Renaming f N) (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) n N N') (h₂ : Steps (Step sys) m (N.map f) M')
    (hn₁ : Normal (Step sys) N') (hn₂ : Normal (Step sys) M') :
    ∃ g, Renaming g N' ∧ (∀ i, N.Used i → g i = f i) ∧ M' = N'.map g ∧ n = m := by
  obtain ⟨g, hg, e, s⟩ := Steps.map hN hf h₁
  have hn := (hg.normal (Steps.wf hN h₁)).1 hn₁
  obtain ⟨rfl, rfl⟩ := normal_form_unique (hf.wf_map hN) s h₂ hn hn₂
  exact ⟨g, hg, e, rfl, rfl⟩

/-! ### Renamings exist -/

theorem Net.map_id (N : Net S) : N.map id = N := by
  apply Net.ext'
  · intro i γ
    constructor
    · rintro ⟨i', rfl, h⟩
      exact h
    · exact fun h => ⟨i, rfl, h⟩
  · intro p q
    constructor
    · rintro ⟨p', q', rfl, rfl, h⟩
      exact h
    · exact fun h => ⟨p, q, rfl, rfl, h⟩
  · intro p
    constructor
    · rintro ⟨p', rfl, h⟩
      exact h
    · exact fun h => ⟨p, rfl, h⟩

/-- The identity is a renaming of every well-formed net. -/
theorem Renaming.id {ar : S → Nat} (hN : N.WF ar) : Renaming id N where
  inj := fun _ _ e => e
  fresh := by
    intro a α i l hg hu e
    have e' : i = l ++ a := e
    subst e'
    exact hN.fresh l hg hu

theorem relabel_inj {π : Nat → Nat} (hπ : ∀ {m n}, π m = π n → m = n) :
    ∀ {i j : Id}, i.map π = j.map π → i = j
  | [], [], _ => rfl
  | [], _ :: _, e => by simp at e
  | _ :: _, [], e => by simp at e
  | m :: i, n :: j, e => by
    simp only [List.map_cons, List.cons.injEq] at e
    rw [hπ e.1, relabel_inj hπ e.2]

/-- Relabelling the numbers that make up the identifiers, by any injective
function, is a renaming of every well-formed net.  The function need not be
monotone, so the order that `pick` consults may be reversed. -/
theorem Renaming.relabel {ar : S → Nat} (hN : N.WF ar) {π : Nat → Nat}
    (hπ : ∀ {m n}, π m = π n → m = n) : Renaming (List.map π) N where
  inj := fun _ _ e => relabel_inj hπ e
  fresh := by
    intro a α i l hg hu e
    obtain ⟨l₁, l₂, rfl, rfl, e₂⟩ := List.map_eq_append_iff.1 e
    obtain rfl := relabel_inj hπ e₂
    have e₁ := hN.fresh l₁ hg hu
    subst e₁
    rfl

/-! ### Nets up to names and history -/

/-- `M` is a copy of `N` up to the names of the agents and the history of
the wires: the renaming `f` of `N` is observationally equivalent to `M`. -/
structure Net.Iso (ar : S → Nat) (f : Id → Id) (N M : Net S) : Prop where
  ren : Renaming f N
  obs : (N.map f).ObsEq ar M

/-- Observationally equivalent nets are copies of each other. -/
theorem Net.ObsEq.iso {ar : S → Nat} (ho : N.ObsEq ar M) (hN : N.WF ar) : N.Iso ar id M :=
  ⟨Renaming.id hN, by rw [Net.map_id]; exact ho⟩

namespace Net.Iso

/-- **Bisimulation up to names**: a step of a net is matched by a step of
any copy of it, and the results are copies of each other, by a renaming
that extends the given one. -/
theorem step (hi : N.Iso sys.ar f M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h : Step sys N N') :
    ∃ g M', (∀ i, N.Used i → g i = f i) ∧ Step sys M M' ∧ N'.Iso sys.ar g M' := by
  obtain ⟨g, hg, e, s⟩ := Step.map hN hi.ren h
  obtain ⟨M', s', ho⟩ := hi.obs.step (hi.ren.wf_map hN) hM s
  exact ⟨g, M', e, s', hg, ho⟩

/-- The other direction: a step of the copy is matched by a step of the net. -/
theorem step_inv (hi : N.Iso sys.ar f M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h : Step sys M M') :
    ∃ g N', (∀ i, N.Used i → g i = f i) ∧ Step sys N N' ∧ N'.Iso sys.ar g M' := by
  obtain ⟨P, s, ho⟩ := hi.obs.symm.step hM (hi.ren.wf_map hN) h
  obtain ⟨N', g, s', hg, e, rfl⟩ := Step.of_map hN hi.ren s
  exact ⟨g, N', e, s', hg, ho.symm⟩

theorem steps {n : Nat} (hi : N.Iso sys.ar f M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h : Steps (Step sys) n N N') :
    ∃ g M', (∀ i, N.Used i → g i = f i) ∧ Steps (Step sys) n M M' ∧ N'.Iso sys.ar g M' := by
  obtain ⟨g, hg, e, s⟩ := Steps.map hN hi.ren h
  obtain ⟨M', s', ho⟩ := hi.obs.steps (hi.ren.wf_map hN) hM s
  exact ⟨g, M', e, s', hg, ho⟩

/-- A net and its copies are normal together. -/
theorem normal (hi : N.Iso sys.ar f M) (hN : N.WF sys.ar) (hM : M.WF sys.ar) :
    Normal (Step sys) N ↔ Normal (Step sys) M :=
  (hi.ren.normal hN).trans
    ⟨hi.obs.normal (hi.ren.wf_map hN) hM, hi.obs.symm.normal hM (hi.ren.wf_map hN)⟩

/-- **Normal forms do not depend on the names of the agents**: if two nets
are copies of each other, so are their normal forms, by a renaming that
extends the given one, and they are reached in the same number of steps. -/
theorem normal_form {n m : Nat} (hi : N.Iso sys.ar f M) (hN : N.WF sys.ar) (hM : M.WF sys.ar)
    (h₁ : Steps (Step sys) n N N') (h₂ : Steps (Step sys) m M M')
    (hn₁ : Normal (Step sys) N') (hn₂ : Normal (Step sys) M') :
    ∃ g, (∀ i, N.Used i → g i = f i) ∧ N'.Iso sys.ar g M' ∧ n = m := by
  obtain ⟨g, M₁, e, s₁, hi₁⟩ := hi.steps hN hM h₁
  have hn := (hi₁.normal (Steps.wf hN h₁) (Steps.wf hM s₁)).1 hn₁
  obtain ⟨rfl, rfl⟩ := normal_form_unique hM s₁ h₂ hn hn₂
  exact ⟨g, e, hi₁, rfl⟩

end Net.Iso

/-! ### Renaming, compaction and the reducer -/

namespace Renaming

variable {ar : S → Nat}

/-- The pairing of ends in a renamed net. -/
theorem paired_map (hf : Renaming f N) (hN : N.WF ar) {p q : Port} :
    (N.map f).Paired ar p q ↔
      ∃ p' q', p = mapPort f p' ∧ q = mapPort f q' ∧ N.Paired ar p' q' := by
  constructor
  · rintro ⟨hp, hq, hc⟩
    obtain ⟨p', rfl, hp'⟩ := Net.end_of_map hp
    obtain ⟨q', rfl, hq'⟩ := Net.end_of_map hq
    obtain ⟨q'', hq'', -, hc'⟩ := hN.end_conn hp'
    have e := Net.Conn.det (hf.wf_map hN) hp (Net.end_map hq'') hq
      (hf.conn_map hN.symm hc') hc
    obtain rfl := hf.port_inj hq''.used hq'.used e
    exact ⟨p', q'', rfl, rfl, hp', hq'', hc'⟩
  · rintro ⟨p', q', rfl, rfl, hp', hq', hc⟩
    exact ⟨Net.end_map hp', Net.end_map hq', hf.conn_map hN.symm hc⟩

/-- **Compaction commutes with renaming.** -/
theorem compact_map (hf : Renaming f N) (hN : N.WF ar) :
    (N.map f).compact ar = (N.compact ar).map f :=
  Net.ext' (fun _ _ => Iff.rfl) (fun _ _ => hf.paired_map hN) (fun _ => Iff.rfl)

theorem compact (hf : Renaming f N) : Renaming f (N.compact ar) := by
  have hu : ∀ {i}, (N.compact ar).Used i → N.Used i := by
    rintro i (hg | ⟨k, q, hp, -⟩ | hfr)
    · exact .inl hg
    · exact hp.used
    · exact .inr (.inr hfr)
  exact ⟨fun hi hj e => hf.inj (hu hi) (hu hj) e, fun l hg hi e => hf.fresh l hg (hu hi) e⟩

end Renaming

section CompactRename

variable {C C' D : Net S}

/-- Reduction without history commutes with renaming.  The extended
renaming agrees with the given one on the interface. -/
theorem CStep.map (hC : C.WF sys.ar) (hf : Renaming f C) (h : CStep sys C C') :
    ∃ g, Renaming g C' ∧ (∀ p, C.free p → g p.1 = f p.1) ∧ CStep sys (C.map f) (C'.map g) := by
  obtain ⟨N', s, rfl⟩ := h
  obtain ⟨g, hg, e, s'⟩ := Step.map hC hf s
  exact ⟨g, hg.compact, fun p hp => e _ (.inr (.inr ⟨p.2, hp⟩)), N'.map g, s',
    (hg.compact_map (Step.wf hC s)).symm⟩

theorem CStep.of_map (hC : C.WF sys.ar) (hf : Renaming f C) (h : CStep sys (C.map f) D) :
    ∃ C', CStep sys C C' := by
  obtain ⟨N', s, -⟩ := h
  obtain ⟨N'', g, s', -⟩ := Step.of_map hC hf s
  exact ⟨_, N'', s', rfl⟩

theorem Steps.cmap {n : Nat} (hC : C.WF sys.ar) (hf : Renaming f C)
    (h : Steps (CStep sys) n C C') :
    ∃ g, Renaming g C' ∧ (∀ p, C.free p → g p.1 = f p.1) ∧
      Steps (CStep sys) n (C.map f) (C'.map g) := by
  induction h generalizing f with
  | refl C => exact ⟨f, hf, fun _ _ => rfl, .refl _⟩
  | head h₁ _ ih =>
    obtain ⟨g₁, hg₁, e₁, s₁⟩ := CStep.map hC hf h₁
    obtain ⟨g, hg, e, s⟩ := ih (CStep.wf hC h₁) hg₁
    refine ⟨g, hg, fun p hp => (e p ?_).trans (e₁ p hp), .head s₁ s⟩
    obtain ⟨N', st, rfl⟩ := h₁
    have ef := Step.free st
    show N'.free p
    rw [ef]
    exact hp

end CompactRename

/-! ### Copies form an equivalence, up to history -/

/-- Ends that are paired in the renamed net were paired in the net. -/
theorem Renaming.paired_of_map {ar : S → Nat} {N : Net S} {f : Id → Id} (hf : Renaming f N)
    (hN : N.WF ar) {p q : Port} (hp : N.End ar p) (hq : N.End ar q)
    (h : (N.map f).Paired ar (mapPort f p) (mapPort f q)) : N.Paired ar p q := by
  obtain ⟨q₀, hq₀, -, hc⟩ := hN.end_conn hp
  have h₀ := hf.conn_map (ar := ar) hN.symm hc
  have e := Net.Conn.det (hf.wf_map hN) h.1 (Net.end_map hq₀) h.2.1 h₀ h.2.2
  rw [← hf.port_inj hq₀.used hq.used e]
  exact ⟨hp, hq₀, hc⟩

/-- A name in use in a net without history is the name of an end. -/
theorem Net.used_compact {ar : S → Nat} {N : Net S} {i : Id}
    (h : (N.compact ar).Used i) : ∃ k, N.End ar (i, k) := by
  rcases h with ⟨γ, hg⟩ | ⟨k, q, hl⟩ | ⟨k, hfr⟩
  · exact ⟨0, .inr ⟨γ, hg, Nat.zero_le _⟩⟩
  · exact ⟨k, hl.1⟩
  · exact ⟨k, .inl hfr⟩

/-- An inverse of a renaming on the names of the ends of the net: the name
of the end that is renamed to `j`, if there is one. -/
noncomputable def Renaming.back (ar : S → Nat) (f : Id → Id) (N : Net S) (j : Id) : Id :=
  @dite _ (∃ i, (∃ k, N.End ar (i, k)) ∧ f i = j) (Classical.propDecidable _)
    (fun h => Classical.choose h) (fun _ => j)

theorem Renaming.back_apply {ar : S → Nat} {N : Net S} {f : Id → Id} (hf : Renaming f N)
    {i : Id} {k : Nat} (h : N.End ar (i, k)) : Renaming.back ar f N (f i) = i := by
  have hex : ∃ i', (∃ k, N.End ar (i', k)) ∧ f i' = f i := ⟨i, ⟨k, h⟩, rfl⟩
  unfold Renaming.back
  split
  · rename_i h'
    obtain ⟨⟨k', hk'⟩, e⟩ := Classical.choose_spec h'
    exact hf.inj hk'.used h.used e
  · rename_i h'
    exact absurd hex h'

/-- **Copies, the other way round.**  If `M` is a copy of `N`, then `N` is a
copy of `M` without its history, by an inverse of the renaming.  The
history of `M` has to go: it may use names that `N` reserves. -/
theorem Net.Iso.symm {ar : S → Nat} {N M : Net S} {f : Id → Id} (hi : N.Iso ar f M)
    (hN : N.WF ar) (hM : M.WF ar) : (M.compact ar).Iso ar (Renaming.back ar f N) N := by
  have hC := hM.compact
  have hend : ∀ {q : Port}, M.End ar q → ∃ p, q = mapPort f p ∧ N.End ar p := fun h =>
    Net.end_of_map ((hi.obs.end_iff _).2 h)
  have hused : ∀ {j : Id}, (M.compact ar).Used j → ∃ i k, j = f i ∧ N.End ar (i, k) := by
    intro j hu
    obtain ⟨k, hk⟩ := Net.used_compact hu
    obtain ⟨p, e, hp⟩ := hend hk
    exact ⟨p.1, p.2, (Prod.mk.inj e).1, hp⟩
  have hback : ∀ {p : Port}, N.End ar p →
      mapPort (Renaming.back ar f N) (mapPort f p) = p := by
    intro p hp
    show (Renaming.back ar f N (f p.1), p.2) = p
    rw [Renaming.back_apply hi.ren (k := p.2) hp]
  have hren : Renaming (Renaming.back ar f N) (M.compact ar) := by
    constructor
    · intro j₁ j₂ h₁ h₂ e
      obtain ⟨i₁, k₁, rfl, e₁⟩ := hused h₁
      obtain ⟨i₂, k₂, rfl, e₂⟩ := hused h₂
      rw [Renaming.back_apply hi.ren e₁, Renaming.back_apply hi.ren e₂] at e
      rw [e]
    · intro a α i l hg hu e
      obtain ⟨i', k', rfl, e₁⟩ := hused hu
      obtain ⟨a', rfl, hg'⟩ := (hi.obs.agent a α).2 hg
      rw [Renaming.back_apply hi.ren e₁,
        Renaming.back_apply hi.ren (k := 0) (.inr ⟨α, hg', Nat.zero_le _⟩)] at e
      refine hN.fresh l hg' ?_
      rw [← e]
      exact e₁.used
  refine ⟨hren, ?_, ?_, ?_⟩
  · intro i γ
    constructor
    · rintro ⟨j, rfl, hg⟩
      obtain ⟨a', rfl, hg'⟩ := (hi.obs.agent j γ).2 hg
      rw [Renaming.back_apply hi.ren (k := 0) (.inr ⟨γ, hg', Nat.zero_le _⟩)]
      exact hg'
    · intro hg
      exact ⟨f i, (Renaming.back_apply hi.ren (k := 0) (.inr ⟨γ, hg, Nat.zero_le _⟩)).symm,
        (hi.obs.agent (f i) γ).1 ⟨i, rfl, hg⟩⟩
  · intro p
    constructor
    · rintro ⟨q, rfl, hfr⟩
      obtain ⟨p', rfl, hfr'⟩ := (hi.obs.free q).2 hfr
      rw [hback (.inl hfr')]
      exact hfr'
    · intro hfr
      exact ⟨mapPort f p, (hback (.inl hfr)).symm, (hi.obs.free _).1 ⟨p, rfl, hfr⟩⟩
  · intro p q
    constructor
    · intro h
      obtain ⟨p', rfl, hp'⟩ := Net.end_of_map h.1
      obtain ⟨q', rfl, hq'⟩ := Net.end_of_map h.2.1
      have h₁ := hren.paired_of_map hC hp' hq' h
      have h₂ := (hi.obs.paired p' q').2 (Net.compact_paired.1 h₁)
      obtain ⟨p'', rfl, hp''⟩ := Net.end_of_map h₂.1
      obtain ⟨q'', rfl, hq''⟩ := Net.end_of_map h₂.2.1
      rw [hback hp'', hback hq'']
      exact hi.ren.paired_of_map hN hp'' hq'' h₂
    · intro h
      have h₁ := (hi.ren.paired_map hN).2 ⟨_, _, rfl, rfl, h⟩
      have h₂ := Net.compact_paired.2 ((hi.obs.paired _ _).1 h₁)
      have h₃ := (hren.paired_map hC).2 ⟨_, _, rfl, rfl, h₂⟩
      rw [hback h.1, hback h.2.1] at h₃
      exact h₃

/-- A copy without history has the net as a copy. -/
theorem Net.Iso.symm_compact {ar : S → Nat} {N M : Net S} {f : Id → Id} (hi : N.Iso ar f M)
    (hN : N.WF ar) (hM : M.WF ar) (hc : M.compact ar = M) :
    M.Iso ar (Renaming.back ar f N) N := by
  have h := hi.symm hN hM
  rw [hc] at h
  exact h

/-- **A copy of a copy is a copy**, of the net without its history, by the
two renamings one after the other. -/
theorem Net.Iso.trans {ar : S → Nat} {N M P : Net S} {f g : Id → Id} (h₁ : N.Iso ar f M)
    (h₂ : M.Iso ar g P) (hN : N.WF ar) (hM : M.WF ar) :
    (N.compact ar).Iso ar (g ∘ f) P := by
  have hC := hN.compact
  have hMend : ∀ {p : Port}, N.End ar p → M.End ar (mapPort f p) := fun h =>
    (h₁.obs.end_iff _).1 (Net.end_map h)
  have hgf : Renaming (g ∘ f) (N.compact ar) := by
    constructor
    · intro i j hi hj e
      obtain ⟨k₁, e₁⟩ := Net.used_compact hi
      obtain ⟨k₂, e₂⟩ := Net.used_compact hj
      exact h₁.ren.inj e₁.used e₂.used
        (h₂.ren.inj (hMend e₁).used (hMend e₂).used e)
    · intro a α i l hg hu e
      obtain ⟨k₁, e₁⟩ := Net.used_compact hu
      exact h₂.ren.fresh l ((h₁.obs.agent _ _).1 ⟨a, rfl, hg⟩) (hMend e₁).used e
  refine ⟨hgf, ?_, ?_, ?_⟩
  · intro i γ
    constructor
    · rintro ⟨i', rfl, hg⟩
      exact (h₂.obs.agent _ _).1 ⟨f i', rfl, (h₁.obs.agent _ _).1 ⟨i', rfl, hg⟩⟩
    · intro hg
      obtain ⟨j, rfl, hj⟩ := (h₂.obs.agent _ _).2 hg
      obtain ⟨i', rfl, hi'⟩ := (h₁.obs.agent _ _).2 hj
      exact ⟨i', rfl, hi'⟩
  · intro p
    constructor
    · rintro ⟨p', rfl, hfr⟩
      exact (h₂.obs.free _).1 ⟨mapPort f p', rfl, (h₁.obs.free _).1 ⟨p', rfl, hfr⟩⟩
    · intro hfr
      obtain ⟨q, rfl, hq⟩ := (h₂.obs.free _).2 hfr
      obtain ⟨p', rfl, hp'⟩ := (h₁.obs.free _).2 hq
      exact ⟨p', rfl, hp'⟩
  · intro p q
    constructor
    · intro h
      obtain ⟨p', rfl, hp'⟩ := Net.end_of_map h.1
      obtain ⟨q', rfl, hq'⟩ := Net.end_of_map h.2.1
      have a₁ := Net.compact_paired.1 (hgf.paired_of_map hC hp' hq' h)
      have a₂ := (h₁.obs.paired _ _).1 ((h₁.ren.paired_map hN).2 ⟨_, _, rfl, rfl, a₁⟩)
      exact (h₂.obs.paired _ _).1 ((h₂.ren.paired_map hM).2 ⟨_, _, rfl, rfl, a₂⟩)
    · intro h
      have b₁ := (h₂.obs.paired _ _).2 h
      obtain ⟨p₁, rfl, hp₁⟩ := Net.end_of_map b₁.1
      obtain ⟨q₁, rfl, hq₁⟩ := Net.end_of_map b₁.2.1
      have b₂ := (h₁.obs.paired _ _).2 (h₂.ren.paired_of_map hM hp₁ hq₁ b₁)
      obtain ⟨p₂, rfl, hp₂⟩ := Net.end_of_map b₂.1
      obtain ⟨q₂, rfl, hq₂⟩ := Net.end_of_map b₂.2.1
      have b₃ := h₁.ren.paired_of_map hN hp₂ hq₂ b₂
      exact (hgf.paired_map hC).2 ⟨_, _, rfl, rfl, Net.compact_paired.2 b₃⟩

/-- `M` is a copy of `N`, by some renaming. -/
def Net.Copy (ar : S → Nat) (N M : Net S) : Prop := ∃ f, N.Iso ar f M

/-- **On well-formed nets without history, being a copy is an equivalence
relation.** -/
theorem Net.Copy.refl {ar : S → Nat} {N : Net S} (hN : N.WF ar) : N.Copy ar N :=
  ⟨id, (Net.ObsEq.refl N).iso hN⟩

theorem Net.Copy.symm {ar : S → Nat} {N M : Net S} (h : N.Copy ar M) (hN : N.WF ar)
    (hM : M.WF ar) (hc : M.compact ar = M) : M.Copy ar N := by
  obtain ⟨f, hi⟩ := h
  exact ⟨_, hi.symm_compact hN hM hc⟩

theorem Net.Copy.trans {ar : S → Nat} {N M P : Net S} (h₁ : N.Copy ar M) (h₂ : M.Copy ar P)
    (hN : N.WF ar) (hM : M.WF ar) (hc : N.compact ar = N) : N.Copy ar P := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  have h := hf.trans hg hN hM
  rw [hc] at h
  exact ⟨_, h⟩

end Rename

end INet
