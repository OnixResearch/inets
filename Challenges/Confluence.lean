/-! # The statement of confluence, for Comparator

This file restates, word for word, the definitions that the statements of
the main theorems of `InteractionNets.Confluence` depend on, and states
those theorems with their proofs left open.  It is trusted: a reader who
accepts these definitions as Lafont's interaction nets can check, with
`lake comparator --config Challenges/Confluence.json`, that the library
proves exactly these statements, with no axiom but `propext`,
`Quot.sound` and `Classical.choice`, and that its proofs pass the kernel.
It is not part of the library, and nothing imports it. -/

namespace INet

universe u v

section Rewriting

variable {A : Type u}

/-- `Steps r n a b`: `a` rewrites to `b` in exactly `n` steps of `r`. -/
inductive Steps (r : A → A → Prop) : Nat → A → A → Prop
  | refl (a : A) : Steps r 0 a a
  | head {n : Nat} {a b c : A} : r a b → Steps r n b c → Steps r (n + 1) a c

/-- A term is normal when no step leaves it. -/
def Normal (r : A → A → Prop) (a : A) : Prop := ∀ b, ¬ r a b

end Rewriting

section Wires

variable {V : Type u}

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

end Wires

/-- Agent identifiers. -/
abbrev Id := List Nat

/-- A port: an agent identifier and a port index (`0` is the principal port). -/
abbrev Port := Id × Nat

/-- Select one of two things by a side (`false` = left, `true` = right). -/
def sel {X : Type u} (x y : X) : Bool → X
  | false => x
  | true => y

/-- A total order on identifiers (lexicographic).  It is used for one thing
only: choosing one of two identifiers in a way that does not depend on the
order in which they are given. -/
def idLe : Id → Id → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && idLe xs ys)

/-- One of two identifiers, the same whichever way round they are given. -/
def pick (a b : Id) : Id := if idLe a b then a else b

/-- Exchange the two sides in the owner of a new agent (see `LPort`). -/
def flipOwner (o : Option Bool) : Option Bool := o.map (!·)

/-- The agent after which a new agent is named: the fired agent of its own
side, or, for a new agent owned by neither side, one of the two fired agents
chosen independently of their order. -/
def par (a b : Id) : Option Bool → Id
  | some s => sel a b s
  | none => pick a b

/-- Position of a new agent among those named after the same fired agent. -/
def slot : Option Bool → Nat → Nat
  | some _, j => 2 * j
  | none, j => 2 * j + 1

/-- Identifier of the `j`-th new agent with owner `o` when `a` and `b` fire. -/
def child (a b : Id) (o : Option Bool) (j : Nat) : Id := slot o j :: par a b o

variable {S : Type}

/-- A net over the set of symbols `S`. -/
structure Net (S : Type) where
  /-- `agent i α`: agent `i` is live and carries symbol `α`. -/
  agent : Id → S → Prop
  /-- Wire segments. -/
  link : Port → Port → Prop
  /-- The interface: free ports. -/
  free : Port → Prop

/-- An *end* is a real port of the net: a free port, or a port of a live agent
whose index is within the arity of its symbol. -/
def Net.End (ar : S → Nat) (N : Net S) (p : Port) : Prop :=
  N.free p ∨ ∃ γ, N.agent p.1 γ ∧ p.2 ≤ ar γ

/-- Identifiers occurring in the net. -/
def Net.Used (N : Net S) (i : Id) : Prop :=
  (∃ γ, N.agent i γ) ∨ (∃ k q, N.link (i, k) q) ∨ ∃ k, N.free (i, k)

/-- Two ports are the extremities of a wire: they are joined by a chain of
segments running through junctions only. -/
def Net.Conn (ar : S → Nat) (N : Net S) (p q : Port) : Prop :=
  INet.Conn N.link (N.End ar) p q

/-- Well-formed nets. -/
structure Net.WF (ar : S → Nat) (N : Net S) : Prop where
  /-- An agent has one symbol. -/
  agent_fun : ∀ {i α β}, N.agent i α → N.agent i β → α = β
  symm : ∀ {p q}, N.link p q → N.link q p
  irrefl : ∀ {p}, ¬ N.link p p
  /-- Every end is attached to at most one segment. -/
  end_unique : ∀ {p q r}, N.End ar p → N.link p q → N.link p r → q = r
  /-- The wire leaving an end reaches another end. -/
  end_conn : ∀ {p}, N.End ar p → ∃ q, N.End ar q ∧ q ≠ p ∧ N.Conn ar p q
  /-- Every point is attached to at most two segments. -/
  deg : ∀ {p x y z}, N.link p x → N.link p y → N.link p z → x = y ∨ x = z ∨ y = z
  /-- Free ports are not ports of live agents. -/
  free_agent : ∀ {i k α}, N.free (i, k) → ¬ N.agent i α
  /-- Names reserved for the descendants of a live agent are not in use. -/
  fresh : ∀ {a α} (l : List Nat), N.agent a α → N.Used (l ++ a) → l = []

/-- Ports of the right-hand side of a rule.  Side `false` is the first agent
of the active pair, side `true` the second.  Every new agent has an *owner*:
`some s` if it belongs to side `s`, `none` if it belongs to neither side.
Exchanging the two sides exchanges the agents of side `false` with those of
side `true` and leaves the agents owned by neither side where they are. -/
inductive LPort
  /-- The `k`-th auxiliary port of the agent on side `s`. -/
  | ifc (s : Bool) (k : Nat)
  /-- Port `k` of the `j`-th new agent with owner `o`. -/
  | new (o : Option Bool) (j k : Nat)
  deriving DecidableEq

/-- Exchange the two sides. -/
def LPort.swap : LPort → LPort
  | .ifc s k => .ifc (!s) k
  | .new o j k => .new (flipOwner o) j k

/-- The right-hand side of an interaction rule. -/
structure Rhs (S : Type) where
  /-- Symbol of the `j`-th new agent with owner `o`, if there is one. -/
  lab : Option Bool → Nat → Option S
  /-- Wires of the right-hand side. -/
  link : LPort → LPort → Prop

/-- The ports that exist in the right-hand side of a rule for `α ⋈ β`. -/
def Rhs.Valid (ar : S → Nat) (R : Rhs S) (α β : S) : LPort → Prop
  | .ifc s k => k < ar (sel α β s)
  | .new o j k => ∃ γ, R.lab o j = some γ ∧ k ≤ ar γ

/-- A right-hand side for `α ⋈ β` is a net whose interface is made of the
auxiliary ports of `α` and `β`: every port is attached to exactly one wire. -/
structure Rhs.WF (ar : S → Nat) (R : Rhs S) (α β : S) : Prop where
  symm : ∀ {x y}, R.link x y → R.link y x
  irrefl : ∀ {x}, ¬ R.link x x
  valid : ∀ {x y}, R.link x y → R.Valid ar α β x
  unique : ∀ {x y z}, R.link x y → R.link x z → y = z
  total : ∀ {x}, R.Valid ar α β x → ∃ y, R.link x y

/-- `R'` is `R` with the two sides exchanged. -/
def Rhs.Mirror (R R' : Rhs S) : Prop :=
  (∀ o j, R'.lab o j = R.lab (flipOwner o) j) ∧ ∀ x y, R'.link x y ↔ R.link x.swap y.swap

/-- An interaction system: symbols with arities, and at most one rule for
each pair of symbols, given consistently in both orientations. -/
structure System (S : Type) where
  ar : S → Nat
  rule : S → S → Option (Rhs S)
  rule_wf : ∀ {α β R}, rule α β = some R → R.WF ar α β
  rule_symm : ∀ {α β R}, rule α β = some R → ∃ R', rule β α = some R' ∧ R.Mirror R'

/-- Where a port of the right-hand side lands when agents `a` and `b` fire. -/
def emb (a b : Id) : LPort → Port
  | .ifc s k => (sel a b s, k + 1)
  | .new o j k => (child a b o j, k)

/-- Replace the agents `a` and `b` by the right-hand side `R`. -/
def Net.fire (N : Net S) (a b : Id) (R : Rhs S) : Net S where
  agent i γ := (N.agent i γ ∧ i ≠ a ∧ i ≠ b) ∨ ∃ o j, i = child a b o j ∧ R.lab o j = some γ
  link p q := N.link p q ∨ ∃ x y, R.link x y ∧ p = emb a b x ∧ q = emb a b y
  free := N.free

/-- An active pair: two distinct live agents whose principal ports are joined
by a wire, together with the rule that applies to them. -/
structure Redex (sys : System S) (N : Net S) (a b : Id) (α β : S) (R : Rhs S) : Prop where
  ha : N.agent a α
  hb : N.agent b β
  ne : a ≠ b
  conn : N.Conn sys.ar (a, 0) (b, 0)
  rule : sys.rule α β = some R

/-- One step of reduction: fire an active pair. -/
def Step (sys : System S) (N N' : Net S) : Prop :=
  ∃ a b α β R, Redex sys N a b α β R ∧ N' = N.fire a b R

variable {sys : System S} {N N₁ N₂ : Net S}

/-- Reduction keeps nets well formed. -/
theorem Step.wf (hN : N.WF sys.ar) (h : Step sys N N₁) : N₁.WF sys.ar := by
  sorry

/-- Reduction keeps the interface. -/
theorem Step.free (h : Step sys N N₁) : N₁.free = N.free := by
  sorry

theorem Step.diamond (hN : N.WF sys.ar) (h₁ : Step sys N N₁) (h₂ : Step sys N N₂) :
    N₁ = N₂ ∨ ∃ N', Step sys N₁ N' ∧ Step sys N₂ N' := by
  sorry

theorem confluence {n m : Nat} (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) n N N₁) (h₂ : Steps (Step sys) m N N₂) :
    ∃ N' k l, Steps (Step sys) k N₁ N' ∧ Steps (Step sys) l N₂ N' ∧ n + k = m + l := by
  sorry

theorem normal_form_unique {n m : Nat} (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) n N N₁) (h₂ : Steps (Step sys) m N N₂)
    (hn₁ : Normal (Step sys) N₁) (hn₂ : Normal (Step sys) N₂) : N₁ = N₂ ∧ n = m := by
  sorry

theorem reduction_bounded {n m : Nat} (hN : N.WF sys.ar)
    (h₁ : Steps (Step sys) n N N₁) (hn₁ : Normal (Step sys) N₁)
    (h₂ : Steps (Step sys) m N N₂) : m ≤ n ∧ Steps (Step sys) (n - m) N₂ N₁ := by
  sorry

end INet
