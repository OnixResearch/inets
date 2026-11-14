import InteractionNets.Trees

namespace INet

universe u v

variable {S : Type}

variable {sys : System S} {N N₁ N₂ : Net S}

/-! ### Everything counted

The counts so far left three things out of an operation on a map: the
cells read to compare two names, the work of the balancing functions, and
the nodes built.  Here they are all counted.  The balancing functions of
the library are written again with the nodes they build, and the
comparison of two names with the cells it reads; both are proved to
return what the library returns.  The names grow by one cell for an
interaction at most, which is proved, and the time of the program on
ordered maps alone, with everything counted, is bounded for every
schedule. -/

section FullCount

open Std.DTreeMap.Internal

variable {α : Type} {β : α → Type}

/-- The left balancing function of the library with the nodes it builds:
the equations of `Impl.balanceL!`, and next to each tree the number of
nodes that branch makes. -/
def balanceLF (k : α) (v : β k) (l r : Impl α β) : Impl α β × Nat :=
  match r with
  | .leaf => match l with
    | .leaf => (.inner 1 k v .leaf .leaf, 1)
    | .inner _ _ _ .leaf .leaf => (.inner 2 k v l .leaf, 1)
    | .inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
      (.inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf), 3)
    | .inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
      (.inner 3 lk lv ll (.inner 1 k v .leaf .leaf), 2)
    | .inner ls lk lv ll@(.inner _ _ _ _ _) lr@(.inner lrs _ _ _ _) =>
      (.inner (1 + ls) lk lv ll (.inner (1 + lrs) k v lr .leaf), 2)
  | .inner rs _ _ _ _ => match l with
    | .leaf => (.inner (1 + rs) k v .leaf r, 1)
    | .inner ls lk lv ll lr =>
      if ls > delta * rs then match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
          if lrs < ratio * lls then
            (.inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r), 2)
          else
            (.inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
              (.inner (1 + rs + lrr.size) k v lrr r), 3)
        | .inner _ _ _ _ _, .leaf => (default, 0)
        | .leaf, _ => (default, 0)
      else (.inner (1 + ls + rs) k v l r, 1)

theorem balanceLF_fst (k : α) (v : β k) (l r : Impl α β) :
    (balanceLF k v l r).1 = Impl.balanceL! k v l r := by
  cases r with
  | leaf =>
    cases l with
    | leaf => rfl
    | inner ls lk lv ll lr => cases ll <;> cases lr <;> rfl
  | inner rs rk rv rl rr =>
    cases l with
    | leaf => rfl
    | inner ls lk lv ll lr =>
      unfold balanceLF Impl.balanceL!
      dsimp only
      by_cases h : ls > delta * rs
      · rw [ite_pos' h, ite_pos' h]
        cases ll with
        | leaf => rfl
        | inner lls llk llv lll llr =>
          cases lr with
          | leaf => rfl
          | inner lrs lrk lrv lrl lrr =>
            dsimp only
            by_cases h' : lrs < ratio * lls
            · rw [ite_pos' h', ite_pos' h']
            · rw [ite_neg' h', ite_neg' h']
      · rw [ite_neg' h, ite_neg' h]

theorem balanceLF_snd (k : α) (v : β k) (l r : Impl α β) : (balanceLF k v l r).2 ≤ 3 := by
  unfold balanceLF
  repeat' split
  all_goals exact Nat.le_of_ble_eq_true rfl

/-- The right balancing function of the library with the nodes it builds:
the equations of `Impl.balanceR!`. -/
def balanceRF (k : α) (v : β k) (l r : Impl α β) : Impl α β × Nat :=
  match l with
  | .leaf => match r with
    | .leaf => (.inner 1 k v .leaf .leaf, 1)
    | .inner _ _ _ .leaf .leaf => (.inner 2 k v .leaf r, 1)
    | .inner _ rk rv .leaf rr@(.inner _ _ _ _ _) =>
      (.inner 3 rk rv (.inner 1 k v .leaf .leaf) rr, 2)
    | .inner _ rk rv (.inner _ rlk rlv _ _) .leaf =>
      (.inner 3 rlk rlv (.inner 1 k v .leaf .leaf) (.inner 1 rk rv .leaf .leaf), 3)
    | .inner rs rk rv rl@(.inner rls _ _ _ _) rr@(.inner _ _ _ _ _) =>
      (.inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr, 2)
  | .inner ls _ _ _ _ => match r with
    | .leaf => (.inner (1 + ls) k v l .leaf, 1)
    | .inner rs rk rv rl rr =>
      if rs > delta * ls then match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
          if rls < ratio * rrs then
            (.inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr, 2)
          else
            (.inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
              (.inner (1 + rrs + rlr.size) rk rv rlr rr), 3)
        | .inner _ _ _ _ _, .leaf => (default, 0)
        | .leaf, _ => (default, 0)
      else (.inner (1 + ls + rs) k v l r, 1)

theorem balanceRF_fst (k : α) (v : β k) (l r : Impl α β) :
    (balanceRF k v l r).1 = Impl.balanceR! k v l r := by
  cases l with
  | leaf =>
    cases r with
    | leaf => rfl
    | inner rs rk rv rl rr => cases rl <;> cases rr <;> rfl
  | inner ls lk lv ll lr =>
    cases r with
    | leaf => rfl
    | inner rs rk rv rl rr =>
      unfold balanceRF Impl.balanceR!
      dsimp only
      by_cases h : rs > delta * ls
      · rw [ite_pos' h, ite_pos' h]
        cases rl with
        | leaf => rfl
        | inner rls rlk rlv rll rlr =>
          cases rr with
          | leaf => rfl
          | inner rrs rrk rrv rrl rrr =>
            dsimp only
            by_cases h' : rls < ratio * rrs
            · rw [ite_pos' h', ite_pos' h']
            · rw [ite_neg' h', ite_neg' h']
      · rw [ite_neg' h, ite_neg' h]

theorem balanceRF_snd (k : α) (v : β k) (l r : Impl α β) : (balanceRF k v l r).2 ≤ 3 := by
  unfold balanceRF
  repeat' split
  all_goals exact Nat.le_of_ble_eq_true rfl

/-- A balancing after a counted result on the left: the tree, and the
count with `c` and the nodes built added. -/
def balLl (k : α) (v : β k) (d : Impl α β × Nat) (r : Impl α β) (c : Nat) : Impl α β × Nat :=
  ((balanceLF k v d.1 r).1, d.2 + (c + (balanceLF k v d.1 r).2))

def balLr (k : α) (v : β k) (l : Impl α β) (d : Impl α β × Nat) (c : Nat) : Impl α β × Nat :=
  ((balanceLF k v l d.1).1, d.2 + (c + (balanceLF k v l d.1).2))

def balRl (k : α) (v : β k) (d : Impl α β × Nat) (r : Impl α β) (c : Nat) : Impl α β × Nat :=
  ((balanceRF k v d.1 r).1, d.2 + (c + (balanceRF k v d.1 r).2))

def balRr (k : α) (v : β k) (l : Impl α β) (d : Impl α β × Nat) (c : Nat) : Impl α β × Nat :=
  ((balanceRF k v l d.1).1, d.2 + (c + (balanceRF k v l d.1).2))

theorem balLl_fst (k : α) (v : β k) (d : Impl α β × Nat) (r : Impl α β) (c : Nat) :
    (balLl k v d r c).1 = Impl.balanceL! k v d.1 r := balanceLF_fst k v d.1 r

theorem balLr_fst (k : α) (v : β k) (l : Impl α β) (d : Impl α β × Nat) (c : Nat) :
    (balLr k v l d c).1 = Impl.balanceL! k v l d.1 := balanceLF_fst k v l d.1

theorem balRl_fst (k : α) (v : β k) (d : Impl α β × Nat) (r : Impl α β) (c : Nat) :
    (balRl k v d r c).1 = Impl.balanceR! k v d.1 r := balanceRF_fst k v d.1 r

theorem balRr_fst (k : α) (v : β k) (l : Impl α β) (d : Impl α β × Nat) (c : Nat) :
    (balRr k v l d c).1 = Impl.balanceR! k v l d.1 := balanceRF_fst k v l d.1

theorem balLl_snd (k : α) (v : β k) (d : Impl α β × Nat) (r : Impl α β) (c : Nat) :
    (balLl k v d r c).2 ≤ d.2 + c + 3 := by
  have h := balanceLF_snd k v d.1 r
  show d.2 + (c + (balanceLF k v d.1 r).2) ≤ d.2 + c + 3
  omega

theorem balLr_snd (k : α) (v : β k) (l : Impl α β) (d : Impl α β × Nat) (c : Nat) :
    (balLr k v l d c).2 ≤ d.2 + c + 3 := by
  have h := balanceLF_snd k v l d.1
  show d.2 + (c + (balanceLF k v l d.1).2) ≤ d.2 + c + 3
  omega

theorem balRl_snd (k : α) (v : β k) (d : Impl α β × Nat) (r : Impl α β) (c : Nat) :
    (balRl k v d r c).2 ≤ d.2 + c + 3 := by
  have h := balanceRF_snd k v d.1 r
  show d.2 + (c + (balanceRF k v d.1 r).2) ≤ d.2 + c + 3
  omega

theorem balRr_snd (k : α) (v : β k) (l : Impl α β) (d : Impl α β × Nat) (c : Nat) :
    (balRr k v l d c).2 ≤ d.2 + c + 3 := by
  have h := balanceRF_snd k v l d.1
  show d.2 + (c + (balanceRF k v l d.1).2) ≤ d.2 + c + 3
  omega

/-- **The lookup with everything counted**: one for each call, and for
each comparison of two keys what `w` says it reads. -/
def implGetF {δ : Type} [Ord α] (w : α → α → Nat) : Impl α (fun _ => δ) → α → Option δ × Nat
  | .leaf, _ => (none, 1)
  | .inner _ k' v' l r, k =>
    match compare k k' with
    | .lt => ((implGetF w l k).1, (implGetF w l k).2 + (1 + w k k'))
    | .gt => ((implGetF w r k).1, (implGetF w r k).2 + (1 + w k k'))
    | .eq => (some v', 1 + w k k')

theorem implGetF_fst {δ : Type} [Ord α] (w : α → α → Nat) (t : Impl α (fun _ => δ)) (k : α) :
    (implGetF w t k).1 = Impl.Const.get? t k := by
  induction t with
  | leaf => rw [Impl.Const.get?.eq_def] <;> rfl
  | inner sz k' v' l r ihl ihr =>
    rw [Impl.Const.get?.eq_def, implGetF]
    dsimp only
    cases compare k k' with
    | lt => exact ihl
    | gt => exact ihr
    | eq => rfl

theorem implGetF_snd {δ : Type} [Ord α] (w : α → α → Nat) (t : Impl α (fun _ => δ)) (k : α)
    {c : Nat} (hw : ∀ k', w k k' + 4 ≤ c) : (implGetF w t k).2 ≤ c * implDepth t + 2 := by
  induction t with
  | leaf => exact Nat.le_add_left _ _
  | inner sz k' v' l r ihl ihr =>
    have hm₁ := Nat.mul_le_mul_left c (Nat.le_max_left (implDepth l) (implDepth r))
    have hm₂ := Nat.mul_le_mul_left c (Nat.le_max_right (implDepth l) (implDepth r))
    have e : c * (max (implDepth l) (implDepth r) + 1) =
        c * max (implDepth l) (implDepth r) + c := Nat.mul_succ _ _
    have hk := hw k'
    rw [implGetF]
    show _ ≤ c * (max (implDepth l) (implDepth r) + 1) + 2
    rw [e]
    cases compare k k' with
    | lt =>
      show (implGetF w l k).2 + (1 + w k k') ≤ _
      omega
    | gt =>
      show (implGetF w r k).2 + (1 + w k k') ≤ _
      omega
    | eq =>
      show 1 + w k k' ≤ _
      omega

/-- **The insertion with everything counted**: calls, comparisons and the
nodes built, those of the balancing included. -/
def implInsertF [Ord α] (w : α → α → Nat) (k : α) (v : β k) : Impl α β → Impl α β × Nat
  | .leaf => (.inner 1 k v .leaf .leaf, 2)
  | .inner sz k' v' l r =>
    match compare k k' with
    | .lt => balLl k' v' (implInsertF w k v l) r (1 + w k k')
    | .gt => balRr k' v' l (implInsertF w k v r) (1 + w k k')
    | .eq => (.inner sz k v l r, 1 + w k k' + 1)

theorem implInsertF_fst [Ord α] (w : α → α → Nat) (k : α) (v : β k) (t : Impl α β) :
    (implInsertF w k v t).1 = Impl.insert! k v t := by
  induction t with
  | leaf => rw [Impl.insert!.eq_def] <;> rfl
  | inner sz k' v' l r ihl ihr =>
    rw [Impl.insert!.eq_def, implInsertF]
    dsimp only
    cases compare k k' with
    | lt =>
      show (balLl k' v' (implInsertF w k v l) r (1 + w k k')).1 = _
      rw [balLl_fst, ihl]
    | gt =>
      show (balRr k' v' l (implInsertF w k v r) (1 + w k k')).1 = _
      rw [balRr_fst, ihr]
    | eq => rfl

theorem implInsertF_snd [Ord α] (w : α → α → Nat) (k : α) (v : β k) (t : Impl α β)
    {c : Nat} (hw : ∀ k', w k k' + 4 ≤ c) : (implInsertF w k v t).2 ≤ c * implDepth t + 2 := by
  induction t with
  | leaf => exact Nat.le_add_left _ _
  | inner sz k' v' l r ihl ihr =>
    have hm₁ := Nat.mul_le_mul_left c (Nat.le_max_left (implDepth l) (implDepth r))
    have hm₂ := Nat.mul_le_mul_left c (Nat.le_max_right (implDepth l) (implDepth r))
    have e : c * (max (implDepth l) (implDepth r) + 1) =
        c * max (implDepth l) (implDepth r) + c := Nat.mul_succ _ _
    have hk := hw k'
    rw [implInsertF]
    show _ ≤ c * (max (implDepth l) (implDepth r) + 1) + 2
    rw [e]
    cases compare k k' with
    | lt =>
      have hb := balLl_snd k' v' (implInsertF w k v l) r (1 + w k k')
      show (balLl k' v' (implInsertF w k v l) r (1 + w k k')).2 ≤ _
      omega
    | gt =>
      have hb := balRr_snd k' v' l (implInsertF w k v r) (1 + w k k')
      show (balRr k' v' l (implInsertF w k v r) (1 + w k k')).2 ≤ _
      omega
    | eq =>
      show 1 + w k k' + 1 ≤ _
      omega

/-- Taking the least entry out, everything counted. -/
def implMinViewF : (k : α) → β k → Impl α β → Impl α β → Impl.RawView α β × Nat
  | k, v, .leaf, r => (⟨k, v, r⟩, 1)
  | k, v, .inner _ k' v' l' r', r =>
    (⟨(implMinViewF k' v' l' r').1.k, (implMinViewF k' v' l' r').1.v,
        (balanceRF k v (implMinViewF k' v' l' r').1.tree r).1⟩,
      (implMinViewF k' v' l' r').2 +
        (1 + (balanceRF k v (implMinViewF k' v' l' r').1.tree r).2))

theorem implMinViewF_fst (k : α) (v : β k) (l r : Impl α β) :
    (implMinViewF k v l r).1 = Impl.minView! k v l r := by
  induction l generalizing k v r with
  | leaf => rw [Impl.minView!.eq_def] <;> rfl
  | inner sz k' v' l' r' ihl ihr =>
    rw [Impl.minView!.eq_def, implMinViewF]
    dsimp only
    rw [balanceRF_fst, ihl k' v' r']

theorem implMinViewF_snd (k : α) (v : β k) (l r : Impl α β) :
    (implMinViewF k v l r).2 ≤ 4 * implDepth l + 1 := by
  induction l generalizing k v r with
  | leaf => exact Nat.le_add_left _ _
  | inner sz k' v' l' r' ihl ihr =>
    have h₁ := Nat.le_max_left (implDepth l') (implDepth r')
    have ih := ihl k' v' r'
    have hb := balanceRF_snd k v (implMinViewF k' v' l' r').1.tree r
    show (implMinViewF k' v' l' r').2 +
      (1 + (balanceRF k v (implMinViewF k' v' l' r').1.tree r).2) ≤
        4 * (max (implDepth l') (implDepth r') + 1) + 1
    omega

/-- Taking the greatest entry out, everything counted. -/
def implMaxViewF : (k : α) → β k → Impl α β → Impl α β → Impl.RawView α β × Nat
  | k, v, l, .leaf => (⟨k, v, l⟩, 1)
  | k, v, l, .inner _ k' v' l' r' =>
    (⟨(implMaxViewF k' v' l' r').1.k, (implMaxViewF k' v' l' r').1.v,
        (balanceLF k v l (implMaxViewF k' v' l' r').1.tree).1⟩,
      (implMaxViewF k' v' l' r').2 +
        (1 + (balanceLF k v l (implMaxViewF k' v' l' r').1.tree).2))

theorem implMaxViewF_fst (k : α) (v : β k) (l r : Impl α β) :
    (implMaxViewF k v l r).1 = Impl.maxView! k v l r := by
  induction r generalizing k v l with
  | leaf => rw [Impl.maxView!.eq_def] <;> rfl
  | inner sz k' v' l' r' ihl ihr =>
    rw [Impl.maxView!.eq_def, implMaxViewF]
    dsimp only
    rw [balanceLF_fst, ihr k' v' l']

theorem implMaxViewF_snd (k : α) (v : β k) (l r : Impl α β) :
    (implMaxViewF k v l r).2 ≤ 4 * implDepth r + 1 := by
  induction r generalizing k v l with
  | leaf => exact Nat.le_add_left _ _
  | inner sz k' v' l' r' ihl ihr =>
    have h₂ := Nat.le_max_right (implDepth l') (implDepth r')
    have ih := ihr k' v' l'
    have hb := balanceLF_snd k v l (implMaxViewF k' v' l' r').1.tree
    show (implMaxViewF k' v' l' r').2 +
      (1 + (balanceLF k v l (implMaxViewF k' v' l' r').1.tree).2) ≤
        4 * (max (implDepth l') (implDepth r') + 1) + 1
    omega

/-- Joining the two sides of a node taken out, everything counted. -/
def implGlueF (l r : Impl α β) : Impl α β × Nat :=
  match l with
  | .leaf => (r, 0)
  | .inner sz k v l' r' =>
    match r with
    | .leaf => (l, 0)
    | .inner sz' k' v' l'' r'' =>
      if sz < sz' then
        ((balanceLF (implMinViewF k' v' l'' r'').1.k (implMinViewF k' v' l'' r'').1.v l
            (implMinViewF k' v' l'' r'').1.tree).1,
          (implMinViewF k' v' l'' r'').2 +
            (balanceLF (implMinViewF k' v' l'' r'').1.k (implMinViewF k' v' l'' r'').1.v l
              (implMinViewF k' v' l'' r'').1.tree).2)
      else
        ((balanceRF (implMaxViewF k v l' r').1.k (implMaxViewF k v l' r').1.v
            (implMaxViewF k v l' r').1.tree r).1,
          (implMaxViewF k v l' r').2 +
            (balanceRF (implMaxViewF k v l' r').1.k (implMaxViewF k v l' r').1.v
              (implMaxViewF k v l' r').1.tree r).2)

theorem implGlueF_fst (l r : Impl α β) : (implGlueF l r).1 = l.glue! r := by
  cases l with
  | leaf => rw [Impl.glue!.eq_def] <;> rfl
  | inner sz k v l' r' =>
    cases r with
    | leaf => rw [Impl.glue!.eq_def] <;> rfl
    | inner sz' k' v' l'' r'' =>
      rw [Impl.glue!.eq_def]
      unfold implGlueF
      dsimp only
      by_cases h : sz < sz'
      · rw [ite_pos' h, ite_pos' h]
        show (balanceLF (implMinViewF k' v' l'' r'').1.k (implMinViewF k' v' l'' r'').1.v
          (Impl.inner sz k v l' r') (implMinViewF k' v' l'' r'').1.tree).1 = _
        rw [balanceLF_fst, implMinViewF_fst]
      · rw [ite_neg' h, ite_neg' h]
        show (balanceRF (implMaxViewF k v l' r').1.k (implMaxViewF k v l' r').1.v
          (implMaxViewF k v l' r').1.tree (Impl.inner sz' k' v' l'' r'')).1 = _
        rw [balanceRF_fst, implMaxViewF_fst]

theorem implGlueF_snd (l r : Impl α β) :
    (implGlueF l r).2 ≤ 4 * max (implDepth l) (implDepth r) := by
  cases l with
  | leaf => exact Nat.zero_le _
  | inner sz k v l' r' =>
    cases r with
    | leaf => exact Nat.zero_le _
    | inner sz' k' v' l'' r'' =>
      have h₁ := Nat.le_max_left (implDepth (Impl.inner sz k v l' r'))
        (implDepth (Impl.inner sz' k' v' l'' r''))
      have h₂ := Nat.le_max_right (implDepth (Impl.inner sz k v l' r'))
        (implDepth (Impl.inner sz' k' v' l'' r''))
      have e₁ : implDepth (Impl.inner sz k v l' r') = max (implDepth l') (implDepth r') + 1 := rfl
      have e₂ : implDepth (Impl.inner sz' k' v' l'' r'') =
          max (implDepth l'') (implDepth r'') + 1 := rfl
      have m₁ := Nat.le_max_right (implDepth l') (implDepth r')
      have m₂ := Nat.le_max_left (implDepth l'') (implDepth r'')
      have s₁ := implMinViewF_snd k' v' l'' r''
      have s₂ := implMaxViewF_snd k v l' r'
      have b₁ := balanceLF_snd (implMinViewF k' v' l'' r'').1.k (implMinViewF k' v' l'' r'').1.v
        (Impl.inner sz k v l' r') (implMinViewF k' v' l'' r'').1.tree
      have b₂ := balanceRF_snd (implMaxViewF k v l' r').1.k (implMaxViewF k v l' r').1.v
        (implMaxViewF k v l' r').1.tree (Impl.inner sz' k' v' l'' r'')
      unfold implGlueF
      dsimp only
      by_cases h : sz < sz'
      · rw [ite_pos' h]
        show (implMinViewF k' v' l'' r'').2 +
          (balanceLF (implMinViewF k' v' l'' r'').1.k (implMinViewF k' v' l'' r'').1.v
            (Impl.inner sz k v l' r') (implMinViewF k' v' l'' r'').1.tree).2 ≤ _
        omega
      · rw [ite_neg' h]
        show (implMaxViewF k v l' r').2 +
          (balanceRF (implMaxViewF k v l' r').1.k (implMaxViewF k v l' r').1.v
            (implMaxViewF k v l' r').1.tree (Impl.inner sz' k' v' l'' r'')).2 ≤ _
        omega

/-- **The erasure with everything counted.** -/
def implEraseF [Ord α] (w : α → α → Nat) (k : α) : Impl α β → Impl α β × Nat
  | .leaf => (.leaf, 1)
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => balRl k' v' (implEraseF w k l) r (1 + w k k')
    | .gt => balLr k' v' l (implEraseF w k r) (1 + w k k')
    | .eq => ((implGlueF l r).1, (implGlueF l r).2 + (1 + w k k'))

theorem implEraseF_fst [Ord α] (w : α → α → Nat) (k : α) (t : Impl α β) :
    (implEraseF w k t).1 = Impl.erase! k t := by
  induction t with
  | leaf => rw [Impl.erase!.eq_def] <;> rfl
  | inner sz k' v' l r ihl ihr =>
    rw [Impl.erase!.eq_def, implEraseF]
    dsimp only
    cases compare k k' with
    | lt =>
      show (balRl k' v' (implEraseF w k l) r (1 + w k k')).1 = _
      rw [balRl_fst, ihl]
    | gt =>
      show (balLr k' v' l (implEraseF w k r) (1 + w k k')).1 = _
      rw [balLr_fst, ihr]
    | eq => exact implGlueF_fst l r

theorem implEraseF_snd [Ord α] (w : α → α → Nat) (k : α) (t : Impl α β)
    {c : Nat} (hw : ∀ k', w k k' + 4 ≤ c) : (implEraseF w k t).2 ≤ c * implDepth t + 2 := by
  induction t with
  | leaf => exact Nat.le_add_left _ _
  | inner sz k' v' l r ihl ihr =>
    have hm₁ := Nat.mul_le_mul_left c (Nat.le_max_left (implDepth l) (implDepth r))
    have hm₂ := Nat.mul_le_mul_left c (Nat.le_max_right (implDepth l) (implDepth r))
    have e : c * (max (implDepth l) (implDepth r) + 1) =
        c * max (implDepth l) (implDepth r) + c := Nat.mul_succ _ _
    have hk := hw k'
    have h4 : 4 * max (implDepth l) (implDepth r) ≤ c * max (implDepth l) (implDepth r) :=
      Nat.mul_le_mul_right _ (by omega)
    have hg := implGlueF_snd l r
    rw [implEraseF]
    show _ ≤ c * (max (implDepth l) (implDepth r) + 1) + 2
    rw [e]
    cases compare k k' with
    | lt =>
      have hb := balRl_snd k' v' (implEraseF w k l) r (1 + w k k')
      show (balRl k' v' (implEraseF w k l) r (1 + w k k')).2 ≤ _
      omega
    | gt =>
      have hb := balLr_snd k' v' l (implEraseF w k r) (1 + w k k')
      show (balLr k' v' l (implEraseF w k r) (1 + w k k')).2 ≤ _
      omega
    | eq =>
      show (implGlueF l r).2 + (1 + w k k') ≤ _
      omega

end FullCount

/-- **The comparison of two names with the cells it reads**: the
equations of the order of lists, and one for each call. -/
def cmpC : List Nat → List Nat → Ordering × Nat
  | [], [] => (.eq, 1)
  | [], _ :: _ => (.lt, 1)
  | _ :: _, [] => (.gt, 1)
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => (.lt, 1)
    | .eq => ((cmpC xs ys).1, (cmpC xs ys).2 + 1)
    | .gt => (.gt, 1)

/-- It is the comparison of the library. -/
theorem cmpC_fst : ∀ a b : List Nat, (cmpC a b).1 = compare a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    have e : compare (x :: xs) (y :: ys) =
        match compare x y with
        | .lt => .lt
        | .eq => compare xs ys
        | .gt => .gt := rfl
    rw [e, cmpC]
    have ih := cmpC_fst xs ys
    cases compare x y with
    | lt => rfl
    | eq => exact ih
    | gt => rfl

/-- **A comparison reads no more cells than the first name has, and
one.** -/
theorem cmpC_snd : ∀ a b : List Nat, (cmpC a b).2 ≤ a.length + 1
  | [], [] => Nat.le_refl _
  | [], _ :: _ => Nat.le_refl _
  | _ :: _, [] => Nat.le_add_left _ _
  | x :: xs, y :: ys => by
    have ih := cmpC_snd xs ys
    rw [cmpC]
    show _ ≤ xs.length + 1 + 1
    cases compare x y with
    | lt => exact Nat.le_add_left _ _
    | eq =>
      show (cmpC xs ys).2 + 1 ≤ _
      omega
    | gt => exact Nat.le_add_left _ _

section FullMaps

open Std.DTreeMap.Internal

variable {V : Type}

/-- What a comparison of two numbers reads: one. -/
def natW : Nat → Nat → Nat := fun _ _ => 1

/-- What a comparison of two names reads: the cells that `cmpC` counts. -/
def nameW (a b : List Nat) : Nat := (cmpC a b).2

/-- The lookup in a map keyed by numbers, everything counted. -/
def tgetF (t : Std.TreeMap Nat V) (k : Nat) : Option V × Nat := implGetF natW t.inner.inner k

/-- The insertion in a map keyed by numbers, everything counted. -/
def tinsertF (t : Std.TreeMap Nat V) (k : Nat) (v : V) : Impl Nat (fun _ => V) × Nat :=
  implInsertF natW k v t.inner.inner

/-- The erasure in a map keyed by numbers, everything counted. -/
def teraseF (t : Std.TreeMap Nat V) (k : Nat) : Impl Nat (fun _ => V) × Nat :=
  implEraseF natW k t.inner.inner

/-- The lookup of a name, everything counted. -/
def ngetF (t : Std.TreeMap (List Nat) V) (k : List Nat) : Option V × Nat :=
  implGetF nameW t.inner.inner k

/-- The insertion at a name, everything counted. -/
def ninsertF (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    Impl (List Nat) (fun _ => V) × Nat :=
  implInsertF nameW k v t.inner.inner

/-- The erasure at a name, everything counted. -/
def neraseF (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    Impl (List Nat) (fun _ => V) × Nat :=
  implEraseF nameW k t.inner.inner

/-- **The fully counted operations are those of the library.** -/
theorem tgetF_fst (t : Std.TreeMap Nat V) (k : Nat) : (tgetF t k).1 = t[k]? :=
  implGetF_fst natW t.inner.inner k

theorem tinsertF_fst (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (tinsertF t k v).1 = (t.insert k v).inner.inner := by
  show (implInsertF natW k v t.inner.inner).1 =
    (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl
  rw [implInsertF_fst, Impl.insert_eq_insert!]

theorem teraseF_fst (t : Std.TreeMap Nat V) (k : Nat) :
    (teraseF t k).1 = (t.erase k).inner.inner := by
  show (implEraseF natW k t.inner.inner).1 =
    (Impl.erase k t.inner.inner t.inner.wf.balanced).impl
  rw [implEraseF_fst, Impl.erase_eq_erase!]

theorem ngetF_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) : (ngetF t k).1 = t[k]? :=
  implGetF_fst nameW t.inner.inner k

theorem ninsertF_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    (ninsertF t k v).1 = (t.insert k v).inner.inner := by
  show (implInsertF nameW k v t.inner.inner).1 =
    (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl
  rw [implInsertF_fst, Impl.insert_eq_insert!]

theorem neraseF_fst (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (neraseF t k).1 = (t.erase k).inner.inner := by
  show (implEraseF nameW k t.inner.inner).1 =
    (Impl.erase k t.inner.inner t.inner.wf.balanced).impl
  rw [implEraseF_fst, Impl.erase_eq_erase!]

/-- **On numbers an operation costs at most five for each level of the
tree, and two**: a call, a comparison and three nodes at most. -/
theorem tgetF_snd (t : Std.TreeMap Nat V) (k : Nat) : (tgetF t k).2 ≤ 5 * tdepth t + 2 :=
  implGetF_snd natW t.inner.inner k (fun _ => Nat.le_refl _)

theorem tinsertF_snd (t : Std.TreeMap Nat V) (k : Nat) (v : V) :
    (tinsertF t k v).2 ≤ 5 * tdepth t + 2 :=
  implInsertF_snd (β := fun _ => V) natW k v t.inner.inner (fun _ => Nat.le_refl _)

theorem teraseF_snd (t : Std.TreeMap Nat V) (k : Nat) : (teraseF t k).2 ≤ 5 * tdepth t + 2 :=
  implEraseF_snd natW k t.inner.inner (fun _ => Nat.le_refl _)

theorem nameW_le (k k' : List Nat) : nameW k k' + 4 ≤ k.length + 5 := by
  have h := cmpC_snd k k'
  show (cmpC k k').2 + 4 ≤ k.length + 5
  omega

/-- **On names an operation costs at most the length of the name and five
for each level of the tree, and two.** -/
theorem ngetF_snd (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (ngetF t k).2 ≤ (k.length + 5) * ndepth t + 2 :=
  implGetF_snd nameW t.inner.inner k (nameW_le k)

theorem ninsertF_snd (t : Std.TreeMap (List Nat) V) (k : List Nat) (v : V) :
    (ninsertF t k v).2 ≤ (k.length + 5) * ndepth t + 2 :=
  implInsertF_snd (β := fun _ => V) nameW k v t.inner.inner (nameW_le k)

theorem neraseF_snd (t : Std.TreeMap (List Nat) V) (k : List Nat) :
    (neraseF t k).2 ≤ (k.length + 5) * ndepth t + 2 :=
  implEraseF_snd nameW k t.inner.inner (nameW_le k)

end FullMaps

section FullCost

variable [DecidableEq S] {xs : XSys S}

/-- Looking a name up, everything counted. -/
def OMem.symF (O : OMem S) (i : Id) : Nat := (ngetF O.live i).2

/-- Looking the neighbours of a port up, everything counted. -/
def OMem.nbF (O : OMem S) (p : Port) : Nat := (ngetF O.nbrs (portKey p)).2

/-- Taking an agent out, everything counted. -/
def OMem.takeF (O : OMem S) (a : Id) : Nat :=
  match O.live[a]? with
  | some v => (teraseF O.cells v.1).2 + (neraseF O.live a).2
  | none => 0

/-- Writing an agent, everything counted. -/
def OMem.putF (O : OMem S) (i : Id) (γ : S) : Nat :=
  (tinsertF O.cells O.stamp (i, γ)).2 + (ninsertF O.live i (O.stamp, γ)).2

/-- Writing a segment, everything counted. -/
def OMem.linkF (O : OMem S) (p q : Port) : Nat :=
  O.nbF p + (ninsertF O.nbrs (portKey p) (pushNb q (O.nb p))).2

/-- **What an action costs on ordered maps alone, everything counted.**
As `OMach.ccost`, but an operation on a map is charged every call it
makes, every cell that a comparison of two keys reads, and every node it
builds, those of the balancing included. -/
def OMach.fcost (xs : XSys S) (O : OMem S) (T : TThread S) : Nat :=
  match T.st with
  | .idle =>
    match (tmaxC T.todo).1 with
    | none => 0
    | some s =>
      match T.todo[s]? with
      | some e =>
        1 + ((tmaxC T.todo).2 + (tgetF T.todo s).2 + (teraseF T.todo s).2) + O.symF e.1
      | none => 1 + ((tmaxC T.todo).2 + (tgetF T.todo s).2)
  | .look a _ => 2 + O.nbF (a, 0)
  | .seek _ _ p c =>
    if c.2 = 0 then
      1 + O.symF c.1 + if (O.sym c.1).isSome then 0 else O.nbF c + findCells p (O.nb c)
    else 1 + O.nbF c + findCells p (O.nb c)
  | .ready a _ α _ => 1 + O.symF a + if O.sym a = some α then O.takeF a else 0
  | .half a b α β =>
    1 + O.symF b + if O.sym b = some β ∧ a ≠ b then
        match xs.rule α β with
        | some R =>
          O.takeF b + (R.newAgents a b).length + (R.newLinks xs.sys.ar a b α β).length
        | none => O.putF a α
      else O.putF a α
  | .write ((i, γ) :: _) _ => 1 + O.putF i γ
  | .write [] ((p, q) :: _) => 4 + O.linkF p q
  | .write [] [] => 1

/-- What the action of thread `t` costs, everything counted. -/
def OMach.stepFcost (xs : XSys S) (M : OMach S) (t : Nat) : Nat :=
  match M.ths[t]? with
  | some T => OMach.fcost xs M.mem T
  | none => 0

/-- **The running time on ordered maps alone, everything counted.** -/
def OMach.ftime (xs : XSys S) (σ : Nat → Nat) (M : OMach S) : Nat → Nat
  | 0 => 0
  | i + 1 => OMach.ftime xs σ M i + (M.trace xs σ i).1.stepFcost xs (σ i)

theorem OMach.stepFcost_rest (xs : XSys S) {M : OMach S} (h : M.resting = true) (t : Nat) :
    M.stepFcost xs t = 0 := by
  unfold OMach.stepFcost
  cases hT : M.ths[t]? with
  | none => rfl
  | some T =>
    obtain ⟨todo, rfl, hmax⟩ := OMach.rest_thread h hT
    show OMach.fcost xs M.mem ⟨todo, .idle⟩ = 0
    unfold OMach.fcost
    dsimp only
    rw [hmax]

/-- Once the program is at rest this time too stays what it is. -/
theorem OMach.ftime_rest (σ : Nat → Nat) {M : OMach S} {B : Nat}
    (h : (M.trace xs σ B).1.resting = true) : ∀ d, M.ftime xs σ (B + d) = M.ftime xs σ B
  | 0 => rfl
  | d + 1 => by
    have z : (M.trace xs σ (B + d)).1.stepFcost xs (σ (B + d)) = 0 := by
      rw [OMach.trace_rest σ h d]
      exact OMach.stepFcost_rest xs h _
    show M.ftime xs σ (B + d) + (M.trace xs σ (B + d)).1.stepFcost xs (σ (B + d)) = _
    rw [z, Nat.add_zero]
    exact OMach.ftime_rest σ h d

end FullCost

/-- A count that is `c` for each level and two, on a tree of depth under
`Dm`, with `c` at most `L`, is at most `L * Dm`. -/
theorem op_le {x c d Dm L : Nat} (hx : x ≤ c * d + 2) (hc : 2 ≤ c) (hd : d + 1 ≤ Dm)
    (hL : c ≤ L) : x ≤ L * Dm := by
  have h₁ : c * (d + 1) = c * d + c := Nat.mul_succ c d
  have h₂ := Nat.mul_le_mul_left c hd
  have h₃ := Nat.mul_le_mul_right Dm hL
  omega

section Names

variable [DecidableEq S] {xs : XSys S}

/-- **Every name in the memory has at most `L` cells.** -/
def XNet.NamesLe (X : XNet S) (L : Nat) : Prop :=
  (∀ e ∈ X.agents, e.1.length ≤ L) ∧ ∀ e ∈ X.wires, e.1.1.length ≤ L ∧ e.2.1.length ≤ L

/-- Every name a thread has in hand has at most `L` cells. -/
def TState.NamesLe : TState S → Nat → Prop
  | .idle, _ => True
  | .look a _, L => a.length ≤ L
  | .seek a _ p c, L => a.length ≤ L ∧ p.1.length ≤ L ∧ c.1.length ≤ L
  | .ready a b _ _, L => a.length ≤ L ∧ b.length ≤ L
  | .half a b _ _, L => a.length ≤ L ∧ b.length ≤ L
  | .write as ls, L =>
    (∀ e ∈ as, e.1.length ≤ L) ∧ ∀ e ∈ ls, e.1.1.length ≤ L ∧ e.2.1.length ≤ L

/-- Every name of a thread has at most `L` cells. -/
def XThread.NamesLe (T : XThread S) (L : Nat) : Prop :=
  (∀ e ∈ T.todo, e.1.length ≤ L) ∧ T.st.NamesLe L

omit [DecidableEq S] in
theorem XNet.NamesLe.mono {X : XNet S} {L L' : Nat} (h : X.NamesLe L) (hl : L ≤ L') :
    X.NamesLe L' :=
  ⟨fun e he => Nat.le_trans (h.1 e he) hl,
    fun e he => ⟨Nat.le_trans (h.2 e he).1 hl, Nat.le_trans (h.2 e he).2 hl⟩⟩

omit [DecidableEq S] in
theorem TState.NamesLe.mono {s : TState S} {L L' : Nat} (h : s.NamesLe L) (hl : L ≤ L') :
    s.NamesLe L' := by
  cases s with
  | idle => trivial
  | look a α => exact Nat.le_trans h hl
  | seek a α p c => exact ⟨Nat.le_trans h.1 hl, Nat.le_trans h.2.1 hl, Nat.le_trans h.2.2 hl⟩
  | ready a b α β => exact ⟨Nat.le_trans h.1 hl, Nat.le_trans h.2 hl⟩
  | half a b α β => exact ⟨Nat.le_trans h.1 hl, Nat.le_trans h.2 hl⟩
  | write as ls =>
    exact ⟨fun e he => Nat.le_trans (h.1 e he) hl,
      fun e he => ⟨Nat.le_trans (h.2 e he).1 hl, Nat.le_trans (h.2 e he).2 hl⟩⟩

omit [DecidableEq S] in
theorem XThread.NamesLe.mono {T : XThread S} {L L' : Nat} (h : T.NamesLe L) (hl : L ≤ L') :
    T.NamesLe L' :=
  ⟨fun e he => Nat.le_trans (h.1 e he) hl, h.2.mono hl⟩

omit [DecidableEq S] in
theorem XNet.NamesLe.take {X : XNet S} {L : Nat} (h : X.NamesLe L) (a : Id) :
    (X.takeAgent a).NamesLe L :=
  ⟨fun e he => h.1 e (List.mem_filter.1 he).1, h.2⟩

omit [DecidableEq S] in
theorem XNet.NamesLe.put {X : XNet S} {L : Nat} (h : X.NamesLe L) {i : Id}
    (hi : i.length ≤ L) (γ : S) : (X.putAgent i γ).NamesLe L := by
  refine ⟨fun e he => ?_, h.2⟩
  have he' : e ∈ (i, γ) :: X.agents := he
  rcases List.mem_cons.1 he' with rfl | he''
  · exact hi
  · exact h.1 e he''

omit [DecidableEq S] in
theorem XNet.NamesLe.link {X : XNet S} {L : Nat} (h : X.NamesLe L) {p q : Port}
    (hp : p.1.length ≤ L) (hq : q.1.length ≤ L) : (X.putLink p q).NamesLe L := by
  refine ⟨h.1, fun e he => ?_⟩
  have he' : e ∈ (p, q) :: X.wires := he
  rcases List.mem_cons.1 he' with rfl | he''
  · exact ⟨hp, hq⟩
  · exact h.2 e he''

/-- A new agent is named by one cell before the name of one of the two
that fire. -/
theorem child_length {a b : Id} {L : Nat} (ha : a.length ≤ L) (hb : b.length ≤ L)
    (o : Option Bool) (j : Nat) : (child a b o j).length ≤ L + 1 := by
  show (par a b o).length + 1 ≤ L + 1
  rcases par_eq a b o with e | e <;> rw [e] <;> omega

theorem emb_length {a b : Id} {L : Nat} (ha : a.length ≤ L) (hb : b.length ≤ L)
    (x : LPort) : (emb a b x).1.length ≤ L + 1 := by
  cases x with
  | ifc s k =>
    show (sel a b s).length ≤ L + 1
    cases s
    · exact Nat.le_trans ha (Nat.le_add_right _ _)
    · exact Nat.le_trans hb (Nat.le_add_right _ _)
  | new o j k => exact child_length ha hb o j

/-- **An action lengthens the names by one cell at most, and only when it
claims.** -/
theorem XMach.act_names (xs : XSys S) {X : XNet S} {T : XThread S} {L : Nat}
    (hX : X.NamesLe L) (hT : T.NamesLe L) :
    (XMach.act xs X T).1.NamesLe (L + (XMach.act xs X T).2.2) ∧
      (XMach.act xs X T).2.1.NamesLe (L + (XMach.act xs X T).2.2) := by
  obtain ⟨todo, st⟩ := T
  obtain ⟨hTd, hTs⟩ := hT
  cases st with
  | idle =>
    cases todo with
    | nil => exact ⟨hX, hTd, trivial⟩
    | cons e rest =>
      cases hact : XMach.act xs X ⟨e :: rest, .idle⟩ with
      | mk X' r =>
        obtain ⟨T', k⟩ := r
        unfold XMach.act at hact
        dsimp only at hact
        have hr : ∀ x ∈ rest, x.1.length ≤ L := fun x hx => hTd x (List.mem_cons_of_mem _ hx)
        split at hact
        · cases hact
          exact ⟨hX, hr, hTd e List.mem_cons_self⟩
        · cases hact
          exact ⟨hX, hr, trivial⟩
  | look a α =>
    have ha : a.length ≤ L := hTs
    cases hact : XMach.act xs X ⟨todo, .look a α⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · rename_i q hq
        cases hact
        exact ⟨hX, hTd, ha, ha, (hX.2 _ (assoc_mem hq)).2⟩
      · cases hact
        exact ⟨hX, hTd, trivial⟩
  | seek a α p c =>
    obtain ⟨ha, hp, hc⟩ : a.length ≤ L ∧ p.1.length ≤ L ∧ c.1.length ≤ L := hTs
    cases hact : XMach.act xs X ⟨todo, .seek a α p c⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · split at hact
        · cases hact
          exact ⟨hX, hTd, ha, hc⟩
        · cases hact
          exact ⟨hX, hTd, trivial⟩
      · split at hact
        · rename_i q hq
          cases hact
          exact ⟨hX, hTd, ha, hc, (hX.2 _ (nextSeg_spec hq).1).2⟩
        · cases hact
          exact ⟨hX, hTd, trivial⟩
  | ready a b α β =>
    obtain ⟨ha, hb⟩ : a.length ≤ L ∧ b.length ≤ L := hTs
    cases hact : XMach.act xs X ⟨todo, .ready a b α β⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · cases hact
        exact ⟨hX.take a, hTd, ha, hb⟩
      · cases hact
        exact ⟨hX, hTd, trivial⟩
  | half a b α β =>
    obtain ⟨ha, hb⟩ : a.length ≤ L ∧ b.length ≤ L := hTs
    cases hact : XMach.act xs X ⟨todo, .half a b α β⟩ with
    | mk X' r =>
      obtain ⟨T', k⟩ := r
      unfold XMach.act at hact
      dsimp only at hact
      split at hact
      · rename_i R hR
        cases hact
        by_cases hc : assoc b X.agents = some β ∧ a ≠ b
        · rw [ite_pos' hc] at hR
          obtain ⟨-, hW⟩ := xs.writes hc.2 hR
          refine ⟨(hX.take b).mono (Nat.le_add_right L 1),
            fun e he => Nat.le_trans (hTd e he) (Nat.le_add_right L 1), fun e he => ?_,
            fun e he => ?_⟩
          · obtain ⟨i, γ⟩ := e
            obtain ⟨o, j, rfl, -⟩ := hW.agent.1 he
            exact child_length ha hb o j
          · obtain ⟨p, q⟩ := e
            obtain ⟨x, y, -, rfl, rfl⟩ := hW.link.1 he
            exact ⟨emb_length ha hb x, emb_length ha hb y⟩
        · rw [ite_neg' hc] at hR
          cases hR
      · cases hact
        exact ⟨hX.put ha α, hTd, trivial⟩
  | write as ls =>
    obtain ⟨has, hls⟩ : (∀ e ∈ as, e.1.length ≤ L) ∧
        ∀ e ∈ ls, e.1.1.length ≤ L ∧ e.2.1.length ≤ L := hTs
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      exact ⟨hX.put (has (i, γ) List.mem_cons_self) γ, hTd,
        fun x hx => has x (List.mem_cons_of_mem _ hx), hls⟩
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have h := hls (p, q) List.mem_cons_self
        exact ⟨hX.link h.1 h.2, hTd, has, fun x hx => hls x (List.mem_cons_of_mem _ hx)⟩
      | nil => exact ⟨hX, hX.1, trivial⟩

/-- Every name of the program has at most `L` cells. -/
def XMach.NamesLe (M : XMach S) (L : Nat) : Prop :=
  M.mem.NamesLe L ∧ ∀ T ∈ M.ths, T.NamesLe L

theorem XMach.step_names (xs : XSys S) {M : XMach S} {L : Nat} (h : M.NamesLe L) (t : Nat) :
    (M.step xs t).1.NamesLe (L + (M.step xs t).2) := by
  unfold XMach.step
  cases hT : M.ths[t]? with
  | none => exact h
  | some T =>
    obtain ⟨a, b⟩ := XMach.act_names xs h.1 (h.2 T (List.mem_of_getElem? hT))
    refine ⟨a, fun T' hT' => ?_⟩
    have hT'' : T' ∈ M.ths.set t (XMach.act xs M.mem T).2.1 := hT'
    rcases List.mem_or_eq_of_mem_set hT'' with hm | rfl
    · exact (h.2 T' hm).mono (Nat.le_add_right _ _)
    · exact b

theorem XMach.trace_names (σ : Nat → Nat) {M : XMach S} {L : Nat} (h : M.NamesLe L) :
    ∀ i, (M.trace xs σ i).1.NamesLe (L + (M.trace xs σ i).2)
  | 0 => h
  | i + 1 => by
    have ih := XMach.trace_names σ h i
    have hs := XMach.step_names xs ih (σ i)
    show ((M.trace xs σ i).1.step xs (σ i)).1.NamesLe
      (L + ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2))
    rw [← Nat.add_assoc]
    exact hs

omit [DecidableEq S] in
theorem XMach.init_names {X : XNet S} {L : Nat} (hX : X.NamesLe L) (nt : Nat) :
    (XMach.init X nt).NamesLe L := by
  refine ⟨hX, fun T hT => ?_⟩
  have hT' : T ∈ (List.range nt).map fun t =>
      (⟨X.agents.drop t ++ X.agents.take t, .idle⟩ : XThread S) := hT
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT'
  refine ⟨fun e he => ?_, trivial⟩
  have he' : e ∈ X.agents.drop t ++ X.agents.take t := he
  rcases List.mem_append.1 he' with h | h
  · exact hX.1 e (List.mem_of_mem_drop h)
  · exact hX.1 e (List.mem_of_mem_take h)

/-- **Along a run no name grows beyond the longest of the net by more
cells than there are interactions.** -/
theorem XMach.names_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {L : Nat}
    (hL : X.NamesLe L) (nt : Nat) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (i : Nat) : ((XMach.init X nt).trace xs σ i).1.NamesLe (L + n) := by
  have run : MRun xs.sys ((XMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((XMach.init X nt).trace xs σ i).1.toMach := by
    have h := XMach.trace_run xs σ (XMach.init X nt) i
    rw [XMach.init_toMach] at h
    exact h
  have bound : ((XMach.init X nt).trace xs σ i).2 ≤ n := run.claims_le hX hs hn
  have h := XMach.trace_names (xs := xs) σ (XMach.init_names hL nt) i
  exact ⟨h.1.mono (by omega), fun T hT => (h.2 T hT).mono (by omega)⟩

/-- **Everything counted, an action costs the size of a rule, four, and
four operations**, each at most `L + 6` for each level of a tree under
`Dm` deep, when no name the thread has in hand is longer than `L`. -/
theorem OMach.fcost_le {C D : Nat} (hb : xs.Bounded C D) (O : OMem S) (T : TThread S)
    {Dm L : Nat} (hc : tdepth O.cells + 1 ≤ Dm) (hl : ndepth O.live + 1 ≤ Dm)
    (hn : ndepth O.nbrs + 1 ≤ Dm) (ht : tdepth T.todo + 1 ≤ Dm)
    (hf : ∀ p c, findCells p (O.nb c) ≤ 2) (hN : T.toX.NamesLe L) :
    OMach.fcost xs O T ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * T.toX.busy := by
  have hD : Dm ≤ (L + 6) * Dm := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have symB : ∀ i : Id, i.length ≤ L → O.symF i ≤ (L + 6) * Dm := fun i hi =>
    op_le (ngetF_snd O.live i) (by omega) hl (by omega)
  have nbB : ∀ p : Port, p.1.length ≤ L → O.nbF p ≤ (L + 6) * Dm := fun p hp =>
    op_le (ngetF_snd O.nbrs (portKey p)) (by omega)
      hn (by show (p.2 :: p.1).length + 5 ≤ L + 6; show p.1.length + 1 + 5 ≤ L + 6; omega)
  have takeB : ∀ a : Id, a.length ≤ L → O.takeF a ≤ 2 * ((L + 6) * Dm) := by
    intro a ha
    unfold OMem.takeF
    cases O.live[a]? with
    | none => exact Nat.zero_le _
    | some v =>
      have h₁ := op_le (L := L + 6) (teraseF_snd O.cells v.1) (by omega) hc (by omega)
      have h₂ := op_le (L := L + 6) (neraseF_snd O.live a) (by omega) hl (by omega)
      show (teraseF O.cells v.1).2 + (neraseF O.live a).2 ≤ 2 * ((L + 6) * Dm)
      omega
  have putB : ∀ (i : Id) (γ : S), i.length ≤ L → O.putF i γ ≤ 2 * ((L + 6) * Dm) := by
    intro i γ hi
    have h₁ := op_le (L := L + 6) (tinsertF_snd O.cells O.stamp (i, γ)) (by omega) hc
      (by omega)
    have h₂ := op_le (L := L + 6) (ninsertF_snd O.live i (O.stamp, γ)) (by omega) hl
      (by omega)
    show (tinsertF O.cells O.stamp (i, γ)).2 + (ninsertF O.live i (O.stamp, γ)).2 ≤
      2 * ((L + 6) * Dm)
    omega
  have linkB : ∀ p q : Port, p.1.length ≤ L → O.linkF p q ≤ 2 * ((L + 6) * Dm) := by
    intro p q hp
    have h₁ := nbB p hp
    have h₂ := op_le (L := L + 6)
      (ninsertF_snd O.nbrs (portKey p) (pushNb q (O.nb p))) (by omega) hn
      (by show (p.2 :: p.1).length + 5 ≤ L + 6; show p.1.length + 1 + 5 ≤ L + 6; omega)
    show O.nbF p + (ninsertF O.nbrs (portKey p) (pushNb q (O.nb p))).2 ≤ 2 * ((L + 6) * Dm)
    omega
  obtain ⟨todo, s⟩ := T
  have ht' : tdepth todo + 1 ≤ Dm := ht
  obtain ⟨hNd, hNs⟩ := hN
  cases s with
  | idle =>
    cases hmax : (tmaxC todo).1 with
    | none =>
      have e : OMach.fcost xs O ⟨todo, .idle⟩ = 0 := by
        unfold OMach.fcost
        dsimp only
        rw [hmax]
      rw [e]
      exact Nat.zero_le _
    | some s =>
      have hmax' : todo.maxKey? = some s := by rw [← tmaxC_fst, hmax]
      obtain ⟨v, -, hlst⟩ := treeList_max todo hmax'
      have eb : (TThread.toX (⟨todo, .idle⟩ : TThread S)).busy = 1 := by
        show XThread.busy ⟨treeList todo, .idle⟩ = 1
        rw [hlst]
        rfl
      have h₁ := tmaxC_snd todo
      have h₂ := op_le (L := L + 6) (tgetF_snd todo s) (by omega) ht' (by omega)
      have h₃ := op_le (L := L + 6) (teraseF_snd todo s) (by omega) ht' (by omega)
      have e : OMach.fcost xs O ⟨todo, .idle⟩ =
          match todo[s]? with
          | some e =>
            1 + ((tmaxC todo).2 + (tgetF todo s).2 + (teraseF todo s).2) + O.symF e.1
          | none => 1 + ((tmaxC todo).2 + (tgetF todo s).2) := by
        unfold OMach.fcost
        dsimp only
        rw [hmax] <;> rfl
      rw [e, eb]
      cases hg : todo[s]? with
      | none =>
        show 1 + ((tmaxC todo).2 + (tgetF todo s).2) ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
        omega
      | some e =>
        have h₄ := symB e.1 (hNd e ((mem_treeList todo e).2 ⟨s, hg⟩))
        show 1 + ((tmaxC todo).2 + (tgetF todo s).2 + (teraseF todo s).2) + O.symF e.1 ≤
          (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
        omega
  | look a α =>
    have ha : a.length ≤ L := hNs
    have h₁ := nbB (a, 0) ha
    show 2 + O.nbF (a, 0) ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
    omega
  | seek a α p c =>
    obtain ⟨-, -, hc'⟩ : a.length ≤ L ∧ p.1.length ≤ L ∧ c.1.length ≤ L := hNs
    have h₁ := symB c.1 hc'
    have h₂ := nbB c hc'
    have h₃ := hf p c
    show (if c.2 = 0 then
        1 + O.symF c.1 + (if (O.sym c.1).isSome then 0 else O.nbF c + findCells p (O.nb c))
      else 1 + O.nbF c + findCells p (O.nb c)) ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
    split
    · split <;> omega
    · omega
  | ready a b α β =>
    obtain ⟨ha, -⟩ : a.length ≤ L ∧ b.length ≤ L := hNs
    have h₁ := symB a ha
    have h₂ := takeB a ha
    show 1 + O.symF a + (if O.sym a = some α then O.takeF a else 0) ≤
      (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
    split <;> omega
  | half a b α β =>
    obtain ⟨ha, hb'⟩ : a.length ≤ L ∧ b.length ≤ L := hNs
    have h₁ := symB b hb'
    have h₂ := takeB b hb'
    have h₃ := putB a α ha
    have eb : (TThread.toX (⟨todo, .half a b α β⟩ : TThread S)).busy = 1 := rfl
    rw [eb]
    unfold OMach.fcost
    dsimp only
    split
    · split
      · rename_i R hR
        obtain ⟨hC, hD'⟩ := hb α β R hR
        have hal := Nat.le_trans (R.newAgents_length a b) hC
        have hll := Nat.le_trans (R.newLinks_length xs.sys.ar a b α β) hD'
        show 1 + O.symF b + (O.takeF b + (R.newAgents a b).length +
          (R.newLinks xs.sys.ar a b α β).length) ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
        omega
      · show 1 + O.symF b + O.putF a α ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
        omega
    · show 1 + O.symF b + O.putF a α ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
      omega
  | write as ls =>
    obtain ⟨has, hls⟩ : (∀ e ∈ as, e.1.length ≤ L) ∧
        ∀ e ∈ ls, e.1.1.length ≤ L ∧ e.2.1.length ≤ L := hNs
    cases as with
    | cons e as =>
      obtain ⟨i, γ⟩ := e
      have h₁ := putB i γ (has (i, γ) List.mem_cons_self)
      show 1 + O.putF i γ ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
      omega
    | nil =>
      cases ls with
      | cons e ls =>
        obtain ⟨p, q⟩ := e
        have h₁ := linkB p q (hls (p, q) List.mem_cons_self).1
        show 4 + O.linkF p q ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
        omega
      | nil =>
        show 1 ≤ (C + D + 4 + 4 * ((L + 6) * Dm)) * 1
        omega

/-- **The time on ordered maps alone, everything counted.**  Let no name
of the net have more than `L` cells.  Under the hypotheses of
`IMach.time_bound`, on every run the time is at most

    C + D + 4 + 4 * ((L + n + 6) * (3 * lg m))

for each action that is not a rest, where `m` is what the memory can hold,
`X.agents.length + C * n + (X.wires.length + D * n)`.  Calls, the cells
read to compare names, and the nodes built are all in the count; the names
grow by one cell for an interaction at most, and that is the factor
`L + n`. -/
theorem OMach.ftime_le_work {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {L : Nat} (hL : X.NamesLe L) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) :
    ∀ i, (OMach.init X nt).ftime xs σ i ≤
      (C + D + 4 + 4 * ((L + n + 6) *
          (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))) *
        (XMach.init X nt).work xs σ i := by
  obtain ⟨Φ, -, hΦ⟩ := XMach.work_measure hX hnd hnt hb hs hn σ
  have htodo := TMach.todo_le (xs := xs) hX hnd hnt hb hs hn σ
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨⟨am, at'⟩, -⟩ := OMach.trace_agree xs σ (OMach.init_agree X nt) i
    obtain ⟨a, -, ok⟩ := TMach.init_sim (xs := xs) hX hnd hnt σ i
    obtain ⟨hA, -, -⟩ := hΦ i
    have hW := XMach.wires_le (xs := xs) hX hnt hb hs hn σ i
    have hNm := XMach.names_le (xs := xs) hX hL nt hs hn σ i
    have sz := OMach.trace_sized xs σ (M := OMach.init X nt) (OMem.ofX_sized X) i
    have emem : ((TMach.init X nt).trace xs σ i).1.mem.toX =
        ((XMach.init X nt).trace xs σ i).1.mem := congrArg XMach.mem a
    have hm : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? =
        (((OMach.init X nt).trace xs σ i).1.ths[σ i]?).map TThread.toX := by
      rw [← a, at']
      show (((TMach.init X nt).trace xs σ i).1.ths.map TThread.toX)[σ i]? = _
      rw [List.getElem?_map]
    have hcells : ((OMach.init X nt).trace xs σ i).1.mem.cells.size ≤
        X.agents.length + C * n := by
      rw [am.cells, ← treeList_length]
      show ((TMach.init X nt).trace xs σ i).1.mem.toX.agents.length ≤ _
      rw [emem]
      exact hA
    have hwires : ((OMach.init X nt).trace xs σ i).1.mem.wires.length ≤
        X.wires.length + D * n := by
      rw [am.wires]
      show ((TMach.init X nt).trace xs σ i).1.mem.toX.wires.length ≤ _
      rw [emem]
      exact hW
    have hlive := sz.live
    have hnbrs := sz.nbrs
    have d₁ := tdepth_lt ((OMach.init X nt).trace xs σ i).1.mem.cells
    have d₂ := ndepth_lt ((OMach.init X nt).trace xs σ i).1.mem.live
    have d₃ := ndepth_lt ((OMach.init X nt).trace xs σ i).1.mem.nbrs
    have m₁ := lg_mono (Nat.le_trans hcells
      (Nat.le_add_right _ (X.wires.length + D * n)))
    have m₂ := lg_mono (Nat.le_trans (Nat.le_trans hlive hcells)
      (Nat.le_add_right _ (X.wires.length + D * n)))
    have m₃ := lg_mono (Nat.le_trans (Nat.le_trans hnbrs hwires)
      (Nat.le_add_left _ (X.agents.length + C * n)))
    have hfc : ∀ p c, findCells p (((OMach.init X nt).trace xs σ i).1.mem.nb c) ≤ 2 := by
      intro p c
      rw [am.nb c, ok.nbrs c]
      exact findCells_nbOf _ c p
    have hstep : ((OMach.init X nt).trace xs σ i).1.stepFcost xs (σ i) ≤
        (C + D + 4 + 4 * ((L + n + 6) *
            (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))) *
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i) := by
      unfold OMach.stepFcost XMach.stepTally
      rw [hm]
      cases hT : ((OMach.init X nt).trace xs σ i).1.ths[σ i]? with
      | none => exact Nat.zero_le _
      | some T =>
        have hT' : ((TMach.init X nt).trace xs σ i).1.ths[σ i]? = some T := by
          rw [← at']
          exact hT
        have hTX : ((XMach.init X nt).trace xs σ i).1.ths[σ i]? = some T.toX := by
          rw [hm, hT]
          rfl
        have m₄ := lg_mono (Nat.le_trans (htodo i T (List.mem_of_getElem? hT'))
          (Nat.le_add_right _ (X.wires.length + D * n)))
        have d₄ := tdepth_lt T.todo
        exact OMach.fcost_le hb _ T (by omega) (by omega) (by omega) (by omega) hfc
          (hNm.2 T.toX (List.mem_of_getElem? hTX))
    show (OMach.init X nt).ftime xs σ i +
        ((OMach.init X nt).trace xs σ i).1.stepFcost xs (σ i) ≤
      (C + D + 4 + 4 * ((L + n + 6) *
          (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))) *
        ((XMach.init X nt).work xs σ i +
          ((XMach.init X nt).trace xs σ i).1.stepTally XThread.busy (σ i))
    rw [Nat.mul_add]
    omega

/-- **A bound on the running time on ordered maps alone, everything
counted, whatever the schedule.** -/
theorem OMach.ftime_bound {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {L : Nat} (hL : X.NamesLe L) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') (σ : Nat → Nat)
    (i : Nat) :
    (OMach.init X nt).ftime xs σ i ≤
      ((nt + n) * X.passBound n C D + n * (C + D + 1)) *
        (C + D + 4 + 4 * ((L + n + 6) *
          (3 * lg (X.agents.length + C * n + (X.wires.length + D * n))))) := by
  have h₁ := OMach.ftime_le_work (xs := xs) hX hnd hnt hb hL hs hn σ i
  have h₂ := Nat.mul_le_mul_left
    (C + D + 4 + 4 * ((L + n + 6) *
      (3 * lg (X.agents.length + C * n + (X.wires.length + D * n)))))
    (XMach.work_le hX hnd hnt hb hs hn σ i)
  rw [Nat.mul_comm ((nt + n) * X.passBound n C D + n * (C + D + 1))]
  omega

end Names

end INet
