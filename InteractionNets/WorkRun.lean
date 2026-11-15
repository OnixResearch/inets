import InteractionNets.WorkCount
import InteractionNets.RoundRobin

/-! # Running the program that rechecks only what a rule touched, and reading

`XNet.runRead` runs `XMach` with threads that take turns and reads a
numeral when they are at rest; its bound on actions grows as the square of
the steps (`XNet.runRead_bound`).  `XNet.wrunRead` does the same with
`WMach`.  Whatever it returns is the numeral of the normal form
(`XNet.wrunRead_sound`), and it returns it after the bound of
`WMach.fair_bound` with a window of one action per thread, once the
claims that join interface ports are bounded (`XNet.wrunRead_bound`): for
a system whose rules join none, linear in the steps.
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

omit [DecidableEq S] in
theorem WMach.init_segs (X : XNet S) (nt : Nat) :
    (WMach.init X nt).segs = X.wires.length := by
  have h := (XMach.init_sizes X nt).1
  have e : (WMach.init X nt).toX = XMach.init X nt := by
    show WMach.toX ⟨X, _⟩ = ⟨X, _⟩
    unfold WMach.toX
    rw [List.map_map]
    rfl
  unfold WMach.segs
  rw [e]
  exact h

/-- **Along a run the memory holds at most the segments of the net and
`D` for each step to the normal form.** -/
theorem WMach.trace_wires_le {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (nt : Nat) (σ : Nat → Nat) (i : Nat) :
    ((WMach.init X nt).trace xs σ i).1.mem.wires.length ≤ X.wires.length + D * n := by
  have run : MRun xs.sys ((WMach.init X nt).trace xs σ i).2 (Mach.init X.toNet)
      ((WMach.init X nt).trace xs σ i).1.toMach := by
    have h := WMach.trace_run xs σ (WMach.init X nt) i
    rw [WMach.init_toMach] at h
    exact h
  have hc := run.claims_le hX hs hn
  have h := (WMach.trace_sizes σ (WMach.init X nt) hb i).1
  rw [WMach.init_segs] at h
  have h1 : ((WMach.init X nt).trace xs σ i).1.mem.wires.length ≤
      ((WMach.init X nt).trace xs σ i).1.segs := Nat.le_add_right _ _
  have h2 := Nat.mul_le_mul_left D hc
  omega

/-- **A run at rest has computed the normal form**, under any schedule:
the claims are the steps of the sequential reduction and the memory holds
the normal form. -/
theorem WMach.trace_rest {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') (σ : Nat → Nat) {i : Nat}
    (hr : ((WMach.init X nt).trace xs σ i).1.resting = true) :
    ((WMach.init X nt).trace xs σ i).2 = n ∧
      ((WMach.init X nt).trace xs σ i).1.mem.toNet = N' := by
  obtain ⟨hq, hnorm⟩ := (WMach.trace_live σ (WMach.init_live (xs := xs) hX hnt) i).rest hr
  have run := WMach.trace_run xs σ (WMach.init X nt) i
  rw [WMach.init_toMach] at run
  obtain ⟨-, hu⟩ := run.final hX hq hnorm
  obtain ⟨e₁, e₂⟩ := (hu hs).2 hn
  exact ⟨e₂.symm, e₁.symm⟩

section Read

variable {zero succ : S}

/-- **Run a memory with `WMach` and read a numeral.**  `nt` threads take
turns for `steps` actions; if they are then at rest, the numeral on the
port `p` is read. -/
def XNet.wrunRead (xs : XSys S) (zero succ : S) (X : XNet S) (p : Port) (nt steps : Nat) :
    Option Nat :=
  if ((WMach.init X nt).trace xs (fun j => j % nt) steps).1.resting = true then
    ((WMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.readNum zero succ steps steps p
  else none

/-- **Whatever the run returns is the numeral of the normal form.** -/
theorem XNet.wrunRead_sound (xs : XSys S) (hzs : zero ≠ succ) (hsucc : 1 ≤ xs.sys.ar succ)
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {p : Port}
    {v₀ : Nat} (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) {nt steps v : Nat}
    (hnt : 0 < nt) (h : XNet.wrunRead xs zero succ X p nt steps = some v) : v = v₀ := by
  unfold XNet.wrunRead at h
  by_cases hr : ((WMach.init X nt).trace xs (fun j => j % nt) steps).1.resting = true
  · rw [ite_pos' hr] at h
    obtain ⟨-, e⟩ := WMach.trace_rest hX hnt hs hn _ hr
    have hW : ((WMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet.WF
        xs.sys.ar := by
      rw [e]
      exact Steps.wf hX hs
    have hnum' : Addition.IsNum xs.sys.ar zero succ
        ((WMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet p v₀ := by
      rw [e]
      exact hnum
    obtain ⟨i, hpi, -⟩ := hnum'
    exact Addition.IsNum.unique hzs hW (XNet.readNum_sound hsucc hW _ _ _ _ hpi.1 h)
      (by rw [e]; exact hnum)
  · rw [ite_neg' hr] at h
    cases h

/-- **How many actions are enough to run with `WMach` and read.**  Let the
net reduce to a normal form with the numeral `v₀` on the port `p`, and let
no run of threads taking turns make more than `m` claims that join
interface ports.  Run for at least `nt` times the bound of
`WMach.fair_bound`, the segments the memory can hold and the length of the
numeral, the threads return `v₀`. -/
theorem XNet.wrunRead_bound (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') {p : Port} {v₀ : Nat}
    (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) {m : Nat}
    (hm : ∀ i, WMach.joined xs (fun j => j % nt) (WMach.init X nt) i ≤ m) (s : Nat)
    (h₁ : nt * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
          m * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)) +
          (7 * (C * n) + (X.wires.length + D * n)) + 1) ≤ s)
    (h₂ : X.wires.length + D * n ≤ s) (h₃ : v₀ + 1 ≤ s) :
    XNet.wrunRead xs zero succ X p nt s = some v₀ := by
  obtain ⟨hr, -, e⟩ := WMach.fair_bound hX hnd hnt hb hs hn (fun j => j % nt)
    roundRobin_fair hm s h₁
  have hW : ((WMach.init X nt).trace xs (fun j => j % nt) s).1.mem.toNet.WF xs.sys.ar := by
    rw [e]
    exact Steps.wf hX hs
  have hnum' : Addition.IsNum xs.sys.ar zero succ
      ((WMach.init X nt).trace xs (fun j => j % nt) s).1.mem.toNet p v₀ := by
    rw [e]
    exact hnum
  have hread := XNet.readNum_bounded hzs hW v₀ p hnum'
  have hwl := WMach.trace_wires_le hX hb hs hn nt (fun j => j % nt) s
  unfold XNet.wrunRead
  rw [ite_pos' hr]
  exact XNet.readNum_mono (by omega) hread h₃

/-- **Given enough actions, the run returns the numeral of the normal
form.** -/
theorem XNet.wrunRead_complete (hzs : zero ≠ succ) {X : XNet S} (hX : X.toNet.WF xs.sys.ar)
    (hnd : (X.agents.map Prod.fst).Nodup) {nt : Nat} (hnt : 0 < nt) {C D : Nat}
    (hb : xs.Bounded C D) {n : Nat} {N' : Net S} (hs : Steps (Step xs.sys) n X.toNet N')
    (hn : Normal (Step xs.sys) N') {p : Port} {v₀ : Nat}
    (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) :
    ∃ s₀, ∀ s, s₀ ≤ s → XNet.wrunRead xs zero succ X p nt s = some v₀ := by
  have hm : ∀ i, WMach.joined xs (fun j => j % nt) (WMach.init X nt) i ≤ n := by
    intro i
    have run := WMach.trace_run xs (fun j => j % nt) (WMach.init X nt) i
    rw [WMach.init_toMach] at run
    exact Nat.le_trans (WMach.joined_le _ _ i) (run.claims_le hX hs hn)
  refine ⟨nt * ((7 * X.agents.length + (X.wires.length + D * n)) + n * (C + D + 1) +
      n * (7 * (X.agents.length + (C - 2) * n) + (X.wires.length + D * n)) +
      (7 * (C * n) + (X.wires.length + D * n)) + 1) + (X.wires.length + D * n) + (v₀ + 1),
    fun s hs' => ?_⟩
  exact XNet.wrunRead_bound hzs hX hnd hnt hb hs hn hnum hm s (by omega) (by omega) (by omega)

end Read

end INet
