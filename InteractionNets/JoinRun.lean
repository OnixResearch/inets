import InteractionNets.JoinLive
import InteractionNets.ReadBack

/-! # Runs of the program that walks the joined wires, and reading them

A run of `JMach` that comes to rest has reached a normal form, in as many
steps as it made claims, whatever the schedule and the number of threads
(`JMach.exec_rest_steps`, `JMach.rest_steps`); no normal form has to be
known beforehand.  `XNet.jrunRead` runs it with threads that take turns and
reads a numeral at rest, and whatever it returns is the numeral of the
normal form (`XNet.jrunRead_sound`).  That a fair run comes to rest, and
when, is in `JoinBound.lean`.
-/

namespace INet

variable {S : Type} [DecidableEq S] {xs : XSys S}

/-- **A run that comes to rest has reached a normal form**, in as many steps
as it made claims. -/
theorem JMach.exec_rest_steps {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat}
    (hnt : 0 < nt) (σ : List Nat) (hr : ((JMach.init X nt).exec xs σ).1.resting = true) :
    Steps (Step xs.sys) ((JMach.init X nt).exec xs σ).2 X.toNet
        ((JMach.init X nt).exec xs σ).1.mem.toNet ∧
      Normal (Step xs.sys) ((JMach.init X nt).exec xs σ).1.mem.toNet := by
  obtain ⟨hq, hnorm⟩ := (JMach.exec_live σ (JMach.init_live hX hnt)).rest hr
  exact ⟨((JMach.exec_mrun xs X nt σ).final hX hq hnorm).1, hnorm⟩

/-- The state after `i` actions of the schedule `σ`, and the claims so
far. -/
def JMach.trace (xs : XSys S) (σ : Nat → Nat) (M : JMach S) : Nat → JMach S × Nat
  | 0 => (M, 0)
  | i + 1 =>
    (((JMach.trace xs σ M i).1.step xs (σ i)).1,
      (JMach.trace xs σ M i).2 + ((JMach.trace xs σ M i).1.step xs (σ i)).2)

theorem JMach.trace_run (xs : XSys S) (σ : Nat → Nat) (M : JMach S) :
    ∀ i, MRun xs.sys (M.trace xs σ i).2 M.toMach (M.trace xs σ i).1.toMach
  | 0 => .refl _
  | i + 1 => by
    have ih := JMach.trace_run xs σ M i
    show MRun xs.sys ((M.trace xs σ i).2 + ((M.trace xs σ i).1.step xs (σ i)).2) M.toMach
      ((M.trace xs σ i).1.step xs (σ i)).1.toMach
    rcases JMach.step_sim xs (M.trace xs σ i).1 (σ i) with ⟨e₁, e₂⟩ | hs
    · rw [e₂, e₁, Nat.add_zero]
      exact ih
    · exact ih.trans (.step hs (.refl _))

theorem JMach.trace_live (σ : Nat → Nat) {M : JMach S} (hL : M.Live xs) :
    ∀ i, (M.trace xs σ i).1.Live xs
  | 0 => hL
  | i + 1 => JMach.step_live (JMach.trace_live σ hL i) (σ i)

/-- **A run that comes to rest has reached a normal form**, for a schedule
given as a function. -/
theorem JMach.rest_steps {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {nt : Nat} (hnt : 0 < nt)
    {σ : Nat → Nat} {j : Nat} (hr : ((JMach.init X nt).trace xs σ j).1.resting = true) :
    Steps (Step xs.sys) ((JMach.init X nt).trace xs σ j).2 X.toNet
        ((JMach.init X nt).trace xs σ j).1.mem.toNet ∧
      Normal (Step xs.sys) ((JMach.init X nt).trace xs σ j).1.mem.toNet := by
  obtain ⟨hq, hnorm⟩ := (JMach.trace_live σ (JMach.init_live (xs := xs) hX hnt) j).rest hr
  have run := JMach.trace_run xs σ (JMach.init X nt) j
  rw [JMach.init_toMach] at run
  exact ⟨(run.final hX hq hnorm).1, hnorm⟩

section Read

variable {zero succ : S}

/-- **Run a memory with `JMach` and read a numeral.** -/
def XNet.jrunRead (xs : XSys S) (zero succ : S) (X : XNet S) (p : Port) (nt steps : Nat) :
    Option Nat :=
  if ((JMach.init X nt).trace xs (fun j => j % nt) steps).1.resting = true then
    ((JMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.readNum zero succ steps steps p
  else none

/-- **Whatever the run returns is the numeral of the normal form.** -/
theorem XNet.jrunRead_sound (xs : XSys S) (hzs : zero ≠ succ) (hsucc : 1 ≤ xs.sys.ar succ)
    {X : XNet S} (hX : X.toNet.WF xs.sys.ar) {n : Nat} {N' : Net S}
    (hs : Steps (Step xs.sys) n X.toNet N') (hn : Normal (Step xs.sys) N') {p : Port}
    {v₀ : Nat} (hnum : Addition.IsNum xs.sys.ar zero succ N' p v₀) {nt steps v : Nat}
    (hnt : 0 < nt) (h : XNet.jrunRead xs zero succ X p nt steps = some v) : v = v₀ := by
  unfold XNet.jrunRead at h
  by_cases hr : ((JMach.init X nt).trace xs (fun j => j % nt) steps).1.resting = true
  · rw [ite_pos' hr] at h
    obtain ⟨hs', hn'⟩ := JMach.rest_steps hX hnt hr
    have e : ((JMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet = N' :=
      normal_form_unique hX hs' hs hn' hn |>.1
    have hW : ((JMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet.WF
        xs.sys.ar := by
      rw [e]
      exact Steps.wf hX hs
    have hnum' : Addition.IsNum xs.sys.ar zero succ
        ((JMach.init X nt).trace xs (fun j => j % nt) steps).1.mem.toNet p v₀ := by
      rw [e]
      exact hnum
    obtain ⟨i, hpi, -⟩ := hnum'
    exact Addition.IsNum.unique hzs hW (XNet.readNum_sound hsucc hW _ _ _ _ hpi.1 h)
      (by rw [e]; exact hnum)
  · rw [ite_neg' hr] at h
    cases h

end Read

end INet
