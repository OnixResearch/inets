-- Run by `lake exe inets-check`: every constant of the library, and the
-- foundations it rests on.  Not part of any library.
import Lean
import InteractionNets
open Lean Elab Command

elab "#check_all_axioms" : command => do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut n : Nat := 0
  for (nm, _) in env.constants.toList do
    match env.getModuleIdxFor? nm with
    | some idx =>
      let mod := env.header.moduleNames[idx]!
      if (`InteractionNets).isPrefixOf mod then
        n := n + 1
        let axs ← liftTermElabM <| Lean.collectAxioms nm
        for a in axs do seen := seen.insert a
    | none => pure ()
  logInfo m!"checked {n} constants; axioms: {seen.toList.map toString}"

#check_all_axioms
