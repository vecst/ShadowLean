/- Executed by `lake env python3 audit/check_axioms.py`, which prepends imports
   for every RequestProject source module. Selection uses originating modules,
   not declaration namespaces, and includes private/generated declarations. -/
import Lean
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let mut violations : Nat := 0
  let mut modules : Std.HashSet Name := {}
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if (`RequestProject).isPrefixOf modName then
        let axioms ← collectAxioms name
        let unexpected := axioms.filter fun ax => !allowed.contains ax
        unless unexpected.isEmpty do
          violations := violations + 1
          logError m!"UNEXPECTED_AXIOMS declaration={name} axioms={unexpected}"
        count := count + 1
        modules := modules.insert modName
        match info with
        | .thmInfo _ => theoremCount := theoremCount + 1
        | _ => pure ()
        logInfo m!"AUDITED {modName} | {name} | {axioms}"
  if count == 0 then
    throwError "ALLOWLIST_EMPTY: No project declarations found; audit selection failed."
  if violations > 0 then
    throwError "ALLOWLIST_FAIL violations={violations}"
  logInfo m!"ALLOWLIST_PASS declarations={count} theorems={theoremCount} modules={modules.size}"
