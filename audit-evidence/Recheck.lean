import ErdosMahlerLean.Proposition21
import Lean

set_option maxHeartbeats 0

open Lean Elab Command in
run_elab do
  let env := (← getEnv).setExporting false
  let mut pending := #[`ErdosMahlerLean.proposition21]
  let mut visited : NameSet := {}
  let mut checked : Nat := 0
  let mut checkedProject : Nat := 0
  let mut bodyless : Array String := #[]
  let mut axioms : Array String := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some info := env.find? n | throwError "Missing declaration {n}"
    let mut deps := info.type.getUsedConstants
    if let .axiomInfo _ := info then axioms := axioms.push n.toString
    if let .inductInfo v := info then deps := deps ++ v.ctors.toArray
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
      match Kernel.check env {} value with
      | .error _ => throwError "Kernel rejected the body of {n}"
      | .ok inferred =>
        match Kernel.isDefEq env {} inferred info.type with
        | .ok true => pure ()
        | _ => throwError "Body/type mismatch for {n}"
      checked := checked + 1
      if (`ErdosMahlerLean).isPrefixOf n then checkedProject := checkedProject + 1
      if checked % 1000 == 0 then
        liftM <| IO.FS.writeFile "audit-evidence/recheck-progress.txt" s!"Checked {checked} bodies; current: {n}\n"
    else
      bodyless := bodyless.push n.toString
    pending := pending ++ deps
  let result := Json.mkObj [
    ("total_transitive_constants", toJson visited.toArray.size),
    ("checked_bodies", toJson checked),
    ("checked_project_bodies", toJson checkedProject),
    ("axioms", toJson axioms),
    ("bodyless_declarations", toJson bodyless)]
  liftM <| IO.FS.writeFile "audit-evidence/kernel-recheck.json" (result.pretty ++ "\n")
  logInfo m!"Independently rechecked {checked} transitive bodies, including {checkedProject} project bodies."
