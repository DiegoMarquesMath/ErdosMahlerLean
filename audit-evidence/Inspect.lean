import ErdosMahlerLean.Proposition21
import Lean

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option format.width 120
set_option maxHeartbeats 0

#check ErdosMahlerLean.proposition21
#print ErdosMahlerLean.proposition21
#print axioms ErdosMahlerLean.proposition21
#print ErdosMahlerLean.Proposition21
#print ErdosMahlerLean.ComparableToB
#print ErdosMahlerLean.NegligibleToB
#print ErdosMahlerLean.External.WuWang
#print ErdosMahlerLean.External.MatolcsiRuzsaThree
#print ErdosMahlerLean.External.SubspaceTwoThree
#print ErdosMahlerLean.External.MatveevRational
#print ErdosMahlerLean.External.matveevRealConstant
#print ErdosMahlerLean.External.matveevWeightedCoefficient
#print ErdosMahlerLean.rationalLogHeight
#print ErdosMahlerLean.subspaceProduct
#print ErdosMahlerLean.subspaceEuclideanHeight

open Lean Elab Command in
run_elab do
  let env := (← getEnv).setExporting false
  let mut pending := #[`ErdosMahlerLean.proposition21]
  let mut visited : NameSet := {}
  let mut edges : Array Json := #[]
  let mut axioms : Array String := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some info := env.find? n | throwError "Missing declaration {n}"
    if let .axiomInfo _ := info then axioms := axioms.push n.toString
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if let .inductInfo v := info then deps := deps ++ v.ctors.toArray
    pending := pending ++ deps
    if (`ErdosMahlerLean).isPrefixOf n then
      let range ← findDeclarationRanges? n
      let sourceModule := (env.getModuleIdxFor? n).map fun idx => env.header.modules[idx.toNat]!.module.toString
      edges := edges.push <| Json.mkObj [
        ("declaration", toJson n.toString),
        ("module", toJson sourceModule),
        ("line", toJson (range.map (·.range.pos.line))),
        ("dependencies", toJson (deps.map Name.toString)),
        ("has_value", toJson (info.value? (allowOpaque := true)).isSome)]
  liftM <| IO.FS.writeFile "audit-evidence/dependencies.json" <|
    (Json.mkObj [("root", toJson "ErdosMahlerLean.proposition21"),
      ("total_transitive_constants", toJson visited.toArray.size),
      ("transitive_constants", toJson (visited.toArray.map Name.toString)),
      ("axioms", toJson axioms), ("project_declarations", toJson edges)]).pretty
