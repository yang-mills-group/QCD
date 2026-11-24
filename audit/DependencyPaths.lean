import YM.Plata.Massive
import Lean.Util.FoldConsts

/-! Read-only declaration-graph inspection. This is a compiler-environment
 diagnostic, not a new theorem or a proof that an assumption is indispensable.
 Edges include constants in types and values. Only YM declarations are traversed. -/
set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let root := `YM.Massive.interacting_six
  let targets : Array Name := #[
    `YM.QCD.Acre.Stratum.MarchQ.Earlier,
    `YM.QCD.Acre.Stratum.MarchQ.delta₀,
    `YM.QCD.Acre.Stratum.MarchQ.Track.slope_all,
    `YM.QCD.Acre.Stratum.MarchQ.Track.perimeter,
    `YM.QCD.Raft.betaQ,
    `YM.QCD.Pearl.wilson,
    `YM.QCD.Pearl.docket,
    `YM.QCD.Raft.calibrated,
    `YM.QCD.Acre.Stratum.MarchQ.Track.Survey.sum_toll,
    `YM.QCD.Pearl.chargeF,
    `YM.QCD.Acre.Rails.canopyR,
    `YM.QCD.Acre.Stratum.SurveyT.perimeter]
  let mut queue := #[root]
  let mut parent : Std.HashMap Name Name := ({} : Std.HashMap Name Name).insert root root
  let mut head := 0
  while head < queue.size do
    let n := queue[head]!
    head := head+1
    if let some info := env.find? n then
      for dep in info.getUsedConstantsAsSet.toList do
        if (`YM).isPrefixOf dep && !parent.contains dep then
          parent := parent.insert dep n
          queue := queue.push dep
  let mut results : Array Json := #[]
  for target in targets do
    let mut path := #[]
    if parent.contains target then
      let mut current := target
      path := path.push current.toString
      while current != root do
        current := parent[current]!
        path := path.push current.toString
      path := path.reverse
    results := results.push <| Json.mkObj [
      ("target",toJson target.toString),
      ("present_in_environment",toJson (env.find? target).isSome),
      ("in_restricted_dependency_closure",toJson (parent.contains target)),
      ("path",toJson path)]
  let result := Json.mkObj [("root",toJson root.toString),("visited_YM_declarations",toJson queue.size),
    ("edges",toJson "Constants in declaration types and values; YM-only traversal; not an indispensability proof"),
    ("targets",toJson results)]
  logInfo m!"DEPENDENCY_JSON {result.compress}"
