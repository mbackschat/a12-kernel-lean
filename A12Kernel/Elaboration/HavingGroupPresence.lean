import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.CorrelationWellFormed

namespace A12Kernel

/-- Resolve group content once while leaving candidate admission to the whole filter's reopened-level gate (spec/07 §3). Captured reads must already fit the host environment. -/
def FlatModel.resolveHavingGroupPresence (model : FlatModel) (declaringGroup : GroupPath)
    (outerLevels : List RepeatableLevel) (origin : HavingOrigin) (surface : SurfaceGroupReference) :
    Except CorrelationElabError ComputationGroupOperand := do
  let reference ← (model.resolveFixedTargetListGroupReference declaringGroup surface).mapError .groupPresence
  let scope := model.repeatableScopeForGroupPath reference.path
  if origin == .outer then
    if let some missing := scope.find? fun level => !outerLevels.contains level then
      throw (.repetitionOutsideEnvironment origin reference.path outerLevels missing)
  pure {
    reference := { reference with boundRepeatableScope := scope }
    content := model.computationGroupSource reference.path
    members := (model.groupSubtreeFields reference.path).map (·.id) }

/-- Group-list filters preserve authored entity identity, origin and order. Duplicate/overlap and arity gates precede the final whole-filter candidate gate, as for the existing field-list route. -/
def FlatModel.resolveHavingGroupFill (model : FlatModel) (declaringGroup : GroupPath)
    (outerLevels : List RepeatableLevel) (operator : GroupFillQuantifier)
    (first : SurfaceHavingEntityOperand) (rest : List SurfaceHavingEntityOperand) :
    Except CorrelationElabError (HavingGroupOperand × List HavingGroupOperand) := do
  let resolved ← resolveHavingEntityListOperands model declaringGroup [] outerLevels { first, rest }
  checkHavingEntityDuplicates resolved
  if let some path := resolved.findSome? fun read => read.categoryPath? then
    throw (.groupFill (.categoryNotAllowed path))
  if let some path := resolved.findSome? fun read => read.operand.rootGroupPath? then
    if operator.requiresMultipleOperands || !rest.isEmpty then
      throw (.groupFill (.rootGroupOperand path))
  if operator.requiresMultipleOperands && resolved.any (fun read => match read.operand with
      | .starredGroup _ | .starredGroupPresence _ => true | _ => false) then
    throw .groupListStarNotAllowed
  if operator.requiresMultipleOperands && rest.isEmpty then throw (.groupFill .tooFewFields)
  let group (origin : HavingOrigin) (reference : ResolvedGroupReference) (starPath : Option StarPath := none) :=
    HavingGroupOperand.group origin {
      reference := { reference with boundRepeatableScope := model.repeatableScopeForGroupPath reference.path }
      content := model.computationGroupSource reference.path
      members := (model.groupSubtreeFields reference.path).map (·.id)
      starPath
      dependencyKind := if reference.isRoot && starPath.isNone then .conditionalPresence else .ordinaryList }
  let operands ← resolved.mapM fun read => do
    let origin := read.origin
    match read.operand with
    | .field declaration .stored => pure (.field { origin, field := declaration.id })
    | .group reference => pure (group origin reference)
    | .starredGroup source => pure (group origin { path := source.group.path, origin := .path } (some source.path))
    | .starredGroupPresence source => pure (group origin { path := source.groupPath, origin := .path } (some source.path))
    | _ => throw .numericExpressionUnsupported
  match operands with
  | first :: rest => pure (first, rest)
  | [] => throw .incoherentCore
end A12Kernel
