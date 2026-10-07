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

private def resolveOperand (model : FlatModel) (declaringGroup : GroupPath)
    (outerLevels : List RepeatableLevel) (origin : HavingOrigin) (surface : SurfaceGroupReference) :
    Except CorrelationElabError (HavingGroupOperand × GroupPath) := do
  let reference ← surface.resolveAgainst declaringGroup |>.mapError (fun error => .groupPresence (.reference error))
  if model.hasGroupPath reference.path then
    let source ← model.resolveHavingGroupPresence declaringGroup outerLevels origin surface
    pure (.group origin { source with dependencyKind :=
      if source.reference.isRoot then .conditionalPresence else .ordinaryList }, reference.path)
  else
    let some name := reference.path.getLast? | throw (.groupPresence (.unknownGroup reference.path))
    let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup {
      base := .absolute, groups := reference.path.dropLast, field := name }).mapError .resolve
    if origin == .outer && !declaration.repeatableScope.isPrefixOf outerLevels then
      throw (.fieldOutsideEnvironment origin declaration.path outerLevels declaration.repeatableScope)
    pure (.field { origin, field := declaration.id }, declaration.path)

/-- Group-list filters preserve authored entity identity, origin and order. Duplicate/overlap and arity gates precede the final whole-filter candidate gate, as for the existing field-list route. -/
def FlatModel.resolveHavingGroupFill (model : FlatModel) (declaringGroup : GroupPath)
    (outerLevels : List RepeatableLevel) (operator : GroupFillQuantifier)
    (first : HavingOrigin × SurfaceGroupReference) (rest : List (HavingOrigin × SurfaceGroupReference)) :
    Except CorrelationElabError (HavingGroupOperand × List HavingGroupOperand) := do
  let operands : List (HavingGroupOperand × GroupPath) ← (first :: rest).mapM fun (origin, surface) =>
    resolveOperand model declaringGroup outerLevels origin surface
  if let some (origin, path) := firstDuplicateInEncounterOrder?
      (fun (operand, path) => some (operand.origin, path)) operands then
    match operands.find? (fun (operand, found) => operand.origin == origin && found == path) with
    | some (HavingGroupOperand.field reference, _) => throw (.groupFill (.duplicateOperand reference.field))
    | _ => throw (.groupFill (.duplicateGroupOperand path))
  if let some (left, right) := firstOverlappingHavingPaths? (operands.map fun (operand, path) => (operand.origin, path)) then
    throw (.groupFill (.overlappingOperands left right))
  if let some path := operands.findSome? fun
      | (.group _ source, _) => if source.reference.isRoot then some source.reference.path else none
      | _ => none then
    if operator.requiresMultipleOperands || !rest.isEmpty then
      throw (.groupFill (.rootGroupOperand path))
  if operator.requiresMultipleOperands && rest.isEmpty then throw (.groupFill .tooFewFields)
  match operands.map (·.1) with
  | first :: rest => pure (first, rest)
  | [] => throw .incoherentCore
end A12Kernel
