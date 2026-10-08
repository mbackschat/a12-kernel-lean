import A12Kernel.Elaboration.HavingEntityList
import A12Kernel.Elaboration.CheckedGroupPresence

namespace A12Kernel

def HavingGroupCountOperand.expectedCapacity? (operand : HavingGroupCountOperand) (model : FlatModel) : Option Nat :=
  match operand.source.starPath with
  | none => some 1
  | some path => match operand.kind with
      | .rows => (model.repeatableGroups.find? (·.path == operand.source.reference.path)).bind (·.repeatability)
      | .content => (path.axes.drop path.firstStar).foldlM (m := Option) (init := 1)
          fun product axis => (product * ·) <$> axis.repeatability

def HavingGroupCountOperand.wellFormed (operand : HavingGroupCountOperand) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  !operand.source.reference.isRoot &&
    operand.source.dependencyKind == .ordinaryList &&
    operand.source.admitted model (operand.origin.availableLevels candidateLevels outerLevels) &&
    operand.capacity == operand.expectedCapacity? model &&
    match operand.source.starPath with
    | none => operand.kind == .content
    | some _ =>
        let terminalRepeatable := model.repeatableGroups.any (·.path == operand.source.reference.path)
        (operand.kind == .rows) == terminalRepeatable &&
          (!terminalRepeatable || model.groupContributesField operand.source.reference.path)

/-- Equal starred operands are independent positions; equal fixed operands retain capture
identity, while strict containment is forbidden across captures (spec/07 §3–§5). -/
def HavingGroupCount.firstOverlap? : List HavingGroupCountOperand → Option (GroupPath × GroupPath)
  | [] => none
  | first :: rest =>
      let path := first.source.reference.path
      match rest.find? (fun other =>
        let otherPath := other.source.reference.path
        if path == otherPath then first.origin == other.origin &&
          (first.source.starPath.isNone || other.source.starPath.isNone)
        else path.isPrefixOf otherPath || otherPath.isPrefixOf path) with
      | some other => some (path, other.source.reference.path)
      | none => firstOverlap? rest

def HavingGroupCount.wellFormed (operands : List HavingGroupCountOperand) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  !operands.isEmpty && (operands.length > 1 || operands.any (·.source.starPath.isSome)) &&
    (firstOverlap? operands).isNone && operands.all (·.wellFormed model candidateLevels outerLevels)

private def groupOperand (model : FlatModel) (origin : HavingOrigin)
    (reference : ResolvedGroupReference) (starPath : Option StarPath) (kind : HavingGroupCountKind) : HavingGroupCountOperand :=
  let operand : HavingGroupCountOperand := {
    origin, kind, capacity := none
    source := {
      reference := { reference with boundRepeatableScope := model.repeatableScopeForGroupPath reference.path }
      content := model.computationGroupSource reference.path
      members := (model.groupSubtreeFields reference.path).map (·.id)
      starPath, dependencyKind := .ordinaryList } }
  { operand with capacity := operand.expectedCapacity? model }

private def resolveCountedGroup (model : FlatModel) (declaringGroup : GroupPath) :
    SurfaceHavingEntityOperand → Except CorrelationElabError HavingGroupCountOperand
  | .entity reference => do
      if reference.form != .stored then throw .numericExpressionUnsupported
      let resolved ← model.resolveFixedTargetListGroupReference declaringGroup (.path {
        base := reference.field.base, turningPoint := reference.field.turningPoint
        groups := reference.field.groups ++ [reference.field.field] }) |>.mapError .groupPresence
      pure (groupOperand model reference.origin resolved none .content)
  | .group origin reference => do
      let resolved ← model.resolveFixedTargetListGroupReference declaringGroup reference |>.mapError .groupPresence
      pure (groupOperand model origin resolved none .content)
  | .star origin reference form => do
      if form != .stored then throw .numericExpressionUnsupported
      let resolved ← elaborateStarredGroupOperandSource model declaringGroup reference
        |>.mapError (fun _ => CorrelationElabError.numericExpressionUnsupported)
      match resolved with
      | .terminalRepeatable source => pure (groupOperand model origin
          { path := source.group.path, origin := .path } (some source.path) .rows)
      | .terminalPresence source => pure (groupOperand model origin
          { path := source.groupPath, origin := .path } (some source.path) .content)

def elaborateHavingGroupCount (model : FlatModel) (declaringGroup : GroupPath)
    (_candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError (List HavingGroupCountOperand) := do
  model.validate |>.mapError .resolve
  let operands ← (source.first :: source.rest).mapM (resolveCountedGroup model declaringGroup)
  for operand in operands do
    if operand.origin == .outer && !operand.bindingScope.isPrefixOf outerLevels then
      throw (.fieldOutsideEnvironment .outer operand.source.reference.path outerLevels operand.bindingScope)
  if operands.length == 1 && operands.all (·.source.starPath.isNone) then throw (.groupFill .tooFewFields)
  if let some (left, right) := HavingGroupCount.firstOverlap? operands then
    throw (.groupFill (.overlappingOperands left right))
  if let some root := operands.find? (·.source.reference.isRoot) then
    throw (.groupFill (.rootGroupOperand root.source.reference.path))
  pure operands

end A12Kernel
