import A12Kernel.Elaboration.FieldEntityList

namespace A12Kernel

private def ordinaryOperand (model : FlatModel) (declaringGroup : GroupPath) :
    SurfaceHavingEntityOperand → SurfaceFieldEntityOperand
  | .entity reference => match model.groupNamedBy? declaringGroup reference.field with
      | some path => if reference.form == .stored then .group (.path { base := .absolute, groups := path })
          else .field reference.field reference.form
      | none => .field reference.field reference.form
  | .group _ reference => .group reference
  | .star _ path _ =>
      let last := path.groups.getLast?.getD { name := "" }
      let field : SurfaceStarFieldPath := { base := path.base, groups := path.groups.dropLast, field := last.name }
      if !last.starred && (model.resolveFieldDeclarationUnchecked declaringGroup field.toFieldPath).isOk then
        .star field
      else .starredGroup path

/-- Ordinary entity-list shape and category gates are applied before the enclosing filter's
candidate-scope gate. Captured references retain their immediate host-scope check (spec/07 §3). -/
def resolveHavingEntityListOperands (model : FlatModel) (declaringGroup : GroupPath)
    (_candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError (List (HavingOrigin × ResolvedFieldEntityOperand model)) := do
  model.validate |>.mapError .resolve
  (source.first :: source.rest).mapM fun authored => do
    let operand ← resolveFieldEntityOperandIn model declaringGroup []
      (ordinaryOperand model declaringGroup authored) (some declaringGroup) declaringGroup
      |>.mapError .fieldFill
    if let .star _ _ (.projected _) := authored then
      throw (.fieldFill (.categoryNotAllowed operand.entityPath))
    let operand := match operand with
      | .group reference => .group { reference with boundRepeatableScope := model.repeatableScopeForGroupPath reference.path }
      | other => other
    if authored.origin == .outer then
      if !operand.bindingScope.isPrefixOf outerLevels then
        throw (.fieldOutsideEnvironment .outer operand.entityPath outerLevels operand.bindingScope)
    pure (authored.origin, operand)

/-- Preserve the authored extent while projecting its declared members for a typed consumer. -/
def havingResolvedEntitySlots (operands : List (HavingOrigin × ResolvedFieldEntityOperand model)) :
    Except CorrelationElabError (List (HavingFieldListSlot (ResolvedHavingDirectFieldOperand model))) := do
  operands.mapM fun (origin, operand) => do
    let references := operand.expansionDeclarations.map fun declaration =>
      ({ origin, declaration, form := .stored } : ResolvedHavingDirectFieldOperand model)
    match operand with
    | .field declaration form => pure (.direct { origin, declaration, form })
    | .star source => pure (.extent (.starField source.declaration.groupPath source.path) references)
    | .group reference => pure (.extent (.group reference) references)
    | .starredGroup source => pure (.extent (.starredGroup source.group.path source.path) references)
    | .starredGroupPresence source => pure (.extent (.starredGroup source.groupPath source.path) references)
    | _ => throw .incoherentCore

def checkHavingEntityDuplicates (operands : List (HavingOrigin × ResolvedFieldEntityOperand model)) :
    Except CorrelationElabError Unit := do
  if let some (_, duplicate) := firstDuplicateInEncounterOrder?
      (fun (origin, operand) => operand.exactIdentity?.map (origin, ·)) operands then
    match duplicate with
    | .field (field, _) | .indexed (field, _) => throw (.fieldFill (.duplicateOperand field))
    | .fixedGroup path | .keyedGroup path _ => throw (.fieldFill (.duplicateGroupOperand path))
  if let some (left, right) := firstResolvedOperandOverlap? (operands.map (·.2)) then
    throw (.fieldFill (.overlappingOperands left right))

def checkHavingEntityRoots (operands : List (HavingOrigin × ResolvedFieldEntityOperand model)) :
    Except CorrelationElabError Unit := do
  if let some path := operands.findSome? (fun (_, operand) => operand.rootGroupPath?) then
    throw (.fieldFill (.rootGroupOperand path))

def elaborateHavingEntityList (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError (List (HavingFieldListSlot (ResolvedHavingDirectFieldOperand model))) := do
  let operands ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels source
  checkHavingEntityDuplicates operands
  checkHavingEntityRoots operands
  if let some path := operands.findSome? (fun (_, operand) => operand.categoryPath?) then
    throw (.fieldFill (.categoryNotAllowed path))
  if operands.length < 2 && !operands.any (fun (_, operand) => operand.isAlreadyMany) then
    throw (.fieldFill .tooFewFields)
  havingResolvedEntitySlots operands

namespace HavingFieldListSlot

def bindingScope? (model : FlatModel) : HavingFieldListSlot HavingPresenceRef → Option (List RepeatableLevel)
  | .direct reference => (model.lookupUniqueId reference.field).toOption.map (·.repeatableScope)
  | .extent (.group reference) _ => some reference.boundRepeatableScope
  | .extent (.starField _ path) _ | .extent (.starredGroup _ path) _ => some path.bindingScope

def outerIterationScope? (slot : HavingFieldListSlot HavingPresenceRef)
    (model : FlatModel) : Option (List RepeatableLevel) := do
  let reference ← slot.references.head?
  if reference.origin != .outer then none
  let scope ← slot.bindingScope? model
  if scope.isEmpty then none else some scope

def entityPath? (model : FlatModel) : HavingFieldListSlot HavingPresenceRef → Option (List String × Bool)
  | .direct reference | .extent (.starField _ _) [reference] =>
      (model.lookupUniqueId reference.field).toOption.map fun declaration => (declaration.path, false)
  | .extent (.group reference) _ => some (reference.path, true)
  | .extent (.starredGroup path _) _ => some (path, true)
  | _ => none

def exactIdentity? : HavingFieldListSlot HavingPresenceRef → Option (HavingOrigin × Sum FieldId GroupPath)
  | .direct reference => some (reference.origin, .inl reference.field)
  | .extent (.group source) (reference :: _) => some (reference.origin, .inr source.path)
  | _ => none

/-- Certificates retain the full declared expansion and exact model axes, including capacity;
checking only flattened references would accept forged extents or erase wildcard identity. -/
def wellFormedForEnvironments (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (slot : HavingFieldListSlot HavingPresenceRef) : Bool :=
  match slot.references.head?, slot.bindingScope? model with
  | some first, some scope =>
    slot.references.all (fun reference => reference.origin == first.origin) &&
      scope.isPrefixOf (first.origin.availableLevels candidateLevels outerLevels) &&
      match slot with
      | .direct reference => (model.lookupUniqueId reference.field).isOk
      | .extent source references =>
        let fields := references.map (·.field)
        let starValid (path : GroupPath) (selection : StarPath) :=
          model.repeatableAxesForScope? (model.repeatableScopeForGroupPath path) == some selection.axes &&
            selection.firstStar < selection.axes.length
        match source with
        | .starField group selection =>
            references.length == 1 && (model.lookupUniqueId first.field).toOption.any fun declaration =>
              declaration.groupPath == group && starValid group selection
        | .group reference =>
            model.hasGroupPath reference.path && !reference.isRoot &&
              reference.boundRepeatableScope == model.repeatableScopeForGroupPath reference.path &&
              fields == (model.groupSubtreeFields reference.path).map (·.id)
        | .starredGroup path selection =>
            model.hasGroupPath path && starValid path selection &&
              fields == (model.groupSubtreeFields path).map (·.id)
  | _, _ => false

end HavingFieldListSlot

def havingEntityListWellFormed (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (slots : List (HavingFieldListSlot HavingPresenceRef)) : Bool :=
  !slots.isEmpty && (slots.length > 1 || slots.any (! ·.isDirect)) &&
    slots.all (·.wellFormedForEnvironments model candidateLevels outerLevels) &&
    (firstDuplicateInEncounterOrder? HavingFieldListSlot.exactIdentity? slots).isNone &&
    !(slots.any fun left => slots.any fun right =>
      (left.entityPath? model).any fun (leftPath, leftGroup) =>
        (right.entityPath? model).any fun (rightPath, rightGroup) =>
          entityListPathsOverlap leftPath rightPath leftGroup rightGroup)

end A12Kernel
