import A12Kernel.Elaboration.DateFromDateTime

/-! # Repeatable `DateFromDateTime`

This bounded carrier certifies one target-bound complete DateTime source and full-Date target, enumerates only physical target rows, and retains exact source and target addresses. Sibling parallel iteration, scheduling, and result application remain separate.
-/

namespace A12Kernel

inductive AddressedDateFromDateTimeElabError where
  | targetLookup (cause : ResolveError)
  | target (cause : FullDateTargetElabError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | source (cause : ResolveError)
  | sourceNotTemporal (field : FieldId)
  | sourceKind (field : FieldId) (actual : TemporalKind)
  | sourceComponents (field : FieldId) (actual : TemporalComponents)
  | scopeMismatch (target source : List String)
  deriving Repr, DecidableEq

/-- One exact repeatable extraction certified against a validated model. -/
structure CheckedAddressedDateFromDateTime (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  sourceReference : SurfaceFieldPath
  sourceDeclaration : FlatFieldDecl
  source : FlatTemporalField
  target : CheckedFullDateTarget model
  sourceResolved : model.resolveFieldDeclarationUnchecked declaringGroup sourceReference = .ok sourceDeclaration
  sourceOwned : sourceDeclaration.toTemporalField? = some source
  targetInDeclaringGroup : target.checked.declaration.groupPath = declaringGroup
  targetRepeatable : target.checked.declaration.repeatableScope ≠ []
  sourceScopeBound : sourceDeclaration.repetitionBoundBy
    target.checked.declaration.repeatableScope = true
  sourceAdmitted : model.admitsCompleteDateTimeSourceIn
    target.checked.declaration.repeatableScope source = true

/-- Certify one source whose repeatable levels the target's own scope binds. -/
def checkAddressedDateFromDateTime
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedDateFromDateTimeElabError
      (CheckedAddressedDateFromDateTime model) := do
  let targetDeclaration ← model.lookupUniqueId targetField |>.mapError .targetLookup
  let checkedTarget ←
    elaborateTemporalTargetPolicyIn model targetDeclaration.repeatableScope targetField
      |>.mapError (fun cause => .target (.targetPolicy cause))
  let target ← checkedTarget.toFullDateTarget |>.mapError .target
  if hGroup : target.checked.declaration.groupPath = declaringGroup then
    if hRepeatable : target.checked.declaration.repeatableScope.isEmpty then
      throw (.targetNotRepeatable target.checked.declaration.path)
    else
      match hResolved :
          model.resolveFieldDeclarationUnchecked declaringGroup sourceReference with
      | .error cause => throw (.source cause)
      | .ok sourceDeclaration =>
        match hSource : sourceDeclaration.toTemporalField? with
        | none => throw (.sourceNotTemporal sourceDeclaration.id)
        | some source =>
          if source.kind != .dateTime then
            throw (.sourceKind source.id source.kind)
          else if !source.components.isFullDateTime then
            throw (.sourceComponents source.id source.components)
          else if hScope : sourceDeclaration.repetitionBoundBy
              target.checked.declaration.repeatableScope = true then
            if hAdmitted : model.admitsCompleteDateTimeSourceIn
                target.checked.declaration.repeatableScope source then
              pure {
                declaringGroup, sourceReference, sourceDeclaration, source, target
                sourceResolved := hResolved
                sourceOwned := hSource
                targetInDeclaringGroup := hGroup
                targetRepeatable := by
                  intro empty
                  simp [empty] at hRepeatable
                sourceScopeBound := hScope
                sourceAdmitted := hAdmitted
              }
            else
              throw (.source (.repeatableReference sourceDeclaration.path))
          else
            throw (.scopeMismatch target.checked.declaration.path sourceDeclaration.path)
  else
    throw (.targetOutsideDeclaringGroup target.checked.declaration.path declaringGroup)

inductive AddressedDateFromDateTimeFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | sourceRead (cause : CheckedDocumentError)
  | sourceValueKind (source : CellAddr)
  | sourceExtractionUnavailable (source : CellAddr)
  | target (cause : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One row-local outcome with both addresses needed by Execute and Explain consumers. -/
structure AddressedDateFromDateTimeOutcome where
  sourceField : CellAddr
  targetField : CellAddr
  outcome : FullDateTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedAddressedDateFromDateTime

/-- Classify one reached source cell without losing clean absence or formal poison. -/
def evaluateSourceCell (operation : CheckedAddressedDateFromDateTime model)
    (sourceAddress : CellAddr) (cell : CheckedCell) :
    Except AddressedDateFromDateTimeFault TemporalComputationResult :=
  match observeCell .computation cell with
  | .empty => pure .noValue
  | .poison cause | .unknown cause => pure (.poison cause)
  | .value (.temporal value) =>
      match dateFromDateTime? operation.target.profile value with
      | some date => pure (.value date.instant)
      | none => throw (.sourceExtractionUnavailable sourceAddress)
  | .value _ => throw (.sourceValueKind sourceAddress)

private def evaluateAtEnvironment
    (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedDateFromDateTimeFault AddressedDateFromDateTimeOutcome := do
  let sourcePath ←
    (environment.pathForScope operation.sourceDeclaration.repeatableScope)
      |>.mapError .environment
  let targetPath ←
    (environment.pathForScope operation.target.checked.declaration.repeatableScope)
      |>.mapError .environment
  let sourceAddress : CellAddr := { field := operation.source.id, path := sourcePath }
  let targetAddress : CellAddr := {
    field := operation.target.checked.target.id, path := targetPath
  }
  let sourceCell ← input.read sourceAddress |>.mapError .sourceRead
  let result ← operation.evaluateSourceCell sourceAddress sourceCell
  let outcome ← operation.target.evaluate result |>.mapError .target
  pure { sourceField := sourceAddress, targetField := targetAddress, outcome }

/-- Execute once per physically instantiated target row in document order. -/
def execute (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model) :
    Except AddressedDateFromDateTimeFault
      (List AddressedDateFromDateTimeOutcome) := do
  let environments ←
    input.actualRowEnvironments operation.target.checked.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAtEnvironment input)

end CheckedAddressedDateFromDateTime

end A12Kernel
