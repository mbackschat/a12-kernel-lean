import A12Kernel.Elaboration.NumericComputation.RunApplication

/-! # Shared repeatable numeric-leaf placement

This module owns the model-certified target/source placement and exact addressed execution seam shared by completed one-source numeric leaves. A specialized leaf still owns source-kind admission, static result scale, and the exact scalar evaluator it passes here.
-/

namespace A12Kernel

/-- Fail-closed errors for the shared repeatable placement. These are library diagnostics, not claims about kernel diagnostic precedence. -/
inductive AddressedNumericPlacementElabError where
  | model (cause : ResolveError)
  | target (cause : ResolveError)
  | source (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | targetPolicyUnavailable (path : List String)
  | targetNotRepeatable (path : List String)
  | targetSelfReference (field : FieldId)
  /-- The source crosses a repeatable level the target's own scope does not bind. -/
  | scopeMismatch (target source : List String)
  deriving Repr, DecidableEq

/-- The checked target half of an addressed numeric operation: one repeatable Number computation target inside its declaring group, with its complete target policy. This is everything execution needs, so it is separate from any source declaration — a legal computation may reference no field at all. -/
structure CheckedAddressedNumericTarget (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  targetField : FieldId
  targetDeclaration : FlatFieldDecl
  targetPolicy : NumericTargetPolicy
  modelWellFormed : model.validate.isOk = true
  targetOwned :
    model.lookupUniqueId targetField = .ok targetDeclaration
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetContainedInDeclaringGroup :
    GroupPath.isPrefixOf declaringGroup targetDeclaration.groupPath = true
  targetPolicyOwned :
    targetDeclaration.toNumericTargetPolicy? = some targetPolicy
  targetRepeatable : targetDeclaration.repeatableScope ≠ []

/-- The common checked placement of one Number target at a nonempty repeatable scope and one source declaration whose own repeatable levels that scope binds. -/
structure CheckedAddressedNumericPlacement (model : FlatModel) where
  private mk ::
  target : CheckedAddressedNumericTarget model
  sourceReference : SurfaceFieldPath
  sourceDeclaration : FlatFieldDecl
  sourceResolved :
    model.resolveFieldDeclarationUnchecked target.declaringGroup
        sourceReference =
      .ok sourceDeclaration
  sourceNotTarget : sourceDeclaration.id ≠ target.targetField
  /-- Every repeatable level the source crosses is bound by the target's own scope, so the source
  addresses at its own — possibly shorter — path inside the target's row. Measured: an outer-scope
  source computing a row target is admitted, while a sibling or deeper source is `MVK_NO_WILDCARD`. -/
  sourceScopeBound :
    sourceDeclaration.repetitionBoundBy
      target.targetDeclaration.repeatableScope = true

namespace CheckedAddressedNumericPlacement

/-- Every target fact of a placement is the fact of its target half. These forwarders keep the completed one-source owners unchanged by the split. -/
@[simp] def declaringGroup (placement : CheckedAddressedNumericPlacement model) :
    GroupPath := placement.target.declaringGroup

@[simp] def targetField (placement : CheckedAddressedNumericPlacement model) :
    FieldId := placement.target.targetField

@[simp] def targetDeclaration (placement : CheckedAddressedNumericPlacement model) :
    FlatFieldDecl := placement.target.targetDeclaration

@[simp] def targetPolicy (placement : CheckedAddressedNumericPlacement model) :
    NumericTargetPolicy := placement.target.targetPolicy

theorem modelWellFormed (placement : CheckedAddressedNumericPlacement model) :
    model.validate.isOk = true := placement.target.modelWellFormed

theorem targetOwned (placement : CheckedAddressedNumericPlacement model) :
    model.lookupUniqueId placement.targetField =
      .ok placement.targetDeclaration := placement.target.targetOwned

/-- The declaring group is a representable path. Containment against `[]` is vacuous, so this is what
makes the next forwarder load-bearing rather than trivially satisfied. -/
theorem declaringGroupValid (placement : CheckedAddressedNumericPlacement model) :
    GroupPath.isValid placement.declaringGroup = true :=
  placement.target.declaringGroupValid

/-- The target lies at or below its declaring group; an ancestor declaration satisfies it. -/
theorem targetContainedInDeclaringGroup
    (placement : CheckedAddressedNumericPlacement model) :
    GroupPath.isPrefixOf placement.declaringGroup
      placement.targetDeclaration.groupPath = true :=
  placement.target.targetContainedInDeclaringGroup

theorem targetPolicyOwned
    (placement : CheckedAddressedNumericPlacement model) :
    placement.targetDeclaration.toNumericTargetPolicy? =
      some placement.targetPolicy := placement.target.targetPolicyOwned

theorem targetRepeatable
    (placement : CheckedAddressedNumericPlacement model) :
    placement.targetDeclaration.repeatableScope ≠ [] :=
  placement.target.targetRepeatable

end CheckedAddressedNumericPlacement

/-- Check only the target facts, which every addressed numeric operation needs whether or not it references a field. -/
def checkAddressedNumericTarget
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Except AddressedNumericPlacementElabError
      (CheckedAddressedNumericTarget model) :=
  match hModel : model.validate with
  | .error cause => .error (.model cause)
  | .ok () =>
    match hTargetOwned : model.lookupUniqueId targetField with
    | .error cause => .error (.target cause)
    | .ok targetDeclaration =>
      if hValid : GroupPath.isValid declaringGroup = true then
        if hGroup : GroupPath.isPrefixOf
            declaringGroup targetDeclaration.groupPath = true then
          match hTargetKind : targetDeclaration.policy.kind with
          | .number _ =>
            match hTargetPolicy : targetDeclaration.toNumericTargetPolicy? with
            | none => .error (.targetPolicyUnavailable targetDeclaration.path)
            | some targetPolicy =>
              if hRepeatable : targetDeclaration.repeatableScope.isEmpty then
                .error (.targetNotRepeatable targetDeclaration.path)
              else
                .ok {
                  declaringGroup
                  targetField
                  targetDeclaration
                  targetPolicy
                  modelWellFormed := by
                    rw [hModel]
                    rfl
                  targetOwned := hTargetOwned
                  declaringGroupValid := hValid
                  targetContainedInDeclaringGroup := hGroup
                  targetPolicyOwned := hTargetPolicy
                  targetRepeatable := by
                    intro empty
                    simp [empty] at hRepeatable
                }
          | actual =>
              .error (.targetKindMismatch
                targetDeclaration.path actual.surfaceKind)
        else
          .error (.targetOutsideDeclaringGroup
            targetDeclaration.path declaringGroup)
      else
        .error (.target (.invalidRuleGroup declaringGroup))

/-- Check only the placement facts common to completed one-source addressed numeric leaves. -/
def checkAddressedNumericPlacement
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedNumericPlacementElabError
      (CheckedAddressedNumericPlacement model) :=
  match hModel : model.validate with
  | .error cause => .error (.model cause)
  | .ok () =>
    match hTargetOwned : model.lookupUniqueId targetField with
    | .error cause => .error (.target cause)
    | .ok targetDeclaration =>
      if hValid : GroupPath.isValid declaringGroup = true then
        if hGroup : GroupPath.isPrefixOf
            declaringGroup targetDeclaration.groupPath = true then
          match hTargetKind : targetDeclaration.policy.kind with
          | .number _ =>
            match hTargetPolicy :
                targetDeclaration.toNumericTargetPolicy? with
            | none =>
                .error (.targetPolicyUnavailable targetDeclaration.path)
            | some targetPolicy =>
              if hRepeatable :
                  targetDeclaration.repeatableScope.isEmpty then
                .error (.targetNotRepeatable targetDeclaration.path)
              else
                match hSourceResolved :
                    model.resolveFieldDeclarationUnchecked
                      declaringGroup sourceReference with
                | .error cause => .error (.source cause)
                | .ok sourceDeclaration =>
                  if hSelf : sourceDeclaration.id == targetField then
                    .error (.targetSelfReference targetField)
                  else if hScope :
                      sourceDeclaration.repetitionBoundBy
                        targetDeclaration.repeatableScope = true then
                    .ok {
                      target := {
                        declaringGroup
                        targetField
                        targetDeclaration
                        targetPolicy
                        modelWellFormed := by
                          rw [hModel]
                          rfl
                        targetOwned := hTargetOwned
                        declaringGroupValid := hValid
                        targetContainedInDeclaringGroup := hGroup
                        targetPolicyOwned := hTargetPolicy
                        targetRepeatable := by
                          intro empty
                          simp [empty] at hRepeatable
                      }
                      sourceReference
                      sourceDeclaration
                      sourceResolved := hSourceResolved
                      sourceNotTarget := by
                        intro equal
                        simp [equal] at hSelf
                      sourceScopeBound := hScope
                    }
                  else
                    .error (.scopeMismatch
                      targetDeclaration.path sourceDeclaration.path)
          | actual =>
              .error (.targetKindMismatch
                targetDeclaration.path actual.surfaceKind)
        else
          .error (.targetOutsideDeclaringGroup
            targetDeclaration.path declaringGroup)
      else
        .error (.target (.invalidRuleGroup declaringGroup))

/-- Shared execution faults for one checked addressed numeric operation. Direct leaves use `sourceRead`; resolved repeatable sources retain their wider addressing failures separately. -/
inductive AddressedNumericLeafFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | sourceRead (cause : CheckedDocumentError)
  | sourceAddressing (cause : CheckedAddressingError)
  | evaluation (cause : NumericComputationFault)
  | targetCheck (cause : NumericTargetCheckFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedNumericTarget

/-- The physically instantiated environments at the operation's exact target scope. Repetition comes from the computed target's own declaration, so an operation that references no field still iterates. -/
def targetEnvironments
    (target : CheckedAddressedNumericTarget model)
    (input : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  input.computationRowEnvironments target.targetDeclaration.repeatableScope

end CheckedAddressedNumericTarget

namespace CheckedAddressedNumericPlacement

def targetEnvironments
    (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  placement.target.targetEnvironments input

/-- Evaluate one already-checked scalar atom against the exact source cell selected by this placement. -/
def evaluateSourceAtom
    (placement : CheckedAddressedNumericPlacement model)
    (sourceCell : CheckedCell)
    (atom : ResolvedNumericAtom FlatFieldDecl) :
    Except NumericComputationFault NumericComputationResult :=
  let context : ScalarComputationContext := {
    read := fun field =>
      if field == placement.sourceDeclaration.id then
        sourceCell
      else
        malformedCheckedCell
  }
  context.readNumericComputationAtom atom

end CheckedAddressedNumericPlacement

namespace CheckedAddressedNumericTarget

private def executeAtEnvironmentUsing (placement : CheckedAddressedNumericTarget model)
    (input : CheckedDocument model)
    (checkTarget : NumericComputationResult → NumericTargetCheckResult)
    (evaluate : Env →
      Except AddressedNumericLeafFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) := do
  let environments ←
    (placement.targetEnvironments input).mapError .targetRows
  environments.mapM fun environment => do
    let path ←
      (environment.pathForScope
        placement.targetDeclaration.repeatableScope).mapError .environment
    let targetAddress : CellAddr := {
      field := placement.targetField
      path
    }
    let result ← evaluate environment
    let outcome ←
      match checkTarget result with
      | .supported outcome => pure outcome
      | .unsupported cause => throw (.targetCheck cause)
    pure {
      targetField := targetAddress
      outcome
      source := input.numericTargetPlacementStateAt targetAddress
    }

/-- Execute through the ordinary unsuppressed target checker. The callback receives the row
environment rather than the target's path, because a source addresses at its own scope. -/
def executeAtEnvironment (placement : CheckedAddressedNumericTarget model)
    (input : CheckedDocument model)
    (evaluate : Env →
      Except AddressedNumericLeafFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  placement.executeAtEnvironmentUsing input placement.targetPolicy.check evaluate

/-- Execute through this placement's own warning-suppressed target checker. -/
def executeAtEnvironmentScaleWarningSuppressed
    (placement : CheckedAddressedNumericTarget model)
    (input : CheckedDocument model)
    (evaluate : Env →
      Except AddressedNumericLeafFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  placement.executeAtEnvironmentUsing input
    placement.targetPolicy.checkWithScaleWarningSuppressed evaluate

end CheckedAddressedNumericTarget

namespace CheckedAddressedNumericPlacement

/-- Execute through the target half's ordinary unsuppressed checker. -/
def executeAtEnvironment (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (evaluate : Env →
      Except AddressedNumericLeafFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  placement.target.executeAtEnvironment input evaluate

/-- Execute through the target half's own warning-suppressed checker. -/
def executeAtEnvironmentScaleWarningSuppressed
    (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (evaluate : Env →
      Except AddressedNumericLeafFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  placement.target.executeAtEnvironmentScaleWarningSuppressed input evaluate

/-- Execute one source-cell evaluator through a caller-supplied exact-address view and the shared path-indexed target owner. -/
def executeWithRead (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (evaluate : CheckedCell →
      Except NumericComputationFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  placement.executeAtEnvironment input fun environment => do
    let sourcePath ←
      (environment.pathForScope
        placement.sourceDeclaration.repeatableScope).mapError .environment
    let sourceAddress : CellAddr := {
      field := placement.sourceDeclaration.id
      path := sourcePath
    }
    let sourceCell ← (read sourceAddress).mapError .sourceRead
    (evaluate sourceCell).mapError .evaluation

/-- Execute one source-cell evaluator through the immutable checked document. -/
def executeWith (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (evaluate : CheckedCell →
      Except NumericComputationFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  placement.executeWithRead input input.read evaluate

/-- Classify caller-read addressed outcomes against immutable source target state without collapsing their exact row keys. -/
def executeResultWithRead
    (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (evaluate : CheckedCell →
      Except NumericComputationFault NumericComputationResult)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumericLeafFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let outcomes ← placement.executeWithRead input read evaluate
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    MessagePointer.ofCellAddr payloadAt supplied outcomes)

/-- Immutable-document specialization of the shared addressed result projection. -/
def executeResultWith
    (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (evaluate : CheckedCell →
      Except NumericComputationFault NumericComputationResult)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumericLeafFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  placement.executeResultWithRead input input.read evaluate payloadAt supplied

end CheckedAddressedNumericPlacement

end A12Kernel
