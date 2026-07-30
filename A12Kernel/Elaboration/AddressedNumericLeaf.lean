import A12Kernel.Elaboration.NumericComputation.RunApplication

/-! # Shared same-scope repeatable numeric-leaf placement

This module owns the model-certified target/source placement and exact addressed execution seam shared by completed one-source numeric leaves. A specialized leaf still owns source-kind admission, static result scale, and the exact scalar evaluator it passes here.
-/

namespace A12Kernel

/-- Fail-closed errors for the shared same-scope repeatable placement. These are library diagnostics, not claims about kernel diagnostic precedence. -/
inductive AddressedNumericPlacementElabError where
  | model (cause : ResolveError)
  | target (cause : ResolveError)
  | source (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | targetPolicyUnavailable (path : List String)
  | targetNotRepeatable (path : List String)
  | targetSelfReference (field : FieldId)
  | scopeMismatch (target source : List String)
  deriving Repr, DecidableEq

/-- The common checked placement of one Number target and one source declaration at the same nonempty repeatable scope. -/
structure CheckedAddressedNumericPlacement (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  sourceReference : SurfaceFieldPath
  targetField : FieldId
  targetDeclaration : FlatFieldDecl
  targetPolicy : NumericTargetPolicy
  sourceDeclaration : FlatFieldDecl
  modelWellFormed : model.validate.isOk = true
  targetOwned :
    model.lookupUniqueId targetField = .ok targetDeclaration
  sourceResolved :
    model.resolveFieldDeclarationUnchecked declaringGroup sourceReference =
      .ok sourceDeclaration
  targetInDeclaringGroup :
    targetDeclaration.groupPath = declaringGroup
  targetPolicyOwned :
    targetDeclaration.toNumericTargetPolicy? = some targetPolicy
  targetRepeatable : targetDeclaration.repeatableScope ≠ []
  sourceNotTarget : sourceDeclaration.id ≠ targetField
  sameScope :
    sourceDeclaration.repeatableScope = targetDeclaration.repeatableScope

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
      if hGroup : targetDeclaration.groupPath = declaringGroup then
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
                    sourceDeclaration.repeatableScope =
                      targetDeclaration.repeatableScope then
                  .ok {
                    declaringGroup
                    sourceReference
                    targetField
                    targetDeclaration
                    targetPolicy
                    sourceDeclaration
                    modelWellFormed := by
                      rw [hModel]
                      rfl
                    targetOwned := hTargetOwned
                    sourceResolved := hSourceResolved
                    targetInDeclaringGroup := hGroup
                    targetPolicyOwned := hTargetPolicy
                    targetRepeatable := by
                      intro empty
                      simp [empty] at hRepeatable
                    sourceNotTarget := by
                      intro equal
                      simp [equal] at hSelf
                    sameScope := hScope
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

/-- Shared execution faults for one checked addressed numeric leaf. -/
inductive AddressedNumericLeafFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | sourceRead (cause : CheckedDocumentError)
  | evaluation (cause : NumericComputationFault)
  | targetCheck (cause : NumericTargetCheckFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedNumericPlacement

/-- The physically instantiated environments at the operation's exact target scope. -/
def targetEnvironments
    (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  input.actualRowEnvironments placement.targetDeclaration.repeatableScope

/-- Execute one source-cell evaluator per physical target environment and retain the exact row key for result classification and application. -/
def executeWith (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (evaluate : CheckedCell →
      Except NumericComputationFault NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) := do
  let environments ←
    (placement.targetEnvironments input).mapError .targetRows
  environments.mapM fun environment => do
    let path ←
      (environment.pathForScope
        placement.targetDeclaration.repeatableScope).mapError .environment
    let sourceAddress : CellAddr := {
      field := placement.sourceDeclaration.id
      path
    }
    let targetAddress : CellAddr := {
      field := placement.targetField
      path
    }
    let sourceCell ←
      (input.read sourceAddress).mapError .sourceRead
    let result ← (evaluate sourceCell).mapError .evaluation
    let outcome ←
      match placement.targetPolicy.check result with
      | .supported outcome => pure outcome
      | .unsupported cause => throw (.targetCheck cause)
    pure {
      targetField := targetAddress
      outcome
      source := input.numericTargetPlacementStateAt targetAddress
    }

/-- Classify shared addressed outcomes against the immutable source document without collapsing their exact row keys. -/
def executeResultWith
    (placement : CheckedAddressedNumericPlacement model)
    (input : CheckedDocument model)
    (evaluate : CheckedCell →
      Except NumericComputationFault NumericComputationResult)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumericLeafFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let outcomes ← placement.executeWith input evaluate
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    ComputationErrorPointer.ofCellAddr payloadAt supplied outcomes)

end CheckedAddressedNumericPlacement

end A12Kernel
