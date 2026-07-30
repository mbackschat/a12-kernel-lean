import A12Kernel.Elaboration.NumericComputation.RunApplication

/-! # Same-scope repeatable `FieldValueAsNumber`

This capsule admits one ordinary repeatable Number target whose sole expression is `FieldValueAsNumber` over a checked String declaration in the same repeatable scope. Execution enumerates physically instantiated target environments, reads the exact checked String cell, and delegates conversion, target checking, source-relative result classification, and retained-action application to their existing owners.

Enumeration/category conversion, other numeric expressions, guards, cascades, and scheduling remain separate.
-/

namespace A12Kernel

/-- Fail-closed errors for the bounded same-scope repeatable placement. These are library diagnostics, not claims about kernel diagnostic precedence. -/
inductive AddressedFieldValueAsNumberElabError where
  | model (cause : ResolveError)
  | target (cause : ResolveError)
  | source (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | targetPolicyUnavailable (path : List String)
  | targetNotRepeatable (path : List String)
  | targetSelfReference (field : FieldId)
  | sourceKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | sourceNotConvertible (path : List String)
  | scopeMismatch (target source : List String)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

/-- One exact same-scope repeatable String-to-Number operation certified against a validated model. -/
structure CheckedAddressedFieldValueAsNumber (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  sourceReference : SurfaceFieldPath
  targetField : FieldId
  targetDeclaration : FlatFieldDecl
  targetPolicy : NumericTargetPolicy
  sourceDeclaration : FlatFieldDecl
  source : ResolvedFieldValueAsNumberSource
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
  sourceCertified :
    sourceDeclaration.resolveFieldValueAsNumberSource .stored = .ok source
  sourceString :
    ∃ field, source.operand = .string field
  targetRepeatable : targetDeclaration.repeatableScope ≠ []
  sameScope :
    sourceDeclaration.repeatableScope = targetDeclaration.repeatableScope
  sameScale : source.scale = targetPolicy.info.scale

/-- Validate the exact repeatable placement without widening the existing nonrepeatable numeric-expression elaborator. -/
def checkAddressedFieldValueAsNumber
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedFieldValueAsNumberElabError
      (CheckedAddressedFieldValueAsNumber model) :=
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
                if sourceDeclaration.id == targetField then
                  .error (.targetSelfReference targetField)
                else
                  match hSourceKind : sourceDeclaration.policy.kind with
                  | .string =>
                    match hSourceCertified :
                        sourceDeclaration.resolveFieldValueAsNumberSource
                          .stored with
                    | .error _ =>
                        .error
                          (.sourceNotConvertible sourceDeclaration.path)
                    | .ok source =>
                      match hSourceString : source.operand with
                      | .enumeration _ =>
                          .error
                            (.sourceNotConvertible sourceDeclaration.path)
                      | .string field =>
                        if hScope :
                            sourceDeclaration.repeatableScope =
                              targetDeclaration.repeatableScope then
                          if hScale :
                              source.scale = targetPolicy.info.scale then
                            .ok {
                              declaringGroup
                              sourceReference
                              targetField
                              targetDeclaration
                              targetPolicy
                              sourceDeclaration
                              source
                              modelWellFormed := by
                                rw [hModel]
                                rfl
                              targetOwned := hTargetOwned
                              sourceResolved := hSourceResolved
                              targetInDeclaringGroup := hGroup
                              targetPolicyOwned := hTargetPolicy
                              sourceCertified := hSourceCertified
                              sourceString := ⟨field, hSourceString⟩
                              targetRepeatable := by
                                intro empty
                                simp [empty] at hRepeatable
                              sameScope := hScope
                              sameScale := hScale
                            }
                          else
                            .error (.scaleMismatch
                              targetPolicy.info.scale source.scale)
                        else
                          .error (.scopeMismatch
                            targetDeclaration.path sourceDeclaration.path)
                  | actual =>
                      .error (.sourceKindMismatch
                        sourceDeclaration.path actual.surfaceKind)
        | actual =>
            .error (.targetKindMismatch
              targetDeclaration.path actual.surfaceKind)
      else
        .error (.targetOutsideDeclaringGroup
          targetDeclaration.path declaringGroup)

inductive AddressedFieldValueAsNumberFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | sourceRead (cause : CheckedDocumentError)
  | evaluation (cause : NumericComputationFault)
  | targetCheck (cause : NumericTargetCheckFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedFieldValueAsNumber

/-- The physically instantiated environments at the operation's exact target scope. -/
def targetEnvironments
    (operation : CheckedAddressedFieldValueAsNumber model)
    (input : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  input.actualRowEnvironments operation.targetDeclaration.repeatableScope

/-- Execute one addressed instance per physical target environment and retain the exact row key for later result classification and application. -/
def execute (operation : CheckedAddressedFieldValueAsNumber model)
    (input : CheckedDocument model) :
    Except AddressedFieldValueAsNumberFault
      (List (SourcedNumericTargetOutcome CellAddr)) := do
  let environments ←
    (operation.targetEnvironments input).mapError .targetRows
  environments.mapM fun environment => do
    let path ←
      (environment.pathForScope
        operation.targetDeclaration.repeatableScope).mapError .environment
    let sourceAddress : CellAddr := {
      field := operation.sourceDeclaration.id
      path
    }
    let targetAddress : CellAddr := {
      field := operation.targetField
      path
    }
    let sourceCell ←
      (input.read sourceAddress).mapError .sourceRead
    let context : ScalarComputationContext := {
      read := fun field =>
        if field == operation.sourceDeclaration.id then
          sourceCell
        else
          malformedCheckedCell
    }
    let result ←
      (context.readNumericComputationAtom
        (.fieldValueAsNumber operation.source)).mapError .evaluation
    let outcome ←
      match operation.targetPolicy.check result with
      | .supported outcome => pure outcome
      | .unsupported cause => throw (.targetCheck cause)
    pure {
      targetField := targetAddress
      outcome
      source := input.numericTargetPlacementStateAt targetAddress
    }

/-- Classify the addressed rich outcomes against the immutable source document without collapsing their exact row keys. -/
def executeResult
    (operation : CheckedAddressedFieldValueAsNumber model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedFieldValueAsNumberFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let outcomes ← operation.execute input
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    ComputationErrorPointer.ofCellAddr payloadAt supplied outcomes)

end CheckedAddressedFieldValueAsNumber

end A12Kernel
