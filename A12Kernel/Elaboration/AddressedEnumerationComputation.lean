import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.StringComputationRunApplication

/-! # Repeatable Enumeration computation

This capsule extends the ordinary literal and direct stored/category Enumeration source surface to one exact repeatable target. It enumerates physical target rows, reads each field source at its own bound scope, and retains exact target addresses through the established String-shaped result and cell-state application fold.

Stars, filters, sibling parallel iteration, row reconstruction, and scheduling remain separate.
-/

namespace A12Kernel

/-- The ordinary Enumeration refusal domain plus the three placement-specific boundaries. -/
inductive AddressedEnumerationComputationElabError where
  | ordinary (cause : EnumerationComputationElabError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | scopeMismatch (target source : List String)
  deriving Repr, DecidableEq

namespace AddressedEnumerationComputationElabError

def targetDiagnostic? :
    AddressedEnumerationComputationElabError → Option KernelStaticDiagnostic
  | .ordinary cause => cause.targetDiagnostic?
  | _ => none

end AddressedEnumerationComputationElabError

/-- One repeatable stored-Enumeration target tied to its validated model. -/
structure CheckedAddressedEnumerationTarget (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  targetField : FieldId
  declaration : FlatFieldDecl
  enumeration : EnumerationDeclaration
  checked : CheckedEnumerationDeclaration
  projection : CheckedEnumerationProjection
  modelWellFormed : model.validate.isOk = true
  owned : model.lookupUniqueId targetField = .ok declaration
  targetKind : declaration.policy.kind = .enumeration
  enumerationOwned : declaration.enumeration = some enumeration
  checkedExact : elaborateEnumeration enumeration = .ok checked
  projectionExact : checkEnumerationProjection checked .stored = .ok projection
  inDeclaringGroup : declaration.groupPath = declaringGroup
  repeatable : declaration.repeatableScope ≠ []

namespace CheckedAddressedEnumerationTarget

def field (target : CheckedAddressedEnumerationTarget model) : FieldId :=
  target.targetField

end CheckedAddressedEnumerationTarget

/-- A literal or exact addressed stored/category Enumeration source. -/
inductive CheckedAddressedEnumerationSource (model : FlatModel)
    (targetScope : List RepeatableLevel) where
  | literal (token : String)
  | field (declaringGroup : GroupPath) (reference : SurfaceFieldPath)
      (declaration : FlatFieldDecl) (operand : FlatEnumerationOperand)
      (enumeration : EnumerationDeclaration)
      (checked : CheckedEnumerationDeclaration)
      (projection : CheckedEnumerationProjection)
      (resolved : model.resolveFieldDeclarationUnchecked declaringGroup reference =
        .ok declaration)
      (sourceKind : declaration.policy.kind = .enumeration)
      (enumerationOwned : declaration.enumeration = some enumeration)
      (checkedExact : elaborateEnumeration enumeration = .ok checked)
      (projectionExact :
        checkEnumerationProjection checked operand.projectionRef = .ok projection)
      (scopeBound : declaration.repetitionBoundBy targetScope = true)

namespace CheckedAddressedEnumerationSource

def referencesField (source : CheckedAddressedEnumerationSource model scope)
    (field : FieldId) : Bool :=
  match source with
  | .literal _ => false
  | .field _ _ _ operand _ _ _ _ _ _ _ _ _ => operand.field.id == field

def allowedFor (target : CheckedEnumerationProjection) :
    CheckedAddressedEnumerationSource model scope → Bool
  | .literal token => target.declaration.literalAllowed target.projection token
  | .field _ _ _ _ _ _ projection _ _ _ _ _ _ =>
      projection.compatibleWithTarget target

end CheckedAddressedEnumerationSource

/-- One bounded repeatable Enumeration assignment with target/source scope certificates. -/
structure CheckedAddressedEnumerationComputation (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  target : CheckedAddressedEnumerationTarget model
  source : CheckedAddressedEnumerationSource model target.declaration.repeatableScope
  sourceAllowed : source.allowedFor target.projection = true
  targetNotReferenced : source.referencesField target.field = false

def checkAddressedEnumerationTarget
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Except AddressedEnumerationComputationElabError
      (CheckedAddressedEnumerationTarget model) :=
  match hModel : model.validate with
  | .error cause => .error (.ordinary (.resolve cause))
  | .ok () =>
    match hOwned : model.lookupUniqueId targetField with
    | .error cause => .error (.ordinary (.resolve cause))
    | .ok declaration =>
      if hGroup : declaration.groupPath = declaringGroup then
        match hKind : declaration.policy.kind, hEnumeration : declaration.enumeration with
        | .enumeration, some source =>
          match hChecked : elaborateEnumeration source with
          | .error _ => .error (.ordinary .incoherentCore)
          | .ok checked =>
            match hProjection : checkEnumerationProjection checked .stored with
            | .error _ => .error (.ordinary .incoherentCore)
            | .ok projection =>
              if hRepeatable : declaration.repeatableScope.isEmpty then
                .error (.targetNotRepeatable declaration.path)
              else
                .ok {
                  declaringGroup, targetField, declaration
                  enumeration := source
                  checked
                  projection
                  modelWellFormed := by rw [hModel]; rfl
                  owned := hOwned
                  targetKind := hKind
                  enumerationOwned := hEnumeration
                  checkedExact := hChecked
                  projectionExact := hProjection
                  inDeclaringGroup := hGroup
                  repeatable := by
                    intro empty
                    simp [empty] at hRepeatable
                }
        | actual, _ =>
            .error (.ordinary (.targetKindMismatch declaration.path actual.surfaceKind))
      else
        .error (.targetOutsideDeclaringGroup declaration.path declaringGroup)

private def checkAddressedEnumerationSource
    (model : FlatModel) (declaringGroup : GroupPath)
    (target : CheckedAddressedEnumerationTarget model)
    (authored : SurfaceEnumerationComputationSource) :
    Except AddressedEnumerationComputationElabError
      (CheckedAddressedEnumerationSource model target.declaration.repeatableScope) := do
  match authored with
  | .literal token => pure (.literal token)
  | .field surface =>
    let reference := match surface with
      | .direct field | .category field _ => field
    let projectionRef : EnumerationProjectionRef := match surface with
      | .direct _ => .stored
      | .category _ name => .category name
    match hResolved :
        model.resolveFieldDeclarationUnchecked declaringGroup reference with
    | .error cause => throw (.ordinary (.source (.resolve cause)))
    | .ok declaration =>
      if hScope : declaration.repetitionBoundBy
          target.declaration.repeatableScope = true then
        match hKind : declaration.policy.kind,
            hEnumeration : declaration.enumeration with
        | .enumeration, some source =>
          match hChecked : elaborateEnumeration source with
          | .error _ => throw (.ordinary .incoherentCore)
          | .ok checked =>
            match hProjection : checkEnumerationProjection checked projectionRef with
            | .error cause => throw (.ordinary (.source
                (.enumerationOperand declaration.path cause)))
            | .ok projection =>
              let operand : FlatEnumerationOperand := {
                field := { id := declaration.id }
                projectionRef
                projection := projection.projection
              }
              pure (.field declaringGroup reference declaration operand source checked
                projection hResolved hKind hEnumeration hChecked hProjection hScope)
        | actual, _ =>
            throw (.ordinary (.source
              (.textFieldOperandKindMismatch declaration.path actual.surfaceKind)))
      else
        throw (.scopeMismatch target.declaration.path declaration.path)

/-- Check one repeatable Enumeration target with the complete ordinary literal/direct/category source surface. -/
def checkAddressedEnumerationComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceEnumerationComputationSource) :
    Except AddressedEnumerationComputationElabError
      (CheckedAddressedEnumerationComputation model) := do
  let target ← checkAddressedEnumerationTarget model declaringGroup targetField
  let source ← checkAddressedEnumerationSource model declaringGroup target authored
  if hReference : source.referencesField target.field = true then
    match source with
    | .literal _ => throw (.ordinary .incoherentCore)
    | .field _ _ _ operand _ _ _ _ _ _ _ _ _ =>
      match operand.projectionRef with
      | .stored =>
          throw (.ordinary (.targetSelfReferenceAtDirectField target.field))
      | .category _ =>
          if source.allowedFor target.projection then
            throw (.ordinary
              (.targetSelfReferenceAtCompatibleCategory target.field))
          else
            throw (.ordinary (.targetSelfReference target.field))
  else if hAllowed : source.allowedFor target.projection = true then
    pure {
      declaringGroup, target, source
      sourceAllowed := hAllowed
      targetNotReferenced := by
        cases hValue : source.referencesField target.field with
        | false => rfl
        | true => exact False.elim (hReference hValue)
    }
  else
    match source with
    | .literal token =>
        throw (.ordinary (.literalOutsideTarget target.declaration.path token))
    | .field _ _ declaration _ _ _ _ _ _ _ _ _ _ =>
        throw (.ordinary
          (.sourceIncompatible declaration.path target.declaration.path))

inductive AddressedEnumerationComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | sourceRead (cause : CheckedDocumentError)
  deriving Repr, DecidableEq

/-- Enumeration's public name for the shared exact-address token outcome. -/
abbrev AddressedEnumerationComputationOutcome := AddressedTokenComputationOutcome

/-- One checked addressed Enumeration result backed by the common String channels. -/
structure AddressedEnumerationComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedEnumerationComputation model
  string : StringComputationRunView ResidualMessage CellAddr

/-- Classify supplied exact-address Enumeration outcomes against immutable source-target state without attaching a checked operation identity. -/
def projectAddressedEnumerationResults
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedEnumerationComputationOutcome) :
    StringComputationRunView ResidualMessage CellAddr :=
  projectAddressedTokenResults input residualMessages outcomes

namespace CheckedAddressedEnumerationComputation

private def fieldResult (operand : FlatEnumerationOperand) (cell : CheckedCell) :
    TokenComputationResult :=
  match (FlatTextFieldOperand.enumeration operand).checkedValueListCellAt
      .computation cell with
  | .empty => .noValue
  | .present token => .value token
  | .unknown cause => .poison cause

private def evaluateAtWithRead
    (operation : CheckedAddressedEnumerationComputation model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedEnumerationComputationFault
      AddressedEnumerationComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.declaration.repeatableScope
      |>.mapError .environment
  let result ← match operation.source with
    | .literal token => pure (.value token)
    | .field _ _ declaration operand _ _ _ _ _ _ _ _ _ => do
      let sourcePath ← environment.pathForScope declaration.repeatableScope
        |>.mapError .environment
      let cell ← read { field := declaration.id, path := sourcePath }
        |>.mapError .sourceRead
      pure (fieldResult operand cell)
  pure {
    targetField := { field := operation.target.field, path := targetPath }
    result
  }

/-- Execute once per physically instantiated target row while reading through one caller-supplied transient overlay. Target-row ownership remains with the immutable checked input. -/
def executeWithRead (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedEnumerationComputationFault
      (List AddressedEnumerationComputationOutcome) := do
  let environments ← input.actualRowEnvironments
      operation.target.declaration.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead read)

/-- Execute once per physically instantiated target row in document order against the immutable input. -/
def execute (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationComputationFault
      (List AddressedEnumerationComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Execute and classify each exact target address against the immutable source target state. -/
def executeResult (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedEnumerationComputationFault
      (AddressedEnumerationComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure {
    operation
    string := projectAddressedEnumerationResults input residualMessages outcomes
  }

end CheckedAddressedEnumerationComputation

namespace AddressedEnumerationComputationRunView

/-- Apply only retained exact-address actions to a separate same-model destination cell-state projection. -/
def applyToChecked
    (view : AddressedEnumerationComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end AddressedEnumerationComputationRunView

end A12Kernel
