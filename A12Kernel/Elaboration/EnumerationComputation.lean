import A12Kernel.Elaboration.Flat.Context
import A12Kernel.Semantics.FirstFilledValue
import A12Kernel.Semantics.StringComputation

/-! # Checked ordinary Enumeration computation targets

This capsule checks the narrow ordinary closed-Enumeration computation surface separately from general String expressions. Literal, direct Enumeration, and category sources reuse the existing checked projection and exact-token computation result. Target-domain and direct-display compatibility are static obligations; runtime evaluation adds no second token reader or target-result type.
-/

namespace A12Kernel

/-- The complete first ordinary-Enumeration operation surface: one constant or one direct stored/category field read. `FirstFilledValue` remains a separate source shape because it has its own list legality and scan semantics. -/
inductive SurfaceEnumerationComputationSource where
  | literal (token : String)
  | field (operand : SurfaceTextFieldOperand)
  deriving Repr, DecidableEq

/-- One source already tied to the exact validated flat model. The field case retains the existing checked Enumeration projection instead of defining another token reader. -/
inductive CheckedEnumerationComputationSource (model : FlatModel) where
  | literal (token : String)
  | field (path : List String) (operand : FlatEnumerationOperand)
      (checked : CheckedEnumerationProjection)
      (owned : model.checkedEnumerationOperand? operand = some checked)

namespace CheckedEnumerationProjection

/-- Every possible projected source token must belong to the target domain. A direct stored-Enumeration source additionally preserves display remapping compatibility; an explicit category has already selected its target-visible token domain and bypasses that direct-display gate. -/
def compatibleWithTarget (source target : CheckedEnumerationProjection) : Bool :=
  let domainFits := source.selectedTokens.all fun token =>
    target.declaration.literalAllowed target.projection token
  let displayFits := match source.projectionRef with
    | .stored =>
        directFieldComparisonAllowed
          source.declaration.directComparableField
          target.declaration.directComparableField
    | .category _ => true
  domainFits && displayFits

end CheckedEnumerationProjection

namespace CheckedEnumerationComputationSource

def referencesField (source : CheckedEnumerationComputationSource model)
    (field : FieldId) : Bool :=
  match source with
  | .literal _ => false
  | .field _ operand _ _ => operand.field.id == field

def allowedFor (target : CheckedEnumerationProjection) :
    CheckedEnumerationComputationSource model → Bool
  | .literal token => target.declaration.literalAllowed target.projection token
  | .field _ _ checked _ => checked.compatibleWithTarget target

/-- Evaluate through the established computation-phase checked-cell projection and exact-token result. -/
def evaluate (context : FlatContext) :
    CheckedEnumerationComputationSource model → TokenComputationResult
  | .literal token => .value token
  | .field _ operand _ _ =>
      match (FlatTextFieldOperand.enumeration operand).checkedValueListCellAt
          .computation (context.read operand.field.id) with
      | .empty => .noValue
      | .present token => .value token
      | .unknown cause => .poison cause

end CheckedEnumerationComputationSource

namespace TokenComputationResult

/-- Project an exact-token computation into the common String-shaped target result. Static Enumeration compatibility makes an out-of-domain value unrepresentable; the empty check defensively preserves the common root-store rule. -/
def asEnumerationTargetOutcome : TokenComputationResult → StringTargetOutcome
  | .value token =>
      if nonempty : token ≠ "" then
        .accepted { text := token, nonempty }
      else
        .noValue
  | .noValue => .noValue
  | .poison cause => .poison cause

end TokenComputationResult

inductive EnumerationComputationElabError where
  | resolve (error : ResolveError)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | source (error : ElabError)
  | literalOutsideTarget (targetPath : List String) (literal : String)
  | sourceIncompatible (sourcePath targetPath : List String)
  | targetSelfReference (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

/-- The exact ordinary closed-Enumeration target shared by every checked source form. -/
structure CheckedEnumerationComputationTarget (model : FlatModel) where
  field : FieldId
  path : List String
  targetOperand : FlatEnumerationOperand
  projection : CheckedEnumerationProjection
  targetOwned : model.checkedEnumerationOperand? targetOperand = some projection
  modelWellFormed : model.validate.isOk = true

/-- Resolve and certify an ordinary nonrepeatable closed-Enumeration computation target once. -/
def elaborateEnumerationComputationTarget
    (model : FlatModel) (targetField : FieldId) :
    Except EnumerationComputationElabError
      (CheckedEnumerationComputationTarget model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let targetDeclaration ←
        (model.resolveNonrepeatableDeclarationById targetField).mapError .resolve
      match targetDeclaration.policy.kind, targetDeclaration.enumeration with
      | .enumeration, some targetSource =>
          let targetChecked ← match elaborateEnumeration targetSource with
            | .ok checked => pure checked
            | .error _ => throw .incoherentCore
          let targetOperand : FlatEnumerationOperand := {
            field := { id := targetField }
            projectionRef := .stored
            projection := targetChecked.storedProjection
          }
          match hTargetOwned : model.checkedEnumerationOperand? targetOperand with
          | none => throw .incoherentCore
          | some projection =>
              pure {
                field := targetField
                path := targetDeclaration.path
                targetOperand
                projection
                targetOwned := hTargetOwned
                modelWellFormed := by
                  rw [hModel]
                  rfl
              }
      | actual, _ =>
          throw (.targetKindMismatch targetDeclaration.path actual.surfaceKind)

/-- One checked ordinary Enumeration computation. The target and every field source are re-derived from the same validated model, while compatibility and self-reference remain proof-bearing static obligations. -/
structure CheckedEnumerationComputationOperation (model : FlatModel) where
  target : CheckedEnumerationComputationTarget model
  source : CheckedEnumerationComputationSource model
  sourceAllowed : source.allowedFor target.projection = true
  targetNotReferenced : source.referencesField target.field = false

/-- Check one ordinary closed-Enumeration target together with a literal or direct stored/category source. General String expressions cannot inhabit this surface. -/
def elaborateEnumerationComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceEnumerationComputationSource) :
    Except EnumerationComputationElabError
      (CheckedEnumerationComputationOperation model) :=
  do
    let target ← elaborateEnumerationComputationTarget model targetField
    let source ← match authored with
      | .literal token =>
          pure (.literal token)
      | .field surface =>
          let (path, _, operand) ←
            elaborateEnumerationFieldOperand model declaringGroup surface
              |>.mapError .source
          match hSourceOwned :
              model.checkedEnumerationOperand? operand with
          | none => throw .incoherentCore
          | some checked =>
              pure (.field path operand checked hSourceOwned)
    if hReference : source.referencesField target.field = true then
      throw (.targetSelfReference target.field)
    else if hAllowed : source.allowedFor target.projection = true then
      pure {
        target
        source
        sourceAllowed := hAllowed
        targetNotReferenced := by
          cases hValue : source.referencesField target.field with
          | false => rfl
          | true => exact False.elim (hReference hValue)
      }
    else
      match source with
      | .literal token =>
          throw (.literalOutsideTarget target.path token)
      | .field sourcePath _ _ _ =>
          throw (.sourceIncompatible sourcePath target.path)

namespace CheckedEnumerationComputationOperation

/-- Use the exact model-owned checked context, then project the shared token computation result into the common String-shaped target result. -/
def evaluate (operation : CheckedEnumerationComputationOperation model)
    (raw : RawFlatContext) : StringTargetOutcome :=
  (operation.source.evaluate (model.checkContext raw)).asEnumerationTargetOutcome

end CheckedEnumerationComputationOperation

end A12Kernel
