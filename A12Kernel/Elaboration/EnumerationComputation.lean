import A12Kernel.Elaboration.Flat.Context
import A12Kernel.Elaboration.ComputationNormalForm
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Semantics.FirstFilledValue

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

inductive EnumerationComputationElabError where
  | resolve (error : ResolveError)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | source (error : ElabError)
  | literalOutsideTarget (targetPath : List String) (literal : String)
  | sourceIncompatible (sourcePath targetPath : List String)
  | copyComparison (targetPath sourcePath : List String) (refusal : CopyComparisonRefusal)
  /-- A String the generated comparison admits into an unlabelled target, which the calculation then
      refuses. -/
  | stringSource (sourcePath targetPath : List String)
  /-- An Enumeration whose display the comparison admits, reading a token the target does not
      declare. -/
  | sourceOutsideTargetDomain (sourcePath targetPath : List String)
  | targetSelfReference (field : FieldId)
  | targetSelfReferenceAtDirectField (field : FieldId)
  | targetSelfReferenceAtCompatibleCategory (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

namespace EnumerationComputationElabError

/-- The comparison refusals carry a measured Kernel identity: the literal-domain refusal
([checkpoint](../../docs/sources/temporal-constant-and-base-year-probes.md#src-constant-literal-family-gate)) and a copied field's
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)).
The calculation's own refusals are `calculationRefusal?`'s. The others are this project's own
routing, or gates whose Kernel class was never observed, so they claim none. -/
def diagnostic? : EnumerationComputationElabError → Option KernelStaticDiagnostic
  | .literalOutsideTarget _ _ => some .invalidStringConstantForEnumComparison
  | .copyComparison _ _ refusal => some refusal.diagnostic
  | .resolve _ | .targetKindMismatch _ _ | .source _
  | .sourceIncompatible _ _ | .stringSource _ _ | .sourceOutsideTargetDomain _ _
  | .targetSelfReference _
  | .targetSelfReferenceAtDirectField _
  | .targetSelfReferenceAtCompatibleCategory _
  | .incoherentCore => none

/-- The calculation's own class for a source the comparison admitted, measured for a String into an
unlabelled target and for a wider Enumeration
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)),
and for a category whose tokens leave the target's domain
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-enum-source)). -/
def calculationRefusal? : EnumerationComputationElabError → Option CalculationRefusal
  | .stringSource _ _ | .sourceOutsideTargetDomain _ _ => some .invalidEnumCalculation
  | _ => none

/-- Project the measured direct and compatible-category Enumeration
target-reference refusals to their distinct Kernel diagnostic classes. Domain,
display, kind, and resolution failures remain local until separately measured. -/
def targetDiagnostic? :
    EnumerationComputationElabError → Option KernelStaticDiagnostic
  | .targetSelfReferenceAtDirectField _ =>
      some .errorReferenceToCalculatedField
  | .targetSelfReferenceAtCompatibleCategory _ =>
      some .errorSemanticIndexOrCategoryForErrorField
  | _ => none

end EnumerationComputationElabError

/-- The exact ordinary closed-Enumeration target shared by every checked source form. -/
structure CheckedEnumerationComputationTarget (model : FlatModel) where
  private mk ::
  path : List String
  targetOperand : FlatEnumerationOperand
  projection : CheckedEnumerationProjection
  targetOwned : model.checkedEnumerationOperand? targetOperand = some projection
  modelWellFormed : model.validate.isOk = true

namespace CheckedEnumerationComputationTarget

/-- The computation target is definitionally the exact field certified by its model-owned Enumeration operand. -/
def field (target : CheckedEnumerationComputationTarget model) : FieldId :=
  target.targetOperand.field.id

end CheckedEnumerationComputationTarget

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

/-- The comparison the computation generates between its target and a directly copied stored field,
asked after the target's read and then the copied field's read. The comparison answers ahead of the
calculation, so where a wider source's display fails too, the display class is the one drawn
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)).
A category read skips the display arm and has no spelling on another kind's target here. -/
private def FlatModel.checkEnumerationCopyComparison (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId) :
    SurfaceEnumerationComputationSource → Except EnumerationComputationElabError Unit
  | .field (.direct reference) => do
      let target ← (model.resolveNonrepeatableDeclarationById targetField).mapError .resolve
      if target.fieldValueReadRefusal?.isNone then
        let source ← (model.resolveProjectedFieldValueRead declaringGroup reference .stored).mapError
          (.source ∘ .resolve)
        match target.copyComparisonRefusal? source, target.policy.kind,
            source.toTextFieldComparison? with
        | some refusal, _, _ => throw (.copyComparison target.path source.path refusal)
        | none, .enumeration, some (_, .plainString) =>
            throw (.stringSource source.path target.path)
        | _, _, _ => pure ()
  | _ => pure ()

/-- Check one ordinary closed-Enumeration target together with a literal or direct stored/category source. General String expressions cannot inhabit this surface. -/
def elaborateEnumerationComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceEnumerationComputationSource) :
    Except EnumerationComputationElabError
      (CheckedEnumerationComputationOperation model) :=
  do
    let target ← match elaborateEnumerationComputationTarget model targetField with
      | .ok target => pure target
      | .error (.targetKindMismatch path actual) => do
          model.checkEnumerationCopyComparison declaringGroup targetField authored
          throw (.targetKindMismatch path actual)
      | .error error => throw error
    model.checkEnumerationCopyComparison declaringGroup targetField authored
    let source ← match authored with
      | .literal token =>
          pure (.literal token)
      | .field surface =>
          -- The copied field is a bracketed read, whose gates answer ahead of the operand's own.
          discard <| (model.resolveProjectedFieldValueRead declaringGroup surface.reference
            surface.projectionRef).mapError (.source ∘ .resolve)
          let (path, _, operand) ←
            elaborateEnumerationFieldOperand model declaringGroup surface
              |>.mapError .source
          match hSourceOwned :
              model.checkedEnumerationOperand? operand with
          | none => throw .incoherentCore
          | some checked =>
              pure (.field path operand checked hSourceOwned)
    if hReference : source.referencesField target.field = true then
      match source with
      | .literal _ => throw .incoherentCore
      | .field _ operand _ _ =>
          match operand.projectionRef with
          | .stored =>
              throw (.targetSelfReferenceAtDirectField target.field)
          | .category _ =>
              if source.allowedFor target.projection then
                throw (.targetSelfReferenceAtCompatibleCategory target.field)
              else
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
      -- The display arm has already answered for a stored source, and a category read has none, so
      -- what remains is the domain.
      | .field sourcePath _ _ _ =>
          throw (.sourceOutsideTargetDomain sourcePath target.path)

namespace CheckedEnumerationComputationOperation

/-- Use the exact model-owned checked context, then project the shared token computation result into the common String-shaped target result. -/
def evaluate (operation : CheckedEnumerationComputationOperation model)
    (raw : RawFlatContext) : StringTargetOutcome :=
  (operation.source.evaluate (model.checkContext raw)).asExactStringTargetOutcome

end CheckedEnumerationComputationOperation

end A12Kernel
