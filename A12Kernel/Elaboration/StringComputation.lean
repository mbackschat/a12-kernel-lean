import A12Kernel.Elaboration.StringContext
import A12Kernel.Semantics.StringComputation

/-! # Checked String-computation expression lowering

This capsule resolves parser-independent field paths in copy/literal/`RangeAsString`/concatenation expressions into the existing `StringExpr FieldId` runtime tree. It accepts only nonrepeatable String declarations from one validated flat model. `RangeAsString` preserves the kernel's static gate order: resolve the nonrepeatable field shape, check 1-based inclusive bounds, then certify the String value kind. The integrated ordinary-target entry point additionally retains the declaration-owned line-break/minimum/maximum policy and rejects direct target self-reference before evaluation. Alternatives, concrete syntax, repeatable reads, patterns, raw/custom targets, and scheduling remain outside.
-/

namespace A12Kernel

/-- Fail-closed errors owned by checked String-computation expression lowering. Keeping this domain local avoids widening validation or public reference diagnostics. -/
inductive StringComputationElabError where
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | invalidRange (start finish : Nat)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | rawStringTarget (path : List String)
  | customStringTarget (path : List String)
  | patternStringTarget (path : List String)
  | targetSelfReference (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Admit one already-resolved nonrepeatable declaration as a String-value computation leaf. -/
def admitStringComputationValueField
    (declaration : FlatFieldDecl) : Except StringComputationElabError FieldId :=
  match declaration.toStringValueField? with
  | some field => pure field.id
  | none =>
      if declaration.isRawString then
        throw (.rawStringValue declaration.path)
      else
        throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)

/-- Resolve one legal nonrepeatable String-value field for scalar String computation syntax. -/
def elaborateStringValueField (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except StringComputationElabError FieldId := do
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
  admitStringComputationValueField declaration

/-- Whether one runtime leaf is the exact nonrepeatable String-value declaration in the model. -/
private def FlatModel.admitsStringComputationOperand (model : FlatModel)
    (fieldId : FieldId) : Bool :=
  match model.lookupUniqueId fieldId with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toStringValueField? == some { id := fieldId }
  | .error _ => false

namespace StringExpr

/-- Check that every runtime leaf names the exact nonrepeatable String declaration in one model. -/
def wellFormedBool (model : FlatModel) : StringExpr FieldId → Bool
  | StringExpr.field fieldId =>
      model.admitsStringComputationOperand fieldId
  | StringExpr.literal _ => true
  | StringExpr.range fieldId start finish =>
      validStringRange start finish &&
        model.admitsStringComputationOperand fieldId
  | StringExpr.concat left right =>
      left.wellFormedBool model && right.wellFormedBool model

def WellFormed (expression : StringExpr FieldId) (model : FlatModel) : Prop :=
  expression.wellFormedBool model = true

/-- Whether the resolved expression contains the named field anywhere in its authored tree. -/
def referencesField (field : FieldId) : StringExpr FieldId → Bool
  | .field candidate => candidate == field
  | .literal _ => false
  | .range candidate _ _ => candidate == field
  | .concat left right => left.referencesField field || right.referencesField field

end StringExpr

/-- A lowered String expression certified against the same model used to resolve all of its leaves. -/
structure CheckedStringExpr (model : FlatModel) where
  core : StringExpr FieldId
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- The exact ordinary nonrepeatable String target/policy relation retained by checked computation lowering. -/
def FlatModel.admitsStringComputationTarget (model : FlatModel)
    (field : FieldId) (policy : StringFieldPolicy) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.policy.kind == .string &&
        declaration.stringValueMode == .evaluated &&
        declaration.customType.isNone &&
        declaration.stringPatternSource.isNone &&
        declaration.enumeration.isNone &&
        declaration.stringPolicy == policy
  | .error _ => false

/-- One ordinary String target and expression certified against the same validated model. Target policy cannot be substituted after elaboration. -/
structure CheckedStringComputationOperation (model : FlatModel) where
  expression : CheckedStringExpr model
  targetField : FieldId
  targetPolicy : StringFieldPolicy
  targetAdmitted : model.admitsStringComputationTarget targetField targetPolicy = true
  targetNotReferenced : expression.core.referencesField targetField = false

/-- Resolve one authored String-expression tree without evaluating or reordering it. The caller supplies a validated model; each field still passes through the shared nonrepeatable path resolver. -/
def elaborateStringExprCore (model : FlatModel) (declaringGroup : GroupPath) :
    StringExpr SurfaceFieldPath →
      Except StringComputationElabError (StringExpr FieldId)
  | StringExpr.field reference => do
      pure (.field (← elaborateStringValueField model declaringGroup reference))
  | StringExpr.literal value => pure (.literal value)
  | StringExpr.range reference start finish => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      if !validStringRange start finish then
        throw (.invalidRange start finish)
      pure (.range (← admitStringComputationValueField declaration) start finish)
  | StringExpr.concat left right => do
      pure (.concat
        (← elaborateStringExprCore model declaringGroup left)
        (← elaborateStringExprCore model declaringGroup right))

private def certifyStringExpr (model : FlatModel)
    (hModel : model.validate = .ok ()) (core : StringExpr FieldId) :
    Except StringComputationElabError (CheckedStringExpr model) :=
  if hCore : core.wellFormedBool model = true then
    pure {
      core
      modelWellFormed := by
        rw [hModel]
        rfl
      wellFormed := hCore
    }
  else
    throw .incoherentCore

/-- Validate the flat model once, preserve the authored expression tree exactly, and certify every resolved runtime leaf before returning it to computation evaluation. -/
def elaborateStringExpr (model : FlatModel) (declaringGroup : GroupPath)
    (expression : StringExpr SurfaceFieldPath) :
    Except StringComputationElabError (CheckedStringExpr model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let core ← elaborateStringExprCore model declaringGroup expression
      certifyStringExpr model hModel core

/-- Resolve one ordinary nonrepeatable String target and expression together. The declaration supplies the complete basic target policy, and direct self-reference is rejected before a runtime operation exists. -/
def elaborateStringComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : StringExpr SurfaceFieldPath) :
    Except StringComputationElabError (CheckedStringComputationOperation model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let declaration ←
        (model.resolveNonrepeatableDeclarationById targetField).mapError .resolve
      match declaration.policy.kind with
      | .string => pure ()
      | actual => throw (.targetKindMismatch declaration.path actual.surfaceKind)
      if declaration.stringValueMode == .raw then
        throw (.rawStringTarget declaration.path)
      if declaration.customType.isSome then
        throw (.customStringTarget declaration.path)
      if declaration.stringPatternSource.isSome then
        throw (.patternStringTarget declaration.path)
      let core ← elaborateStringExprCore model declaringGroup expression
      let checked ← certifyStringExpr model hModel core
      if hReference : checked.core.referencesField targetField = true then
        throw (.targetSelfReference targetField)
      else
        if hTarget : model.admitsStringComputationTarget
            targetField declaration.stringPolicy = true then
          pure {
            expression := checked
            targetField
            targetPolicy := declaration.stringPolicy
            targetAdmitted := hTarget
            targetNotReferenced := by
              cases hValue : checked.core.referencesField targetField with
              | false => rfl
              | true => exact False.elim (hReference hValue)
          }
        else
          throw .incoherentCore

namespace CheckedStringExpr

/-- Read raw cells through the prepared context for the model that certified the expression, then run only the established String evaluator. -/
def evaluate (expression : CheckedStringExpr model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) :
    Except StringComputationFault StringStore :=
  expression.core.evaluate { read := (prepared.checkContext locale raw).read }

end CheckedStringExpr

namespace CheckedStringComputationOperation

/-- Read through the prepared model context, then apply the retained declaration policy to the exact root write attempt. -/
def evaluateOutcome (operation : CheckedStringComputationOperation model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) :
    Except StringComputationFault StringTargetOutcome := do
  pure (operation.targetPolicy.checkTarget
    (← operation.expression.evaluate prepared locale raw))

end CheckedStringComputationOperation

end A12Kernel
