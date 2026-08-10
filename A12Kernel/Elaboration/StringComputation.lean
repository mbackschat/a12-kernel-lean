import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.StringComputation

/-! # Checked String-computation expression lowering

This capsule resolves parser-independent field paths in copy/Number-`FieldValueAsString`/literal/`RangeAsString`/concatenation expressions into the existing `StringExpr FieldId` runtime tree. It accepts only nonrepeatable declarations of the exact kind required by each leaf. `RangeAsString` preserves the kernel's static gate order: resolve the nonrepeatable field shape, check 1-based inclusive bounds, then certify the String value kind. The integrated ordinary-target entry point additionally retains the declaration-owned line-break/pattern/minimum/maximum policy and rejects direct target self-reference before evaluation. Root direct-copy and `RangeAsString` target references retain separate refusal provenance for their measured exact Kernel projection; wider target reads remain locally rejected and externally unmapped. Alternatives, concrete syntax, repeatable reads, indexed coercion, raw/custom targets, and scheduling remain outside.
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
  | targetSelfReference (field : FieldId)
  | targetSelfReferenceAtRoot (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

namespace StringComputationElabError

/-- Project only the measured root direct-copy and `RangeAsString` target
reference refusals to their exact Kernel diagnostic class. -/
def targetDiagnostic? :
    StringComputationElabError → Option KernelStaticDiagnostic
  | .targetSelfReferenceAtRoot _ => some .errorReferenceToCalculatedField
  | _ => none

end StringComputationElabError

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

/-- Admit one already-resolved nonrepeatable Number declaration as a `FieldValueAsString` operand. -/
def admitNumberAsStringField
    (declaration : FlatFieldDecl) : Except StringComputationElabError FieldId :=
  match declaration.policy.kind with
  | .number _ => pure declaration.id
  | actual => throw (.fieldKindMismatch declaration.path actual.surfaceKind)

/-- Resolve one legal nonrepeatable Number field for `FieldValueAsString`. -/
def elaborateNumberAsStringField (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except StringComputationElabError FieldId := do
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
  admitNumberAsStringField declaration

/-- Whether one runtime leaf is the exact nonrepeatable String-value declaration in the model. -/
private def FlatModel.admitsStringComputationOperand (model : FlatModel)
    (fieldId : FieldId) : Bool :=
  match model.lookupUniqueId fieldId with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toStringValueField? == some { id := fieldId }
  | .error _ => false

/-- Whether one runtime coercion leaf is the exact nonrepeatable Number declaration in the model. -/
private def FlatModel.admitsNumberAsStringOperand (model : FlatModel)
    (fieldId : FieldId) : Bool :=
  match model.lookupUniqueId fieldId with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        match declaration.policy.kind with
        | .number _ => true
        | _ => false
  | .error _ => false

namespace StringExpr

/-- Check that every runtime leaf names the exact nonrepeatable String declaration in one model. -/
def wellFormedBool (model : FlatModel) : StringExpr FieldId → Bool
  | StringExpr.field fieldId =>
      model.admitsStringComputationOperand fieldId
  | StringExpr.fieldValueAsString fieldId =>
      model.admitsNumberAsStringOperand fieldId
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
  | .fieldValueAsString candidate => candidate == field
  | .literal _ => false
  | .range candidate _ _ => candidate == field
  | .concat left right => left.referencesField field || right.referencesField field

/-- Whether the complete expression is one of the measured root target-read
shapes rather than a wider expression that merely contains the target. -/
private def isRootTargetReference (field : FieldId) : StringExpr FieldId → Bool
  | .field candidate => candidate == field
  | .range candidate _ _ => candidate == field
  | _ => false

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
  | StringExpr.fieldValueAsString reference => do
      pure (.fieldValueAsString
        (← elaborateNumberAsStringField model declaringGroup reference))
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
      let core ← elaborateStringExprCore model declaringGroup expression
      let checked ← certifyStringExpr model hModel core
      if hReference : checked.core.referencesField targetField = true then
        if checked.core.isRootTargetReference targetField then
          throw (.targetSelfReferenceAtRoot targetField)
        else
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

/-- Read through the immutable checked document that owns Number storage-regime selection, then run only the established String evaluator. -/
def evaluate (expression : CheckedStringExpr model)
    (input : CheckedDocument model) :
    Except StringComputationFault StringStore :=
  expression.core.evaluate input.stringComputationContext

end CheckedStringExpr

namespace PreparedFlatStringPatterns

/-- Recover the exact optional matcher already prepared for a model-owned target declaration. A missing or substituted required entry fails closed. -/
def targetMatcher?
    (prepared : PreparedFlatStringPatterns model compilePattern)
    (field : FieldId) : Option (Option (String → Bool)) :=
  match model.lookupUniqueId field with
  | .error _ => none
  | .ok declaration =>
      match declaration.effectiveStringPatternSource with
      | none => some none
      | some _ =>
          match prepared.lookup? field with
          | none => none
          | some preparedField =>
              if preparedField.declaration == declaration then
                some (preparedField.pattern.map (·.wholeValueMatches))
              else
                none

end PreparedFlatStringPatterns

namespace CheckedStringComputationOperation

/-- Read through the immutable checked document, then apply the retained declaration policy and exact prepared target matcher to the root write attempt. -/
def evaluateOutcome (operation : CheckedStringComputationOperation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except StringComputationFault StringTargetOutcome := do
  let matcher ← match patterns.targetMatcher? operation.targetField with
    | some matcher => pure matcher
    | none => throw (.targetPatternUnavailable operation.targetField)
  pure (operation.targetPolicy.checkTargetWithPattern matcher
    (← operation.expression.evaluate input))

end CheckedStringComputationOperation

end A12Kernel
