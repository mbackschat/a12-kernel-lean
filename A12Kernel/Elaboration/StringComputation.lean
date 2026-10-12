import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Semantics.StringComputation

/-! # Checked String-computation expression lowering

This capsule resolves parser-independent field paths in copy/Number-`FieldValueAsString`/literal/`RangeAsString`/concatenation expressions into the existing `StringExpr FieldId` runtime tree. The expression binder accepts declarations at the target scope, while the fixed-operation certificate retains its nonrepeatable boundary. Ordinary String reads, ranges, and Number coercion keep their distinct kind gates. `RangeAsString` preserves the kernel's static gate order: resolve the entity source at the consumer scope, check 1-based inclusive bounds, then certify the String value kind. The integrated ordinary-target entry point additionally retains the declaration-owned line-break/pattern/minimum/maximum policy and rejects direct target self-reference before evaluation. A read of the target, at the root or inside a concatenation, projects the one measured Kernel class, and a raw target is refused with its read's class. Alternatives, concrete syntax and scheduling are assembled by their existing owners. Indexed coercion remains outside this binder; raw targets are rejected and Custom targets use reduced validation.
-/

namespace A12Kernel

/-- The ordinary evaluated-String carrier used by the first-filled declaration-matching boundary. -/
def FlatFieldDecl.isOrdinaryStringComputationCarrier
    (declaration : FlatFieldDecl) : Bool :=
  declaration.policy.kind == .string &&
    declaration.stringValueMode == .evaluated &&
    declaration.customType.isNone && declaration.enumeration.isNone


/-- Expression targets accept evaluated Custom Strings, whose reduced checks differ from ordinary
String policy; first-filled carriers retain their separate declaration-matching contract. -/
def FlatFieldDecl.isStringExpressionTarget (declaration : FlatFieldDecl) : Bool :=
  declaration.policy.kind == .string && declaration.stringValueMode == .evaluated &&
    declaration.enumeration.isNone

def FlatFieldDecl.stringTargetRegime (declaration : FlatFieldDecl) : StringTargetRegime :=
  match declaration.customType with
  | some customType => .custom customType
  | none => .ordinary

def FlatFieldDecl.checkStringExpressionTarget (declaration : FlatFieldDecl)
    (matcher : Option (String → Bool)) (store : StringStore)
    (context : StringComputationContext) : Except StringComputationFault StringTargetOutcome :=
  declaration.stringTargetRegime.check declaration.stringPolicy matcher store context

/-- Fail-closed errors owned by checked String-computation expression lowering. Keeping this domain local avoids widening validation or public reference diagnostics. -/
inductive StringComputationElabError where
  | indexed (error : SemanticIndexElabError)
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | invalidRange (start finish : Nat)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | copyComparison (targetPath sourcePath : List String) (refusal : CopyComparisonRefusal)
  | rawStringTarget (path : List String)
  | targetSelfReference (field : FieldId)
  /-- The group a target-less expression is judged in repeats, so its hypothetical target is a row
  target, which this carrier never evaluates. Claims no class. -/
  | repeatableTargetGroup (group : GroupPath)
  | incoherentCore
  deriving Repr, DecidableEq

namespace StringComputationElabError

/-- Project the measured target refusals to their exact Kernel diagnostic class: a read of the
target, which draws one class on every shape measured, a root copy or range
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-computed-target-reference)) and
a concatenation around the read
([checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-computation-self-read-sweep)),
a raw target, which the generated comparison reads before the operation, and a copied field that
comparison refuses. The raw row is measured with
a String field source ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26c-target-read)); a literal
source takes it by that read, which does not depend on the operation. -/
def targetDiagnostic? :
    StringComputationElabError → Option KernelStaticDiagnostic
  | .targetSelfReference _ => some .errorReferenceToCalculatedField
  | .rawStringTarget _ => some .rawTypeOperandInvalid
  | .copyComparison _ _ refusal => some refusal.diagnostic
  | _ => none

end StringComputationElabError

/-- Admit one already-resolved declaration as a String-value computation leaf. -/
def admitStringComputationValueField
    (declaration : FlatFieldDecl) : Except StringComputationElabError FieldId :=
  match declaration.toStringValueField? with
  | some field => pure field.id
  | none =>
      if declaration.isRawString then
        throw (.rawStringValue declaration.path)
      else
        throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)

/-- Immediate concatenation fields require no effective display remapping; a grouped operand keeps
its stored-token read without that restriction (spec/06 Part A §7). Range keeps its stricter gate. -/
def admitStringExpressionField (declaration : FlatFieldDecl) (allowStoredEnumeration : Bool := false) :
    Except StringComputationElabError FieldId := do
  if let some (_, .enumeration display) := declaration.toEnumerationTextFieldComparison? .stored then
    if allowStoredEnumeration || !display.hasEffectiveDisplay then return declaration.id
  admitStringComputationValueField declaration

/-- Resolve the declared category once so evaluation and consumers retain its positional mapping. -/
def stringCategory? (declaration : FlatFieldDecl) (name : String) :
    Option ResolvedEnumerationCategory := do
  let (.enumeration operand, _) ← declaration.toEnumerationTextFieldComparison? (.category name)
    | none
  let .category mapping := operand.projection | none
  pure mapping

/-- Resolve one legal String-value field at its target scope. The
copied field is a field-value read, so its gates refuse a raw String ahead of this carrier's own
refusal. -/
def elaborateStringValueField (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (reference : SurfaceFieldPath) (allowStoredEnumeration : Bool := false) : Except StringComputationElabError FieldId := do
  let declaration ←
    (model.resolveComputationFieldValueRead declaringGroup targetGroup reference).mapError .resolve
  admitStringExpressionField declaration allowStoredEnumeration

/-- Admit one already-resolved Number declaration as a `FieldValueAsString` operand. -/
def admitNumberAsStringField
    (declaration : FlatFieldDecl) : Except StringComputationElabError FieldId :=
  match declaration.policy.kind with
  | .number _ => pure declaration.id
  | actual => throw (.fieldKindMismatch declaration.path actual.surfaceKind)

/-- Resolve one legal Number field at its target scope for `FieldValueAsString`, a parameter asking the group
    gate alone: its raw String draws the conversion's Number class rather than the raw one
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
def elaborateNumberAsStringField (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except StringComputationElabError FieldId := do
  let declaration ←
    (model.resolveComputationEntityRead declaringGroup targetGroup reference).mapError .resolve
  admitNumberAsStringField declaration

/-- Require the same textual kind and display gates after nonrepeatable resolution. -/
private def FlatModel.admitsStringComputationOperand (model : FlatModel)
    (fieldId : FieldId) (allowStoredEnumeration : Bool := false) : Bool :=
  match model.lookupUniqueId fieldId with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        (admitStringExpressionField declaration allowStoredEnumeration).toOption == some fieldId
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

/-- Certify every resolved leaf against the same model and nonrepeatable scope. -/
def wellFormedBool (model : FlatModel) (expression : StringExpr FieldId)
    (allowStoredEnumeration : Bool := false) : Bool :=
  match expression with
  | StringExpr.field fieldId =>
      model.admitsStringComputationOperand fieldId allowStoredEnumeration
  | .category fieldId projection =>
      (model.lookupUniqueId fieldId).toOption.any fun declaration =>
        declaration.repeatableScope.isEmpty &&
          declaration.enumeration.any fun source => source.categories.any fun category =>
            stringCategory? declaration category.name == some projection
  | StringExpr.fieldValueAsString fieldId =>
      model.admitsNumberAsStringOperand fieldId
  | StringExpr.literal _ => true
  | StringExpr.range fieldId start finish =>
      validStringRange start finish &&
        (model.lookupUniqueId fieldId).toOption.any (fun field =>
          field.repeatableScope.isEmpty && field.toStringValueField?.isSome)
  | StringExpr.concat left right =>
      left.wellFormedBool model && right.wellFormedBool model
  | .group body => body.wellFormedBool model true

def WellFormed (expression : StringExpr FieldId) (model : FlatModel) : Prop :=
  expression.wellFormedBool model = true

/-- Whether the resolved expression contains the named field anywhere in its authored tree. -/
def referencesField (field : FieldId) : StringExpr FieldId → Bool
  | .field candidate | .category candidate _ => candidate == field
  | .fieldValueAsString candidate => candidate == field
  | .literal _ => false
  | .range candidate _ _ => candidate == field
  | .concat left right => left.referencesField field || right.referencesField field
  | .group body => body.referencesField field

end StringExpr

/-- A lowered String expression certified against the same model used to resolve all of its leaves. -/
structure CheckedStringExpr (model : FlatModel) where
  core : StringExpr FieldId
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- The exact nonrepeatable ordinary-or-Custom String target/policy relation retained by checked lowering. -/
def FlatModel.admitsStringComputationTarget (model : FlatModel)
    (field : FieldId) (policy : StringFieldPolicy) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.policy.kind == .string &&
        declaration.stringValueMode == .evaluated &&
        declaration.enumeration.isNone &&
        declaration.stringPolicy == policy
  | .error _ => false

/-- One ordinary-or-Custom String target and expression certified against the same validated model. The
declaration group remains definition identity even when fixed target placement owns execution scope.
Target policy cannot be substituted after elaboration. -/
structure CheckedStringComputationOperation (model : FlatModel) where
  declaringGroup : GroupPath
  expression : CheckedStringExpr model
  targetField : FieldId
  targetPolicy : StringFieldPolicy
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetAdmitted : model.admitsStringComputationTarget targetField targetPolicy = true
  targetNotReferenced : expression.core.referencesField targetField = false

/-- Resolve one authored String-expression tree without evaluating or reordering it. The caller supplies a validated model; each field still passes through the shared target-scope path resolver. -/
def elaborateStringExprCore (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (expression : StringExpr SurfaceFieldPath String) (allowStoredEnumeration : Bool := false) :
    Except StringComputationElabError (StringExpr FieldId) :=
  match expression with
  | StringExpr.field reference => do
      pure (.field (← elaborateStringValueField model declaringGroup targetGroup reference allowStoredEnumeration))
  | .category reference name => do
      let declaration ←
        (model.resolveComputationFieldValueRead declaringGroup targetGroup reference).mapError .resolve
      match stringCategory? declaration name with
      | some projection => pure (.category declaration.id projection)
      | none => throw .incoherentCore
  | StringExpr.fieldValueAsString reference => do
      pure (.fieldValueAsString
        (← elaborateNumberAsStringField model declaringGroup targetGroup reference))
  | StringExpr.literal value => pure (.literal value)
  | StringExpr.range reference start finish => do
      let declaration ←
        (model.resolveComputationOperandUnchecked declaringGroup targetGroup
          reference).mapError .resolve
      if !validStringRange start finish then
        throw (.invalidRange start finish)
      pure (.range (← admitStringComputationValueField declaration) start finish)
  | .group body => .group <$> elaborateStringExprCore model declaringGroup targetGroup body true
  | StringExpr.concat left right => do
      pure (.concat
        (← elaborateStringExprCore model declaringGroup targetGroup left)
        (← elaborateStringExprCore model declaringGroup targetGroup right))

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

/-- Validate the flat model once, preserve the authored expression tree exactly, and certify every resolved runtime leaf before returning it to computation evaluation. Without a target the expression is judged as if its target lay in the declaring group, where an undeclared declaring group defaults. A repeating target group is refused first: the computation binding would bind its levels, which this carrier's fixed-target evaluator cannot read. -/
def elaborateStringExpr (model : FlatModel) (declaringGroup : GroupPath)
    (expression : StringExpr SurfaceFieldPath String) (targetGroup : GroupPath := declaringGroup) :
    Except StringComputationElabError (CheckedStringExpr model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      if !(model.repeatableScopeForGroupPath targetGroup).isEmpty then
        throw (.repeatableTargetGroup targetGroup)
      let core ← elaborateStringExprCore model declaringGroup targetGroup expression
      certifyStringExpr model hModel core

/-- The comparison the computation generates between its target and a **directly copied** field,
asked after the target's read and then the copied field's read, as the Kernel asks them
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)).
A wider expression is not typed here: the rows measure a whole-expression copy. A pair the comparison
admits falls through to this carrier's expression gates, including the stored-token leaf for an
unlabelled Enumeration copied into a String. -/
private def FlatModel.checkStringCopyComparison (model : FlatModel) (declaringGroup : GroupPath)
    (target : FlatFieldDecl) : StringExpr SurfaceFieldPath String → Except StringComputationElabError Unit
  | .field reference => do
      if target.fieldValueReadRefusal?.isNone then
        let source ←
          (model.resolveComputationFieldValueRead declaringGroup target.groupPath reference).mapError
            .resolve
        if let some refusal := target.copyComparisonRefusal? source then
          throw (.copyComparison target.path source.path refusal)
  | .group body => model.checkStringCopyComparison declaringGroup target body
  | _ => pure ()

/-- Check computation-group syntax independently of operands, including operand-free literals. -/
private def certifyStringComputationDeclaringGroup (declaringGroup : GroupPath) :
    Except StringComputationElabError { group : GroupPath // GroupPath.isValid group = true } :=
  if hValid : GroupPath.isValid declaringGroup = true then
    .ok ⟨declaringGroup, hValid⟩
  else
    .error (.resolve (.invalidRuleGroup declaringGroup))

/-- Resolve one ordinary-or-Custom nonrepeatable String target and expression together. The declaration supplies the complete basic target policy, and direct self-reference is rejected before a runtime operation exists. -/
def elaborateStringComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : StringExpr SurfaceFieldPath String) :
    Except StringComputationElabError (CheckedStringComputationOperation model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let checkedDeclaringGroup ←
        certifyStringComputationDeclaringGroup declaringGroup
      let declaration ←
        (model.resolveNonrepeatableDeclarationById targetField).mapError .resolve
      match declaration.policy.kind with
      | .string => pure ()
      | actual =>
          model.checkStringCopyComparison checkedDeclaringGroup.val declaration expression
          throw (.targetKindMismatch declaration.path actual.surfaceKind)
      if declaration.stringValueMode == .raw then
        throw (.rawStringTarget declaration.path)
      model.checkStringCopyComparison checkedDeclaringGroup.val declaration expression
      let core ←
        elaborateStringExprCore model checkedDeclaringGroup.val declaration.groupPath expression
      let checked ← certifyStringExpr model hModel core
      if hReference : checked.core.referencesField targetField = true then
        throw (.targetSelfReference targetField)
      else
        if hTarget : model.admitsStringComputationTarget
            targetField declaration.stringPolicy = true then
          pure {
            declaringGroup := checkedDeclaringGroup.val
            expression := checked
            targetField
            targetPolicy := declaration.stringPolicy
            declaringGroupValid := checkedDeclaringGroup.property
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
  let declaration ← match model.lookupUniqueId operation.targetField with
    | .ok declaration => pure declaration
    | .error _ => throw (.fieldKindMismatch operation.targetField)
  declaration.checkStringExpressionTarget matcher (← operation.expression.evaluate input)
    input.stringComputationContext

end CheckedStringComputationOperation

end A12Kernel
