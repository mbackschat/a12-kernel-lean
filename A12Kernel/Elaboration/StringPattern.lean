import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.StringPattern

/-! # A12Kernel.Elaboration.StringPattern — checked two-stage pattern admission

The kernel first requires Java-pattern compilation and then applies a finite source gate. Compilation remains an injected capability that returns the whole-value matcher compiled from the exact source, so checked evaluation cannot accidentally substitute a matcher for another pattern. The source scan below is an original character walk over the canonically documented exclusion families, including the separately observed uppercase-`\P` exclusion. Passing this gate is not a JavaScript-portability claim.
-/

namespace A12Kernel

/-- A pure host capability that either rejects Java syntax or returns the whole-value matcher compiled from that exact source. Construction-time caching remains the caller's responsibility. -/
abbrev StringPatternCompiler := String → Option (String → Bool)

inductive PatternAdmissionError where
  | javaSyntax
  | kernelRestriction
  deriving Repr, DecidableEq

inductive PatternAdmission where
  | admitted
  | rejected (error : PatternAdmissionError)
  deriving Repr, DecidableEq

private def isForbiddenEscapeLetter (character : Char) : Bool :=
  character == 'A' || character == 'G' || character == 'Z' ||
    character == 'z' || character == 'a' || character == 'e' ||
    character == 'p' || character == 'P' || character == 'Q' ||
    character == 'E'

/-- Detect the finite adjacent source forms rejected after Java compilation. This is deliberately a character scanner, not a transcription of the kernel's regular expression. -/
private def containsForbiddenPatternSequence : List Char → Bool
  | first :: second :: remaining =>
      let possessive :=
        (first == '?' || first == '+' || first == '}' || first == '*') &&
          second == '+'
      let forbiddenEscape := first == '\\' && isForbiddenEscapeLetter second
      let forbiddenGroupPrefix :=
        match remaining with
        | third :: _ => first == '(' && second == '?' && (third == '<' || third == '>')
        | [] => false
      possessive || forbiddenEscape || forbiddenGroupPrefix ||
        containsForbiddenPatternSequence (second :: remaining)
  | _ => false

/-- Reject a second unescaped class opener before the first class closes. Escaping is intentionally source-local: an immediately preceding backslash protects the following bracket. -/
private def containsNestedClassOpen (source : List Char) : Bool :=
  let rec scan (insideClass previousWasBackslash : Bool) : List Char → Bool
    | [] => false
    | character :: remaining =>
        let isUnescaped := !previousWasBackslash
        if character == '[' && isUnescaped then
          if insideClass then true else scan true false remaining
        else if character == ']' && isUnescaped then
          scan false false remaining
        else
          scan insideClass (character == '\\') remaining
  scan false false source

/-- The documented post-compilation source gate. It is a bounded exclusion predicate, not an invented complete regex grammar. -/
def kernelPatternSourceAllowed (source : String) : Bool :=
  !containsForbiddenPatternSequence source.toList &&
    !containsNestedClassOpen source.toList

/-- Classify the two admission stages while preserving compiler-rejection precedence. -/
def classifyStringPattern (compilePattern : StringPatternCompiler)
    (source : String) : PatternAdmission :=
  match compilePattern source with
  | none => .rejected .javaSyntax
  | some _ =>
      if kernelPatternSourceAllowed source then .admitted
      else .rejected .kernelRestriction

/-- A pattern source paired with the exact matcher returned by the injected compiler and the post-compilation kernel admission fact. -/
structure AdmittedStringPattern (compilePattern : StringPatternCompiler) where
  source : String
  wholeValueMatches : String → Bool
  compiledSource :
    compilePattern source = some wholeValueMatches
  kernelSourceAllowed : kernelPatternSourceAllowed source = true

/-- Construct the proof-bearing pattern capability or retain the exact failed stage. -/
def admitStringPattern (compilePattern : StringPatternCompiler)
    (source : String) :
    Except PatternAdmissionError (AdmittedStringPattern compilePattern) :=
  match hCompiled : compilePattern source with
  | none => .error .javaSyntax
  | some wholeValueMatches =>
    if hAllowed : kernelPatternSourceAllowed source = true then
      .ok {
        source
        wholeValueMatches
        compiledSource := hCompiled
        kernelSourceAllowed := hAllowed
      }
    else
      .error .kernelRestriction

/-- Evaluate only after both admission stages have succeeded. Runtime truth remains owned by the existing resolved consumer. -/
def AdmittedStringPattern.evalResolved
    (admitted : AdmittedStringPattern compilePattern)
    (op : StringPatternOp)
    (operand : SimpleComparisonOperand String) : Verdict :=
  op.evalResolved admitted.wholeValueMatches operand

/-- Convenience boundary for consumers that check and immediately evaluate one source. -/
def evalAdmittedStringPattern (compilePattern : StringPatternCompiler) (source : String)
    (op : StringPatternOp)
    (operand : SimpleComparisonOperand String) : Except PatternAdmissionError Verdict :=
  match admitStringPattern compilePattern source with
  | .error error => .error error
  | .ok admitted => .ok (admitted.evalResolved op operand)

/-- The parser-level pattern shape: a direct field path, one of the two dedicated operators, and a constant source. Arbitrary expressions cannot inhabit this type. -/
structure SurfaceStringPatternCondition where
  op : StringPatternOp
  field : SurfaceFieldPath
  source : String
  deriving Repr, DecidableEq

/-- Exact checked-construction failures for the ordinary nonrepeatable String fragment. Prepared custom/predefined fields and arbitrary declaration patterns need their own checked context instead of bypassing formal validation. -/
inductive StringPatternConditionElabError where
  | model (error : ResolveError)
  | fieldReference (error : ResolveError)
  | fieldKind (path : List String) (kind : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | preparedCustomFieldRequired (path : List String)
  | declaredPatternRequiresPreparation (path : List String)
  | pattern (error : PatternAdmissionError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Recheck that a field belongs to the validated model and is executable through the ordinary declaration-owned String context used by this capsule. -/
def FlatModel.admitsOrdinaryStringPatternField (model : FlatModel)
    (field : FlatStringField) : Bool :=
  match model.lookupUniqueId field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.customType.isNone &&
        declaration.toStringValueField? == some field

/-- One authored condition whose direct field and exact compiled pattern are certified against the same model. It is a checked leaf, not a second connective tree. -/
structure CheckedStringPatternCondition (model : FlatModel)
    (compilePattern : StringPatternCompiler) where
  rowGroup : GroupPath
  op : StringPatternOp
  field : FlatStringField
  pattern : AdmittedStringPattern compilePattern
  modelWellFormed : model.validate.isOk = true
  fieldWellFormed :
    model.admitsOrdinaryStringPatternField field = true

/-- Resolve and certify the smallest ordinary checked pattern condition. Admission order follows the checked model, direct nonrepeatable field, field capability, and pattern-source stages. -/
def elaborateStringPatternCondition (compilePattern : StringPatternCompiler)
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceStringPatternCondition) :
    Except StringPatternConditionElabError
      (CheckedStringPatternCondition model compilePattern) :=
  match hModel : model.validate with
  | .error error => .error (.model error)
  | .ok () => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked rowGroup surface.field)
          |>.mapError .fieldReference
      if declaration.customType.isSome then
        throw (.preparedCustomFieldRequired declaration.path)
      if declaration.isRawString then
        throw (.rawStringValue declaration.path)
      let field ←
        match declaration.toStringValueField? with
        | some field => pure field
        | none =>
            match declaration.policy.kind with
            | .string =>
                throw (.declaredPatternRequiresPreparation declaration.path)
            | kind => throw (.fieldKind declaration.path kind.surfaceKind)
      let pattern ←
        (admitStringPattern compilePattern surface.source).mapError .pattern
      if hField : model.admitsOrdinaryStringPatternField field = true then
        pure {
          rowGroup
          op := surface.op
          field
          pattern
          modelWellFormed := by
            rw [hModel]
            rfl
          fieldWellFormed := hField
        }
      else
        throw .incoherentCore

namespace CheckedStringPatternCondition

/-- Evaluate an already-selected checked row through the exact compiler-associated matcher. -/
def evalSelected (checked : CheckedStringPatternCondition model compilePattern)
    (context : FlatContext) : Verdict :=
  checked.pattern.evalResolved checked.op
    (context.resolveDirectStringComparisonOperand checked.field)

/-- Apply the ordinary full-validation row gate, then use the declaration-owned checked String context. Pattern leaves cannot fire on an all-empty row. -/
def evalFull (checked : CheckedStringPatternCondition model compilePattern)
    (raw : RawFlatContext) (hasContent : Bool) : Verdict :=
  if hasContent then
    checked.evalSelected (model.checkContext raw)
  else
    .notFired

/-- The direct field is the condition's only model reference. -/
def referencesField (checked : CheckedStringPatternCondition model compilePattern)
    (field : FieldId) : Bool :=
  checked.field.id == field

end CheckedStringPatternCondition

end A12Kernel
