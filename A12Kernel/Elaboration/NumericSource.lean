import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.DateDifference
import A12Kernel.Semantics.String

/-! # Shared checked numeric-expression sources

Validation and computation both consume Number-field references, numeric `BaseYear`, direct numeric date-component extraction from a Base-Year date source, direct Date/Time/DateTime field-component sources, checked ordinary String/Enumeration/category conversion, Date-only month/year differences, and direct resolved Number field-list aggregates through the same authored expression tree. Consumer-specific field resolution, model coherence, and runtime reads remain with each checked owner.
-/

namespace A12Kernel

/-- Kernel 30.8.1's authored Number digit budget for String/Enumeration conversion. Dot and leading minus do not consume the budget. -/
def maxFieldValueAsNumberDigits : Nat := 15

/-- One exactly parsed Java-host decimal token together with the static facts used by `FieldValueAsNumber` admission. Leading zeros and negative zero are retained only through digit count/scale; numeric evaluation observes their exact rational amount. -/
structure ParsedJavaDecimalToken where
  value : Rat
  scale : Nat
  digitCount : Nat
  deriving Repr, DecidableEq

/-- Starts of the ten-code-point BMP decimal blocks accepted by Java 21's `Character.isDigit(char)`. Commons Lang 3.20.0 iterates UTF-16 `char`, so supplementary-plane decimal code points are deliberately absent. -/
private def java21BmpDecimalDigitStarts : List Nat :=
  [0x0030, 0x0660, 0x06F0, 0x07C0, 0x0966, 0x09E6, 0x0A66, 0x0AE6,
   0x0B66, 0x0BE6, 0x0C66, 0x0CE6, 0x0D66, 0x0DE6, 0x0E50, 0x0ED0,
   0x0F20, 0x1040, 0x1090, 0x17E0, 0x1810, 0x1946, 0x19D0, 0x1A80,
   0x1A90, 0x1B50, 0x1BB0, 0x1C40, 0x1C50, 0xA620, 0xA8D0, 0xA900,
   0xA9D0, 0xA9F0, 0xAA50, 0xABF0, 0xFF10]

private def java21DecimalDigitValueFrom? (code : Nat) : List Nat → Option Nat
  | [] => none
  | start :: rest =>
      if start ≤ code ∧ code < start + 10 then
        some (code - start)
      else
        java21DecimalDigitValueFrom? code rest

/-- Decimal value under the exact Java 21 UTF-16 `Character.isDigit(char)` profile used by the pinned kernel's Commons Lang parser. -/
def java21DecimalDigitValue? (character : Char) : Option Nat :=
  java21DecimalDigitValueFrom? character.toNat java21BmpDecimalDigitStarts

private def parseJavaDecimalDigitsAux (accumulator : Nat) :
    List Char → Option Nat
  | [] => some accumulator
  | character :: rest => do
      let digit ← java21DecimalDigitValue? character
      parseJavaDecimalDigitsAux (accumulator * 10 + digit) rest

private def parseJavaDecimalDigitsAllowEmpty
    (characters : List Char) : Option Nat :=
  if characters.isEmpty then some 0
  else parseJavaDecimalDigitsAux 0 characters

/-- Parse exactly the Java 21 `NumberUtils.isParsable` decimal fragment consumed by ordinary numeric Enumeration values: optional leading minus, at most one dot, at least one digit, and no trailing dot. A leading dot is legal. Digit-budget admission remains a separate model check. -/
def parseJavaDecimalToken? (input : String) : Option ParsedJavaDecimalToken := do
  let (negative, characters) := match input.toList with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  let (wholeCharacters, suffix) := characters.span (· != '.')
  let (fractionCharacters, scale) ← match suffix with
    | [] => some ([], 0)
    | '.' :: fraction =>
        if fraction.isEmpty then none else some (fraction, fraction.length)
    | _ => none
  if wholeCharacters.isEmpty && fractionCharacters.isEmpty then
    none
  else
    let whole ← parseJavaDecimalDigitsAllowEmpty wholeCharacters
    let fraction ← parseJavaDecimalDigitsAllowEmpty fractionCharacters
    let factor := 10 ^ scale
    let magnitude : Rat := whole + (fraction : Rat) / factor
    some {
      value := if negative then -magnitude else magnitude
      scale
      digitCount := wholeCharacters.length + fractionCharacters.length }

/-- Derive the conversion result scale only when every selected token belongs to the pinned Java-host decimal profile and stays within the kernel digit budget. -/
def CheckedEnumerationProjection.numericScale?
    (checked : CheckedEnumerationProjection) : Option Nat := do
  let parsed ← checked.selectedTokens.mapM parseJavaDecimalToken?
  if parsed.all (fun token => token.digitCount ≤ maxFieldValueAsNumberDigits) then
    some (parsed.foldl (fun scale token => max scale token.scale) 0)
  else
    none

/-- One ordinary String or closed Enumeration/category source statically certified for `FieldValueAsNumber`. The source reuses the shared textual operand and keeps its derived non-expandable scale alongside it. -/
structure ResolvedFieldValueAsNumberSource where
  operand : FlatTextFieldOperand
  scale : Nat
  deriving Repr, DecidableEq

namespace ResolvedFieldValueAsNumberSource

def fieldId (source : ResolvedFieldValueAsNumberSource) : FieldId :=
  source.operand.field.id

def projectionRef (source : ResolvedFieldValueAsNumberSource) :
    EnumerationProjectionRef :=
  match source.operand with
  | .string _ => .stored
  | .enumeration operand => operand.projectionRef

/-- Project the exact checked String or stored/category Enumeration token without introducing a conversion-specific text operand. -/
def tokenForValue? (source : ResolvedFieldValueAsNumberSource) :
    Value → Option String
  | .str token =>
      match source.operand with
      | .string _ =>
          if matchesAsciiDigitsPattern token then some token else none
      | .enumeration _ => none
  | .enum stored =>
      match source.operand with
      | .string _ => none
      | .enumeration operand => operand.projection.tokenFor? stored
  | _ => none

def valueFor? (source : ResolvedFieldValueAsNumberSource)
    (value : Value) : Option Rat := do
  let token ← source.tokenForValue? value
  let parsed ← parseJavaDecimalToken? token
  pure parsed.value

end ResolvedFieldValueAsNumberSource

inductive FieldValueAsNumberSourceError where
  | notConvertible
  | enumeration (error : EnumerationOperandError)
  | incoherentEnumeration
  deriving Repr, DecidableEq

namespace SurfaceTextFieldOperand

def reference : SurfaceTextFieldOperand → SurfaceFieldPath
  | .direct field | .category field _ => field

def projectionRef : SurfaceTextFieldOperand → EnumerationProjectionRef
  | .direct _ => .stored
  | .category _ name => .category name

end SurfaceTextFieldOperand

/-- Admit one exact bounded value-validating String or ordinary closed Enumeration/category source after field/path resolution. -/
def FlatFieldDecl.resolveFieldValueAsNumberSource
    (declaration : FlatFieldDecl) (projectionRef : EnumerationProjectionRef) :
    Except FieldValueAsNumberSourceError ResolvedFieldValueAsNumberSource :=
  match declaration.policy.kind, declaration.enumeration, projectionRef with
  | .string, none, .stored =>
      match declaration.toStringValueField?, declaration.stringPatternSource,
          declaration.stringPolicy.maxLength with
      | some field, some pattern, some maximum =>
          if declaration.customType.isNone &&
              pattern == asciiDigitsPatternSource &&
              maximum ≤ maxFieldValueAsNumberDigits then
            .ok { operand := .string field, scale := 0 }
          else
            .error .notConvertible
      | _, _, _ => .error .notConvertible
  | .enumeration, some source, _ =>
      match elaborateEnumeration source with
      | .error _ => .error .incoherentEnumeration
      | .ok checked =>
          match checkEnumerationProjection checked projectionRef with
          | .error error => .error (.enumeration error)
          | .ok projection =>
              match projection.numericScale? with
              | none => .error .notConvertible
              | some scale => .ok {
                  operand := .enumeration {
                    field := { id := declaration.id }
                    projectionRef := projection.projectionRef
                    projection := projection.projection }
                  scale }
  | _, _, _ => .error .notConvertible

/-- Re-derive one resolved conversion source from the same model declaration. This keeps forged nonnumeric domains and scale summaries outside checked validation/computation cores. -/
def FlatModel.admitsFieldValueAsNumberSource (model : FlatModel)
    (source : ResolvedFieldValueAsNumberSource) : Bool :=
  match model.lookupUniqueId source.fieldId with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        match declaration.resolveFieldValueAsNumberSource source.projectionRef with
        | .error _ => false
        | .ok resolved => decide (resolved = source)

/-- The seven direct scalar temporal component functions, grouped by the source half they project. -/
inductive TemporalNumericPart where
  | date (part : DateNumericPart)
  | time (part : TimeNumericPart)
  deriving Repr, DecidableEq

namespace TemporalNumericPart

/-- Static kind/component admission for one direct temporal numeric function. -/
def admittedBy (part : TemporalNumericPart) (field : FlatTemporalField)
    (hasBaseYear : Bool) : Bool :=
  match part with
  | .date datePart =>
      (field.kind == .date || field.kind == .dateTime) &&
        datePart.admittedBy hasBaseYear field.components
  | .time timePart =>
      (field.kind == .time || field.kind == .dateTime) &&
        timePart.admittedBy field.components

/-- Extract the selected amount from the matching decoded payload half. -/
def project? (part : TemporalNumericPart) (value : TemporalValue) : Option Rat :=
  match part with
  | .date datePart => value.dateParts?.map datePart.extract
  | .time timePart => value.time?.map timePart.extract

end TemporalNumericPart

/-- Validation-phase projection through the existing Date and Time operand owners. -/
def FlatContext.resolveTemporalNumericOperand (context : FlatContext)
    (field : FlatTemporalField) : TemporalNumericPart → NumericOperand
  | .date part => context.resolveDateNumericOperand field part
  | .time part => context.resolveTimeNumericOperand field part

inductive SurfaceDateDifferenceOperand where
  | field (path : SurfaceFieldPath)
  | baseYear (source : BaseYearDateSource)
  deriving Repr, DecidableEq

inductive ResolvedDateDifferenceOperand where
  | field (source : FlatTemporalField)
  | baseYear (year : Int) (source : BaseYearDateSource)
  deriving Repr, DecidableEq

namespace ResolvedDateDifferenceOperand

def isField : ResolvedDateDifferenceOperand → Bool
  | .field _ => true
  | .baseYear _ _ => false

def components : ResolvedDateDifferenceOperand → TemporalComponents
  | .field source => source.components
  | .baseYear _ _ => TemporalComponents.baseYear

def references (field : FieldId) : ResolvedDateDifferenceOperand → Bool
  | .field source => source.id == field
  | .baseYear _ _ => false

def validationOperand (context : FlatContext) :
    ResolvedDateDifferenceOperand → DateDifferenceOperand
  | .field source => DateDifferenceOperand.ofObservation
      (context.observeValidationAt source.id)
  | .baseYear year source => .value (source.parts year)

end ResolvedDateDifferenceOperand

/-- The Number-valued field-list aggregate operations whose resolved folds share one classified-cell owner. -/
inductive NumericAggregateOp where
  | sum
  | minimum
  | maximum
  | distinctCount
  deriving Repr, DecidableEq

/-- A parser-independent direct Number aggregate field list. Checked direct-list admission requires at least two entries; starred/group operands expand through separate owners. -/
structure SurfaceNumericAggregateFields where
  first : SurfaceFieldPath
  rest : List SurfaceFieldPath
  deriving Repr, DecidableEq

/-- One nonempty resolved Number aggregate source in authored encounter order. -/
structure ResolvedNumericAggregateFields where
  first : FlatNumberField
  rest : List FlatNumberField
  deriving Repr, DecidableEq

namespace ResolvedNumericAggregateFields

def fields (source : ResolvedNumericAggregateFields) : List FlatNumberField :=
  source.first :: source.rest

def hasMultipleFields (source : ResolvedNumericAggregateFields) : Bool :=
  !source.rest.isEmpty

def firstDuplicateFieldId? : List FieldId → Option FieldId :=
  FieldId.firstDuplicate?

def firstDuplicate? (source : ResolvedNumericAggregateFields) : Option FieldId :=
  firstDuplicateFieldId? (source.fields.map (·.id))

def hasUniqueFields (source : ResolvedNumericAggregateFields) : Bool :=
  source.firstDuplicate?.isNone

/-- Field-list aggregates derive the maximum contributing declaration scale and never gain literal expansion capability. -/
def scaleSummary (source : ResolvedNumericAggregateFields) :
    NumericScaleSummary :=
  source.rest.foldl
    (fun summary field => summary.union (NumericScaleSummary.field field.info.scale))
    (NumericScaleSummary.field source.first.info.scale)

end ResolvedNumericAggregateFields

namespace NumericAggregateOp

/-- Ordinary value aggregates retain the union of contributing declaration scales; a distinct count is an integral result independently of operand scale. -/
def scaleSummary (op : NumericAggregateOp)
    (source : ResolvedNumericAggregateFields) : NumericScaleSummary :=
  match op with
  | .sum | .minimum | .maximum => source.scaleSummary
  | .distinctCount => NumericScaleSummary.field 0

end NumericAggregateOp

inductive SurfaceNumericAtom where
  | field (path : SurfaceFieldPath)
  | baseYear
  | baseYearDatePart (source : BaseYearDateSource) (part : DateNumericPart)
  | temporalFieldPart (path : SurfaceFieldPath) (part : TemporalNumericPart)
  | stringLength (path : SurfaceFieldPath)
  | stringRange (path : SurfaceFieldPath) (start finish : Nat)
  | fieldValueAsNumber (source : SurfaceTextFieldOperand)
  | dateDifference (unit : DateDifferenceUnit)
      (left right : SurfaceDateDifferenceOperand)
  | aggregate (op : NumericAggregateOp) (source : SurfaceNumericAggregateFields)
  | filledGroupCount (groups : List SurfaceGroupReference)
  deriving Repr, DecidableEq

inductive ResolvedNumericAtom (Field : Type) where
  | field (source : Field)
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource)
      (part : DateNumericPart)
  | temporalFieldPart (source : FlatTemporalField) (part : TemporalNumericPart)
  | stringLength (source : FlatStringField)
  | stringRange (source : FlatStringField) (start finish : Nat)
  | fieldValueAsNumber (source : ResolvedFieldValueAsNumberSource)
  | dateDifference (unit : DateDifferenceUnit)
      (left right : ResolvedDateDifferenceOperand)
  | aggregate (op : NumericAggregateOp) (source : ResolvedNumericAggregateFields)
  | filledGroupCount (groups : List ResolvedGroupReference)
  deriving Repr, DecidableEq

namespace ResolvedNumericAtom

def isDataDependent : ResolvedNumericAtom Field → Bool
  | .field _ => true
  | .baseYear _ => false
  | .baseYearDatePart _ _ _ => false
  | .temporalFieldPart _ _ => true
  | .stringLength _ => true
  | .stringRange _ _ _ => true
  | .fieldValueAsNumber _ => true
  | .dateDifference _ left right => left.isField || right.isField
  | .aggregate _ _ => true
  | .filledGroupCount _ => true

def summary (fieldSummary : Field → NumericScaleSummary) :
    ResolvedNumericAtom Field → NumericScaleSummary
  | .field source => fieldSummary source
  | .baseYear _ => NumericScaleSummary.field 0
  | .baseYearDatePart _ _ _ => NumericScaleSummary.field 0
  | .temporalFieldPart _ _ => NumericScaleSummary.field 0
  | .stringLength _ => NumericScaleSummary.field 0
  | .stringRange _ _ _ => NumericScaleSummary.field 0
  | .fieldValueAsNumber source => NumericScaleSummary.field source.scale
  | .dateDifference _ _ _ => NumericScaleSummary.field 0
  | .aggregate op source => op.scaleSummary source
  | .filledGroupCount _ => NumericScaleSummary.field 0

end ResolvedNumericAtom

/-- The wrapper checker rejects only an immediate numeric literal or its grouped form. Semantically fixed sources such as numeric `BaseYear` remain distinct syntax and are admitted. -/
def AuthoredNumericExpr.isImmediateResolvedNumericLiteral :
    AuthoredNumericExpr (ResolvedNumericAtom Field) → Bool
  | .literal _ => true
  | .group body => body.isImmediateResolvedNumericLiteral
  | _ => false

/-- Check the source-specific immediate-literal prohibition at every rounding/absolute-value boundary while traversing the complete numeric operation tree, including operand-list calls and their normalized folds. -/
def AuthoredNumericExpr.respectsResolvedWrapperLiteralBoundary :
    AuthoredNumericExpr (ResolvedNumericAtom Field) → Bool
  | .round _ _ body | .abs body =>
      !body.isImmediateResolvedNumericLiteral &&
        body.respectsResolvedWrapperLiteralBoundary
  | .atom _ | .literal _ => true
  | .group body => body.respectsResolvedWrapperLiteralBoundary
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.respectsResolvedWrapperLiteralBoundary &&
        right.respectsResolvedWrapperLiteralBoundary
  | .extremumCall _ body => body.respectsResolvedWrapperLiteralBoundary

/-- A resolved numeric operation must satisfy the shared authored shape and the source-specific wrapper boundary at every depth. -/
def AuthoredNumericExpr.isAdmittedResolvedNumericOperation
    (expression : AuthoredNumericExpr (ResolvedNumericAtom Field)) : Bool :=
  expression.isAdmittedNumericOperation &&
    expression.respectsResolvedWrapperLiteralBoundary

end A12Kernel
