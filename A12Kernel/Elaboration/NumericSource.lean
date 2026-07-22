import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.DateDifference
import A12Kernel.Semantics.String

/-! # Shared checked numeric-expression sources

Validation and computation both consume Number-field references, numeric `BaseYear`, direct numeric date-component extraction from a Base-Year date source, direct Date/Time/DateTime field-component sources, checked ordinary Enumeration/category conversion, Date-only month/year differences, and direct resolved Number field-list aggregates through the same authored expression tree. Consumer-specific field resolution, model coherence, and runtime reads remain with each checked owner.
-/

namespace A12Kernel

/-- Kernel 30.8.1's authored Number digit budget for String/Enumeration conversion. Dot and leading minus do not consume the budget. -/
def maxFieldValueAsNumberDigits : Nat := 15

/-- One exactly parsed ASCII decimal token together with the static facts used by `FieldValueAsNumber` admission. Leading zeros and negative zero are retained only through digit count/scale; numeric evaluation observes their exact rational amount. -/
structure ParsedAsciiDecimalToken where
  value : Rat
  scale : Nat
  digitCount : Nat
  deriving Repr, DecidableEq

private def parseAsciiDigitsAllowEmpty (characters : List Char) : Option Nat :=
  if characters.isEmpty then some 0
  else parseAsciiNatural? (String.ofList characters)

/-- Parse the ASCII subset of Java `NumberUtils.isParsable` consumed by ordinary numeric Enumeration values: optional leading minus, at most one dot, at least one digit, and no trailing dot. A leading dot is legal. Digit-budget admission remains a separate model check. -/
def parseAsciiDecimalToken? (input : String) : Option ParsedAsciiDecimalToken := do
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
    let whole ← parseAsciiDigitsAllowEmpty wholeCharacters
    let fraction ← parseAsciiDigitsAllowEmpty fractionCharacters
    let factor := 10 ^ scale
    let magnitude : Rat := whole + (fraction : Rat) / factor
    some {
      value := if negative then -magnitude else magnitude
      scale
      digitCount := wholeCharacters.length + fractionCharacters.length }

/-- The exact selected stored/category token domain of one already-checked Enumeration projection. -/
def CheckedEnumerationProjection.selectedTokens
    (checked : CheckedEnumerationProjection) : List String :=
  match checked.projection with
  | .stored => checked.declaration.declaration.storedTokens
  | .category mapping => mapping.categoryTokens

/-- Derive the conversion result scale only when every selected token belongs to the currently supported ASCII subset and stays within the kernel digit budget. -/
def CheckedEnumerationProjection.numericAsciiScale?
    (checked : CheckedEnumerationProjection) : Option Nat := do
  let parsed ← checked.selectedTokens.mapM parseAsciiDecimalToken?
  if parsed.all (fun token => token.digitCount ≤ maxFieldValueAsNumberDigits) then
    some (parsed.foldl (fun scale token => max scale token.scale) 0)
  else
    none

/-- One ordinary closed Enumeration/category source statically certified for the implemented `FieldValueAsNumber` subset. The source keeps the shared runtime projection and its derived non-expandable scale together. -/
structure ResolvedFieldValueAsNumberSource where
  operand : FlatEnumerationOperand
  scale : Nat
  deriving Repr, DecidableEq

namespace ResolvedFieldValueAsNumberSource

def fieldId (source : ResolvedFieldValueAsNumberSource) : FieldId :=
  source.operand.field.id

def valueForStored? (source : ResolvedFieldValueAsNumberSource)
    (stored : String) : Option Rat := do
  let token ← source.operand.projection.tokenFor? stored
  let parsed ← parseAsciiDecimalToken? token
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

/-- Admit the ordinary closed-Enumeration ASCII subset after field/path resolution. Numeric String declarations remain fail-closed because the current flat model deliberately does not retain their exact `[0-9]+` pattern fact. -/
def FlatFieldDecl.resolveFieldValueAsNumberSource
    (declaration : FlatFieldDecl) (projectionRef : EnumerationProjectionRef) :
    Except FieldValueAsNumberSourceError ResolvedFieldValueAsNumberSource :=
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .error _ => .error .incoherentEnumeration
      | .ok checked =>
          match checkEnumerationProjection checked projectionRef with
          | .error error => .error (.enumeration error)
          | .ok projection =>
              match projection.numericAsciiScale? with
              | none => .error .notConvertible
              | some scale => .ok {
                  operand := {
                    field := { id := declaration.id }
                    projectionRef := projection.projectionRef
                    projection := projection.projection }
                  scale }
  | _, _ => .error .notConvertible

/-- Re-derive one resolved conversion source from the same model declaration. This keeps forged nonnumeric domains and scale summaries outside checked validation/computation cores. -/
def FlatModel.admitsFieldValueAsNumberSource (model : FlatModel)
    (source : ResolvedFieldValueAsNumberSource) : Bool :=
  match model.lookupUniqueId source.fieldId with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        match declaration.resolveFieldValueAsNumberSource source.operand.projectionRef with
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
  | stringRange (path : SurfaceFieldPath) (start finish : Nat)
  | fieldValueAsNumber (source : SurfaceTextFieldOperand)
  | dateDifference (unit : DateDifferenceUnit)
      (left right : SurfaceDateDifferenceOperand)
  | aggregate (op : NumericAggregateOp) (source : SurfaceNumericAggregateFields)
  deriving Repr, DecidableEq

inductive ResolvedNumericAtom (Field : Type) where
  | field (source : Field)
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource)
      (part : DateNumericPart)
  | temporalFieldPart (source : FlatTemporalField) (part : TemporalNumericPart)
  | stringRange (source : FlatStringField) (start finish : Nat)
  | fieldValueAsNumber (source : ResolvedFieldValueAsNumberSource)
  | dateDifference (unit : DateDifferenceUnit)
      (left right : ResolvedDateDifferenceOperand)
  | aggregate (op : NumericAggregateOp) (source : ResolvedNumericAggregateFields)
  deriving Repr, DecidableEq

namespace ResolvedNumericAtom

def isField : ResolvedNumericAtom Field → Bool
  | .field _ => true
  | .baseYear _ => false
  | .baseYearDatePart _ _ _ => false
  | .temporalFieldPart _ _ => true
  | .stringRange _ _ _ => true
  | .fieldValueAsNumber _ => true
  | .dateDifference _ left right => left.isField || right.isField
  | .aggregate _ _ => true

def requiresPlainArithmetic : ResolvedNumericAtom Field → Bool
  | .field _ => false
  | .baseYear _ | .baseYearDatePart _ _ _
  | .temporalFieldPart _ _ => true
  | .stringRange _ _ _ => true
  | .fieldValueAsNumber _ => true
  | .dateDifference _ _ _ => true
  | .aggregate _ _ => true

def summary (fieldSummary : Field → NumericScaleSummary) :
    ResolvedNumericAtom Field → NumericScaleSummary
  | .field source => fieldSummary source
  | .baseYear _ => NumericScaleSummary.field 0
  | .baseYearDatePart _ _ _ => NumericScaleSummary.field 0
  | .temporalFieldPart _ _ => NumericScaleSummary.field 0
  | .stringRange _ _ _ => NumericScaleSummary.field 0
  | .fieldValueAsNumber source => NumericScaleSummary.field source.scale
  | .dateDifference _ _ _ => NumericScaleSummary.field 0
  | .aggregate op source => op.scaleSummary source

end ResolvedNumericAtom

/-- The wrapper checker rejects only an immediate literal-like child. Numeric `BaseYear` is represented as an atom so it can participate in plain arithmetic, but it retains that source-level constant classification here; grouping does not hide either kind of immediate constant. -/
def AuthoredNumericExpr.isImmediateResolvedNumericConstant :
    AuthoredNumericExpr (ResolvedNumericAtom Field) → Bool
  | .literal _ | .atom (.baseYear _) => true
  | .group body => body.isImmediateResolvedNumericConstant
  | _ => false

/-- Root operation-form rounding and absolute value accept one already-checked plain-arithmetic child unless that complete child is an immediate literal-like constant. The wrapper delegates its body-local division and power checks; this predicate deliberately says nothing about a wrapper nested inside an enclosing arithmetic region. -/
def AuthoredNumericExpr.isRootResolvedUnaryValueFunction :
    AuthoredNumericExpr (ResolvedNumericAtom Field) → Bool
  | .round _ _ body | .abs body =>
      body.isPlainArithmetic && !body.isImmediateResolvedNumericConstant
  | _ => false

/-- Source operations participate in the audited arithmetic grammar, and one root unary wrapper may consume that complete plain-arithmetic tree. Enclosing arithmetic around a wrapper remains fail-closed until its legacy traversal is characterized separately. -/
def AuthoredNumericExpr.isAdmittedResolvedNumericOperation
    (expression : AuthoredNumericExpr (ResolvedNumericAtom Field)) : Bool :=
  if expression.isRootResolvedUnaryValueFunction then
    true
  else if expression.anyAtom ResolvedNumericAtom.requiresPlainArithmetic then
    expression.isPlainArithmetic
  else
    expression.isAdmittedNumericOperation

end A12Kernel
