import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.DateDifference

/-! # Shared checked numeric-expression sources

Validation and computation both consume Number-field references, numeric `BaseYear`, direct numeric date-component extraction from a Base-Year date source, direct Date/Time/DateTime field-component sources, Date-only month/year differences, and direct resolved Number field-list aggregates through the same authored expression tree. Consumer-specific field resolution, model coherence, and runtime reads remain with each checked owner.
-/

namespace A12Kernel

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
  | .dateDifference _ left right => left.isField || right.isField
  | .aggregate _ _ => true

def requiresPlainArithmetic : ResolvedNumericAtom Field → Bool
  | .field _ => false
  | .baseYear _ | .baseYearDatePart _ _ _
  | .temporalFieldPart _ _ => true
  | .stringRange _ _ _ => true
  | .dateDifference _ _ _ => true
  | .aggregate _ _ => true

def summary (fieldSummary : Field → NumericScaleSummary) :
    ResolvedNumericAtom Field → NumericScaleSummary
  | .field source => fieldSummary source
  | .baseYear _ => NumericScaleSummary.field 0
  | .baseYearDatePart _ _ _ => NumericScaleSummary.field 0
  | .temporalFieldPart _ _ => NumericScaleSummary.field 0
  | .stringRange _ _ _ => NumericScaleSummary.field 0
  | .dateDifference _ _ _ => NumericScaleSummary.field 0
  | .aggregate op source => op.scaleSummary source

end ResolvedNumericAtom

/-- The checked aggregate grammar admits the established direct aggregate-rounding form without treating aggregates as ordinary scalar fields for every value function. -/
def AuthoredNumericExpr.isDirectAggregateRound :
    AuthoredNumericExpr (ResolvedNumericAtom Field) → Bool
  | .round _ _ (.atom (.aggregate _ _)) => true
  | _ => false

/-- Source operations participate in the audited arithmetic grammar but do not implicitly widen separately checked direct Number-field value-function shapes. -/
def AuthoredNumericExpr.isAdmittedResolvedNumericOperation
    (expression : AuthoredNumericExpr (ResolvedNumericAtom Field)) : Bool :=
  if expression.isDirectAggregateRound then
    true
  else if expression.anyAtom ResolvedNumericAtom.requiresPlainArithmetic then
    expression.isPlainArithmetic
  else
    expression.isAdmittedNumericOperation

end A12Kernel
