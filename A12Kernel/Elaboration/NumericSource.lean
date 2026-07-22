import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression

/-! # Shared checked numeric-expression sources

Validation and computation both consume Number-field references, numeric `BaseYear`, direct numeric date-component extraction from a Base-Year date source, and direct Date/Time/DateTime field-component sources through the same authored expression tree. Consumer-specific field resolution, model coherence, and runtime reads remain with each checked owner.
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

inductive SurfaceNumericAtom where
  | field (path : SurfaceFieldPath)
  | baseYear
  | baseYearDatePart (source : BaseYearDateSource) (part : DateNumericPart)
  | temporalFieldPart (path : SurfaceFieldPath) (part : TemporalNumericPart)
  deriving Repr, DecidableEq

inductive ResolvedNumericAtom (Field : Type) where
  | field (source : Field)
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource)
      (part : DateNumericPart)
  | temporalFieldPart (source : FlatTemporalField) (part : TemporalNumericPart)
  deriving Repr, DecidableEq

namespace ResolvedNumericAtom

def isField : ResolvedNumericAtom Field → Bool
  | .field _ => true
  | .baseYear _ => false
  | .baseYearDatePart _ _ _ => false
  | .temporalFieldPart _ _ => true

def requiresPlainArithmetic : ResolvedNumericAtom Field → Bool
  | .field _ => false
  | .baseYear _ | .baseYearDatePart _ _ _
  | .temporalFieldPart _ _ => true

def summary (fieldSummary : Field → NumericScaleSummary) :
    ResolvedNumericAtom Field → NumericScaleSummary
  | .field source => fieldSummary source
  | .baseYear _ => NumericScaleSummary.field 0
  | .baseYearDatePart _ _ _ => NumericScaleSummary.field 0
  | .temporalFieldPart _ _ => NumericScaleSummary.field 0

end ResolvedNumericAtom

/-- Source operations participate in the audited arithmetic grammar but do not implicitly widen separately checked direct Number-field value-function shapes. -/
def AuthoredNumericExpr.isAdmittedResolvedNumericOperation
    (expression : AuthoredNumericExpr (ResolvedNumericAtom Field)) : Bool :=
  if expression.anyAtom ResolvedNumericAtom.requiresPlainArithmetic then
    expression.isPlainArithmetic
  else
    expression.isAdmittedNumericOperation

end A12Kernel
