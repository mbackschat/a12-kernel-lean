import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression

/-! # Shared checked numeric-expression sources

Validation and computation both consume Number-field references, numeric `BaseYear`, and direct numeric date-component extraction from a Base-Year date source through the same authored expression tree. Consumer-specific field resolution, model coherence, and runtime reads remain with each checked owner.
-/

namespace A12Kernel

inductive SurfaceNumericAtom where
  | field (path : SurfaceFieldPath)
  | baseYear
  | baseYearDatePart (source : BaseYearDateSource) (part : DateNumericPart)
  deriving Repr, DecidableEq

inductive ResolvedNumericAtom (Field : Type) where
  | field (source : Field)
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource)
      (part : DateNumericPart)
  deriving Repr, DecidableEq

namespace ResolvedNumericAtom

def isField : ResolvedNumericAtom Field → Bool
  | .field _ => true
  | .baseYear _ => false
  | .baseYearDatePart _ _ _ => false

def isBaseYear : ResolvedNumericAtom Field → Bool
  | .field _ => false
  | .baseYear _ => true
  | .baseYearDatePart _ _ _ => true

def summary (fieldSummary : Field → NumericScaleSummary) :
    ResolvedNumericAtom Field → NumericScaleSummary
  | .field source => fieldSummary source
  | .baseYear _ => NumericScaleSummary.field 0
  | .baseYearDatePart _ _ _ => NumericScaleSummary.field 0

end ResolvedNumericAtom

/-- Base Year participates in the audited arithmetic grammar but does not implicitly widen separately checked direct value-function shapes. -/
def AuthoredNumericExpr.isAdmittedResolvedNumericOperation
    (expression : AuthoredNumericExpr (ResolvedNumericAtom Field)) : Bool :=
  if expression.anyAtom ResolvedNumericAtom.isBaseYear then
    expression.isPlainArithmetic
  else
    expression.isAdmittedNumericOperation

end A12Kernel
