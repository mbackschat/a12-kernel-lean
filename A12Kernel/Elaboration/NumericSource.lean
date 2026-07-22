import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression

/-! # Shared checked numeric-expression sources

Validation and computation both consume Number-field references and the model-declared numeric `BaseYear` through the same authored expression tree. Consumer-specific field resolution, model coherence, and runtime reads remain with each checked owner.
-/

namespace A12Kernel

inductive SurfaceNumericAtom where
  | field (path : SurfaceFieldPath)
  | baseYear
  deriving Repr, DecidableEq

inductive ResolvedNumericAtom (Field : Type) where
  | field (source : Field)
  | baseYear (year : Int)
  deriving Repr, DecidableEq

namespace ResolvedNumericAtom

def isField : ResolvedNumericAtom Field → Bool
  | .field _ => true
  | .baseYear _ => false

def isBaseYear : ResolvedNumericAtom Field → Bool
  | .field _ => false
  | .baseYear _ => true

def summary (fieldSummary : Field → NumericScaleSummary) :
    ResolvedNumericAtom Field → NumericScaleSummary
  | .field source => fieldSummary source
  | .baseYear _ => NumericScaleSummary.field 0

end ResolvedNumericAtom

/-- Base Year participates in the audited arithmetic grammar but does not implicitly widen separately checked direct value-function shapes. -/
def AuthoredNumericExpr.isAdmittedResolvedNumericOperation
    (expression : AuthoredNumericExpr (ResolvedNumericAtom Field)) : Bool :=
  if expression.anyAtom ResolvedNumericAtom.isBaseYear then
    expression.isPlainArithmetic
  else
    expression.isAdmittedNumericOperation

end A12Kernel
