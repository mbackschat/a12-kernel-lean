import A12Kernel.Elaboration.Flat.Condition.Core

/-! # Flat-condition surface-lowering vocabulary -/

namespace A12Kernel

def SurfaceComparisonOp.toEquality? : SurfaceComparisonOp → Option EqualityOp
  | .equal => some .equal
  | .notEqual => some .notEqual
  | _ => none

def SurfaceComparisonOp.toNumeric? : SurfaceComparisonOp → Option NumericComparisonOp
  | .equal => some .equal
  | .notEqual => some .notEqual
  | .less => some .less
  | .lessEqual => some .lessEqual
  | .greater => some .greater
  | .greaterEqual => some .greaterEqual

def SurfaceComparisonOp.toStringLength? : SurfaceComparisonOp →
    Option StringLengthComparisonOp
  | .less => some .less
  | .lessEqual => some .lessEqual
  | .greater => some .greater
  | .greaterEqual => some .greaterEqual
  | _ => none

def SurfaceComparisonOp.toTemporal : SurfaceComparisonOp → TemporalComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .before
  | .lessEqual => .beforeOrEqual
  | .greater => .after
  | .greaterEqual => .afterOrEqual

def SurfaceComparisonOp.swapped : SurfaceComparisonOp → SurfaceComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .greater
  | .lessEqual => .greaterEqual
  | .greater => .less
  | .greaterEqual => .lessEqual

def temporalPointComparison (comparison : TemporalComparisonOp)
    (position : SurfacePointInTimePosition) (point field : FlatTemporalOperand) :
    FlatCondition :=
  match position with
  | .left => .compare (.temporal comparison point field)
  | .right => .compare (.temporal comparison field point)

def BaseYearRangeEndpoint.surfacePath : BaseYearRangeEndpoint → List String
  | .start => ["<StartOfDateRange(BaseYear)>"]
  | .finish => ["<EndOfDateRange(BaseYear)>"]

/-- Direct temporal comparisons use the declared formats to select clock or instant identity. -/
def elaborateTemporalFieldPair (hasBaseYear : Bool) (op : TemporalComparisonOp)
    (left right : FlatFieldDecl) : Except ElabError FlatComparison := do
  let some leftField := left.toTemporalField? |
    throw (.temporalOperandKindMismatch left.path right.path left.policy.kind.surfaceKind right.policy.kind.surfaceKind)
  let some rightField := right.toTemporalField? |
    throw (.temporalOperandKindMismatch left.path right.path left.policy.kind.surfaceKind right.policy.kind.surfaceKind)
  if !op.admitsFormats hasBaseYear leftField.components rightField.components then
    throw (.temporalFormatsIncompatible left.path right.path)
  if !leftField.components.hasDate && !rightField.components.hasDate then
    pure (.time op leftField rightField)
  else
    pure (.temporal op (.fieldValue leftField) (.fieldValue rightField))

end A12Kernel
