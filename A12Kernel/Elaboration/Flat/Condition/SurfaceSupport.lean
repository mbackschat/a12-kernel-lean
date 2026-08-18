import A12Kernel.Elaboration.Flat.Condition.Core

/-! # Flat-condition surface-lowering vocabulary -/

namespace A12Kernel

def FieldKind.surfaceKind : FieldKind → SurfaceScalarKind
  | .number _ => .number
  | .boolean => .boolean
  | .confirm => .confirm
  | .string => .string
  | .enumeration => .enumeration
  | .temporal kind _ => .temporal kind
  | .dateRange => .dateRange

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

end A12Kernel
