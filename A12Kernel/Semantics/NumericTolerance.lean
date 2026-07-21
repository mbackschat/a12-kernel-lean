import A12Kernel.Semantics.NumericComparison

/-! # Fixed numeric-tolerance comparisons

The kernel exposes four closed tolerance bands. Each operand is normalized independently at the ordinary comparison scale before the absolute difference is tested. Polarity follows directional inequality: only a legal movement toward the other operand can repair a firing.
-/

namespace A12Kernel

inductive NumericToleranceRange where
  | range1
  | range2
  | range5
  | range10
  deriving Repr, DecidableEq

def NumericToleranceRange.threshold : NumericToleranceRange → Rat
  | .range1 => 1
  | .range2 => 2
  | .range5 => 5
  | .range10 => 10

def normalizedNumericDifference (left right : Rat) : Rat :=
  (normalizedComparisonValue left - normalizedComparisonValue right).abs

def NumericToleranceRange.holds (range : NumericToleranceRange) (left right : Rat) : Bool :=
  range.threshold < normalizedNumericDifference left right

def NumericToleranceRange.eval (range : NumericToleranceRange)
    (left right : NumericOperand) : Verdict :=
  match left, right with
  | .unknown _, _ => .unknown
  | _, .unknown _ => .unknown
  | .value leftAmount leftFill, .value rightAmount rightFill =>
      if range.holds leftAmount rightAmount then
        if numericDifferenceFillCanClose leftAmount rightAmount leftFill rightFill then
          .fired .omission
        else
          .fired .value
      else
        .notFired

/-- Closed operator family admitted by the checked numeric-validation leaf. -/
inductive NumericValidationOp where
  | ordinary (op : NumericComparisonOp)
  | tolerance (range : NumericToleranceRange)
  deriving Repr, DecidableEq

/-- Dispatch two already classified operands without changing either primitive operation's semantics. -/
def NumericValidationOp.eval (op : NumericValidationOp)
    (left right : NumericOperand) : Verdict :=
  match op with
  | .ordinary comparison => comparison.eval left right
  | .tolerance range => range.eval left right

/-- Specialize the shared closed dispatch to a fixed literal on the right. -/
def NumericValidationOp.evalFixedRight (op : NumericValidationOp)
    (left : NumericOperand) (expected : Rat) : Verdict :=
  op.eval left (.value expected .fixed)

/-- Shared validation projection: formal invalidity stays unknown and arithmetic domain failure stays quiet before operator dispatch. -/
def NumericValidationOp.evalArithmetic (op : NumericValidationOp)
    (left right : Except FormalCause NumericArithmeticOutcome) : Verdict :=
  match left, right with
  | .error _, _ | _, .error _ => .unknown
  | .ok .notEvaluated, _ | _, .ok .notEvaluated => .notFired
  | .ok (.value left leftFill), .ok (.value right rightFill) =>
      op.eval (.value left leftFill) (.value right rightFill)

end A12Kernel
