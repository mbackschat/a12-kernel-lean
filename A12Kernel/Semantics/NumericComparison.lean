import A12Kernel.Cell
import A12Kernel.Semantics.NumericFillability

/-! # A12Kernel.Semantics.NumericComparison — numeric truth and directional polarity

Numeric comparison has two independent outputs: whether the normalized values satisfy the condition, and whether later filling could move a substituted value far enough to clear a firing. This module owns the shared scale-19 comparison boundary and the left-operand fillability needed by the current field-versus-literal fragment.
-/

namespace A12Kernel

inductive NumericComparisonOp where
  | equal
  | notEqual
  | less
  | greaterEqual
  deriving Repr, DecidableEq

/-- A numeric comparison operand after the consuming clause has applied its own empty-value rule. -/
inductive NumericOperand where
  | value (amount : Rat) (fillability : NumericFillability)
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Rounding preserves the operand's invalid cause or directional fillability; it changes only a known amount. -/
def NumericOperand.round (operand : NumericOperand) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) : NumericOperand :=
  match operand with
  | .value amount fillability => .value (roundDecimal mode amount places) fillability
  | .unknown cause => .unknown cause

/-- The fixed decimal scale applied to both numeric operands before every comparison. -/
def comparisonScale : Nat := decimalPreRoundScale

def normalizedComparisonValue (value : Rat) : Rat :=
  rescaleHalfUp value comparisonScale

def NumericComparisonOp.holds (op : NumericComparisonOp) (left right : Rat) : Bool :=
  let left := normalizedComparisonValue left
  let right := normalizedComparisonValue right
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .less => left < right
  | .greaterEqual => left >= right

/-- Whether an available operand movement can close the current normalized numeric gap. Callers use this only when the normalized operands differ. -/
def numericDifferenceFillCanClose (left right : Rat)
    (leftFill rightFill : NumericFillability) : Bool :=
  if normalizedComparisonValue left < normalizedComparisonValue right then
    leftFill.canGrow || rightFill.canShrink
  else
    leftFill.canShrink || rightFill.canGrow

/-- Whether filling the left operand in an available direction could falsify a condition that currently holds against a fixed literal. For inequality, the breaking direction depends on which normalized side is smaller. -/
def NumericComparisonOp.leftFillCanBreak (op : NumericComparisonOp) (left right : Rat)
    (fillability : NumericFillability) : Bool :=
  match op with
  | .equal => fillability.canGrow || fillability.canShrink
  | .notEqual => numericDifferenceFillCanClose left right fillability .fixed
  | .less => fillability.canGrow
  | .greaterEqual => fillability.canShrink

/-- Evaluate one numeric expression against a fixed literal. Unknown remains distinct from false; a firing is omission-typed exactly when filling can move the left operand in a breaking direction. -/
def NumericComparisonOp.evalFixedRight (op : NumericComparisonOp) (operand : NumericOperand)
    (expected : Rat) : Verdict :=
  match operand with
  | .unknown _ => .unknown
  | .value actual fillability =>
      if op.holds actual expected then
        if op.leftFillCanBreak actual expected fillability then
          .fired .omission
        else
          .fired .value
      else
        .notFired

/-- Validation's fixed-right projection distinguishes a formal-invalid expression from a pure arithmetic domain failure. -/
def NumericComparisonOp.evalArithmeticFixedRight (op : NumericComparisonOp)
    (outcome : Except FormalCause NumericArithmeticOutcome) (expected : Rat) : Verdict :=
  match outcome with
  | .error _ => .unknown
  | .ok .notEvaluated => .notFired
  | .ok (.value amount fillability) =>
      op.evalFixedRight (.value amount fillability) expected

end A12Kernel
