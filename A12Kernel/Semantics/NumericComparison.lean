import A12Kernel.Cell
import A12Kernel.Semantics.NumericFillability

/-! # A12Kernel.Semantics.NumericComparison — numeric truth and directional polarity

Numeric comparison has two independent outputs: whether the normalized values satisfy the condition, and whether later filling could move either substituted operand far enough to clear a firing. This module owns the shared scale-19 comparison boundary and the complete two-sided directional-polarity dispatch.
-/

namespace A12Kernel

inductive NumericComparisonOp where
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq

/-- A numeric comparison operand after the consuming clause has applied its own empty-value rule. -/
inductive NumericOperand where
  | value (amount : Rat) (fillability : NumericFillability)
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

namespace CellObservation

/-- Apply the direct-validation Number empty rule to an already phase-classified cell. This shared seam keeps ordinary and semantic-index reads from inventing different numeric substitutions. -/
def asValidationNumericOperand (field : NumField) :
    CellObservation → NumericOperand
  | .empty => NumericOperand.value 0 (.emptyNumber field.signed)
  | .value observed =>
      match observed with
      | .num amount => NumericOperand.value amount .fixed
      | _ => NumericOperand.unknown .malformed
  | .unknown cause => NumericOperand.unknown cause
  | .poison cause => NumericOperand.unknown cause

end CellObservation

/-- Apply the symmetric empty-to-zero rule shared by temporal numeric component consumers. Present projected values are fixed; exact unavailability causes remain available to later verdict projection. -/
def symmetricValidationNumericOperand (project : α → Rat)
    (observation : CellObservation α) : NumericOperand :=
  match observation with
  | .empty => NumericOperand.value 0 .both
  | .value value => NumericOperand.value (project value) .fixed
  | .unknown cause => NumericOperand.unknown cause
  | .poison cause => NumericOperand.unknown cause

/-- Transform only a known amount and its directional metadata; preserve the exact invalid cause. -/
def NumericOperand.mapValue (operand : NumericOperand)
    (transform : Rat → NumericFillability → Rat × NumericFillability) : NumericOperand :=
  match operand with
  | .value amount fillability =>
      let transformed := transform amount fillability
      .value transformed.1 transformed.2
  | .unknown cause => .unknown cause

/-- Rounding preserves the operand's invalid cause or directional fillability; it changes only a known amount. -/
def NumericOperand.round (operand : NumericOperand) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) : NumericOperand :=
  operand.mapValue (fun amount fillability =>
    (roundDecimal mode amount places, fillability))

/-- Absolute value preserves an invalid cause and transforms known directional metadata from the operand's current sign. -/
def NumericOperand.absolute (operand : NumericOperand) : NumericOperand :=
  operand.mapValue (fun amount fillability =>
    (absoluteNumeric amount,
      fillability.absolute (NumericSign.ofRat amount)))

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
  | .lessEqual => left <= right
  | .greater => left > right
  | .greaterEqual => left >= right

/-- Whether an available operand movement can close the current normalized numeric gap. Callers use this only when the normalized operands differ. -/
def numericDifferenceFillCanClose (left right : Rat)
    (leftFill rightFill : NumericFillability) : Bool :=
  if normalizedComparisonValue left < normalizedComparisonValue right then
    leftFill.canGrow || rightFill.canShrink
  else
    leftFill.canShrink || rightFill.canGrow

/-- Whether filling either operand in an available direction could falsify a numeric condition that currently holds. -/
def NumericComparisonOp.fillCanBreak (op : NumericComparisonOp) (left right : Rat)
    (leftFill rightFill : NumericFillability) : Bool :=
  match op with
  | .equal =>
      leftFill.canGrow || leftFill.canShrink ||
        rightFill.canGrow || rightFill.canShrink
  | .notEqual => numericDifferenceFillCanClose left right leftFill rightFill
  | .less | .lessEqual => leftFill.canGrow || rightFill.canShrink
  | .greater | .greaterEqual => leftFill.canShrink || rightFill.canGrow

/-- Evaluate two numeric operands. Unknown remains distinct from false; a firing is omission-typed exactly when filling can move either operand in a breaking direction. -/
def NumericComparisonOp.eval (op : NumericComparisonOp)
    (leftOperand rightOperand : NumericOperand) : Verdict :=
  match leftOperand, rightOperand with
  | .unknown _, _ | _, .unknown _ => .unknown
  | .value left leftFill, .value right rightFill =>
      if op.holds left right then
        if op.fillCanBreak left right leftFill rightFill then
          .fired .omission
        else
          .fired .value
      else
        .notFired

/-- Evaluate one numeric expression against a fixed literal. -/
def NumericComparisonOp.evalFixedRight (op : NumericComparisonOp) (operand : NumericOperand)
    (expected : Rat) : Verdict :=
  op.eval operand (.value expected .fixed)

end A12Kernel
