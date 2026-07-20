import A12Kernel.Core

/-! # Static numeric-scale summaries

Numeric authoring checks use a signed exact scale or unknown plus a separate capability saying that the expression's scale may be expanded by trailing zeros. This metadata is independent of runtime numeric values.
-/

namespace A12Kernel

namespace ScaleInfo

def maxExact : ScaleInfo → ScaleInfo → ScaleInfo
  | .exact left, .exact right => .exact (max left right)
  | _, _ => .unknown

def addExact : ScaleInfo → ScaleInfo → ScaleInfo
  | .exact left, .exact right => .exact (left + right)
  | _, _ => .unknown

end ScaleInfo

structure NumericScaleSummary where
  scale : ScaleInfo
  canExpandScale : Bool
  deriving Repr, DecidableEq

inductive NumericScaleBinaryOp where
  | add
  | subtract
  | multiply
  | divide
  deriving Repr, DecidableEq

namespace NumericScaleSummary

def field (scale : Nat) : NumericScaleSummary :=
  { scale := .exact scale, canExpandScale := false }

/-- Construct the summary of an already-decoded numeric constant. The signed scale preserves authored fractional length or integer trailing-zero stripping. -/
def constant (scale : Int) : NumericScaleSummary :=
  { scale := .exact scale, canExpandScale := true }

def rounded (scale : Nat) : NumericScaleSummary :=
  { scale := .exact scale, canExpandScale := false }

/-- Combine scale metadata for an additive or operand-list extremum result: the largest exact operand scale wins, and trailing-zero expansion remains available only when every operand supplies it. -/
def union (left right : NumericScaleSummary) : NumericScaleSummary :=
  { scale := left.scale.maxExact right.scale
    canExpandScale := left.canExpandScale && right.canExpandScale }

def binary (op : NumericScaleBinaryOp)
    (left right : NumericScaleSummary) : NumericScaleSummary :=
  match op with
  | .add | .subtract => left.union right
  | .multiply =>
      { scale := left.scale.addExact right.scale
        canExpandScale := left.canExpandScale || right.canExpandScale }
  | .divide =>
      { scale := .unknown, canExpandScale := false }

def validPowerExponent (exponent : NumericScaleSummary) : Bool :=
  match exponent.scale with
  | .exact scale => scale <= 0
  | .unknown => false

/-- Check the exponent-scale rule and derive the narrow known power scale. Numeric integrality and the runtime `-1000..1000` domain are separate checks. -/
def power? (base exponent : NumericScaleSummary)
    (simpleNonnegativeConstantExponent : Bool) : Option NumericScaleSummary :=
  if exponent.validPowerExponent then
    let resultScale :=
      match base.scale with
      | .exact 0 =>
          if simpleNonnegativeConstantExponent then .exact 0 else .unknown
      | _ => .unknown
    some { scale := resultScale, canExpandScale := false }
  else
    none

end NumericScaleSummary

/-- The unsuppressed static gate for numeric equality and inequality. Equal exact scales pass; otherwise only a capable smaller-scale side may be padded. -/
def exactNumericScaleComparisonAllowed
    (left right : NumericScaleSummary) : Bool :=
  match left.scale, right.scale with
  | .exact leftScale, .exact rightScale =>
      (leftScale == rightScale) ||
        (decide (leftScale < rightScale) && left.canExpandScale) ||
        (decide (rightScale < leftScale) && right.canExpandScale)
  | _, _ => false

end A12Kernel
