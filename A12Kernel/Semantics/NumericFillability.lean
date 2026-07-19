import A12Kernel.Semantics.NumericArithmetic

/-! # A12Kernel.Semantics.NumericFillability — directional arithmetic propagation -/

namespace A12Kernel

/-- Current sign of a known numeric operand; fill propagation depends on it for multiplication. -/
inductive NumericSign where
  | negative
  | zero
  | positive
  deriving Repr, DecidableEq

namespace NumericSign

def ofRat (value : Rat) : NumericSign :=
  if value < 0 then .negative else if value = 0 then .zero else .positive

end NumericSign

/-- Directions in which filling a currently substituted numeric result can move it. -/
structure NumericFillability where
  canGrow : Bool
  canShrink : Bool
  deriving Repr, DecidableEq

namespace NumericFillability

def fixed : NumericFillability := { canGrow := false, canShrink := false }

def growOnly : NumericFillability := { canGrow := true, canShrink := false }

def shrinkOnly : NumericFillability := { canGrow := false, canShrink := true }

def both : NumericFillability := { canGrow := true, canShrink := true }

def emptyNumber (signed : Bool) : NumericFillability :=
  { canGrow := true, canShrink := signed }

def swapDirections (fillability : NumericFillability) : NumericFillability :=
  { canGrow := fillability.canShrink, canShrink := fillability.canGrow }

def add (left right : NumericFillability) : NumericFillability :=
  { canGrow := left.canGrow || right.canGrow
    canShrink := left.canShrink || right.canShrink }

def subtract (left right : NumericFillability) : NumericFillability :=
  { canGrow := left.canGrow || right.canShrink
    canShrink := left.canShrink || right.canGrow }

private def canGrowWhenScaledBy (fillability : NumericFillability) : NumericSign → Bool
  | .negative => fillability.canShrink
  | .zero => false
  | .positive => fillability.canGrow

private def canShrinkWhenScaledBy (fillability : NumericFillability) : NumericSign → Bool
  | .negative => fillability.canGrow
  | .zero => false
  | .positive => fillability.canShrink

def productCanGrow (left : NumericFillability) (leftSign : NumericSign)
    (right : NumericFillability) (rightSign : NumericSign) : Bool :=
  (left.canGrow && right.canGrow) ||
    (left.canShrink && right.canShrink) ||
    canGrowWhenScaledBy left rightSign ||
    canGrowWhenScaledBy right leftSign

def productCanShrink (left : NumericFillability) (leftSign : NumericSign)
    (right : NumericFillability) (rightSign : NumericSign) : Bool :=
  (left.canGrow && right.canShrink) ||
    (left.canShrink && right.canGrow) ||
    canShrinkWhenScaledBy left rightSign ||
    canShrinkWhenScaledBy right leftSign

def multiply (left : NumericFillability) (leftSign : NumericSign)
    (right : NumericFillability) (rightSign : NumericSign) : NumericFillability :=
  { canGrow := productCanGrow left leftSign right rightSign
    canShrink := productCanShrink left leftSign right rightSign }

end NumericFillability

/-- Propagate directional fillability through one total arithmetic node. -/
def NumericArithmeticOp.fillability (op : NumericArithmeticOp)
    (leftValue : Rat) (leftFill : NumericFillability)
    (rightValue : Rat) (rightFill : NumericFillability) : NumericFillability :=
  match op with
  | .add => leftFill.add rightFill
  | .subtract => leftFill.subtract rightFill
  | .multiply =>
      leftFill.multiply (NumericSign.ofRat leftValue)
        rightFill (NumericSign.ofRat rightValue)

/--
A known numeric arithmetic result carries its value and directional fillability together. A
domain-undefined child absorbs its enclosing arithmetic node; formal-invalid operands remain a separate
checked-expression concern.
-/
inductive NumericArithmeticOutcome where
  | value (amount : Rat) (fillability : NumericFillability)
  | notEvaluated
  deriving Repr, DecidableEq

namespace NumericArithmeticOutcome

/-- Evaluate one total arithmetic node, absorbing a domain-undefined child before doing arithmetic. -/
def eval (op : NumericArithmeticOp) :
    NumericArithmeticOutcome → NumericArithmeticOutcome → NumericArithmeticOutcome
  | .value leftValue leftFill, .value rightValue rightFill =>
      .value (op.eval leftValue rightValue)
        (op.fillability leftValue leftFill rightValue rightFill)
  | _, _ => .notEvaluated

private def reciprocalFillability (fillability : NumericFillability) :
    NumericSign → NumericFillability
  | .negative =>
      { canGrow := fillability.canShrink || fillability.canGrow
        canShrink := fillability.canGrow }
  | .zero => fillability.swapDirections
  | .positive =>
      { canGrow := fillability.canShrink
        canShrink := fillability.canGrow || fillability.canShrink }

/--
Divide two arithmetic outcomes. The value route reuses direct precision-50 division; only the
fillability route treats the divisor as a reciprocal, and a current zero divisor is rejected first.
-/
def divide : NumericArithmeticOutcome → NumericArithmeticOutcome → NumericArithmeticOutcome
  | .value dividend dividendFill, .value divisor divisorFill =>
      match divideNumeric dividend divisor with
      | .notEvaluated => .notEvaluated
      | .value quotient =>
          let divisorSign := NumericSign.ofRat divisor
          .value quotient
            (dividendFill.multiply (NumericSign.ofRat dividend)
              (reciprocalFillability divisorFill divisorSign) divisorSign)
  | _, _ => .notEvaluated

end NumericArithmeticOutcome

end A12Kernel
