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

end A12Kernel
