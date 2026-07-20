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

/-- Absolute value can grow when either source direction moves the magnitude; only movement toward zero can shrink it. -/
def absolute (fillability : NumericFillability)
    (sign : NumericSign) : NumericFillability :=
  { canGrow := fillability.canGrow || fillability.canShrink
    canShrink := match sign with
      | .negative => fillability.canGrow
      | .zero => false
      | .positive => fillability.canShrink }

/-- Directional fillability for `Min(left, right)`: either operand may lower the result; only the currently smaller operand may raise it, and both must be able to raise an exact tie. -/
def minimum (left : NumericFillability) (leftValue : Rat)
    (right : NumericFillability) (rightValue : Rat) : NumericFillability :=
  { canGrow :=
      if leftValue < rightValue then left.canGrow
      else if rightValue < leftValue then right.canGrow
      else left.canGrow && right.canGrow
    canShrink := left.canShrink || right.canShrink }

/-- Directional fillability for `Max(left, right)`: either operand may raise the result; only the currently larger operand may lower it, and both must be able to lower an exact tie. -/
def maximum (left : NumericFillability) (leftValue : Rat)
    (right : NumericFillability) (rightValue : Rat) : NumericFillability :=
  { canGrow := left.canGrow || right.canGrow
    canShrink :=
      if rightValue < leftValue then left.canShrink
      else if leftValue < rightValue then right.canShrink
      else left.canShrink && right.canShrink }

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

namespace NumericExtremumOp

/-- Select two available arithmetic outcomes at full precision while combining their directional fillability; unavailability absorbs on either side. -/
def selectOutcome (op : NumericExtremumOp) :
    NumericArithmeticOutcome → NumericArithmeticOutcome → NumericArithmeticOutcome
  | .value leftValue leftFill, .value rightValue rightFill =>
      let selectedFill := match op with
        | minimum =>
            NumericFillability.minimum leftFill leftValue rightFill rightValue
        | maximum =>
            NumericFillability.maximum leftFill leftValue rightFill rightValue
      .value (selectAmount op leftValue rightValue) selectedFill
  | _, _ => .notEvaluated

end NumericExtremumOp

namespace NumericArithmeticOutcome

/-- Transform only an available amount and its directional metadata; domain failure remains unavailable. -/
def mapValue (outcome : NumericArithmeticOutcome)
    (transform : Rat → NumericFillability → Rat × NumericFillability) :
    NumericArithmeticOutcome :=
  match outcome with
  | .value amount fillability =>
      let transformed := transform amount fillability
      .value transformed.1 transformed.2
  | .notEvaluated => .notEvaluated

/-- Transform an available amount and its sign-sensitive directions; domain failure remains unavailable. -/
def absolute (outcome : NumericArithmeticOutcome) : NumericArithmeticOutcome :=
  outcome.mapValue (fun amount fillability =>
    (absoluteNumeric amount,
      fillability.absolute (NumericSign.ofRat amount)))

/-- Round a known amount while preserving its directional metadata; domain failure remains unavailable. -/
def round (outcome : NumericArithmeticOutcome)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) : NumericArithmeticOutcome :=
  outcome.mapValue (fun amount fillability =>
    (roundDecimal mode amount places, fillability))

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

private def fillabilityIsFixed (fillability : NumericFillability) : Bool :=
  !fillability.canGrow && !fillability.canShrink

private def powerWithFixedExponent (base : Rat) (baseFill : NumericFillability)
    (exponent : Nat) : NumericFillability :=
  if exponent = 0 then
    .fixed
  else if fillabilityIsFixed baseFill then
    .fixed
  else
    let even : Bool := decide (exponent % 2 = 0)
    { canGrow := baseFill.canGrow || even
      canShrink :=
        (baseFill.canShrink && (!even || decide (0 < base))) ||
          (even && decide (base < 0) && baseFill.canGrow) }

private def powerWithFixedZeroBase (exponentFill : NumericFillability)
    (exponent : Nat) : NumericFillability :=
  if !exponentFill.canShrink then
    if exponent = 0 then .shrinkOnly else .fixed
  else
    .growOnly

private def powerWithFixedNegativeBase (base : Rat)
    (exponentFill : NumericFillability) (exponent : Nat) : NumericFillability :=
  let even : Bool := decide (exponent % 2 = 0)
  if -1 < base then
    if !exponentFill.canShrink then
      if even then .shrinkOnly else .growOnly
    else
      .both
  else if base = -1 then
    if even then .shrinkOnly else .growOnly
  else if !exponentFill.canGrow then
    if even then .shrinkOnly else .growOnly
  else
    .both

private def powerWithFixedBase (base : Rat) (exponentFill : NumericFillability)
    (exponent : Nat) : NumericFillability :=
  if 1 < base then
    exponentFill
  else if base = 1 then
    .fixed
  else if 0 < base then
    exponentFill.swapDirections
  else if base = 0 then
    powerWithFixedZeroBase exponentFill exponent
  else
    powerWithFixedNegativeBase base exponentFill exponent

/-- The kernel's conservative directional metadata for a domain-valid power with a nonnegative integral exponent. This is a branch table, not exact mathematical reachability. -/
private def powerNonnegativeFillability (base : Rat)
    (baseFill exponentFill : NumericFillability) (exponent : Nat) :
    NumericFillability :=
  if fillabilityIsFixed exponentFill then
    powerWithFixedExponent base baseFill exponent
  else if fillabilityIsFixed baseFill then
    powerWithFixedBase base exponentFill exponent
  else if decide (1 < base) && !exponentFill.canShrink && !baseFill.canShrink then
    .growOnly
  else
    .both

/-- Direction helper called only after `powerNumeric` succeeds; `.fixed` in its rejected branches is an unreachable totality fallback. -/
private def powerFillability (base : Rat) (baseFill : NumericFillability)
    (exponent : Rat) (exponentFill : NumericFillability) :
    NumericFillability :=
  match checkedPowerExponent? exponent with
  | none => .fixed
  | some (.ofNat magnitude) =>
      powerNonnegativeFillability base baseFill exponentFill magnitude
  | some (.negSucc predecessor) =>
      match divideNumeric 1 base with
      | .notEvaluated => .fixed
      | .value reciprocal =>
          powerNonnegativeFillability reciprocal
            (reciprocalFillability baseFill (NumericSign.ofRat base))
            exponentFill.swapDirections (predecessor + 1)

/-- Evaluate power value and directional metadata together. The staged value evaluator is the sole domain gate; directional metadata is computed only for a successful value. Either unavailable child absorbs before comparison, and negative powers reuse the precision-50 reciprocal route and swap exponent directions. -/
def power : NumericArithmeticOutcome → NumericArithmeticOutcome → NumericArithmeticOutcome
  | .value base baseFill, .value exponent exponentFill =>
      match powerNumeric base exponent with
      | .notEvaluated => .notEvaluated
      | .value amount =>
          .value amount (powerFillability base baseFill exponent exponentFill)
  | _, _ => .notEvaluated

end NumericArithmeticOutcome

end A12Kernel
