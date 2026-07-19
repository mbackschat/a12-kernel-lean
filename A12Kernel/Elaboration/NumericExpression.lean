import A12Kernel.Elaboration.NumericScale
import A12Kernel.Semantics.NumericArithmetic

/-! # Authored and evaluation numeric expressions

The authored tree retains syntax-derived literal scale and grouping. Evaluation uses a distinct lowered tree because the kernel performs one order-sensitive post-order rewrite of multiplication nodes containing immediate divided factors before applying per-node decimal arithmetic.
-/

namespace A12Kernel

/-- One numeric token after decoding. `authoredScale` is syntax metadata and cannot be recovered from `value`; for example, `0` and `0.00` have the same value but scales 0 and 2. -/
structure DecodedNumericLiteral where
  value : Rat
  authoredScale : Int
  deriving Repr, DecidableEq

/-- Parser-independent numeric syntax. `group` retains curly braces for authoring checks even though evaluation lowering later erases that wrapper. -/
inductive AuthoredNumericExpr (Atom : Type) where
  | atom (atom : Atom)
  | literal (literal : DecodedNumericLiteral)
  | group (body : AuthoredNumericExpr Atom)
  | binary (op : NumericScaleBinaryOp)
      (left right : AuthoredNumericExpr Atom)
  | power (base exponent : AuthoredNumericExpr Atom)
  | round (mode : DecimalRoundingMode) (places : RoundingPlaces)
      (body : AuthoredNumericExpr Atom)
  deriving Repr, DecidableEq

/-- Runtime arithmetic tree after the source-ordered division rewrite. It deliberately has no static-summary API: authoring checks consume `AuthoredNumericExpr` before lowering. -/
inductive LoweredNumericExpr (Atom : Type) where
  | atom (atom : Atom)
  | literal (value : Rat)
  | binary (op : NumericScaleBinaryOp)
      (left right : LoweredNumericExpr Atom)
  | power (base exponent : LoweredNumericExpr Atom)
  | round (mode : DecimalRoundingMode) (places : RoundingPlaces)
      (body : LoweredNumericExpr Atom)
  deriving Repr, DecidableEq

namespace AuthoredNumericExpr

/-- The narrow power-scale exception recognizes only an ungrouped, nonnegative numeric literal. Runtime exponent legality is checked separately. -/
def isSimpleNonnegativeConstant : AuthoredNumericExpr Atom → Bool
  | .literal decoded => decide (0 ≤ decoded.value)
  | _ => false

/-- Derive the static summary from the authored tree, propagating an illegal exponent as `none`. Grouping preserves the summary but remains visible to the power syntax classifier above. -/
def summary? (atomSummary : Atom → NumericScaleSummary) :
    AuthoredNumericExpr Atom → Option NumericScaleSummary
  | .atom sourceAtom => some (atomSummary sourceAtom)
  | .literal decoded => some (NumericScaleSummary.constant decoded.authoredScale)
  | .group body => body.summary? atomSummary
  | .binary op left right => do
      let leftSummary ← left.summary? atomSummary
      let rightSummary ← right.summary? atomSummary
      pure (NumericScaleSummary.binary op leftSummary rightSummary)
  | .power base exponent => do
      let baseSummary ← base.summary? atomSummary
      let exponentSummary ← exponent.summary? atomSummary
      NumericScaleSummary.power? baseSummary exponentSummary
        exponent.isSimpleNonnegativeConstant
  | .round _ places body => do
      let _ ← body.summary? atomSummary
      pure (NumericScaleSummary.rounded places.val)

end AuthoredNumericExpr

namespace LoweredNumericExpr

def rootDivision? : LoweredNumericExpr Atom →
    Option (LoweredNumericExpr Atom × LoweredNumericExpr Atom)
  | .binary .divide numerator denominator => some (numerator, denominator)
  | _ => none

/-- Apply the transformer’s one local multiplication step after both original children have been lowered. Ordinary factors keep their order and precede extracted numerators; newly constructed products are not revisited. -/
def lowerMultiply (left right : LoweredNumericExpr Atom) : LoweredNumericExpr Atom :=
  match left.rootDivision?, right.rootDivision? with
  | some (leftNumerator, leftDenominator),
      some (rightNumerator, rightDenominator) =>
      .binary .divide
        (.binary .multiply leftNumerator rightNumerator)
        (.binary .multiply leftDenominator rightDenominator)
  | some (numerator, denominator), none =>
      .binary .divide (.binary .multiply right numerator) denominator
  | none, some (numerator, denominator) =>
      .binary .divide (.binary .multiply left numerator) denominator
  | none, none => .binary .multiply left right

private def evalBinary (op : NumericScaleBinaryOp)
    (left right : NumericArithmeticResult) : NumericArithmeticResult :=
  match left, right with
  | .value leftValue, .value rightValue =>
      match op with
      | .add => .value (NumericArithmeticOp.add.eval leftValue rightValue)
      | .subtract => .value (NumericArithmeticOp.subtract.eval leftValue rightValue)
      | .multiply => .value (NumericArithmeticOp.multiply.eval leftValue rightValue)
      | .divide => divideNumeric leftValue rightValue
  | _, _ => .notEvaluated

/-- Evaluate only the admitted numeric-value fragment. A field reader or arithmetic child may return `notEvaluated`, which absorbs the enclosing expression. -/
def evalValue (read : Atom → NumericArithmeticResult) :
    LoweredNumericExpr Atom → NumericArithmeticResult
  | .atom sourceAtom => read sourceAtom
  | .literal amount => .value amount
  | .binary op left right =>
      evalBinary op (left.evalValue read) (right.evalValue read)
  | .power base exponent =>
      match base.evalValue read, exponent.evalValue read with
      | .value baseValue, .value exponentValue => powerNumeric baseValue exponentValue
      | _, _ => .notEvaluated
  | .round mode places body =>
      match body.evalValue read with
      | .value value => .value (roundDecimal mode value places)
      | .notEvaluated => .notEvaluated

end LoweredNumericExpr

namespace AuthoredNumericExpr

/-- Perform exactly one bottom-up lowering pass. Braces do not block a parent from recognizing a lowered root division; addition, subtraction, power, and rounding do. -/
def lowerForEvaluation : AuthoredNumericExpr Atom → LoweredNumericExpr Atom
  | .atom sourceAtom => .atom sourceAtom
  | .literal decoded => .literal decoded.value
  | .group body => body.lowerForEvaluation
  | .binary op left right =>
      let loweredLeft := left.lowerForEvaluation
      let loweredRight := right.lowerForEvaluation
      match op with
      | .multiply => LoweredNumericExpr.lowerMultiply loweredLeft loweredRight
      | .add => .binary .add loweredLeft loweredRight
      | .subtract => .binary .subtract loweredLeft loweredRight
      | .divide => .binary .divide loweredLeft loweredRight
  | .power base exponent =>
      .power base.lowerForEvaluation exponent.lowerForEvaluation
  | .round mode places body =>
      .round mode places body.lowerForEvaluation

/-- The executable meaning of an authored expression is evaluation of its one-pass lowered tree. -/
def evalValue (expression : AuthoredNumericExpr Atom)
    (read : Atom → NumericArithmeticResult) : NumericArithmeticResult :=
  expression.lowerForEvaluation.evalValue read

end AuthoredNumericExpr

end A12Kernel
