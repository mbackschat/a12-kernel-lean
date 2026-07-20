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

/-- Result of the plain-arithmetic authoring check. `outsideFragment` makes no kernel-legality judgment about operation-valued wrappers. -/
inductive NumericAuthoringCheck where
  | accepted
  | tooManyDivisions
  | directLeftNestedPower
  | tooManyDivisionsAndDirectLeftNestedPower
  | outsideFragment
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

private def isDirectPower : AuthoredNumericExpr Atom → Bool
  | .power _ _ => true
  | _ => false

private structure AuthoringScan where
  exposedDivisions : Nat
  tooManyDivisions : Bool
  directLeftNestedPower : Bool

private def authoringScan? : AuthoredNumericExpr Atom → Option AuthoringScan
  | .atom _ | .literal _ => some ⟨0, false, false⟩
  | .group body => do
      let bodyScan ← body.authoringScan?
      pure ⟨0, bodyScan.tooManyDivisions, bodyScan.directLeftNestedPower⟩
  | .binary op left right => do
      let leftScan ← left.authoringScan?
      let rightScan ← right.authoringScan?
      let divisionViolation :=
        leftScan.tooManyDivisions || rightScan.tooManyDivisions
      let powerViolation :=
        leftScan.directLeftNestedPower || rightScan.directLeftNestedPower
      match op with
      | .add | .subtract => pure ⟨0, divisionViolation, powerViolation⟩
      | .multiply | .divide =>
          let ownDivision := if op = .divide then 1 else 0
          let exposed :=
            leftScan.exposedDivisions + rightScan.exposedDivisions + ownDivision
          pure ⟨exposed, divisionViolation || decide (1 < exposed), powerViolation⟩
  | .power base exponent => do
      let baseScan ← base.authoringScan?
      let exponentScan ← exponent.authoringScan?
      pure ⟨0,
        baseScan.tooManyDivisions || exponentScan.tooManyDivisions,
        base.isDirectPower ||
          baseScan.directLeftNestedPower ||
          exponentScan.directLeftNestedPower⟩
  | .round _ _ _ => none

/-- Check the exact plain arithmetic fragment: multiplication/division regions contain at most one division, and a power may not have an ungrouped power as its direct left operand. Addition, subtraction, power, and grouping reset the division contribution. Any rounding wrapper fails closed because the kernel's legacy function traversal is not a compositional region rule. -/
def authoringCheck (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  match expression.authoringScan? with
  | some scan =>
      match scan.tooManyDivisions, scan.directLeftNestedPower with
      | false, false => .accepted
      | true, false => .tooManyDivisions
      | false, true => .directLeftNestedPower
      | true, true => .tooManyDivisionsAndDirectLeftNestedPower
  | none => .outsideFragment

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

end LoweredNumericExpr

namespace NumericScaleBinaryOp

/-- Evaluate one binary numeric node over two known values. Consumer-specific failure and metadata propagation stay outside this shared primitive dispatch. -/
def evalValues (op : NumericScaleBinaryOp) (left right : Rat) :
    NumericArithmeticResult :=
  match op with
  | .add => .value (NumericArithmeticOp.add.eval left right)
  | .subtract => .value (NumericArithmeticOp.subtract.eval left right)
  | .multiply => .value (NumericArithmeticOp.multiply.eval left right)
  | .divide => divideNumeric left right

end NumericScaleBinaryOp

namespace LoweredNumericExpr

private def evalBinary (op : NumericScaleBinaryOp)
    (left right : NumericArithmeticResult) : NumericArithmeticResult :=
  match left, right with
  | .value leftValue, .value rightValue => op.evalValues leftValue rightValue
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
      (body.evalValue read).round mode places

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
