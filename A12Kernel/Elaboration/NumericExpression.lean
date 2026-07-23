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
  | abs (body : AuthoredNumericExpr Atom)
  | extremum (op : NumericExtremumOp)
      (left right : AuthoredNumericExpr Atom)
  | extremumCall (op : NumericExtremumOp)
      (body : AuthoredNumericExpr Atom)
  | round (mode : DecimalRoundingMode) (places : RoundingPlaces)
      (body : AuthoredNumericExpr Atom)
  deriving Repr, DecidableEq

/-- Runtime arithmetic tree after the source-ordered division rewrite. Each extrema call retains only its source-derived direct-constant result because ordinary lowering may change operand topology but cannot change that per-call authoring fact. -/
inductive LoweredNumericExpr (Atom : Type) where
  | atom (atom : Atom)
  | literal (value : Rat)
  | binary (op : NumericScaleBinaryOp)
      (left right : LoweredNumericExpr Atom)
  | power (base exponent : LoweredNumericExpr Atom)
  | abs (body : LoweredNumericExpr Atom)
  | extremum (op : NumericExtremumOp)
      (left right : LoweredNumericExpr Atom)
  | extremumCall (op : NumericExtremumOp) (constantUse : Option Bool)
      (body : LoweredNumericExpr Atom)
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

/-- Traverse every atom from left to right while preserving the authored expression shape and all syntax metadata. This is the shared path-resolution seam for checked validation and computation consumers. -/
def mapM {SourceAtom TargetAtom Error : Type}
    (resolve : SourceAtom → Except Error TargetAtom) :
    AuthoredNumericExpr SourceAtom → Except Error (AuthoredNumericExpr TargetAtom)
  | .atom sourceAtom => (resolve sourceAtom).map .atom
  | .literal decoded => pure (.literal decoded)
  | .group body => (body.mapM resolve).map .group
  | .binary op left right => do
      pure (.binary op (← left.mapM resolve) (← right.mapM resolve))
  | .power base exponent => do
      pure (.power (← base.mapM resolve) (← exponent.mapM resolve))
  | .abs body => (body.mapM resolve).map .abs
  | .extremum op left right => do
      pure (.extremum op (← left.mapM resolve) (← right.mapM resolve))
  | .extremumCall op body =>
      (body.mapM resolve).map (.extremumCall op)
  | .round mode places body =>
      (body.mapM resolve).map (.round mode places)

def hasAtom : AuthoredNumericExpr Atom → Bool
  | .atom _ => true
  | .literal _ => false
  | .group body => body.hasAtom
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.hasAtom || right.hasAtom
  | .abs body | .extremumCall _ body => body.hasAtom
  | .round _ _ body => body.hasAtom

/-- Check one predicate against every atom without erasing authored tree structure. -/
def allAtoms (predicate : Atom → Bool) : AuthoredNumericExpr Atom → Bool
  | .atom sourceAtom => predicate sourceAtom
  | .literal _ => true
  | .group body => body.allAtoms predicate
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.allAtoms predicate && right.allAtoms predicate
  | .abs body | .extremumCall _ body => body.allAtoms predicate
  | .round _ _ body => body.allAtoms predicate

def anyAtom (predicate : Atom → Bool) : AuthoredNumericExpr Atom → Bool
  | .atom sourceAtom => predicate sourceAtom
  | .literal _ => false
  | .group body => body.anyAtom predicate
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.anyAtom predicate || right.anyAtom predicate
  | .abs body | .extremumCall _ body => body.anyAtom predicate
  | .round _ _ body => body.anyAtom predicate

/-- Preserve one source-level nonempty numeric operand-list call. The explicit list boundary keeps the per-call constant budget distinct from a nested call. -/
def extremumList (op : NumericExtremumOp)
    (first : AuthoredNumericExpr Atom)
    (rest : List (AuthoredNumericExpr Atom)) : AuthoredNumericExpr Atom :=
  .extremumCall op
    (rest.foldl (fun result operand => .extremum op result operand) first)

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
  | .abs body => body.summary? atomSummary
  | .extremum _ left right => do
      let leftSummary ← left.summary? atomSummary
      let rightSummary ← right.summary? atomSummary
      pure (leftSummary.union rightSummary)
  | .extremumCall _ body => body.summary? atomSummary
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

private def authoringScan? (allowUnaryWrappers : Bool) :
    AuthoredNumericExpr Atom → Option AuthoringScan
  | .atom _ | .literal _ => some ⟨0, false, false⟩
  | .group body => do
      let bodyScan ← body.authoringScan? allowUnaryWrappers
      pure ⟨0, bodyScan.tooManyDivisions, bodyScan.directLeftNestedPower⟩
  | .binary op left right => do
      let leftScan ← left.authoringScan? allowUnaryWrappers
      let rightScan ← right.authoringScan? allowUnaryWrappers
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
      let baseScan ← base.authoringScan? allowUnaryWrappers
      let exponentScan ← exponent.authoringScan? allowUnaryWrappers
      pure ⟨0,
        baseScan.tooManyDivisions || exponentScan.tooManyDivisions,
        base.isDirectPower ||
          baseScan.directLeftNestedPower ||
          exponentScan.directLeftNestedPower⟩
  | .abs body | .round _ _ body =>
      if allowUnaryWrappers then body.authoringScan? true else none
  | .extremum _ left right =>
      if allowUnaryWrappers then do
        let leftScan ← left.authoringScan? true
        let rightScan ← right.authoringScan? true
        let exposed := leftScan.exposedDivisions + rightScan.exposedDivisions
        pure ⟨exposed,
          leftScan.tooManyDivisions || rightScan.tooManyDivisions ||
            decide (1 < exposed),
          leftScan.directLeftNestedPower || rightScan.directLeftNestedPower⟩
      else none
  | .extremumCall _ body =>
      if allowUnaryWrappers then body.authoringScan? true else none

private def authoringResult : Option AuthoringScan → NumericAuthoringCheck
  | some scan =>
      match scan.tooManyDivisions, scan.directLeftNestedPower with
      | false, false => .accepted
      | true, false => .tooManyDivisions
      | false, true => .directLeftNestedPower
      | true, true => .tooManyDivisionsAndDirectLeftNestedPower
  | none => .outsideFragment

/-- Check the exact plain arithmetic fragment: multiplication/division regions contain at most one division, and a power may not have an ungrouped power as its direct left operand. Addition, subtraction, power, and grouping reset the division contribution. Operation-valued wrappers fail closed because the kernel's legacy function traversal is not a compositional region rule. -/
def authoringCheck (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  authoringResult (expression.authoringScan? false)

/-- Whether an authored tree uses only atoms, literals, grouping, ordinary binary arithmetic, and power. -/
def isPlainArithmetic : AuthoredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .group body => body.isPlainArithmetic
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .extremumCall _ _ | .round _ _ _ => false

def hasUnaryValueFunction : AuthoredNumericExpr Atom → Bool
  | .atom _ | .literal _ => false
  | .group body => body.hasUnaryValueFunction
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.hasUnaryValueFunction || right.hasUnaryValueFunction
  | .extremumCall _ _ | .abs _ | .round _ _ _ => true

mutual

  /-- Complete numeric operations after source-level Min/Max calls have retained their call boundaries. The raw `extremum` constructor is only an internal list fold and is never admitted without its enclosing call marker. -/
  def isNumericOperation : AuthoredNumericExpr Atom → Bool
    | .atom _ | .literal _ => true
    | .group body => body.isNumericOperation
    | .binary _ left right | .power left right =>
        left.isNumericOperation && right.isNumericOperation
    | .abs body | .round _ _ body => body.isNumericOperation
    | .extremumCall op body => (body.extremumFoldConstantUse? op).isSome
    | .extremum _ _ _ => false

  /-- Classify one immediate Min/Max operand as a direct/grouped literal or a complete nonconstant numeric operation. -/
  private def extremumOperandConstant? :
      AuthoredNumericExpr Atom → Option Bool
    | .atom _ => some false
    | .literal _ => some true
    | .group body => body.extremumOperandConstant?
    | .binary _ left right | .power left right =>
        if left.isNumericOperation && right.isNumericOperation then
          some false
        else none
    | .abs body | .round _ _ body =>
        if body.isNumericOperation then some false else none
    | .extremumCall op body => do
        let _ ← body.extremumFoldConstantUse? op
        pure false
    | .extremum _ _ _ => none

  /-- Validate the left-associated internal fold of one authored Min/Max call and report whether that call—not any nested call—uses its single permitted immediate/grouped constant. -/
  private def extremumFoldConstantUse? (expected : NumericExtremumOp) :
      AuthoredNumericExpr Atom → Option Bool
    | .atom _ => some false
    | .literal _ => some true
    | .group body => body.extremumFoldConstantUse? expected
    | .binary _ left right | .power left right =>
        if left.isNumericOperation && right.isNumericOperation then
          some false
        else none
    | .abs body | .round _ _ body =>
        if body.isNumericOperation then some false else none
    | .extremum actual left right => do
        if actual != expected then none else
          let leftConstantUsed ← left.extremumFoldConstantUse? expected
          let rightIsConstant ← right.extremumOperandConstant?
          if leftConstantUsed && rightIsConstant then none
          else pure (leftConstantUsed || rightIsConstant)
    | .extremumCall op body => do
        let _ ← body.extremumFoldConstantUse? op
        pure false

end

/-- Recognize one authored numeric operand-list call and report whether that call—not its nested calls—uses its single permitted immediate/grouped constant. -/
def extremumCallConstantUse? (expected : NumericExtremumOp) :
    AuthoredNumericExpr Atom → Option Bool
  | .group body => body.extremumCallConstantUse? expected
  | .extremumCall actual body =>
      if actual != expected then none
      else body.extremumFoldConstantUse? expected
  | _ => none

/-- Recognize one complete Min/Max operand-list call whose arbitrary numeric operands satisfy the per-call immediate-constant budget. -/
def isExtremumCall : AuthoredNumericExpr Atom → Bool
  | expression@(.extremumCall op _) =>
      (expression.extremumCallConstantUse? op).isSome
  | .group body => body.isExtremumCall
  | _ => false

/-- The shared checked numeric-operation shape. Source-specific operand restrictions remain a separate gate. -/
def isAdmittedNumericOperation (expression : AuthoredNumericExpr Atom) : Bool :=
  expression.isNumericOperation

/-- Check the complete child of an operation-form rounding or absolute-value node, descending through every reached numeric value function. -/
def numericWrapperBodyAuthoringCheck
    (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  authoringResult (expression.authoringScan? true)

/-- Rounding and absolute-value operations delegate their static checks through nested value functions. Enclosing arithmetic follows the legacy walk through each reached value-function subtree: division contributions cross it, while each function node structurally separates an outer direct-left power relation. -/
def numericOperationAuthoringCheck
    (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  match expression with
  | .round _ _ body | .abs body => body.numericWrapperBodyAuthoringCheck
  | _ =>
      if expression.isExtremumCall then
        .accepted
      else if expression.hasUnaryValueFunction then
        authoringResult (expression.authoringScan? true)
      else
        expression.authoringCheck

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
  | .abs body => (body.evalValue read).absolute
  | .extremum op left right =>
      op.selectArithmeticResult (left.evalValue read) (right.evalValue read)
  | .extremumCall _ _ body => body.evalValue read
  | .round mode places body =>
      (body.evalValue read).round mode places

end LoweredNumericExpr

namespace AuthoredNumericExpr

/-- Perform exactly one bottom-up lowering pass. Braces do not block a parent from recognizing a lowered root division; addition, subtraction, power, absolute value, operand-list extrema, and rounding do. -/
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
  | .abs body => .abs body.lowerForEvaluation
  | .extremum op left right =>
      .extremum op left.lowerForEvaluation right.lowerForEvaluation
  | .extremumCall op body =>
      .extremumCall op
        ((AuthoredNumericExpr.extremumCall op body).extremumCallConstantUse? op)
        body.lowerForEvaluation
  | .round mode places body =>
      .round mode places body.lowerForEvaluation

/-- The executable meaning of an authored expression is evaluation of its one-pass lowered tree. -/
def evalValue (expression : AuthoredNumericExpr Atom)
    (read : Atom → NumericArithmeticResult) : NumericArithmeticResult :=
  expression.lowerForEvaluation.evalValue read

end AuthoredNumericExpr

end A12Kernel
