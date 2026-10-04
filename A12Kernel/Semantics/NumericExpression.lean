import A12Kernel.Document
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.NumericLiteral
import A12Kernel.Semantics.NumericArithmetic
import A12Kernel.Semantics.NumericTolerance
import A12Kernel.Semantics.NumericComputationResult

/-! # Shared numeric expressions and phase-specific evaluation

Authored scale and syntax, one-pass arithmetic lowering, and atom-parametric comparisons belong to
one semantic owner. Validation retains fillability and unavailability; computation retains ordered
poison and arithmetic domain failure. Model and path admission remain with the checked consumers.
-/

namespace A12Kernel

/-- A row-bound structural operand retains its complete ancestry separately from its own coordinate:
    a fixed descendant requires ancestor bindings but returns one (`spec/08` §4). -/
structure BoundCurrentRepetitionSource where
  path : List String
  scope : List RepeatableLevel
  level : Option RepeatableLevel
  deriving Repr, DecidableEq

/-- Check every required binding before selecting the group's own coordinate. A present terminal
    coordinate cannot compensate for a missing, duplicated, or zero ancestor binding. -/
def BoundCurrentRepetitionSource.coordinateAt (source : BoundCurrentRepetitionSource)
    (environment : Env) : Except EnvBindingError Nat := do
  let _ ← environment.pathForScope source.scope
  match source.level with
  | none => pure 1
  | some level => environment.bindingAt level


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

/-- The single exact-scale warning directive admits an otherwise rejected pair without changing either scale summary. Validation equality/inequality and computed-target assignment share this gate. -/
def exactNumericScaleComparisonAllowedWithSuppression
    (suppressExactScaleWarning : Bool)
    (left right : NumericScaleSummary) : Bool :=
  suppressExactScaleWarning || exactNumericScaleComparisonAllowed left right

/-- Ordering is scale-exempt; unsuppressed equality and inequality use the exact authored-scale gate. This dispatch is shared by checked expression comparison and the polymorphic numeric Base Year constant. -/
def NumericComparisonOp.acceptsScales (op : NumericComparisonOp)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .equal | .notEqual => exactNumericScaleComparisonAllowed left right
  | .less | .lessEqual | .greater | .greaterEqual => true

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

/-- Transform every atom while preserving the complete authored expression shape and syntax metadata. -/
def map (transform : SourceAtom → TargetAtom) :
    AuthoredNumericExpr SourceAtom → AuthoredNumericExpr TargetAtom
  | .atom sourceAtom => .atom (transform sourceAtom)
  | .literal decoded => .literal decoded
  | .group body => .group (body.map transform)
  | .binary op left right =>
      .binary op (left.map transform) (right.map transform)
  | .power base exponent =>
      .power (base.map transform) (exponent.map transform)
  | .abs body => .abs (body.map transform)
  | .extremum op left right =>
      .extremum op (left.map transform) (right.map transform)
  | .extremumCall op body => .extremumCall op (body.map transform)
  | .round mode places body =>
      .round mode places (body.map transform)

/-- Retain the strict subterm bound when numeric atoms recursively contain another expression family.
Elaboration and evaluation use the same traversal without fuel or an opaque recursive callback. -/
@[simp]
def mapMSubterm [SizeOf A] (expression : AuthoredNumericExpr A)
    (resolve : (atom : A) → sizeOf atom < sizeOf expression → Except E B) :
    Except E (AuthoredNumericExpr B) :=
  match expression with
  | .atom sourceAtom => (resolve sourceAtom (by simp)).map .atom
  | .literal decoded => pure (.literal decoded)
  | .group body => (mapMSubterm body (fun atom h => resolve atom (by simp_all; omega))).map .group
  | .abs body => (mapMSubterm body (fun atom h => resolve atom (by simp_all; omega))).map .abs
  | .extremumCall op body =>
      (mapMSubterm body (fun atom h => resolve atom (by simp_all; omega))).map (.extremumCall op)
  | .round mode places body =>
      (mapMSubterm body (fun atom h => resolve atom (by simp_all; omega))).map (.round mode places)
  | .binary op left right => do
      pure (.binary op (← mapMSubterm left (fun atom h => resolve atom (by simp_all; omega)))
        (← mapMSubterm right (fun atom h => resolve atom (by simp_all; omega))))
  | .power left right => do
      pure (.power (← mapMSubterm left (fun atom h => resolve atom (by simp_all; omega)))
        (← mapMSubterm right (fun atom h => resolve atom (by simp_all; omega))))
  | .extremum op left right => do
      pure (.extremum op (← mapMSubterm left (fun atom h => resolve atom (by simp_all; omega)))
        (← mapMSubterm right (fun atom h => resolve atom (by simp_all; omega))))

/-- Traverse every atom from left to right while preserving the authored expression shape and all syntax metadata. This is the shared path-resolution seam for checked validation and computation consumers. -/
def mapM {SourceAtom TargetAtom Error : Type}
    (resolve : SourceAtom → Except Error TargetAtom)
    (expression : AuthoredNumericExpr SourceAtom) : Except Error (AuthoredNumericExpr TargetAtom) :=
  expression.mapMSubterm (fun source _ => resolve source)

/-- Numeric sources in authored occurrence order, without deduplication or loss of repeated reads. -/
def atoms : AuthoredNumericExpr Atom → List Atom
  | .atom source => [source]
  | .literal _ => []
  | .group body | .abs body | .extremumCall _ body | .round _ _ body => body.atoms
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.atoms ++ right.atoms

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

/-- Whether this side is an **immediate** written-out value rather than an expression. The
    comparison's constant gate reads exactly this and nothing else: two immediate literals are
    refused while `1 + 2 > 0` and `1 > 1 + 2` are admitted, so a literal under any operation stops
    being immediate. A signed literal is still one literal. The parenthesised form does not reach
    this gate — the Kernel's parser refuses it at that site — so classifying `.group` as an
    expression is unobservable rather than a claim. -/
def isImmediateLiteral : AuthoredNumericExpr Atom → Bool
  | .literal _ => true
  | .atom _ | .group _ | .binary _ _ _ | .power _ _ | .extremum _ _ _
  | .abs _ | .extremumCall _ _ | .round _ _ _ => false

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

/-- Whether a subtree holds a node satisfying `predicate`, the node itself included. -/
def anyNode (predicate : AuthoredNumericExpr Atom → Bool) :
    AuthoredNumericExpr Atom → Bool
  | expression@(.atom _) | expression@(.literal _) => predicate expression
  | expression@(.group body) | expression@(.abs body) | expression@(.extremumCall _ body)
  | expression@(.round _ _ body) => predicate expression || body.anyNode predicate
  | expression@(.binary _ left right) | expression@(.power left right)
  | expression@(.extremum _ left right) =>
      predicate expression || left.anyNode predicate || right.anyNode predicate

/-- What one division walk over a subtree found: a second division, an end of the walk, or neither
yet, with whether a division was seen. -/
inductive DivisionWalk where
  | violation
  | stopped
  | open (seen : Bool)
  deriving Repr, DecidableEq

/-- A construct walked afresh keeps a violation it found and otherwise ends the enclosing walk. -/
private def DivisionWalk.close : DivisionWalk → DivisionWalk
  | .violation => .violation
  | .stopped | .open _ => .stopped

/-- The Kernel's division walk over one subtree, in pre-order, carrying whether a division was seen.
A division seen twice is a violation. The walk passes through `Abs`, rounding and every operand of a
`Max` or `Min` call, so their operands share the enclosing walk. A brace, an addition or subtraction, and
a power are each walked afresh, operand by operand, and then end the whole walk, so whatever the walk
had not reached yet is never counted
([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-division-walk)):
`[a] / Max({[b]}, [b] / [a])` passes while `[a] / Max([b] / [a], {[b]})` does not. -/
def divisionWalk (seen : Bool) : AuthoredNumericExpr Atom → DivisionWalk
  | .atom _ | .literal _ => .open seen
  | .group body => (body.divisionWalk false).close
  | .binary .add left right | .binary .subtract left right | .power left right =>
      match left.divisionWalk false with
      | .open _ => (right.divisionWalk false).close
      | found => found.close
  | .binary op left right =>
      let division := op == .divide
      if division && seen then .violation
      else
        match left.divisionWalk (seen || division) with
        | .open seenAfter => right.divisionWalk seenAfter
        | found => found
  | .abs body | .round _ _ body | .extremumCall _ body => body.divisionWalk seen
  | .extremum _ left right =>
      match left.divisionWalk seen with
      | .open seenAfter => right.divisionWalk seenAfter
      | found => found

/-- Whether the Kernel's division check refuses at this node. It runs at every arithmetic operator and
power as that node closes, walking the node's own subtree, and at no other node: a call, a wrapper or a
brace is never itself checked, so `Max([a] / [b], [b] / [a])` passes at the root while
`[a] + Max([a] / [b], [b] / [a])` does not. -/
def divisionGateRefuses : AuthoredNumericExpr Atom → Bool
  | expression@(.binary _ _ _) | expression@(.power _ _) =>
      expression.divisionWalk false == .violation
  | _ => false

/-- Whether this node is a power directly on the left of a power, which the Kernel refuses at every
power node wherever it stands; a brace around the inner power separates them. -/
def directLeftNestedPowerAt : AuthoredNumericExpr Atom → Bool
  | .power (.power _ _) _ => true
  | _ => false

/-- The two gates' verdicts over every node of one tree. -/
def authoringResult (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  match expression.anyNode divisionGateRefuses, expression.anyNode directLeftNestedPowerAt with
  | false, false => .accepted
  | true, false => .tooManyDivisions
  | false, true => .directLeftNestedPower
  | true, true => .tooManyDivisionsAndDirectLeftNestedPower

/-- Whether an authored tree uses only atoms, literals, grouping, ordinary binary arithmetic, and power. -/
def isPlainArithmetic : AuthoredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .group body => body.isPlainArithmetic
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .extremumCall _ _ | .round _ _ _ => false

/-- Check the plain arithmetic fragment by the Kernel's division and power gates. Inside it the walk is
the compositional region rule: addition, subtraction, power and grouping close a region, and a
multiplication or division region holds at most one division. An operation-valued wrapper is outside
this fragment; `numericOperationAuthoringCheck` owns it. -/
def authoringCheck (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  if expression.isPlainArithmetic then authoringResult expression else .outsideFragment

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

/-- Check one complete operation by the Kernel's division and power gates at every node it checks,
the nodes inside a value function's operands included. A root call, wrapper or brace is no checked node
itself, so a value function at the root leaves its operands to their own checks, while one under an
operator shares that operator's division walk
([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-division-walk)). -/
def numericOperationAuthoringCheck
    (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  authoringResult expression

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

/-- Resolved runtime representation parameterized only at the checked numeric-source boundary. -/
structure NumericComparisonOf (Atom : Type) where
  op : NumericValidationOp
  left : AuthoredNumericExpr Atom
  right : AuthoredNumericExpr Atom
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

/-- Tolerance deliberately bypasses the ordinary exact-comparison scale gate. -/
def NumericValidationOp.acceptsScales (op : NumericValidationOp)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .ordinary comparison => comparison.acceptsScales left right
  | .tolerance _ => true

/-- The one legal parser warning suppression bypasses only the exact-comparison scale gate. Every other authoring check remains independent. -/
def NumericValidationOp.acceptsScalesWithSuppression
    (op : NumericValidationOp) (suppressExactScaleWarning : Bool)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .ordinary .equal | .ordinary .notEqual =>
      exactNumericScaleComparisonAllowedWithSuppression
        suppressExactScaleWarning left right
  | .ordinary .less | .ordinary .lessEqual
  | .ordinary .greater | .ordinary .greaterEqual
  | .tolerance _ => true

def combineNumericValidationOutcomes
    (combine : NumericArithmeticOutcome → NumericArithmeticOutcome →
      NumericArithmeticOutcome)
    (left right : Except Error NumericArithmeticOutcome) :
    Except Error NumericArithmeticOutcome :=
  match left, right with
  | .error cause, _ => .error cause
  | _, .error cause => .error cause
  | .ok leftOutcome, .ok rightOutcome => .ok (combine leftOutcome rightOutcome)

def evalPlainBinary (op : NumericScaleBinaryOp)
    (left right : Except Error NumericArithmeticOutcome) :
    Except Error NumericArithmeticOutcome :=
  combineNumericValidationOutcomes
    (fun leftOutcome rightOutcome =>
      match op with
        | .add => NumericArithmeticOutcome.eval .add leftOutcome rightOutcome
        | .subtract => NumericArithmeticOutcome.eval .subtract leftOutcome rightOutcome
        | .multiply => NumericArithmeticOutcome.eval .multiply leftOutcome rightOutcome
        | .divide => NumericArithmeticOutcome.divide leftOutcome rightOutcome)
    left right

/-- Whether a lowered tree lies in the consumer's binary-arithmetic runtime subset. -/
def LoweredNumericExpr.isPlainArithmetic : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .extremumCall _ _ _ | .round _ _ _ => false

/-- Runtime-shape mirror of one authored extremum call, including its independent per-call constant budget. -/
def LoweredNumericExpr.extremumCallConstantUse?
    (expected : NumericExtremumOp) :
    LoweredNumericExpr Atom → Option Bool
  | .extremumCall actual constantUse _ =>
      if actual != expected then none else constantUse
  | _ => none

/-- Read the source-derived admission certificate retained across lowering. -/
def LoweredNumericExpr.isExtremumCall : LoweredNumericExpr Atom → Bool
  | .extremumCall _ constantUse _ => constantUse.isSome
  | _ => false

/-- Runtime-capable numeric-operation shape after grouping erasure. -/
def LoweredNumericExpr.isNumericOperation : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right | .power left right =>
      left.isNumericOperation && right.isNumericOperation
  | .abs body | .round _ _ body => body.isNumericOperation
  | expression@(.extremumCall _ _ _) => expression.isExtremumCall
  | .extremum _ _ _ => false

def LoweredNumericExpr.isAdmittedValidation (expression : LoweredNumericExpr Atom) :
    Bool :=
  expression.isNumericOperation

/-- Preserve the first formal cause across exact extremum selection of two reached validation outcomes. -/
def NumericExtremumOp.selectValidationOutcome (op : NumericExtremumOp) :
    Except Error NumericArithmeticOutcome →
      Except Error NumericArithmeticOutcome →
        Except Error NumericArithmeticOutcome
  | left, right =>
      combineNumericValidationOutcomes op.selectOutcome left right

def LoweredNumericExpr.evalNumericOperationTree
    (read : Atom → Except Error NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Except Error NumericArithmeticOutcome
  | .atom sourceAtom => read sourceAtom
  | .literal amount => .ok (.value amount .fixed)
  | .binary op left right =>
      evalPlainBinary op
        (left.evalNumericOperationTree read)
        (right.evalNumericOperationTree read)
  | .power base exponent =>
      combineNumericValidationOutcomes NumericArithmeticOutcome.power
        (base.evalNumericOperationTree read)
        (exponent.evalNumericOperationTree read)
  | .abs body =>
      match body.evalNumericOperationTree read with
      | .ok outcome => .ok outcome.absolute
      | .error cause => .error cause
  | .extremum op left right =>
      op.selectValidationOutcome
        (left.evalNumericOperationTree read)
        (right.evalNumericOperationTree read)
  | .extremumCall _ _ body => body.evalNumericOperationTree read
  | .round mode places body =>
      match body.evalNumericOperationTree read with
      | .ok outcome => .ok (outcome.round mode places)
      | .error cause => .error cause

/-- Evaluate one complete numeric operation after checking its lowered admission certificate. -/
def LoweredNumericExpr.evalNumericOperation?
    (read : Atom → Except Error NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except Error NumericArithmeticOutcome) :=
  if expression.isNumericOperation then
    some (expression.evalNumericOperationTree read)
  else
    none

/-- Evaluate exactly the checked runtime fragment. Value functions compose recursively with arithmetic while formal invalidity and arithmetic domain failure remain distinct. -/
def LoweredNumericExpr.evalAdmittedValidation?
    (read : Atom → Except Error NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except Error NumericArithmeticOutcome) :=
  expression.evalNumericOperation? read

/-- Evaluate a raw core through one supplied numeric-source resolver. The unknown fallback fails closed for a forged unsupported operand and is unreachable through every checked specialization. -/
def NumericComparisonOf.evalWith
    (comparison : NumericComparisonOf Atom)
    (resolve :
      Atom →
        Except Error NumericArithmeticOutcome) : Verdict :=
  match
      comparison.left.lowerForEvaluation.evalAdmittedValidation?
        resolve,
      comparison.right.lowerForEvaluation.evalAdmittedValidation?
        resolve with
  | some left, some right => comparison.op.evalArithmeticWith left right
  | _, _ => .unknown

namespace NumericComputationResult

/-- Combine two already-reached arithmetic operands through the shared poison/domain/value table. -/
def evalBinary (op : NumericScaleBinaryOp) :
    NumericComputationResult → NumericComputationResult → NumericComputationResult
  | left, right =>
      NumericComputationResult.combineReached
        (fun leftValue rightValue => ofArithmetic (op.evalValues leftValue rightValue))
        left right

/-- Evaluate an ordered pair once. A left poison prevents the right computation from being reached; a value or domain failure reaches it and delegates the final result to the supplied semantic combiner. -/
def evalOrdered {Fault : Type}
    (left : Except Fault NumericComputationResult)
    (right : Unit → Except Fault NumericComputationResult)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult) :
    Except Fault NumericComputationResult := do
  let leftResult ← left
  match leftResult with
  | .poison cause => pure (.poison cause)
  | .value _ | .domainFailure =>
      pure (combine leftResult (← right ()))

end NumericComputationResult

namespace LoweredNumericExpr

/-- Evaluate the admitted computation fragment left-to-right. A reached poison aborts the remaining expression; arithmetic domain failure remains a value-level result and propagates through later arithmetic, including runtime-invalid power. -/
def evalComputation {Fault : Type}
    (read : Atom → Except Fault NumericComputationResult) :
    LoweredNumericExpr Atom →
      Except Fault NumericComputationResult
  | .atom sourceAtom => read sourceAtom
  | .literal amount => pure (.value amount)
  | .binary op left right =>
      NumericComputationResult.evalOrdered
        (left.evalComputation read) (fun _ => right.evalComputation read)
        (NumericComputationResult.evalBinary op)
  | .power base exponent =>
      NumericComputationResult.evalOrdered
        (base.evalComputation read) (fun _ => exponent.evalComputation read)
        NumericComputationResult.evalPower
  | .abs body => do
      pure ((← body.evalComputation read).absolute)
  | .extremum op left right =>
      NumericComputationResult.evalOrdered
        (left.evalComputation read) (fun _ => right.evalComputation read)
        op.selectComputationResult
  | .extremumCall _ _ body => body.evalComputation read
  | .round mode places body => do
      pure ((← body.evalComputation read).round mode places)

end LoweredNumericExpr

/-- The wrapper checker rejects only an immediate numeric literal or its grouped form. Semantically fixed sources such as numeric `BaseYear` remain distinct syntax and are admitted. -/
def AuthoredNumericExpr.isImmediateResolvedNumericLiteral :
    AuthoredNumericExpr Atom → Bool
  | .literal _ => true
  | .group body => body.isImmediateResolvedNumericLiteral
  | _ => false

/-- Check the source-specific immediate-literal prohibition at every rounding/absolute-value boundary while traversing the complete numeric operation tree, including operand-list calls and their normalized folds. -/
def AuthoredNumericExpr.respectsResolvedWrapperLiteralBoundary :
    AuthoredNumericExpr Atom → Bool
  | .round _ _ body | .abs body =>
      !body.isImmediateResolvedNumericLiteral &&
        body.respectsResolvedWrapperLiteralBoundary
  | .atom _ | .literal _ => true
  | .group body => body.respectsResolvedWrapperLiteralBoundary
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.respectsResolvedWrapperLiteralBoundary &&
        right.respectsResolvedWrapperLiteralBoundary
  | .extremumCall _ body => body.respectsResolvedWrapperLiteralBoundary

/-- A resolved numeric operation must satisfy the shared authored shape and the source-specific wrapper boundary at every depth. -/
def AuthoredNumericExpr.isAdmittedResolvedNumericOperation
    (expression : AuthoredNumericExpr Atom) : Bool :=
  expression.isAdmittedNumericOperation &&
    expression.respectsResolvedWrapperLiteralBoundary

/-- Shared comparison admission, parameterized only by each carrier's atom certificate and scale. -/
def NumericComparisonOf.admittedWith (comparison : NumericComparisonOf Atom)
    (admitted : Atom → Bool) (summary : Atom → NumericScaleSummary) : Bool :=
  !(comparison.left.isImmediateLiteral && comparison.right.isImmediateLiteral) &&
    comparison.left.isAdmittedResolvedNumericOperation &&
    comparison.right.isAdmittedResolvedNumericOperation &&
    comparison.left.allAtoms admitted && comparison.right.allAtoms admitted &&
    comparison.left.numericOperationAuthoringCheck == .accepted &&
    comparison.right.numericOperationAuthoringCheck == .accepted &&
    match comparison.left.summary? summary, comparison.right.summary? summary with
    | some left, some right => comparison.op.acceptsScalesWithSuppression
        comparison.suppressExactScaleWarning left right
    | _, _ => false

/-- Compare complete numeric expressions in computation order. A reached poison stops the
right side; arithmetic domain failure still reaches it and otherwise supplies clean non-holding. -/
def NumericComparisonOf.evalComputationWith (comparison : NumericComparisonOf Atom)
    (read : Atom → Except Error NumericComputationResult) :
    Except Error ComputationConditionResult := do
  let left ← comparison.left.lowerForEvaluation.evalComputation read
  match left with
  | .poison cause => pure (.poison cause)
  | _ =>
      let right ← comparison.right.lowerForEvaluation.evalComputation read
      match left, right with
      | _, .poison cause => pure (.poison cause)
      | .value left, .value right =>
          pure (match comparison.op.eval (.value left .fixed) (.value right .fixed) with
            | .fired _ => .holds
            | _ => .notTrue)
      | _, _ => pure .notTrue

end A12Kernel
