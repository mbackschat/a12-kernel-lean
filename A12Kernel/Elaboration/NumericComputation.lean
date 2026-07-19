import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.NumericComputationResult

/-! # Numeric computation-expression outcomes

This capsule evaluates one already-resolved numeric expression before target checking. It preserves ordinary values, arithmetic domain failure, and inherited computation-read poison as three distinct results. The input is not a claim about concrete syntax or general operation-wrapper authoring legality. Target policy, rendered storage, application, delta projection, selection, and scheduling remain outside this module.
-/

namespace A12Kernel

/-- Fail-closed faults outside the admitted numeric computation-expression fragment. -/
inductive NumericComputationFault where
  | fieldKindMismatch (field : FieldId)
  | unsupportedPower
  deriving Repr, DecidableEq

namespace ScalarComputationContext

/-- Read one already-resolved declaration in computation phase. A non-Number declaration is a structural fault even when its cell is empty; required-only Number emptiness remains zero and ordinary formal invalidity remains poison. -/
def readNumeric (context : ScalarComputationContext) (declaration : FlatFieldDecl) :
    Except NumericComputationFault NumericComputationResult :=
  match declaration.toNumberField? with
  | none => throw (.fieldKindMismatch declaration.id)
  | some field =>
      match observeCell .computation (context.read field.id) with
      | .empty => pure (.value 0)
      | .value (.num amount) => pure (.value amount)
      | .value _ => throw (.fieldKindMismatch field.id)
      | .unknown cause | .poison cause => pure (.poison cause)

end ScalarComputationContext

namespace NumericComputationResult

private def ofArithmetic : NumericArithmeticResult → NumericComputationResult
  | .value amount => .value amount
  | .notEvaluated => .domainFailure

/-- Combine two already-evaluated computation operands. The caller enforces read order; this total table prefers a left poison, then a right poison, then arithmetic domain failure. -/
def evalBinary (op : NumericScaleBinaryOp) :
    NumericComputationResult → NumericComputationResult → NumericComputationResult
  | .poison cause, _ => .poison cause
  | _, .poison cause => .poison cause
  | .domainFailure, _ => .domainFailure
  | _, .domainFailure => .domainFailure
  | .value left, .value right => ofArithmetic (op.evalValues left right)

end NumericComputationResult

namespace LoweredNumericExpr

/-- The first structural fault in the complete lowered tree. This pass runs before any context read, so a non-Number declaration or unsupported power cannot be hidden by data-dependent poison. -/
def computationFault? : LoweredNumericExpr FlatFieldDecl →
    Option NumericComputationFault
  | .atom declaration =>
      if declaration.toNumberField?.isSome then
        none
      else
        some (.fieldKindMismatch declaration.id)
  | .literal _ => none
  | .binary _ left right =>
      match left.computationFault? with
      | some fault => some fault
      | none => right.computationFault?
  | .power _ _ => some .unsupportedPower
  | .round _ _ body => body.computationFault?

/-- Evaluate the admitted computation fragment left-to-right. A reached poison aborts the remaining expression; arithmetic domain failure remains a value-level result and propagates through later arithmetic. Power fails closed because its computation projection is not yet audited. -/
def evalComputation
    (read : Atom → Except NumericComputationFault NumericComputationResult) :
    LoweredNumericExpr Atom →
      Except NumericComputationFault NumericComputationResult
  | .atom sourceAtom => read sourceAtom
  | .literal amount => pure (.value amount)
  | .binary op left right => do
      let leftResult ← left.evalComputation read
      match leftResult with
      | .poison cause => pure (.poison cause)
      | .value _ | .domainFailure =>
          let rightResult ← right.evalComputation read
          pure (NumericComputationResult.evalBinary op leftResult rightResult)
  | .power _ _ => throw .unsupportedPower
  | .round mode places body => do
      match ← body.evalComputation read with
      | .value amount => pure (.value (roundDecimal mode amount places))
      | .domainFailure => pure .domainFailure
      | .poison cause => pure (.poison cause)

end LoweredNumericExpr

namespace AuthoredNumericExpr

/-- Lower exactly once, then evaluate one already-resolved numeric computation expression against the common checked computation context. -/
def evaluateComputation (expression : AuthoredNumericExpr FlatFieldDecl)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  let lowered := expression.lowerForEvaluation
  match lowered.computationFault? with
  | some fault => .error fault
  | none => lowered.evalComputation context.readNumeric

end AuthoredNumericExpr

end A12Kernel
