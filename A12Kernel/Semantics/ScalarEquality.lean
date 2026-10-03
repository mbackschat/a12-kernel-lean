import A12Kernel.Cell
import A12Kernel.Semantics.Condition

/-! # Shared scalar equality and inequality

This module owns classified scalar comparison shared by validation, Enumeration projection and computation guards. Validation retains VALUE/OMISSION polarity; computation retains ordered poison and runtime failure. Consuming clauses remain responsible for typed reads and their empty substitution or not-evaluated rule.
-/

namespace A12Kernel

/-- Equality and inequality are separate surface operators; there is no generic condition negation in the language. -/
inductive EqualityOp where
  | equal
  | notEqual
  deriving Repr, DecidableEq

/-- Comparison-local classification for nonnumeric clauses whose substitution polarity is symmetric. Numeric operands use directional fillability instead. -/
inductive SimpleComparisonOperand (α : Type) where
  | value (value : α) (given : Bool)
  | notEvaluated
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

namespace CellObservation

/-- Classify a typed validation observation for a comparison whose empty rule is “not evaluated” and whose present direct value is fixed. A computation-only poison is preserved defensively as formal unavailability. -/
def asValidationSimpleOperand (observation : CellObservation α) :
    SimpleComparisonOperand α :=
  match observation with
  | @A12Kernel.CellObservation.empty _ => .notEvaluated
  | @A12Kernel.CellObservation.value _ observed => .value observed true
  | @A12Kernel.CellObservation.unknown _ cause => .unknown cause
  | @A12Kernel.CellObservation.poison _ cause => .unknown cause

end CellObservation

/-- Evaluate two classified scalar operands with symmetric missing polarity. Formal unavailability dominates no value; a true comparison is omission-typed exactly when either present operand retains missing provenance. -/
def evalSymmetricComparison (holds : α → α → Bool)
    (leftOperand rightOperand : SimpleComparisonOperand α) : Verdict :=
  match leftOperand, rightOperand with
  | .unknown _, _ | _, .unknown _ => .unknown
  | .notEvaluated, _ | _, .notEvaluated => .notFired
  | .value left leftGiven, .value right rightGiven =>
      if holds left right then
        if leftGiven && rightGiven then .fired .value else .fired .omission
      else
        .notFired

/-- Computation comparisons preserve reached poison before empty suppression; missing provenance
only affects validation polarity (spec/02 §A.3 and the comparison-guard grid, 2026-10-04). -/
def evalComputationComparison (holds : α → α → Bool)
    (left right : SimpleComparisonOperand α) : ComputationConditionResult :=
  match left, right with
  | .unknown cause, _ | _, .unknown cause => .poison cause
  | .notEvaluated, _ | _, .notEvaluated => .notTrue
  | .value left _, .value right _ => if holds left right then .holds else .notTrue

/-- Read in authored order. A reached left poison aborts before a right runtime failure; an empty
left still reaches the right. The caller retains runtime failure separately from operand poison
(comparison-guard grid, 2026-10-04). -/
def evalComputationComparisonExcept (holds : α → α → Bool)
    (left : Except Error (SimpleComparisonOperand α))
    (right : Unit → Except Error (SimpleComparisonOperand α)) :
    Except Error ComputationConditionResult := do
  let left ← left
  match left with
  | .unknown cause => pure (.poison cause)
  | _ => pure (evalComputationComparison holds left (← right ()))

/-- The other equality operator, the complement rule negation uses. -/
def EqualityOp.complement : EqualityOp → EqualityOp
  | .equal => .notEqual
  | .notEqual => .equal

def EqualityOp.holds (op : EqualityOp) (equivalent : Bool) : Bool :=
  match op with
  | .equal => equivalent
  | .notEqual => !equivalent

/-- Evaluate exact equality or inequality after the consuming clause has classified empty and unavailable input. -/
def EqualityOp.evalSimple (op : EqualityOp) (equivalent : α → α → Bool)
    (operand : SimpleComparisonOperand α) (expected : α) : Verdict :=
  match operand with
  | .notEvaluated => .notFired
  | .unknown _ => .unknown
  | .value actual given =>
      if op.holds (equivalent actual expected) then
        if given then .fired .value else .fired .omission
      else
        .notFired

/-- Evaluate equality or inequality between two already-classified operands. Formal unavailability and no-value suppression remain owned by the shared symmetric comparison. -/
def EqualityOp.evalSymmetric (op : EqualityOp) (equivalent : α → α → Bool)
    (left right : SimpleComparisonOperand α) : Verdict :=
  evalSymmetricComparison (fun left right => op.holds (equivalent left right)) left right

end A12Kernel
