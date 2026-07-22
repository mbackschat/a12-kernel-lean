import A12Kernel.Cell

/-! # Shared scalar equality and inequality

This module owns the small comparison seam shared by direct flat scalar validation and resolved Enumeration projection. It models only an already-classified operand, exact caller-supplied equivalence, and VALUE/OMISSION polarity. Consuming clauses remain responsible for their own empty substitution or not-evaluated rule.
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

private def EqualityOp.holds (op : EqualityOp) (equivalent : Bool) : Bool :=
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
