import A12Kernel.Semantics.DateTimeComparison
import A12Kernel.Semantics.Observation

/-! # Resolved DateTime instant-comparison locks -/

namespace A12Kernel.Conformance.DateTimeComparison

open A12Kernel

private def instant (epochSecond : Int) : Instant :=
  Instant.ofEpochSecond epochSecond

private def instantMillis (epochMillis : Int) : Instant := { epochMillis }

private def checkedInstant (value : Instant) : CheckedCell Instant :=
  { rawPresent := true, parsed := some value, findings := [] }

private def emptyInstant : CheckedCell Instant :=
  { rawPresent := false, parsed := none, findings := [] }

/- Every operator is separated on two distinct exact instants. -/
example :
    TemporalComparisonOp.equal.holdsInstant (instant 100) (instant 101) = false ∧
      TemporalComparisonOp.notEqual.holdsInstant (instant 100) (instant 101) = true ∧
      TemporalComparisonOp.before.holdsInstant (instant 100) (instant 101) = true ∧
      TemporalComparisonOp.beforeOrEqual.holdsInstant (instant 100) (instant 101) = true ∧
      TemporalComparisonOp.after.holdsInstant (instant 100) (instant 101) = false ∧
      TemporalComparisonOp.afterOrEqual.holdsInstant (instant 100) (instant 101) = false := by
  native_decide

/- Typed checked DateTime observations reuse exact-instant comparison and preserve formal unavailability. -/
example :
    TemporalComparisonOp.before.evalInstantObserved
        (observeCell .validation (checkedInstant (instant 100)))
        (observeCell .validation (checkedInstant (instant 101))) = .fired .value ∧
      TemporalComparisonOp.equal.evalInstantObserved
        (observeCell .validation emptyInstant)
        (observeCell .validation (checkedInstant (instant 101))) = .notFired ∧
      TemporalComparisonOp.before.evalInstantObserved
        (observeCell .validation (emptyInstant.withFinding .declaredConstraint))
        (observeCell .validation emptyInstant) = .unknown := by
  native_decide

/- Equality separates strict from inclusive instant ordering. -/
example :
    TemporalComparisonOp.equal.holdsInstant (instant 100) (instant 100) = true ∧
      TemporalComparisonOp.notEqual.holdsInstant (instant 100) (instant 100) = false ∧
      TemporalComparisonOp.before.holdsInstant (instant 100) (instant 100) = false ∧
      TemporalComparisonOp.beforeOrEqual.holdsInstant (instant 100) (instant 100) = true ∧
      TemporalComparisonOp.after.holdsInstant (instant 100) (instant 100) = false ∧
      TemporalComparisonOp.afterOrEqual.holdsInstant (instant 100) (instant 100) = true := by
  native_decide

/- Classified DateTime operands reuse the same symmetric VALUE/OMISSION/no-value/UNKNOWN projection as Dates. -/
example :
    TemporalComparisonOp.before.evalInstant
        (.value (instant 100) true) (.value (instant 101) true) = .fired .value ∧
      TemporalComparisonOp.before.evalInstant
        (.value (instant 100) false) (.value (instant 101) true) = .fired .omission ∧
      TemporalComparisonOp.before.evalInstant
        (.notEvaluated : SimpleComparisonOperand Instant) (.value (instant 101) true) = .notFired ∧
      TemporalComparisonOp.before.evalInstant
        (.notEvaluated : SimpleComparisonOperand Instant) (.unknown .malformed) = .unknown := by
  native_decide

/- The selected Berlin fall-back separator compares physical instants, not equal-looking wall labels. -/
example :
    let chainedDaylightSide : Instant := instant 1729989000
    let freshStandardSide : Instant := instant 1729992600
    TemporalComparisonOp.equal.holdsInstant chainedDaylightSide freshStandardSide = false ∧
      TemporalComparisonOp.notEqual.holdsInstant chainedDaylightSide freshStandardSide = true ∧
      TemporalComparisonOp.before.holdsInstant chainedDaylightSide freshStandardSide = true := by
  native_decide

/- `Now` retains the validation clock's millisecond identity even though authored DateTime values have whole-second precision. -/
example :
    TemporalComparisonOp.equal.holdsInstant
        (instantMillis 100000) (instantMillis 100999) = false ∧
      TemporalComparisonOp.before.holdsInstant
        (instantMillis 100000) (instantMillis 100999) = true := by
  native_decide

end A12Kernel.Conformance.DateTimeComparison
