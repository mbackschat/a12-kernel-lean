import A12Kernel.Semantics.DateTimeComparison

/-! # Resolved DateTime instant-comparison locks -/

namespace A12Kernel.Conformance.DateTimeComparison

open A12Kernel

private def instant (epochSecond : Int) : Instant := { epochSecond }

/- Every operator is separated on two distinct exact instants. -/
example :
    DateComparisonOp.equal.holdsInstant (instant 100) (instant 101) = false ∧
      DateComparisonOp.notEqual.holdsInstant (instant 100) (instant 101) = true ∧
      DateComparisonOp.before.holdsInstant (instant 100) (instant 101) = true ∧
      DateComparisonOp.beforeOrEqual.holdsInstant (instant 100) (instant 101) = true ∧
      DateComparisonOp.after.holdsInstant (instant 100) (instant 101) = false ∧
      DateComparisonOp.afterOrEqual.holdsInstant (instant 100) (instant 101) = false := by
  native_decide

/- Equality separates strict from inclusive instant ordering. -/
example :
    DateComparisonOp.equal.holdsInstant (instant 100) (instant 100) = true ∧
      DateComparisonOp.notEqual.holdsInstant (instant 100) (instant 100) = false ∧
      DateComparisonOp.before.holdsInstant (instant 100) (instant 100) = false ∧
      DateComparisonOp.beforeOrEqual.holdsInstant (instant 100) (instant 100) = true ∧
      DateComparisonOp.after.holdsInstant (instant 100) (instant 100) = false ∧
      DateComparisonOp.afterOrEqual.holdsInstant (instant 100) (instant 100) = true := by
  native_decide

/- Classified DateTime operands reuse the same symmetric VALUE/OMISSION/no-value/UNKNOWN projection as Dates. -/
example :
    DateComparisonOp.before.evalInstant
        (.value (instant 100) true) (.value (instant 101) true) = .fired .value ∧
      DateComparisonOp.before.evalInstant
        (.value (instant 100) false) (.value (instant 101) true) = .fired .omission ∧
      DateComparisonOp.before.evalInstant
        (.notEvaluated : SimpleComparisonOperand Instant) (.value (instant 101) true) = .notFired ∧
      DateComparisonOp.before.evalInstant
        (.notEvaluated : SimpleComparisonOperand Instant) (.unknown .malformed) = .unknown := by
  native_decide

/- The selected Berlin fall-back separator compares physical instants, not equal-looking wall labels. -/
example :
    let chainedDaylightSide : Instant := instant 1729989000
    let freshStandardSide : Instant := instant 1729992600
    DateComparisonOp.equal.holdsInstant chainedDaylightSide freshStandardSide = false ∧
      DateComparisonOp.notEqual.holdsInstant chainedDaylightSide freshStandardSide = true ∧
      DateComparisonOp.before.holdsInstant chainedDaylightSide freshStandardSide = true := by
  native_decide

end A12Kernel.Conformance.DateTimeComparison
