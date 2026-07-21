import A12Kernel.Semantics.DateAggregate

/-! # Resolved stored-Date extremum locks -/

namespace A12Kernel.Conformance.DateAggregate

open A12Kernel

private def fullDate (year : Int) (month day : Nat)
    (admitted : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admitted

private def january : FullDate := fullDate 2026 1 5 (by native_decide)

private def february : FullDate := fullDate 2026 2 1 (by native_decide)

private def march : FullDate := fullDate 2026 3 10 (by native_decide)

private def side (operands : List (SimpleComparisonOperand FullDate))
    (hasUninstantiatedTail := false) (hasHaving := false) :
    ResolvedDateAggregateSide :=
  { operands, hasUninstantiatedTail, hasHaving }

/- A zero-length or all-empty Date fold has no synthetic value. -/
example :
    evalDateExtremumAggregate .minimum (side []) = .notEvaluated ∧
      evalDateExtremumAggregate .maximum
        (side [.notEvaluated, .notEvaluated]) = .notEvaluated := by
  native_decide

/- Minimum and maximum select chronologically from present values. -/
example :
    evalDateExtremumAggregate .minimum
        (side [.value march true, .value january true, .value february true]) =
          .value january true ∧
      evalDateExtremumAggregate .maximum
        (side [.value march true, .value january true, .value february true]) =
          .value march true := by
  native_decide

/- Empty inputs do not compete, but their missing provenance survives on a selected result. -/
example :
    evalDateExtremumAggregate .minimum
        (side [.notEvaluated, .value february true]) = .value february false ∧
      evalDateExtremumAggregate .maximum
        (side [.value february true, .notEvaluated]) = .value february false := by
  native_decide

/- Missing provenance on a present nested operand also survives even when another value wins. -/
example :
    evalDateExtremumAggregate .minimum
        (side [.value march false, .value january true]) = .value january false ∧
      evalDateExtremumAggregate .maximum
        (side [.value january false, .value march true]) = .value march false := by
  native_decide

/- Every reached formal unavailability poisons the complete fold, including after a selected value. -/
example :
    evalDateExtremumAggregate .minimum
        (side [.unknown .malformed, .value january true]) = .unknown .malformed ∧
      evalDateExtremumAggregate .maximum
        (side [.value march true, .unknown .declaredConstraint]) =
          .unknown .declaredConstraint := by
  native_decide

/- An omitted tail or `Having` marker makes an otherwise fixed selected Date missing. -/
example :
    evalDateExtremumAggregate .minimum
        (side [.value january true] true false) = .value january false ∧
      evalDateExtremumAggregate .maximum
        (side [.value march true] false true) = .value march false := by
  native_decide

/- Aggregate missingness feeds the existing symmetric Date-comparison polarity without another comparison path. -/
example :
    TemporalComparisonOp.before.eval
        (evalDateExtremumAggregate .minimum
          (side [.value february true, .notEvaluated]))
        (.value march true) = .fired .omission ∧
      TemporalComparisonOp.before.eval
        (evalDateExtremumAggregate .minimum
          (side [.value february true]))
        (.value march true) = .fired .value ∧
      TemporalComparisonOp.after.eval
        (evalDateExtremumAggregate .minimum
          (side [.value february true, .notEvaluated]))
        (.value march true) = .notFired := by
  native_decide

end A12Kernel.Conformance.DateAggregate
