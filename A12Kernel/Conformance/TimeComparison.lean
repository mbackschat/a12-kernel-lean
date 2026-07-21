import A12Kernel.Semantics.TimeComparison

/-! # Resolved time-of-day comparison locks -/

namespace A12Kernel.Conformance.TimeComparison

open A12Kernel

private def time (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  { hour, minute, second, valid }

private def morning : TimeOfDay := time 9 30 15 (by decide)

private def evening : TimeOfDay := time 17 45 30 (by decide)

/- All six operators compare decoded time-of-day coordinates, not rendered text. -/
example :
    TemporalComparisonOp.equal.holdsTime morning evening = false ∧
      TemporalComparisonOp.notEqual.holdsTime morning evening = true ∧
      TemporalComparisonOp.before.holdsTime morning evening = true ∧
      TemporalComparisonOp.beforeOrEqual.holdsTime morning evening = true ∧
      TemporalComparisonOp.after.holdsTime morning evening = false ∧
      TemporalComparisonOp.afterOrEqual.holdsTime morning evening = false := by
  native_decide

/- Equal decoded times satisfy equality and both inclusive directions only. -/
example :
    TemporalComparisonOp.equal.holdsTime morning morning = true ∧
      TemporalComparisonOp.notEqual.holdsTime morning morning = false ∧
      TemporalComparisonOp.before.holdsTime morning morning = false ∧
      TemporalComparisonOp.beforeOrEqual.holdsTime morning morning = true ∧
      TemporalComparisonOp.after.holdsTime morning morning = false ∧
      TemporalComparisonOp.afterOrEqual.holdsTime morning morning = true := by
  native_decide

/- Classified Time operands reuse the symmetric temporal verdict path. -/
example :
    TemporalComparisonOp.before.evalTime
        (.value morning true) (.value evening true) = .fired .value ∧
      TemporalComparisonOp.before.evalTime
        (.value morning false) (.value evening true) = .fired .omission ∧
      TemporalComparisonOp.before.evalTime
        .notEvaluated (.value evening true) = .notFired ∧
      TemporalComparisonOp.before.evalTime
        (.unknown .malformed) (.value evening true) = .unknown := by
  native_decide

end A12Kernel.Conformance.TimeComparison
