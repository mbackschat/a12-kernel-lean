import A12Kernel.Semantics.TimeAggregate

/-! # Resolved time-of-day extremum locks -/

namespace A12Kernel.Conformance.TimeAggregate

open A12Kernel

private def time (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  { hour, minute, second, valid }

private def early : TimeOfDay := time 9 30 15 (by decide)

private def late : TimeOfDay := time 9 30 16 (by decide)

/- Both selectors use the decoded whole-second coordinate and retain the left value on ties. -/
example :
    TemporalExtremumOp.minimum.selectTime early late = early ∧
      TemporalExtremumOp.maximum.selectTime early late = late ∧
      TemporalExtremumOp.minimum.selectTime early early = early ∧
      TemporalExtremumOp.maximum.selectTime early early = early := by
  native_decide

/- Empty Time input does not manufacture a value, while a reached unavailable input aborts. -/
example :
    evalTimeExtremumAggregate .minimum {
      operands := []
      hasUninstantiatedTail := false
      hasHaving := false
    } = .notEvaluated ∧
      evalTimeExtremumAggregate .maximum {
        operands := [.unknown .malformed]
        hasUninstantiatedTail := false
        hasHaving := false
      } = .unknown .malformed := by
  native_decide

/- Empty operands are skipped from selection but retain symmetric missing provenance. -/
example :
    evalTimeExtremumAggregate .minimum {
      operands := [.notEvaluated, .value late true, .value early true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value early false ∧
      evalTimeExtremumAggregate .maximum {
        operands := [.value early true, .value late true]
        hasUninstantiatedTail := true
        hasHaving := false
      } = .value late false := by
  native_decide

end A12Kernel.Conformance.TimeAggregate
