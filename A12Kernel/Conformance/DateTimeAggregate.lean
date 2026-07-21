import A12Kernel.Semantics.DateTimeAggregate

/-! # Resolved DateTime instant-extremum locks -/

namespace A12Kernel.Conformance.DateTimeAggregate

open A12Kernel

private def instant (epochSecond : Int) : Instant :=
  Instant.ofEpochSecond epochSecond

/- Both selectors use exact instant chronology and retain the left value on ties. -/
example :
    TemporalExtremumOp.minimum.selectInstant (instant 100) (instant 101) = instant 100 ∧
      TemporalExtremumOp.maximum.selectInstant (instant 100) (instant 101) = instant 101 ∧
      TemporalExtremumOp.minimum.selectInstant (instant 100) (instant 100) = instant 100 ∧
      TemporalExtremumOp.maximum.selectInstant (instant 100) (instant 100) = instant 100 := by
  native_decide

/- Empty DateTime input does not manufacture an instant, while a reached unavailable input aborts. -/
example :
    evalDateTimeExtremumAggregate .minimum {
      operands := []
      hasUninstantiatedTail := false
      hasHaving := false
    } = .notEvaluated ∧
      evalDateTimeExtremumAggregate .maximum {
        operands := [.unknown .malformed]
        hasUninstantiatedTail := false
        hasHaving := false
      } = .unknown .malformed := by
  native_decide

/- Empty operands are skipped from selection but retain symmetric missing provenance. -/
example :
    evalDateTimeExtremumAggregate .minimum {
      operands := [.notEvaluated, .value (instant 101) true, .value (instant 100) true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value (instant 100) false ∧
      evalDateTimeExtremumAggregate .maximum {
        operands := [.value (instant 100) true, .value (instant 101) true]
        hasUninstantiatedTail := true
        hasHaving := false
      } = .value (instant 101) false := by
  native_decide

/- Equal-looking Berlin overlap sides remain distinct and the earlier physical instant wins minimum. -/
example :
    let chainedDaylightSide : Instant := instant 1729989000
    let freshStandardSide : Instant := instant 1729992600
    evalDateTimeExtremumAggregate .minimum {
      operands := [.value chainedDaylightSide true, .value freshStandardSide true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value chainedDaylightSide true ∧
      evalDateTimeExtremumAggregate .maximum {
        operands := [.value chainedDaylightSide true, .value freshStandardSide true]
        hasUninstantiatedTail := false
        hasHaving := false
      } = .value freshStandardSide true := by
  native_decide

end A12Kernel.Conformance.DateTimeAggregate
