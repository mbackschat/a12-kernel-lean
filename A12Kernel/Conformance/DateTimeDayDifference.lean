import A12Kernel.Semantics.DateTimeDayDifference

/-! # Model-zone calendar-day difference locks

These cases pin kernel 31.1.1's wall-clock day count (spec/05 §2.5) against the rows a12-dmkits locks at `1124b523f` (`CalendarStepDifferenceInDaysDiffTest`, `OverlapInstantInComputationDiffTest`). Each separates the wall-clock account from the elapsed-instant quotient or from kernel 30.8.1's stateful calendar-day steps.
-/

namespace A12Kernel.Conformance.DateTimeDayDifference

open A12Kernel ModelZone

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

private def berlinDays (first second : LocalDateTime) : Option Int :=
  ConcreteProfile.europeBerlin.differenceInDays? first second

/- One wall day across the spring change counts once although only 23 instant hours elapse; the elapsed quotient answers 0. -/
example :
    berlinDays (dateTime 2024 3 30 12 0 0 (by native_decide))
        (dateTime 2024 3 31 12 0 0 (by native_decide)) = some 1 := by
  native_decide

/- 23 h 15 m of wall clock is no whole day in either order, where kernel 30.8.1's adjusted landing counted 1; moving the endpoint to 01:29:59 changes nothing. -/
example :
    berlinDays (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 45 0 (by native_decide)) = some 0 ∧
    berlinDays (dateTime 2024 3 31 1 45 0 (by native_decide))
        (dateTime 2024 3 30 2 30 0 (by native_decide)) = some 0 ∧
    berlinDays (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 29 59 (by native_decide)) = some 0 := by
  native_decide

/- A gap endpoint reads as the label after the gap: `02:30` on the change day counts as `03:30`. -/
example :
    berlinDays (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 3 30 0 (by native_decide)) = some 1 ∧
    berlinDays (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 2 30 0 (by native_decide)) = some 1 := by
  native_decide

/- Long spans count wall days: kernel 30.8.1's stepping answered 369 and 7670. -/
example :
    berlinDays (dateTime 2023 4 1 2 30 0 (by native_decide))
        (dateTime 2024 4 5 2 30 0 (by native_decide)) = some 370 ∧
    berlinDays (dateTime 2003 3 31 2 30 0 (by native_decide))
        (dateTime 2024 3 31 3 0 0 (by native_decide)) = some 7671 := by
  native_decide

/- Under UTC two wall hours across midnight are no day, and authored order gives the sign. -/
example :
    ConcreteProfile.utc.differenceInDays? (dateTime 2024 5 1 23 0 0 (by native_decide))
        (dateTime 2024 5 2 1 0 0 (by native_decide)) = some 0 ∧
    ConcreteProfile.utc.differenceInDays? (dateTime 2024 5 1 12 0 0 (by native_decide))
        (dateTime 2024 5 2 12 0 0 (by native_decide)) = some 1 ∧
    ConcreteProfile.utc.differenceInDays? (dateTime 2024 5 2 12 0 0 (by native_decide))
        (dateTime 2024 5 1 12 0 0 (by native_decide)) = some (-1) := by
  native_decide

/- Twenty-four instant hours across the autumn overlap end one wall hour short of a day, from `01:30` and from `00:30`; the same span in June is one day. -/
example :
    let after (label : LocalDateTime) : Option Int := do
      let start ← ConcreteProfile.europeBerlin.resolveLocal? label
      ConcreteProfile.europeBerlin.differenceResolvedInDays? start
        { epochMillis := start.epochMillis + 86400000 }
    after (dateTime 2024 10 27 1 30 0 (by native_decide)) = some 0 ∧
      after (dateTime 2024 10 27 0 30 0 (by native_decide)) = some 0 ∧
      after (dateTime 2024 6 1 1 30 0 (by native_decide)) = some 1 := by
  native_decide

/- Concrete profile selection distinguishes aliases from an unsupported legal zone before evaluation, and the String dispatch refuses the unsupported one rather than extrapolating Berlin. -/
example :
    ConcreteProfile.ofId? "UTC" = some .utc ∧
      ConcreteProfile.ofId? "GMT" = some .utc ∧
      ConcreteProfile.ofId? "Europe/Berlin" = some .europeBerlin ∧
      ConcreteProfile.ofId? "Europe/Paris" = none ∧
      concreteDifferenceInDays? "Europe/Paris" (dateTime 2024 5 1 0 0 0 (by native_decide))
        (dateTime 2024 5 2 0 0 0 (by native_decide)) = none := by
  native_decide

end A12Kernel.Conformance.DateTimeDayDifference
