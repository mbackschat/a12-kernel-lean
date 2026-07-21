import A12Kernel.Semantics.DateTimeDayDifference

/-! # Finite Berlin 2024 calendar-day difference laws

These laws characterize only the declared spring-transition profile. They do not widen its date domain or claim correspondence for another zone, year, or calendar basis.
-/

namespace A12Kernel

/-- A supported fresh spring label is zero calendar days from itself; gap and out-of-profile labels fail closed. -/
theorem berlin2024_differenceInDays_self (dateTime : LocalDateTime) :
    Berlin2024Profile.differenceInDays? dateTime dateTime =
      if Berlin2024Profile.SpringSupported dateTime ∧
          ¬Berlin2024Profile.SpringGap dateTime then
        some 0
      else
        none := by
  by_cases spring : Berlin2024Profile.SpringSupported dateTime
  · have supported : Berlin2024Profile.Supported dateTime := Or.inl spring
    by_cases gap : Berlin2024Profile.SpringGap dateTime
    · simp [Berlin2024Profile.differenceInDays?, spring,
        Berlin2024Profile.resolveLocal?, supported, gap]
    · simp [Berlin2024Profile.differenceInDays?, spring,
        Berlin2024Profile.resolveLocal?, supported, gap]
  · simp [Berlin2024Profile.differenceInDays?, spring]

/-- Swapping two admitted spring-profile operands negates the signed calendar-day result; unsupported and gap inputs remain symmetrically rejected. -/
theorem berlin2024_differenceInDays_swap
    (first second : LocalDateTime) :
    (Berlin2024Profile.differenceInDays? first second).map
        (fun days => -days) =
      Berlin2024Profile.differenceInDays? second first := by
  by_cases firstSpring : Berlin2024Profile.SpringSupported first
  · by_cases secondSpring : Berlin2024Profile.SpringSupported second
    · have firstSupported : Berlin2024Profile.Supported first :=
        Or.inl firstSpring
      have secondSupported : Berlin2024Profile.Supported second :=
        Or.inl secondSpring
      by_cases firstGap : Berlin2024Profile.SpringGap first
      · simp [Berlin2024Profile.differenceInDays?, firstSpring,
          secondSpring, Berlin2024Profile.resolveLocal?, firstSupported,
          firstGap]
      · by_cases secondGap : Berlin2024Profile.SpringGap second
        · simp [Berlin2024Profile.differenceInDays?, firstSpring,
            secondSpring, Berlin2024Profile.resolveLocal?, firstSupported,
            secondSupported, firstGap, secondGap]
        · let firstInstant :=
            (first.resolveUtc.shiftHours
              (Berlin2024Profile.offsetHours first)).epochSecond
          let secondInstant :=
            (second.resolveUtc.shiftHours
              (Berlin2024Profile.offsetHours second)).epochSecond
          by_cases before : firstInstant < secondInstant
          · have notAfter : ¬secondInstant < firstInstant := by omega
            simp [Berlin2024Profile.differenceInDays?, firstSpring,
              secondSpring, Berlin2024Profile.resolveLocal?, firstSupported,
              secondSupported, firstGap, secondGap, firstInstant,
              secondInstant, before, notAfter]
          · by_cases after : secondInstant < firstInstant
            · simp [Berlin2024Profile.differenceInDays?, firstSpring,
                secondSpring, Berlin2024Profile.resolveLocal?,
                firstSupported, secondSupported, firstGap, secondGap,
                firstInstant, secondInstant, before, after]
            · simp [Berlin2024Profile.differenceInDays?, firstSpring,
                secondSpring, Berlin2024Profile.resolveLocal?,
                firstSupported, secondSupported, firstGap, secondGap,
                firstInstant, secondInstant, before, after]
    · simp [Berlin2024Profile.differenceInDays?, firstSpring,
        secondSpring]
  · simp [Berlin2024Profile.differenceInDays?, firstSpring]

end A12Kernel
