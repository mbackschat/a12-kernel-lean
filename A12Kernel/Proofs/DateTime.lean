import A12Kernel.Semantics.DateTime

/-! # Decoded DateTime and selected overlap laws -/

namespace A12Kernel

/-- Whole-second time construction succeeds exactly when each component is in range. -/
theorem timeOfDay_ofHms_isSome_iff (hour minute second : Nat) :
    (TimeOfDay.ofHms? hour minute second).isSome = true ↔
      hour < 24 ∧ minute < 60 ∧ second < 60 := by
  simp [TimeOfDay.ofHms?]

/-- Every decoded time lies within one civil day. -/
theorem timeOfDay_secondsSinceMidnight_lt (time : TimeOfDay) :
    time.secondsSinceMidnight < 86400 := by
  rcases time.valid with ⟨hourValid, minuteValid, secondValid⟩
  unfold TimeOfDay.secondsSinceMidnight
  omega

/-- Combining an admitted Date with components succeeds exactly for a valid time. -/
theorem localDateTime_ofDateHms_isSome_iff
    (date : FullDate) (hour minute second : Nat) :
    (LocalDateTime.ofDateHms? date hour minute second).isSome = true ↔
      hour < 24 ∧ minute < 60 ∧ second < 60 := by
  simp [LocalDateTime.ofDateHms?, TimeOfDay.ofHms?]

/-- End-to-end construction succeeds exactly when both the Date and time constructors succeed. -/
theorem localDateTime_ofYmdHms_isSome_iff
    (year : Int) (month day hour minute second : Nat) :
    (LocalDateTime.ofYmdHms? year month day hour minute second).isSome = true ↔
      (FullDate.ofYmd? year month day).isSome = true ∧
        hour < 24 ∧ minute < 60 ∧ second < 60 := by
  generalize dateEq : FullDate.ofYmd? year month day = date
  cases date <;>
    simp [LocalDateTime.ofYmdHms?, dateEq, LocalDateTime.ofDateHms?,
      TimeOfDay.ofHms?]

/-- UTC resolution is exactly civil-day coordinate plus seconds since midnight. -/
theorem localDateTime_resolveUtc_epochSecond (dateTime : LocalDateTime) :
    dateTime.resolveUtc.epochSecond =
      dateTime.date.unixEpochDay * 86400 +
        (dateTime.time.secondsSinceMidnight : Int) :=
  rfl

/-- For one local Date, UTC differences reduce exactly to time-of-day differences. -/
theorem localDateTime_sameDate_difference
    (date : FullDate) (left right : TimeOfDay) :
    (LocalDateTime.resolveUtc { date, time := right }).epochSecond -
        (LocalDateTime.resolveUtc { date, time := left }).epochSecond =
      (right.secondsSinceMidnight : Int) -
        (left.secondsSinceMidnight : Int) := by
  change
    (date.unixEpochDay * 86400 + (right.secondsSinceMidnight : Int)) -
        (date.unixEpochDay * 86400 + (left.secondsSinceMidnight : Int)) =
      (right.secondsSinceMidnight : Int) -
        (left.secondsSinceMidnight : Int)
  omega

/-- The `AddHours` runtime core shifts scalar instant identity by exactly the requested number of whole hours. -/
theorem instant_shiftHours_epochSecond
    (instant : Instant) (hours : Int) :
    (instant.shiftHours hours).epochSecond =
      instant.epochSecond + hours * 3600 :=
  rfl

/-- Zero hours preserve the exact instant. -/
theorem instant_shiftHours_zero (instant : Instant) :
    instant.shiftHours 0 = instant := by
  cases instant
  simp [Instant.shiftHours]

/-- Consecutive whole-hour shifts compose by addition. -/
theorem instant_shiftHours_add
    (instant : Instant) (first second : Int) :
    (instant.shiftHours first).shiftHours second =
      instant.shiftHours (first + second) := by
  cases instant
  simp [Instant.shiftHours]
  omega

/-- Shifting by an amount and its negation restores the exact instant. -/
theorem instant_shiftHours_inverse
    (instant : Instant) (hours : Int) :
    (instant.shiftHours hours).shiftHours (-hours) = instant := by
  calc
    (instant.shiftHours hours).shiftHours (-hours) =
        instant.shiftHours (hours + -hours) :=
      instant_shiftHours_add instant hours (-hours)
    _ = instant.shiftHours 0 := by congr; omega
    _ = instant := instant_shiftHours_zero instant

/-- The narrow Berlin resolver succeeds exactly on its one declared transition date. -/
theorem berlinAutumn2024_resolveLocal_isSome_iff
    (dateTime : LocalDateTime) :
    (BerlinAutumn2024.resolveLocal? dateTime).isSome = true ↔
      BerlinAutumn2024.Supported dateTime := by
  simp [BerlinAutumn2024.resolveLocal?]

/-- Fresh labels before the repeated hour resolve with the daylight offset. -/
theorem berlinAutumn2024_resolve_before_two
    (dateTime : LocalDateTime)
    (supported : BerlinAutumn2024.Supported dateTime)
    (beforeTwo : dateTime.time.hour < 2) :
    BerlinAutumn2024.resolveLocal? dateTime =
      some (dateTime.resolveUtc.shiftHours (-2)) := by
  simp [BerlinAutumn2024.resolveLocal?, supported, beforeTwo]

/-- Fresh labels from the repeated hour onward resolve with the standard offset. -/
theorem berlinAutumn2024_resolve_at_or_after_two
    (dateTime : LocalDateTime)
    (supported : BerlinAutumn2024.Supported dateTime)
    (atOrAfterTwo : 2 ≤ dateTime.time.hour) :
    BerlinAutumn2024.resolveLocal? dateTime =
      some (dateTime.resolveUtc.shiftHours (-1)) := by
  simp [BerlinAutumn2024.resolveLocal?, supported,
    show ¬dateTime.time.hour < 2 by omega]

end A12Kernel
