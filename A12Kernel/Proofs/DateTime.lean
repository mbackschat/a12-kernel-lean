import A12Kernel.Proofs.FullDate
import A12Kernel.Semantics.DateTime

/-! # Decoded DateTime and selected overlap laws -/

namespace A12Kernel

private theorem daysInMonth_some_bounds (year : Int) (month lastDay : Nat)
    (found : DateParts.daysInMonth? year month = some lastDay) :
    1 ≤ month ∧ month ≤ 12 := by
  have positive : 0 < month := by
    by_cases zero : month = 0
    · subst month
      simp [DateParts.daysInMonth?] at found
    · omega
  have belowThirteen : month < 13 := by
    by_cases high : 13 ≤ month
    · obtain ⟨offset, monthEq⟩ :=
        Nat.exists_eq_add_of_le' high
      rw [monthEq] at found
      simp [DateParts.daysInMonth?] at found
    · omega
  omega

private theorem civilDate_real_components (date : CivilDate) :
    0 < date.parts.year ∧
      ∃ lastDay,
        DateParts.daysInMonth? date.parts.year date.parts.month =
            some lastDay ∧
          0 < date.parts.day ∧ date.parts.day ≤ lastDay := by
  have reality := (dateParts_real_iff date.parts).mp date.real
  cases found :
      DateParts.daysInMonth? date.parts.year date.parts.month with
  | none => simp [found] at reality
  | some lastDay =>
      refine ⟨reality.1, lastDay, rfl, ?_⟩
      simpa [found] using reality.2

private theorem civilDate_daysBeforeYear_succ (year : Int) (positive : 0 < year) :
    CivilDate.daysBeforeYear (year + 1) =
      CivilDate.daysBeforeYear year +
        if DateParts.isLeapYear year then 366 else 365 := by
  have div4 :=
    Int.add_one_tdiv_of_pos (a := year - 1) (b := 4) (by decide)
  have div100 :=
    Int.add_one_tdiv_of_pos (a := year - 1) (b := 100) (by decide)
  have div400 :=
    Int.add_one_tdiv_of_pos (a := year - 1) (b := 400) (by decide)
  have normalize : year - 1 + 1 = year := by omega
  rw [normalize] at div4 div100 div400
  have notNegative : ¬year - 1 < 0 := by omega
  simp only [positive, true_and, notNegative, false_and] at div4 div100 div400
  by_cases divisible4 : (4 : Int) ∣ year <;>
    by_cases divisible100 : (100 : Int) ∣ year <;>
    by_cases divisible400 : (400 : Int) ∣ year
  all_goals
    simp [CivilDate.daysBeforeYear, DateParts.isLeapYear,
      divisible4, divisible100, divisible400] at div4 div100 div400 ⊢
  all_goals omega

private theorem daysBeforeMonth_succ
    (year : Int) (month : Nat) (positive : 0 < month) :
    CivilDate.daysBeforeMonth year (month + 1) =
      CivilDate.daysBeforeMonth year month +
        (DateParts.daysInMonth? year month).getD 0 := by
  have recover : month - 1 + 1 = month :=
    Nat.sub_add_cancel positive
  have rangeEq :
      List.range month = List.range (month - 1) ++ [month - 1] := by
    calc
      List.range month =
          List.range (month - 1 + 1) :=
        congrArg List.range recover.symm
      _ = List.range (month - 1) ++ [month - 1] :=
        List.range_succ
  simp [CivilDate.daysBeforeMonth, rangeEq, recover]

private theorem daysBeforeMonth_monotone
    (year : Int) (left right : Nat)
    (positive : 0 < left) (ordered : left ≤ right) :
    CivilDate.daysBeforeMonth year left ≤
      CivilDate.daysBeforeMonth year right := by
  obtain ⟨gap, rfl⟩ := Nat.exists_eq_add_of_le ordered
  induction gap with
  | zero => simp
  | succ gap ih =>
      have prior := ih (by omega)
      have shape : left + (gap + 1) = (left + gap) + 1 := by omega
      rw [shape, daysBeforeMonth_succ year (left + gap) (by omega)]
      omega

private theorem daysBeforeMonth_yearLength (year : Int) :
    CivilDate.daysBeforeMonth year 13 =
      if DateParts.isLeapYear year then 366 else 365 := by
  by_cases leap : DateParts.isLeapYear year = true <;>
    simp [CivilDate.daysBeforeMonth, DateParts.daysInMonth?, leap] <;>
    decide

private theorem civilDate_dayOffset_bounds (date : CivilDate) :
    0 ≤ date.dayOffset ∧
      date.dayOffset <
        if DateParts.isLeapYear date.parts.year then 366 else 365 := by
  obtain ⟨_, lastDay, found, dayBounds⟩ :=
    civilDate_real_components date
  have monthBounds :=
    daysInMonth_some_bounds date.parts.year date.parts.month lastDay found
  have prefixStep :=
    daysBeforeMonth_succ date.parts.year date.parts.month
      (by omega)
  rw [found] at prefixStep
  have prefixBound :=
    daysBeforeMonth_monotone date.parts.year
      (date.parts.month + 1) 13 (by omega) (by omega)
  have yearLength :=
    daysBeforeMonth_yearLength date.parts.year
  simp only [Option.getD_some] at prefixStep
  have withinYear :
      CivilDate.daysBeforeMonth date.parts.year date.parts.month +
          date.parts.day ≤
        CivilDate.daysBeforeMonth date.parts.year 13 := by
    omega
  constructor
  · simp only [CivilDate.dayOffset]
    omega
  · simp only [CivilDate.dayOffset]
    by_cases leap : DateParts.isLeapYear date.parts.year = true
    all_goals simp [leap] at yearLength ⊢
    all_goals omega

private theorem civilDate_dayOffset_strict_of_sameYear
    (left right : CivilDate)
    (sameYear : left.parts.year = right.parts.year)
    (withinYear :
      left.parts.month < right.parts.month ∨
        left.parts.month = right.parts.month ∧
          left.parts.day < right.parts.day) :
    left.dayOffset < right.dayOffset := by
  rcases left with ⟨⟨leftYear, leftMonth, leftDay⟩, leftReal⟩
  rcases right with ⟨⟨rightYear, rightMonth, rightDay⟩, rightReal⟩
  simp only at sameYear
  subst rightYear
  have leftComponents :=
    civilDate_real_components
      ⟨⟨leftYear, leftMonth, leftDay⟩, leftReal⟩
  have rightComponents :=
    civilDate_real_components
      ⟨⟨leftYear, rightMonth, rightDay⟩, rightReal⟩
  simp only at leftComponents rightComponents
  obtain ⟨_, leftLastDay, leftFound, leftDayBounds⟩ :=
    leftComponents
  obtain ⟨_, _, _, rightDayBounds⟩ :=
    rightComponents
  simp only at withinYear
  rcases withinYear with monthBefore | ⟨sameMonth, dayBefore⟩
  · have prefixStep :=
      daysBeforeMonth_succ leftYear leftMonth
        (daysInMonth_some_bounds _ _ _ leftFound).1
    rw [leftFound] at prefixStep
    simp only [Option.getD_some] at prefixStep
    have prefixBound :=
      daysBeforeMonth_monotone leftYear (leftMonth + 1) rightMonth
        (by omega) (by omega)
    simp only [CivilDate.dayOffset]
    omega
  · subst rightMonth
    simp only [CivilDate.dayOffset]
    omega

private theorem civilDate_daysBeforeYear_monotone
    (leftYear rightYear : Int)
    (positive : 0 < leftYear)
    (ordered : leftYear ≤ rightYear) :
    CivilDate.daysBeforeYear leftYear ≤
      CivilDate.daysBeforeYear rightYear := by
  have leftNonnegative : 0 ≤ leftYear - 1 := by omega
  have rightNonnegative : 0 ≤ rightYear - 1 := by omega
  unfold CivilDate.daysBeforeYear
  simp only [Int.tdiv_eq_ediv_of_nonneg leftNonnegative,
    Int.tdiv_eq_ediv_of_nonneg rightNonnegative]
  omega

/-- The executable civil-day coordinate strictly preserves Gregorian chronology. -/
theorem civilDate_before_unixEpochDay (left right : CivilDate)
    (before : left.Before right) :
    left.unixEpochDay < right.unixEpochDay := by
  have leftPositive : 0 < left.parts.year :=
    ((dateParts_real_iff left.parts).mp left.real).1
  have leftOffset := civilDate_dayOffset_bounds left
  have rightOffset := civilDate_dayOffset_bounds right
  rcases before with yearBefore | ⟨sameYear, withinYear⟩
  · have yearStep :=
      civilDate_daysBeforeYear_succ left.parts.year leftPositive
    have laterStart :=
      civilDate_daysBeforeYear_monotone (left.parts.year + 1)
        right.parts.year (by omega) (by omega)
    simp only [CivilDate.unixEpochDay]
    omega
  · have offsetBefore :=
      civilDate_dayOffset_strict_of_sameYear left right sameYear
        withinYear
    simp [CivilDate.unixEpochDay, sameYear] at *
    omega

private theorem civilDate_ofYmd_map_unixEpochDay
    (year : Int) (month day : Nat)
    (real : ({ year, month, day } : DateParts).Real) :
    (CivilDate.ofYmd? year month day).map CivilDate.unixEpochDay =
      some
        (CivilDate.daysBeforeYear year +
          (CivilDate.daysBeforeMonth year month : Int) +
          (day : Int) - 1 - 719162) := by
  simp [CivilDate.ofYmd?, CivilDate.ofParts?, real,
    CivilDate.unixEpochDay, CivilDate.dayOffset]
  omega

private theorem firstOfNextMonth_real
    (year : Int) (month : Nat)
    (positiveYear : 0 < year)
    (monthBounds : 1 ≤ month ∧ month ≤ 12)
    (beforeDecember : month < 12) :
    ({ year, month := month + 1, day := 1 } : DateParts).Real := by
  apply
    (dateParts_real_iff
      { year, month := month + 1, day := 1 }).mpr
  constructor
  · exact positiveYear
  · have monthCases :
        month = 1 ∨ month = 2 ∨ month = 3 ∨ month = 4 ∨
          month = 5 ∨ month = 6 ∨ month = 7 ∨ month = 8 ∨
          month = 9 ∨ month = 10 ∨ month = 11 := by
      omega
    rcases monthCases with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
    all_goals simp [DateParts.daysInMonth?]
    all_goals split <;> omega

/-- The checked civil successor always exists and advances the executable day coordinate by exactly one. -/
theorem civilDate_next_unixEpochDay (date : CivilDate) :
    date.next?.map CivilDate.unixEpochDay =
      some (date.unixEpochDay + 1) := by
  rcases date with ⟨⟨year, month, day⟩, real⟩
  have reality := (dateParts_real_iff { year, month, day }).mp real
  have positiveYear : 0 < year := by
    simpa using reality.1
  cases found : DateParts.daysInMonth? year month with
  | none => simp [found] at reality
  | some lastDay =>
      have dayBounds : 0 < day ∧ day ≤ lastDay := by
        simpa [found] using reality.2
      have monthBounds :=
        daysInMonth_some_bounds year month lastDay found
      by_cases beforeLast : day < lastDay
      · have nextReal :
            ({ year, month, day := day + 1 } : DateParts).Real := by
          apply
            (dateParts_real_iff
              { year, month, day := day + 1 }).mpr
          constructor
          · exact positiveYear
          · rw [found]
            change 0 < day + 1 ∧ day + 1 ≤ lastDay
            omega
        simp only [CivilDate.next?]
        rw [found]
        simp only [beforeLast, if_true]
        rw [civilDate_ofYmd_map_unixEpochDay
          year month (day + 1) nextReal]
        simp [CivilDate.unixEpochDay, CivilDate.dayOffset]
        omega
      · have finalDay : day = lastDay := by omega
        subst day
        by_cases beforeDecember : month < 12
        · have nextReal :=
            firstOfNextMonth_real year month positiveYear monthBounds
              beforeDecember
          have prefixStep :=
            daysBeforeMonth_succ year month monthBounds.1
          rw [found] at prefixStep
          simp only [Option.getD_some] at prefixStep
          simp only [CivilDate.next?]
          rw [found]
          simp only [Nat.lt_irrefl, if_false, beforeDecember, if_true]
          rw [civilDate_ofYmd_map_unixEpochDay
            year (month + 1) 1 nextReal]
          simp [CivilDate.unixEpochDay, CivilDate.dayOffset]
          omega
        · have december : month = 12 := by omega
          subst month
          have lastDayThirtyOne : lastDay = 31 := by
            simpa [DateParts.daysInMonth?] using found.symm
          subst lastDay
          have nextReal :
              ({ year := year + 1, month := 1, day := 1 } :
                DateParts).Real := by
            apply
              (dateParts_real_iff
                { year := year + 1, month := 1, day := 1 }).mpr
            constructor
            · change 0 < year + 1
              omega
            · simp [DateParts.daysInMonth?]
          have yearStep :=
            civilDate_daysBeforeYear_succ year positiveYear
          have monthStep :=
            daysBeforeMonth_succ year 12 (by decide)
          simp [DateParts.daysInMonth?] at monthStep
          have yearLength :=
            daysBeforeMonth_yearLength year
          have januaryStart :
              CivilDate.daysBeforeMonth (year + 1) 1 = 0 := by
            simp [CivilDate.daysBeforeMonth]
          simp only [CivilDate.next?]
          rw [found]
          simp only [Nat.reduceLT, ↓reduceIte]
          rw [civilDate_ofYmd_map_unixEpochDay
            (year + 1) 1 1 nextReal]
          simp [CivilDate.unixEpochDay, CivilDate.dayOffset]
          by_cases leap : DateParts.isLeapYear year = true
          all_goals simp [leap] at yearStep yearLength ⊢
          all_goals omega

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

/-- UTC resolution strictly preserves chronological order on admitted local wall labels. -/
theorem localDateTime_before_resolveUtc
    (left right : LocalDateTime) (before : left.Before right) :
    left.resolveUtc.epochSecond < right.resolveUtc.epochSecond := by
  have leftTime := timeOfDay_secondsSinceMidnight_lt left.time
  rcases before with dateBefore | ⟨sameDate, timeBefore⟩
  · have dayBefore :=
      civilDate_before_unixEpochDay left.date.civil right.date.civil
        dateBefore
    change
      left.date.unixEpochDay * 86400 +
          (left.time.secondsSinceMidnight : Int) <
        right.date.unixEpochDay * 86400 +
          (right.time.secondsSinceMidnight : Int)
    simp only [FullDate.unixEpochDay]
    omega
  · change
      left.date.unixEpochDay * 86400 +
          (left.time.secondsSinceMidnight : Int) <
        right.date.unixEpochDay * 86400 +
          (right.time.secondsSinceMidnight : Int)
    simp only [FullDate.unixEpochDay, sameDate]
    omega

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

end A12Kernel
