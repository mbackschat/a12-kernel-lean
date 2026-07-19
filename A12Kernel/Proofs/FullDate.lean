import A12Kernel.Semantics.FullDate

/-! # Full Date laws -/

namespace A12Kernel

/-- Calendar reality is exactly positive year, a recognized month, and a positive day within that month's leap-aware bound. -/
theorem dateParts_real_iff (parts : DateParts) :
    parts.Real ↔
      0 < parts.year ∧
        match DateParts.daysInMonth? parts.year parts.month with
        | some lastDay => 0 < parts.day ∧ parts.day ≤ lastDay
        | none => False := by
  unfold DateParts.Real DateParts.isReal
  generalize monthDaysEq :
    DateParts.daysInMonth? parts.year parts.month = monthDays
  cases monthDays <;> simp

/-- Civil-date construction succeeds exactly for Gregorian-real parts. -/
theorem civilDate_ofParts_isSome_iff (parts : DateParts) :
    (CivilDate.ofParts? parts).isSome = true ↔ parts.Real := by
  simp [CivilDate.ofParts?]

/-- Every `CivilDate` carries calendar reality by construction. -/
theorem civilDate_is_real (date : CivilDate) :
    date.parts.Real :=
  date.real

/-- Strict civil chronology is irreflexive. -/
theorem civilDate_before_irreflexive (date : CivilDate) :
    ¬date.Before date := by
  simp [CivilDate.Before, DateParts.Before]

/-- Strict civil chronology is asymmetric. -/
theorem civilDate_before_asymmetric (left right : CivilDate)
    (before : left.Before right) :
    ¬right.Before left := by
  unfold CivilDate.Before DateParts.Before at *
  omega

/-- Strict civil chronology is transitive. -/
theorem civilDate_before_transitive (first second third : CivilDate)
    (firstBefore : first.Before second)
    (secondBefore : second.Before third) :
    first.Before third := by
  unfold CivilDate.Before DateParts.Before at *
  omega

/-- Civil chronology is total: not preceding means equal or strictly following. -/
theorem civilDate_not_before_iff_eq_or_after (left right : CivilDate) :
    ¬left.Before right ↔ left = right ∨ right.Before left := by
  rcases left with ⟨⟨leftYear, leftMonth, leftDay⟩, leftReal⟩
  rcases right with ⟨⟨rightYear, rightMonth, rightDay⟩, rightReal⟩
  simp [CivilDate.Before, DateParts.Before]
  omega

/-- Admission succeeds exactly for a real civil date on or after the value floor. -/
theorem fullDate_ofCivil_isSome_iff (civil : CivilDate) :
    (FullDate.ofCivil? civil).isSome = true ↔
      ¬civil.Before CivilDate.gregorianFloor := by
  simp [FullDate.ofCivil?]

/-- End-to-end construction succeeds exactly when the parts are real and meet the value floor. -/
theorem fullDate_ofYmd_isSome_iff (year : Int) (month day : Nat) :
    (FullDate.ofYmd? year month day).isSome = true ↔
      let parts : DateParts := { year, month, day }
      parts.Real ∧ ¬parts.Before CivilDate.gregorianFloor.parts := by
  let parts : DateParts := { year, month, day }
  change ((CivilDate.ofParts? parts).bind FullDate.ofCivil?).isSome = true ↔
    parts.Real ∧ ¬parts.Before CivilDate.gregorianFloor.parts
  by_cases real : parts.Real
  · simp [CivilDate.ofParts?, real, FullDate.ofCivil?, CivilDate.Before]
  · simp [CivilDate.ofParts?, real]

/-- Every constructed `FullDate` remains Gregorian-real. -/
theorem fullDate_is_real (date : FullDate) :
    date.civil.parts.Real :=
  date.civil.real

/-- Every constructed `FullDate` carries the inclusive 1583-10-16 floor. -/
theorem fullDate_not_before_gregorianFloor (date : FullDate) :
    ¬date.civil.Before CivilDate.gregorianFloor :=
  date.admissible

/-- Every constructed `FullDate` is equal to or strictly after the inclusive floor. -/
theorem fullDate_eq_floor_or_floor_before (date : FullDate) :
    date.civil = CivilDate.gregorianFloor ∨
      CivilDate.gregorianFloor.Before date.civil :=
  (civilDate_not_before_iff_eq_or_after
    date.civil CivilDate.gregorianFloor).mp date.admissible

/-- The executable full-Date comparison is exactly strict chronology. -/
theorem fullDate_before_iff (left right : FullDate) :
    left.before right = true ↔ left.civil.Before right.civil := by
  simp [FullDate.before]

/-- No full Date strictly precedes itself. -/
theorem fullDate_before_irreflexive (date : FullDate) :
    date.before date = false := by
  simp [FullDate.before, CivilDate.Before, DateParts.Before]

/-- Executable strict full-Date comparison is transitive. -/
theorem fullDate_before_transitive (first second third : FullDate)
    (firstBefore : first.before second = true)
    (secondBefore : second.before third = true) :
    first.before third = true := by
  rw [fullDate_before_iff] at firstBefore secondBefore ⊢
  exact civilDate_before_transitive _ _ _ firstBefore secondBefore

end A12Kernel
