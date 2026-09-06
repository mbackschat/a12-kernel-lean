import A12Kernel.Semantics.FullDate
import A12Kernel.Semantics.TemporalFormat

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

/-! ## The masked comparison identity

The one law the component-omitting temporal folds owe beyond their examples: the identity they
compare is a function of the operand's **declared component set** and the model's Base Year, and not
of the components that set omits. It is stated here because `maskedDateComponents` is, and for the
same reason — two completed consumers, the distinct count and the extrema, share only that
projection.

It is a theorem rather than more cases because of where the omitted components come from. The
document's coherence check re-derives boolean, confirm and DateRange values from their stored text
but not temporal ones, so for a `yyyy-MM` declaration nothing pins which day the producer chose. A
fold that varied with that choice would not be a semantics, and no same-producer example can rule it
out. The congruence rules it out for every cell pair at once.
-/

/-- Two decoded values that agree on every component the declared set **names** compare as one
    value, whatever they hold in the components it omits.

    Stated as a congruence rather than as "the omitted field is ignored" because that is the form a
    consumer needs: it says exactly which agreements a producer must reproduce to reproduce the
    count, and it is silent about the rest. -/
theorem maskedDateComponents_congr
    (components : TemporalComponents) (baseYear : Option Int) (left right : DateParts)
    (yearAgrees : components.year = true → left.year = right.year)
    (monthAgrees : components.month = true → left.month = right.month)
    (dayAgrees : components.day = true → left.day = right.day) :
    maskedDateComponents components baseYear left
      = maskedDateComponents components baseYear right := by
  unfold maskedDateComponents
  cases hYear : components.year <;> cases hMonth : components.month <;>
    cases hDay : components.day <;>
    simp [hYear, hMonth, hDay, yearAgrees, monthAgrees, dayAgrees]

/-- The complete calendar date is the one set that constrains all three components, so there the
    congruence degenerates to equality of the decoded parts. Recorded as the boundary case: it is
    what makes the theorem above a widening of the old complete-date-only fold rather than a
    different rule. -/
theorem maskedDateComponents_fullDate_injective
    (baseYear : Option Int) (left right : DateParts)
    (agree : maskedDateComponents TemporalComponents.fullDate baseYear left
      = maskedDateComponents TemporalComponents.fullDate baseYear right) :
    left.year = right.year ∧ left.month = right.month ∧ left.day = right.day := by
  unfold maskedDateComponents TemporalComponents.fullDate at agree
  simp at agree
  exact ⟨agree.1, agree.2.1, agree.2.2⟩

end A12Kernel
