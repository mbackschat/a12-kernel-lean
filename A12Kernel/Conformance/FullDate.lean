import A12Kernel.Semantics.FullDate

/-! # Full Date conformance

Executable separators for the post-parse, full-precision civil Date baseline. Parsing, field formats, empty/formal operands, Date construction, zones, and arithmetic remain outside this capsule.
-/

namespace A12Kernel

private def full (year : Int) (month day : Nat)
    (admissible : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admissible

private def floorDate : FullDate :=
  full 1583 10 16 (by native_decide)

private def floorNext : FullDate :=
  full 1583 10 17 (by native_decide)

private def endOf2023 : FullDate :=
  full 2023 12 31 (by native_decide)

private def startOf2024 : FullDate :=
  full 2024 1 1 (by native_decide)

private def leapDay2000 : FullDate :=
  full 2000 2 29 (by native_decide)

private def march2000 : FullDate :=
  full 2000 3 1 (by native_decide)

/- Calendar-reality construction is Gregorian and independent of the later value floor. -/
example :
    (List.range 12).map (fun offset =>
      DateParts.daysInMonth? 2023 (offset + 1)) =
      [some 31, some 28, some 31, some 30, some 31, some 30,
        some 31, some 31, some 30, some 31, some 30, some 31] := by
  native_decide
example : (CivilDate.ofYmd? 2000 2 29).isSome = true := by native_decide
example : (CivilDate.ofYmd? 1900 2 29).isNone = true := by native_decide
example : (CivilDate.ofYmd? 2004 2 29).isSome = true := by native_decide
example : (CivilDate.ofYmd? 2100 2 29).isNone = true := by native_decide
example : (CivilDate.ofYmd? 2024 4 30).isSome = true := by native_decide
example : (CivilDate.ofYmd? 2024 4 31).isNone = true := by native_decide
example : (CivilDate.ofYmd? 2024 1 32).isNone = true := by native_decide
example : (CivilDate.ofYmd? 2024 0 1).isNone = true := by native_decide
example : (CivilDate.ofYmd? 2024 13 1).isNone = true := by native_decide
example : (CivilDate.ofYmd? 2024 1 0).isNone = true := by native_decide
example : (CivilDate.ofYmd? 0 1 1).isNone = true ∧ (CivilDate.ofYmd? (-1) 1 1).isNone = true := by native_decide

/- The always-on value floor is exact and is not the optional 1900 check. -/
example : (CivilDate.ofYmd? 1583 10 15).isSome = true := by native_decide
example : (FullDate.ofYmd? 1583 10 15).isNone = true := by native_decide
example : (FullDate.ofYmd? 1583 10 16).isSome = true := by native_decide
example : (CivilDate.ofYmd? 1500 1 1).isSome = true := by native_decide
example : (FullDate.ofYmd? 1500 1 1).isNone = true := by native_decide
example : (FullDate.ofYmd? 1899 12 31).isSome = true := by native_decide

/- Strict comparison follows chronological component order. -/
example : floorDate.before floorNext = true := by native_decide
example : endOf2023.before startOf2024 = true := by native_decide
example : startOf2024.before startOf2024 = false := by native_decide
example : startOf2024.before endOf2023 = false := by native_decide
example : leapDay2000.before march2000 = true := by native_decide

/- Chronology is lexicographic, not a conjunction of componentwise comparisons. -/
example :
    endOf2023.civil.parts.month > startOf2024.civil.parts.month ∧
      endOf2023.civil.parts.day > startOf2024.civil.parts.day ∧
      endOf2023.before startOf2024 = true := by
  native_decide

end A12Kernel
