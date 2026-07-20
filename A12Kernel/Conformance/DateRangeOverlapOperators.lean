import A12Kernel.Semantics.DateRangeOverlapOperators

/-! # Resolved Date-range overlap operator locks

These cases start after authored operands have been expanded and filtered into ordered slots. They separate the any-pair and scalar-versus-list scans, including their different filter-derived polarity rules.
-/

namespace A12Kernel.Conformance.DateRangeOverlapOperators

open A12Kernel

private def date2024 (month day : Nat)
    (admissible : (FullDate.ofYmd? 2024 month day).isSome) : FullDate :=
  (FullDate.ofYmd? 2024 month day).get admissible

private def jan1 := date2024 1 1 (by native_decide)
private def jan15 := date2024 1 15 (by native_decide)
private def jan31 := date2024 1 31 (by native_decide)
private def feb1 := date2024 2 1 (by native_decide)
private def feb15 := date2024 2 15 (by native_decide)
private def feb28 := date2024 2 28 (by native_decide)
private def mar1 := date2024 3 1 (by native_decide)
private def mar31 := date2024 3 31 (by native_decide)

private def january : ResolvedDateRange :=
  { start := jan1, finish := jan31 }

private def lateJanuary : ResolvedDateRange :=
  { start := jan15, finish := jan31 }

private def february : ResolvedDateRange :=
  { start := feb1, finish := feb28 }

private def lateFebruary : ResolvedDateRange :=
  { start := feb15, finish := feb28 }

private def march : ResolvedDateRange :=
  { start := mar1, finish := mar31 }

private def operand (hasFilter : Bool)
    (slots : List ResolvedDateRangeSlot) : ResolvedDateRangeOperand :=
  { slots, hasFilter }

private def plain (ranges : List ResolvedDateRange) : ResolvedDateRangeOperand :=
  operand false (ranges.map .kept)

private def filtered (ranges : List ResolvedDateRange) : ResolvedDateRangeOperand :=
  operand true (ranges.map .kept)

/- A disjoint first operand cannot hide an internal pair in a later operand. -/
example :
    evalDateRangesOverlap [plain [march], plain [january, lateJanuary]] =
      .fired .value := by
  native_decide

/- Equal values arriving through two operand positions remain two occurrences. -/
example :
    evalDateRangesOverlap [plain [january], plain [january]] =
      .fired .value := by
  native_decide

/- A single occurrence cannot form a pair. -/
example : evalDateRangesOverlap [plain [january]] = .notFired := by
  native_decide

/- A filtered operand contributes polarity only after a kept occurrence is reached. -/
example :
    evalDateRangesOverlap
      [operand true [.skipped], plain [january, lateJanuary]] =
      .fired .value := by
  native_decide

/- A kept filtered occurrence taints a later any-pair firing even when it is disjoint. -/
example :
    evalDateRangesOverlap
      [filtered [march], plain [january, lateJanuary]] =
      .fired .omission := by
  native_decide

/- A filtered current occurrence contributes polarity before it is compared with the seen prefix. -/
example :
    evalDateRangesOverlap
      [plain [january], filtered [lateJanuary]] =
      .fired .omission := by
  native_decide

/- A filter after the first match is never reached. -/
example :
    evalDateRangesOverlap
      [plain [january, lateJanuary], filtered [march]] =
      .fired .value := by
  native_decide

/- Reordering can preserve truth while changing the any-pair polarity. -/
example :
    evalDateRangesOverlap
        [filtered [march], plain [january, lateJanuary]] =
          .fired .omission ∧
      evalDateRangesOverlap
        [plain [january, lateJanuary], filtered [march]] =
          .fired .value := by
  native_decide

/- Pairwise-disjoint occurrences do not fire. -/
example :
    evalDateRangesOverlap [plain [january, february, march]] =
      .notFired := by
  native_decide

/- Internal list overlap cannot rescue a skipped scalar. -/
example :
    evalAtLeastOneDateRangeOverlaps .skipped
      [plain [january, lateJanuary]] = .notFired := by
  native_decide

/- Internal list overlap also cannot rescue a kept but disjoint scalar. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept march)
      [plain [january, lateJanuary]] = .notFired := by
  native_decide

/- A filtered disjoint list operand does not taint a later unfiltered match. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [filtered [march], plain [lateJanuary]] =
        .fired .value := by
  native_decide

/- Polarity comes from the list operand containing the first match. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [plain [march], filtered [lateJanuary]] =
        .fired .omission := by
  native_decide

/- A later filtered match is irrelevant after an earlier unfiltered match. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [plain [lateJanuary], filtered [january]] =
        .fired .value := by
  native_decide

/- A scalar with no matching list occurrence does not fire. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [plain [lateFebruary, march]] = .notFired := by
  native_decide

end A12Kernel.Conformance.DateRangeOverlapOperators
