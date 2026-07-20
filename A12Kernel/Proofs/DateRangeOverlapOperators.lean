import A12Kernel.Semantics.DateRangeOverlapOperators
import A12Kernel.Proofs.DateRangeOverlap

/-! # Resolved Date-range overlap operator laws

These laws cover the two ordered scans after cell classification and filter selection. They preserve the distinction between any-pair reached-filter polarity and scalar-versus-list matched-container polarity.
-/

namespace A12Kernel

/-- The any-pair operator has no UNKNOWN result at this resolved skipped-or-kept boundary. -/
theorem scanDateRangesOverlapOccurrences_ne_unknown
    (seen : List ResolvedDateRange)
    (reachedFilter : Bool)
    (occurrences : List ResolvedDateRangeOccurrence) :
    scanDateRangesOverlapOccurrences seen reachedFilter occurrences ≠
      .unknown := by
  induction occurrences generalizing seen reachedFilter with
  | nil =>
      simp [scanDateRangesOverlapOccurrences]
  | cons current rest ih =>
      by_cases overlap : seen.any current.range.overlaps
      · simp [scanDateRangesOverlapOccurrences, overlap]
      · simpa [scanDateRangesOverlapOccurrences, overlap] using
          ih (current.range :: seen)
            (reachedFilter || current.fromFilteredOperand)

/-- The scalar-versus-list operator also has no UNKNOWN result after unavailable cells have become skipped slots. -/
theorem scanAtLeastOneDateRangeOverlapOccurrences_ne_unknown
    (scalar : ResolvedDateRange)
    (occurrences : List ResolvedDateRangeOccurrence) :
    scanAtLeastOneDateRangeOverlapOccurrences scalar occurrences ≠
      .unknown := by
  induction occurrences with
  | nil =>
      simp [scanAtLeastOneDateRangeOverlapOccurrences]
  | cons current rest ih =>
      by_cases overlap : scalar.overlaps current.range
      · simp [scanAtLeastOneDateRangeOverlapOccurrences, overlap]
      · simpa [scanAtLeastOneDateRangeOverlapOccurrences, overlap] using ih

/-- Grouping and filter provenance cannot introduce UNKNOWN into the resolved any-pair evaluator. -/
theorem dateRangesOverlap_ne_unknown
    (operands : List ResolvedDateRangeOperand) :
    evalDateRangesOverlap operands ≠ .unknown :=
  scanDateRangesOverlapOccurrences_ne_unknown [] false
    (flattenDateRangeOccurrences operands)

/-- Neither a skipped scalar nor any resolved list scan can produce UNKNOWN. -/
theorem atLeastOneDateRangeOverlaps_ne_unknown
    (scalar : ResolvedDateRangeSlot)
    (operands : List ResolvedDateRangeOperand) :
    evalAtLeastOneDateRangeOverlaps scalar operands ≠ .unknown := by
  cases scalar with
  | skipped =>
      simp [evalAtLeastOneDateRangeOverlaps]
  | kept range =>
      exact scanAtLeastOneDateRangeOverlapOccurrences_ne_unknown range
        (flattenDateRangeOccurrences operands)

/-- Scalar-versus-list firing forgets polarity exactly to existence of a primitive overlap in the flattened kept occurrences. -/
theorem scanAtLeastOneDateRangeOverlapOccurrences_fired_iff
    (scalar : ResolvedDateRange)
    (occurrences : List ResolvedDateRangeOccurrence) :
    (∃ polarity,
        scanAtLeastOneDateRangeOverlapOccurrences scalar occurrences =
          .fired polarity) ↔
      occurrences.any (fun occurrence =>
        scalar.overlaps occurrence.range) = true := by
  induction occurrences with
  | nil =>
      simp [scanAtLeastOneDateRangeOverlapOccurrences]
  | cons current rest ih =>
      by_cases overlap : scalar.overlaps current.range
      · simp [scanAtLeastOneDateRangeOverlapOccurrences, overlap]
      · simp [scanAtLeastOneDateRangeOverlapOccurrences, overlap, ih]

/-- A kept scalar fires exactly when one flattened kept list occurrence overlaps it; operand grouping and filter provenance affect polarity, not truth. -/
theorem atLeastOneDateRangeOverlaps_fired_iff
    (scalar : ResolvedDateRange)
    (operands : List ResolvedDateRangeOperand) :
    (∃ polarity,
        evalAtLeastOneDateRangeOverlaps (.kept scalar) operands =
          .fired polarity) ↔
      (flattenDateRangeOccurrences operands).any (fun occurrence =>
        scalar.overlaps occurrence.range) = true := by
  exact scanAtLeastOneDateRangeOverlapOccurrences_fired_iff scalar
    (flattenDateRangeOccurrences operands)

private def anyDateRangeOccurrenceOverlapsSeen
    (seen : List ResolvedDateRange)
    (occurrences : List ResolvedDateRangeOccurrence) : Bool :=
  occurrences.any fun occurrence =>
    seen.any occurrence.range.overlaps

private theorem list_any_or_distributes
    (values : List α)
    (left right : α → Bool) :
    values.any (fun value => left value || right value) =
      (values.any left || values.any right) := by
  induction values with
  | nil =>
      rfl
  | cons value rest ih =>
      simp only [List.any_cons]
      rw [ih]
      cases left value <;> cases right value <;>
        cases rest.any left <;> cases rest.any right <;> rfl

private theorem list_any_dateRange_overlap_symmetric
    (range : ResolvedDateRange)
    (ranges : List ResolvedDateRange) :
    ranges.any range.overlaps =
      ranges.any (fun candidate => candidate.overlaps range) := by
  induction ranges with
  | nil =>
      rfl
  | cons candidate rest ih =>
      simp only [List.any_cons]
      rw [dateRange_overlap_symmetric range candidate, ih]

private theorem dateRangeOverlap_tailTruth
    (seen : List ResolvedDateRange)
    (current : ResolvedDateRangeOccurrence)
    (rest : List ResolvedDateRangeOccurrence)
    (noSeenOverlap : seen.any current.range.overlaps = false) :
    (anyDateRangeOccurrenceOverlapsSeen (current.range :: seen) rest ||
        anyPairDateRangesOverlap (rest.map (·.range))) =
      (anyDateRangeOccurrenceOverlapsSeen seen (current :: rest) ||
        anyPairDateRangesOverlap ((current :: rest).map (·.range))) := by
  have restSymmetry :
      rest.any (fun occurrence =>
        occurrence.range.overlaps current.range) =
        rest.any (fun occurrence =>
          current.range.overlaps occurrence.range) := by
    simpa only [List.any_map, Function.comp_def] using
      (list_any_dateRange_overlap_symmetric current.range
        (rest.map (·.range))).symm
  simp [anyDateRangeOccurrenceOverlapsSeen,
    anyPairDateRangesOverlap, noSeenOverlap,
    list_any_or_distributes,
    restSymmetry,
    Function.comp_def,
    Bool.or_left_comm, Bool.or_comm]

private theorem scanDateRangesOverlapOccurrences_fired_iff
    (seen : List ResolvedDateRange)
    (reachedFilter : Bool)
    (occurrences : List ResolvedDateRangeOccurrence) :
    (∃ polarity,
        scanDateRangesOverlapOccurrences seen reachedFilter occurrences =
          .fired polarity) ↔
      (anyDateRangeOccurrenceOverlapsSeen seen occurrences ||
        anyPairDateRangesOverlap (occurrences.map (·.range))) = true := by
  induction occurrences generalizing seen reachedFilter with
  | nil =>
      simp [scanDateRangesOverlapOccurrences,
        anyDateRangeOccurrenceOverlapsSeen,
        anyPairDateRangesOverlap]
  | cons current rest ih =>
      by_cases overlap : seen.any current.range.overlaps
      · simp [scanDateRangesOverlapOccurrences,
          anyDateRangeOccurrenceOverlapsSeen,
          anyPairDateRangesOverlap, overlap]
      · have noSeenOverlap :
            seen.any current.range.overlaps = false := by
          simpa using overlap
        rw [scanDateRangesOverlapOccurrences]
        rw [if_neg overlap]
        rw [ih (current.range :: seen)
          (reachedFilter || current.fromFilteredOperand)]
        rw [dateRangeOverlap_tailTruth seen current rest noSeenOverlap]

/-- Any-pair firing forgets polarity exactly to the flat occurrence-preserving truth relation; grouping and filter provenance affect only which firing polarity is retained. -/
theorem dateRangesOverlap_fired_iff_flatTruth
    (operands : List ResolvedDateRangeOperand) :
    (∃ polarity, evalDateRangesOverlap operands = .fired polarity) ↔
      anyPairDateRangesOverlap
        ((flattenDateRangeOccurrences operands).map (·.range)) = true := by
  simpa [evalDateRangesOverlap,
    anyDateRangeOccurrenceOverlapsSeen] using
    scanDateRangesOverlapOccurrences_fired_iff [] false
      (flattenDateRangeOccurrences operands)

/-- A filter-bearing operand with one skipped slot contributes neither truth nor polarity. -/
theorem dateRangesOverlap_filteredSkippedOperand_inert
    (operands : List ResolvedDateRangeOperand) :
    evalDateRangesOverlap
        ({ slots := [.skipped], hasFilter := true } :: operands) =
      evalDateRangesOverlap operands := by
  rfl

/-- Two unfiltered kept occurrences delegate exactly to the closed primitive overlap relation. -/
theorem dateRangesOverlap_unfiltered_pair
    (left right : ResolvedDateRange) :
    evalDateRangesOverlap
        [{ slots := [.kept left, .kept right], hasFilter := false }] =
      if left.overlaps right then .fired .value else .notFired := by
  simp [evalDateRangesOverlap, flattenDateRangeOccurrences,
    ResolvedDateRangeOperand.occurrences,
    scanDateRangesOverlapOccurrences, dateRange_overlap_symmetric]

/-- Once a kept filtered occurrence is reached, a later unfiltered pair is omission-typed even when that filtered occurrence is disjoint from both members. -/
theorem dateRangesOverlap_reachedFilteredPrefix
    (prior left right : ResolvedDateRange)
    (priorLeft : prior.overlaps left = false)
    (priorRight : prior.overlaps right = false)
    (pair : left.overlaps right = true) :
    evalDateRangesOverlap
        [{ slots := [.kept prior], hasFilter := true },
         { slots := [.kept left, .kept right], hasFilter := false }] =
      .fired .omission := by
  simp [evalDateRangesOverlap, flattenDateRangeOccurrences,
    ResolvedDateRangeOperand.occurrences,
    scanDateRangesOverlapOccurrences, dateRange_overlap_symmetric,
    priorLeft, priorRight, pair]

/-- A filtered current occurrence contributes its filter before the overlap check that fires. -/
theorem dateRangesOverlap_filteredCurrentMatch
    (left right : ResolvedDateRange)
    (pair : left.overlaps right = true) :
    evalDateRangesOverlap
        [{ slots := [.kept left], hasFilter := false },
         { slots := [.kept right], hasFilter := true }] =
      .fired .omission := by
  simp [evalDateRangesOverlap, flattenDateRangeOccurrences,
    ResolvedDateRangeOperand.occurrences,
    scanDateRangesOverlapOccurrences, dateRange_overlap_symmetric, pair]

/-- A filter after an unfiltered match is unreachable and cannot change its polarity. -/
theorem dateRangesOverlap_laterFilter_irrelevant
    (left right : ResolvedDateRange)
    (later : List ResolvedDateRangeSlot)
    (pair : left.overlaps right = true) :
    evalDateRangesOverlap
        [{ slots := [.kept left, .kept right], hasFilter := false },
         { slots := later, hasFilter := true }] =
      .fired .value := by
  simp [evalDateRangesOverlap, flattenDateRangeOccurrences,
    ResolvedDateRangeOperand.occurrences,
    scanDateRangesOverlapOccurrences, dateRange_overlap_symmetric, pair]

/-- A skipped scalar terminates before the list side is inspected. -/
theorem atLeastOneDateRangeOverlaps_skippedScalar
    (operands : List ResolvedDateRangeOperand) :
    evalAtLeastOneDateRangeOverlaps .skipped operands =
      .notFired := by
  rfl

/-- The first matching list occurrence determines scalar-versus-list polarity from its own operand only. -/
theorem atLeastOneDateRangeOverlap_headMatch
    (scalar : ResolvedDateRange)
    (current : ResolvedDateRangeOccurrence)
    (rest : List ResolvedDateRangeOccurrence)
    (overlap : scalar.overlaps current.range = true) :
    scanAtLeastOneDateRangeOverlapOccurrences scalar (current :: rest) =
      .fired
        (if current.fromFilteredOperand then .omission else .value) := by
  simp [scanAtLeastOneDateRangeOverlapOccurrences, overlap]

/-- A disjoint occurrence, filtered or not, leaves no sticky polarity in the scalar-versus-list scan. -/
theorem atLeastOneDateRangeOverlap_disjointHead
    (scalar : ResolvedDateRange)
    (current : ResolvedDateRangeOccurrence)
    (rest : List ResolvedDateRangeOccurrence)
    (disjoint : scalar.overlaps current.range = false) :
    scanAtLeastOneDateRangeOverlapOccurrences scalar (current :: rest) =
      scanAtLeastOneDateRangeOverlapOccurrences scalar rest := by
  simp [scanAtLeastOneDateRangeOverlapOccurrences, disjoint]

/-- With one kept list occurrence, scalar-versus-list truth delegates to primitive overlap and polarity is exactly that operand's filter bit. -/
theorem atLeastOneDateRangeOverlaps_singleOccurrence
    (scalar candidate : ResolvedDateRange)
    (hasFilter : Bool) :
    evalAtLeastOneDateRangeOverlaps (.kept scalar)
        [{ slots := [.kept candidate], hasFilter }] =
      if scalar.overlaps candidate then
        .fired (if hasFilter then .omission else .value)
      else
        .notFired := by
  simp [evalAtLeastOneDateRangeOverlaps,
    flattenDateRangeOccurrences,
    ResolvedDateRangeOperand.occurrences,
    scanAtLeastOneDateRangeOverlapOccurrences]

end A12Kernel
