import A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

/-! # Generated-computation repeatable-source locks -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.Repeatable

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable
open A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

/- A Transform/Compile consumer discovers a filtered source through the complete shared condition tree, even though it is nested inside the generated mismatch branch. The unfiltered aggregate is the negative control. -/
example :
    repeatablePartialCompileDecision repeatableFirstFilledOperation
        "computedRepeatableFirstFilled" =
      some .emitHavingSkip ∧
    repeatablePartialCompileDecision repeatableValueCountOperation
        "computedRepeatableValueCount" =
      some .emitHavingSkip ∧
    repeatablePartialCompileDecision repeatableTokenValueCountOperation
        "computedRepeatableTokenValueCount" =
      some .emitHavingSkip ∧
    repeatablePartialCompileDecision repeatableAggregateOperation
        "computedRepeatableAggregate" =
      some .evaluate ∧
    repeatablePartialCompileDecision productAggregateOperation
        "computedProductAggregate" =
      some .evaluate := by
  native_decide

/- Token value-count generated validation exposes the selected String source and its `Having` dependencies while preserving selected-match polarity through the one checked numeric tree. -/
example :
    let selected : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 1))
      | _ => checkedNumber .empty
    let matching : RowIndex → CheckedCell
      | 1 => formalCheck { kind := .string } (.parsed (.str "A"))
      | _ => formalCheck { kind := .string } .empty
    let nonmatching : RowIndex → CheckedCell
      | 1 => formalCheck { kind := .string } (.parsed (.str "B"))
      | _ => formalCheck { kind := .string } .empty
    let document := repeatableDocument [1]
    repeatableTokenValueCountReferences =
        some (true, true, true, .modelWideCheckedComputation) ∧
      hasAddressedOutcome
        (repeatableTokenValueCountAddressedOutcome document
          (.parsed (.num (-1))) selected matching)
        (.fired (repeatableExpectedMessage
          "computedRepeatableTokenValueCount" .omission)) ∧
      hasAddressedOutcome
        (repeatableTokenValueCountAddressedOutcome document
          (.parsed (.num (-1))) selected nonmatching)
        (.fired (repeatableExpectedMessage
          "computedRepeatableTokenValueCount" .value)) := by
  native_decide

/- Value-count generated validation preserves source and filter dependencies plus the current matching-filter witness. Flattening to aggregate-wide filter presence would incorrectly make the selected non-match shrinkable. -/
example :
    let selected : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 1))
      | _ => checkedNumber .empty
    let matching : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 5))
      | _ => checkedNumber .empty
    let nonmatching : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 7))
      | _ => checkedNumber .empty
    let document := repeatableDocument [1]
    repeatableValueCountReferences =
        some (true, true, true, .modelWideCheckedComputation) ∧
      hasAddressedOutcome
        (repeatableValueCountAddressedOutcome document
          (.parsed (.num (-1))) selected matching)
        (.fired (repeatableExpectedMessage
          "computedRepeatableValueCount" .omission)) ∧
      hasAddressedOutcome
        (repeatableValueCountAddressedOutcome document
          (.parsed (.num (-1))) selected nonmatching)
        (.fired (repeatableExpectedMessage
          "computedRepeatableValueCount" .value)) := by
  native_decide

/- The model-indexed leaf exposes the target, selected repeatable field, and both `Having` dependencies to Analyze/Transform consumers, then executes through the sole checked tree. Structural address failure remains outside semantic UNKNOWN. -/
example :
    let filterRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 0))
      | 2 => checkedNumber (.parsed (.num 1))
      | _ => checkedNumber .empty
    let targetRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 9))
      | 2 => checkedNumber (.parsed (.num 5))
      | _ => checkedNumber .empty
    let malformed : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    repeatableFirstFilledReferences =
        some (true, true, true, .modelWideCheckedComputation) ∧
      hasAddressedOutcome (repeatableFirstFilledAddressedOutcome
        (repeatableDocument [1, 2]) (.parsed (.num 1))
        (.parsed (.num 5)) filterRows targetRows) .notFired ∧
      hasAddressedOutcome (repeatableFirstFilledAddressedOutcome
        (repeatableDocument [1, 2]) (.parsed (.num 1))
        (.parsed (.num 6)) filterRows targetRows)
          (.fired repeatableFirstFilledExpectedMessage) ∧
      hasAddressingError (repeatableFirstFilledAddressedOutcome malformed
        (.parsed (.num 1)) (.parsed (.num 5)) filterRows targetRows)
          (.invalidRowDepth 10 [1, 2] 1) := by
  native_decide

/- Analyze sees each checked dependency while Execute preserves full aggregate folding versus row-aligned products. The 9/75 results reject first-filled flattening and Cartesian multiplication; malformed topology remains structural insufficient information. -/
example :
    let leftRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 2))
      | 2 => checkedNumber (.parsed (.num 3))
      | 3 => checkedNumber (.parsed (.num 4))
      | _ => checkedNumber .empty
    let rightRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 5))
      | 2 => checkedNumber (.parsed (.num 7))
      | 3 => checkedNumber (.parsed (.num 11))
      | _ => checkedNumber .empty
    let complete := repeatableDocument [1, 2, 3]
    let malformed : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    repeatableAggregateReferences =
        some (true, true, .modelWideCheckedComputation) ∧
      productAggregateReferences =
        some (true, true, true, .modelWideCheckedComputation) ∧
      hasAddressedOutcome
        (repeatableAggregateAddressedOutcome complete
          (.parsed (.num 9)) leftRows) .notFired ∧
      hasAddressedOutcome
        (repeatableAggregateAddressedOutcome complete
          (.parsed (.num 10)) leftRows)
          (.fired repeatableAggregateExpectedMessage) ∧
      hasAddressedOutcome
        (productAggregateAddressedOutcome complete
          (.parsed (.num 75)) leftRows rightRows) .notFired ∧
      hasAddressedOutcome
        (productAggregateAddressedOutcome complete
          (.parsed (.num 76)) leftRows rightRows)
          (.fired productAggregateExpectedMessage) ∧
      hasAddressingError
        (repeatableAggregateAddressedOutcome malformed
          (.parsed (.num 9)) leftRows)
          (.invalidRowDepth 10 [1, 2] 1) ∧
      hasAddressingError
        (productAggregateAddressedOutcome malformed
          (.parsed (.num 75)) leftRows rightRows)
          (.invalidRowDepth 10 [1, 2] 1) := by
  native_decide

/- Direct generated `FirstFilledValue` checks relevance in source order: a present head hides a nonrelevant suffix, while an empty head reaches that suffix. -/
example :
    let sourceAndTarget := fun field =>
      field == crossGroupSource.id || field == crossGroupTarget.id
    firstFilledGeneratedError = none ∧
      firstFilledGeneratedScope = some .modelWideNonrepeatable ∧
      crossGroupFirstFilledVerdict
        (.parsed (.num 3)) (.rejected .malformed) (.parsed (.num 3))
        sourceAndTarget = some .notFired ∧
      crossGroupFirstFilledVerdict
        .empty (.parsed (.num 2)) (.parsed (.num 2))
        sourceAndTarget = some .unknown ∧
      crossGroupFirstFilledVerdict
        .empty (.parsed (.num 2)) (.parsed (.num 2))
        (fun _ => true) = some .notFired := by
  native_decide

/- Generated validation narrows the checked absolute-value/String-range tree without rebuilding either layer and compares the same nonnegative result model-wide. -/
example :
    crossGroupStringRangeOutcome 12 = some .notFired ∧
      crossGroupStringRangeOutcome 13 =
        some (.fired (crossGroupStringRangeExpectedMessage .value)) ∧
      crossGroupStringRangeOutcome 13 .empty =
        some (.fired (crossGroupStringRangeExpectedMessage .omission)) ∧
      crossGroupStringRangeOutcome 13 (.parsed (.str "AB")) =
        some (.fired (crossGroupStringRangeExpectedMessage .value)) ∧
      crossGroupStringRangeOperation.isOk = true := by
  native_decide

/- Generated validation narrows the checked rounding/conversion tree without rebuilding either layer, preserving its category projection and missing-source polarity across the computation boundary. -/
example :
    crossGroupFieldValueAsNumberOutcome 20 = some .notFired ∧
      crossGroupFieldValueAsNumberOutcome 21 =
        some (.fired (crossGroupFieldValueAsNumberExpectedMessage .value)) ∧
      crossGroupFieldValueAsNumberOutcome 21 .empty =
        some (.fired (crossGroupFieldValueAsNumberExpectedMessage .omission)) ∧
      crossGroupFieldValueAsNumberOperation.isOk = true := by
  native_decide


end A12Kernel.Conformance.GeneratedComputationValidation.Repeatable
