import A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

/-! # Generated-computation cross-group locks -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.CrossGroup

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable
open A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

/- Generated expression validation preserves computation's model-wide nonrepeatable operand scope; ordinary target-group validation still rejects the same cross-group reference. -/
example :
    hasScalarOutcome crossGroupScalarCapability .notFired = true ∧
      crossGroupOutcome 3 3 = some .notFired ∧
      crossGroupOutcome 3 4 = some (.fired crossGroupExpectedMessage) ∧
      crossGroupGeneratedBoundary =
        some (["Output"], .modelWideNonrepeatable) ∧
      crossGroupOrdinaryError =
        some (.fieldOutsideRowGroup ["Input", "Source"] ["Output"]) := by
  native_decide

/- The model-wide generated route traverses the same admitted temporal-component wrapper tree rather than treating direct Number as a special case. -/
example :
    (match crossGroupDatePartOperation with
    | .error _ => false
    | .ok operation =>
        (assembleGeneratedNumericOperationRule crossGroupModel operation
          "computedDatePart" none messagePlan).isOk) = true ∧
      crossGroupDatePartOutcome 2024 = some .notFired ∧
      crossGroupDatePartOutcome 2023 =
        some (.fired crossGroupDatePartExpectedMessage) := by
  native_decide

/- Generated validation preserves the checked profile-selected calendar-day atom and compares its scale-0 result without rebuilding temporal syntax. -/
example :
    crossGroupDayDifferenceOperation.isOk = true ∧
      crossGroupDayDifferenceOutcome 1 = some .notFired ∧
      crossGroupDayDifferenceOutcome 0 =
        some (.fired crossGroupDayDifferenceExpectedMessage) := by
  native_decide

/- Checked expression payloads reuse the source table: computation selects the first holding row, generated validation retains the later root-rounding/arithmetic mismatch, and tolerance remains validation-only. -/
example :
    selectedCrossGroupExpression =
      crossGroupNumberOperation.toOption.map
        (fun operation => operation.core.expression) := by
  rfl

example :
    crossGroupExpressionTableOutcome =
        some (.fired expressionTableExpectedMessage) ∧
      crossGroupExpressionTableOutcome (some .range1) = some .notFired ∧
      crossGroupExpressionSingletonOutcome 3 = some .notFired ∧
      crossGroupExpressionSingletonOutcome 4 =
        some (.fired expressionTableExpectedMessage) ∧
      crossGroupExpressionTableOutcome none
        (some (.fieldFilled crossGroupDate.id)) = some .notFired ∧
      crossGroupExpressionTargetMismatch = some (.operationTargetMismatch 2
        crossGroupTarget.id crossGroupOtherTarget.id) := by
  native_decide

/- A checked round/absolute/extremum/aggregate tree reaches both singleton and guarded all-alternative validation through the same expression narrowing; the later aggregate mismatch remains observable without a source-specific comparison wrapper. -/
example :
    crossGroupAggregateOutcome 4 = some .notFired ∧
      crossGroupAggregateOutcome 5 = some (.fired aggregateExpectedMessage) ∧
      crossGroupAggregateTableOutcome 3 =
        some (.fired aggregateExpectedMessage) := by
  native_decide

/- A category-projected value count reaches generated validation as the same checked numeric atom, retaining both selected dependencies and its scalar scope. -/
example :
    crossGroupTokenCategoryCountOperation.isOk = true ∧
      crossGroupTokenCategoryCountReferences =
        some (true, true, true, .modelWideNonrepeatable) := by
  native_decide

/- Every checked repeatable numeric source retains its address through generated-validation assembly rather than being flattened into scalar fields. -/
example :
    repeatableFirstFilledGeneratedError = none ∧
      repeatableAggregateGeneratedError = none ∧
      repeatableValueCountGeneratedError = none ∧
      repeatableTokenValueCountGeneratedError = none ∧
      productAggregateGeneratedError = none ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability repeatableFirstFilledOperation
            "computedRepeatableFirstFilled") = true ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability repeatableAggregateOperation
            "computedRepeatableAggregate") = true ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability repeatableValueCountOperation
            "computedRepeatableValueCount") = true ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability
            repeatableTokenValueCountOperation
            "computedRepeatableTokenValueCount") = true ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability productAggregateOperation
            "computedProductAggregate") = true := by
  native_decide


end A12Kernel.Conformance.GeneratedComputationValidation.CrossGroup
