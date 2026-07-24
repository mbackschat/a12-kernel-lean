import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Conformance.ValidationRule.OrdinarySupport

/-! # Ordinary repeatable whole-rule admission locks -/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryAdmission

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

example :
    (ordinaryIterationRule?.map fun rule =>
      (rule.iterationScope, rule.errorDeclaration.repeatableScope)) =
      some (some [10, 20], [10, 20]) := by
  native_decide

/- Calendar-day difference is a distinct two-operand zero-sensitive operation that admits DateTime but not Time. -/
example :
    dateDifferenceConditionLegality?
      (repeatableDayDifferenceCondition?
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.field
          (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
        (.ordinary .equal) 0) =
      some (.invalid 10) ∧
    dateDifferenceConditionLegality?
      (repeatableDayDifferenceCondition?
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.field
          (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
        (.ordinary .equal) 1) =
      some .legal ∧
    (repeatableDayDifferenceCondition?
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerTime"))
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
      (.ordinary .equal) 1).isNone := by
  native_decide

/- Sub-day differences are distinct zero-sensitive operations over two DateTime operands only. -/
example :
    dateDifferenceConditionLegality?
      (repeatableDateTimeDifferenceCondition? .hours
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
        (.field
          (ordinaryPath ["Order", "Sections", "Items"]
            "InnerEarlierDateTime"))
        (.ordinary .equal) 0) =
      some (.invalid 10) ∧
    dateDifferenceConditionLegality?
      (repeatableDateTimeDifferenceCondition? .seconds
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
        (.field
          (ordinaryPath ["Order", "Sections", "Items"]
            "InnerEarlierDateTime"))
        (.ordinary .equal) 1) =
      some .legal ∧
    (repeatableDateTimeDifferenceCondition? .hours
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
      (.ordinary .equal) 1).isNone ∧
    (repeatableDateTimeDifferenceCondition? .minutes
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerTime"))
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
      (.ordinary .equal) 1).isNone ∧
    (repeatableDateTimeDifferenceCondition? .seconds
      (.baseYear .direct)
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
      (.ordinary .equal) 1).isNone := by
  native_decide

/- Date-only completed-period differences preserve their two ordered checked operands while sharing the direct-operation host-zero branch. -/
example :
    repeatableDateDifferenceLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableDateDifferenceLegality? (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableDateDifferenceLegality? (.ordinary .equal) 17 =
      some .legal ∧
    (repeatableDateDifferenceCondition? .years
      "InnerDateTime" "InnerEarlierDate" (.ordinary .equal) 1).isNone := by
  native_decide

/- Compatible nested operands select the deeper field scope, Base Year contributes no scope, and a sibling repeatable branch is rejected before execution. -/
example :
    dateDifferenceConditionLegality?
      (repeatableDateDifferenceConditionWith? .months
        (.field (ordinaryPath ["Order", "Sections"] "OuterDate"))
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.ordinary .equal) 0) =
      some (.invalid 10) ∧
    dateDifferenceConditionLegality?
      (repeatableDateDifferenceConditionWith? .years
        (.baseYear .direct)
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.ordinary .equal) 1) =
      some .legal ∧
    (repeatableDateDifferenceConditionWith? .months
      (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
      (.field (ordinaryPath ["Order", "Sections", "Notes"] "SiblingDate"))
      (.ordinary .equal) 1).isNone := by
  native_decide

/- A deeper error declaration cannot manufacture a deeper iteration level when the condition references only the outer scope. -/
example :
    (outerIterationCondition?.map fun condition =>
      match assembleResolvedValidationRule ordinaryIterationModel condition
          innerAmount.id "ordinaryIteration" .error { parts := [] } with
      | .ok _ => none
      | .error error => some error) =
      some (some
        (.iterationScopeMismatch innerAmount.id [10] [10, 20])) := by
  native_decide

/- A repeatable Number comparison must enter the existing ordered numeric condition carrier and derive the current-row scope without a new expression tree. -/
example :
    (ordinaryRepeatableNumericRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
      some (some [10], true) ∧
    (nestedRepeatableNumericRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
      some (some [10, 20], true) := by
  native_decide

/- A checked deeper-star aggregate composes with the ordinary current-row Number under the same addressed numeric tree; the star contributes only its captured outer binding to whole-rule iteration. -/
example :
    (outerWithInnerAggregateRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
      some (some [10], true) := by
  native_decide

/- The existing checked prefix and counting sources enter the same addressed whole-rule bridge and contribute only the fixed outer binding above their reopened star. -/
example :
    (outerWithInnerFirstFilledRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
        some (some [10], true) ∧
      (outerWithInnerValueCountRule?.map fun rule =>
        (rule.iterationScope, rule.requiresAddressedValidation)) =
        some (some [10], true) := by
  native_decide

/- Ordinary group paths and `RuleGroup` retain distinct authored origins while deriving the same current-row scope. -/
example :
    (outerGroupPathRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation,
        match rule.condition.core with
        | .leaf (.groupPresence _ reference) => reference.origin
        | _ => .ruleGroup)) =
        some (some [10], true, .path) ∧
    (outerRuleGroupRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation,
        match rule.condition.core with
        | .leaf (.groupPresence _ reference) => reference.origin
        | _ => .path)) =
        some (some [10], true, .ruleGroup) := by
  native_decide

private def outerEmptyCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .notFilled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

private def outerEmptyRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← outerEmptyCondition?
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerEmpty" .error { parts := [] }).toOption

private def ordinaryAssemblyError?
    (condition? : Option
      (CheckedValidationCondition ordinaryIterationModel))
    (target : FlatFieldDecl) : Option FlatRuleAssemblyError := do
  let condition ← condition?
  match assembleResolvedValidationRule ordinaryIterationModel condition target.id
      "iterationLegality" .error { parts := [] } with
  | .ok _ => none
  | .error error => some error

private def outerGroupEmptyCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
    ["Order"] (absoluteGroup ["Order", "Sections"]) .notFilled).toOption

private def guardedOrMissingInnerLevelCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ← outerIterationCondition?
  let innerGroup ← innerGroupFilledCondition?
  (outer.or innerGroup).toOption

private def guardedOuterOrCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ← outerIterationCondition?
  let outerGroup ←
    (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
      ["Order"] (absoluteGroup ["Order", "Sections"]) .filled).toOption
  (outer.or outerGroup).toOption

/- Per-level static legality rejects pure negative field and group conditions at their outer repeatable level. -/
example :
    outerEmptyRule?.isNone = true ∧
    ordinaryAssemblyError? outerEmptyCondition? outerAmount =
      some (.negativeConditionInIteration 10) ∧
    ordinaryAssemblyError? outerGroupEmptyCondition? outerAmount =
      some (.negativeConditionInIteration 10) := by
  native_decide

/- Direct iterating Number comparisons against host-converted zero reproduce the source visitor's exact operator partition in both operand orders. -/
example :
    directRepeatableNumericLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    directRepeatableNumericLegality? (.ordinary .lessEqual) 0 =
      some (.invalid 10) ∧
    directRepeatableNumericLegality? (.ordinary .greaterEqual) 0 =
      some (.invalid 10) ∧
    directRepeatableNumericLegality? (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    ordinaryAssemblyError?
      (directRepeatableNumericCondition? (.ordinary .equal) 0)
      outerAmount = some (.negativeConditionInIteration 10) := by
  native_decide

/- Strict, not-equal, tolerance, and converted-nonzero controls are admitted; a rational that is not representable at its asserted authored scale remains explicitly unclassified. -/
example :
    directRepeatableNumericLegality? (.ordinary .notEqual) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .less) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .greater) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.tolerance .range1) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .equal) 1 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .equal) (2 / 5) =
      some (.insufficient 10) := by
  native_decide

private def halfTieFromBelow : DecodedNumericLiteral :=
  { value := (1 / 2 : Rat) - 1 / (2 ^ 55)
    authoredScale := 55 }

private def belowHalfTie : DecodedNumericLiteral :=
  { value := halfTieFromBelow.value - 1 / (10 ^ 56)
    authoredScale := 56 }

/- The pure conversion owner also retains Java's asymmetric half rounding, long saturation, signed-int wrap, and the checked finite-decimal representation boundary. -/
example :
    DecodedNumericLiteral.iterationHostInt32?
      { value := -1 / 2, authoredScale := 1 } = some 0 ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := -51 / 100, authoredScale := 2 } = some (-1) ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := 9223372036854775807, authoredScale := 0 } = some (-1) ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := -9223372036854775808, authoredScale := 0 } = some 0 ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := 2 / 5, authoredScale := 0 } = none ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := 1, authoredScale := -1 } = none := by
  native_decide

/- The checked decimal carrier is sufficient for the kernel host conversion. Binary64 tie-to-even can move an exact value below one half onto one half; Java rounding and signed-32-bit narrowing then determine the static zero test. -/
example :
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      { value := 2 / 5, authoredScale := 1 } =
        some (.invalid 10) ∧
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      { value := 1 / 2, authoredScale := 1 } =
        some .legal ∧
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      halfTieFromBelow = some .legal ∧
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      belowHalfTie = some (.invalid 10) ∧
    directRepeatableNumericLiteralLegality? (.ordinary .equal)
      { value := 4294967296, authoredScale := 0 } =
        some (.invalid 10) ∧
    directRepeatableNumericLiteralLegality? (.ordinary .equal)
      { value := 4294967297, authoredScale := 0 } =
        some .legal := by
  native_decide

/- An outer guard cannot legalize an inner negative condition: the first unguarded level remains explicit. Adding the existing inner group-presence guard closes that same level. -/
example :
    (nestedUnguardedCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some (.invalid 20) ∧
    (ordinaryIterationCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some .legal := by
  native_decide

/- `Or` requires every branch to reference and guard each selected level. Two outer guards are legal, but an outer-only branch does not guard the inner level selected by its sibling. -/
example :
    (guardedOuterOrCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some .legal ∧
    (guardedOrMissingInnerLevelCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some (.invalid 20) := by
  native_decide

/- A top-level composite arithmetic operation is admitted even where its direct field/zero counterpart is rejected; the source visitor's direct-zero branch does not erase parse-tree topology. -/
example :
    compositeRepeatableNumericLegality? (.ordinary .equal) 0 =
        some .legal ∧
    (ordinaryRepeatableNumericRule?.bind fun rule =>
      rule.condition.core.iterationLegality.toOption) =
        some .legal ∧
    (nestedRepeatableNumericRule?.bind fun rule =>
      rule.condition.core.iterationLegality.toOption) =
        some .legal := by
  native_decide

/- Direct-field operation-list wrappers retain their distinct zero guard while sharing the same checked expression tree. -/
example :
    wrappedRepeatableNumericLegality? (fun body => .abs body)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality? (fun body => .abs body)
      (.ordinary .equal) 0 true = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality?
      (fun body => .round .floor omittedRoundingPlaces body)
      (.ordinary .greaterEqual) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality? (fun body => .abs body)
      (.ordinary .notEqual) 0 = some .legal ∧
    wrappedRepeatableNumericLegality?
      (fun body => .round .floor omittedRoundingPlaces body)
      (.ordinary .equal) 1 = some .legal := by
  native_decide

/- Evaluated String `Length` is a direct field operation with the same host-zero branch; its own repeatable field supplies the ordinary scope. -/
example :
    repeatableStringLengthLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .greaterEqual) 0 =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .lessEqual) 0 =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .greaterEqual) 0 true =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .equal) 1 =
      some .legal ∧
    repeatableStringLengthLegality? (.ordinary .less) 0 =
      some .legal := by
  native_decide

/- `FieldValueAsNumber` retains its checked String or category projection while sharing the direct-operation host-zero branch. -/
example :
    repeatableFieldValueAsNumberLegality? repeatableNumericCode
        (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericCode
        (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericCode
        (.ordinary .equal) 7 =
      some .legal ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericFactor
        (.ordinary .greaterEqual) 0 =
      some (.invalid 10) ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericFactor
        (.ordinary .less) 0 =
      some .legal := by
  native_decide

/- `RangeAsNumber` retains its checked interval while sharing the direct-operation host-zero branch. -/
example :
    repeatableStringRangeLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableStringRangeLegality? (.ordinary .equal) 0 2 3 true =
      some (.invalid 10) ∧
    repeatableStringRangeLegality? (.ordinary .equal) 12 =
      some .legal ∧
    repeatableStringRangeLegality? (.ordinary .less) 0 =
      some .legal ∧
    repeatableStringRangeLegality? (.ordinary .equal) 12 0 3 =
      none := by
  native_decide

/- Direct temporal component extraction retains its kind/component certificate while sharing the direct-operation host-zero branch. -/
example :
    repeatableTemporalPartLegality? "InnerDate" (.date .day)
        (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableTemporalPartLegality? "InnerTime" (.time .second)
        (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableTemporalPartLegality? "InnerDateTime" (.date .quarter)
        (.ordinary .equal) 2 =
      some .legal ∧
    repeatableTemporalPartLegality? "InnerDate" (.time .hour)
        (.ordinary .equal) 5 =
      none ∧
    repeatableTemporalPartLegality? "InnerTime" (.date .year)
        (.ordinary .equal) 2024 =
      none := by
  native_decide

/- Single-field operand-list Min/Max calls retain the same top-level operation-list guard without being flattened into direct fields. -/
example :
    wrappedRepeatableNumericLegality?
      (fun body => .extremumCall .minimum body)
      (.ordinary .lessEqual) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality?
      (fun body => .extremumCall .minimum
        (.extremum .minimum body body))
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality?
      (fun body => .extremumCall .maximum body)
      (.ordinary .notEqual) 0 = some .legal := by
  native_decide

/- Plain-star entity-list operations retain distinct zero and positive-threshold admission families. -/
example :
    plainStarEntityLegality? (fun source => .firstFilled source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    plainStarEntityLegality? (fun source => .valueCount 4 source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    plainStarEntityLegality? (fun source => .aggregate .sum source)
      (.ordinary .greaterEqual) 0 = some (.invalid 10) ∧
    plainStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .equal) 0 = some .legal ∧
    plainStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .lessEqual) 1 = some (.invalid 10) ∧
    plainStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .greaterEqual) 1 true = some (.invalid 10) ∧
    plainStarEntityLegality? (fun source => .firstFilled source)
      (.ordinary .notEqual) 1 = some .legal ∧
    plainStarEntityLegality? (fun source => .valueCount 4 source)
      (.ordinary .notEqual) 1 = some (.invalid 10) := by
  native_decide

/- Mixed-scope operation lists remain all-iterating at their common outer level but reject every numeric-constant comparison at the inner level where one reference stops iterating. -/
example :
    mixedScopeWrappedNumericLegality? (.ordinary .equal) 0 =
        some (.invalid 10) ∧
    mixedScopeWrappedNumericLegality? (.ordinary .equal) 1 =
        some (.invalid 20) ∧
    mixedScopeWrappedNumericLegality? (.ordinary .greater) 1 =
        some (.invalid 20) := by
  native_decide

/- A direct-plus-star entity list is mixed at the star's surrounding level, so every immediate numeric literal is rejected without consulting comparison direction or host conversion. -/
example :
    mixedDirectStarEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 1 = some (.invalid 10) ∧
    mixedDirectStarEntityLegality?
      (fun source => .firstFilled source)
      (.ordinary .notEqual) (-1) true = some (.invalid 10) ∧
    mixedDirectStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    mixedDirectStarEntityLegality?
      (fun source => .valueCount 4 source)
      (.ordinary .greater) (2 / 5) = some (.invalid 10) := by
  native_decide

/- `Having` references do not participate in the operation-list reference classifier. A filtered target keeps its own star scope even when its filter also reads a noniterating field. -/
example :
    filteredEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 1 = some .legal ∧
    filteredEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    filteredEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .equal) 0 = some .legal ∧
    filterMixedReferenceEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 1 = some .legal := by
  native_decide

/- String/Enumeration `NumberOfValueInFields` has the same zero and positive-threshold sensitivities as its Number overload. A mixed direct/star target list takes the stronger any-literal branch. -/
example :
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .lessEqual) 1 = some (.invalid 10) ∧
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .greaterEqual) 1 true = some (.invalid 10) ∧
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .equal) 1 = some .legal ∧
    tokenValueCountLegality? mixedTokenValueCountSource?
      (.ordinary .greater) (2 / 5) = some (.invalid 10) := by
  native_decide

/- Positive-threshold classification observes the same narrowed host integer rather than the exact positive decimal. -/
example :
    (plainStarTokenValueCountSource?.bind fun source =>
      orderedAtomLiteralLegality? (.tokenValueCount source)
        (.ordinary .less)
        { value := 4294967296, authoredScale := 0 }) =
      some .legal ∧
    (plainStarTokenValueCountSource?.bind fun source =>
      orderedAtomLiteralLegality? (.tokenValueCount source)
        (.ordinary .less)
        { value := 4294967297, authoredScale := 0 }) =
      some (.invalid 10) := by
  native_decide

/- `SumOfProducts` shares only the plain-star zero-sensitive branch; a positive not-equal threshold remains admitted. -/
example :
    plainStarProductLegality? (.ordinary .equal) 0 =
        some (.invalid 10) ∧
    plainStarProductLegality? (.ordinary .notEqual) 1 =
        some .legal ∧
    (guardedPlainStarProductRule?.map fun rule =>
      (rule.iterationScope, rule.condition.core.iterationLegality.toOption,
        rule.requiresAddressedValidation)) =
      some (some [10], some .legal, true) := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryAdmission
