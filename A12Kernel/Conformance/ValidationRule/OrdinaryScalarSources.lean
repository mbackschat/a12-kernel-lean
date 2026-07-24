import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Runtime
import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Temporal

/-! # Ordinary repeatable scalar-source whole-rule locks -/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryScalarSources

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

private def temporalDateParts : DateParts :=
  { year := 2024, month := 6, day := 25 }

private def temporalClock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def repeatableStringLengthData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := [{
      address := { field := innerToken.id, path := [1, 1] }
      stored := "ABC"
      raw := .parsed (.str "ABC")
    }] }

private def repeatableStringLengthSnapshot? :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableStringLengthRule?
  let outcomes ← evalOrdinaryRule? rule repeatableStringLengthData
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableStringLengthStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ← repeatableStringLengthRule?
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US" repeatableStringLengthData).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

/- Addressed `Length` reads the checked evaluated String through the existing UTF-16 owner, attaches the message to the complete current row, and preserves a missing binding structurally. -/
example :
    (repeatableStringLengthSnapshot? ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
      repeatableStringLengthStructuralFailure? =
        some (.environment (.missingBinding 10)) := by
  native_decide

private def repeatableFieldValueAsNumberData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := [
      { address := { field := innerNumericCode.id, path := [1, 1] }
        stored := "007"
        raw := .parsed (.str "007") },
      { address := { field := innerNumericChoice.id, path := [1, 1] }
        stored := "1.50"
        raw := .parsed (.enum "1.50") }] }

private def repeatableFieldValueAsNumberSnapshot?
    (source : SurfaceTextFieldOperand) (expected : Rat) (target : FieldId) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableFieldValueAsNumberRule? source expected target
  let outcomes ← evalOrdinaryRule? rule repeatableFieldValueAsNumberData
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableFieldValueAsNumberStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ←
    repeatableFieldValueAsNumberRule? repeatableNumericFactor 15
      innerNumericChoice.id
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US"
      repeatableFieldValueAsNumberData).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def repeatableFieldValueAsNumberRejectedVerdict? : Option Verdict := do
  let rule ←
    repeatableFieldValueAsNumberRule? repeatableNumericCode 7
      innerNumericCode.id
  let data : DocumentData := {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := [{
      address := { field := innerNumericCode.id, path := [1, 1] }
      stored := "ABC"
      raw := .parsed (.str "ABC")
    }] }
  let outcomes ← evalOrdinaryRule? rule data
  outcomes.head?.map (·.2.verdict)

/- Addressed conversion reuses the checked String policy and exact Enumeration category projection; a missing outer binding remains structural. -/
example :
    (repeatableFieldValueAsNumberSnapshot? repeatableNumericCode 7
      innerNumericCode.id ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerNumericCode.id, path := [1, 1] })])) = true ∧
    (repeatableFieldValueAsNumberSnapshot? repeatableNumericFactor 15
      innerNumericChoice.id ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerNumericChoice.id, path := [1, 1] })])) = true ∧
    repeatableFieldValueAsNumberRejectedVerdict? = some .unknown ∧
    repeatableFieldValueAsNumberStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

private def repeatableStringRangeData (raw : Option RawCell) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := match raw with
      | none => []
      | some cell => [{
          address := { field := innerToken.id, path := [1, 1] }
          stored := match cell with
            | .parsed (.str value) => value
            | _ => ""
          raw := cell
        }] }

private def repeatableStringRangeSnapshot?
    (op : NumericValidationOp) (expected : Rat) (raw : Option RawCell) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableStringRangeRule? op expected
  let outcomes ← evalOrdinaryRule? rule (repeatableStringRangeData raw)
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableStringRangeStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ← repeatableStringRangeRule? (.ordinary .equal) 12
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US"
      (repeatableStringRangeData (some (.parsed (.str "A12B"))))).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

/- Addressed range selection reuses the checked normalized String. Missing input keeps grow-only omission polarity, a present nondigit fallback is fixed VALUE zero, and missing bindings remain structural. -/
example :
    (repeatableStringRangeSnapshot? (.ordinary .equal) 12
      (some (.parsed (.str "A12B"))) ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
    (repeatableStringRangeSnapshot? (.ordinary .less) 100 none ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .omission,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
    (repeatableStringRangeSnapshot? (.ordinary .less) 100
      (some (.parsed (.str "ABCD"))) ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
    repeatableStringRangeStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

private def repeatableTemporalPartData
    (field : FieldId) (stored : String) (raw : Option RawCell) :
    DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := raw.toList.map fun cell => {
      address := { field, path := [1, 1] }
      stored
      raw := cell } }

private def repeatableTemporalPartSnapshot?
    (fieldName : String) (field : FieldId) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat)
    (stored : String) (raw : Option RawCell) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableTemporalPartRule? fieldName part op expected field
  let outcomes ←
    evalOrdinaryRule? rule (repeatableTemporalPartData field stored raw)
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableTemporalPartStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ←
    repeatableTemporalPartRule? "InnerDateTime" (.time .minute)
      (.ordinary .equal) 21 innerDateTime.id
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let data := repeatableTemporalPartData innerDateTime.id
    "2024-06-25T05:21:07"
    (some (.parsed (.temporal (.dateTime { epochMillis := 0 }
      temporalDateParts temporalClock .storedGregorian))))
  let document ← (checkDocument prepared "en_US" data).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def repeatableTemporalConsumerSnapshot? :
    Option (List String × List RepeatableLevel × FlatTemporalField ×
      TemporalNumericPart × CellAddr × Option String × Verdict) := do
  let declaration ←
    (ordinaryIterationModel.lookupUniqueId innerDateTime.id).toOption
  let temporal ← declaration.toTemporalField?
  let data := repeatableTemporalPartData innerDateTime.id
    "2024-06-25T05:21:07"
    (some (.parsed (.temporal (.dateTime { epochMillis := 0 }
      temporalDateParts temporalClock .storedGregorian))))
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let addressed ←
    (document.addressedCell [(10, 1), (20, 1)] innerDateTime.id).toOption
  let rule ←
    repeatableTemporalPartRule? "InnerDateTime" (.date .quarter)
      (.ordinary .equal) 2 innerDateTime.id
  let outcomes ← evalOrdinaryRule? rule data
  let outcome ← outcomes.head?
  pure (declaration.path, declaration.repeatableScope, temporal,
    .date .quarter, addressed.address, addressed.stored, outcome.2.verdict)

private def expectedRepeatableTemporalSnapshot
    (verdict : Verdict) (address : Option CellAddr) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) :=
  some (some [10, 20], true, [
    ([(10, 1), (20, 1)], verdict, address)])

/- Addressed temporal extraction reuses the checked decoded Date, Time, and DateTime payload owners. Empty input preserves symmetric omission polarity, formal invalidity remains UNKNOWN, and missing bindings remain structural. -/
example :
    (repeatableTemporalPartSnapshot? "InnerDate" innerDate.id
      (.date .day) (.ordinary .equal) 25 "2024-06-25"
      (some (.parsed (.temporal (.date { epochMillis := 0 }
        temporalDateParts .storedGregorian)))) ==
      expectedRepeatableTemporalSnapshot (.fired .value)
        (some { field := innerDate.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerTime" innerTime.id
      (.time .second) (.ordinary .equal) 7 "05:21:07"
      (some (.parsed (.temporal (.time { epochMillis := 0 }
        temporalClock)))) ==
      expectedRepeatableTemporalSnapshot (.fired .value)
        (some { field := innerTime.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerDateTime" innerDateTime.id
      (.date .quarter) (.ordinary .equal) 2 "2024-06-25T05:21:07"
      (some (.parsed (.temporal (.dateTime { epochMillis := 0 }
        temporalDateParts temporalClock .storedGregorian)))) ==
      expectedRepeatableTemporalSnapshot (.fired .value)
        (some { field := innerDateTime.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerTime" innerTime.id
      (.time .hour) (.ordinary .less) 100 "" none ==
      expectedRepeatableTemporalSnapshot (.fired .omission)
        (some { field := innerTime.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerDate" innerDate.id
      (.date .day) (.ordinary .equal) 25 "bad"
      (some (.rejected .malformed)) ==
      expectedRepeatableTemporalSnapshot .unknown none) = true ∧
    repeatableTemporalPartStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

/- Execute uses the same checked DateTime cell whose declaration, exact selected component, complete address, and stored payload remain available to Transform and Explain consumers. -/
example :
    (repeatableTemporalConsumerSnapshot? ==
      some (
        ["Order", "Sections", "Items", "InnerDateTime"],
        [10, 20],
        { id := innerDateTime.id, kind := .dateTime,
          components := dateTimeComponents },
        .date .quarter,
        { field := innerDateTime.id, path := [1, 1] },
        some "2024-06-25T05:21:07",
        .fired .value)) = true := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryScalarSources
