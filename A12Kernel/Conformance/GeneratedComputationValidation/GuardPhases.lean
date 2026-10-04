import A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

/-! # Computation guard and generated-validation phase separators -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.GuardPhases

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

/- Computation aborts on a reached invalid text guard; generated validation applies UNKNOWN Or TRUE
and still reports the target mismatch. This locks the phase boundary, not a Kernel capture claim. -/
example :
    (do
      let source := { model with fields := model.fields ++ [
        { textGuard with id := 7, name := "HealthyText" }] }
      let guard : ComputationCondition := .or
        (.leaf (.text (.string .equal { id := textGuard.id } "A")))
        (.leaf (.text (.string .equal { id := 7 } "A")))
      let candidate := singletonComputation (some guard) 3
      let raw : RawFlatContext := { read := fun field =>
        if field == target.id then .parsed (.num 1)
        else if field == textGuard.id then .rejected .malformed
        else if field == 7 then .parsed (.str "A") else .empty }
      let selected := GeneratedComputationTable.selectFirst candidate
        { read := (source.checkContext raw).read }
      let rule ← (assembleGeneratedLiteralNumberRule source candidate).toOption
      let outcome ← evalFlatRule? source rule raw true
      pure (selected, outcome)) =
        some (.poison .malformed, .fired (expectedMessage .value)) := by
  native_decide

/-- A scalar Number membership's computation poison becomes validation UNKNOWN; the healthy
Or branch still exposes the generated mismatch. This is an internal phase-preservation lock. -/
example : (do
    let predicate ← (model.elaborateComputationPredicate ["Form"] ["Form"]
      (.scalarMembership .included (.direct (absolutePath ["Form"] "Gate")) (.numbers [1]))).toOption
    let guard : CheckedComputationCondition model := .or (.leaf (.predicate predicate)) (.fieldFilled textGuard.id)
    let operation ← (elaborateNumericComputationOperation model ["Form"] target.id
      (.literal { value := 3, authoredScale := 0 })).toOption
    let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
      targetField := target.id, name := "computedTarget", commonPrecondition := some guard
      alternatives := .singleton { operation }, messagePlan }
    let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
    let prepared ← (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler model).toOption
    let raw : RawFlatContext := { read := fun field =>
      if field == gate.id then .rejected .malformed
      else if field == textGuard.id then .parsed (.str "A")
      else if field == target.id then .parsed (.num 1) else .empty }
    let selected ← (guard.evalChecked { read := (model.checkContext raw).read }).toOption
    let outcome ← (rule.evalFull prepared "en_US" raw GroupPresenceContext.unavailable true).toOption
    pure (selected, outcome)) = some (.poison .malformed, .fired (expectedMessage .value)) := by
  native_decide

private def comparisonModel : FlatModel := { model with fields := model.fields ++ [
  { id := 7, groupPath := ["Form"], name := "B1", policy := { kind := .boolean } },
  { id := 8, groupPath := ["Form"], name := "B2", policy := { kind := .boolean } },
  { id := 9, groupPath := ["Form"], name := "R1", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
  { id := 10, groupPath := ["Form"], name := "R2", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
  { id := 11, groupPath := ["Form"], name := "Z1", policy := { kind := .temporal .dateTime TemporalComponents.now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
  { id := 12, groupPath := ["Form"], name := "Z2", policy := { kind := .temporal .dateTime TemporalComponents.now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }] }

private def comparisonPhases (predicate : SurfaceComputationPredicate) (bad : FieldId) (cause : BaseFormalCause) := do
  let source := comparisonModel
  let predicate ← (source.elaborateComputationPredicate ["Form"] ["Form"] predicate).toOption
  let guard : CheckedComputationCondition source := .or (.leaf (.predicate predicate)) (.fieldFilled textGuard.id)
  let operation ← (elaborateNumericComputationOperation source ["Form"] target.id
    (.literal { value := 3, authoredScale := 0 })).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation source) (CheckedComputationCondition source) := {
    targetField := target.id, name := "computedTarget", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan }
  let rule ← (assembleGeneratedNumericOperationTableRule source table).toOption
  let prepared ← (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler source).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [
    { address := { field := bad, path := [] }, stored := "bad", raw := .rejected cause },
    { address := { field := textGuard.id, path := [] }, stored := "A", raw := .parsed (.str "A") },
    { address := { field := target.id, path := [] }, stored := "1", raw := .parsed (.num 1) }] }).toOption
  let selected ← (guard.evalChecked (document.scalarComputationContext evaluationWorld)).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := {
      fields := document.flatContext.withWorld evaluationWorld
      groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (selected, outcome)

example :
    comparisonPhases (.fieldComparison .equal
      (absolutePath ["Form"] "B1") (absolutePath ["Form"] "B2")) 7 .booleanToken =
        some (.poison .booleanToken, .fired (expectedMessage .value)) ∧
    comparisonPhases (.fieldComparison .equal
      (absolutePath ["Form"] "R1") (absolutePath ["Form"] "R2")) 9 .dateRangeSeparator =
        some (.poison .dateRangeSeparator, .fired (expectedMessage .value)) ∧
    comparisonPhases (.temporal .before
      (.field (absolutePath ["Form"] "Z1")) (.field (absolutePath ["Form"] "Z2"))) 11 .malformed =
        some (.poison .malformed, .fired (expectedMessage .value)) := by native_decide

example :
    comparisonPhases (.overlap {
      first := .field (absolutePath ["Form"] "R1")
      rest := [.field (absolutePath ["Form"] "R2")] }) 9 .dateRangeSeparator =
        some (.poison .dateRangeSeparator, .fired (expectedMessage .value)) ∧
    comparisonPhases (.scalarOverlap {
      scalar := .field (absolutePath ["Form"] "R1")
      list := { first := .field (absolutePath ["Form"] "R2"), rest := [] } }) 9 .dateRangeSeparator =
        some (.poison .dateRangeSeparator, .fired (expectedMessage .value)) := by native_decide

end A12Kernel.Conformance.GeneratedComputationValidation.GuardPhases
