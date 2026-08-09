import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Runtime

/-!
# Checked once-evaluation validation-rule locks

This family remains independently buildable with `lake build A12Kernel.Conformance.ValidationRule.Once`; the validation-rule conformance module is only its import umbrella.
-/

namespace A12Kernel.Conformance.ValidationRule.Once

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

private def sectionsAmountStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections", starred := true }]
    field := "OuterAmount" }

private def onceCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let source ←
    (elaborateNumberEntitySource ordinaryIterationModel ["Order"] {
      first := .star sectionsAmountStar
      rest := []
    }).toOption
  let core : OrderedNumericComparison ordinaryIterationModel := {
    op := .ordinary .less
    left := .atom (.aggregate .minimum source)
    right := .literal { value := 5, authoredScale := 0 }
  }
  let checked ←
    if hCore : core.wellFormedInBool ["Order"] .sameGroupAddressed = true then
      some {
        rowGroup := ["Order"]
        operandScope := .sameGroupAddressed
        core
        modelWellFormed := by native_decide
        wellFormed := hCore
      }
    else
      none
  (CheckedValidationCondition.fromOrderedNumeric checked).toOption

private def onceRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← onceCondition?
  (assembleResolvedValidationRule ordinaryIterationModel condition
    outerAmount.id "once" .error { parts := [] }).toOption

private def rootContentData : DocumentData :=
  { instantiatedRows := []
    cells := [classifiedCell baseAmount.id [] "1" (.parsed (.num 1))] }

private def emptyData : DocumentData :=
  { instantiatedRows := [], cells := [] }

private def rowOnlyData : DocumentData :=
  { instantiatedRows := [{ group := 10, path := [1] }], cells := [] }

private def rejectedRootData : DocumentData :=
  { instantiatedRows := []
    cells := [classifiedCell baseAmount.id [] "bad" (.rejected .malformed)] }

private def snapshot? (data : DocumentData) :
    Option (OrdinaryRuleIterationPlan × Env × Verdict × Option MessagePointer) := do
  let rule ← onceRule?
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let result ← (rule.evalOrdinaryOnceFull checked).toOption
  pure (rule.ordinaryIterationPlan, result.1, result.2.verdict,
    result.2.message?.map (·.errorAddress))

private def rootRelevant : ValidationRelevanceScope :=
  .partialSet [{ path := ["Order"], indices := [.concrete 1] }]

private def errorRowOnly : ValidationRelevanceScope :=
  .partialSet [{
    path := outerAmount.path
    indices := [.concrete 1, .concrete 1, .concrete 1]
  }]

private def otherErrorRowOnly : ValidationRelevanceScope :=
  .partialSet [{
    path := outerAmount.path
    indices := [.concrete 1, .concrete 2, .concrete 1]
  }]

private def partialSnapshot? (scope : ValidationRelevanceScope) :
    Option PartialOnceRuleOutcome := do
  let rule ← onceRule?
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let checked ← (checkDocument prepared "en_US" emptyData).toOption
  (rule.evalOrdinaryOncePartial checked scope).toOption

/- A star-only rule has no per-row scope, but its repeatable error declaration yields an explicit once plan pinned to row 1. Root value-content admits the evaluation even though no physical repeatable row or target cell exists. -/
example :
    snapshot? rootContentData =
      some (
        .once [10],
        [(10, 1)],
        .fired .omission,
        some (MessagePointer.ofCellAddr {
          field := outerAmount.id
          path := [1]
        })) := by
  native_decide

/- The same synthetic frame remains content-gated in full validation. Neither physical repeatable-row existence nor a rejected root cell substitutes for admitted root value-content, and constructing the address never inserts a row into the immutable document. -/
example :
    (snapshot? emptyData ==
      some (.once [10], [(10, 1)], .notFired, none)) = true ∧
    (snapshot? rowOnlyData ==
      some (.once [10], [(10, 1)], .notFired, none)) = true ∧
    (snapshot? rejectedRootData ==
      some (.once [10], [(10, 1)], .notFired, none)) = true := by
  native_decide

/- Partial admission bypasses full root-content gating when the error path is relevant below the zero levels bound by the once plan. Relevance at either concrete error row admits the row-1 pointer; neither concrete selector establishes the all-rows extent needed by the star aggregate, so both controls evaluate UNKNOWN rather than becoming rule skips. -/
example :
    (partialSnapshot? rootRelevant ==
      some (
        .evaluated [(10, 1)] (.fired {
          errorAddress := MessagePointer.ofCellAddr {
            field := outerAmount.id
            path := [1]
          }
          errorCode := "once"
          severity := .error
          messageType := .omission
          text := { text := "" }
        }))) = true ∧
    partialSnapshot? (.partialSet []) =
      some .skipped ∧
    partialSnapshot? errorRowOnly =
      some (.evaluated [(10, 1)] .unknown) ∧
    partialSnapshot? otherErrorRowOnly =
      some (.evaluated [(10, 1)] .unknown) := by
  native_decide

end A12Kernel.Conformance.ValidationRule.Once
