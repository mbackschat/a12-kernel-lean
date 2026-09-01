import A12Kernel.Elaboration.ValidationCondition

/-! # Nonrepeatable group terminals below starred ancestors -/

namespace A12Kernel.Conformance.StarredGroupPresence

open A12Kernel

private def detailValue : FlatFieldDecl :=
  { id := 1
    groupPath := ["Order", "Sections", "Items", "Details"]
    name := "Value"
    policy := { kind := .string }
    repeatableScope := [10, 20] }

private def optionValue : FlatFieldDecl :=
  { id := 2
    groupPath := ["Order", "Sections", "Items", "Details", "Options"]
    name := "Value"
    policy := { kind := .string }
    repeatableScope := [10, 20, 30] }

private def model : FlatModel :=
  { fields := [detailValue, optionValue]
    repeatableGroups := [
      { level := 10
        path := ["Order", "Sections"]
        repeatability := some 2 },
      { level := 20
        path := ["Order", "Sections", "Items"]
        repeatability := some 3 },
      { level := 30
        path := ["Order", "Sections", "Items", "Details", "Options"]
        repeatability := some 2 }
    ] }

private def detailsStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections", starred := true },
      { name := "Items", starred := true },
      { name := "Details" }
    ] }

private def condition?
    (operator : GroupFillQuantifier) :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromGroupList model ["Order"] operator
    [detailsStar]).toOption

private def world : World where
  now := { epochMillis := 0 }

private def checkedDocument? (data : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" data).toOption

private inductive EvaluationSnapshot where
  | verdict (value : Verdict)
  | structuralFailure
  deriving DecidableEq

private def evaluate? (operator : GroupFillQuantifier)
    (data : DocumentData) : Option EvaluationSnapshot := do
  let condition ← condition? operator
  let document ← checkedDocument? data
  pure <| match condition.core.evalAddressed {
    scalar := {
      fields := model.checkContext { read := fun _ => .empty }
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  } with
    | .ok verdict => .verdict verdict
    | .error _ => .structuralFailure

private def section1 : RowAddr := { group := 10, path := [1] }
private def item11 : RowAddr := { group := 20, path := [1, 1] }
private def item12 : RowAddr := { group := 20, path := [1, 2] }
private def item13 : RowAddr := { group := 20, path := [1, 3] }
private def item14 : RowAddr := { group := 20, path := [1, 4] }
private def option111 : RowAddr := { group := 30, path := [1, 1, 1] }

private def emptyDetails : DocumentData :=
  { instantiatedRows := [section1, item11]
    cells := [] }

private def filledSecondDetails : DocumentData :=
  { instantiatedRows := [section1, item11, item12]
    cells := [{
      address := { field := detailValue.id, path := [1, 2] }
      stored := "filled"
      raw := .parsed (.str "filled")
    }] }

private def repeatableDescendantOnly : DocumentData :=
  { instantiatedRows := [section1, item11, option111]
    cells := [] }

private def malformedOnly : DocumentData :=
  { instantiatedRows := [section1, item11]
    cells := [{
      address := { field := detailValue.id, path := [1, 1] }
      stored := "malformed"
      raw := .rejected .malformed
    }] }

private def filledWithMalformedPeer : DocumentData :=
  { instantiatedRows := [section1, item11, item12]
    cells := [{
      address := { field := detailValue.id, path := [1, 1] }
      stored := "malformed"
      raw := .rejected .malformed
    }, {
      address := { field := detailValue.id, path := [1, 2] }
      stored := "filled"
      raw := .parsed (.str "filled")
    }] }

private def overLimitDetailsOnly : DocumentData :=
  { instantiatedRows := [section1, item11, item12, item13, item14]
    cells := [{
      address := { field := detailValue.id, path := [1, 4] }
      stored := "over-limit"
      raw := .parsed (.str "over-limit")
    }] }

/- An instantiated starred ancestor does not by itself fill its nonrepeatable terminal. -/
example :
    evaluate? .atLeastOneGroupFilled emptyDetails = some (.verdict .unknown) ∧
    evaluate? .noGroupFilled emptyDetails =
      some (.verdict (.fired .omission)) := by
  native_decide

/- The terminal product admits scalar content and instantiated repeatable descendants, but leaves malformed-only content unavailable. -/
example :
    evaluate? .atLeastOneGroupFilled filledSecondDetails =
      some (.verdict (.fired .value)) ∧
    evaluate? .noGroupFilled filledSecondDetails = some (.verdict .unknown) ∧
    evaluate? .atLeastOneGroupFilled repeatableDescendantOnly =
      some (.verdict (.fired .value)) ∧
    evaluate? .atLeastOneGroupFilled malformedOnly =
      some (.verdict .unknown) ∧
    evaluate? .noGroupFilled malformedOnly = some (.verdict .unknown) ∧
    evaluate? .atLeastOneGroupFilled filledWithMalformedPeer =
      some (.verdict (.fired .value)) ∧
    evaluate? .noGroupFilled filledWithMalformedPeer =
      some (.verdict .unknown) := by
  native_decide

/- A descendant present only below an over-limit parent is outside both threshold quantifiers.
   The empty in-capacity prefix is the separator: a physical-topology account would make the
   positive form fire and the zero form stay silent. Kernel-locked at a12-dmkits `abe50e717`. -/
example :
    evaluate? .atLeastOneGroupFilled overLimitDetailsOnly =
      some (.verdict .unknown) ∧
    evaluate? .noGroupFilled overLimitDetailsOnly =
      some (.verdict (.fired .omission)) := by
  native_decide

end A12Kernel.Conformance.StarredGroupPresence
