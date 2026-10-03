import A12Kernel.Elaboration.ComputationNumericGuard
import A12Kernel.Conformance.NumericComputation.Support

namespace A12Kernel.Conformance.ComputationNumericGuard

open A12Kernel

private def number : FieldKind := .number { scale := 0, signed := true }

private def model : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["Root"], name := "A", policy := { kind := number } },
      { id := 1, groupPath := ["Root"], name := "B", policy := { kind := number } },
      { id := 2, groupPath := ["Root"], name := "T", policy := { kind := number } },
      { id := 3, groupPath := ["Root"], name := "Text", policy := { kind := .string } }] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def sumGuard : SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate :=
  .numeric {
    op := .ordinary .greater
    left := .atom (.numeric (.aggregate .sum {
      first := .field (path "A"), rest := [.field (path "B")] }))
    right := .literal { value := 0, authoredScale := 0 } }

private def read (first second : RawCell) : ScalarComputationContext :=
  { read := fun field => formalCheck { kind := number }
      (if field == 0 then first else if field == 1 then second else .empty) }

private def result (surface : SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate)
    (context : ScalarComputationContext) : Option ComputationConditionResult := do
  let checked ← (model.elaborateCheckedComputationCondition ["Root"] ["Root"] surface).toOption
  (checked.evalChecked context).toOption

example :
    result sumGuard (read (.parsed (.num 2)) .empty) = some .holds ∧
      result sumGuard (read .empty .empty) = some .notTrue ∧
      result sumGuard (read (.rejected .malformed) (.parsed (.num 2))) =
        some (.poison .malformed) := by
  native_decide

example :
    result (.and (.fieldFilled (path "A")) sumGuard)
      (read .empty (.rejected .malformed)) = some .notTrue ∧
      result (.and sumGuard (.fieldFilled (path "A")))
        (read .empty (.rejected .malformed)) = some (.poison .malformed) := by
  native_decide

example :
    (model.elaborateCheckedComputationCondition ["Root"] ["Root"] sumGuard).toOption.map
      (fun guard => (guard.referencesField 0, guard.referencesField 1,
        guard.referencesField 2, guard.forbidsTarget 0)) = some (true, true, false, true) := by
  native_decide

private def missingNumericGuardDiagnostic : Option KernelStaticDiagnostic :=
  match model.elaborateCheckedComputationCondition ["Root"] ["Root"] (.numeric {
      op := .ordinary .greater
      left := .atom (.numeric (.field (path "Missing")))
      right := .literal { value := 0, authoredScale := 0 } }) with
  | .ok _ => none
  | .error error => (NumericComputationTableElabError.precondition 1 error).diagnostic?

example : missingNumericGuardDiagnostic = some .invalidEntity := by native_decide

namespace Addressed

open A12Kernel.Conformance.NumericComputation.Support

private def filterGuard : SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate :=
  .numeric {
    op := .ordinary .greater
    left := surfaceRepeatableFirstFilled
    right := .literal { value := 4, authoredScale := 0 } }

private def filterInput : NumericComputationEvaluationContext :=
  firstFilledContext (checkedNumber (.parsed (.num 1)))
    (numberCells3 (.parsed (.num 1)) .empty .empty)
    (numberCells3 (.parsed (.num 5)) .empty .empty)

private def filterResult : Option ComputationConditionResult := do
  let guard ← (A12Kernel.Conformance.NumericComputation.Support.model.elaborateCheckedComputationCondition
    ["Root"] ["Root"] filterGuard).toOption
  (guard.evalCheckedIn filterInput).toOption

private def filterTableResult : Option NumericTargetCheckResult := do
  let guard ← (A12Kernel.Conformance.NumericComputation.Support.model.elaborateCheckedComputationCondition
    ["Root"] ["Root"] filterGuard).toOption
  let operation ← (elaborateNumericTargetComputationOperation
    A12Kernel.Conformance.NumericComputation.Support.model ["Root"] targetId
    (.literal { value := 2, authoredScale := 0 })).toOption
  let table ← (certifyNumericComputationTable [{ precondition := guard, operation }]).toOption
  (table.evaluateIn filterInput).toOption

example : filterResult = some .holds ∧
    filterTableResult = some (.supported (.accepted { unscaled := 2, scale := 0 })) := by
  native_decide

end Addressed

end A12Kernel.Conformance.ComputationNumericGuard
