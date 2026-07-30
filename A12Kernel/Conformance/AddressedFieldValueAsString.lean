import A12Kernel.Elaboration.StringComputationRunApplication

/-! # Addressed `FieldValueAsString` locks

The first lock requires the existing String result and application boundary to preserve exact repeatable target addresses before the checked same-scope operation is added.
-/

namespace A12Kernel.Conformance.AddressedFieldValueAsString

open A12Kernel

private def firstTarget : CellAddr := { field := 2, path := [1] }

private def secondTarget : CellAddr := { field := 2, path := [2] }

private def value250 : StoredString := ⟨"250", by decide⟩

private def valueStale : StoredString := ⟨"stale", by decide⟩

private def addressedView :
    StringComputationRunView FormalCause CellAddr :=
  StringComputationRunView.fromSourcedOutcomes
    ([] : List FormalCause)
    [
      {
        targetField := firstTarget
        outcome := .accepted value250
        source := .absent
      },
      {
        targetField := secondTarget
        outcome := .noValue
        source := .presentValue valueStale
      }
    ]

/- Exact target keys survive source-relative classification and retained-action application. -/
example : (do
    let destination : StringComputationDestination CellAddr :=
      fun _ => .absent
    let applied ← (addressedView.applyTo destination).toOption
    pure (addressedView.withChanges.map (·.targetField),
      addressedView.cleared, applied firstTarget, applied secondTarget)) =
    some ([firstTarget], [secondTarget], .presentValue value250,
      .presentEmpty) := by
  native_decide

end A12Kernel.Conformance.AddressedFieldValueAsString
