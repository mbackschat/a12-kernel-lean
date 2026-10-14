import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ComputationAssemblyLocks

open Lean

private inductive InputKind where
  | accepted | reported | rejected | malformed
  deriving DecidableEq

private def rejection : RegisteredCustomRejection := { projectCode := "CODE_BAD" }
private def report : RegisteredCustomRejection := { projectCode := "testIDNummer" }
private def targetRejection : RegisteredCustomRejection := { projectCode := "TARGET_BAD" }

private def model (kind : InputKind) (rejectTarget : Bool) : FlatModel := {
  fields := [
    { id := 1, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := if kind == .malformed then .number { scale := 0, signed := true } else .string }
      customType := if kind == .malformed then none else some { name := "Code" } },
    { id := 2, name := "Copy", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .string }, customType := if rejectTarget then some { name := "Copy" } else none },
    { id := 3, name := "Audit", groupPath := ["Form"], policy := { kind := .string }
      customType := some { name := "Audit" } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 1 }] }

private def world (kind : InputKind) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name => some fun value _ =>
    if name == "Code" then match kind with
      | .accepted | .malformed => none
      | .reported => some report
      | .rejected => some rejection
    else if name == "Copy" then some targetRejection
    else if value == "audited" then none else some { projectCode := "AUDIT_NOT_COMPLETED" } }

private structure Summary where
  result : Except (ComputationFormalInputRunFault MixedComputationPlanFault) MixedComputationCheckedResult
  reader : Lowering (List ComputedOutcome)
  execution : Except MixedComputationPlanFault (List MixedComputationOutcome)
  originalCopies : List String

private def summary (kind : InputKind) (same : Bool := false)
    (copy : Bool := true) (audit : Bool := false) (rejectTarget : Bool := false) : Option Summary := do
  let model := model kind rejectTarget
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let values := if kind == .malformed then ["bad", "worse"]
    else ["ABCD", if same then "ABCD" else "EFGH"]
  let rows := values.map fun text => Json.mkObj [("Code", toJson text), ("Copy", "old")]
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", Json.arr rows.toArray)])])).toOption
  if !data.refusals.isEmpty then none
  let world := world kind
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input ← (checkDocument prepared "en_US" data.data).toOption
  let copyDeclaration : DmComputation := {
    group := ["Form", "Rows"], name := "CopyCode", targetRelPath := "../Copy"
    commonPrecondition := none
    alternatives := [{
      precondition := none
      operation := if kind == .malformed then "FieldValueAsString(Code)" else "[Code]" }]
    errorCodesToSuppress := [] }
  let auditDeclaration : DmComputation := {
    group := ["Form"], name := "Audit", targetRelPath := "../Audit"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "\"audited\"" }]
    errorCodesToSuppress := [] }
  let declarations := (if copy then [copyDeclaration] else []) ++ (if audit then [auditDeclaration] else [])
  let lowered ← declarations.mapM fun declaration =>
    (lowerComputation model .english declaration).toOption.map (·.2)
  let steps := lowered.map (·.toMixedStep builtinStringPatternCompiler)
  let plan ← (certifyAuthoredMixedComputationPlan steps).toOption
  let inputPlan ← plan.formalInputPlan.toOption
  let staged ← (inputPlan.prepare input).toOption
  pure {
    result := plan.executeResultWithFormalInputs world prepared.patterns input
    reader := runComputations world prepared input lowered
    execution := plan.execute world prepared.patterns staged.preliminary.computationInput
    originalCopies := input.source.cells.filterMap fun cell =>
      if cell.address.field == 2 then some cell.stored else none }

private def finding (row : Nat) (cause : FormalCause) : ComputationFormalInputFinding := {
  address := { field := 1, path := [row] }, cause }

private def copyOutcome (row : Nat) (outcome : StringTargetOutcome) : MixedComputationOutcome :=
  .document { field := 2, path := [row] } (.string outcome)

private def readerChanges (scenario : Option Summary) : Option (List (String × String)) := do
  let scenario ← scenario
  let changes ← scenario.reader.toOption
  pure (changes.map fun change => (change.pointer, change.outcome))

private def collisionGuard (scenario : Option Summary) : Option Bool := do
  let scenario ← scenario
  match scenario.result, scenario.reader with
  | .error (.assembly findings (.duplicatePointer pointer)), .error refusal =>
      pure (findings == [finding 1 (.registeredCustomValidation report),
        finding 2 (.registeredCustomValidation report), finding 1 .duplicateIndex,
        finding 2 .duplicateIndex] &&
        [MessagePointer.ofCellAddr { field := 1, path := [1] },
          MessagePointer.ofCellAddr { field := 1, path := [2] }].contains pointer &&
        refusal.construct == "ComputationRun" &&
        refusal.detail == oneLine ((repr (ComputationFormalInputRunFault.assembly findings
          (.duplicatePointer pointer) : ComputationFormalInputRunFault MixedComputationPlanFault)).pretty 100000) &&
        (scenario.result.toOption.bind fun result => some result.outcomes).isNone &&
        scenario.originalCopies == ["old", "old"])
  | _, _ => pure false

example : collisionGuard (summary .reported true) = some true := by native_decide

example : (summary .accepted true).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.poison .duplicateIndex), copyOutcome 2 (.poison .duplicateIndex)]
    formalErrorsInOperands := [finding 1 .duplicateIndex, finding 2 .duplicateIndex] }) ∧
    readerChanges (summary .accepted true) = some [
      ("Form/Rows/Copy", "cleared"), ("Form/Rows[2]/Copy", "cleared")] := by native_decide

example : (summary .reported).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.accepted ⟨"ABCD", by decide⟩),
      copyOutcome 2 (.accepted ⟨"EFGH", by decide⟩)]
    formalErrorsInOperands := [finding 1 (.registeredCustomValidation report),
      finding 2 (.registeredCustomValidation report)] }) ∧
    readerChanges (summary .reported) = some [
      ("Form/Rows/Copy", "value ABCD"), ("Form/Rows[2]/Copy", "value EFGH")] := by native_decide

example : (summary .rejected).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.poison (.registeredCustomValidation rejection)),
      copyOutcome 2 (.poison (.registeredCustomValidation rejection))]
    formalErrorsInOperands := [finding 1 (.registeredCustomValidation rejection),
      finding 2 (.registeredCustomValidation rejection)] }) ∧
    readerChanges (summary .rejected) = some [
      ("Form/Rows/Copy", "cleared"), ("Form/Rows[2]/Copy", "cleared")] := by native_decide

example : (summary .malformed).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.poison .malformed), copyOutcome 2 (.poison .malformed)]
    formalErrorsInOperands := [finding 1 .malformed, finding 2 .malformed] }) ∧
    readerChanges (summary .malformed) = some [
      ("Form/Rows/Copy", "cleared"), ("Form/Rows[2]/Copy", "cleared")] := by native_decide

example : (summary .reported true false true).map (·.result.toOption) = some (some {
    outcomes := [.string 3 (.accepted ⟨"audited", by decide⟩)]
    formalErrorsInOperands := [] }) ∧
    readerChanges (summary .reported true false true) = some [("Form/Audit", "value audited")] := by native_decide

example : (summary .accepted false true false true).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.errored ⟨"ABCD", by decide⟩ (.custom targetRejection)),
      copyOutcome 2 (.errored ⟨"EFGH", by decide⟩ (.custom targetRejection))]
    formalErrorsInOperands := [] }) ∧
    readerChanges (summary .accepted false true false true) = some [
      ("Form/Rows/Copy", "errored ABCD"), ("Form/Rows[2]/Copy", "errored EFGH")] := by native_decide

example : collisionGuard (summary .reported true true true) = some true ∧
    (summary .reported true true true).map (·.execution.toOption) = some (some [
      copyOutcome 1 (.poison .duplicateIndex), copyOutcome 2 (.poison .duplicateIndex),
      .string 3 (.accepted ⟨"audited", by decide⟩)]) := by native_decide

end A12Kernel.Dm.ComputationAssemblyLocks
