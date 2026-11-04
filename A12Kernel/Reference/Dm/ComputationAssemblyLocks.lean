import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ComputationAssemblyLocks

open Lean

private inductive InputKind where
  | accepted | rejected (code : String) | malformed
  deriving DecidableEq

private def rejectedWith (code : String) : RegisteredCustomRejection := { projectCode := code }
/-- The former test-range code and an ordinary one: the twin pair every rejection row is asserted over. -/
private def twinCodes : List String := ["testIDNummer", "CODE_BAD"]
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
      | .rejected code => some (rejectedWith code)
    else if name == "Copy" then some targetRejection
    else if value == "audited" then none else some { projectCode := "AUDIT_NOT_COMPLETED" } }

private structure Summary where
  result : Except (ComputationFormalInputRunFault MixedComputationPlanFault) MixedComputationCheckedResult
  reader : Lowering (List ComputedOutcome)
  execution : Except MixedComputationPlanFault (List MixedComputationOutcome)

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
    execution := plan.execute world prepared.patterns staged.preliminary.computationInput }

private def finding (row : Nat) (cause : FormalCause) : ComputationFormalInputFinding := {
  address := { field := 1, path := [row] }, cause }

private def copyOutcome (row : Nat) (outcome : StringTargetOutcome) : MixedComputationOutcome :=
  .document { field := 2, path := [row] } (.string outcome)

private def readerChanges (scenario : Option Summary) : Option (List (String × String)) := do
  let scenario ← scenario
  let changes ← scenario.reader.toOption
  pure (changes.map fun change => (change.pointer, change.outcome))

example : (summary .accepted true).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.poison .duplicateIndex), copyOutcome 2 (.poison .duplicateIndex)]
    formalErrorsInOperands := [finding 1 .duplicateIndex, finding 2 .duplicateIndex] }) ∧
    readerChanges (summary .accepted true) = some [
      ("Form/Rows/Copy", "cleared"), ("Form/Rows[2]/Copy", "cleared")] := by native_decide

private def clearedCopies : List (String × String) :=
  [("Form/Rows/Copy", "cleared"), ("Form/Rows[2]/Copy", "cleared")]

private def rejectedResult (code : String) : MixedComputationCheckedResult := {
  outcomes := [copyOutcome 1 (.poison (.registeredCustomValidation (rejectedWith code))),
    copyOutcome 2 (.poison (.registeredCustomValidation (rejectedWith code)))]
  formalErrorsInOperands := [finding 1 (.registeredCustomValidation (rejectedWith code)),
    finding 2 (.registeredCustomValidation (rejectedWith code))] }

private def copiesWithAudit (code : String) : List MixedComputationOutcome :=
  (rejectedResult code).outcomes ++ [.string 3 (.accepted ⟨"audited", by decide⟩)]

/- Unmeasured on 31.1.1. A rejected operand poisons the dependent copy and clears it in the reader route, and a `testIDNummer` rejection does so exactly as the ordinary code does. -/
example : twinCodes.all (fun code =>
    (summary (.rejected code)).map (·.result.toOption) == some (some (rejectedResult code)) &&
    readerChanges (summary (.rejected code)) == some clearedCopies) = true := by native_decide

/- Locked: a12-dmkits `ComputationDiagnosticAssemblyLawsTest` at `1124b523f`, kernel 31.1.1. Equal rejected index cells keep the rejection as their one formal-input finding (validation still reports `uniqueIndex` beside it, locked in `MessageCacheOrder`), so result assembly completes with the same result as distinct keys; the ordinary code behaves identically. -/
example : twinCodes.all (fun code =>
    (summary (.rejected code) true).map (·.result.toOption) == some (some (rejectedResult code)) &&
    readerChanges (summary (.rejected code) true) == some clearedCopies) = true := by native_decide

example : (summary .malformed).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.poison .malformed), copyOutcome 2 (.poison .malformed)]
    formalErrorsInOperands := [finding 1 .malformed, finding 2 .malformed] }) ∧
    readerChanges (summary .malformed) = some [
      ("Form/Rows/Copy", "cleared"), ("Form/Rows[2]/Copy", "cleared")] := by native_decide

/- Unmeasured on 31.1.1. A rejected field outside the computation's operand union contributes no formal-input finding, for `testIDNummer` as for an ordinary code. -/
example : twinCodes.all (fun code =>
    (summary (.rejected code) true false true).map (·.result.toOption) == some (some {
      outcomes := [.string 3 (.accepted ⟨"audited", by decide⟩)]
      formalErrorsInOperands := [] }) &&
    readerChanges (summary (.rejected code) true false true) ==
      some [("Form/Audit", "value audited")]) = true := by native_decide

example : (summary .accepted false true false true).map (·.result.toOption) = some (some {
    outcomes := [copyOutcome 1 (.errored ⟨"ABCD", by decide⟩ (.custom targetRejection)),
      copyOutcome 2 (.errored ⟨"EFGH", by decide⟩ (.custom targetRejection))]
    formalErrorsInOperands := [] }) ∧
    readerChanges (summary .accepted false true false true) = some [
      ("Form/Rows/Copy", "errored ABCD"), ("Form/Rows[2]/Copy", "errored EFGH")] := by native_decide

/- Unmeasured on 31.1.1. Beside an independent computation, equal rejected index cells still contribute only their rejection: the copies are poisoned by the custom finding in both the assembled result and the staged execution. -/
example : twinCodes.all (fun code =>
    (summary (.rejected code) true true true).map (fun scenario =>
      (scenario.result.toOption.map (·.outcomes), scenario.execution.toOption)) ==
      some (some (copiesWithAudit code), some (copiesWithAudit code))) = true := by
  native_decide

end A12Kernel.Dm.ComputationAssemblyLocks
