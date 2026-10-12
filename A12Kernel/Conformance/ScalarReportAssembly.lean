import A12Kernel.Elaboration.ScalarComputationFormalInput
import A12Kernel.Elaboration.NumericComputation.FormalInput

namespace A12Kernel.Conformance.ScalarReportAssembly

open A12Kernel

private def inputStringId : FieldId := 0
private def inputNumberId : FieldId := 1
private def firstNumberId : FieldId := 3

private def model : FlatModel := {
  fields := [
    { id := 0, name := "InputString", groupPath := ["Form"], policy := { kind := .string },
      stringPolicy := { maxLength := some 15 }, stringPatternSource := some "[0-9]+" },
    { id := 1, name := "InputNumber", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "FirstNumber", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }] }

private def world : World := { now := { epochMillis := 0 } }
private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get (by native_decide)

private def literalNumber (value : Rat) : AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def numberTable? (target : FieldId)
    (rows : List (Option (CheckedComputationCondition model) × AuthoredNumericExpr SurfaceNumericAtom))
    (suppressExactScaleWarning : Bool := false) :
    Option (CheckedNumericComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← (elaborateNumericTargetComputationOperation model ["Form"] target expression suppressExactScaleWarning).toOption
    pure ({ precondition := guard, operation } :
      CheckedComputationAlternative model (CheckedNumericTargetComputationOperation model))
  (certifyNumericComputationTable alternatives).toOption

private def firstNumberValue :=
  (numberTable? firstNumberId [(none, literalNumber 7)]).get (by native_decide)

private def firstNumberUnreadInputString :=
  (numberTable? firstNumberId [
    (some (.fieldNotFilled inputNumberId), literalNumber 3),
    (some (.fieldNotFilled inputNumberId), .atom (.fieldValueAsNumber (.direct { base := .relative 0, groups := [], field := "InputString" })))]).get (by native_decide)

private def malformedStringCell (field : FieldId) : ClassifiedCellInput := {
  address := { field, path := [] }, stored := "bad", raw := .rejected .malformed }

private def checkedDocument (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption

private def formalFinding (field : FieldId) (cause : FormalCause) : ComputationFormalInputFinding := {
  address := { field, path := [] }, cause }

private def suppliedReport (field : FieldId) (code : String) : ComputationFormalMessage Unit := {
  pointer := MessagePointer.ofCellAddr { field, path := [] }
  errorCode := code, messageType := .value, payload := () }

private def suppliedResult? (table : CheckedNumericComputationTable model)
    (messages : List (ComputationFormalMessage Unit)) (cells : List ClassifiedCellInput := []) :
    Option (Except ScalarComputationFormalInputRunFault (ScalarComputationFormalInputRunView model Unit Unit)) := do
  let run ← (certifyScalarComputationRun [.number table]).toOption
  let input ← checkedDocument cells
  pure (run.executeResultWithFormalInputs world prepared.patterns input (fun _ => ()) messages [])

example : [firstNumberId, inputNumberId].all (fun field =>
    match suppliedResult? firstNumberValue [suppliedReport field "A", suppliedReport field "B"] with
    | some (.error (.assembly [] (.duplicatePointer pointer))) =>
        pointer == MessagePointer.ofCellAddr { field, path := [] }
    | _ => false) = true := by native_decide

private def valuelessNumber := (numberTable? firstNumberId [
  (none, .binary .divide (literalNumber 1) (literalNumber 0))] true).get (by native_decide)

example : (match suppliedResult? valuelessNumber [suppliedReport firstNumberId "SUPPLIED"] with
    | some (.error (.assembly [] (.duplicatePointer pointer))) =>
        pointer == MessagePointer.ofCellAddr { field := firstNumberId, path := [] }
    | _ => false) = true ∧
    (match suppliedResult? firstNumberUnreadInputString [suppliedReport inputStringId "SUPPLIED"]
        [malformedStringCell inputStringId] with
    | some (.error (.assembly findings (.duplicatePointer pointer))) =>
        findings == [formalFinding inputStringId .malformed] &&
          pointer == MessagePointer.ofCellAddr { field := inputStringId, path := [] }
    | _ => false) = true := by native_decide

example : (do
    let result ← suppliedResult? firstNumberValue [suppliedReport firstNumberId "SUPPLIED"]
    let view ← result.toOption
    pure (view.scalar.number.withoutErrors.map (fun value => (value.targetField, value.value)),
      view.scalar.number.formalErrorsInOperands)) = some ([
        (firstNumberId, { unscaled := 7, scale := 0 })], []) ∧
    (do
      let result ← suppliedResult? valuelessNumber []
      let view ← result.toOption
      pure view.scalar.number.formalErrorsInOperands) =
      some [suppliedReport firstNumberId berechnungsWertFehler] := by native_decide


end A12Kernel.Conformance.ScalarReportAssembly

namespace A12Kernel.Conformance.GuardReportAssembly

private def model : FlatModel := {
  fields := [
    { id := 90, name := "Code", groupPath := ["Form", "Box", "Rows"], repeatableScope := [90],
      policy := { kind := .string }, customType := some { name := "Code" } },
    { id := 91, name := "Target", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 92, name := "Gate", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 90, path := ["Form", "Box", "Rows"], repeatability := some 2, indexField := some 90 }] }
private def world : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun _ => some fun _ _ => some { projectCode := "testIDNummer" } }
private def boxGuard : CheckedComputationCondition model := .leaf (.groupPresence .filled {
  reference := { path := ["Form", "Box"], origin := .path, boundRepeatableScope := [] }
  content := model.computationGroupSource ["Form", "Box"]
  members := (model.groupSubtreeFields ["Form", "Box"]).map (·.id) })
private def table? : Option (CheckedNumericComputationTable model) :=
  (elaborateNumericTargetComputationTable model ["Form"] 91 [
    (some (.fieldNotFilled 92), .literal { value := 1, authoredScale := 0 }),
    (some boxGuard, .literal { value := 2, authoredScale := 0 })]).toOption

private def results? (same : Bool) : Option (Bool × Bool × Nat ×
    Option (List (FieldId × Int × Nat)) × Option (List (FieldId × Int × Nat))) := do
  let table ← table?
  let numeric ← (certifyNumericComputationRun [table]).toOption
  let scalar ← (certifyScalarComputationRun [.number table]).toOption
  let patterns ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input ← (checkDocument patterns "en_US" {
    instantiatedRows := [{ group := 90, path := [1] }, { group := 90, path := [2] }]
    cells := [
      { address := { field := 90, path := [1] }, stored := "ABCD", raw := .parsed (.str "ABCD") },
      { address := { field := 90, path := [2] }, stored := if same then "ABCD" else "EFGH",
        raw := .parsed (.str (if same then "ABCD" else "EFGH")) }] }).toOption
  let plan ← numeric.formalInputPlan.toOption
  let prepared ← (plan.prepare input).toOption
  let numericResult := numeric.executeResultWithFormalInputs world input
  let scalarResult := scalar.executeResultWithFormalInputs world patterns.patterns input (fun _ => ()) [] ([] : List Unit)
  let numericFailed := match numericResult with
    | .error (.assembly _ _) => true
    | _ => false
  let scalarFailed := match scalarResult with
    | .error (.assembly _ _) => true
    | _ => false
  pure (numericFailed, scalarFailed, prepared.formalErrorsInOperands.length,
    numericResult.toOption.map fun view => view.numeric.withoutErrors.map fun entry =>
      (entry.targetField, entry.value.unscaled, entry.value.scale),
    scalarResult.toOption.map fun view => view.scalar.number.withoutErrors.map fun entry =>
      (entry.targetField, entry.value.unscaled, entry.value.scale))

example : (results? false == some (false, false, 2,
    some [(91, 1, 0)], some [(91, 1, 0)])) = true := by native_decide
example : (results? true == some (true, true, 4, none, none)) = true := by native_decide

end A12Kernel.Conformance.GuardReportAssembly
