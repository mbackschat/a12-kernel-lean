import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ComputationOverlapLocks

private def rangeField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Form"], policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def numberField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Form"]
  policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [rangeField 1 "A", rangeField 2 "B", rangeField 3 "C",
    numberField 4 "Out", numberField 5 "Dependent", rangeField 12 "Fresh",
    { rangeField 6 "R" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { numberField 7 "Gate" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { numberField 13 "Out" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { numberField 14 "Dependent" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { rangeField 8 "R" with groupPath := ["Form", "Pool"] },
    { rangeField 9 "S" with groupPath := ["Form", "Pool"] },
    { rangeField 10 "R" with groupPath := ["Form", "RangeRows"], repeatableScope := [20] },
    { rangeField 11 "S" with groupPath := ["Form", "RangeRows"], repeatableScope := [20] }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3 },
    { level := 20, path := ["Form", "RangeRows"], repeatability := some 3 }] }

private structure Inputs where
  rows : List Lean.Json := []
  rangeRows : List Lean.Json := []
  pool : List (String × Lean.Json) := []
  yearless : Bool := false
  producer : Bool := false
  gateProducer : Bool := false
  rowTarget : Bool := false
  stringTarget : Bool := false

private def run (guard a b c : String) (inputs : Inputs := {}) : Option (List String) := do
  let model := if inputs.yearless then { model with fields := model.fields.map fun field =>
      if field.policy.kind == .dateRange then
        { field with dateRangePolicy := some { format := "MM-dd", separator := "/" } }
      else field } else model
  let model := if inputs.stringTarget then { model with fields := model.fields.map fun field =>
      if field.id == 4 then { field with policy := { kind := .string } } else field } else model
  let dm : DmModel := {
    flat := model, computations := [], rules := []
    conditionLanguage := "en_US", refusals := [] }
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("A", .str a), ("B", .str b), ("C", .str c),
    ("Fresh", .str "2024-03-01/2024-03-10"),
    ("Out", .str "99"), ("Dependent", .str "99"),
    ("Rows", .arr inputs.rows.toArray), ("RangeRows", .arr inputs.rangeRows.toArray),
    ("Pool", Lean.Json.mkObj inputs.pool)])]
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let consumer : DmComputation := {
    name := "Consumer", group := ["Form"]
    targetRelPath := if inputs.rowTarget then "../Rows/Out" else "../Out"
    commonPrecondition := some guard, alternatives := [{
      precondition := none
      operation := if inputs.stringTarget then "\"yes\"" else "1" }]
    errorCodesToSuppress := [] }
  let dependent : DmComputation := {
    name := "Dependent", group := ["Form"]
    targetRelPath := if inputs.rowTarget then "../Rows/Dependent" else "../Dependent"
    commonPrecondition := none, alternatives := [{
      precondition := none
      operation := if inputs.rowTarget then "[Rows/Out] + 1"
        else if inputs.stringTarget then "Length(Out)" else "[Out] + 1" }]
    errorCodesToSuppress := [] }
  let producer : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Fresh"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "FirstFilledValue(A,C)" }]
    errorCodesToSuppress := [] }
  let gateProducer : DmComputation := {
    name := "GateProducer", group := ["Form"], targetRelPath := "../Rows/Gate"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "1" }]
    errorCodesToSuppress := [] }
  let authored := [consumer, dependent] ++ (if inputs.producer then [producer] else []) ++
    (if inputs.gateProducer then [gateProducer] else [])
  let lowered ← authored.mapM fun definition =>
    (lowerComputation model .english definition).toOption
  let results ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (results.map fun result => result.pointer ++ ":" ++ result.outcome)

private def january := "2024-01-01/2024-01-10"
private def touching := "2024-01-10/2024-01-20"
private def march := "2024-03-01/2024-03-10"

private def row (range gate : String) : Lean.Json := Lean.Json.mkObj [
  ("R", .str range), ("Gate", .str gate), ("Out", .str "99"), ("Dependent", .str "99")]

private def rangeRow (r s : String) : Lean.Json := Lean.Json.mkObj [("R", .str r), ("S", .str s)]

private def holds := some ["Form/Out:value 1", "Form/Dependent:value 2"]
private def poisoned := some ["Form/Out:cleared", "Form/Dependent:cleared"]
private def misses := some ["Form/Out:cleared", "Form/Dependent:value 1"]

example : run "DateRangesOverlap(A,B,C)" january touching "bad" =
    some ["Form/Out:value 1", "Form/Dependent:value 2"] := by native_decide

example : run "DateRangesOverlap(C,A,B)" january touching "bad" =
    some ["Form/Out:cleared", "Form/Dependent:cleared"] := by native_decide

example : run "AtLeastOneDateRangeOverlaps(A In B,C)" "" "bad" march =
    some ["Form/Out:cleared", "Form/Dependent:value 1"] := by native_decide

example : run "AtLeastOneDateRangeOverlaps(A In B,C)" january march march =
    some ["Form/Out:cleared", "Form/Dependent:value 1"] := by native_decide

example : run "AtLeastOneDateRangeOverlaps(A In B,C)" january touching "bad" = holds ∧
    run "AtLeastOneDateRangeOverlaps(C In A,B)" january touching "bad" = poisoned := by native_decide

example : run "DateRangesOverlap(Rows*/R)" january touching march
      { rows := [row january "1", row touching "1", row "bad" "1"] } = holds ∧
    run "DateRangesOverlap(Rows*/R)" january touching march
      { rows := [row "bad" "1", row january "1", row touching "1"] } = poisoned := by native_decide

example : run "DateRangesOverlap(Rows*/R Having [Rows/Gate] > 0)" january touching march
      { rows := [row "bad" "0", row january "1", row touching "1"] } = holds ∧
    run "DateRangesOverlap(Rows*/R Having [Rows/Gate] > 0)" january touching march
      { rows := [row "bad" "1", row january "1", row touching "1"] } = poisoned := by native_decide

example : run "DateRangesOverlap(Rows*/R Having [Rows/Gate] > 0)" january touching march
      { rows := [row january "1", row touching "1", row march "bad"] } = poisoned ∧
    run "AtLeastOneDateRangeOverlaps(A In Rows*/R Having [Rows/Gate] > 0)" january touching march
      { rows := [row january "1", row touching "1", row march "bad"] } = holds ∧
    run "DateRangesOverlap(Rows*/R Having [Rows/Gate] > 0)" january touching march
      { rows := [row january "1", row touching "1", row "bad" "1"] } = holds := by native_decide

example : run "AtLeastOneDateRangeOverlaps(A In Rows*/R Having [Rows/Gate] > 0)" january touching march
      { rows := [row january "1", row march "bad", row touching "1"] } = poisoned ∧
    run "AtLeastOneDateRangeOverlaps(A In Rows*/R Having [Rows/Gate] > 0)" "" touching march
      { rows := [row "bad" "bad"] } = misses := by native_decide

example : run "AtLeastOneDateRangeOverlaps(A In Pool)" january touching march
      { pool := [("R", .str january), ("S", .str "bad")] } = holds ∧
    run "AtLeastOneDateRangeOverlaps(A In Pool)" january touching march
      { pool := [("R", .str "bad"), ("S", .str january)] } = poisoned := by native_decide

example : run "AtLeastOneDateRangeOverlaps(A In RangeRows*)" january touching march
      { rangeRows := [rangeRow march january, rangeRow "bad" march] } = poisoned ∧
    run "AtLeastOneDateRangeOverlaps(A In RangeRows*)" january touching march
      { rangeRows := [rangeRow january march, rangeRow "bad" march] } = holds := by native_decide

example : run "DateRangesOverlap(A,B)" "02-01/02-29" "02-29/03-01" ""
      { yearless := true } = holds ∧
    run "AtLeastOneDateRangeOverlaps(A In B)" "02-01/02-29" "02-29/03-01" ""
      { yearless := true } = holds ∧
    run "DateRangesOverlap(A,B)" "03-01/02-01" "02-15/02-20" ""
      { yearless := true } = poisoned := by native_decide

example : run "DateRangesOverlap(Fresh,B)" january touching march { producer := true } =
    some ["Form/Fresh:value 2024-01-01/2024-01-10", "Form/Out:value 1", "Form/Dependent:value 2"] := by native_decide

example : run "AtLeastOneDateRangeOverlaps(A In Rows*/R Having [Rows/Gate] > 0)" january touching march
      { gateProducer := true, rows := [row january "bad"] } =
    some ["Form/Rows/Gate:value 1", "Form/Out:value 1", "Form/Dependent:value 2"] := by native_decide

example : run "DateRangesOverlap(Rows*/R Having [Rows/Gate] > 0)" "" "" ""
      { yearless := true, rows := [row "02-01/02-29" "1", row "02-29/03-01" "1"] } = holds ∧
    run "AtLeastOneDateRangeOverlaps(A In RangeRows*)" "02-01/02-29" "" ""
      { yearless := true, rangeRows := [rangeRow "03-01/03-10" "02-29/03-01"] } = holds := by native_decide

example : run "DateRangesOverlap(A,Rows/R)" january touching march
      { rowTarget := true, rows := [row january "1", row march "1"] } =
    some ["Form/Rows/Out:value 1", "Form/Rows[2]/Out:cleared",
      "Form/Rows/Dependent:value 2", "Form/Rows[2]/Dependent:value 1"] := by native_decide

example : run "DateRangesOverlap(A,B,C)" january touching "bad" { stringTarget := true } =
      some ["Form/Out:value yes", "Form/Dependent:value 3"] ∧
    run "DateRangesOverlap(C,A,B)" january touching "bad" { stringTarget := true } =
      some ["Form/Out:cleared", "Form/Dependent:cleared"] := by native_decide

example : run "DateRangesOverlap(Pool)" january touching march = none ∧
    run "DateRangesOverlap(A,A)" january touching march = none ∧
    run "DateRangesOverlap(A,Out)" january touching march = none ∧
    run "DateRangesOverlap(Rows*/R Having [$Out] > 0)" january touching march = none ∧
    run "AtLeastOneDateRangeOverlaps(Rows*/R In A)" january touching march = none ∧
    run "DateRangesOverlap(A,Rows/R)" january touching march = none := by native_decide

end A12Kernel.Dm.ComputationOverlapLocks
