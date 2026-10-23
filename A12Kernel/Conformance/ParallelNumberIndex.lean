import A12Kernel.Elaboration.ParallelFieldRule
import A12Kernel.Elaboration.ParallelNumericDirectRun

/-! # Numeric parallel iteration tokens and lookup identity

Kernel 30.8.1's two-stage index normalization is captured in
`evidence/kernel-30.8.1/captures/parallel-number-index-2026-10-10`.
-/

namespace A12Kernel.Conformance.ParallelNumberIndex

open A12Kernel

private def indexDecl (id level minimum : Nat) (group : String)
    (scale : Nat := 2) : FlatFieldDecl := {
  id, groupPath := ["Form", group], name := "Key", repeatableScope := [level]
  policy := { kind := .number { scale, signed := true } }
  numericTargetConstraints := { minFractionalDigits := minimum }
}

private def valueDecl (id level : Nat) (group : String) : FlatFieldDecl := {
  id, groupPath := ["Form", group], name := "Value", repeatableScope := [level]
  policy := { kind := .string }
}

private def leftGroup : RepeatableGroupDecl := {
  level := 10, path := ["Form", "Left"], repeatability := some 5, indexField := some 1
}
private def rightGroup : RepeatableGroupDecl := {
  level := 20, path := ["Form", "Right"], repeatability := some 5, indexField := some 3
}
private def model (rightMinimum : Nat := 2) (scale : Nat := 2) : FlatModel := {
  fields := [indexDecl 1 10 0 "Left" scale, valueDecl 2 10 "Left",
    indexDecl 3 20 rightMinimum "Right" scale, valueDecl 4 20 "Right"]
  repeatableGroups := [leftGroup, rightGroup]
}

private def rowCells (indexField coordinate : Nat) (key : String × Rat) :
    List ClassifiedCellInput := [
  { address := { field := indexField, path := [coordinate] },
    stored := key.1, raw := .parsed (.num key.2) },
  { address := { field := indexField + 1, path := [coordinate] },
    stored := "filled", raw := .parsed (.str "filled") }
]

private def rowsData (left right : List (String × Rat)) : DocumentData := {
  instantiatedRows :=
    (left.mapIdx fun index _ => { group := 10, path := [index + 1] }) ++
    (right.mapIdx fun index _ => { group := 20, path := [index + 1] })
  cells := (left.mapIdx fun index key => rowCells 1 (index + 1) key).flatten ++
    (right.mapIdx fun index key => rowCells 3 (index + 1) key).flatten
}

private def source (left right : String := "5.00") (value : Rat := 5) : DocumentData :=
  rowsData [(left, value)] [(right, value)]

private def preliminary (candidate : FlatModel) (data : DocumentData) :
    Option (CheckedIndexPreliminary candidate) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler candidate).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  checked.applyFullIndexPreliminary.toOption

private def run (data : DocumentData := source) (rightMinimum : Nat := 2)
    (op : FieldFillQuantifier := .allFieldsFilled) (errorField : Nat := 2)
    (scale : Nat := 2) : Option (List ParallelRuleRowOutcome) := do
  let view ← preliminary (model rightMinimum scale) data
  let rule ← (checkParallelFieldRule (model rightMinimum scale) 2 4 errorField
    (.leaf (.fill op .left .right)) "MATCH" .error { parts := [] }).toOption
  (rule.evalFull view).toOption

private def firedAt (field : Nat) (coordinates : List MessageRepetitionCoordinate)
    (polarity : Polarity := .value) : FlatRuleOutcome :=
  .fired {
    errorAddress := { entity := .field field, coordinates }, errorCode := "MATCH", severity := .error
    messageType := polarity, text := { text := "" }
  }

private def observed (rows : Option (List ParallelRuleRowOutcome)) :
    Option (List (String × SemanticIndexKey × FlatRuleOutcome)) :=
  rows.map (·.map fun row => (row.iterationToken, row.key, row.outcome))

private def matchedFive := [
  ("5", SemanticIndexKey.number 5, firedAt 2 [.concrete 1]),
  ("5.00", .number 5, firedAt 2 [.concrete 1])
]

example : observed run = some matchedFive ∧
    observed (run (source "5" "5.00")) = some matchedFive := by
  native_decide

example : observed (run source 0) =
    some [("5", .number 5, firedAt 2 [.concrete 1])] := by
  native_decide

example : observed (run (source "-5.00" "-5.00" (-5))) =
    some [("-5", .number (-5), firedAt 2 [.concrete 1]),
      ("-5.00", .number (-5), firedAt 2 [.concrete 1])] ∧
    observed (run (source "5.25" "5.25" (21 / 4))) =
      some [("5.25", .number (21 / 4), firedAt 2 [.concrete 1])] := by
  native_decide

private def unmatched := rowsData [("5", 5)] [("6.00", 6)]

example : observed (run unmatched) =
    some [("5", .number 5, .unknown), ("6.00", .number 6, .unknown)] ∧
    observed (run unmatched 2 .fieldsNotCollectivelyFilled) =
      some [("5", .number 5, firedAt 2 [.concrete 1] .omission),
        ("6.00", .number 6, firedAt 2 [.unknown] .omission)] ∧
    observed (run unmatched 2 .fieldsNotCollectivelyFilled 4) =
      some [("5", .number 5, firedAt 4 [.unknown] .omission),
        ("6.00", .number 6, firedAt 4 [.concrete 1] .omission)] := by
  native_decide

private def duplicateLeft := rowsData
  [("5", 5), ("5.00", 5), ("9", 9)] [("5.00", 5), ("9.00", 9)]

example : (preliminary model duplicateLeft).map (·.findings) =
    some [
      { address := { field := 1, path := [1] }, kind := .unique },
      { address := { field := 1, path := [2] }, kind := .unique }] ∧
    observed (run duplicateLeft) =
      some [("5.00", .number 5, .unknown),
        ("9", .number 9, firedAt 2 [.concrete 3]),
        ("9.00", .number 9, firedAt 2 [.concrete 3])] ∧
    observed (run duplicateLeft 2 .fieldsNotCollectivelyFilled) =
      some [("5.00", .number 5, .unknown),
        ("9", .number 9, .unknown), ("9.00", .number 9, .unknown)] := by
  native_decide

example : observed (run (rowsData [("5", 5), ("5.00", 5)]
    [("5.00", 5), ("5.00", 5)])) = some [] ∧
    observed (run (rowsData [] [])) = some [] := by
  native_decide

private def cleanWithOtherKeys :=
  rowsData [("5", 5), ("9", 9)] [("5.00", 5), ("6.00", 6)]

private def unavailableRight (raw : RawCell) (stored : String) : DocumentData := {
  cleanWithOtherKeys with cells := cleanWithOtherKeys.cells.map fun input =>
    if input.address == { field := 3, path := [2] } then
      { input with stored, raw }
    else input
}

private def absentRight : DocumentData := {
  cleanWithOtherKeys with cells := cleanWithOtherKeys.cells.filter fun input =>
    input.address != { field := 3, path := [2] }
}

private def unavailableOutcomes := [
  ("5", SemanticIndexKey.number 5, firedAt 2 [.concrete 1]),
  ("5.00", .number 5, firedAt 2 [.concrete 1]),
  ("9", .number 9, FlatRuleOutcome.unknown)
]

example : [unavailableRight (.rejected .malformed) "bad",
    unavailableRight .presentEmpty "", absentRight].all (fun data =>
      observed (run data) == some unavailableOutcomes &&
      observed (run data 2 .fieldsNotCollectivelyFilled) ==
        some [("5", .number 5, .unknown), ("5.00", .number 5, .unknown),
          ("9", .number 9, .unknown)]) = true := by
  native_decide

example : observed (run (rowsData [("2", 2), ("10", 10)]
    [("2.00", 2), ("10.00", 10)])) =
    some [("10", .number 10, firedAt 2 [.concrete 2]),
      ("10.00", .number 10, firedAt 2 [.concrete 2]),
      ("2", .number 2, firedAt 2 [.concrete 1]),
      ("2.00", .number 2, firedAt 2 [.concrete 1])] := by
  native_decide

private def decimalSource : DocumentData := {
  source with cells := source.cells.map fun input =>
    if input.address.field == 1 || input.address.field == 3 then
      { input with numericDecimal := some { unscaled := 500, scale := 2 } }
    else input
}

example : decimalSource.cells.map (·.stored) = source.cells.map (·.stored) ∧
    observed (run decimalSource) = some matchedFive := by
  native_decide

private def preciseValue : Rat := 12345678901234 / 100000000000000
private def nextPreciseValue : Rat := 12345678901235 / 100000000000000
private def preciseSource := source "0.12345678901234" "0.12345678901234" preciseValue

example : observed (run preciseSource 2 .allFieldsFilled 2 14) =
    some [("0.12345678901234", .number preciseValue,
      firedAt 2 [.concrete 1])] ∧
    observed (run (rowsData [("0.12345678901234", preciseValue)]
      [("0.12345678901235", nextPreciseValue)])
      2 .fieldsNotCollectivelyFilled 2 14) =
      some [("0.12345678901234", .number preciseValue,
        firedAt 2 [.concrete 1] .omission),
        ("0.12345678901235", .number nextPreciseValue,
          firedAt 2 [.unknown] .omission)] := by
  native_decide

example : (match ({} : NumericTargetConstraints).checkFormalRead { scale := 14, signed := true }
      (.text "0.100000000000000000001") with
      | .error .totalDigitsTooLong => true
      | _ => false) = true ∧
    (do
      let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
        builtinStringPatternCompiler (model 2 14)).toOption
      match checkDocument prepared "en_US" (source "0.100000000000000000001"
          "0.100000000000000000001" (100000000000000000001 / 1000000000000000000000)) with
      | .error error => some error
      | .ok _ => none) = some (.incoherentCell { field := 1, path := [1] }) := by
  native_decide

example : (match (model 2 21).validate with
    | .error (.numericFractionalDigitsAboveCap path declared maximum) =>
        path == ["Form", "Left", "Key"] && declared == 21 && maximum == 14
    | _ => false) = true := by
  native_decide

private def computationModel : FlatModel := {
  model with fields := model.fields.map fun declaration =>
    if declaration.id == 2 || declaration.id == 4 then
      { declaration with policy := { kind := .number { scale := 0, signed := true } } }
    else declaration
}

private def computation (data : DocumentData) : Option (List ParallelNumericDirectOutcome) := do
  let numericData := { data with cells := data.cells.map fun input =>
    if input.address.field == 2 || input.address.field == 4 then
      let value : Int := if input.address.field == 2 then 0
        else if input.address.path == [1] then 7 else 9
      { input with stored := toString value, raw := .parsed (.num value) }
    else input }
  let view ← preliminary computationModel numericData
  let checked ← (checkIsolatedParallelNumericDirectRun computationModel ["Form"] 2
    { base := .absolute, groups := ["Form", "Right"], field := "Value" }).toOption
  (checked.execute view).toOption

example : computation source = some [
    { address := { field := 2, path := [1] }, outcome := .accepted { unscaled := 7, scale := 0 } }] ∧
    computation (rowsData [("5", 5)] [("6.00", 6), ("5.00", 5)]) = some [
      { address := { field := 2, path := [1] }, outcome := .accepted { unscaled := 9, scale := 0 } }] := by
  native_decide

end A12Kernel.Conformance.ParallelNumberIndex
