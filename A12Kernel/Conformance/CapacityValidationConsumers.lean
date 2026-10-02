import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.TemporalDistinctCount
import A12Kernel.Elaboration.NumericAggregate.Entities

/-! # Validation consumers read a star's in-capacity extent, on full and partial validation

A root `Rg` with Number `F9` and String `TF` over a repeatable `Rows` of at most two rows holding
Number `N` and `M`, String `T` and a `yyyy-MM-dd` Date `D`. The consumers are those of the
[validation capacity grid](../../evidence/kernel-30.8.1/captures/validation-capacity-consumers-2026-10-02/):
`FirstFilledValue(Rows*/M, F9)`, `FirstFilledValue(Rows*/T, TF)`, `Sum(Rows*/N)` and
`NumberOfDifferentValues(Rows*/D)`, each evaluated on full validation and under a partial scope
covering every row, as the grid's `validatePart` rows cover the whole root. Its documents are a first
row holding `N` `5` and `D` `2020-01-01`, an empty second row, and a third row beyond capacity holding
`N` `100`, `M` `7`, `T` `x` and `D` `2021-01-01`; the same values in capacity as the second row; and
the first two rows alone.

The Kernel answers the over-limit document exactly as the one without its third row, on both
observations, while the in-capacity control reads the values, so each consumer leaves the row out
rather than reading it as unavailable.
-/

namespace A12Kernel.Conformance.CapacityValidationConsumers

open A12Kernel

private def rowsPath : GroupPath := ["Rg", "Rows"]

private def names : List String := ["F9", "TF", "N", "M", "T", "D"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let base : FlatFieldDecl := if ["F9", "TF"].contains name then
      { id := idOf name, groupPath := ["Rg"], name, policy := { kind := .string } }
    else { id := idOf name, groupPath := rowsPath, name, repeatableScope := [10], policy := { kind := .string } }
  match name with
  | "F9" | "N" | "M" => { base with policy := { kind := .number { scale := 0, signed := true } } }
  | "D" => { base with
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full } }
  | _ => base

private def model : FlatModel :=
  { fields := names.map declaration
    repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 2 }]
    timeZoneId := "Europe/Berlin" }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def classified (declaration : FlatFieldDecl) (text : String) : RawCell :=
  match declaration.policy.kind with
  | .number _ => match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
  | .temporal _ _ => match certifyFullDateInputField declaration with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD
          (.rejected .dateFormat)
      | .error _ => .rejected .dateFormat
  | _ => .parsed (.str text)

private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  let declaration := declaration name
  { address := { field := declaration.id, path }, stored := text, raw := classified declaration text
    numericDecimal := if ["F9", "N", "M"].contains name then
      text.toInt?.map ({ unscaled := ·, scale := 0 }) else none }

/-- One document of `Rows` rows, each a list of `(field, text)` cells, beside `F9 = 9` and `TF = fb`. -/
private def document? (rows : List (List (String × String))) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US"
    { instantiatedRows := rows.zipIdx.map fun (_, index) => { group := 10, path := [index + 1] }
      cells := [cell "F9" [] "9", cell "TF" [] "fb"] ++ rows.zipIdx.flatMap fun (row, index) =>
        row.map fun (name, text) => cell name [index + 1] text }).toOption

private def overLimit : List (List (String × String)) :=
  [[("N", "5"), ("D", "2020-01-01")], [], [("N", "100"), ("M", "7"), ("T", "x"), ("D", "2021-01-01")]]

private def inCapacity : List (List (String × String)) :=
  [[("N", "5"), ("D", "2020-01-01")], [("N", "100"), ("M", "7"), ("T", "x"), ("D", "2021-01-01")]]

private def noThird : List (List (String × String)) := [[("N", "5"), ("D", "2020-01-01")], []]

/-- Every field covered, every `Rows` row included. -/
private def everyRow : ValidationRelevanceScope :=
  .partialSet (names.map fun name =>
    if ["F9", "TF"].contains name then { path := ["Rg", name], indices := [.concrete 1, .concrete 1] }
    else { path := rowsPath ++ [name], indices := [.concrete 1, .all, .concrete 1] })

private def rowsStar (field : String) : SurfaceStarFieldPath :=
  { base := .relative 0, groups := [{ name := "Rows", starred := true }], field }

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def numberFirstFilled? (scope : ValidationRelevanceScope) (rows : List (List (String × String))) :
    Option PartialValidationFirstFilledNumberResult := do
  let source ← (elaborateFirstFilledNumberSource model ["Rg"]
    { first := .star (rowsStar "M"), rest := [.field (bare "F9")] }).toOption
  let document ← document? rows
  (source.evaluateCheckedDocumentValidation document [] scope).toOption

private def tokenFirstFilled? (rows : List (List (String × String))) : Option (Option FirstFilledTokenResult) := do
  let source ← (elaborateFirstFilledTokenSource model ["Rg"]
    { first := .star (rowsStar "T"), rest := [.field (bare "TF")] }).toOption
  let document ← document? rows
  (source.evaluateCheckedDirectStarFirstFilledValidation? document []).toOption

private def sumSource? : Option (CheckedNumberEntitySource model) :=
  (elaborateNumberEntitySource model ["Rg"] { first := .star (rowsStar "N"), rest := [] }).toOption

private def sum? (rows : List (List (String × String))) : Option NumericOperand := do
  let document ← document? rows
  (← sumSource?).evaluateCheckedDocumentValidationAggregate .sum document [] |>.toOption

private def partialSum? (rows : List (List (String × String))) :
    Option PartialValidationNumberAggregateResult := do
  let document ← document? rows
  (← sumSource?).evaluateCheckedDocumentPartialAggregate .sum document [] everyRow |>.toOption

private def distinctDays? (rows : List (List (String × String))) : Option NumericOperand := do
  let source ← (elaborateTemporalDistinctCountSource model ["Rg"]
    { first := .star (rowsStar "D"), rest := [] }).toOption
  let run ← (checkTemporalDistinctCountRun source).toOption
  let document ← document? rows
  (run.evaluate document []).toOption

private def numberValue : Option PartialValidationFirstFilledNumberResult → String
  | some (.evaluated (.value amount _)) => toString amount
  | _ => "-"

private def operandValue : Option NumericOperand → String
  | some (.value amount _) => toString amount
  | _ => "-"

/-- The Number scan in full and partial validation, the token scan, `Sum` in full and partial
validation, and the Date distinct count, each its value or `-` where it answers none. -/
private def values (rows : List (List (String × String))) : List String :=
  [numberValue (numberFirstFilled? .full rows), numberValue (numberFirstFilled? everyRow rows),
    match tokenFirstFilled? rows with
    | some (some (.value text _)) => text
    | _ => "-",
    operandValue (sum? rows),
    match partialSum? rows with
    | some (.evaluated operand) => operandValue (some operand)
    | _ => "-",
    operandValue (distinctDays? rows)]

/- The over-limit document reads as the one without its third row, on full and partial validation,
while the same values in capacity are read: the scans reach their fallbacks, `Sum` stays `5` and one
day is distinct. -/
example :
    values overLimit = ["9", "9", "fb", "5", "5", "1"] ∧
      values noThird = ["9", "9", "fb", "5", "5", "1"] ∧
      values inCapacity = ["7", "7", "x", "105", "105", "2"] := by
  native_decide

end A12Kernel.Conformance.CapacityValidationConsumers
