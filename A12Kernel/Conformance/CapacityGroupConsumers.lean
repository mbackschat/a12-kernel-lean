import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.TemporalDistinctCount
import A12Kernel.Elaboration.TokenEntityValueList
import A12Kernel.Elaboration.NumericAggregate.Entities

/-! # Group operands and a filtered star leave an over-limit row out

A root `Rg` with String `W` and `X`, Number `Y` and `F9`, over five groups each holding at most two
rows: `Rows` of Number `N`, `M` and `Gate`, `DRows` of a `yyyy-MM-dd` Date `D`, a fixed `DShell` over
`SRows` of the same Date `S`, `TRows` of String `T`, and `NRows` of Number `V`. The consumers are the
[group-capacity grid](../../evidence/kernel-30.8.1/captures/group-capacity-consumers-2026-10-02/)'s:
`NumberOfDifferentValues` over the starred `DRows*` and the fixed `DShell`, the `No` value list
`TRows*/T In X` and `TRows* In X`, a filtered `FirstFilledValue(Rows*/M Having …, F9)`, and
`Sum(Rows*/N)` through the partial view the library's partial rule evaluation reads. Lean's
correlated filter takes no Number literal, so it compares `[Rows/Gate] < [$F9]` where the grid writes
`[Rows/Gate] > 0`. A `Gate` is either absent or `1` here and `F9` is `9`, so both keep exactly the
rows holding a `Gate`.

Every group's first row holds `2020-01-01`, `a` or `5`, its second is empty, and a third beyond
capacity holds `2021-01-01`, `x` or `100`, with `Rows` holding `N` `100`, `M` `7` and `Gate` `1`
there. The controls are the same values in capacity as the second row, and the first two rows alone.
The Kernel answers the over-limit document as the one without its third row on every consumer, on
full validation, under a partial scope of the whole root, and under one naming rows 1 and 2 of each
group; partial validation skips the filtered scan under both scopes.

Two of the grid's rows have no lock here. Its `NRows` value lists take a sole `Y` on the values side,
which the Kernel admits and Lean's Number value list refuses as `tooFewFields`. Under the rows-1-and-2
scope its token value lists fire, where Lean answers unknown because it counts only a wildcard index
as covering a value list's extent. Both are recorded as gaps rather than locked.
-/

namespace A12Kernel.Conformance.CapacityGroupConsumers

open A12Kernel

private def names : List String := ["W", "X", "Y", "F9", "N", "M", "Gate", "D", "S", "T", "V"]

private def idOf (name : String) : FieldId := names.idxOf name

/-- Each repeatable group's level, path and the fields it holds. -/
private def groups : List (Nat × GroupPath × List String) :=
  [(10, ["Rg", "Rows"], ["N", "M", "Gate"]), (20, ["Rg", "DRows"], ["D"]),
    (30, ["Rg", "DShell", "SRows"], ["S"]), (40, ["Rg", "TRows"], ["T"]), (50, ["Rg", "NRows"], ["V"])]

private def placement (name : String) : Option (Nat × GroupPath) :=
  (groups.find? fun (_, _, fields) => fields.contains name).map fun (level, path, _) => (level, path)

private def declaration (name : String) : FlatFieldDecl :=
  let base : FlatFieldDecl := match placement name with
    | some (level, path) =>
        { id := idOf name, groupPath := path, name, repeatableScope := [level], policy := { kind := .string } }
    | none => { id := idOf name, groupPath := ["Rg"], name, policy := { kind := .string } }
  match name with
  | "Y" | "F9" | "N" | "M" | "Gate" | "V" =>
      { base with policy := { kind := .number { scale := 0, signed := true } } }
  | "D" | "S" => { base with
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full } }
  | _ => base

private def model : FlatModel :=
  { fields := names.map declaration
    repeatableGroups := groups.map fun (level, path, _) =>
      { level, path, repeatability := some 2 }
    timeZoneId := "Europe/Berlin" }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def isNumber (name : String) : Bool := ["Y", "F9", "N", "M", "Gate", "V"].contains name

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
    numericDecimal := if isNumber name then text.toInt?.map ({ unscaled := ·, scale := 0 }) else none }

private def firstRow : List (String × String) :=
  [("N", "5"), ("D", "2020-01-01"), ("S", "2020-01-01"), ("T", "a"), ("V", "5")]

private def thirdRow : List (String × String) :=
  [("N", "100"), ("M", "7"), ("Gate", "1"), ("D", "2021-01-01"), ("S", "2021-01-01"), ("T", "x"),
    ("V", "100")]

/-- Every group's rows, each a list of `(field, text)` cells, beside `W`, `X`, `Y` and `F9`. -/
private def document? (rows : List (List (String × String))) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US"
    { instantiatedRows := groups.flatMap fun (level, _, _) =>
        rows.zipIdx.map fun (_, index) => { group := level, path := [index + 1] }
      cells := [cell "W" [] "w", cell "X" [] "x", cell "Y" [] "100", cell "F9" [] "9"] ++
        rows.zipIdx.flatMap fun (row, index) => row.map fun (name, text) => cell name [index + 1] text }).toOption

private def overLimit : List (List (String × String)) := [firstRow, [], thirdRow]

private def inCapacity : List (List (String × String)) := [firstRow, thirdRow]

private def noThird : List (List (String × String)) := [firstRow, []]

/-- The whole root relevant, as the grid's `/Rg` entry makes it. -/
private def wholeRoot : ValidationRelevanceScope :=
  .partialSet [{ path := ["Rg"], indices := [.concrete 1] }]

/-- The root's own fields and rows 1 and 2 of every group, as the grid's `reps` entries name them. -/
private def firstTwoRows : ValidationRelevanceScope :=
  .partialSet ((["W", "X", "Y", "F9"].map fun name => { path := ["Rg", name], indices := [.all, .all] }) ++
    groups.flatMap fun (_, path, _) => [1, 2].map fun row =>
      { path, indices := (path.dropLast.map fun _ => .concrete 1) ++ [.concrete row] })

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def star (group field : String) : SurfaceStarFieldPath :=
  { base := .relative 0, groups := [{ name := group, starred := true }], field }

private def starredGroup (group : String) : SurfaceStarGroupPath :=
  { base := .relative 0, groups := [{ name := group, starred := true }] }

private def distinctDays? (operand : SurfaceFieldEntityOperand) (rows : List (List (String × String))) :
    Option NumericOperand := do
  let source ← (elaborateTemporalDistinctCountSource model ["Rg"] { first := operand, rest := [] }).toOption
  let run ← (checkTemporalDistinctCountRun source).toOption
  (run.evaluate (← document? rows) []).toOption

private def tokenList? (operand : SurfaceFieldEntityOperand) :
    Option (CheckedTokenEntityValueListSource model) :=
  (elaborateTokenEntityValueListSource model ["Rg"]
    { quantifier := .no, fields := { first := operand, rest := [] }
      values := { first := .field (bare "X"), rest := [] } }).toOption

/-- `[Rows/Gate] < [$F9]`, a row's `Gate` against the root's `9`. -/
private def gated : SurfaceCorrelatedHaving :=
  .compareNumbers .less
    { origin := .inner, field := { base := .relative 0, groups := ["Rows"], field := "Gate" } }
    { origin := .outer, field := bare "F9" }

private def filteredFirstFilled? (rows : List (List (String × String))) :
    Option PartialValidationFirstFilledNumberResult := do
  let source ← (elaborateFirstFilledNumberSource model ["Rg"]
    { first := .starHaving (star "Rows" "M") gated, rest := [.field (bare "F9")] }).toOption
  (source.evaluateCheckedDocumentValidation (← document? rows) [] .full).toOption

/-- `Sum(Rows*/N)` through the call-local partial view the library's partial rule evaluation reads. -/
private def partialSum? (scope : ValidationRelevanceScope) (rows : List (List (String × String))) :
    Option PartialValidationNumberAggregateViewResult := do
  let source ← (elaborateNumberEntitySource model ["Rg"] { first := .star (star "Rows" "N"), rest := [] }).toOption
  let document ← document? rows
  (source.evaluatePartialViewAggregate .sum document [] scope fun environment field =>
    (document.validationAddressedCell environment field).map fun addressed => some addressed.cell).toOption

private def operandValue : Option NumericOperand → String
  | some (.value amount _) => toString amount
  | _ => "-"

private def verdictValue : Option Verdict → String
  | some (.fired _) => "fired"
  | some .notFired => "notFired"
  | _ => "-"

private def partialVerdictValue : Option PartialHavingValueListResult → String
  | some (.evaluated verdict) => verdictValue (some verdict)
  | _ => "-"

/-- The distinct counts over `DRows*` and `DShell`, the token lists over `TRows*/T` and `TRows*` on
full validation and then under the whole root, and the filtered scan, each its value or `-`. -/
private def values (rows : List (List (String × String))) : List String := Id.run do
  let some document := document? rows | return []
  let fields := [tokenList? (.star (star "TRows" "T")), tokenList? (.starredGroup (starredGroup "TRows"))]
  return [operandValue (distinctDays? (.starredGroup (starredGroup "DRows")) rows),
    operandValue (distinctDays? (.group (.path { base := .relative 0, groups := ["DShell"] })) rows)] ++
    fields.map (fun source => verdictValue (source.bind (·.evaluateFull document [] |>.toOption))) ++
    fields.map (fun source => partialVerdictValue (source.bind (·.evaluatePartial document [] wholeRoot |>.toOption))) ++
    [match filteredFirstFilled? rows with
      | some (.evaluated (.value amount _)) => toString amount
      | _ => "-"]

/- The over-limit document reads as the one without its third row, while the same values in capacity
are read: one day is distinct on the starred and the fixed group, no `T` equals `x` on either form and
either observation, and the filtered scan reaches its fallback. -/
example :
    values overLimit = ["1", "1", "fired", "fired", "fired", "fired", "9"] ∧
      values noThird = ["1", "1", "fired", "fired", "fired", "fired", "9"] ∧
      values inCapacity = ["2", "2", "notFired", "notFired", "notFired", "notFired", "7"] := by
  native_decide

private def sumValue : Option PartialValidationNumberAggregateViewResult → String
  | some (.result (.evaluated (.value amount _))) => toString amount
  | some (.result .nonRelevant) => "nonRelevant"
  | _ => "-"

/- `Sum` on partial validation's own route leaves the over-limit row out under the whole root; naming
rows 1 and 2 leaves it non-relevant on every document, as the Kernel's rule stays silent on all three. -/
example :
    ([overLimit, noThird, inCapacity].map fun rows => sumValue (partialSum? wholeRoot rows)) =
        ["5", "5", "105"] ∧
      ([overLimit, noThird, inCapacity].map fun rows => sumValue (partialSum? firstTwoRows rows)) =
        ["nonRelevant", "nonRelevant", "nonRelevant"] := by
  native_decide

end A12Kernel.Conformance.CapacityGroupConsumers
