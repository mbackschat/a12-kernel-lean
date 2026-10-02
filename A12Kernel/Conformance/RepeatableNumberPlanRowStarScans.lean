import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: scans and counts over a star read from inside a row

The entity-list scans and counts over a star, each elaborated at a repeatable target and run at every
row. A repeatable `Rows` (at most three rows) holds a repeatable `Sub` (at most two) with Number `IA`
and `IB`, String `IT` and Boolean `IBo`. At a `Rows` target `F = FirstFilledValue(Sub*/IA)`,
`V = NumberOfValueInFields(5 In Sub*/IA)`, `TV = NumberOfValueInFields("x" In Sub*/IT)`,
`BV = NumberOfValueInFields(True In Sub*/IBo)`, `P = SumOfProducts(Sub*/IA, Sub*/IB)` and
`G = NumberOfFilledGroups(Sub*)` read the row's own `Sub` rows, and `FA = FirstFilledValue(/Rg/Rows*/CA)`
every `Rows` row's computed `CA = [A]`. At the fixed root `R = FirstFilledValue(Rows*/Sub*/IA)` and
`RT = NumberOfValueInFields("x" In Rows*/Sub*/IT)` read every `Sub` row. Every reader is authored ahead
of what it reads, and every target is seeded with a stale `99`. The documents are the Kernel's rows of the
[row-scan grid](../../evidence/kernel-30.8.1/captures/row-star-scans-2026-10-02/), measured on both
codegen strategies.

Each binds the row above its first starred level as the
[aggregates](RepeatableNumberPlanRowAggregates.lean) do. The rows separate that from a union over every
row, a malformed source reached by exactly the scans that read it, an over-limit row left out of every
scan and count at a row and at the root, as a computation reads every star over its in-capacity
extent, a scan finding nothing filled, which reads `0`, an instantiated empty row, which the
group count counts, and a computed `0`, which a scan takes as filled.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowStarScans

open A12Kernel

private def rowsPath : GroupPath := ["Rg", "Rows"]
private def subPath : GroupPath := rowsPath ++ ["Sub"]

private def rowsNames : List String := ["A", "CA", "F", "V", "TV", "BV", "P", "G", "FA"]
private def subNames : List String := ["IA", "IB", "IT", "IBo"]

private def names : List String := rowsNames ++ subNames ++ ["R", "RT"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let kind : FieldKind := match name with
    | "IT" => .string
    | "IBo" => .boolean
    | _ => .number { scale := 0, signed := true }
  if name.startsWith "R" then
    { id := idOf name, groupPath := ["Rg"], name, policy := { kind } }
  else if rowsNames.contains name then
    { id := idOf name, groupPath := rowsPath, name, repeatableScope := [10], policy := { kind } }
  else
    { id := idOf name, groupPath := subPath, name, repeatableScope := [10, 20], policy := { kind } }

private def model : FlatModel where
  fields := names.map declaration
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 3 },
    { level := 20, path := subPath, repeatability := some 2 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

/-- `Sub*/field`, read from a `Rows` target. -/
private def subStar (field : String) : SurfaceStarFieldPath :=
  { base := .relative 0, groups := [{ name := "Sub", starred := true }], field }

private def sole (operand : SurfaceFieldEntityOperand) : SurfaceFieldEntitySource :=
  { first := operand, rest := [] }

private def step? (target : String) (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) :=
  (elaborateCompleteNumericTargetComputationTable model rowsPath (idOf target) [(none, expression)]
    (targetScope := .row)).toOption

/-- `Rows*/Sub*/field`, read from the fixed root. -/
private def rootStar (field : String) : SurfaceStarFieldPath :=
  { base := .relative 0, groups := [{ name := "Rows", starred := true }, { name := "Sub", starred := true }]
    field }

private def rootStep? (target : String)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) :=
  (elaborateCompleteNumericTargetComputationTable model ["Rg"] (idOf target) [(none, expression)]).toOption

/-- The grid's computations in its authored order, `FA` ahead of the `CA` it reads. -/
private def authored : List (Option (CheckedNumericComputationTable model)) :=
  [rootStep? "R" (.atom (.firstFilled (sole (.star (rootStar "IA"))))),
    rootStep? "RT" (.atom (.tokenValueCount "x" { first := .star (rootStar "IT") .stored, rest := [] })),
    step? "F" (.atom (.firstFilled (sole (.star (subStar "IA"))))),
    step? "V" (.atom (.valueCount 5 (sole (.star (subStar "IA"))))),
    step? "TV" (.atom (.tokenValueCount "x" { first := .star (subStar "IT") .stored, rest := [] })),
    step? "BV" (.atom (.booleanValueCount true (sole (.star (subStar "IBo"))))),
    step? "P" (.atom (.sumOfProducts { left := subStar "IA", right := subStar "IB" })),
    step? "G" (.atom (.numeric (.filledGroupCount
      [.starred (.terminallyStarred (.relative 0) ["Sub"])]))),
    step? "FA" (.atom (.firstFilled (sole (.star
      { base := .absolute, groups := [{ name := "Rg" }, { name := "Rows", starred := true }], field := "CA" })))),
    step? "CA" (.atom (.numeric (.field { base := .relative 0, groups := [], field := "A" })))]

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan (← authored.mapM id)).toOption

/-- One cell of a present text, classified by its field's kind. -/
private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  let address : CellAddr := { field := idOf name, path }
  match name with
  | "IT" => { address, stored := text, raw := .parsed (.str text) }
  | "IBo" => { address, stored := text, raw := .parsed (.bool (text == "true")) }
  | _ =>
      { address, stored := text
        raw := match text.toInt? with
          | some amount => .parsed (.num amount)
          | none => .rejected .malformed
        numericDecimal := text.toInt?.map ({ unscaled := ·, scale := 0 }) }

/-- One `Sub` row's `IA`, `IB`, `IT` and `IBo` texts, `""` for an absent cell. -/
private abbrev SubInput := List String

/-- One document of `Rows` rows, each its `A` text and its `Sub` rows, every target seeded with `99`. -/
private def document? (rows : List (String × List SubInput)) : Option (CheckedDocument model) :=
  let indexed := rows.zipIdx.map fun (row, index) => (row, index + 1)
  let present (name : String) (path : List Nat) (text : String) :=
    if text == "" then [] else [cell name path text]
  (checkDocument prepared "en_US" {
    instantiatedRows := indexed.flatMap fun ((_, subs), r) =>
      { group := 10, path := [r] } :: subs.zipIdx.map fun (_, s) => { group := 20, path := [r, s + 1] }
    cells := [cell "R" [] "99", cell "RT" [] "99"] ++ indexed.flatMap fun ((a, subs), r) =>
      (rowsNames.drop 1).map (cell · [r] "99") ++ present "A" [r] a ++
        subs.zipIdx.flatMap fun (texts, s) =>
          (subNames.zip texts).flatMap fun (name, text) => present name [r, s + 1] text
  }).toOption

/-- The stored amount, or `-` for a target the Kernel reports cleared without a formal error at it. -/
private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue | .inheritedPoison _ => some "-"
  | .invalidNoValue _ | .rejected _ _ => none

/-- Every outcome as `target row value`, sorted. -/
private def outcomes? (rows : List (String × List SubInput)) : Option (List String) := do
  let plan ← plan?
  let input ← document? rows
  let outcomes ← (plan.execute world input).toOption
  let rendered ← outcomes.mapM fun outcome => (reported outcome.outcome).map fun value =>
    s!"{names.getD outcome.targetField.field ""} {".".intercalate
      (outcome.targetField.path.map toString)} {value}"
  pure (rendered.mergeSort (decide <| · ≤ ·))

/- `h01`: every scan and count reads the row's own `Sub` rows, `F` skipping an empty `IA` and a row
with none reading `0`, while `FA` takes the first row's `CA` at every row. -/
example :
    outcomes? [("3", [["", "2", "x", "true"], ["5", "3", "y", "false"]]),
      ("4", [["7", "1", "x", "true"]]), ("6", [])] = some
      ["BV 1 1", "BV 2 1", "BV 3 0", "CA 1 3", "CA 2 4", "CA 3 6", "F 1 5", "F 2 7", "F 3 0",
      "FA 1 3", "FA 2 3", "FA 3 3", "G 1 2", "G 2 1", "G 3 0", "P 1 15", "P 2 7", "P 3 0", "R  5",
      "RT  2", "TV 1 1", "TV 2 1", "TV 3 0", "V 1 1", "V 2 0", "V 3 0"] := by
  native_decide

/- `h02`: a malformed `IA` clears the first row's `F`, `V` and `P`, which read it, and leaves the
counts over the other fields and the group count, which takes the row as filled. -/
example :
    outcomes? [("3", [["", "2", "x", "true"], ["x", "3", "y", "false"]]),
      ("4", [["7", "1", "x", "true"]]), ("6", [])] = some
      ["BV 1 1", "BV 2 1", "BV 3 0", "CA 1 3", "CA 2 4", "CA 3 6", "F 1 -", "F 2 7", "F 3 0",
      "FA 1 3", "FA 2 3", "FA 3 3", "G 1 2", "G 2 1", "G 3 0", "P 1 -", "P 2 7", "P 3 0", "R  -",
      "RT  2", "TV 1 1", "TV 2 1", "TV 3 0", "V 1 -", "V 2 0", "V 3 0"] := by
  native_decide

/- `h03`: an over-limit `Sub` row, the only one under the first row holding a filled `IA`, an `x` and
a `True`, is left out of every scan and count, the root's `R` reaching the second row's `7`. -/
example :
    outcomes? [("3", [["", "2", "y", "false"], ["", "3", "y", "false"], ["5", "1", "x", "true"]]),
      ("4", [["7", "1", "x", "true"]]), ("6", [])] = some
      ["BV 1 0", "BV 2 1", "BV 3 0", "CA 1 3", "CA 2 4", "CA 3 6", "F 1 0", "F 2 7", "F 3 0",
      "FA 1 3", "FA 2 3", "FA 3 3", "G 1 2", "G 2 1", "G 3 0", "P 1 0", "P 2 7", "P 3 0", "R  7",
      "RT  1", "TV 1 0", "TV 2 1", "TV 3 0", "V 1 0", "V 2 0", "V 3 0"] := by
  native_decide

/- `h04`: an empty `A` copies as a computed `0`, which `FA` takes as filled at every row, and an
instantiated `Sub` row holding no cell counts as a filled group. -/
example :
    outcomes? [("", [["5", "2", "", ""]]), ("4", [["", "", "", ""]]), ("6", [])] = some
      ["BV 1 0", "BV 2 0", "BV 3 0", "CA 1 0", "CA 2 4", "CA 3 6", "F 1 5", "F 2 0", "F 3 0",
      "FA 1 0", "FA 2 0", "FA 3 0", "G 1 1", "G 2 1", "G 3 0", "P 1 10", "P 2 0", "P 3 0", "R  5",
      "RT  0", "TV 1 0", "TV 2 0", "TV 3 0", "V 1 1", "V 2 0", "V 3 0"] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowStarScans
