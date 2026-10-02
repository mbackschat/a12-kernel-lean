import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: the remaining atoms read from inside a row

A repeatable `Rows` (at most three rows) holds Number `A` and `B`, a digits-only String `T`, a
repeatable `Sub` (at most two) of Number `IA` over a fixed `Det` of Number `DA`, and fixed `Box` and
`Pad` of Number `BX` and `PX`; a fixed root `Fix` holds Number `FA` and `FB`. At every `Rows` row,
`MN = Min([A], [B])`, `FV = FieldValueAsNumber(T)`, `MV = MinValue(Sub*/IA)`,
`DV = NumberOfDifferentValues(Sub*/IA)`, `FF = FirstFilledValue(/Rg/Rows*/A Having [$A] < [/Rg/Rows/A])`,
`VC = NumberOfValueInFields(10 In …)` over the same filtered star, `FX = Sum(/Rg/Fix)`,
`BS = Sum(Sub*/Det)`, `ML = NumberOfFilledGroups(Sub*, /Rg/Fix)` and
`GC = NumberOfFilledGroups(Box, Pad)`, every target seeded with `99`. The documents are the Kernel's
rows of the [row-atom grid](../../evidence/kernel-30.8.1/captures/row-atoms-2026-10-02/), measured on
both codegen strategies.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowAtoms

open A12Kernel

private def rowsPath : GroupPath := ["Rg", "Rows"]
private def subPath : GroupPath := rowsPath ++ ["Sub"]

private def targets : List String := ["MN", "FV", "MV", "DV", "FF", "VC", "FX", "BS", "ML", "GC"]

private def rowsNames : List String := ["A", "B", "T"] ++ targets

private def names : List String := rowsNames ++ ["IA", "DA", "BX", "PX", "FA", "FB"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let (groupPath, repeatableScope) : GroupPath × List RepeatableLevel :=
    if rowsNames.contains name then (rowsPath, [10])
    else match name with
      | "IA" => (subPath, [10, 20])
      | "DA" => (subPath ++ ["Det"], [10, 20])
      | "BX" => (rowsPath ++ ["Box"], [10])
      | "PX" => (rowsPath ++ ["Pad"], [10])
      | _ => (["Rg", "Fix"], [])
  if name == "T" then
    { id := idOf name, groupPath, name, repeatableScope, policy := { kind := .string }
      stringPolicy := { maxLength := some 15 }, stringPatternSource := some "[0-9]+" }
  else
    { id := idOf name, groupPath, name, repeatableScope
      policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel where
  fields := names.map declaration
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 3 },
    { level := 20, path := subPath, repeatability := some 2 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def star (base : PathBase) (groups : List (String × Bool)) (field : String) :
    SurfaceStarFieldPath :=
  { base, groups := groups.map fun (name, starred) => { name, starred }, field }

private def starredGroup (groups : List (String × Bool)) : SurfaceStarGroupPath :=
  { base := .relative 0, groups := groups.map fun (name, starred) => { name, starred } }

private def fixedRoot : SurfaceGroupReference := .path { base := .absolute, groups := ["Rg", "Fix"] }

private def numeric (atom : SurfaceNumericAtom SurfaceNumberEntitySource) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric atom)

private def sole (operand : SurfaceFieldEntityOperand) : SurfaceNumberEntitySource :=
  { first := operand, rest := [] }

/-- `[$A] < [/Rg/Rows/A]`, a starred row's `A` exceeding the computing row's own. -/
private def exceedsOwn : SurfaceCorrelatedHaving :=
  .compareNumbers .less
    { origin := .outer, field := bare "A" }
    { origin := .inner, field := { base := .absolute, groups := rowsPath, field := "A" } }

private def filteredRows : SurfaceFieldEntityOperand :=
  .starHaving (star .absolute [("Rg", false), ("Rows", true)] "A") exceedsOwn

private def subStar (field : String) : SurfaceFieldEntityOperand :=
  .star (star (.relative 0) [("Sub", true)] field)

private def expression : String → AuthoredNumericExpr SurfaceNumericComputationAtom
  | "MN" => .extremumCall .minimum (.extremum .minimum (numeric (.field (bare "A"))) (numeric (.field (bare "B"))))
  | "FV" => numeric (.fieldValueAsNumber (.direct (bare "T")))
  | "MV" => numeric (.aggregate .minimum (sole (subStar "IA")))
  | "DV" => numeric (.aggregate .distinctCount (sole (subStar "IA")))
  | "FF" => .atom (.firstFilled (sole filteredRows))
  | "VC" => .atom (.valueCount 10 (sole filteredRows))
  | "FX" => numeric (.aggregate .sum (sole (.group fixedRoot)))
  | "BS" => numeric (.aggregate .sum (sole (.starredGroup (starredGroup [("Sub", true), ("Det", false)]))))
  | "ML" => numeric (.filledGroupCount [.starred (starredGroup [("Sub", true)]), .fixed fixedRoot])
  | _ => numeric (.filledGroupCount [.fixed (.path { base := .relative 0, groups := ["Box"] }),
      .fixed (.path { base := .relative 0, groups := ["Pad"] })])

private def step (target : String) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  elaborateCompleteNumericTargetComputationTable model rowsPath (idOf target) [(none, expression target)]
    (targetScope := .row)

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan (← targets.mapM fun target => (step target).toOption)).toOption

private def classified (name : String) (text : String) : RawCell :=
  if name == "T" then
    if !text.isEmpty && text.all Char.isDigit then .parsed (.str text) else .rejected .declaredConstraint
  else match text.toInt? with
    | some amount => .parsed (.num amount)
    | none => .rejected .malformed

private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  { address := { field := idOf name, path }, stored := text, raw := classified name text
    numericDecimal := if name == "T" then none else text.toInt?.map ({ unscaled := ·, scale := 0 }) }

/-- A cell for each present text, `""` standing for an absent one. -/
private def present (name : String) (path : List Nat) (text : String) : List ClassifiedCellInput :=
  if text == "" then [] else [cell name path text]

/-- One `Rows` row: its `A`, `B` and `T` texts, its `Sub` rows' `IA` and `DA` texts, and its `BX` and
`PX` texts, `""` for each absent cell. -/
private structure RowInput where
  a : String
  b : String := ""
  t : String := ""
  subs : List (String × String) := []
  box : String := ""
  pad : String := ""

/-- One document of the given `Rows` rows and `Fix` texts, every target seeded with `99`. -/
private def document? (rows : List RowInput) (fix : List String) : Option (CheckedDocument model) :=
  let indexed := rows.zipIdx.map fun (row, index) => (row, index + 1)
  (checkDocument prepared "en_US" {
    instantiatedRows := indexed.flatMap fun (row, r) =>
      { group := 10, path := [r] } :: row.subs.zipIdx.map fun (_, s) => { group := 20, path := [r, s + 1] }
    cells :=
      indexed.flatMap (fun (row, r) =>
        targets.map (cell · [r] "99") ++ present "A" [r] row.a ++ present "B" [r] row.b ++
          present "T" [r] row.t ++ present "BX" [r] row.box ++ present "PX" [r] row.pad ++
          row.subs.zipIdx.flatMap fun ((ia, da), s) => present "IA" [r, s + 1] ia ++ present "DA" [r, s + 1] da) ++
      (["FA", "FB"].zip fix).flatMap fun (name, text) => present name [] text
  }).toOption

/-- The stored amount, or `-` for a target the Kernel reports cleared without a formal error at it. -/
private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue | .inheritedPoison _ => some "-"
  | .invalidNoValue _ | .rejected _ _ => none

/-- Every outcome as `target row value`, sorted. -/
private def outcomes? (rows : List RowInput) (fix : List String) : Option (List String) := do
  let plan ← plan?
  let input ← document? rows fix
  let outcomes ← (plan.execute world input).toOption
  let rendered ← outcomes.mapM fun outcome => (reported outcome.outcome).map fun value =>
    s!"{names.getD outcome.targetField.field ""} {".".intercalate
      (outcome.targetField.path.map toString)} {value}"
  pure (rendered.mergeSort (decide <| · ≤ ·))

private def clean : List RowInput :=
  [{ a := "1", b := "5", t := "12", subs := [("2", "1"), ("3", "")], box := "1", pad := "1" },
    { a := "4", b := "2", t := "7", subs := [("6", "5")], pad := "1" }, { a := "10", t := "3" }]

/- `a01`: the row's own `A`, `B`, `T` and `Sub` rows, an empty `B` reading as zero for `Min`; the
filtered star keeps the rows whose `A` exceeds the computing row's, the third row's keeping none;
`FX` reads the root `Fix` at every row, `BS` the row's own `Det` groups, `ML` the row's own `Sub` rows
beside `Fix`, and `GC` the row's own `Box` and `Pad`. -/
example :
    outcomes? clean ["7", "9"] = some
      ["BS 1 1", "BS 2 5", "BS 3 0", "DV 1 2", "DV 2 1", "DV 3 0", "FF 1 4", "FF 2 10", "FF 3 0",
        "FV 1 12", "FV 2 7", "FV 3 3", "FX 1 16", "FX 2 16", "FX 3 16", "GC 1 2", "GC 2 1", "GC 3 0",
        "ML 1 3", "ML 2 2", "ML 3 1", "MN 1 1", "MN 2 2", "MN 3 0", "MV 1 2", "MV 2 6", "MV 3 0",
        "VC 1 1", "VC 2 1", "VC 3 0"] := by
  native_decide

/- `a02`: a malformed `IA` clears only its own row's `MV` and `DV`, and a malformed `DA` its row's
`BS`; a malformed `A` clears its own `MN` and every row's filtered `FF` and `VC`, since every filter
reads it; a pattern-violating `T` clears its `FV`. -/
example :
    outcomes? [{ a := "1", b := "5", t := "12", subs := [("2", "1"), ("x", "")], box := "1", pad := "1" },
        { a := "x", b := "2", t := "7", subs := [("6", "x")], pad := "1" }, { a := "10", t := "z" }]
        ["7", "9"] = some
      ["BS 1 1", "BS 2 -", "BS 3 0", "DV 1 -", "DV 2 1", "DV 3 0", "FF 1 -", "FF 2 -", "FF 3 -",
        "FV 1 12", "FV 2 7", "FV 3 -", "FX 1 16", "FX 2 16", "FX 3 16", "GC 1 2", "GC 2 1", "GC 3 0",
        "ML 1 3", "ML 2 2", "ML 3 1", "MN 1 1", "MN 2 -", "MN 3 0", "MV 1 -", "MV 2 6", "MV 3 0",
        "VC 1 -", "VC 2 -", "VC 3 -"] := by
  native_decide

/- `a03`: an over-limit `Sub` row and an over-limit `Rows` row are left out of every star spanning
them, and the over-limit row's own targets clear. -/
example :
    outcomes? [{ a := "1", b := "5", t := "12", subs := [("2", "1"), ("3", ""), ("1", "100")], box := "1", pad := "1" },
        { a := "4", b := "2", t := "7", subs := [("6", "5")], pad := "1" }, { a := "10", t := "3" },
        { a := "2", b := "1", t := "1" }] ["7", "9"] = some
      ["BS 1 1", "BS 2 5", "BS 3 0", "BS 4 -", "DV 1 2", "DV 2 1", "DV 3 0", "DV 4 -", "FF 1 4",
        "FF 2 10", "FF 3 0", "FF 4 -", "FV 1 12", "FV 2 7", "FV 3 3", "FV 4 -", "FX 1 16", "FX 2 16",
        "FX 3 16", "FX 4 -", "GC 1 2", "GC 2 1", "GC 3 0", "GC 4 -", "ML 1 3", "ML 2 2", "ML 3 1",
        "ML 4 -", "MN 1 1", "MN 2 2", "MN 3 0", "MN 4 -", "MV 1 2", "MV 2 6", "MV 3 0", "MV 4 -",
        "VC 1 1", "VC 2 1", "VC 3 0", "VC 4 -"] := by
  native_decide

/- `a04`: an empty computing-row `A` keeps every row with a positive `A`, an empty `T` reads as zero, an instantiated
`Sub` row with no cell is a filled group for `ML` and holds no distinct value, and no `Fix` counts
nothing. -/
example :
    outcomes? [{ a := "", subs := [("", "")] }, { a := "4", b := "2", t := "7", subs := [("6", "5")] },
        { a := "10" }] [] = some
      ["BS 1 0", "BS 2 5", "BS 3 0", "DV 1 0", "DV 2 1", "DV 3 0", "FF 1 4", "FF 2 10", "FF 3 0",
        "FV 1 0", "FV 2 7", "FV 3 0", "FX 1 0", "FX 2 0", "FX 3 0", "GC 1 0", "GC 2 0", "GC 3 0",
        "ML 1 1", "ML 2 1", "ML 3 0", "MN 1 0", "MN 2 2", "MN 3 0", "MV 1 0", "MV 2 6", "MV 3 0",
        "VC 1 1", "VC 2 1", "VC 3 0"] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowAtoms
