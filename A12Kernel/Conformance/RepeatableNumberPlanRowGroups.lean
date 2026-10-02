import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: group operands read from inside a row

A repeatable `Rows` (at most three rows) holds fixed `NB` of Number `N1` and `N2`, fixed `Box` and
`Pad` of `BX` and `PX`, and a repeatable `Sub` (at most two) of `IV`. At every `Rows` row
`NV = NumberOfValueInFields(5 In NB)` and `FF = FirstFilledValue(NB)` read the row's own `NB`, and at
every `Sub` row `SX = NumberOfFilledGroups(/Rg/Rows/Box, /Rg/Rows/Pad)` reads its enclosing row's `Box`
and `Pad`, every target seeded with `99`. The documents are the Kernel's rows of the
[row-group grid](../../evidence/kernel-30.8.1/captures/row-groups-2026-10-02/), measured on both
codegen strategies; the grid's token and Boolean group counts have no Number-atom surface here.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowGroups

open A12Kernel

private def rowsPath : GroupPath := ["Rg", "Rows"]
private def subPath : GroupPath := rowsPath ++ ["Sub"]

private def targets : List String := ["NV", "FF"]

private def names : List String := targets ++ ["N1", "N2", "BX", "PX", "IV", "SX"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let (groupPath, repeatableScope) : GroupPath × List RepeatableLevel := match name with
    | "N1" | "N2" => (rowsPath ++ ["NB"], [10])
    | "BX" => (rowsPath ++ ["Box"], [10])
    | "PX" => (rowsPath ++ ["Pad"], [10])
    | "IV" | "SX" => (subPath, [10, 20])
    | _ => (rowsPath, [10])
  { id := idOf name, groupPath, name, repeatableScope
    policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel where
  fields := names.map declaration
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 3 },
    { level := 20, path := subPath, repeatability := some 2 }]

private def group (path : List String) : SurfaceGroupReference := .path { base := .relative 0, groups := path }

private def expression : String → AuthoredNumericExpr SurfaceNumericComputationAtom
  | "NV" => .atom (.valueCount 5 { first := .group (group ["NB"]), rest := [] })
  | "FF" => .atom (.firstFilled { first := .group (group ["NB"]), rest := [] })
  | _ => .atom (.numeric (.filledGroupCount [.fixed (.path { base := .absolute, groups := rowsPath ++ ["Box"] }),
      .fixed (.path { base := .absolute, groups := rowsPath ++ ["Pad"] })]))

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def step? (target : String) : Option (CheckedNumericComputationTable model) :=
  (elaborateCompleteNumericTargetComputationTable model
    (if target == "SX" then subPath else rowsPath) (idOf target) [(none, expression target)]
    (targetScope := .row)).toOption

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan (← (targets ++ ["SX"]).mapM step?)).toOption

private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  { address := { field := idOf name, path }, stored := text
    raw := match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
    numericDecimal := text.toInt?.map ({ unscaled := ·, scale := 0 }) }

/-- A cell for each present text, `""` standing for an absent one. -/
private def present (name : String) (path : List Nat) (text : String) : List ClassifiedCellInput :=
  if text == "" then [] else [cell name path text]

/-- One `Rows` row: its `N1`, `N2`, `BX` and `PX` texts and the `IV` texts of its `Sub` rows. -/
private structure RowInput where
  n1 : String := ""
  n2 : String := ""
  box : String := ""
  pad : String := ""
  subs : List String := []
  deriving Inhabited

/-- One document of the given `Rows` rows, every target seeded with `99`. -/
private def document? (rows : List RowInput) : Option (CheckedDocument model) :=
  let indexed := rows.zipIdx.map fun (row, index) => (row, index + 1)
  (checkDocument prepared "en_US" {
    instantiatedRows := indexed.flatMap fun (row, r) =>
      { group := 10, path := [r] } :: row.subs.zipIdx.map fun (_, s) => { group := 20, path := [r, s + 1] }
    cells := indexed.flatMap fun (row, r) =>
      targets.map (cell · [r] "99") ++ present "N1" [r] row.n1 ++ present "N2" [r] row.n2 ++
        present "BX" [r] row.box ++ present "PX" [r] row.pad ++
        row.subs.zipIdx.flatMap fun (iv, s) => cell "SX" [r, s + 1] "99" :: present "IV" [r, s + 1] iv
  }).toOption

/-- The stored amount, or `-` for a target the Kernel reports cleared without a formal error at it. -/
private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue | .inheritedPoison _ => some "-"
  | .invalidNoValue _ | .rejected _ _ => none

/-- Every outcome as `target row value`, its row written `r` or `r.s`, sorted. -/
private def outcomes? (rows : List RowInput) : Option (List String) := do
  let plan ← plan?
  let input ← document? rows
  let outcomes ← (plan.execute world input).toOption
  let rendered ← outcomes.mapM fun outcome => (reported outcome.outcome).map fun value =>
    s!"{names.getD outcome.targetField.field ""} {".".intercalate
      (outcome.targetField.path.map toString)} {value}"
  pure (rendered.mergeSort (decide <| · ≤ ·))

private def clean : List RowInput :=
  [{ n1 := "5", n2 := "7", box := "1", pad := "1", subs := ["1", "2"] },
    { n2 := "5", pad := "1", subs := ["3"] }, {}]

/- `o01`: each row reads its own `NB`, the second's first filled member its `N2`; each `Sub` row counts
its enclosing row's `Box` and `Pad`. -/
example :
    outcomes? clean = some ["FF 1 5", "FF 2 5", "FF 3 0", "NV 1 1", "NV 2 1", "NV 3 0", "SX 1.1 2",
      "SX 1.2 2", "SX 2.1 1"] := by
  native_decide

/- `o02`: a malformed `N1` clears its own row's scan and count, the other rows computing. -/
example :
    outcomes? ({ clean.head! with n1 := "x" } :: clean.tail) = some ["FF 1 -", "FF 2 5", "FF 3 0",
      "NV 1 -", "NV 2 1", "NV 3 0", "SX 1.1 2", "SX 1.2 2", "SX 2.1 1"] := by
  native_decide

/- `o03`: an over-limit `Sub` row and an over-limit `Rows` row clear their own targets and leave every
other row unchanged. -/
example :
    outcomes? ({ clean.head! with subs := ["1", "2", "3"] } :: clean.tail ++
        [{ n1 := "5", box := "1", pad := "1", subs := ["1"] }]) = some
      ["FF 1 5", "FF 2 5", "FF 3 0", "FF 4 -", "NV 1 1", "NV 2 1", "NV 3 0", "NV 4 -", "SX 1.1 2",
        "SX 1.2 2", "SX 1.3 -", "SX 2.1 1", "SX 4.1 -"] := by
  native_decide

/- `o04`: an empty `NB` scans and counts to zero, and an empty `Box` and `Pad` count nothing. -/
example :
    outcomes? [{ subs := [""] }, { n2 := "6" }, {}] = some ["FF 1 0", "FF 2 6", "FF 3 0", "NV 1 0",
      "NV 2 0", "NV 3 0", "SX 1.1 0"] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowGroups
