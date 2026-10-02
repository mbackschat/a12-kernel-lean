import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: group operands read from inside a row

A repeatable `Rows` (at most three rows) holds fixed `TB` of String `T1` and `T2`, `BB` of Boolean
`B1` and `B2`, `NB` of Number `N1` and `N2`, `Box` and `Pad` of `BX` and `PX`, and a repeatable `Sub`
(at most two) of `IV`, beside a fixed root `TR` of String `R1` and `R2`. At every `Rows` row
`TV = NumberOfValueInFields("a" In TB)`, `BV = NumberOfValueInFields(True In BB)`,
`NV = NumberOfValueInFields(5 In NB)` and `FF = FirstFilledValue(NB)` read the row's own group and
`TR = NumberOfValueInFields("r" In /Rg/TR)` the root's, and at every `Sub` row
`SX = NumberOfFilledGroups(/Rg/Rows/Box, /Rg/Rows/Pad)` reads its enclosing row's `Box` and `Pad`, every
target seeded with `99`. The documents are the Kernel's rows of the
[row-group grid](../../evidence/kernel-30.8.1/captures/row-groups-2026-10-02/), measured on both
codegen strategies. A root Number `RN` and a repeatable `Oth` (at most two) of Number `OT` serve only
the static refusals at the end.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowGroups

open A12Kernel

private def rowsPath : GroupPath := ["Rg", "Rows"]
private def subPath : GroupPath := rowsPath ++ ["Sub"]

private def targets : List String := ["TV", "BV", "NV", "FF", "TR"]

private def names : List String :=
  targets ++ ["T1", "T2", "B1", "B2", "N1", "N2", "BX", "PX", "IV", "SX", "R1", "R2", "RN", "OT"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let (groupPath, repeatableScope) : GroupPath × List RepeatableLevel := match name with
    | "T1" | "T2" => (rowsPath ++ ["TB"], [10])
    | "B1" | "B2" => (rowsPath ++ ["BB"], [10])
    | "R1" | "R2" => (["Rg", "TR"], [])
    | "RN" => (["Rg"], [])
    | "OT" => (["Rg", "Oth"], [30])
    | "N1" | "N2" => (rowsPath ++ ["NB"], [10])
    | "BX" => (rowsPath ++ ["Box"], [10])
    | "PX" => (rowsPath ++ ["Pad"], [10])
    | "IV" | "SX" => (subPath, [10, 20])
    | _ => (rowsPath, [10])
  let kind : FieldKind := match name with
    | "T1" | "T2" | "R1" | "R2" => .string
    | "B1" | "B2" => .boolean
    | _ => .number { scale := 0, signed := true }
  { id := idOf name, groupPath, name, repeatableScope, policy := { kind } }

private def model : FlatModel where
  fields := names.map declaration
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 3 },
    { level := 20, path := subPath, repeatability := some 2 },
    { level := 30, path := ["Rg", "Oth"], repeatability := some 2 }]

private def group (path : List String) : SurfaceGroupReference := .path { base := .relative 0, groups := path }

private def expression : String → AuthoredNumericExpr SurfaceNumericComputationAtom
  | "TV" => .atom (.tokenEntityValueCount "a" { first := .group (group ["TB"]), rest := [] })
  | "TR" => .atom (.tokenEntityValueCount "r"
      { first := .group (.path { base := .absolute, groups := ["Rg", "TR"] }), rest := [] })
  | "BV" => .atom (.booleanValueCount true { first := .group (group ["BB"]), rest := [] })
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

/-- A cell parsed by its field's kind, a Number text that is no integer rejected as malformed. -/
private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  let raw : RawCell := match (declaration name).policy.kind with
    | .boolean => classifyStoredBooleanText text
    | .string => .parsed (.str text)
    | _ => match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
  { address := { field := idOf name, path }, stored := text, raw
    numericDecimal := text.toInt?.map ({ unscaled := ·, scale := 0 }) }

/-- A cell for each present text, `""` standing for an absent one. -/
private def present (name : String) (path : List Nat) (text : String) : List ClassifiedCellInput :=
  if text == "" then [] else [cell name path text]

/-- One `Rows` row: its `T1`, `T2`, `B1`, `B2`, `N1`, `N2`, `BX` and `PX` texts and the `IV` texts of
its `Sub` rows. -/
private structure RowInput where
  t1 : String := ""
  t2 : String := ""
  b1 : String := ""
  b2 : String := ""
  n1 : String := ""
  n2 : String := ""
  box : String := ""
  pad : String := ""
  subs : List String := []
  deriving Inhabited

/-- One document of the given `Rows` rows and root `R1` text, every target seeded with `99`. -/
private def document? (rows : List RowInput) (r1 : String) : Option (CheckedDocument model) :=
  let indexed := rows.zipIdx.map fun (row, index) => (row, index + 1)
  (checkDocument prepared "en_US" {
    instantiatedRows := indexed.flatMap fun (row, r) =>
      { group := 10, path := [r] } :: row.subs.zipIdx.map fun (_, s) => { group := 20, path := [r, s + 1] }
    cells := present "R1" [] r1 ++ indexed.flatMap fun (row, r) =>
      targets.map (cell · [r] "99") ++ present "T1" [r] row.t1 ++ present "T2" [r] row.t2 ++
        present "B1" [r] row.b1 ++ present "B2" [r] row.b2 ++ present "N1" [r] row.n1 ++
        present "N2" [r] row.n2 ++ present "BX" [r] row.box ++ present "PX" [r] row.pad ++
        row.subs.zipIdx.flatMap fun (iv, s) => cell "SX" [r, s + 1] "99" :: present "IV" [r, s + 1] iv
  }).toOption

/-- The stored amount; a cleared target as `-` when it is clean and `poison` when it carries a read
fault, both of which the Kernel reports as cleared. -/
private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue => some "-"
  | .inheritedPoison _ => some "poison"
  | .invalidNoValue _ | .rejected _ _ => none

/-- Every outcome as `target row value`, its row written `r` or `r.s`, sorted. -/
private def outcomes? (rows : List RowInput) (r1 : String := "r") : Option (List String) := do
  let plan ← plan?
  let input ← document? rows r1
  let outcomes ← (plan.execute world input).toOption
  let rendered ← outcomes.mapM fun outcome => (reported outcome.outcome).map fun value =>
    s!"{names.getD outcome.targetField.field ""} {".".intercalate
      (outcome.targetField.path.map toString)} {value}"
  pure (rendered.mergeSort (decide <| · ≤ ·))

private def clean : List RowInput :=
  [{ t1 := "a", t2 := "a", b1 := "true", b2 := "false", n1 := "5", n2 := "7", box := "1", pad := "1",
      subs := ["1", "2"] },
    { t2 := "a", b2 := "true", n2 := "5", pad := "1", subs := ["3"] }, {}]

/- `o01`: each row reads its own `TB`, `BB` and `NB`, the second's first filled member its `N2`, and
every row the same root `TR`; each `Sub` row counts its enclosing row's `Box` and `Pad`. -/
example :
    outcomes? clean = some
      ["BV 1 1", "BV 2 1", "BV 3 0", "FF 1 5", "FF 2 5", "FF 3 0", "NV 1 1", "NV 2 1", "NV 3 0",
       "SX 1.1 2", "SX 1.2 2", "SX 2.1 1", "TR 1 1", "TR 2 1", "TR 3 1", "TV 1 2", "TV 2 1",
       "TV 3 0"] := by
  native_decide

/- `o02`: a malformed `N1` poisons its own row's scan and count and a malformed `B1` its Boolean count,
the row's String counts and the other rows computing. -/
example :
    outcomes? ({ clean.head! with b1 := "maybe", n1 := "x" } :: clean.tail) = some
      ["BV 1 poison", "BV 2 1", "BV 3 0", "FF 1 poison", "FF 2 5", "FF 3 0", "NV 1 poison", "NV 2 1",
       "NV 3 0",
       "SX 1.1 2", "SX 1.2 2", "SX 2.1 1", "TR 1 1", "TR 2 1", "TR 3 1", "TV 1 2", "TV 2 1",
       "TV 3 0"] := by
  native_decide

/- `o03`: an over-limit `Sub` row and an over-limit `Rows` row clear their own targets clean, the root
count included, and leave every other row unchanged. -/
example :
    outcomes? ({ clean.head! with subs := ["1", "2", "3"] } :: clean.tail ++
        [{ t1 := "a", b1 := "true", n1 := "5", box := "1", pad := "1", subs := ["1"] }]) = some
      ["BV 1 1", "BV 2 1", "BV 3 0", "BV 4 -", "FF 1 5", "FF 2 5", "FF 3 0", "FF 4 -", "NV 1 1",
       "NV 2 1", "NV 3 0", "NV 4 -", "SX 1.1 2", "SX 1.2 2", "SX 1.3 -", "SX 2.1 1", "SX 4.1 -",
       "TR 1 1", "TR 2 1", "TR 3 1", "TR 4 -", "TV 1 2", "TV 2 1", "TV 3 0", "TV 4 -"] := by
  native_decide

/- `o04`: empty groups scan and count to zero, and members holding other values count nothing. -/
example :
    outcomes? [{ subs := [""] }, { t2 := "b", b2 := "false", n2 := "6" }, {}] "" = some
      ["BV 1 0", "BV 2 0", "BV 3 0", "FF 1 0", "FF 2 6", "FF 3 0", "NV 1 0", "NV 2 0", "NV 3 0",
       "SX 1.1 0", "TR 1 0", "TR 2 0", "TR 3 0", "TV 1 0", "TV 2 0", "TV 3 0"] := by
  native_decide

/-- Whether `SX`'s count, written at `target` in `declaringGroup`, is refused at its first operand
because nothing binds that operand's `Rows` level. -/
private def refusesUnboundRows (declaringGroup : GroupPath) (target : String)
    (scope : ComputationTargetScope) : Bool :=
  match elaborateCompleteNumericTargetComputationTable model declaringGroup (idOf target)
      [(none, expression "SX")] (targetScope := scope) with
  | .error (.operation _ (.groupReference (.unboundOperandLevel ["Rg", "Rows", "Box"] _))) => true
  | _ => false

/- The count reads `Box` and `Pad` as the instance of the `Rows` row binding them, so where no row
binds `Rows`, at the root's fixed `RN` or at a row of the unrelated repeatable `Oth`, elaboration
refuses it before any row is read. -/
example : refusesUnboundRows ["Rg"] "RN" .fixed ∧ refusesUnboundRows ["Rg", "Oth"] "OT" .row := by
  native_decide

/- The token count over the shared entity-list shape meets that shape's gates: `TB` authored twice is
refused as a repeated group, which the projection-bearing form has no group slot to ask. -/
example :
    (match elaborateCompleteNumericTargetComputationTable model rowsPath (idOf "TV")
        [(none, .atom (.tokenEntityValueCount "a"
          { first := .group (group ["TB"]), rest := [.group (group ["TB"])] }))]
        (targetScope := .row) with
      | .error (.operation _ (.tokenValueCount (.source (.shape
          (.duplicateGroupOperand ["Rg", "Rows", "TB"]))))) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowGroups
