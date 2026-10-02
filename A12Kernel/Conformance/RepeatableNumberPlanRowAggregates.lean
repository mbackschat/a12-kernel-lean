import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: star aggregates read from inside a row

Number aggregates over a star, each elaborated at a repeatable target and run at every row. A
repeatable `Rows` (at most three rows) holds a repeatable `Sub` (at most two), beside a repeatable
`Oth`. At a `Rows` target `S = Sum(Sub*/IA)`, `M = MaxValue(Sub*/IA)` and `SC = Sum(Sub*/IC)` read the
row's own `Sub` rows, `ALL = Sum(/Rg/Rows*/CA)` and `AMX = MaxValue(/Rg/Rows*/A)` every `Rows` row,
`SIB = Sum(/Rg/Oth*/OX)` every `Oth` row, and `SG = Sum(/Rg/Rows*/A Having [/Rg/Rows/A] > [$A])` every
`Rows` row whose `A` exceeds the computing row's own. At a `Sub` target `ISUM = Sum(../Sub*/IA)` reads
the enclosing row's `Sub` rows and `IALL = Sum(../../Rows*/Sub*/IA)` every `Sub` row of every `Rows`
row. `CA = [A]` and `IC = [IA]` are copies, and every reader is authored ahead of what it reads. Every
target is seeded with a stale `99`. The documents are the Kernel's rows of the
[row-aggregate grid](../../evidence/kernel-30.8.1/captures/row-star-aggregates-2026-10-02/), measured
on both codegen strategies.

So a star binds only the repeatable levels above its first starred level to the computing row, and
reopens the starred level fully ([`spec/09`](../../spec/09-computations.md) §5), which is the star
addressing the validation arm already uses. The rows separate that from an own-row collapse and from
a union over every enclosing row, a fresh computed copy from its seed, a malformed source that clears
exactly the rows whose star reaches it, an over-limit row left out of every star that spans it, and an
empty star, which sums and maximizes to zero.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowAggregates

open A12Kernel

private def rowsPath : GroupPath := ["Rg", "Rows"]
private def subPath : GroupPath := rowsPath ++ ["Sub"]
private def othPath : GroupPath := ["Rg", "Oth"]

private def rowsNames : List String := ["A", "CA", "S", "M", "SC", "ALL", "AMX", "SIB", "SG"]
private def subNames : List String := ["IA", "IC", "ISUM", "IALL"]

private def names : List String := rowsNames ++ subNames ++ ["OX"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let (groupPath, repeatableScope) :=
    if rowsNames.contains name then (rowsPath, [10])
    else if subNames.contains name then (subPath, [10, 20])
    else (othPath, [30])
  { id := idOf name, groupPath, name, repeatableScope
    policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel where
  fields := names.map declaration
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 3 },
    { level := 20, path := subPath, repeatability := some 2 },
    { level := 30, path := othPath, repeatability := some 2 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def star (base : PathBase) (groups : List (String × Bool)) (field : String) :
    SurfaceStarFieldPath :=
  { base, groups := groups.map fun (name, starred) => { name, starred }, field }

private def aggregate (op : NumericAggregateOp) (operand : SurfaceFieldEntityOperand) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.aggregate op { first := operand, rest := [] }))

private def copy (field : String) : AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.field { base := .relative 0, groups := [], field }))

/-- `[/Rg/Rows/A] > [$A]`, a starred row's `A` against the computing row's own. -/
private def greaterThanOwn : SurfaceCorrelatedHaving :=
  .compareNumbers .greater
    { origin := .inner, field := { base := .absolute, groups := rowsPath, field := "A" } }
    { origin := .outer, field := { base := .relative 0, groups := [], field := "A" } }

private def step? (group : GroupPath) (target : String)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) :=
  (elaborateCompleteNumericTargetComputationTable model group (idOf target) [(none, expression)]
    (targetScope := .row)).toOption

/-- The grid's computations in its authored order, every reader ahead of what it reads. -/
private def authored : List (Option (CheckedNumericComputationTable model)) :=
  [step? rowsPath "S" (aggregate .sum (.star (star (.relative 0) [("Sub", true)] "IA"))),
    step? rowsPath "M" (aggregate .maximum (.star (star (.relative 0) [("Sub", true)] "IA"))),
    step? rowsPath "SC" (aggregate .sum (.star (star (.relative 0) [("Sub", true)] "IC"))),
    step? rowsPath "ALL" (aggregate .sum (.star (star .absolute [("Rg", false), ("Rows", true)] "CA"))),
    step? rowsPath "AMX" (aggregate .maximum (.star (star .absolute [("Rg", false), ("Rows", true)] "A"))),
    step? rowsPath "SIB" (aggregate .sum (.star (star .absolute [("Rg", false), ("Oth", true)] "OX"))),
    step? rowsPath "SG" (aggregate .sum
      (.starHaving (star .absolute [("Rg", false), ("Rows", true)] "A") greaterThanOwn)),
    step? rowsPath "CA" (copy "A"),
    step? subPath "ISUM" (aggregate .sum (.star (star (.relative 1) [("Sub", true)] "IA"))),
    step? subPath "IALL" (aggregate .sum (.star (star (.relative 2) [("Rows", true), ("Sub", true)] "IA"))),
    step? subPath "IC" (copy "IA")]

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan (← authored.mapM id)).toOption

private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  { address := { field := idOf name, path }, stored := text
    raw := match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
    numericDecimal := text.toInt?.map ({ unscaled := ·, scale := 0 }) }

/-- A cell for each present text, `""` standing for an absent one. -/
private def present (name : String) (path : List Nat) (text : String) : List ClassifiedCellInput :=
  if text == "" then [] else [cell name path text]

/-- One `Rows` row: its `A` text and the `IA` texts of its `Sub` rows. -/
private abbrev RowInput := String × List String

/-- One document of the given `Rows` rows and `OX` texts, every target seeded with `99`. -/
private def document? (rows : List RowInput) (others : List String) : Option (CheckedDocument model) :=
  let indexed := rows.zipIdx.map fun (row, index) => (row, index + 1)
  (checkDocument prepared "en_US" {
    instantiatedRows :=
      indexed.flatMap (fun ((_, subs), r) =>
        { group := 10, path := [r] } :: subs.zipIdx.map fun (_, s) => { group := 20, path := [r, s + 1] }) ++
      others.zipIdx.map fun (_, o) => { group := 30, path := [o + 1] }
    cells :=
      indexed.flatMap (fun ((a, subs), r) =>
        (rowsNames.drop 1).map (cell · [r] "99") ++ present "A" [r] a ++
          subs.zipIdx.flatMap fun (ia, s) =>
            (subNames.drop 1).map (cell · [r, s + 1] "99") ++ present "IA" [r, s + 1] ia) ++
      others.zipIdx.flatMap fun (ox, o) => present "OX" [o + 1] ox
  }).toOption

/-- The stored amount, or `-` for a target the Kernel reports cleared without a formal error at it. -/
private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue | .inheritedPoison _ => some "-"
  | .invalidNoValue _ | .rejected _ _ => none

/-- Every outcome as `target row value`, its row written `r` or `r.s`, sorted. -/
private def outcomes? (rows : List RowInput) (others : List String) : Option (List String) := do
  let plan ← plan?
  let input ← document? rows others
  let outcomes ← (plan.execute world input).toOption
  let rendered ← outcomes.mapM fun outcome => (reported outcome.outcome).map fun value =>
    s!"{names.getD outcome.targetField.field ""} {".".intercalate
      (outcome.targetField.path.map toString)} {value}"
  pure (rendered.mergeSort (decide <| · ≤ ·))

private def others : List String := ["7", "9"]

/- `g01`: `S`, `M` and `SC` read the row's own `Sub` rows, a third row with none summing and
maximizing to zero; `ALL`, `AMX`, `SIB` and `SG` span every row; `ISUM` reads the enclosing row's
`Sub` rows and `IALL` every one. -/
example :
    outcomes? [("1", ["2", "3"]), ("4", ["6"]), ("10", [])] others = some
      ["ALL 1 15", "ALL 2 15", "ALL 3 15", "AMX 1 10", "AMX 2 10", "AMX 3 10", "CA 1 1", "CA 2 4",
      "CA 3 10", "IALL 1.1 11", "IALL 1.2 11", "IALL 2.1 11", "IC 1.1 2", "IC 1.2 3", "IC 2.1 6",
      "ISUM 1.1 5", "ISUM 1.2 5", "ISUM 2.1 6", "M 1 3", "M 2 6", "M 3 0", "S 1 5", "S 2 6", "S 3 0",
      "SC 1 5", "SC 2 6", "SC 3 0", "SG 1 14", "SG 2 10", "SG 3 0", "SIB 1 16", "SIB 2 16",
      "SIB 3 16"] := by
  native_decide

/- `g02`: a malformed `IA` under the first row clears exactly the readers whose star reaches it: the
first row's `S`, `M` and `SC`, its own `ISUM`s, and every `IALL`, the second row computing. -/
example :
    outcomes? [("1", ["2", "x"]), ("4", ["6"]), ("10", [])] others = some
      ["ALL 1 15", "ALL 2 15", "ALL 3 15", "AMX 1 10", "AMX 2 10", "AMX 3 10", "CA 1 1", "CA 2 4",
      "CA 3 10", "IALL 1.1 -", "IALL 1.2 -", "IALL 2.1 -", "IC 1.1 2", "IC 1.2 -", "IC 2.1 6",
      "ISUM 1.1 -", "ISUM 1.2 -", "ISUM 2.1 6", "M 1 -", "M 2 6", "M 3 0", "S 1 -", "S 2 6", "S 3 0",
      "SC 1 -", "SC 2 6", "SC 3 0", "SG 1 14", "SG 2 10", "SG 3 0", "SIB 1 16", "SIB 2 16",
      "SIB 3 16"] := by
  native_decide

/- `g03`: a malformed `A` clears its `CA` and, at every row, the `ALL`, `AMX` and `SG` spanning it,
`SG`'s filter reading it at every starred row. -/
example :
    outcomes? [("1", ["2", "3"]), ("x", ["6"]), ("10", [])] others = some
      ["ALL 1 -", "ALL 2 -", "ALL 3 -", "AMX 1 -", "AMX 2 -", "AMX 3 -", "CA 1 1", "CA 2 -",
      "CA 3 10", "IALL 1.1 11", "IALL 1.2 11", "IALL 2.1 11", "IC 1.1 2", "IC 1.2 3", "IC 2.1 6",
      "ISUM 1.1 5", "ISUM 1.2 5", "ISUM 2.1 6", "M 1 3", "M 2 6", "M 3 0", "S 1 5", "S 2 6", "S 3 0",
      "SC 1 5", "SC 2 6", "SC 3 0", "SG 1 -", "SG 2 -", "SG 3 -", "SIB 1 16", "SIB 2 16", "SIB 3 16"] := by
  native_decide

/- `g04`: an over-limit `Sub` row and an over-limit `Rows` row, each holding `100`, are cleared and left
out of every star spanning them, which `M` and `AMX` separate from a read. -/
example :
    outcomes? [("1", ["2", "3", "100"]), ("4", ["6"]), ("10", []), ("100", [])] others = some
      ["ALL 1 15", "ALL 2 15", "ALL 3 15", "ALL 4 -", "AMX 1 10", "AMX 2 10", "AMX 3 10", "AMX 4 -",
      "CA 1 1", "CA 2 4", "CA 3 10", "CA 4 -", "IALL 1.1 11", "IALL 1.2 11", "IALL 1.3 -",
      "IALL 2.1 11", "IC 1.1 2", "IC 1.2 3", "IC 1.3 -", "IC 2.1 6", "ISUM 1.1 5", "ISUM 1.2 5",
      "ISUM 1.3 -", "ISUM 2.1 6", "M 1 3", "M 2 6", "M 3 0", "M 4 -", "S 1 5", "S 2 6", "S 3 0",
      "S 4 -", "SC 1 5", "SC 2 6", "SC 3 0", "SC 4 -", "SG 1 14", "SG 2 10", "SG 3 0", "SG 4 -",
      "SIB 1 16", "SIB 2 16", "SIB 3 16", "SIB 4 -"] := by
  native_decide

/- `g05`: an empty `IA` and an empty `A` read as zero, `SG` comparing against the computing row's zero,
and no `Oth` row sums to zero. -/
example :
    outcomes? [("1", ["", "4"]), ("", ["6"]), ("10", [])] [] = some
      ["ALL 1 11", "ALL 2 11", "ALL 3 11", "AMX 1 10", "AMX 2 10", "AMX 3 10", "CA 1 1", "CA 2 0",
      "CA 3 10", "IALL 1.1 10", "IALL 1.2 10", "IALL 2.1 10", "IC 1.1 0", "IC 1.2 4", "IC 2.1 6",
      "ISUM 1.1 4", "ISUM 1.2 4", "ISUM 2.1 6", "M 1 4", "M 2 6", "M 3 0", "S 1 4", "S 2 6", "S 3 0",
      "SC 1 4", "SC 2 6", "SC 3 0", "SG 1 10", "SG 2 11", "SG 3 0", "SIB 1 0", "SIB 2 0", "SIB 3 0"] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowAggregates
