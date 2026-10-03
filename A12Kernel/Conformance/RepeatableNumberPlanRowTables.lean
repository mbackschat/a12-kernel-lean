import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: complete Number tables at a row

Row steps over the complete Number surface, each a Number table elaborated at its repeatable target and
run at every row. A repeatable `Rows` (at most three rows) declares `CA = [A]` and, authored ahead of
it, `MX = Max([CA], [B])`, `DV = RoundAccounting([CA] / [B], 2)`, `AB = Abs([CA] - [B])`,
`FF = FirstFilledValue(CA, B)`, `VN = NumberOfValueInFields(5 In CA, B)`, and the guards `K = 1` under
`FieldFilled(FF)` and `KN = 1` under `FieldNotFilled(FF)`. Every target is seeded with a stale `99`. The
documents are the Kernel's rows of the
[row-producer grid](../../evidence/kernel-30.8.1/captures/repeatable-row-producers-2026-10-02/),
measured on both codegen strategies.

The rows separate a fresh per-row read of `CA` from its seed, an empty `A` copied as zero from a
cleared copy, a malformed `A` whose poison reaches every reader of its row, an over-limit row cleared
without evaluation, and a zero or empty divisor, which clears only the division.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowTables

open A12Kernel

private def names : List String := ["A", "B", "CA", "MX", "DV", "AB", "FF", "VN", "K", "KN"]

private def idOf (name : String) : FieldId := names.idxOf name

private def rowsPath : GroupPath := ["Rg", "Rows"]

private def declaration (name : String) : FlatFieldDecl :=
  { id := idOf name, groupPath := rowsPath, name, repeatableScope := [10]
    policy := { kind := .number { scale := if name == "DV" then 2 else 0, signed := true } } }

private def model : FlatModel where
  fields := names.map declaration
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 3 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def read (field : String) : AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.field (bare field)))

private def entities : SurfaceFieldEntitySource :=
  { first := .field (bare "CA"), rest := [.field (bare "B")] }

private def one : DecodedNumericLiteral := { value := 1, authoredScale := 0 }

private def step? (target : String) (guard : Option (CheckedComputationCondition model))
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) :=
  (elaborateCompleteNumericTargetComputationTable model rowsPath (idOf target)
    [(guard, expression)] (targetScope := .row)).toOption

/-- The grid's computations in its authored order, every reader ahead of `CA`. -/
private def authored : List (Option (CheckedNumericComputationTable model)) :=
  [step? "K" (some (.fieldFilled (idOf "FF"))) (.literal one),
    step? "KN" (some (.fieldNotFilled (idOf "FF"))) (.literal one),
    step? "MX" none (.extremumCall .maximum (.extremum .maximum (read "CA") (read "B"))),
    step? "DV" none (.round .halfUp ⟨2, by decide⟩ (.binary .divide (read "CA") (read "B"))),
    step? "AB" none (.abs (.binary .subtract (read "CA") (read "B"))),
    step? "FF" none (.atom (.firstFilled entities)),
    step? "VN" none (.atom (.valueCount 5 entities)),
    step? "CA" none (read "A")]

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan (← authored.mapM id)).toOption

private def cell (name : String) (row : Nat) (text : String) : ClassifiedCellInput :=
  { address := { field := idOf name, path := [row] }, stored := text
    raw := match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
    numericDecimal := text.toInt?.map ({ unscaled := ·, scale := 0 }) }

private def seeded : List String := ["CA", "MX", "DV", "AB", "FF", "VN", "K", "KN"]

/-- One document whose rows hold the given `A` and `B` texts, `""` for an absent cell. -/
private def document? (rows : List (String × String)) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.zipIdx.map fun (_, index) => { group := 10, path := [index + 1] }
    cells := rows.zipIdx.flatMap fun ((a, b), index) =>
      seeded.map (cell · (index + 1) "99") ++
        ([("A", a), ("B", b)].filter (·.2 != "")).map fun (name, text) => cell name (index + 1) text
  }).toOption

/-- The stored amount, `-` for a target the Kernel reports cleared without a formal error at it, and
`domain` for one it clears with its calculation-value error at the target. -/
private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue | .inheritedPoison _ => some "-"
  | .invalidNoValue .calculationValue => some "domain"
  | .rejected _ _ => none

/-- Every row's `CA`, `MX`, `DV`, `AB`, `FF`, `VN`, `K` and `KN`, in row order. -/
private def rows? (rows : List (String × String)) : Option (List (List String)) := do
  let plan ← plan?
  let input ← document? rows
  let outcomes ← (plan.execute world input).toOption
  let found ← outcomes.mapM fun outcome => (reported outcome.outcome).map (outcome.targetField, ·)
  (List.range rows.length).mapM fun index => seeded.mapM fun name =>
    (found.find? (·.1 == { field := idOf name, path := [index + 1] })).map (·.2)

/- Row `r1`: a fresh `CA` read at its own row, an empty `A` copied as zero, which `FF` then holds, a
malformed `A` whose poison reaches every reader of its row and both guards, and a fourth row beyond the
capacity of three, cleared without evaluation. -/
example :
    rows? [("5", "2"), ("", "3"), ("x", "4"), ("7", "1")] = some [
      ["5", "5", "2.5", "3", "5", "1", "1", "-"],
      ["0", "3", "0", "3", "0", "0", "1", "-"],
      ["-", "-", "-", "-", "-", "-", "-", "-"],
      ["-", "-", "-", "-", "-", "-", "-", "-"]] := by
  native_decide

/- Row `r2`: an empty and a zero divisor clear only the division, as a domain failure, every other
reader of the row computing, and a quotient is kept at the target's two places. -/
example :
    rows? [("5", ""), ("0", "0"), ("9", "5")] = some [
      ["5", "5", "domain", "5", "5", "1", "1", "-"],
      ["0", "0", "domain", "0", "0", "0", "1", "-"],
      ["9", "9", "1.8", "4", "9", "1", "1", "-"]] := by
  native_decide

/- Every reader runs after the `CA` it reads, and `K` and `KN` after the `FF` their guards read; only
those producer-before-reader pairs are measured, the rest is the shared rule's earliest-ready order. -/
example : (plan?.map fun plan => plan.execution.map (·.targetField)) =
    some ([("CA" : String), "MX", "DV", "AB", "FF", "K", "KN", "VN"].map idOf) := by
  native_decide

/-- A row `T` beside fixed `Box`, holding a nested repeatable `In`, `Pad` and `Pad2` inside the row,
and fixed `Out`, holding a repeatable `OutRows`, and `Out2` outside it, for the reading scope's static
boundary. -/
private def nested : FlatModel where
  fields := [("T", rowsPath, [10]), ("S", rowsPath ++ ["Box", "In"], [10, 20]),
      ("U", rowsPath ++ ["Pad"], [10]), ("V", rowsPath ++ ["Pad2"], [10]),
      ("W", ["Rg", "Out"], []), ("X", ["Rg", "Out", "OutRows"], [30]), ("Y", ["Rg", "Out2"], [])].zipIdx.map
    fun ((name, groupPath, repeatableScope), id) =>
      { id, groupPath, name, repeatableScope, policy := { kind := .number { scale := 0, signed := true } } }
  repeatableGroups := [{ level := 10, path := rowsPath },
    { level := 20, path := rowsPath ++ ["Box", "In"] }, { level := 30, path := ["Rg", "Out", "OutRows"] }]

private def nestedTable (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable nested) :=
  elaborateCompleteNumericTargetComputationTable nested rowsPath 0 [(none, expression)]
    (targetScope := .row)

/-- `NumberOfFilledGroups` over two fixed groups, each `parents` levels up and then down `groups`. -/
private def groupCount (operands : List (Nat × List String)) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.filledGroupCount (operands.map fun (parents, groups) =>
    .fixed (.path { base := .relative parents, groups }))))

/-- The plan's refusal of a one-table plan at the row target, `none` where it certifies. -/
private def planned (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (Option RepeatableNumberPlanError) :=
  (nestedTable expression).toOption.map fun table =>
    match certifyRepeatableNumberPlan [table] with
    | .ok _ => none
    | .error error => some error

/- The target's scope binds only its own levels: a read crossing the nested level below it is refused
`MVK_NO_WILDCARD` ([`spec/09`](../../spec/09-computations.md) §5). A count of fixed groups inside the
row certifies, whether a group holds a repeatable level or not, reading the instance the row binds as
the [row-atom grid](../../docs/sources/computation-scheduling-probes.md#src-row-atoms) measures; a
count of fixed groups outside the row certifies too, one holding a repeatable level included. -/
example :
    (match nestedTable (.atom (.numeric (.field { base := .relative 0, groups := ["Box", "In"], field := "S" }))) with
      | .error error => error.diagnostic? == some .noWildcard
      | .ok _ => false) = true ∧
    planned (groupCount [(0, ["Pad"]), (0, ["Pad2"])]) = some none ∧
    planned (groupCount [(0, ["Box"]), (0, ["Pad"])]) = some none ∧
    planned (groupCount [(1, ["Out"]), (1, ["Out2"])]) = some none := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowTables
