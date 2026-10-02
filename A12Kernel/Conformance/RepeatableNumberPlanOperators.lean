import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored two-level repeatable Number plan locks: operators, guards and a fixed computed read

The second two-level grid of the authored repeatable plan. A root `Fix = [Base]` and
`RootSum = Sum(Outer*/OP)`, a repeatable `Outer` (at most two rows) with `OP = [OBase]` under
`FieldFilled(OGate)`, `OSub = [OP] - [/Rows/Fix]`, `OMul = [OP] * [OBase2]`, and `OH`, `OHN` copying
`OBase2` under `FieldFilled(OP)` and `FieldNotFilled(OP)`, and a nested repeatable `Inner` (at most
three rows) with `ISub = [IBase] - [../OP]` and `IMul = [IBase] * [../OP]`. Every reader of `OP` and
`Fix` is authored ahead of what it reads, `RootSum` after the `OP` it sums, and every computed target
is seeded with a stale `99`. The nine documents are the
Kernel's rows at the
[repeatable operator checkpoint](../../docs/sources/computation-scheduling-probes.md#src-repeatable-join-operators-and-guards),
measured on both codegen strategies.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanOperators

open A12Kernel

private def baseId : FieldId := 0
private def fixId : FieldId := 1
private def rootSumId : FieldId := 2
private def oBaseId : FieldId := 3
private def oBase2Id : FieldId := 4
private def oGateId : FieldId := 5
private def opId : FieldId := 6
private def oSubId : FieldId := 7
private def oMulId : FieldId := 8
private def ohId : FieldId := 9
private def ohnId : FieldId := 10
private def iBaseId : FieldId := 11
private def iSubId : FieldId := 12
private def iMulId : FieldId := 13

private def outerPath : GroupPath := ["Rows", "Outer"]
private def innerPath : GroupPath := ["Rows", "Outer", "Inner"]

private def number (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl where
  id
  groupPath := group
  name
  repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } }

private def model : FlatModel where
  fields := [
    number baseId "Base" ["Rows"] [], number fixId "Fix" ["Rows"] [],
    number rootSumId "RootSum" ["Rows"] [],
    number oBaseId "OBase" outerPath [10], number oBase2Id "OBase2" outerPath [10],
    { id := oGateId, groupPath := outerPath, name := "OGate", repeatableScope := [10],
      policy := { kind := .string } },
    number opId "OP" outerPath [10], number oSubId "OSub" outerPath [10],
    number oMulId "OMul" outerPath [10], number ohId "OH" outerPath [10],
    number ohnId "OHN" outerPath [10],
    number iBaseId "IBase" innerPath [10, 20], number iSubId "ISub" innerPath [10, 20],
    number iMulId "IMul" innerPath [10, 20]]
  repeatableGroups := [
    { level := 10, path := outerPath, repeatability := some 2 },
    { level := 20, path := innerPath, repeatability := some 3 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def fixPath : SurfaceFieldPath := { base := .absolute, groups := ["Rows"], field := "Fix" }

private def outerStar : SurfaceStarFieldPath :=
  { base := .relative 0, groups := [{ name := "Outer", starred := true }], field := "OP" }

private def fixedStep? (operation : Option (CheckedNumericTargetComputationOperation model)) :
    Option (CheckedNumericComputationTable model) := do
  let table ← (certifyNumericComputationTable
    [({ precondition := none, operation := ← operation } :
      ComputationAlternative (CheckedNumericTargetComputationOperation model))]).toOption
  pure table

private def rootSum? := fixedStep? (elaborateNumberEntityTargetComputationOperation model ["Rows"]
  rootSumId (.atom (.aggregate .sum { first := .star outerStar, rest := [] }))).toOption

private def fix? := fixedStep?
  (elaborateNumericTargetComputationOperation model ["Rows"] fixId (.atom (.field (bare "Base")))).toOption

private def row? (group : GroupPath) (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : Option ComputationCondition := none) :
    Option (CheckedNumericComputationTable model) :=
  (elaborateNumericTargetComputationTable model group target [(guard, expression)]
    (targetScope := .row)).toOption

private def binary (group : GroupPath) (target : FieldId) (left right : SurfaceFieldPath)
    (op : NumericScaleBinaryOp) : Option (CheckedNumericComputationTable model) :=
  row? group target (.binary op (.atom (.field left)) (.atom (.field right)))

private def copy (group : GroupPath) (target : FieldId) (source : SurfaceFieldPath)
    (guard : ComputationCondition) : Option (CheckedNumericComputationTable model) :=
  row? group target (.atom (.field source)) (some guard)

/-- The model's nine computations in its authored order: every reader of `OP` ahead of it, `OSub`
ahead of `Fix`, and only `RootSum` after the `OP` it sums. -/
private def authored : List (Option (CheckedNumericComputationTable model)) :=
  [binary innerPath iSubId (bare "IBase") (parent "OP") .subtract,
    binary innerPath iMulId (bare "IBase") (parent "OP") .multiply,
    binary outerPath oSubId (bare "OP") fixPath .subtract,
    binary outerPath oMulId (bare "OP") (bare "OBase2") .multiply,
    copy outerPath ohId (bare "OBase2") (.fieldFilled opId),
    copy outerPath ohnId (bare "OBase2") (.fieldNotFilled opId),
    copy outerPath opId (bare "OBase") (.fieldFilled oGateId),
    rootSum?,
    fix?]

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan (← authored.mapM id)).toOption

private inductive Source where
  | value (number : Int)
  | malformed
  | absent

private structure OuterRow where
  base : Source := .value 7
  base2 : Source := .value 3
  gate : Bool := true
  inner : List Source := [.value 1, .value 2]

private def numberCell (field : FieldId) (path : List Nat) (number : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored := toString number, raw := .parsed (.num number) }

private def sourceCells (field : FieldId) (path : List Nat) : Source → List ClassifiedCellInput
  | .value number => [numberCell field path number]
  | .malformed => [{ address := { field, path }, stored := "bad", raw := .rejected .malformed }]
  | .absent => []

private def seeded (fields : List FieldId) (path : List Nat) : List ClassifiedCellInput :=
  fields.map (numberCell · path 99)

private def document? (base : Source) (rows : List OuterRow) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.zipIdx.flatMap fun (row, outer) =>
      { group := 10, path := [outer + 1] } ::
        row.inner.zipIdx.map fun (_, inner) => { group := 20, path := [outer + 1, inner + 1] }
    cells := sourceCells baseId [] base ++ seeded [fixId, rootSumId] [] ++
      rows.zipIdx.flatMap fun (row, outer) =>
        sourceCells oBaseId [outer + 1] row.base ++ sourceCells oBase2Id [outer + 1] row.base2 ++
          (if row.gate then
            [{ address := { field := oGateId, path := [outer + 1] }, stored := "x", raw := .parsed (.str "x") }]
          else []) ++
          seeded [opId, oSubId, oMulId, ohId, ohnId] [outer + 1] ++
          row.inner.zipIdx.flatMap fun (inner, index) =>
            sourceCells iBaseId [outer + 1, index + 1] inner ++
              seeded [iSubId, iMulId] [outer + 1, index + 1]
  }).toOption

private def reported? : NumericTargetOutcome → Option (Option Int)
  | .accepted stored => if stored.scale = 0 then some (some stored.unscaled) else none
  | .noValue | .inheritedPoison _ => some none
  | .rejected _ _ | .invalidNoValue _ => none

private def outcomes? (base : Source) (rows : List OuterRow) :
    Option (List (CellAddr × Option Int)) := do
  let plan ← plan?
  let input ← document? base rows
  let outcomes ← (plan.executeSteps world input plan.execution []).toOption
  outcomes.mapM fun outcome => (reported? outcome.outcome).map (outcome.targetField, ·)

private def secondRow : OuterRow := { base := .value 5, base2 := .value 4, inner := [.value 3] }

/-- Equal as sets of addressed reports: the Kernel sorts its report by field, so the order Lean emits
rows in is not compared. -/
private def reportsAs (base : Source) (rows : List OuterRow)
    (expected : List (CellAddr × Option Int)) : Bool :=
  match outcomes? base rows with
  | some actual => actual.length == expected.length && expected.all actual.contains
  | none => false

private def report (field : FieldId) (path : List Nat) (value : Option Int) : CellAddr × Option Int :=
  ({ field, path }, value)

/- Every reader runs after what it reads, `OSub` after the fixed `Fix`, although all but `RootSum` are
authored ahead of what they read; only those producer-before-reader pairs are measured, the rest is the shared rule's
earliest-ready order. -/
example : (plan?.map fun plan => plan.execution.map (·.targetField)) =
    some [opId, iSubId, iMulId, oMulId, ohId, ohnId, rootSumId, fixId, oSubId] := by
  native_decide

/- Every source readable: subtraction and multiplication read the fresh `OP` and `Fix`, each inner row
   reads its own outer row's `OP`, and the filled guard on `OP` holds while the not-filled one does not. -/
example : reportsAs (.value 10) [{}, secondRow] [
    report fixId [] (some (10)), report iMulId [1, 1] (some (7)), report iSubId [1, 1] (some (-6)),
    report iMulId [1, 2] (some (14)), report iSubId [1, 2] (some (-5)), report ohId [1] (some (3)),
    report ohnId [1] none, report oMulId [1] (some (21)), report opId [1] (some (7)),
    report oSubId [1] (some (-3)), report iMulId [2, 1] (some (15)),
    report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)), report ohnId [2] none,
    report oMulId [2] (some (20)), report opId [2] (some (5)), report oSubId [2] (some (-5)),
    report rootSumId [] (some (12))] := by
  native_decide

/- A malformed outer source poisons its `OP`, which clears every reader in that row and its inner rows,
   both guards on it included, so a fill guard on a poisoned target holds neither way; the aggregate
   clears too. -/
example : reportsAs (.value 10) [{ base := .malformed }, secondRow] [
    report fixId [] (some (10)), report iMulId [1, 1] none, report iSubId [1, 1] none,
    report iMulId [1, 2] none, report iSubId [1, 2] none, report ohId [1] none,
    report ohnId [1] none, report oMulId [1] none, report opId [1] none, report oSubId [1] none,
    report iMulId [2, 1] (some (15)), report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)),
    report ohnId [2] none, report oMulId [2] (some (20)), report opId [2] (some (5)),
    report oSubId [2] (some (-5)), report rootSumId [] none] := by
  native_decide

/- An unmet guard clears `OP` cleanly: its readers substitute zero, the not-filled guard sees the fresh
   clear rather than the seed, and the filled one does not hold. -/
example : reportsAs (.value 10) [{ gate := false }, secondRow] [
    report fixId [] (some (10)), report iMulId [1, 1] (some (0)), report iSubId [1, 1] (some (1)),
    report iMulId [1, 2] (some (0)), report iSubId [1, 2] (some (2)), report ohId [1] none,
    report ohnId [1] (some (3)), report oMulId [1] (some (0)), report opId [1] none,
    report oSubId [1] (some (-10)), report iMulId [2, 1] (some (15)),
    report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)), report ohnId [2] none,
    report oMulId [2] (some (20)), report opId [2] (some (5)), report oSubId [2] (some (-5)),
    report rootSumId [] (some (5))] := by
  native_decide

/- A malformed root source poisons the fixed `Fix`, which clears `OSub` in every row while nothing else
   reads it. -/
example : reportsAs .malformed [{}, secondRow] [
    report fixId [] none, report iMulId [1, 1] (some (7)), report iSubId [1, 1] (some (-6)),
    report iMulId [1, 2] (some (14)), report iSubId [1, 2] (some (-5)), report ohId [1] (some (3)),
    report ohnId [1] none, report oMulId [1] (some (21)), report opId [1] (some (7)),
    report oSubId [1] none, report iMulId [2, 1] (some (15)), report iSubId [2, 1] (some (-2)),
    report ohId [2] (some (4)), report ohnId [2] none, report oMulId [2] (some (20)),
    report opId [2] (some (5)), report oSubId [2] none, report rootSumId [] (some (12))] := by
  native_decide

/- An absent root source copies as zero into `Fix`, so `OSub` answers `OP` in every row. -/
example : reportsAs .absent [{}, secondRow] [
    report fixId [] (some (0)), report iMulId [1, 1] (some (7)), report iSubId [1, 1] (some (-6)),
    report iMulId [1, 2] (some (14)), report iSubId [1, 2] (some (-5)), report ohId [1] (some (3)),
    report ohnId [1] none, report oMulId [1] (some (21)), report opId [1] (some (7)),
    report oSubId [1] (some (7)), report iMulId [2, 1] (some (15)),
    report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)), report ohnId [2] none,
    report oMulId [2] (some (20)), report opId [2] (some (5)), report oSubId [2] (some (5)),
    report rootSumId [] (some (12))] := by
  native_decide

/- A negative outer source carries its sign through every operator and the aggregate. -/
example : reportsAs (.value 10) [{ base := .value (-2) }, secondRow] [
    report fixId [] (some (10)), report iMulId [1, 1] (some (-2)), report iSubId [1, 1] (some (3)),
    report iMulId [1, 2] (some (-4)), report iSubId [1, 2] (some (4)), report ohId [1] (some (3)),
    report ohnId [1] none, report oMulId [1] (some (-6)), report opId [1] (some (-2)),
    report oSubId [1] (some (-12)), report iMulId [2, 1] (some (15)),
    report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)), report ohnId [2] none,
    report oMulId [2] (some (20)), report opId [2] (some (5)), report oSubId [2] (some (-5)),
    report rootSumId [] (some (3))] := by
  native_decide

/- An absent outer source copies as zero into `OP`, which the filled guard reads as filled. -/
example : reportsAs (.value 10) [{ base := .absent }, secondRow] [
    report fixId [] (some (10)), report iMulId [1, 1] (some (0)), report iSubId [1, 1] (some (1)),
    report iMulId [1, 2] (some (0)), report iSubId [1, 2] (some (2)), report ohId [1] (some (3)),
    report ohnId [1] none, report oMulId [1] (some (0)), report opId [1] (some (0)),
    report oSubId [1] (some (-10)), report iMulId [2, 1] (some (15)),
    report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)), report ohnId [2] none,
    report oMulId [2] (some (20)), report opId [2] (some (5)), report oSubId [2] (some (-5)),
    report rootSumId [] (some (5))] := by
  native_decide

/- A malformed second operand clears the product and the copy whose guard holds; the other copy's
   guard is unmet, as on the clean row. -/
example : reportsAs (.value 10) [{ base2 := .malformed }, secondRow] [
    report fixId [] (some (10)), report iMulId [1, 1] (some (7)), report iSubId [1, 1] (some (-6)),
    report iMulId [1, 2] (some (14)), report iSubId [1, 2] (some (-5)), report ohId [1] none,
    report ohnId [1] none, report oMulId [1] none, report opId [1] (some (7)),
    report oSubId [1] (some (-3)), report iMulId [2, 1] (some (15)),
    report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)), report ohnId [2] none,
    report oMulId [2] (some (20)), report opId [2] (some (5)), report oSubId [2] (some (-5)),
    report rootSumId [] (some (12))] := by
  native_decide

/- A malformed inner source clears that inner row's two readers alone. -/
example : reportsAs (.value 10) [{ inner := [.malformed, .value 2] }, secondRow] [
    report fixId [] (some (10)), report iMulId [1, 1] none, report iSubId [1, 1] none,
    report iMulId [1, 2] (some (14)), report iSubId [1, 2] (some (-5)), report ohId [1] (some (3)),
    report ohnId [1] none, report oMulId [1] (some (21)), report opId [1] (some (7)),
    report oSubId [1] (some (-3)), report iMulId [2, 1] (some (15)),
    report iSubId [2, 1] (some (-2)), report ohId [2] (some (4)), report ohnId [2] none,
    report oMulId [2] (some (20)), report opId [2] (some (5)), report oSubId [2] (some (-5)),
    report rootSumId [] (some (12))] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanOperators
