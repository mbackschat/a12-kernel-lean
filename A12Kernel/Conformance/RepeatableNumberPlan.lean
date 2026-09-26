import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored two-level repeatable Number plan locks

The fixture is the model of the
[two-level checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-two-level-repeatable-join):
a root `RootSum = Sum(Outer*/OP)`, a repeatable `Outer` (at most two rows) with `OP = [OBase]` under
`FieldFilled(OGate)`, and a nested repeatable `Inner` (at most three rows) with
`IJoin = [IA] + [../OP]` and `IA = [IBase]`, authored in that order, so the aggregate and the join
come ahead of what they read. Every computed target is seeded with a stale `99`. The seven documents
are the retained Kernel rows, measured on both codegen strategies; each reports the computed value
or, where the Kernel clears the target, `none`.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlan

open A12Kernel

private def rootSumId : FieldId := 0
private def oBaseId : FieldId := 1
private def oGateId : FieldId := 2
private def opId : FieldId := 3
private def iBaseId : FieldId := 4
private def iaId : FieldId := 5
private def iJoinId : FieldId := 6

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
    number rootSumId "RootSum" ["Rows"] [],
    number oBaseId "OBase" outerPath [10],
    { id := oGateId, groupPath := outerPath, name := "OGate", repeatableScope := [10],
      policy := { kind := .string } },
    number opId "OP" outerPath [10],
    number iBaseId "IBase" innerPath [10, 20],
    number iaId "IA" innerPath [10, 20],
    number iJoinId "IJoin" innerPath [10, 20]]
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

private def outerStar : SurfaceStarFieldPath :=
  { base := .relative 0, groups := [{ name := "Outer", starred := true }], field := "OP" }

private def rootSum? : Option (CheckedRepeatableNumberPlanStep model) := do
  let operation ← (elaborateNumberEntityTargetComputationOperation model ["Rows"] rootSumId
    (.atom (.aggregate .sum { first := .star outerStar, rest := [] }))).toOption
  let table ← (certifyNumericComputationTable
    [({ precondition := none, operation } :
      ComputationAlternative (CheckedNumericTargetComputationOperation model))]).toOption
  pure (.fixed table)

private def row? (operation : Option (CheckedRepeatableNumberRowOperation model))
    (guard : Option ComputationCondition := none) :
    Option (CheckedRepeatableNumberPlanStep model) := do
  let step ← (checkRepeatableNumberRowStep (← operation) guard).toOption
  pure (.row step)

private def op? := row?
  ((checkAddressedNumberField model outerPath opId (bare "OBase")).toOption.map .direct)
  (some (.fieldFilled oGateId))

private def iJoin? := row?
  ((checkAddressedNumberBinary model innerPath iJoinId (bare "IA") (parent "OP") .add).toOption.map
    .binary)

private def ia? := row?
  ((checkAddressedNumberField model innerPath iaId (bare "IBase")).toOption.map .direct)

/-- The model's four computations in its authored order. -/
private def authored : List (CheckedRepeatableNumberPlanStep model) :=
  [rootSum?, op?, iJoin?, ia?].filterMap id

private def plan? : Option (CheckedRepeatableNumberPlan model) :=
  (certifyRepeatableNumberPlan authored).toOption

private inductive Source where
  | value (number : Int)
  | malformed
  | absent

/-- The guard field `OGate`: filled, absent, or holding a rejected value, which the measured model's
unbounded String cannot store and which only the poisoned-guard lock uses. -/
private inductive Gate where
  | filled
  | absent
  | poisoned

private structure OuterRow where
  base : Source
  gate : Gate := .filled
  inner : List Source

private def numberCell (field : FieldId) (path : List Nat) (number : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored := toString number, raw := .parsed (.num number) }

private def sourceCells (field : FieldId) (path : List Nat) : Source → List ClassifiedCellInput
  | .value number => [numberCell field path number]
  | .malformed => [{ address := { field, path }, stored := "bad", raw := .rejected .malformed }]
  | .absent => []

private def gateCells (path : List Nat) : Gate → List ClassifiedCellInput
  | .filled => [{ address := { field := oGateId, path }, stored := "g", raw := .parsed (.str "g") }]
  | .absent => []
  | .poisoned =>
      [{ address := { field := oGateId, path }, stored := "g", raw := .rejected .declaredConstraint }]

private def document? (rows : List OuterRow) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.zipIdx.flatMap fun (row, outer) =>
      { group := 10, path := [outer + 1] } ::
        row.inner.zipIdx.map fun (_, inner) => { group := 20, path := [outer + 1, inner + 1] }
    cells := numberCell rootSumId [] 99 :: rows.zipIdx.flatMap fun (row, outer) =>
      sourceCells oBaseId [outer + 1] row.base ++
        gateCells [outer + 1] row.gate ++
        numberCell opId [outer + 1] 99 ::
        row.inner.zipIdx.flatMap fun (inner, index) =>
          sourceCells iBaseId [outer + 1, index + 1] inner ++
            [numberCell iaId [outer + 1, index + 1] 99,
              numberCell iJoinId [outer + 1, index + 1] 99]
  }).toOption

/-- A computed value, `none` for a cleared target, or no projection for an errored outcome or a value
at another scale, which no Kernel row reports: every target the grid clears is reported not errored,
and every target declares no fraction digits. -/
private def reported? : NumericTargetOutcome → Option (Option Int)
  | .accepted stored => if stored.scale = 0 then some (some stored.unscaled) else none
  | .noValue | .inheritedPoison _ => some none
  | .rejected _ _ | .invalidNoValue _ => none

/-- Run the steps `order` picks from the plan; the certified run uses its execution order. -/
private def outcomes? (rows : List OuterRow)
    (order : CheckedRepeatableNumberPlan model → List (CheckedRepeatableNumberPlanStep model)) :
    Option (List (CellAddr × Option Int)) := do
  let plan ← plan?
  let input ← document? rows
  let outcomes ← (plan.executeSteps world input (order plan) []).toOption
  outcomes.mapM fun outcome => (reported? outcome.outcome).map (outcome.targetField, ·)

/-- Equal as sets of addressed reports: the Kernel sorts its report by field, so the order Lean emits
rows in is not compared. -/
private def reportsAs (rows : List OuterRow) (expected : List (CellAddr × Option Int))
    (order : CheckedRepeatableNumberPlan model → List (CheckedRepeatableNumberPlanStep model) :=
      (·.execution)) : Bool :=
  match outcomes? rows order with
  | some actual => actual.length == expected.length && expected.all actual.contains
  | none => false

private def report (field : FieldId) (path : List Nat) (report : Option Int) : CellAddr × Option Int :=
  ({ field, path }, report)

private def twoRows (first : OuterRow) : List OuterRow :=
  [first, { base := .value 5, inner := [.value 3] }]

private def firstRow : OuterRow := { base := .value 7, inner := [.value 1, .value 2] }

/- Each join is authored ahead of what it reads and runs after it; only those producer-before-reader
pairs are measured, and the relative order of `RootSum` and `IA` is the shared rule's own. -/
example : (plan?.map fun plan => (plan.execution.map (·.targetField))) =
    some [opId, rootSumId, iaId, iJoinId] := by native_decide

example : reportsAs (twoRows firstRow) [
    report opId [1] (some 7), report opId [2] (some 5), report rootSumId [] (some 12),
    report iaId [1, 1] (some 1), report iaId [1, 2] (some 2), report iaId [2, 1] (some 3),
    report iJoinId [1, 1] (some 8), report iJoinId [1, 2] (some 9), report iJoinId [2, 1] (some 8)] := by
  native_decide

/- Run in authored order instead, the aggregate and the join read their producers pending and
therefore empty, not the seeded `99`, and neither answers what the Kernel does. -/
example : reportsAs (twoRows firstRow) (order := (·.authored)) [
    report opId [1] (some 7), report opId [2] (some 5), report rootSumId [] (some 0),
    report iaId [1, 1] (some 1), report iaId [1, 2] (some 2), report iaId [2, 1] (some 3),
    report iJoinId [1, 1] (some 7), report iJoinId [1, 2] (some 7), report iJoinId [2, 1] (some 5)] := by
  native_decide

/- A malformed outer source poisons its `OP`, which clears both inner joins that read it and the
aggregate, while the other outer row still computes. -/
example : reportsAs (twoRows { firstRow with base := .malformed }) [
    report opId [1] none, report opId [2] (some 5), report rootSumId [] none,
    report iaId [1, 1] (some 1), report iaId [1, 2] (some 2), report iaId [2, 1] (some 3),
    report iJoinId [1, 1] none, report iJoinId [1, 2] none, report iJoinId [2, 1] (some 8)] := by
  native_decide

/- An unmet guard clears `OP` cleanly, so its readers substitute zero rather than clearing. -/
example : reportsAs (twoRows { firstRow with gate := .absent }) [
    report opId [1] none, report opId [2] (some 5), report rootSumId [] (some 5),
    report iaId [1, 1] (some 1), report iaId [1, 2] (some 2), report iaId [2, 1] (some 3),
    report iJoinId [1, 1] (some 1), report iJoinId [1, 2] (some 2), report iJoinId [2, 1] (some 8)] := by
  native_decide

/- No Kernel row reads a poisoned guard, so this locks Lean's account alone: the guard's poison reaches
`OP` as inherited poison, which its readers clear on rather than substituting zero as they do for an
unmet guard. -/
example : reportsAs (twoRows { firstRow with gate := .poisoned }) [
    report opId [1] none, report opId [2] (some 5), report rootSumId [] none,
    report iaId [1, 1] (some 1), report iaId [1, 2] (some 2), report iaId [2, 1] (some 3),
    report iJoinId [1, 1] none, report iJoinId [1, 2] none, report iJoinId [2, 1] (some 8)] := by
  native_decide

/- An absent outer source copies as zero and gives the readers the same values. -/
example : reportsAs (twoRows { firstRow with base := .absent }) [
    report opId [1] (some 0), report opId [2] (some 5), report rootSumId [] (some 5),
    report iaId [1, 1] (some 1), report iaId [1, 2] (some 2), report iaId [2, 1] (some 3),
    report iJoinId [1, 1] (some 1), report iJoinId [1, 2] (some 2), report iJoinId [2, 1] (some 8)] := by
  native_decide

/- A malformed inner source clears its own row's `IA` and `IJoin` alone. -/
example : reportsAs (twoRows { firstRow with inner := [.malformed, .value 2] }) [
    report opId [1] (some 7), report opId [2] (some 5), report rootSumId [] (some 12),
    report iaId [1, 1] none, report iaId [1, 2] (some 2), report iaId [2, 1] (some 3),
    report iJoinId [1, 1] none, report iJoinId [1, 2] (some 9), report iJoinId [2, 1] (some 8)] := by
  native_decide

/- A third outer row is over the limit: its `OP` and every inner target under it clear, and the
aggregate does not read its seeded `99`. -/
example : reportsAs [
      { base := .value 7, inner := [.value 1] },
      { base := .value 5, inner := [.value 3] },
      { base := .value 4, inner := [.value 2] }] [
    report opId [1] (some 7), report opId [2] (some 5), report opId [3] none, report rootSumId [] (some 12),
    report iaId [1, 1] (some 1), report iaId [2, 1] (some 3), report iaId [3, 1] none,
    report iJoinId [1, 1] (some 8), report iJoinId [2, 1] (some 8), report iJoinId [3, 1] none] := by
  native_decide

/- A fourth inner row is over the limit and clears its own targets alone. -/
example : reportsAs
    (twoRows { firstRow with inner := [.value 1, .value 2, .value 3, .value 4] }) [
    report opId [1] (some 7), report opId [2] (some 5), report rootSumId [] (some 12),
    report iaId [1, 1] (some 1), report iaId [1, 2] (some 2), report iaId [1, 3] (some 3), report iaId [1, 4] none,
    report iaId [2, 1] (some 3),
    report iJoinId [1, 1] (some 8), report iJoinId [1, 2] (some 9), report iJoinId [1, 3] (some 10),
    report iJoinId [1, 4] none, report iJoinId [2, 1] (some 8)] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlan
