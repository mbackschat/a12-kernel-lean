import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: a fill guard on a malformed source field

A root `Gate` with Number `NG`, `A`, `P = [A]` under `FieldFilled(NG)`, `PN = [A]` under
`FieldNotFilled(NG)`, `D = [P] + 1` and `DN = [PN] + 1`, and a repeatable `Rows` (at most two rows)
with the same shape per row: `RP = [RA]` and `RPN = [RA]` guarded on `RG`, `RD = [RP] + [RB]` and
`RDN = [RPN] + [RB]`. Each reader is authored ahead of what it reads and every computed target is seeded
with a stale `99`. The four documents are the Kernel's rows at the
[guard-source checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-guard-on-malformed-source),
measured on both codegen strategies.

The three accounts a malformed guard field admits predict disjoint rows: read as filled, `D` is `6` and
`DN` `1`; read as not filled, `D` is `1` and `DN` `6`; read as poison, both copies and both readers
clear. The Kernel answers poison on both carriers, the other row of the same call computing.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanGateSources

open A12Kernel

private def ngId : FieldId := 0
private def aId : FieldId := 1
private def pId : FieldId := 2
private def pnId : FieldId := 3
private def dId : FieldId := 4
private def dnId : FieldId := 5
private def rgId : FieldId := 6
private def raId : FieldId := 7
private def rbId : FieldId := 8
private def rpId : FieldId := 9
private def rpnId : FieldId := 10
private def rdId : FieldId := 11
private def rdnId : FieldId := 12

private def rowsPath : GroupPath := ["Gate", "Rows"]

private def number (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl where
  id
  groupPath := group
  name
  repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } }

private def model : FlatModel where
  fields := [
    number ngId "NG" ["Gate"] [], number aId "A" ["Gate"] [], number pId "P" ["Gate"] [],
    number pnId "PN" ["Gate"] [], number dId "D" ["Gate"] [], number dnId "DN" ["Gate"] [],
    number rgId "RG" rowsPath [10], number raId "RA" rowsPath [10], number rbId "RB" rowsPath [10],
    number rpId "RP" rowsPath [10], number rpnId "RPN" rowsPath [10],
    number rdId "RD" rowsPath [10], number rdnId "RDN" rowsPath [10]]
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 2 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def read (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (bare field))

private def fixed? (target : FieldId) (guard : Option ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedRepeatableNumberPlanStep model) := do
  let operation ← (elaborateNumericTargetComputationOperation model ["Gate"] target expression).toOption
  let table ← (certifyNumericComputationTable
    [({ precondition := guard, operation } :
      ComputationAlternative (CheckedNumericTargetComputationOperation model))]).toOption
  pure (.fixed table)

private def row? (operation : Option (CheckedRepeatableNumberRowOperation model))
    (guard : Option ComputationCondition := none) :
    Option (CheckedRepeatableNumberPlanStep model) := do
  let step ← (checkRepeatableNumberRowStep (← operation) guard).toOption
  pure (.row step)

private def sum (target : FieldId) (left right : String) :
    Option (CheckedRepeatableNumberRowOperation model) :=
  (checkAddressedNumberBinary model rowsPath target (bare left) (bare right) .add).toOption.map .binary

private def copy (target : FieldId) (source : String) :
    Option (CheckedRepeatableNumberRowOperation model) :=
  (checkAddressedNumberField model rowsPath target (bare source)).toOption.map .direct

private def plusOne (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (read field) (.literal { value := 1, authoredScale := 0 })

/-- The model's eight computations in its authored order, every reader ahead of what it reads. -/
private def authored : List (Option (CheckedRepeatableNumberPlanStep model)) :=
  [fixed? dId none (plusOne "P"), fixed? dnId none (plusOne "PN"),
    fixed? pId (some (.fieldFilled ngId)) (read "A"),
    fixed? pnId (some (.fieldNotFilled ngId)) (read "A"),
    row? (sum rdId "RP" "RB"), row? (sum rdnId "RPN" "RB"),
    row? (copy rpId "RA") (some (.fieldFilled rgId)),
    row? (copy rpnId "RA") (some (.fieldNotFilled rgId))]

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan (← authored.mapM id)).toOption

private inductive Gate where
  | value (number : Int)
  | malformed
  | absent

private def numberCell (field : FieldId) (path : List Nat) (number : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored := toString number, raw := .parsed (.num number) }

private def gateCells (field : FieldId) (path : List Nat) : Gate → List ClassifiedCellInput
  | .value number => [numberCell field path number]
  | .malformed => [{ address := { field, path }, stored := "x", raw := .rejected .malformed }]
  | .absent => []

private def seeded (fields : List FieldId) (path : List Nat) : List ClassifiedCellInput :=
  fields.map (numberCell · path 99)

/-- The root gate and one gate per row; the rows' own sources are `RA` `7` and `3`, each `RB` `1`. -/
private def document? (root first second : Gate) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
    cells := gateCells ngId [] root ++ [numberCell aId [] 5] ++ seeded [pId, pnId, dId, dnId] [] ++
      ([(first, 7), (second, 3)].zipIdx.flatMap fun ((gate, source), index) =>
        gateCells rgId [index + 1] gate ++
          [numberCell raId [index + 1] source, numberCell rbId [index + 1] 1] ++
          seeded [rpId, rpnId, rdId, rdnId] [index + 1])
  }).toOption

private def reported? : NumericTargetOutcome → Option (Option Int)
  | .accepted stored => if stored.scale = 0 then some (some stored.unscaled) else none
  | .noValue | .inheritedPoison _ => some none
  | .rejected _ _ | .invalidNoValue _ => none

/-- Each target's report in a fixed order: `P`, `PN`, `D`, `DN`, then `RP`, `RPN`, `RD`, `RDN` for
the first row and the second. `none` is a clear. -/
private def reports? (root first second : Gate) : Option (List (Option Int)) := do
  let plan ← plan?
  let input ← document? root first second
  let outcomes ← (plan.executeSteps world input plan.execution []).toOption
  let found ← outcomes.mapM fun outcome =>
    (reported? outcome.outcome).map (outcome.targetField, ·)
  let at? := fun (field : FieldId) (path : List Nat) =>
    (found.find? (·.1 == { field, path })).map (·.2)
  [at? pId [], at? pnId [], at? dId [], at? dnId [],
    at? rpId [1], at? rpnId [1], at? rdId [1], at? rdnId [1],
    at? rpId [2], at? rpnId [2], at? rdId [2], at? rdnId [2]].mapM id

/- Row `g01`: every gate filled, so each `FieldFilled` copy and its reader compute and each
`FieldNotFilled` copy clears, its reader substituting zero. -/
example : reports? (.value 1) (.value 1) (.value 1) =
    some [some 5, none, some 6, some 1, some 7, none, some 8, some 1, some 3, none, some 4, some 1] := by
  native_decide

/- Row `g02`: a malformed gate poisons both copies it guards and both of their readers, on the root and
in the first row alike, while the second row's clean gate computes. Reading the malformed gate as filled
would give `D` `6` and `DN` `1`; reading it as not filled, `1` and `6`. -/
example : reports? .malformed .malformed (.value 1) =
    some [none, none, none, none, none, none, none, none, some 3, none, some 4, some 1] := by
  native_decide

/- Rows `g03` and `g04`: an absent gate clears the `FieldFilled` copy cleanly, which its reader reads as
empty, and selects the `FieldNotFilled` copy; a gate holding `0` is filled. -/
example : reports? .absent .absent (.value 1) =
      some [none, some 5, some 1, some 6, none, some 7, some 1, some 8, some 3, none, some 4, some 1] ∧
    reports? (.value 0) (.value 0) .absent =
      some [some 5, none, some 6, some 1, some 7, none, some 8, some 1, none, some 3, some 1, some 4] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanGateSources
