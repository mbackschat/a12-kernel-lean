import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: a nested star aggregate over a computed row target

A root `Nest` with `NS = Sum(Outer*/Inner*/IP)` and the control `NS2 = Sum(Outer*/Inner*/IBase)`, a
repeatable `Outer` (at most two rows) holding a repeatable `Inner` (at most three rows) with `IBase` and
the row copy `IP = [IBase]`. Every computed target is seeded with a stale `99`. The four documents are
the Kernel's rows at the
[nested-star checkpoint](../../docs/sources/computation-scheduling-probes.md#src-repeatable-nested-star-aggregate),
measured on both codegen strategies.

`NS` reads every inner row's fresh copy across both outer rows, so a stale or one-level read would
differ; a malformed inner source poisons the aggregate; and an over-limit inner row holding `100` is left
out of both sums, which a read of its source would not be.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanNestedStar

open A12Kernel

private def nsId : FieldId := 0
private def ns2Id : FieldId := 1
private def iBaseId : FieldId := 2
private def ipId : FieldId := 3

private def outerPath : GroupPath := ["Nest", "Outer"]
private def innerPath : GroupPath := ["Nest", "Outer", "Inner"]

private def number (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl where
  id
  groupPath := group
  name
  repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } }

private def model : FlatModel where
  fields := [number nsId "NS" ["Nest"] [], number ns2Id "NS2" ["Nest"] [],
    number iBaseId "IBase" innerPath [10, 20], number ipId "IP" innerPath [10, 20]]
  repeatableGroups := [
    { level := 10, path := outerPath, repeatability := some 2 },
    { level := 20, path := innerPath, repeatability := some 3 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def nestedStar (field : String) : SurfaceStarFieldPath :=
  { base := .relative 0
    groups := [{ name := "Outer", starred := true }, { name := "Inner", starred := true }]
    field }

private def sum? (target : FieldId) (field : String) : Option (CheckedRepeatableNumberPlanStep model) := do
  let operation ← (elaborateNumberEntityTargetComputationOperation model ["Nest"] target
    (.atom (.aggregate .sum { first := .star (nestedStar field), rest := [] }))).toOption
  let table ← (certifyNumericComputationTable
    [({ precondition := none, operation } :
      ComputationAlternative (CheckedNumericTargetComputationOperation model))]).toOption
  pure (.fixed table)

private def copy? : Option (CheckedRepeatableNumberPlanStep model) := do
  let operation ← (checkAddressedNumberField model innerPath ipId
    { base := .relative 0, groups := [], field := "IBase" }).toOption
  pure (.row (← (checkRepeatableNumberRowStep (.direct operation) none).toOption))

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  (certifyRepeatableNumberPlan [← sum? nsId "IP", ← sum? ns2Id "IBase", ← copy?]).toOption

private inductive Source where
  | value (number : Int)
  | malformed
  | absent

private def numberCell (field : FieldId) (path : List Nat) (number : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored := toString number, raw := .parsed (.num number) }

private def sourceCells (path : List Nat) : Source → List ClassifiedCellInput
  | .value number => [numberCell iBaseId path number]
  | .malformed => [{ address := { field := iBaseId, path }, stored := "x", raw := .rejected .malformed }]
  | .absent => []

/-- Outer rows, each listing its inner rows' sources; an inner row past the third is over the limit. -/
private def document? (outer : List (List Source)) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := outer.zipIdx.flatMap fun (inner, o) =>
      { group := 10, path := [o + 1] } ::
        inner.zipIdx.map fun (_, i) => { group := 20, path := [o + 1, i + 1] }
    cells := [numberCell nsId [] 99, numberCell ns2Id [] 99] ++
      outer.zipIdx.flatMap fun (inner, o) => inner.zipIdx.flatMap fun (source, i) =>
        sourceCells [o + 1, i + 1] source ++ [numberCell ipId [o + 1, i + 1] 99]
  }).toOption

private def reported? : NumericTargetOutcome → Option (Option Int)
  | .accepted stored => if stored.scale = 0 then some (some stored.unscaled) else none
  | .noValue | .inheritedPoison _ => some none
  | .rejected _ _ | .invalidNoValue _ => none

/-- `NS`, `NS2`, then `IP` at each listed inner address; `none` is a clear. -/
private def reports? (outer : List (List Source)) (inner : List (List Nat)) :
    Option (List (Option Int)) := do
  let plan ← plan?
  let input ← document? outer
  let outcomes ← (plan.execute world input).toOption
  let found ← outcomes.mapM fun outcome => (reported? outcome.outcome).map (outcome.targetField, ·)
  let at? := fun (field : FieldId) (path : List Nat) =>
    (found.find? (·.1 == { field, path })).map (·.2)
  ([at? nsId [], at? ns2Id []] ++ inner.map (at? ipId ·)).mapM id

private def clean : List (List Source) := [[.value 1, .value 2], [.value 3]]

/- Rows `n01` and `n03`: every inner copy is read fresh across both outer rows, and an absent source
copies as zero. -/
example :
    reports? clean [[1, 1], [1, 2], [2, 1]] = some [some 6, some 6, some 1, some 2, some 3] ∧
    reports? [[.value 1, .absent], [.value 3]] [[1, 1], [1, 2], [2, 1]] =
      some [some 4, some 4, some 1, some 0, some 3] := by
  native_decide

/- Row `n02`: a malformed inner source clears its copy and poisons both sums. -/
example : reports? [[.value 1, .malformed], [.value 3]] [[1, 1], [1, 2], [2, 1]] =
    some [none, none, some 1, none, some 3] := by
  native_decide

/- Row `n04`: the fourth inner row of the second outer row is over the limit, so its copy clears and
both sums leave it out, its source's `100` included. -/
example : reports? [[.value 1, .value 2], [.value 3, .value 4, .value 5, .value 100]]
      [[1, 1], [1, 2], [2, 1], [2, 2], [2, 3], [2, 4]] =
    some [some 15, some 15, some 1, some 2, some 3, some 4, some 5, none] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanNestedStar
