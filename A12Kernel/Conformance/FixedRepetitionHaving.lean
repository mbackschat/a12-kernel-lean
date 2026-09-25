import A12Kernel.Elaboration.ValidationCondition.StaticIteration

namespace A12Kernel.Conformance.FixedRepetitionHaving

open A12Kernel

private def base : FlatFieldDecl :=
  { id := 1, groupPath := ["Rep", "Rows"], name := "Base"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def fixedPath : GroupPath := ["Rep", "Rows", "Fixed"]
private def metaPath : GroupPath := ["Rep", "Meta"]

private def model : FlatModel :=
  { fields := [base,
      { base with id := 2, groupPath := fixedPath, name := "Value" },
      { base with id := 3, groupPath := metaPath, name := "Tag", repeatableScope := [] }]
    repeatableGroups := [
      { level := 10, path := base.groupPath, repeatability := some 5 }] }

private def source : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Rep" }, { name := "Rows", starred := true }]
    field := "Base" }

private def reference (origin : HavingOrigin) (path : GroupPath) :
    SurfaceHavingRepetitionRef :=
  { origin, group := .path { base := .absolute, groups := path } }

private def condition (origin : HavingOrigin) (path : GroupPath)
    (op : SurfaceComparisonOp := .equal) : SurfaceCorrelatedHaving :=
  .compareRepetitions op (reference origin path) (reference .inner base.groupPath)

private def cells? (origin : HavingOrigin) (path : GroupPath)
    (op : SurfaceComparisonOp := .equal) (outer : Env := []) :
    Option (List (Option Rat)) := do
  let declaringGroup := if outer.isEmpty then ["Rep"] else base.groupPath
  let checked ← (elaborateStarNumberHavingSource model declaringGroup source
    (condition origin path op) declaringGroup).toOption
  let document : Document :=
    { instantiatedRows := [1, 2, 3].map fun row => { group := 10, path := [row] }
      rawCells := fun _ => none }
  let side ← (checked.resolvedValueSide document outer
    (fun _ _ => formalCheck base.policy .empty)
    (fun env _ => .parsed (.num (match env with
      | [(10, 1)] => 1
      | [(10, 2)] => 2
      | _ => 4)))).toOption
  pure (side.cells.map fun cell => match cell with
    | .present value => some value
    | _ => none)

example : cells? .inner fixedPath = some [some 1] := by native_decide
example : cells? .inner fixedPath .notEqual = some [some 2, some 4] := by native_decide
example : cells? .inner metaPath = some [some 1] := by native_decide
example : cells? .outer metaPath = some [some 1] := by native_decide
example : cells? .outer fixedPath .equal [(10, 3)] = some [some 1] := by native_decide

private def error? (declaringGroup : GroupPath) (having : SurfaceCorrelatedHaving) :
    Option CorrelationElabError :=
  match elaborateStarNumberHavingSource model declaringGroup (writtenGroup := declaringGroup) source having with
  | .error (.having error) => some error
  | _ => none

example : error? ["Rep"] (condition .outer fixedPath) =
    some (.repetitionOutsideEnvironment .outer fixedPath [] 10) := by native_decide

example : (error? ["Rep"] (condition .outer fixedPath)).bind
    CorrelationElabError.diagnostic? = some .noWildcard := by native_decide

example :
    let error := error? base.groupPath
      (.compareRepetitions .equal (reference .outer fixedPath) (reference .outer fixedPath))
    error = some .missingInner ∧
      error.bind CorrelationElabError.diagnostic? = some .noIterationForWildcard := by native_decide

example :
    let error := error? ["Rep"]
      (.compareRepetitions .equal (reference .inner metaPath) (reference .inner metaPath))
    error = some .missingInner ∧
      error.bind CorrelationElabError.diagnostic? = some .noIterationForWildcard := by native_decide

example : (elaborateStarNumberHavingSource model ["Rep"] (writtenGroup := ["Rep"]) source
    (.compareRepetitions .equal (reference .inner fixedPath) (reference .inner fixedPath))).isOk
    = true := by native_decide

private def checkedHaving? (path : GroupPath) : Option CorrelatedHaving :=
  (elaborateStarNumberHavingSource model base.groupPath (writtenGroup := base.groupPath) source
    (condition .outer path)).toOption.map (·.having)

example : checkedHaving? fixedPath = some
    (.compareRepetitions .equal
      { origin := .outer, source := .fixed fixedPath }
      { origin := .inner, source := .repeatable 10 }) := by native_decide

example : checkedHaving? fixedPath ≠ checkedHaving? metaPath := by native_decide

example :
    ({ origin := .outer, source := .fixed fixedPath } : HavingRepetitionRef).scope? model =
      some [10] ∧
    ({ origin := .outer, source := .fixed metaPath } : HavingRepetitionRef).scope? model =
      some [] ∧
    ({ origin := .inner, source := .fixed base.groupPath } : HavingRepetitionRef).scope? model =
      none := by native_decide

private def iterationScope? (origin : HavingOrigin) (path : GroupPath) :
    Option (Sum ValidationCondition.RuleIterationScopeError
      (Option (List RepeatableLevel))) := do
  let values ← (elaborateNumberEntitySource model base.groupPath
    { first := .starHaving source (condition origin path), rest := [] }).toOption
  let comparison : OrderedNumericComparison model :=
    { op := .ordinary .greater
      left := .atom (.aggregate .sum values)
      right := .literal { value := 0, authoredScale := 0 } }
  pure (match (ValidationCondition.orderedNumericIn
    .modelWideCheckedComputation comparison).ordinaryIterationScope with
    | .error error => .inl error
    | .ok scope => .inr scope)

example : iterationScope? .outer fixedPath = some (.inr (some [10])) ∧
    iterationScope? .inner fixedPath = some (.inr none) ∧
    iterationScope? .outer metaPath = some (.inr none) := by native_decide

end A12Kernel.Conformance.FixedRepetitionHaving
