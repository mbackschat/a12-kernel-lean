import A12Kernel.Elaboration.BooleanFirstFilledComputation

/-! # Direct one-star Boolean `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.BooleanFirstFilledComputation

open A12Kernel

private def target : FlatFieldDecl := {
  id := 1
  groupPath := ["Review"]
  name := "FirstApproved"
  policy := { kind := .boolean }
}

private def source : FlatFieldDecl := {
  id := 2
  groupPath := ["Review", "Rows"]
  name := "Approved"
  policy := { kind := .boolean }
  repeatableScope := [10]
}

private def confirmSource : FlatFieldDecl := {
  source with id := 3, name := "Confirmed", policy := { kind := .confirm }
}

private def repeatedTarget : FlatFieldDecl := {
  source with id := 4, name := "RepeatedTarget"
}

private def nestedSource : FlatFieldDecl := {
  source with
    id := 5
    groupPath := ["Review", "Rows", "Details"]
    name := "NestedApproved"
    repeatableScope := [10, 20]
}

private def unrelated : FlatFieldDecl := {
  target with id := 6, name := "Unrelated"
}

private def model : FlatModel := {
  fields := [target, source, confirmSource, repeatedTarget, nestedSource,
    unrelated]
  repeatableGroups := [
    { level := 10, path := ["Review", "Rows"], repeatability := some 4 },
    { level := 20, path := ["Review", "Rows", "Details"], repeatability := some 3 }]
}

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Review" }, { name := "Rows", starred := true }]
  field
}

private def nestedStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Review" },
    { name := "Rows", starred := true },
    { name := "Details", starred := true }]
  field := "NestedApproved"
}

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  (checkBooleanFirstFilledComputation model ["Review"] targetField (.star authored)).toOption

/-- The same check with the declaring group varied instead of the target, which is how a target
outside the declaring group is expressed under a single model root. -/
private def checkedAt? (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :=
  (checkBooleanFirstFilledComputation model declaringGroup targetField (.star authored)).toOption

private def dependencyModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == target.id then { field with groupPath := ["Review", "Target"] } else field }

private def candidateFilled : SurfaceCorrelatedHaving :=
  .presence .filled {
    origin := .inner
    field := { base := .absolute, groups := ["Review", "Rows"], field := "Approved" } }

private def containingGroup : SurfaceGroupReference :=
  .path { base := .absolute, groups := ["Review", "Target"] }

private def filtered (guard : SurfaceCorrelatedHaving) (directTarget : Bool := false) : SurfaceFirstFilledSource :=
  .list {
    first := .starHaving (star "Approved") (.and candidateFilled guard)
    rest := if directTarget then [.field { base := .absolute, groups := ["Review", "Target"], field := "FirstApproved" }] else [] }

private def positiveGroup : SurfaceCorrelatedHaving := .groupPresence .filled .inner containingGroup
private def negativeGroup : SurfaceCorrelatedHaving := .groupPresence .notFilled .inner containingGroup
private def ordinaryGroup : SurfaceCorrelatedHaving := .groupFill .atLeastOneGroupFilled (.group .inner containingGroup) []
private def directTarget : SurfaceCorrelatedHaving := .presence .filled {
  origin := .inner
  field := { base := .absolute, groups := ["Review", "Target"], field := "FirstApproved" } }

example : [positiveGroup, negativeGroup, ordinaryGroup, directTarget].all (fun guard =>
    (checkFirstFilledSite dependencyModel ["Review"] target.id (filtered guard)).isOk) = true := by native_decide

example : (checkBooleanFirstFilledComputation dependencyModel ["Review"] target.id (filtered positiveGroup)).isOk = true ∧
    [filtered negativeGroup, filtered ordinaryGroup, filtered directTarget, filtered positiveGroup true].all
      (fun authored => match checkBooleanFirstFilledComputation dependencyModel ["Review"] target.id authored with
        | .error (.targetSelfReference path) => path == ["Review", "Target", "FirstApproved"]
        | _ => false) = true := by native_decide

private def dependencyQueries? (guard : SurfaceCorrelatedHaving) (direct : Bool := false) :
    Option (Bool × Bool × Bool × Bool × Bool) := do
  let site ← (checkFirstFilledSite dependencyModel ["Review"] target.id (filtered guard direct)).toOption
  pure (site.referencesField target.id,
    site.referencesWith target.id (·.forbidsTarget target.id),
    site.referencesWith target.id (fun having => having.requiresProducer target.id target.id (fun _ => true)),
    site.referencesWith target.id (fun _ => false), site.referencesWith source.id (fun _ => false))

example : dependencyQueries? positiveGroup = some (true, false, false, false, true) ∧
    [negativeGroup, ordinaryGroup, directTarget].map dependencyQueries? =
      List.replicate 3 (some (true, true, true, false, true)) ∧
    dependencyQueries? positiveGroup true = some (true, true, true, true, true) := by native_decide

example : (do
    let operation ← (checkBooleanFirstFilledComputation dependencyModel ["Review"] target.id (filtered positiveGroup)).toOption
    pure (operation.referencesField target.id,
      operation.referencesWith target.id (·.forbidsTarget target.id),
      operation.referencesWith target.id (fun having => having.requiresProducer target.id target.id (fun _ => false)),
      operation.referencesWith source.id (fun having => having.requiresProducer target.id source.id (fun _ => true)))) =
      some (true, false, false, true) := by native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? (sourceStored : Option String) : Option (CheckedDocument model) :=
  let sourceCell := sourceStored.map fun stored => {
    address := { field := source.id, path := [1] }
    stored
    raw := classifyStoredBooleanText stored
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := [{
      address := { field := target.id, path := [] }
      stored := "false"
      raw := .parsed (.bool false)
    }] ++ sourceCell.toList
  }).toOption

private def result? (sourceStored : Option String) :
    Option FirstFilledBooleanComputationResult := do
  let operation ← checked? target.id (star "Approved")
  let input ← input? sourceStored
  let [entry] ← operation.execute input |>.toOption | none
  pure entry.result

private def document? (targetStored sourceStored : Option String)
    (unrelatedStored : String := "false") : Option (CheckedDocument model) :=
  let placed (field : FlatFieldDecl) (stored : String)
      (path : List Nat := []) : ClassifiedCellInput := {
    address := { field := field.id, path }
    stored
    raw := classifyStoredBooleanText stored
  }
  checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := (targetStored.map (placed target)).toList ++
      (sourceStored.map (fun stored => placed source stored [1])).toList ++
      [placed unrelated unrelatedStored]
  } |>.toOption

private def resultView? (input : CheckedDocument model)
    (residualMessages : List FormalCause := []) := do
  let operation ← checked? target.id (star "Approved")
  operation.executeResult input residualMessages |>.toOption

private def root (field : FieldId) : CellAddr := { field, path := [] }

/- The empty selection clears a seeded false target, while a filled true source preserves true. Kernel-calibrated
   per kind on a seeded target — BOOLEAN, CUSTOM, DATE_FRAGMENT, DATE, STRING, ENUM, TIME, DATE_TIME and DATE_RANGE
   all clear, NUMBER returns the fillable zero
   ([provenance](../../docs/sources/inbound-handbacks.md#inbound-2026-09-07-dispositions)). The seed is what makes the clear
   observable at all: an unseeded target reports nothing under either account, which is how a published clause of
   this project once came to call the same run "no outcome". -/
example :
    result? none = some .noValue ∧
      result? (some "true") = some (.value true) := by
  native_decide

/- False is a filled Boolean: the scan consults the cell's presence and never its value, Kernel-calibrated on all
   three engines against an absent-first row that falls through, which is the pair no single row establishes. -/
example : result? (some "false") = some (.value false) := by
  native_decide

/- A reached malformed Boolean poisons rather than clearing; this internal branch is not externally calibrated by the source case. -/
example : result? (some "TRUE") = some (.poison .booleanToken) := by
  native_decide

/- Typed source equality determines the changed subset before application; an unchanged success remains inert against a different destination. -/
example : (do
    let input ← document? (some "true") (some "true")
    let destination ← document? (some "false") none
    let result ← resultView? input
    let applied := result.applyToChecked destination
    pure (result.withoutErrors, result.withChanges, result.withErrors,
      applied (root target.id), applied (root unrelated.id))) =
  some ([{ targetField := root target.id, value := true }], [], [],
    .presentValue false, .presentValue false) := by
  native_decide

/- A changed Boolean value overwrites only the exact checked target. -/
example : (do
    let input ← document? (some "false") (some "true")
    let destination ← document? (some "false") none
    let result ← resultView? input
    let applied := result.applyToChecked destination
    pure (result.withChanges, applied (root target.id), applied (root unrelated.id))) =
  some ([{ targetField := root target.id, value := true }],
    .presentValue true, .presentValue false) := by
  native_decide

/- Exhaustion clears a source-filled target and materializes an absent destination target; an absent source target mints no action. -/
example : (do
    let filledInput ← document? (some "false") none
    let absentInput ← document? none none
    let destination ← document? none none
    let filledResult ← resultView? filledInput
    let absentResult ← resultView? absentInput
    pure (filledResult.cleared,
      (filledResult.applyToChecked destination) (root target.id),
      absentResult.cleared,
      (absentResult.applyToChecked destination) (root target.id))) =
  some ([root target.id], .presentEmpty, [], .absent) := by
  native_decide

/- Reached formal poison has no computed-error payload and applies through the source-filled clear action. -/
example : (do
    let input ← document? (some "false") (some "TRUE")
    let destination ← document? (some "true") none
    let result ← resultView? input
    let applied := result.applyToChecked destination
    pure (result.withoutErrors, result.withErrors, result.cleared,
      applied (root target.id), applied (root unrelated.id))) =
  some ([], [], [root target.id], .presentEmpty, .presentValue false) := by
  native_decide

/- The independently supplied residual channel is retained and solely controls the Boolean result's error predicate. -/
example : (do
    let input ← document? (some "true") (some "true")
    let result ← resultView? input [.malformed]
    pure (result.formalErrorsInOperands, result.noErrorOccurred)) =
  some ([.malformed], false) := by
  native_decide

/- The checked boundary admits only a fixed Boolean target and one direct single-level starred Boolean source. Placement is not part of that boundary. Declaring at `["Review", "Rows"]` puts the fixed target *above* the declaring group, which the checkpoint's `star-rowgroup` row measures as admitted: a star aggregate derives no iteration, so the Kernel's containment gate cannot fire. An unrepresentable declaring group is still refused, and so is the repeatable target, whose direct star reopens its own row rather than a sibling. Varying the declaring group rather than the target's group keeps the fixture to one model root, as an authored A12 model is. -/
example :
    (checked? target.id (star "Approved")).isSome = true ∧
      (checkedAt? ["Review", "Rows"] target.id (star "Approved")).isSome = true ∧
      (checkedAt? [] target.id (star "Approved")).isNone = true ∧
      (checked? target.id (star "Confirmed")).isNone = true ∧
      (checked? repeatedTarget.id (star "Approved")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

private structure RuntimeProjection where
  changes : List Bool := []
  cleared : Bool := false
  deriving Repr, DecidableEq

private def runtimeProjection? (sources : List (Option String))
    (seed : Option String) : Option RuntimeProjection := do
  let placed (field : FieldId) (path : List Nat) (stored : String) : ClassifiedCellInput := {
    address := { field, path }, stored, raw := classifyStoredBooleanText stored
  }
  let sourceCells := sources.zipIdx |>.flatMap fun (text, index) =>
    (text.map fun stored => placed source.id [index + 1] stored).toList
  let input ← (checkDocument prepared "en_US" {
    instantiatedRows := sources.zipIdx |>.map fun (_, index) =>
      { group := 10, path := [index + 1] }
    cells := sourceCells ++ (seed.map (placed target.id [])).toList
  }).toOption
  let result ← resultView? input
  pure { changes := result.withChanges.map (·.value), cleared := !result.cleared.isEmpty }

example :
    runtimeProjection? [some "false", some "true"] none =
      some { changes := [false] } ∧
    runtimeProjection? [some "false", some "true"] (some "false") = some {} ∧
    runtimeProjection? [none, some "false"] (some "true") =
      some { changes := [false] } ∧
    runtimeProjection? [none, none] (some "true") = some { cleared := true } ∧
    runtimeProjection? [none, none] none = some {} := by
  native_decide

example :
    runtimeProjection? [some "maybe", some "false"] (some "true") =
      some { cleared := true } ∧
    runtimeProjection? [some "maybe", some "false"] none = some {} ∧
    runtimeProjection? [some "false", some "maybe"] (some "true") =
      some { changes := [false] } := by
  native_decide

end A12Kernel.Conformance.BooleanFirstFilledComputation
