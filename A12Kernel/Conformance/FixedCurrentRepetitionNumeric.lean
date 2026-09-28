import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Conformance.FixedCurrentRepetitionNumeric

private def source : FlatFieldDecl :=
  { id := 1, groupPath := ["Root"], name := "Source"
    policy := { kind := .number { scale := 0, signed := true } } }

private def fixedPath : GroupPath := ["Root", "Meta", "Details"]
private def boundFixedPath : GroupPath := ["Root", "Rows", "Fixed"]

private def model : FlatModel :=
  { fields := [source, { source with id := 2, name := "Target" },
      { source with id := 3, groupPath := fixedPath },
      { source with id := 4, groupPath := boundFixedPath, repeatableScope := [10] }]
    repeatableGroups := [
      { level := 10, path := ["Root", "Rows"], repeatability := some 5 }] }

private def repetition (path : GroupPath) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.currentRepetition { base := .absolute, groups := path })

private def field : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field { base := .absolute, groups := ["Root"], field := "Source" })

private def literal (value : Rat) : AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def operation (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
  elaborateNumericComputationOperation model ["Root"] 2 expression

private def computation? (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option NumericComputationResult := do
  let checked ← (operation expression).toOption
  (checked.evaluate { read := fun _ => source.checkRaw (.rejected .malformed) }).toOption

private def validation? (value : Rat)
    (left right : AuthoredNumericExpr SurfaceNumericAtom) : Option Verdict := do
  let checked ← (elaborateNumericComparison model ["Root"]
    { op := .ordinary .equal, left, right }).toOption
  pure (checked.evalFull (model.checkContext
    { read := fun id => if id == source.id then .parsed (.num value)
        else .rejected .malformed }) true)

private def error? (path : GroupPath) : Option FixedGroupReferenceError :=
  match operation (repetition path) with
  | .error (.currentRepetitionSource error) => some error
  | _ => none

private def retained? (path : GroupPath) : Option (GroupPath × Bool × NumericScaleSummary) := do
  let checked ← (operation (repetition path)).toOption
  match checked.core.expression with
  | .atom (.numeric (.fixedCurrentRepetition reference)) =>
      some (reference.path,
        checked.core.expression.anyAtom (CheckedNumericComputationAtom.references model 2),
        (.fixedCurrentRepetition reference : NumericValidationAtom).summary (fun _ => .field 9))
  | _ => none

private def generated? : Option (GroupPath × Verdict × Verdict) := do
  let checked ← (operation (repetition fixedPath)).toOption
  let generated ← (checked.generatedMismatchComparison none).toOption
  match generated.core.right with
  | .atom (.ordinary (.fixedCurrentRepetition reference)) =>
      let context (value : Rat) : FlatContext := model.checkContext
        { read := fun id => if id == 2 then .parsed (.num value) else .rejected .malformed }
      some (reference.path, generated.evalFull (context 1) true,
        generated.evalFull (context 2) true)
  | _ => none

example : computation? (repetition ["Root"]) = some (.value 1) ∧
    computation? (repetition fixedPath) = some (.value 1) ∧
    computation? (.abs (repetition fixedPath)) = some (.value 1) ∧
    computation? (.binary .add (repetition fixedPath) (literal 2)) = some (.value 3) := by
  native_decide

example : validation? 1 field (repetition fixedPath) = some (.fired .value) ∧
    validation? 2 field (repetition fixedPath) = some .notFired ∧
    validation? 1 (.binary .add (repetition fixedPath) field) (literal 2) =
      some (.fired .value) := by
  native_decide

example : retained? ["Root"] = some (["Root"], false, .field 0) ∧
    retained? fixedPath = some (fixedPath, false, .field 0) := by
  native_decide

example : generated? = some (fixedPath, .notFired, .fired .value) := by
  native_decide

example : (operation (.abs (literal 1))).isOk = false ∧
    (operation (.abs (repetition fixedPath))).isOk = true := by
  native_decide

example : error? ["Root", "Rows"] =
      some (.repeatableGroupRequiresAddress ["Root", "Rows"]) ∧
    error? boundFixedPath = some (.repeatableGroupRequiresAddress boundFixedPath) ∧
    error? ["Root", "Missing"] = some (.unknownGroup ["Root", "Missing"]) := by
  native_decide

private def comparisonDiagnostic? (path : GroupPath) : Option (Option KernelStaticDiagnostic) :=
  match elaborateNumericComparison model ["Root"]
      { op := .ordinary .greater, left := repetition path, right := literal 0 } with
  | .ok _ => none
  | .error error => some error.repetitionScopeDiagnostic?

/-- The operand cascade's unstarred group rows from a root rule: a name resolving to nothing, a
repeatable group the rule does not iterate, and an admitted fixed group. The unresolved name's class
is what separates resolution from the scope gate, which a projection leaving it unmapped would hide
(peer `PathGatePopulation.repetitionRows`,
[inbound](../../docs/SOURCES.md#inbound-2026-09-27a-current-repetition)). -/
example : comparisonDiagnostic? ["Root", "Missing"] = some (some .invalidEntity) ∧
    comparisonDiagnostic? ["Root", "Rows"] = some (some .noWildcard) ∧
    comparisonDiagnostic? fixedPath = none := by
  native_decide

example :
    !(model.admitsNumericComputationOperand
      (.numeric (.fixedCurrentRepetition
        { path := boundFixedPath, origin := .path }))) = true ∧
    !(model.admitsNumericComputationOperand
      (.numeric (.fixedCurrentRepetition
        { path := ["Root"], origin := .ruleGroup }))) = true ∧
    !(model.admitsNumericComputationOperand
      (.numeric (.fixedCurrentRepetition
        { path := fixedPath, origin := .path, boundRepeatableScope := [10] }))) = true := by
  native_decide

end A12Kernel.Conformance.FixedCurrentRepetitionNumeric
