import A12Kernel.Elaboration.ValidationCondition.StaticIteration
import A12Kernel.Elaboration.ValidationCondition.Reference
import A12Kernel.Elaboration.ValidationCondition.Assembly

namespace A12Kernel.Conformance.BoundCurrentRepetitionNumeric

private def outerPath : GroupPath := ["Root", "Rows"]
private def innerPath : GroupPath := outerPath ++ ["Items"]
private def fixedPath : GroupPath := innerPath ++ ["Fixed"]

private def rootField : FlatFieldDecl :=
  { id := 1, groupPath := ["Root"], name := "Base"
    policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel :=
  { fields := [rootField,
      { rootField with id := 2, groupPath := innerPath, repeatableScope := [10, 20] },
      { rootField with id := 3, groupPath := fixedPath, repeatableScope := [10, 20] }]
    repeatableGroups := [
      { level := 10, path := outerPath, repeatability := some 5 },
      { level := 20, path := innerPath, repeatability := some 5 }] }

private def repetition (path : GroupPath) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.currentRepetition { base := .absolute, groups := path })

private def compare (right : AuthoredNumericExpr SurfaceNumericAtom)
    (host : GroupPath := innerPath) :=
  elaborateRepeatableNumericComparison model host
    { op := .ordinary .equal
      left := .atom (.field { base := .absolute, groups := ["Root"], field := "Base" })
      right }

private def context (outer : Env) (value : Rat) : AddressedValidationEvaluationContext model :=
  let fields := model.checkContext
    { read := fun id => if id == 1 then .parsed (.num value) else .rejected .malformed }
  { outer
    scalar := { fields, groups := GroupPresenceContext.unavailable }
    input := .legacy { instantiatedRows := [], rawCells := fun _ => none }
      (fun _ _ => rootField.checkRaw (.rejected .malformed)) }

private def evaluate? (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (outer : Env) (value : Rat) : Option (Sum CheckedAddressingError Verdict) := do
  let checked ← (compare expression).toOption
  match checked.evalAddressed (context outer value) with
  | .ok verdict => some (.inr verdict)
  | .error error => some (.inl error)

private def scopeAndReferences? (path : GroupPath) :
    Option (Option (List RepeatableLevel) × List MessagePointer × Bool) := do
  let checked ← (compare (repetition path)).toOption
  let condition ← (CheckedValidationCondition.fromOrderedNumeric checked).toOption
  let scope ← condition.core.ordinaryIterationScope.toOption
  let references ← (condition.core.referencePointers [(10, 2), (20, 1)]).toOption
  some (scope, references, checked.core.requiresAddressedValidation)

private def error? (path host : GroupPath) : Option NumericValidationElabError :=
  match compare (repetition path) host with
  | .ok _ => none
  | .error error => some error

private def scopeDiagnostic? (path host : GroupPath) : Option KernelStaticDiagnostic :=
  (error? path host).bind NumericValidationElabError.repetitionScopeDiagnostic?

private def retained? (path : GroupPath) :
    Option (GroupPath × List RepeatableLevel × Option RepeatableLevel × Bool) := do
  let checked ← (compare (repetition path)).toOption
  match checked.core.right with
  | .atom (.ordinary (.boundCurrentRepetition source)) =>
      some (source.path, source.scope, source.level, checked.core.supportsAddressedPartial)
  | _ => none

example : evaluate? (repetition fixedPath) [(10, 2), (20, 3)] 1 =
      some (.inr (.fired .value)) ∧
    evaluate? (repetition fixedPath) [(10, 2), (20, 3)] 3 = some (.inr .notFired) := by
  native_decide

example : evaluate? (repetition outerPath) [(10, 2), (20, 3)] 2 =
      some (.inr (.fired .value)) ∧
    evaluate? (repetition innerPath) [(10, 2), (20, 3)] 3 =
      some (.inr (.fired .value)) ∧
    evaluate? (repetition innerPath) [(10, 2), (20, 3)] 2 = some (.inr .notFired) := by
  native_decide

example :
    let expression := AuthoredNumericExpr.binary .add
      (.binary .multiply (repetition outerPath) (.literal { value := 10, authoredScale := 0 }))
      (repetition innerPath)
    evaluate? expression [(10, 1), (20, 2)] 12 = some (.inr (.fired .value)) ∧
      evaluate? expression [(20, 1), (10, 2), (30, 0)] 21 = some (.inr (.fired .value)) := by
  native_decide

example : [innerPath, fixedPath].all (fun path =>
    evaluate? (repetition path) [(20, 3)] 1 ==
      some (.inl (.environment (.missingBinding 10))) &&
    evaluate? (repetition path) [(10, 2)] 1 ==
      some (.inl (.environment (.missingBinding 20))) &&
    evaluate? (repetition path) [(10, 0), (20, 3)] 1 ==
      some (.inl (.environment (.zeroBinding 10))) &&
    evaluate? (repetition path) [(10, 2), (10, 1), (20, 3)] 1 ==
      some (.inl (.environment (.duplicateBinding 10)))) = true := by
  native_decide

example : scopeAndReferences? outerPath =
      some (some [10], [{ field := 1, coordinates := [] }], true) ∧
    scopeAndReferences? innerPath =
      some (some [10, 20], [{ field := 1, coordinates := [] }], true) ∧
    scopeAndReferences? fixedPath =
      some (some [10, 20], [{ field := 1, coordinates := [] }], true) := by
  native_decide

example : error? innerPath outerPath =
      some (.currentRepetitionSource (.repeatableGroupRequiresAddress innerPath)) ∧
    error? fixedPath ["Root"] =
      some (.currentRepetitionSource (.repeatableGroupRequiresAddress fixedPath)) := by
  native_decide

/-- The coordinate clears the comparison's constant gate only where it **binds**. Hosted by the
group it names, the comparison is admitted; hosted by an enclosing group, the identical comparison
reports `MVK_NO_WILDCARD` — a different gate, and the one that decides the row. Both scopes are
locked together because a reading that took the outer row for the constant gate's answer would
conclude the opposite of the truth (peer `kf451`, measured 2026-09-22 at a12-dmkits `48a24aec9`). -/
example : scopeDiagnostic? innerPath outerPath = some .noWildcard ∧
    scopeDiagnostic? fixedPath ["Root"] = some .noWildcard ∧
    error? innerPath innerPath = none ∧
    error? outerPath outerPath = none ∧
    KernelStaticDiagnostic.noWildcard.kernelCode = "MVK_NO_WILDCARD" := by
  native_decide

/-- Retention preserves the authored path, its bound scope, and the level the coordinate names, and
    both shapes support partial evaluation: the coordinate answers from the row environment rather
    than from a cell, so no coverage can leave it unresolved
    ([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-repetition-operand-partial-relevance)). -/
example : retained? innerPath = some (innerPath, [10, 20], some 20, true) ∧
    retained? fixedPath = some (fixedPath, [10, 20], none, true) := by
  native_decide

example :
    let fixed : BoundCurrentRepetitionSource := { path := fixedPath, scope := [10, 20], level := none }
    let repeated : BoundCurrentRepetitionSource :=
      { path := innerPath, scope := [10, 20], level := some 20 }
    fixed.wellFormedIn model [10, 20] = true ∧
      repeated.wellFormedIn model [10, 20] = true ∧
      { fixed with level := some 20 }.wellFormedIn model [10, 20] = false ∧
      { repeated with level := none }.wellFormedIn model [10, 20] = false ∧
      { repeated with scope := [20] }.wellFormedIn model [10, 20] = false := by
  native_decide

end A12Kernel.Conformance.BoundCurrentRepetitionNumeric
