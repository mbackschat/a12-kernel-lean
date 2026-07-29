import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Boolean/Confirm value-count computation locks -/

namespace A12Kernel.Conformance.NumericComputation.BooleanValueCount

open A12Kernel

private def target : FlatFieldDecl :=
  { id := 1
    groupPath := ["Flags"]
    name := "Count"
    policy := { kind := .number { scale := 0, signed := false } } }

private def firstBoolean : FlatFieldDecl :=
  { id := 2
    groupPath := ["Flags"]
    name := "A"
    policy := { kind := .boolean } }

private def secondBoolean : FlatFieldDecl :=
  { id := 3
    groupPath := ["Flags"]
    name := "B"
    policy := { kind := .boolean } }

private def confirmation : FlatFieldDecl :=
  { id := 4
    groupPath := ["Flags"]
    name := "Confirmed"
    policy := { kind := .confirm } }

private def model : FlatModel :=
  { fields := [target, firstBoolean, secondBoolean, confirmation] }

private def path (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Flags"], field := name }

private def source (first second : String) :
    SurfaceBooleanValueCountSource :=
  { first := .field (path first)
    rest := [.field (path second)] }

private def surface (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.booleanValueCount expected authored)

private def operation (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :=
  elaborateCompleteNumericComputationOperation model ["Flags"] target.id
    (surface expected authored)

private def operationError (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :
    Option NumericComputationElabError :=
  match operation expected authored with
  | .ok _ => none
  | .error error => some error

private def context (a b confirmed : RawCell) :
    ScalarComputationContext where
  read field :=
    if field == firstBoolean.id then firstBoolean.checkRaw a
    else if field == secondBoolean.id then secondBoolean.checkRaw b
    else if field == confirmation.id then confirmation.checkRaw confirmed
    else malformedCheckedCell

private def evaluated (expected : Bool)
    (authored : SurfaceBooleanValueCountSource)
    (a b confirmed : RawCell) : Option NumericComputationResult := do
  let checked ← (operation expected authored).toOption
  (checked.evaluate (context a b confirmed)).toOption

private def checkedFacts :
    Option (Bool × Bool × Bool × NumericScaleSummary × Bool) := do
  let checked ← (operation true (source "A" "Confirmed")).toOption
  pure (
    checked.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model target.id),
    checked.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model firstBoolean.id),
    checked.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model confirmation.id),
    (checked.core.expression.summary?
      CheckedNumericComputationAtom.numericScaleSummary).getD
        { scale := .unknown, canExpandScale := false },
    checked.core.expression.allAtoms
      CheckedNumericComputationAtom.supportsScalarEvaluation)

private def generatedFacts :
    Option (Bool × Bool × NumericOperandScope) := do
  let checked ← (operation true (source "A" "Confirmed")).toOption
  let comparison ← (checked.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField firstBoolean.id,
    comparison.core.referencesField confirmation.id,
    comparison.operandScope)

private def generatedVerdict
    (count : Rat) (a confirmed : RawCell) : Option Verdict := do
  let checked ← (operation true (source "A" "Confirmed")).toOption
  let comparison ← (checked.generatedMismatchComparison none).toOption
  let raw : RawFlatContext := {
    read field :=
      if field == target.id then .parsed (.num count)
      else if field == firstBoolean.id then a
      else if field == confirmation.id then confirmed
      else .empty }
  pure (comparison.evalFull (model.checkContext raw) true)

/- `True` admits Boolean plus Confirm, while the computation boundary preserves the `False` family rejection for Confirm. -/
example :
    operationError true (source "A" "Confirmed") = none ∧
      operationError false (source "A" "B") = none ∧
      operationError false (source "A" "Confirmed") =
        some (.booleanValueCount
          (.fieldKindMismatch confirmation.path false .confirm)) := by
  native_decide

/- Scalar computation counts canonical checked values, and the first reached formal failure remains poison. -/
example :
    evaluated true (source "A" "Confirmed")
        (.parsed (.bool true)) .empty (.parsed (.conf true)) =
      some (.value 2) ∧
    evaluated false (source "A" "B")
        (.parsed (.bool true)) (.parsed (.bool false)) .empty =
      some (.value 1) ∧
    evaluated true (source "A" "Confirmed")
        (.rejected .booleanToken) .empty (.parsed (.conf true)) =
      some (.poison .booleanToken) := by
  native_decide

/- The checked atom has integral scale, references exactly its source fields, and remains scalar-executable. A Number target cannot inhabit the statically Boolean/Confirm source family. -/
example :
    checkedFacts =
      some (false, true, true, NumericScaleSummary.field 0, true) := by
  native_decide

/- Generated validation retains the same checked source and direct model-wide scope; equality suppresses the generated mismatch and a different target fires it. -/
example :
    generatedFacts =
        some (true, true, .modelWideNonrepeatable) ∧
      generatedVerdict 2 (.parsed (.bool true)) (.parsed (.conf true)) =
        some .notFired ∧
      generatedVerdict 1 (.parsed (.bool true)) (.parsed (.conf true)) =
        some (.fired .value) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.BooleanValueCount
