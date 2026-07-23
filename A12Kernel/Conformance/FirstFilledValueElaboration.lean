import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.CheckedStarDocument

/-! # Checked multi-operand Number `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.FirstFilledValueElaboration

open A12Kernel

private def fallback : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Fallback"
    policy := { kind := .number { scale := 2, signed := false } } }

private def note : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Note"
    policy := { kind := .string } }

private def primary : FlatFieldDecl :=
  { id := 3, groupPath := ["Form", "Primary"], name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def secondary : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Secondary"], name := "Amount"
    policy := { kind := .number { scale := 1, signed := true } }
    repeatableScope := [20] }

private def nested : FlatFieldDecl :=
  { id := 5, groupPath := ["Form", "Primary", "Nested"], name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10, 30] }

private def model : FlatModel :=
  { fields := [fallback, note, primary, secondary, nested]
    repeatableGroups := [
      { level := 10, path := ["Form", "Primary"], repeatability := some 2 },
      { level := 20, path := ["Form", "Secondary"], repeatability := some 2 },
      { level := 30, path := ["Form", "Primary", "Nested"], repeatability := some 2 }] }

private def world : World :=
  { now := { epochMillis := 0 } }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def star (group : String) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Form" }, { name := group, starred := true }]
    field := "Amount" }

private def nestedStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Primary", starred := true },
      { name := "Nested", starred := true }]
    field := "Amount" }

private def nestedChildStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Primary" },
      { name := "Nested", starred := true }]
    field := "Amount" }

private def groupPath (group : String) : SurfaceGroupPath :=
  { base := .absolute, groups := ["Form", group] }

private def falseHaving (group : String) : SurfaceCorrelatedHaving :=
  .compareRepetitions .less
    { origin := .inner, group := .path (groupPath group) }
    { origin := .inner, group := .path (groupPath group) }

private def source (first : SurfaceFirstFilledNumberOperand)
    (rest : List SurfaceFirstFilledNumberOperand) : SurfaceFirstFilledNumberSource :=
  { first, rest }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def directRead (value : RawCell) : RawFlatContext where
  read field := if field == fallback.id then value else .empty

private def starRead (primaryCell secondaryCell : RawCell)
    (environment : Env) (field : FieldId) : RawCell :=
  if field == primary.id && environment == [(10, 1)] then primaryCell
  else if field == secondary.id && environment == [(20, 1)] then secondaryCell
  else .empty

private def unusedFilterRead (_ : Env) (_ : FieldId) : CheckedCell :=
  malformedCheckedCell

private inductive EvaluationError where
  | elaboration (error : FirstFilledNumberElabError)
  | addressing (error : StarAddressingError)
  deriving Repr, DecidableEq

private inductive EvaluationSnapshot where
  | result (value : PartialValidationFirstFilledNumberResult)
  | error
  deriving Repr, DecidableEq

private def evaluate (authored : SurfaceFirstFilledNumberSource)
    (rows : List RowAddr) (primaryCell secondaryCell fallbackCell : RawCell)
    (scope : ValidationRelevanceScope := .full) :
    Except EvaluationError PartialValidationFirstFilledNumberResult :=
  match elaborateFirstFilledNumberSource model ["Form"] authored with
  | .error error => Except.error (EvaluationError.elaboration error)
  | .ok checked =>
      (checked.evaluatePartialValidation (document rows) [] scope
        (directRead fallbackCell) unusedFilterRead
        (starRead primaryCell secondaryCell)).mapError EvaluationError.addressing

private def snapshot (authored : SurfaceFirstFilledNumberSource)
    (rows : List RowAddr) (primaryCell secondaryCell fallbackCell : RawCell)
    (scope : ValidationRelevanceScope := .full) : EvaluationSnapshot :=
  match evaluate authored rows primaryCell secondaryCell fallbackCell scope with
  | .ok result => .result result
  | .error _ => .error

private def scaleOf (authored : SurfaceFirstFilledNumberSource) :
    Option NumericScaleSummary :=
  match elaborateFirstFilledNumberSource model ["Form"] authored with
  | .ok checked => some checked.scaleSummary
  | .error _ => none

private def errorOf (authored : SurfaceFirstFilledNumberSource) :
    Option FirstFilledNumberElabError :=
  match elaborateFirstFilledNumberSource model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

private def relevance (path : List String) (indices : List RelevanceIndex) :
    RelevantEntityPattern :=
  { path, indices }

private def checkedDocument? (data : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" data).toOption

private def directPresentData : DocumentData :=
  { instantiatedRows := []
    cells := [{
      address := { field := fallback.id, path := [] }
      stored := "9"
      raw := .parsed (.num 9)
    }] }

private def primaryPresentData : DocumentData :=
  { instantiatedRows := [{ group := 10, path := [1] }]
    cells := [{
      address := { field := primary.id, path := [1] }
      stored := "7"
      raw := .parsed (.num 7)
    }] }

private def primaryAndFallbackData : DocumentData :=
  { primaryPresentData with
    cells := primaryPresentData.cells ++ directPresentData.cells }

private inductive CheckedEvaluationSnapshot where
  | validation (result : PartialValidationFirstFilledNumberResult)
  | computation (result : FirstFilledNumberResult)
  | error (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

private def checkedValidationSnapshot
    (authored : SurfaceFirstFilledNumberSource) (data : DocumentData)
    (outer : Env := []) : Option CheckedEvaluationSnapshot := do
  let checkedDocument ← checkedDocument? data
  let checkedSource ←
    (elaborateFirstFilledNumberSource model ["Form"] authored).toOption
  pure (match checkedSource.evaluateCheckedDocumentValidation
      checkedDocument outer .full with
    | .ok result => .validation result
    | .error cause => .error cause)

private def checkedComputationSnapshot
    (authored : SurfaceFirstFilledNumberSource) (data : DocumentData)
    (outer : Env := []) : Option CheckedEvaluationSnapshot := do
  let checkedDocument ← checkedDocument? data
  let checkedSource ←
    (elaborateFirstFilledNumberSource model ["Form"] authored).toOption
  pure (match checkedSource.evaluateCheckedDocumentComputation
      checkedDocument outer with
    | .ok result => .computation result
    | .error cause => .error cause)

/- The immutable checked document supplies both direct and repeated cells without changing authored prefix order or missing polarity. -/
example :
    checkedValidationSnapshot
        (source (.field (bare "Fallback")) [.star (star "Primary")])
        primaryPresentData =
      some (.validation (.evaluated (.value 7 true))) ∧
    checkedComputationSnapshot
        (source (.field (bare "Fallback")) [.star (star "Primary")])
        primaryPresentData =
      some (.computation (.value 7 true)) := by
  native_decide

/- A reached false filter uses the checked document's resolving context in both phases and carries its slot into the direct fallback's missing polarity. -/
example :
    checkedValidationSnapshot
        (source (.starHaving (star "Primary") (falseHaving "Primary"))
          [.field (bare "Fallback")]) primaryAndFallbackData =
      some (.validation (.evaluated (.value 9 true))) ∧
    checkedComputationSnapshot
        (source (.starHaving (star "Primary") (falseHaving "Primary"))
          [.field (bare "Fallback")]) primaryAndFallbackData =
      some (.computation (.value 9 true)) := by
  native_decide

/- A terminal direct value prevents the checked route from resolving a later star with an unavailable fixed outer binding. Empty direct input reaches the same star and reports structural addressing rather than semantic unavailability. -/
example :
    checkedValidationSnapshot
        (source (.field (bare "Fallback")) [.star nestedChildStar])
        directPresentData =
      some (.validation (.evaluated (.value 9 false))) ∧
    checkedComputationSnapshot
        (source (.field (bare "Fallback")) [.star nestedChildStar])
        directPresentData =
      some (.computation (.value 9 false)) ∧
    checkedValidationSnapshot
        (source (.field (bare "Fallback")) [.star nestedChildStar])
        { instantiatedRows := [], cells := [] } =
      some (.error (.addressing (.missingBinding 10))) ∧
    checkedComputationSnapshot
        (source (.field (bare "Fallback")) [.star nestedChildStar])
        { instantiatedRows := [], cells := [] } =
      some (.error (.addressing (.missingBinding 10))) := by
  native_decide

/- Mixed star/direct declarations retain authored order and the maximum declaration scale. -/
example :
    scaleOf (source (.star (star "Primary")) [
      .starHaving (star "Secondary") (falseHaving "Secondary"),
      .field (bare "Fallback")]) = some (NumericScaleSummary.field 2) ∧
    scaleOf (source (.star (star "Primary")) [
      .starHaving (star "Secondary") (falseHaving "Secondary")]) =
      some (NumericScaleSummary.field 1) := by
  native_decide

/- A terminal first slot hides a malformed later filtered-star topology and the direct fallback. -/
example :
    snapshot
      (source (.star (star "Primary")) [
        .starHaving (star "Secondary") (falseHaving "Secondary"),
        .field (bare "Fallback")])
      [{ group := 10, path := [1] }, { group := 20, path := [2] }]
      (.parsed (.num 9)) (.rejected .malformed) (.parsed (.num 11)) =
      .result (.evaluated (.value 9 false)) ∧
    snapshot
      (source (.star (star "Primary")) [
        .starHaving (star "Secondary") (falseHaving "Secondary"),
        .field (bare "Fallback")])
      [{ group := 10, path := [1] }, { group := 20, path := [2] }]
      .presentEmpty (.rejected .malformed) (.parsed (.num 11)) = .error := by
  native_decide

/- A direct head retains the same lazy boundary: its value hides a malformed later star, while its empty state reaches that topology. -/
example :
    snapshot (source (.field (bare "Fallback")) [.star (star "Secondary")])
        [{ group := 20, path := [2] }] .empty (.rejected .malformed)
        (.parsed (.num 9)) = .result (.evaluated (.value 9 false)) ∧
      snapshot (source (.field (bare "Fallback")) [.star (star "Secondary")])
        [{ group := 20, path := [2] }] .empty (.rejected .malformed)
        .presentEmpty = .error := by
  native_decide

/- A reached no-row star and an instantiated empty star cell both taint a later direct value. -/
example :
    snapshot (source (.star (star "Primary")) [.field (bare "Fallback")])
        [] .empty .empty (.parsed (.num 9)) =
        .result (.evaluated (.value 9 true)) ∧
      snapshot (source (.star (star "Primary")) [.field (bare "Fallback")])
        [{ group := 10, path := [1] }] .presentEmpty .empty
        (.parsed (.num 9)) = .result (.evaluated (.value 9 true)) := by
  native_decide

/- The same wrapper rule applies at a reopened nested level: an actual outer row with no inner row still contributes a not-given prefix. -/
example :
    snapshot (source (.star nestedStar) [.field (bare "Fallback")])
      [{ group := 10, path := [1] }] .empty .empty (.parsed (.num 9)) =
      .result (.evaluated (.value 9 true)) := by
  native_decide

/- A reached filtered slot is retained even when it selects no row before the direct fallback. -/
example :
    snapshot
      (source (.starHaving (star "Primary") (falseHaving "Primary"))
        [.field (bare "Fallback")])
      [{ group := 10, path := [1] }] (.parsed (.num 7)) .empty
      (.parsed (.num 9)) = .result (.evaluated (.value 9 true)) := by
  native_decide

/- Direct-slot relevance is checked only when the scan reaches that slot. -/
example :
    let primaryOnly := ValidationRelevanceScope.partialSet [
      relevance primary.path [.concrete 1, .concrete 1, .concrete 1]]
    snapshot (source (.star (star "Primary")) [.field (bare "Fallback")])
        [{ group := 10, path := [1] }] (.parsed (.num 9)) .empty
        (.rejected .malformed) primaryOnly = .result (.evaluated (.value 9 false)) ∧
      snapshot (source (.star (star "Primary")) [.field (bare "Fallback")])
        [{ group := 10, path := [1] }] .presentEmpty .empty
        (.rejected .malformed) primaryOnly = .result .nonRelevant := by
  native_decide

/- Reference resolution, direct-duplicate rejection, and cardinality precede common Number-kind checking. Repeated direct references fail even when separated by a star, while wildcarded slots are deliberately not deduplicated. -/
example :
    errorOf (source (.star (star "Primary")) []) = none ∧
      errorOf (source
        (.starHaving (star "Primary") (falseHaving "Primary")) []) = none ∧
      errorOf (source (.field (bare "Fallback")) []) = some .tooFewFields ∧
      errorOf (source (.field (bare "Note")) []) = some .tooFewFields ∧
      errorOf (source (.field (bare "Fallback")) [.field (bare "Fallback")]) =
        some (.duplicateOperand fallback.id) ∧
      errorOf (source (.field (bare "Fallback")) [
        .field (bare "Fallback"), .field (bare "Missing")]) =
        some (.resolve (.invalidEntity (bare "Missing"))) ∧
      errorOf (source (.field (bare "Note")) [.field (bare "Note")]) =
        some (.duplicateOperand note.id) ∧
      errorOf (source (.field (bare "Fallback")) [
        .star (star "Primary"), .field (bare "Fallback")]) =
        some (.duplicateOperand fallback.id) ∧
      errorOf (source (.star (star "Primary")) [.star (star "Primary")]) = none ∧
      errorOf (source (.star (star "Primary")) [
        .starHaving (star "Primary") (falseHaving "Primary")]) = none ∧
      errorOf (source
        (.starHaving (star "Primary") (falseHaving "Primary")) [
          .starHaving (star "Primary") (falseHaving "Primary")]) =
        none ∧
      errorOf (source (.field (bare "Fallback")) [.field (bare "Note")]) =
        some (.fieldKindMismatch note.path .string) := by
  native_decide

end A12Kernel.Conformance.FirstFilledValueElaboration
