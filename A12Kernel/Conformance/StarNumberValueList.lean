import A12Kernel.Elaboration.StarNumberValueList

/-! # Checked nested Number-star value-list locks -/

namespace A12Kernel.Conformance.StarNumberValueList

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Sections", "Items"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10, 20] }

private def note : FlatFieldDecl :=
  { amount with id := 8, name := "Note", policy := { kind := .string } }

private def needle : FlatFieldDecl :=
  { id := 1, groupPath := ["Shop"], name := "Needle",
    policy := { kind := .number { scale := 0, signed := false } } }

private def spare : FlatFieldDecl :=
  { needle with id := 2, name := "Spare" }

private def text : FlatFieldDecl :=
  { needle with id := 3, name := "Text", policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [amount, note, needle, spare, text]
    repeatableGroups := [
      { level := 20, path := ["Shop", "Sections", "Items"], repeatability := some 2 },
      { level := 10, path := ["Shop", "Sections"], repeatability := some 2 }] }

private def starPath (field : String := "Amount") : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Shop" }, { name := "Sections", starred := true },
      { name := "Items", starred := true }]
    field }

private def fieldPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Shop"], field }

private def authored (quantifier : ValueListQuantifier)
    (fields : SurfaceStarNumberValueListFields := .star (starPath))
    (firstValue : String := "Needle") (restValues : List String := []) :
    SurfaceStarNumberValueListSource :=
  { quantifier
    fields
    firstValue := fieldPath firstValue
    restValues := restValues.map fieldPath }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def sparseRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] }]

private def fullRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] },
  { group := 20, path := [1, 2] }, { group := 10, path := [2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def directRead (needleRaw spareRaw : RawCell) : RawFlatContext where
  read id := if id == needle.id then needleRaw else if id == spare.id then spareRaw else .empty

private def unusedFilterRead (_ : Env) (_ : FieldId) : CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := false } } .empty

private def constantStarRead (raw : RawCell) (_ : Env) (_ : FieldId) : RawCell := raw

private def malformedThenFive (environment : Env) (_ : FieldId) : RawCell :=
  match environment with
  | [(10, 1), (20, 1)] => .rejected .malformed
  | _ => .parsed (.num 5)

private def verdictOf (surface : SurfaceStarNumberValueListSource)
    (rows : List RowAddr) (direct : RawFlatContext)
    (starRead : Env → FieldId → RawCell) (outer : Env := [])
    (filterRead : Env → FieldId → CheckedCell := unusedFilterRead) : Option Verdict :=
  match elaborateStarNumberValueListSource model amount.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateFull (document rows) outer direct filterRead starRead with
      | .error _ => none
      | .ok verdict => some verdict

private def partialResultOf (surface : SurfaceStarNumberValueListSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (direct : RawFlatContext) (starRead : Env → FieldId → RawCell)
    (outer : Env := []) : Option PartialStarNumberValueListResult :=
  match elaborateStarNumberValueListSource model amount.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartial (document rows) outer scope direct starRead with
      | .error _ => none
      | .ok result => some result

private def errorOf (surface : SurfaceStarNumberValueListSource) :
    Option StarNumberValueListElabError :=
  match elaborateStarNumberValueListSource model amount.groupPath surface with
  | .ok _ => none
  | .error error => some error

/- A malformed fields cell is skipped by `AtLeastOne` and `NotAll`, but poisons `No`. -/
example :
    verdictOf (authored .atLeastOne) fullRows
      (directRead (.parsed (.num 5)) .empty) malformedThenFive =
        some (.fired .value) ∧
    verdictOf (authored .no) fullRows
      (directRead (.parsed (.num 9)) .empty) malformedThenFive =
        some .unknown ∧
    verdictOf (authored .notAll) fullRows
      (directRead (.parsed (.num 5)) .empty) malformedThenFive =
        some .notFired := by
  native_decide

private def entity (path : List String) (indices : List RelevanceIndex) :
    RelevantEntityPattern :=
  { path, indices }

private def firstAmountAndNeedle : ValidationRelevanceScope :=
  .partialSet [
    entity amount.path [.concrete 1, .concrete 1, .concrete 1, .concrete 1],
    entity needle.path [.concrete 1, .concrete 1]]

/- Nonrelevant fields cells are absent from the present search: a relevant witness still decides the two existential quantifiers, while `No` retains UNKNOWN poison. -/
example :
    partialResultOf (authored .atLeastOne) fullRows firstAmountAndNeedle
        (directRead (.parsed (.num 5)) .empty)
        (constantStarRead (.parsed (.num 5))) =
      some (.evaluated (.fired .value)) ∧
    partialResultOf (authored .notAll) fullRows firstAmountAndNeedle
        (directRead (.parsed (.num 5)) .empty)
        (constantStarRead (.parsed (.num 7))) =
      some (.evaluated (.fired .value)) ∧
    partialResultOf (authored .no) fullRows firstAmountAndNeedle
        (directRead (.parsed (.num 5)) .empty)
        (constantStarRead (.parsed (.num 7))) =
      some (.evaluated .unknown) := by
  native_decide

private def allAmountsAndSpare : ValidationRelevanceScope :=
  .partialSet [
    entity amount.path [.concrete 1, .all, .all, .concrete 1],
    entity spare.path [.concrete 1, .concrete 1]]

/- Direct values-side nonrelevance uses the same classification: `AtLeastOne` can use another relevant member, while `No` and `NotAll` are poisoned. -/
example :
    partialResultOf (authored .atLeastOne (restValues := ["Spare"]))
        fullRows allAmountsAndSpare
        (directRead (.rejected .malformed) (.parsed (.num 7)))
        (constantStarRead (.parsed (.num 7))) =
      some (.evaluated (.fired .value)) ∧
    partialResultOf (authored .no (restValues := ["Spare"]))
        fullRows allAmountsAndSpare
        (directRead (.rejected .malformed) (.parsed (.num 9)))
        (constantStarRead (.parsed (.num 7))) =
      some (.evaluated .unknown) ∧
    partialResultOf (authored .notAll (restValues := ["Spare"]))
        fullRows allAmountsAndSpare
        (directRead (.rejected .malformed) (.parsed (.num 9)))
        (constantStarRead (.parsed (.num 7))) =
      some (.evaluated .unknown) := by
  native_decide

/- A fields-side omitted tail types `No` as OMISSION, but never taints `NotAll`. -/
example :
    verdictOf (authored .no) sparseRows
      (directRead (.parsed (.num 5)) .empty)
      (constantStarRead (.parsed (.num 7))) = some (.fired .omission) ∧
    verdictOf (authored .no) fullRows
      (directRead (.parsed (.num 5)) .empty)
      (constantStarRead (.parsed (.num 7))) = some (.fired .value) ∧
    verdictOf (authored .notAll) sparseRows
      (directRead (.parsed (.num 5)) .empty)
      (constantStarRead (.parsed (.num 7))) = some (.fired .value) := by
  native_decide

/- Empty and malformed value fields retain the three operators' asymmetric value-side rules. -/
example :
    verdictOf (authored .no) fullRows (directRead .empty .empty)
      (constantStarRead (.parsed (.num 7))) = some (.fired .omission) ∧
    verdictOf (authored .notAll) fullRows (directRead .empty .empty)
      (constantStarRead (.parsed (.num 7))) = some (.fired .omission) ∧
    verdictOf (authored .atLeastOne (restValues := ["Spare"])) fullRows
      (directRead (.rejected .malformed) (.parsed (.num 7)))
      (constantStarRead (.parsed (.num 7))) = some (.fired .value) ∧
    verdictOf (authored .notAll) fullRows
      (directRead (.rejected .malformed) .empty)
      (constantStarRead (.parsed (.num 7))) = some .unknown := by
  native_decide

private def repetition (origin : HavingOrigin) (groups : List String) :
    SurfaceHavingRepetitionRef :=
  { origin, group := { base := .absolute, groups } }

private def earlierSibling : SurfaceCorrelatedHaving :=
  .and
    (.compareRepetitions .equal
      (repetition .inner ["Shop", "Sections"])
      (repetition .outer ["Shop", "Sections"]))
    (.compareRepetitions .less
      (repetition .inner ["Shop", "Sections", "Items"])
      (repetition .outer ["Shop", "Sections", "Items"]))

private def selectedOnly (environment : Env) (_ : FieldId) : RawCell :=
  if environment == [(10, 1), (20, 1)] then .parsed (.num 5)
  else .rejected .malformed

/- `Having` selects before target classification and escalates a reached firing. -/
example :
    verdictOf (authored .atLeastOne
      (.starHaving (starPath) earlierSibling)) fullRows
      (directRead (.parsed (.num 5)) .empty) selectedOnly
      [(10, 1), (20, 2)] = some (.fired .omission) := by
  native_decide

/- Partial validation skips a `Having`-bearing source before malformed topology or either value reader is reached. -/
example :
    partialResultOf (authored .atLeastOne
        (.starHaving (starPath) earlierSibling))
      [{ group := 20, path := [1, 1] }] .full
      (directRead (.rejected .malformed) .empty)
      (constantStarRead (.rejected .malformed)) =
        some .skippedHaving := by
  native_decide

/- Static admission resolves duplicates before Number certification and retains the star's exact kind gate. -/
example :
    errorOf (authored .atLeastOne (firstValue := "Needle")
      (restValues := ["Needle"])) = some (.duplicateValueField needle.id) ∧
    errorOf (authored .atLeastOne (firstValue := "Text")) =
      some (.valueFieldNotNumber text.path .string) ∧
    errorOf (authored .atLeastOne (.star (starPath "Note"))) =
      some (.fields (.fieldNotNumber note.path)) := by
  native_decide

end A12Kernel.Conformance.StarNumberValueList
