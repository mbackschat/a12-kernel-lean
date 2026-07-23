import A12Kernel.Elaboration.CheckedIndexPreliminary

/-! # Full-validation checked index preliminary locks -/

namespace A12Kernel.Conformance.CheckedIndexPreliminary

open A12Kernel

private def key : FlatFieldDecl :=
  { id := 1
    groupPath := ["Order", "Sections", "Items"]
    name := "Key"
    policy := { kind := .number { scale := 2, signed := false } }
    repeatableScope := [10, 20] }

private def sections : RepeatableGroupDecl :=
  { level := 10, path := ["Order", "Sections"], repeatability := some 2 }

private def items : RepeatableGroupDecl :=
  { level := 20
    path := ["Order", "Sections", "Items"]
    repeatability := some 3
    indexField := some key.id }

private def model : FlatModel :=
  { fields := [key], repeatableGroups := [sections, items] }

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def rows : List RowAddr := [
  row 10 [1], row 20 [1, 1], row 20 [1, 2],
  row 10 [2], row 20 [2, 1], row 20 [2, 2]]

private def cell (path : List Nat) (stored : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field := key.id, path }, stored, raw }

private def checkedFor (candidate : FlatModel) (data : DocumentData) :
    Option (CheckedDocument candidate) := do
  let prepared ←
    (prepareFlatStringContext
      ({ now := { epochMillis := 0 } } : World)
      builtinStringPatternCompiler candidate).toOption
  (checkDocument prepared "en_US" data).toOption

private def preliminaryFor (candidate : FlatModel) (data : DocumentData) :
    Option (CheckedIndexPreliminary candidate) := do
  let checked ← checkedFor candidate data
  (checked.applyFullIndexPreliminary).toOption

private def preliminaryErrorFor (candidate : FlatModel) (data : DocumentData) :
    Option CheckedIndexPreliminaryError := do
  let checked ← checkedFor candidate data
  match checked.applyFullIndexPreliminary with
  | .ok _ => none
  | .error error => some error

private def duplicateData : DocumentData :=
  { instantiatedRows := rows
    cells := [
      cell [1, 1] "5.00" (.parsed (.num 5)),
      cell [1, 2] "5" (.parsed (.num 5)),
      cell [2, 1] "5" (.parsed (.num 5)),
      cell [2, 2] "6" (.parsed (.num 6))
    ] }

/- Duplicate identity is Number-normalized, all participants are marked, and the equal key beneath another parent remains unique. -/
example : ((preliminaryFor model duplicateData).bind fun preliminary => do
    let first ←
      (preliminary.readAuthoredValidation { field := 1, path := [1, 1] }).toOption
    let second ←
      (preliminary.readAuthoredValidation { field := 1, path := [1, 2] }).toOption
    let otherParent ←
      (preliminary.readAuthoredValidation { field := 1, path := [2, 1] }).toOption
    let presence ←
      (preliminary.groupPresenceInput ["Order", "Sections", "Items"]
        [(10, 1), (20, 1)] .fullyRelevant false).toOption
    pure (
      preliminary.findingKindAt? { field := 1, path := [1, 1] } == some .unique &&
      preliminary.findingKindAt? { field := 1, path := [1, 2] } == some .unique &&
      preliminary.findingKindAt? { field := 1, path := [2, 1] } == none &&
      observeCell .validation first == .unknown .duplicateIndex &&
      observeCell .validation second == .unknown .duplicateIndex &&
      observeCell .validation otherParent == .value (.num 5) &&
      first.admitsGroupContent &&
      presence.derive ==
        { content := true, erroneous := true, relevance := .fullyRelevant })) =
    some true := by
  native_decide

private def emptyAndInvalidData : DocumentData :=
  { instantiatedRows := [
      row 10 [1], row 20 [1, 1], row 20 [1, 2], row 20 [1, 3]]
    cells := [
      cell [1, 2] "7" (.parsed (.num 7)),
      cell [1, 3] "bad" (.rejected .malformed)
    ] }

/- An empty key beside a filled key receives mandatory rather than uniqueness, while an earlier scalar failure is retained without another preliminary finding. -/
example : ((preliminaryFor model emptyAndInvalidData).bind fun preliminary => do
    let empty ←
      (preliminary.readAuthoredValidation { field := 1, path := [1, 1] }).toOption
    let filled ←
      (preliminary.readAuthoredValidation { field := 1, path := [1, 2] }).toOption
    let malformed ←
      (preliminary.readAuthoredValidation { field := 1, path := [1, 3] }).toOption
    let presence ←
      (preliminary.groupPresenceInput ["Order", "Sections", "Items"]
        [(10, 1), (20, 1)] .fullyRelevant false).toOption
    pure (
      preliminary.findingKindAt? { field := 1, path := [1, 1] } == some .mandatory &&
      preliminary.findingKindAt? { field := 1, path := [1, 2] } == none &&
      preliminary.findingKindAt? { field := 1, path := [1, 3] } == none &&
      observeCell .validation empty == .unknown .required &&
      observeCell .validation filled == .value (.num 7) &&
      observeCell .validation malformed == .unknown .malformed &&
      presence.derive ==
        { content := true, erroneous := true, relevance := .fullyRelevant })) =
    some true := by
  native_decide

/- An all-empty key scope produces one mandatory finding per row and never a duplicate cluster. -/
example : (preliminaryFor model {
    instantiatedRows := rows.take 3, cells := []
  }).map (fun preliminary =>
    (preliminary.findingKindAt? { field := 1, path := [1, 1] },
      preliminary.findingKindAt? { field := 1, path := [1, 2] })) =
    some (some .mandatory, some .mandatory) := by
  native_decide

private def stringKey : FlatFieldDecl :=
  { key with policy := { kind := .string } }

private def stringModel : FlatModel :=
  { model with fields := [stringKey] }

private def stringData (left right : String) : DocumentData :=
  { instantiatedRows := rows.take 3
    cells := [
      cell [1, 1] left (.parsed (.str left)),
      cell [1, 2] right (.parsed (.str right))
    ] }

/- Every non-Number index uses exact stored text: numeric-looking spellings remain distinct, while equal stored tokens mark both rows. -/
example :
    (preliminaryFor stringModel (stringData "5" "5.00")).map
        (fun preliminary => preliminary.findings.isEmpty) = some true ∧
    (preliminaryFor stringModel (stringData "A" "A")).map
        (fun preliminary =>
          (preliminary.findingKindAt? { field := 1, path := [1, 1] },
            preliminary.findingKindAt? { field := 1, path := [1, 2] })) =
      some (some .unique, some .unique) := by
  native_decide

/- A model-valid but source-unclosed index kind returns explicit insufficient information instead of borrowing String token semantics. -/
example :
    let booleanKey := { key with policy := { kind := .boolean } }
    let booleanModel := { model with fields := [booleanKey] }
    preliminaryErrorFor booleanModel { instantiatedRows := rows.take 3, cells := [] } =
      some (.unsupportedIndexKind booleanKey.path .boolean) := by
  native_decide

end A12Kernel.Conformance.CheckedIndexPreliminary
