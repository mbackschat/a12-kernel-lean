import A12Kernel.Elaboration.CheckedIndexPreliminary

/-! # Full and partial checked generated-preliminary locks -/

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

private def world : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "IndexCustom" then
      some (fun _ _ => none)
    else
      none

private def checkedFor (candidate : FlatModel) (data : DocumentData) :
    Option (CheckedDocument candidate) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler candidate).toOption
  (checkDocument prepared "en_US" data).toOption

private def preliminaryFor (candidate : FlatModel) (data : DocumentData) :
    Option (CheckedIndexPreliminary candidate) := do
  let checked ← checkedFor candidate data
  (checked.applyFullIndexPreliminary).toOption

private def partialFor (candidate : FlatModel) (data : DocumentData)
    (relevant : List RelevantEntityPattern)
    (absoluteRequiredFields : List FieldId := []) :
    Option (CheckedPartialPreliminary candidate) := do
  let checked ← checkedFor candidate data
  (checked.applyPartialGeneratedPreliminary relevant
    absoluteRequiredFields).toOption

private def partialErrorFor (candidate : FlatModel) (data : DocumentData)
    (relevant : List RelevantEntityPattern) :
    Option CheckedIndexPreliminaryError := do
  let checked ← checkedFor candidate data
  match checked.applyPartialGeneratedPreliminary relevant [] with
  | .ok _ => none
  | .error error => some error

private def resolveErrorOf {value : Type} :
    Except ResolveError value → Option ResolveError
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

private def relevantKey (sectionIndex item : Nat) : RelevantEntityPattern :=
  { path := key.path
    indices := [.concrete 1, .concrete sectionIndex, .concrete item, .concrete 1] }

private def relevantItems (sectionIndex : Nat) : RelevantEntityPattern :=
  { path := items.path
    indices := [.concrete 1, .concrete sectionIndex, .all] }

/- Partial uniqueness is rebuilt from relevant physical candidates. Both partners are marked when both are relevant; reusing the full finding list would incorrectly mark the one-partner control. -/
example :
    (partialFor model duplicateData [relevantKey 1 1, relevantKey 1 2]).map
        (fun view =>
          (view.index.findingKindAt? { field := 1, path := [1, 1] },
            view.index.findingKindAt? { field := 1, path := [1, 2] })) =
      some (some .unique, some .unique) ∧
    (partialFor model duplicateData [relevantKey 1 1]).map
        (fun view => view.index.findings.isEmpty) = some true ∧
    (partialFor model duplicateData [relevantItems 1]).map
        (fun view => view.index.findings.length) = some 2 := by
  native_decide

/- A relevant instantiated empty index receives mandatory, but a relevant pointer to an absent in-cap row neither creates topology nor a generated finding. -/
example :
    (partialFor model emptyAndInvalidData [relevantKey 1 1]).map
        (fun view =>
          view.index.findingKindAt? { field := 1, path := [1, 1] }) =
      some (some .mandatory) ∧
    ((partialFor model duplicateData [relevantKey 1 3]).bind fun view => do
      let presence ←
        (view.groupPresenceInput ["Order", "Sections", "Items"]
          [(10, 1), (20, 3)] .partlyRelevant false).toOption
      pure (view.index.findings.isEmpty &&
        presence.derive ==
          { content := false, erroneous := false,
            relevance := .partlyRelevant })) = some true := by
  native_decide

/- A selected cell that already failed scalar checking remains malformed and receives no generated index finding. -/
example : ((partialFor model emptyAndInvalidData [relevantKey 1 3]).bind fun view =>
    (view.readAuthoredValidation { field := 1, path := [1, 3] }).toOption.map
      fun cell =>
        (view.index.findings.isEmpty, observeCell .validation cell)) =
    some (true, .unknown .malformed) := by
  native_decide

/- The call-local view cannot expose a nonrelevant scalar or let its formal error contaminate a relevant ancestor-group slice. -/
example :
    let checked := checkedFor model emptyAndInvalidData
    checked.bind (fun document => do
      let view ←
        (document.applyPartialGeneratedPreliminary [relevantKey 1 2] []).toOption
      let readError :=
        match view.readAuthoredValidation { field := 1, path := [1, 3] } with
        | .ok _ => none
        | .error error => some error
      let presence ←
        (view.groupPresenceInput ["Order", "Sections"]
          [(10, 1)] .partlyRelevant false).toOption
      pure (readError, presence.derive.erroneous)) =
      some (some (.nonRelevantAddress { field := 1, path := [1, 3] }), false) := by
  native_decide

/- A concrete selector beyond declared capacity is ignored rather than turning an over-limit physical row into a partial generated finding. -/
example :
    (partialFor model emptyAndInvalidData [relevantKey 1 4]).map
        (fun view => view.index.findings.isEmpty) = some true := by
  native_decide

private def requiredField : FlatFieldDecl :=
  { id := 2
    groupPath := ["Order"]
    name := "Required"
    policy := { kind := .string } }

private def requiredModel : FlatModel := { fields := [requiredField] }

private def relevantRequired : RelevantEntityPattern :=
  { path := requiredField.path, indices := [.concrete 1, .concrete 1] }

/- Absolute nonrepeatable requiredness still targets its canonical absent cell when relevant, without making the root group physically filled. Its generated role stays separate from the index channel. -/
example : ((partialFor requiredModel
    { instantiatedRows := [], cells := [] }
    [relevantRequired] [requiredField.id]).bind fun view => do
      let authored ←
        (view.readAuthoredValidation
          { field := requiredField.id, path := [] }).toOption
      let presence ←
        (view.groupPresenceInput ["Order"] [] .partlyRelevant false).toOption
      pure (
        view.requiredVerdictAt? { field := requiredField.id, path := [] } ==
          some (.fired .omission) &&
        view.index.findings.isEmpty &&
        observeCell .validation authored == .unknown .required &&
        observeCell .computation authored == .empty &&
        presence.derive ==
          { content := false, erroneous := true,
            relevance := .partlyRelevant })) = some true := by
  native_decide

/- The same absent absolute field is not readable when its error field is outside the call-local relevant set. -/
example :
    let address : CellAddr := { field := requiredField.id, path := [] }
    let checked := checkedFor requiredModel
      { instantiatedRows := [], cells := [] }
    checked.bind (fun document => do
      let view ←
        (document.applyPartialGeneratedPreliminary [] [requiredField.id]).toOption
      match view.readAuthoredValidation address with
      | .ok _ => none
      | .error error => some error) =
      some (.nonRelevantAddress address) := by
  native_decide

/- Unknown, misaligned, and zero-index relevant entities fail explicitly; none is silently interpreted as an empty relevant set. -/
example :
    let unknown : RelevantEntityPattern :=
      { path := ["Order", "Missing"], indices := [.all, .all] }
    let misaligned : RelevantEntityPattern :=
      { path := key.path, indices := [.all] }
    let zero : RelevantEntityPattern :=
      { path := key.path
        indices := [.concrete 1, .concrete 1, .concrete 0, .concrete 1] }
    partialErrorFor requiredModel
        { instantiatedRows := [], cells := [] } [unknown] =
      some (.unknownRelevantEntity unknown.path) ∧
    partialErrorFor model duplicateData [misaligned] =
      some (.relevantIndexArity misaligned.path
        misaligned.path.length misaligned.indices.length) ∧
    partialErrorFor model duplicateData [zero] =
      some (.zeroRelevantIndex zero.path 2) := by
  native_decide

private def duplicateDataFor (stored : String) (raw : RawCell) : DocumentData :=
  { instantiatedRows := rows.take 3
    cells := [cell [1, 1] stored raw, cell [1, 2] stored raw] }

private def duplicatesFor (declaration : FlatFieldDecl)
    (stored : String) (raw : RawCell) : Bool :=
  let candidate := { model with fields := [declaration] }
  match preliminaryFor candidate (duplicateDataFor stored raw) with
  | none => false
  | some preliminary => preliminary.findings.length == 2

private def dateComponents : TemporalComponents :=
  { year := true, month := true, day := true
    hour := false, minute := false, second := false }

private def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false
    hour := true, minute := true, second := true }

private def dateTimeComponents : TemporalComponents :=
  { year := true, month := true, day := true
    hour := true, minute := true, second := true }

private def instant : Instant := { epochMillis := 1719292867000 }

private def dateParts : DateParts :=
  { year := 2024, month := 6, day := 25 }

private def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

/- Every legal scalar index kind uses the one duplicate relation: Number remains numeric, while all other kinds compare their exact stored token after formal admission. -/
example :
    duplicatesFor { key with policy := { kind := .boolean } }
      "Y" (.parsed (.bool true)) &&
    duplicatesFor { key with policy := { kind := .confirm } }
      "Y" (.parsed (.conf true)) &&
    duplicatesFor {
        key with
        policy := { kind := .string }
        customType := some { name := "IndexCustom" } }
      "A" (.parsed (.str "A")) &&
    duplicatesFor {
        key with
        policy := { kind := .enumeration }
        enumeration := some { storedTokens := ["A"] } }
      "A" (.parsed (.enum "A")) &&
    duplicatesFor {
        key with policy := { kind := .temporal .date dateComponents } }
      "2024-06-25"
      (.parsed (.temporal (.date instant dateParts .storedGregorian))) &&
    duplicatesFor {
        key with policy := { kind := .temporal .time timeComponents } }
      "05:21:07" (.parsed (.temporal (.time instant clock))) &&
    duplicatesFor {
        key with
        policy := { kind := .temporal .dateTime dateTimeComponents } }
      "2024-06-25T05:21:07"
      (.parsed (.temporal
        (.dateTime instant dateParts clock .storedGregorian))) = true := by
  native_decide

/- The shared model certificate rejects a raw/no-value String index before preliminary dispatch. -/
example :
    let rawKey := {
      key with
      policy := { kind := .string }
      stringValueMode := .raw
      stringPolicy := { lineBreaksPermitted := true }
    }
    resolveErrorOf ({ model with fields := [rawKey] }).validate =
      some (.invalidIndexField items.path rawKey.id) := by
  native_decide

end A12Kernel.Conformance.CheckedIndexPreliminary
