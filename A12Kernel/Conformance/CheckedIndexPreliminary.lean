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
    (relevant : List RelevantEntityPattern) :
    Option (CheckedPartialPreliminary candidate) := do
  let checked ← checkedFor candidate data
  (checked.applyPartialGeneratedPreliminary relevant).toOption

private def partialErrorFor (candidate : FlatModel) (data : DocumentData)
    (relevant : List RelevantEntityPattern) :
    Option CheckedIndexPreliminaryError := do
  let checked ← checkedFor candidate data
  match checked.applyPartialGeneratedPreliminary relevant with
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

/- Non-Number index identity uses normalized cache text: numeric-looking spellings remain distinct, while equal stored tokens mark both rows. -/
example :
    (preliminaryFor stringModel (stringData "5" "5.00")).map
        (fun preliminary => preliminary.findings.isEmpty) = some true ∧
    (preliminaryFor stringModel (stringData "A" "A")).map
        (fun preliminary =>
          (preliminary.findingKindAt? { field := 1, path := [1, 1] },
            preliminary.findingKindAt? { field := 1, path := [1, 2] })) =
      some (some .unique, some .unique) := by
  native_decide

private def multilineStringModel : FlatModel :=
  { model with fields := [{ stringKey with stringPolicy := { lineBreaksPermitted := true } }] }

example :
    (preliminaryFor multilineStringModel (stringData "a\r\nb" "a\nb")).map
        (fun preliminary => preliminary.findings.map (·.kind)) =
      some [.unique, .unique] ∧
    (preliminaryFor multilineStringModel (stringData "a\rb" "a\nb")).map
        (fun preliminary => preliminary.findings.isEmpty) = some true := by
  native_decide

private def relevantKey (sectionIndex item : Nat) : RelevantEntityPattern :=
  { path := key.path
    indices := [.concrete 1, .concrete sectionIndex, .concrete item, .concrete 1] }

private def defaultKey : FlatFieldDecl :=
  { key with
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["A", "B"]
      defaultStoredToken := some "B"
    } }

private def defaultModel : FlatModel :=
  { model with fields := [defaultKey] }

private def oneDefaultRow (cells : List ClassifiedCellInput := []) :
    DocumentData :=
  { instantiatedRows := [row 10 [1], row 20 [1, 1]]
    cells }

private def defaultAddress : CellAddr :=
  { field := defaultKey.id, path := [1, 1] }

example : [oneDefaultRow, oneDefaultRow [cell [1, 1] "" .presentEmpty]].all
    (fun data => (do
      let preliminary ← preliminaryFor defaultModel data
      let input := preliminary.computationInput
      let checked ← (input.read defaultAddress).toOption
      pure (observeCell .computation checked == .value (.enum "B") &&
        input.storedTextAt defaultAddress == some "B" &&
        input.source.cells == data.cells)) == some true) = true := by native_decide

/- Full validation injects the checked stored default into its transient view for both an absent and a physically present-empty cell, without mutating the checked source. -/
example :
    let absent := preliminaryFor defaultModel (oneDefaultRow)
    let presentEmpty :=
      preliminaryFor defaultModel
        (oneDefaultRow [cell [1, 1] "" .presentEmpty])
    absent.bind (fun preliminary => do
      let base ← (preliminary.base.read defaultAddress).toOption
      let staged ←
        (preliminary.readAuthoredValidation defaultAddress).toOption
      let presence ←
        (preliminary.groupPresenceInput
          ["Order", "Sections", "Items"]
          [(10, 1), (20, 1)] .fullyRelevant false).toOption
      pure (
        preliminary.defaultStoredAt? defaultAddress == some "B" &&
        preliminary.findingKindAt? defaultAddress == none &&
        observeCell .validation base == .empty &&
        observeCell .validation staged == .value (.enum "B") &&
        presence.derive ==
          { content := true, erroneous := false,
            relevance := .fullyRelevant })) =
      some true ∧
    presentEmpty.bind (fun preliminary => do
      let staged ←
        (preliminary.readAuthoredValidation defaultAddress).toOption
      pure (
        preliminary.defaultStoredAt? defaultAddress == some "B" &&
        observeCell .validation staged == .value (.enum "B") &&
        preliminary.base.source.cells.length == 1)) =
      some true := by
  native_decide

/- Partial validation retains the same eligible address as silent call-local unavailability: no generated index finding is exposed, dependent reads do not see the default, and the containing group remains erroneous. -/
example :
    ((partialFor defaultModel (oneDefaultRow)
        [relevantKey 1 1]).bind fun view => do
      let read ← (view.readAuthoredValidation defaultAddress).toOption
      let presence ←
        (view.groupPresenceInput ["Order", "Sections", "Items"]
          [(10, 1), (20, 1)] false).toOption
      pure (
        view.silentlyUnavailable.contains defaultAddress &&
        view.index.findingKindAt? defaultAddress == none &&
        read == .silentlyUnavailable &&
        presence.derive ==
          { content := true, erroneous := true,
            relevance := .fullyRelevant })) =
      some true := by
  native_decide

/- Default suppression is relevance-local: an excluded eligible default cannot contaminate a queried relevant ancestor group. -/
example :
    let selectedData : DocumentData := {
      instantiatedRows := [
        row 10 [1], row 20 [1, 1],
        row 10 [2], row 20 [2, 1]]
      cells := [cell [1, 1] "A" (.parsed (.enum "A"))]
    }
    ((partialFor defaultModel selectedData [relevantKey 1 1]).bind fun view => do
      let presence ←
        (view.groupPresenceInput ["Order"] []
          false).toOption
      pure (
        view.silentlyUnavailable.isEmpty &&
        presence.derive ==
          { content := true, erroneous := false,
            relevance := .partlyRelevant })) =
      some true := by
  native_decide

/- Eligibility remains source-grounded: two sibling rows, explicit requiredness, an admitted explicit value, a non-Enumeration index, and no physical row cannot manufacture a default. -/
example :
    let twoRows : DocumentData :=
      { instantiatedRows := [
          row 10 [1], row 20 [1, 1], row 20 [1, 2]]
        cells := [] }
    let mandatoryKey := {
      defaultKey with
      requiredness := some .absoluteOrNearestRepeatableAncestor
    }
    let mandatoryModel := { defaultModel with fields := [mandatoryKey] }
    let explicit :=
      oneDefaultRow [cell [1, 1] "A" (.parsed (.enum "A"))]
    (preliminaryFor defaultModel twoRows).map
        (fun preliminary =>
          preliminary.defaulted.isEmpty &&
          preliminary.findings.length == 2) =
      some true ∧
    (preliminaryFor mandatoryModel (oneDefaultRow)).map
        (fun preliminary =>
          preliminary.defaulted.isEmpty &&
          preliminary.findingKindAt? defaultAddress == some .mandatory) =
      some true ∧
    (preliminaryFor defaultModel explicit).bind
        (fun preliminary => do
          let staged ←
            (preliminary.readAuthoredValidation defaultAddress).toOption
          pure (
            preliminary.defaulted.isEmpty &&
            observeCell .validation staged == .value (.enum "A"))) =
      some true ∧
    (preliminaryFor stringModel (oneDefaultRow)).map
        (fun preliminary => preliminary.defaulted.isEmpty) =
      some true ∧
    (preliminaryFor defaultModel
        { instantiatedRows := [row 10 [1]], cells := [] }).map
        (fun preliminary =>
          preliminary.defaulted.isEmpty && preliminary.findings.isEmpty) =
      some true := by
  native_decide

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
          [(10, 1), (20, 3)] false).toOption
      pure (view.index.findings.isEmpty &&
        presence.derive ==
          { content := false, erroneous := false,
            relevance := .fullyRelevant })) = some true := by
  native_decide

/- A selected cell that already failed scalar checking remains malformed and receives no generated index finding. -/
example : ((partialFor model emptyAndInvalidData [relevantKey 1 3]).bind fun view => do
    let read ←
      (view.readAuthoredValidation { field := 1, path := [1, 3] }).toOption
    match read with
    | .checked cell =>
        some (view.index.findings.isEmpty, observeCell .validation cell)
    | .silentlyUnavailable => none) =
    some (true, .unknown .malformed) := by
  native_decide

/- The call-local view cannot expose a nonrelevant scalar or let its formal error contaminate a relevant ancestor-group slice. -/
example :
    let checked := checkedFor model emptyAndInvalidData
    checked.bind (fun document => do
      let view ←
        (document.applyPartialGeneratedPreliminary [relevantKey 1 2]).toOption
      let readError :=
        match view.readAuthoredValidation { field := 1, path := [1, 3] } with
        | .ok _ => none
        | .error error => some error
      let presence ←
        (view.groupPresenceInput ["Order", "Sections"]
          [(10, 1)] false).toOption
      pure (readError, presence.derive.erroneous)) =
      some (some (.nonRelevantAddress { field := 1, path := [1, 3] }), false) := by
  native_decide

/- A concrete selector beyond declared capacity creates no partial generated finding for the over-limit row; retaining its ancestor relevance does not admit that row. -/
example :
    (partialFor model emptyAndInvalidData [relevantKey 1 4]).map
        (fun view => view.index.findings.isEmpty) = some true := by
  native_decide

private def requiredField : FlatFieldDecl :=
  { id := 2
    groupPath := ["Order"]
    name := "Required"
    policy := { kind := .string }
    requiredness := some .absoluteOrNearestRepeatableAncestor }

private def requiredModel : FlatModel := { fields := [requiredField] }

private def relevantRequired : RelevantEntityPattern :=
  { path := requiredField.path, indices := [.concrete 1, .concrete 1] }

/- Absolute nonrepeatable requiredness still targets its canonical absent cell when relevant, without making the root group physically filled. Its generated role stays separate from the index channel. -/
example : ((partialFor requiredModel
    { instantiatedRows := [], cells := [] }
    [relevantRequired]).bind fun view => do
      let authored ←
        (view.readAuthoredValidation
          { field := requiredField.id, path := [] }).toOption
      let presence ←
        (view.groupPresenceInput ["Order"] [] false).toOption
      match authored with
      | .silentlyUnavailable => none
      | .checked cell =>
          pure (
            view.requiredVerdictAt? { field := requiredField.id, path := [] } ==
              some (.fired .omission) &&
            view.index.findings.isEmpty &&
            observeCell .validation cell == .unknown .required &&
            observeCell .computation cell == .empty &&
            presence.derive ==
              { content := false, erroneous := true,
                relevance := .fullyRelevant })) = some true := by
  native_decide

/- The model, not a caller inventory, supplies every relevant absolute-required generated rule. -/
example :
    let address : CellAddr := { field := requiredField.id, path := [] }
    (partialFor requiredModel
      { instantiatedRows := [], cells := [] }
      [relevantRequired]).map
        (fun view => view.requiredVerdictAt? address) =
      some (some (.fired .omission)) := by
  native_decide

/- The same absent absolute field is not readable when its error field is outside the call-local relevant set. -/
example :
    let address : CellAddr := { field := requiredField.id, path := [] }
    let checked := checkedFor requiredModel
      { instantiatedRows := [], cells := [] }
    checked.bind (fun document => do
      let view ← (document.applyPartialGeneratedPreliminary []).toOption
      match view.readAuthoredValidation address with
      | .ok _ => none
      | .error error => some error) =
      some (.nonRelevantAddress address) := by
  native_decide

/- The call-local preliminary constructor owns global augmentation, so a global field remains relevant even when the caller supplies an empty entity set. -/
example :
    let globalField := { requiredField with isGlobal := true }
    let globalModel : FlatModel := { fields := [globalField] }
    let address : CellAddr := { field := globalField.id, path := [] }
    (partialFor globalModel { instantiatedRows := [], cells := [] } []).map
        (fun view => view.isAddressRelevant address) =
      some true := by
  native_decide

/- An optional declaration produces no generated rule, and a parent-gated one draws no finding while its parent holds no content; neither becomes mandatory. -/
example :
    let optionalField := { requiredField with requiredness := none }
    let optionalModel : FlatModel := { fields := [optionalField] }
    let parentField := {
      requiredField with requiredness := some .relativeToParent }
    let parentModel : FlatModel := { fields := [parentField] }
    (partialFor optionalModel
        { instantiatedRows := [], cells := [] }
        [relevantRequired]).map (fun view => (RequiredEvaluation.mandatoryAddresses view.required).isEmpty) =
      some true ∧
    (partialFor parentModel
        { instantiatedRows := [], cells := [] }
        [relevantRequired]).map (fun view => (RequiredEvaluation.mandatoryAddresses view.required).isEmpty) =
      some true := by
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

private def dateMidnight : Instant := { epochMillis := 1719273600000 }

private def dateParts : DateParts :=
  { year := 2024, month := 6, day := 25 }

private def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

/- Every legal scalar index kind uses the one duplicate relation: Number remains numeric, while all other kinds compare their exact stored token after formal admission. -/
example :
    duplicatesFor { key with policy := { kind := .boolean } }
      "true" (.parsed (.bool true)) &&
    duplicatesFor { key with policy := { kind := .confirm } }
      "true" (.parsed (.conf true)) &&
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
      (.parsed (.temporal (.date {
        instant, parts := dateParts, basis := .storedGregorian }))) &&
    duplicatesFor {
        key with policy := { kind := .temporal .time timeComponents } }
      "05:21:07" (.parsed (.temporal (.time instant clock))) &&
    duplicatesFor {
        key with
        policy := { kind := .temporal .dateTime dateTimeComponents } }
      "2024-06-25T05:21:07"
      (.parsed (.temporal
        (.dateTime instant dateParts clock .storedGregorian))) &&
    duplicatesFor {
        key with
        policy := { kind := .dateRange }
        dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }
      "2024-06-25/2024-06-25"
      (.parsed (.dateRange (.exact {
        start := {
          instant := dateMidnight
          parts := dateParts
          basis := .storedGregorian }
        finish := {
          instant := dateMidnight
          parts := dateParts
          basis := .storedGregorian } }))) = true := by
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

/-! ### An index field nominated in a non-repeatable group

`Claim/Holder` is non-repeatable and nominates `HolderKey`; the repeatable `Claim/Covers` holds the
non-repeatable `Detail`, which nominates `DetailKey`. The rows replay the three-engine
`NonRepeatableIndexFieldGeneratedChecksDiffTest` at a12-dmkits `fecf8552`
([inbound](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27)). The generated check is
the mandatory one only: no uniqueness arm, and no check without the group's content. -/

private def holderName : FlatFieldDecl :=
  { id := 1, groupPath := ["Claim", "Holder"], name := "Name", policy := { kind := .string } }

private def holderKey : FlatFieldDecl :=
  { id := 2, groupPath := ["Claim", "Holder"], name := "HolderKey", policy := { kind := .string } }

private def detailNote : FlatFieldDecl :=
  { id := 3, groupPath := ["Claim", "Covers", "Detail"], name := "Note", policy := { kind := .string }
    repeatableScope := [10] }

private def detailKey : FlatFieldDecl :=
  { detailNote with id := 4, name := "DetailKey" }

private def nominatedModel : FlatModel :=
  { fields := [holderName, holderKey, detailNote, detailKey]
    repeatableGroups := [{ level := 10, path := ["Claim", "Covers"], repeatability := some 3 }]
    nonrepeatableIndexFields :=
      [(["Claim", "Holder"], holderKey.id), (["Claim", "Covers", "Detail"], detailKey.id)] }

/-- The control: the same fields and documents with no key nominated. -/
private def unnominatedModel : FlatModel := { nominatedModel with nonrepeatableIndexFields := [] }

private def textCell (field : FieldId) (path : List Nat) (stored : String) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw := .parsed (.str stored) }

private def holderOnly : DocumentData :=
  { instantiatedRows := [], cells := [textCell holderName.id [] "Ada"] }

private def detailNoteOnly : DocumentData :=
  { instantiatedRows := [row 10 [1]], cells := [textCell detailNote.id [1] "n"] }

private def sharedDetailKey : DocumentData :=
  { instantiatedRows := [row 10 [1], row 10 [2]]
    cells := [
      textCell detailNote.id [1] "n", textCell detailKey.id [1] "a",
      textCell detailNote.id [2] "m", textCell detailKey.id [2] "a"] }

private def coverWithoutDetail : DocumentData :=
  { instantiatedRows := [row 10 [1]], cells := [] }

private def mandatoryAt (field : FieldId) (path : List Nat) : IndexPreliminaryFinding :=
  { address := { field, path }, kind := .mandatory }

/- A present group whose key is empty draws the mandatory finding at the key, whether the group is
fixed under the root or inside a repeatable row. -/
example :
    (preliminaryFor nominatedModel holderOnly).map (·.findings) = some [mandatoryAt holderKey.id []] ∧
      (preliminaryFor nominatedModel detailNoteOnly).map (·.findings) =
        some [mandatoryAt detailKey.id [1]] := by
  native_decide

/- Two details sharing a key draw no finding, because no uniqueness arm exists there, and neither does
a cover without a `Detail`, whose group has no content. -/
example :
    (preliminaryFor nominatedModel sharedDetailKey).map (·.findings) = some [] ∧
      (preliminaryFor nominatedModel coverWithoutDetail).map (·.findings) = some [] := by
  native_decide

/- The control: with the keys not nominated, the same empty-key documents draw no finding. -/
example :
    (preliminaryFor unnominatedModel holderOnly).map (·.findings) = some [] ∧
      (preliminaryFor unnominatedModel detailNoteOnly).map (·.findings) = some [] := by
  native_decide

/- The finding carries the annotation a repeatable index field's mandatory finding carries: the cell
reads as required-unknown to authored validation. The Kernel rows above observe the generated
message, not this cell annotation, so the annotation on this carrier is not measured. -/
example :
    ((preliminaryFor nominatedModel holderOnly).bind fun preliminary => do
      let cell ← (preliminary.readAuthoredValidation { field := holderKey.id, path := [] }).toOption
      pure (observeCell .validation cell == .unknown .required)) = some true := by
  native_decide

/- A partial call generates the finding only while the group and its key are relevant: the gate reads the
call's relevance-filtered slice as the generated requirement does, so a relevant key beside an
irrelevant `Name` finds the group without admitted content. Neither this slice nor the relevance
scope is measured on this carrier; both are the requirement's and the repeatable index arm's, applied
unchanged. -/
example :
    let relevantHolder : RelevantEntityPattern :=
      { path := ["Claim", "Holder"], indices := [.concrete 1, .concrete 1] }
    let relevantHolderKey : RelevantEntityPattern :=
      { path := ["Claim", "Holder", "HolderKey"], indices := [.concrete 1, .concrete 1, .concrete 1] }
    let relevantNote : RelevantEntityPattern :=
      { path := ["Claim", "Covers", "Detail", "Note"]
        indices := [.concrete 1, .concrete 1, .concrete 1, .concrete 1] }
    ((partialFor nominatedModel holderOnly [relevantHolder]).map (·.index.findings)) =
        some [mandatoryAt holderKey.id []] ∧
      ((partialFor nominatedModel holderOnly [relevantHolderKey]).map (·.index.findings)) = some [] ∧
      ((partialFor nominatedModel holderOnly [relevantNote]).map (·.index.findings)) = some [] := by
  native_decide

end A12Kernel.Conformance.CheckedIndexPreliminary
