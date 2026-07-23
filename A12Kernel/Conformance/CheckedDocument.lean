import A12Kernel.Elaboration.CheckedRequired

/-! # A12Kernel.Conformance.CheckedDocument — immutable checked-document boundary -/

namespace A12Kernel.Conformance.CheckedDocument

open A12Kernel

private def rejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def validator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "accepted" then none else some rejection

private def world : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some validator else none

private def customCode : FlatFieldDecl :=
  { id := 1
    groupPath := ["Order", "Details"]
    name := "Code"
    policy := { kind := .string }
    customType := some { name := "ProjectCode" } }

private def note : FlatFieldDecl :=
  { id := 2
    groupPath := ["Order", "Details"]
    name := "Note"
    policy := { kind := .string } }

private def itemText : FlatFieldDecl :=
  { id := 3
    groupPath := ["Order", "Items"]
    name := "Text"
    policy := { kind := .string }
    repeatableScope := [10] }

private def count : FlatFieldDecl :=
  { id := 4
    groupPath := ["Order", "Details"]
    name := "Count"
    policy := { kind := .number { scale := 0, signed := true } } }

private def lineText : FlatFieldDecl :=
  { id := 5
    groupPath := ["Order", "Items", "Lines"]
    name := "Text"
    policy := { kind := .string }
    repeatableScope := [10, 11] }

private def model : FlatModel :=
  { fields := [customCode, note, itemText, count, lineText]
    repeatableGroups := [
      { level := 10, path := ["Order", "Items"], repeatability := some 2 },
      { level := 11, path := ["Order", "Items", "Lines"], repeatability := some 5 }
    ] }

private def row1 : RowAddr := { group := 10, path := [1] }
private def row2 : RowAddr := { group := 10, path := [2] }
private def row3 : RowAddr := { group := 10, path := [3] }
private def line31 : RowAddr := { group := 11, path := [3, 1] }

private def classified : DocumentData :=
  { instantiatedRows := [row1]
    cells := [
      { address := { field := 1, path := [] }
        stored := "rejected"
        raw := .parsed (.str "rejected") },
      { address := { field := 2, path := [] }
        stored := ""
        raw := .presentEmpty }
    ] }

private def checked? (data : DocumentData) : Option (CheckedDocument model) :=
  match prepareFlatStringContext world builtinStringPatternCompiler model with
  | .error _ => none
  | .ok prepared => (checkDocument prepared "en_US" data).toOption

private def overLimitRows : DocumentData :=
  { instantiatedRows := [row1, row2, row3]
    cells := [
      { address := { field := 3, path := [2] }
        stored := "within"
        raw := .parsed (.str "within") },
      { address := { field := 3, path := [3] }
        stored := "beyond"
        raw := .rejected .malformed }
    ] }

/- The finite input compiles to the established functional document view without inferring rows from cells. -/
example : classified.toDocument.instantiatedRows = [row1] ∧
    classified.toDocument.rawCells { field := 2, path := [] } = some "" ∧
    classified.toDocument.rawCells { field := 4, path := [] } = none := by
  native_decide

/- One construction supplies the existing flat evaluator with cached prepared-custom and placement distinctions. -/
example : ((checked? classified).map fun checked =>
    (checked.flatContext.observeValidationAt 1,
      (checked.read { field := 2, path := [] }).toOption.map (·.rawPresent),
      (checked.read { field := 4, path := [] }).toOption.map (·.rawPresent))) =
    some (.unknown (.registeredCustomValidation rejection), some true, some false) := by
  native_decide

/- An instantiated empty repeat row remains group content even with no cell placement. -/
example : ((checked? classified).bind fun checked =>
    (checked.groupPresenceInput ["Order", "Items"] [(10, 1)]
      .fullyRelevant false).toOption.map (·.derive)) =
    some { content := true, erroneous := false, relevance := .fullyRelevant } := by
  native_decide

/- The otherwise identical absent-row input remains cleanly empty. -/
example : ((checked? { classified with instantiatedRows := [] }).bind fun checked =>
    (checked.groupPresenceInput ["Order", "Items"] [(10, 1)]
      .fullyRelevant false).toOption.map (·.derive)) =
    some { content := false, erroneous := false, relevance := .fullyRelevant } := by
  native_decide

/- Prepared formal rejection is error without admitted group content. -/
example : ((checked? classified).bind fun checked =>
    (checked.groupPresenceInput ["Order", "Details"] []
      .fullyRelevant false).toOption.map (·.derive)) =
    some { content := false, erroneous := true, relevance := .fullyRelevant } := by
  native_decide

/- Missing scope and unknown group identity are explicit construction failures, not group UNKNOWN. -/
example : ((checked? classified).map fun checked =>
    (match checked.groupPresenceInput ["Order", "Items"] []
        .fullyRelevant false with
      | .error (.missingBinding 10) => true
      | _ => false,
    match checked.groupPresenceInput ["Order", "Missing"] []
        .fullyRelevant false with
      | .error (.unknownGroup ["Order", "Missing"]) => true
      | _ => false)) = some (true, true) := by
  native_decide

/- Structural addressing failure remains separate from semantic UNKNOWN. -/
example : ((checked? classified).map fun checked =>
    match checked.read { field := 3, path := [2] } with
    | .error (.missingRow row) => row == { group := 10, path := [2] }
    | _ => false) = some true := by
  native_decide

/- The declared-capacity boundary is shared by checked star paths and the immutable checked document: an in-cap sibling remains a value while the over-limit descendant is unavailable in both phases. -/
example : ((checked? overLimitRows).bind fun checked => do
    let within ← (checked.read { field := 3, path := [2] }).toOption
    let beyond ← (checked.read { field := 3, path := [3] }).toOption
    pure (observeCell .validation within,
      observeCell .validation beyond,
      observeCell .computation beyond)) =
    some (.value (.str "within"),
      .unknown .overRepetition,
      .poison .overRepetition) := by
  native_decide

/- An over-limit row remains immutable structural content even without a placed descendant cell, while its structural error is derived rather than supplied by the caller. -/
example : ((checked? { overLimitRows with cells := [] }).bind fun checked =>
    (checked.groupPresenceInput ["Order", "Items"] [(10, 3)]
      .fullyRelevant false).toOption.bind fun presence =>
        (checked.read { field := 3, path := [3] }).toOption.map fun cell =>
          (presence.derive, observeCell .validation cell)) =
    some ({ content := true, erroneous := true, relevance := .fullyRelevant },
      .unknown .overRepetition) := by
  native_decide

/- Capacity is checked hierarchically: an otherwise in-cap inner coordinate is unavailable beneath an over-limit outer ancestor. -/
example : ((checked? {
    instantiatedRows := [row1, row2, row3, line31]
    cells := [{
      address := { field := 5, path := [3, 1] }
      stored := "nested"
      raw := .parsed (.str "nested")
    }]
  }).bind fun checked =>
    (checked.read { field := 5, path := [3, 1] }).toOption.map fun cell =>
      (observeCell .validation cell, observeCell .computation cell)) =
    some (.unknown .overRepetition, .poison .overRepetition) := by
  native_decide

/- Requiredness annotates a later validation view while computation retains the base empty observation. -/
example : ((checked? classified).bind fun checked =>
    (checked.applyAbsoluteRequiredAt 4).toOption.map fun result =>
      (result.mandatoryVerdict,
        observeCell .validation (result.authoredContext.read 4),
        observeCell .computation (result.authoredContext.read 4),
        observeCell .computation (checked.flatContext.read 4))) =
    some (.fired .omission, .unknown .required, .empty, .empty) := by
  native_decide

/- Existing formal rejection is retained and is not relabelled as required. -/
example : ((checked? classified).bind fun checked =>
    (checked.applyAbsoluteRequiredAt 1).toOption.map fun result =>
      (result.mandatoryVerdict,
        observeCell .validation (result.authoredContext.read 1),
        observeCell .computation (result.authoredContext.read 1))) =
    some (.unknown,
      .unknown (.registeredCustomValidation rejection),
      .poison (.registeredCustomValidation rejection)) := by
  native_decide

/- Absolute-required construction rejects a repeatable target instead of erasing its scope. -/
example : ((checked? classified).map fun checked =>
    match checked.applyAbsoluteRequiredAt 3 with
    | .error (.repeatableReference path) => path == ["Order", "Items", "Text"]
    | _ => false) = some true := by
  native_decide

/- Duplicate physical cells and incoherent empty classification fail at construction. -/
example : (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.map
    (fun prepared => (
      (match checkDocument prepared "en_US"
        { classified with cells := classified.cells ++ [{
            address := { field := 1, path := [] }
            stored := "rejected"
            raw := .parsed (.str "rejected")
          }] } with
      | .error (.duplicateCell address) => address == { field := 1, path := [] }
      | _ => false),
      (match checkDocument prepared "en_US" {
          classified with cells := [
          { address := { field := 2, path := [] }
            stored := ""
            raw := .parsed (.str "not empty") }
        ] } with
      | .error (.incoherentCell address) => address == { field := 2, path := [] }
      | _ => false))) = some (true, true) := by
  native_decide

end A12Kernel.Conformance.CheckedDocument
