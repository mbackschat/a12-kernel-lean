import A12Kernel.Elaboration.CheckedDocument

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

private def model : FlatModel :=
  { fields := [customCode, note, itemText, count]
    repeatableGroups := [
      { level := 10, path := ["Order", "Items"], repeatability := some 2 }
    ] }

private def row1 : RowAddr := { group := 10, path := [1] }

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

/- Structural addressing failure remains separate from semantic UNKNOWN. -/
example : ((checked? classified).map fun checked =>
    match checked.read { field := 3, path := [2] } with
    | .error (.missingRow row) => row == { group := 10, path := [2] }
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
