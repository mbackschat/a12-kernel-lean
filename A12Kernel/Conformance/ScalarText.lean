import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.ScalarText

/-! # Stored Boolean and Confirm text locks

These cases exercise the canonical storage formal-check boundary before ordinary checked-document and scalar consumers. Display tokens, ingress conversion, and model-declared `@NotInD` alternatives are deliberately absent from the classifier.
-/

namespace A12Kernel.Conformance.ScalarText

open A12Kernel

private def boolean : FlatFieldDecl := {
  id := 1
  groupPath := ["Flags"]
  name := "Boolean"
  policy := { kind := .boolean }
}

private def confirm : FlatFieldDecl := {
  id := 2
  groupPath := ["Flags"]
  name := "Confirm"
  policy := { kind := .confirm }
}

private def model : FlatModel := {
  fields := [boolean, confirm]
}

private def world : World := {
  now := { epochMillis := 0 }
}

private def cell (field : FieldId) (stored : String) (raw : RawCell) :
    ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

private def checked? (booleanText confirmText : String) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      cell boolean.id booleanText
        (classifyStoredBooleanText booleanText),
      cell confirm.id confirmText
        (classifyStoredConfirmText confirmText)
    ]
  } |>.toOption

private def forgedError? (field : FieldId) (stored : String)
    (raw : RawCell) : Option CheckedDocumentError := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  match checkDocument prepared "en_US" {
      instantiatedRows := []
      cells := [cell field stored raw]
    } with
  | .error error => some error
  | .ok _ => none

/- Only the exact canonical lowercase tokens become values; an empty physical placement stays present-empty. -/
example :
    classifyStoredBooleanText "" = .presentEmpty ∧
      classifyStoredBooleanText "true" = .parsed (.bool true) ∧
      classifyStoredBooleanText "false" = .parsed (.bool false) ∧
      classifyStoredConfirmText "" = .presentEmpty ∧
      classifyStoredConfirmText "true" = .parsed (.conf true) := by
  native_decide

/- Casing, display spellings, declared-token spellings, and Confirm false retain their exact formal cause and fixed code. -/
example :
    ["TRUE", "False", "yes", "Y", "N", "ja"].map
        classifyStoredBooleanText =
      List.replicate 6 (.rejected .booleanToken) ∧
    ["TRUE", "false", "yes", "Y", "ja"].map
        classifyStoredConfirmText =
      List.replicate 5 (.rejected .confirmToken) ∧
    FormalCause.booleanToken.fixedFormalErrorCode? =
      some "feldJaNeinFalsch" ∧
    FormalCause.confirmToken.fixedFormalErrorCode? =
      some "feldJaFalsch" := by
  native_decide

/- Canonical values survive checked-document construction and reach the established scalar operands without reparsing. -/
example :
    (do
      let checked ← checked? "false" "true"
      pure (
        checked.flatContext.resolveBooleanComparisonOperand { id := 1 },
        checked.flatContext.resolveConfirmComparisonOperand { id := 2 },
        (FlatComparison.boolean .equal { id := 1 } false).eval
          checked.flatContext,
        (FlatComparison.confirm .equal { id := 2 }).eval
          checked.flatContext)) =
      some (.value false true, .value true true,
        .fired .value, .fired .value) := by
  native_decide

/- Invalid stored tokens remain distinct formal unavailability after document checking; they never silently evaluate as false. -/
example :
    (do
      let checked ← checked? "TRUE" "false"
      pure (
        checked.flatContext.observeValidationAt 1,
        checked.flatContext.observeValidationAt 2,
        (FlatComparison.boolean .equal { id := 1 } false).eval
          checked.flatContext,
        (FlatComparison.confirm .notEqual { id := 2 }).eval
          checked.flatContext)) =
      some (.unknown .booleanToken, .unknown .confirmToken,
        .unknown, .unknown) := by
  native_decide

/- Empty placed text remains distinguishable from absence while both scalar consumers retain their established empty rules. -/
example :
    (do
      let checked ← checked? "" ""
      let booleanCell ← checked.read { field := 1, path := [] } |>.toOption
      let confirmCell ← checked.read { field := 2, path := [] } |>.toOption
      pure (
        booleanCell.rawPresent,
        confirmCell.rawPresent,
        checked.flatContext.resolveBooleanComparisonOperand { id := 1 },
        checked.flatContext.resolveConfirmComparisonOperand { id := 2 })) =
      some (true, true, .notEvaluated, .value false false) := by
  native_decide

/- Checked-document construction certifies the text/classification pair; a caller cannot bypass the canonical gate with a forged parsed value. -/
example :
    forgedError? 1 "TRUE" (.parsed (.bool true)) =
        some (.incoherentCell { field := 1, path := [] }) ∧
      forgedError? 1 "Y" (.parsed (.bool true)) =
        some (.incoherentCell { field := 1, path := [] }) ∧
      forgedError? 2 "false" (.parsed (.conf true)) =
        some (.incoherentCell { field := 2, path := [] }) := by
  native_decide

end A12Kernel.Conformance.ScalarText
