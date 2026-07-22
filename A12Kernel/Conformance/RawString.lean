import A12Kernel.Elaboration.RawString
import A12Kernel.Elaboration.RepetitionNotUnique
import A12Kernel.Elaboration.StarStringValueList
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.TokenEntityList

/-! # Raw-String checked-authoring conformance locks -/

namespace A12Kernel.Conformance.RawString

open A12Kernel

private def rawNote : FlatFieldDecl :=
  { id := 1
    groupPath := ["Claim"]
    name := "IncidentNote"
    policy := { kind := .string }
    stringValueMode := .raw
    stringPolicy := { lineBreaksPermitted := true } }

private def other : FlatFieldDecl :=
  { id := 2
    groupPath := ["Claim"]
    name := "Other"
    policy := { kind := .string } }

private def rawBlob : FlatFieldDecl :=
  { id := 3
    groupPath := ["Claim", "Attachments"]
    name := "Blob"
    policy := { kind := .string }
    stringValueMode := .raw
    stringPolicy := { lineBreaksPermitted := true }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [rawNote, other, rawBlob]
    repeatableGroups := [{
      level := 10
      path := ["Claim", "Attachments"]
      repeatability := some 3 }] }

private def directPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Claim"], field }

private def blobPath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Claim", "Attachments"], field := "Blob" }

private def blobStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Claim" }, { name := "Attachments", starred := true }]
    field := "Blob" }

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def coreOf (result : Except ElabError (CheckedFlatCondition model)) :
    Option FlatCondition :=
  match result with
  | .ok checked => some checked.core
  | .error _ => none

/- Raw mode is a String-only declaration capability. -/
example : model.validate.isOk = true := by
  native_decide

example : errorOf ({ model with fields := [{ rawNote with
      policy := { kind := .boolean } }] }).validate =
    some (.rawValueModeRequiresString ["Claim", "IncidentNote"]) := by
  native_decide

/- The declaration-owned gate closes both a reported direct comparison and the independent list route. -/
example : errorOf (elaborate model ["Claim"]
    (.compare .equal (directPath "IncidentNote") (.string "x"))) =
      some (.rawStringValue ["Claim", "IncidentNote"]) := by
  native_decide

example : errorOf (elaborate model ["Claim"]
    (.stringValueMembership .included (directPath "IncidentNote") ["x"])) =
      some (.rawStringValue ["Claim", "IncidentNote"]) := by
  native_decide

example : model.admitsComparison
    (.string .equal { id := 1 } "x") = false := by
  native_decide

/- Ordinary condition lowering cannot accidentally turn the exceptional shape into runtime code. -/
example : errorOf (elaborate model ["Claim"]
    (.lengthCompare .greater (directPath "IncidentNote") 5)) =
      some (.rawStringLength ["Claim", "IncidentNote"]) := by
  native_decide

/- The exact whole-condition and mirrored forms become metadata and expose no runtime condition. -/
example :
    (elaborateFlatRuleCondition model ["Claim"]
      (.lengthCompare .greater (directPath "IncidentNote") 5)).toRawMaximum? =
        some (1, 5) ∧
    (elaborateFlatRuleCondition model ["Claim"]
      (.literalCompareLength (-1) .less (directPath "IncidentNote"))).toRawMaximum? =
        some (1, -1) := by
  native_decide

example : coreOf (elaborate model ["Claim"]
    (.literalCompareLength 5 .less (directPath "Other"))) =
      some (.compare (.stringLength .greater { id := 2 } 5)) := by
  native_decide

/- A non-strict or nested length use is not the exceptional whole-rule declaration. -/
example :
    errorOf (elaborateFlatRuleCondition model ["Claim"]
      (.lengthCompare .greaterEqual (directPath "IncidentNote") 5)) =
        some (.rawStringLength ["Claim", "IncidentNote"]) ∧
    errorOf (elaborateFlatRuleCondition model ["Claim"]
      (.and
        (.lengthCompare .greater (directPath "IncidentNote") 5)
        (.fieldFilled (directPath "Other")))) =
        some (.rawStringLength ["Claim", "IncidentNote"]) ∧
    errorOf (elaborateFlatRuleCondition model ["Claim"]
      (.lengthCompare .greater (directPath "IncidentNote") ((1 : Rat) / 2))) =
        some (.rawStringLength ["Claim", "IncidentNote"]) := by
  native_decide

/- Presence remains an ordinary stored-cell observation over the same raw declaration. -/
example : rawNote.checkRaw (.parsed (.str "ABCDEF")) = {
    rawPresent := true
    parsed := some (.str "ABCDEF")
    findings := [] } := by
  native_decide

example : (FlatField.string { id := 1 }).evalFilled {
    read := fun id =>
      if id == 1 then rawNote.checkRaw (.parsed (.str "ABCDEF"))
      else malformedCheckedCell } = .fired .value := by
  native_decide

/- Checked computation, repeatable list, aggregate-source, and uniqueness routes share the same gate. -/
example : errorOf (elaborateStringExpr model ["Claim"]
    (.field (directPath "IncidentNote"))) =
      some (.rawStringValue ["Claim", "IncidentNote"]) := by
  native_decide

example : errorOf (elaborateStarStringValueListSource model ["Claim", "Attachments"] {
    quantifier := .no
    fields := blobStar
    values := ["x"] }) =
      some (.rawStringValue ["Claim", "Attachments", "Blob"]) := by
  native_decide

example : errorOf (elaborateTokenEntitySource model ["Claim"] {
    first := .star blobStar
    rest := [] }) =
      some (.rawStringValue ["Claim", "Attachments", "Blob"]) := by
  native_decide

example : errorOf (elaborateRepetitionNotUniqueSource model ["Claim"] {
    firstKey := blobPath
    restKeys := [] }) =
      some (.rawStringValue ["Claim", "Attachments", "Blob"]) := by
  native_decide

end A12Kernel.Conformance.RawString
