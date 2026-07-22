import A12Kernel.Elaboration.Flat

/-! # A12Kernel.Conformance.FlatEnumeration — checked nonrepeatable integration locks -/

namespace A12Kernel.Conformance.FlatEnumeration

open A12Kernel

private def enumSource : EnumerationDeclaration :=
  { storedTokens := ["A", "B"]
    categories := [{ name := "Kind", tokens := ["Shared", "Shared"] }] }

private def enumDecl : FlatFieldDecl :=
  { id := 20
    groupPath := ["Order"]
    name := "Code"
    policy := { kind := .enumeration }
    enumeration := some enumSource }

private def model : FlatModel := { fields := [enumDecl] }

private def path : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := "Code" }

private def coreOf {model : FlatModel}
    (result : Except ElabError (CheckedFlatCondition model)) :
    Option FlatCondition :=
  match result with
  | .ok checked => some checked.core
  | .error _ => none

private def errorOf (result : Except ElabError α) : Option ElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def verdictOf (result : Except ElabError Verdict) : Option Verdict :=
  match result with
  | .ok verdict => some verdict
  | .error _ => none

private def resolveErrorOf (result : Except ResolveError Unit) : Option ResolveError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def storedCore : FlatCondition :=
  .compare (.enumeration .equal { id := 20 } .stored .stored "A")

private def categoryMapping : ResolvedEnumerationCategory :=
  { storedTokens := ["A", "B"], categoryTokens := ["Shared", "Shared"] }

private def categoryCore : FlatCondition :=
  .compare (.enumeration .equal { id := 20 } (.category "Kind")
    (.category categoryMapping) "Shared")

example : coreOf (elaborate model ["Order"] (.compare .equal path (.string "A"))) =
    some storedCore := by native_decide

example : coreOf (elaborate model ["Order"]
    (.compareEnumeration .equal path (.category "Kind") "Shared")) =
    some categoryCore := by native_decide

private def raw (value : RawCell) : RawFlatContext where
  read _ := value

private def world : World := { now := { epochMillis := 0 } }

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (raw (.parsed (.enum "A"))) true (.compare .equal path (.string "A"))) =
    some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (raw (.parsed (.enum "B"))) true (.compare .equal path (.string "A"))) =
    some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (raw (.parsed (.enum "B"))) true
      (.compareEnumeration .equal path (.category "Kind") "Shared")) =
    some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (raw (.parsed (.enum "C"))) true (.compare .equal path (.string "A"))) =
    some .unknown := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (raw (.parsed (.str "A"))) true (.compare .equal path (.string "A"))) =
    some .unknown := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (raw .empty) true (.fieldNotFilled path)) = some (.fired .omission) := by native_decide

example : storedCore.evalSelected (model.checkContext (raw (.parsed (.enum "A"))))
    (fun _ => false) = .unknown := by native_decide

example : errorOf (elaborate model ["Order"] (.compare .equal path (.string "C"))) =
    some (.enumerationOperand ["Order", "Code"] (.invalidLiteral "C")) := by native_decide

example : errorOf (elaborate model ["Order"]
    (.compareEnumeration .equal path (.category "kind") "Shared")) =
    some (.enumerationOperand ["Order", "Code"] (.unknownCategory "kind")) := by native_decide

example : errorOf (elaborate model ["Order"]
    (.compareEnumeration .less path .stored "A")) =
    some (.unsupportedOperator .less) := by native_decide

private def missingMetadataModel : FlatModel :=
  { fields := [{ enumDecl with enumeration := none }] }

example : resolveErrorOf missingMetadataModel.validate =
    some (.enumerationDeclarationRequired ["Order", "Code"]) := by native_decide

private def invalidDeclarationModel : FlatModel :=
  { fields := [{ enumDecl with enumeration := some { storedTokens := [] } }] }

example : resolveErrorOf invalidDeclarationModel.validate =
    some (.invalidEnumerationDeclaration ["Order", "Code"] .emptyStoredDomain) := by native_decide

private def stringDecl : FlatFieldDecl :=
  { id := 10, groupPath := ["Order"], name := "Text", policy := { kind := .string } }

private def identityEnumDecl : FlatFieldDecl :=
  { enumDecl with id := 21, name := "Identity", enumeration := some {
      storedTokens := ["A", "B"]
      displayFacts := [
        { locale := "en", stored := "A", display := "A" },
        { locale := "en", stored := "B", display := "B" }] } }

private def displayEnumDecl : FlatFieldDecl :=
  { enumDecl with id := 22, name := "Display", enumeration := some {
      storedTokens := ["A", "B"]
      displayFacts := [
        { locale := "en", stored := "A", display := "Alpha" },
        { locale := "en", stored := "B", display := "Beta" }] } }

private def compatibleEnumDecl : FlatFieldDecl :=
  { enumDecl with id := 23, name := "Compatible", enumeration := some {
      storedTokens := ["A", "C"]
      displayFacts := [
        { locale := "en", stored := "A", display := "Alpha" },
        { locale := "en", stored := "C", display := "Gamma" }] } }

private def conflictingEnumDecl : FlatFieldDecl :=
  { enumDecl with id := 24, name := "Conflict", enumeration := some {
      storedTokens := ["A", "C"]
      displayFacts := [
        { locale := "en", stored := "A", display := "Another" },
        { locale := "en", stored := "C", display := "Gamma" }] } }

private def fieldModel : FlatModel :=
  { fields := [stringDecl, enumDecl, identityEnumDecl, displayEnumDecl,
      compatibleEnumDecl, conflictingEnumDecl] }

private def fieldPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def rawPair (leftId : FieldId) (left : RawCell)
    (rightId : FieldId) (right : RawCell) : RawFlatContext where
  read id := if id == leftId then left else if id == rightId then right else .empty

private def textEnumCore : FlatCondition :=
  .compare (.textFields .equal (.string { id := 10 }) (.enumeration { id := 20 }))

example : coreOf (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Text") (fieldPath "Code"))) = some textEnumCore := by native_decide

example : coreOf (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Text") (fieldPath "Text"))) = some
      (.compare (.textFields .equal (.string { id := 10 }) (.string { id := 10 }))) := by
  native_decide

example : coreOf (elaborate fieldModel ["Order"] (.compareFields .notEqual
    (fieldPath "Code") (fieldPath "Identity"))) = some
      (.compare (.textFields .notEqual (.enumeration { id := 20 })
        (.enumeration { id := 21 }))) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 10 (.parsed (.str "A")) 20 (.parsed (.enum "A"))) true
    (.compareFields .equal (fieldPath "Text") (fieldPath "Code"))) =
    some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "A")) 21 (.parsed (.enum "B"))) true
    (.compareFields .notEqual (fieldPath "Code") (fieldPath "Identity"))) =
    some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 10 (.parsed (.str "A")) 20 (.parsed (.enum "C"))) true
    (.compareFields .equal (fieldPath "Text") (fieldPath "Code"))) =
    some .unknown := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 10 (.parsed (.str "A")) 20 .empty) true
    (.compareFields .notEqual (fieldPath "Text") (fieldPath "Code"))) =
    some .notFired := by native_decide

example : textEnumCore.evalSelected
    (fieldModel.checkContext (rawPair 10 (.parsed (.str "A")) 20 (.parsed (.enum "A"))))
    (fun id => id == 10) = .unknown := by native_decide

example : (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Display") (fieldPath "Compatible"))).isOk = true := by native_decide

example : errorOf (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Text") (fieldPath "Display"))) = some
      (.enumerationComparability ["Order", "Text"] ["Order", "Display"]
        .displayClassMismatch) := by native_decide

example : errorOf (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Display") (fieldPath "Conflict"))) = some
      (.enumerationComparability ["Order", "Display"] ["Order", "Conflict"]
        .displayMapConflict) := by native_decide

example : errorOf (elaborate fieldModel ["Order"] (.compareFields .less
    (fieldPath "Text") (fieldPath "Code"))) = some (.unsupportedOperator .less) := by
  native_decide

end A12Kernel.Conformance.FlatEnumeration
