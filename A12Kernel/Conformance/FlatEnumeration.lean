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
  .compare (.enumeration .equal
    { field := { id := 20 }, projectionRef := .stored, projection := .stored } "A")

private def categoryMapping : ResolvedEnumerationCategory :=
  { storedTokens := ["A", "B"], categoryTokens := ["Shared", "Shared"] }

private def categoryCore : FlatCondition :=
  .compare (.enumeration .equal {
    field := { id := 20 }
    projectionRef := .category "Kind"
    projection := .category categoryMapping } "Shared")

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

private def categoryPeerDecl : FlatFieldDecl :=
  { enumDecl with id := 25, name := "CategoryPeer", enumeration := some {
      storedTokens := ["Shared", "Other"]
      displayFacts := [
        { locale := "en", stored := "Shared", display := "Gemeinsam" },
        { locale := "en", stored := "Other", display := "Anders" }]
      categories := [{ name := "Kind", tokens := ["Shared", "Other"] }] } }

private def fieldModel : FlatModel :=
  { fields := [stringDecl, enumDecl, identityEnumDecl, displayEnumDecl,
      compatibleEnumDecl, conflictingEnumDecl, categoryPeerDecl] }

private def fieldPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def rawPair (leftId : FieldId) (left : RawCell)
    (rightId : FieldId) (right : RawCell) : RawFlatContext where
  read id := if id == leftId then left else if id == rightId then right else .empty

private def textEnumCore : FlatCondition :=
  .compare (.textFields .equal (.string { id := 10 })
    (.enumeration {
      field := { id := 20 }, projectionRef := .stored, projection := .stored }))

example : coreOf (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Text") (fieldPath "Code"))) = some textEnumCore := by native_decide

example : coreOf (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Text") (fieldPath "Text"))) = some
      (.compare (.textFields .equal (.string { id := 10 }) (.string { id := 10 }))) := by
  native_decide

example : coreOf (elaborate fieldModel ["Order"] (.compareFields .notEqual
    (fieldPath "Code") (fieldPath "Identity"))) = some
      (.compare (.textFields .notEqual (.enumeration {
          field := { id := 20 }, projectionRef := .stored, projection := .stored })
        (.enumeration {
          field := { id := 21 }, projectionRef := .stored, projection := .stored }))) := by
  native_decide

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

private def categoryCode : SurfaceTextFieldOperand :=
  .category (fieldPath "Code") "Kind"

private def directCategoryPeer : SurfaceTextFieldOperand :=
  .direct (fieldPath "CategoryPeer")

example : coreOf (elaborate fieldModel ["Order"] (.compareTextFields .equal
    categoryCode directCategoryPeer)) = some (.compare (.textFields .equal
      (.enumeration {
        field := { id := 20 }
        projectionRef := .category "Kind"
        projection := .category categoryMapping })
      (.enumeration {
        field := { id := 25 }, projectionRef := .stored, projection := .stored }))) := by
  native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "B")) 25 (.parsed (.enum "Shared"))) true
    (.compareTextFields .equal categoryCode directCategoryPeer)) =
    some (.fired .value) := by native_decide

example : (elaborate fieldModel ["Order"] (.compareFields .equal
    (fieldPath "Code") (fieldPath "CategoryPeer"))).isOk = false := by native_decide

example : coreOf (elaborate fieldModel ["Order"] (.compareTextFields .equal
    categoryCode (.direct (fieldPath "Text")))) = some (.compare (.textFields .equal
      (.enumeration {
        field := { id := 20 }
        projectionRef := .category "Kind"
        projection := .category categoryMapping })
      (.string { id := 10 }))) := by native_decide

example : (elaborate fieldModel ["Order"] (.compareTextFields .equal
    categoryCode (.category (fieldPath "CategoryPeer") "Kind"))).isOk = true := by
  native_decide

example : errorOf (elaborate fieldModel ["Order"] (.compareTextFields .equal
    (.category (fieldPath "Code") "kind") directCategoryPeer)) = some
      (.enumerationOperand ["Order", "Code"] (.unknownCategory "kind")) := by native_decide

example : errorOf (elaborate fieldModel ["Order"] (.compareTextFields .equal
    (.category (fieldPath "Text") "Kind") directCategoryPeer)) = some
      (.textFieldOperandKindMismatch ["Order", "Text"] .string) := by native_decide

private def incoherentCategoryCore : FlatCondition :=
  .compare (.textFields .equal
    (.enumeration {
      field := { id := 20 }
      projectionRef := .category "Kind"
      projection := .stored })
    (.enumeration {
      field := { id := 25 }, projectionRef := .stored, projection := .stored }))

example : incoherentCategoryCore.wellFormedBool fieldModel = false := by native_decide

private def storedValueList : SurfaceCondition :=
  .enumerationValueList .atLeastOne [(.direct (fieldPath "Code"))] ["A", "B"]

private def storedValueListCore : FlatCondition :=
  .tokenValueList .atLeastOne
    [.enumeration {
      field := { id := 20 }, projectionRef := .stored, projection := .stored }]
    (.literals ["A", "B"])

example : coreOf (elaborate fieldModel ["Order"] storedValueList) =
    some storedValueListCore := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw (.parsed (.enum "B"))) true storedValueList) =
    some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw .empty) false (.enumerationValueList .no
      [(.direct (fieldPath "Code"))] ["A"])) = some (.fired .omission) := by
  native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw .empty) false (.enumerationValueList .notAll
      [(.direct (fieldPath "Code"))] ["A"])) = some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw .empty) false (.enumerationValueList .no
      [categoryCode] ["Shared"])) = some (.fired .omission) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw .empty) false (.enumerationValueList .notAll
      [categoryCode] ["Shared"])) = some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw (.parsed (.enum "B"))) true (.enumerationValueList .atLeastOne
      [categoryCode] ["Shared"])) = some (.fired .value) := by native_decide

example : storedValueListCore.evalSelected
    (fieldModel.checkContext (raw (.parsed (.enum "A")))) (fun _ => false) =
    .notFired := by native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationValueList .atLeastOne [(.direct (fieldPath "Code"))] ["Shared"])) =
    some (.enumerationOperand ["Order", "Code"] (.invalidLiteral "Shared")) := by
  native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationValueList .atLeastOne [categoryCode] ["A"])) =
    some (.enumerationOperand ["Order", "Code"] (.invalidLiteral "A")) := by
  native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationValueList .atLeastOne [(.direct (fieldPath "Code"))] [])) =
    some (.emptyValueList ["Order", "Code"]) := by native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationValueList .atLeastOne [(.direct (fieldPath "Text"))] ["A"])) =
    some (.textFieldOperandKindMismatch ["Order", "Text"] .string) := by native_decide

private def storedIncluded : SurfaceCondition :=
  .enumerationValueMembership .included (.direct (fieldPath "Code")) ["A"]

example : coreOf (elaborate fieldModel ["Order"] storedIncluded) = some
    (.tokenValueList .atLeastOne
      [.enumeration {
        field := { id := 20 }, projectionRef := .stored, projection := .stored }]
      (.literals ["A"])) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw (.parsed (.enum "A"))) true storedIncluded) = some (.fired .value) := by
  native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw (.parsed (.enum "B"))) true (.enumerationValueMembership .notIncluded
      (.direct (fieldPath "Code")) ["A"])) = some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw .empty) true storedIncluded) = some .notFired ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (raw .empty) true (.enumerationValueMembership .notIncluded
        (.direct (fieldPath "Code")) ["A"])) = some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (raw (.parsed (.enum "B"))) true (.enumerationValueMembership .included
      categoryCode ["Shared"])) = some (.fired .value) := by native_decide

private def enumerationFieldMembership (op : ValueListMembershipOp) : SurfaceCondition :=
  .enumerationFieldValueMembership op categoryCode
    [(.direct (fieldPath "CategoryPeer"))]

example : coreOf (elaborate fieldModel ["Order"]
    (enumerationFieldMembership .included)) = some
      (.tokenValueList .atLeastOne
        [.enumeration {
          field := { id := 20 }
          projectionRef := .category "Kind"
          projection := .category categoryMapping }]
        (.fields [.enumeration {
          field := { id := 25 }, projectionRef := .stored, projection := .stored }])) ∧
    coreOf (elaborate fieldModel ["Order"]
      (enumerationFieldMembership .notIncluded)) = some
        (.tokenValueList .notAll
          [.enumeration {
            field := { id := 20 }
            projectionRef := .category "Kind"
            projection := .category categoryMapping }]
          (.fields [.enumeration {
            field := { id := 25 }, projectionRef := .stored, projection := .stored }])) := by
  native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "A")) 25 (.parsed (.enum "Shared"))) true
    (enumerationFieldMembership .included)) = some (.fired .value) ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (rawPair 20 (.parsed (.enum "A")) 25 (.parsed (.enum "Other"))) true
      (enumerationFieldMembership .notIncluded)) = some (.fired .value) := by
  native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 .empty 25 (.parsed (.enum "Shared"))) true
    (enumerationFieldMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (rawPair 20 .empty 25 (.parsed (.enum "Shared"))) true
      (enumerationFieldMembership .notIncluded)) = some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.rejected .malformed) 25 (.parsed (.enum "Shared"))) true
    (enumerationFieldMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (rawPair 20 (.rejected .malformed) 25 (.parsed (.enum "Shared"))) true
      (enumerationFieldMembership .notIncluded)) = some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "A")) 25 .empty) true
    (enumerationFieldMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (rawPair 20 (.parsed (.enum "A")) 25 .empty) true
      (enumerationFieldMembership .notIncluded)) = some (.fired .omission) := by
  native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "A")) 25 (.rejected .malformed)) true
    (enumerationFieldMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (rawPair 20 (.parsed (.enum "A")) 25 (.rejected .malformed)) true
      (enumerationFieldMembership .notIncluded)) = some .unknown := by native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationFieldValueMembership .included categoryCode [])) =
    some .emptyValueListValueFields := by native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationFieldValueMembership .included
      (.direct (fieldPath "Code")) [(.direct (fieldPath "Code"))])) =
    some (.duplicateValueListField ["Order", "Code"] .stored) := by native_decide

example : (elaborate fieldModel ["Order"]
    (.enumerationFieldValueMembership .included categoryCode
      [(.direct (fieldPath "Code"))])).isOk = true := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 25 (.parsed (.enum "Shared")) 20 (.parsed (.enum "A"))) true
    (.enumerationFieldValueMembership .included
      (.direct (fieldPath "CategoryPeer")) [categoryCode])) =
    some (.fired .value) := by native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationFieldValueMembership .included categoryCode
      [(.direct (fieldPath "Text"))])) =
    some (.textFieldOperandKindMismatch ["Order", "Text"] .string) := by native_decide

private def twoFieldValueList : SurfaceCondition :=
  .enumerationValueList .atLeastOne
    [(.direct (fieldPath "Code")), (.direct (fieldPath "CategoryPeer"))]
    ["A", "Other"]

private def twoFieldValueListCore : FlatCondition :=
  .tokenValueList .atLeastOne [
      .enumeration {
        field := { id := 20 }, projectionRef := .stored, projection := .stored },
      .enumeration {
        field := { id := 25 }, projectionRef := .stored, projection := .stored }]
      (.literals ["A", "Other"])

example : coreOf (elaborate fieldModel ["Order"] twoFieldValueList) =
    some twoFieldValueListCore := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "B")) 25 (.parsed (.enum "Other"))) true
    twoFieldValueList) = some (.fired .value) := by native_decide

example : twoFieldValueListCore.evalSelected
    (fieldModel.checkContext
      (rawPair 20 (.parsed (.enum "A")) 25 (.parsed (.enum "Other"))))
    (fun id => id == 20) = .fired .value := by native_decide

example : (elaborate fieldModel ["Order"] (.enumerationValueList .atLeastOne
    [(.direct (fieldPath "Code")), categoryCode] ["A", "Shared"])).isOk = true := by
  native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationValueList .atLeastOne [] ["A"])) =
    some .emptyValueListFields := by native_decide

example : errorOf (elaborate fieldModel ["Order"] (.enumerationValueList .atLeastOne
    [(.direct (fieldPath "Code")), (.direct (fieldPath "Code"))] ["A"])) =
    some (.duplicateValueListField ["Order", "Code"] .stored) := by native_decide

example : errorOf (elaborate fieldModel ["Order"] (.enumerationValueList .atLeastOne
    [(.direct (fieldPath "Code")), (.direct (fieldPath "CategoryPeer"))] ["Missing"])) =
    some (.enumerationOperand ["Order", "Code"] (.invalidLiteral "Missing")) := by
  native_decide

private def enumerationFieldValueList : SurfaceCondition :=
  .enumerationFieldValueList .atLeastOne
    [categoryCode] [(.direct (fieldPath "CategoryPeer"))]

private def enumerationFieldValueListCore : FlatCondition :=
  .tokenValueList .atLeastOne
    [.enumeration {
      field := { id := 20 },
      projectionRef := .category "Kind",
      projection := .category categoryMapping }]
    (.fields [
      .enumeration {
        field := { id := 25 }, projectionRef := .stored, projection := .stored }])

example : coreOf (elaborate fieldModel ["Order"] enumerationFieldValueList) =
    some enumerationFieldValueListCore := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "A")) 25 (.parsed (.enum "Shared"))) true
    enumerationFieldValueList) = some (.fired .value) := by native_decide

private def fieldValued (quantifier : ValueListQuantifier) : SurfaceCondition :=
  .enumerationFieldValueList quantifier
    [(.direct (fieldPath "Code"))] [(.direct (fieldPath "CategoryPeer"))]

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "A")) 25 .empty) true
    (fieldValued .atLeastOne)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (rawPair 20 (.parsed (.enum "A")) 25 .empty) true
      (fieldValued .no)) = some (.fired .omission) ∧
    verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
      (rawPair 20 (.parsed (.enum "A")) 25 .empty) true
      (fieldValued .notAll)) = some (.fired .omission) := by native_decide

example : verdictOf (elaborateAndEvalFull fieldModel world ["Order"]
    (rawPair 20 (.parsed (.enum "A")) 25 (.rejected .malformed)) true
    (fieldValued .no)) = some .unknown := by native_decide

example : enumerationFieldValueListCore.evalSelected
    (fieldModel.checkContext
      (rawPair 20 (.parsed (.enum "A")) 25 (.parsed (.enum "Shared"))))
    (fun id => id == 20) = .notFired := by native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationFieldValueList .atLeastOne
      [(.direct (fieldPath "Code"))] [])) =
    some .emptyValueListValueFields := by native_decide

example : errorOf (elaborate fieldModel ["Order"]
    (.enumerationFieldValueList .atLeastOne
      [(.direct (fieldPath "Code"))] [(.direct (fieldPath "Code"))])) =
    some (.duplicateValueListField ["Order", "Code"] .stored) := by native_decide

example : (elaborate fieldModel ["Order"]
    (.enumerationFieldValueList .atLeastOne
      [(.direct (fieldPath "Code"))] [categoryCode])).isOk = true := by native_decide

end A12Kernel.Conformance.FlatEnumeration
