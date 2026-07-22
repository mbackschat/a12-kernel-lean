import A12Kernel.Elaboration.Enumeration

/-! # A12Kernel.Conformance.EnumerationElaboration — ordinary closed declaration locks -/

namespace A12Kernel.Conformance.EnumerationElaboration

open A12Kernel

private def display (locale stored text : String) : EnumerationDisplayFact :=
  { locale, stored, display := text }

private def category (name : String) (tokens : List String) : EnumerationCategoryDeclaration :=
  { name, tokens }

private def declaration (storedTokens : List String)
    (displayFacts : List EnumerationDisplayFact := [])
    (categories : List EnumerationCategoryDeclaration := []) : EnumerationDeclaration :=
  { storedTokens, displayFacts, categories }

private def rejectsWith (source : EnumerationDeclaration)
    (expected : EnumerationDeclarationError) : Bool :=
  match source.validate with
  | .error actual => actual == expected
  | .ok () => false

private def isAccepted (source : EnumerationDeclaration) : Bool :=
  match source.validate with
  | .ok () => true
  | .error _ => false

example : rejectsWith (declaration []) .emptyStoredDomain := by native_decide

example : rejectsWith (declaration [""]) (.emptyStoredToken 0) := by native_decide

example : rejectsWith (declaration ["A", "A"]) (.duplicateStoredToken "A") := by native_decide

example : rejectsWith (declaration ["A"] [display "en" "B" "Bee"])
    (.unknownDisplayStoredToken "en" "B") := by native_decide

example : rejectsWith (declaration ["A", "B"] [display "en" "A" "Ay"])
    (.incompleteDisplayLocale "en" "B") := by native_decide

example : rejectsWith (declaration ["A", "B"]
    [display "en" "A" "Same", display "en" "B" "Same"])
    (.duplicateDisplayText "en" "Same") := by native_decide

example : rejectsWith (declaration ["A"]
    [display "en" "A" "Ay", display "en" "A" "Again"])
    (.duplicateDisplayStoredToken "en" "A") := by native_decide

example : rejectsWith (declaration ["A", "B"] []
    [category "" ["X", "Y"]]) (.emptyCategoryName 0) := by native_decide

example : rejectsWith (declaration ["A", "B"] []
    [category "Kind" ["X", "Y"], category "Kind" ["P", "Q"]])
    (.duplicateCategoryName "Kind") := by native_decide

example : rejectsWith (declaration ["A", "B"] []
    [category "Kind" ["X"]]) (.categoryArityMismatch "Kind" 2 1) := by native_decide

example : rejectsWith (declaration ["A", "B"] []
    [category "Kind" ["X", ""]]) (.emptyCategoryToken "Kind" 1) := by native_decide

private def complete : EnumerationDeclaration :=
  declaration ["A", "B"]
    [display "en" "A" "Ay", display "en" "B" "Bee",
      display "de" "A" "Ah", display "de" "B" "Bee"]
    [category "Kind" ["Shared", "Shared"]]

example : isAccepted complete := by native_decide

private def checkedComplete : CheckedEnumerationDeclaration :=
  { declaration := complete, wellFormed := by rfl }

example : checkedComplete.displayProfile.hasEffectiveDisplay := by native_decide

private def identityLabels : EnumerationDeclaration :=
  declaration ["A", "B"]
    [display "en" "A" "A", display "en" "B" "B"]

private def checkedIdentityLabels : CheckedEnumerationDeclaration :=
  { declaration := identityLabels, wellFormed := by rfl }

example : !checkedIdentityLabels.displayProfile.hasEffectiveDisplay := by native_decide

example : checkedComplete.storedProjection.tokenFor? "B" = some "B" := by native_decide

example : checkedComplete.categoryTokenFor? "Kind" "B" = some "Shared" := by native_decide

example : (checkedComplete.categoryProjection? "kind").isNone := by native_decide

end A12Kernel.Conformance.EnumerationElaboration
