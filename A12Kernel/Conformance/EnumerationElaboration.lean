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

example : isAccepted {
    storedTokens := ["A", "B"]
    defaultStoredToken := some "B"
  } := by
  native_decide

example : rejectsWith {
    storedTokens := ["A", "B"]
    defaultStoredToken := some "C"
  } (.unknownDefaultStoredToken "C") := by
  native_decide

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

/-- **The arity mismatch surfaces two codes, and the direction picks which.** A shortfall and a
surplus are one local error because the payload separates them, so the pair is asserted rather than
left to a reader to infer from the constructor's name — which names neither direction. The surplus
row is the one an account keyed on "a category is missing a value" gets wrong. -/
example :
    (declaration ["A", "B"] [] [category "Kind" ["X"]]).validate.toOption.isNone ∧
    (EnumerationDeclarationError.categoryArityMismatch "Kind" 2 1).kernelCode? =
      some "MVK_MISSING_CATEGORY_VALUE" ∧
    (EnumerationDeclarationError.categoryArityMismatch "Kind" 2 3).kernelCode? =
      some "MVK_MISSING_INTERNAL_VALUE" ∧
    (EnumerationDeclarationError.emptyStoredDomain).kernelCode? = none := by
  native_decide

/-- An empty category token list is a shortfall rather than a class of its own, so it draws the same
code as any other short list. The Kernel reports it once per unclassified value where this validator
reports once; [`Enumeration.lean`](../Elaboration/Enumeration.lean) owns why the multiplicity is not
representable here, and this row locks the class it does decide. -/
example : rejectsWith (declaration ["A", "B"] [] [category "Kind" []])
      (.categoryArityMismatch "Kind" 2 0) ∧
    (EnumerationDeclarationError.categoryArityMismatch "Kind" 2 0).kernelCode? =
      some "MVK_MISSING_CATEGORY_VALUE" := by native_decide

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
