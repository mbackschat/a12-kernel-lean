import A12Kernel.Elaboration.Enumeration
import A12Kernel.Elaboration.EnumerationDeclarationNotification

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

example : isAccepted (declaration ["", "B"]) := by native_decide

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

/- The S-value law reads both sides after Java's `trim` and asks nothing of a blank default, while a
no-break space is no trimmed character and a case difference names nothing (spec/01 §1.3). -/
example : [" B", "B\t", " ", "\t"].all (fun token => isAccepted { storedTokens := ["A", "B"], defaultStoredToken := some token }) ∧
    isAccepted { storedTokens := [" B"], defaultStoredToken := some "B" } ∧
    rejectsWith { storedTokens := ["A", "B"], defaultStoredToken := some "b" } (.unknownDefaultStoredToken "b") ∧
    rejectsWith { storedTokens := ["A", "B"], defaultStoredToken := some "\u00A0B" }
      (.unknownDefaultStoredToken "\u00A0B") := by
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
surplus are one local validator error because the payload separates them, but the Kernel reports a
notification per element: the unclassified stored values on the shortfall side and the surplus
category tokens on the other. The surplus row is the one an account keyed on "a category is missing a
value" gets wrong. -/
example :
    (declaration ["A", "B"] [] [category "Kind" ["X"]]).validate.toOption.isNone ∧
    (declaration ["A", "B"] [] [category "Kind" ["X"]]).notifications .defaultBmp =
      [.missingCategoryValue "Kind" "B"] ∧
    (declaration ["A", "B"] [] [category "Kind" ["X", "Y", "Z", "W"]]).notifications .defaultBmp =
      [.missingInternalValue "Kind" "Z", .missingInternalValue "Kind" "W"] ∧
    (EnumerationDeclarationNotification.missingCategoryValue "Kind" "B").kernelCode? =
      some "MVK_MISSING_CATEGORY_VALUE" ∧
    (EnumerationDeclarationNotification.missingInternalValue "Kind" "Z").kernelCode? =
      some "MVK_MISSING_INTERNAL_VALUE" := by
  native_decide

/-- An empty category token list is a shortfall rather than a class of its own, so it draws the
shortfall code once per stored value, which the first-refusal validator cannot express. -/
example : rejectsWith (declaration ["A", "B"] [] [category "Kind" []])
      (.categoryArityMismatch "Kind" 2 0) ∧
    (declaration ["A", "B"] [] [category "Kind" []]).notifications .defaultBmp =
      [.missingCategoryValue "Kind" "A", .missingCategoryValue "Kind" "B"] := by
  native_decide

/-- The two classes the Kernel raises without a code carry no code here either, and an empty stored
domain raises nothing because the Kernel never builds such a model. -/
example :
    EnumerationDeclarationNotification.supplementaryCharacter.kernelCode? = none ∧
    (EnumerationDeclarationNotification.repeatedValue "A").kernelCode? = none ∧
    (declaration [] [] [category "Kind" ["X"]]).notifications .defaultBmp = [] := by
  native_decide

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
