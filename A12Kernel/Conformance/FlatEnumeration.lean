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

private def coreOf (result : Except ElabError (CheckedFlatCondition model)) :
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

end A12Kernel.Conformance.FlatEnumeration
