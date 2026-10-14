import A12Kernel.Semantics.CheckedEnumeration

/-! # A12Kernel.Conformance.CheckedEnumeration — checked observation and literal locks -/

namespace A12Kernel.Conformance.CheckedEnumeration

open A12Kernel

private def source : EnumerationDeclaration :=
  { storedTokens := ["A", "B"]
    categories := [{ name := "Kind", tokens := ["Shared", "Shared"] }] }

private def checked : CheckedEnumerationDeclaration :=
  { declaration := source, wellFormed := by rfl }

private def categoryMapping : ResolvedEnumerationCategory :=
  { storedTokens := ["A", "B"], categoryTokens := ["Shared", "Shared"] }

private def storedEqualsA : CheckedEnumerationLiteralComparison :=
  { operand := {
      declaration := checked
      projectionRef := .stored
      projection := .stored
      projectionChecked := by rfl }
    op := .equal
    expected := "A"
    literalChecked := by rfl }

private def categoryEqualsShared : CheckedEnumerationLiteralComparison :=
  { operand := {
      declaration := checked
      projectionRef := .category "Kind"
      projection := .category categoryMapping
      projectionChecked := by rfl }
    op := .equal
    expected := "Shared"
    literalChecked := by rfl }

example : classifyEnumerationLiteral checked .stored .equal "A" =
    .accepted .stored := by native_decide

example : classifyEnumerationLiteral checked .stored .notEqual "A" =
    .accepted .stored := by native_decide

example : classifyEnumerationLiteral checked .stored .equal "C" =
    .rejected (.invalidLiteral "C") := by native_decide

example : classifyEnumerationLiteral checked (.category "kind") .equal "Shared" =
    .rejected (.unknownCategory "kind") := by native_decide

private def checkedExpected? (projectionRef : EnumerationProjectionRef)
    (op : EqualityOp) (literal : String) : Option String :=
  match checkEnumerationLiteralComparison checked projectionRef op literal with
  | .ok comparison => some comparison.expected
  | .error _ => none

example : checkedExpected? (.category "Kind") .notEqual "Shared" =
    some "Shared" := by native_decide

example : storedEqualsA.evalRaw (.parsed (.enum "A")) = .fired .value := by native_decide

private def emptyTokenChecked : CheckedEnumerationDeclaration :=
  { declaration := { storedTokens := ["", "B"] }, wellFormed := by rfl }

private def storedDiffersFromEmpty : Option CheckedEnumerationLiteralComparison :=
  (checkEnumerationLiteralComparison emptyTokenChecked .stored .notEqual "").toOption

/-- A declared empty token is an admitted literal, and `!= ""` stays silent on a filled `B` and on a
stored `""`, which is empty (empty-token capture `rNe0`, 2026-10-14). The direct-String account would
also stay silent; the separating wrong account is the plain token inequality, which fires on `B`. -/
example : storedDiffersFromEmpty.map (fun comparison =>
      (comparison.evalRaw (.parsed (.enum "B")), comparison.evalRaw (.parsed (.enum "")))) =
    some (.notFired, .notFired) := by native_decide

example : storedEqualsA.evalRaw (.parsed (.enum "B")) = .notFired := by native_decide

example : categoryEqualsShared.evalRaw (.parsed (.enum "A")) = .fired .value := by native_decide

example : categoryEqualsShared.evalRaw (.parsed (.enum "B")) = .fired .value := by native_decide

example : storedEqualsA.evalRaw .empty = .notFired := by native_decide

example : storedEqualsA.evalRaw (.parsed (.enum "")) = .notFired := by native_decide

example : storedEqualsA.evalRaw (.parsed (.enum "C")) = .unknown := by native_decide

example : storedEqualsA.evalRaw (.parsed (.str "A")) = .unknown := by native_decide

example : storedEqualsA.evalRaw (.rejected .unsupportedCharacter) = .unknown := by native_decide

end A12Kernel.Conformance.CheckedEnumeration
