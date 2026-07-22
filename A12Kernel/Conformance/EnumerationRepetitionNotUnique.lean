import A12Kernel.Semantics.EnumerationRepetitionNotUnique

/-! # A12Kernel.Conformance.EnumerationRepetitionNotUnique — checked key locks -/

namespace A12Kernel.Conformance.EnumerationRepetitionNotUnique

open A12Kernel

private def source : EnumerationDeclaration :=
  { storedTokens := ["A", "B"]
    categories := [{ name := "Kind", tokens := ["Shared", "Shared"] }] }

private def checked : CheckedEnumerationDeclaration :=
  { declaration := source, wellFormed := by rfl }

private def categoryMapping : ResolvedEnumerationCategory :=
  { storedTokens := ["A", "B"], categoryTokens := ["Shared", "Shared"] }

private def storedOperand : CheckedEnumerationProjection :=
  { declaration := checked
    projectionRef := .stored
    projection := .stored
    projectionChecked := by rfl }

private def categoryOperand : CheckedEnumerationProjection :=
  { declaration := checked
    projectionRef := .category "Kind"
    projection := .category categoryMapping
    projectionChecked := by rfl }

example : storedOperand.classifyRawKey (.parsed (.enum "A")) =
    .present (.token "A") := by native_decide

example : categoryOperand.classifyRawKey (.parsed (.enum "B")) =
    .present (.token "Shared") := by native_decide

example : storedOperand.classifyRawKey .empty = .empty := by native_decide

example : storedOperand.classifyRawKey (.parsed (.enum "C")) =
    .unknown .declaredConstraint := by native_decide

example : storedOperand.classifyRawKey (.rejected .unsupportedCharacter) =
    .unknown .unsupportedCharacter := by native_decide

private def row (index : Nat) (key : List RepetitionKeyComponent) :
    ResolvedRepetitionKeyRow :=
  { row := [(1, index)], key }

private def categoryRows : List ResolvedRepetitionKeyRow :=
  [row 1 [categoryOperand.classifyRawKey (.parsed (.enum "A"))],
    row 2 [categoryOperand.classifyRawKey (.parsed (.enum "B"))]]

example : (evalRepetitionNotUnique categoryRows).map (·.verdict) =
    [.fired .value, .fired .value] := by native_decide

example : (evalRepetitionNotUnique categoryRows).map (·.cluster) =
    [[[(1, 1)], [(1, 2)]], [[(1, 1)], [(1, 2)]]] := by native_decide

private def omissionRows : List ResolvedRepetitionKeyRow :=
  [row 1 [categoryOperand.classifyRawKey (.parsed (.enum "A")), .empty],
    row 2 [categoryOperand.classifyRawKey (.parsed (.enum "B")), .empty]]

example : (evalRepetitionNotUnique omissionRows).map (·.verdict) =
    [.fired .omission, .fired .omission] := by native_decide

private def rowsWithInvalid : List ResolvedRepetitionKeyRow :=
  categoryRows ++ [row 3 [storedOperand.classifyRawKey (.parsed (.enum "C"))]]

example : (evalRepetitionNotUnique rowsWithInvalid).map (·.verdict) =
    [.fired .value, .fired .value, .unknown] := by native_decide

example : (evalRepetitionNotUnique
    [row 1 [storedOperand.classifyRawKey (.parsed (.enum "A"))],
      row 2 [storedOperand.classifyRawKey (.parsed (.enum "B"))]]).map (·.verdict) =
    [.notFired, .notFired] := by native_decide

end A12Kernel.Conformance.EnumerationRepetitionNotUnique
