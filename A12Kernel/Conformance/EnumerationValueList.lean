import A12Kernel.Semantics.EnumerationValueList

/-! # A12Kernel.Conformance.EnumerationValueList — checked token-side locks -/

namespace A12Kernel.Conformance.EnumerationValueList

open A12Kernel

private def source : EnumerationDeclaration :=
  { storedTokens := ["A", "B"]
    categories := [{ name := "Kind", tokens := ["Shared", "Shared"] }] }

private def checked : CheckedEnumerationDeclaration :=
  { declaration := source, wellFormed := by rfl }

private def categoryMapping : ResolvedEnumerationCategory :=
  { storedTokens := ["A", "B"], categoryTokens := ["Shared", "Shared"] }

private def storedOperand : CheckedEnumerationValueListOperand :=
  { declaration := checked
    projectionRef := .stored
    projection := .stored
    projectionChecked := by rfl }

private def categoryOperand : CheckedEnumerationValueListOperand :=
  { declaration := checked
    projectionRef := .category "Kind"
    projection := .category categoryMapping
    projectionChecked := by rfl }

private def tokenCellEquals (left right : ValueListCell .token) : Bool :=
  match left, right with
  | .present leftToken, .present rightToken => leftToken == rightToken
  | .empty, .empty => true
  | .unknown leftCause, .unknown rightCause => leftCause == rightCause
  | _, _ => false

example : tokenCellEquals (storedOperand.classifyRaw (.parsed (.enum "A")))
    (.present "A") := by native_decide

example : tokenCellEquals (categoryOperand.classifyRaw (.parsed (.enum "B")))
    (.present "Shared") := by native_decide

example : tokenCellEquals (storedOperand.classifyRaw .empty) .empty := by native_decide

example : tokenCellEquals (categoryOperand.classifyRaw .empty) .empty := by native_decide

example : tokenCellEquals (storedOperand.classifyRaw (.parsed (.enum ""))) .empty := by native_decide

example : tokenCellEquals (storedOperand.classifyRaw (.parsed (.enum "C")))
    (.unknown .declaredConstraint) := by native_decide

example : tokenCellEquals (storedOperand.classifyRaw (.rejected .unsupportedCharacter))
    (.unknown .unsupportedCharacter) := by native_decide

private def literalSide (tokens : List String) : ResolvedValueListSide .token :=
  { cells := tokens.map .present, hasUninstantiatedTail := false, hasHaving := false }

private def rawSide (operand : CheckedEnumerationValueListOperand)
    (raw : List RawCell) : ResolvedValueListSide .token :=
  operand.classifyRawSide raw false false

example : evalValueListAtLeastOne (rawSide categoryOperand [.parsed (.enum "B")])
    (literalSide ["Shared"]) = .fired .value := by native_decide

example : evalValueListNo (rawSide storedOperand [.parsed (.enum "A")])
    (literalSide ["B"]) = .fired .value := by native_decide

example : evalValueListNotAll (rawSide storedOperand [.parsed (.enum "A")])
    (literalSide ["B"]) = .fired .value := by native_decide

private def invalidMember : ResolvedValueListSide .token :=
  rawSide storedOperand [.parsed (.enum "C")]

example : evalValueListAtLeastOne (rawSide storedOperand [.parsed (.enum "A")])
    invalidMember = .notFired := by native_decide

example : evalValueListNo (rawSide storedOperand [.parsed (.enum "A")])
    invalidMember = .unknown := by native_decide

example : evalValueListNotAll (rawSide storedOperand [.parsed (.enum "A")])
    invalidMember = .unknown := by native_decide

end A12Kernel.Conformance.EnumerationValueList
