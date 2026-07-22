import A12Kernel.Elaboration.Flat

/-! # A12Kernel.Conformance.FlatStringValueList — checked nonrepeatable String list locks -/

namespace A12Kernel.Conformance.FlatStringValueList

open A12Kernel

private def textDecl : FlatFieldDecl :=
  { id := 10, groupPath := ["Order"], name := "Text", policy := { kind := .string } }

private def peerDecl : FlatFieldDecl :=
  { id := 11, groupPath := ["Order"], name := "Peer", policy := { kind := .string } }

private def enumDecl : FlatFieldDecl :=
  { id := 20
    groupPath := ["Order"]
    name := "Code"
    policy := { kind := .enumeration }
    enumeration := some { storedTokens := ["A", "B"] } }

private def model : FlatModel := { fields := [textDecl, peerDecl, enumDecl] }

private def path (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def rawPair (leftId : FieldId) (left : RawCell)
    (rightId : FieldId) (right : RawCell) : RawFlatContext where
  read id := if id == leftId then left else if id == rightId then right else .empty

private def world : World := { now := { epochMillis := 0 } }

private def coreOf {model : FlatModel}
    (result : Except ElabError (CheckedFlatCondition model)) : Option FlatCondition :=
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

private def literalList : SurfaceCondition :=
  .stringValueList .atLeastOne [path "Text", path "Peer"] ["AB\nCD", "Other"]

private def literalListCore : FlatCondition :=
  .tokenValueList .atLeastOne [.string { id := 10 }, .string { id := 11 }]
    (.literals ["AB\nCD", "Other"])

example : coreOf (elaborate model ["Order"] literalList) = some literalListCore := by
  native_decide

/- The field side consumes the checked one-pass CRLF-normalized value. -/
example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "Miss")) 11 (.parsed (.str "AB\r\nCD"))) true
    literalList) = some (.fired .value) := by native_decide

private def fieldList (quantifier : ValueListQuantifier) : SurfaceCondition :=
  .stringFieldValueList quantifier [path "Text"] [path "Peer"]

private def fieldListCore : FlatCondition :=
  .tokenValueList .atLeastOne [.string { id := 10 }]
    (.fields [.string { id := 11 }])

example : coreOf (elaborate model ["Order"] (fieldList .atLeastOne)) =
    some fieldListCore := by native_decide

/- Both field-valued sides consume the same normalized evaluation cache. -/
example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "AB\r\nCD")) 11 (.parsed (.str "AB\nCD"))) true
    (fieldList .atLeastOne)) = some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "A")) 11 (.parsed (.str ""))) true
    (fieldList .atLeastOne)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "A")) 11 (.parsed (.str ""))) true
      (fieldList .no)) = some (.fired .omission) ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "A")) 11 (.parsed (.str ""))) true
      (fieldList .notAll)) = some (.fired .omission) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "A")) 11 (.rejected .malformed)) true
    (fieldList .atLeastOne)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "A")) 11 (.rejected .malformed)) true
      (fieldList .no)) = some .unknown ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "A")) 11 (.rejected .malformed)) true
      (fieldList .notAll)) = some .unknown := by native_decide

/- Partial relevance removes masked cells before reads: a masked member is skipped, while a relevant matching subject still survives a masked subject sibling. -/
example : fieldListCore.evalSelected
      (model.checkContext
        (rawPair 10 (.parsed (.str "A")) 11 (.parsed (.str "A"))))
      (fun id => id == 10) = .notFired ∧
    literalListCore.evalSelected
      (model.checkContext
        (rawPair 10 (.parsed (.str "AB\r\nCD")) 11 (.rejected .malformed)))
      (fun id => id == 10) = .fired .value := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (.stringValueList .atLeastOne [] ["A"])) =
    some .emptyValueListFields := by native_decide

example : errorOf (elaborate model ["Order"]
    (.stringFieldValueList .atLeastOne [path "Text"] [])) =
    some .emptyValueListValueFields := by native_decide

example : errorOf (elaborate model ["Order"]
    (.stringFieldValueList .atLeastOne [path "Text"] [path "Text"])) =
    some (.duplicateStringValueListField ["Order", "Text"]) := by native_decide

example : errorOf (elaborate model ["Order"]
    (.stringValueList .atLeastOne [path "Code"] ["A"])) =
    some (.textFieldOperandKindMismatch ["Order", "Code"] .enumeration) := by
  native_decide

private def mixedCore : FlatCondition :=
  .tokenValueList .atLeastOne [.string { id := 10 }]
    (.fields [.enumeration {
      field := { id := 20 }, projectionRef := .stored, projection := .stored }])

example : mixedCore.wellFormedBool model = false := by native_decide

private def membership (op : ValueListMembershipOp) : SurfaceCondition :=
  .stringValueMembership op (path "Text") ["AB\nCD", "Other"]

example : coreOf (elaborate model ["Order"] (membership .included)) =
    some (.tokenValueList .atLeastOne [.string { id := 10 }]
      (.literals ["AB\nCD", "Other"])) ∧
    coreOf (elaborate model ["Order"] (membership .notIncluded)) =
      some (.tokenValueList .notAll [.string { id := 10 }]
        (.literals ["AB\nCD", "Other"])) := by
  native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "AB\r\nCD")) 11 .empty) true
    (membership .included)) = some (.fired .value) ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "Miss")) 11 .empty) true
      (membership .notIncluded)) = some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "")) 11 .empty) true
    (membership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "")) 11 .empty) true
      (membership .notIncluded)) = some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.rejected .malformed) 11 .empty) true
    (membership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.rejected .malformed) 11 .empty) true
      (membership .notIncluded)) = some .notFired := by native_decide

example : errorOf (elaborate model ["Order"]
    (.stringValueMembership .included (path "Text") [])) =
    some (.emptyValueList ["Order", "Text"]) := by native_decide

example : errorOf (elaborate model ["Order"]
    (.stringValueMembership .included (path "Code") ["A"])) =
    some (.textFieldOperandKindMismatch ["Order", "Code"] .enumeration) := by
  native_decide

private def fieldMembership (op : ValueListMembershipOp) : SurfaceCondition :=
  .stringFieldValueMembership op (path "Text") [path "Peer"]

example : coreOf (elaborate model ["Order"] (fieldMembership .included)) =
    some (.tokenValueList .atLeastOne [.string { id := 10 }]
      (.fields [.string { id := 11 }])) ∧
    coreOf (elaborate model ["Order"] (fieldMembership .notIncluded)) =
      some (.tokenValueList .notAll [.string { id := 10 }]
        (.fields [.string { id := 11 }])) := by
  native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "AB\r\nCD")) 11 (.parsed (.str "AB\nCD"))) true
    (fieldMembership .included)) = some (.fired .value) ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "Miss")) 11 (.parsed (.str "Other"))) true
      (fieldMembership .notIncluded)) = some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "A")) 11 .empty) true
    (fieldMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "A")) 11 .empty) true
      (fieldMembership .notIncluded)) = some (.fired .omission) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 10 (.parsed (.str "A")) 11 (.rejected .malformed)) true
    (fieldMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 10 (.parsed (.str "A")) 11 (.rejected .malformed)) true
      (fieldMembership .notIncluded)) = some .unknown := by native_decide

example : errorOf (elaborate model ["Order"]
    (.stringFieldValueMembership .included (path "Text") [])) =
    some .emptyValueListValueFields := by native_decide

example : errorOf (elaborate model ["Order"]
    (.stringFieldValueMembership .included (path "Text") [path "Text"])) =
    some (.duplicateStringValueListField ["Order", "Text"]) := by native_decide

end A12Kernel.Conformance.FlatStringValueList
