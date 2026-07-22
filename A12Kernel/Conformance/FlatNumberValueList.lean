import A12Kernel.Elaboration.Flat

/-! # A12Kernel.Conformance.FlatNumberValueList — checked nonrepeatable Number list locks -/

namespace A12Kernel.Conformance.FlatNumberValueList

open A12Kernel

private def countInfo : NumField := { signed := true, scale := 2 }
private def peerInfo : NumField := { signed := false, scale := 0 }
private def otherInfo : NumField := { signed := true, scale := 4 }

private def countDecl : FlatFieldDecl :=
  { id := 1, groupPath := ["Order"], name := "Count", policy := { kind := .number countInfo } }

private def peerDecl : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "Peer", policy := { kind := .number peerInfo } }

private def otherDecl : FlatFieldDecl :=
  { id := 3, groupPath := ["Order"], name := "Other", policy := { kind := .number otherInfo } }

private def textDecl : FlatFieldDecl :=
  { id := 10, groupPath := ["Order"], name := "Text", policy := { kind := .string } }

private def model : FlatModel := { fields := [countDecl, peerDecl, otherDecl, textDecl] }

private def path (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def rawPair (leftId : FieldId) (left : RawCell)
    (rightId : FieldId) (right : RawCell) : RawFlatContext where
  read id := if id == leftId then left else if id == rightId then right else .empty

private def rawTriple (firstId : FieldId) (first : RawCell)
    (secondId : FieldId) (second : RawCell)
    (thirdId : FieldId) (third : RawCell) : RawFlatContext where
  read id :=
    if id == firstId then first
    else if id == secondId then second
    else if id == thirdId then third
    else .empty

private def numberRaw (amount : Rat) : RawCell :=
  .parsed (.num amount)

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

private def literalMembership (op : ValueListMembershipOp) : SurfaceCondition :=
  .numberValueMembership op (path "Count") [5, -2]

private def countOperand : FlatNumberField := { id := 1, info := countInfo }
private def peerOperand : FlatNumberField := { id := 2, info := peerInfo }
private def otherOperand : FlatNumberField := { id := 3, info := otherInfo }

example : coreOf (elaborate model ["Order"] (literalMembership .included)) =
    some (.numberValueList .atLeastOne [countOperand] (.literals [5, -2])) ∧
    coreOf (elaborate model ["Order"] (literalMembership .notIncluded)) =
      some (.numberValueList .notAll [countOperand] (.literals [5, -2])) := by
  native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 1 (numberRaw 5) 2 .empty) true
    (literalMembership .included)) = some (.fired .value) ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 1 (numberRaw 7) 2 .empty) true
      (literalMembership .notIncluded)) = some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 1 .empty 2 .empty) true (literalMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 1 .empty 2 .empty) true (literalMembership .notIncluded)) =
        some .notFired := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 1 (.rejected .malformed) 2 .empty) true
    (literalMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 1 (.rejected .malformed) 2 .empty) true
      (literalMembership .notIncluded)) = some .notFired := by native_decide

example : errorOf (elaborate model ["Order"]
    (.numberValueMembership .included (path "Count") [])) =
    some (.emptyValueList ["Order", "Count"]) := by native_decide

example : errorOf (elaborate model ["Order"]
    (.numberValueMembership .included (path "Text") [5])) =
    some (.literalKindMismatch ["Order", "Text"] .number .string) := by native_decide

private def fieldMembership (op : ValueListMembershipOp) : SurfaceCondition :=
  .numberFieldValueMembership op (path "Count") [path "Peer"]

example : coreOf (elaborate model ["Order"] (fieldMembership .included)) =
    some (.numberValueList .atLeastOne [countOperand] (.fields [peerOperand])) ∧
    coreOf (elaborate model ["Order"] (fieldMembership .notIncluded)) =
      some (.numberValueList .notAll [countOperand] (.fields [peerOperand])) := by
  native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 1 (numberRaw (1 / 3)) 2 (numberRaw (1 / 3))) true
    (fieldMembership .included)) = some (.fired .value) ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 1 (numberRaw 5) 2 (numberRaw 7)) true
      (fieldMembership .notIncluded)) = some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawPair 1 (numberRaw 0) 2 .empty) true
    (fieldMembership .included)) = some .notFired ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawPair 1 (numberRaw 0) 2 .empty) true
      (fieldMembership .notIncluded)) = some (.fired .omission) := by native_decide

example : errorOf (elaborate model ["Order"]
    (.numberFieldValueMembership .included (path "Count") [])) =
    some .emptyValueListValueFields := by native_decide

example : errorOf (elaborate model ["Order"]
    (.numberFieldValueMembership .included (path "Count") [path "Count"])) =
    some (.duplicateNumberValueListField ["Order", "Count"]) := by native_decide

private def fieldList (quantifier : ValueListQuantifier) : SurfaceCondition :=
  .numberFieldValueList quantifier [path "Count", path "Peer"] [path "Other"]

private def fieldListCore (quantifier : ValueListQuantifier) : FlatCondition :=
  .numberValueList quantifier [countOperand, peerOperand] (.fields [otherOperand])

example : coreOf (elaborate model ["Order"] (fieldList .atLeastOne)) =
    some (fieldListCore .atLeastOne) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawTriple 1 (numberRaw 7) 2 (numberRaw 9)
      3 (numberRaw 9)) true
    (fieldList .atLeastOne)) = some (.fired .value) := by native_decide

example : verdictOf (elaborateAndEvalFull model world ["Order"]
    (rawTriple 1 .empty 2 .empty 3 .empty) false
    (fieldList .no)) = some (.fired .omission) ∧
    verdictOf (elaborateAndEvalFull model world ["Order"]
      (rawTriple 1 (numberRaw 7) 2 .empty 3 (numberRaw 9)) true
      (fieldList .notAll)) = some (.fired .value) := by native_decide

/- Partial validation classifies nonrelevance per cell before applying the ordinary asymmetric quantifier. A nonrelevant values member is skipped by `AtLeastOne`, rather than suppressing the whole leaf. -/
example : (fieldListCore .atLeastOne).evalSelected
    (model.checkContext
      (rawTriple 1 (numberRaw 7) 2 (numberRaw 9)
        3 (numberRaw 9)))
    (fun id => id != 3) = .notFired := by native_decide

/- A relevant witness survives a nonrelevant fields sibling for the existential operators, while `No` retains its UNKNOWN poison. -/
example :
    (fieldListCore .atLeastOne).evalSelected
        (model.checkContext
          (rawTriple 1 (numberRaw 7) 2 (numberRaw 9)
            3 (numberRaw 7)))
        (fun id => id != 2) = .fired .value ∧
      (fieldListCore .notAll).evalSelected
        (model.checkContext
          (rawTriple 1 (numberRaw 7) 2 (numberRaw 9)
            3 (numberRaw 5)))
        (fun id => id != 2) = .fired .value ∧
      (fieldListCore .no).evalSelected
        (model.checkContext
          (rawTriple 1 (numberRaw 7) 2 (numberRaw 9)
            3 (numberRaw 5)))
        (fun id => id != 2) = .unknown := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (.numberFieldValueList .atLeastOne [] [path "Other"])) =
    some .emptyValueListFields := by native_decide

example : errorOf (elaborate model ["Order"]
    (.numberFieldValueList .atLeastOne [path "Count"] [])) =
    some .emptyValueListValueFields := by native_decide

example : errorOf (elaborate model ["Order"]
    (.numberFieldValueList .atLeastOne [path "Count"] [path "Count"])) =
    some (.duplicateNumberValueListField ["Order", "Count"]) := by native_decide

example : errorOf (elaborate model ["Order"]
    (.numberFieldValueList .atLeastOne [path "Count"] [path "Text"])) =
    some (.literalKindMismatch ["Order", "Text"] .number .string) := by native_decide

private def incoherentCore : FlatCondition :=
  .numberValueList .atLeastOne [{ countOperand with info := peerInfo }]
    (.literals [5])

example : incoherentCore.wellFormedBool model = false := by native_decide

example : (FlatCondition.numberValueList .atLeastOne
    [countOperand, peerOperand] (.literals [5])).wellFormedBool model = false := by
  native_decide

example : (FlatCondition.numberValueList .atLeastOne
    [countOperand] (.literals [1 / 2])).wellFormedBool model = false := by
  native_decide

end A12Kernel.Conformance.FlatNumberValueList
