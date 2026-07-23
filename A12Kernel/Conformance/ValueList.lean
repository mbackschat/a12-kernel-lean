import A12Kernel.Semantics.ValueList

/-! # Resolved value-list quantifier separating cases

These examples start after field/value expansion and `Having` filtering. They cover the operation-specific Number/canonical-token runtime from `spec/06-strings-and-enumerations.md` §B.3; checked path lowering, comparability, and repeatable expansion remain outside this capsule.
-/

namespace A12Kernel.Conformance.ValueList

open A12Kernel

private def tokenSide (cells : List (ValueListCell .token))
    (hasUninstantiatedTail := false) (hasHaving := false) :
    ResolvedValueListSide .token := {
  cells
  hasUninstantiatedTail
  hasHaving }

private def fieldsWithUnknown : ResolvedValueListSide .token :=
  tokenSide [.present "outside", .unknown .malformed]

private def knownMembers : ResolvedValueListSide .token :=
  tokenSide [.present "A"]

/- `No` and `NotAll` are not duals: an unknown field poisons only `No`. -/
example :
    ValueListQuantifier.no.eval fieldsWithUnknown knownMembers = .unknown ∧
      ValueListQuantifier.notAll.eval fieldsWithUnknown knownMembers =
        .fired .value := by
  native_decide

/- `AtLeastOne` skips empty and unknown cells on both sides. `Having` changes only a firing's polarity after filtering. -/
example :
    ValueListQuantifier.atLeastOne.eval
        (tokenSide [.present "A", .empty, .unknown .malformed])
        (tokenSide [.present "A", .empty, .unknown .declaredConstraint]) =
          .fired .value ∧
      ValueListQuantifier.atLeastOne.eval
        (tokenSide [.present "A"])
        (tokenSide [.empty, .unknown .malformed]) = .notFired ∧
      ValueListQuantifier.atLeastOne.eval
        (tokenSide [.present "A"] false true)
        (tokenSide [.present "A"]) = .fired .omission := by
  native_decide

/- `No` poison-checks the complete values side first, then scans fields until the first match or unavailable cell; its clean vacuous fire is omission-typed exactly when either side can still gain a value. -/
example :
    ValueListQuantifier.no.eval
        (tokenSide [.present "B"]) knownMembers = .fired .value ∧
      ValueListQuantifier.no.eval
        (tokenSide [.empty]) knownMembers = .fired .omission ∧
      ValueListQuantifier.no.eval
        (tokenSide [] true) knownMembers = .fired .omission ∧
      ValueListQuantifier.no.eval
        (tokenSide [.present "B"])
        (tokenSide [.present "A", .empty]) = .fired .omission ∧
      ValueListQuantifier.no.eval
        (tokenSide [.present "A"]) knownMembers = .notFired ∧
      ValueListQuantifier.no.eval
        (tokenSide [.present "A", .unknown .malformed]) knownMembers =
          .notFired := by
  native_decide

/- `NotAll` first requires one present field. Only then can an unknown member poison it; fields-side empty/unknown cells neither poison nor alter polarity. -/
example :
    ValueListQuantifier.notAll.eval
        (tokenSide [.present "B"]) knownMembers = .fired .value ∧
      ValueListQuantifier.notAll.eval
        (tokenSide [.present "A"]) knownMembers = .notFired ∧
      ValueListQuantifier.notAll.eval
        (tokenSide [.present "B", .empty, .unknown .malformed])
        knownMembers = .fired .value ∧
      ValueListQuantifier.notAll.eval
        (tokenSide [.present "B"])
        (tokenSide [.present "A", .empty]) = .fired .omission ∧
      ValueListQuantifier.notAll.eval
        (tokenSide [.present "B"])
        (tokenSide [.present "A", .unknown .malformed]) = .unknown ∧
      ValueListQuantifier.notAll.eval
        (tokenSide [.empty, .unknown .malformed])
        (tokenSide [.unknown .declaredConstraint]) = .notFired ∧
      ValueListQuantifier.notAll.eval
        (tokenSide [.present "B"]) (tokenSide [.present "A"] false true) =
          .fired .omission := by
  native_decide

private def numberSide (cells : List (ValueListCell .number))
    (hasUninstantiatedTail := false) (hasHaving := false) :
    ResolvedValueListSide .number := {
  cells
  hasUninstantiatedTail
  hasHaving }

private def belowHalfUlp : Rat := 49 / ((10 : Rat) ^ 21)

/- Numeric membership reuses scale-19 equality, while an empty numeric member is never substituted with zero. -/
example :
    ValueListQuantifier.atLeastOne.eval
        (numberSide [.present 0])
        (numberSide [.present belowHalfUlp]) = .fired .value ∧
      ValueListQuantifier.atLeastOne.eval
        (numberSide [.present 0]) (numberSide [.empty]) = .notFired ∧
      ValueListQuantifier.no.eval
        (numberSide [.present 0]) (numberSide [.empty]) = .fired .omission ∧
      ValueListQuantifier.notAll.eval
        (numberSide [.present 0]) (numberSide [.empty]) = .fired .omission := by
  native_decide

/- A pre-filtered empty side still carries `Having` for polarity, without inventing dropped cells. -/
example :
    ValueListQuantifier.atLeastOne.eval
        (tokenSide [] false true) knownMembers = .notFired ∧
      ValueListQuantifier.no.eval
        (tokenSide [] false true) knownMembers = .fired .omission ∧
      ValueListQuantifier.notAll.eval
        (tokenSide [] false true) knownMembers = .notFired := by
  native_decide

/- Ordered operand boundaries matter: fields-side `No` stops at its first match, values-side poison precedes fields, and `NotAll` skips values when its fields-presence prepass fails. -/
example :
    ValueListQuantifier.no.evalOrdered
        [tokenSide [.present "A"], tokenSide [.unknown .malformed]]
        [knownMembers] = .notFired ∧
      ValueListQuantifier.no.evalOrdered
        [tokenSide [.unknown .malformed], tokenSide [.present "A"]]
        [knownMembers] = .unknown ∧
      ValueListQuantifier.no.evalOrdered
        [tokenSide [.present "A"]]
        [tokenSide [.present "A", .unknown .malformed]] = .unknown ∧
      ValueListQuantifier.notAll.evalOrdered
        [tokenSide [.empty]]
        [tokenSide [.unknown .malformed]] = .notFired := by
  native_decide

/- Filter polarity is witness-sensitive on the fields side and selected-present-sensitive for `AtLeastOne` members; `No` keeps reached filter uncertainty sticky. -/
example :
    ValueListQuantifier.atLeastOne.evalOrdered
        [tokenSide [.present "B"] false true, tokenSide [.present "A"]]
        [knownMembers] = .fired .value ∧
      ValueListQuantifier.atLeastOne.evalOrdered
        [tokenSide [.present "A"] false true, tokenSide [.present "B"]]
        [knownMembers] = .fired .omission ∧
      ValueListQuantifier.atLeastOne.evalOrdered
        [tokenSide [.present "A"]]
        [tokenSide [.empty] false true, knownMembers] = .fired .value ∧
      ValueListQuantifier.atLeastOne.evalOrdered
        [tokenSide [.present "A"]]
        [tokenSide [.present "B"] false true, knownMembers] =
          .fired .omission ∧
      ValueListQuantifier.no.evalOrdered
        [tokenSide [.present "B"] false true, tokenSide [.present "C"]]
        [knownMembers] = .fired .omission ∧
      ValueListQuantifier.notAll.evalOrdered
        [tokenSide [.present "A"] false true, tokenSide [.present "B"]]
        [knownMembers] = .fired .value := by
  native_decide

example :
    ValueListQuantifier.atLeastOne.canFireOnEmpty = false ∧
      ValueListQuantifier.no.canFireOnEmpty = true ∧
      ValueListQuantifier.notAll.canFireOnEmpty = false := by
  decide

end A12Kernel.Conformance.ValueList
