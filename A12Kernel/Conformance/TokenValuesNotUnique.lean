import A12Kernel.Elaboration.TokenValuesNotUnique

/-! # `FieldValuesNotUnique` conformance locks over the String overload -/

namespace A12Kernel

private def tokens (cells : List (ValueListCell .token)) :
    List (ValueListCell .token × Bool) :=
  cells.map (·, false)

/- Canonical token identity is exact, so a duplicate must match byte for byte and case differences are two distinct values. -/
example :
    evalValuesNotUniqueVerdict (tokens [.present "A", .present "A"]) =
      .fired .value ∧
    evalValuesNotUniqueVerdict (tokens [.present "A", .present "a"]) = .notFired := by
  native_decide

/- The ordered scan skips empties here exactly as it does for Number, and it skips a formally
   unavailable cell the same way rather than suppressing: the duplicate around one still fires, while
   two equal unavailable values are not a duplicate at all. -/
example :
    evalValuesNotUniqueVerdict (tokens [.empty, .empty]) = .notFired ∧
    evalValuesNotUniqueVerdict (tokens [.present "A", .empty]) = .notFired ∧
    evalValuesNotUniqueVerdict
      (tokens [.present "A", .unknown .malformed, .present "A"]) = .fired .value ∧
    evalValuesNotUniqueVerdict
      (tokens [.unknown .malformed, .unknown .malformed]) = .notFired := by
  native_decide

private def stringField (id : FieldId) (name : String) : FlatFieldDecl :=
  { id, groupPath := ["Form"], name, policy := { kind := .string },
    stringPolicy := { lineBreaksPermitted := true } }

private def enumerationField : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "Priority",
    policy := { kind := .enumeration },
    enumeration := some { storedTokens := ["A", "B"] } }

private def secondEnumerationField : FlatFieldDecl :=
  { enumerationField with id := 4, name := "Fallback" }

private def model : FlatModel := {
  fields := [stringField 1 "Code", stringField 2 "Alternate", enumerationField,
    secondEnumerationField]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def source? (first second : String) :
    Option (CheckedTokenValuesNotUniqueSource model) :=
  (elaborateTokenValuesNotUniqueSource model ["Form"]
    { first := .field (bare first), rest := [.field (bare second)] }).toOption

/- Two String operands are admitted, and so are two stored-Enumeration operands, while any mix of the two kinds is refused in either order. This operator is therefore stricter than the distinct count it shares an entity list with, which admits that same comparable mix. -/
example :
    (source? "Code" "Alternate").isSome = true ∧
    (source? "Priority" "Fallback").isSome = true ∧
    (source? "Code" "Priority").isNone = true ∧
    (source? "Priority" "Code").isNone = true := by
  native_decide

/- Stored Enumeration tokens fold through the same exact-identity membership as String, so the evaluation half needs no kind-specific rule. -/
example :
    evalValuesNotUniqueVerdict (tokens [.present "A", .present "B", .present "A"]) =
      .fired .value ∧
    evalValuesNotUniqueVerdict (tokens [.present "A", .present "B"]) = .notFired := by
  native_decide

end A12Kernel
