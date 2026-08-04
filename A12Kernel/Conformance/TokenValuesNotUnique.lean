import A12Kernel.Elaboration.TokenValuesNotUnique

/-! # `FieldValuesNotUnique` conformance locks over the String overload -/

namespace A12Kernel

private def tokenSide (cells : List (ValueListCell .token)) :
    ResolvedValueListSide .token :=
  { cells, hasUninstantiatedTail := false, hasHaving := false }

/- Canonical token identity is exact, so a duplicate must match byte for byte and case differences are two distinct values. -/
example :
    evalValuesNotUnique (tokenSide [.present "A", .present "A"]).cells = .tru ∧
    evalValuesNotUnique (tokenSide [.present "A", .present "a"]).cells = .fls := by
  native_decide

/- The shared present-scan skips empties here exactly as it does for Number, and a reached formal unavailability suppresses. -/
example :
    evalValuesNotUnique (tokenSide [.empty, .empty]).cells = .fls ∧
    evalValuesNotUnique (tokenSide [.present "A", .empty]).cells = .fls ∧
    evalValuesNotUnique
      (tokenSide [.present "A", .unknown .malformed, .present "A"]).cells
      = .unknown := by
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
    evalValuesNotUnique (tokenSide [.present "A", .present "B", .present "A"]).cells
      = .tru ∧
    evalValuesNotUnique (tokenSide [.present "A", .present "B"]).cells = .fls := by
  native_decide

end A12Kernel
