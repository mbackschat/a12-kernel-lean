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
  { id := 3, groupPath := ["Form"], name := "Priority", policy := { kind := .enumeration },
    enumeration := some { storedTokens := ["A", "B"] } }

private def secondEnumerationField : FlatFieldDecl :=
  { enumerationField with id := 4, name := "Fallback" }

private def numberField : FlatFieldDecl :=
  { id := 5, groupPath := ["Form"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := true } } }

private def booleanField : FlatFieldDecl :=
  { id := 6, groupPath := ["Form"], name := "Flag", policy := { kind := .boolean } }

private def confirmField : FlatFieldDecl :=
  { id := 7, groupPath := ["Form"], name := "Consent", policy := { kind := .confirm } }

private def model : FlatModel := {
  fields := [stringField 1 "Code", stringField 2 "Alternate", enumerationField,
    secondEnumerationField, numberField, booleanField, confirmField]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def source? (first second : String) :
    Option (CheckedTokenValuesNotUniqueSource model) :=
  (elaborateTokenValuesNotUniqueSource model ["Form"]
    { first := .field (bare first), rest := [.field (bare second)] }).toOption

private def staticError? (first : String) (rest : List String) :
    Option TokenValuesNotUniqueElabError :=
  match elaborateTokenValuesNotUniqueSource model ["Form"]
      { first := .field (bare first), rest := rest.map fun name => .field (bare name) } with
  | .error error => some error
  | .ok _ => none

private def staticDiagnostic? (first : String) (rest : List String) :
    Option KernelStaticDiagnostic :=
  (staticError? first rest).bind TokenValuesNotUniqueElabError.diagnostic?

/- Two String operands are admitted, and so are two stored-Enumeration operands, while any mix of the two kinds is refused in either order. This operator is therefore stricter than the distinct count it shares an entity list with, which admits that same comparable mix. -/
example :
    (source? "Code" "Alternate").isSome = true ∧
    (source? "Priority" "Fallback").isSome = true ∧
    (source? "Code" "Priority").isNone = true ∧
    (source? "Priority" "Code").isNone = true := by
  native_decide

/- String and Enumeration remain separate categories for this operator. Number is another
   category, while BOOLEAN and CONFIRM take the earlier whole-list kind gate in either order. -/
example :
    staticDiagnostic? "Code" [] = some .paramSizeInvalidN ∧
      staticDiagnostic? "Consent" [] = some .paramSizeInvalidN ∧
      staticDiagnostic? "Code" ["Priority"] = some .varyingTypesNotAllowed ∧
      staticDiagnostic? "Priority" ["Code"] = some .varyingTypesNotAllowed ∧
      staticDiagnostic? "Code" ["Amount"] = some .varyingTypesNotAllowed ∧
      staticDiagnostic? "Code" ["Flag"] = some .onlyStringEnumNumberDateAllowed ∧
      staticDiagnostic? "Code" ["Consent"] = some .onlyStringEnumNumberDateAllowed ∧
      staticDiagnostic? "Code" ["Amount", "Flag"] = some .onlyStringEnumNumberDateAllowed ∧
      staticDiagnostic? "Code" ["Flag", "Amount"] = some .onlyStringEnumNumberDateAllowed := by
  native_decide

/- Static refusals retain their exact offending path and kind, and duplicate identity stays
   unmapped because this capsule established no Kernel diagnostic for it. -/
example :
    staticError? "Code" ["Priority"] = some (.mixedCategories ["Form", "Priority"] .enumeration) ∧
      staticError? "Code" ["Flag"] = some (.inadmissibleKind ["Form", "Flag"] .boolean) ∧
      staticDiagnostic? "Code" ["Code"] = none := by
  native_decide

/- Stored Enumeration tokens fold through the same exact-identity membership as String, so the evaluation half needs no kind-specific rule. -/
example :
    evalValuesNotUniqueVerdict (tokens [.present "A", .present "B", .present "A"]) =
      .fired .value ∧
    evalValuesNotUniqueVerdict (tokens [.present "A", .present "B"]) = .notFired := by
  native_decide

end A12Kernel
