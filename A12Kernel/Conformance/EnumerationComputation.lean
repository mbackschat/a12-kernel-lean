import A12Kernel.Elaboration.EnumerationComputation

/-! # Checked ordinary Enumeration computation locks -/

namespace A12Kernel.Conformance.EnumerationComputation

open A12Kernel

private def enumField (id : FieldId) (name : String)
    (enumeration : EnumerationDeclaration) : FlatFieldDecl :=
  {
    id
    groupPath := ["Form"]
    name
    policy := { kind := .enumeration }
    enumeration := some enumeration
  }

private def targetDomain : EnumerationDeclaration :=
  { storedTokens := ["A", "B"] }

private def directDomain : EnumerationDeclaration :=
  { storedTokens := ["A", "B"] }

private def widerDomain : EnumerationDeclaration :=
  { storedTokens := ["A", "C"] }

private def displayedDomain : EnumerationDeclaration :=
  {
    storedTokens := ["A", "B"]
    displayFacts := [
      { locale := "en", stored := "A", display := "Alpha" },
      { locale := "en", stored := "B", display := "Beta" }
    ]
  }

private def categoryDomain : EnumerationDeclaration :=
  {
    storedTokens := ["X", "Y"]
    displayFacts := [
      { locale := "en", stored := "X", display := "Ex" },
      { locale := "en", stored := "Y", display := "Why" }
    ]
    categories := [{ name := "Target", tokens := ["A", "B"] }]
  }

private def target := enumField 0 "Target" targetDomain
private def direct := enumField 1 "Direct" directDomain
private def wider := enumField 2 "Wider" widerDomain
private def displayed := enumField 3 "Displayed" displayedDomain
private def category := enumField 4 "Category" categoryDomain
private def plainString : FlatFieldDecl :=
  {
    id := 5
    groupPath := ["Form"]
    name := "PlainString"
    policy := { kind := .string }
  }

private def model : FlatModel :=
  { fields := [target, direct, wider, displayed, category, plainString] }

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def rawAt (field : FieldId) (cell : RawCell) : RawFlatContext where
  read candidate := if candidate == field then cell else .empty

private def errorOf (source : SurfaceEnumerationComputationSource) :
    Option EnumerationComputationElabError :=
  match elaborateEnumerationComputation model ["Form"] target.id source with
  | .ok _ => none
  | .error error => some error

private def outcomeOf (source : SurfaceEnumerationComputationSource)
    (raw : RawFlatContext) : Option StringTargetOutcome := do
  let checked ←
    (elaborateEnumerationComputation model ["Form"] target.id source).toOption
  some (checked.evaluate raw)

/- Literals are checked against the exact target domain before runtime. -/
example :
    outcomeOf (.literal "A") (rawAt 99 .empty) =
        some (.accepted { text := "A", nonempty := by decide }) ∧
      errorOf (.literal "C") =
        some (.literalOutsideTarget target.path "C") := by
  native_decide

/- A compatible direct source preserves value, clean empty, and formal poison through the shared token result. -/
example :
    outcomeOf (.field (.direct (bare "Direct")))
        (rawAt direct.id (.parsed (.enum "B"))) =
          some (.accepted { text := "B", nonempty := by decide }) ∧
      outcomeOf (.field (.direct (bare "Direct")))
        (rawAt direct.id .presentEmpty) = some .noValue ∧
      outcomeOf (.field (.direct (bare "Direct")))
        (rawAt direct.id (.parsed (.enum "C"))) =
          some (.poison .declaredConstraint) := by
  native_decide

/- Complete selected-domain containment and direct display compatibility are independent static gates. -/
example :
    errorOf (.field (.direct (bare "Wider"))) =
        some (.sourceIncompatible wider.path target.path) ∧
      errorOf (.field (.direct (bare "Displayed"))) =
        some (.sourceIncompatible displayed.path target.path) := by
  native_decide

/- A category source is checked by its projected token domain and bypasses direct display remapping. -/
example :
    outcomeOf (.field (.category (bare "Category") "Target"))
        (rawAt category.id (.parsed (.enum "X"))) =
      some (.accepted { text := "A", nonempty := by decide }) := by
  native_decide

/- Direct target self-reference is rejected before compatibility can make it look harmless. -/
example :
    errorOf (.field (.direct (bare "Target"))) =
      some (.targetSelfReference target.id) := by
  native_decide

/- An ordinary String field cannot enter the Enumeration-producing source surface merely because both store text. -/
example :
    errorOf (.field (.direct (bare "PlainString"))) =
      some (.source (.textFieldOperandKindMismatch plainString.path .string)) := by
  native_decide

end A12Kernel.Conformance.EnumerationComputation
