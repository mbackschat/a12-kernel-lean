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
  {
    storedTokens := ["A", "B"]
    categories := [
      { name := "Choice", tokens := ["A", "B"] },
      { name := "Foreign", tokens := ["X", "Y"] }
    ]
  }

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
    categories := [{ name := "Target", tokens := ["A", "B"] }, { name := "Wide", tokens := ["A", "C"] }]
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

private def targetDiagnosticOf (source : SurfaceEnumerationComputationSource) :
    Option KernelStaticDiagnostic :=
  (errorOf source).bind EnumerationComputationElabError.targetDiagnostic?

private def outcomeOf (source : SurfaceEnumerationComputationSource)
    (raw : RawFlatContext) : Option StringTargetOutcome := do
  let checked ←
    (elaborateEnumerationComputation model ["Form"] target.id source).toOption
  some (checked.evaluate raw)

/- Literals are checked against the exact target domain before runtime, and the refusal carries the
   Kernel identity it was measured with. This is the one constant family whose target constrains the
   literal's **value** statically rather than rendering it, which is why the admitted token stores
   verbatim while an undeclared one never reaches runtime
   ([checkpoint](../../docs/SOURCES.md#src-constant-literal-family-gate)). -/
example :
    outcomeOf (.literal "A") (rawAt 99 .empty) =
        some (.accepted { text := "A", nonempty := by decide }) ∧
      errorOf (.literal "C") =
        some (.literalOutsideTarget target.path "C") ∧
      (errorOf (.literal "C")).bind
          (fun cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode) =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON" := by
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

/- Complete selected-domain containment and direct display compatibility are independent static gates:
   the display is the generated comparison's and the domain the calculation's. Neither row fails both,
   so the order between them is locked on the field-copy grid, where a wider Enumeration into a
   labelled target draws the display class. -/
example :
    errorOf (.field (.direct (bare "Wider"))) =
        some (.sourceOutsideTargetDomain wider.path target.path) ∧
      errorOf (.field (.direct (bare "Displayed"))) =
        some (.copyComparison target.path displayed.path (.displayArm .displayClassMismatch)) := by
  native_decide

/- A category whose projected tokens leave the target's domain draws the calculation's class, as the
   Kernel's local `[Banded -> Wide]` into an Enumeration does
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-25i-enum-source)). -/
example :
    errorOf (.field (.category (bare "Category") "Wide")) =
        some (.sourceOutsideTargetDomain category.path target.path) ∧
      ((errorOf (.field (.category (bare "Category") "Wide"))).bind
        EnumerationComputationElabError.calculationRefusal?) = some .invalidEnumCalculation := by
  native_decide

/- A category source is checked by its projected token domain and bypasses direct display remapping.
   A stored token outside the source's own domain has no category to project, and the read poisons
   rather than answering EMPTY, exactly like the direct read above
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-category-read-poison)). -/
example :
    outcomeOf (.field (.category (bare "Category") "Target"))
        (rawAt category.id (.parsed (.enum "X"))) =
      some (.accepted { text := "A", nonempty := by decide }) ∧
    outcomeOf (.field (.category (bare "Category") "Target"))
        (rawAt category.id (.parsed (.enum "Z"))) =
      some (.poison .declaredConstraint) := by
  native_decide

/- Direct target self-reference is rejected before compatibility can make it look harmless. -/
example :
    errorOf (.field (.direct (bare "Target"))) =
        some (.targetSelfReferenceAtDirectField target.id) ∧
      targetDiagnosticOf (.field (.direct (bare "Target"))) =
        some .errorReferenceToCalculatedField := by
  native_decide

/- The compatible target-category projection carries its distinct measured
Kernel class. An incompatible category and unrelated Enumeration refusals stay
local. -/
example :
    targetDiagnosticOf (.field (.direct (bare "Direct"))) = none ∧
      targetDiagnosticOf (.literal "C") = none ∧
      targetDiagnosticOf (.field (.direct (bare "Wider"))) = none ∧
      targetDiagnosticOf (.field (.direct (bare "Displayed"))) = none ∧
      targetDiagnosticOf (.field (.direct (bare "PlainString"))) = none ∧
      errorOf (.field (.category (bare "Target") "Choice")) =
        some (.targetSelfReferenceAtCompatibleCategory target.id) ∧
      targetDiagnosticOf (.field (.category (bare "Target") "Choice")) =
        some .errorSemanticIndexOrCategoryForErrorField ∧
      errorOf (.field (.category (bare "Target") "Foreign")) =
        some (.targetSelfReference target.id) ∧
      targetDiagnosticOf (.field (.category (bare "Target") "Foreign")) = none ∧
      KernelStaticDiagnostic.kernelCode
        .errorSemanticIndexOrCategoryForErrorField =
          "MVK_ERROR_SEMANTIC_INDEX_OR_CATEGORY_FOR_ERRORFIELD" := by
  native_decide

/- An ordinary String field cannot enter the Enumeration-producing source surface merely because both
   store text: the comparison admits it into this unlabelled target, and the calculation refuses it. -/
example :
    errorOf (.field (.direct (bare "PlainString"))) =
      some (.stringSource plainString.path target.path) := by
  native_decide

end A12Kernel.Conformance.EnumerationComputation
