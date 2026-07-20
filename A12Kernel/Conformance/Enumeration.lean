import A12Kernel.Semantics.Enumeration

/-! # Resolved Enumeration/category comparison conformance

These cases begin after ordinary closed-Enumeration declaration checks, field observation, and category-name selection. Admitted comparisons also begin after literal-domain checking; two explicitly defensive total-runtime controls instead supply an out-of-domain display or projection token to prove that runtime access does not silently switch domains. Those controls carry no authored-kernel correspondence claim. Display transport and field-to-field comparability remain outside this capsule.
-/

namespace A12Kernel

private def category (categoryTokens : List String) :
    ResolvedEnumerationCategory :=
  {
    storedTokens := ["F", "D"]
    categoryTokens
  }

private def observedEnum (stored : String) : CellObservation :=
  .value (.enum stored)

/- Direct Enumeration comparison uses the stored token. The out-of-domain display label is a defensive total-runtime separator, not an authored case. -/
example :
    ResolvedEnumerationProjection.stored.evalLiteral
        .equal (observedEnum "F") "F" = .fired .value ∧
      ResolvedEnumerationProjection.stored.evalLiteral
        .equal (observedEnum "F") "France" = .notFired ∧
      ResolvedEnumerationProjection.stored.evalLiteral
        .notEqual (observedEnum "F") "D" = .fired .value ∧
      ResolvedEnumerationProjection.stored.evalLiteral
        .notEqual (observedEnum "F") "F" = .notFired := by
  native_decide

/- Repeated category tokens are legal: distinct stored values can intentionally compare alike. -/
example :
    let projection := ResolvedEnumerationProjection.category (category ["EU", "EU"])
    projection.evalLiteral .equal (observedEnum "F") "EU" = .fired .value ∧
      projection.evalLiteral .equal (observedEnum "D") "EU" = .fired .value := by
  native_decide

/- Category association is positional; swapping only the category vector changes the selected token. -/
example :
    let original := ResolvedEnumerationProjection.category (category ["EU", "NA"])
    let swapped := ResolvedEnumerationProjection.category (category ["NA", "EU"])
    original.evalLiteral .equal (observedEnum "F") "EU" = .fired .value ∧
      swapped.evalLiteral .equal (observedEnum "F") "EU" = .notFired ∧
      original.evalLiteral .equal (observedEnum "D") "NA" = .fired .value ∧
      original.evalLiteral .notEqual (observedEnum "D") "EU" = .fired .value := by
  native_decide

/- Direct and category projections are distinct. The stored token is outside this category's literal domain and serves only as a defensive total-runtime separator. -/
example :
    let projection := ResolvedEnumerationProjection.category (category ["EU", "NA"])
    ResolvedEnumerationProjection.stored.evalLiteral
        .equal (observedEnum "F") "F" = .fired .value ∧
      projection.evalLiteral .equal (observedEnum "F") "F" = .notFired := by
  native_decide

/- Empty Enumeration is not evaluated under either operator or projection; inequality is not verdict negation. -/
example :
    let projection := ResolvedEnumerationProjection.category (category ["EU", "NA"])
    ResolvedEnumerationProjection.stored.evalLiteral
        .equal .empty "F" = .notFired ∧
      ResolvedEnumerationProjection.stored.evalLiteral
        .notEqual .empty "F" = .notFired ∧
      projection.evalLiteral .equal .empty "EU" = .notFired ∧
      projection.evalLiteral .notEqual .empty "EU" = .notFired := by
  native_decide

/- Formal unavailability remains UNKNOWN for both operators and projections. -/
example :
    let projection := ResolvedEnumerationProjection.category (category ["EU", "NA"])
    ResolvedEnumerationProjection.stored.evalLiteral
        .equal (.unknown .declaredConstraint) "F" = .unknown ∧
      ResolvedEnumerationProjection.stored.evalLiteral
        .notEqual (.unknown .declaredConstraint) "F" = .unknown ∧
      projection.evalLiteral
        .equal (.unknown .declaredConstraint) "EU" = .unknown ∧
      projection.evalLiteral
        .notEqual (.unknown .declaredConstraint) "EU" = .unknown := by
  native_decide

/- The boundary keeps Enumeration distinct from String despite their shared token representation. -/
example :
    ResolvedEnumerationProjection.stored.evalLiteral
        .equal (.value (.str "F")) "F" = .unknown := by
  native_decide

/- Incoherent stored/category domains fail closed; lookup miss is not ordinary enum emptiness. -/
example :
    let incomplete : ResolvedEnumerationCategory := {
      storedTokens := ["F", "D"]
      categoryTokens := ["EU"]
    }
    let projection := ResolvedEnumerationProjection.category incomplete
    projection.evalLiteral .equal (observedEnum "D") "EU" = .unknown ∧
      projection.evalLiteral .notEqual (observedEnum "D") "EU" = .unknown := by
  native_decide

end A12Kernel
