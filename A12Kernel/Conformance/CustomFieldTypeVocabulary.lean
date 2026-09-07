import A12Kernel.Semantics.CustomFieldTypeVocabulary

/-! # Locks on the custom field type refusal vocabulary

The cases below lock the two-axis structure, and in particular the two places where the obvious simplification — one code per type, one type per key — is wrong.
-/

namespace A12Kernel.Conformance.CustomFieldTypeVocabulary

open A12Kernel

/- The catalog is exactly the thirty-six detail keys and thirteen types, and no name repeats. A
   duplicate would silently merge two of the Kernel's refusals into one. -/
example :
    CustomFieldTypeDetail.all.length = 36 ∧
      (CustomFieldTypeDetail.all.map (·.catalogKey)).eraseDups.length = 36 ∧
      CustomFieldType.all.length = 13 ∧
      (CustomFieldType.all.map (·.errorCode)).eraseDups.length = 13 := by
  native_decide

/- Every refusal key has an owner and the success sentinel has none, so `owners` partitions the
   catalog rather than merely annotating it. -/
example :
    CustomFieldTypeDetail.noError.owners = [] ∧
      (CustomFieldTypeDetail.all.filter (fun d => d.owners.isEmpty)).length = 1 := by
  native_decide

/- Every type's refusal set is nonempty and every refusal key is reachable from exactly one type's
   set, except the shared date key which is reachable from two. Summing the per-type sets therefore
   double-counts by exactly one, which is the arithmetic a consumer building a per-type switch has
   to get right. -/
example :
    (CustomFieldType.all.map (fun t => (CustomFieldTypeDetail.refusalsOf t).length)).sum = 36 ∧
      CustomFieldTypeDetail.all.length - 1 = 35 := by
  native_decide

/- First counterexample to the obvious simplification: one detail key, two owning types. A consumer
   reading the type off the key gets the wrong one half the time. -/
example :
    CustomFieldTypeDetail.dateInvalid.owners = [.dateMonthYear, .dateDayMonthYear] ∧
      CustomFieldTypeDetail.dateInvalid.surfacedCode .dateMonthYear = "ungueltigesDatumMMJJ" ∧
      CustomFieldTypeDetail.dateInvalid.surfacedCode .dateDayMonthYear =
        "ungueltigesDatumTTMMJJ" := by
  native_decide

/- Second counterexample, in the other direction: one type, two surfaced codes. The reserved
   test-range key is the only detail in the whole catalog whose surfaced code is not its owner's,
   and the neighbouring identification-number refusals are what make that visible. -/
example :
    CustomFieldTypeDetail.identificationNumberTestOnly.surfacedCode .identificationNumber =
        "testIDNummer" ∧
      CustomFieldTypeDetail.identificationNumberCheckDigit.surfacedCode .identificationNumber =
        "ungueltigeIDNummer" ∧
      (CustomFieldTypeDetail.all.filter fun d =>
        d.owners.any fun t => d.surfacedCode t ≠ t.errorCode).length = 1 := by
  native_decide

/- The identification number carries the deepest refusal set and the country abbreviation the
   shallowest, so the family's spread is one to six rather than uniform. -/
example :
    (CustomFieldTypeDetail.refusalsOf .identificationNumber).length = 6 ∧
      (CustomFieldTypeDetail.refusalsOf .countryAbbreviation).length = 1 ∧
      (CustomFieldTypeDetail.refusalsOf .bicInternational).length = 1 := by
  native_decide

/- The German and international IBAN validators are separate types with disjoint keys, and the
   international one carries no country-code key at all — the difference a consumer would erase by
   treating one as a mode of the other. -/
example :
    (CustomFieldTypeDetail.refusalsOf .iban).length = 5 ∧
      (CustomFieldTypeDetail.refusalsOf .ibanInternational).length = 4 ∧
      (CustomFieldTypeDetail.refusalsOf .iban).all
        (fun d => !(CustomFieldTypeDetail.refusalsOf .ibanInternational).contains d) ∧
      (CustomFieldTypeDetail.refusalsOf .iban).contains .ibanCountryCode := by
  native_decide

end A12Kernel.Conformance.CustomFieldTypeVocabulary
