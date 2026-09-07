import A12Kernel.Elaboration.UnraisedDiagnostic
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Locks on the never-reported catalog keys

The point of the negative vocabulary is that a consumer can subtract it from a catalog enumeration, so the cases below lock the two properties that makes safe: the two vocabularies never claim the same key, and the near-miss key pairs stay apart.
-/

namespace A12Kernel.Conformance.UnraisedDiagnostic

open A12Kernel

/- No key is listed twice, so subtracting the list from a catalog enumeration removes exactly its
   length. -/
example :
    (A12Kernel.UnraisedDiagnostic.all.map (·.catalogKey)).eraseDups.length =
      A12Kernel.UnraisedDiagnostic.all.length := by
  native_decide

/- The separating property the whole module exists for: a key established as never reported is not
   also established as reported. A single overlap would mean one of the two vocabularies rests on a
   wrong reading, and a consumer trusting either would branch on a class that cannot arrive. -/
example :
    A12Kernel.UnraisedDiagnostic.all.all fun unraised =>
      KernelStaticDiagnostic.all.all fun reported =>
        unraised.catalogKey ≠ reported.kernelCode := by
  native_decide

/- The two mechanisms partition the slice, and neither side is empty — an empty side would mean the
   distinction was recorded without being exercised. -/
example :
    A12Kernel.UnraisedDiagnostic.neverRaised.length = 8 ∧
      A12Kernel.UnraisedDiagnostic.labelsOnly.length = 7 ∧
      A12Kernel.UnraisedDiagnostic.neverRaised.length +
          A12Kernel.UnraisedDiagnostic.labelsOnly.length =
        A12Kernel.UnraisedDiagnostic.all.length := by
  native_decide

/- The near-miss pair, and the reason a consumer cannot collapse the two spellings: the plural form
   is a class the Kernel reports, and the form differing only by a `_NO_FIELD` suffix is not. -/
example :
    A12Kernel.UnraisedDiagnostic.onlyStringEnumNumberCmpDateAllowedNoField.catalogKey =
        KernelStaticDiagnostic.onlyStringEnumNumberCmpDateAllowed.kernelCode ++ "_NO_FIELD" ∧
      A12Kernel.UnraisedDiagnostic.onlyStringEnumNumberCmpDateAllowedNoField.reason =
        .declaredNeverRaised := by
  native_decide

/- An interpolated label sits in a catalog beside real diagnostics, so the catalog alone cannot tell
   a consumer which it is holding. -/
example :
    A12Kernel.UnraisedDiagnostic.categoryRefOp.catalog = "vk_parser_error_messages" ∧
      A12Kernel.UnraisedDiagnostic.categoryRefOp.reason = .interpolatedLabelOnly ∧
      A12Kernel.UnraisedDiagnostic.noVordruckzeile.catalog =
        "vk_service_errortext_error_messages" ∧
      A12Kernel.UnraisedDiagnostic.noVordruckzeile.reason = .declaredNeverRaised := by
  native_decide

/- Four catalogs contribute, so this is not one module's local accident. -/
example :
    ((A12Kernel.UnraisedDiagnostic.all.map (·.catalog)).eraseDups).length = 4 := by
  native_decide

end A12Kernel.Conformance.UnraisedDiagnostic
