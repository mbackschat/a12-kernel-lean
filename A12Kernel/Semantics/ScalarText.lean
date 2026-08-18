import A12Kernel.Semantics.Observation

/-! # Canonical stored Boolean and Confirm text

This capsule classifies the stored data-document text consumed by Boolean and Confirm formal checking. Boolean admits only exact lowercase `true` and `false`; Confirm admits only exact lowercase `true`. Empty physical text remains present-empty. Display conversion, host ingress normalization, model-declared `@NotInD` tokens, and every other scalar type remain separate.
-/

namespace A12Kernel

/-- Classify one physically stored Boolean text before ordinary formal checking. Equality is exact and case-sensitive. -/
def classifyStoredBooleanText (text : String) : RawCell :=
  if text.isEmpty then
    .presentEmpty
  else if text == "true" then
    .parsed (.bool true)
  else if text == "false" then
    .parsed (.bool false)
  else
    .rejected .booleanToken

/-- Classify one physically stored Confirm text before ordinary formal checking. Confirm has no stored false value. -/
def classifyStoredConfirmText (text : String) : RawCell :=
  if text.isEmpty then
    .presentEmpty
  else if text == "true" then
    .parsed (.conf true)
  else
    .rejected .confirmToken

end A12Kernel
