import A12Kernel.Elaboration.ValidationMessageAuthoring
import A12Kernel.Elaboration.StaticDiagnostic

namespace A12Kernel

/-- The established named class of a bounded rule-message refusal.

The [retained rule-message checks](../../docs/SOURCES.md#src-message-template-character-repertoire)
and [group lexical checks](../../docs/SOURCES.md#src-message-group-parameter-resolution) fix these
classes. This projection is for the rule producer; the shared error type alone supplies no evidence
for a String-pattern or computation-message carrier. A codeless repertoire finding remains in the
original error, beside any named cause. `none` means no established named class, never acceptance;
in particular the fragment's generic parse and semantic-index refusals stay unmapped. -/
def ValidationMessageTemplateError.namedRuleDiagnostic? :
    ValidationMessageTemplateError → Option KernelStaticDiagnostic
  | .emptyTemplate => some .ruleHasNoErrorText
  | .lineSeparator => some .invalidMessageLinebreak
  | .controlCharacter _ => some .invalidMessageCharacters
  | .oddDollarCount => some .wrongNumberOfDollars
  | .noBaseYear => some .noMessageBaseYear
  | .fieldNotReferenced _ _ => some .messageFieldNotReferenced
  | .missingCategoryName _ => some .missingMessageCategory
  | .parameterCharacter _ _ => some .lexerStandardError
  | .groupParameterLexical _ .quote => some .lexerStandardError
  | .groupParameterLexical _ .truncated => some .incompleteInput
  | .groupParameterLexical _ .separator => some .unexpectedToken
  | .unsupportedCharacterWithError _ cause => cause.namedRuleDiagnostic?
  | _ => none

/-- The established named class of a String-pattern field-message refusal.

A line separator draws `INVALID_LINEBREAK` and a control character `INVALID_CHARACTERS`, as on a
rule's message ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)), and a named
parameter other than the two tokens `INVALID_PARAMETER`
([ledger](../../docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#exp-2026-07-30-01)).
The empty pair is refused with no recorded class, and no field-carrier row names dollar parity's, so
both stay `none` like every other refusal here, and `none` never means acceptance. -/
def ValidationMessageTemplateError.namedStringPatternDiagnostic? :
    ValidationMessageTemplateError → Option KernelStaticDiagnostic
  | .lineSeparator => some .invalidMessageLinebreak
  | .controlCharacter _ => some .invalidMessageCharacters
  | .invalidParameter parameter => if parameter.isEmpty then none else some .invalidMessageParameter
  | .unsupportedCharacterWithError _ cause => cause.namedStringPatternDiagnostic?
  | _ => none

end A12Kernel
