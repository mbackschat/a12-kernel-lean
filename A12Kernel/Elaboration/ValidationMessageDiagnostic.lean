import A12Kernel.Elaboration.ValidationMessageAuthoring
import A12Kernel.Elaboration.StaticDiagnostic

namespace A12Kernel

/-- The established named class of a bounded rule-message refusal.

The [retained rule-message checks](../../docs/SOURCES.md#src-message-template-character-repertoire)
and [group lexical checks](../../docs/SOURCES.md#src-message-group-parameter-resolution) fix these
classes, and the group position's model classes and the name position's path classes are measured at
the [group-argument checkpoints](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)
and the [name-position](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-refusals) and [carrier](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers) checkpoints. This projection is for the rule producer; the shared error type alone supplies no evidence
for a String-pattern or computation-message carrier. A codeless repertoire finding remains in the
original error, beside any named cause. `none` means no established named class, never acceptance;
in particular the fragment's generic parse refusals and its unmodelled index gate stay unmapped. -/
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
  | .groupParameterLexical _ .lexer => some .lexerStandardError
  | .groupParameterLexical _ .truncated => some .incompleteInput
  | .groupParameterLexical _ .expectedToken => some .expectedTokenNotFound
  | .groupParameterLexical _ .separator => some .unexpectedToken
  | .groupParameterLexical _ .unexpected => some .unexpectedToken
  | .unsupportedCharacterWithError _ cause => cause.namedRuleDiagnostic?
  | .reference _ (.unknownRootGroup _) => some .messageInvalidRootGroup
  | .reference _ (.invalidEntity _) => some .messageInvalidEntity
  | .reference _ (.aboveRoot _) => some .parameterTooManyParentGroups
  | .reference _ (.shortNameNotUnique _) => some .messageFieldNameNotUnique
  | .groupInNamePosition _ _ => some .messageFieldNotReferenced
  | .groupInFormPointer _ _ => some .invalidFieldInParameter
  | .categoryFieldNotEnumeration _ _ => some .indexFieldNoEnumeration
  | .category _ (.unknownCategory _) => some .indexFieldCategoryUnknown
  | .nestedSemanticIndex _ => some .illegalSemanticIndex
  | .invalidGroupParameter _ => some .invalidGroupInParameter
  | .groupShortNameNotUnique _ _ => some .messageFieldNameNotUnique
  | .groupParameterAboveRoot _ => some .parameterTooManyParentGroups
  | .groupTurningPointMismatch _ => some .messageInvalidEntity
  | .unknownRootGroup _ _ => some .messageInvalidRootGroup
  | .retiredGroupTerminal _ _ => some .parameterInvalidInNewWorld
  | .ruleGroupImmediatelyBelowRoot _ => some .ruleGroupImmediatelyBelowRoot
  | _ => none

/-- The established named class of a String-pattern field-message refusal.

A line separator draws `INVALID_LINEBREAK` and a control character `INVALID_CHARACTERS`, as on a
rule's message ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)); an odd dollar
count `WRONG_NUMBER_OF_DOLLARS`, a parameter other than the two tokens, the empty one included,
`INVALID_PARAMETER`, and an empty text the pairing class `MVK_ERROR_MESSAGE_AND_PATTERN_INVALID`
([inbound](../../docs/SOURCES.md#inbound-2026-09-26n-field-message-gates)). The parameter-body
character refusal has no field-carrier row and stays `none`, which never means acceptance. -/
def ValidationMessageTemplateError.namedStringPatternDiagnostic? :
    ValidationMessageTemplateError → Option KernelStaticDiagnostic
  | .lineSeparator => some .invalidMessageLinebreak
  | .controlCharacter _ => some .invalidMessageCharacters
  | .oddDollarCount => some .wrongNumberOfDollars
  | .invalidParameter _ => some .invalidMessageParameter
  | .emptyTemplate => some .errorMessageAndPatternInvalid
  | .unsupportedCharacterWithError _ cause => cause.namedStringPatternDiagnostic?
  | _ => none

end A12Kernel
