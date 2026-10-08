import A12Kernel.Elaboration.ValidationMessageAuthoring
import A12Kernel.Elaboration.StaticDiagnostic

namespace A12Kernel

/-- The established named class of a bounded rule-message refusal.

The [retained rule-message checks](../../docs/sources/message-and-pointer-probes.md#src-message-template-character-repertoire)
and [group lexical checks](../../docs/sources/message-and-pointer-probes.md#src-message-group-parameter-resolution) fix these
classes, and the group position's model classes and the name position's path classes are measured at
the [group-argument checkpoints](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)
and the [name-position](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-refusals) and [carrier](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers) checkpoints. This projection is for the rule producer; the shared error type alone supplies no evidence
for a String-pattern or computation-message carrier. A codeless repertoire finding remains in the
original error, beside any named cause. `none` means no established named class, never acceptance;
the `index(...)` form and the rule-group terminal where the Kernel fails internally stay unmapped. -/
def ValidationMessageTemplateError.namedRuleDiagnostic? :
    ValidationMessageTemplateError → Option KernelStaticDiagnostic
  | .emptyTemplate => some .ruleHasNoErrorText
  | .lineSeparator => some .invalidMessageLinebreak
  | .controlCharacter _ => some .invalidMessageCharacters
  | .oddDollarCount => some .wrongNumberOfDollars
  | .noBaseYear => some .noMessageBaseYear
  | .fieldNotReferenced _ _ => some .messageFieldNotReferenced
  | .missingCategoryName _ => some .missingMessageCategory
  | .categoryFieldNotEnumeration _ _ => some .indexFieldNoEnumeration
  | .category _ (.unknownCategory _) => some .indexFieldCategoryUnknown
  | .parameterSyntax _ .lexer => some .lexerStandardError
  | .parameterSyntax _ .truncated => some .incompleteInput
  | .parameterSyntax _ .expectedToken => some .expectedTokenNotFound
  | .parameterSyntax _ .separator => some .unexpectedToken
  | .parameterSyntax _ .unexpected => some .unexpectedToken
  | .unsupportedCharacterWithError _ cause => cause.namedRuleDiagnostic?
  | .reference _ (.unknownRootGroup _) => some .messageInvalidRootGroup
  | .reference _ (.invalidEntity _) => some .messageInvalidEntity
  | .reference _ (.aboveRoot _) => some .parameterTooManyParentGroups
  | .reference _ (.shortNameNotUnique _) => some .messageFieldNameNotUnique
  | .groupInNamePosition _ _ => some .messageFieldNotReferenced
  | .groupInFormPointer _ _ => some .invalidFieldInParameter
  | .nestedSemanticIndex _ => some .illegalSemanticIndex
  | .keyNotInCondition _ => some .indexForErrorTextInvalid
  | .ruleGroupParameter _ => some .invalidMessageParameter
  | .invalidGroupParameter _ => some .invalidGroupInParameter
  | .groupShortNameNotUnique _ _ => some .messageFieldNameNotUnique
  | .parameterAboveRoot _ => some .parameterTooManyParentGroups
  | .turningPointMismatch _ => some .messageInvalidEntity
  | .unknownRootGroup _ _ => some .messageInvalidRootGroup
  | .retiredGroupTerminal _ _ => some .parameterInvalidInNewWorld
  | .ruleGroupImmediatelyBelowRoot _ => some .ruleGroupImmediatelyBelowRoot
  | _ => none

/-- The established named class of a String-pattern field-message refusal.

A line separator draws `INVALID_LINEBREAK` and a control character `INVALID_CHARACTERS`, as on a
rule's message ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-message-characters)); an odd dollar
count `WRONG_NUMBER_OF_DOLLARS`, a parameter other than the two tokens, the empty one included,
`INVALID_PARAMETER`, and an empty text the pairing class `MVK_ERROR_MESSAGE_AND_PATTERN_INVALID`
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates)). The parameter-body
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
