/-! # Catalog keys the Kernel declares but never reports

[`StaticDiagnostic.lean`](StaticDiagnostic.lean) admits a class only once this project has established that the Kernel *reports* it. This module records the complement for one measured slice: catalog keys that exist, carry a localized message, and are reachable by name from a consumer's message bundle, yet correspond to no diagnostic any Kernel code path emits.

The distinction matters to three consumer profiles that the positive vocabulary alone misleads. A Qualify consumer enumerating the Kernel's catalogs to build its own diagnostic type would give each of these a constructor and then wait forever for an input that produces one. An Explain consumer would carry a rendering path it can never exercise. And an importer deciding whether a rejected model is repairable would branch on a class no rejection can carry. Each of those is a real cost paid for a key that looks exactly like its live neighbours in the `.properties` file, because in the file it *is* exactly like them.

Two mechanisms produce such a key, and they are kept apart because they behave differently:

* **Declared, never raised.** The constant is declared in its error-type enum and has catalog entries, but no source location passes it to a reporting call. Nothing about the key is wrong; the check it was written for was never wired, or was removed and left its vocabulary behind. One of these has an observed consequence: `NO_VORDRUCKZEILE` names the intended refusal for an error-text parameter addressing a field with no form-line, and the unguarded path throws an internal error instead ([checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-unraised-diagnostic-vocabulary)).
* **Interpolated label only.** The constant is live, but it is not a diagnostic. It resolves through the Kernel's bare-message lookup to supply the operand *name* interpolated into some other diagnostic's text. A consumer will see its words inside another message and will never see it as a class.

**Claim scope.** The status below is measured by exhaustive search of the `../a12-kernel` checkout — every tracked and build-generated `.java`, `.kt`, and `.xml` file, plus each key's own catalogs — for any occurrence that is not the declaration itself. It is a statement about that source tree, not a proof that no configuration of the running engine can emit these keys; a reflective or string-assembled reference would not be found by it, and none was observed. Four of the eight never-raised keys are independently marked out of scope by the Kernel's own analyst documentation, which is a second mechanism agreeing rather than the same reading twice.

This vocabulary carries **no** rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md): the key is a functional identifier a conforming consumer must compute, while the sentence beside it in the catalog is the Kernel's own localization resource.
-/

namespace A12Kernel

/-- Why a declared catalog key never reaches a consumer as a diagnostic class. -/
inductive UnraisedReason where
  /-- Declared in an error-type enum with catalog entries, but passed to no reporting call. -/
  | declaredNeverRaised
  /-- Live, but resolved through the bare-message lookup to name an operand inside another
  diagnostic's text rather than to classify a refusal of its own. -/
  | interpolatedLabelOnly
  deriving Repr, DecidableEq

/-- A catalog key this project has established the Kernel never reports as a diagnostic class. Constructor names are local; `catalogKey` carries the exact identity a consumer would have compared against. -/
inductive UnraisedDiagnostic where
  /-- A rule marks a field as calculated while deriving no calculation for it. The live neighbour
  `MVK_GROUP_AS_CALCULATED_FIELD` in the same enum *is* raised, so this is not a dead family. -/
  | calculationFieldAndNoCalculationRule
  /-- A character of the model's declared character set is unusable in the generator's target
  language. Its catalog sibling `MVK_ENUM_VALUE_WITH_INVALID_CHARACTER` is raised, and reaches
  ordinary authoring through the consistency check's code-generation rule. -/
  | invalidCharInRestrictedCharset
  /-- An operand fails a named predefined-type constraint. The live custom-field-type route reports
  `MVK_NO_STRING_OR_ENUM_OR_EXT_ENUM` for the operand kind and defers the type name itself to the
  runtime client SPI, which is why nothing static needs this key. -/
  | invalidPredefinedType
  /-- No resource bundle supplies the formal-error messages for a target language. -/
  | noFormalErrorResourceBundle
  /-- A rule group does not contain the rule's error field. -/
  | notOnErrorfieldPath
  /-- The singular-spelled companion of the live `MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED`. Only
  the plural form is raised; the two differ by the `_NO_FIELD` suffix alone, which is exactly the
  shape that invites a consumer to treat them as one class with two spellings. -/
  | onlyStringEnumNumberCmpDateAllowedNoField
  /-- An error-text parameter addresses a form name inside a hierarchical model. -/
  | noVordrucknameInH
  /-- An error-text parameter addresses a field that specifies no form line. The observed
  consequence of nothing raising it is an internal error from the unguarded path. -/
  | noVordruckzeile
  /-- Names the error-text parameter position inside another error-text diagnostic. -/
  | errorTextParameter
  /-- Wraps a field-level error-text finding into the message that names the offending field. -/
  | fieldInvalidPrefix
  /-- Names the category-access operand inside a parser diagnostic. -/
  | categoryRefOp
  /-- Names the condition itself inside the parser's default error-strategy message. -/
  | condition
  /-- Names the field-value operand inside a parser diagnostic. -/
  | fieldRefOp
  /-- Names the semantic-index operand inside a parser diagnostic. -/
  | semanticIndexRefOp
  /-- Names the offending rule and language inside an error-text diagnostic. -/
  | ruleErrortextWrong
  deriving Repr, DecidableEq

namespace UnraisedDiagnostic

/-- The exact catalog identity, which is what a consumer compares against. -/
def catalogKey : UnraisedDiagnostic → String
  | .calculationFieldAndNoCalculationRule => "MVK_CALCULATION_FIELD_AND_NO_CALCULATION_RULE"
  | .invalidCharInRestrictedCharset => "MVK_INVALID_CHAR_IN_RESTRICTED_CHARSET"
  | .invalidPredefinedType => "MVK_INVALID_PREDEFINED_TYPE"
  | .noFormalErrorResourceBundle => "MVK_NO_FORMAL_ERROR_RESOURCE_BUNDLE"
  | .notOnErrorfieldPath => "MVK_NOT_ON_ERRORFIELD_PATH"
  | .onlyStringEnumNumberCmpDateAllowedNoField =>
      "MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED_NO_FIELD"
  | .noVordrucknameInH => "NO_VORDRUCKNAME_IN_H"
  | .noVordruckzeile => "NO_VORDRUCKZEILE"
  | .errorTextParameter => "ERROR_TEXT_PARAMETER"
  | .fieldInvalidPrefix => "FIELD_INVALID_PREFIX"
  | .categoryRefOp => "MVK_CATEGORY_REF_OP"
  | .condition => "MVK_CONDITION"
  | .fieldRefOp => "MVK_FIELD_REF_OP"
  | .semanticIndexRefOp => "MVK_SEMANTIC_INDEX_REF_OP"
  | .ruleErrortextWrong => "RULE_ERRORTEXT_WRONG"

/-- Which of the two mechanisms keeps this key out of a consumer's diagnostic stream. -/
def reason : UnraisedDiagnostic → UnraisedReason
  | .calculationFieldAndNoCalculationRule => .declaredNeverRaised
  | .invalidCharInRestrictedCharset => .declaredNeverRaised
  | .invalidPredefinedType => .declaredNeverRaised
  | .noFormalErrorResourceBundle => .declaredNeverRaised
  | .notOnErrorfieldPath => .declaredNeverRaised
  | .onlyStringEnumNumberCmpDateAllowedNoField => .declaredNeverRaised
  | .noVordrucknameInH => .declaredNeverRaised
  | .noVordruckzeile => .declaredNeverRaised
  | .errorTextParameter => .interpolatedLabelOnly
  | .fieldInvalidPrefix => .interpolatedLabelOnly
  | .categoryRefOp => .interpolatedLabelOnly
  | .condition => .interpolatedLabelOnly
  | .fieldRefOp => .interpolatedLabelOnly
  | .semanticIndexRefOp => .interpolatedLabelOnly
  | .ruleErrortextWrong => .interpolatedLabelOnly

/-- The Kernel message catalog the key is declared in, which is where a consumer enumerating catalogs would have picked it up. -/
def catalog : UnraisedDiagnostic → String
  | .calculationFieldAndNoCalculationRule => "vk_calc_error_messages"
  | .invalidCharInRestrictedCharset => "vk_codegen_no_meta_model_ckecks_error_messages"
  | .invalidPredefinedType => "vk_parser_error_messages"
  | .noFormalErrorResourceBundle => "vk_codegen_no_meta_model_ckecks_error_messages"
  | .notOnErrorfieldPath => "vk_parser_error_messages"
  | .onlyStringEnumNumberCmpDateAllowedNoField => "vk_parser_error_messages"
  | .noVordrucknameInH => "vk_service_errortext_error_messages"
  | .noVordruckzeile => "vk_service_errortext_error_messages"
  | .errorTextParameter => "vk_service_errortext_error_messages"
  | .fieldInvalidPrefix => "vk_service_errortext_error_messages"
  | .categoryRefOp => "vk_parser_error_messages"
  | .condition => "vk_parser_error_messages"
  | .fieldRefOp => "vk_parser_error_messages"
  | .semanticIndexRefOp => "vk_parser_error_messages"
  | .ruleErrortextWrong => "vk_service_errortext_error_messages"

/-- Every key in the measured slice, so a consumer can subtract it from a catalog enumeration. -/
def all : List UnraisedDiagnostic :=
  [.calculationFieldAndNoCalculationRule, .invalidCharInRestrictedCharset,
    .invalidPredefinedType, .noFormalErrorResourceBundle, .notOnErrorfieldPath,
    .onlyStringEnumNumberCmpDateAllowedNoField, .noVordrucknameInH, .noVordruckzeile,
    .errorTextParameter, .fieldInvalidPrefix, .categoryRefOp, .condition, .fieldRefOp,
    .semanticIndexRefOp, .ruleErrortextWrong]

/-- The keys a consumer must not expect from any Kernel code path. -/
def neverRaised : List UnraisedDiagnostic := all.filter (fun d => d.reason == .declaredNeverRaised)

/-- The keys whose words a consumer will meet inside another diagnostic's text, never as a class. -/
def labelsOnly : List UnraisedDiagnostic := all.filter (fun d => d.reason == .interpolatedLabelOnly)

end UnraisedDiagnostic

end A12Kernel
