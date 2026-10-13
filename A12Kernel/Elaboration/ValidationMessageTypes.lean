import A12Kernel.Elaboration.IndexMessageAuthoring
import A12Kernel.Elaboration.MessageGroupArgument
import A12Kernel.Elaboration.JavaOtherCategory
import A12Kernel.Elaboration.ErrorTextParameterAddressing

/-! Shared message-template errors, language profile and lexical gates. These gates also serve
field-pattern messages; checked rule-parameter resolution belongs to ValidationMessageAuthoring. -/

namespace A12Kernel

inductive ValidationMessageTemplateError where
  | emptyTemplate
  | lineSeparator
  | controlCharacter (character : Char)
  /-- A character outside the template's BMP repertoire. The Kernel refuses it **codelessly**, through
  the runtime formal class its message text belongs to rather than through a bracketed parameter key. -/
  | unsupportedCharacter (character : Char)
  /-- Preserve the other check's cause beside the repertoire refusal ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-repertoire-co-reporting)); an unsupported-fragment cause remains local rather than acquiring a Kernel class. -/
  | unsupportedCharacterWithError (character : Char)
      (cause : ValidationMessageTemplateError)
  | oddDollarCount
  /-- A parameter alternative the decoder does not represent. -/
  | invalidParameter (parameter : String)
  | indexParameter (parameter : String) (error : IndexMessageAuthoringError)
  | groupReferenceMode (parameter : String) (diagnostic : KernelStaticDiagnostic)
  | groupReferenceMetadataRequired (parameter : String)
  | reference (parameter : String) (error : ResolveError)
  /-- A name-position path that names a declared group rather than a field. The Kernel resolves the
  group and refuses it on the class of a field the condition does not read, `INVALID_FIELD`, even when
  the condition reads inside the group
  ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-refusals)),
  and a value or category suffix keeps that class
  ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). -/
  | groupInNamePosition (parameter : String) (group : GroupPath)
  /-- A form pointer whose entity names a declared group. The pointer skips the membership gate, so its
  refusal is the field requirement's own, `INVALID_FIELD_IN_PARAMETER`, and not the unread field's
  ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). -/
  | groupInFormPointer (parameter : String) (group : GroupPath)
  | fieldNotReferenced (parameter : String) (field : FieldId)
  /-- A value suffix refused by one of its two gates, `PARAM_VALUE_WITH_STARREFERENCE` or
  `INVALID_NO_VALUE_VALIDATION` (`valueAccessRefusal`). -/
  | valueAccess (parameter : String) (diagnostic : KernelStaticDiagnostic)
  /-- A category suffix was written with no category name after the arrow. -/
  | missingCategoryName (parameter : String)
  /-- A category suffix was applied to a field that is not an Enumeration declaration. -/
  | categoryFieldNotEnumeration (parameter : String) (field : FieldId)
  /-- The named category is not one this Enumeration declaration declares, or the declaration itself
  is ill-formed. Both arrive through the one existing Enumeration projection gate. -/
  | category (parameter : String) (error : EnumerationOperandError)
  /-- A group-position argument that names no available group: an unknown group below a declared root
  or below the rule's group, a field, or a declared group that is neither an ancestor of the rule's
  group nor holds a field the condition reads. They share this one refusal, which is the Kernel's own
  grouping — an **unknown root** is separated onto `unknownRootGroup`, and an ambiguous bare word onto
  `groupShortNameNotUnique`. -/
  | invalidGroupParameter (parameter : String)
  /-- A bare group word that names nothing directly below the rule's group and is the short name of
  more than one field, refused `ERROR_TEXT_FIELDNAME_NOT_UNIQUE`. The lookup covers fields only, so a
  group's short name is never found this way. -/
  | groupShortNameNotUnique (parameter name : String)
  /-- A parameter's parent walk, naming no segment after it or in the group position, climbs past the
  root group, refused on the message route's own above-root class
  `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS`, distinct from the condition parser's. -/
  | parameterAboveRoot (parameter : String)
  /-- A parameter's turning point does not name the group its parent walk reaches. The Kernel refuses
  it on its entity class `INVALID_ENTITY` in either position, not on the group class. -/
  | turningPointMismatch (parameter : String)
  /-- A parameter the parameter grammar refuses, carrying which of the Kernel's lexical and syntax
  classes the malformed shape falls into, at the point in the parser's events where it meets it. Kept
  apart from the refusals of a well-formed spelling. -/
  | parameterSyntax (parameter : String) (fault : MessageParameterFault)
  /-- The first segment of an absolute group argument names no declared root group. Root existence is
  a gate of its own, ahead of the lookup below it and of availability, and reported apart from both,
  so it fires whatever follows the root.

  A root the model declares but leaves **empty** is a declared root for this gate, so it reaches the
  ordinary group class instead (`FlatModel.declaresEmptyGroup`). -/
  | unknownRootGroup (parameter root : String)
  /-- A historic group terminal the Kernel still recognizes and refuses on the modern route. It stays
  distinct from `invalidGroupParameter` because the Kernel's own code is distinct. -/
  | retiredGroupTerminal (parameter terminal : String)
  /-- The `RuleGroup` shorthand written from a rule whose own group **is** the root group, refused
  `RULEGROUP_IMMEDIATELY_BELOW_ROOT`. The gate belongs to that one word: from the identical locus the
  root shorthand and the absolute spelling of that very group are both admitted, so the group is
  nameable and the position works — what is refused is the abbreviation whose meaning would there
  coincide with `RootGroup`. -/
  | ruleGroupImmediatelyBelowRoot (parameter : String)
  /-- A Base Year parameter was authored against a model that declares none. -/
  | noBaseYear
  /-- A semantic-index key that is an entity carrying a key of its own, refused only after every name in
  the parameter has resolved
  ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). -/
  | nestedSemanticIndex (parameter : String)
  /-- A keyed name-position parameter, refused `MVK_INDEX_FOR_ERROR_TEXT_INVALID` because no flat
  condition reads a field under a key. The Kernel admits a keyed parameter only on the condition's own
  keyed field or the group's index field under the key the condition uses, so a condition with no key
  admits none, which the flat model measures on a referenced field, a group and a literal containing
  the key terminal ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). -/
  | keyNotInCondition (parameter : String)
  /-- The rule-group terminal as a field, with or without a suffix or key, refused `INVALID_PARAMETER`
  by the field's own check before any other gate. -/
  | ruleGroupParameter (parameter : String)
  /-- The rule-group terminal where the Kernel's check expects a resolved entity: a form pointer's
  entity or a field's key. The Kernel fails there with `MVK_INTERNAL_ERROR`, a defect this fragment
  refuses on its own arm and does not model. -/
  | ruleGroupUnresolved (parameter : String)
  deriving Repr, DecidableEq

private def isLineSeparator (character : Char) : Bool :=
  character == '\n' || character == '\r' ||
    character.toNat == 0x2028 || character.toNat == 0x2029

/-- The Kernel's `INVALID_CHARACTERS` class over a message template: every code point Java's `\p{C}`
matches on JDK 21, control, format, private-use and unassigned alike, asked after the line gate so a
line separator keeps its own class ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-message-characters)). -/
private def isControlCharacter (character : Char) : Bool :=
  isJavaOtherCategory character

/-- The template's repertoire is the **BMP**, the same bound a stored value's default charset applies.
An earlier printable-ASCII bound here was an over-refusal: fourteen BMP code points spanning Latin-1,
Latin Extended-A, currency, Greek, Cyrillic, CJK, punctuation and `U+FFFD` are admitted in message text,
while both supplementary-plane scalars measured are refused — and the Kernel reports that refusal without
a bracketed key, through the runtime formal class its message text belongs to. -/
private def isSupportedTemplateCharacter (character : Char) : Bool :=
  character.toNat < 0x10000

/-- Retain one local locator for the repertoire refusal; the Kernel reports the template once even with two offending characters ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-repertoire-co-reporting)). -/
def firstUnsupportedMessageTemplateCharacter? (source : String) : Option Char :=
  source.toList.find? (fun character => !isSupportedTemplateCharacter character)

/-- The quoting rule for a rule-message parameter. A name colliding with one of the selected
language's terminals must be quoted, **except** for the terminals this producer has historically
accepted unquoted inside an entity name. The exemption belongs to this producer rather than to the
path grammar, which is why it does not live on `PathKeywordProfile`. -/
structure ValidationMessageKeywordProfile where
  path : PathKeywordProfile
  unquotedTerminals : List String := []
  /-- The selected language's spelling of the Base Year parameter terminal. It is data because the
  parameter grammar is bilingual and this project does not choose a language for the author. -/
  baseYearTerminal : String
  /-- The selected language's spelling of the semantic-index key terminal. -/
  forTerminal : String
  /-- The selected language's spelling of the **value suffix**, without the grammar's leading dot.
  It is data for the same reason the terminals around it are: the Kernel takes `value` under an
  English condition language and `Wert` under German, whatever the message's locale, and each draws a
  lexer refusal in the other's model on the `index(...)` terminal
  ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-index-german-suffix)).
  This was the one suffix the parser matched as a literal while every sibling was supplied, so a
  German model would have been read with the English word. -/
  valueSuffixTerminal : String
  /-- The selected language's spelling of the group position's root shorthand. -/
  rootGroupTerminal : String
  /-- The selected language's spelling of the group position's own-group shorthand. -/
  ruleGroupTerminal : String
  /-- The two form-pointer terminals. The Kernel's own bundles spell both identically in English and
  German, but they are data like every sibling terminal rather than literals, because the one exception
  to that discipline was a latent bilingual defect ([`LF166`](../../docs/LEAN-FINDINGS.md)). -/
  formLineTerminal : String
  formNameTerminal : String
  /-- The historic group terminals the Kernel recognizes in the group position and refuses on the
  modern route. Measured under the English condition language the set is `Zeile` and `Usb`; whether it
  is selected by language at all is unmeasured, so the caller supplies it like the other terminals. -/
  retiredGroupTerminals : List String := []
  /-- The retired group terminals that take a signed offset, `$#Zeile-1$`. Measured on `Zeile` under the
  English condition language, where `Usb` takes none. -/
  offsetGroupTerminals : List String := []
  deriving Repr, DecidableEq

/-- The en_US parameter terminals, read off the Kernel's own English terminal bundle, with the seven
this producer historically accepts unquoted inside an entity name; only `For`, `RuleGroup` and
`BaseYear` therefore need the quote escape
([parameter surface](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates)). -/
def ValidationMessageKeywordProfile.english : ValidationMessageKeywordProfile := {
  path := { reserved := ["For", "index", "RootGroup", "RuleGroup", "Usb", "Vordruckname",
    "Vordruckzeile", "BaseYear", "value", "Zeile"] }
  unquotedTerminals := ["value", "RootGroup", "Zeile", "Usb", "index", "Vordruckzeile", "Vordruckname"]
  baseYearTerminal := "BaseYear"
  forTerminal := "For"
  valueSuffixTerminal := "value"
  rootGroupTerminal := "RootGroup"
  ruleGroupTerminal := "RuleGroup"
  formLineTerminal := "Vordruckzeile"
  formNameTerminal := "Vordruckname"
  retiredGroupTerminals := ["Zeile", "Usb"]
  offsetGroupTerminals := ["Zeile"] }

/-- The de_DE parameter terminals, read off the Kernel's German terminal bundle in the same grammar
roles; a German condition language selects them whatever the message's locale, and the retired
terminals are shared ([German terminals](../../docs/sources/message-and-pointer-probes.md#src-german-condition-language-terminals),
[index suffix](../../docs/sources/message-and-pointer-probes.md#src-index-german-suffix)). -/
def ValidationMessageKeywordProfile.german : ValidationMessageKeywordProfile := {
  path := { reserved := ["Fuer", "index", "LfdNr", "RegelKontext", "Usb", "Vordruckname",
    "Vordruckzeile", "Referenzjahr", "Wert", "Zeile"] }
  unquotedTerminals := ["Wert", "LfdNr", "Zeile", "Usb", "index", "Vordruckzeile", "Vordruckname"]
  baseYearTerminal := "Referenzjahr"
  forTerminal := "Fuer"
  valueSuffixTerminal := "Wert"
  rootGroupTerminal := "LfdNr"
  ruleGroupTerminal := "RegelKontext"
  formLineTerminal := "Vordruckzeile"
  formNameTerminal := "Vordruckname"
  retiredGroupTerminals := ["Zeile", "Usb"]
  offsetGroupTerminals := ["Zeile"] }

/-- The words the parameter decoder distinguishes, read off the profile: the path grammar's reserved
words, and the exemption from quoting that keeps a reserved word a name. -/
def ValidationMessageKeywordProfile.parameterKeywords (profile : ValidationMessageKeywordProfile) :
    MessageParameterKeywords :=
  { reserved := profile.path.reserved, exempt := profile.unquotedTerminals,
    exemptNonFinal :=
      [profile.valueSuffixTerminal, profile.formLineTerminal, profile.formNameTerminal],
    ruleGroup := profile.ruleGroupTerminal, rootGroup := profile.rootGroupTerminal,
    retired := profile.retiredGroupTerminals, offset := profile.offsetGroupTerminals,
    forTerminal := profile.forTerminal }

/-- The name position's own terminals, read off the profile. -/
def ValidationMessageKeywordProfile.nameTerminals (profile : ValidationMessageKeywordProfile) :
    MessageNameTerminals :=
  { baseYear := profile.baseYearTerminal, valueSuffix := profile.valueSuffixTerminal,
    formLine := profile.formLineTerminal, formName := profile.formNameTerminal }

private def validateMessageTemplatePrefix (source : String) :
    Except ValidationMessageTemplateError Unit := do
  if source.isEmpty then throw .emptyTemplate
  match source.toList.find? isLineSeparator with
  | some _ => throw .lineSeparator
  | none => pure ()
  match source.toList.find? isControlCharacter with
  | some character => throw (.controlCharacter character)
  | none => pure ()

private def validateMessageTemplateSegments (source : String) :
    Except ValidationMessageTemplateError (List String) := do
  if source.toList.count '$' % 2 != 0 then throw .oddDollarCount
  pure (source.splitOn "$")

/-- The lexical gates both producers share: the line and control gates, then dollar parity. The
repertoire refusal is not one of them; each producer adds it with `withMessageRepertoire`, since it
stands beside these failures. -/
def validateMessageTemplateSource (source : String) :
    Except ValidationMessageTemplateError (List String) := do
  validateMessageTemplatePrefix source
  validateMessageTemplateSegments source

/-- Add the codeless repertoire refusal to a producer's result, keeping the producer's own first
failure beside it. It stands beside a named class on a rule's message
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-repertoire-co-reporting)) and beside the control class
on a field's pattern message ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-message-characters)). -/
def withMessageRepertoire (source : String)
    (checked : Except ValidationMessageTemplateError α) :
    Except ValidationMessageTemplateError α :=
  match firstUnsupportedMessageTemplateCharacter? source, checked with
  | none, result => result
  | some character, .ok _ => .error (.unsupportedCharacter character)
  | some character, .error cause => .error (.unsupportedCharacterWithError character cause)

end A12Kernel
