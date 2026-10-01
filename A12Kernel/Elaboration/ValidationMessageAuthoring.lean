import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.MessageGroupArgument
import A12Kernel.Elaboration.JavaOtherCategory

/-! # Checked authoring for bounded flat validation-message templates

Each parameter is decoded on its own by `MessageParameterSyntax` into the events the Kernel's parser
meets — every name resolved as it ends, a key's nesting refused, a fault where it stands — and its
form's check, and this module runs them in that order. A parameter's entity spec is the **shared path
grammar** the condition parser uses, so the decoder reads the same separators and hands the result to
the one existing field resolver rather than carrying a second lookup: a leading `/` is absolute, each leading `..` crosses one enclosing group
with an optional explicit turning point after the last of them, and `/` separates the remaining group
names from the field. A field is therefore addressable by its bare name when that name is unique, by
a path relative to the rule group, or absolutely when it lies outside the rule context.

A name that collides with a terminal is written in the grammar's **single-quote** escape, and the
quotes are erased before any semantic lookup, so an unnecessary quote is transparent. This producer's
quoting requirement is deliberately **narrower** than the condition language's: a set of terminals is
historically accepted unquoted inside an entity name, and the caller supplies both lists from the
language version it supports.

A field reference may carry an Enumeration **category** suffix, `->Name`, whose three gates are the
Kernel's own: a missing name, a field that is not an Enumeration, and a name that is not one of that
declaration's categories. It carries neither of the value suffix's extra gates, and combining it with the value suffix is a parse failure — the two really are alternatives. A **doubled** arrow is refused
only after the first category's kind and membership gates pass. Its diagnostic therefore depends on
that first name: an undeclared category or a non-Enumeration field stops at its own gate, while a
declared category reaches the trailing-syntax refusal. What a category access **renders** is measured: the category
token the field's current stored value maps to, so the checked part carries the declaration's own
mapping and the caller supplies only the stored token. An absent stored token renders as the empty
string, which is measured. A token the category does not map cannot arise, and that is now the
Kernel's rule rather than this fragment's convenience: a category's token list must have exactly as
many entries as the enum has values, paired by position, so every value carries exactly one token
([reconciliation](../../docs/SOURCES.md#src-2026-08-29-reconciliation)).

A field reference may finally carry a **semantic-index key**, `For "k"` or `For SomeField`, after any
value or category suffix — that order is the grammar's, not a preference. Its gate is on the
**semantic index**, not on the field: the condition must use that same index the same way, and the
keyed field itself need not be a condition operand at all. That freedom is **narrower than it first
measured**, and the correction is worth carrying here because the wide reading is the natural one.
A keyed parameter may name a field the condition never references, but only one such field — the
group's **declared index field** — so the admitted set is exactly the field the condition keys
together with that index field, and a *third* field of the same group, keyed identically, is
refused. What must match is the keyed group and key plus the displayed field being one of those two,
not the group's fields at large; a fixture whose group declares only those two cannot tell the two
readings apart, which is how both this project and a12-dmkits published the wide one
([checkpoint](../../docs/SOURCES.md#src-keyed-parameter-admits-the-index-field-only)). The unkeyed
spelling of a keyed field stays refused, so condition membership belongs to the unkeyed form alone,
and the pairing is exact in the other direction too: a keyed condition operand does not license an
unkeyed parameter.

No flat condition reads a field under a key, so the index gate refuses every keyed parameter here,
`MVK_INDEX_FOR_ERROR_TEXT_INVALID` in the name position and `INVALID_GROUP` in the group position,
both measured on the flat model; the grammar in front of that gate — suffix order, key spelling,
nesting, whitespace — answers first.

A parameter written `$#...$` occupies the **group position**, which is a different position from the
name one and resolves the same words differently: bare `$RootGroup$` is an entity lookup and refused,
while `$#RootGroup$` is admitted. Its argument is one of the two keyword shorthands for the endpoints
of the rule's ancestor chain or a group path, absolute or relative to the rule's group, so a bare word
names a group directly below it, falling back to a field's short name and never to a group's. The
argument is refused in the order the Kernel's parser meets it: each lexer or syntax fault where it
stands, a keyword or path's check once that alternative is complete, and a token left after it only
then. The named group
must be **available**: the rule's own group and its ancestors always are, and so is any group holding a
field the condition reads, which admits a read descendant or sibling and refuses the same group when
nothing in it is read. An absolute path resolves in two stages the Kernel reports apart, an undeclared
root ahead of availability, and its segments take the same quote escape as a name — but only an
unquoted word opens a keyword alternative, so quoting a terminal turns it back into an ordinary group
name. Two historic terminals keep their own refusal class, which the Kernel reports distinctly rather
than as an unknown group, and quoting removes that reading too.

One **non-field** parameter form is admitted: the Base Year terminal with an optional signed offset.
Its only static gate is that the model declares a Base Year, and the offset is applied at authoring
because nothing about it depends on the document.

Two **form-pointer** forms are admitted beside those, `<entity>.Vordruckzeile` and
`<entity>.Vordruckname`. They share the name position's entity spec and nothing else: their one gate
resolves that entity to a field, and the condition-membership requirement every other field form
carries **does not apply** — the Kernel admits both on a field the condition never references, which
is why the checked part has no membership witness to carry rather than an unset one. What either
renders is unmeasured and stays caller-supplied.

What stays outside is the rest of the parameter grammar: `index(...)`, the remaining non-field forms,
and repeatable targets. Two of the Kernel's own `.value` gates are unreachable in this
fragment rather than modelled — a star reference needs a repeatable path, and a declaration's "no
value validation" flag has no representation here.
-/

namespace A12Kernel

inductive ValidationMessageTemplateError where
  | emptyTemplate
  | lineSeparator
  | controlCharacter (character : Char)
  /-- A character outside the template's BMP repertoire. The Kernel refuses it **codelessly**, through
  the runtime formal class its message text belongs to rather than through a bracketed parameter key. -/
  | unsupportedCharacter (character : Char)
  /-- Preserve the other check's cause beside the repertoire refusal ([checkpoint](../../docs/SOURCES.md#src-message-repertoire-co-reporting)); an unsupported-fragment cause remains local rather than acquiring a Kernel class. -/
  | unsupportedCharacterWithError (character : Char)
      (cause : ValidationMessageTemplateError)
  | oddDollarCount
  /-- A parameter alternative this fragment does not model, `index(...)`. -/
  | invalidParameter (parameter : String)
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

  A root the model declares but leaves **empty** would be reported by the Kernel on the ordinary group
  class instead. `FlatModel` cannot express such a group, so no input reaching here separates the two;
  `FlatModel.hasGroupPath` owns that limit. -/
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
line separator keeps its own class ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)). -/
private def isControlCharacter (character : Char) : Bool :=
  isJavaOtherCategory character

/-- The template's repertoire is the **BMP**, the same bound a stored value's default charset applies.
An earlier printable-ASCII bound here was an over-refusal: fourteen BMP code points spanning Latin-1,
Latin Extended-A, currency, Greek, Cyrillic, CJK, punctuation and `U+FFFD` are admitted in message text,
while both supplementary-plane scalars measured are refused — and the Kernel reports that refusal without
a bracketed key, through the runtime formal class its message text belongs to. -/
private def isSupportedTemplateCharacter (character : Char) : Bool :=
  character.toNat < 0x10000

/-- Retain one local locator for the repertoire refusal; the Kernel reports the template once even with two offending characters ([checkpoint](../../docs/SOURCES.md#src-message-repertoire-co-reporting)). -/
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
  It is data for the same reason the terminals around it are: the Kernel's own terminal tables give
  `value` under an English condition language and `Wert` under German, and each draws a lexer refusal
  in the other's model ([checkpoint](../../docs/SOURCES.md#src-index-terminal-admitting-spelling)).
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

/-- Treat an exempt terminal as if the author had quoted it, then reuse the one existing
quote-provenance lowering. The exemption says exactly "no quote is needed here", so recording it as
quoted expresses that decision in the shared type instead of duplicating the lowering walk. -/
private def exemptQuoting (profile : ValidationMessageKeywordProfile)
    (name : AuthoredPathName) : AuthoredPathName :=
  if profile.unquotedTerminals.contains name.text then
    { name with quoted := true }
  else
    name

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
([checkpoint](../../docs/SOURCES.md#src-message-repertoire-co-reporting)) and beside the control class
on a field's pattern message ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)). -/
def withMessageRepertoire (source : String)
    (checked : Except ValidationMessageTemplateError α) :
    Except ValidationMessageTemplateError α :=
  match firstUnsupportedMessageTemplateCharacter? source, checked with
  | none, result => result
  | some character, .ok _ => .error (.unsupportedCharacter character)
  | some character, .error cause => .error (.unsupportedCharacterWithError character cause)

/-- The model a message parameter's name resolves in: the same declarations with the short-name tier
always on. Measured, a model whose flag is off still answers a message name by its model-wide short
name — ambiguous, unread, read, or form-pointed — while the same model's condition refuses a short name
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). -/
def FlatModel.messageNameModel (model : FlatModel) : FlatModel :=
  { model with fieldRefByShortNameAllowed := true }

/-- One checked field reference of a message parameter. `parameter` retains the authored spelling for
Explain, including any value suffix; `reference` is its decoded path, which is what resolved. -/
structure CheckedValidationMessageReference
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  parameter : String
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  resolved :
    model.messageNameModel.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
      .ok declaration
  conditionReferenced :
    condition.core.referencesField declaration.id = true

/-- One checked form-pointer parameter. It is deliberately **not** a `CheckedValidationMessageReference`
carrying a flag: the difference between the two is precisely that this one has no membership witness to
carry, and a shared record with an optional field would let a consumer read the exemption as missing
data rather than as the measured rule. -/
structure CheckedValidationMessageFormPointer
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  parameter : String
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  pointer : MessageFormPointer
  resolved :
    model.messageNameModel.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
      .ok declaration

/-- One checked category access: the field reference beside the resolved projection, with witnesses
that the projection belongs to *that* field's own Enumeration declaration and selects *that* category.
Together with the projection's own check this is the complete gate. -/
structure CheckedValidationMessageCategory
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  reference : CheckedValidationMessageReference model condition
  category : String
  projection : CheckedEnumerationProjection
  enumerationOwned :
    reference.declaration.enumeration = some projection.declaration.declaration
  categorySelected : projection.projectionRef = .category category

/-- Whether a message may name `group` in the group position: it is the rule's own group or one of its
ancestors, or it holds, at any depth, a field the condition reads. The second arm is why a descendant,
a sibling, and an intermediate group holding no read field directly are all nameable once the condition
reads below them, and why the same groups are refused when it does not
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-availability)). A
field is never available, because its own path is never a prefix of its group's. -/
def messageGroupAvailable (model : FlatModel) (condition : CheckedFlatCondition model)
    (group : GroupPath) : Bool :=
  GroupPath.isPrefixOf group condition.rowGroup ||
    model.fields.any fun declaration =>
      condition.core.referencesField declaration.id &&
        GroupPath.isPrefixOf group declaration.groupPath

/-- One admitted group-position parameter: the group the author named, beside the witnesses that it is
a representable path and that it is **available** to this rule's message. -/
structure CheckedValidationMessageGroup
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  parameter : String
  group : GroupPath
  valid : GroupPath.isValid group = true
  available : messageGroupAvailable model condition group = true

/-- Admit one resolved group under the two gates every argument shares: it is a representable path,
and it is available. Below the root gate, availability needs no separate existence test, because every
ancestor of a declared group and every group holding a declared field is itself declared — so a group
passing it is declared, and one failing it is refused whether or not the model declares it, which is
what a **declared** unread group and an unknown one sharing one refusal already says. -/
def admitMessageGroup {model : FlatModel}
    (condition : CheckedFlatCondition model) (parameter : String)
    (group : GroupPath) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageGroup model condition) :=
  if hValid : GroupPath.isValid group = true then
    if hAvailable : messageGroupAvailable model condition group = true then
      .ok { parameter, group, valid := hValid, available := hAvailable }
    else
      .error (.invalidGroupParameter parameter)
  else
    .error (.invalidGroupParameter parameter)

/-- Whether a path names a declared group or field. -/
def FlatModel.declaresEntityPath (model : FlatModel) (path : GroupPath) : Bool :=
  model.hasGroupPath path || model.fields.any (·.path == path)

/-- A relative group argument's parent walk and its check, which the Kernel runs when the walk's own
rule ends: a climb past the root first, then a turning point that does not name the group reached. -/
def walkMessageGroup {model : FlatModel} (condition : CheckedFlatCondition model)
    (parameter : String) (parents : Nat) (turningPoint : Option String) :
    Except ValidationMessageTemplateError GroupPath :=
  match GroupPath.walkUp condition.rowGroup parents with
  | .error _ => .error (.parameterAboveRoot parameter)
  | .ok base =>
      if base.matchesTurningPoint turningPoint then .ok base
      else .error (.turningPointMismatch parameter)

/-- Look one group-position argument up against the rule's own group, before its availability is
asked. An absolute path resolves in the two stages the Kernel reports apart: its first segment must
name a declared root group, and then the whole path must name an entity. The root gate belongs to the
absolute form alone — a keyword or a relative path resolves from the rule's own group, which
introduces no root the model might not declare. A relative path walks up first, refusing a climb past
the root, then checks its turning point against the group reached, and only then descends. A single
bare word that names nothing below the rule's group falls back to the short name of a **field**, the
only kind that lookup covers
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)). -/
def resolveMessageGroup {model : FlatModel} (condition : CheckedFlatCondition model)
    (parameter : String) : AuthoredMessageGroup → Except ValidationMessageTemplateError GroupPath
  -- The root shorthand is the top of the *rule's own* ancestor chain rather than a model-wide root.
  -- A model with two roots separates the two readings, and the rule's own chain is what the Kernel
  -- admits: under the second root the shorthand is accepted while the first root is refused.
  -- The shorthand carries a placement condition the other two spellings do not: a rule sitting
  -- directly in a root group may not use it. Measured on both carriers, and it is the gate the
  -- availability test cannot express, because a root group is trivially its own ancestor.
  | .ruleGroup =>
      if condition.rowGroup.length ≤ 1 then
        .error (.ruleGroupImmediatelyBelowRoot parameter)
      else
        .ok condition.rowGroup
  | .rootGroup => .ok (condition.rowGroup.take 1)
  | .absolute [] => .error (.invalidGroupParameter parameter)
  | .absolute (root :: rest) =>
      if !model.hasGroupPath [root] then
        .error (.unknownRootGroup parameter root)
      else if model.declaresEntityPath (root :: rest) then
        .ok (root :: rest)
      else
        .error (.invalidGroupParameter parameter)
  | .relative parents turningPoint path =>
      match walkMessageGroup condition parameter parents turningPoint with
      | .error error => .error error
      | .ok base =>
          if model.declaresEntityPath (base ++ path) then
            .ok (base ++ path)
          else
            match parents, path with
            | 0, [name] =>
                match model.fields.filter (·.name == name) with
                | [declaration] => .ok declaration.path
                | [] => .error (.invalidGroupParameter parameter)
                | _ => .error (.groupShortNameNotUnique parameter name)
            | _, _ => .error (.invalidGroupParameter parameter)

/-- Check one group-position argument: look it up, accept the group only if it is available, and only
then refuse a token left after the path. The lookup and availability are the alternative's check,
which the Kernel runs before it meets the end of the text: `$#He-ad$` and the unavailable `$#Side-x$`
draw the group class, and only `$#Head-x$` the syntax class
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events)). A
fault met after a complete parent walk waits for the walk's check and the lookup of the names consumed
before it, so `$#..Wrong/$` draws the turning-point class and `$#../Nope/$` the group class rather than
the truncated one. `keyCheck` is the outcome of a key's events, which the caller resolves on this
position's classes. -/
def checkMessageGroup {model : FlatModel} (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredMessageGroup)
    (remainder : MessageGroupRemainder := .none)
    (keyCheck : Except ValidationMessageTemplateError Unit := .ok ()) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageGroup model condition) :=
  match remainder, authored with
  | .afterWalk fault, .relative parents turningPoint names =>
      match walkMessageGroup condition parameter parents turningPoint with
      | .error error => .error error
      | .ok _ =>
          if names.isEmpty then .error (.parameterSyntax parameter fault)
          else
            match resolveMessageGroup condition parameter authored with
            | .error error => .error error
            | .ok _ => .error (.parameterSyntax parameter fault)
  | .afterWalk fault, _ => .error (.parameterSyntax parameter fault)
  -- The group's own lookup runs as its names end, the key's events after it, and the key's gate last:
  -- no flat condition reads a group under a key, so a keyed group that survives its key is refused
  -- `INVALID_GROUP` whatever its availability, measured on an admitted group.
  | .keyed _, _ =>
      match resolveMessageGroup condition parameter authored with
      | .error error => .error error
      | .ok _ =>
          match keyCheck with
          | .error error => .error error
          | .ok () => .error (.invalidGroupParameter parameter)
  | _, _ =>
      match resolveMessageGroup condition parameter authored with
      | .error error => .error error
      | .ok group =>
          match admitMessageGroup condition parameter group with
          | .error error => .error error
          | .ok access =>
              if remainder = .trailing then .error (.parameterSyntax parameter .unexpected)
              else .ok access

inductive CheckedValidationMessagePart
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  | text (value : String)
  | fieldName (reference : CheckedValidationMessageReference model condition)
  | fieldValue (reference : CheckedValidationMessageReference model condition)
  | fieldCategory (access : CheckedValidationMessageCategory model condition)
  /-- The Base Year with its authored offset already applied, beside the witnesses that the model
  declares that year and that the arithmetic is the authored one. -/
  | baseYear (offset year : Int)
      (declared : model.baseYear = some (year - offset))
  | group (access : CheckedValidationMessageGroup model condition)
  /-- A form-pointer parameter, whose resolved entity carries no membership witness because the
  Kernel requires none here. -/
  | formPointer (access : CheckedValidationMessageFormPointer model condition)

structure CheckedValidationMessageTemplate
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  source : String
  parts : List (CheckedValidationMessagePart model condition)

/-- One resolved name-bearing parameter position, carrying its resolution witness but **no**
membership requirement. -/
private structure ResolvedMessageEntity
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  resolved :
    model.messageNameModel.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
      .ok declaration

/-- Resolve one name-bearing parameter position to a declaration, or to the declared group it names.
This is the part a keyed parameter shares with an unkeyed one: measured, an unresolvable name is
refused for both, while a group is an entity each form refuses on its own class or not at all
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). -/
private def resolveMessageEntity (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError
      (ResolvedMessageEntity model condition ⊕ GroupPath) := do
  -- Every name-bearing position is checked, because a terminal may sit at any path level.
  let reference ← match ({ authored with
      turningPoint := authored.turningPoint.map (exemptQuoting profile)
      groups := authored.groups.map (exemptQuoting profile)
      field := exemptQuoting profile authored.field
    } : AuthoredFieldPath).lower profile.path with
    | .ok reference => pure reference
    -- The lexer forms an unquoted reserved word as a keyword, which no name slot takes, so the
    -- decoder has already refused it as this token; the lowering's own refusal agrees.
    | .error (.unquotedKeyword _) => throw (.parameterSyntax parameter .unexpected)
  match hResolved :
      model.messageNameModel.resolveNonrepeatableFieldUnchecked condition.rowGroup reference with
  | .error error =>
      match error.isGroupDisplaceableMiss, model.groupNamedBy? condition.rowGroup reference with
      | true, some group => pure (.inr group)
      | _, _ => throw (.reference parameter error)
  | .ok declaration => pure (.inl { reference, declaration, resolved := hResolved })

/-- Resolve one name-position entity spec as the parser resolves it when its names end: a path to a
field or a declared group, a bare parent walk to the group it reaches, and the rule-group terminal to
nothing, since the Kernel's name check skips it. A bare walk's climb past the root and its turning
point answer on the group position's classes, measured in the name position too. -/
private def resolveMessageSpec (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (parameter : String) :
    MessageEntitySpec →
      Except ValidationMessageTemplateError
        (Option (ResolvedMessageEntity model condition ⊕ GroupPath))
  | .ruleGroup => pure none
  | .walk parents turningPoint =>
      (some ∘ .inr) <$> walkMessageGroup condition parameter parents (turningPoint.map (·.text))
  | .path authored => some <$> resolveMessageEntity model profile condition parameter authored

private def resolveMessageReference (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model)
    (parameter : String) (spec : MessageEntitySpec) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageReference model condition) := do
  let entity ← match ← resolveMessageSpec model profile condition parameter spec with
    | some (.inl entity) => pure entity
    | some (.inr group) => throw (.groupInNamePosition parameter group)
    | none => throw (.ruleGroupParameter parameter)
  if hReferenced :
      condition.core.referencesField entity.declaration.id = true then
    pure {
      parameter
      reference := entity.reference
      declaration := entity.declaration
      resolved := entity.resolved
      conditionReferenced := hReferenced
    }
  else
    throw (.fieldNotReferenced parameter entity.declaration.id)

/-- Check the category after entity resolution and condition membership, including an empty name.

The [category-order checkpoint](../../docs/SOURCES.md#src-message-category-gate-order) separates
these prerequisite failures from the missing-name refusal. Kind and declared-category checks then
reuse the existing Enumeration projection boundary. -/
private def resolveMessageCategory
    (reference : CheckedValidationMessageReference model condition)
    (parameter category : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageCategory model condition) := do
  if category.isEmpty then throw (.missingCategoryName parameter)
  match hSource : reference.declaration.enumeration with
  | none =>
      throw (.categoryFieldNotEnumeration parameter reference.declaration.id)
  | some source =>
      match elaborateEnumeration source with
      | .error _ =>
          throw (.category parameter (.unknownCategory category))
      | .ok checked =>
          match checkEnumerationProjection checked (.category category) with
          | .error error => throw (.category parameter error)
          | .ok projection =>
              if hOwned : source = projection.declaration.declaration ∧
                  projection.projectionRef =
                    EnumerationProjectionRef.category category then
                .ok {
                  reference, category, projection
                  enumerationOwned := by rw [hSource, hOwned.1]
                  categorySelected := hOwned.2 }
              else
                throw (.category parameter (.unknownCategory category))

/-- Run a parameter's events in the parser's order, stopping at the first that fails. A name inside a
group-position key is looked up by the same check as anywhere else, but an unresolved one draws the
group class there, and the rule-group terminal as such a key fails inside the Kernel, which this
fragment leaves unclassed; a root, a parent walk and a turning point keep their classes
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). -/
private def runMessageEvents (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (parameter : String) (inGroupKey : Bool) :
    List MessageParameterEvent → Except ValidationMessageTemplateError Unit
  | [] => pure ()
  | .resolve spec :: rest => do
      if inGroupKey && spec == .ruleGroup then throw (.ruleGroupUnresolved parameter)
      match resolveMessageSpec model profile condition parameter spec with
      | .ok _ => pure ()
      | .error error =>
          throw (if inGroupKey && error matches .reference _ (.invalidEntity _) then
            .invalidGroupParameter parameter else error)
      runMessageEvents model profile condition parameter inGroupKey rest
  | .nestedKey :: _ => throw (.nestedSemanticIndex parameter)
  | .fault fault :: _ => throw (.parameterSyntax parameter fault)

/-- The field's own check, which the Kernel runs where the field's rule ends: the rule-group terminal
first, then the key's gate, then the membership gate and the suffix's gates. -/
private def checkMessageField (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (parameter : String)
    (entity : MessageEntitySpec) (suffix : MessageFieldSuffix) :
    Option MessageKeyHead →
      Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition)
  | some key =>
      if entity == .ruleGroup then throw (.ruleGroupParameter parameter)
      else if key == .entity .ruleGroup then throw (.ruleGroupUnresolved parameter)
      else throw (.keyNotInCondition parameter)
  | none => do
      let reference ← resolveMessageReference model profile condition parameter entity
      match suffix with
      | .none => pure (.fieldName reference)
      | .value => pure (.fieldValue reference)
      | .category name => pure (.fieldCategory (← resolveMessageCategory reference parameter name))

/-- Check one name-position parameter: its events, then its form's own check, then a fault the parser
meets at the end it requires. -/
private def checkMessageName (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (parameter : String)
    (decoded : DecodedMessageName) :
    Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition) := do
  runMessageEvents model profile condition parameter false decoded.events
  let part ← match decoded.form with
    | none => throw (.invalidParameter parameter)
    | some (.field entity suffix key) =>
        checkMessageField model profile condition parameter entity suffix key
    | some (.formPointer entity pointer) =>
        -- The one field form the Kernel admits on a field the condition never references, measured on
        -- six admitted spellings against the same model's own membership refusals.
        match ← resolveMessageSpec model profile condition parameter entity with
        | some (.inl entity) =>
            pure (.formPointer {
              parameter
              reference := entity.reference
              declaration := entity.declaration
              pointer
              resolved := entity.resolved })
        | some (.inr group) => throw (.groupInFormPointer parameter group)
        | none => throw (.ruleGroupUnresolved parameter)
    | some (.baseYear offset) =>
        match hDeclared : model.baseYear with
        | none => throw .noBaseYear
        | some base =>
            pure (.baseYear offset (base + offset) (by rw [hDeclared, Int.add_sub_cancel]))
    | some .indexField => throw (.invalidParameter parameter)
  match decoded.trailing with
  | some fault => throw (.parameterSyntax parameter fault)
  | none => pure part

/-- Check one parameter body on its own, as the Kernel's service parses each with a parser of its own.
The position marker selects the grammar: a body whose first token is `#` is the group position. -/
private def checkMessageParameter (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (parameter : String) :
    Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition) :=
  let keywords := profile.parameterKeywords
  match ParameterToken.ofParameter keywords parameter with
  | .hash :: rest =>
      match decodeMessageGroupTokens keywords rest with
      | .error (.syntax fault) => .error (.parameterSyntax parameter fault)
      | .error (.retired terminal) => .error (.retiredGroupTerminal parameter terminal)
      | .ok (authored, remainder) =>
          let keyCheck := match remainder with
            | .keyed events => runMessageEvents model profile condition parameter true events
            | _ => .ok ()
          .group <$> checkMessageGroup condition parameter authored remainder keyCheck
  | tokens =>
      checkMessageName model profile condition parameter
        (decodeMessageName keywords profile.nameTerminals tokens)

/-- Every part of a balanced template, each parameter checked independently. -/
private def checkMessageSegments (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) :
    List String →
      List (Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition))
  | [] => []
  | [text] => if text.isEmpty then [] else [.ok (.text text)]
  | text :: parameter :: rest =>
      (if text.isEmpty then [] else [.ok (.text text)]) ++
        [if parameter.isEmpty then .ok (.text "$")
          else checkMessageParameter model profile condition parameter] ++
        checkMessageSegments model profile condition rest

/-- Every refusal a rule message's template draws: the template-level gate that stops it, or one
refusal for each parameter that fails, in written order. The Kernel's service parses each parameter on
its own and reports each one's first failure, so `$Nope$ and $Nope2$` draws two
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). The codeless
repertoire finding is not among them; `withMessageRepertoire` keeps it beside the first. -/
def validationMessageTemplateRefusals (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (source : String) :
    List ValidationMessageTemplateError :=
  match validateMessageTemplateSource source with
  | .error error => [error]
  | .ok segments =>
      (checkMessageSegments model profile condition segments).filterMap fun
        | .error error => some error
        | .ok _ => none

/-- Check a rule message's template. A refused template reports its first refusal in written order;
`validationMessageTemplateRefusals` lists the rest. -/
def elaborateValidationMessageTemplate (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (source : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) :=
  let checked : Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) := do
    let segments ← validateMessageTemplateSource source
    pure { source, parts := ← (checkMessageSegments model profile condition segments).mapM id }
  withMessageRepertoire source checked

structure ValidationMessageInputs where
  fieldName : FieldId → MessageNameInput
  fieldValue : FieldId → MessageValueInput
  /-- The field's current stored token. The category mapping is applied by the checked part, not by
  the caller, because the mapping is the declaration's and is measured. -/
  fieldStoredToken : FieldId → Option String
  /-- What a form pointer renders. Caller-supplied because it is unmeasured; the field and which of
  the two terminals was written are both passed, so a caller need not re-derive either. -/
  formPointer : FieldId → MessageFormPointer → String

def CheckedValidationMessagePart.toRenderPart
    (inputs : ValidationMessageInputs) :
    CheckedValidationMessagePart model condition → MessageRenderPart
  | .text value => .text value
  | .fieldName reference => .fieldName (inputs.fieldName reference.declaration.id)
  | .fieldValue reference => .fieldValue (inputs.fieldValue reference.declaration.id)
  | .fieldCategory access =>
      .fieldCategory {
        categoryToken :=
          (inputs.fieldStoredToken access.reference.declaration.id).bind
            (access.projection.declaration.categoryTokenFor? access.category) }
  | .baseYear _ year _ => .baseYear year
  -- The measured rendering is the named group's repetition index in the firing row. Every group
  -- admissible here is nonrepeatable — see `MessageGroupInput` — so the index is the constant the
  -- Kernel renders for that case, and no caller-supplied bytes enter the message any more.
  | .group _ => .group { repetitionIndex := 1 }
  | .formPointer access =>
      .formPointer { text := inputs.formPointer access.declaration.id access.pointer }

def CheckedValidationMessageTemplate.toRenderPlan
    (template : CheckedValidationMessageTemplate model condition)
    (inputs : ValidationMessageInputs) : MessageRenderPlan :=
  { parts := template.parts.map (·.toRenderPart inputs) }

end A12Kernel
