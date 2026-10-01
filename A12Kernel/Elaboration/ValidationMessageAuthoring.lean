import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.MessageGroupArgument
import A12Kernel.Elaboration.JavaOtherCategory

/-! # Checked authoring for bounded flat validation-message templates

A parameter's entity spec is the **shared path grammar** the condition parser uses, so this fragment
decodes the same separators and hands the result to the one existing field resolver rather than
carrying a second lookup: a leading `/` is absolute, each leading `..` crosses one enclosing group
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

A semantic index needs a repeatable group, and this fragment's model is nonrepeatable, so a keyed
parameter is decoded and then refused as outside the fragment. The refusal is deliberately *not*
mapped to the Kernel's pairing class, because the Kernel's gate is a question this condition spine
cannot pose; the grammar in front of it — well-formedness, suffix order, key spelling, nesting — is
measured and modeled exactly.

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

What stays outside is the rest of the parameter grammar: the remaining non-field forms, the semantic
index suffix, and repeatable targets. Two of the Kernel's own `.value` gates are unreachable in this
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
  /-- A non-ASCII character inside a rule message's **parameter body**, which the surrounding text
  admits. Carries the parameter as authored; the Kernel additionally reports the character's 1-based
  offset. -/
  | parameterCharacter (parameter : String) (character : Char)
  | oddDollarCount
  | invalidParameter (parameter : String)
  /-- A name colliding with a terminal was written without the grammar's quote escape. -/
  | unquotedTerminalName (name : String)
  | reference (parameter : String) (error : ResolveError)
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
  /-- A relative group argument whose parent walk climbs past the root group, refused on the message
  route's own above-root class `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS`, distinct from the
  condition parser's. -/
  | groupParameterAboveRoot (parameter : String)
  /-- A relative group argument whose turning point does not name the group its parent walk reaches.
  The Kernel refuses it on its entity class `INVALID_ENTITY`, not on the group class. -/
  | groupTurningPointMismatch (parameter : String)
  /-- A group argument the parameter grammar refuses, carrying which of the Kernel's lexical and syntax
  classes the malformed shape falls into. Every fault but a token left after a complete path is
  reported before any group is looked up. Kept apart from `invalidGroupParameter`, which is a group
  **refusal** on a well-formed spelling. -/
  | groupParameterLexical (parameter : String) (fault : MessageGroupLexicalFault)
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
  /-- A semantic-index key is itself keyed. -/
  | nestedSemanticIndex (parameter : String)
  /-- A **well-formed** keyed parameter, refused because this fragment's model is nonrepeatable and so
  declares no semantic index for the key to name. This is the fragment's own boundary, not the
  Kernel's pairing class: the Kernel gates a keyed parameter on whether the **condition uses that same
  semantic index** *and* on the displayed field being either the condition's keyed field or the
  group's index field, neither of which a flat condition spine can pose. -/
  | semanticIndexUnsupported (parameter : String)
  deriving Repr, DecidableEq

/-- Which of the two form-pointer terminals a parameter carries. They are one form with two words
rather than two forms: the grammar gives them the same shape and the checker the same single gate, and
no measured row separates them anywhere ([checkpoint](../../docs/SOURCES.md#src-message-parameter-surface-and-iteration-gates)). -/
inductive MessageFormPointer where
  | line
  | name
  deriving Repr, DecidableEq

/-- Which suffix a keyed field reference carries. The grammar puts the suffix **before** the key, so
a keyed parameter is one shape with three suffix cases rather than three keyed shapes. -/
inductive MessageParameterSuffix where
  | none
  | value
  | category (name : String)
  deriving Repr, DecidableEq

/-- A key as the author spelled it: a decoded quoted literal, or a path to the keying field. -/
inductive AuthoredMessageKey where
  | literal (token : String)
  | field (reference : AuthoredFieldPath)
  deriving Repr, DecidableEq

private inductive ParsedValidationMessagePart where
  | text (value : String)
  /-- The authored spelling beside the path it decoded to. Both travel, because the spelling is what
  a diagnostic and an Explain consumer quote while the path is what resolves. -/
  | fieldName (parameter : String) (reference : AuthoredFieldPath)
  | fieldValue (parameter : String) (reference : AuthoredFieldPath)
  | fieldCategory (parameter : String) (reference : AuthoredFieldPath)
      (category : String)
  /-- A doubled category arrow. The first category is checked before the remaining syntax is refused,
  so this stays distinct from an undifferentiated parse failure. -/
  | fieldCategoryWithTrailingSyntax (parameter : String)
      (reference : AuthoredFieldPath) (category : String)
  | baseYear (offset : Int)
  /-- A group-position argument, beside the authored spelling a diagnostic quotes and what the parser
  still owes after the part whose check runs first. -/
  | group (parameter : String) (authored : AuthoredMessageGroup)
      (remainder : MessageGroupRemainder)
  /-- A form-pointer parameter. It shares the name position's entity spec and nothing else: its one
  gate resolves that entity to a field, and the condition-membership requirement every other field
  form carries does not apply. -/
  | formPointer (parameter : String) (reference : AuthoredFieldPath)
      (pointer : MessageFormPointer)
  /-- Any field form above, keyed. The suffix travels so one arm serves all three. -/
  | keyed (parameter : String) (reference : AuthoredFieldPath)
      (suffix : MessageParameterSuffix) (key : AuthoredMessageKey)

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

/-- A **parameter body** keeps a bound the template does not: printable ASCII together with the seven
German letters the `nameOhnePunkt` token grammar names. The Kernel reports anything else inside a
parameter through its lexer, naming the character and its 1-based offset, where the same character in
surrounding text is admitted — and the seven are measured on the near side of that line, since an
unknown name spelled with `ö` or `ß` reaches entity lookup while `é`, `€` and a CJK letter do not
([checkpoint](../../docs/SOURCES.md#src-message-template-character-repertoire)). The offset is a payload
this fragment does not track. -/
private def isBoundedAscii (character : Char) : Bool :=
  character.toNat ≤ 0x7e || messageNameGermanLetters.contains character

private def isBareName (name : String) : Bool :=
  !name.isEmpty && name.toList.all isMessageNameCharacter

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

/-- The words the group argument's decoder distinguishes, read off the profile: the path grammar's
reserved words, and the exemption from quoting that keeps a reserved word a name. -/
def ValidationMessageKeywordProfile.groupKeywords (profile : ValidationMessageKeywordProfile) :
    MessageGroupKeywords :=
  { reserved := profile.path.reserved, exempt := profile.unquotedTerminals,
    exemptNonFinal :=
      [profile.valueSuffixTerminal, profile.formLineTerminal, profile.formNameTerminal],
    ruleGroup := profile.ruleGroupTerminal, rootGroup := profile.rootGroupTerminal,
    retired := profile.retiredGroupTerminals, offset := profile.offsetGroupTerminals }

/-- Treat an exempt terminal as if the author had quoted it, then reuse the one existing
quote-provenance lowering. The exemption says exactly "no quote is needed here", so recording it as
quoted expresses that decision in the shared type instead of duplicating the lowering walk. -/
private def exemptQuoting (profile : ValidationMessageKeywordProfile)
    (name : AuthoredPathName) : AuthoredPathName :=
  if profile.unquotedTerminals.contains name.text then
    { name with quoted := true }
  else
    name

/-- Decode one authored segment's quote syntax into the shared name-with-provenance type. -/
private def decodeSegment (segment : String) : Option AuthoredPathName :=
  match segment.toList with
  | '\'' :: rest =>
      match rest.reverse with
      | '\'' :: inner =>
          let text := String.ofList inner.reverse
          if isBareName text then some { text, quoted := true } else none
      | _ => none
  | _ => if isBareName segment then some { text := segment } else none

/-- Decode a list of authored segments, failing as a whole if any segment is malformed. -/
private def decodeSegments : List String → Option (List AuthoredPathName)
  | [] => some []
  | segment :: rest => do
      let name ← decodeSegment segment
      pure (name :: (← decodeSegments rest))

/-- Split the up-run off a relative spec, returning the parent count, the optional turning point, and
the remaining segments. A name attached directly to a `..` is the turning point, so it ends the run;
one written after a `/` is an ordinary path element. -/
private def splitParentWalk :
    Nat → List String → Nat × Option String × List String
  | parents, ".." :: rest => splitParentWalk (parents + 1) rest
  | parents, segment :: rest =>
      if segment.startsWith ".." then
        (parents + 1, some (segment.drop 2).toString, rest)
      else
        (parents, none, segment :: rest)
  | parents, [] => (parents, none, [])

/-- Decode one parameter's entity spec into the shared structured path. Failure is the Kernel's own
single parse class rather than a family of shape classes, because that is what the parameter parser
reports for every malformed spec. -/
private def parseMessagePath (parameter spec : String) :
    Except ValidationMessageTemplateError AuthoredFieldPath :=
  -- The refusal quotes the whole authored parameter rather than the spec it was split from, because
  -- a diagnostic naming a fragment the author never wrote sends them looking in the wrong place.
  let segments := spec.splitOn "/"
  let malformed :=
    Except.error (ValidationMessageTemplateError.invalidParameter parameter)
  match segments with
  | [] => malformed
  | first :: rest =>
      if first.isEmpty then
        -- A leading separator is the absolute form, which needs at least one group and a field.
        match rest.reverse with
        | field :: group :: groups =>
            match decodeSegments (field :: group :: groups) with
            | some (field :: groups) =>
                .ok { base := .absolute, groups := groups.reverse, field }
            | _ => malformed
        | _ => malformed
      else
        let (parents, turningPoint, remaining) := splitParentWalk 0 segments
        match remaining.reverse, turningPoint with
        | field :: groups, none =>
            match decodeSegments (field :: groups) with
            | some (field :: groups) =>
                .ok { base := .relative parents, groups := groups.reverse, field }
            | _ => malformed
        | field :: groups, some turningPoint =>
            match decodeSegments (field :: groups), decodeSegment turningPoint with
            | some (field :: groups), some turningPoint =>
                .ok { base := .relative parents, turningPoint := some turningPoint
                      groups := groups.reverse, field }
            | _, _ => malformed
        | [], _ => malformed

/-- Decode the optional signed offset of a Base Year parameter. An absent offset is zero, which is
the same parameter with no calculation rather than a distinguished shape. -/
private def parseBaseYearOffset (remainder : String) : Option Int :=
  if remainder.isEmpty then
    some 0
  else
    match remainder.toList with
    | sign :: digits =>
        if digits.isEmpty || !digits.all Char.isDigit then none
        else
          let magnitude := (String.ofList digits).toNat!
          match sign with
          | '+' => some (Int.ofNat magnitude)
          | '-' => some (-Int.ofNat magnitude)
          | _ => none
    | [] => none

/-- Decode one group-position argument through the group argument's own decoder, carrying the
parameter as authored into the refusal. -/
private def parseMessageGroup (profile : ValidationMessageKeywordProfile)
    (parameter argument : String) :
    Except ValidationMessageTemplateError (AuthoredMessageGroup × MessageGroupRemainder) :=
  match decodeMessageGroupArgument profile.groupKeywords argument with
  | .error (.syntax fault) => .error (.groupParameterLexical parameter fault)
  | .error (.retired terminal) => .error (.retiredGroupTerminal parameter terminal)
  | .ok decoded => .ok decoded

/-- Decode a key's own spelling. A literal is the grammar's double-quoted token with `""` as its
escape; anything else is a path to the keying field, and an unquoted bare word therefore resolves as a
field rather than as a token. -/
private def parseMessageKey (parameter key : String) :
    Except ValidationMessageTemplateError AuthoredMessageKey :=
  if key.startsWith "\"" && key.endsWith "\"" && key.length ≥ 2 then
    .ok (.literal
      (((key.drop 1).dropEnd 1).toString.replace "\"\"" "\""))
  else
    .field <$> parseMessagePath parameter key

/-- Split the trailing key off a parameter, then decode the remaining spec's own suffix. The key
separator is the selected language's `For` terminal surrounded by spaces, which is the canonical
authored spelling; this fragment does not accept the grammar's whitespace-free forms. -/
private def splitMessageKey (profile : ValidationMessageKeywordProfile)
    (parameter : String) : String × Option String :=
  match parameter.splitOn s!" {profile.forTerminal} " with
  | [spec] => (spec, none)
  | spec :: rest => (spec, some (String.intercalate s!" {profile.forTerminal} " rest))
  | [] => (parameter, none)

/-- Recognize a form-pointer parameter, `<entity>.Vordruckzeile` or `<entity>.Vordruckname`. Returns
`none` when neither terminal ends the parameter, so the caller falls through to the ordinary forms —
the bare terminal without an entity is therefore an entity lookup and not a parameter of this shape,
which is what the Kernel does with it. -/
private def parseFormPointer (profile : ValidationMessageKeywordProfile)
    (parameter : String) :
    Option (Except ValidationMessageTemplateError ParsedValidationMessagePart) :=
  let attempt (terminal : String) (pointer : MessageFormPointer) :
      Option (Except ValidationMessageTemplateError ParsedValidationMessagePart) :=
    match parameter.splitOn ("." ++ terminal) with
    | [spec, ""] =>
        if spec.isEmpty then none
        else some ((.formPointer parameter · pointer) <$>
          parseMessagePath parameter spec)
    -- A further suffix after this one is refused by the Kernel, so it stays this fragment's single
    -- parse class rather than becoming a second admitted spelling.
    | [_, _] => some (.error (.invalidParameter parameter))
    | _ => none
  (attempt profile.formLineTerminal .line).orElse fun _ =>
    attempt profile.formNameTerminal .name

/-- Strip the value suffix, then decode the remaining entity spec as a path. The suffix is taken at
the end of the whole spec, which is this fragment's committed reading of a grammar that also lets a
trailing reserved word belong to the name itself. -/
private def parseParameter (profile : ValidationMessageKeywordProfile)
    (parameter : String) :
    Except ValidationMessageTemplateError ParsedValidationMessagePart :=
  -- The position marker is read first, because it selects a different grammar rather than a different
  -- form inside the name grammar. Nothing in the name grammar can begin with it.
  if parameter.startsWith "#" then
    (fun (authored, remainder) => ParsedValidationMessagePart.group parameter authored remainder) <$>
      parseMessageGroup profile parameter (parameter.drop 1).toString
  else
  -- The Base Year terminal is checked first: it is a terminal, so an unquoted occurrence is never a
  -- field name, and its offset syntax is not part of any path.
  match splitMessageKey profile parameter with
  | (spec, some keyText) =>
      if (splitMessageKey profile keyText).2.isSome then
        .error (.nestedSemanticIndex parameter)
      else do
        let key ← parseMessageKey parameter keyText
        -- The suffix sits before the key, so the spec is re-split by the ordinary rules.
        match spec.splitOn "->" with
        | [inner, category] =>
            pure (.keyed parameter (← parseMessagePath parameter inner)
              (.category category) key)
        | [_] =>
            match spec.splitOn ("." ++ profile.valueSuffixTerminal) with
            | [inner, ""] =>
                pure (.keyed parameter (← parseMessagePath parameter inner) .value
                  key)
            | [inner] =>
                pure (.keyed parameter (← parseMessagePath parameter inner) .none
                  key)
            | _ => throw (.invalidParameter parameter)
        | _ => throw (.invalidParameter parameter)
  | (_, none) =>
  if parameter.startsWith profile.baseYearTerminal then
    match parseBaseYearOffset
        ((parameter.drop profile.baseYearTerminal.length).toString) with
    | some offset => .ok (.baseYear offset)
    | none => .error (.invalidParameter parameter)
  else
  -- The two suffixes are alternatives in the grammar, and the arrow cannot occur inside a name, so
  -- splitting on it first is unambiguous. A doubled arrow retains its first category so the semantic
  -- gates can decide before the trailing syntax is refused.

  match parameter.splitOn "->" with
  | [spec, category] =>
      (.fieldCategory parameter · category) <$> parseMessagePath parameter spec
  | spec :: category :: _ =>
      (.fieldCategoryWithTrailingSyntax parameter · category) <$>
        parseMessagePath parameter spec
  | [_] =>
      -- The two form-pointer terminals are tried before the value suffix, which cannot occur inside
      -- either word, so the order is a reading convenience rather than a precedence claim. A suffix
      -- written *after* one is not an alternative spelling: the Kernel refuses it, so a nonempty tail
      -- falls through to this fragment's single parse class exactly as a doubled value suffix does.
      match parseFormPointer profile parameter with
      | some parsed => parsed
      | none =>
      match parameter.splitOn ("." ++ profile.valueSuffixTerminal) with
      | [spec, ""] => .fieldValue parameter <$> parseMessagePath parameter spec
      | [spec] => .fieldName parameter <$> parseMessagePath parameter spec
      | _ => .error (.invalidParameter parameter)
  | _ => .error (.invalidParameter parameter)

private def textPart (value : String) : List ParsedValidationMessagePart :=
  if value.isEmpty then [] else [.text value]

private def parseSegments (profile : ValidationMessageKeywordProfile) :
    List String →
      Except ValidationMessageTemplateError (List ParsedValidationMessagePart)
  | [] => .ok []
  | [text] => .ok (textPart text)
  | text :: parameter :: rest => do
      let parameterPart ←
        if parameter.isEmpty then
          pure (.text "$")
        else
          parseParameter profile parameter
      pure (textPart text ++ [parameterPart] ++ (← parseSegments profile rest))

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

/-- A rule message's parameter bodies, the odd-indexed pieces of a balanced split, carry the ASCII
bound its reference lexer imposes. A field's own message compares its parameters with two fixed tokens
instead, so a non-ASCII letter there is a wrong name, not a lexer failure
([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-count-placement-overlap-list-grid)). -/
private def checkRuleMessageParameterBodies (segments : List String) :
    Except ValidationMessageTemplateError Unit :=
  match segments.zipIdx.find? fun (segment, index) =>
      index % 2 == 1 && segment.toList.any (fun c => !isBoundedAscii c) with
  | some (segment, _) =>
      match segment.toList.find? (fun c => !isBoundedAscii c) with
      | some character => throw (.parameterCharacter segment character)
      | none => pure ()
  | none => pure ()

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

private def parseValidationMessageTemplate
    (profile : ValidationMessageKeywordProfile) (source : String) :
    Except ValidationMessageTemplateError (List ParsedValidationMessagePart) := do
  let segments ← validateMessageTemplateSource source
  checkRuleMessageParameterBodies segments
  parseSegments profile segments

/-- One checked field reference of a message parameter. `parameter` retains the authored spelling for
Explain, including any value suffix; `reference` is its decoded path, which is what resolved. -/
structure CheckedValidationMessageReference
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  parameter : String
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  resolved :
    model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
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
    model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
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
  | .error _ => .error (.groupParameterAboveRoot parameter)
  | .ok base =>
      if base.matchesTurningPoint turningPoint then .ok base
      else .error (.groupTurningPointMismatch parameter)

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
fault met after a complete parent walk waits only for the walk's check, so `$#..Wrong/$` draws the
turning-point class rather than the truncated one. -/
def checkMessageGroup {model : FlatModel} (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredMessageGroup)
    (remainder : MessageGroupRemainder := .none) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageGroup model condition) :=
  match remainder, authored with
  | .afterWalk fault, .relative parents turningPoint _ =>
      match walkMessageGroup condition parameter parents turningPoint with
      | .error error => .error error
      | .ok _ => .error (.groupParameterLexical parameter fault)
  | .afterWalk fault, _ => .error (.groupParameterLexical parameter fault)
  | _, _ =>
      match resolveMessageGroup condition parameter authored with
      | .error error => .error error
      | .ok group =>
          match admitMessageGroup condition parameter group with
          | .error error => .error error
          | .ok access =>
              if remainder = .trailing then .error (.groupParameterLexical parameter .unexpected)
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
    model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
      .ok declaration

/-- Resolve one name-bearing parameter position to a declaration. This is the part a keyed parameter
shares with an unkeyed one: measured, an unresolvable name is refused for both, while only the unkeyed
form additionally requires the condition to name the field. -/
private def resolveMessageEntity (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError
      (ResolvedMessageEntity model condition) := do
  -- Every name-bearing position is checked, because a terminal may sit at any path level.
  let reference ← match ({ authored with
      turningPoint := authored.turningPoint.map (exemptQuoting profile)
      groups := authored.groups.map (exemptQuoting profile)
      field := exemptQuoting profile authored.field
    } : AuthoredFieldPath).lower profile.path with
    | .ok reference => pure reference
    | .error (.unquotedKeyword name) => throw (.unquotedTerminalName name)
  match hResolved :
      model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference with
  | .error error => throw (.reference parameter error)
  | .ok declaration => pure { reference, declaration, resolved := hResolved }

private def resolveMessageReference (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageReference model condition) := do
  let entity ← resolveMessageEntity model profile condition parameter authored
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

private def checkMessageParts (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) :
    List ParsedValidationMessagePart →
      Except ValidationMessageTemplateError
        (List (CheckedValidationMessagePart model condition))
  | [] => .ok []
  | .text value :: rest => do
      pure (.text value :: (← checkMessageParts model profile condition rest))
  | .fieldName parameter reference :: rest => do
      pure (.fieldName
        (← resolveMessageReference model profile condition parameter reference) ::
        (← checkMessageParts model profile condition rest))
  | .fieldValue parameter reference :: rest => do
      pure (.fieldValue
        (← resolveMessageReference model profile condition parameter reference) ::
        (← checkMessageParts model profile condition rest))
  | .baseYear offset :: rest => do
      match hDeclared : model.baseYear with
      | none => throw .noBaseYear
      | some base =>
          pure (.baseYear offset (base + offset) (by
            rw [hDeclared, Int.add_sub_cancel]) ::
            (← checkMessageParts model profile condition rest))
  | .group parameter authored remainder :: rest => do
      pure (.group (← checkMessageGroup condition parameter authored remainder) ::
        (← checkMessageParts model profile condition rest))
  | .formPointer parameter reference pointer :: rest => do
      -- `resolveMessageEntity`, not `resolveMessageReference`: this is the one field form the Kernel
      -- admits on a field the condition never references, measured on six admitted spellings against
      -- the same model's own membership refusals.
      let entity ←
        resolveMessageEntity model profile condition parameter reference
      pure (.formPointer {
          parameter
          reference := entity.reference
          declaration := entity.declaration
          pointer
          resolved := entity.resolved
        } ::
        (← checkMessageParts model profile condition rest))
  | .keyed parameter reference _suffix key :: rest => do
      -- A keyed parameter is *not* subject to the condition-membership gate an unkeyed one carries,
      -- but its own admitted set is only the condition's keyed field plus the group's declared index
      -- field — not any field of the keyed group. Both name-bearing positions are still resolved as
      -- entities, because an unresolvable name is refused there rather than at the index gate — so
      -- these resolutions are kept for their refusals, and their results are unusable here. The
      -- decoded suffix is likewise unusable, since no part this fragment can build carries a key.
      discard <| resolveMessageEntity model profile condition parameter reference
      match key with
        | .literal _ => pure ()
        | .field keyReference =>
            discard <|
              resolveMessageEntity model profile condition parameter keyReference
      throw (.semanticIndexUnsupported parameter)
  | .fieldCategory parameter reference category :: rest => do
      let resolved ←
        resolveMessageReference model profile condition parameter reference
      pure (.fieldCategory
        (← resolveMessageCategory resolved parameter category) ::
        (← checkMessageParts model profile condition rest))
  | .fieldCategoryWithTrailingSyntax parameter reference category :: _ => do
      let resolved ←
        resolveMessageReference model profile condition parameter reference
      discard <| resolveMessageCategory resolved parameter category
      throw (.invalidParameter parameter)

def elaborateValidationMessageTemplate (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (source : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) :=
  let checked : Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) := do
    let parsed ← parseValidationMessageTemplate profile source
    pure { source, parts := ← checkMessageParts model profile condition parsed }
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
