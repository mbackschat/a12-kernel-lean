# 11 — Error-message interpolation and CustomCondition (§13 + §14)

Two areas. Interpolation turns an already-fired message's authored template into its end-user text; apart from the keyed-row fault of A.11, it is a pure render step that changes neither the firing nor its type. `CustomCondition` is the rule language's host-code predicate hook. The separate registered [custom field-type validator](06-strings-and-enumerations.md#a3-custom-field-type-validation) classifies stored cells during formal observation and is not a `CustomCondition`.

Section numbers inside this chapter are written A.n and B.n; a bare `§n` in a link label is the taxonomy number of the linked chapter.

---

## Part A — §13 Error-message interpolation

**An authored template carries producer-specific parameters, which are resolved against the evaluated document into the end-user text.** Five producers carry a template, and they do not share one grammar:

| Producer | Template | Grammar and static gates | Rendering |
|---|---|---|---|
| validation rule | the rule's error text | A.1–A.10 | A.11 |
| computation | the computation's message, which is the message of the validation rule the computation generates | as a validation rule's, A.12 | A.11, A.12 |
| String pattern | the String field's invalid-value text | two fixed tokens, A.13 | A.13 |
| Enumeration | the Enumeration field's invalid-value text | the String-pattern grammar, A.13 | A.13 |
| requiredness | the required field's own text | never checked, A.13 | A.13 |

The first two are **rule-owned**, the other three **field-owned**.

### A.1 The rule-owned template: characters, dollars and locales

**A template is read by splitting it at each `$`.** The pieces alternate text, parameter, text and so on, starting with text, so every `$` opens or closes a parameter and the count of `$` must be even. An empty parameter piece, `$$` where a parameter would open, is one literal `$`. Inside a parameter the first `$` closes it and the second opens the next, so `see $Premium$$Adjuster$` is **two** parameters, and A12 answers it with two diagnostics rather than one; `see $Prem$$ium$` is likewise the two names `Prem` and `ium`, not the single name `Prem$ium`. Each parameter is parsed and checked on its own (A.3, A.4), and each failing parameter reports its own first refusal, in written order.

**Character gates come in three tiers, and only the innermost is ASCII.** The whole template's repertoire is the **BMP**: Latin-1, Latin Extended-A, currency, Greek, Cyrillic, CJK, punctuation, NBSP and `U+FFFD` are admitted, while both supplementary-plane scalars measured are refused. That repertoire refusal is codeless and conveys the runtime formal charset class. The named template gates then run in this order, each withholding every gate after it:

| Order | Gate | Class | Members |
|---|---|---|---|
| 1 | line break | `INVALID_LINEBREAK` | exactly LF, CR, `U+2028` and `U+2029` |
| 2 | control character | `INVALID_CHARACTERS` | every code point Java's `\p{C}` matches: control, format, private use, unassigned and a lone surrogate |
| 3 | dollar parity | `WRONG_NUMBER_OF_DOLLARS` | an odd count of `$` |
| 4 | each parameter on its own | its own class, A.3–A.10 | — |

- Measured `\p{C}` members: C0, tab, DELETE, the C1 block with `NEL`, soft hyphen, zero-width space, `U+FEFF`, `U+200E`, `U+E000` and the unassigned `U+0378`. Which code points are unassigned is the running JDK's Unicode version's; the rows were measured on JDK 21.
- The control gate is asked of a code point, so a supplementary character inside `\p{C}` (`U+F0000`, `U+E0001`) draws the repertoire refusal and `INVALID_CHARACTERS`, one outside it (`U+1F600`) the repertoire refusal alone, and a lone surrogate both.
- Withholding, measured: beside a tab, a zero-width space or a line separator an unknown name draws no `INVALID_ENTITY`, and beside a zero-width space an unclosed parameter draws no `WRONG_NUMBER_OF_DOLLARS`. That dollar parity withholds the parameter classes is measured on the String-pattern producer (A.13); for a rule-owned template it is source reading, unmeasured.
- A computation's message draws the same classes on the four rows measured there: LF and `U+2029` draw `INVALID_LINEBREAK`, a tab and `U+FEFF` `INVALID_CHARACTERS`. The field-owned producers' character gates are A.13's.
- The third tier, a parameter body's narrower character bound, belongs to the parameter lexer (A.3).

**The repertoire refusal coexists with named failures.** On the measured validation-rule carrier, a supplementary-plane scalar accompanies a separate linebreak, control-character, odd-dollar, unknown-entity or parameter-lexer diagnostic. The retained envelopes list the codeless finding first and the named finding second; that reporting order does not establish an internal check execution order. A valid parameter does not suppress the repertoire refusal, and two offending scalars still produce one codeless finding. A projection containing only named codes loses this distinction and cannot establish an exclusive failure priority.

**The checker examines only the locales the model declares, each by its last entry.** A parameter error in a declared locale is rejected, while the identical text under an undeclared locale is silently accepted and stored, because that locale is not examined; a well-formed undeclared-locale text is observationally identical at this gate. This holds for every checker class measured: a control character, an odd dollar count and `$BaseYear$` without a Base Year are each admitted under an undeclared `fr_FR`. Of two entries for one declared locale only the last is examined, so an unknown parameter in the first entry is admitted and in the second draws `INVALID_ENTITY`. An entry belongs to the declared locale its parsed locale equals ([01 §1.1](01-data-model.md#member-binding)): on a rule's message an `en-US` entry answers a declared `en_US` and the reverse, while an `en_US` entry does not answer a declared `en`; other carriers are unmeasured, beside the hint list's repeated locale of [01 §1.2](01-data-model.md#defects-that-leave-no-model). A rule's message written for an undeclared locale draws no refusal; [01 §1.1](01-data-model.md#11-the-two-special-model-level-configurations) owns the model's other texts. Authoring tools may deliberately reject undeclared locale keys before calling the Kernel, but that stricter instrument policy is not Kernel semantics.

**Every declared locale must be answered.** `RULE_HAS_NO_ERRORTEXT` asks after every declared locale, an answered one beside it included, and is drawn once for each locale it finds without a text, on a rule and on a computation alike:

| Declared `en_US` and `de_DE`, with `en_US` answered | Classes |
|---|---|
| an empty `de_DE` text, or no `de_DE` entry | `MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING` and `RULE_HAS_NO_ERRORTEXT` |
| a whitespace-only `de_DE` text | `MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING` alone |
| an answered `en_US` entry followed by an empty `en_US` entry | both, the last entry being the one judged |

With **no declared locale** no locale is answered and none is asked: a rule draws `MVK_ERROR_MESSAGE_MISSING` whether or not it writes a text, beside the model's own `MVK_SUPP_LANGUAGES_MISSING`, and no `RULE_HAS_NO_ERRORTEXT`.

Sources: [inbound 2026-10-29a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29a), [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [message-parameter decoder checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder), [character-repertoire checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-template-character-repertoire), [inbound 2026-09-26m message characters](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-message-characters), [repertoire co-reporting checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-repertoire-co-reporting), [inbound 2026-09-26m model texts](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-model-texts), [inbound 2026-09-25 message withheld](../docs/sources/inbound-handbacks.md#inbound-2026-09-25-message-withheld), [inbound KF558 multiplicity](../docs/sources/inbound-handbacks.md#src-inbound-kf558-multiplicity), [inbound 2026-09-25b message](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-message), [sort-list capacity supplement](../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity).

### A.2 Which error-text classes a refused declaration withholds

**A refused DSL member withholds the error-text checker's classes, and the message's presence classes stand.** When the owning declaration's condition or operation draws a class of its own, the classes the rule error-text checker draws are withheld, while `MVK_ERROR_MESSAGE_MISSING` and `MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING` are reported beside the member's class. The split follows the checker, not the `MVK_` prefix: a parameter's parse class and the index-key class are withheld with the unprefixed ones.

| Withheld, measured | Standing |
|---|---|
| a control character's `INVALID_CHARACTERS`, an unread parameter's `INVALID_FIELD`, an odd count's `WRONG_NUMBER_OF_DOLLARS`, a descendant group parameter's `INVALID_GROUP`, a Base-Year parameter's `NO_BASE_YEAR` in a model without one, a parameter's parse class `MVK_UNEXPECTED_TOKEN`, a key on an unindexed field's `MVK_INDEX_FOR_ERROR_TEXT_INVALID`, and `RULE_HAS_NO_ERRORTEXT` | `MVK_ERROR_MESSAGE_MISSING`, `MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING` |

The member classes measured to withhold them:

| Carrier | Member classes | Measured withholding |
|---|---|---|
| rule | a text that does not parse, `MVK_INVALID_ENTITY` for a name that does not resolve, `MVK_LEXER_STANDARD_ERROR`, `MVK_EXPECTED_TOKEN_NOT_FOUND`, `MVK_FIELDNAME_NOT_UNIQUE`, `MVK_TOO_MANY_PARENT_GROUPS`, `MVK_UNEXPECTED_TOKEN`, `MVK_INVALID_ROOT_GROUP`, `MVK_PARAMSIZE_INVALID1`, `MVK_DUPLICATE_PARAM1`, `MVK_INVALID_COMPARE_TO_ENUM_OR_STRING`, `MVK_INVALID_WILDCARD`, `MVK_NO_WILDCARD`, `MVK_NO_WILDCARDS_ALLOWED` | the set above |
| rule | `MVK_ERROR_FIELD_NOT_REFERENCED`, which is post-parse | a control character, an odd dollar count, a parameter's parse class, a key on an unindexed field and `RULE_HAS_NO_ERRORTEXT`, beside the presence classes, which stand |
| rule | an error target that names nothing, its condition being unparsed ([§9](07-repetition-and-iteration.md)) | the set above |
| computation | `MVK_INVALID_WILDCARD` | both template classes |
| computation | `MVK_NO_WILDCARD` | the control character |
| computation, messageless | a refused operation or precondition | `RULE_HAS_NO_ERRORTEXT` is lost, `MVK_ERROR_MESSAGE_MISSING` kept |

- Not every checker class is measured beside every member class; a pair outside the measured sets is predicted to behave alike and is unmeasured.
- A condition naming `BaseYear` in a model without one draws `MVK_NO_BASE_YEAR` alone, that class being the member's own.
- **A class about another member does not withhold the message's:** a rule-name refusal `MVK_RULE_NAME_INVALID` or a blank error code `MVK_ERROR_CODE_MISSING` is reported together with the message's class.
- So the gate is the DSL member's own verdict: the name and error-code rows rule out "the declaration drew anything", and `MVK_ERROR_FIELD_NOT_REFERENCED` on a condition that parses and resolves rules out "the condition did not parse or resolve".

Sources: [inbound 2026-09-24e message withheld](../docs/sources/inbound-handbacks.md#inbound-2026-09-24e-message-withheld), [inbound 2026-09-25 message withheld](../docs/sources/inbound-handbacks.md#inbound-2026-09-25-message-withheld), [inbound 2026-09-25b message](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-message).

### A.3 The parameter grammar

**A parameter is written in one of two positions, chosen by its first token.** A body opening on `#` is the **group position**, `$#…$` (A.10); any other body is the **name position**, `$…$` (A.4–A.9). The two positions share one lexer and one entity-path syntax, but they resolve the same words differently and carry different terminal sets: bare `$RootGroup$` is an entity lookup and draws `INVALID_ENTITY`, while `$#RootGroup$` is a group terminal and is admitted.

**Tokens.** Whitespace inside a parameter is hidden from the parser, so `$ Grade -> Band $` is `$Grade->Band$`. The parameter lexer forms the tokens below and refuses a character outside them with `MVK_LEXER_STANDARD_ERROR`, measured for the characters the body bound below lists; that it refuses every other character is source reading, unmeasured:

| Token | Spelling |
|---|---|
| name | a run of name characters, the alphabet of [concrete syntax §1](12-concrete-syntax.md#1-lexical-structure); a run of digits alone is a digit run, which a path takes as a name and an offset as its digits |
| quoted name | the single-quoted name of [concrete syntax §1](12-concrete-syntax.md#1-lexical-structure), its quotes erased before any lookup |
| literal | a double-quoted literal, the form a semantic-index key takes |
| symbol | `/`, `..`, `.`, `->`, `+`, `-`, `#`, `(` and `)` |

- **A parameter body is bounded to printable ASCII together with `ÄÜÖäüöß`.** `é`, `€` and a CJK letter each draw `MVK_LEXER_STANDARD_ERROR`, naming the character and its 1-based parameter offset, while the same characters in the surrounding text are admitted, and an unknown name using the seven German letters reaches entity lookup and draws `INVALID_ENTITY`. Measured printable characters that form no token: `[`, `*`, `%`, `,`, `{`, `}`, `@`, `=` and `^`. So a parameter path takes no asterisk.
- **A quoted segment is lexed as a unit, so an illegal character inside it is refused a layer earlier than the same character bare.** `'Ro-ws'`, `'Ro ws'` and `'1Rows'` in the group position each draw `MVK_LEXER_STANDARD_ERROR`, while their bare spellings reach the group lookup and draw `INVALID_GROUP`, the code an undeclared but well-formed name draws. An unbalanced quote and an empty quoted segment also draw `MVK_LEXER_STANDARD_ERROR`. The two codes report different layers: only the lexer one says the text was never a name.

**The terminals.** Ten words have a role in the parameter grammar. The model's condition language selects their spelling, and exactly five differ by language; for the index terminal's suffix the choice is measured to hold whatever locale the message is written for (A.9). A terminal that is not quote-exempt is a **keyword**, which the lexer never forms as a name; a quote-exempt terminal lexes as a name and is read as its terminal only where the grammar asks for it.

| Role | English | German | Lexes as | May end a dotted name |
|---|---|---|---|---|
| semantic-index key | `For` | `Fuer` | keyword | — |
| the rule's own group | `RuleGroup` | `RegelKontext` | keyword | — |
| Base Year | `BaseYear` | `Referenzjahr` | keyword | — |
| value suffix | `value` | `Wert` | quote-exempt name | no |
| root of the rule's chain | `RootGroup` | `LfdNr` | quote-exempt name | yes |
| index terminal | `index` | `index` | quote-exempt name | yes |
| retired line terminal | `Zeile` | `Zeile` | quote-exempt name | yes |
| retired USB terminal | `Usb` | `Usb` | quote-exempt name | yes |
| form-line pointer | `Vordruckzeile` | `Vordruckzeile` | quote-exempt name | no |
| form-name pointer | `Vordruckname` | `Vordruckname` | quote-exempt name | no |

- **Quoting.** A name that collides with a keyword of the selected language is written in the parameter grammar's single-quote escape. The quotes are erased before any lookup, so an unnecessary quote is transparent, at admission and at rendering (A.11). The rule-message producer's quoting requirement is therefore narrower than the condition language's: the seven quote-exempt terminals are accepted unquoted inside an entity name for historic reasons, and only the three keywords need the escape. Only an unquoted word opens a terminal reading, so quoting a terminal turns it back into an ordinary name (A.10).
- **A trailing value word is never part of a name.** A quote-exempt word may end a dotted name only when it is one of the four the table marks, `RootGroup`/`LfdNr`, `index`, `Zeile` and `Usb`, so `.value` after a name is always the suffix.
- **Wrong-language spellings.** In the name position, the other language's value, Base-Year or rule-group terminal is an ordinary name, looked up as an entity, and draws `INVALID_ENTITY`; the own-language rule-group terminal is recognized but invalid there and draws `INVALID_PARAMETER` (A.8). In the key position, the other language's `For`/`Fuer` is a parse failure, `MVK_UNEXPECTED_TOKEN`. `RootGroup`/`LfdNr` in the name position draws `INVALID_ENTITY` in both languages on the rule-owned carrier, which is no claim about other parameter owners that share the terminal set.
- **`Zeile` and `Usb` are retired.** The group position recognizes both in either language and refuses them on the modern route with `PARAM_INVALID_IN_NEW_WORLD` (A.10); no admitted use of either is known.

**Dotted names.** A dot is not a name character, but a name may continue with dotted words and is then one path segment. The word after a dot decides:

| Word after the dot | Continues the name | May end it |
|---|---|---|
| a letter-initial name or a quoted name | yes | yes |
| a quote-exempt terminal | yes | only `RootGroup`/`LfdNr`, `index`, `Zeile` and `Usb` |
| a keyword, a digit run or a digit-initial name | no | — |
| nothing | no | — |

A word that continues no name is a token left after the name, refused where the parser meets it (A.4). So `$Anchor.Nope$` reaches entity lookup and draws `INVALID_ENTITY`, while `$Anchor.2$` never becomes a name and draws `MVK_UNEXPECTED_TOKEN`; a slash-separated numeric segment is by contrast an ordinary path element, so `$Anchor/2$` draws `INVALID_ENTITY`. Those two spellings are the old-world running-number and line specifiers, whose grammar production is gated on the model being an H-model; from an A12 document model no witness reaching their own `INVALID_FIELD_L` or `INVALID_FIELD_Z` class is known as of the measured revision. The group position's dotted rows are A.10's.

**The grammar.** An original re-expression; quoted words are the selected language's terminals from the table above, and `( … )` groups.

```
parameter    = "#" groupArgument [ key ]                      group position, A.10
             | "BaseYear" [ ( "+" | "-" ) digits ]            A.8
             | entitySpec "." ( "Vordruckzeile" | "Vordruckname" )   form pointer, A.8
             | "index" "(" entitySpec ")" [ suffix ]         index terminal, A.9
             | entitySpec [ suffix ] [ key ]                  field reference, A.6, A.7
suffix       = "." "value" | "->" categoryName
key          = "For" ( literal | entitySpec [ key ] )
entitySpec   = "RuleGroup" | path
path         = "/" segments                                   absolute
             | walk [ "/" segments ]                          relative, walking up first
             | segments                                       relative to the rule's group
walk         = ".." { "/" ".." } [ turningPoint ]
segments     = name { "/" name }
groupArgument = "RuleGroup" | "RootGroup" | "Zeile" [ ( "+" | "-" ) digits ] | "Usb" | path
```

- `name` is a name, a quoted name, a digit run or a dotted name; `categoryName` is one name token with no dotted continuation; a `turningPoint` is a name written directly after the last `..` and names the group the walk reaches.
- **A suffix comes before the key.** A suffix written after the key is a token left after the parameter, `MVK_UNEXPECTED_TOKEN`, not an alternative spelling.
- **A literal key takes no key of its own**, while an entity key may carry one, which the checker then refuses (A.7). Reading a `For` after a literal key as a token left after the key is source reading, unmeasured (A.7).
- **The rule-group terminal is a complete entity spec**, so no path extends it: `$RuleGroup/Field$` draws `MVK_UNEXPECTED_TOKEN`.
- In the group position a word that is both a group terminal and a name — `RootGroup`/`LfdNr`, `Zeile`, `Usb` — is its terminal only at the end of the argument or, for `Zeile`, before its signed offset; before a separator, a dot or a key it is a path segment, with the measured cases in A.10.
- `index` is lowercase and takes exactly one argument: a capitalised `Index(` or an empty `index()` draws `MVK_UNEXPECTED_TOKEN`, and bare `$index$` without parentheses is an entity lookup drawing `INVALID_ENTITY`.

Sources: [parameter surface and iteration gates checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates), [character-repertoire checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-template-character-repertoire), [group argument layers checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers), [group argument events checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events), [German condition-language terminals checkpoint](../docs/sources/message-and-pointer-probes.md#src-german-condition-language-terminals), [index terminal admitting-spelling checkpoint](../docs/sources/message-and-pointer-probes.md#src-index-terminal-admitting-spelling), [message-parameter decoder checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder), [inbound 2026-10-01 group arguments](../docs/sources/inbound-handbacks.md#inbound-2026-10-01-group-arguments), [inbound 2026-10-01a parent walk and dotted names](../docs/sources/inbound-handbacks.md#inbound-2026-10-01a-parent-walk-and-dotted-names).

### A.4 Parse order: which event answers first

**A parameter is refused at the first event its parser meets.** The parser follows the three-event model of [concrete syntax §3.1](12-concrete-syntax.md#31-which-class-a-refused-text-draws), and a syntax fault takes the class that section's table gives:

1. **A lexer fault answers when its token is fetched**, which happens as the token before it is consumed, so it answers before any check that waits for that consumption.
2. **A syntax fault answers where the parser meets it**, with that table's class.
3. **A check runs where its grammar rule ends**, so a check already run answers before a fault after its rule:

| Check | Runs when |
|---|---|
| an entity spec's lookup (A.5) | its names end; for a spec opening on a name or a separator, after the look-ahead window below |
| each name of a spec opening on a parent walk | as that name is consumed |
| a parent walk's climb past the root and its turning point (A.5) | when the walk ends, before any name after it |
| a key's nesting refusal (A.7) | when the inner key ends, after every name in the parameter has resolved |
| the field reference's own gates: membership or key, then suffix (A.6, A.7) | when the field ends, after its suffix and key and before a token left after it |
| the Base Year gate (A.8) | after its offset, before a token left after it |
| a group argument's lookup and admission (A.10) | when its alternative completes, before a token left after it |

**The look-ahead window.** An entity spec opening on a name or a separator is read whole before any of its names is looked up, because its two grammar alternatives share their path syntax, and in the name position the parser reads on to the token after it, because the field and both form-pointer alternatives begin with that spec. So a fault inside that window answers before the name's lookup. A spec opening on a parent walk opens no such choice and looks each name up as it is consumed, in a key and in the group position alike.

Measured name-position cases:

| Parameter | Class | Event that answers |
|---|---|---|
| `$Grade->Nope x$` | `INVALID_CATEGORY` | a category name is one token; the field's gates run before the token left |
| `$Grade->Band x$`, `$Grade->Band.value$` | `MVK_UNEXPECTED_TOKEN` | the gates pass, then the token left |
| `$BaseYear x$` without a Base Year | `NO_BASE_YEAR` | the Base Year gate before the token left |
| `$Grade->Nope For$` | `MVK_INCOMPLETE_INPUT` | a key's syntax lies inside the field |
| `$Grade->Nope é$` | `MVK_LEXER_STANDARD_ERROR` | the lexer fault is fetched as the category name is consumed |
| `$Grade->Nope.%$` | `INVALID_CATEGORY` | a dot is a token the category name never reads past |
| `$Grade->Band.%$` | `MVK_UNEXPECTED_TOKEN` | the gates pass, then the dot |
| `$Nope x$`, `$Nope.Vordruckzeile x$`, `$RuleGroup x$` | `MVK_UNEXPECTED_TOKEN` | a fault inside the window, before the lookup |
| `$Nope/$` | `MVK_INCOMPLETE_INPUT` | the same |
| `$Nope é$` | `MVK_LEXER_STANDARD_ERROR` | the same |
| `$Nope For$`, `$Nope For é$` | `INVALID_ENTITY` | the window ends at the key, so the lookup answers first |
| `$Score For Nope/$` | `MVK_INCOMPLETE_INPUT` | a key's spec reads the same window |
| `$Score For Nope/%$` | `MVK_LEXER_STANDARD_ERROR` | the same |
| `$Score For Nope$` | `INVALID_ENTITY` | the key's lookup |
| `$Score For ../Nope/$` | `INVALID_ENTITY` | a parent walk looks each name up as it is consumed |
| `$#../Nope/$` | `INVALID_GROUP` | the same, in the group position |

The group position's measured cases are A.10's.

Sources: [message-parameter decoder checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder), [group argument events checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events).

### A.5 Entity lookup and the shared root gate

**An entity spec resolves from the rule's own group, in two gates reported apart, and the root gate is shared by both positions.** The rule's own group is the group the owning declaration is declared in. An absolute spec's first segment must name a declared root group; below the root, and for a relative spec, the path must name an entity. Only the gate below the root is position-specific: the name position resolves a group *or* a field and answers `INVALID_ENTITY`, the group position answers `INVALID_GROUP`, and neither localizes the failure further, so a bad middle segment and a bad leaf draw the same code.

| Failure | Name position | Group position |
|---|---|---|
| the absolute first segment names no declared root, whatever follows (`$#/Nope$` and `$#/Nope/Rows$` alike); the match is case-sensitive | `INVALID_ROOT_GROUP` | `INVALID_ROOT_GROUP` |
| an unknown name below a declared root (`$#/Probe/Nope$`), or an unknown relative name or path | `INVALID_ENTITY` | `INVALID_GROUP` |
| a parent walk climbing past the root group | `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS` | `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS` |
| a turning point naming another group than the one the walk reaches | `INVALID_ENTITY` | `INVALID_ENTITY` |
| a short name two fields share | `ERROR_TEXT_FIELDNAME_NOT_UNIQUE` | `ERROR_TEXT_FIELDNAME_NOT_UNIQUE`, through the bare-word fallback of A.10 |

- **A relative spec walks up first.** Each leading `..` crosses one enclosing group; a turning point written directly after the last step must name the group reached and is compared by its **first word** alone, in both positions, so `$..Probe.x$` draws `INVALID_FIELD` like `$..Probe$`, and from `/Probe/Store` `$#..Probe.x$` is admitted while `$#..Wrong.x$` draws `INVALID_ENTITY`; then `/` names downwards.
- **A bare parent walk is an entity naming the group it reaches:** `$..$` draws `INVALID_FIELD`, `$..Nope$` `INVALID_ENTITY`, and a walk past the root `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS`.
- **A lone absolute segment is an entity spec rather than malformed:** `$/Probe$` names the root group, and `$/Nope$` draws `INVALID_ROOT_GROUP`.
- **The name position's short names.** A field is addressable by its bare name when that name is unique, by a path relative to the rule's group, or absolutely. A first segment two fields share draws `ERROR_TEXT_FIELDNAME_NOT_UNIQUE` as a bare name and with more path after it, `$X/Foo$` or `$X/Foo.value$`, while a unique first segment followed by more path is an unknown entity.
- **The message's short-name tier does not follow the model's short-name flag**, which still gates the same model's condition: with the flag off, a bare `$X$` two fields share still draws `ERROR_TEXT_FIELDNAME_NOT_UNIQUE`, a unique unread `$Z$` resolves to its field and draws `INVALID_FIELD`, and a read `$Z$` and an unread `$Z.Vordruckzeile$` are admitted.
- **A name resolves wherever its path leads**, a repeatable field included: a field in the rule's group, in a deeper group or in a starred group resolves alike, and the form's own gates then decide.

Sources: [two positions share the root gate checkpoint](../docs/sources/message-and-pointer-probes.md#src-two-positions-share-the-root-gate), [name-position carriers checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers), [message-parameter decoder checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder), [group argument layers checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers), [parameter surface and iteration gates checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates).

### A.6 Name-position field references

**A field reference `$Field$`, `$Field.value$` or `$Field->Category$`, optionally keyed, passes its gates in this order** once its entity spec has resolved (A.4, A.5), the first failing stage answering. `Field` stands for a rule-relative field path (A.5), not a fixed word.

| Stage | Passes when | Refusal |
|---|---|---|
| 1. key events (keyed only) | every name in the key resolves (A.5), and the key carries no key of its own | the lookup's class; `ILLEGAL_SEMANTIC_INDEX` (A.7) |
| 2. the entity is a field | — | the rule-group terminal: `INVALID_PARAMETER` (A.8); a group: `INVALID_FIELD` unkeyed, `MVK_INDEX_FOR_ERROR_TEXT_INVALID` keyed |
| 3. membership | unkeyed: the field is a member of the condition's footprint (below); keyed: the condition selects it under the same key (A.7) | `INVALID_FIELD`; `MVK_INDEX_FOR_ERROR_TEXT_INVALID` |
| 4. suffix | value suffix: an unstarred read, then value validation (below); category suffix: a category name, an Enumeration field, a declared category (below) | `PARAM_VALUE_WITH_STARREFERENCE`, `INVALID_NO_VALUE_VALIDATION`; `NO_CATEGORY`, `FIELD_NO_ENUM`, `INVALID_CATEGORY` |
| 5. nothing left | the parameter ends | `MVK_UNEXPECTED_TOKEN`, or the fault A.4 gives |

Measured placements: a key's lookup before the key gate (A.7), membership before an empty category name and the key gate before the category gates (below, A.7). That the star gate answers before the value-validation gate on a field failing both is source reading, unmeasured.

**A name that resolves to a group is refused as no read field, `INVALID_FIELD`, even when the condition reads inside that group.** Beside a read of `Store/X`, `$Store$` draws `INVALID_FIELD` and `$Store/X$` is admitted. The suffixed forms keep that class, `$Store.value$` and `$Store->Cat$` each drawing `INVALID_FIELD`, as does the root group named as `$/Probe$`. A form pointer on a group draws its own class (A.8), and a keyed parameter on a group meets the index class (A.7).

**Membership: an unkeyed field reference must name a field the condition reads.** A field is a member when the condition reads it other than only through a semantic-index selection of it, directly or through a read of a group containing it. What the condition references is therefore its footprint, not only its field operands:

- **A group read makes every field inside the group a member.** Beside a read of `Loans/Book`, `GroupFilled(Loans)` admits `$Borrower$`, `$Borrower.value$` and the nested `$Details/Note$`, each `INVALID_FIELD` without it, while a field outside the group, `../Returns/Book`, stays refused; `GroupFilled(RuleGroup)` reaches the same fields.
- **A key selection does not make a member:** a keyed condition operand does not license the unkeyed spelling of that field, which is refused `INVALID_FIELD`, and beside `GroupFilled(Rows For "k1")` the unkeyed spelling of a field of `Rows` is refused the same way.
- **The gate's domain is the unkeyed field reference.** A keyed reference meets the key gate instead (A.7); the form pointers (A.8), the Base Year (A.8), the index terminal (A.9) and the group position (A.10) carry gates of their own and no membership gate. A computation's computed target is always a member, because the generated condition reads it (A.12).

**The value suffix carries two independent static gates, each with its own class, and the second is a field-declaration property.**

- **The star gate:** `$Field.value$` needs some read of the field written without an asterisk on any of the field's repeatable levels, else `PARAM_VALUE_WITH_STARREFERENCE`. Measured where the condition reaches the field only through a starred aggregate operand; the same field's bare `$Field$` is admitted in the same message, so the gate belongs to the suffix and not to the reference. The gate is existential: beside a keyed read and a starred read of the same field `$Base.value$` is admitted.
- **The star gate reads different references than membership.** Membership needs a read that is not a key selection; the star gate takes any read written without an asterisk, a keyed one included. A key selection writes no asterisk on its own group's level and reads that group's index field there, but a deeper group inside a keyed group's extent keeps its own: beside `GroupFilled(Rows For "k1")` the name `$Rows/Sub/SubV For "k1"$` is admitted while `$Rows/Sub/SubV.value For "k1"$` draws `PARAM_VALUE_WITH_STARREFERENCE`.
- **An unstarred group read also clears the star gate:** beside `NoFieldFilled(Loans*/Borrower)`, `$Borrower.value$` is admitted with `GroupFilled(Loans)` and draws `PARAM_VALUE_WITH_STARREFERENCE` without it.
- **The value-validation gate:** a String field declared with **no value validation** refuses `$Field.value$` with `INVALID_NO_VALUE_VALIDATION`, whose text states the rule, while `$Field$` on that field and `$Field.value$` on an ordinary String field are both admitted. The gate is asked of a String field only. So a checker must read the referenced field's declaration and not only the condition.
- **The declaration gates apply to a field reached through a group read too:** a no-value-validation field's `.value` draws `INVALID_NO_VALUE_VALIDATION`, and a String field's category suffix `FIELD_NO_ENUM`.
- **A suffix after a suffix is neither an alternative nor a composition:** `$Field.value.value$` draws `MVK_INCOMPLETE_INPUT`.

**The category suffix, `$Field->Category$`, is an alternative to the value suffix rather than a further decoration of it.** Its three gates run after entity resolution and the membership gate, in this order: the arrow must be followed by a category name, `NO_CATEGORY`; the field must be an **Enumeration** declaration, `FIELD_NO_ENUM`; and the name must be one of that declaration's declared categories, `INVALID_CATEGORY`. It requires neither an unstarred reference nor value validation.

- **An empty category name is a semantic refusal, not an early syntax refusal**, so the prerequisite gates answer first: an unknown field reports `INVALID_ENTITY`, an unreferenced field `INVALID_FIELD`, and a referenced field `NO_CATEGORY`, even when it is not an Enumeration. The same ordering holds when another arrow follows the empty first category.
- **A doubled arrow has no single diagnostic class,** because the first suffix is checked before the trailing syntax: a declared first category reaches `MVK_UNEXPECTED_TOKEN`, an undeclared first category draws `INVALID_CATEGORY`, and a non-Enumeration field draws `FIELD_NO_ENUM`.
- **The two suffixes do not compose:** `$Field.value->Cat$` is `MVK_UNEXPECTED_TOKEN`.

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [keyed message membership checkpoint](../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15) (rows `s01`, `v01`, `v02`, `k09`, `g01`, `g02`), [parameter surface and iteration gates checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates), [inbound 2026-09-30a message reference admission](../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-message-reference-admission), [name-position refusals checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-name-position-refusals), [name-position carriers checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers), [category gate order checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-category-gate-order).

### A.7 Semantic-index keys

**A field reference may carry a semantic-index key last, `$Field For "k"$` or `$Field For KeyField$`, which looks the field up in a repeatable group by that key.** The key follows any value or category suffix (A.3). It is either a **quoted literal** or a **path to the keying field**; an unquoted bare word is therefore read as a field reference and refused `INVALID_ENTITY` when no such entity exists, not as an unlexable token.

**A key carrying a key of its own is refused `ILLEGAL_SEMANTIC_INDEX`, quoting the inner index**, whether the key is a keyed field or a keyed group, but only after every name in the parameter has resolved, so an unresolvable outer, inner or innermost name answers `INVALID_ENTITY` first. A literal takes no key (A.3), so `$Top For "k1" For "k2"$` is not a nesting: where the key gate below refuses `Top`, it draws that gate's `MVK_INDEX_FOR_ERROR_TEXT_INVALID`; where the gate would pass, the trailing key's class is unmeasured.

**A keyed parameter's gate is on the semantic index, not on the field.** The key selects a row of the field's nearest enclosing repeatable group that declares an index field, measured where the groups between are unindexed, and the condition must use that same index the same way. A keyed parameter is admitted exactly when the condition selects that group under the same key:

| The condition's keyed read | Admits a keyed parameter on |
|---|---|
| a keyed **field** read | that field, and the group's declared index field |
| a keyed **group** read | every field of the group, at any depth below it, any suffix included |

Otherwise the parameter draws `MVK_INDEX_FOR_ERROR_TEXT_INVALID`:

- **A condition that reads no field under a key admits no keyed parameter.** On a field the condition reads, `$Score For "k"$`, spaced any way, and `$Score For "a For b"$`, whose literal contains the key terminal, draw `MVK_INDEX_FOR_ERROR_TEXT_INVALID`.
- A third field of the same group, keyed identically beside a keyed field read, is refused; so what must match is the keyed group and key *plus* the displayed field being one of the two the read covers, not the group's fields at large.
- **The pairing is exact in both directions.** A condition that reads the group plainly, or keys it by a *different* key, refuses the keyed parameter `MVK_INDEX_FOR_ERROR_TEXT_INVALID`; the unkeyed spelling is A.6's membership gate.
- **A literal key matches by its spelling, not by its value.** On a Number index field the condition's `For "1"` admits `$V For "1"$` and refuses `$V For "01"$` and `$V For "1.0"$`, and a condition keyed `"01"` refuses `"1"`; the group position compares the same way (A.10). Measured on a scale-0 Number index only.
- **A field-valued key must be the condition's own key field;** another resolvable field draws the index class.
- **A group in the name position resolves as an entity and meets this gate:** `$Store For "k"$` and `$Top For Store$` draw `MVK_INDEX_FOR_ERROR_TEXT_INVALID`, while a key naming nothing, `$Store For Nope$`, draws `INVALID_ENTITY`. A keyed group in the name position, `$Rows For "k1"$`, draws `MVK_INDEX_FOR_ERROR_TEXT_INVALID` beside a condition keying that group or one of its fields.

**The key gate answers before the suffix gates.** A wrong key with an undeclared category draws the index class. With a literal key absent from the condition, `$Field-> For "k"$` reports `MVK_INDEX_FOR_ERROR_TEXT_INVALID` for a resolved field whether or not the condition references it plainly, ahead of the empty category name; an unknown field reports `INVALID_ENTITY` first. A field-valued key and the value suffix both compose with the gate, and so does the category suffix: a valid category on a plainly read Enumeration still draws the index class.

**An index on the root or a fixed group meets the same gate.** Beside `[Cover/Amount For "X"] > 0`, with the index on the root or on the fixed `Cover`, `$Cover/Amount For "X"$` is admitted, as is `$Cover/Amount For Key$` beside the condition's own key field `Key`, and the parameter renders the field's name as `$Field$` does (A.11); `$Cover/Amount$` beside that keyed read draws `INVALID_FIELD`, a key selection being no unkeyed read. A value or category suffix on such a parameter is unmeasured.

**A name-position keyed parameter needs no presence guard.** Beside `FieldNotFilled(/Kp/Rows/Base For "k1")`, a negative presence predicate, keyed parameters on `Base` and on the group's index field are admitted. The keyed presence guard belongs to the group position (A.10).

**The key literal must also be a valid value for the index field's declared kind:** a Number index field keyed `"k1"` refuses the *condition* with `MVK_INDEX_VALUE_INVALID`, before any parameter question arises, so the two gates report apart.

Sources: [name-position carriers checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers), [keyed parameter admits the index field only checkpoint](../docs/sources/message-and-pointer-probes.md#src-keyed-parameter-admits-the-index-field-only), [keyed message membership checkpoint](../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15) (rows `k01`–`k30`, `a01`–`a10`, `b01`, `e01`–`e03`, `f11`–`f22`), [message-parameter decoder checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder), [category gate order checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-category-gate-order), [parameter surface and iteration gates checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates), [single-instance key checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-single-instance-key) (rows `m1`–`m4`, rule `LM1`).

### A.8 Form pointers, the rule-group terminal and the Base Year

**`$Entity.Vordruckzeile$` and `$Entity.Vordruckname$` are live name-position forms that carry no membership gate.** Both are admitted on a field the rule's condition never references, on a Number field as on a String one, on a field inside a repeatable group, and under the bare, group-relative and absolute spellings of the entity — where every other name-position form on an unreferenced field draws `INVALID_FIELD`.

- Their only measured gate is that the entity resolves to a **field**: an undeclared name draws `INVALID_ENTITY`, and a group draws `INVALID_FIELD_IN_PARAMETER` rather than the membership class — `$Store.Vordruckzeile$` from a root rule, `$/Probe/Store.Vordruckname$`, and from inside `/Probe/Store` its subgroup `$Deep.Vordruckzeile$`. Spelled from inside `Store` itself, `$Store.Vordruckzeile$` names no group there and is an undeclared name, `INVALID_ENTITY`.
- Neither composes with a further suffix: `.value` after one draws `MVK_INCOMPLETE_INPUT` and `->Category` draws `MVK_UNEXPECTED_TOKEN`. The bare terminal without an entity, `$Vordruckzeile$`, is an entity lookup drawing `INVALID_ENTITY`.
- What either form renders is unmeasured, and no rendering is specified.

**The rule-group terminal is a group, so every field-shaped spelling of it is refused, and one spelling escapes as an internal error.** `$RuleGroup$`, `$RuleGroup.value$` and `$RuleGroup->Category$` draw `INVALID_PARAMETER`, and `$RuleGroup/Field$` draws `MVK_UNEXPECTED_TOKEN` (A.3). `$RuleGroup.Vordruckzeile$` and `$RuleGroup.Vordruckname$` draw **`MVK_INTERNAL_ERROR`**, whose text reports a missing referenced entity for the `RuleGroup` context, reproduced from a root-group rule and from one two levels down. The same code answers the terminal as a key in either position, `$Score For RuleGroup$` and `$#/Probe/Cases For RuleGroup$`. That is a Kernel defect surfacing through a static rule check rather than a semantic class, so the code is an internal fault and not a diagnosis of the authored text.

**The Base Year terminal, `BaseYear` in English and `Referenzjahr` in German, is the one non-field name-position form**, optionally followed by a signed integer offset, `$BaseYear+3$` or `$BaseYear-1$`. Its only static gate is that the model declares a Base Year, else `NO_BASE_YEAR`; there is no bound on the offset. It renders from the model alone (A.11).

Sources: [parameter surface and iteration gates checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates), [name-position carriers checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers).

### A.9 The index terminal

**`index(Key)` is a live terminal in the name position, which the group position does not have.** `$index(Key).value$` is admitted, and renders, where the rule's error field sits inside a repeatable group whose declared index field is `Key`. The terminal resolves its argument against the error field's own path, then cross-checks the condition's references, then reads its suffix; the first failing stage answers:

| Stage | Passes when | Refusal |
|---|---|---|
| 1. resolution | the argument is the **bare short name** of exactly one index field on the error field's own path | none: `INVALID_INDEX_FIELD`; several: `INVALID_INDEX_FIELD_AMBIGUOUS`; a group declaring several index field names: `INVALID_INDEX_FIELD_COMPOSED_INDEX` |
| 2. repeatability scan | every index field the condition references under that short name agrees with the resolved one, visited in full-name order, the first failure answering | `INVALID_INDEX_FIELD_REP`, `INVALID_INDEX_FIELD_REP_ITER`, `INVALID_INDEX_FIELD_NONREP_ENUM` |
| 3. suffix written | a suffix is present | `INVALID_INDEX_FIELD_PARAMETER` |
| 4. suffix scan | the referenced declarations agree on what the suffix reads | `->Category`: `FIELD_NO_ENUM`, `INVALID_CATEGORY`, `INVALID_INDEX_FIELD_ENUM_XML_VALUES`, `INVALID_INDEX_FIELD_ENUM_XML_TO_CAT`; `.value`: `INVALID_INDEX_FIELD_INCONSISTENT_TYPES`, `INVALID_INDEX_FIELD_ENUM_XML_VALUES`, `INVALID_INDEX_FIELD_ENUM_XML_TO_DISPLAY` |

That stage 3 follows the repeatability scan, and that `INVALID_INDEX_FIELD_INCONSISTENT_TYPES` answers under `.value` only, are source reading, unmeasured.

**Resolution.** An absolute path, a group-relative path, a nonexistent name and a non-index field of the same group all draw `INVALID_INDEX_FIELD`, whose text names three alternative causes: the argument is not an index field, is referenced the wrong way, or does not occur in the rule's condition. The index field must lie on the **error field's own path**, so the same parameter under a root-group error field draws that class too. The lookup refuses on multiplicity as well as absence: two nested repeatable groups whose index fields share a short name draw `INVALID_INDEX_FIELD_AMBIGUOUS`, where the identical parameter is admitted from an error field on the level carrying only one of them. `INVALID_INDEX_FIELD_COMPOSED_INDEX` has no witness known as of a12-dmkits `a4091041`: the model format searched declares one index field name per group.

**The repeatability scan reads the condition.** The checker filters the index fields the **condition** references by the parameter's short name and cross-checks each against the resolved one, so what the condition does with that field decides the parameter:

- **Index-reference metadata follows authored paths.** A referenced entity contributes the index fields on its own ancestor chain; reading a parent or root group does not create references to indices declared inside its descendants, even though the group's presence observes those descendant fields (source reading). The same rule bounds the group position's index-reference mode (A.10).
- **An empty filtered set skips the stage entirely:** a condition naming only a differently named index field, or none, leaves nothing to check, which is why a parameter can be admitted beside a condition that never mentions the index field it names.
- **Repeatability disagreement** between a referenced index field and the resolved one is `INVALID_INDEX_FIELD_REP`, raised in either direction: an error field in a repeatable indexed group whose condition reads a field of a non-repeatable indexed group draws it, and so does a non-repeatable error path beside a starred read of a repeatable group whose index field is visited first.
- **On a repeatable error path**, a referenced index field read plainly and unstarred is admitted, while a `For "k"`-keyed read and a **starred** read each draw `INVALID_INDEX_FIELD_REP_ITER` under either suffix. That a keyed or starred read draws it even beside a plain read of the same index is source reading, unmeasured.
- **On a non-repeatable error path the gate admits exactly one declaration shape.** Where the index field sits on a group that does not repeat, the parameter draws `INVALID_INDEX_FIELD_NONREP_ENUM` unless that index field is an Enumeration whose declared value set holds a single value and whose S-value is set; on that one declaration it is admitted. An Enumeration declaring two values and an Enumeration declaring one value with no S-value each refuse, while the same String index field on a *repeatable* group admits the identical parameter, so the trigger is the group's repeatability and not the field's kind. Both suffixes draw the class alike, which places this gate before the suffix stages. Every refusing declaration is itself legal: the model passes consistency checking on its own, and the refusal appears only once a message names the index field.
- **Two conjuncts of that shape are read from the checker rather than separated by measurement.** The Enumeration requirement: in the model format searched, over all fifteen field types, only an Enumeration declares a value set or an S-value, so a non-Enumeration index field fails the other two conjuncts as well and no observation separates the three. The S-value conjunct tests only that the S-value is set, not that it names the declared value: a non-member S-value is refused `MVK_S_VALUE_INVALID` by the model gate before any parameter is examined, measured, so the two readings agree on it. They agree on a blank S-value as well: an empty S-value draws `INVALID_INDEX_FIELD_NONREP_ENUM` under both suffixes, while a one-space S-value is admitted under both, so the conjunct tests that the S-value is non-empty, not that it is a member.
- **The scan visits the referenced index fields in full-name order and reports the first failure**, so the class depends on the names. From a non-repeatable error path, a starred read of a repeatable group draws `INVALID_INDEX_FIELD_REP` when that group's index field sorts before the error path's own; when it sorts after, the error path's own index field is visited first and draws `INVALID_INDEX_FIELD_NONREP_ENUM` exactly when it fails that class's single-valued Enumeration shape. A repeatable group declared after the error path's but sorting before it shows that the order is by name, not by declaration.

**The suffix is mandatory, and the two suffixes are live alternatives on one declaration.** Omitting the suffix draws `INVALID_INDEX_FIELD_PARAMETER`, on an Enumeration index field as on a String one. `->Category` is admitted on an Enumeration index field carrying that category; its own refusals are the field's kind, `FIELD_NO_ENUM` on a non-Enumeration index field, and the category's existence, `INVALID_CATEGORY`, whose text reports it as an incorrect error text for the language rather than as an entity fault. The suffixes do not compose: `.value->Cat` is `MVK_UNEXPECTED_TOKEN`. That an empty category name after the arrow draws `NO_CATEGORY` after the repeatability scan is source reading, unmeasured.

**Past the repeatability scan the checker compares the referenced declarations against each other, and the two suffixes read different parts of the same declarations.** The witness shape is a condition that iterates a repeatable group off the error field's own path, which puts two same-short-named index fields in the filtered set.

| Mismatch between two Enumeration index fields | `->Category` | `.value` |
|---|---|---|
| different stored value sets | `INVALID_INDEX_FIELD_ENUM_XML_VALUES` | `INVALID_INDEX_FIELD_ENUM_XML_VALUES` |
| identical value sets, different value-to-category mapping | `INVALID_INDEX_FIELD_ENUM_XML_TO_CAT` | admitted |
| different value-to-display mapping | admitted | `INVALID_INDEX_FIELD_ENUM_XML_TO_DISPLAY` |

- Under a non-parallel condition both suffixes are admitted on the same pair, which attributes the classes to the pair rather than to the parameter.
- One Enumeration index field against one of another kind is `INVALID_INDEX_FIELD_INCONSISTENT_TYPES`, with no witness known as of a12-dmkits `a4091041`: a String against an Enumeration index field read by a starred aggregate draws `INVALID_INDEX_FIELD_REP_ITER` first, and read in parallel the condition is refused `MVK_ERROR_FIELD_INVALID_INDEX_TYPE`.

**The keyword and the suffix are case-sensitive, and the suffix is chosen by the condition language.** Under an English condition language the suffix is lowercase `value`, while a capitalised `Value` and the German `Wert` each draw `MVK_UNEXPECTED_TOKEN`. Under a German condition language the suffix is `Wert` and the English word is refused the same way: `$index(Key).Wert$` is admitted, `.value` and a capitalised `Index(` each draw `MVK_UNEXPECTED_TOKEN`, and the suffix-free form still draws `INVALID_INDEX_FIELD_PARAMETER`, so the keyword is lowercase `index` in both languages. Across the `en_US` and `de_DE` message locales measured, the condition language alone picks the suffix: a German message text under an English condition language still takes `value` and refuses `Wert`.

Sources: [index terminal admitting-spelling checkpoint](../docs/sources/message-and-pointer-probes.md#src-index-terminal-admitting-spelling), [index terminal refusal classes checkpoint](../docs/sources/message-and-pointer-probes.md#src-index-terminal-refusal-classes), [non-repeatable index field gate checkpoint](../docs/sources/message-and-pointer-probes.md#src-nonrepeatable-index-field-gate), [index German suffix checkpoint](../docs/sources/message-and-pointer-probes.md#src-index-german-suffix), [parameter surface and iteration gates checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates), [keyed message membership checkpoint](../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15) (rows `r01`, `r11`, `z01`–`z03`, `o01`, `t01`, `t02`, `d01`, `d02`, `d11`, `d12`, `i01`, `i02`, `t10`, `t11`), [index message rendering source account](../docs/sources/message-parameter-rendering-probes.md#src-index-message-rendering), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### A.10 The group position

**A parameter written `$#…$` occupies the group position.** Its argument is one of two keyword shorthands for the endpoints of the rule's ancestor chain, or a group path. It renders a coordinate, not a name (A.11), and it has **no explicit index syntax**: `$#/Msg/Rows[1]$` is refused `MVK_LEXER_STANDARD_ERROR`, brackets not being in that grammar at all, so the position renders the firing row's own coordinate and cannot be pinned to another row.

**The terminal set.** `$#RootGroup$` and `$#RuleGroup$` are both admitted. `$#RootGroup$` names the root of the **rule's own** ancestor chain rather than a model-wide root, which a model with two root groups separates: from a rule under either root `$#RootGroup$` and `$#RuleGroup$` are admitted, while the other root's absolute spelling draws `INVALID_GROUP`. `$#Zeile$` and `$#Usb$` draw `PARAM_INVALID_IN_NEW_WORLD`, a code distinct from `INVALID_GROUP`, so the Kernel recognizes both and refuses them on the modern route. `$#Vordruckzeile$`, `$#Vordruckname$` and `$#index(...)$` draw plain `INVALID_GROUP` on this carrier, so they are not terminals in this position.

**The two keyword shorthands belong to the condition language, in both directions, while the retired terminals do not.** On a model whose condition language is German, `$#LfdNr$` is admitted and `$#RuleGroup$` and `$#RootGroup$` both draw `INVALID_GROUP`; on an English one the verdicts are exactly reversed. The absolute-path spelling is admitted under either language, so only the keyword set is selected. A retired terminal is language-independent: `$#Zeile$` draws `PARAM_INVALID_IN_NEW_WORLD` under German exactly as under English. Whether a model's condition language can change under authored rules is [concrete syntax §1](12-concrete-syntax.md#1-lexical-structure)'s.

**Only an unquoted word opens a keyword, and a word that is also a name is its keyword only at the end of the argument.**

- Quoting removes the terminal reading rather than merely being stripped first: `$#'RootGroup'$` and `$#'RuleGroup'$` draw `INVALID_GROUP`, naming a group of that name, and `$#'Zeile'$` draws `INVALID_GROUP` rather than the retired code.
- `RuleGroup` is a keyword, the keyword whatever follows, and its gate answers before a token left after it.
- `RootGroup`, `Zeile` and `Usb` are also names, each a path segment before a separator, a dot or a key (A.3); `Usb` in all three places and `Zeile` before a dot rest on source reading, unmeasured. Beside a root group holding a group named `RootGroup` with a read field below it, `$#RootGroup/Inner$` is admitted; with that group unread, `$#RootGroup$` is admitted as the root while `$#'RootGroup'$` and `$#RootGroup/Inner$` draw `INVALID_GROUP`; `$#Zeile/Store$` draws `INVALID_GROUP` rather than the retired code; `$#RootGroup.x$` is a path segment and draws `INVALID_GROUP`; and `$#RootGroup For "k"$` and `$#Zeile For "k"$` draw `INVALID_GROUP`, as the keyword's `$#RuleGroup For "k"$` does.
- `Zeile` alone also takes a signed offset: `$#Zeile-1$` draws the retired code and `$#Zeile-$` `MVK_EXPECTED_TOKEN_NOT_FOUND`. Before any other token neither reading continues and no check runs: `$#RootGroup-x$`, `$#Zeile-x$` and `$#Usb x$` draw `MVK_UNEXPECTED_TOKEN`.
- The German condition language makes the same decisions on its own words: from a root rule `$#RegelKontext/Loans$` draws `RULEGROUP_IMMEDIATELY_BELOW_ROOT`, `$#LfdNr/Loans$` `INVALID_GROUP` and `$#LfdNr-x$` `MVK_UNEXPECTED_TOKEN`.

**A group path is absolute after a leading slash and otherwise relative to the rule's group**, with A.5's `..` parent walk and turning point. A bare word therefore names a group directly below the rule's group, and one that names nothing there falls back to the short name of a **field**, never of a group: from `/Probe/Rows` the rule's own group spelled `$#Rows$` draws `INVALID_GROUP`, a root rule reading `Store/Deep/Y` refuses `$#Deep$` while admitting `$#Store/Deep$`, and a bare `$#X$` whose `X` is two fields elsewhere draws `ERROR_TEXT_FIELDNAME_NOT_UNIQUE`. A path naming a field, by a relative path or through that fallback, names no group and draws `INVALID_GROUP` at availability. Each segment may take the single-quote escape, `$#/'Probe'/'Rows'$` being admitted, and quoting is transparent (A.3).

**The named group must be available, and two arms make it so:** the rule's own group and its ancestors at any depth, and any group holding, at any depth, something the condition reads. A group failing both arms draws `INVALID_GROUP`, the class an unknown group draws; the lookup runs first, so the shared code does not mean that availability alone decides.

| Rule's group | The condition reads | Admitted | Refused `INVALID_GROUP` |
|---|---|---|---|
| `/Probe/Rows` | its own field only | `$#/Probe/Rows$`, `$#/Probe$` | the declared descendant `$#/Probe/Rows/Deeper$`, the sibling `$#/Probe/Store$` |
| `/Probe/Rows/Deeper` | its own field only | its own group, `/Probe/Rows`, `/Probe`, `$#RootGroup$` | the sibling `/Probe/Store` |
| the root | `Store/X` | `$#Store$`, `$#/Probe/Store$` | — |
| the root | `Store/Deep/Y` | the intermediate `$#Store$` | — |
| `/Probe/Store` | `/Probe/Beside/Z` | `$#../Beside$`, `$#/Probe/Beside$`, `$#..Probe/Beside$` | — |

A `GroupFilled` read counts as reading inside its group: beside `GroupFilled(Loans)` the nested `$#Details$` is admitted, and without it refused. So availability is neither containment of the rule's group nor its converse.

**`RuleGroup` carries a placement condition the other shorthand does not.** A declaration sitting directly in the root group may not use it: `$#RuleGroup$` there is refused `RULEGROUP_IMMEDIATELY_BELOW_ROOT`, whose text states the rule, while the same message one level down is admitted. The gate belongs to that word alone: from the same root-declared locus, `$#RootGroup$` and the **absolute** spelling of that very group are both admitted, so the group is nameable and the position works; what is refused is the shorthand whose meaning would there coincide with `RootGroup`. Both carriers share the gate, measured separately: a validation rule whose error field sits directly in the root group draws the same refusal, with the same three-spelling contrast from that one locus, and so does a computation in a root group (A.12).

**`$#RootGroup$` has one gate of its own, and it reads the condition rather than the model: parallel iteration.** Where the condition iterates a repeatable group off the error field's own path — reachable when that group's index field shares its short name with the error path's — `$#RootGroup$` draws `INVALID_HASH_LFDNR_FOR_PARALLEL_ITERATION`, whose text states the rule and directs the author to a parallel-iteration parameter instead. The identical parameter from the identical error field is admitted once the condition is not parallel, so the gate is the condition's shape and not the locus. The absolute spelling of that same root, and the absolute spelling of the iterated group, both stay admitted under parallel iteration.

**Admission is one ordered check.** Once the argument has decoded (A.4), the first failing stage answers:

| Stage | Passes when | Refusal |
|---|---|---|
| 1. retired terminal | the argument is not `Zeile` or `Usb` | `PARAM_INVALID_IN_NEW_WORLD` |
| 2. shorthand gates | `RuleGroup`: the rule's group is not a root group; `RootGroup`: the condition does not iterate in parallel | `RULEGROUP_IMMEDIATELY_BELOW_ROOT`; `INVALID_HASH_LFDNR_FOR_PARALLEL_ITERATION` |
| 3. lookup | A.5's gates, then the path names a declared entity, or a bare word the short name of exactly one field | `INVALID_ROOT_GROUP`, `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS`, `INVALID_ENTITY` (turning point), `INVALID_GROUP`, `ERROR_TEXT_FIELDNAME_NOT_UNIQUE` |
| 4. key events (keyed only) | the key's names resolve on this position's classes, and the key carries no key of its own | see the keyed bullets below |
| 5. availability | the path names a group available by the two arms above | `INVALID_GROUP` |
| 6. index-reference mode | see below | `INVALID_GROUP` |
| 7. star reference | for a repeatable group whose declared repeatability exceeds one, some authored reference inside the group reads its level without an asterisk; a key selection of the group counts | `ITER_PARAM_WITH_STARREFERENCE` |
| 8. keyed presence guard (keyed only) | the condition guards the group under the same key (below) | `INVALID_USE_OF_SEMANTIC_INDEX` |
| 9. nothing left | the argument ends | `MVK_UNEXPECTED_TOKEN`, or the fault A.4 gives |

- **Stage 6, the index-reference mode, decides between the keyed and unkeyed spellings of an indexed group.** A *keyed* parameter needs a repeatable group that declares an index field and a condition that selects that group under the same key spelling, through a keyed read of the group or of a field inside it; any other group draws `INVALID_GROUP`. An *unkeyed* parameter on a repeatable group that declares an index field needs an authored reference inside the group that is not a key selection of it; failing that, it is admitted only through the ancestor arm, when the group is the rule's own group or an ancestor and the condition selects no group by key. References follow authored paths, as in A.9.
- **Stage 7's star rule is existential.** A condition referencing `Rows` without a star admits the row parameter; against a condition reaching `Rows` only through `NumberOfFilledGroups(/Et/Rows*)` the same parameter draws `ITER_PARAM_WITH_STARREFERENCE`, and adding the unstarred reference back as a conjunct admits it again, the starred one still present. The starred-only condition carrying a plain message is admitted, which keeps the class on the parameter rather than the condition.
- **Measured scope.** Stages 1–5 and 8, stage 7's existential star rule and the keyed identity of stage 6 are measured; their order is measured where a row places two of them, an undeclared group drawing `INVALID_GROUP` ahead of the star class. Stage 7's restriction to a group whose declared repeatability exceeds one and its counting of a key selection are source reading, unmeasured. The unkeyed half of stage 6 rests on source reading, witnessed where a condition keying a group refuses that group's unkeyed parameter.

**The keyed group parameter: exact key identity, then the presence guard.** `$#/Probe/Cases2 For "X"$` takes the semantic-index key, and the key must match the condition's exactly. From a condition keying `/Probe/Cases2/Score2` with `For "X"`, the unkeyed `$#/Probe/Cases2$` and the differently keyed `$#/Probe/Cases2 For "Y"$` both draw `INVALID_GROUP`, the same class an off-path group draws, and `$#/Probe/Cases2 For "X"$` passes the identity gate. So the keyed and unkeyed spellings are not alternatives at one locus: whichever the condition established is the one the parameter must use. A literal key matches by spelling: beside `GroupFilled(/Kp/NRows For "1")`, `$#/Kp/NRows For "1"$` is admitted and the `"01"` spelling draws `INVALID_GROUP`. A key literal invalid for the index field's kind refuses the condition first (A.7).

- **A condition that reads no field under a key admits no keyed group parameter.** The group's own lookup answers first, then the key's events in order, its names looked up on the group position's classes, and then the key's gate draws `INVALID_GROUP` even on an otherwise admitted group: `$#/Probe/Cases For "k"$` and `$#/Probe/Cases For Nope$` draw `INVALID_GROUP`, `$#/Probe/Cases For Score For "k"$` `ILLEGAL_SEMANTIC_INDEX`, and `$#/Probe/Cases For Score/$` `MVK_INCOMPLETE_INPUT`.
- **A key name resolving nowhere draws `INVALID_GROUP` ahead of the nesting**, `$#/Probe/Cases For Nope For "k"$` included, while an undeclared root draws `INVALID_ROOT_GROUP`, a walk past the root `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS` and a turning point naming another group `INVALID_ENTITY`. That a key naming a group draws `INVALID_GROUP` is source reading, unmeasured. The rule-group terminal as a key is A.8's internal error.

#### The keyed presence guard

**A matching keyed reference alone does not license a keyed group parameter.** After availability, the index-reference mode and the star reference, the condition must provide a **positive structural presence guard** for the same group and key, or the parameter draws `INVALID_USE_OF_SEMANTIC_INDEX`. A guard is a condition leaf in one of these classes; [the operator reference](14-operator-reference.md#keyed-message-guard) assigns each leaf its class:

| Class | The leaf guards the group under the key when |
|---|---|
| `leaf` | its keyed operand selects that group under that key: a keyed `FieldFilled` of a field inside it, or a keyed `GroupFilled` of it |
| `one operand` | at least one of its operands selects that group under that key |
| `every operand` | it has operands and every one selects that group under that key |
| `none` | never |

- **Composition:** one guarding conjunct suffices, and every disjunct of an `Or` must guard.
- **Negative presence predicates and comparisons, of any operands, supply no guard,** and neither does any other leaf outside the first three classes (source reading).
- **A name-position keyed parameter needs no guard** (A.7).
- **Measured scope:** beside `GroupFilled(/Kp/Rows For "k1")` the keyed group parameter is admitted, and a condition whose matching keyed read guards nothing draws `INVALID_USE_OF_SEMANTIC_INDEX`. An `AtLeastOneFieldValueIncludedInValueList` reading a field of the group under the key supplies no guard and draws that class, and a keyed `GroupFilled` conjunct beside it admits the parameter, which measures the `none` assignment of that quantifier and the one-guarding-conjunct rule. The other class assignments and the `Or` composition rest on source reading.

**Parse order in the group position.** The parser's events (A.4) decide among faults and checks: each fault answers where the parser meets it, an alternative's check — the walk's, the lookup and admission — runs once the alternative is complete, and a token left after it answers last.

| Mechanism | Measured rows |
|---|---|
| A malformed spelling is refused on its lexical code before any lookup, even on an unknown name | an unbalanced quote and an empty quoted segment: `MVK_LEXER_STANDARD_ERROR`; a trailing separator: `MVK_INCOMPLETE_INPUT`; a doubled separator: `MVK_UNEXPECTED_TOKEN`; a character with no token, such as `[`, `*` or `%`: `MVK_LEXER_STANDARD_ERROR` |
| A token left after a complete path waits for the path's check | `$#Sto-re$`: `INVALID_GROUP`; `$#Store-x$`, whose `Store` resolves: `MVK_UNEXPECTED_TOKEN` |
| A lexer fault in the token after the path answers first; availability precedes a trailing token | `$#Store//%$`: `MVK_UNEXPECTED_TOKEN`; `$#Store/%$` and `$#Store%$`: `MVK_LEXER_STANDARD_ERROR`; on a declared but unavailable `Beside`, `$#Beside%$`: `MVK_LEXER_STANDARD_ERROR` and `$#Beside-x$`: `INVALID_GROUP`; a `,`, `{`, `}`, `@`, `=` or `^` after a name is a lexer fault |
| A turning point is checked before the child below it | from a `Loans` rule reading its sibling, `$#..Wrong/Missing$`: `INVALID_ENTITY`; `$#..Library/Missing$`: `INVALID_GROUP` |
| An up-step after a turning point or a leading slash continues nothing | `$#..Library/..$`, `$#/..$`: `MVK_UNEXPECTED_TOKEN` |
| A parent walk is checked once the parser ends it, before any name after it | from the root, `$#../RuleGroup$`: `ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS`; from `Loans`, `$#..Wrong/$`, `$#..Wrong//%$` and `$#..Wrong/%$`: `INVALID_ENTITY` |
| The parser ends a walk one token past its last separator, so a `%` there answers first. When that token continues no name — a sign or a bracket among them — a run of two or more up-steps counts one step more than written, while a digit run or a quoted name ends the run as written; a single up-step counts as written | two levels below the root, `$#../../$`, `$#../..//$` and `$#../../RuleGroup$`: the above-root class, and `$#../../Nope$`: `INVALID_GROUP`; three levels below, `$#../../$`: `MVK_EXPECTED_TOKEN_NOT_FOUND` and `$#../../RuleGroup$`: `MVK_UNEXPECTED_TOKEN`; one level below, `$#../$`: `MVK_INCOMPLETE_INPUT` |
| A digit run is a name; a keyword is never one | `$#123$`: `INVALID_GROUP`; `$#Store/RuleGroup$`, `$#For$` and `$#Store/BaseYear$`: `MVK_UNEXPECTED_TOKEN`; the quote-exempt `$#Store/value$`: `INVALID_GROUP` |
| A dotted name is one segment, which no group on the measured models is named | `$#Store.X$`, `$#Store.x.y$` and `$#Loans.'For'$`: `INVALID_GROUP` |
| A quote-exempt word continues a name and ends it unless it is the value suffix or a form-pointer terminal (A.3) | `$#Loans.Zeile$`: `INVALID_GROUP`; `$#Loans.value$` and `$#Loans.Vordruckname$`: `MVK_UNEXPECTED_TOKEN`; `$#Store.value.x$`, `$#Store.Vordruckname.x$`, `$#Store.Usb.x$` and `$#Store.RootGroup.x$`: `INVALID_GROUP` |
| A keyword, a digit run or nothing continues no name and is a token left after it | `$#Loans.RuleGroup$`, `$#Store.1$` and `$#Store.$`: `MVK_UNEXPECTED_TOKEN`; a dot after a retired offset's digits, `$#Zeile-1.x$`: the retired code |
| A lexer fault right after a dot answers before the check its name waits for | `$#Store.%$` and `$#..Wrong.%$`: `MVK_LEXER_STANDARD_ERROR` |
| `RuleGroup`'s placement gate answers before a token left after it, and a lexer fault right after the keyword answers first | from a root-declared rule, `$#RuleGroup/Loans$`, `$#RuleGroup-x$` and `$#RuleGroup+1$`: `RULEGROUP_IMMEDIATELY_BELOW_ROOT`, and `$#RuleGroup%$`: `MVK_LEXER_STANDARD_ERROR`; one level down, `$#RuleGroup/Details$` and `$#RuleGroup-x$`: `MVK_UNEXPECTED_TOKEN` |

Sources: [group argument layers checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers), [group availability checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-availability), [inbound 2026-09-30a message reference admission](../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-message-reference-admission), [RuleGroup root gate checkpoint](../docs/sources/message-and-pointer-probes.md#src-rulegroup-shorthand-root-gate), [RuleGroup root gate on the rule carrier checkpoint](../docs/sources/message-and-pointer-probes.md#src-rulegroup-root-gate-on-the-rule-carrier), [German condition-language terminals checkpoint](../docs/sources/message-and-pointer-probes.md#src-german-condition-language-terminals), [group argument events checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events), [inbound 2026-10-01 group arguments](../docs/sources/inbound-handbacks.md#inbound-2026-10-01-group-arguments), [inbound 2026-10-01a parent walk and dotted names](../docs/sources/inbound-handbacks.md#inbound-2026-10-01a-parent-walk-and-dotted-names), [inbound 2026-10-01a event order](../docs/sources/inbound-handbacks.md#inbound-2026-10-01a-event-order), [group walk and dotted names checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names), [group parameter checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-parameter), [group parameter resolution checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-parameter-resolution), [two positions share the root gate checkpoint](../docs/sources/message-and-pointer-probes.md#src-two-positions-share-the-root-gate), [parameter surface and iteration gates checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates), [error-text row parameter checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-error-text-row-parameter), [keyed message membership checkpoint](../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15) (rows `a04`, `b02`, `h01`–`h04`, `w01`–`w05`, `rg01`–`rg03`), [message-parameter decoder checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder), [index message rendering source account](../docs/sources/message-parameter-rendering-probes.md#src-index-message-rendering), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### A.11 Rendering a rule-owned message

**A fired message carries the interpolated end-user text**: every parameter already resolved against the evaluated document, while the authored template stays in the model. Only the runtime can produce it, because it depends on the data.

| Parameter | Renders |
|---|---|
| `$Field$` | the field's display name, by the identifier-display policy below |
| `$Field.value$` | the field's value, presented by the message locale's profile below; an Enumeration value's declared label, falling back to the stored token when that value is unlabelled |
| `$Field->Category$` | the **category token the field's current stored value maps to**, not the category's name or stored value |
| `$BaseYear±n$` | the declared Base Year with the offset applied, as a plain decimal: against a Base Year of 2020, `$BaseYear$`, `$BaseYear+3$` and `$BaseYear-1$` render `2020`, `2023` and `2019`; it depends on the model alone, not on the document |
| `$#Group$` | the 1-based repetition index of the named group (below) |
| `$index(Key).value$`, `$index(Key)->Category$` | the index field's stored token or category (below) |
| `$Entity.Vordruckzeile$`, `$Entity.Vordruckname$` | unmeasured (A.8) |

- An **empty** Enumeration renders the empty string under both suffixes, while its `$Field$` label still renders.
- A number's **unit trait** (amount, percent, permille) does **not** render into `$Field.value$`: the interpolation yields the bare number, and the unit is a UI concern.

**`$Field$` delegates to the runtime identifier-display policy.** On the public service route, an available label-provider result wins exactly, including `""`; otherwise a nonempty localized model label wins; otherwise the resolved identifier's path/index debug representation is used. On the Kernel's own `validateFull`, which configures no provider, that last branch renders the field's **short name**, `Amount`, not a path; a declared label still wins. A configured provider may itself choose label-or-name, but that is caller policy rather than the Kernel's built-in fallback.

**`$Field.value$` applies a presentation profile selected by the message locale's exact tag**, not by a locale cascade or the field's declared storage format. The complete measured lookup:

| Locale tag | Date | Decimal | Grouping |
|---|---|---|---|
| `en`, `en_US`, `us` | `MM/dd/yyyy` | `.` | `,` |
| `de`, `de_DE` | `dd.MM.yyyy` | `,` | `.` |
| `ch` | `dd.MM.yyyy` | `.` | `'` |
| `fr` | `dd/MM/yyyy` | `,` | space |
| `gb` | `dd/MM/yyyy` | `.` | `,` |
| `nl` | `dd-MM-yyyy` | `,` | `.` |

- An unmapped tag, `fr_FR` included, performs no presentation and leaves the stored value unchanged.
- The mapped profile reaches Date, Number, DateTime and DateRange values; Time remains unchanged. DateTime's `T` and DateRange's declared separator become a space when presented. What a Boolean or Confirm value renders is unmeasured.
- Numeric sign and the stored fractional-digit count are preserved, so presentation neither pads `1234.5` nor drops its sign.
- **A partially known Date renders its stored spelling, zero markers and all**, rather than either interval boundary it denotes: stored `2024-06-00` renders `06/00/2024`, `2024-00-00` renders `00/00/2024`, and `0000-00-00` renders `00/00/0000`. A renderer reads the stored components and must not complete them: completing the first would print `06/01/2024`, its earliest boundary and a date the document never stated. The marker belongs to its **component**, not to a text position, and travels with it: the same omitted-day value renders `06/00/2024` under `en_US` and `00.06.2024` under `de_DE`.

**A missing or empty display value renders the referenced field format's exact default**, as the actual presentation route supplies it; the default is not inferred from or transformed by the message locale. On the modern `DocumentV2` route, a Number's **minimum** fractional digits determine **`0`**, **`0.00`** and so on, and that default keeps `.` even under `de_DE`; a String supplies **`""`**. A legacy or presentation-information route is unmeasured. Display bytes are opaque: message rendering neither reads nor renormalizes the evaluation cache.

**A name-position value or category parameter renders the cell of the row it reads.**

- A field on the rule's own levels renders the firing row's cell; a read of an enclosing level renders the enclosing row's, so `$../Base.value$` from a rule in `Rows/Sub` renders the `Rows` row the firing `Sub` row lies in; a field of a group iterated in parallel renders the row the join pairs with the firing row, not the row at the firing row's coordinate; and a keyed parameter renders the row its key selects, a field-valued key being read at its own cell.
- A literal key's spelling is the gate's identity (A.7) while its value selects the row, so on a Number index `$V.value For "2"$` renders the row keyed 2 and `$#NRows For "2"$` renders `2`, and beside a condition keyed `"02"` the parameters keyed `"02"` render that same row.
- An empty String cell renders empty.
- **A level the firing row leaves unbound renders its first row**, whether that row's cell is filled or empty: beside a keyed and a starred read, `$/Kp/Rows/Base.value$` from a rule above `Rows` renders the first row's `Base`, not the keyed row's, and an empty first-row cell renders empty; a category follows the same row.
- A field-valued key is read as a checked value, so a key cell failing its own pattern selects no row even where a row carries its text. Only the rendered locale's text is evaluated: a German text keyed by a missing literal does not fault an English rendering.

**A key that selects no row faults a value parameter only.** The rule's evaluation then fails as a runtime failure does ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)): the finding keeps its code, field and severity but is a value error even where the condition would report an omission, its whole text becomes the evaluation-fault text of `ERROR_DURING_DATA_CHECK_EVAL`, and its referenced and fill-to-fix lists are empty. In a rule that iterates rows the fault ends the row loop: earlier findings stay, later rows report nothing, and the one finding takes the iterator's first address, which the measured rule reached at its first row. The same key in a name renders the name and in a category renders empty, and the finding keeps its reference lists.

**A group parameter renders the 1-based repetition index of the group it names in the firing row, and a nonrepeatable group renders the constant `1`.**

- The index is the row's own coordinate, not a firing ordinal: over a three-row document whose rule fires on rows 2 and 3, `$#/Msg/Rows$` renders `2` and `3`, not `1` and `2`.
- **Each parameter renders the coordinate of the level it names, not the firing row's innermost one.** Under a **repeatable** root with two stacked repeatable levels below it, one message firing at consignment 2, box 3, item 4 renders `item=4`, `box=3`, `cons=2`, `$#RuleGroup$` as `4` and `$#RootGroup$` as `2`.
- The two keyword shorthands render exactly as the paths they abbreviate: `$#RuleGroup$` follows the rule's own group and `$#RootGroup$` its chain root, rendering a repeatable root's own index and the constant `1` for a nonrepeatable root. The German shorthands render the same coordinates as their English twins: on a `de_DE` model with a repeatable root, `$#RegelKontext$` advances with the firing item while `$#LfdNr$` holds at the root's own index.
- Relative and quoted spellings render as their absolute twin: over `Lines` firing on rows 2 and 3, a root-declared `$#Lines$` and a `Lines`-declared `$#../Lines$` each render `2` and then `3` beside `$#/Claim/Lines$`, on both runtime strategies, and the per-segment quote escape renders exactly as the bare spelling does.
- **This is a number, not a label or a path**, and a declared label does not change it: with labels on both the repeatable group and the root, every group parameter renders exactly as before, while labelling the *field* changes what the name position renders in the same message. So the name position renders a field's label or name and the group position a coordinate.
- **A keyed group parameter** resolves the named group's selected cache coordinate inside its current parent, using the literal key or the key field's own bound address; an unresolved selection renders `?`. A duplicate selection follows the shared message cache's insertion-order contract, not a separately inferred document order (source reading).

**The index terminal renders from the firing context.** An admitted `.value` renders the firing row's stored index token, measured as `k0` for a String index and `A` for an unlabelled Enumeration. The account behind it, source reading beyond those rows:

- An ordinary `index(Key)` reads the declared index field at its own enclosing repetition coordinates, discarding deeper firing coordinates; a parallel iteration key replaces that stored read.
- Missing or empty index text renders empty.
- The value suffix runs the index declaration's full formal conversion and renders empty if conversion fails. A String retains its text; an Enumeration uses the selected supported display locale when Enumeration presentation is enabled, otherwise its stored token.
- The category suffix looks up the raw stored token in the declaration's category mapping, independently of value conversion, and renders empty for an absent mapping.
- None of these uses an ordinary field value's default display.

> **Non-normative implementation note.** Keep a producer-specific checked parser in front of one shared left-to-right renderer. For a rule-owned template, field-name input is `{ providerResult?, modelLabel?, debugDisplay }` and field-value input is `{ displayValue?, exactFormatDefault }`. Keep rendering separate from firing and formal classification: the decision and cause are established first, and interpolation shapes only the text of that already-decided result, the keyed-row fault above being the one case where a parameter changes the finding.

Sources: [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13), [message-parameter rows checkpoint](../docs/sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15), [group parameter rendered index checkpoint](../docs/sources/message-and-pointer-probes.md#src-message-group-parameter-rendered-index), [inbound 2026-09-30a relative render](../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-relative-render), [group-parameter render reconciliation](../docs/sources/message-and-pointer-probes.md#src-2026-09-05-group-parameter-render-reconciliation), [German shorthand render reconciliation](../docs/sources/message-and-pointer-probes.md#src-2026-09-05-german-shorthand-render-reconciliation), [index message rendering source account](../docs/sources/message-parameter-rendering-probes.md#src-index-message-rendering).

### A.12 Computation messages

**A computation's message is the message of the validation rule the computation generates** ([§11 §6](09-computations.md#6-the-implicit-validation-rule-precisely)), declared in the computation's group, so the terminal set is **owned by the message, not by the rule**, and `RuleGroup` names the *owning declaration's* group rather than a validation rule's. On a computation message the absolute path, both keyword shorthands and a name-position field are admitted, and the retired `$#Zeile$` draws the same `PARAM_INVALID_IN_NEW_WORLD` it draws on a rule; the Kernel's own refusal text there calls the computation a rule and names it by its path. So "rule" in the terminal's spelling is internal vocabulary, and the terminals are not validation-only.

**Its parameters are gated by the generated rule's condition.**

- The computed target, a common precondition's reads, an alternative's precondition's reads and every alternative's operation's reads are members, while a field the computation never reads draws `INVALID_FIELD`. A precondition `GroupFilled(Returns)` admits `../Returns/Book`, which is refused without it, while the computed target is admitted either way.
- A field read only under a star refuses its value suffix `PARAM_VALUE_WITH_STARREFERENCE`, a key the generated condition never selects draws the index class, and a computation in a root group refuses `$#RuleGroup$` as a root rule does.
- Its character gates and withheld classes are A.1's and A.2's, and `RULE_HAS_NO_ERRORTEXT` asks after every declared locale as on a rule (A.1); that only declared locales are examined, each by its last entry, is unmeasured on this carrier.

**The message renders on the generated rule's firings only** ([§11 §6](09-computations.md#6-the-implicit-validation-rule-precisely)), with that row's cells and coordinates.

Sources: [terminal bundle on the computation carrier checkpoint](../docs/sources/message-and-pointer-probes.md#src-terminal-bundle-on-the-computation-carrier), [computation message members checkpoint](../docs/sources/message-parameter-rendering-probes.md#src-computation-message-members-k15), [inbound 2026-09-30a message reference admission](../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-message-reference-admission).

### A.13 Field-owned producers

**A field-owned producer's tokens name only its owning field, never a rule-relative path.** The String-pattern producer inserts the field's name and stored value as opaque text in one pass, so an inserted value never becomes template syntax, and an Enumeration's invalid-value text renders as the String-pattern text does; requiredness instead re-reads the running text on each pass (below). Whether any field-owned producer applies the rule-owned provider cascade or its empty-display default (A.11) is unmeasured.

**A String pattern's own invalid-value text accepts exactly two fixed tokens, spelled in the model's condition language whatever locale the text is written for:** `$field$` and `$field.value$` in English, `$Feld$` and `$Feld.Wert$` in German.

- The stylized `$Field$`, an actual field name such as `$Code$`, the other language's token, and a token with one non-ASCII letter, `$fïeld$`, are invalid parameters, `INVALID_PARAMETER`; the rule message's parameter-body bound, whose lexer refuses that letter, does not apply here.
- **The parameters are the pieces a split at each `$` returns once trailing empty pieces are dropped.** An empty pair inside the text (`cost $$ in capitals`) or at its start (`$$ capitals only`) is an empty parameter and invalid, while an empty pair at the very end (`capitals only $$`) or alone (`$$`) names no parameter and is admitted, and two parameters back to back (`$field$$field.value$`) are admitted. An empty pair is never a literal-dollar escape at this producer, and an admitted one renders verbatim: `Cost $$` renders `Cost $$` and `$$` renders `$$`, on both runtime strategies and on an Enumeration's invalid-value message alike.
- **Gate order:** the character gates come before dollar parity, and parity before the parameters, each withholding what follows: a tab beside an odd count draws `INVALID_CHARACTERS` alone, and a wrong name beside an odd count `WRONG_NUMBER_OF_DOLLARS` alone.
- **The character gates are a rule message's (A.1), behind an encoding gate.** Measured with both line separators, tab, `NEL`, soft hyphen, zero-width space, `U+FEFF`, `U+200E`, `U+E000`, `U+0378` and both supplementary rows; a lone surrogate draws `WRONG_ENCODING` in place of `INVALID_CHARACTERS`. The repertoire refusal is reported on the field, measured beside a named class with `U+F0000`, which draws `INVALID_CHARACTERS` and the refusal, and a lone surrogate, which draws `WRONG_ENCODING` and the refusal, while `U+1F600` draws the refusal alone; beside the line, parity and parameter classes no row reads it. An Enumeration's invalid-value message reports it on the field too.
- **An empty text is not a message:** it draws `MVK_ERROR_MESSAGE_AND_PATTERN_INVALID`, the pattern-message pairing's class, and no character class.
- **Rendering is one pass.** With template `Value [$field.value$]` and stored invalid value `$field$`, the resolved text is exactly `Value [$field$]`. The tokens are chosen by the condition language and the label they render by the requested locale: an English-language model's `$field$: $field.value$` renders the field's German label under a German locale, and a German-language model's `$Feld$: $Feld.Wert$` its English label under a US one.

**An Enumeration's invalid-value text shares the String-pattern grammar and rendering:** `$field$` becomes the label or short name and `$field.value$` the stored value outside the domain, while `$BaseYear$`, another field, a category suffix, a wrong case and `$$` inside the text draw `INVALID_PARAMETER`.

**The field-message check reports one class per field, from the first locale in declared order whose text fails.**

- With a tab in the `en_US` text and a line feed in the `de_DE` one, declaring `en_US` first draws `INVALID_CHARACTERS` and declaring `de_DE` first `INVALID_LINEBREAK`, whichever entry the model writes first.
- Of two entries for one locale the later is asked, and a pattern message for a locale the model does not declare is never asked: a tab for `fr_FR` and `U+1F600` for `de_DE` are both admitted; no row reads an Enumeration's message in such a locale.
- An Enumeration's invalid-value message meets the same gates, a tab drawing `INVALID_CHARACTERS` and `$Status$` `INVALID_PARAMETER` while `$field$` is admitted.
- A String message with no pattern meets them too, a tab drawing `INVALID_CHARACTERS` beside `MVK_ERROR_MESSAGE_AND_NO_PATTERN`, and that pairing class needs a text that is not blank: with no pattern, an empty and a single-space `en_US` text are admitted, a tab-only one draws `INVALID_CHARACTERS` alone, and the text `capitals` draws the pairing class in the declared `en_US` and nothing in the undeclared `fr_FR`.
- A required field's own message is not checked (below), a tab there being admitted.
- A field its own `ONLY` variant filter deletes is never asked, as the filter deletes a rule.

**A field whose path, or an ancestor group's, draws a path class draws nothing about its message.** A tab in the pattern message of a field named `Codeé`, `1Code`, `Co.1de`, `Co._de`, `Co..de`, `Co.` or `Co-de`, or beneath a nested group named `Parté` or `1Part` or a root group whose name draws the path class such as `Parté`, draws `MVK_PATH_INVALID` and no `INVALID_CHARACTERS`, and a `/` in either name draws `MVK_PATHS_INCONSISTENT` and no `INVALID_CHARACTERS`. A name class that is not a path class does not have that effect: a field named `Co.de`, `Co:de` or `_Code`, a group named `Teilä`, and a root group named `1Claim` each keep the message's `INVALID_CHARACTERS` beside whatever name class they draw; the discriminating pair is `Co.de` against `Co.1de`, both dotted. A rule's refusal elsewhere in the group withholds nothing on the field: a rule condition's parse error or a missing error target is reported beside the field's `INVALID_CHARACTERS`.

**Requiredness is a distinct field-owned producer whose text the Kernel never checks.** Every text is admitted, and rendering replaces five fixed tokens in succession over the whole text, in a model of either condition language:

| Pass | Token | Becomes |
|---|---|---|
| 1 | the literal `$<fieldName>.Value$` | the empty text |
| 2 | `$Feld$` | the field's label for the message locale, or its short name when it declares none |
| 3 | `$field$` | the same |
| 4 | `$Feld.Wert$` | the empty text, since the producer fires only on an empty field |
| 5 | `$field.value$` | the empty text |

- Every other dollar sequence stays verbatim: `$$`, an unclosed `$field`, `$FIELD$`, `$field.Wert$`, `$ field $`, `$BaseYear$`, another field's name, a category or key suffix and a group argument.
- **The replacements are successive rather than one scan:** `$field$Feld$` renders `$field` followed by the label, `$Feld.Wert$field$` keeps `$Feld.Wert` before it, and `$field$<fieldName>.Value$` keeps `$field` alone, so the literal token goes first.
- **Each pass reads the running text**, so a token a label carries in is replaced by a later pass and by no earlier one: the label `Carrier $field$` under `$Feld$` renders `Carrier Carrier $field$`.
- Whether the field's own name written in place of `<fieldName>` is replaced is unmeasured.
- A field without a template takes the catalog's default text.

Sources: [inbound 2026-09-26n field message gates](../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates), [count placement overlap list grid checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-count-placement-overlap-list-grid), [inbound 2026-09-27a field message render](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-field-message-render), [inbound 2026-09-26m message characters](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-message-characters), [inbound 2026-09-27a element paths](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-element-paths), [field-owned message producers checkpoint](../docs/sources/message-parameter-rendering-probes.md#src-field-owned-message-producers), [inbound 2026-10-18](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18).

### A.14 Parameter tokens and declared names

**A parameter's name token is wider than any group may be named.** The Kernel refuses to declare a group named `1Rows` or `Ro-ws` with `MVK_PATH_INVALID`, and a digit-initial or `:`-bearing name is refused on every declaring carrier measured, so the token grammar's digit-initial and `:`-bearing names are well formed but no witness of one resolving is known; their `INVALID_GROUP` is the only answer measured.

**The declared-name alphabet is the carrier's, and it is not one law;** the per-carrier table, its rules and a rule name's classes are [data model §1.3](01-data-model.md#names-groups-and-texts)'s.

Sources: [parameter token versus group declaration alphabet checkpoint](../docs/sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet).

---

## Part B — §14 CustomCondition — the escape hatch

**When the language cannot express a check, `CustomCondition <Name>` delegates the decision to host code that the consuming system registers.** The engine parses and places the rule like any other, and calls out to that implementation to decide whether the leaf fires.

```
FieldFilled(id) And CustomCondition NotReverse
```

### B.1 The name

`<Name>` is a name token of [concrete syntax §1](12-concrete-syntax.md#1-lexical-structure), a digit-only name included. A name that collides with a keyword is single-quoted: `CustomCondition 'Today'` names the callback `Today`.

### B.2 Static constraints

- **Forbidden in computation rules** ([§11 §1](09-computations.md#1-the-ground-rules)) and **inside filter (`Having`) conditions**.
- **It does not exempt the rule from the error-field rule** ([§9](07-repetition-and-iteration.md)): in the example the `FieldFilled(id)` conjunct references the error field, while a **bare** `CustomCondition X` referencing no field is rejected, `MVK_ERROR_FIELD_NOT_REFERENCED`.
- **In a parallel rule a `CustomCondition` leaf guards no iteration.** Beside a field pair it is admitted under `And`, in either order, while `pair Or CustomCondition X` draws `MVK_PARALLEL_ITERATION_INVALID`, as two negative presence leaves and `pair Or FieldFilled(Note)` do; an `Or` arm pairing a joined read with the leaf, `pair Or ([Supply/Headcount] > 0 And CustomCondition X)`, is admitted.

Sources: [parallel custom condition checkpoint](../docs/sources/key-join-and-parallel-probes.md#src-parallel-custom-condition), [parallel reach checkpoint](../docs/sources/key-join-and-parallel-probes.md#src-k22-parallel-custom-reach).

### B.3 The invocation

**When ordinary rule evaluation reaches `CustomCondition X`, the Kernel invokes the registered callback with four inputs:** the document/data view, the partial-validation relevant-entity set (or an all-relevant marker during full validation), the complete set of formally incorrect field instances, and the current rule error-field `PartiallyKnownDocumentMultiPointer` ([§2.1](01-data-model.md#21-repetition-contexts-the-iteration-environment)). Under parallel iteration the pointer may carry `UNKNOWN` and then has no exact-pointer counterpart: the callback is invoked per joined row with that row's error-field pointer, a coordinate being `UNKNOWN` where the error side is unmatched and no outer row binds it.

- **The data view hands over a placed empty or blank String as a value.** A callback asking the view for a field's value receives none only where the cell is absent: a condition answering whether that value exists holds for `""` and for `" "` as for `"x"`, on both strategies.
- **The view is the whole document whatever the call's relevant set:** a repeatable cell reads the same way when it is not relevant, and so does a cell of a row beyond its group's declared capacity, which the same call reports as formally invalid; the callback is still called only at the relevant iterated rows.
- **Formal errors do not automatically suppress the invocation.** Only the callback knows its hidden dependencies, so the callback contract requires it to inspect relevance and the formal-invalid inputs and return `false` when one of its own necessary fields cannot be used; unrelated formal errors need not decide it.
- **The result:** `true` contributes a **VALUE** firing leaf and `false` a `notFired` leaf, after which normal `And`/`Or` composition and rule emission apply ([§12 §3](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-)).
- **Empty-row eligibility belongs to the complete condition, not to a callback-internal read set the Kernel cannot see.** A `CustomCondition` leaf is structurally classified as able to fire on empty ([§2](03-empty-and-required.md)); the common `FieldFilled(id) And CustomCondition X` form is blocked on an empty row by its `FieldFilled` conjunct, while `CustomCondition X Or FieldFilled(id)` may reach the callback on that row.

Sources: [k22 static s6 checkpoint](../docs/sources/group-count-topology.md#src-k22-static-s6) (`when-filled`), [k22 runtime r7 checkpoint](../docs/sources/group-count-topology.md#src-k22-runtime-r7) (`rB`), [parallel reach checkpoint](../docs/sources/key-join-and-parallel-probes.md#src-k22-parallel-custom-reach).

### B.4 Registration and reach

- **Registration lookup is deferred until the leaf is reached.** A validation-call factory replaces the registered fallback chain, including when that factory returns no match; without a call-specific factory, the first matching registered factory wins.
- **A reached name no factory resolves fails the rule, not the validation.** The rule reports its own code at its error field as a VALUE message with empty referenced and fill-to-fix sets, through the runtime-failure handler of [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification), which owns its error address, the rows and joined rows it still reports and the iterator start a partial call gives it ([§12 §5.2](10-validation-and-polarity.md#52-which-rules-run-and-where)).
- **Whether the name is reached follows the two passes of rule evaluation** ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)), as a callback's call count does. In a parallel rule, a field pair whose fill quantifier does not fire on a joined row also ends the `And` there.
- A callback may also throw through the documented host failure route, which is outside this account. Neither a missing registration nor a throw is silently converted into "did not fire".

Sources: [custom-condition call checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-custom-condition-calls), [inbound KF52](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-reconciliation), [parallel reach checkpoint](../docs/sources/key-join-and-parallel-probes.md#src-k22-parallel-custom-reach).

### B.5 A rule reporting on a group

**On a rule whose error target is a group, every reached `CustomCondition` fails the rule the same way, whatever its name resolves to.** The rule reports its own code once, as a VALUE message with empty referenced and fill-to-fix sets, at the group's first address, whatever the name answers and whether or not it is registered; the callback is never invoked, and the name is never looked up: a factory recording its queries in order sees a field-target rule's name looked up and then called, and the group-target rule's name not at all. This holds on a once and a repeatable rule, with the leaf first or behind a guard, on the branch of an `Or` reached when the other operand does not fire, and beside a join, while a leaf the condition never reaches raises nothing and a field target's leaf is called per row as B.3 says. Partial validation reports no group-target rule ([§12 §5.2](10-validation-and-polarity.md#52-which-rules-run-and-where)).

Sources: [group-target custom abort checkpoint](../docs/sources/key-join-and-parallel-probes.md#src-k22-group-target-custom-abort), [inbound 2026-10-25](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-25).

### B.6 The extensibility surface

**Custom conditions and [custom field types](06-strings-and-enumerations.md#a3-custom-field-type-validation) are the engine's only known custom hooks**; no custom *computation* or function is known. A custom field validator contributes a formal cell observation; `CustomCondition` contributes a rule-predicate result. A computation's operation vocabulary is closed ([§11 §1](09-computations.md#1-the-ground-rules)), and `CustomCondition`, the one predicate hook that could otherwise reach a computation, is barred there.

> **Non-normative implementation note.** Introduce an explicit `CustomConditionInvocation` carrying the document/data view, full-versus-partial relevance, the formal-invalid address set and the current error-field pointer, then parameterise the successful-result fragment by `customConditions : Name → CustomConditionInvocation → Bool`, separate from the custom-field-validator map in `World`. The row gate and surrounding condition decide whether the oracle is invoked; do not derive an `unknown` result merely from a nonempty formal-invalid set. Oracle `true` yields `.fired .value`, and `false` yields `.notFired`. An implementation may make the oracle pure and total for reproducibility; the Kernel's host runtime enforces neither, and purity alone does not imply locality or monotonicity, so whole-rule theorems must exclude custom conditions or require an explicit oracle contract.

---

## Checklist for §13 + §14

- [ ] A rule-owned template splits at `$`: text and parameters alternate, the count must be even, an empty parameter outside a parameter is one literal `$`, and each parameter is checked on its own; the character tiers (BMP repertoire, line break, control, parity, parameter body) run in order, the codeless repertoire refusal standing beside the named classes; only declared locales are checked, each by its last entry, and every declared locale must be answered.
- [ ] A refused declaration withholds the error-text checker's classes, the parse and index-key classes included, and leaves the message's presence classes standing.
- [ ] The parameter grammar has two positions over one lexer; the ten terminals are selected by the condition language, three are keywords, and four quote-exempt words may end a dotted name; a suffix precedes the key.
- [ ] A parameter is refused at the first event its parser meets: lexer faults when fetched, syntax faults where met, checks where their grammar rule ends, the look-ahead window answering before a lookup.
- [ ] The root gate is shared by both positions; below it the name position answers `INVALID_ENTITY` and the group position `INVALID_GROUP`.
- [ ] An unkeyed field reference passes the membership gate over the condition's footprint, a group read making every field inside it a member; the value suffix adds the existential star gate and the value-validation gate; the category suffix checks a name, an Enumeration and a declared category, after membership.
- [ ] A keyed parameter is gated on the semantic index by spelling, exactly and in both directions, before the suffix gates, and needs no presence guard in the name position.
- [ ] Form pointers carry no membership gate; the rule-group terminal refuses every field-shaped spelling; the Base Year needs only a declared Base Year.
- [ ] The index terminal resolves a bare short name on the error path, scans the condition's same-named index references in full-name order for repeatability, requires a suffix, and compares the referenced declarations per suffix.
- [ ] A group parameter passes the ordered check: retired terminal, shorthand gates, lookup, key events, availability, index-reference mode, star reference, keyed presence guard, then the end of the argument.
- [ ] Rendering: `$Field$` uses provider result → nonempty model label → debug display (short name on `validateFull`), a present empty provider result still winning; display bytes are opaque and the evaluation cache is neither read nor renormalized; `$Field.value$` uses the exact-tag presentation profile, the stored spelling of a partial Date and the exact format default for a missing value, never the unit trait; each parameter renders the row it reads; a key selecting no row faults a value parameter; a group parameter renders the coordinate of the level it names.
- [ ] A computation's message is its generated rule's: the same terminals and gates, membership over everything the computation reads.
- [ ] Field-owned templates stay distinct: the String-pattern and Enumeration grammar takes the condition language's two tokens, rejects an empty `$$` inside the text or at its start and admits one at its end or alone, reports one class per field from the first failing locale in declared order, and inserts opaque bytes once; the requiredness text is never checked and replaces five fixed tokens in succession, the literal `$<fieldName>.Value$` first.
- [ ] Declared-name alphabets are per carrier; a parameter token may be well formed and still name no declarable group.
- [ ] A reached `CustomCondition` receives document, relevance, formal-invalid addresses and the current error pointer; its callback, not an evaluator pre-gate, decides its hidden dependencies; `true` is VALUE and `false` `notFired`; whole-condition structure decides empty-row reach; the rule must reference the error field; the construct is **barred** in computations and filters.
- [ ] A reached unregistered name fails its rule through the runtime-failure handler, and on a group-target rule every reached `CustomCondition` does, unlooked-up; a throwing host callback is outside this account.
- [ ] A `CustomCondition` result is distinct from the declaration-driven custom-field formal observation owned by §7.
- [ ] The known extensibility surface is custom conditions and custom field types; no custom computation or function is known.
