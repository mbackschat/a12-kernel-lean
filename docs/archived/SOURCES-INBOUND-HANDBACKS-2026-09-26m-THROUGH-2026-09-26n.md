# Archived inbound handback checkpoints of 2026-09-26m and 2026-09-26n

This immutable archive contains the 6 terminal inbound handback receipts reviewed from the peer's `-2026-09-26m` and `-2026-09-26n` letters, frozen when [`../SOURCES.md`](../SOURCES.md) neared its 195,000-byte archiving threshold. Every obligation they recorded already lives in its gap or implementation owner. Stable `inbound-` anchors remain authoritative here, and every original `SOURCES.md#inbound-…` citation still resolves through the anchor the hub keeps.

### Inbound 2026-09-26n handback

<a id="inbound-2026-09-26n-field-message-gates"></a>
#### Reviewed 2026-09-26n field-message handback — a field type's own message takes its condition language's two tokens as the pieces of a split that drops trailing empty pieces, reports one class per field from the first failing declared locale, and draws nothing where a path class stops the element walk

a12-dmkits revision `37b68148da09d00ebe300941700901b47df24d3f` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26n`, frozen as sent in the user's exchange directory with SHA-256 `7639da2d939436bf88245fa9e0ec19481befa39706f8f603dd07dba8fbbfab57`. The locks were read at that revision, not run here. It answers no ledger entry and creates none. Its §7 names the field checker's order, its per-language loop and the element walk's early return as source-read hypotheses, and its §8 reports the peer's own records; neither is recorded as a claim.

**Claim.** Its §1 (`FieldTypeMessageTextLawsTest`), a String `Code` whose `[A-Z]+` pattern carries its own message in the one declared `en_US`, the condition language English unless a row says German. `capitals only`, `$field$ takes capitals`, `$field.value$ is not capitals`, `$field$$field.value$`, `capitals only $$` and `$$` are admitted. `$field takes capitals` draws `WRONG_NUMBER_OF_DOLLARS`, as does `$Code$ and $field` alone.

`$Field$ …`, `$Code$ …`, `cost $$ in capitals`, `$$ capitals only` and, under English, `$Feld$ takes capitals` draw `INVALID_PARAMETER`. A tab beside an odd count draws `INVALID_CHARACTERS` alone. Under German, `$Feld$ …` and `$Feld.Wert$ …` are admitted and `$field$ …` draws `INVALID_PARAMETER`. The peer's `kf42`, the source of this project's former reading that `$$` is refused at this producer, is corrected in place.

Its §2, with a tab in the `en_US` text and a line feed in the `de_DE` one where both are defective. Declaring `en_US` first draws `INVALID_CHARACTERS` and declaring `de_DE` first `INVALID_LINEBREAK`, in either entry order. Only the second declared locale defective draws `INVALID_CHARACTERS`. Of two `en_US` entries a tab in the first is admitted and in the second draws `INVALID_CHARACTERS`. A tab for the undeclared `fr_FR` is admitted, and a lone low surrogate draws `WRONG_ENCODING`.

A String message with a tab and no pattern draws `INVALID_CHARACTERS` with `MVK_ERROR_MESSAGE_AND_NO_PATTERN`. An Enumeration `Status`'s invalid-value message draws `INVALID_CHARACTERS` for a tab and `INVALID_PARAMETER` for `$Status$ is not allowed`, and admits `$field$ is not allowed`. A required field's message with a tab is admitted, an empty pattern message draws `MVK_ERROR_MESSAGE_AND_PATTERN_INVALID`, and a tab on a field its own `ONLY` filter deletes is admitted.

Its §3, a tab in the named field's pattern message. A field named `Codeé`, `Co.1de` or beneath a group named `Parté` or `1Part` draws `MVK_PATH_INVALID` alone, a plain message the same for `Codeé` and `Parté`. `1Code` draws `MVK_PATH_INVALID` with `MVK_NAME_STARTS_WITH_DIGIT_A12_DV`, and `Co/de` or a group `Pa/rt` `MVK_PATHS_INCONSISTENT`. `Co.de` and `Co:de` draw `INVALID_CHARACTERS` with `MVK_NAME_INVALID_DOT_COLON_A12_DV`, and `_Code`, a group `Teilä` and a root group `Schadenä` `INVALID_CHARACTERS`. A root group `1Claim` draws `INVALID_CHARACTERS` with `MVK_NAME_STARTS_WITH_DIGIT`.

Its §4, a rule `ProbeRule` beside the field. The condition `FieldFilled(Reference) And And FieldFilled(Code)` draws `INVALID_CHARACTERS` with `MVK_UNEXPECTED_TOKEN`, and the error target `../NoSuchField` `INVALID_CHARACTERS` with `MVK_ERROR_FIELD_MISSING` and `MVK_MISSING_ERROR_FIELD`.

Its §5 takes §3's group rows against the peer's `kf315`, corrected in place: a group admits `ä` and `ö` and refuses `é`. The letter reports `Ö` measured too; the peer's pointer places it on a root group named `Ördner`, admitted in `DeclaredNameShapeLawsTest` at the same revision and read there, and the letter names the group pattern's seven German letters as source-read.

Its §6 (`ModelTextRepertoireLawsTest`), `U+1F600` in a String type's pattern message and in an Enumeration's invalid-value message draws the codeless repertoire refusal on the field, and in a pattern message for the undeclared `de_DE`, written into the model file, is admitted.

**Lean.** Corrected. [`elaborateStringPatternMessageTemplate`](../../A12Kernel/Elaboration/StringPatternMessage.lean) now takes the condition language's two tokens and reads the parameters as the split pieces with trailing empty pieces dropped. [`namedStringPatternDiagnostic?`](../../A12Kernel/Elaboration/ValidationMessageDiagnostic.lean) projects the parity, parameter and empty-text classes, and [`StringPatternMessage`](../../A12Kernel/Conformance/StringPatternMessage.lean) locks every §1 row and the empty one. An admitted trailing pair renders as literal dollars, an assumption [SG25](../gaps/strings-and-messages.md#gap-sg25) records.

A field message has no locale, and no Lean surface carries a second locale, an Enumeration's invalid-value message, a message with no pattern, a required field's message, a field's variant filter, or a rule beside the field, so §2's other rows, §4 and §6's Enumeration and undeclared-locale rows have none. §6's String-pattern row is locked as the codeless repertoire refusal in [`StringPatternMessage`](../../A12Kernel/Conformance/StringPatternMessage.lean), and §2's lone surrogate has none, since a Lean `Char` cannot hold one. §3 fits [`EntityContainerIntegrity`](../../A12Kernel/Elaboration/EntityContainerIntegrity.lean)'s blocking stages, which stop an entity's check and the walk into its children, but that module takes a path's validity as an input and composes with no field-message check, so neither §3 nor §5 has a Lean row.

### Inbound 2026-09-26m handback

<a id="inbound-2026-09-26m-message-characters"></a>
#### Reviewed 2026-09-26m message-character handback — a rule message's two character gates are the four line characters and Java's `\p{C}` asked per code point, and a computation's and a field's message draw the same classes on the rows each carries

a12-dmkits revision `2c43d17e4e35381dff4017998990fbf05ed0e2ea` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26m`, frozen as sent in the user's exchange directory with SHA-256 `a7dc83578a1a3d61700787c9163b3ced88009f4d3486900132f6e63c88e3ce21`. The locks were read at that revision, not run here. It answers no ledger entry and creates none. Its §7 reports the peer's own records, and its §2 names the field checker's order, its parity class, its Enumeration carrier and its per-language pass as source-read and not yet measured, the parameter class being measured on the String carrier by the peer's `kf42`; none of those is recorded as a claim.

**Claim.** Its §1 and §2 (`ErrorTextCharacterGateLawsTest`, `MessageTextControlCharacterLawsTest`), a rule at `/Claim` reporting on `Reference` beside a String `Code` whose `[A-Z]+` pattern carries the field message. On the rule's message `U+2029`, and `U+2028` beside a tab, draw `INVALID_LINEBREAK` alone; `NEL`, `U+FEFF`, `U+200E`, `U+E000` and the unassigned `U+0378` draw `INVALID_CHARACTERS`; a lone high surrogate, `U+F0000` and `U+E0001` draw the codeless repertoire refusal with `INVALID_CHARACTERS`, and `U+1F600` the refusal alone.

The field's message draws the same two classes for each separator and each of tab, `NEL`, `U+200B`, `U+00AD`, `U+FEFF`, `U+200E`, `U+E000` and `U+0378`, admits `U+00A0`, answers a lone surrogate with `WRONG_ENCODING` and the refusal on the field, `U+F0000` and `U+E0001` with `INVALID_CHARACTERS` and the refusal on the field, and `U+1F600` with the refusal alone.

`see $NoSuchField$` draws `INVALID_ENTITY`, beside `U+200B` `INVALID_CHARACTERS` alone and beside `U+2028` `INVALID_LINEBREAK` alone, and the unclosed `see $Reference` beside `U+200B` `INVALID_CHARACTERS` alone. A computation's message draws `INVALID_LINEBREAK` for a line feed and `U+2029` and `INVALID_CHARACTERS` for a tab and `U+FEFF`, the four rows of `MessageTextControlCharacterLawsTest` at that revision. The predicates are the peer's source reading of the Kernel's message-text checks; this project confirmed on a local JDK 21 that its `\p{C}` matches `NEL`, `U+FEFF`, `U+200E`, `U+E000`, `U+0378`, `U+F0000`, `U+E0001` and a lone high surrogate, and not `U+2029`, `U+00A0` or `U+1F600`.

**Lean.** Partly adopted. [`namedStringPatternDiagnostic?`](../../A12Kernel/Elaboration/ValidationMessageDiagnostic.lean) now projects the field message's two character classes and its parameter class, measured for a named parameter by [`EXP-2026-07-30-01`](A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#exp-2026-07-30-01), locked in [`StringPatternMessage`](../../A12Kernel/Conformance/StringPatternMessage.lean), and [`ValidationMessageAuthoring`](../../A12Kernel/Conformance/ValidationMessageAuthoring.lean) locks the separator and withholding rows.

With the owner's approval the shared control predicate is now [`JavaOtherCategory`](../../A12Kernel/Elaboration/JavaOtherCategory.lean), JDK 21's `\p{C}` as a pinned table, and both producers add the repertoire refusal through one composition, so every row above that Lean can spell is locked; a lone surrogate has no `Char`. A computation's message template is not modelled.

<a id="inbound-2026-09-26m-model-texts"></a>
#### Reviewed 2026-09-26m model-text handback — the codeless repertoire refusal meets every text of a rule, a computation and a field or group's names, annotations and enumeration entries, once per element, but no label

It shares the provenance of the message-character record above and takes the letter's §3.

**Claim.** Its §3 (`ModelTextRepertoireLawsTest`), a rule at `/Claim` reporting on `Reference`, each text carrying `U+1F600` in turn with an `é` twin. The refusal names the rule for its condition's literal, comment and bare text, the last beside `MVK_LEXER_STANDARD_ERROR`, its error code, its name and its message; the computation, named a rule, for its operation's literal and comment, its common and alternative precondition, its name and its message; the field for its annotation name and value and an enumeration value and label, and beside `MVK_PATH_INVALID` for its name; and the nested group for its name, beside `MVK_PATH_INVALID` and repeated on its field and on a rule inside it, and for its annotation name and value.

The model's, the group's and the field's labels, and a message or an enumeration label in the undeclared `de_DE`, are admitted. Two texts of one rule or one field draw one refusal; a lone high or low surrogate in a message draws it with `INVALID_CHARACTERS`. The `é` twins are admitted except outside a literal, `MVK_LEXER_STANDARD_ERROR`, and on the error code and the field name, which draw their own codeless laws where `U+1F600` draws the refusal in their place.

With `see 😀` as the message, `../NoSuchField` draws the refusal with `MVK_ERROR_FIELD_MISSING` and `MVK_MISSING_ERROR_FIELD`, `../Summary` the refusal with `MVK_ERROR_FIELD_NOT_REFERENCED`, and `variantFilter` `ONLY ["premium"]` is admitted, each beside a plain-message twin drawing the same without the refusal.

**Lean.** No change. The rule message's refusal was already co-reported; condition, name, annotation and enumeration texts carry no repertoire check and a message has no locale, which [SG25](../gaps/strings-and-messages.md#gap-sg25) records.

<a id="inbound-2026-09-26m-error-target-paths"></a>
#### Reviewed 2026-09-26m error-target handback — a declared error target takes `..` lexically from the rule element, and a group target is judged like an unnamed field except the rule's own group, which fails the build

It shares the provenance of the message-character record above and takes the letter's §4.

**Claim.** Its §4 (`ErrorFieldRelativePathLawsTest`, `kf284` extended), `/Order` holding a String `Code`, a group `Meta` holding a String `Ref`, and a repeatable `Lines`, each rule in `/Order` over `FieldFilled(Code)` unless placed otherwise. `../Meta/../Code` is admitted, `../Meta` and `../Meta/Ref/..` draw `MVK_ERROR_FIELD_NOT_REFERENCED`, `../Code/..` and `../../Order` fail the build, and `Code` draws `MVK_ERROR_FIELD_MISSING` with `MVK_MISSING_ERROR_FIELD`. From a rule in `/Order/Meta` over `FieldFilled(Ref)`, `../../Meta` fails the build and `../..` draws `MVK_ERROR_FIELD_NOT_REFERENCED`. A computation in `/Order` into `../Code` is admitted, and into `..` or `../Meta` fails the build. A failed build carries an internal exception's text and no class.

**Lean.** Docstring only. [`ErrorFieldDeclaration`](../../A12Kernel/Elaboration/ErrorTargetDeclaration.lean) now names the companion member class beside its missing class. Rule and computation targets are field identities, so no relative path or group reaches them, which [SG9](../gaps/paths-and-groups.md#gap-sg9) and [SG4](../gaps/keystone.md#gap-sg4) record.

<a id="inbound-2026-09-26m-index-key-pattern"></a>
#### Reviewed 2026-09-26m index-key handback — a String index key must meet its length bounds and its pattern, the pattern matched over code points

It shares the provenance of the message-character record above and takes the letter's §5.

**Claim.** Its §5 (`CheckerIndexKeyConstantAgreementTest`, `kf481`), each probe `Sum(<group>/Amount For "<key>") > 0` from the root, where an admitted key draws `MVK_PARAMSIZE_INVALIDN` and a refused one `MVK_INDEX_VALUE_INVALID`. Admitted against refused: over `[A-Z]+-[0-9]{2,3}` `AB-12` against `AB-1234` and `-12`, over `[^0-9]*` `abc` against `a1`, over `[a-z]?[0-9]*` `5` and `a` against `ab`, over `[0-9]{3,}` `123` against `12`, and over maximum length 3 with `[A-Z]+` `AB` against `ABCD` and `ab`. Over `.{2}` `ab` is admitted and `a` refused, and with maximum length 1 `ab` is refused. Over `[^0-9]{2}` `😀a` is admitted and `😀` refused, each beside the repertoire refusal. The peer read the length check as asked before the pattern.

**Lean.** Docstring only. [`SemanticIndexAdmissionKey.constant`](../../A12Kernel/Elaboration/SemanticIndexAdmission.lean) takes the key's fit as an input and now says what decides it for a String; deriving it is [SG9](../gaps/paths-and-groups.md#gap-sg9)'s.

<a id="inbound-2026-09-26m-marked-keyed-read"></a>
#### Reviewed 2026-09-26m marked-keyed-read handback — a `$`-marked keyed read in a body draws the index class from a root rule reporting at the root too, and after the parse

It shares the provenance of the message-character record above and takes the letter's §6.

**Claim.** Its §6 (`CheckerFilterBodyAgreementTest`, `kf487`), on the `-26d` claims policy with each rule at the root. Reporting on `Reference`, `Sum(Claims*/Paid Having [Claims/Units] > 1 And [$Orders/Note For "A"] == "x") > 0` draws `MVK_SEMANTIC_INDEX_NOT_ALLOWED`. Reporting on `Claims/Notes`, `Sum(Parties*/Count Having [Parties/Name] == [$Orders/Note For "A"]) > 0 And Sum(Parties*/Count Having [Orders/Note] == "y") > 0` draws `MVK_INVALID_ITERATION_IN_FILTER_CONDITION` alone.

**Lean.** No change. A filter reference carries no key, so neither row has a spelling.
