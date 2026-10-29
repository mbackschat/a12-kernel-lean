# 12 — Concrete syntax: lexing, keywords, directives, grammar sketch

The other chapters describe how a condition *evaluates*; this chapter describes how a condition or an operation is *written*: the tokens, the grammar, the shape of each operator's arguments, and the layer at which a malformed text is refused and with which class. It is a **sketch of the surface**, not a transcription of the engine's grammar file; production *names* are borrowed for orientation, and the EBNF below is an original re-expression.

Section numbers inside this chapter are written "concrete syntax §n"; a bare `§n` in a link label is the taxonomy number of the linked chapter.

---

## 1. Lexical structure

**The lexer turns a text into tokens — keywords of the model's condition language, names, number literals, quoted literals, symbols, comments and the `#Zeile` token — separated by whitespace, and refuses a character it cannot take with `MVK_LEXER_STANDARD_ERROR`.** A token is lexed only when the parser first needs it (concrete syntax §3.1), so a lexical defect is reported only if no earlier failure answers first.

**Keyword languages.**

- **A model's `conditionLanguage` selects one keyword map, and the two maps are nested rather than parallel.** The model writes the code bare or as an object's `code`, and the two spellings declare one language ([member binding](01-data-model.md#member-binding)). The supported codes are exactly `en_US` and `de_DE`; a model declaring any other code is refused before lexing begins, by a class no chapter states. There is no fallback to the other map: a spelling the selected language does not carry lexes as an ordinary name. So `And` is a connective in an English model and a plain field name in a German one, and `Und` is the reverse.
- **The maps hold 112 English spellings against 125 German.** Every English keyword has a German twin; the 13 extra German spellings are the H-model form constructs listed in concrete syntax §5, which have no English spelling and are keywords only in a German model.
- **The language cannot be switched under authored rules.** Changing a model's condition language once its rules are written in the other language is refused with one `MVK_UNEXPECTED_TOKEN` per rule, naming the keyword that no longer parses.
- **Symbols are language-neutral.** The comparison, arithmetic and path symbols `== != < <= > >= + - * / ^ -> $` are identical in both languages. The infix arithmetic set is exactly `+ - * / ^`; `%` is no operator and is refused by the lexer.

**Keyword spelling.** The lexer enumerates the accepted spellings of each keyword and never folds case:

| Family | English spellings | German spellings |
|---|---|---|
| conjunction | `And`, `and`, `AND` | `Und`, `und`, `UND` |
| disjunction | `Or`, `or`, `OR` | `Oder`, `oder`, `ODER` |
| value-list separator | `In`, `in`, `IN` | `In`, `in`, `IN` |
| range separator | `To`, `to`, `TO` | `Zu`, `zu`, `ZU` |
| every other keyword | its one spelling in concrete syntax §5 | its one spelling in concrete syntax §5 |

Any other casing is not that keyword: `fieldfilled`, `FIELDFILLED` and `aNd` are refused. The other language's range keyword is an ordinary name, so `ValueNotConsistent(Tier Zu Premium, "gold")` in an English model and `WertNichtKonsistent(Tier To Premium, "gold")` in a German one draw `MVK_UNEXPECTED_TOKEN` in all three casings, where the native spelling reaches the operand gate; `In` parses in both languages.

**Names.**

- **A name is a run of name characters:** ASCII letters, ASCII digits, `_`, `:` and the German letters `ÄÖÜäöüß`. An unquoted name may begin with a digit, `_` or `:` and may consist of digits only. Hyphen, dot, slash and whitespace are not name characters. Field and group names are case-sensitive. Measured scope: custom-condition names ([§14](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)) and message parameters ([§13 A.3](11-messages-and-custom.md#a3-the-parameter-grammar)); that a condition's path segments share the alphabet is unmeasured.
- **A name that collides with a keyword must be single-quoted** where it stands in a path: `Order/'Date'` names a field called `Date`. A quoted name begins with a non-digit name character and otherwise uses the same alphabet; it is lexed as one unit, so an illegal character inside it is a lexical defect, `MVK_LEXER_STANDARD_ERROR` (measured in message parameters, [§13 A.3](11-messages-and-custom.md#a3-the-parameter-grammar)).
- **Where a position takes only some names, its own rule says so.** The suppress-warning preamble's name position is one: a digit-initial name there, `7_DAYS`, is refused `MVK_UNEXPECTED_TOKEN` (measured; concrete syntax §4).

**Whitespace and comments.**

- **Whitespace is exactly five characters** — space, CR, TAB, FF and LF — which separate tokens and are otherwise insignificant. Any other space character where whitespace would separate tokens is refused `MVK_LEXER_STANDARD_ERROR`: measured on a no-break space, a vertical tab, an em space, an ideographic space and U+0085. Inside a string literal every character but a quote is admitted.
- **A comment runs from `;;` to the next CR or LF**, so a lone carriage return ends one as a line feed does and the text after it is live. Every other character inside a comment is admitted, a no-break space, a vertical tab and a non-ASCII letter included.
- **A comment is a token the grammar places, not skippable trivia.** Measured admitted positions: before and after a condition branch, and before an arithmetic operand after `+`. Measured refused positions, each `MVK_UNEXPECTED_TOKEN`: inside a predicate's argument list, before a rounding operator's place count, and between the sign and the digits of a number literal or on either side of its point (concrete syntax §3.3). Every other position — after `-`, `*`, `/`, `^` or a comparator, inside `[ ]`, inside a filter body — is unmeasured. In the engine's round-trip a leading comment is preserved on write-back.

**Digits and special tokens.**

- **Digits are ASCII.** A number literal and a rounding digit count take only `0`–`9`: `[BaseFee] > ٣`, a fullwidth `５`, `1٣`, `3.٥` and `RoundDownValue(Quantity, ٣)` draw `MVK_LEXER_STANDARD_ERROR`, although the document reader converts a stored Arabic-Indic digit. A date constant's digits are ASCII too ([§6](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-)).
- **A number literal is a digit run with an optional point and fractional digit run;** whitespace may stand inside it, a comment may not, and one leading `-` belongs to it (concrete syntax §3.3). Its total digit count is ungated (concrete syntax §2).
- **`#Zeile`, the H-model row iteration, is one language-independent token** to which the grammar gives no production. In an English model it is lexed and then refused by the grammar, `MVK_UNEXPECTED_TOKEN` (measured); in a German model its class is unmeasured. `#Zeil`, a lone `#` and a lone `!` are refused by the lexer, `MVK_LEXER_STANDARD_ERROR`.

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [production close](../docs/sources/inbound-handbacks.md#inbound-2026-09-26o-production-close), [comment terminators](../docs/sources/inbound-handbacks.md#inbound-2026-09-25-comment-terminators), [comment placement](../docs/sources/inbound-handbacks.md#inbound-2026-09-27-comment-placement), [number-literal whitespace](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-number-literal-whitespace), [lexer and blank text](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-lexer-and-blank-text), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [condition-language terminals](../docs/sources/message-and-pointer-probes.md#src-german-condition-language-terminals), [form-level constructs](../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-form-condition-constructs), [name and group alphabets](../docs/sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet), [inbound 2026-10-29d](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29d), [model frame members](../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-members).

---

## 2. Literals

**A literal's kind is fixed by its own spelling before any context reads it.** An unquoted digit run is a number literal where the grammar expects a value, and a name where it expects a name — a digit-only `CustomCondition` name ([§14](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)) and a bare numeric token in a `Date` component, which is read as an entity name ([§6 §3](05-dates-and-time.md#3-constructing-dates-and-checking-validity)); a double-quoted literal is a date, an omitted-year date, a clock, a date-time or a String by its content alone; `True` and `False` are keywords. The kinds, their meaning and the quoted shapes are owned by the chapters linked below; this table holds the remaining spelling rules.

| Literal | Written | Spelling rule |
|---|---|---|
| number | `123`, `-1.5`, `0.000` | ASCII digits, the decimal separator always `.`, at most one leading `-`, and whether a leading `+` is admitted is unmeasured. **The total digit count is ungated**: a 16-digit literal is measured admitted, and [§9 §1.9](07-repetition-and-iteration.md#19-converting-the-comparison-constant) measures 19-digit ones. The scale a literal carries and how `==` and `!=` pad it are [§5 §1](04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time)'s: on a scale-0 field `[Quantity] == 1.00` is refused in either operand order, and on a scale-2 field `[UnitPrice] == 1` is admitted. |
| date | `"31.12.2024"` | the date shape of [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-). |
| omitted-year date | `"13.07."` | the omitted-year shape of [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-). Which year completes it, and where a missing Base Year refuses it, are [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-)'s and [§11 §4.1](09-computations.md#41-temporal-constants)'s. |
| clock | `"12:30:00"` | the clock shape of [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-). |
| date-time | `"05.03.2024T12:30:00"` | the date-time shape of [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-). Which targets accept it, and its zone-dependent static check, are [§11 §4.1](09-computations.md#41-temporal-constants)'s. |
| String | `"abc"` | any other double-quoted content ([§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-)). `""` is not an empty-string value ([§2 A.1](03-empty-and-required.md#a1-the-per-kind-default)). |
| Boolean | `True`, `False` | keywords, compared to Boolean and Confirm fields per [§1](02-logic-and-formal-errors.md#a3-boolean-is-a-three-state-field-type-distinct-from-three-valued-logic). |
| value list | `"A", "B"` or `1, 2, 3` | unparenthesised literals and members; which operator takes which list, and after which separator, is the slot signature of concrete syntax §3.2. |

**A value list is never parenthesised.** A parenthesised argument is refused (concrete syntax §3.3), and a parenthesised list after `In` is no exception: `AtLeastOneFieldValueIncludedInValueList(Note, Memo In ("A", "B"))` draws `MVK_UNEXPECTED_TOKEN` where the unparenthesised list is admitted.

Sources: [Number literal leaf grid](../docs/sources/having-filter-probes.md#src-having-number-leaf-grid), [Date constant target formatting](../docs/sources/temporal-constant-and-base-year-probes.md#src-date-constant-target-formatting), [yearless anchor](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year), [literal composition](../docs/sources/temporal-constant-and-base-year-probes.md#src-temporal-constant-literal-composition), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

---

## 3. The condition and operation grammar (sketch)

**A text is one of two tiers: a condition, which yields a truth, or an operation, which yields a value.** A rule's condition, a computation's preconditions and a filter body are conditions; a computation's operation is an operation; a comparison embeds operations, and some calls take entities as arguments. Parentheses group conditions and braces group operations (concrete syntax §3.3).

**The structural laws:**

- **One connective per bracket pair.** All connectives joining the parts of one bracket pair must be the same; mixing `And` and `Or` there is refused `MVK_BRACKET_MISSING`, because the Kernel declines to supply a precedence ([§1 A.1](02-logic-and-formal-errors.md#a1-connectives-and-mandatory-parentheses)). `A And B And C` is admitted and `A And B Or C` refused. A bracket pair joins any number of parts: four joined by `And` and four joined by `Or` are both admitted. The scope is the pair, not the depth: two sibling parenthesised parts one level deep, one carrying `And` and the other `Or`, joined at the outer level by a single connective, are admitted, while mixing that outer level still refuses. A call's own parentheses and a `Having` filter's body each open a pair of their own, so `And` inside a filter with `Or` outside it is admitted.
- **Division and power are limited by checks, not by the grammar.** A second unbraced division within one arithmetic region draws `MVK_TOO_MANY_DIV_FOR_CALC`, so `[a] / [b] + [c] / [d]` is admitted and `{ [G] / [F] } / 2` is the braced form; [§5 §4.2](04-numbers-and-decimals.md#42-division-and-power-shape) owns the region and its walk through value functions. A power written as the direct left operand of another power, `a ^ b ^ c` (powers associate to the left), draws `MVK_TOO_MANY_POW_FOR_CALC`, while `{a ^ b} ^ c`, `a ^ {b ^ c}` and powers joined by multiplication pass this check. The exponent's scale is a third check, so a grouped power exponent passes only where its own operands allow it: `[N] ^ {2 ^ 2}` is admitted, while `[A] ^ {[B] ^ [C]}` over scale-0 Number fields draws it. That check is `MVK_INVALID_NUMBER_FOR_EXP`: `[Base] ^ [Exponent]` over two Number fields parses and is then refused where `[Base] ^ 2` is admitted; the restriction is on the exponent's derived scale, not on its being a field ([§5 §1.3](04-numbers-and-decimals.md#13-power-scale-and-the-exponent-gate)).
- **Path legality is the path chapters'.** Which segments may carry a `*`, that a `..` step may not ([§10 §1](08-paths-and-references.md#1-absolute-relative-and-short-name-references)), that every repeatable level below a starred one must be starred too ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)), and where a star binds ([§9 §4](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-)) are owned there; this chapter owns only the order in which a path's checks are raised (concrete syntax §3.1).

**The grammar.** Choice points, where the parser chooses among productions by look-ahead, are marked `(* choice *)`; concrete syntax §3.1 says where a failed choice is reported. Where the sketch and a rule of this chapter differ, the rule decides.

```ebnf
(* ---- entry ---- *)
conditionText    = [ preamble ] , condition , EOF ;
operationText    = operand , EOF ;                                   (* a computation's operation; concrete syntax §4 says how its suppressed codes reach the text *)
preamble         = "@SuppressWarning" , "(" , name , ")" ;           (* exactly one name; only MVK_INVALID_COMPARE_DEC_PLACES is admitted, concrete syntax §4 *)

(* ---- conditions ---- *)
condition        = branch , { logOp , branch } ;                    (* one logOp per bracket pair (MVK_BRACKET_MISSING); branch count unbounded *)
logOp            = "And" | "Or" ;
branch           = [ comment ] , ( parenCondition | simpleCondition ) , [ comment ] ;   (* choice *)
parenCondition   = "(" , condition , ")" ;
simpleCondition  = comparison                                       (* choice *)
                 | conditionCall
                 | customCondition ;
comparison       = operand , compareOp , operand ;
compareOp        = "==" | "!=" | "<" | "<=" | ">" | ">="
                 | "PatternMatched" | "PatternViolated"
                 | "DiffersWithToleranceRange1" | "DiffersWithToleranceRange2"
                 | "DiffersWithToleranceRange5" | "DiffersWithToleranceRange10" ;   (* the six keywords are infix, written between operands like the symbols *)
conditionCall    = conditionKeyword , "(" , callArguments , ")" ;     (* conditionKeyword: the condition-call category of concrete syntax §5 *)
customCondition  = "CustomCondition" , name ;                        (* name: concrete syntax §1, quoted when it collides with a keyword *)

(* ---- operations (arithmetic) ---- *)
operand          = term , { ( "+" , [ comment ] | "-" ) , term } ;
term             = power , { ( "*" | "/" ) , power } ;               (* division count: a check, §5 §4 *)
power            = atom , { "^" , atom } ;                            (* left-associative; a chained power and the exponent's scale are checks *)
atom             = [ "-" ] , number                                   (* choice; the only signed operand, concrete syntax §3.3 *)
                 | quotedLiteral                                     (* date, clock, date-time or String by content, concrete syntax §2 *)
                 | fieldValue
                 | braceGroup                                        (* the only grouping of an operation *)
                 | constantKeyword                                   (* True, False, Today, Now, BaseYear: no argument list *)
                 | operationCall ;
braceGroup       = "{" , operand , "}" ;
operationCall    = operationKeyword , "(" , callArguments , ")" ;     (* operationKeyword: concrete syntax §5; only Time also takes "()" *)

(* ---- arguments ---- *)
callArguments    = argumentList , [ "In" , argumentList ] , [ "@From" , reference ] ;   (* which operators take In and @From: their slot signature, concrete syntax §3.2 *)
argumentList     = argument , { "," , argument } ;
argument         = slot , [ "To" , slot ] ;                           (* the range form, as in ValueNotConsistent(Tier To Premium, "gold") *)
slot             = reference | operand ;                             (* choice; which one each slot takes is its slot class, concrete syntax §3.2 *)

(* ---- references and paths ---- *)
fieldValue       = "[" , reference , "]" ;                            (* a field's value; a bare reference stands only in an entity slot *)
reference        = path , [ category ] , [ semanticIndex ] , [ havingFilter ] ;
category         = "->" , name ;                                     (* enumeration category read *)
semanticIndex    = "For" , ( stringLiteral | reference ) ;           (* row selection by literal or field-valued key; a key reference owns a following Having, §10 §4 *)
havingFilter     = "Having" , condition ;                            (* filters a starred operand *)
path             = [ "$" ] , ( absolutePath | relativePath | namePath ) ;   (* choice; "$" correlates, only inside a Having filter *)
absolutePath     = "/" , segment , { "/" , segment } ;
relativePath     = upRun , [ "/" , segment , { "/" , segment } ] ;
upRun            = ".." , { "/" , ".." } , [ name ] ;                 (* a name written directly after the last ".." is its turning point: ..Name/rest *)
namePath         = segment , { "/" , segment } ;                     (* from the rule's group; a single segment may be a short name, §10 §1 *)
segment          = ( name | "'" , name , "'" ) , [ "*" | ".*" ] ;      (* ".*" is the H-model spelling, refused MVK_POINT_IN_A12_MODEL *)
```

The grammar gives `#Zeile` and the German-only form constructs no production; their measured members draw the classes of concrete syntax §1 and §5, and the others are unmeasured.

**Which layer refuses a form.** A form is refused either by the grammar, with a syntax class, or by a check that a completed production runs, with the check's own class; concrete syntax §3.1 orders them. The forms whose layer a parser built from the sketch alone could misplace:

| Form | Layer | Class |
|---|---|---|
| a character outside the lexical alphabet: `%`, a lone `#` or `!`, a non-ASCII digit, a space character other than the five, an unclosed quote | lexer | `MVK_LEXER_STANDARD_ERROR` |
| a token no production can take: a bare name in a value slot, a bracketed read in an entity slot, a sign on a non-literal, a parenthesised argument or operation, a condition call where an operation stands, an up-step outside a relative path's leading run, `#Zeile` in an English model | grammar | `MVK_UNEXPECTED_TOKEN`, `MVK_EXPECTED_TOKEN_NOT_FOUND` or `MVK_INCOMPLETE_INPUT` by concrete syntax §3.1 |
| mixed `And` and `Or` at one bracket pair | check, raised during the parse (concrete syntax §3.1) | `MVK_BRACKET_MISSING` |
| a second unbraced division in one region | check at the arithmetic node's close | `MVK_TOO_MANY_DIV_FOR_CALC` |
| a power as the direct left operand of a power | check at the power node's close | `MVK_TOO_MANY_POW_FOR_CALC` |
| an exponent of fractional or unknown scale | check at the power node's close | `MVK_INVALID_NUMBER_FOR_EXP` |
| a `.*` segment suffix | raised on the walked step (concrete syntax §3.1) | `MVK_POINT_IN_A12_MODEL` |
| a `*` on a `..` step, `..*/Budget` | check | `MVK_INVALID_WILDCARD_REL` ([§10 §1](08-paths-and-references.md#1-absolute-relative-and-short-name-references)) |
| an unresolved name, an operator's operand gate | check at its production's close | the check's class |
| a preamble name other than the supported code | check | `MVK_INVALID_SUPPRESSED_WARNING` |
| a rule whose condition does not reference its error field | check after the whole text | `MVK_ERROR_FIELD_NOT_REFERENCED` |

At one arithmetic node the checks run operand typing (the exponent's scale included) first, then the division walk, then the power rule ([§5 §4.2](04-numbers-and-decimals.md#42-division-and-power-shape)).

> **Non-normative implementation note.** Parse to one untyped tree whose nodes mirror `simpleCondition`, `operand` and the calls, keeping every distinction a later check needs: the parenthesised argument, the braced condition, the bare versus bracketed reference and the comment's position. Refuse in the grammar only what the table above assigns to the grammar, and run each check where concrete syntax §3.1 raises it: a check encoded as a grammar rule reports a syntax class where the Kernel reports the check's, and at a different position. Keep `Having` and `For` as path modifiers and `$` as a correlated path form, since they modify how a path resolves ([§9](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation), [§10](08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-)) rather than being operators in their own right.

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [condition positions](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-condition-positions).

### 3.1 Which class a refused text draws

**A refused text draws one class, the first raised, in the order the text is read.** The condition parser reads left to right and stops at its first failure, so of two defects the earlier one answers, whichever layer — the lexer, the grammar or a check — owns it.

**Three kinds of event interleave, left to right.**

1. A token is lexed only when the parser, or a look-ahead choosing between productions, first needs it.
2. A look-ahead reads as many tokens as its choice needs and runs no check.
3. A production that completes runs its checks, children before parents and left to right, and it completes only once the parser has read the token after it. A completed production's reads bind at the error field, as an admitted rule's do: `Max(AddDays(Items/ShipOn, 1), Items/ShipOn)`, its second slot a bare value, draws `MVK_UNEXPECTED_TOKEN` when the error field is `Items/Count`, and the completed shift's `MVK_NO_WILDCARD` for its unbound `Items` when the error field is a root field.

Measured scope: the syntax failures below are confirmed by a trace of the Kernel's parser, and the checks by the measured rows cited. That a look-ahead runs no check, that checks run children before parents, and the order of two checks no row places against each other rest on source reading, witnessed only where a row below places them.

**A syntax failure's class is what failed, crossed with whether the text had ended.**

| What failed | At the end of the text | At a real token |
|---|---|---|
| a required token is missing | `MVK_EXPECTED_TOKEN_NOT_FOUND` | `MVK_UNEXPECTED_TOKEN` |
| a choice between productions that none survives | `MVK_INCOMPLETE_INPUT` | `MVK_UNEXPECTED_TOKEN` |
| a character the lexer cannot take | `MVK_LEXER_STANDARD_ERROR` | `MVK_LEXER_STANDARD_ERROR` |

So a lone computation operation ending on `+` draws `MVK_INCOMPLETE_INPUT` and one with `{` open `MVK_EXPECTED_TOKEN_NOT_FOUND` ([§11](09-computations.md)). A required token fails at the cursor. A choice fails at its first token when its productions share no opening, and otherwise at the first token none continues, which for a reference can lie several tokens past its start. An optional part that does not see its token just ends (source reading), as `FieldFilled(Lines/Qty). And …` witnesses, failing at the `.` on the match that ends the condition. Measured scope: over a 9,063-condition population each failure's code is the one this table predicts and is among the classes the whole-model check reports; that a refused text draws exactly that code rests on the one-class rule above.

**A lexical defect in the token that completes a production answers first; one a token later does not.** After `FieldFilled(Total) And`, `[Items*/Count] %` and `[Items*/Count]   %` draw `MVK_LEXER_STANDARD_ERROR`, the count being of tokens and not of characters, where `[Items*/Count] > %` and a line comment before `%` draw the read's `MVK_NO_WILDCARDS_ALLOWED`. A parse failure at an earlier real token keeps its own class: `FieldFilled(Title) And Amount == ٥` draws `MVK_UNEXPECTED_TOKEN` at the bare `Amount`, two tokens before the digit the lexer cannot take. An operation completes the same way, so `[Qty] + [Label] +` draws the addition's `MVK_NO_STRING_OR_NUMBER_FOR_ADD`, not `MVK_INCOMPLETE_INPUT`. On those single-line ASCII rows the parser error's source range for a refused read covers its opening `[` alone, not the whole bracketed read.

**A check is raised where the production that owns it ends**, ahead of an unresolved name or a grammar error read past that end.

- Measured on six operator gates: text in a rounding or a date slot, an argument too many, a filtered group in a count, text ordered against a number, and two scales held equal.
- That end is not always the call's: `DifferenceInDays(Reference, NoSuchField) > 0` draws the date slot's `MVK_NO_DATE`, the slot being one argument, while `FieldFilled(Reference, NoSuchField)` draws `MVK_INVALID_ENTITY`, the name standing inside the call that owns the gate.
- A call read to its end keeps its check when the call around it then fails to parse: `Abs(RoundUpValue(Reference, 2) > 1) > 0` draws `MVK_NO_NUMBER`, while a stray token read before a comparison's type gate answers instead.
- A condition call where an operation stands fails at its keyword, before its arguments are read: `Abs(FieldFilled(NoSuch)) > 0`, `[Score] + FieldFilled(Score) > 0` and `[Score] > FieldFilled(Score)` draw the token class, while `RoundUpValue(Reference, 2) + FieldFilled(Score) > 0` keeps the rounding's `MVK_NO_NUMBER` and `Abs(YearFromDate(Reference) + FieldFilled(Score)) > 0` the date slot's `MVK_NO_DATE`. The condition calls are the category of concrete syntax §5; measured on `FieldFilled` in every position above, and on `FieldValueIncludedInValueList` and `GroupFilled` as an operation's operand (`Abs(GroupFilled(/Shipment)) > 0`), the other members unmeasured.

**A reference is checked where its production closes.**

- `FieldFilled(NoSuch Code)` draws `MVK_INVALID_ENTITY`, the name closing before the stray `Code`, while `FieldFilled(NoSuch/)` draws `MVK_UNEXPECTED_TOKEN`, the path still open.
- At one offset, `FieldFilled(Reference) NoSuchField` draws `MVK_UNEXPECTED_TOKEN` and `FieldFilled(NoSuchField` `MVK_INVALID_ENTITY`.
- An arithmetic chain is checked where it closes: `[Code] * 2 == "ABC"` draws `MVK_NO_NUMBER_FOR_CALC` and `[Code] * == "ABC"` the token class alone.
- An aggregate's field list takes no arithmetic: `MinValue(Items*/Count - 1)` draws the token class beside an admitted `MinValue(Items*/Count)`.
- Only the time constructor takes an empty argument list: `Today()` draws the token class and `Time() == Time()` is admitted.
- A category arrow needs its name: `[Code -> ] == "x"` draws the token class.

**A path the parser walks as it reads it checks each step whose production completed, even when the path never closes; a step it stops inside draws no class.** A path is walked when it is `$`-marked, opens with an up-run, or carries a star on a segment read before the stop, a `.*` suffix included, whichever segment is bad.

| Path | Walked | Class |
|---|---|---|
| `FieldFilled(Items*/NoSuch/)`, `FieldFilled(NoSuch/Items*/)`, from a nested group `FieldFilled(../NoSuch/)`, a `Having` body's `[$NoSuch/]`, `FieldFilled(NoSuch.*/Items/)` | yes | `MVK_INVALID_ENTITY` |
| `FieldFilled(/NoRoot/Items*/)` | yes | `MVK_INVALID_ROOT_GROUP` |
| `Items*/Count/`, a walked prefix that resolves | yes | `MVK_UNEXPECTED_TOKEN` |
| `Items*/NoSuch.`, a step the walk stops inside | yes | `MVK_UNEXPECTED_TOKEN` |
| `Items.*/Count` | yes | `MVK_POINT_IN_A12_MODEL`, the `.*` step's own |
| `Items/NoSuch/`, `[NoSuch/]`, `/NoRoot/` | no | `MVK_UNEXPECTED_TOKEN` |

The account that an unwalked path is still inside the look-ahead choosing between a path's two written forms, and that those spellings end it, is source-read, so the table and not that account decides a walk. [§10 §1](08-paths-and-references.md#1-absolute-relative-and-short-name-references) applies the same triggers to an up-step written past a path's leading run.

**Some checks are raised before their production completes.** Each raise event below is measured; every other check is unmeasured for an early raise.

| Check | Raised | Witness |
|---|---|---|
| mixed connective, `MVK_BRACKET_MISSING` | after the part following the mixing connective has run its reference checks, and before any later part's | after `FieldFilled(Reference) And FieldFilled(Score) Or`, a bad name in the next part draws `MVK_INVALID_ENTITY` and one in a later part `MVK_BRACKET_MISSING` |
| a filtered operand's kind | as `Having` is read | a group is refused ahead of a defect in its body ([§9 §3.1](07-repetition-and-iteration.md#31-the-filter-condition-and-its-static-gates)) |
| the rest of a filter's chain | once the whole filter specification is read | a body's defect answers ahead of the operand's missing star ([§9 §3.1](07-repetition-and-iteration.md#31-the-filter-condition-and-its-static-gates)) |
| a German model's H-model form construct, `MVK_INVALID_ROOT_GROUP_CONSTR` | on its keyword, before its argument list, wherever a condition opens | `VordruckAngegeben(` draws the construct class alone, as does `VordruckAngegeben(NoSuchForm)`; it answers ahead of a later unresolved name and grammar error and yields to an earlier name |

After a completed condition or as a field operand, a form-level construct is `MVK_UNEXPECTED_TOKEN` (measured on `VordruckAngegeben`). The class each German-only construct draws where a condition opens is listed in concrete syntax §5.

**A post-parse class yields to the parse-time classes measured beside it:** `MVK_ERROR_FIELD_NOT_REFERENCED` yields to an unresolved name on either side and to every one of the six operator gates above but the filtered count, which is not measured there.

Sources: [class order](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-condition-class-order), [parse events](../docs/sources/inbound-handbacks.md#inbound-2026-09-28-parse-events), [token demand](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-token-demand), [gate raise points](../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-gate-raise-points), [production close](../docs/sources/inbound-handbacks.md#inbound-2026-09-26o-production-close), [walked path](../docs/sources/inbound-handbacks.md#inbound-2026-09-26p-walked-path), [completed steps](../docs/sources/inbound-handbacks.md#inbound-2026-09-27-completed-steps), [filter body](../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-filter-body), [form keyword](../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-form-keyword), [form-level constructs](../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-form-condition-constructs), [handback rows 2026-10-23](../docs/sources/model-structure-and-declaration-probes.md#src-handback-rows-2026-10-23) (`production-binding`), [K22 static batch 6](../docs/sources/group-count-topology.md#src-k22-static-s6) (`z10`), [predicate operand classes](../docs/sources/model-structure-and-declaration-probes.md#src-predicate-operand-classes), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### 3.2 Argument slots

**Each argument slot of an operator is typed, and its type decides how a field is written there.** A field's value is read only through a bracket: `atom` has no bare path, and a bare reference stands only in a slot typed as an entity. Every slot belongs to one of the classes below; [the operator reference's S column](14-operator-reference.md#argument-slots) assigns each operator's slots.

| Class | What the slot takes | How a field is written | Refused there |
|---|---|---|---|
| `entity` | a reference, with the modifiers its operator admits (category, semantic index, `Having`), and whatever non-field operands its operator's chapter admits | bare: `Length(/Order/Note)` | a bracketed read, `MVK_UNEXPECTED_TOKEN` |
| `range entity` | an `entity` slot of a date-range operator | bare | a bracketed read, and a String literal at its start, `MVK_UNEXPECTED_TOKEN` |
| `value` | an operation: a literal, a bracketed read, a constant keyword, an operation call, a brace group, arithmetic | bracketed: `Abs([Items/Count])` | a bare name, `$`-marked or not, `MVK_UNEXPECTED_TOKEN` |
| `member` | a String literal, a number literal with an optional sign, or a bracketed read | bracketed | a bare name or a constant keyword such as `True`, `MVK_UNEXPECTED_TOKEN` |
| `digits` | an unsigned number literal | — | a bare name or a bracketed read, `MVK_UNEXPECTED_TOKEN` |
| `literal` | a Number or String literal, `True` or `False` | — | not stated |
| `type name` | a String literal naming a custom type | — | not stated |
| `pattern` | a String literal holding the pattern | — | not stated |
| `endpoint` | the keyword `FirstDay` or `LastDay` | — | not stated |
| `name` | a name or a quoted name (concrete syntax §1) | — | not stated |
| `none` | no argument list | — | an argument list, `()` included: `Today()` draws `MVK_UNEXPECTED_TOKEN` (measured on `Today`) |

A comparison side and an arithmetic term are `value` positions too, as are a brace group's content, a parenthesised condition's side and a filter body's side.

**The `value` refusal.** A bare name in a `value` position draws `MVK_UNEXPECTED_TOKEN` at the name: nothing after it is read and the name is never resolved, so `NoSuchField > 0` draws the token class where a parser taking a bare name as a reference would draw `MVK_INVALID_ENTITY`. A name that is no keyword, written before `(` in a `value` position, draws the token class the same way. Measured members: a comparison side, an arithmetic term, a brace group's content, a parenthesised condition's side, a filter body's side, a computation's operation, `AddDays`' amount (`AddDays(Due, Anchor)`), and the value operands of `Abs`, `RoundUp`, `RoundDown` and `RoundAccounting` (the first argument) and of `Min` and `Max` (every argument), bare outside a filter body and bare or `$`-marked inside one, and inside a nested operand such as `Max([Items/Count], Abs(Items/Count))`. The other shifts' amounts share `AddDays`' production, unmeasured. `Max([Items/Count], [Items/Count])` and `Abs([Items/Count])` are admitted, and so are `RoundUpValue(Total, 0) > 0`, `[Total] == Sum(Lines*/Qty)` and a computation's `[Fees/Handling]`.

**The `entity` refusal.** A bracketed read in an `entity` slot is a token defect: `Length([/Order/Qty])` and `Length([/Order/Note])` draw `MVK_UNEXPECTED_TOKEN` while `Length(/Order/Note)` is admitted. Measured members: `Length` (absolute and relative, `Length([Note])`), both slots of `DifferenceInDays` (`DifferenceInDays([/G/F], …)`), and the DateTime projections `DateFromDateTime` and `TimeFromDateTime` ([§6 §3](05-dates-and-time.md#3-constructing-dates-and-checking-validity)). The other `entity` slots, the other differences included, are unmeasured.

**In an `entity` slot, and inside a bracket, a name is read as a path and resolved before a following `(` is refused**, so an undeclared name draws `MVK_INVALID_ENTITY` and a declared one the token class. `FieldFilled(Foo(Stamp))`, `DifferenceInDays(Foo(Stamp), Due)` in either slot, `YearFromDate(Foo(Stamp))`, `Sum(Foo(Stamp))`, `Length(Foo(Stamp))`, `FirstFilledValue(Foo(Stamp), Title)`, a bracketed `[Foo(Stamp)]` and a computation's `DifferenceInDays(Foo(Stamp), Due)` draw the entity class, while `DifferenceInDays(Due(Stamp), Day)` and `Abs(Foo(Stamp))`, a `value` operand, draw the token class.

**In an `entity` slot a `*` directly after a bare name is that name's repetition star, not a product:** `FieldFilled(Premium * 2)` draws `MVK_INVALID_WILDCARD` for the starred single field ahead of the stray `2`, and `FieldFilled(NoSuch * 2)` `MVK_INVALID_ENTITY`, while every other operator after a bare reference draws the token class.

**The `member`, `range entity` and `digits` refusals.** A value list's member is a String literal, a number literal or a bracketed read, and a bare name or `True` there draws `MVK_UNEXPECTED_TOKEN` ([§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-)). A String literal, a range literal `"2020-01-01/2020-02-01"` included, draws `MVK_UNEXPECTED_TOKEN` in a `DateRange` endpoint, a `StartOfDateRange` or `EndOfDateRange` operand, any `DateRangesOverlap` operand, the subject of `AtLeastOneDateRangeOverlaps` and an `In` list of it that opens with a field; an `In` list that opens with a String literal parses as a literal list instead ([§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap)). A bare name in a rounding operator's place count draws `MVK_UNEXPECTED_TOKEN`, and so does a bracketed read there, measured on `RoundUp`; a bracketed read in the other rounding operators' place counts is unmeasured.

**Separators.** `In` separates an operator's leading arguments from its trailing list, `To` joins the two ends of a range argument, and `@From` names a uniqueness scope; which operators take each is their S cell. The singular value-list forms `FieldValueIncludedInValueList` and `FieldValueNotIncludedInValueList` write their members after the subject's comma, not after `In`: `FieldValueIncludedInValueList(Note In "A", "B")` draws `MVK_UNEXPECTED_TOKEN` where `FieldValueIncludedInValueList(Note, "A", "B")` is admitted, and the `In` form of `FieldValueNotIncludedInValueList` is unmeasured; the quantifier forms take their list after `In` ([§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-), [§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-)).

Sources: [bare entity](../docs/sources/inbound-handbacks.md#inbound-2026-09-25f-bare-entity), [production close](../docs/sources/inbound-handbacks.md#inbound-2026-09-26o-production-close), [K22 static batch 5](../docs/sources/group-count-topology.md#src-k22-static-s5) (`slots`), [parser static-legality sweep](../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-parser-static-legality-sweep) (row `R40`), [handback rows 2026-10-23](../docs/sources/model-structure-and-declaration-probes.md#src-handback-rows-2026-10-23) (`value-slots`, `value-slot-twins`, `peer-rows` rows `os004`, `os006`, `os007`), [condition class projection](../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection) (rows `O08`, `O09`, `O09b`), [yearless anchor](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year), [K22 static classes](../docs/sources/group-count-topology.md#src-k22-static-classes), [K22 static batch 2](../docs/sources/group-count-topology.md#src-k22-static-s2), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### 3.3 Grouping, signs and literal spacing

**Parentheses group conditions only, and braces group operations.**

- Refused `MVK_UNEXPECTED_TOKEN`: a parenthesised comparison side, a parenthesised operation leading a comparison, a parenthesised argument such as `Sum((Claims*/Amount))` or `Max(([Score] > 1), 2)`, and a computation's parenthesised operation.
- Admitted: `[Score] > {[Score] + 1}`, a computation's `{[Score] + 1}`, and a parenthesised condition.
- Also refused: a comparison in braces; a connective, a comparison or a predicate call as a field operand; a comparison or a predicate call as an operation argument; a predicate call as a comparison side; and a predicate call or a comparison as a computation's whole operation.
- A filter body is a condition, so a comparison, the same in parentheses and a predicate call are admitted there and an operand alone is refused, as is a comparison in a semantic index's key or a `@From` scope.

**A sign is admitted on a number literal and refused on every other operand measured.** In a rule `[BaseFee] > -1` and `[BaseFee] - -1 > 1` are admitted, and a sign on a reference, a braced operation or a call, or a second sign, is `MVK_UNEXPECTED_TOKEN`. In a computation `-5` and `[BaseFee] * -1` are admitted, and a sign on a reference is refused alone, as a factor, in braces and as a rounding argument. A negated operation is written as a subtraction, `0 - [BaseFee]`.

**Whitespace may stand inside a number literal, and a comment may not.** Against a one-fraction-digit Number, each of the five whitespace characters between the sign and the digits of `-2.5`, or on either side of its point in `-2.5` and `2.5`, is admitted and evaluates as the contiguous literal on both runtime strategies, while a line comment at any of those three positions of `-2.5` is refused.

Sources: [condition positions](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-condition-positions), [number-literal whitespace](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-number-literal-whitespace).

---

## 4. Directives and the special entities

| Form | Written | Meaning |
|---|---|---|
| suppress-warning preamble | `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)` | waive the equality scale gate — the **only** suppressible warning ([§5 §1](04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time)) |
| reference-group scope | `RepetitionNotUnique(a, b @From Group)` | choose the uniqueness scope ([§9 §6](07-repetition-and-iteration.md#6-repetitionnotunique-precisely-)) |
| the rule's own group | `RuleGroup` | the rule's containing group as an entity; counts as referencing the error field; a `*` on it is rejected ([§10 §1](08-paths-and-references.md#1-absolute-relative-and-short-name-references)) |
| semantic index | `[Field For "value"]` or `[Field For CustomerName]` | select a row by a literal index value or by the value read from the named field ([§10 §4](08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-)) |
| correlation | `$path` (inside `Having`) | pin to the current outer repetition ([§9 §3.2](07-repetition-and-iteration.md#32-correlation--and-currentrepetition)) |
| list separator | `… In …` | separates an operator's leading arguments from its trailing list (concrete syntax §3.2) |

**A rule carries the preamble as written text; a computation's `errorCodesToSuppress` reaches the same preamble as text.** The computation's entries are joined with `,` into `@SuppressWarning(…)` ahead of the condition and parsed by the condition lexer and parser in the model's condition language, so the first failure in that text answers, whether it is a character the lexer cannot take or a token the parser cannot use. An absent or empty list is admitted.

| Entry text | Class | Measured members |
|---|---|---|
| the supported name, alone | admitted | padded with spaces, or with a tab and a line break, too |
| one entry that lexes as a single name other than the supported code | `MVK_INVALID_SUPPRESSED_WARNING` | `Late_Fee`, `_LATE_FEE`, `MVK:LATE`, `MVK_GEBÜHR`, `MVK_CODE7`, the supported name in lower case, a keyword of the *other* condition language |
| text that lexes but is not one usable name | `MVK_UNEXPECTED_TOKEN` | `7_DAYS`, `MVK_LATE FEE`, `MVK_LATE.FEE`, either quoted form, a trailing `;;` comment, `#Zeile`, a blank entry, a keyword of the model's own language (`And`, `Sum` in an English model, `Summe` in a German one) |
| two or more entries | `MVK_UNEXPECTED_TOKEN` | the supported name twice or three times; a list led by an unsupported name, whose parse failure answers ahead of the name gate |
| a character the lexer cannot take | `MVK_LEXER_STANDARD_ERROR`, unless a parser failure comes earlier in the text | `MVK_FRAÉ`, an unclosed quote, `#LATE`, a no-break space before the name; `7_DAYS É` and `And É` are `MVK_UNEXPECTED_TOKEN`, and `MVK_FRAÉ` followed by the supported name is the lexer error while the reverse order is `MVK_UNEXPECTED_TOKEN` |

Under the alphabet of concrete syntax §1 `7_DAYS` spells one name, yet this position refuses it as a token rather than as an unsupported name; which other spellings take that route is unmeasured.

**Being the text's first part, the preamble's class answers ahead of the classes measured beside it:** an unsupported name draws `MVK_INVALID_SUPPRESSED_WARNING` beside an operation or precondition naming nothing, a text in a rounding slot, a read of the computed field and a control character in the message, each of which draws its own class without the member, and the supported name twice draws `MVK_UNEXPECTED_TOKEN` beside the unresolved operation, the rounding slot and the control character.

Sources: [list reads](../docs/sources/inbound-handbacks.md#inbound-2026-09-26h-list-reads), [lexer and blank text](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-lexer-and-blank-text), [computation texts](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-computation-texts).

---

## 5. Keyword catalog (English ↔ German, verified pairs)

**The table is the complete set of keyword pairs, with each keyword's grammatical category.** A spelling in neither column is an ordinary name. With the language-neutral `In` family (`In`, `in`, `IN`) and the case variants of concrete syntax §1 (two more spellings each for `And`, `Or` and `To` in either language) it accounts for the 112 English spellings, and with the 13 German-only constructs below for the 125 German ones. Symbols are language-neutral. German uses the domain nouns *Feld* = field, *Kontext* = repetition/group-context, *Wiederholung* = repetition, *Angegeben* = specified/filled.

| Category | Grammatical role |
|---|---|
| connective | joins condition parts (`logOp`) |
| comparator | infix between two operands (`compareOp`) |
| condition call | a call that is a whole condition (`conditionCall`); where an operation stands it fails at its keyword (concrete syntax §3.1) |
| custom condition | `CustomCondition` followed by a name (`customCondition`) |
| operation call | a call yielding a value (`operationCall`) |
| constant | a value keyword written without an argument list |
| argument keyword | a keyword standing as one operator's argument |
| modifier | attaches to a reference or a call: filter, semantic index, uniqueness scope |
| separator | separates or joins arguments |
| entity | names an entity |
| directive | the preamble |

| English | German | Category |
|---|---|---|
| `FieldFilled` | `FeldAngegeben` | condition call |
| `FieldNotFilled` | `FeldNichtAngegeben` | condition call |
| `And` | `Und` | connective |
| `Or` | `Oder` | connective |
| `DiffersWithToleranceRange1` | `UngleichMitToleranz1` | comparator |
| `DiffersWithToleranceRange2` | `UngleichMitToleranz2` | comparator |
| `DiffersWithToleranceRange5` | `UngleichMitToleranz5` | comparator |
| `DiffersWithToleranceRange10` | `UngleichMitToleranz10` | comparator |
| `AllFieldsFilled` | `AlleFelderAngegeben` | condition call |
| `NoFieldFilled` | `KeinFeldAngegeben` | condition call |
| `AtLeastOneFieldFilled` | `MindestensEinFeldAngegeben` | condition call |
| `NotAllFieldsFilled` | `NichtAlleFelderOderKeinFeldAngegeben` | condition call |
| `FieldsNotCollectivelyFilled` | `FelderNichtGemeinsamAngegeben` | condition call |
| `NotExactlyOneFieldFilled` | `NichtGenauEinFeldAngegeben` | condition call |
| `MoreThanOneFieldFilled` | `MehrAlsEinFeldAngegeben` | condition call |
| `GroupFilled` | `KontextAngegeben` | condition call |
| `GroupNotFilled` | `KontextNichtAngegeben` | condition call |
| `AllGroupsFilled` | `AlleKontexteAngegeben` | condition call |
| `NoGroupFilled` | `KeinKontextAngegeben` | condition call |
| `AtLeastOneGroupFilled` | `MindestensEinKontextAngegeben` | condition call |
| `NotAllGroupsFilled` | `NichtAlleOderKeinKontextAngegeben` | condition call |
| `GroupsNotCollectivelyFilled` | `KontexteNichtGemeinsamAngegeben` | condition call |
| `True` | `Wahr` | constant |
| `False` | `Falsch` | constant |
| `Length` | `Laenge` | operation call |
| `PatternMatched` | `WieMuster` | comparator |
| `PatternViolated` | `NichtWieMuster` | comparator |
| `FieldValueIncludedInValueList` | `FeldWertInWerteListe` | condition call |
| `FieldValueNotIncludedInValueList` | `FeldWertNichtInWerteListe` | condition call |
| `AtLeastOneFieldValueIncludedInValueList` | `MindestensEinFeldWertInWerteListe` | condition call |
| `NoFieldValueIncludedInValueList` | `KeinFeldWertInWerteListe` | condition call |
| `NotAllFieldValuesIncludedInValueList` | `NichtAlleFeldWerteInWerteListe` | condition call |
| `NumberOfFilledFields` | `AnzahlAngegebenerFelder` | operation call |
| `NumberOfFilledGroups` | `AnzahlAngegebenerKontexte` | operation call |
| `RepetitionNotUnique` | `WiederholungNichtEindeutig` | condition call |
| `@From` | `@Von` | modifier |
| `FieldValuesNotUnique` | `FeldWerteNichtEindeutig` | condition call |
| `Sum` | `Summe` | operation call |
| `MaxValue` | `MaxWert` | operation call |
| `MinValue` | `MinWert` | operation call |
| `RoundDown` | `Abrunden` | operation call |
| `RoundDownValue` | `AbrundenWert` | operation call |
| `RoundUpValue` | `AufrundenWert` | operation call |
| `RoundAccountingValue` | `RundenWert` | operation call |
| `AbsValue` | `AbsWert` | operation call |
| `Abs` | `Abs` | operation call |
| `Min` | `Min` | operation call |
| `Max` | `Max` | operation call |
| `RoundUp` | `Aufrunden` | operation call |
| `RoundAccounting` | `Runden` | operation call |
| `NumberOfDifferentValues` | `AnzahlVerschiedenerWerte` | operation call |
| `NumberOfValueInFields` | `AnzahlWertInFeldliste` | operation call |
| `Having` | `Mit` | modifier |
| `CurrentRepetition` | `AktuelleWiederholung` | operation call |
| `CustomCondition` | `ApplikationsBedingung` | custom condition |
| `For` | `Fuer` | modifier |
| `Today` | `Heute` | constant |
| `DifferenceInDays` | `DifferenzInTagen` | operation call |
| `DifferenceInMonths` | `DifferenzInMonaten` | operation call |
| `DifferenceInYears` | `DifferenzInJahren` | operation call |
| `DifferenceInHours` | `DifferenzInStunden` | operation call |
| `DifferenceInMinutes` | `DifferenzInMinuten` | operation call |
| `DifferenceInSeconds` | `DifferenzInSekunden` | operation call |
| `AddDays` | `AddiereTage` | operation call |
| `AddMonths` | `AddiereMonate` | operation call |
| `AddYears` | `AddiereJahre` | operation call |
| `AddHours` | `AddiereStunden` | operation call |
| `AddMinutes` | `AddiereMinuten` | operation call |
| `AddSeconds` | `AddiereSekunden` | operation call |
| `YearFromDate` | `JahrAusDatum` | operation call |
| `MonthFromDate` | `MonatAusDatum` | operation call |
| `DayFromDate` | `TagAusDatum` | operation call |
| `QuarterFromDate` | `QuartalAusDatum` | operation call |
| `StartOfDateRange` | `StartAusDatumBereich` | operation call |
| `EndOfDateRange` | `EndeAusDatumBereich` | operation call |
| `DateRangesOverlap` | `DatumsBereicheUeberlappend` | condition call |
| `AtLeastOneDateRangeOverlaps` | `MindestensEinDatumsBereichUeberlappend` | condition call |
| `HoursFromTime` | `StundenAusZeit` | operation call |
| `MinutesFromTime` | `MinutenAusZeit` | operation call |
| `SecondsFromTime` | `SekundenAusZeit` | operation call |
| `DateFromDateTime` | `DatumAusDateTime` | operation call |
| `TimeFromDateTime` | `ZeitAusDateTime` | operation call |
| `RangeAsString` | `BereichAlsString` | operation call |
| `FieldValueAsString` | `FeldWertAlsString` | operation call |
| `RangeAsNumber` | `BereichAlsZahl` | operation call |
| `FieldValueAsNumber` | `FeldWertAlsZahl` | operation call |
| `ValueAsDate` | `WertAlsDatum` | operation call |
| `FirstDay` | `ErsterTag` | argument keyword |
| `LastDay` | `LetzterTag` | argument keyword |
| `Date` | `Datum` | operation call |
| `Time` | `Zeit` | operation call |
| `DateTime` | `DateTime` | operation call |
| `Now` | `Jetzt` | constant |
| `BaseYear` | `Referenzjahr` | constant |
| `Valid` | `Gueltig` | condition call |
| `Invalid` | `Ungueltig` | condition call |
| `SumOfProducts` | `SummeVonProdukten` | operation call |
| `FirstFilledValue` | `ErsterAngegebenerWert` | operation call |
| `DateRange` | `DatumBereich` | operation call |
| `RuleGroup` | `RegelKontext` | entity |
| `@SuppressWarning` | `@UnterdrueckeWarnung` | directive |
| `ValueNotConsistent` | `WertNichtKonsistent` | condition call |
| `To` | `Zu` | separator |

The language-neutral `In` family is a separator. The category counts are closed: 2 connectives, 6 comparators, 28 condition calls, 1 custom condition, 53 operation calls, 5 constants, 2 argument keywords, 3 modifiers, 1 separator besides `In`, 1 entity and 1 directive.

**The German-only constructs are the H-model form constructs.** They have no English twin and no row in the operator reference. In an English model each lexes as a name; written as a whole condition, the constructs of the table's first six rows and its three `Zeile…` rows are measured to draw `MVK_UNEXPECTED_TOKEN` there, and the other four are unmeasured. In a German model each is a keyword, and every measured one is refused by a class that depends on the construct and its position (concrete syntax §3.1):

| German-only construct | Class in a German model, where a condition opens |
|---|---|
| `VordruckAngegeben` | `MVK_INVALID_ROOT_GROUP_CONSTR` |
| `VordruckNichtAngegeben` | `MVK_INVALID_ROOT_GROUP_CONSTR` |
| `KeinVordruckAngegeben` | `MVK_INVALID_ROOT_GROUP_CONSTR` |
| `MindestensEinVordruckAngegeben` | `MVK_INVALID_ROOT_GROUP_CONSTR` |
| `VordruckNichtFortlaufend` | `MVK_INVALID_ROOT_GROUP_CONSTR` |
| `UsbNichtFortlaufend` | `MVK_INVALID_ROOT_GROUP_CONSTR` |
| `AnzahlAngegebenerVordrucke` | `MVK_INVALID_ROOT_GROUP_CONSTR`, measured as `AnzahlAngegebenerVordrucke(Order) > 0` |
| `AktuelleVordruckNummer` | `MVK_UNEXPECTED_TOKEN`, measured as `AktuelleVordruckNummer(Code) > 0` |
| `MaximalAngegebenerZeilenindex` | `MVK_UNEXPECTED_TOKEN`, measured as `MaximalAngegebenerZeilenindex(Code) > 0` |
| `ZeileNichtEindeutig` | `MVK_UNEXPECTED_TOKEN`, in an English model too |
| `ZeilenLueckenlos` | `MVK_UNEXPECTED_TOKEN`, in an English model too |
| `ZeilenNichtAufsteigend` | `MVK_UNEXPECTED_TOKEN`, in an English model too |
| `AnzahlAngegebeneUsb` | unmeasured |

The six constructs drawing `MVK_INVALID_ROOT_GROUP_CONSTR` as whole conditions draw it with a starred and an unstarred root operand alike, the construct's class answering ahead of the classes that read its argument. In other positions concrete syntax §3.1 decides.

> **Non-normative implementation note.** Model keywords as a table of explicitly accepted spellings mapped to `(keyword, language)`, plus one canonical render spelling per `(keyword, language)` and the category above. Do not normalize case before lookup. Keep it *data*, not code — a future port to another surface re-reads the same table. English is the canonical render target; German is a supported second target.

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [form-level constructs](../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-form-condition-constructs), [form keyword](../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-form-keyword), [class order](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-condition-class-order).

---

## Checklist for the concrete syntax

- [ ] Two keyword languages, one selected per model with no fallback; only the enumerated English `And`/`Or`/`In`/`To` and German `Und`/`Oder`/`In`/`Zu` case families are accepted; writing is canonical; symbols are language-neutral; names use the alphabet of concrete syntax §1 and are quoted where they collide with a keyword; `;;` comments stand only where concrete syntax §1 measures them.
- [ ] Literal kind fixed by spelling: number (ASCII digits, no total-digit bound), the quoted temporal shapes of concrete syntax §2 and [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-), String otherwise; `""` ≠ empty value; value lists unparenthesised.
- [ ] The grammar refuses only the grammar layer's forms; mixed `And`/`Or` per bracket pair (`MVK_BRACKET_MISSING`, part count unbounded, a call's or filter's parentheses a pair of their own), the division count (`MVK_TOO_MANY_DIV_FOR_CALC`, region and walk per [§5 §4](04-numbers-and-decimals.md#4-other-numeric-constraints)), the chained power (`MVK_TOO_MANY_POW_FOR_CALC`) and the exponent's scale (`MVK_INVALID_NUMBER_FOR_EXP`) are checks raised at their node's close.
- [ ] A refused text draws the first class raised under the event model of concrete syntax §3.1.
- [ ] Each argument slot is typed per the operator reference's S column: a field bare in an `entity` slot, bracketed in a `value` position.
- [ ] Paths: absolute `/`, relative up-run with an optional turning point, per-segment `*`, short name, quoted names; specifiers `Having` / `For` with a string or field-reference key / `$` attach to references; their legality is [§10](08-paths-and-references.md)'s and [§9 §4](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-)'s.
- [ ] Directives: `@SuppressWarning(only-that-code)` with the entry classes of concrete syntax §4, `@From`, `RuleGroup`, `In`.
- [ ] Bidirectional keyword table with categories (EN canonical, DE supported); the German-only constructs refused by the classes of concrete syntax §5.
