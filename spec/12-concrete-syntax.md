# 12 — Concrete syntax: lexing, keywords, directives, grammar sketch

The other half of "syntax and semantics". Everything above describes how a condition *evaluates*; this file describes how a condition is *written* — enough to build a lexer/parser or hand the grammar to a parser generator. It is a **sketch of the surface**, not a transcription of the engine's grammar file; production *names* are borrowed for orientation, the EBNF below is an original re-expression.

The AST the parser targets is the closed set of constructs described across §1–§14; [`../docs/LEAN-ENCODING-GUIDE.md`](../docs/LEAN-ENCODING-GUIDE.md) proposes an `inductive` shape.

---

## 1. Lexical structure

- **Two keyword languages, and the two vocabularies are nested rather than parallel.** A model's `conditionLanguage` selects **one** terminal map — the supported codes are exactly `en_US` and `de_DE`, and a model declaring any other is refused before lexing begins — and there is no fallback to the other map: a spelling the selected language does not carry lexes as an ordinary entity name rather than as a keyword. So `And` is an operator in an English model and a plain field name in a German one, and `Und` is the reverse. At kernel 30.8.1 the bundles hold **112 English spellings against 125 German**: every English terminal has a German twin, and the 13 extra German ones are the H-model form constructs, which therefore have no English spelling and are reserved words only in a German model. A consumer holding the *union* of both vocabularies reads such a field as an operator and drops the reference silently, because nothing failed ([inbound](../docs/SOURCES.md#inbound-2026-09-21-corrections)). The comparison and arithmetic *symbols* (`== != < <= > >= + - * / ^ -> $`) are **intrinsic** — identical in both languages.
- **Keyword case variants are fixed per language-specific token family, and writing is canonical.** The lexer enumerates accepted spellings rather than case-folding. English admits `And`/`and`/`AND`, `Or`/`or`/`OR`, `In`/`in`/`IN`, and range-form `to`/`To`/`TO`; German admits `Und`/`und`/`UND`, `Oder`/`oder`/`ODER`, the same `In` family, and range-form `zu`/`Zu`/`ZU`. Every other language-specific keyword spelling has exactly one accepted casing: `fieldfilled`, `FIELDFILLED`, and arbitrary mixed case such as `aNd` are rejected. A case-folding lexer therefore over-accepts. Field/group *names* remain case-sensitive identifiers.
- **Comments** run from `;;` to the next CR or LF, so a lone carriage return ends one as a line feed does and the text after it is live. Every other character inside a comment is admitted, a no-break space, a vertical tab and a non-ASCII letter included ([inbound](../docs/SOURCES.md#inbound-2026-09-25-comment-terminators)). A comment may sit before/after a condition branch and (in the engine's round-trip) the leading comment is preserved on write-back. Treat `;;…\n` as a skippable trivia token that a faithful round-tripping parser may choose to attach to the adjacent branch.
- **Whitespace is exactly five characters** — space, CR, TAB, FF and LF — which separate tokens and are otherwise insignificant. Any other space character where whitespace would separate tokens is refused `MVK_LEXER_STANDARD_ERROR`: a no-break space, a vertical tab, an em space, an ideographic space and U+0085 each are, so a lexer built on a platform's whitespace class over-accepts. Inside a string literal every character but a quote is admitted ([inbound](../docs/SOURCES.md#inbound-2026-09-24b-lexer-and-blank-text)).
- **`#Zeile`, the H-model row iteration, is one language-independent token.** An English model lexes it and refuses it a phase later, `MVK_UNEXPECTED_TOKEN`, while `#Zeil`, a lone `#` and a lone `!` are refused by the lexer, `MVK_LEXER_STANDARD_ERROR` ([inbound](../docs/SOURCES.md#inbound-2026-09-24b-lexer-and-blank-text)).
- **Identifiers that collide with a keyword must be single-quoted** in a path: `Order/'Date'` names a field called `Date`.

The complete bilingual spelling table is source-characterized by the kernel's [`LexerTerminals_en`](../../a12-kernel/kernel-tool/kernel-core-parser/src/main/java/com/mgmtp/a12/kernel/core/parser/internal/grammar/languages/LexerTerminals_en.java) and [`LexerTerminals_de`](../../a12-kernel/kernel-tool/kernel-core-parser/src/main/java/com/mgmtp/a12/kernel/core/parser/internal/grammar/languages/LexerTerminals_de.java). a12-dmkits' [`KeywordCaseVariantParseTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/KeywordCaseVariantParseTest.kt) independently locks the stored-English `And`/`Or`/`In` families and arbitrary mixed-case rejection; it does not claim exhaustive German or range-token coverage. Field-referenced semantic-index keys are differentially locked by [`SemanticIndexFieldKeyedDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SemanticIndexFieldKeyedDiffTest.kt).

---

## 2. Literals

| Literal | Form | Notes |
|---|---|---|
| number | `123`, `-1.5`, `0.000` | decimal separator is always `.`; a literal is **not** scale-exempt — it carries the scale it spells, and on `==`/`!=` only a written-out operand may be rescaled, and only *upward*, so `[Quantity] == 1.00` against a scale-0 field is refused in either operand order while `[UnitPrice] == 1` against a scale-2 field is admitted ([§5](04-numbers-and-decimals.md)); ≤ 15 digits |
| date constant | `"31.12.2024"` | `DD.MM.YYYY`, day-first, always `.`; **a string literal matching this shape *is* a date** ([§6](05-dates-and-time.md)) |
| omitted-year date | `"13.07."` | trailing dot, and it is load-bearing — `"13.07"` is not a date; completes against the model **Base Year** only where the target carries a year ([§10](09-computations.md)) |
| date-time constant | `"05.03.2024T12:30:00"` | the date constant, a literal `T`, and the clock constant, concatenated; `"2024-03-05T12:30:00"` and the space-separated form are **not** date-times; after this spelling classifies, static checking of a spring-forward gap can still depend on the JVM default zone ([§10](09-computations.md)) |
| string | `"abc"` | double-quoted; a **date-shaped** content is a date, an **ISO-shaped** `"2024-12-31"` stays a string; `""` is *not* an empty-string value ([§2](03-empty-and-required.md)) |
| boolean / confirm const | `True` / `False` | compared to Boolean/Confirm fields per [§1](02-logic-and-formal-errors.md) |
| value list | `( "A", "B" )` / `( 1, 2, 3 )` | string list or number list, introduced by the `In` separator (see §4) |

> **Non-normative implementation note.** The date/string ambiguity is a **lexer/typer** decision, not an evaluator one: classify a `"…"` token as `dateConst` iff its content matches `DD.MM.YYYY` (or the omitted-year shape), else `strConst`; ISO shapes are always `strConst`. **The match requires a real calendar date and mandatory zero padding, not merely the shape**: `"29.02.2024"` classifies as a date and `"29.02.2023"` does not, `"30.04.2024"` does and `"31.04.2024"` does not, and `"5.3.2024"` does not where `"05.03.2024"` does. A token that fails the match reaches the target as a String and is refused there, so **on the target carrier** the observable code names a comparison rather than the literal — `MVK_INVALID_COMPARE_TO_DATE` ([checkpoint](../docs/SOURCES.md#src-date-constant-target-formatting)). That is carrier-specific and does not generalize: the same failed token as a **temporal-operation operand** is refused `MVK_INVALID_DATE_STRING`, which names the literal, so a consumer cannot read one code as the classification's signature ([checkpoint](../docs/SOURCES.md#src-yearless-anchor-is-the-base-year)). **The omitted-year shape is witnessed**: `"05.03."` reaches a `MM-dd` target and is admitted, while `"05.03"` and `"03.2024"` stay refused, so the trailing dot classifies and the literal is the complete shape with an empty year position ([checkpoint](../docs/SOURCES.md#src-temporal-constant-literal-composition)). **The calendar requirement applies to that shape too, and it is evaluated in a *common* year regardless of any declared Base Year**: `"30.04."` classifies while `"31.04."`, `"00.01."`, and `"13.13."` do not, and `"29.02."` does not either — including on a model whose Base Year is 2024, whose runtime arithmetic demonstrably has that February 29 ([§5](05-dates-and-time.md)). So the classifier resolves no year at all, and a model may compute across a day it cannot name ([checkpoint](../docs/SOURCES.md#src-yearless-anchor-is-the-base-year)). An earlier round read its three refusals against year-bearing targets as "no witness on this route", which was the target's year-bearing-ness held constant rather than a property of the literal. **The vocabulary also includes an exact `HH:mm:ss` clock literal**, which this note previously omitted: `"12:30:00"` classifies as a temporal constant and `"12:30"` does not, the seconds being required in the same way the date shape's zero padding is. **And the shapes compose**: `dateConst` `T` `clockConst` classifies as a date-time, so a lexer enumerating only atomic literals misses it — the only admitted DATETIME spelling measured is `"05.03.2024T12:30:00"`, built from the two literals above and owing nothing to the target's declared format. Which targets then accept such a token is not a lexing question — the target's declared **format string** decides, independently of its declared kind ([`spec/09`](09-computations.md)). Then the AST literal node already carries the right kind.

---

## 3. The condition and operation grammar (sketch)

Two tiers: **conditions** (yield a truth) and **operations** (arithmetic expressions yielding a value). A rule/computation slot holds a condition; comparisons embed operations.

Key structural laws baked into the grammar:

- **No mixed `And`/`Or` without brackets**, refused `MVK_BRACKET_MISSING` — `A And B And C` is fine, `A And B Or C` is rejected because the Kernel declines to supply a precedence rather than applying one silently ([§1](02-logic-and-formal-errors.md)). **A bracket level joins any number of parts**: four joined by `And` and four joined by `Or` are both admitted, so an earlier "at most three parts per bracket level" reading of the production — whose inner group is starred, its two connective labels being the check's operands rather than a cardinality — over-rejects, which is the one direction a checker may not take. **The level the check is scoped to is a bracket *pair*, not a depth**: two sibling parenthesised parts one level deep, one carrying `And` and the other `Or`, joined at the outer level by a single connective, are admitted, while mixing that outer level still refuses; a call's own parentheses and a `Having` filter's body each open a level of their own, so `And` inside a filter with `Or` outside it is admitted. A checker keyed on a depth *counter* over-rejects all of those ([inbound](../docs/SOURCES.md#inbound-2026-09-21-corrections)).
- **At most one division per calculation without grouping braces** `{ … }`; powers `^` cannot be nested without brackets ([§5](04-numbers-and-decimals.md)).
- A **`..` step itself may not carry `*`**; a named segment after the upward walk may carry it ([§10](08-paths-and-references.md)).

```ebnf
(* ---- entry ---- *)
conditionStart   = [ preamble ] , condition , EOF ;
preamble         = "@SuppressWarning" , "(" , warningName , ")" ;   (* the only preamble; one NAME, which must be MVK_INVALID_COMPARE_DEC_PLACES; see §4 *)

(* ---- conditions ---- *)
condition        = branch , { logOp , branch } ;                    (* all logOps at one bracket pair equal; branch count unbounded *)
logOp            = "And" | "Or" ;
branch           = [ comment ] , ( parenCondition | simpleCondition ) , [ comment ] ;
parenCondition   = "(" , condition , ")" ;
simpleCondition  = comparison
                 | fieldListPredicate         (* AllFieldsFilled(...), FieldValuesNotUnique(...), ... *)
                 | groupPredicate             (* GroupFilled(...), NumberOfFilledGroups(...) uses, ... *)
                 | valueListPredicate         (* FieldValueIncludedInValueList(f In list), AtLeastOne...(...) *)
                 | repetitionPredicate        (* RepetitionNotUnique(keys @From Group) *)
                 | dateValidity               (* Valid/Invalid ( Date(...) )  |  Valid(Field, "Type") *)
                 | customCondition ;          (* CustomCondition Name *)

comparison       = operand , compareOp , operand ;
compareOp        = "==" | "!=" | "<" | "<=" | ">" | ">="
                 | "PatternMatched" | "PatternViolated"
                 | "DiffersWithToleranceRange1" | "...Range2" | "...Range5" | "...Range10" ;

(* ---- operations (arithmetic) ---- *)
operand          = term , { ("+" | "-") , term } ;
term             = factor , { ("*" | "/") , factor } ;               (* ≤ 1 "/" unless brace-grouped *)
factor           = power ;
power            = atom , [ "^" , atom ] ;                            (* no nesting without brackets; the EXPONENT is restricted semantically, not here — see the note below *)
atom             = number | dateConst | stringConst                 (* a number literal may carry one sign; see below *)
                 | fieldValue                 (* [ path ] *)
                 | braceGroup                  (* { operand }: the only grouping of an operation; "(" … ")" groups a condition *)
                 | function ;                  (* Sum(...), MaxValue(...), Length(...), Date(...), AddMonths(...), CurrentRepetition(...), BaseYear, Today, Now, RangeAsNumber(...), ValueAsDate(...), ... *)
braceGroup       = "{" , operand , "}" ;

(* ---- names, paths, specifiers ---- *)
fieldValue       = "[" , path , [ semanticIndex ] , "]" ;
path             = [ "/" ] , segment , { "/" , segment }             (* leading "/" = absolute *)
                 | { "../" } , segment , { "/" , segment }           (* relative; a ".." step itself is never starred *)
                 | shortName ;                                       (* bare [Name] when fieldRefByShortNameAllowed *)
segment          = ( identifier | "'" , identifier , "'" ) , [ "*" ] ; (* per-segment star; lower levels must also star *)
havingFilter     = "Having" , condition ;                            (* filters a *-path before an aggregate *)
semanticIndex    = "For" , ( stringConst | path ) ;                  (* row selection by literal or field-reference index value *)
correlation      = "$" , path ;                                     (* only inside a Having filter *)
category         = "->" , identifier ;                               (* enum category read *)
valueListIntro   = "In" ;                                            (* separates fields from the value list *)
```

*(Predicate/function argument shapes—how many operands and whether a `Having` or `$` form is allowed—vary per operator; consult the operator inventory in §5 and the semantics files for each family's operands. Those operator-specific attachments remain leaves in this sketch. The ordinary bracketed `fieldValue` production explicitly includes its optional literal- or field-keyed semantic index.)*

**Which layer refuses an arithmetic symbol, because the grammar above does not say and a parser built from it alone gets two of them wrong.** The infix set is exactly `+ - * / ^`; `%` is not an operator at any layer and fails in the **lexer**, so no grammar rule mentions it. Against that, `^`'s operand restriction is **semantic and post-parse**: `[Base] ^ [Exponent]` over two Number fields *parses* and is then refused `MVK_INVALID_NUMBER_FOR_EXP`, while `[Base] ^ 2` is admitted — so a consumer whose parser narrows `power`'s right-hand `atom` to a literal names a parse defect for a text the Kernel's own parser accepts. The restriction is on the exponent's derived **scale**, not on its field-ness, and [§5](04-numbers-and-decimals.md) owns it ([inbound](../docs/SOURCES.md#inbound-2026-09-21-corrections)).

**Parentheses group conditions only, and braces group operations** ([inbound](../docs/SOURCES.md#inbound-2026-09-25b-condition-positions)). A parenthesised comparison side, a parenthesised operation leading a comparison, a parenthesised argument such as `Sum((Claims*/Amount))` or `Max(([Score] > 1), 2)`, and a computation's parenthesised operation are each `MVK_UNEXPECTED_TOKEN`, while `[Score] > {[Score] + 1}`, a computation's `{[Score] + 1}` and a parenthesised condition are admitted. A comparison in braces is refused, and so are a connective, a comparison or a predicate call as a field operand, a comparison or a predicate call as an operation argument, a predicate call as a comparison side, and a predicate call or a comparison as a computation's whole operation. A filter body is a condition, so a comparison, the same in parentheses and a predicate call are admitted there and an operand alone is refused, as is a comparison in a semantic index's key or a `@From` scope.

**A sign is admitted on a number literal and refused on every other operand measured.** On a rule `[BaseFee] > -1` and `[BaseFee] - -1 > 1` are admitted, and a sign on a reference, a braced operation or a call, or a second sign, is `MVK_UNEXPECTED_TOKEN`. In a computation `-5` and `[BaseFee] * -1` are admitted, and a sign on a reference is refused alone, as a factor, in braces and as a rounding argument ([inbound](../docs/SOURCES.md#inbound-2026-09-25b-condition-positions)). A negated operation is written as a subtraction, `0 - [BaseFee]`.

**Which one class a refused condition text draws: the first raised, in the order the text is read** ([inbound](../docs/SOURCES.md#inbound-2026-09-25b-condition-class-order)). An unresolved name, a character the lexer cannot take, a climb above the root, an unstarred repeatable read, a keyed parallel level beside an unkeyed error field, a misplaced star, an empty group and a stray token each answer when read first. **A gate is raised where the production that owns it ends** ([inbound](../docs/SOURCES.md#inbound-2026-09-25c-gate-raise-points)), so it answers ahead of an unresolved name and a grammar error read past that end, measured on text in a rounding or a date slot, an argument too many, a filtered group in a count, text ordered against a number and two scales held equal. That end is not always the call's. `DifferenceInDays(Reference, NoSuchField) > 0` draws the date slot's `MVK_NO_DATE`, the slot being one argument, while `FieldFilled(Reference, NoSuchField)`, `[Reference] > [NoSuchField]` and `[Reference] * [NoSuchField] > 0` draw `MVK_INVALID_ENTITY`, the name standing inside the call, the comparison or the arithmetic chain that owns the gate, and `[Reference] * [Score] > [NoSuchField]` draws that chain's `MVK_NO_NUMBER_FOR_CALC`. A gated call read to its end keeps its gate when the call around it then fails to parse, `Abs(RoundUpValue(Reference, 2) > 1) > 0` drawing `MVK_NO_NUMBER`, and so does `RoundUpValue(Reference, 2) And FieldFilled(Reference)`, a call that can never become a comparison, while a stray token read before a comparison's type gate answers instead. The mixed-connective gate is raised once the part after each further connective is read: after `FieldFilled(Reference) And FieldFilled(Score) Or`, a bad name in the next part draws `MVK_INVALID_ENTITY` and one in a later part `MVK_BRACKET_MISSING`. A star in a filter body is refused at the starred reference, `MVK_NO_WILDCARDS_ALLOWED` ahead of a bad name later in the same body, and the containment gate of a per-row read beside an uncontained error field at that read, ahead of a later bad name and behind an earlier one. A year-less date construction and the base-year constant each answer when written first, and an unstarred repeatable group handed to `ValueNotConsistent` draws the reference walk's `MVK_NO_WILDCARD` ahead of the operator's own chain. **A filtered operand is raised at two points** ([§9](07-repetition-and-iteration.md), [inbound](../docs/SOURCES.md#inbound-2026-09-25c-filter-body)): the filtered entity's kind as `Having` is read, so a group is refused ahead of anything its body holds, and the rest of the filter's chain once its whole specification is read, so a defect in its body, a refused comparison included, answers ahead of the operand's own missing star. Of two defects meeting at one offset, `FieldFilled(Reference) NoSuchField` draws `MVK_UNEXPECTED_TOKEN` and `FieldFilled(NoSuchField` `MVK_INVALID_ENTITY`. A post-parse class yields to the parse-time classes measured beside it: `MVK_ERROR_FIELD_NOT_REFERENCED` to an unresolved name on either side and to every one of those gates but the filtered count, which is not measured there. The form-level constructs a German A12 model lexes ([checkpoint](../docs/SOURCES.md#src-form-condition-constructs)) follow the same order: `VordruckAngegeben(Order)` draws `MVK_INVALID_ROOT_GROUP_CONSTR` ahead of a later unresolved name and of a grammar error inside or after its parentheses, an unresolved name before it answers instead, and `VordruckAngegeben(NoSuchForm)`, naming no form, draws the construct class too. The class is raised on the keyword itself, before its argument list is read: `VordruckAngegeben Oder FeldAngegeben(Code)`, with no list, `VordruckAngegeben(` and `VordruckAngegeben(Oder)` draw it alone. It is drawn wherever a condition opens, at the text's start, after a connective, and inside a grouping parenthesis at either place, while the construct after a completed condition, `FeldAngegeben(Code) VordruckAngegeben(Order)`, and as a field operand, `FeldAngegeben(VordruckAngegeben(Order))`, is `MVK_UNEXPECTED_TOKEN`, as is a parse failing ahead of the keyword ([inbound](../docs/SOURCES.md#inbound-2026-09-25c-form-keyword)). `AnzahlAngegebenerVordrucke(Order) > 0` draws that class as well, and `AktuelleVordruckNummer(Code) > 0` and `MaximalAngegebenerZeilenindex(Code) > 0` are `MVK_UNEXPECTED_TOKEN` on that model.

> **Non-normative implementation note.** Parse to a single `inductive Ast` with constructors mirroring `simpleCondition`/`operand`/`function`. Encode the structural laws as *parser* rules (reject mixed And/Or, reject a star attached to a `..` step, reject a second unbraced `/`) rather than as post-hoc validation—they are genuinely syntactic. Keep `Having` and `For` as path modifiers and `$` as a correlated path form, since they modify how a path resolves ([§9](07-repetition-and-iteration.md)/[§10](08-paths-and-references.md)) rather than being operators in their own right.

---

## 4. Directives and the special entities

| Form | Written | Meaning |
|---|---|---|
| suppress-warning preamble | `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)` | waive the equality scale gate — the **only** suppressible warning ([§5](04-numbers-and-decimals.md)) |
| reference-group scope | `RepetitionNotUnique(a, b @From Group)` | choose the uniqueness scope ([§9](07-repetition-and-iteration.md)) |
| the rule's own group | `RuleGroup` | the rule's containing group as an entity; counts as referencing the error field; a `*` on it is rejected ([§10](08-paths-and-references.md)) |
| semantic index | `[Field For "value"]` or `[Field For CustomerName]` | select a row by a literal index value or by the value read from the named field ([§10](08-paths-and-references.md)) |
| correlation | `$path` (inside `Having`) | pin to the current outer repetition ([§9](07-repetition-and-iteration.md)) |
| value-list membership | `… In ( … )` | the `In` separator between fields and the value list |

**A computation's `errorCodesToSuppress` reaches the same preamble as text.** Its entries are joined with `,` into `@SuppressWarning(…)` ahead of the condition and parsed by the condition lexer and parser in the model's condition language, so the first failure in that text answers, whether it is a character the lexer cannot take or a token the parser cannot use. An absent or empty list is admitted. One entry that lexes as a single name other than the supported code is `MVK_INVALID_SUPPRESSED_WARNING` — `Late_Fee`, `_LATE_FEE`, `MVK:LATE`, `MVK_GEBÜHR`, `MVK_CODE7`, the supported name in lower case, and a keyword of the *other* condition language. The supported name padded with spaces, or with a tab and a line break, is admitted. Text that lexes but is not one usable name is `MVK_UNEXPECTED_TOKEN` — `7_DAYS`, `MVK_LATE FEE`, `MVK_LATE.FEE`, either quoted form, a trailing `;;` comment, `#Zeile`, a blank entry, and a keyword of the model's own language (`And`, `Sum` in an English model, `Summe` in a German one) — and so is a list of two names, the supported name twice included. A character the lexer cannot take is `MVK_LEXER_STANDARD_ERROR` — `MVK_FRAÉ`, an unclosed quote, `#LATE`, a no-break space before the name — unless a parser failure comes earlier in the text: `7_DAYS É` and `And É` are `MVK_UNEXPECTED_TOKEN`, and `MVK_FRAÉ` followed by the supported name is the lexer error while the reverse order is `MVK_UNEXPECTED_TOKEN` ([inbound](../docs/SOURCES.md#inbound-2026-09-24b-lexer-and-blank-text)). **Being the text's first part, the preamble's class answers ahead of the classes measured beside it** ([inbound](../docs/SOURCES.md#inbound-2026-09-25b-computation-texts)): an unsupported name draws `MVK_INVALID_SUPPRESSED_WARNING` beside an operation or precondition naming nothing, a text in a rounding slot, a read of the computed field and a control character in the message, each of which draws its own class without the member, and the supported name twice draws `MVK_UNEXPECTED_TOKEN` beside the unresolved operation, the rounding slot and the control character.

---

## 5. Keyword catalog (English ↔ German, verified pairs)

Every English terminal carries a German spelling, but not the converse — the 13 German-only H-model form constructs of §1 have no entry below and no English twin. Symbols are language-neutral. A representative, verified sample (the full set is large; the pattern is systematic — German uses the domain nouns *Feld* = field, *Kontext* = repetition/group-context, *Wiederholung* = repetition, *Angegeben* = specified/filled):

| English | German |
|---|---|
| `And` / `Or` | `Und` / `Oder` |
| `FieldFilled` / `FieldNotFilled` | `FeldAngegeben` / `FeldNichtAngegeben` |
| `AllFieldsFilled` | `AlleFelderAngegeben` |
| `NumberOfFilledFields` | `AnzahlAngegebenerFelder` |
| `GroupFilled` | `KontextAngegeben` |
| `NumberOfFilledGroups` | `AnzahlAngegebenerKontexte` |
| `CurrentRepetition` | `AktuelleWiederholung` |
| `RepetitionNotUnique` | `WiederholungNichtEindeutig` |
| `Length` | `Laenge` |
| `PatternMatched` | `WieMuster` |
| `Sum` | `Summe` |
| `MaxValue` / `MinValue` | `MaxWert` / `MinWert` |
| `FirstFilledValue` | `ErsterAngegebenerWert` |
| `Today` / `Now` | `Heute` / `Jetzt` |
| `DifferenceInDays` | `DifferenzInTagen` |
| `AddMonths` | `AddiereMonate` |
| `Valid` / `Invalid` | `Gueltig` / `Ungueltig` |
| `CustomCondition` | `ApplikationsBedingung` |
| `@SuppressWarning` | `@UnterdrueckeWarnung` |
| `RuleGroup` | `RegelKontext` |
| `BaseYear` | `Referenzjahr` |
| `RangeAsNumber` / `RangeAsString` | `BereichAlsZahl` / `BereichAlsString` |
| `AbsValue` | `AbsWert` |
| `FirstDay` / `LastDay` (of `ValueAsDate`) | `ErsterTag` / `LetzterTag` |

> **Non-normative implementation note.** Model keywords as a table of explicitly accepted spellings mapped to `(opId, lang)`, plus one canonical render spelling per `(opId, lang)`. Do not normalize case before lookup. Keep it *data*, not code — a future port to another surface re-reads the same table. English is the canonical render target; German is a supported second target.

---

## Checklist for the concrete syntax

- [ ] Two keyword languages; only the enumerated English `And`/`Or`/`In`/range-`to` and German `Und`/`Oder`/`In`/range-`zu` case families are accepted; writing is canonical; symbols are language-neutral; `;;` comments and quoted keyword-named identifiers are supported.
- [ ] Literal kind (`number` / `dateConst` / `stringConst`) fixed at lex time; date-shape ⇒ date, ISO-shape ⇒ string, `""` ≠ empty value.
- [ ] Parser enforces: no mixed `And`/`Or` within one bracket pair (`MVK_BRACKET_MISSING`), with the part count unbounded and a call's or filter's parentheses opening their own pair; ≤ 1 unbraced `/`; `^` not nested unbracketed and its **exponent** semantically restricted ([§5](04-numbers-and-decimals.md)); `..`+`*` rejected.
- [ ] Paths: absolute `/`, relative `../`, per-segment `*` (lower levels must star), short name, quoted names; specifiers `Having` / `For` with a string or field-reference key / `$` attach to paths.
- [ ] Directives: `@SuppressWarning(only-that-code)`, `@From`, `RuleGroup`, `In`.
- [ ] Bidirectional keyword table (EN canonical, DE supported).
