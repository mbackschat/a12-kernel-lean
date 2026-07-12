# 12 — Concrete syntax: lexing, keywords, directives, grammar sketch

The other half of "syntax and semantics". Everything above describes how a condition *evaluates*; this file describes how a condition is *written* — enough to build a lexer/parser or hand the grammar to a parser generator. It is a **sketch of the surface**, not a transcription of the engine's grammar file; production *names* are borrowed for orientation, the EBNF below is an original re-expression.

The AST the parser targets is the closed set of constructs described across §1–§14; [`13-lean-encoding-guide.md`](13-lean-encoding-guide.md) proposes an `inductive` shape.

---

## 1. Lexical structure

- **Two keyword languages.** Every worded operator has an English and a German spelling (table in §5). The comparison and arithmetic *symbols* (`== != < <= > >= + - * / ^ -> $`) are **intrinsic** — identical in both languages.
- **Keyword case is read-tolerant, write-canonical.** On *reading*, keyword case variants are accepted (`fieldfilled`, `FIELDFILLED`); on *writing*, the engine (and a faithful renderer) emits the catalog's canonical spelling. Field/group *names* are case-sensitive identifiers.
- **Comments** are `;;` to end of line. A comment may sit before/after a condition branch and (in the engine's round-trip) the leading comment is preserved on write-back. Treat `;;…\n` as a skippable trivia token that a faithful round-tripping parser may choose to attach to the adjacent branch.
- **Whitespace** separates tokens and is otherwise insignificant (except inside string literals).
- **Identifiers that collide with a keyword must be single-quoted** in a path: `Order/'Date'` names a field called `Date`.

---

## 2. Literals

| Literal | Form | Notes |
|---|---|---|
| number | `123`, `-1.5`, `0.000` | decimal separator is always `.`; literals are **scale-exempt** in `==`/`!=` ([§5](04-numbers-and-decimals.md)); ≤ 15 digits |
| date constant | `"31.12.2024"` | `DD.MM.YYYY`, day-first, always `.`; **a string literal matching this shape *is* a date** ([§6](05-dates-and-time.md)) |
| omitted-year date | `"13.07."` | trailing dot; completes against the model **Base Year** (rejected if none) |
| string | `"abc"` | double-quoted; a **date-shaped** content is a date, an **ISO-shaped** `"2024-12-31"` stays a string; `""` is *not* an empty-string value ([§2](03-empty-and-required.md)) |
| boolean / confirm const | `True` / `False` | compared to Boolean/Confirm fields per [§1](02-logic-and-formal-errors.md) |
| value list | `( "A", "B" )` / `( 1, 2, 3 )` | string list or number list, introduced by the `In` separator (see §4) |

> **Lean modelling note.** The date/string ambiguity is a **lexer/typer** decision, not an evaluator one: classify a `"…"` token as `dateConst` iff its content matches `DD.MM.YYYY` (or the omitted-year shape), else `strConst`; ISO shapes are always `strConst`. Then the AST literal node already carries the right kind.

---

## 3. The condition and operation grammar (sketch)

Two tiers: **conditions** (yield a truth) and **operations** (arithmetic expressions yielding a value). A rule/computation slot holds a condition; comparisons embed operations.

Key structural laws baked into the grammar:

- **No mixed `And`/`Or` without brackets**, and **at most three parts per bracket level** — `A And B And C` is fine, `A And B Or C` is a parse error ([§1](02-logic-and-formal-errors.md)).
- **At most one division per calculation without grouping braces** `{ … }`; powers `^` cannot be nested without brackets ([§5](04-numbers-and-decimals.md)).
- A **`..` up-navigation may not be combined with `*`** ([§10](08-paths-and-references.md)).

```ebnf
(* ---- entry ---- *)
conditionStart   = [ preamble ] , condition , EOF ;
preamble         = "@SuppressWarning" , "(" , warningName , ")" ;   (* the only preamble; NAME must be MVK_INVALID_COMPARE_DEC_PLACES *)

(* ---- conditions ---- *)
condition        = branch , { logOp , branch } ;                    (* all logOps at one level equal; ≤ 3 branches *)
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
power            = atom , [ "^" , atom ] ;                            (* no nesting without brackets *)
atom             = number | dateConst | stringConst
                 | fieldValue                 (* [ path ] *)
                 | braceGroup                  (* { operand } *)
                 | "(" , operand , ")"
                 | function ;                  (* Sum(...), MaxValue(...), Length(...), Date(...), AddMonths(...), CurrentRepetition(...), BaseYear, Today, Now, RangeAsNumber(...), ValueAsDate(...), ... *)
braceGroup       = "{" , operand , "}" ;

(* ---- names, paths, specifiers ---- *)
fieldValue       = "[" , path , "]" ;
path             = [ "/" ] , segment , { "/" , segment }             (* leading "/" = absolute *)
                 | { "../" } , segment , { "/" , segment }           (* relative; ".." not combinable with "*" *)
                 | shortName ;                                       (* bare [Name] when fieldRefByShortNameAllowed *)
segment          = ( identifier | "'" , identifier , "'" ) , [ "*" ] ; (* per-segment star; lower levels must also star *)
specifier        = havingFilter | semanticIndex | correlation ;
havingFilter     = "Having" , condition ;                            (* filters a *-path before an aggregate *)
semanticIndex    = "For" , stringConst ;                             (* row selection by index value *)
correlation      = "$" , path ;                                     (* only inside a Having filter *)
category         = "->" , identifier ;                               (* enum category read *)
valueListIntro   = "In" ;                                            (* separates fields from the value list *)
```

*(Predicate/function argument shapes — how many operands, whether a `Having`/index/`$` specifier is allowed — vary per operator; consult the operator inventory in §5 and the semantics files for each family's operands. The sketch above shows the *frame*; the per-operator argument lists are the leaves.)*

> **Lean modelling note.** Parse to a single `inductive Ast` with constructors mirroring `simpleCondition`/`operand`/`function`. Encode the structural laws as *parser* rules (reject mixed And/Or, reject `..`+`*`, reject a second unbraced `/`) rather than as post-hoc validation — they are genuinely syntactic. Keep `Having`/`For`/`$` as *specifiers* attached to a path node, since they modify how a path resolves ([§9](07-repetition-and-iteration.md)/[§10](08-paths-and-references.md)) rather than being operators in their own right.

---

## 4. Directives and the special entities

| Form | Written | Meaning |
|---|---|---|
| suppress-warning preamble | `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)` | waive the equality scale gate — the **only** suppressible warning ([§5](04-numbers-and-decimals.md)) |
| reference-group scope | `RepetitionNotUnique(a, b @From Group)` | choose the uniqueness scope ([§9](07-repetition-and-iteration.md)) |
| the rule's own group | `RuleGroup` | the rule's containing group as an entity; counts as referencing the error field; a `*` on it is rejected ([§10](08-paths-and-references.md)) |
| semantic index | `[Field For "value"]` | select a row by index value ([§10](08-paths-and-references.md)) |
| correlation | `$path` (inside `Having`) | pin to the current outer repetition ([§9](07-repetition-and-iteration.md)) |
| value-list membership | `… In ( … )` | the `In` separator between fields and the value list |

---

## 5. Keyword catalog (English ↔ German, verified pairs)

Worded operators carry both spellings; symbols are language-neutral. A representative, verified sample (the full set is large; the pattern is systematic — German uses the domain nouns *Feld* = field, *Kontext* = repetition/group-context, *Wiederholung* = repetition, *Angegeben* = specified/filled):

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

> **Lean modelling note.** Model keywords as a **bidirectional table** `keyword ↔ (opId, lang)`, so the lexer maps either language to one `opId` and the renderer maps `opId + lang` back to a spelling. Keep it *data*, not code — a future port to another surface re-reads the same table. English is the canonical render target; German is a supported second target.

---

## Checklist for the concrete syntax

- [ ] Two keyword languages, case-read-tolerant/canonical-write; symbols language-neutral; `;;` comments; quoted keyword-named identifiers.
- [ ] Literal kind (`number` / `dateConst` / `stringConst`) fixed at lex time; date-shape ⇒ date, ISO-shape ⇒ string, `""` ≠ empty value.
- [ ] Parser enforces: no mixed `And`/`Or` unbracketed (≤ 3 parts/level); ≤ 1 unbraced `/`; `^` not nested unbracketed; `..`+`*` rejected.
- [ ] Paths: absolute `/`, relative `../`, per-segment `*` (lower levels must star), short name, quoted names; specifiers `Having` / `For "…"` / `$` attach to paths.
- [ ] Directives: `@SuppressWarning(only-that-code)`, `@From`, `RuleGroup`, `In`.
- [ ] Bidirectional keyword table (EN canonical, DE supported).
