# A12 Kernel validation and computation semantics

<a id="a12-kernel-validation-language-semantics-mapped-for-a-lean-reimplementation"></a>
<a id="a12-kernel--validation-language-semantics-mapped-for-a-lean-reimplementation"></a>

This is the entry point to a standalone, language-neutral description of how the **A12 Kernel's validation and computation language evaluates** in Kernel version 30.8.1: the Kernel validates a Document/DocumentV2 (a data document) against a DocumentModel, and computes derived fields over the same pair. **This map is a non-normative summary and navigation aid.** Every rule it mentions is owned by the chapter it links, and where this map and a chapter differ, the chapter wins. Read it for the mental model, the vocabulary and the route to the owning clause; implement from the chapters.

> **How to read this set.** The numbered chapters state the observable behaviour and static legality; [the operator reference](14-operator-reference.md) assigns every operator its class per mechanism. In a link label, `§n` is the taxonomy number of the target chapter (§3 below), not its file number; links into spec/01 are labelled "data model §n", into spec/12 "concrete syntax §n", and into spec/14 "operator reference". A **Non-normative implementation note** in a chapter carries implementation advice only. A chapter section that cites sources ends with one `Sources:` line naming its provenance; [`docs/SOURCES.md`](../docs/SOURCES.md) owns provenance and source navigation, and [`docs/LEAN-ENCODING-GUIDE.md`](../docs/LEAN-ENCODING-GUIDE.md) the project's Lean encoding guidance.

---

## 0. Provenance, scope, and the license posture

- **What is described.** The evaluation semantics of the A12 Kernel's validation language (also called the condition language or DSL) and computation language in Kernel 30.8.1: when a rule fires, which message type it carries, what a computation produces, and which authored shapes are legal.
- **What is out of scope** is [data model §5](01-data-model.md#5-what-is-not-modelled-here)'s list: model include/expansion, the editor and its required checkbox, persistence and wire format (apart from the one JSON conversion of [data model §2.3](01-data-model.md#23-reading-a-document-from-json)), and code-generation targets, the Groovy-dynamic strategy being the observation anchor. These are touched only where they change evaluation. The kernel's host pointer API is not excluded: [data model §2.1](01-data-model.md#21-repetition-contexts-the-iteration-environment) states the rules an implementation reproducing it must follow.
- **Where provenance lives.** Source routes, the Kernel revision and reviewed a12-dmkits provenance are in [`docs/SOURCES.md`](../docs/SOURCES.md); outbound reconciliation state is in [`docs/A12-DMKITS-SPEC-SYNC-LEDGER.md`](../docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).
- **Clean-room posture.** The chapters describe observable behaviour — what the engine does for given inputs, established by experiment and by reading its specification and source — not a transcription of engine source. Read them to learn the exact behaviour, then write original code and lock it against the behaviour with tests: copy the *mechanism*, never the *expression*.

**The chapters bound their claims with a fixed vocabulary.** A rule stated without a qualifier is the chapter's account of Kernel 30.8.1; these terms narrow it:

| Term | What it binds |
|---|---|
| `Measured scope: …` | the cases the cited observations cover; the rule is stated beyond them but unmeasured there |
| `Measured members: …; others unmeasured` | a list given by example: the named members are observed, membership of any other is not |
| `unmeasured`, `not measured` | the rule or case has no Kernel observation behind it |
| `source reading` | the rule rests on reading the Kernel's source, not on a run |
| `no witness known` | no admitted input reaching the case is known; the clause still states a total rule |
| `not stated` | no chapter decides the case; in the operator reference, a cell whose column applies but whose class no chapter decides |
| ⚠ | a trap: behaviour a plausible reimplementation is likely to get wrong |

---

## 1. The kernel in one page

### 1.1 Models, documents, groups, fields

A **document model** declares a *tree* ([data model §1](01-data-model.md#1-model--a-typed-tree)):

- **Groups** are the internal nodes; the root is a single group. A group is **non-repeatable** (at most once wherever its parent occurs) or **repeatable** (rows `1 … rowCount` within a declared `repeatability` bound).
- **Fields** are the leaves. Each has a **type** (§2 below) and per-type configuration such as a Number's scale, a String's pattern and lengths, an Enumeration's value set or a Date's format and precision.
- **Declarations meet static legality** before anything is evaluated: model consistency rules, declaration generation classes and variant filters ([data model §1.2](01-data-model.md#12-model-consistency-rules), [data model §1.3](01-data-model.md#13-declaration-generation-classes), [data model §1.4](01-data-model.md#14-variant-filters-and-where-a-filtered-declaration-is-seen)).

A **document** instantiates the model: repeatable groups are expanded into rows, and fields hold values or are empty. One field at one repetition context is a **cell** ([data model §2](01-data-model.md#2-document--an-instance-of-the-tree)).

```
Order                     (root group, non-repeatable)
├─ OrderDate  : Date
├─ Customer   : String
└─ LineItem*  : group     (repeatable — the * marks it)
   ├─ Sku      : String
   ├─ Quantity : Number(scale 0)
   └─ UnitPrice: Number(scale 2)
```

A document over this model might instantiate three `LineItem` rows; `LineItem*/Quantity` then denotes a *column* of three cells.

### 1.2 Two operations, one language

The kernel does two things over (model, document) ([data model §3](01-data-model.md#3-rules-and-computations)):

1. **Validation** runs the model's **rules** and produces a set of structured **messages**, each with a severity, a message *type*, an error field address, `referenced` and `fillToFix` pointer sets and interpolated text ([data model §3.1](01-data-model.md#31-rules-validation)).
2. **Computation** runs the model's **computation rules** and produces a result for the computed fields, which a separate apply step writes ([data model §4.3](01-data-model.md#43-the-compute--apply--validate-flow)).

Both are written in the **same** expression language ([§11](09-computations.md)). They differ in how they treat a formally invalid cell: validation excludes it, computation is poisoned by it ([§3 B.6](02-logic-and-formal-errors.md#b6-validation-excludes-computation-poisons)).

### 1.3 A rule states the *error* — and that polarity is fixed ⚠

A rule has exactly **one** condition slot, and **the condition is TRUE precisely when the data is invalid**; there is no assertion form ([data model §3.1](01-data-model.md#31-rules-validation)).

```
FieldNotFilled(Customer)          -- the rule "Customer is missing" (fires when empty)
[Quantity] < 1                    -- the rule "Quantity below 1 is an error"
```

A requirement is therefore authored as *its violation*. A positively phrased condition is admitted like any other, since admission does not decide satisfiability ([§3 B.1](02-logic-and-formal-errors.md#b1-what-a-formal-error-is)), and so silently states the opposite rule.

### 1.4 Severity is metadata; message *type* is computed

A rule's severity — **ERROR / WARNING / INFO** — is message metadata: the condition fires identically whatever the severity, and only ERROR messages make the document invalid ([§12 §2](10-validation-and-polarity.md#2-severity-is-metadata)).

Independently, every fired message carries a **message type**, **VALUE** or **OMISSION**, computed from the data rather than fixed per operator: OMISSION means filling some currently empty field could satisfy the rule, VALUE that no fill can and only changing an entered value helps ([§12 §3](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-)). This second dimension has its own algebra beside truth ([§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)).

### 1.5 The call surface and the form-engine flow

- **`validateFull(document)`** evaluates every rule over the whole document ([data model §4.1](01-data-model.md#41-validatefull)).
- **`validatePart(document, relevantSet)`** evaluates a relevant subset. Its guarantee is one-directional: it never reports an error fixable only outside the subset, but it may skip checks, so a document passing a partial validation can still fail a full one ([data model §4.2](01-data-model.md#42-validatepart), [§12 §5](10-validation-and-polarity.md#5-full-vs-partial-validation)).
- **Validation never computes first.** The consumer composes **compute → apply → validate**; application is placement-sensitive, each change action (VALUE, CLEARED, ERRORED) having its own effect on the destination ([data model §4.3](01-data-model.md#43-the-compute--apply--validate-flow)).

---

## 2. Field types at a glance

The field's **type** decides which operators are legal on it and how an empty or mismatched value behaves. Each row summarises the linked clauses.

| Field type | Key configuration | An **empty** value, in a comparison | Notes that bite | Owner |
|---|---|---|---|---|
| **Number** | scale (maximum fractional digits), digit counts, min/max, sign | the fillable **`0`** | scale gates `==`/`!=` statically, while ordering and tolerance comparisons are scale-exempt; `MinValue`/`MaxValue` drop an empty cell | [§5 §1](04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time), [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default), [§2 A.2](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default) |
| **Boolean** | — | **not evaluated** | three states: `[F] == True` is not `FieldFilled(F)`, and an unset Boolean satisfies neither `== True` nor `== False` | [§1 A.3](02-logic-and-formal-errors.md#a3-boolean-is-a-three-state-field-type-distinct-from-three-valued-logic) |
| **Confirm** | — | **`False`** | differs from Boolean; a stored `false` is a formal error | [§1 A.3](02-logic-and-formal-errors.md#a3-boolean-is-a-three-state-field-type-distinct-from-three-valued-logic), [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default) |
| **String** | pattern, min/max length, line breaks, raw type (`noValueValidation`) | **not evaluated** | `Length` and the declared minimum and maximum lengths count UTF-16 code units after CRLF normalization; a raw String's presence is readable and its value is not; there is no empty String value, so `[F] == ""` and `[F] != ""` never hold | [§7](06-strings-and-enumerations.md#part-a--7-strings-and-patterns), [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default) |
| **Enumeration** | value set, localized labels, categories, S-value | **not evaluated** | compared by stored value, not display text; display labels decide direct-field comparability; `->` reads a value's category | [§8 B.1](06-strings-and-enumerations.md#b1-comparison-is-by-stored-value-and-direct-field-comparability-depends-on-effective-display-remapping), [§8 B.2](06-strings-and-enumerations.md#b2-categories-via--) |
| **Date** | a format from the shared temporal vocabulary; date precision `FULL`, `DAY_OPTIONAL`, `MONTH_OPTIONAL` or `YEAR_OPTIONAL` | **not evaluated** | a quoted `DD.MM.YYYY` literal naming a real date *is* a date constant | [§6](05-dates-and-time.md#declared-formats-and-stored-temporal-text), [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-), [§6 §6.2](05-dates-and-time.md#62-partially-known-dates) |
| **Time** | a format from the same vocabulary | **not evaluated** | the declared format, never the kind, decides every temporal gate; an extractor needs a format carrying its component | [§6](05-dates-and-time.md#the-format-decides-never-the-kind), [§6 §9](05-dates-and-time.md#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-) |
| **DateTime** | a format from the same vocabulary | **not evaluated** | `Now` is a DateTime; sub-day arithmetic works on epoch milliseconds | [§6 §2.6](05-dates-and-time.md#26-sub-day-arithmetic), [§6 §7](05-dates-and-time.md#7-the-point-in-time-and-reference-sources) |
| **DateFragment** | any format of the shared temporal vocabulary, under `formatOfFragment` | **not evaluated** | a deliberately imprecise date; with a Base Year it completes to its earliest concrete date where an operation needs one | [§6 §6.1](05-dates-and-time.md#61-fragments), [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default) |
| **DateRange** | a declared `(format, separator)` pair, one of eight admitted; `interpretationOfYear` | **not evaluated** | only `==`/`!=`; `DateRange(start, end)` endpoints are bare entity references whose formats carry the same date-only component set, and a construction is not admitted in overlap or bound extraction; overlap intervals are closed | [§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap), [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default) |
| **Custom** | registered validator name; optional min/max length | as a String: **not evaluated** | an empty cell does not invoke the validator; a relevant concrete value is passed with effective bounds, locale and stored/display mode; a rejection keeps its project code and optional message; `Valid(F, "Name")` invokes the validator as an explicit predicate | [§7 A.3](06-strings-and-enumerations.md#a3-custom-field-type-validation), [§6 §3.7](05-dates-and-time.md#37-valid-and-invalid-over-a-named-type), [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default) |
| **TypeDefinition** | references a reusable type | its base kind's | a typedef field is its base kind at every measured gate | [data model §5](01-data-model.md#5-what-is-not-modelled-here) |

**⚠ The most common real-world bug** is the empty column: `[Amount] < 100` **fires** on an empty Number (empty reads `0`), while `[Date] > "01.01.2022"` **stays quiet** on an empty Date (not evaluated). Same shape, opposite behaviour, decided by type; [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default) owns it, and [operator reference column N](14-operator-reference.md#empty-read) gives each operator's own empty read.

---

## 3. The taxonomy

The chapters are listed in file order. The `§n` column is the taxonomy number that link labels use: it follows the language's areas, not the files, so §1 and §3 share spec/02 while §2 and §4 share spec/03, and spec/01, spec/12, spec/13 and spec/14 carry none. **Difficulty** rates how hard an area is to reimplement faithfully (★ easy … ★★★★★ where reimplementations fail).

| File | § | Area | In one line | Difficulty |
|---|---|---|---|---|
| [`01-data-model.md`](01-data-model.md) | — | Data model & call surface | the model tree and its declaration legality (repeatability, consistency rules, declaration generation classes, variant filters); documents, cells and repetition contexts; JSON reading; rules, computations and their message channels; `validateFull`, `validatePart` and compute → apply → validate | ★★☆☆☆ |
| [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md) | §1 | Truth values & logical evaluation | strong-Kleene `And`/`Or` with mandatory brackets; no generic `Not`; the three-state Boolean type; fill quantifiers and group scopes | ★★★☆☆ |
| [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md) | §3 | Formal errors & the "unknown" state | the third cell state and its producers; branch-scoped suppression; validation excludes, computation poisons | ★★★★★ |
| [`03-empty-and-required.md`](03-empty-and-required.md) | §2 | Non-specified (empty) values | the per-kind default; operator overrides; all-empty aggregate identities; the row gate | ★★★★☆ |
| [`03-empty-and-required.md`](03-empty-and-required.md) | §4 | The "required" property | a generated rule plus a validation-scoped formal finding; the index field's mandatory and unique checks | ★★★☆☆ |
| [`04-numbers-and-decimals.md`](04-numbers-and-decimals.md) | §5 | Numbers & decimals | the storage regime; static scale gates on `==`/`!=`; three rounding modes; consumer-sensitive domain failures; operand-list `Min`/`Max`, value functions and Number-valued sources; the scale-19 and 50-digit precision constants | ★★★★☆ |
| [`05-dates-and-time.md`](05-dates-and-time.md) | §6 | Dates & time | the format vocabulary, where the format decides and never the kind; literal classification; asymmetric calendar-corrected shifts and differences; construction and validity; the Gregorian floor; time zones; fragments; point-in-time sources; date ranges and overlap; per-operator operand gates | ★★★★☆ |
| [`06-strings-and-enumerations.md`](06-strings-and-enumerations.md) | §7 | Strings, patterns & field-type checks | stored-value checking and CRLF normalization; UTF-16 `Length`; pattern admission and execution; `+` concatenation; raw-type Strings; the legal charset; custom field-type validation | ★★☆☆☆ |
| [`06-strings-and-enumerations.md`](06-strings-and-enumerations.md) | §8 | Enumerations | stored-value comparison and display-bearing comparability; categories via `->`; value-list quantifiers; scalar membership; table-backed Enumerations | ★★★☆☆ |
| [`07-repetition-and-iteration.md`](07-repetition-and-iteration.md) | §9 | Repetition, iteration & cross-array evaluation | iteration scope from condition references; evaluation domains; error-field admission and the negative-condition guard; the parallel join; `Having`, `$` and ordered aggregation; star binding; group presence; `RepetitionNotUnique` | ★★★★★ |
| [`08-paths-and-references.md`](08-paths-and-references.md) | §10 | Paths & references | absolute, relative and short-name paths; bare-name resolution order; star placement and `$`; rows addressed by semantic key, never by position | ★★★★☆ |
| [`09-computations.md`](09-computations.md) | §11 | Computations | first-match selection across alternatives and its generated all-alternatives validation rule; the target self-read gate; five outcomes and their change actions; the eager formal-operand inventory; empty cascade versus poison; the stored form; scope and the parallel join | ★★★★★ |
| [`10-validation-and-polarity.md`](10-validation-and-polarity.md) | §12 | The validation model | formal versus rule validation; severity metadata; VALUE/OMISSION typing by directional fill; full versus partial validation | ★★★★★ |
| [`11-messages-and-custom.md`](11-messages-and-custom.md) | §13 | Error-message interpolation | producer-specific template grammars; parse order; rendering a rule-owned message; field-owned producers | ★★☆☆☆ |
| [`11-messages-and-custom.md`](11-messages-and-custom.md) | §14 | CustomCondition — the escape hatch | a host-code predicate; refused in computations and filters | ★★☆☆☆ |
| [`12-concrete-syntax.md`](12-concrete-syntax.md) | — | Concrete syntax | lexical structure, literals, a grammar sketch, the class a refused text draws, argument slots, directives and the English/German keyword catalog | ★★★☆☆ |
| [`13-lean-encoding-guide.md`](13-lean-encoding-guide.md) | — | Lean encoding guide | a navigation stub pointing to [`docs/LEAN-ENCODING-GUIDE.md`](../docs/LEAN-ENCODING-GUIDE.md) | — |
| [`14-operator-reference.md`](14-operator-reference.md) | — | Operator reference | which class every operator takes per mechanism: unavailable reads, classification, polarity, filter effect, partial extent, traversal, argument slots, keyed guard, temporal gate, empty read, content gate, static scale, raw String operand, keyed and category operands, fill-to-fix | — |

---

## 4. The five things a naive reimplementation gets wrong

Each is the root of a family of bugs and is owned by the linked clauses.

1. **There are three cell states, not two — empty ≠ invalid.** Besides *empty* and *filled*, a cell is **not-check-relevant** while it carries a formal finding, which need not be a stored value: a malformed or out-of-constraint value, a custom-validator rejection, a duplicate index value, an over-repetition row, or the validation-scoped required finding on an empty cell. Validation reads such a cell as UNKNOWN (counted neither filled nor empty, an all-cells aggregate over it UNKNOWN); computation reads it as poison, except that a required-and-empty cell reads as plain empty, and a group presence read never poisons. Non-relevance under partial validation is a separate, call-local source of UNKNOWN, not a cell state. A reached `CustomCondition` receives the formal-invalid set instead of a suppressed read. ([§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty), [§3 B.3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state), [§14 B.3](11-messages-and-custom.md#b3-the-invocation))

2. **UNKNOWN comes from the data, never from a connective.** `And` and `Or` are strong-Kleene and introduce no third value; UNKNOWN enters only when an operand reads a third-state cell or another UNKNOWN source, and the tables decide how far it reaches — **branch-scoped, not rule-scoped**: `healthy Or [broken] > 0` still fires, `healthy And [broken] > 0` is suppressed. ([§1 A.1](02-logic-and-formal-errors.md#a1-connectives-and-mandatory-parentheses), [§3 B.4](02-logic-and-formal-errors.md#b4-suppression-is-branch-scoped-and-reaches-presence-checks))

3. **"Empty" is per kind, and operators override it.** An empty Number reads the fillable `0` (so `[n] < 100` fires), an empty Confirm `False`, and an empty Boolean, String, Enumeration, Date, Time or DateTime leaves the comparison not evaluated. Operators override the default: for example `+` concatenation reads `""`, `Length` reads `0`, the cell counts never count an empty, and operand-list `Min`/`Max` substitute `0` for a Number but skip an empty Date. ([§2 A.1](03-empty-and-required.md#a1-the-per-kind-default), [§2 A.2](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default), [operator reference column N](14-operator-reference.md#empty-read))

4. **Message polarity (VALUE vs OMISSION) is a second dimension computed beside truth.** It is derived from **directional fillability**: each operand carries whether a fill could still make it grow or shrink (a single not-given bit for temporal operands and Strings), and the consuming comparison decides whether a legal fill could falsify the firing. Among fired operands, OMISSION wins under `And` and VALUE wins under `Or`. ([§12 §3](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-), [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing))

5. **Computation's failure propagation is order-dependent poison, not a pure cascade.** A target cleared cleanly (precondition false, no alternative, no value) reads as plain EMPTY in its dependents; a read of an unavailable cell **poisons**: the reading instance aborts, produces no value, is marked invalid, and poisons its own dependents. The poison is **read-driven** — `And`/`Or` short-circuit and scans stop early — so an invalid cell that an evaluation never reaches never poisons it. ([§11 §3](09-computations.md#3-two-kinds-of-no-value--the-empty-cascade-vs-the-poison-))

---

## 5. Cross-cutting invariants

These hold across the language; each restates the linked clause, which owns it.

- **Fixed rule polarity.** A rule's condition is its *error* condition; there is no assertion form and no negation flag. ([§1.3 above](#13-a-rule-states-the-error--and-that-polarity-is-fixed-), [data model §3.1](01-data-model.md#31-rules-validation))
- **No generic negation.** Each negative check is a dedicated predicate, and a positive/negative pair is not assumed to be complementary: `NotAllFieldsFilled` includes the all-empty case, and `Valid`/`Invalid` over `Date(...)` have complementary truth but different VALUE/OMISSION projections. ([§1 A.2](02-logic-and-formal-errors.md#a2-there-is-no-not), [§6 §3.6](05-dates-and-time.md#36-valid-and-invalid-over-date))
- **Rule iteration scope comes from condition references, never from placement or the error entity alone.** The error field must be referenced and scope-compatible but does not select a level. A rule with no iteration-bearing reference evaluates at most once, and an error-path level its iteration leaves unbound is addressed at concrete row `1` unless semantic-index reanchoring replaces it; a message's `referenced` pointer for a starred field keeps wildcard `0` at its reopened level, and a starred group operand wildcards every repeatable level at or below its star. Computation targets and operands have their own scope contract. ([§9 §1.1](07-repetition-and-iteration.md#11-iteration-scope), [data model §3.1](01-data-model.md#31-rules-validation), [§11 §5](09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join))
- **Rows are addressed by semantic key, never by position.** There is no positional row read; `CurrentRepetition` yields a bound row coordinate, or `1` for a non-repeatable group, to compare or correlate with, and the semantic index `[Field For key]` is the only row selection. ([§10 §4](08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-))
- **Empty substitutions presuppose content.** Under full validation a rule is evaluated at an instance without content only when its condition can fire on empty (leaf classes composed through `And`/`Or`), a lifting count stands on a comparison's small side, it reads a second root, or it does not iterate the repeatable root holding its error field. Partial validation overrides the gate for relevant instances. ([§2 A.4](03-empty-and-required.md#a4-the-row-gate--where-the-substitutions-stop), [operator reference column B](14-operator-reference.md#content-gate))
- **Formal validity is prior to built-in rule reads.** Author rules never make a field unavailable; only formal findings do, and every built-in consumer of such a cell settles it by its class. A reached `CustomCondition` receives the formal-invalid set instead. ([§12 §1](10-validation-and-polarity.md#1-formal-validation-vs-rule-validation), [§3 B.1](02-logic-and-formal-errors.md#b1-what-a-formal-error-is))
- **Every computation generates an all-alternatives validation rule.** With mutually exclusive guards it checks the result computation selects; with overlapping guards a later holding mismatch can fire even when the stored value equals the first result. ([§11 §6](09-computations.md#6-the-implicit-validation-rule-precisely))
- **Each carrier that compares values has its own value identity.** Comparison is typed — a Number by numeric value (scale-0 `5` equals scale-2 `5.00`), an Enumeration by stored token, a date chronologically — while uniqueness, distinct counts and join keys each name their own identity, some of them exact stored text. ([§5 §5](04-numbers-and-decimals.md#5-internal-precision--the-constants-that-must-match-exactly), [§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-), [§8 B.1](06-strings-and-enumerations.md#b1-comparison-is-by-stored-value-and-direct-field-comparability-depends-on-effective-display-remapping), [§9 §3.6](07-repetition-and-iteration.md#36-value-identity))

---

## 6. Implementation orientation

<a id="6-lean-encoding-orientation"></a>

The chapters imply a phase-aware checked-cell boundary, strong-Kleene truth, a verdict that retains message polarity, explicit repetition environments, and separate validation and computation outcomes. The project's Lean representation, dependency spine, encoding traps and proof/evidence gate live in [`docs/LEAN-ENCODING-GUIDE.md`](../docs/LEAN-ENCODING-GUIDE.md); this section is only the bridge to that non-normative guide.

---

## 7. Glossary

The recurring vocabulary, each term defined by the linked clause.

| Term | Meaning | Defined in |
|---|---|---|
| **cell** | one field's value, empty or invalid state at one repetition context | [data model §2](01-data-model.md#2-document--an-instance-of-the-tree) |
| **row** | one instantiated repetition of a repeatable group | [data model §1](01-data-model.md#1-model--a-typed-tree) |
| **(index) column** | a field's cells across the rows of its group, the unit uniqueness and starred aggregates scan | [§9](07-repetition-and-iteration.md) |
| **repetition context** | the mapping from each enclosing repeatable group to a row that addresses a cell | [data model §2.1](01-data-model.md#21-repetition-contexts-the-iteration-environment) |
| **cell observation** | what a phase reads from a cell: empty, a value, validation UNKNOWN or computation poison | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty), [§3 B.6](02-logic-and-formal-errors.md#b6-validation-excludes-computation-poisons) |
| **not-check-relevant** | the third cell state: the cell carries a formal finding from a producer of §3 B.3, whether or not it holds a value; built-in validation reads see UNKNOWN, computation normally poison, the required-empty finding excepted. Non-relevance under partial validation is not this state | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) |
| **formal error** | a violation of a field's data-type configuration, or another formal finding (required-and-empty, duplicate index, over-repetition, custom-validator rejection); it carries no rule-authored message and blocks built-in rule consumers | [§3 B.1](02-logic-and-formal-errors.md#b1-what-a-formal-error-is), [§3 B.3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state) |
| **3VL / Kleene** | three-valued logic (TRUE / FALSE / UNKNOWN); `And` and `Or` follow the strong-Kleene tables and introduce no third value of their own | [§1 A.1](02-logic-and-formal-errors.md#a1-connectives-and-mandatory-parentheses), [§3 B.5](02-logic-and-formal-errors.md#b5-the-strong-kleene-tables-the-exact-algebra) |
| **suppression** | a formal error on a built-in operand makes that operand UNKNOWN, and `And`/`Or` decide how far it reaches (branch-scoped) | [§3 B.4](02-logic-and-formal-errors.md#b4-suppression-is-branch-scoped-and-reaches-presence-checks) |
| **empty read / not-given** | how an operand reads an empty cell: its kind's default (Number the fillable `0`, Confirm `False`, other primitive kinds not evaluated) or its operator's own class | [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default), [§2 A.2](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default) |
| **row gate** (content gate) | the full-validation rule that a rule is evaluated at an instance without content only under the conditions of §2 A.4 | [§2 A.4](03-empty-and-required.md#a4-the-row-gate--where-the-substitutions-stop) |
| **polarity: VALUE vs OMISSION** | a fired message's type: OMISSION when some fill could clear the firing, VALUE when none can | [§12 §3](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-) |
| **directional fillability** | whether filling something currently empty could still make an operand grow or shrink; the basis of polarity | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) |
| **poison** | in computation, a read of an unavailable cell aborts the computing instance and marks it invalid, cascading to its dependents; read-driven, hence order-dependent | [§11 §3.2](09-computations.md#32-an-invalidity-clear-poisons) |
| **cascade (empty vs poison)** | a cleanly cleared target reads as EMPTY in its dependents; an invalidity poisons them | [§11 §3](09-computations.md#3-two-kinds-of-no-value--the-empty-cascade-vs-the-poison-) |
| **stored form** | the string a computed value is stored as, in the target's declared shape; what downstream reads see | [§11 §4](09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape) |
| **compute outcome / change action** | each computed instance has one of five outcomes; the change actions VALUE, CLEARED and ERRORED are projected from them against the computation source | [§11 §2](09-computations.md#2-separate-operations-and-the-three-outcomes), [data model §4.3](01-data-model.md#43-the-compute--apply--validate-flow) |
| **iteration scope** | the repeatable path a rule's iteration-bearing condition references contribute; it decides how often and at which rows the rule evaluates | [§9 §1.1](07-repetition-and-iteration.md#11-iteration-scope) |
| **parallel iteration** | the outer join of two repeatable groups, neither nested in the other, keyed by an index field each declares under the same name | [§9 §2](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key) |
| **`Having` / `$`** | `Having` filters a starred field operand to the rows where its condition holds before an aggregate or quantifier consumes it; `$`, written only inside a filter condition, reads the captured outer repetition, making the filter a correlated subquery | [§9 §3](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation), [§10 §3.6](08-paths-and-references.md#36-the--marker) |
| **semantic index** | `[Field For key]`, the only row selection: a row is addressed by its index-field value, never by ordinal position | [§10 §4](08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-) |
| **phantom row** | under partial validation, a row the relevant set names that does not physically exist but is still evaluated; full validation's visits to declared slots holding no stored row are a separate notion | [data model §2.2](01-data-model.md#22-over-repetition-and-phantom-rows) |
| **relevant set** | the cells `validatePart` is asked to check, given as wildcardable patterns; global-flagged fields are added at all repetitions | [§12 §5.1](10-validation-and-polarity.md#51-the-relevant-set) |
| **scale** | a Number field's declared maximum count of fractional digits, a static property of the field that gates `==`/`!=` | [§5 §1](04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time) |
| **Base Year** | a model-level reference year that omitted-year date literals and date fragments complete against | [data model §1.1](01-data-model.md#11-the-two-special-model-level-configurations) |

---

## 8. The document set

Read the chapters in file order for a first pass, using the table in §3; for a targeted question, find the owning clause through §3 or the glossary and read it there. The operator reference answers per-operator questions once its column's defining clause is understood. Project-specific implementation guidance starts in [`docs/LEAN-ENCODING-GUIDE.md`](../docs/LEAN-ENCODING-GUIDE.md).

---

## 9. Drilling into the authoritative sources

[`docs/SOURCES.md`](../docs/SOURCES.md) owns the authority order, the engine-layer routing rule, Kernel entry points, the per-clause drill table and reviewed a12-dmkits provenance; a chapter section that cites sources ends with one `Sources:` line naming the records behind it. This map does not duplicate either.

Sources: a12-dmkits [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md), the peer's per-clause prose, test and corpus index.

---

## 10. Lean coverage lives in the project documentation

The specification does not record Lean implementation, proof, conformance or evidence status. [`docs/IMPLEMENTATION-MAP.md`](../docs/IMPLEMENTATION-MAP.md) owns clause-level executable and proof coverage, [`docs/EVIDENCE.md`](../docs/EVIDENCE.md) retained external observations, and [`docs/LEAN-FORMALIZATION.md`](../docs/LEAN-FORMALIZATION.md) the proof and trust contract.
