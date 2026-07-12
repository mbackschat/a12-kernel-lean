# A12 Kernel — validation-language semantics, mapped for a Lean reimplementation

This is the entry point to a standalone description of how the **A12 kernel's validation/computation language evaluates**, written so a future reader with no access to the source project can (a) understand the semantics precisely and (b) reimplement them — the working assumption is **Lean 4** as the eventual target, but the content is a language-neutral specification with Lean-flavoured modelling notes layered on top.

> **How to read this set.** This file is the *map*: the mental model, the taxonomy, the difficulty ranking, the cross-cutting invariants, the recommended Lean core types, and a glossary. Each numbered companion file deep-dives one area. You do **not** need any other repository or document — everything needed to reason about (and reimplement) the semantics is inside this folder. Where a companion file exists it is linked; where it is still to be written the map entry already states the essential behaviour.

---

## 0. Provenance, scope, and the license posture

- **What is being described.** The evaluation semantics of the A12 kernel's *validation language* (also called the condition language or DSL) as observed in kernel version **30.8.1**. "Evaluation semantics" means: given a document model and a document instance, *when does a rule fire, what message type does it carry, and what value does a computation produce* — beyond what the surface syntax shows.
- **What is out of scope.** The kernel's Java/host API surface, its code-generation targets, model include/expansion mechanics, the editor UI, and persistence. These are touched only where they change evaluation (mainly full-vs-partial validation, and the compute→apply→validate flow).
- **Clean-room posture (important if you reimplement).** Everything here describes *observable behaviour* — facts about what the engine does for given inputs, established by experiment and by reading the specification, not by transcribing engine source. Behaviour and ideas are free to reimplement; a line-by-line port of the original engine's source expression would be a derivative work. So: **read this to learn the exact behaviour, then write original code and lock it against the behaviour with tests.** Copy the *mechanism*, never the *expression*.
- **Confidence markers.** Claims are of two kinds. Most are settled behaviour verified against kernel 30.8.1 (by differential testing against the real engine and by source reading); a few carry the caveat *"observed, not exhaustively pinned"* inline. Where a behaviour was surprising enough that a naive reimplementation is likely to get it wrong, it is flagged **⚠ trap**.

---

## 1. The kernel in one page

### 1.1 Models, documents, groups, fields

A **document model** (DM) declares a *tree*:

- **Groups** are the internal nodes. A group is either **non-repeatable** (occurs at most once) or **repeatable** (an array: zero or more **rows**, up to a declared `repeatability` bound). The root of a model is a group.
- **Fields** are the leaves. Each field has a **type** (String, Number, Boolean, Confirm, Enumeration, Date, DateTime, Time, DateFragment, DateRange, Custom, …) and per-type configuration (a Number's *scale* = max fractional digits; a String's pattern/length; an Enumeration's value set; a Date's format/precision).

A **document** is an *instance* of a model: a tree in which repeatable groups have been instantiated into some number of rows, and fields hold values (or are empty). The pairing "a specific field at a specific repetition" is the atomic addressable unit; this document set calls it a **cell** (the kernel has no single word for it — see the glossary).

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

The kernel does two things over (model, document):

1. **Validation** — run the model's **rules**; produce a set of structured **messages** (each with a severity, a message *type*, an error field it attaches to, and interpolated text).
2. **Computation** — run the model's **computation rules**; produce new **values** for computed fields (write-back).

Both are expressed in the **same** language — the same operators, the same treatment of empty and invalid values apply to a rule condition and to a computation's operation.

### 1.3 A rule states the *error* — and that polarity is fixed ⚠

A rule has exactly **one** condition slot, and its meaning is fixed: **the condition is TRUE precisely when the data is invalid.** There is no "assert this holds" form.

```
FieldNotFilled(Customer)          -- the rule "Customer is missing" (fires when empty)
[Quantity] < 1                    -- the rule "Quantity below 1 is an error"
```

A requirement must therefore be authored as *its violation*. A positively-phrased "requirement" is structurally legal but encodes the opposite rule — a mistake the engine cannot catch. **A Lean model should bake this in**: a `Rule` carries an `errorCondition`, and there is no polarity flag to get wrong.

### 1.4 Severity is metadata; message *type* is computed

A rule carries a severity — **ERROR / WARNING / INFO** — that is pure message metadata: the condition fires identically whatever the severity, and only **ERROR** messages make the document invalid (a warning or info surfaces text without failing validation).

Independently, every fired message carries a **message type**, **VALUE** or **OMISSION**, computed from the data (not fixed per operator): OMISSION means "filling some currently-empty field could satisfy the rule" (*something is missing*); VALUE means "no fill can — only changing an entered value helps" (*what you entered is wrong*). This is a whole second semantic dimension, orthogonal to truth; it has its own algebra and is one of the genuinely hard parts of the language ([§12](#3-the-taxonomy), file [`10-validation-and-polarity.md`](10-validation-and-polarity.md)).

### 1.5 The call surface and the form-engine flow

- **`validateFull(document)`** validates the whole document.
- **`validatePart(document, relevantSet)`** validates a *relevant subset* (e.g. one wizard page). It guarantees only one direction — it never reports an error that could only be fixed outside the subset — and may skip some checks for performance. A document that passes a partial validation can still fail a full one.
- **Validation never computes first.** The typical form-engine flow is composed by the consumer: **compute → apply → validate**, where *apply* writes back only clean computed values and empties errored/cleared cells. A Lean model should keep `compute` and `validate` as **separate total functions** over the document and compose them explicitly.

---

## 2. Field types at a glance

Which operators are legal on a field, and how a missing/mismatched value behaves, is decided by the field's **type**. Hold this table in mind; the per-topic files expand each row.

| Field type | Key config | An **empty** value, in a comparison, behaves as… | Notes that bite |
|---|---|---|---|
| **Number** | *scale* = max fractional digits; min/max; signed? | substituted **`0`** | scale **gates `==`/`!=`** at parse time; ordering is scale-exempt; empty is *ignored* by min/max aggregates |
| **Boolean** | true / false / unset | **not evaluated** (three states) | `[F] == True` ≠ `FieldFilled(F)`; an unset boolean is neither `== True` nor `== False` |
| **Confirm** | true / unset (a checkbox) | treated as **`False`** | differs from Boolean; a stored `false` is itself a formal error |
| **String** | pattern; min/max length | **not evaluated** | length counts Unicode combining sequences as several chars; there is no empty string (`== ""` never holds) |
| **Enumeration** | value set; optional localized texts; categories | **not evaluated** | compared by stored *value* not display text; `->` reads a value's category |
| **Date** | format; precision (full/day/month/year-optional) | **not evaluated** | constants are `DD.MM.YYYY`; a string literal matching that format *is* a date |
| **DateTime** (extends Date) | — | not evaluated | the operand for `Now`, sub-day differences/additions |
| **Time** (extends Date) | — | not evaluated | operand for `HoursFromTime`, … |
| **DateFragment** | fragment format (`MM`, `yyyy`, `yyyy-MM`, `MM-dd`) | not evaluated | a deliberately imprecise date; completes to a concrete date at evaluation |
| **DateRange** | endpoint format; separator `/` | not evaluated | only `==`/`!=` (no ordering); cannot nest in another construct; overlap is inclusive |
| **Custom** | name; min/max length | as a **string** | whole formal check delegated to a registered validator; `Valid(F,"Name")` runs it |
| **TypeDefinition** | references a reusable type by id | *delegates* | legality is the underlying type's, known only after model expansion |

**⚠ The single most common real-world bug** is getting the *empty* column wrong: `[Amount] < 100` **fires** on an empty amount (because empty → `0 < 100`), while `[Date] > "01.01.2022"` **stays quiet** on an empty date (not evaluated). Same shape, opposite behaviour, decided silently by type. File [`03-empty-and-required.md`](03-empty-and-required.md) is entirely about this.

---

## 3. The taxonomy

Fourteen numbered areas cover the language. This is the same `§n` numbering the deep-dive files use. **Difficulty** rates how hard the area is to reimplement faithfully (★ easy … ★★★★★ this is where reimplementations fail).

| § | Area | In one line | Difficulty | Deep-dive file |
|---|---|---|---|---|
| §1 | Truth values & logical evaluation | Two-valued connectives over data that can be "unknown"; no generic `Not`; explicit parens required | ★★★☆☆ | [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md) |
| §2 | Non-specified (empty) values | Per-kind treatment of empty operands; empty-as-`0` vs not-evaluated; aggregate identities; the row gate | ★★★★☆ | [`03-empty-and-required.md`](03-empty-and-required.md) |
| §3 | Formal errors & the "unknown" state | The **third** cell state (filled-but-invalid); makes operands UNKNOWN; branch-scoped suppression | ★★★★★ | [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md) |
| §4 | The "required" property | Expands to a generated rule; manifests as a formal error; index-field auto-checks (mandatory + unique) | ★★★☆☆ | [`03-empty-and-required.md`](03-empty-and-required.md) |
| §5 | Numbers & decimals | Static scale gates `==`; three rounding modes; scale-19 rescale; quiet div-by-zero | ★★★★☆ | [`04-numbers-and-decimals.md`](04-numbers-and-decimals.md) |
| §6 | Dates & time | `DD.MM.YYYY`; string/date literal ambiguity; asymmetric add/difference; Gregorian floor; fragments; DST | ★★★★☆ | [`05-dates-and-time.md`](05-dates-and-time.md) |
| §7 | Strings & patterns | Unicode-combining length; anchored portable-subset regex; `+` overload (add vs concat) | ★★☆☆☆ | [`06-strings-and-enumerations.md`](06-strings-and-enumerations.md) |
| §8 | Enumerations | Compare by stored value; texts-bearing comparability; category `->`; value-list quantifiers | ★★★☆☆ | [`06-strings-and-enumerations.md`](06-strings-and-enumerations.md) |
| §9 | Repetition, iteration & cross-array eval | Rules become per-row queries; scope from references; joins by index; `Having`/`$`; star binding | ★★★★★ | [`07-repetition-and-iteration.md`](07-repetition-and-iteration.md) |
| §10 | Paths & references | Absolute/relative/short-name; `..`-plus-`*` needs absolute; semantic index; addressed by key never position | ★★★★☆ | [`08-paths-and-references.md`](08-paths-and-references.md) |
| §11 | Computations | Also a validation rule; three outcomes VALUE/CLEARED/ERRORED; empty-cascade vs order-dependent poison | ★★★★★ | [`09-computations.md`](09-computations.md) |
| §12 | The validation model | Severity metadata; VALUE/OMISSION typing via directional fill; full vs partial validation | ★★★★★ | [`10-validation-and-polarity.md`](10-validation-and-polarity.md) |
| §13 | Error-message interpolation | `$Field$` / `$Field.value$`; label provider; empty → `0`/empty string | ★★☆☆☆ | [`11-messages-and-custom.md`](11-messages-and-custom.md) |
| §14 | CustomCondition — the escape hatch | Delegates the decision to host code; barred in compute + filters | ★★☆☆☆ | [`11-messages-and-custom.md`](11-messages-and-custom.md) |
| — | Concrete syntax (lexing & grammar) | Keyword catalog (EN/DE), comments, `@`-directives, literals, path grammar, an EBNF sketch | ★★★☆☆ | [`12-concrete-syntax.md`](12-concrete-syntax.md) |
| — | Lean encoding guide | Recommended core types, the encoding traps, a "start here" order, what to property-test | — | [`13-lean-encoding-guide.md`](13-lean-encoding-guide.md) |
| — | Data model & call surface | Documents/models/rows, the compute→apply→validate flow, the iteration environment | ★★☆☆☆ | [`01-data-model.md`](01-data-model.md) |

---

## 4. The five things a naive reimplementation gets wrong

If you internalise nothing else, internalise these. Each is the root of a whole family of bugs, and each is expanded in a deep-dive file.

1. **There are three cell states, not two — empty ≠ invalid.** Besides *empty* and *filled*, a cell can be **not-check-relevant**: present but formally invalid (wrong format, out of range, pattern miss, duplicate index, over-repetition, required-and-empty). This third state answers *every* question with "unknown" and behaves differently from empty in every position — it is counted as neither filled nor empty, it makes aggregates non-evaluable, it suppresses rules, and in computation it *poisons*. A two-state (`Option`) value domain cannot express the language. **Model the value domain with three states from the start.** ([§3](#3-the-taxonomy))

2. **Evaluation is three-valued (Kleene), but only the *data* is three-valued.** Connectives (`And`/`Or`) and predicates are two-valued; the third value ("unknown") enters only when an operand reads an invalid cell, and then ordinary Kleene `And`/`Or` decides how far it reaches — **branch-scoped, not rule-scoped**: `healthy Or [broken] > 0` still fires; `healthy And [broken] > 0` is suppressed. ([§1](#3-the-taxonomy), [§3](#3-the-taxonomy))

3. **"Empty" is per-kind, and the same syntax changes meaning with the operand's type.** An empty **Number** substitutes `0` (so `[n] < 100` fires); an empty **Confirm** is `False`; an empty **String/Date/Boolean/Enum** makes the comparison *not evaluated*. And several operators override their kind's default (string `+` concatenation treats empty as `""`; `Length` treats empty as `0`; the count family never counts an empty; operand-list `Min`/`Max` substitute `0` for numbers but skip empty dates). ([§2](#3-the-taxonomy))

4. **Message polarity (VALUE vs OMISSION) is a second lattice you must compute alongside truth.** It is not a per-operator constant — it is derived from **directional fillability**: each operand tracks "could this still grow / still shrink if something were filled", propagated through arithmetic, functions and aggregates, and the enclosing comparison's direction decides whether a fill could clear the firing. Under `And`, omission wins; under `Or`, value wins. A faithful engine evaluates *two* things per node — a Kleene truth and a polarity. ([§12](#3-the-taxonomy))

5. **Computation's failure propagation is *order-dependent poison*, not a pure cascade.** A cleared-by-precondition field cascades to dependents as plain *empty*; a cleared-by-*invalidity* field **poisons** — reading it throws inside the computing instance, which aborts and marks itself invalid, cascading in turn. The poison is **read-driven**: `And`/`Or` short-circuit and quantifier scans stop early, so an invalid cell that a given evaluation never actually reads never poisons it. Two documents that differ only in evaluation order can differ in output. ([§11](#3-the-taxonomy))

---

## 5. Cross-cutting invariants

These hold across the whole language; a reimplementation can assert them as global laws.

- **Fixed rule polarity.** A rule's condition is its *error* condition (true ⇒ invalid). There is no assertion form and no negation flag. ([§1.3](#13-a-rule-states-the-error--and-that-polarity-is-fixed-))
- **No generic negation.** The language has no `Not`. Each negative check is a dedicated predicate with its own logic, and positive/negative predicate pairs are **not always complements** (e.g. `NotAllFieldsFilled` includes the all-empty case; `Valid`/`Invalid` are not complements when a part is malformed). ([§1](#3-the-taxonomy))
- **Iteration scope comes from *references*, never placement.** A rule (or computation) iterates over the set of repeatable fields its condition and target reference — not over where its node sits in the model tree. A rule with no repeatable reference evaluates exactly once. ([§9](#3-the-taxonomy), [§11](#3-the-taxonomy))
- **Rows are addressed by semantic key, never by position.** There is no `[Field At n]`, no neighbour offset. `CurrentRepetition` *yields* an index to compare or correlate, never one to select with; the only row-selection form is the semantic index `[Field For key]`. ([§10](#3-the-taxonomy))
- **Empty is not evaluable to a value; invalid is UNKNOWN; only content-bearing instances evaluate.** The empty-as-`0` substitutions presuppose a content-bearing row (the "row gate"); an all-empty instance is evaluated only by conditions that *can* fire on emptiness (the negative-presence family). Partial validation overrides this for relevant instances. ([§2](#3-the-taxonomy), [§12](#3-the-taxonomy))
- **Formal validity is prior to rules.** A formally invalid cell is unknown to *every* rule that reads it; author rules never make a field unevaluable, only formal errors do. ([§3](#3-the-taxonomy))
- **Every computation is also a validation rule.** If a computed field is filled and disagrees with what its computation would produce, that is an error. ([§11](#3-the-taxonomy))
- **Typed equality throughout.** Equality between numbers is by numeric value after rescale (a scale-0 `5` equals a scale-2 `5.00`), enums by stored value, dates chronologically — never by stored string. ([§5](#3-the-taxonomy), [§8](#3-the-taxonomy))

---

## 6. Lean-encoding orientation

The full plan is [`13-lean-encoding-guide.md`](13-lean-encoding-guide.md); this is the orientation so the deep-dive callouts have shared vocabulary. Six core types carry the semantics.

**(a) The three-valued cell state.** Every cell read resolves to one of three states before anything else looks at it:

```lean
inductive CellState where
  | empty                    -- not specified
  | filled (v : Value)       -- a well-formed value of the field's type
  | notCheckRelevant         -- present but formally invalid ("unknown")
```

**(b) Kleene three-valued logic** for truth, with the caveat that the third value arises only from reads, and the connectives are the strong-Kleene tables:

```lean
inductive K where | tru | fls | unknown
def K.and : K → K → K | .fls,_ => .fls | _,.fls => .fls | .tru,.tru => .tru | _,_ => .unknown
def K.or  : K → K → K | .tru,_ => .tru | _,.tru => .tru | .fls,.fls => .fls | _,_ => .unknown
-- (there is no K.not: the language has no negation combinator)
```

**(c) The polarity lattice** — an orthogonal result carried alongside truth for a *firing* message:

```lean
inductive Polarity where | value | omission
-- combine under And: omission wins; under Or: value wins
```

Evaluating a rule against a row therefore yields something like `firedAsValue | firedAsOmission | notFired` — a *three*-way outcome with its own And/Or algebra (see [§12](#3-the-taxonomy)).

**(d) The value domain** must model per-kind values *and* the "not-given / fillable" information polarity needs. A first cut:

```lean
inductive Value where
  | num  (d : Decimal) (scale : Nat)     -- scale is a static field property, not the runtime value
  | str  (s : String)
  | bool (b : Bool)
  | date (d : CalDate)                   -- with precision; unreal dates are a *bottom*, not a value
  | enum (stored : String)               -- compared by stored token, not display text
  -- …
```

**(e) The AST** is a closed hierarchy — the ideal case for a Lean `inductive` + exhaustive pattern-match evaluator. (Concrete shape: [`12-concrete-syntax.md`](12-concrete-syntax.md).)

**(f) The environment / document.** Evaluation happens *at a repetition context* — a binding of each enclosing repeatable level to a row index. Iteration produces a set of such contexts; a path resolves against one. Model this explicitly (an `Env` mapping repeatable levels → row indices) rather than trying to thread positions implicitly — the star-binding and correlation rules ([§9](#3-the-taxonomy), [§10](#3-the-taxonomy)) are *about* how that environment is extended.

> **The one-sentence encoding thesis.** A faithful evaluator is a function `eval : Ast → Env → Document → (K × Polarity)` over a three-state value domain, where `compute` is a *separate* function with an order-dependent poison effect — and the hard parts are (3) the third state, (4) the polarity, and (9)/(11) the environment and the poison.

---

## 7. Glossary

Self-contained definitions of the recurring vocabulary (the deep-dive files assume these).

| Term | Meaning |
|---|---|
| **cell** | one field value at one repetition (a repeated field's value in a specific row). The kernel has no single noun for this; it is this document set's shorthand. |
| **row** | one instantiated repetition of a repeatable group. |
| **(index) column** | a field's values across all rows of its group — the scan unit for uniqueness and starred aggregates. |
| **cell state** | the three-way evaluability of a cell: **empty** · **filled** · **not-check-relevant**. |
| **not-check-relevant** | the third cell state: present but formally invalid; behaves as UNKNOWN everywhere and is counted as *neither* filled nor empty. |
| **formal error** | a violation of a field's *data-type configuration* (type, pattern, scale, range, charset, leading/trailing blanks, required-and-empty, duplicate index, over-repetition). Puts the cell in the not-check-relevant state; uses a fixed, non-authorable message; blocks the field from all rules. |
| **3VL / Kleene** | three-valued logic (TRUE / FALSE / UNKNOWN); the truth model. Only data is three-valued; connectives are two-valued and use the strong-Kleene tables. |
| **suppression** | a formal error on an operand makes that operand UNKNOWN; the ordinary `And`/`Or` algebra decides how far it reaches (**branch-scoped**). |
| **empty-as-0 / NOT-GIVEN** | per-kind treatment of an unspecified operand: a Number reads a fillable `0` in comparisons/aggregates; a String/Date reads NOT-GIVEN (not evaluated); a Confirm reads `False`. |
| **row gate** | the rule that empty-as-`0` substitutions only fire inside a *content-bearing* instance; an all-empty instance is evaluated only by conditions that can fire on emptiness. |
| **polarity: VALUE vs OMISSION** | a fired message's type. VALUE = "what you entered is wrong" (no fill helps); OMISSION = "something is missing" (a fill could clear it). Computed from directional fillability. |
| **directional fillability** | per-operand flags "could this still grow / still shrink if a field were filled", propagated through the expression; the basis for polarity. |
| **poison / poison-on-read** | in *computation*, reading a formally-invalid cell throws inside the computing instance, aborting it and marking it invalid, cascading to dependents. Read-driven, hence **order-dependent**. |
| **cascade (empty vs poison)** | a field cleared by a *precondition* cascades to dependents as plain EMPTY; a field cleared by *invalidity* POISONS them. Which one decides downstream behaviour. |
| **stored form** | the exact string a computed value is stored as (a date in the target's declared format; a number padded to the target's min fractional digits). What downstream reads and formal checks see. |
| **compute outcome** | per computed cell: **VALUE** (a value), **CLEARED** (no value — any stale value wiped), or **ERRORED** (a value the target cannot legally hold, returned but flagged). |
| **iteration scope** | the set of repeatable fields a rule/computation references; determines how many times it evaluates and at which rows. Derived from references, never from node placement. |
| **parallel iteration** | joining two repeatable groups (neither nested in the other) by a shared **index field** — an outer join over index values; an unmatched side reads "not specified". |
| **`Having` / `$`** | `Having` filters a `*`-path to the rows where a condition holds, before an aggregate consumes it; `$` (only inside a filter) pins a reference to the current *outer* repetition, making the filter a correlated subquery. |
| **semantic index** | `[Field For key]` — the only positional-free row lookup; addresses a row by an index-field value, never by ordinal position. |
| **phantom row** | in partial validation, a row in the relevant set that does not physically exist in the document but is still evaluated. |
| **relevant set** | the subset of cells `validatePart` is asked to check; global fields are auto-added. |
| **scale** | a Number field's declared maximum count of fractional digits — a *static* property of the field, checked at parse time; gates `==`/`!=`. |
| **Base Year** | a model-level reference year that omitted-year date literals and date fragments complete against. |

---

## 8. The document set

| File | Covers | Status |
|---|---|---|
| [`SEMANTICS-MAP.md`](SEMANTICS-MAP.md) | this map | ✅ written |
| [`01-data-model.md`](01-data-model.md) | mental model, data model, call surface, iteration environment | ✅ written |
| [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md) | §1 truth/logic + §3 formal errors / the third state | ✅ written |
| [`03-empty-and-required.md`](03-empty-and-required.md) | §2 empty values + §4 the required property | ✅ written |
| [`04-numbers-and-decimals.md`](04-numbers-and-decimals.md) | §5 numbers & decimals | ✅ written |
| [`05-dates-and-time.md`](05-dates-and-time.md) | §6 dates & time | ✅ written |
| [`06-strings-and-enumerations.md`](06-strings-and-enumerations.md) | §7 strings & patterns + §8 enumerations | ✅ written |
| [`07-repetition-and-iteration.md`](07-repetition-and-iteration.md) | §9 repetition, iteration, cross-array evaluation | ✅ written |
| [`08-paths-and-references.md`](08-paths-and-references.md) | §10 paths & references | ✅ written |
| [`09-computations.md`](09-computations.md) | §11 computations | ✅ written |
| [`10-validation-and-polarity.md`](10-validation-and-polarity.md) | §12 the validation model, VALUE/OMISSION | ✅ written |
| [`11-messages-and-custom.md`](11-messages-and-custom.md) | §13 interpolation + §14 CustomCondition | ✅ written |
| [`12-concrete-syntax.md`](12-concrete-syntax.md) | lexing, keyword catalog, directives, grammar sketch | ✅ written |
| [`13-lean-encoding-guide.md`](13-lean-encoding-guide.md) | the consolidated Lean formalization plan | ✅ written |

The status column is updated as files land. Read in file order for a first pass; the map plus any single deep-dive is self-contained for a targeted question.
