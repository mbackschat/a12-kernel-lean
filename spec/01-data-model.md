# 01 — The data model and the call surface

*Prerequisite reading for everything else.* This file fixes the vocabulary and the shapes the rest of the set evaluates over: what a model is, what a document is, how repetition works, what "a cell" means precisely, and the two operations (validate, compute) with their call surface. It is deliberately mechanical; the *interesting* semantics start in [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md).

See [`SEMANTICS-MAP.md`](SEMANTICS-MAP.md) for the glossary and the taxonomy; terms like *cell*, *row*, *not-check-relevant* are defined there.

---

## 1. Model = a typed tree

A **document model** is a static declaration — a tree:

- **Groups** are internal nodes. Each group is **non-repeatable** (occurs at most once wherever its parent occurs) or **repeatable** (an ordered array of **rows**, `0 … repeatability`). The model's root is a single group.
- **Fields** are leaves. Each has a **type** and per-type configuration. (The type table is in [`SEMANTICS-MAP.md §2`](SEMANTICS-MAP.md#2-field-types-at-a-glance); per-type evaluation is in files 04–06.)

Groups nest arbitrarily; a repeatable group may contain repeatable subgroups, giving multi-dimensional arrays.

```
Order                       group (root, non-repeatable)
├─ OrderDate  : Date
├─ Customer   : String
├─ Totals                   group (non-repeatable)
│  └─ Net     : Number(scale 2, computed)
└─ LineItem*                group (repeatable, repeatability = 99)
   ├─ Sku      : String
   ├─ Quantity : Number(scale 0)
   ├─ UnitPrice: Number(scale 2)
   └─ Discount*             group (repeatable, nested inside each LineItem row)
      └─ Pct   : Number(scale 2)
```

> **Lean modelling note.** A model is naturally a `structure`/`inductive` of group and field declarations. Keep the *static* configuration (a Number's scale, a Date's format, a group's repeatability, whether a field is signed) in the model, **not** in runtime values — several semantics (the scale gate on `==`, number fillability, fragment completion) are decided from the *declared* configuration, sometimes before any value exists. A common early mistake is to attach scale to the runtime decimal; scale is a property of the *field*.

### 1.1 The two special model-level configurations

A handful of model-wide settings change evaluation globally; carry them in the model, not per field:

- **Base Year** — a reference year that omitted-year date literals (`"13.07."`) and date fragments complete against. Absent ⇒ those constructs are rejected. ([§6](05-dates-and-time.md))
- **Time zone** — meta key `TimeZone`, **default `UTC`**, only other supported value `Europe/Berlin`. Applied at parse time; affects sub-day date-time differences across a daylight-saving transition. ([§6](05-dates-and-time.md))
- **Supported characters** — an optional legal charset. If the model declares one it is runtime-enforced; otherwise the legal set is the full Basic Multilingual Plane (`U+0000..U+FFFF`), so any supplementary-plane character is a formal error. ([§3](02-logic-and-formal-errors.md))
- **`fieldRefByShortNameAllowed`** — enables model-wide unique short-name field references. ([§10](08-paths-and-references.md))

---

## 2. Document = an instance of the tree

A **document** instantiates the model: repeatable groups are expanded into concrete rows, and fields hold **values** or are **empty**. A field is not just "value or empty" — recall the **three cell states** ([§3](02-logic-and-formal-errors.md)):

- **empty** — no value specified,
- **filled** — a well-formed value of the field's type,
- **not-check-relevant** — a value is present but formally invalid.

A **cell** is *the value (or empty/invalid) of one field at one repetition context*. A non-repeated field has exactly one cell per document; a field inside a repeatable group has one cell per row (and, under nested repetition, one per combination of enclosing row indices).

### 2.1 Repetition contexts (the iteration environment)

Because a field can live under several repeatable ancestors, addressing a cell requires knowing *which row* at each repeatable level. Call that a **repetition context** (the kernel's `Kontext`/`Kontextnummer`): a mapping from each enclosing repeatable group to a row index.

```
LineItem[1]/Discount[0]/Pct         -- the Pct cell in the first LineItem's zeroth Discount row
```

This is the single most important runtime structure to model well, because *iteration is the act of producing these contexts* and *path resolution is the act of reading a cell relative to one* ([§9](07-repetition-and-iteration.md), [§10](08-paths-and-references.md)).

> **Lean modelling note.** Represent a repetition context explicitly, e.g. `Env := List (RepeatableLevel × RowIndex)` (an association from each enclosing repeatable group to its chosen row), and make `eval` take it as a parameter: `eval : Ast → Env → Document → …`. Iteration extends `Env`; a bare relative path reads against the current `Env`; a `*` in a path *re-opens* iteration at that level (binding all rows); `$` correlates back to the outer `Env`. Trying to smuggle positions through implicit indices is the classic way the star-binding rules ([§9](07-repetition-and-iteration.md)) come out wrong.

### 2.2 Over-repetition and phantom rows

Two edge shapes matter:

- An instantiated row **beyond** the group's declared `repeatability` is itself a formal error on that row (`zuGrosseZeile` / `zuGrosseKontextnummer`, a VALUE error), and that row's ordinary checks are suppressed. ([§9](07-repetition-and-iteration.md))
- Under **partial** validation only, the relevant set can name a row that does **not** physically exist — a **phantom row** — and it is still evaluated. Full validation never does this. ([§12](10-validation-and-polarity.md))

---

## 3. Rules and computations

A model carries two families of behaviour, both written in the one shared language ([`12-concrete-syntax.md`](12-concrete-syntax.md)).

### 3.1 Rules (validation)

A **rule** has:

- an **error condition** — the single condition slot; **TRUE means the data is invalid** (fixed polarity — there is no assertion form; [`SEMANTICS-MAP §1.3`](SEMANTICS-MAP.md#13-a-rule-states-the-error--and-that-polarity-is-fixed-));
- an **error field** — where a fired message attaches. The error field must be *referenced* by the condition (directly, or indirectly via an enclosing `GroupFilled`), or the model is rejected; and it must share the condition's iteration scope ([§9](07-repetition-and-iteration.md));
- **message metadata** — severity (ERROR/WARNING/INFO) and authored error text (with interpolation, [§13](11-messages-and-custom.md)).

Firing a rule against a repetition context yields either *no message* or a **message** carrying: the error field's resolved location, the severity, the computed **message type** (VALUE/OMISSION, [§12](10-validation-and-polarity.md)), and the interpolated text.

> **Lean modelling note.** A faithful `Rule` is roughly `structure Rule where errorCond : Ast; errorField : Path; severity : Severity; text : Template`. There is deliberately no `polarity` or `assert` field — those are *derived* (polarity from the data; the error semantics from "condition true ⇒ invalid").

### 3.2 Computations

A **computation rule** writes a value into a **computed field**. It has:

- a **target** (the computed field),
- an optional **common precondition**, then one or more **alternatives**, each a `(precondition, operation)` pair. Alternatives are tried top-to-bottom; the **first** whose precondition holds supplies the value; none holding ⇒ the target is **CLEARED**.

Three cross-cutting facts (detailed in [§11](09-computations.md)):

1. **Every computation is also a validation rule**: if the computed field is *filled* and its stored value disagrees with what the computation would produce, that is an error.
2. The computed field's declared **scale must equal** the operation's derived scale, or the model is rejected (wrap in a rounding construct to match).
3. The computed field may appear **neither** in a precondition **nor** in an operation (guarding via its *containing group* is allowed).

---

## 4. The call surface

### 4.1 `validateFull`

`validateFull(document)` evaluates every rule (authored and auto-generated) over the whole document and returns the full message set. `noErrorOccurred()` on the result considers **only ERROR-severity** messages — warnings and infos never make the document invalid.

### 4.2 `validatePart`

`validatePart(document, relevantSet)` evaluates only the rules whose **error-field instance is in the relevant set**, treating references outside the set as three-valued UNKNOWN. Its guarantee is **one-directional**: it never reports an error fixable only outside the subset, but it does *not* promise a complete check of the relevant fields (some checks may be skipped for performance, and which is an implementation detail). Consequences worth pinning ([§12](10-validation-and-polarity.md)):

- Global-flagged fields are auto-added to the relevant set at all repetitions.
- A relevant instance is *always* evaluated (overriding the content-gate of [§2](03-empty-and-required.md)), even if empty or phantom.
- Uniqueness checks need the duplicate **partner** in the relevant set too.

### 4.3 The compute → apply → validate flow

Validation and computation are **separate operations**; `validateFull` does **not** compute first. The consumer (a form engine) composes the loop:

```
compute(document)   →  a per-cell outcome map (VALUE / CLEARED / ERRORED)
apply(...)          →  apply each outcome under its placement guard
validate(document)  →  messages over the now-updated document
```

For each target cell, a **VALUE** is written and creates the cell plus any missing ancestor rows when absent. A **CLEARED** outcome is produced only for an input-filled cell and empties that existing cell in place; clearing never removes the cell instance. An **ERRORED** outcome empties the target only when the target cell already exists, so an absent target remains absent rather than being created as present-empty. A computed-nothing outcome changes nothing: a present-empty target remains present-empty and an absent target remains absent. Untouched cells preserve their placement and raw stored text, including a stored CRLF pair; evaluation-side normalization never rewrites the document. Read-back therefore distinguishes **absent**, **present-empty**, and **present-value**.

a12-dmkits' dual-strategy [`AppliedCellStateDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/AppliedCellStateDiffTest.kt) (IF126) locks the target-cell cases inside an existing group—VALUE into absent/stale/equal, CLEARED over filled/empty/absent, ERRORED over filled/empty/absent, computed-nothing, and untouched CRLF storage. VALUE creating missing ancestor rows is separately source-characterized by the kernel's [`GroupDocCommonImpl.updateNested`](../../a12-kernel/kernel-md/kernel-md-document-v2/src/main/java/com/mgmtp/a12/kernel/md/document/internal/service/implV2/immutable/GroupDocCommonImpl.java); that ancestor-creation clause is not independently exercised by this differential.

This matters for reimplementation packaging: model **`compute`** and **`validate`** as two total functions over the document, and make `apply` an explicit, placement-sensitive step. Do not fuse them.

> **Lean modelling note.** Signatures to aim for:
> ```lean
> def validateFull : Model → World → Document → List Message
> def validatePart : Model → World → Document → RelevantSet → List Message
> def compute      : Model → World → Document → List (CellAddr × ComputeOutcome)
> def apply        : Document → List (CellAddr × ComputeOutcome) → Document
> ```
> Keeping `compute` as *outcome-producing* rather than *document-mutating* isolates the order-dependent poison ([§11](09-computations.md)) inside one function and lets `apply`/`validate` stay pure.

---

## 5. What is *not* modelled here

To keep the reimplementation scope honest, these are explicitly out of the evaluation semantics (they belong to the host platform):

- model **include/expansion** (resolving `TypeDefinition`s and included submodels) — assume an already-expanded model;
- the **editor** and its "required" checkbox UI — you receive the *generated* rule ([§4](03-empty-and-required.md)), not the checkbox;
- **persistence / wire format** of documents — you receive an in-memory tree;
- **code-generation targets** — the kernel can generate Groovy/Java/JS evaluators, but the semantics they must all match are exactly what this set describes. (Two documented exceptions where a codegen target's *rejection* fires later than the parse check are noted in [§6](05-dates-and-time.md): `Now` against a plain date, and date arithmetic over a DateTime.)
