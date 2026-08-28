# 01 — The data model and the call surface

*Prerequisite reading for everything else.* This file fixes the vocabulary and the shapes the rest of the set evaluates over: what a model is, what a document is, how repetition works, what "a cell" means precisely, and the two operations (validate, compute) with their call surface. It is deliberately mechanical; the *interesting* semantics start in [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md).

See [`SEMANTICS-MAP.md`](SEMANTICS-MAP.md) for the glossary and the taxonomy; terms like *cell*, *row*, *not-check-relevant* are defined there.

---

## 1. Model = a typed tree

A **document model** is a static declaration — a tree:

- **Groups** are internal nodes. Each group is **non-repeatable** (occurs at most once wherever its parent occurs) or **repeatable** (declares an ordered 1-based row-address range `1 … repeatability`; a valid document may instantiate only a prefix `1 … rowCount`, where `rowCount ≤ repeatability`). The model's root is a single group.
- **Fields** are leaves. Each has a **type** and per-type configuration. (The type table is in [`SEMANTICS-MAP.md §2`](SEMANTICS-MAP.md#2-field-types-at-a-glance); per-type evaluation is in files 04–06.)

A group's direct children form an ordered declaration sequence. Groups nest arbitrarily; a repeatable group may contain repeatable subgroups, giving multi-dimensional arrays. Recursive expansion to descendant fields preserves model declaration order: a child field is visited when reached, while a child group's descendant fields are visited recursively before the next sibling.

A repeatable A12 group may designate at most one direct value-validating child as its **index field**; table-backed Enumeration and no-value-validation profiles are not legal index declarations. Generated validation requires that field when the group row is present and requires its stored value to be unique among sibling rows under the same parent. Every admitted non-Number scalar kind uses exact stored-text identity for that uniqueness relation, while Number uses normalized numeric equality.

An ordinary closed Enumeration may additionally designate one stored token as its **S-value**. This is a model-owned index default, not a document value: the validation call may transiently supply it only under the eligibility rules in [§12](10-validation-and-polarity.md#5-full-vs-partial-validation).

A Custom field names a registered validator and preserves whether its optional length bounds were declared; the exact formal-check contract is in [§7](06-strings-and-enumerations.md#a3-custom-field-type-validation).

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

> **Non-normative implementation note.** A model is naturally a `structure`/`inductive` of group and field declarations. Keep the *static* configuration (a Number's scale, a Date's format, a group's repeatability, whether a field is signed) in the model, **not** in runtime values — several semantics (the scale gate on `==`, number fillability, fragment completion) are decided from the *declared* configuration, sometimes before any value exists. A common early mistake is to attach scale to the runtime decimal; scale is a property of the *field*.

### 1.1 The two special model-level configurations

A handful of model-wide settings change evaluation globally; carry them in the model, not per field:

- **Base Year** — a reference year that omitted-year date literals (`"13.07."`) and date fragments complete against. When it is absent, a consumer that requires concrete year-bearing Dates rejects those constructs; same-profile yearless DateRange equality and inequality remain the measured exception and do not imply an instant. ([§6](05-dates-and-time.md))
- **Time zone** — the DM-JSON key `content.modelConfig.timeZone` (the capitalized `TimeZone` is the *internal* metamodel key code generation copies it into). Absent means `UTC`. An explicit id is model-legal exactly when it is the literal `GMT` or legacy `java.util.TimeZone.getTimeZone(id).getID() != "GMT"`; known IANA ids, `GMT±HH:MM`, `UTC`, `Zulu`, and `Etc/UTC` are legal, while an empty, unknown, or misspelled id that collapses to `GMT` is rejected with `MVK_INVALID_TIME_ZONE`. The zone is applied at **parse time** to every DATE and DATE_TIME through legacy `java.util.TimeZone` plus non-lenient `SimpleDateFormat`, not `java.time`; a plain date is midnight in that zone. ([§6](05-dates-and-time.md))
- **Supported characters** — an optional legal charset. An absent or empty list uses the default Basic Multilingual Plane policy; a list containing an empty entry is malformed. The configured definition is runtime-enforced according to the exact entry and atomic-matching rules in [§7](06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching).
- **`fieldRefByShortNameAllowed`** — enables model-wide unique short-name field references. ([§10](08-paths-and-references.md))

---

## 2. Document = an instance of the tree

A **document** instantiates the model: repeatable groups are expanded into concrete rows, and fields hold **values** or are **empty**. A field is not just "value or empty" — recall the **three cell states** ([§3](02-logic-and-formal-errors.md)):

- **empty** — no evaluation value (whether the field placement is absent or present-empty),
- **filled** — a well-formed value of the field's type,
- **not-check-relevant** — a value is present but formally invalid.

A cell's physical placement and its evaluation state are separate dimensions. At the in-memory evaluation-ingestion boundary, an omitted field cell is **absent**; a present field cell whose stored content is `null` or the empty text `""` is **present-empty**; and a present cell with nonempty text proceeds through parsing and formal checking to become either filled or not-check-relevant. Classifying a placed `""` as empty supplies no semantic String value but does not erase that placement or rewrite the document's stored input. A nonempty value that cannot be converted likewise remains physically present with its exact stored text and becomes not-check-relevant; conversion failure never drops the placement or substitutes absence. Field-level fill predicates, fill quantifiers, and requiredness therefore treat absent and present-empty alike as unfilled, while placement-sensitive read-back and application may distinguish them ([§4.3](#43-the-compute--apply--validate-flow)). Non-repeatable group content follows descendant evaluation values, whereas an explicitly instantiated repeatable row remains structural content even when all its field cells are present-empty ([§9](07-repetition-and-iteration.md#5-groupfilled-and-the-other-repetition-rules)).

**Where a stored Number's scale comes from.** Rules below distinguish decimal values that have the same amount but different stored scale—most visibly the scale-sensitive computation change test in [§11](09-computations.md#33-what-compute-reports). That coefficient-and-scale identity is an input at this boundary, fixed when the host constructs the in-memory document; it is not reconstructed by evaluation. A host that first parses a decimal through binary floating point can therefore change `250.00` into scale-1 `250.0`, or lose digits from a large decimal, and silently change later results. Persistence remains outside this account, but the host must deliver the decimal amount and authored scale intact. The same decimal model has no negative zero, so an ingested `-0.0` has the identity of `0.0`.

A **cell** is *the value (or empty/invalid) of one field at one repetition context*. A non-repeated field has exactly one cell per document; a field inside a repeatable group has one cell per row (and, under nested repetition, one per combination of enclosing row indices).

### 2.1 Repetition contexts (the iteration environment)

Because a field can live under several repeatable ancestors, addressing a cell requires knowing *which row* at each repeatable level. Call that a **repetition context** (the kernel's `Kontext`/`Kontextnummer`): a mapping from each enclosing repeatable group to a row index.

```
LineItem[1]/Discount[2]/Pct         -- the Pct cell in the first LineItem's second Discount row
```

Concrete repetition indices are **1-based**, and an omitted bracket means repetition `1`. The example spells `[1]` for clarity; the canonical exact-pointer string omits it and has no leading slash, so `LineItem/Discount[2]/Pct` addresses the same cell. A leading slash is accepted as redundant input. A zero-part exact pointer is legal and denotes the document root; its canonical string is empty, while the kernel's diagnostic display names it `(empty DocumentPointer)`.

The repetition slot is an A12-owned vocabulary rather than one unrestricted integer. Its complete `IIdentifier` domain is: `>= 1` for a concrete repetition (`1` at a non-repeatable level), `0` = `ALL_INDICES`, `-1` = `ITERATION`, `-2` = `USB_NOT_SPECIFIED`, `-4` = `SEMANTIC_INDEX`, `-5` = `UNKNOWN`, `-6` = `PARALLEL_ITERATION`, and `-7` = the `RepetitionNotUnique` replacement marker. `0` and the negative values do not have one meaning at every API boundary:

| owner | admitted repetition slot | meaning of `0` |
|---|---|---|
| exact `DocumentPointer` | every part is `>= 1`, except that the last part may be `0` | the last-part `RepetitionsV2` slot, not a wildcard |
| `DocumentMultiPointer` | `>= 0` at every part | all repetitions at that level |
| `IIdentifier` used for relevant sets and meta pointers | the complete vocabulary above | `ALL_INDICES`, the authored asterisk |
| message `PartiallyKnownDocumentMultiPointer` | `>= 1`, `0`, or `UNKNOWN` (`-5`) at every level | all repetitions at that level |

The negative `IIdentifier` values are principally kernel-produced planning or result markers, not caller-authored row coordinates. Of them, `UNKNOWN` is the observable message coordinate for a semantic-index no-match or an unmatched parallel-iteration side; `SEMANTIC_INDEX`, `PARALLEL_ITERATION`, and the `RepetitionNotUnique` marker remain plan-internal. An implementation must not put the whole vocabulary into the exact-pointer type.

The exact pointer's **value** and **string codec** also have different name domains. A `PathPart` requires only a nonempty name and a nonnegative index; names such as `a/b`, `Order$`, `Order Item`, and `Order[2]` are legal part values. The part-list `DocumentPointer` factory adds the exact-pointer position rule but no string grammar. Only the string entry point applies its per-part `([\w_-]+)(\[(\d+)?\])?` grammar, because a written pointer must parse back to the same value. Consequently `fullName()` is not the canonical pointer codec: it joins part names with leading slashes, omits indices, and returns `""` at the exact root, while the canonical exact-pointer string is slashless and carries every non-`1` index. Hoisting the codec grammar onto value construction would reject legal A12 values on the read path.

Every runtime message address uses the distinct `PartiallyKnownDocumentMultiPointer`. Its state is a name string plus a repetition-index list, not exact `PathPart` values; it may carry a wildcard or `UNKNOWN` at any level and therefore converts only partially to exact or wildcard pointers. Conversion to an exact `DocumentPointer` succeeds only when every coordinate before the last is concrete and positive, the last is nonnegative, the name/index arity matches, and every name is nonempty. Conversion to `DocumentMultiPointer` succeeds when every coordinate is nonnegative; any `UNKNOWN` prevents it. A wildcard above the last level, `UNKNOWN`, or a name that exact `PathPart` cannot represent yields no exact pointer in production. The zero-part message root is constructible and has `fullName() = "/"`, but its exact conversion raises rather than returning the exact root. The raw message factory does not enforce name/index arity, so a mismatched value can exist even though it has no well-formed exact counterpart. The message-pointer type has no A12 textual parser or renderer of its own; its `fullName()` and repetition list are accessors, not a serialization contract.

This is the single most important runtime structure to model well, because *iteration is the act of producing these contexts* and *path resolution is the act of reading a cell relative to one* ([§9](07-repetition-and-iteration.md), [§10](08-paths-and-references.md)).

> **Non-normative implementation note.** Represent a repetition context explicitly, e.g. `Env := List (RepeatableLevel × RowIndex)` (an association from each enclosing repeatable group to its chosen row), and make `eval` take it as a parameter: `eval : Ast → Env → Document → …`. Iteration extends `Env`; a bare relative path reads against the current `Env`; a `*` in a path *re-opens* iteration at that level (binding all rows); `$` correlates back to the outer `Env`. Trying to smuggle positions through implicit indices is the classic way the star-binding rules ([§9](07-repetition-and-iteration.md)) come out wrong.

### 2.2 Over-repetition and phantom rows

Two edge shapes matter:

- An instantiated row **beyond** the group's declared `repeatability` is itself a formal error on that row (`zuGrosseZeile` / `zuGrosseKontextnummer`, a VALUE error). This address-formal gate runs before scalar conversion, suppresses that row's ordinary checks, and leaves the immutable physical row instantiated. ([§3](02-logic-and-formal-errors.md), [§9](07-repetition-and-iteration.md))
- Under **partial** validation only, the relevant set can name a row that does **not** physically exist — a **phantom row** — and it is still evaluated. Full validation never does this. ([§12](10-validation-and-polarity.md))

---

## 3. Rules and computations

A model carries two families of behaviour, both written in the one shared language ([`12-concrete-syntax.md`](12-concrete-syntax.md)).

### 3.1 Rules (validation)

A **rule** has:

- an **error condition** — the single condition slot; **TRUE means the data is invalid** (fixed polarity — there is no assertion form; [`SEMANTICS-MAP §1.3`](SEMANTICS-MAP.md#13-a-rule-states-the-error--and-that-polarity-is-fixed-));
- an **error field** — where a fired message attaches. The error field must be *referenced* by the condition (directly, or indirectly via an enclosing `GroupFilled`), or the model is rejected; and it must share the condition's iteration scope ([§9](07-repetition-and-iteration.md));
- **message metadata** — severity (ERROR/WARNING/INFO) and authored error text (with interpolation, [§13](11-messages-and-custom.md));
- a **name**, which may not begin with the engine-reserved prefix `VK_`. The check is case-**insensitive**, so `VK_x`, `Vk_x`, and `vk_x` are all rejected with `MVK_RULE_NAME_INVALID`; an implementation that compares the prefix case-sensitively admits models the kernel refuses.

Firing a rule against a repetition context yields either *no message* or a **message** carrying: the error field's `PartiallyKnownDocumentMultiPointer`, the severity, the computed **message type** (VALUE/OMISSION, [§12](10-validation-and-polarity.md)), the interpolated text, and two structured sets of the same message-pointer type. `referenced` reports the condition operands associated with the firing; for an OMISSION, `fillToFix` reports the kernel's omission-responsibility projection, which need not be a minimal set of empty cells whose literal filling alone repairs the rule, while a VALUE message has no fill-to-fix pointers. An operator may define a more specific projection, such as the complete duplicate-peer expansion of [`RepetitionNotUnique`](07-repetition-and-iteration.md#6-repetitionnotunique-precisely); these channels are sets, so no pointer order is specified. A partially known message address is not an exact pointer with a wider integer slot: wildcard/`UNKNOWN` coordinates and partial exact conversion are part of its type.

Ordinary `referenced` pointers are a **structural projection of the checked condition, not a trace of the values read during evaluation.** Consequently a later `FirstFilledValue` fallback stays referenced even when an earlier operand determined the value. A starred *field* retains wildcard `0` at its reopened group context. A *group* operand of either repetition shape expands recursively to its descendant field pointers rather than yielding a group pointer, and **one depth rule gives both their coordinates**: a repeatable level *above* the operand stays concrete at the firing row, and every repeatable level *at or below* it is wildcarded. For a starred group that boundary is its own star, and every reopened group-context part beneath it is wildcarded — **including a non-repeatable descendant group context**. For an unstarred group the boundary is the operand's own group, which the wildcard gate keeps non-repeatable, so the wildcarding begins at the first repeatable level inside the subtree: `/Shipment/Carrier` reaches `/Shipment[1]/Carrier[1]/Handoffs[0]/Site` beside `/Shipment[1]/Carrier[1]/Name`. The two forms therefore differ in **where** that boundary falls, not in whether one wildcards at all, and the expansion's wildcarded address is a different address of the same firing from the message's own anchor, which stays concrete throughout ([§9](07-repetition-and-iteration.md)). The at-or-below half is measured on both forms; no observation places a repeatable level above a group operand, so the concrete half is stated from the rule rather than from a witness. The relation is identical in the single-operand presence, entity-list quantifier, and numeric filled-count positions, and it is what lets an error field inside the operand group satisfy the reference gate indirectly in all three. `Having` field operands and the selected starred value field are included; an unmarked candidate reference is wildcarded, while a `$` reference resolves at its concrete captured outer row; `CurrentRepetition` contributes no field pointer. Membership is set-valued, so no pointer order is specified.

> **Non-normative implementation note.** A faithful `Rule` is roughly `structure Rule where errorCond : Ast; errorField : Path; severity : Severity; text : Template`. There is deliberately no `polarity` or `assert` field — those are *derived* (polarity from the data; the error semantics from "condition true ⇒ invalid").

### 3.2 Computations

A **computation rule** writes a value into a **computed field**. It has:

- a **target** (the computed field),
- an optional **common precondition**, then one or more **alternatives**. Each alternative contains its precondition, its operation, and an optional fixed `toleranceRangeOp`. The tolerance metadata does not affect first-match selection or operation evaluation; it changes only that alternative's implicit generated mismatch from strict `!=` to the named fixed tolerance-band predicate ([the precise generated-rule account](09-computations.md#6-the-implicit-validation-rule-precisely)). Alternatives are tried top-to-bottom: clean false/unknown falls through, a poisoned read aborts, and the **first** holding precondition selects its operation and ends the scan even if that operation later produces no value. No match ⇒ the target is **CLEARED**.

Three cross-cutting facts (detailed in [§11](09-computations.md)):

1. **Every computation also generates a validation rule** with one guarded mismatch clause per alternative. With mutually exclusive guards this checks the selected computed result; with overlapping guards a later holding mismatch can fire even though computation itself selected the first operation.
2. The computed field's declared **scale is admitted by the same predicate as `==`/`!=`**: an equal derived scale always passes, a smaller derived scale passes only while the whole operation retains multiplicative-constant capability, and a larger or unknown derived scale is rejected absent suppression (wrap in a rounding construct to force a scale). Plain equality is the special case that holds once any non-capable field reference enters the operation.
3. The computed field may appear **neither** in a precondition **nor** in an operation (guarding via its *containing group* is allowed).

---

## 4. The call surface

### 4.1 `validateFull`

`validateFull(document)` evaluates every rule (authored and auto-generated) over the whole document and returns the full message set. `noErrorOccurred()` on the result considers **only ERROR-severity** messages — warnings and infos never make the document invalid.

### 4.2 `validatePart`

`validatePart(document, relevantSet)` evaluates only the rules whose **error-field instance is in the relevant set**, treating references outside the set as three-valued UNKNOWN. Its guarantee is **one-directional**: it never reports an error fixable only outside the subset, but it does *not* promise a complete check of the relevant fields (some checks may be skipped for performance, and which is an implementation detail). Consequences worth pinning ([§12](10-validation-and-polarity.md)):

- Global-flagged fields are auto-added to the relevant set at all repetitions.
- A relevant instance is *always* evaluated (overriding the content-gate of [§2](03-empty-and-required.md)), even if empty or phantom.
- Uniqueness checks need the duplicate **partner** in the relevant set too. For a composite `RepetitionNotUnique` key, every key component of every participating row must be relevant; a cluster is built only from rows whose complete keys are relevant ([§9](07-repetition-and-iteration.md#6-repetitionnotunique-precisely)).

### 4.3 The compute → apply → validate flow

Validation and computation are **separate operations**; `validateFull` does **not** compute first. The consumer (a form engine) composes the loop:

```
compute(source, context)  →  a rich result with Kernel-compatible projections
apply(result, destination) → an updated destination under placement guards
validate(updated, context) → messages over the updated document
```

The V2 result preserves five observables rather than only a change delta: all successful non-clearing computed instances, including successes unchanged from the computation source; the source-relative changed subset of those successes; erroneous computed instances; cleared instances that were filled in the source; and formal operand errors collected eagerly as a separate channel. `noErrorOccurred` is true exactly when both the erroneous-instance and formal-operand-error channels are empty. Formal operand collection is not dependency evaluation: later skipping or poison remains read- and schedule-sensitive even though the formal errors were already inventoried. Public computed-instance collections are compared extensionally by pointer and payload; their iteration order is not an execution-schedule contract without separate evidence.

The **VALUE / CLEARED / ERRORED** vocabulary describes the source-relative change/application actions, not the complete result. VALUE actions are the changed successful subset. CLEARED contains source-filled instances that were explicitly cleared or were not computed because no precondition applied, an error cascaded, or operands had formal errors; an erroneous computed instance reports through ERRORED instead of CLEARED. A caller may apply the stable result to a model-compatible destination other than the computation source. Application uses the classifications already fixed relative to the source—it does not recompute change equality against the destination—and successful unchanged instances are not writes merely because they appear in the broader successful collection.

For each retained action, a **VALUE** writes its exact value and creates the cell plus its directly addressed missing ancestor rows. A **CLEARED** action likewise places a present-empty cell and directly addressed missing ancestors even when that target was absent in the destination; it is a source-classified action, not a destination-relative “clear only if present” request. An **ERRORED** action empties the target only when the target cell already exists, so an absent target remains absent rather than being created as present-empty. If the computation source target was absent and no value was produced, no CLEARED action is minted at all, so applying the result changes nothing at that address. Untouched cells preserve their placement and raw stored text, including a stored CRLF pair; evaluation-side normalization never rewrites the document. Read-back therefore distinguishes **absent**, **present-empty**, and **present-value**.

a12-dmkits' dual-strategy [`AppliedCellStateDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/AppliedCellStateDiffTest.kt) (IF126) locks the same-document target-cell cases, where a CLEARED action can exist only for a source-present target. At revision `c876c207bc092912ac5a35bff0db7298b63f92b0`, [`SeparateDestinationClearDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SeparateDestinationClearDiffTest.kt) runs the retained-result CLEARED/no-action/ERRORED/changed-VALUE/filled-target discriminator through dynamic Groovy, generated Java, and the standalone interpreter route. Multiplatform [`RetainedComputationResultTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/retained/RetainedComputationResultTest.kt) maintains the public source-relative contract on JVM and Node, including missing-row creation, no destination-time recomputation, immutability, same-document composition, and refusal across different prepared-model owners. `PublicInterpreterApiTest` locks Number coefficient-plus-scale source identity, including negative scale. At reviewed revision `38aeb23b5849b831f8ae6ee09579367e28ce982b`, `SourceIdentityIngressRouteDiffTest` separates V1 String ingress from typed V2 ingress across String and seven non-String kinds, while `ComputedTimeTargetDiffTest` and `RepeatableTimeConstructionChangedDiffTest` lock source-identical Time reapplication as unchanged on scalar and repeatable targets. The interpreter's `ComputedTimeTargetTest` retains report-all constructed and extracted values, and `RetainedComputationFixtureGuardTest` keeps the shared model authored through modelkit/a12-dmkits rather than a private interpreter fixture.

For one repeatable level, application of a Number or String VALUE or CLEARED action at row coordinate `k` materializes the complete predecessor prefix `1…k` in numeric address order. The predecessor rows are empty unless they already existed, in which case their cells and coordinates are preserved. Actions keep their own coordinates even though retained application processes CLEARED before changed VALUE: placing row 3 before row 1 yields the same three-row topology as the reverse action classes, rather than appending rows in encounter order. An ERRORED action validates its address and empties an existing target but does not materialize an absent row. For exactly two finite direct repeatable Number or String levels, an action at outer coordinate `i` and inner coordinate `j` materializes the complete outer prefix `1…i` and the complete inner prefix `1…j` only beneath outer row `i`; synthetic outer predecessors gain no inner rows. Distinct actions retain their exact nested coordinates, existing destination cells survive, and an ERRORED action against an absent nested target creates no outer or inner row. A later validation over the returned applied document, without another computation, enumerates that topology and observes placed values at their exact rows. In the measured one-level matrices, `Amount > 0` and `Length(Label) > 0` each fire at rows 1 and 3 and not at the empty materialized row 2, while the two-level Number and String matrices fire only at outer/inner coordinates `[1,2]` and `[3,4]`. This is exact for direct finite one- and two-level Number and String targets. Number and String nesting beyond two levels, other target families, general later-rule execution, transport reconstruction, and pointer rendering remain unmeasured or outside the current result domain. Model compatibility remains a caller precondition in the kernel account. a12-dmkits deliberately enforces the stronger same-`PreparedModel` owner boundary and throws `ModelOwnerMismatchError`; that library safety policy is not a kernel rejection rule.

This matters for reimplementation packaging: model **`compute`** and **`validate`** as two total functions over the document, and make `apply` an explicit, placement-sensitive step. Do not fuse them.

> **Non-normative implementation note.** Signatures to aim for:
> ```lean
> def validateFull : Model → World → Document → List Message
> def validatePart : Model → World → Document → RelevantSet → List Message
> def compute      : Model → World → Document → ComputeResult
> def apply        : ComputeResult → Document → Document
> ```
> `World` in these signatures denotes the complete immutable processing context for the admitted fragment, even when a Lean implementation passes family capabilities separately. It supplies the injected current instant and resolved current date, including a configured test override or the actual date sampled once at the host boundary; the effective error-message locale; total named [custom-condition](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch) and [custom-field-type](06-strings-and-enumerations.md#a3-custom-field-type-validation) semantics; deprecated additional-information input while compatibility with that kernel 30.8.1 surface is claimed; and a versioned zone-rule oracle/profile capable of resolving every time-zone id admitted by the model checker. A deliberately narrower product may reject an unsupported capability or legal zone id before evaluation, but that product boundary does not narrow the canonical kernel legal-input domain.
> Keeping `compute` as *result-producing* rather than *document-mutating* isolates the order-dependent poison ([§11](09-computations.md)) inside one function and lets `apply`/`validate` stay pure. The pure signature expresses the immutable V2 behavioral boundary; deprecated V1 mutation and object aliasing are a separate API-compatibility claim rather than semantics that the result type should encode.

---

## 5. What is *not* modelled here

To keep the reimplementation scope honest, these are explicitly out of the evaluation semantics (they belong to the host platform):

- model **include/expansion** (resolving `TypeDefinition`s and included submodels) — assume an already-expanded model;
- the **editor** and its "required" checkbox UI — you receive the *generated* rule ([§4](03-empty-and-required.md)), not the checkbox;
- **persistence / wire format** of documents — you receive an in-memory tree;
- **code-generation targets** — this set describes the normative Groovy-dynamic behavioral account. Generated static-Java is required co-evidence, and a strategy-split detector **with a bounded reach**: operand lowering is single-sourced by construction — every dialect's operand template interpolates the same codegen backing-bean property, and that property carries no target-language branch — so a split cannot originate there. Its detector power applies to the **rule/computation frame** layer, where Groovy has size-triggered lowering modes that static-Java has at no size: condition-line splitting at fifty or more atomic conditions, calculation closures, and rule-object splitting above ten rules per class. When a legal target-specific split exists, it is recorded rather than flattened into a false uniformity claim. An operand-level split can therefore arise only from host-language semantics, a different runtime path being reached, or the caching and service layer — an exhaustive set for that layer rather than a plausible list. The kernel TypeScript target is never allowed to override the Groovy-dynamic anchor. (The documented DateTime rejection for month/year arithmetic fires later at code generation; mixed DATE/DATETIME ordering is legal.)
