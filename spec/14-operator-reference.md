# 14 — Operator reference

The chapters define each mechanism once and name its classes; this chapter says which class every operator belongs to. It holds one row per operator and condition leaf of the validation and computation language, grouped by family, and one column per membership question. A column's classes are defined in the chapter section its vocabulary below links, and that section owns the mechanism, its formulas, its exceptions and its witnesses; a cell here only names the class.

**Membership is per operator.** No class follows from family resemblance: an operator's class is the one its cell names, and an assignment is unmeasured unless its owning clause records a measurement.

---

## Reading the table

Each row names an operator by its English keyword and, where [concrete syntax §5](12-concrete-syntax.md#5-keyword-catalog-english--german-verified-pairs) gives one, its German twin; a symbol is the same in both languages. A row qualified by a carrier, such as `MinValue` over Date/Time/DateTime operands, applies to that carrier only.

| Column | Question |
|---|---|
| **V** | How validation lands a not-check-relevant cell the operator reads ([§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty)) |
| **C** | Whether a computation's read of such a cell poisons ([§3 B.6](02-logic-and-formal-errors.md#b6-validation-excludes-computation-poisons)) |
| **E** | Whether the operator enables message classification ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)) |
| **P** | How a firing over the operator is typed VALUE or OMISSION ([§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)) |
| **F** | What a reached `Having` filter on its operand does to that typing ([§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)) |
| **X** | Which extent predicate partial validation applies to its multi-cell operand ([§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand)) |
| **T** | Which evaluation domain its multi-cell operand walks, and which scan a filter on that operand uses ([§9 §1.3](07-repetition-and-iteration.md#13-evaluation-domains)) |
| **S** | Which slot class each of its argument slots takes, and so how a field is written there ([concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots)) |

A cell holds one of three things:

- **a class name** from the column's vocabulary below;
- **`n/a`** when the column does not apply to the operator, for example a filter effect for an operator whose operand takes no filter, or any column for an operator with no known admitted witness;
- **`not stated`** when the column applies but no chapter decides the class.

`n/a` for a static reason holds only where a chapter states that the operator cannot take the input; each column section names that basis.

A kind-dependent cell names its classes per operand kind, such as "`leaf seed` (Number); `not-given` (other kinds)".

---

## The columns

Each section's table names the column's classes, links the clause that defines each one, and glosses it in a few words; the definition, its exceptions and its measured scope live only in that clause.

### Unavailable read in validation

| Class | Defined in | Meaning |
|---|---|---|
| `scalar read` | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty), [§3 B.4](02-logic-and-formal-errors.md#b4-suppression-is-branch-scoped-and-reaches-presence-checks) | the reading operand is UNKNOWN |
| `presence/fill` | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty), [§1 A.4.3](02-logic-and-formal-errors.md#a43-classifying-a-slot) | neither filled nor empty |
| `all-cells` | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) | UNKNOWN wherever the cell sits |
| `stop-at-first` | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) | UNKNOWN only when reached |
| `skip-invalid` | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty), [§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap) | skipped like an empty cell |
| `group presence` | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty), [§1 A.4.7](02-logic-and-formal-errors.md#a47-group-list-quantifiers), [§1 A.4.8](02-logic-and-formal-errors.md#a48-numberoffilledgroups) | blocks only the negative answer |
| `value-list` | [§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-), [§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-) | per quantifier and side |
| `row drop` | [§9 §6.2](07-repetition-and-iteration.md#62-the-duplicate-relation) | an invalid key drops its row |
| `callback` | [§3 B.1](02-logic-and-formal-errors.md#b1-what-a-formal-error-is) | the callback decides |
| `n/a` | — | the operator reads no cell |

`AtLeastOneDateRangeOverlaps`' class concerns its list cells; its scalar follows [§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap).

**Measured scope.** [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) records the measured members, and [§2 A.2](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default) and [§9 §3.8](07-repetition-and-iteration.md#38-sumofproducts) the count family's and `SumOfProducts`' measurements.

### Unavailable read in computation

| Class | Defined in | Meaning |
|---|---|---|
| `poisons` | [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty), [§3 B.6](02-logic-and-formal-errors.md#b6-validation-excludes-computation-poisons), [§11 §3.2](09-computations.md#32-an-invalidity-clear-poisons) | a reached read aborts the instance |
| `never poisons` | [§3 B.6](02-logic-and-formal-errors.md#b6-validation-excludes-computation-poisons), [§1 A.4.8](02-logic-and-formal-errors.md#a48-numberoffilledgroups) | a group presence read |
| `n/a` | — | the operator reads no cell, or a computation refuses it ([§11 §1](09-computations.md#1-the-ground-rules)) |

**Measured scope.** `never poisons` is measured on `NumberOfFilledGroups` ([§1 A.4.8](02-logic-and-formal-errors.md#a48-numberoffilledgroups)), and [§3 B.6](02-logic-and-formal-errors.md#b6-validation-excludes-computation-poisons) cites the group-presence computation checkpoint for the class. `poisons` is the general rule; members are measured where their own clauses say so, among them the field-fill scans ([§1 A.4.6](02-logic-and-formal-errors.md#a46-computation-ordered-field-fill-scans)), `FieldValuesNotUnique` ([§9 §5](07-repetition-and-iteration.md#5-groupfilled-and-the-other-repetition-rules)), the overlap predicates ([§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap)) and category reads ([§11 §3.2](09-computations.md#32-an-invalidity-clear-poisons)).

### Classification enablement

| Class | Defined in | Meaning |
|---|---|---|
| `enables` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | always enables the pass |
| `never` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | never enables it |
| `unless root` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | enables unless an operand is a root group |
| `with Having` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | enables only with a filtered operand |
| `with field member` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | enables only with a field-valued member |
| `field-dependent` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | enables when an operand is a field source |
| `field source` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | reads a document field |
| `constant source` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | reads no document field |
| `transparent` | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) | a field source when an operand is one |
| `n/a` | — | a connective, or an operator no admitted rule contains |

The first six classes are leaf classes; the last three are operand classes, consulted by a `field-dependent` comparison.

**Measured scope.** [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) records which assignments are measured and which rest on source reading.

### Polarity class

| Class | Defined in | Meaning |
|---|---|---|
| `leaf seed` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | directions seeded at the leaf |
| `arithmetic propagation` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | the operator's propagation formula |
| `Number aggregate missingness` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | the aggregate's own directions |
| `count headroom` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | grows while headroom remains |
| `not-given` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | one not-given bit |
| `prefix` | [§12 §4.1](10-validation-and-polarity.md#41-the-same-rule-fires-either-type) | the scanned prefix decides |
| `comparison dispatch` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | the per-operator direction dispatch |
| `fill tally` | [§1 A.4.4](02-logic-and-formal-errors.md#a44-validation-the-unfiltered-field-fill-tally), [§1 A.4.5](02-logic-and-formal-errors.md#a45-validation-filtered-field-fill-lists) | the field-fill polarity column |
| `group tally` | [§1 A.4.7](02-logic-and-formal-errors.md#a47-group-list-quantifiers) | the group-list polarity column |
| `positional` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | where the filtered value was collected |
| `value-list` | [§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-), [§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-) | the quantifier's omission-potential rule |
| `key fillability` | [§9 §6.3](07-repetition-and-iteration.md#63-the-leaf-its-polarity-and-its-references) | whether a duplicate key is complete |
| `date validity` | [§6 §3](05-dates-and-time.md#3-constructing-dates-and-checking-validity) | incomplete or unreal construction |
| `overlap scan` | [§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap) | the overlap predicate's scan |
| `pair product` | [§9 §3.8](07-repetition-and-iteration.md#38-sumofproducts) | per-pair missingness |
| `always VALUE` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | every firing is VALUE |
| `always OMISSION` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | every firing is OMISSION |
| `n/a` | — | a connective ([§12 §3](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-)), or an operator no admitted rule contains |

**The constant classes.** `FieldFilled`'s `always VALUE` and `FieldNotFilled`'s `always OMISSION` follow from the general rule of [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) over the verdicts of [§12 §3](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-). `GroupFilled` and `GroupNotFilled` are typed by [§9 §1](07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) and the singleton semantics of [§1 A.4.7](02-logic-and-formal-errors.md#a47-group-list-quantifiers); the pattern predicates by [§7 Part A](06-strings-and-enumerations.md#part-a--7-strings-and-patterns); custom-type `Valid` and `Invalid` by [§7 A.3](06-strings-and-enumerations.md#a3-custom-field-type-validation); and `CustomCondition` by [§14](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).

**Seeds outside the leaf-seed table.** Temporal components and differences seed as [§6 §2](05-dates-and-time.md#2-addition-and-difference-are-asymmetric-and-calendar-corrected) states, components of a constructed Date as [§6 §3](05-dates-and-time.md#3-constructing-dates-and-checking-validity) states, and a semantic-index read that selects no row as [§10 §4.1](08-paths-and-references.md#41-what-a-semantic-index-read-yields) states. `Length` seeds as an unsigned empty Number field does: grow-only over an empty or empty-text source, fixed over a filled one.

**Measured scope.** [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) and [§12 §4.1](10-validation-and-polarity.md#41-the-same-rule-fires-either-type) record which seeds, propagation rows, dispatch arms and extremum conditions are measured, and the predicate classes carry the measurements their own clauses record. Among the constant classes, `FieldNotFilled`'s OMISSION is measured ([§9 §2](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key)), and so are `GroupFilled`'s VALUE and `GroupNotFilled`'s OMISSION ([§9 §1](07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands)). The `Length` seed, the field-form propagation and the not-given rule on Boolean, Confirm, Enumeration and DateRange operands cite no measurement.

### Having filter effect

| Class | Defined in | Meaning |
|---|---|---|
| `full movement` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | grows and shrinks |
| `not-given` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | a not-given result |
| `match shrink` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | shrinks through a filtered match |
| `filled shrink` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | shrinks through a filtered filled cell |
| `slot mark` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | each slot marks its own filter |
| `deciding witness` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing), [§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-) | the quantifier's traversal decides |
| `positional` | [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) | where the filtered value was compared |
| `fill witness` | [§1 A.4.5](02-logic-and-formal-errors.md#a45-validation-filtered-field-fill-lists) | the deciding filled witnesses |
| `overlap scan` | [§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap) | the overlap predicate's scan |
| `n/a` | — | no operand can carry a filter, by the basis below |

**The `n/a` basis.** A filter needs a starred operand and a group operand takes none ([§9 §3](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation)), so F is `n/a` exactly where a chapter rules out a filtered operand:

- a bracketed field-value read refuses a starred path wherever it stands ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)), which covers the comparisons, arithmetic, String concatenation, the rounding and `Abs` operation forms, the Number operand-list `Min` and `Max`, the pattern predicates' field and `[F]`;
- `FieldFilled` and `FieldNotFilled` refuse a group and a starred field ([§1 A.4.9](02-logic-and-formal-errors.md#a49-static-admission-of-group-and-field-slot-operands));
- the singular value-list forms refuse a starred subject ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)), and their members are field-value reads ([§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-));
- the differences and direct component extractors ([§6 §2](05-dates-and-time.md#2-addition-and-difference-are-asymmetric-and-calendar-corrected)), `DateFromDateTime`, `TimeFromDateTime`, custom-type `Valid` and `Invalid` and the `DateRange` constructor's endpoints ([§6 §3](05-dates-and-time.md#3-constructing-dates-and-checking-validity)), `ValueAsDate` ([§6 §6](05-dates-and-time.md#6-date-fragments-and-fragment-ranges)), `StartOfDateRange` and `EndOfDateRange` ([§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap)), `RangeAsNumber` ([§5 §4](04-numbers-and-decimals.md#4-other-numeric-constraints)) and `RangeAsString` ([§11 §1](09-computations.md#1-the-ground-rules)) refuse a starred operand;
- `RepetitionNotUnique`'s keys refuse a star ([§9 §6](07-repetition-and-iteration.md#6-repetitionnotunique-precisely-)), and `SumOfProducts` rejects `Having` ([§9 §3](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation));
- `GroupFilled`, `GroupNotFilled` ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)) and `NumberOfFilledGroups` ([§1 A.4.9](02-logic-and-formal-errors.md#a49-static-admission-of-group-and-field-slot-operands)) refuse a field operand, and `CurrentRepetition` names a group;
- `Today`, `Now`, `BaseYear`, the literals and `CustomCondition` take no operand.

An operator no chapter restricts this way holds `not stated`.

**Measured scope.** [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) records which filter effects are measured.

### Partial extent

| Class | Defined in | Meaning |
|---|---|---|
| `all-rows` | [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) | every reopened level wildcarded |
| `declared slots` | [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) | every declared slot covered |
| `per slot` | [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) | each slot asked individually |
| `ordered prefix` | [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) | the slots before the first filled one |
| `complete cross-product` | [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) | each starred extent as a cross-product |
| `group-count walk` | [§12 §5.6](10-validation-and-polarity.md#56-group-presence-and-group-counts) | the counted group's own instances |
| `group relevance` | [§12 §5.6](10-validation-and-polarity.md#56-group-presence-and-group-counts) | the group relevance judgment |
| `none` | [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) | non-relevant members skipped |
| `key rows` | [§12 §5.3](10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set) | every key component relevant |
| `selection` | [§12 §5.5](10-validation-and-polarity.md#55-a-selection-that-resolves-to-no-row) | index and target coverage |
| `n/a` | — | no multi-cell operand, by the basis below; each cell read is judged by [§12 §5.3](10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set) |

X is `n/a` for the operators the first four bullets above list and for the operators with no operand; `CurrentRepetition` reads no cell ([§12 §5.3](10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set)). A keyed or semantic-index operand of any operator adds the `selection` judgment to that operator's own class ([§12 §5.5](10-validation-and-polarity.md#55-a-selection-that-resolves-to-no-row)).

**Measured scope.** [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) and [§12 §5.6](10-validation-and-polarity.md#56-group-presence-and-group-counts) record which predicates and carriers are measured.

### Traversal

A T cell names the operand's range, then the scan a `Having` filter on that operand uses, as "range; filter scan". The rule's own iteration is not a per-operator class: the rule iteration domain and the uniqueness relation domain of [§9 §1.3](07-repetition-and-iteration.md#13-evaluation-domains) select the rows a rule is evaluated at, and T names what an operand walks from such a row.

| Class | Defined in | Meaning |
|---|---|---|
| `instantiated` | [§9 §4.3](07-repetition-and-iteration.md#43-capacity-rows-beyond-the-declared-repeatability), [§1 A.4.2](02-logic-and-formal-errors.md#a42-the-two-iteration-ranges) | the in-capacity instantiated rows of each reopened level |
| `declared` | [§9 §4.2](07-repetition-and-iteration.md#42-the-open-declared-tail), [§1 A.4.2](02-logic-and-formal-errors.md#a42-the-two-iteration-ranges) | every declared slot of each reopened level, a missing one read empty |
| `instantiated then declared` | [§9 §3.9](07-repetition-and-iteration.md#39-filter-traversal), [§1 A.4.2](02-logic-and-formal-errors.md#a42-the-two-iteration-ranges) | an instantiated presence stage, then a declared empty stage |
| `key relation` | [§9 §6.2](07-repetition-and-iteration.md#62-the-duplicate-relation) | the uniqueness relation domain over the reference group's scope |
| filter `dense` | [§9 §3.9](07-repetition-and-iteration.md#39-filter-traversal) | every candidate of the filter traversal extent, in order |
| filter `sparse-enabled` | [§9 §3.9](07-repetition-and-iteration.md#39-filter-traversal) | dense up to a reopened product of 100, occupancy-skipping above |
| filter `declared` | [§9 §3.9](07-repetition-and-iteration.md#39-filter-traversal) | the filter at every declared coordinate |
| `n/a` | — | no operand reopens a level, by the basis below; as a filter scan, F is `n/a` |

T is `n/a` for the connectives, for the operand-list `Min` and `Max`, which refuse a starred field and a group operand ([§9 §3.5](07-repetition-and-iteration.md#35-entity-list-operand-admission)), for the operators the first four bullets of the F basis list, for the operators with no operand, for `CurrentRepetition`, which reads no cell, and for `ValueNotConsistent`, which has no admitted witness. Its filter part is `n/a` exactly where F is. An operator whose range or scan no chapter decides holds `not stated` in that part.

**Measured scope.** [§9 §3.9](07-repetition-and-iteration.md#39-filter-traversal) records which consumers' scans are measured and which are source-derived; none of them settles partial validation, whose extent is column X.

### Argument slots

An S cell lists the operator's argument slots in written order. `X`… is a nonempty comma-separated list of `X` slots, `[ … ]` an omissible slot, `In`, `To` and `@From` the separators of [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots), and "(infix)" an operator written between its two operands.

| Class | Defined in | Meaning |
|---|---|---|
| `entity` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | a field or group written bare |
| `range entity` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | an `entity` slot refusing a String literal |
| `value` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | an operation; a field bracketed |
| `member` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | a literal or a bracketed read |
| `digits` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | an unsigned number literal |
| `literal` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | a Number or String literal, `True` or `False` |
| `type name` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | a String literal naming a custom type |
| `pattern` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | a String literal holding the pattern |
| `endpoint` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | `FirstDay` or `LastDay` |
| `name` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | a name or a quoted name |
| `none` | [concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) | no argument list |
| `n/a` | — | no argument slots: a connective joins conditions, and a field read or a literal is itself an operand |

The constructors' components, the date-validity predicates' one `Date(...)` argument and the semantic-index key are spelled out in their cells, by [§6 §3](05-dates-and-time.md#3-constructing-dates-and-checking-validity) and [§10 §4](08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-). `ValueNotConsistent`'s cell records the `<subject> To <values>` shape of [§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-), which reaches its subject gate ([concrete syntax §1](12-concrete-syntax.md#1-lexical-structure)), although no admitted witness is known.

**Measured scope.** [Concrete syntax §3.2](12-concrete-syntax.md#32-argument-slots) records which slots' refusals are measured. The spelling a cell names is the one the owning chapters' admitted examples use, and the cells of `DateTime`, the source slot of the shifts other than `AddDays`, the differences other than `DifferenceInDays`, the extractors other than `YearFromDate`, `RangeAsString`, `RangeAsNumber`, `FieldValueAsString`, `FieldValueAsNumber`, `ValueAsDate`, `CurrentRepetition`, `AbsValue` and the pattern predicates' `pattern` slot are unmeasured.

---

## The table

### Connectives

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `And` / `Und` | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a |
| `Or` / `Oder` | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a |

The connectives read no cell and combine their operands' results by [§3 B.5](02-logic-and-formal-errors.md#b5-the-strong-kleene-tables-the-exact-algebra) and [§12 §3](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-).

### Presence and fill predicates

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `FieldFilled` / `FeldAngegeben` | `presence/fill` | `poisons` | `never` | `always VALUE` | n/a | n/a | n/a | `entity` |
| `FieldNotFilled` / `FeldNichtAngegeben` | `presence/fill` | `poisons` | `enables` | `always OMISSION` | n/a | n/a | n/a | `entity` |
| `AllFieldsFilled` / `AlleFelderAngegeben` | `presence/fill` | `poisons` | `with Having` | `fill tally` | `fill witness` | `per slot` | `declared`; filter `declared` | `entity`… |
| `NoFieldFilled` / `KeinFeldAngegeben` | `presence/fill` | `poisons` | `enables` | `fill tally` | `fill witness` | `per slot` | `instantiated`; filter `dense` | `entity`… |
| `AtLeastOneFieldFilled` / `MindestensEinFeldAngegeben` | `presence/fill` | `poisons` | `enables` | `fill tally` | `fill witness` | `per slot` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `MoreThanOneFieldFilled` / `MehrAlsEinFeldAngegeben` | `presence/fill` | `poisons` | `with Having` | `fill tally` | `fill witness` | `per slot` | `instantiated`; filter `dense` | `entity`… |
| `NotAllFieldsFilled` / `NichtAlleFelderOderKeinFeldAngegeben` | `presence/fill` | `poisons` | `enables` | `fill tally` | `fill witness` | `per slot` | `declared`; filter `declared` | `entity`… |
| `NotExactlyOneFieldFilled` / `NichtGenauEinFeldAngegeben` | `presence/fill` | `poisons` | `enables` | `fill tally` | `fill witness` | `per slot` | `instantiated`; filter `dense` | `entity`… |
| `FieldsNotCollectivelyFilled` / `FelderNichtGemeinsamAngegeben` | `presence/fill` | `poisons` | `enables` | `fill tally` | `fill witness` | `per slot` | `instantiated then declared`; filter `sparse-enabled` then `declared` | `entity`… |

`FieldFilled` and `FieldNotFilled` keep their E class on the plain, repeatable and semantic-indexed carriers alike ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)).

### Group presence and group-list predicates

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `GroupFilled` / `KontextAngegeben` | `group presence` | `never poisons` | `unless root` | `always VALUE` | n/a | `group relevance` | not stated; filter n/a | `entity` |
| `GroupNotFilled` / `KontextNichtAngegeben` | `group presence` | `never poisons` | `enables` | `always OMISSION` | n/a | `group relevance` | not stated; filter n/a | `entity` |
| `AllGroupsFilled` / `AlleKontexteAngegeben` | `group presence` | `never poisons` | `unless root` | `group tally` | not stated | `group relevance` | not stated; filter not stated | `entity`… |
| `NoGroupFilled` / `KeinKontextAngegeben` | `group presence` | `never poisons` | `enables` | `group tally` | not stated | `group relevance` | `instantiated`; filter not stated | `entity`… |
| `AtLeastOneGroupFilled` / `MindestensEinKontextAngegeben` | `group presence` | `never poisons` | `unless root` | `group tally` | not stated | `group relevance` | `instantiated`; filter not stated | `entity`… |
| `NotAllGroupsFilled` / `NichtAlleOderKeinKontextAngegeben` | `group presence` | `never poisons` | `unless root` | `group tally` | not stated | `group relevance` | not stated; filter not stated | `entity`… |
| `GroupsNotCollectivelyFilled` / `KontexteNichtGemeinsamAngegeben` | `group presence` | `never poisons` | `unless root` | `group tally` | not stated | `group relevance` | not stated; filter not stated | `entity`… |

`GroupNotFilled` enables over either operand kind, and `GroupFilled` and `GroupNotFilled` over a keyed group enable ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)). Whether a field operand of a group-list quantifier can carry a filter is not stated.

### Value-list predicates

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `FieldValueIncludedInValueList` / `FeldWertInWerteListe` | `value-list` | `poisons` | `with field member` | `value-list` | n/a | n/a | n/a | `entity`, `member`… |
| `FieldValueNotIncludedInValueList` / `FeldWertNichtInWerteListe` | `value-list` | `poisons` | `with field member` | `value-list` | n/a | n/a | n/a | `entity`, `member`… |
| `AtLeastOneFieldValueIncludedInValueList` / `MindestensEinFeldWertInWerteListe` | `value-list` | `poisons` | `with Having` | `value-list` | `deciding witness` | `declared slots` | `instantiated`; filter `sparse-enabled` | `entity`… `In` String literals or `entity`… |
| `NoFieldValueIncludedInValueList` / `KeinFeldWertInWerteListe` | `value-list` | `poisons` | `enables` | `value-list` | `deciding witness` | `declared slots` | `instantiated`; filter `dense` | `entity`… `In` String literals or `entity`… |
| `NotAllFieldValuesIncludedInValueList` / `NichtAlleFeldWerteInWerteListe` | `value-list` | `poisons` | `enables` | `value-list` | `deciding witness` | `declared slots` | `instantiated`; filter `dense` | `entity`… `In` String literals or `entity`… |
| `ValueNotConsistent` / `WertNichtKonsistent` | n/a | n/a | n/a | n/a | n/a | n/a | n/a | `entity` `To` values; the values' slot class not stated |

The two singular forms are the one-subject `AtLeastOne` and `NotAll` quantifiers ([§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-)); a semantic-index subject adds `selection`. `ValueNotConsistent`'s subject gate demands a table-backed Enumeration, for which no admitted witness is known ([§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-)), so no column applies to it.

### Uniqueness

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `FieldValuesNotUnique` / `FeldWerteNichtEindeutig` | `skip-invalid` | `poisons` | `with Having` | `positional` | `positional` | `none` | `instantiated`; filter `dense` | `entity`… |
| `RepetitionNotUnique` / `WiederholungNichtEindeutig` | `row drop` | n/a | `enables` | `key fillability` | n/a | `key rows` | `key relation`; filter n/a | `entity`… [`@From` `entity`] |

A computation refuses `RepetitionNotUnique` in its common precondition (unmeasured), in an alternative's precondition and in its operation ([§11 §1](09-computations.md#1-the-ground-rules)), so its C cell is `n/a`.

### Patterns and validity

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `PatternMatched` / `WieMuster` | `scalar read` | `poisons` | `enables` | `always VALUE` | n/a | n/a | n/a | `value`, `pattern` (infix) |
| `PatternViolated` / `NichtWieMuster` | `scalar read` | `poisons` | `enables` | `always VALUE` | n/a | n/a | n/a | `value`, `pattern` (infix) |
| `Valid` / `Gueltig` over a registered custom type | `scalar read` | `poisons` | `never` | `always VALUE` | n/a | n/a | n/a | `entity`, `type name` |
| `Invalid` / `Ungueltig` over a registered custom type | `scalar read` | `poisons` | `never` | `always VALUE` | n/a | n/a | n/a | `entity`, `type name` |
| `Valid` / `Gueltig` over `Date(...)` | `scalar read` | `poisons` | `enables` | `date validity` | not stated | not stated | not stated | one `Date(...)` call |
| `Invalid` / `Ungueltig` over `Date(...)` | `scalar read` | `poisons` | `enables` | `date validity` | not stated | not stated | not stated | one `Date(...)` call |

### Comparisons

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `==` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `!=` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `<` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `<=` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `>` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `>=` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `DiffersWithToleranceRange1` / `UngleichMitToleranz1` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `DiffersWithToleranceRange2` / `UngleichMitToleranz2` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `DiffersWithToleranceRange5` / `UngleichMitToleranz5` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |
| `DiffersWithToleranceRange10` / `UngleichMitToleranz10` | `scalar read` | `poisons` | `field-dependent` | `comparison dispatch` | n/a | n/a | n/a | `value`, `value` (infix) |

A comparison's V and C cells concern its own reads; each operand's cells are its operator's.

### Arithmetic

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `+` (Number) | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value`, `value` (infix) |
| `-` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value`, `value` (infix) |
| `*` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value`, `value` (infix) |
| `/` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value`, `value` (infix) |
| `^` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value`, `value` (infix) |
| `Min` / `Min` (operand list) | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` (Number); `not-given` (temporal) | n/a (Number); not stated (temporal) | n/a (Number); not stated (temporal) | n/a | `value`… |
| `Max` / `Max` (operand list) | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` (Number); `not-given` (temporal) | n/a (Number); not stated (temporal) | n/a (Number); not stated (temporal) | n/a | `value`… |
| `Abs` / `Abs` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value` |
| `RoundDown` / `Abrunden` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value` [, `digits`] |
| `RoundUp` / `Aufrunden` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value` [, `digits`] |
| `RoundAccounting` / `Runden` | `scalar read` | `poisons` | `transparent` | `arithmetic propagation` | n/a | n/a | n/a | `value` [, `digits`] |
| `AbsValue` / `AbsWert` | `scalar read` | `poisons` | `field source` | `arithmetic propagation` | not stated | not stated | not stated | `entity` |
| `RoundDownValue` / `AbrundenWert` | `scalar read` | `poisons` | `field source` | `arithmetic propagation` | not stated | not stated | not stated | `entity` [, `digits`] |
| `RoundUpValue` / `AufrundenWert` | `scalar read` | `poisons` | `field source` | `arithmetic propagation` | not stated | not stated | not stated | `entity` [, `digits`] |
| `RoundAccountingValue` / `RundenWert` | `scalar read` | `poisons` | `field source` | `arithmetic propagation` | not stated | not stated | not stated | `entity` [, `digits`] |

`RoundDownValue`, `RoundUpValue` and `RoundAccountingValue` take a Number field and have their operation forms' arithmetic ([§5 §2](04-numbers-and-decimals.md#2-rounding)). Each `…Value` field form, `AbsValue` included, propagates directions as its operation form does over the field's read.

### Aggregates and counts

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `Sum` / `Summe` | `all-cells` | `poisons` | `field source` | `Number aggregate missingness` | `full movement` | `all-rows` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `MinValue` / `MinWert` (Number) | `all-cells` | `poisons` | `field source` | `Number aggregate missingness` | `full movement` | `all-rows` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `MaxValue` / `MaxWert` (Number) | `all-cells` | `poisons` | `field source` | `Number aggregate missingness` | `full movement` | `all-rows` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `MinValue` / `MinWert` (Date/Time/DateTime) | `all-cells` | `poisons` | `field source` | `not-given` | `not-given` | `all-rows` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `MaxValue` / `MaxWert` (Date/Time/DateTime) | `all-cells` | `poisons` | `field source` | `not-given` | `not-given` | `all-rows` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `SumOfProducts` / `SummeVonProdukten` | `all-cells` | `poisons` | `field source` | `pair product` | n/a | `complete cross-product` | not stated; filter n/a | `entity`, `entity` |
| `NumberOfFilledFields` / `AnzahlAngegebenerFelder` | `all-cells` | `poisons` | `field source` | `count headroom` | `filled shrink` | `all-rows` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `NumberOfValueInFields` / `AnzahlWertInFeldliste` | `all-cells` | `poisons` | `field source` | `count headroom` | `match shrink` | `declared slots` | `instantiated`; filter `dense` | `literal` `In` `entity`… |
| `NumberOfDifferentValues` / `AnzahlVerschiedenerWerte` | `all-cells` | `poisons` | `field source` | `count headroom` | `full movement` | `all-rows` | `instantiated`; filter `sparse-enabled` | `entity`… |
| `NumberOfFilledGroups` / `AnzahlAngegebenerKontexte` | `group presence` | `never poisons` | `field source` | `count headroom` | n/a | `group-count walk` | `instantiated`; filter n/a | `entity`… |

### `FirstFilledValue`

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `FirstFilledValue` / `ErsterAngegebenerWert` | `stop-at-first` | `poisons` | `field source` | `prefix` | `slot mark` | `ordered prefix` | `instantiated`; filter `dense` | `entity`… |

### Temporal operators

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `Today` / `Heute` | n/a | n/a | `constant source` | `not-given` | n/a | n/a | n/a | `none` |
| `Now` / `Jetzt` | n/a | n/a | `constant source` | `not-given` | n/a | n/a | n/a | `none` |
| `BaseYear` / `Referenzjahr` | n/a | n/a | `constant source` | `leaf seed` | n/a | n/a | n/a | `none` |
| `Date` / `Datum` (constructor) | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | two to four components, each `entity`, String literal or extractor call |
| `Time` / `Zeit` (constructor) | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | zero to three components, each `entity`, String literal or extractor call |
| `DateTime` / `DateTime` (constructor) | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | `entity`, `entity` |
| `DateRange` / `DatumBereich` (constructor) | `scalar read` | `poisons` | `field source` | `not-given` | n/a | n/a | n/a | `range entity`, `range entity` |
| `AddDays` / `AddiereTage` | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | `entity`, `value` |
| `AddMonths` / `AddiereMonate` | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | `entity`, `value` |
| `AddYears` / `AddiereJahre` | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | `entity`, `value` |
| `AddHours` / `AddiereStunden` | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | `entity`, `value` |
| `AddMinutes` / `AddiereMinuten` | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | `entity`, `value` |
| `AddSeconds` / `AddiereSekunden` | `scalar read` | `poisons` | `transparent` | `not-given` | not stated | not stated | not stated | `entity`, `value` |
| `DifferenceInDays` / `DifferenzInTagen` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity`, `entity` |
| `DifferenceInMonths` / `DifferenzInMonaten` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity`, `entity` |
| `DifferenceInYears` / `DifferenzInJahren` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity`, `entity` |
| `DifferenceInHours` / `DifferenzInStunden` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity`, `entity` |
| `DifferenceInMinutes` / `DifferenzInMinuten` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity`, `entity` |
| `DifferenceInSeconds` / `DifferenzInSekunden` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity`, `entity` |
| `YearFromDate` / `JahrAusDatum` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity` |
| `MonthFromDate` / `MonatAusDatum` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity` |
| `DayFromDate` / `TagAusDatum` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity` |
| `QuarterFromDate` / `QuartalAusDatum` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity` |
| `HoursFromTime` / `StundenAusZeit` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity` |
| `MinutesFromTime` / `MinutenAusZeit` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity` |
| `SecondsFromTime` / `SekundenAusZeit` | `scalar read` | `poisons` | `transparent` | `leaf seed` | n/a | n/a | n/a | `entity` |
| `DateFromDateTime` / `DatumAusDateTime` | `scalar read` | `poisons` | `transparent` | `not-given` | n/a | n/a | n/a | `entity` |
| `TimeFromDateTime` / `ZeitAusDateTime` | `scalar read` | `poisons` | `transparent` | `not-given` | n/a | n/a | n/a | `entity` |
| `StartOfDateRange` / `StartAusDatumBereich` | `scalar read` | `poisons` | `field source` | `not-given` | n/a | n/a | n/a | `range entity` |
| `EndOfDateRange` / `EndeAusDatumBereich` | `scalar read` | `poisons` | `field source` | `not-given` | n/a | n/a | n/a | `range entity` |
| `DateRangesOverlap` / `DatumsBereicheUeberlappend` | `skip-invalid` | `poisons` | `enables` | `overlap scan` | `overlap scan` | not stated | `instantiated`; filter `dense` | `range entity`… |
| `AtLeastOneDateRangeOverlaps` / `MindestensEinDatumsBereichUeberlappend` | `skip-invalid` | `poisons` | `with Having` | `overlap scan` | `overlap scan` | not stated | `instantiated`; filter `sparse-enabled` | `range entity` `In` `range entity`… |

A `DateRange` constructor's endpoints and a bound extractor's operand are field references only ([§6 §8](05-dates-and-time.md#8-date-ranges-and-overlap)), which is why both are field sources.

### String operators

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `Length` / `Laenge` | `scalar read` | `poisons` | `field source` | `leaf seed` | not stated | not stated | not stated | `entity` |
| `+` (String concatenation) | `scalar read` | `poisons` | `transparent` | `not-given` | n/a | n/a | n/a | `value`, `value` (infix) |

### Coercions

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `RangeAsString` / `BereichAlsString` | `scalar read` | `poisons` | `field source` | `not-given` | n/a | n/a | n/a | `entity`, `digits`, `digits` |
| `FieldValueAsString` / `FeldWertAlsString` | `scalar read` | `poisons` | `field source` | `not-given` | not stated | not stated | not stated | `entity` |
| `RangeAsNumber` / `BereichAlsZahl` | `scalar read` | `poisons` | `field source` | `leaf seed` | n/a | n/a | n/a | `entity`, `digits`, `digits` |
| `FieldValueAsNumber` / `FeldWertAlsZahl` | `scalar read` | `poisons` | `field source` | `leaf seed` | not stated | not stated | not stated | `entity` |
| `ValueAsDate` / `WertAlsDatum` | `scalar read` | `poisons` | `field source` | `not-given` | n/a | n/a | n/a | `entity`, `endpoint` |

`FirstDay` / `ErsterTag` and `LastDay` / `LetzterTag` are `ValueAsDate`'s endpoint arguments, not operators of their own ([§6 §6](05-dates-and-time.md#6-date-fragments-and-fragment-ranges)).

### Field reads, keyed and indexed reads, literals

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `[F]` field read | `scalar read` | `poisons` | `field source` | `leaf seed` (Number); `not-given` (other kinds) | n/a | n/a | n/a | n/a |
| `[F For key]` / `Fuer` semantic-index read | `scalar read` | `poisons` | `field source` | `leaf seed` (Number); `not-given` (other kinds) | not stated | `selection` | not stated | key: String literal or `entity` |
| `[F -> Category]` category read | `scalar read` | `poisons` | `field source` | `not-given` | not stated | not stated | not stated | n/a |
| Number literal | n/a | n/a | `constant source` | `leaf seed` | n/a | n/a | n/a | n/a |
| String, date, clock and date-time literal | n/a | n/a | `constant source` | `not-given` | n/a | n/a | n/a | n/a |
| `True` / `Wahr`, `False` / `Falsch` | n/a | n/a | `constant source` | `not-given` | n/a | n/a | n/a | `none` |

A semantic-index key may itself carry a filter ([§9 §3](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation)); what that filter does to the read's typing is not stated.

### `CurrentRepetition`

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `CurrentRepetition` / `AktuelleWiederholung` | n/a | n/a | `constant source` | `leaf seed` | n/a | n/a | n/a | `entity` |

`CurrentRepetition` answers from the iterated row and reads no cell, so no relevant set makes it UNKNOWN ([§12 §5.3](10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set)).

### `CustomCondition`

| Operator | V | C | E | P | F | X | T | S |
|---|---|---|---|---|---|---|---|---|
| `CustomCondition` / `ApplikationsBedingung` | `callback` | n/a | `never` | `always VALUE` | n/a | n/a | n/a | `name` |

A computation refuses `CustomCondition` ([§11 §1](09-computations.md#1-the-ground-rules)).

### Spellings without a row

The other keywords of [concrete syntax §5](12-concrete-syntax.md#5-keyword-catalog-english--german-verified-pairs) are not operators: `In`, `To` / `Zu` and `@From` / `@Von` separate an operator's arguments; `Having` / `Mit` is the filter whose effect is column F; `$` marks a correlated path and `RuleGroup` / `RegelKontext` names an entity; `@SuppressWarning` / `@UnterdrueckeWarnung` is the preamble; `FirstDay` and `LastDay` are argument values. The 13 German-only form constructs and `#Zeile` have no row: [concrete syntax §1](12-concrete-syntax.md#1-lexical-structure), [concrete syntax §3.1](12-concrete-syntax.md#31-which-class-a-refused-text-draws) and [concrete syntax §5](12-concrete-syntax.md#5-keyword-catalog-english--german-verified-pairs) state how they lex and which classes the measured ones draw.

---

## Checklist for the operator reference

- [ ] Every operator's class in every column is read from its cell, never inferred from a neighbouring operator.
- [ ] `n/a` means the column does not apply; `not stated` means it applies and no chapter decides it, so an implementation must not present its own choice as specified.
- [ ] A kind-dependent cell is read per operand kind, and a carrier-qualified row only for its carrier.
- [ ] Each class's mechanism comes from the section its vocabulary links; the measured-scope sentence links the clause that records which assignments are measured.
- [ ] A T cell's range and filter scan are read separately: the presence of `Having` alone never selects a sparse scan, and the operand's range never substitutes for the rule's own iteration domain.
- [ ] An S cell decides how a field is written in each slot: bare in an `entity` slot, bracketed in a `value` slot.
