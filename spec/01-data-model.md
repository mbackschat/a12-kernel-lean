# 01 — The data model and the call surface

*Prerequisite reading for everything else.* This file fixes the vocabulary and the shapes the rest of the set evaluates over: what a model is and when a declaration is legal, what a document is, how repetition and addresses work, what "a cell" means precisely, and the two operations (validate, compute) with their call surface. It is deliberately mechanical; the *interesting* semantics start in [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md).

See [`SEMANTICS-MAP.md`](SEMANTICS-MAP.md) for the glossary and the taxonomy; terms like *cell*, *row*, *not-check-relevant* are defined there.

---

## 1. Model = a typed tree

**A document model is a static declaration tree of groups and fields.** Groups are internal nodes and fields are leaves; the model's root is a single group. A group's direct children form an ordered declaration sequence. Groups nest arbitrarily; a repeatable group may contain repeatable subgroups, giving multi-dimensional arrays. Recursive expansion to descendant fields preserves model declaration order: a child field is visited when reached, while a child group's descendant fields are visited recursively before the next sibling.

- **Groups** are **non-repeatable** (occurring at most once wherever their parent occurs) or **repeatable** (declaring an ordered 1-based row-address range `1 … repeatability`; a valid document may instantiate only a prefix `1 … rowCount`, where `rowCount ≤ repeatability`).
- **Fields** are leaves. Each has a **type** and per-type configuration. (The type table is in [`SEMANTICS-MAP.md §2`](SEMANTICS-MAP.md#2-field-types-at-a-glance); per-type evaluation is in files 04–06.)

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

#### Repeatability

**`repeatability` is a finite integer strictly greater than zero, and declaring it is what makes a group repeatable.** A group declaring none is non-repeatable rather than unbounded. There is therefore no unbounded repeatable group; an implementation may keep an optional maximum as a total function but must not expose the absent case as an authorable model. The upper bound is the declaring carrier's rather than one global constant, and the root's and a nested group's bounds are an order of magnitude apart, so a checker holding one bound either refuses a legal nested group or accepts an illegal root one. The member binds as a Java `int` ([§1.1](#member-binding)).

| Declared `repeatability` | Result |
|---|---|
| none | non-repeatable: a wildcard over the group is refused `MVK_INVALID_WILDCARD`, while its bare name is admitted as an ordinary group operand |
| `1` | admitted: a non-repeatable group spelled explicitly |
| `2` up to the carrier's bound | repeatable |
| `0`, below zero, or a present count that reads as no value such as JSON `null` | read by the model reader, so the refusal is not visible at load. The consistency check draws `MVK_MAX_VALUES_INVALID` at the group and once at every group and field beneath it, and none at a rule or computation declared there; it names each affected element separately, worded `zahlIstNullOvz` (a positive-only zero refusal) for `0` and `null` and `zahlMitVorzeichen` (an unsigned-field sign refusal) for a negative. The group alone also draws a codeless notification, not-positive for zero or `null` and signed below zero |
| above `999999999` on a root group, above `1999999999` on a nested group | `MVK_MAX_TOO_BIG`; a root admits `999999999` and refuses `1000000000`, a nested group admits `1999999999` and refuses `2000000000` |
| past a signed 32-bit count | the model is not read at all, so no class is issued; an implementation holding the count as an unbounded integer must reproduce that read failure rather than a verdict |

#### The root group's reserved name

**Exactly one whole name is reserved, and only on the root carrier.** A root group may not be called `Id`, matched case-insensitively over the *entire* name: `Id`, `ID`, `id` and `iD` all draw `MVK_ROOT_GROUP_NAME_INVALID`, while `Identity` and `BinId` are ordinary. A nested group or a field named `Id` is admitted. This is a name equality rather than an alphabet rule, which is why it sits apart from the character-level name laws of [§1.3](#names-groups-and-texts), and a prefix or substring reading of it is wrong.

#### Index field, S-value and Custom field

A repeatable A12 group may designate at most one direct value-validating child as its **index field**; table-backed Enumeration and no-value-validation profiles are not legal index declarations. Generated validation requires that field when the group row is present and requires its stored value to be unique among sibling rows under the same parent. Every admitted non-Number scalar kind uses exact stored-text identity for that uniqueness relation, while Number uses normalized numeric equality. How a nomination is admitted is [§1.3](#index-and-sort-nomination-admission)'s; the generated checks, and a non-repeatable group's nomination, are [§4 B.4](03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique)'s.

An ordinary closed Enumeration may additionally designate one stored token as its **S-value**. This is a model-owned index default, not a document value: the validation call may transiently supply it only under the eligibility rules in [§12](10-validation-and-polarity.md#5-full-vs-partial-validation).

A Custom field names a registered validator and preserves whether its optional length bounds were declared; the exact formal-check contract is in [§7](06-strings-and-enumerations.md#a3-custom-field-type-validation).

#### Type member ranges

**A type member outside its own range draws a codeless verdict and bounds nothing else.** The ranges and not-declared values:

| Member | Range | `−1` |
|---|---|---|
| String or Custom `minLength`, `maxLength` | 1 to 99,999 | the no-bound value |
| Number `minLength`, `maxLength` | 1 to 99,999 | counts as signed |
| Number `maxIntegerDigits` | 1 to 15 | counts as signed |
| `minFractionalDigits`, `maxFractionalDigits` | 0 to 14 | the not-declared sentinel |

- **Five codeless notifications.** A member above its range, a zero where zero lies outside it, or a signed member draws one of five codeless notifications: above 99,999, above 15 or above 14, each naming its range's top; not positive; or signed. Every count below `−1` is signed. Each of the five is reported once per field across its length and digit members. An amount's integer count derived as `15 − maxFractionalDigits` is judged as if declared.
- **Only the type's own laws go silent.** A law that reads an out-of-range member stays silent, while one reading only in-range members still answers. A hint list is not checked against an out-of-range length either. Whether a fractional part is declared is a three-valued disjunction of the two fractional counts, so an in-range positive count decides it beside an out-of-range partner and an in-range zero does not.
- **A rule reader keeps judging with the written length**, `−1` alone reading as absent: `FieldValueAsNumber` converts a `[0-9]+` String whose `maxLength` is `0` or `−5` and not one whose `maxLength` is `100,000` or `−1`, and an index key is judged against a `minLength` of `100,000` though not against a `maxLength` of `0`.
- A field the default variant removes draws none of these, and the model builds, so these are verdicts rather than build failures.

> **Non-normative implementation note.** A model is naturally a `structure`/`inductive` of group and field declarations. Keep the *static* configuration (a Number's scale, a Date's format, a group's repeatability, whether a field is signed) in the model, **not** in runtime values — several semantics (the scale gate on `==`, number fillability, fragment completion) are decided from the *declared* configuration, sometimes before any value exists. A common early mistake is to attach scale to the runtime decimal; scale is a property of the *field*.

Sources: [repeatability checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-repeatability-declaration-domain), [inbound repeatability domain](../docs/sources/inbound-group-operand-batches.md#src-repeatability-domain-peer-measurement), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-24a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-24a), a12-dmkits `KF365` and `KF367` (no local record).

### 1.1 The two special model-level configurations

**Four model-wide settings change evaluation globally; carry them in the model, not per field.**

- **Base Year** — a reference year that omitted-year date literals (`"13.07."`) and date fragments complete against. When it is absent, a consumer that requires concrete year-bearing Dates rejects those constructs; same-profile yearless DateRange equality and inequality remain the measured exception and do not imply an instant. ([§6](05-dates-and-time.md))
- **Time zone** — the DM-JSON key `content.modelConfig.timeZone` (the capitalized `TimeZone` is the *internal* metamodel key code generation copies it into). Absent means `UTC`. The legal id set is a host input, and an explicit id outside it is refused `MVK_INVALID_TIME_ZONE`; [§6 §5](05-dates-and-time.md#5-time-zones-and-the-sub-day-difference) owns that set. The zone is applied at **parse time** to every DATE and DATE_TIME through legacy `java.util.TimeZone` plus non-lenient `SimpleDateFormat`, not `java.time`; a plain date is midnight in that zone.
- **Supported characters** — an optional legal charset. An absent or empty list uses the default Basic Multilingual Plane policy; a list containing an empty entry is malformed. The configured definition is runtime-enforced according to the exact entry and atomic-matching rules in [§7](06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching).
- **`fieldRefByShortNameAllowed`** — enables model-wide unique short-name field references. ([§10](08-paths-and-references.md))

#### The model's own texts meet the default charset

**With no charset configured, a supplementary character in a model text draws the codeless repertoire refusal, one finding per element however many of its texts offend.** The finding names the element, a computation as a rule.

| Carrier | Texts judged |
|---|---|
| rule | a condition's literal, comment or bare text; the error code; the name; the message |
| computation | the operation; either precondition; the name; the message |
| field | an annotation name and value; an enumeration value and label; a String type's pattern message and an Enumeration's invalid-value message, drawn on their field |
| group | an annotation name and value |
| rule annotation | an annotation name and value |

- **Texts that draw none:** the model's, a group's and a field's labels, and a message, a pattern message or an enumeration label for a locale the model does not declare.
- **In a name.** In a field's or a nested group's name the finding stands beside `MVK_PATH_INVALID`, and a group's name carries it to the group, every field beneath it and every rule declared inside it.
- **In an alphabet-governed text.** In the error code and a field name, which have alphabets of their own, it takes the place of that alphabet's own codeless finding, and bare text outside a literal draws `MVK_LEXER_STANDARD_ERROR` beside it.
- **Surrogates.** A lone surrogate in a message is refused as a pair is. A lone surrogate in a String pattern message or an Enumeration invalid-value message draws `WRONG_ENCODING` as the first text gate, beside the repertoire notification. In those two messages a supplementary character that draws `INVALID_CHARACTERS`, such as the noncharacter `U+10FFFF`, draws no repertoire notification, while a control character beside an emoji draws both; in an element annotation `U+10FFFF` draws the repertoire notification.
- A broken or unreferenced error target does not stop it. A rule the variant filter rejects: [§1.4](#14-variant-filters-and-where-a-filtered-declaration-is-seen).

#### Member binding

**A member that is not text binds before any check, and one that cannot bind leaves no model.** Binding comes before the variant filter, so a field the filter deletes still needs bindable members, while a type's object that the field's `type` does not name is never read.

- **Every primitive boolean member binds by one law:** the header's `immutable` and `metaData`, `fieldRefByShortNameAllowed`, a field's `global` and `transient`, `lineBreaksPermitted`, `noValueValidation` and `alphabeticalSorting` on a String, `zeroNotAllowed`, `positivesOnly` and `leadingZerosAllowed` on a Number, `youngerThan1900Check` on a Date, DateRange or DateFragment and `alphabeticalSorting` on an Enumeration, inside a type definition whether or not a field references it.
  - A JSON boolean binds as written and an integer token is set unless zero, `-0` clearing.
  - A number is judged by its token's kind, not its value: a token written with a fraction or an exponent leaves no model, `1e0`, `1E+0`, `1.0`, `10e-1` and `-0.0` included.
  - A text is cut by Java's `String.trim`, which removes only the characters up to U+0020, and must then be exactly `true`, `True`, `TRUE`, `false`, `False` or `FALSE`; an empty text and the text `null` are the default, as JSON `null` and absence are. `"tRUE"`, `"yes"`, `"1"`, a no-break or em space before `true` and a container leave no model.
- **A group's `repeatability` and the header's `baseYear` bind as Java `int`s.**
  - A text is trimmed the same way and read by `Integer.parseInt`, which takes one sign and any decimal digit of the Basic Multilingual Plane, so `" 3 "`, `"+3"`, `"03"` and `"٣"` are 3, while `"3.7"`, `"1e1"`, `"0x3"` and a no-break space beside the digits leave no model.
  - A JSON number is truncated toward zero when its value lies inside the `int` range, whether it is written with a fraction or an exponent, so `3.7` is 3, `1e1` and `10.0` are both 10 and `2.147483647E9` is 2147483647, while `2147483647.5`, `2147483648` and `3e10` leave no model in either spelling.
  - An empty text and the text `null` are no value: a count with no value is refused as [§1](#repeatability) states, and a base year with no value is absent.
- The text `null` is likewise no Number bound.

Sources: [inbound 2026-09-26m model texts](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-model-texts), [inbound 2026-09-26n field message gates](../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates), [inbound 2026-10-18](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-22](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-22).

### 1.2 Model consistency rules

**Reading and member binding come first, then building, and a failure at either leaves no model; a built model then meets six ordered consistency rules, and a model drawing any notification is refused.** Each stage reads either the model as authored or the variant-filtered model of [§1.4](#14-variant-filters-and-where-a-filtered-declaration-is-seen):

| Stage | Reads | A defect shows as |
|---|---|---|
| reading and member binding ([§1.1](#member-binding)) | the authored JSON | no model, no class |
| building | the authored model, with the variant exemptions in the table below | a build failure: no class, and no later stage reports |
| consistency rules 1–6, in order | the authored model, except rule 5, which reads the variant-filtered model | codeless notifications from every rule but the fifth; rule 5's carry the `MVK_*` classes of [§1.3](#13-declaration-generation-classes) |
| code generation and its static checks; evaluation | the variant-filtered model | the condition, operation and message classes of the later chapters; no order against the consistency rules is stated |

#### Defects that leave no model

**Every defect below leaves no model and no rule below reports.** The third column gives the same declaration filtered `ONLY` at the default variant ([§1.4](#14-variant-filters-and-where-a-filtered-declaration-is-seen)); `not stated` means no measurement or chapter decides it.

| Defect | Result | Filtered `ONLY` |
|---|---|---|
| a primitive member that cannot bind ([§1.1](#member-binding)) | no model | no model: binding precedes the filter |
| an unknown, absent or null field type | load or build refusal | kept |
| a Date type without its body object; a Time, DateTime or DateFragment without one (a String or Boolean without one is read) | unreadable | kept for a Date; not stated for the others |
| an empty message entry | load or build refusal | kept |
| `datePrecision` on a temporal kind other than Date; any member a type body does not declare | unreadable | not stated |
| a Number bound written as text outside the reader's decimal grammar ([§1.3](#13-declaration-generation-classes)) | unreadable | not stated |
| an element with an empty name; a Java-blank name of a root, group, field, rule or computation (a no-break space is an ordinary name) | build fails | admitted for a field, rule or computation the filter deletes |
| an object-valued name | build fails | a codeless refusal |
| a type reference with an empty id | build fails | not stated |
| a type-definition reference without its id | build fails | a codeless refusal |
| a computation with an empty target path; a computation target naming any group, its own (`..`) or another | build fails | not stated |
| a rule's error target on its own group ([§3.1](#the-error-fields-declaration)) | build fails | not stated |
| an Enumeration with two categories of one name | build fails | not stated |
| an Enumeration with no value, with categories or without them | build fails | admitted |
| two hint-list entries for one locale | build fails | not stated |
| an empty index-field or sort-field name | build fails | not stated |
| a Java-blank `format` on a Date, DateTime or Time, inside a type definition too (an omitted one is the default; a no-break space is an ordinary invalid format) | build fails | admitted |
| an empty DateFragment `formatOfFragment` | build fails | not stated |
| two fields of one name | build fails | admitted when one of them is filtered `ONLY` |
| a `variantFilter` of unknown, absent, null, object or numeric mode, or a string in the filter's place (an explicit `null` filter is admitted) | build fails | — |
| an unreadable rule error-code member | no declaration verdict | not stated |

Further load and build refusals are stated with their construct: the one measured model declaring a supplementary charset range ([§1.3](#enumeration-declarations)), an empty `interpretationOfYear` token ([§6](05-dates-and-time.md)), and an unknown `roundingMode` ([§11 §6](09-computations.md#6-the-implicit-validation-rule-precisely)). A notification's absence of a class key therefore cannot by itself distinguish a build failure from a codeless verdict.

#### The six rules

**The rules run in this order, each walking type definitions first and then the elements depth-first, a group before its children, and their notifications are reported in that order, each rule's in walk order except the fifth's.** Every rule except the fifth reads the authored model, so a variant-filtered field still meets id uniqueness, the value limits and the group shapes. The notifications of the other five rules carry no `MVK_*` class.

1. **Id uniqueness** over every group, field, rule and computation, type definitions excluded: an id carried by `k ≥ 2` elements draws `k` notifications. The empty id is an ordinary id here.
2. **Number value limits** on every field whose effective type is Number: the maximum, then the minimum, is refused when its nearest double exceeds the double `10^(15−m) − 10^(−m)` at the raw declared maximum fractional count `m`, a minimum by magnitude. The comparison is between doubles, so `maxValue: 9999999999999.991` at `m = 2` passes while `9999999999999.995` does not. A type definition no field uses is not checked.
3. **Attachment groups** (`usageType` `attachment`):
   - one notification when any of the eight required field names (`original_filename`, `internal_filename`, `content`, `attachment_id`, `size`, `mime_type`, `category`, `description`) is missing among the group's direct fields;
   - one when any of the four required rule conditions of the model's condition language, compared as exact text, is missing among the group's direct rules (table below; another condition language is unmeasured);
   - and one when the first direct element named `content` is a field whose declared type, not its effective type, is a String lacking either `noValueValidation` or `lineBreaksPermitted`.
4. **Multi-select groups** (`usageType` `multi-select`): a group repeatable at most once; a group without exactly one direct field; then, for that field, a missing requiredness configuration, its nomination as the group's index field, and an effective type other than String or Enumeration; and finally any direct child group or computation.
5. **Generation of the declaration**, which carries the `MVK_*` classes of [§1.3](#13-declaration-generation-classes), reported as [§1.3](#13-declaration-generation-classes) states rather than in walk order, and, on the variant-filtered model, checks each Number bound's printed text ([§5 §4](04-numbers-and-decimals.md#4-other-numeric-constraints)) with two arms of the value cascade: more than 15 digits, then a minus on zero. For those bound checks a field reports the maximum before the minimum, and an identical notification on the same field only once.
6. **Basic member checks**: an empty type-definition id or name; an empty element id; an empty rule condition or error-entity path; and one notification for a computation with any empty operation. An empty error code and a repeated Enumeration value are reported by this rule too, and are specified with their declarations ([§3.3](#33-member-texts-of-rules-and-computations), [§1.3](#enumeration-declarations)).

The required attachment rule conditions, by condition language:

| `en_US` | `de_DE` |
|---|---|
| `GroupFilled(RuleGroup) and NotExactlyOneFieldFilled(attachment_id, content)` | `KontextAngegeben(RegelKontext) und NichtGenauEinFeldAngegeben(attachment_id, content)` |
| `FieldFilled(content) and FieldNotFilled(size)` | `FeldAngegeben(content) und FeldNichtAngegeben(size)` |
| `GroupFilled(RuleGroup) and FieldNotFilled(internal_filename)` | `KontextAngegeben(RegelKontext) und FeldNichtAngegeben(internal_filename)` |
| `GroupFilled(RuleGroup) and FieldNotFilled(mime_type)` | `KontextAngegeben(RegelKontext) und FeldNichtAngegeben(mime_type)` |

Sources: [model consistency checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-model-consistency-k17) and its [retained capture](../evidence/kernel-30.8.1/captures/model-consistency-2026-10-13/rows.json) (rows `a-ok`, `a-de-ok`), [executable declaration admission checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-executable-declaration-admission), [inbound 2026-09-27a variant filter stages](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-variant-filter-stages), [inbound 2026-09-26m error-target paths](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-error-target-paths), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21).

### 1.3 Declaration generation classes

**Rule 5 of [§1.2](#12-model-consistency-rules) reports its `MVK_*` classes as an unordered collection.** Two models that author the same elements in opposite orders report the same notifications in the same order, and that order is neither the authored one nor a walk, so no order is claimed. A notification identical to another on the same element, same class and same parameters, is reported once. The rule reads the variant-filtered model: a field its own `ONLY` filter deletes draws none of the classes below, while a group is never filtered. A field typed by a type definition is judged on the definition's body, once per referencing field; a definition no field references draws nothing.

#### Field type bodies

Out-of-range members follow [§1](#type-member-ranges) and bind nothing. With the members in range:

- **String.**
  - `noValueValidation` without `lineBreaksPermitted` draws `MVK_STRING_TYPE_NO_VAL_AND_NO_LINE_BREAK`; with a non-empty `pattern` or a `minLength` it draws `MVK_STRING_TYPE_PARAMS_INCONSISTENT` once, an empty pattern, a `maxLength` and a `-1` minimum not counting; with a `hintList` holding an entry it draws `MVK_NO_VAL_AND_HINT_LISTS`. Both flags bind by the boolean law of [§1.1](#member-binding).
  - `lineBreaksPermitted` beside `maxLength: 1` draws `MVK_LINE_BREAK_AND_MAX_LENGTH_1_INVALID`.
  - A minimum length above the maximum draws `MVK_MIN_LENGTH_BIGGER_MAX_LENGTH`, a `-1` maximum being no bound.
  - A non-empty pattern refused by the pattern gate of [§7](06-strings-and-enumerations.md#pattern-admission-and-execution) draws `MVK_PATTERN_INVALID`, a source the regular-expression compiler rejects included; an empty pattern is no pattern, so a message beside it draws `MVK_ERROR_MESSAGE_AND_NO_PATTERN`.
- **Hint lists.** Only entries for declared locales are judged; two entries for one locale are a [build failure](#defects-that-leave-no-model). Each distinct value longer than the maximum length draws `MVK_VALUE_TOO_LONG`, each shorter than the minimum `MVK_VALUE_TOO_SHORT`, and each value written twice or more in one entry `MVK_VALUES_DUPLICATE` once; one value in two locales' entries is admitted. A value holding a supplementary character draws the field's codeless repertoire notification ([§1.1](#the-models-own-texts-meet-the-default-charset)) and none of these three classes, while its sibling values are still judged. The laws hold beside `noValueValidation`.
- **Number.**
  - Both fractional members `-1` draw `MVK_FRACT_DIGITS_MISSING`.
  - With `fp` the fractional part being declared, the three-valued disjunction of [§1](#type-member-ranges), and the sign counted unless `positivesOnly`, a length above `15 + sign + fp` draws `MVK_MAX_LENGTH_TOO_BIG` or `MVK_MIN_LENGTH_TOO_BIG`, and an unknown `fp` draws neither.
  - A maximum length below the positive minimum fractional count plus two draws `MVK_MAX_LENGTH_TOO_SMALL`, whatever the sign and the maximum count.
  - An integer count, declared or derived from the amount trait, plus the minimum fractional count above 15 draws `MVK_ARITY_TOO_BIG`.
  - A minimum length above the maximum draws `MVK_MIN_LENGTH_BIGGER_MAX_LENGTH`.
  - A `minValue` above `maxValue` draws `MVK_MIN_VALUE_BIGGER_THAN_MAX_VALUE`, comparing the bounds as printed for the runtime ([§5 §4](04-numbers-and-decimals.md#4-other-numeric-constraints)): `minValue: 1.4` beside `maxValue: 1` is admitted at no fractional digit and refused at one. The inversion class is withheld beside a bound whose printed form fails its own codeless check, a `-0` at no fractional digit or more than fifteen printed digits, while the magnitude limit of rule 2, read from `maxFractionalDigits` alone and stated even on a field the variant filter deletes, neither withholds it nor is withheld.
  - A bound may also be written as text in the decimal grammar of the DM-JSON reader, surrounding spaces trimmed, a sign, a point and an exponent each optional, so `"1e3"`, `"+5"` and `" 5"` are read; other text is a [read failure](#defects-that-leave-no-model).
- **Custom.** A `name` that is absent, empty or blank ([§3.3](#33-member-texts-of-rules-and-computations)) draws `CUSTOM_FIELD_TYPE_CODENAME_MISSING`; any other name with a character outside ASCII letters, digits and `_` draws a codeless notification, a digit or underscore leading included. The length laws read as for String, the inverted pair drawing the unprefixed `MIN_LENGTH_BIGGER_MAX_LENGTH`.
- **Temporal.**
  - A Date, Time, DateTime or DateFragment format outside the thirteen admitted ones of [§6](05-dates-and-time.md#the-format-vocabulary) draws one codeless notification, whatever the kind; an absent format is the kind's default.
  - A DateRange `(format, separator)` pair outside the eight of [§6 §8.1](05-dates-and-time.md#81-declaration-and-stored-text) draws another, the separator defaulting to `/` and a missing format counting as outside, so `yyyy-MM-dd` alone is admitted and `dd.MM.yyyy` alone refused.
  - A partial `datePrecision` on a Date whose format, `yyyy-MM-dd` when absent, is not a complete pure date draws `MVK_OPTIONAL_DATE_TYPE_INVALID`, beside `MVK_ADDITIONAL_CHECK_INVALID` when the pre-1900 check also fails; that check on a yearless Date or DateFragment format draws `MVK_ADDITIONAL_CHECK_INVALID`.
  - A DateRange is judged on the format the Kernel composes as format, separator, format, an omitted format composing as the text `null` and an omitted separator as `/`. A composite that is empty after Java's `String.trim`, such as a blank format beside an empty or blank separator, draws `MVK_FORMAT_DATE_RANGE_MISSING` alone; an omitted format draws the invalid-format notification; and a separator other than `-` or `/` after trimming also draws the separator notification, while the pair allowlist reads the separator untrimmed. A supplementary character in either member draws the repertoire notification alone.
  - The temporal bodies' load and build failures are in [§1.2](#defects-that-leave-no-model).
- **`UnspecifiedType`** draws `MVK_UNSPECIFIED_TYPE_NO_CODEGEN`, with or without a body.
- **Boolean and Confirm** bodies draw nothing.

#### Enumeration declarations

**An Enumeration declaration's laws read every value, label and category token after Java's `String.trim`, and a text carrying a supplementary character draws the repertoire notification in place of every coded class it would draw, the `sValue` included.** So `o\t` is admitted and `BASIC` beside `BASIC\t` draws `MVK_INTERNAL_VALUES_DUPLICATE`, while the charset check, a constant comparison and an index key read the text as written. Block 6 below is the exception to the trim: it compares stored values as written, so `BASIC` beside `BASIC\t` draws no block-6 notification. The repertoire substitution does not apply to notification blocks 1 and 6 below. An empty value is admitted.

- **Labels.** A label counts only for a declared locale, and a value carries labels when it has one that counts. When some values carry labels and others do not, `MVK_COUNT_OF_VALUES_INVALID` is drawn once per declared locale. When a carrying value lacks a text, or has a blank one, for some declared locale, `MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES` is drawn once. Each text two values share in one declared locale draws `MVK_DISPLAY_VALUES_DUPLICATE`, case-sensitively.
- **Separators.** A tab or `|` draws `MVK_INTERNAL_VALUE_INVALID` per distinct value, `MVK_DISPLAY_VALUE_INVALID` per distinct counted label text and `MVK_CATEGORY_VALUE_INVALID` per distinct category token. A line feed or carriage return in any of them draws one codeless notification for the field instead, that text drawing no tab class.
- **S-value.** An `sValue` that is not empty after Java's `String.trim` and equals no value so trimmed, case-sensitively, draws `MVK_S_VALUE_INVALID`: `" BASIC"` names `BASIC`, while a lone no-break space and `basic` name nothing. The runtime stages the default as written, so a padded `sValue` lands as text no value carries.
- **Category arity.** A category's token list must have exactly as many entries as the Enumeration has values; equal cardinality is the whole rule. A shorter list draws `MVK_MISSING_CATEGORY_VALUE`, once per unclassified value, so an empty list draws it once per value rather than once for the declaration. A longer list draws `MVK_MISSING_INTERNAL_VALUE` once per surplus token, so two surplus tokens draw it twice. Same-length tokens **disjoint** from the Enumeration's own values are admitted, which separates positional pairing from any set-membership reading, and a same-length reordering is admitted too. Repeated category tokens are admitted. Every value therefore has exactly one category token. A second category is judged independently of the first, and a body carrying no `categories` member is admitted. An Enumeration with no value, a [build failure](#defects-that-leave-no-model), raises no arity class. How a category is read at runtime is [§8 B.2](06-strings-and-enumerations.md#b2-categories-via--)'s.

**An Enumeration field's declaration check collects its notifications rather than stopping at the first, so order and multiplicity are observable.** Every notification is an ERROR, and they arrive in six blocks, in this order:

| Block | Notifications |
|---|---|
| 1 | Only under a restricted `supportedCharacters` list: one `MVK_ENUM_VALUE_WITH_INVALID_CHARACTER` per rejected UTF-16 code unit of each stored value, one per rejected index. |
| 2 | One codeless supplementary-plane notification for the whole field when any stored value or display label holds a supplementary-plane scalar, under every charset; BMP non-ASCII text does not raise it. |
| 3 | The category arity classes, every category's `MVK_MISSING_CATEGORY_VALUE` notifications ahead of every category's `MVK_MISSING_INTERNAL_VALUE` notifications, whatever the category order. |
| 4 | One `MVK_CATEGORY_VALUE_DUPLICATE` per repeated stored value and category. |
| 5 | One `MVK_INTERNAL_VALUES_DUPLICATE` per repeated stored value. |
| 6 | One codeless repeated-value notification per repeated stored value. |

- **A stored value holding a supplementary-plane scalar.** In block 1 its high surrogate is rejected even under a range numerically covering it, and its low surrogate is judged alone, rejected unless a declared range numerically covers it: under `A-Z` the scalar counts as two, under `U+0020–U+FFFD` as one, and two scalars sharing a high surrogate in one value under that range count once, while two values sharing it count once each. The one model measured declaring a supplementary range does not build. In block 3 such a value draws no shortfall notification, although its position still counts toward the arity; blocks 4 and 5 skip it, and block 6 does not.
- **Identical notifications collapse:** the same rejected unit twice in one value, or the same surplus token twice in one category, counts once, while equal notifications from different categories stay separate.
- The order of categories or values inside blocks 3 and 4 is not observable through class codes and is not stated.

#### Names, groups and texts

**A declared name's alphabet is the carrier's, and it is not one law.** Every name is judged after Java's `String.trim`. Five of thirteen name shapes answer differently on a **field** than on a **group**, and neither carrier is simply the stricter one:

| Name shape | Root group | Nested group | Field |
|---|---|---|---|
| leading underscore (`_Orders`, `_Slots`) | admitted | `NAME_STARTS_WITH_UNDERSCORE_AND_WRONG_PATTERN`, the prefix being reserved for `__meta` and `__attachment_meta*` | admitted |
| `ä`, `ö` or `ß` inside or trailing (`Teilä`, `Slöts`, `Codeß`, `Codeä`) | admitted | admitted | refused |
| `ä` or `ß` leading (`äCode`, `ßCode`) | admitted | `MVK_PATH_INVALID` | refused |
| `Ö` leading (`Ördner`) | admitted | unmeasured | unmeasured |
| `é`, `中` or the Arabic-Indic digit `١`, leading or inside (`Codeé`) | `MVK_PATH_INVALID` | `MVK_PATH_INVALID` | `MVK_PATH_INVALID` |
| 61 characters | refused, codeless | refused, codeless | admitted |
| `.` or `:`, a leading colon included (`:Code`) | `MVK_PATH_INVALID` alone | `MVK_PATH_INVALID` alone | `MVK_NAME_INVALID_DOT_COLON_A12_DV` |
| a dot followed by a digit, an underscore, another dot or nothing (`Co.1de`, `Co._de`, `Co..de`, `Co.`) | `MVK_PATH_INVALID` alone | `MVK_PATH_INVALID` alone | `MVK_PATH_INVALID` alone |
| digit-initial | `MVK_NAME_STARTS_WITH_DIGIT`, no path class | `MVK_PATH_INVALID`, no name class | `MVK_PATH_INVALID` and `MVK_NAME_STARTS_WITH_DIGIT_A12_DV` |
| `xml`, `XML` or `Xml` prefix | `MVK_NAME_STARTS_WITH_XML` | `MVK_NAME_STARTS_WITH_XML` | `MVK_NAME_STARTS_WITH_XML_A12_DV` |
| `/` inside an otherwise legal name | `MVK_PATHS_INCONSISTENT` | `MVK_PATHS_INCONSISTENT` | `MVK_PATHS_INCONSISTENT` |
| `/` beside a refused path character (`Co/-de`, `-Co/de`) | `MVK_PATH_INVALID` | `MVK_PATH_INVALID` | `MVK_PATH_INVALID` |

- **Carrier rules read off the table.** On a root or nested group all seven measured dot and colon spellings draw `MVK_PATH_INVALID` alone. The group's non-ASCII allowance is not "any non-ASCII letter": that it is exactly the German umlauts and `ß` its name pattern names is source reading, with `ü`, `Ä` and `Ü` unmeasured. The 60-character limit is the group's alone. One carrier's measured law does not transfer to another: applying it refuses legal models.
- **The code moves with the carrier.** A field answers a second validator the group's name never reaches, so its name classes carry the `_A12_DV` suffix, where both group carriers answer with the unsuffixed spellings. Whether a *name* class fires at all splits root from nested, as the digit-initial row shows.
- **A `/` inside an otherwise legal name answers alike everywhere** because it makes the element's own path disagree with the tree rather than being a bad name.
- **A refused path character withholds the carrier's name classes:** `1Codeé`, `xmlCodeé` and `_Codeé` draw `MVK_PATH_INVALID` alone on every carrier, where a field's `1Co.de`, whose dot is not in a refused position, keeps `MVK_PATH_INVALID`, `MVK_NAME_INVALID_DOT_COLON_A12_DV` and `MVK_NAME_STARTS_WITH_DIGIT_A12_DV` together.
- **Codeless notifications.** Where `MVK_PATH_INVALID` is a name's only named class, a codeless notification stands beside it in the whole-model report, except on a root group's `Co/-de`, and none stands beside a field's digit-initial pair; the stage that raises it is not established.
- **A refused group name reaches everything beneath it.** A refused nested or root group name draws `MVK_PATH_INVALID` once, at the group, and its group-path codeless notification at the group and at every element beneath it, nested groups included; a nested name longer than 60 characters draws only that notification, the same way. The elements beneath keep their own codeless name notification, their `_A12_DV` name classes and their type classes, while their own path class and the group `xml` class are not drawn; a field whose own name draws the path class draws no type class. Rules and computations beneath a refused group receive its group-path notification as fields do. A root group draws its own shape notification where a nested group draws the group-path one, and its own notification above 60 characters. Because names are trimmed, a padded group name draws its classes but hands no group-path notification to its own fields, and a root name draws one shape or length notification per value.
- **Reserved words.** The underscore reservation is the exact name `__meta` and any name beginning `__attachment_meta`; the value word ends a dotted field name in any case, `value` in English and `Wert` in German.
- **A rule's name** that is digit-initial or dotted produces a codeless consistency notification; an empty rule name prevents model construction ([§1.2](#defects-that-leave-no-model)). An `xml` prefix on a rule is admitted. A computation's name: [§3.3](#33-member-texts-of-rules-and-computations).
- **A computed field's path.** A computed field whose path holds a dot or a colon, from its own name or from a group above it, draws `MVK_ERROR_INVALID_FIELDNAME` at the computation, after the computation's condition, target and index gates; the computed path meets the condition lexer first, so a character the lexer has no terminal for draws `MVK_LEXER_STANDARD_ERROR` there alone.
- **Groups.** An empty group, fixed, repeatable or root, draws nothing. A group's repeatability classes are [§1](#repeatability)'s.

#### Index and sort nomination admission

**A nomination is bound against the model as authored and judged against the variant it runs in.** An index nomination and a sort nomination answer alike, each under its own class:

| Nominated name | Class |
|---|---|
| resolves nowhere in the authored model, a relative `../Key` whose parent field is absent included | the build fails with no class |
| the group's direct child field of that short name in the default variant is filtered `ONLY` or physically absent | `MVK_INVALID_INDEX_FIELD`; `MVK_INVALID_SORT_FIELD` for a sort nomination |
| that direct child field has value validation off | `MVK_INDEX_FIELD_NO_VALUE_VALIDATION`; `MVK_SORT_FIELD_NO_VALUE_VALIDATION` for a sort nomination |
| its kept short name fails the field-name alphabet | a codeless notification at the group |

- **The local declaration decides, not the referent's.** With `Items` nominating `../Key`, the local `Key` is asked; the parent's `Key` filtered `ONLY` or with value validation off changes nothing. Of two local fields both named `Key` the surviving one is asked, and with both filtered the nomination draws the invalid class. `ALL_EXCEPT` keeps the field, as it does everywhere.
- **The alphabet gate reads the kept short name:** `../Items/Sku` draws nothing, and `Sk-u` draws the notification whether or not a field of that name exists. Only the three sort entries the model holds are judged.
- **An index nomination of a field filtered `ONLY`** draws `MVK_INVALID_INDEX_FIELD` on the root group too, where no sort nomination is measured.
- **The ordering gates are withheld whenever the model's entity walk refused anything:** the invalid and no-value-validation classes of either nomination are withheld then (measured beside a refused path and beside a count below one), while `MVK_SORT_FIELD_DUPLICATE` skips only a refused name.
- **Every sort nomination is judged.** Two disqualified sort fields draw two classes, and an invalid nomination does not stop the later ones. Each distinct name reports its own class once over the whole list, and a field named more than once among the **first three** entries also draws `MVK_SORT_FIELD_DUPLICATE`, once however often it repeats, beside its own class.
- **The sort list holds at most three entries.** Every entry beyond the third draws its own codeless capacity notification whatever it names; a fourth entry repeating an earlier one draws no duplicate class, and an unresolved fourth still draws its own class.
- **A non-empty `sortFields` on a non-repeatable group**, root included, draws `MVK_INVALID_SORTINFO`.

Sources: [field declaration notifications checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-field-declaration-notifications-k17), [Enumeration declaration notifications checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-enumeration-declaration-notifications), [declaration report withholding checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14), [sort list capacity checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity), [executable declaration admission checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-executable-declaration-admission), [parameter token versus group declaration alphabet checkpoint](../docs/sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet), [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [inbound 2026-09-26n field message gates](../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates), [inbound 2026-09-27a element paths](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-element-paths), [inbound 2026-09-27a index and sort lookup](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13), [inbound 2026-10-18](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-24a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-24a).

### 1.4 Variant filters, and where a filtered declaration is seen

**A declaration can be filtered out of the model before code generation, its static checks and evaluation see it, and this conditions every other statement in this set.** A Field, a Rule, and a Computation — those three carriers and no group carrier — may each carry an optional `variantFilter`, serialized `{ "filterType": "ONLY" | "ALL_EXCEPT", "variants": [<names>] }`. Conversion into the checked model keeps a declaration only while the filter accepts it: an absent filter accepts, `ONLY` accepts when the active variant is named, and `ALL_EXCEPT` accepts when it is not. **At the default variant nothing is named**, so the membership test is false for every list — including an empty list, the empty-string name, and an absent `variants` member — and the filter *type* alone decides: `ONLY` rejects, `ALL_EXCEPT` accepts. A rejected declaration is not disabled or flagged; it is **absent** from the model that code generation, its static checks and evaluation then see. **It is still present where the Kernel reads the model as authored**, the stages of [§1.2](#12-model-consistency-rules):

| Stage or check | A declaration filtered `ONLY` at the default variant |
|---|---|
| reading and member binding | read and bound, so every filtered declaration keeps its member binding ([§1.1](#member-binding)) |
| building | per defect, in [the build table](#defects-that-leave-no-model) |
| index and sort nomination binding | takes part ([§1.3](#index-and-sort-nomination-admission)) |
| consistency rules 1–4 and 6 | seen: id uniqueness, the Number value limits, the group shapes; a field keeps the codeless refusal of a Number `maxValue` beyond the value limit and of a duplicated enumeration value, and a rule keeps the empty-code notification of [§3.3](#33-member-texts-of-rules-and-computations) |
| consistency rule 5 | absent: none of the [§1.3](#13-declaration-generation-classes) classes and none of the [§1](#type-member-ranges) member-range notifications. Measured members lost: `MVK_INTERNAL_VALUES_DUPLICATE`, `MVK_CATEGORY_VALUE_DUPLICATE`, `MVK_PATTERN_INVALID`, `MVK_FRACT_DIGITS_INVALID`, the codeless refusal of a fifteen-digit fraction, and every other measured field-declaration class |
| code generation, its static checks, evaluation | absent |

**The consequence splits by carrier, in opposite directions, so neither arm may be inferred from the other.**

- A rejected **rule or computation** is simply not there: it is not checked, emits no code, and never evaluates, so a declaration with a deliberately unresolvable condition is reported **clean**, and so is a rule under `ONLY ["premium"]` whose message carries a supplementary character.
- A rejected **field** is absent from its group, so every surviving declaration that names it is naming something undeclared — a condition mentioning it draws `MVK_INVALID_ENTITY`, and targeting it draws the error-target pair `MVK_ERROR_FIELD_MISSING` with `MVK_MISSING_ERROR_FIELD` instead ([§3.1](#the-error-fields-declaration)), the answer following the naming *role*.
- **A clean static verdict is therefore not a clean bill of health for a declaration carrying `ONLY`**, and a consumer that resolves references against every declared field under-reports against A12.

Measured scope: the omission consequence on all three carriers with unfiltered and `ALL_EXCEPT` controls; the stage rows on one flat root group and the binding rows on a repeatable group beneath it. Nested declarations, type-definition bodies and notification order are unmeasured, and a check not listed above follows the authored-versus-filtered split of [§1.2](#12-model-consistency-rules) unmeasured.

Sources: [variant filter omission checkpoint](../docs/sources/static-admission-and-class-probes.md#src-variant-filter-declaration-omission), [inbound 2026-09-27a variant filter stages](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-variant-filter-stages), [inbound 2026-09-26m model texts](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-model-texts), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), a12-dmkits `KF299`, `KF305` and `FieldVariantStageLawsTest` at `69497f567` (no local record).

---

## 2. Document = an instance of the tree

A **document** instantiates the model: repeatable groups are expanded into concrete rows, and fields hold **values** or are **empty**. A field is not just "value or empty" — recall the **three cell states** ([§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty)):

- **empty** — no evaluation value (whether the field placement is absent or present-empty),
- **filled** — a well-formed value of the field's type,
- **not-check-relevant** — the cell carries a formal finding from one of the producers of [§3 B.3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state), such as a formally invalid value; it need not hold a value. Non-relevance under partial validation is not a cell state.

**A cell's physical placement and its evaluation state are separate dimensions.** At the in-memory evaluation-ingestion boundary, an omitted field cell is **absent**; a present field cell whose stored content is `null` or the empty text `""` is **present-empty**; and a present cell with nonempty text proceeds through parsing and formal checking to become either filled or not-check-relevant. Classifying a placed `""` as empty supplies no semantic String value but does not erase that placement or rewrite the document's stored input. A nonempty value that cannot be converted likewise remains physically present with its exact stored text and becomes not-check-relevant; conversion failure never drops the placement or substitutes absence. Field-level fill predicates, fill quantifiers, and requiredness therefore treat absent and present-empty alike as unfilled, while placement-sensitive read-back and application may distinguish them ([§4.3](#43-the-compute--apply--validate-flow)). Non-repeatable group content follows descendant evaluation values, whereas an explicitly instantiated repeatable row remains structural content even when all its field cells are present-empty ([§9](07-repetition-and-iteration.md#5-groupfilled-and-the-other-repetition-rules)).

**Where a stored Number's scale comes from.** Rules below distinguish decimal values that have the same amount but different stored scale—most visibly the scale-sensitive computation change test in [§11](09-computations.md#33-what-compute-reports). That coefficient-and-scale identity, a negative scale such as `1E+5` included, is an input at this boundary, fixed when the host constructs the in-memory document; it is not reconstructed by evaluation. A host that first parses a decimal through binary floating point can therefore change `250.00` into scale-1 `250.0`, or lose digits from a large decimal, and silently change later results. Persistence remains outside this account, but the host must deliver the decimal amount and authored scale intact. The same decimal model has no negative zero, so an ingested `-0.0` has the identity of `0.0`.

A **cell** is *the value (or empty/invalid) of one field at one repetition context*. A non-repeated field has exactly one cell per document; a field inside a repeatable group has one cell per row (and, under nested repetition, one per combination of enclosing row indices).

Sources: a12-dmkits `PublicInterpreterApiTest` (negative-scale source identity; no local record).

### 2.1 Repetition contexts (the iteration environment)

**Addressing a cell requires knowing which row it occupies at each repeatable level.** Call that a **repetition context** (the kernel's `Kontext`/`Kontextnummer`): a mapping from each enclosing repeatable group to a row index.

```
LineItem[1]/Discount[2]/Pct         -- the Pct cell in the first LineItem's second Discount row
```

Concrete repetition indices are **1-based**, and an omitted bracket means repetition `1`. The example spells `[1]` for clarity; the canonical exact-pointer string omits it and has no leading slash, so `LineItem/Discount[2]/Pct` addresses the same cell. A leading slash is accepted as redundant input. A zero-part exact pointer is legal and denotes the document root; its canonical string is empty, while the kernel's diagnostic display names it `(empty DocumentPointer)`.

This is the single most important runtime structure to model well, because *iteration is the act of producing these contexts* and *path resolution is the act of reading a cell relative to one* ([§9](07-repetition-and-iteration.md), [§10](08-paths-and-references.md)).

#### The repetition slot vocabulary

**The repetition slot is an A12-owned vocabulary rather than one unrestricted integer.** Its complete `IIdentifier` domain is: `>= 1` for a concrete repetition (`1` at a non-repeatable level), `0` = `ALL_INDICES`, `-1` = `ITERATION`, `-2` = `USB_NOT_SPECIFIED`, `-4` = `SEMANTIC_INDEX`, `-5` = `UNKNOWN`, `-6` = `PARALLEL_ITERATION`, and `-7` = the `RepetitionNotUnique` replacement marker. `0` and the negative values do not have one meaning at every API boundary:

| owner | admitted repetition slot | meaning of `0` |
|---|---|---|
| exact `DocumentPointer` | every part is `>= 1`, except that the last part may be `0` | the last part's `RepetitionsV2` slot, its repetitions container in the host document, not a wildcard; whether such a pointer reaches evaluation or a message is not stated |
| `DocumentMultiPointer` | `>= 0` at every part | all repetitions at that level |
| `IIdentifier` used for relevant sets and meta pointers | the complete vocabulary above | `ALL_INDICES`, the authored asterisk |
| message `PartiallyKnownDocumentMultiPointer` | `>= 1`, `0`, or `UNKNOWN` (`-5`) at every level | all repetitions at that level |

The negative `IIdentifier` values are principally kernel-produced planning or result markers, not caller-authored row coordinates. Of them, `UNKNOWN` is the observable message coordinate for a semantic-index no-match or an unmatched parallel-iteration side ([§10 §4.3](08-paths-and-references.md#43-selected-references-in-validation-messages), [§9 §2](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key)); `SEMANTIC_INDEX`, `PARALLEL_ITERATION`, and the `RepetitionNotUnique` marker remain plan-internal. An implementation must not put the whole vocabulary into the exact-pointer type.

#### Message addresses

**Every runtime message address uses the distinct `PartiallyKnownDocumentMultiPointer`.** Its state is a name string plus a repetition-index list, not exact `PathPart` values; it may carry a wildcard or `UNKNOWN` at any level and therefore converts only partially to exact or wildcard pointers:

- Conversion to an exact `DocumentPointer` succeeds only when every coordinate before the last is concrete and positive, the last is nonnegative, the name/index arity matches, and every name is nonempty. A wildcard above the last level, `UNKNOWN`, or a name that exact `PathPart` cannot represent yields no exact pointer in production.
- Conversion to `DocumentMultiPointer` succeeds when every coordinate is nonnegative; any `UNKNOWN` prevents it.
- The message-pointer type has no A12 textual parser or renderer of its own; its `fullName()` and repetition list are accessors, not a serialization contract.

#### The host pointer API

These rules bind an implementation that reproduces the kernel's pointer API.

- **Value and string codec have different name domains.** A `PathPart` requires only a nonempty name and a nonnegative index; names such as `a/b`, `Order$`, `Order Item`, and `Order[2]` are legal part values. The part-list `DocumentPointer` factory adds the exact-pointer position rule but no string grammar. Only the string entry point applies its per-part `([\w_-]+)(\[(\d+)?\])?` grammar, because a written pointer must parse back to the same value. Hoisting the codec grammar onto value construction would reject legal A12 values on the read path.
- **`fullName()` is not the canonical pointer codec:** it joins part names with leading slashes, omits indices, and returns `""` at the exact root, while the canonical exact-pointer string is slashless and carries every non-`1` index.
- **The message root and the raw factory.** The zero-part message root is constructible and has `fullName() = "/"`, but its exact conversion raises rather than returning the exact root. The raw message factory does not enforce name/index arity, so a mismatched value can exist even though it has no well-formed exact counterpart.

> **Non-normative implementation note.** Represent a repetition context explicitly, e.g. `Env := List (RepeatableLevel × RowIndex)` (an association from each enclosing repeatable group to its chosen row), and make `eval` take it as a parameter: `eval : Ast → Env → Document → …`. Iteration extends `Env`; a bare relative path reads against the current `Env`; a `*` in a path *re-opens* iteration at that level (binding all rows); `$` correlates back to the outer `Env`. Trying to smuggle positions through implicit indices is the classic way the star-binding rules ([§9](07-repetition-and-iteration.md)) come out wrong.

### 2.2 Over-repetition and phantom rows

**A row the document instantiates beyond its group's declared `repeatability` is a formal error on that row**, a VALUE error. Its codes are `zuGrosseZeile` / `zuGrosseKontextnummer`, or `zuGrosseLfdNummer` throughout when the violated group is a repeatable root group. This address-formal gate runs before scalar conversion, suppresses that row's ordinary checks and those of everything the document writes beneath it, and leaves the immutable physical row instantiated. [§3 B.3](02-logic-and-formal-errors.md#over-repetition) owns the finding set, the code by position, nested absorption and the partial-validation exception; [§9 §4.3](07-repetition-and-iteration.md#43-capacity-rows-beyond-the-declared-repeatability) owns how operands treat the row.

**Evaluation can visit a coordinate the document does not instantiate, in two distinct ways:**

- **Full validation's rule iteration domain** traverses declared slots in a small declared space and anchors a uniterated error-path level at row `1`, so a rule can fire and report at a coordinate holding no stored row ([§9 §1.1](07-repetition-and-iteration.md#11-iteration-scope), [§9 §1.3](07-repetition-and-iteration.md#13-evaluation-domains)).
- **A phantom row** is the partial-validation notion only: a row the relevant set names that does not physically exist is still evaluated ([§12 §5.2](10-validation-and-polarity.md#52-which-rules-run-and-where)). Full validation has no relevant set and so no phantom row.

### 2.3 Reading a document from JSON

**Runtime evaluation uses the V2-effective repetition structure.** A mutable V1 document may contain only a placement at repetition `n`, but validation and computation first convert it to immutable V2. That conversion creates missing ancestors and pads repetitions `1..n-1` with empty group instances, scoped independently under each concrete parent. Those padded repeatable rows are instantiated content and participate in per-row iteration exactly like explicitly created empty rows.

**This is not an alternative sparse JSON encoding: every object in a canonical Document JSON array is explicit, including `{}`.** At the Kernel Document JSON conversion boundary:

- **Non-object array elements** (including `null`, scalars and nested arrays) are discarded before surviving objects receive consecutive coordinates. A null prefix therefore does not create predecessor rows or preserve the original JSON index; an explicit empty object does. This normalization applies independently within each surviving parent. It is separate from field-valued `null`, which remains present-empty.
- **A member the model declares nothing for is dropped**, leaving no cell, no group and no validation finding, so a document carrying it validates exactly as the one without. Measured members: an undeclared string or object member of a fixed group; an undeclared string key inside a repeatable row; a boolean, `null`, number or array member of a fixed group; an object in a nested fixed group or inside a row; a string beside the root group. Unmeasured: an undeclared boolean, `null`, number or array member inside a row; an undeclared member of any kind other than a string at the document root; any notification the conversion raises for a dropped member.
- **A declared member whose JSON shape does not fit its declaration** (an object where a repeatable group is declared, an array where a fixed group is declared, an object or array where a field is declared) is not stated.
- **An unquoted document value must be a JSON number.** `abc`, `True`, `NaN`, `0x10`, `01`, `1.`, `.5` or `+1` leaves the whole document unread, while `-0`, `1E1` and `5` are read.
- **A native decimal number keeps its coefficient and signed decimal scale, trailing fractional zeros included.** Before field conversion the reader derives canonical decimal-node text: plain notation when the scale is nonnegative and the adjusted exponent (coefficient digit count minus one minus scale, counting zero as one digit) is at least −6; scientific notation otherwise. Thus native `10.50` supplies `10.50`, `1e3` supplies `1E+3`, and `0.0000001` supplies `1E-7`. A Number destination converts that text to its exact decimal identity; a String destination retains the node text. Quoted scalar text bypasses numeric-node formatting. Re-serializing a native negative-scale number in plain notation before ingestion changes its source identity even when its amount is unchanged. How quoted text reaching a Number destination converts is [§5](04-numbers-and-decimals.md#document-ingestion)'s.

Sources: [conversion checkpoint](../docs/sources/evaluation-and-application-routes.md#src-json-row-normalization), [undeclared-member checkpoint](../docs/sources/domain-ingestion-probes.md#src-undeclared-document-members), [inbound 2026-10-23](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-23) (KF1), [Number wire ingestion route](../docs/sources/cross-layer-routes.md#src-number-wire-ingestion), [Number ingress checkpoint](../docs/sources/domain-ingestion-probes.md#src-number-ingress-k16), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21).

---

## 3. Rules and computations

A model carries two families of behaviour, both written in the one shared language ([`12-concrete-syntax.md`](12-concrete-syntax.md)). Either declaration may be filtered out of the checked model by its `variantFilter`, with the opposite consequences for rules and fields that [§1.4](#14-variant-filters-and-where-a-filtered-declaration-is-seen) states.

### 3.1 Rules (validation)

A **rule** has:

- an **error condition** — the single condition slot; **TRUE means the data is invalid** (fixed polarity — there is no assertion form; [`SEMANTICS-MAP §1.3`](SEMANTICS-MAP.md#13-a-rule-states-the-error--and-that-polarity-is-fixed-));
- an **error field** — where a fired message attaches. It must be in the condition's reference set of [§9 §1.4](07-repetition-and-iteration.md#14-the-reference-set), which is the one owner of what that set contains, or the model is rejected `MVK_ERROR_FIELD_NOT_REFERENCED`; and it must inhabit a scope compatible with the condition's iteration, by the gates of [§9 §1.5](07-repetition-and-iteration.md#15-error-field-admission);
- **message metadata** — severity (ERROR/WARNING/INFO) and authored error text (with interpolation, [§13](11-messages-and-custom.md));
- a **name**, which may not begin with the engine-reserved prefix `VK_`. The check is case-**insensitive**, so `VK_x`, `Vk_x`, and `vk_x` are all rejected with `MVK_RULE_NAME_INVALID`; an implementation that compares the prefix case-sensitively admits models the kernel refuses. The name's and the error code's content laws are [§3.3](#33-member-texts-of-rules-and-computations)'s.

#### The error field's declaration

**The error field's declaration is checked before the condition's grammar.** The Kernel resolves the rule's error entity and refuses a null one (`MVK_MISSING_ERROR_FIELD`) before it parses the condition at all, so a rule with no usable error field reports that class and none of the syntax classes its condition would otherwise draw.

- **The error-target pair.** A declared relative path that resolves to nothing lands in the same class, beside `MVK_ERROR_FIELD_MISSING`, the pair a blank path also draws ([§3.3](#33-member-texts-of-rules-and-computations)). `MVK_ERROR_FIELD_NOT_VALID` is the narrower state of an error entity that resolves but is absent from the model's entity container, and it — unlike the missing class — is suppressed under a lenient parse.
- **What the failed target withholds.** The failed target withholds the message's error-text classes too, `RULE_HAS_NO_ERRORTEXT` included, exactly as a refused condition does ([§13 A.2](11-messages-and-custom.md#a2-which-error-text-classes-a-refused-declaration-withholds)). A reserved rule name's `MVK_RULE_NAME_INVALID`, a blank code's `MVK_ERROR_CODE_MISSING` and a missing or blank text's `MVK_ERROR_MESSAGE_MISSING` are reported beside the pair, and so is `MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING` when one of two declared locales has a text.
- **A target naming a group is an ordinary declared entity:** with `../Items` as target and a condition reading only `Value`, the rule draws `MVK_ERROR_FIELD_NOT_REFERENCED`, which withholds the error text and gives way to an unresolved name.

**The declared path climbs from the rule element and takes `..` lexically.** From a rule in `/Order`, `../Code` names `/Order/Code`, while `Code` names a child of the rule element and draws `MVK_ERROR_FIELD_MISSING` with `MVK_MISSING_ERROR_FIELD`. An up-step after a named segment is admitted, `../Meta/../Code` naming `/Order/Code`, where a condition reference refuses it as a token. Under a condition naming no group, a path landing on a group draws `MVK_ERROR_FIELD_NOT_REFERENCED` (`../Meta`, `../Meta/Ref/..`), except on the group the rule is declared in, where the model fails to build and no class is reported, by whichever spelling reaches it (`../Code/..`, `../../Order`); to a rule declared in `/Order/Meta` the root is an ordinary group (`../..`). A computation target naming a group is in [the build table](#defects-that-leave-no-model).

#### The message and its two pointer channels

**Firing a rule against a repetition context yields either *no message* or a message.** The message carries the error field's `PartiallyKnownDocumentMultiPointer`, the severity, the computed **message type** (VALUE/OMISSION, [§12](10-validation-and-polarity.md)), the interpolated text, and two structured sets of the same message-pointer type. `referenced` reports the condition operands associated with the firing. For an OMISSION, `fillToFix` reports the kernel's omission-responsibility projection, which need not be a minimal set of empty cells whose literal filling alone repairs the rule; a VALUE message has no fill-to-fix pointers. An operator may define a more specific projection, such as the complete duplicate-peer expansion of [`RepetitionNotUnique`](07-repetition-and-iteration.md#6-repetitionnotunique-precisely-). These channels are sets, so no pointer order is specified. A partially known message address is not an exact pointer with a wider integer slot: wildcard/`UNKNOWN` coordinates and partial exact conversion are part of its type ([§2.1](#message-addresses)).

**Ordinary `referenced` pointers are a structural projection of the checked condition, not a trace of the values read during evaluation.** A later `FirstFilledValue` fallback stays referenced even when an earlier operand determined the value. An operator with its own projection, such as `RepetitionNotUnique`, may depend on the document instead.

**What `referenced` contains.**

- A starred *field* retains wildcard `0` at its reopened group context.
- An ordinary non-root *group* operand of either repetition shape expands recursively to its descendant field pointers rather than yielding a group pointer. The relation is identical in the single-operand presence, entity-list quantifier, and numeric filled-count positions, and it is what lets an error field inside the operand group satisfy the reference gate indirectly in all three.
- Positive root-group presence (`GroupFilled` or `AtLeastOneGroupFilled` over the root) contributes no fields to either channel.
- `Having` field operands and the selected starred value field are included; an unmarked candidate reference is wildcarded, while a `$` reference resolves at its concrete captured outer row.
- `CurrentRepetition` contributes no field pointer, and neither does a form that names no field: a literal, `True`, `False`, `Today`, `Now` or `BaseYear`.
- [The computation's implicit message](09-computations.md#6-the-implicit-validation-rule-precisely) carries each operand's own reach plus the computed target, with its own exact `fillToFix` projection.

<a id="fill-to-fix-classes"></a>
**What `fillToFix` contains: each operator contributes by one class, and [column O of the operator reference](14-operator-reference.md#fill-to-fix-contribution) assigns each operator its class.** The omission-responsibility inventory is narrower than the referenced inventory:

| Class | Contribution to `fillToFix` |
|---|---|
| `ordinary` | the pointers the operator contributes to `referenced` |
| `presence withheld` | none of its ordinary operands; its filter operands remain eligible |
| `upward count` | when exactly one comparison side contains such a count and the comparison asks that side to be larger (`>` or `>=`, including the mirrored form), neither comparison side contributes ordinary omission-responsible operands; the downward and equality comparisons keep both sides |
| `own projection` | the projection its own clause defines |
| `no field` | nothing, as in `referenced` |

Filter references are collected separately even inside a pruned comparison. Thus `NumberOfFilledFields(A, B) > [Limit]` contributes neither `A`, `B` nor `Limit`, while the corresponding downward and equality comparisons keep both sides. These sets are selected structurally, independently of which cells are currently filled. A connective contributes the union of its branches.

Measured scope: presence-only operands excluded, an upward count comparison excluded on both sides with its filter operands retained, positive root-group presence contributing no fields, and the `NumberOfFilledFields` rows above. The `presence withheld` and `upward count` members are the closed lists column O names; that every other operator is `ordinary` and that a connective unions its branches are unmeasured.

#### Address coordinates

**A message's `referenced` and `fillToFix` entries are partially-known addresses, and one message routinely carries both kinds.** Each is a path plus one coordinate per path part.

**One rule decides a level's coordinate: whether the rule's own iteration bound that level.** A part carries its concrete **1-based** row wherever the rule's iteration bound that level, and every non-repeatable part carries `1`; a repeatable level the iteration left **unbound** carries `0` instead, and one address may carry several. So `0` marks an unbound iterated level and is not row zero: an address is byte-identical across documents holding two rows, two rows, and no rows at all. It is not decided by whether the operand was starred, expanded from a group, or deeper than the anchor: a fixed unstarred group operand reaching through a repeatable descendant produces the same address as a starred field's, a group expanding to non-repeatable fields only leaves nothing unbound, and two references inside a single `Having` differ by nothing but the `$` capture. One exception: beneath a starred group's star, every reopened group-context part is wildcarded, **including a non-repeatable descendant group context**.

Consequences for group operands, by **one depth rule**: a repeatable level *above* the operand stays concrete at the firing row, and every repeatable level *at or below* it is wildcarded.

- For a starred group that boundary is its own star.
- For an unstarred group the boundary is the operand's own group, which the wildcard gate keeps non-repeatable, so the wildcarding begins at the first repeatable level inside the subtree: `/Shipment/Carrier` reaches `/Shipment[1]/Carrier[1]/Handoffs[0]/Site` beside `/Shipment[1]/Carrier[1]/Name`.
- The two forms therefore differ in **where** that boundary falls, not in whether one wildcards at all, and the expansion's wildcarded address is a different address of the same firing from the message's own anchor, which stays concrete throughout ([§9](07-repetition-and-iteration.md)).
- With a `max 2` repeatable ancestor above a fixed group operand, one document fires the rule twice and each firing's expansion carries that ancestor's own row — `/Probe[1]/Outer[1]/Flat[1]/Rows[0]/RowR` beside `/Probe[1]/Outer[2]/Flat[1]/Rows[0]/RowR` — while the wildcarding still begins at the first repeatable level inside the operand's subtree.

Measured scope: the at-or-below half on both forms; the concrete half on the **unstarred** form only, the **starred** form's concrete half being stated from the rule rather than from a witness.

**An address therefore either names exactly one cell or does not**, and a consumer must represent both kinds rather than one shape with an optional index — but it cannot recover the authored operand form from the address, which has to come from the checked condition.

**A12 owns a canonical string only for the exact form** — slashless, repetition one elided, as [§2.1](#21-repetition-contexts-the-iteration-environment) states — and defines neither parser nor renderer for the partially-known one. An observer that prints both kinds therefore chooses its own second form, and two differently-spelled addresses in one artifact may be that choice rather than anything the engine emitted; read the coordinates, not the spelling. The rendered message **text** is a further surface again, carrying a bracket-free declaration path and stating any offending index as a separate rendered number rather than inside the path.

> **Non-normative implementation note.** A faithful `Rule` is roughly `structure Rule where errorCond : Ast; errorField : Path; severity : Severity; text : Template`. There is deliberately no `polarity` or `assert` field — those are *derived* (polarity from the data; the error semantics from "condition true ⇒ invalid").

Sources: [message construction route](../docs/sources/message-and-pointer-probes.md#src-message-construction-route), [address dialect checkpoint](../docs/sources/message-and-pointer-probes.md#src-address-dialect-selector), [declaration report withholding checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14), [sort list capacity supplement](../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity), [inbound 2026-09-26m error-target paths](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-error-target-paths).

### 3.2 Computations

A **computation rule** writes a value into a **computed field**. It has:

- a **target** (the computed field),
- an optional **common precondition**, then one or more **alternatives**. Each alternative contains its operation, an optional precondition, and an optional fixed `toleranceRangeOp`. Within one computation declaration only the sole alternative may omit its precondition, while every row of a multi-alternative declaration is guarded; several declarations for one field concatenate into one table that may hold unguarded rows from separate declarations ([the complete selection account](09-computations.md#53-selection-across-alternatives-and-declarations)). The tolerance metadata does not affect first-match selection or operation evaluation; it changes only that alternative's implicit generated mismatch from strict `!=` to the named fixed tolerance-band predicate ([the precise generated-rule account](09-computations.md#6-the-implicit-validation-rule-precisely)).

**Alternatives are tried top-to-bottom.** An absent precondition selects directly, clean false/unknown falls through, a poisoned read aborts, and the **first** selected alternative ends the scan even if its operation later produces no value. No selected alternative yields a clean no value, which is reported as a **CLEARED** action when the computation source's target was filled ([§4.3](#43-the-compute--apply--validate-flow)).

Three cross-cutting facts (detailed in [§11](09-computations.md)):

1. **Every computation also generates a validation rule** with one guarded mismatch clause per alternative. With mutually exclusive guards this checks the selected computed result; with overlapping guards a later holding mismatch can fire even though computation itself selected the first operation.
2. **The computed field's declared scale is admitted per alternative** ([§11 §1.3](09-computations.md#13-the-scale-gate)). An alternative without a tolerance band compares through the same predicate as `==`/`!=` ([§5 §1.2](04-numbers-and-decimals.md#12-the-equality-scale-gate-and-its-waiver)): an equal derived scale always passes, a smaller derived scale passes only while the whole operation retains the multiplicative-constant capability, and a larger or unknown derived scale is rejected absent suppression (wrap in a rounding construct to force a scale). How the capability propagates — a field reference does not carry it, a capable multiplication such as `[A] * 100` does — is [§5 §1.1](04-numbers-and-decimals.md#11-static-scale-and-the-multiplicative-constant-capability)'s. An alternative declaring a `toleranceRangeOp` meets no scale agreement gate.
3. **The computed field may be read neither in a precondition nor in an operation**, and a reference to any group containing it is such a read; the exemptions are closed: singular `GroupFilled` over such a group, the positive fixed-root `AtLeastOneGroupFilled(Root)` form and a `CurrentRepetition` operand ([§11 §5.2](09-computations.md#52-the-target-self-read-gate)).

### 3.3 Member texts of rules and computations

**A member counts as blank by Java's `Character.isWhitespace`, and only some members draw a missing class.** That predicate holds for U+0009–U+000D, U+001C–U+001F and every Unicode space, line or paragraph separator except the no-break spaces U+00A0, U+2007 and U+202F. Measured members: the vertical tab, the em space and the ideographic space (blank) and the three no-break spaces (not blank); the rest of the class is unmeasured.

| Member | Only a vertical tab, em space or ideographic space | Only a no-break space | Only ASCII spaces |
|---|---|---|---|
| rule `errorCode` | `MVK_ERROR_CODE_MISSING` | its content law, whose refusal carries no class key | `MVK_ERROR_CODE_MISSING` alone (below) |
| rule `errorCondition` | `MVK_CONDITION_MISSING` with `MVK_LEXER_STANDARD_ERROR` | `MVK_LEXER_STANDARD_ERROR` alone | `MVK_CONDITION_MISSING` with `MVK_INCOMPLETE_INPUT` |
| rule `errorEntityRelPath` | `MVK_ERROR_FIELD_MISSING` with `MVK_MISSING_ERROR_FIELD` | the same pair | not stated |
| custom field type `name` | `CUSTOM_FIELD_TYPE_CODENAME_MISSING` | its content law, whose refusal carries no class key | `CUSTOM_FIELD_TYPE_CODENAME_MISSING`, the name being blank |
| computation `operation` | `MVK_LEXER_STANDARD_ERROR` | `MVK_LEXER_STANDARD_ERROR` | `MVK_INCOMPLETE_INPUT` |
| computation `commonPrecondition` | `MVK_LEXER_STANDARD_ERROR` | `MVK_LEXER_STANDARD_ERROR` | `MVK_UNEXPECTED_TOKEN` |
| an alternative's precondition | not stated | not stated | `MVK_UNEXPECTED_TOKEN` |

A computation's operation and common precondition draw no missing class under any of the six measured characters.

**The error code's and the rule name's content laws judge the value after Java's `String.trim`.** So `Probe ` and `C\t` are admitted while an em space is kept and refused.

- **Error code.** It admits letters, digits, underscores and ASCII spaces, padding included (`A B`, ` A`), and refuses `A-B` and a no-break space. Beyond ASCII it admits only `Ä`, `Ö`, `Ü`, `ä`, `ö`, `ü` and `ß`, so `Cé`, `Ç`, `Cœ` and an Arabic-Indic digit are refused. A code written as a JSON number is judged as its text.
- **Rule name.** It admits no letter beyond ASCII. A computation's name meets the error-code alphabet as well as the name alphabet of [§1.3](#names-groups-and-texts).
- A supplementary character draws the repertoire notification in place of either content refusal ([§1.1](#the-models-own-texts-meet-the-default-charset)).

**Declaration notifications retain codeless findings as well as named classes.**

- An absent or exactly empty rule error code has a codeless empty-code notification beside `MVK_ERROR_CODE_MISSING`; an ASCII-space-only or vertical-tab-only code has the missing-code class alone. An empty `errorCode`, not a blank one, still draws its codeless empty-code notification on a rule the `ONLY` filter deletes.
- Independent name and code findings coexist. A malformed rule-name shape, such as a dotted name, suppresses the reserved-prefix class even when the name begins with `vk_vk`; its codeless name notification still coexists with a missing-code finding.
- A member or name that leaves no model: [§1.2](#defects-that-leave-no-model).

Sources: [inbound 2026-09-24b lexer and blank text](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-lexer-and-blank-text), [executable declaration admission checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-executable-declaration-admission), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21).

---

## 4. The call surface

### 4.1 `validateFull`

`validateFull(document)` evaluates every rule (authored and auto-generated) over the whole document and returns the full message set. `noErrorOccurred()` on the result considers **only ERROR-severity** messages — warnings and infos never make the document invalid.

### 4.2 `validatePart`

`validatePart(document, relevantSet)` evaluates a relevant subset of the document, treating references outside the set as three-valued UNKNOWN. Its guarantee is **one-directional**: it never reports an error fixable only outside the subset, but it does *not* promise a complete check of the relevant fields (some checks may be skipped for performance, and which is an implementation detail). [§12 §5](10-validation-and-polarity.md#5-full-vs-partial-validation) owns the algorithm; its parts in order:

- **Relevance** comes from the caller's patterns and the `Global` flag: global-flagged fields are auto-added to the relevant set at all repetitions ([§12 §5.1](10-validation-and-polarity.md#51-the-relevant-set)).
- **Rule admission** is ordered ([§12 §5.2](10-validation-and-polarity.md#52-which-rules-run-and-where)): an empty set reports nothing; every rule containing a `Having` filter is skipped; a rule whose error entity is a group reports nothing; and a rule runs only where its error field's relevant patterns, compressed into one selector, match the levels its iteration bound — not where one concrete error-field instance is relevant, so a rule reporting into a repeatable group it does not iterate runs when any of that group's rows is relevant.
- **Rows**: the admitted rule walks the declared-capacity rows with the content gate of [§2](03-empty-and-required.md#a4-the-row-gate--where-the-substitutions-stop) overridden, so a relevant instance is *always* evaluated, even if empty or phantom.
- **Reads**: uniqueness checks need the duplicate **partner** in the relevant set too. For a composite `RepetitionNotUnique` key, every key component of every participating row must be relevant; a cluster is built only from rows whose complete keys are relevant ([§9](07-repetition-and-iteration.md#6-repetitionnotunique-precisely-)).
- **Formal findings**: cell-conversion findings are gated by relevance, while over-repetition findings are reported for any nonempty relevant set ([§3 B.3](02-logic-and-formal-errors.md#over-repetition)).

### 4.3 The compute → apply → validate flow

**Validation and computation are separate operations; `validateFull` does not compute first.** The consumer (a form engine) composes the loop:

```
compute(source, context)  →  a rich result with Kernel-compatible projections
apply(result, destination) → an updated destination under placement guards
validate(updated, context) → messages over the updated document
```

**The V2 result preserves five observables rather than only a change delta:** all successful non-clearing computed instances, including successes unchanged from the computation source; the source-relative changed subset of those successes; erroneous computed instances; cleared instances that were filled in the source; and formal operand errors collected eagerly as a separate channel. `noErrorOccurred` is true exactly when both the erroneous-instance and formal-operand-error channels are empty. Formal operand collection is not dependency evaluation: later skipping or poison remains read- and schedule-sensitive even though the formal errors were already inventoried. Public computed-instance collections are compared extensionally by pointer and payload; their iteration order is not an execution-schedule contract without separate evidence.

**The VALUE / CLEARED / ERRORED vocabulary describes the source-relative change/application actions, not the complete result.** VALUE actions are the changed successful subset. CLEARED contains source-filled instances that were explicitly cleared or were not computed because no precondition applied, an error cascaded, or operands had formal errors; an erroneous computed instance reports through ERRORED instead of CLEARED. A caller may apply the stable result to a model-compatible destination other than the computation source. Application uses the classifications already fixed relative to the source—it does not recompute change equality against the destination—and successful unchanged instances are not writes merely because they appear in the broader successful collection. Model compatibility remains a caller precondition; a stricter owner check in another implementation is library policy, not a kernel rejection rule.

**Each retained action has its own placement effect:**

| Action | Effect on the destination |
|---|---|
| **VALUE** | writes its exact value and creates the cell plus its directly addressed missing ancestor rows |
| **CLEARED** | places a present-empty cell and directly addressed missing ancestors even when that target was absent in the destination; it is a source-classified action, not a destination-relative "clear only if present" request |
| **ERRORED** | validates its address and empties the target only when the target cell already exists, so an absent target remains absent rather than being created as present-empty, and no absent row is materialized |
| none: the computation source target was absent and no value was produced | no CLEARED action is minted at all, so applying the result changes nothing at that address |

On the computation source itself, a CLEARED action can exist only for a source-present target. Untouched cells preserve their placement and raw stored text, including a stored CRLF pair; evaluation-side normalization never rewrites the document. Read-back therefore distinguishes **absent**, **present-empty**, and **present-value**.

**Row materialization.** For one repeatable level, application of a Number or String VALUE or CLEARED action at row coordinate `k` materializes the complete predecessor prefix `1…k` in numeric address order. The predecessor rows are empty unless they already existed, in which case their cells and coordinates are preserved. Actions keep their own coordinates even though retained application processes CLEARED before changed VALUE: placing row 3 before row 1 yields the same three-row topology as the reverse action classes, rather than appending rows in encounter order. For exactly two finite direct repeatable Number or String levels, an action at outer coordinate `i` and inner coordinate `j` materializes the complete outer prefix `1…i` and the complete inner prefix `1…j` only beneath outer row `i`; synthetic outer predecessors gain no inner rows. Distinct actions retain their exact nested coordinates, existing destination cells survive, and an ERRORED action against an absent nested target creates no outer or inner row.

**Later validation observes the applied topology.** A later validation over the returned applied document, without another computation, enumerates that topology and observes placed values at their exact rows. In the measured one-level matrices, `Amount > 0` and `Length(Label) > 0` each fire at rows 1 and 3 and not at the empty materialized row 2, while the two-level Number and String matrices fire only at outer/inner coordinates `[1,2]` and `[3,4]`.

Measured scope: the materialization rule is exact for direct finite one- and two-level Number and String targets; a prefix rule at any other depth is a hypothesis, and Number and String nesting beyond two levels, other target families, general later-rule execution, transport reconstruction, and pointer rendering remain unmeasured or outside the current result domain.

This matters for reimplementation packaging: model **`compute`** and **`validate`** as two total functions over the document, and make `apply` an explicit, placement-sensitive step. Do not fuse them.

#### The processing context

**Every call reads one complete immutable processing context**, the `World` of the signatures below. It supplies the injected current instant and resolved current date, including a configured test override or the actual date sampled once at the host boundary; the effective error-message locale; total named [custom-condition](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch) and [custom-field-type](06-strings-and-enumerations.md#a3-custom-field-type-validation) semantics; deprecated additional-information input while compatibility with that kernel 30.8.1 surface is claimed; and a versioned zone-rule oracle/profile capable of resolving every time-zone id admitted by the model checker. A deliberately narrower product may reject an unsupported capability or legal zone id before evaluation, but that product boundary does not narrow the canonical kernel legal-input domain.

> **Non-normative implementation note.** Signatures to aim for:
> ```lean
> def validateFull : Model → World → Document → List Message
> def validatePart : Model → World → Document → RelevantSet → List Message
> def compute      : Model → World → Document → ComputeResult
> def apply        : ComputeResult → Document → Document
> ```
> A Lean implementation may pass family capabilities of `World` separately. Keeping `compute` as *result-producing* rather than *document-mutating* isolates the order-dependent poison ([§11](09-computations.md)) inside one function and lets `apply`/`validate` stay pure. The pure signature expresses the immutable V2 behavioral boundary; deprecated V1 mutation and object aliasing are a separate API-compatibility claim rather than semantics that the result type should encode.

Sources: [application kinds checkpoint](../docs/sources/computation-placement-and-constant-probes.md#src-application-kinds-c03), [errored target checkpoint](../docs/sources/evaluation-and-application-routes.md#src-errored-target-applied-state), [valueless outcomes checkpoint](../docs/sources/evaluation-and-application-routes.md#src-valueless-outcome-minting-and-application), [repeatable String application checkpoint](../docs/sources/evaluation-and-application-routes.md#src-repeatable-string-application), [temporal construction route](../docs/sources/temporal-and-message-probes.md#src-temporal-construction-route), a12-dmkits `AppliedCellStateDiffTest` (IF126), `SeparateDestinationClearDiffTest` at `c876c207bc092912ac5a35bff0db7298b63f92b0`, `RetainedComputationResultTest`, `PublicInterpreterApiTest`, and `SourceIdentityIngressRouteDiffTest`, `ComputedTimeTargetDiffTest` and `RepeatableTimeConstructionChangedDiffTest` at `38aeb23b5849b831f8ae6ee09579367e28ce982b`.

---

## 5. What is *not* modelled here

To keep the reimplementation scope honest, these are explicitly out of the evaluation semantics (they belong to the host platform):

- model **include/expansion** (resolving `TypeDefinition`s and included submodels) — evaluation may assume an already-expanded model; the static admission of [§1.2](#12-model-consistency-rules) and [§1.3](#13-declaration-generation-classes) still reads type definitions as stated there. **What makes this evaluation exclusion safe is measured, not assumed:** a typedef field is its base kind at every gate tested — a numeric aggregate's kind gate, the distinct count's homogeneity gate, and an ordering comparison — each row matching its plain-base-kind control under that gate's own code, so expansion loses no observable distinction. A typedef over a config-bearing base kind keeps its configuration where measured: in a date-range value list a definition's range format, separator and year interpretation, and a Number definition's kind, are compared exactly as if declared on the field, while a definition's domain constraints are not varied;
- the **editor** and its "required" checkbox UI — you receive the *generated* rule ([§4](03-empty-and-required.md)), not the checkbox;
- **persistence / wire format** of documents — you receive an in-memory tree; the one JSON conversion the kernel performs before evaluation is [§2.3](#23-reading-a-document-from-json)'s;
- **code-generation targets** — this set describes the normative Groovy-dynamic behavioral account. Generated static-Java is required co-evidence, and a strategy-split detector **with a bounded reach**: by source reading, operand lowering is single-sourced by construction — every dialect's operand template interpolates the same codegen backing-bean property, and that property carries no target-language branch — so no witness is known of a split originating there. Its detector power applies to the **rule/computation frame** layer, where Groovy has size-triggered lowering modes that static-Java has at no size: condition-line splitting at fifty or more atomic conditions, calculation closures, and rule-object splitting above ten rules per class. When a legal target-specific split exists, it is recorded rather than flattened into a false uniformity claim. By the same source reading, the known sources of an operand-level split are host-language semantics, a different runtime path being reached, and the caching and service layer; no witness of another source is known. The kernel TypeScript target is never allowed to override the Groovy-dynamic anchor. (The documented DateTime rejection for month/year arithmetic fires later at code generation; mixed DATE/DATETIME ordering is legal.)

Sources: [typedef base-kind checkpoint](../docs/sources/static-admission-and-class-probes.md#src-typedef-resolves-to-base-kind), [inbound 2026-10-26a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-26a).
