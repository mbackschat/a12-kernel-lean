# 01 — The data model and the call surface

*Prerequisite reading for everything else.* This file fixes the vocabulary and the shapes the rest of the set evaluates over: what a model is and when a declaration is legal, what a document is, how repetition and addresses work, what "a cell" means precisely, and the two operations (validate, compute) with their call surface. It is deliberately mechanical; the *interesting* semantics start in [`02-logic-and-formal-errors.md`](02-logic-and-formal-errors.md).

[`SEMANTICS-MAP.md`](SEMANTICS-MAP.md) summarises the glossary and the taxonomy without defining them; *cell* and *row* are defined in [§2](#2-document--an-instance-of-the-tree) below, and *not-check-relevant* in [§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty).

---

## 1. Model = a typed tree

**A document model is a static declaration tree of groups and fields.** Groups are internal nodes and fields are leaves; the model's root is a single group. A group's direct children form an ordered declaration sequence. Groups nest arbitrarily; a repeatable group may contain repeatable subgroups, giving multi-dimensional arrays. Recursive expansion to descendant fields preserves model declaration order: a child field is visited when reached, while a child group's descendant fields are visited recursively before the next sibling.

- **Groups** are **non-repeatable** (occurring at most once wherever their parent occurs) or **repeatable** (declaring an ordered 1-based row-address range `1 … repeatability`; a valid document may instantiate only a prefix `1 … rowCount`, where `rowCount ≤ repeatability`).
- **Fields** are leaves. Each has a **type** and per-type configuration. (The map's [type table](SEMANTICS-MAP.md#2-field-types-at-a-glance) summarises them; per-type evaluation is in files 04–06.)

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
| `0` or below zero | read by the model reader, so the refusal is not visible at load. The consistency check draws `MVK_MAX_VALUES_INVALID` at the group and once at every group and field beneath it, and none at a rule or computation declared there; it names each affected element separately, worded `zahlIstNullOvz` (a positive-only zero refusal) for `0` and `zahlMitVorzeichen` (an unsigned-field sign refusal) for a negative. The group alone also draws a codeless notification, not-positive for zero and signed below zero |
| a present count with no value: JSON `null`, an empty or blank text, or the text `null` | no model ([§1.1](#member-binding)) |
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
- The model builds, so these are verdicts rather than build failures.

> **Non-normative implementation note.** A model is naturally a `structure`/`inductive` of group and field declarations. Keep the *static* configuration (a Number's scale, a Date's format, a group's repeatability, whether a field is signed) in the model, **not** in runtime values — several semantics (the scale gate on `==`, number fillability, fragment completion) are decided from the *declared* configuration, sometimes before any value exists. A common early mistake is to attach scale to the runtime decimal; scale is a property of the *field*.

Sources: [repeatability checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-repeatability-declaration-domain), [inbound repeatability domain](../docs/sources/inbound-group-operand-batches.md#src-repeatability-domain-peer-measurement), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-24a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-24a), a12-dmkits `KF365` and `KF367` (no local record), [M1–M3 declarations adoption](../docs/sources/inbound-handbacks.md#src-m1m3-declarations-adoption).

### 1.1 The two special model-level configurations

**Four model-wide settings change evaluation globally; carry them in the model, not per field.**

- **Base Year** — a reference year that omitted-year date literals (`"13.07."`) and date fragments complete against. When it is absent, a consumer that requires concrete year-bearing Dates rejects those constructs; same-profile yearless DateRange equality and inequality remain the measured exception and do not imply an instant. ([§6](05-dates-and-time.md))
- **Time zone** — the DM-JSON key `content.modelConfig.timeZone`. Absent and empty both mean `UTC`, and any other id outside the host's legal set is refused `MVK_INVALID_TIME_ZONE`. [§6 §5](05-dates-and-time.md#5-time-zones-and-the-sub-day-difference) owns the legal set, the internal `TimeZone` key and how the zone resolves every temporal value.
- **Supported characters** — an optional legal charset. An absent or empty list uses the default Basic Multilingual Plane policy; a list containing an empty entry is malformed. The configured definition is runtime-enforced according to the exact entry and atomic-matching rules in [§7](06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching).
- **`fieldRefByShortNameAllowed`** — enables model-wide unique short-name field references. ([§10](08-paths-and-references.md))
- **`decimalSeparator`** — the DM-JSON key `content.modelConfig.decimalSeparator`. The literal grammar ([§12](12-concrete-syntax.md)) and the document's stored Number text use `.` throughout. A declared `,` is admitted, and the reads measured under it match `.`: stored `1,5` is a formal error (`zahlHatUngueltigeZeichen`), stored `1.5` reads as a Number under `>`, `==` and `FieldFilled`, and the condition literal `1,5` draws `MVK_UNEXPECTED_TOKEN`. A message's interpolated Number display default renders with `.` too. A computed Number's rendering and the stored text's other consumers ([§4](04-numbers-and-decimals.md#stored-decimal-identity-and-runtime-read-text-depend-on-the-storage-regime): Number `minLength`/`maxLength`, `FieldValueAsString`) under a declared `,` are unmeasured.

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
- A broken or unreferenced error target does not stop it.

#### Member binding

**A member that is not text binds before any check, and one that cannot bind leaves no model.** A member that no field, group, rule or type body declares is read past there, measured on a field, a rule and a type body, as are the retired variant members of [§1.4](#14-retired-variant-members), while a type's object that the field's `type` does not name is never read.

- **An element's body** is the object its `type` names. A group whose body is absent or JSON `null` is an empty group, built and checked as `{}`; a field, rule or computation whose body is absent or `null` leaves no model; and a body that is no object, such as `true`, `7`, `"x"` or `[]`, leaves no model, measured on a group and a field. An element's `name` written as an object or an array leaves no model; absent, `null` and any text bind, and [the converter](#the-validation-model-converter) judges them.
- **A field type** is an object whose `type` is one of twelve spellings, written exactly: `StringType`, `NumberType`, `BooleanType`, `ConfirmType`, `EnumerationType`, `DateType`, `TimeType`, `DateTimeType`, `DateFragmentType`, `DateRangeType`, `CustomFieldType` and `TypeDefType`. Any other type leaves no model, measured on `UnspecifiedType` with and without a body and otherwise the peer's source reading. A type whose body object is absent reads as the same type with an empty body, on all twelve.
- **Required members.** Absent or written JSON `null`, a rule's `errorCode`, `errorEntityRelPath` and `errorCondition`, a computation's `computedFieldRelPath`, a `sortFields` entry's `name` and `order` and the header's `id` leave no model. The header's `id` and `modelVersion`, absent or written `null`, are read and then fail the build ([defects that leave no model](#defects-that-leave-no-model)); kernel 30.8.1 admitted the `id` and built the version written `null` and failed the check below. The header's `locales`, absent or written `null`, is read as no locales on kernel 31.3.1, so the model is checked and draws `MVK_SUPP_LANGUAGES_MISSING` as an empty list does, and neither runtime strategy evaluates it; on 31.1.1 it failed the build. A hint-list entry's `locale` and `values` leave no model when absent; their `null` is unmeasured on 31.1.1. Written empty these members bind and are judged by the rules of [§1.2](#12-model-consistency-rules) and [§1.3](#index-and-sort-nomination-admission). An object or an array, empty or not, in a rule's `errorCode`, `errorEntityRelPath` or `errorCondition`, in a computation alternative's `operation` or `precondition`, or in a group's `indexFieldName` leaves no model. A rule's `severity` is absent, reading `ERROR`, or exactly `ERROR`, `WARNING` or `INFO`; any other value, the empty text, `null`, another case and a number included, leaves no model.
- **A temporal body passes over a member its kind does not declare.** `datePrecision` beside a Time, a DateTime, a DateFragment or a DateRange, measured with a partial precision, and `youngerThan1900Check` beside a DateTime, measured `true` and `false`, and beside a Time, measured `true`, are admitted with no notification, and an enabled check has no effect: a DateTime holding `1850-01-01T10:00:00` draws no finding. Kernel 30.8.1 left a model with `datePrecision` there or `youngerThan1900Check` on a DateTime unread. Sources: [31.1.1 re-capture](../docs/sources/kernel-31-calibration-probes.md#src-kernel-31-recapture), [derived-row capture](../docs/sources/kernel-31-calibration-probes.md#src-kernel-31-derived-rows).
- **Every primitive boolean member binds by one law:** the header's `immutable` and `metaData`, `fieldRefByShortNameAllowed`, a field's `global` and `transient`, `lineBreaksPermitted`, `noValueValidation` and `alphabeticalSorting` on a String, `zeroNotAllowed`, `positivesOnly` and `leadingZerosAllowed` on a Number, `youngerThan1900Check` on a Date, DateRange or DateFragment and `alphabeticalSorting` on an Enumeration, inside a type definition whether or not a field references it, and a mount's `includeConfig.excludeRules` and `excludeComputations`.
  - An absent member is `false`. JSON `null`, the empty text, a blank text and the text `null` leave no model.
  - A JSON boolean binds as written and an integer token is set unless zero, `-0` clearing.
  - A number is judged by its token's kind, not its value: a token written with a fraction or an exponent leaves no model, `1e0`, `1E+0`, `1.0`, `10e-1` and `-0.0` included.
  - A text is cut by Java's `String.trim`, which removes only the characters up to U+0020, and must then be exactly `true`, `True`, `TRUE`, `false`, `False` or `FALSE`. `"tRUE"`, `"yes"`, `"1"`, a no-break or em space before `true` and a container leave no model.
  - Measured on kernel 31.1.1 on `fieldRefByShortNameAllowed`, besides the carriers' own rows: the cases spellings, `"yes"`, `"1"`, `"NULL"`, a tab, line feed, no-break or em space beside `true`, the tokens `2`, `-1`, `0.5`, `1.5` and `1.0`, and the exponent and fraction tokens. Every carrier is measured on absence, `null`, the empty, blank and `null` texts, `"false"`, `1` and `" TRUE"`; the other spellings on the other carriers follow the one law, unmeasured.
- **An integer member binds as a primitive or a boxed Java integer.** The primitive ones are a group's `repeatability` and a Number's `minFractionalDigits` and `maxFractionalDigits`; the boxed ones are the header's `baseYear`, a Number's `minLength`, `maxLength` and `maxIntegerDigits`, and a String's or Custom field's `minLength` and `maxLength`, on a field's own body and in every type definition, referenced or not.
  - JSON `null`, an empty or blank text and the text `null`, padded or not, leave no model on a primitive member and are no value on a boxed one: a base year with no value is absent, and a length with no value is undeclared.
  - A text is trimmed the same way and read by `Integer.parseInt`, which takes one sign and any decimal digit of the Basic Multilingual Plane, so `" 3 "`, `"+3"`, `"03"` and `"٣"` are 3, while `"abc"`, `"3.7"`, `"1e1"`, `"0x3"` and a no-break space beside the digits leave no model. A boolean leaves no model.
  - A JSON number is truncated toward zero when its value lies inside the `int` range, whether it is written with a fraction or an exponent, so `2.7` is 2, `3.7` is 3, `1e1` and `10.0` are both 10 and `2.147483647E9` is 2147483647, while `2147483647.5`, `2147483648` and `3e10` leave no model in either spelling. The `repeatability` token `3e-2147483647` draws `MVK_MAX_VALUES_INVALID`, while `0e2147483648` leaves no model.
  - Measured on kernel 31.1.1 on `repeatability` and the type-body members: `null`, the empty, blank and `null` texts, `"abc"`, `true`, `2.7` and `"2"`, and on `repeatability` also the text and token spellings above. `baseYear` is boxed by source reading, and its other spellings were measured on 30.8.1 only.
- **A number longer than 1000 characters leaves no model**, measured on a Number bound written as text or as a token: 1000 characters build and 1001 do not. Whether the limit also reaches a number token elsewhere in the model is unmeasured. A bound's text `null` is no bound. A bound written as text with an exponent of `2147483647` or `-2147483647` binds, while `2147483648` or `-2147483648` leaves no model; the bound tokens `1e2147483648`, `0e2147483648` and `1e-2147483648` leave no model.

**A localized-text member binds by its own law.** The carriers measured are a field's label and helper text, a group's label, an element's external and internal descriptions, each Enumeration value's label, an Enumeration's message, a patterned String's message, a type definition's description, a rule's message, and a requiredness configuration's message.

- The member's value is iterated as a node: a list yields its entries, an object its values, and any other scalar nothing, so `[]`, `"x"` and `5` bind with no text. `null` leaves no model.
- Each entry must be an object whose `locale` and `text` are both strings, the locale a spelling the locale parser takes. An entry that lacks either, holds `null` or another kind there, or is itself a text or `null` leaves no model.
- The locale parser takes the empty spelling and a lowercase two- or three-letter language alone. It takes that language followed by an uppercase two-letter country or a three-digit area, joined by `_`, or by `-` when the spelling holds no `_`, and after a second separator a nonempty variant that may hold further separators, the country then optional. It takes a spelling opening with its separator and an uppercase country, optionally followed by the same separator and a nonempty variant.
- Two quirks widen it: in a two-segment spelling a three-digit area is taken after any first segment, so `XX_123` parses while `XX_123_x` does not, and a bare uppercase pair parses exactly when the runtime's JDK lists it as a country, so `US` parses and `EN` does not. Letter case and digits follow Unicode's classes.
- So `en_US`, `en-US`, `en`, `eng`, `fr_CA`, `en_US_POSIX` and `en_123` parse, while `en_us`, `EN_US`, `e`, `en_U`, `en_USA`, `klingon`, a padded spelling and `zh_Hans_CN` leave no model.

**A model's frame binds member by member, before any check, and a member that cannot bind leaves no model.** The frame is the `header` and `content` objects and the members under them:

| Member kind | Members | Binds | Leaves no model |
|---|---|---|---|
| text | `header`'s `id`, `modelType` and `description`; `modelInfo`'s `name`, `variant`, `branch`, `revision`, `comment` and `joinedModelsInfo`; `modelConfig`'s `decimalSeparator` and `timeZone` | any scalar, a number or boolean as its text; absence; `null` on every member but `name`, `decimalSeparator` and `timeZone` | an object or an array; `null` on `name`, `decimalSeparator` and `timeZone` |
| list | `header`'s `locales`, `labels`, `annotations` and `modelReferences`; `content`'s `typeDefinitions`; `modelConfig`'s `supportedCharacters`; `modelRoot`'s `rootGroups` | an array; absence; `null` on `locales`, `labels`, `annotations` and `modelReferences` | any other kind; `null` on `typeDefinitions`, `supportedCharacters` and `rootGroups` |
| object | `header`, `content`, `modelInfo`, `modelConfig` and `modelRoot` | an object; absence of `modelInfo`, `modelConfig` or `modelRoot` | any other kind, `null` included; absence of `header` or `content` |
| condition language | `modelConfig`'s `conditionLanguage` | absence, a text, or an object whose `code` is a text, when the locale parser takes the code ([concrete syntax §12](12-concrete-syntax.md)), the two writings and two spellings of one locale declaring one language | `null`, an array, a number, a boolean, an object without `code`, an object whose `code` is `null` or an object, and a code the locale parser refuses |
| supported character | each `supportedCharacters` entry | a text, a number or a boolean, as its text | an object or an array |

- A number binds as its text in the measured integer spelling, except that a supported character written as the number `-0` is admitted where its two-unit text would be refused; how a number written with a fraction or an exponent reads as text, and a `code` written as a number, are unmeasured.
- `header.modelVersion` written as a scalar binds, and the version check then judges it; written as an object or an array it draws no class, and whether it leaves no model or only fails the check is unmeasured.
- **Three shapes bind and build, and then the consistency check fails without a class:** no `content.modelInfo`; a `null` supported character; and a condition language naming a locale other than the two supported ([concrete syntax §12](12-concrete-syntax.md)). The failure withholds every class, not just the clean verdict. Only the entry model needs the version, the model info and a character list without `null`: an included model or a type-definition library lacking them is expanded and checked. A reached included model that does not declare the entry's locales is refused, while a type-definition library declaring fewer locales builds on kernel 31.1.1, where 30.8.1 refused it. The reached-model rows other than the locales were measured on 30.8.1 and are unmeasured on 31.1.1. An included model's unsupported condition language is unmeasured.
- On the measured runtime route a model written with one of those shapes is not evaluated, since that route checks a model before evaluating it; an evaluator follows that route and refuses it. Called with no check in front, both engines evaluate a model whose only such shape is its version, throw before any rule on the other frame shapes: without the model info while generating code, with a `null` character in the code generator's charset precheck, with `null` locales while expanding a rule's localized messages, or in the runtime's own settings when the model has no rule; and throw on an unsupported condition language. On a reached model the version, model-info and `null`-character shapes are evaluated. A caller that skips expansion is unmeasured. These runtime rows were measured on kernel 30.8.1 and are unmeasured on 31.1.1.
- **A member that binds may still be judged by its text, on the entry model only.** An included model carrying the name `xmlC` or `""`, the version `x` or `29.0.0`, the time zone `x` or the supported characters `["ab"]` is built and checked without that judgment; other values on an included model are unmeasured. Where a value below "fails the check without a class", the model is read and expanded and its consistency check then reports nothing, as for the three shapes above.
  - **The generated-code name** is built from `modelInfo.name` and `modelInfo.branch`: the name is lower-cased; when it ends in `_` and the lower-cased branch, those are cut off and rejoined as separate parts; blank parts are dropped and the rest joined by `_`. An empty result or one beginning with `xml` draws `MVK_INVALID_NAME_4_GENERATED_CODE`. So an absent or empty name, the name `"  "`, `xmlP`, `XmLp`, `_xmlb` beside the branch `xmlb` or `XMLB`, `xml_v1` beside `v1`, `_` beside an empty branch and `xmlP` beside the branch `" "` draw it. `x_xmlb` beside `xmlb`, `Policy_V1` beside `v1`, `a_xml` beside `xml`, `xm`, `Prämie`, a lone U+00A0, `5` and `true` do not, so a no-break space is not blank. A branch beside an absent name fails the check without a class. A name whose lower case changes length is measured only on `XMLİ` and `xmlİİ_b` beside `b`, which draw the class, and `İİİ_b` beside `b`, which fails the check without a class. A nonblank branch beside a name not ending in it, and blank characters other than the space and U+00A0, are unmeasured.
  - **The version** `header.modelVersion` is judged as `major.minor.patch` in ASCII digits, with two codeless findings, a pattern finding and a mismatch finding. A version failing the pattern draws both, the pattern finding first: measured on `28.5`, `x`, `28.4.0` with a trailing space, Arabic-Indic digits, `28.4.0.0`, `-28.4.0`, the number `5` and `true`. A version fitting it draws neither when the major is 28 and the minor and patch are at most `4.0` read together as `minor.patch`, so `28.4.0`, `28.0.0`, `28.3.99`, `28.4.00`, `28.04.0`, `028.4.0` and `28.4.0000000000000000001` pass. `28.4.1`, `29.0.0`, `27.9.9` and `2147483647.0.0` draw the mismatch finding alone. A major beyond `2147483647` fails the check without a class. How finely the minor and patch are compared beyond these rows is unmeasured. These rows were measured on kernel 30.8.1, whose DM version is 28.4.0. Kernel 31.1.1 applies the same law with major 29 and the bound `4.0`: `29.4.0`, `29.0.0`, `29.3.99`, `29.04.0`, `029.4.0` and `29.4.0000000000000000001` pass, `28.4.0`, `29.4.1`, `29.5.0`, `30.0.0`, `31.1.1` and `2147483647.0.0` draw the mismatch finding alone, and `29.4` and `x` draw both.
  - **The time zone** draws `MVK_INVALID_TIME_ZONE` by the rule [the time zone setting](#11-the-two-special-model-level-configurations) names.
  - **A supported character** that the [legal charset grammar](06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching) refuses fails the check without a class. A number or boolean entry is judged by its text: `true` is four characters and refused, the number `7` admits the character `7`, and the number `-0` is admitted where the two-unit text `-0` would be refused.
  - **Beside another defect**, measured on these inputs only: the version's findings come first and withhold no other class, the mismatch finding of `29.0.0` beside a computation cycle, a missing entity or the time zone, and the pattern and mismatch findings of `x`, in that order, beside a cycle. A refused time zone or a refused name withholds a cycle's class but not a missing entity's. A refused supported character `["ab"]` beside the time zone `x` or the version `x`, and a lone high surrogate beside the time zone `x`, fail the check without a class. The pattern finding beside a class other than a cycle's, and other pairs, are unmeasured.

**A header's locale code meets the same parser, and a code it refuses leaves no model; the build then fails on a locale with no language and on two codes naming one locale, and demands no well-formed language tag.**

- A `locales` entry is an object carrying the code as `code`, or the code itself as a text, which the same parser and the checks below judge alike: a bare `EN` is unreadable, a bare `US` and a bare `de_CH` beside `de-CH` fail the build, and a bare `de__1996` builds.
- A parsed locale with an empty language fails the build, as `_CH`, `-CH`, `_CH_x`, `CH`, `US` and the empty code do.
- Two codes the parser reads as one locale fail the build: the language's case and `-` against `_` are normalized, and the withdrawn `iw`, `ji` and `in` are read as `he`, `yi` and `id`. So `iw` beside `he`, `de_CH` beside `de-CH`, `DE_419` beside `de_419` and a code written twice fail, while `iw` beside `de` and `de_CH_POSIX` beside `de_CH_posix` build.
- A locale that is no well-formed language tag still builds: `de__1996`, `de_CH_x`, `de_CH_1996_x`, `de_CH_abcd`, `1_419`, `d_419`, `abcdefghi_419`, `ée`, `de_ÄÖ` and `en_US_POSIX_x` build, as do `de`, `und`, `es_419`, `DE_419`, `de_CH_POSIX_WIN32`, `de_CH_x_abc` and `de_CH_a_bcd`.
- Two distinct declared locales with one language tag draw `MVK_SUPP_LANGUAGES_DUPLICATE`, compared case-sensitively. The tag is the JDK's: a language that is not 2–8 ASCII letters reads as `und`, except that a locale with no country and no kept variant subtag but a private-use sequence is tagged with no language, and a country that is not two ASCII letters or three ASCII digits is left out. The variant is split at `_`; the subtags before the first that is not 5–8 ASCII letters or digits, or four opening with a digit, are kept as written, and that one and those after it follow as a private-use `lvariant` sequence, which ends before the first subtag that is not 1–8 ASCII letters or digits.
- So `und` beside `ée`, `und_419` beside `1_419` or `abcdefghi_419`, `1_419` beside `d_419`, `de` beside `de_ÄÖ`, `de_CH` beside `de_CH_abcdefghi`, `en_US` beside `en_US_abcdefghi` or `en_US_abcdefghi_x`, and `en_US_1996` beside `en_US_1996_abcdefghi` draw it, once for three codes sharing one tag, while `en_US` beside `en_US_abcd` or `en_US_x`, `de` beside `de__1996`, `und__abcd` beside `ée__abcd`, `und` beside `de_CH` and `de_CH_POSIX` beside `de_CH_posix` do not. Which consistency rule states it and the order of two such tags are unmeasured.
- **Two locales the JDK tags specially leave no model on kernel 31.1.1**: a header code `ja_JP_JP`, `ja-JP-JP` or `th_TH_TH` beside `en_US`, and a label entry's locale `ja_JP_JP` or `th_TH_TH`, while `ja_JP`, `ja_JP_jp` and a label locale `ja_JP` build. Kernel 30.8.1 built all of them. That the cause is the Kernel's copy of the model, which cannot write those locales' language tags, is the peer's source reading.

#### Model expansion

**A host expands a model before the consistency check: a group carrying an `includeConfig` mounts another model, and the header's `modelReferences` import type-definition libraries.** These rules are the host's and are measured on kernel 31.1.1 through the Kernel's expansion followed by its consistency check; the semantics of this set apply to the expanded model.

- **A mount binds by `includeConfig.reference` alone**, keyed by the included model's id: the header's include entries, their `alias`, a missing or duplicated entry and one naming another model change nothing, and the expanded model carries no references. Without `includeLevel` the mount places the included root group's children into the mounting group, as `SINGLE_RG` does, and local elements beside the mount are replaced by the included content.
- **`includeConfig` shapes.** `null` is a plain group with no mount. An object without `reference`, or one whose `reference` is empty or Java-blank, is refused by the expansion, naming the group; `includeConfig` written as a text or an array, and `reference` written `null` or as an object, leave no model. A number or boolean `reference` resolves as its text, and a no-break space belongs to the id. `excludeRules` and `excludeComputations` bind by the boolean law of [member binding](#member-binding). A group carrying the DM 28 `modelAlias` in place of `includeConfig` is an empty group, with no notification.
- **A provider without a root group** leaves no model when mounted as `SINGLE_RG` and mounts nothing as `MODEL_ROOT`.
- **Type definitions of two sources.** Two imported libraries defining one id are admitted when the definitions agree member by member, members the reader does not know aside; when they differ, in a length, the name, the field type or a member only one writes, the expansion refuses the importer. A model's own definition with the empty id, in a model that imports a library, leaves the expansion unbuilt. A library holding root groups, with or without fields, builds, as one declaring fewer locales than the entry does, where kernel 30.8.1 refused both; a reached model whose header `id` is `null` leaves no model.
- **Ids across a mount.** A provider mounted twice, or a host field reusing a provider field's id, is admitted; a host field reusing the mounting group's id draws [rule 1](#the-six-rules) for the group and the field.
- **The empty member.** After the expansion a Date `format` of `""` and an empty DateRange separator read as absent and are admitted ([§1.2](#defects-that-leave-no-model), [§1.3](#13-declaration-generation-classes)); that the expansion's copy drops every empty declaration member is the peer's source reading.

Sources: [inbound 2026-11-05b](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05b), [header locale codes](../docs/sources/model-structure-and-declaration-probes.md#src-header-locale-codes), [inbound 2026-10-29a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29a), [inbound 2026-10-29](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29), [locale grammar](../docs/sources/model-structure-and-declaration-probes.md#src-locale-spelling-grammar), [inbound 2026-09-26m model texts](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-model-texts), [inbound 2026-09-26n field message gates](../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates), [inbound 2026-10-18](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-22](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-22), a12-dmkits [`kf157`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf157) (the interpolated Number display default under a declared `,`), [model frame members](../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-members), [model frame check route](../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-check-route), [inbound 2026-10-29d](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29d), [inbound 2026-10-30](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-30), [inbound 2026-10-30a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-30a), [inbound 2026-10-30b](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-30b), [M1–M3 declarations adoption](../docs/sources/inbound-handbacks.md#src-m1m3-declarations-adoption).

### 1.2 Model consistency rules

**Reading and member binding come first, then building, and a failure at either leaves no model; a built model then meets six ordered consistency rules, and a model drawing any notification is refused.** Each stage reads either the model as authored or the model [the converter](#the-validation-model-converter) produces from it inside rule 5:

| Stage | Reads | A defect shows as |
|---|---|---|
| reading and member binding ([§1.1](#member-binding)) | the authored JSON | no model, no class |
| building | the authored model | a build failure: no class, and no later stage reports |
| consistency rules 1–6, in order | the authored model, except rule 5, which reads the converted model | codeless notifications, except rule 4's keyed dollar-count class and rule 5's `MVK_*` classes of [§1.3](#13-declaration-generation-classes), which stand beside its codeless converter sentences and printed-bound refusals. The refused temporal format of [spec/05](05-dates-and-time.md#the-format-vocabulary) is codeless too; which rule states it is unmeasured |
| code generation's static checks; evaluation | the converted model | the condition, operation and message classes of the later chapters; no order against the consistency rules is stated |

#### Defects that leave no model

**Every defect below leaves no model and no rule below reports.** The last column names the kernel on which the row was measured; a row measured on 30.8.1 alone is unmeasured on 31.1.1.

| Defect | Result | Measured on |
|---|---|---|
| a primitive or integer member, an element body or name, a field type or a required member that cannot bind ([§1.1](#member-binding)) | no model | 31.1.1 |
| a localized-text member that cannot bind ([§1.1](#member-binding)) | no model | 30.8.1; a rule's `errorMessage` written as an object or `null` on 31.1.1 |
| a frame member that cannot bind ([§1.1](#member-binding)) | no model | 30.8.1; `modelInfo.name` written as an object on 31.1.1 |
| the header's `id` or `modelVersion` absent or written `null` | build fails | 31.1.1; `locales` too on 31.1.1 only |
| two type definitions of a model sharing an id, the empty id included | no model | 31.1.1 |
| a header locale code the parser refuses ([§1.1](#member-binding)) | unreadable | 30.8.1; `EN` on 31.1.1 |
| a header locale with an empty language, or two header codes naming one locale ([§1.1](#member-binding)) | build fails | 31.1.1 |
| a Number bound written as text outside the reader's decimal grammar ([§1.3](#13-declaration-generation-classes)) | unreadable | 31.1.1 |
| a computation whose target the converter resolves to a field it drops, and a root group named exactly `""` holding a rule, computation or ordering member ([the converter](#the-validation-model-converter)) | no model | 31.1.1; an empty reference among them on 31.3.1 |
| a computation target climbing past the technical model root or starting with `/`; a rule error target starting with `/` | build fails | 30.8.1; no model on 31.1.1, whose measured route refuses the input before a build, and for the climb on 31.3.1 (`../../../Customer/Name` from a computation in a root group) |
| a rule's error target on its own group ([§3.1](#the-error-fields-declaration)) | build fails | 31.1.1 |
| an Enumeration with no value, its `values` absent or empty, with categories, a `tableName` or neither | build fails | 31.1.1 |
| an Enumeration with two categories of one name, with equal or different values, an absent and an empty name reading as one name | build fails | 31.1.1 |
| a category `name` written `null`; a category token written as an object or an array | no model | 31.1.1 |
| an Enumeration entry whose empty token carries one declared-locale label with an empty text ([§1.3](#enumeration-declarations)) | build fails | 31.1.1 |
| two hint-list entries for one locale, `en_US` beside `en-US` included (an entry with no values beside a filled one is admitted) | build fails | 30.8.1 |
| an absolute or root-climbing index or sort spelling ([§1.3](#index-and-sort-nomination-admission)) | no model | 31.1.1 |
| a sort entry without its `name` or `order`, or an `order` that binds to neither constant ([§1.3](#index-and-sort-nomination-admission)) | no model | 31.3.1 |
| a Date `format` written `""` or `" "` in the model as checked; a Java-blank `format` on a DateTime or Time, inside a type definition too (an omitted one is the default; a no-break space is an ordinary invalid format) | build fails | 31.1.1 for the Date and for `" "` on a DateTime and a Time; 30.8.1 for the others |
| an empty or absent DateFragment `formatOfFragment`, a `DateFragmentType` without its body included | build fails | 31.1.1 |
| an unreadable rule error-code member | no declaration verdict | 30.8.1; no model on 31.1.1, measured on an object |

Further load and build refusals are stated with their construct: the one measured model declaring a supplementary charset range ([§1.3](#enumeration-declarations)), an empty `interpretationOfYear` token ([§6](05-dates-and-time.md)), and an unknown `roundingMode` ([§11 §6](09-computations.md#6-the-implicit-validation-rule-precisely)). A notification's absence of a class key therefore cannot by itself distinguish a build failure from a codeless verdict. A host that expands a model before checking it copies an empty declaration member as an absent one: there a `format` written `""` on a Date, a Time or a DateTime is admitted as the kind's default, and a runtime on that route reads it so, while `" "` still fails the build.

#### The six rules

**The rules run in this order, each walking type definitions first and then the elements depth-first, a group before its children, and their notifications are reported in that order, each rule's in walk order except the fifth's.** A model with nothing to expand walks its own type definitions in declared order. A model with something to expand walks them by id, ids comparing by UTF-16 code unit, uppercase before lowercase and a Latin-1 letter after every ASCII one, so `Beta`, `Zeta`, `alpha` and `Coverage`, `Prämie`, `deductible`, `Überschuss` are walked in those orders whatever order declares them. Both orders are measured on kernel 31.1.1, the sorted one on a model importing a type-definition library; that a non-empty `modelReferences` list or a group's `includeConfig` other than `null` is what gives a model something to expand is source reading, and supplementary-plane ids are unmeasured. Every rule except the fifth reads the authored model, so a declaration the converter drops still meets id uniqueness and the basic checks, measured, and the group shapes, unmeasured.

1. **Id uniqueness** over every group, field, rule and computation, type definitions excluded: an id carried by `k ≥ 2` elements draws `k` notifications, one at each sharer's path, whatever their kinds, a root group included; a field sharing an id with a type definition is admitted. The empty id is an ordinary id here, drawing rule 6's empty-id class beside it, and a sharer the converter drops still counts.
2. **Attachment groups** (`usageType` `attachment`):
   - one notification when any of the eight required field names (`original_filename`, `internal_filename`, `content`, `attachment_id`, `size`, `mime_type`, `category`, `description`) is missing among the group's direct fields;
   - one when any of the four required rule conditions of the model's condition language, compared as exact text, is missing among the group's direct rules (table below; another condition language is unmeasured);
   - and one when the first direct element named `content` is a field whose declared type, not its effective type, is a String lacking either `noValueValidation` or `lineBreaksPermitted`.
3. **Multi-select groups** (`usageType` `multi-select`): a group repeatable at most once; a group without exactly one direct field; then, for that field, a missing requiredness configuration, its nomination as the group's index field, and an effective type other than String or Enumeration; and finally any direct child group or computation.
4. **Document uniqueness criteria**, as [§1.5](#15-document-uniqueness-criteria) states them. Its place between the multi-select and generation rules is source reading.
5. **Generation of the declaration.** The rule first runs [the converter](#the-validation-model-converter), then reports the `MVK_*` classes of [§1.3](#13-declaration-generation-classes) over the converted model, as [§1.3](#13-declaration-generation-classes) states rather than in walk order, and checks each Number bound's printed text ([§5 §4](04-numbers-and-decimals.md#4-other-numeric-constraints)) with two arms of the value cascade: more than 15 digits, then a minus on zero. For those bound checks a field reports the maximum before the minimum, and an identical notification on the same field only once. Kernel 31.1.1 judges no bound by the magnitude its fractional digits allow. Whether a dropped field's printed bounds are checked is unmeasured.
6. **Basic member checks**: an empty type-definition id or name; an empty element id; an empty element name, an absent or `null` name reading as empty and a blank but non-empty name drawing nothing here; a field's type-definition reference whose id is absent or empty; a computation's empty computed-field path; a group's index field name written empty; an empty rule condition or error-entity path; and one notification for a computation with any empty operation. An empty error code and a repeated Enumeration value are reported by this rule too, and are specified with their declarations ([§3.3](#33-member-texts-of-rules-and-computations), [§1.3](#enumeration-declarations)). Type definitions' notifications come first, one per defect.

The required attachment rule conditions, by condition language:

| `en_US` | `de_DE` |
|---|---|
| `GroupFilled(RuleGroup) and NotExactlyOneFieldFilled(attachment_id, content)` | `KontextAngegeben(RegelKontext) und NichtGenauEinFeldAngegeben(attachment_id, content)` |
| `FieldFilled(content) and FieldNotFilled(size)` | `FeldAngegeben(content) und FeldNichtAngegeben(size)` |
| `GroupFilled(RuleGroup) and FieldNotFilled(internal_filename)` | `KontextAngegeben(RegelKontext) und FeldNichtAngegeben(internal_filename)` |
| `GroupFilled(RuleGroup) and FieldNotFilled(mime_type)` | `KontextAngegeben(RegelKontext) und FeldNichtAngegeben(mime_type)` |

#### The validation-model converter

**Rule 5 first converts the authored model into the model that code generation, its static checks and evaluation read; a declaration it cannot convert draws a codeless sentence and is left out with everything beneath it, and the check goes on.** A name is blank when Java's `isBlank` holds, an absent or `null` name reading as empty, so the empty name, spaces, a tab, a line break and an em space are blank while a no-break space is not. The converter visits the model in document order:

- **A root group** with a blank name draws the root-name sentence at its path and is left out.
- **A child with a blank name** draws the element-name sentence at its holding group and is left out, whatever its kind; a group draws one such sentence however many of its children are blank-named, and a blank name in each of two groups draws two.
- **A child whose name an earlier kept child of its group already holds** draws the duplicate-child sentence at its own path and is left out, whatever the two kinds; the earlier child is kept and judged. Several later children of one name draw one sentence per element kind among them: three rules draw one, a group and a rule after a field draw two.
- **A field typed by a type definition** whose id is absent, empty or names no definition of the model draws the missing-definition sentence and is kept as a String; a rule naming it draws nothing of its own.
- **A computation** whose `computedFieldRelPath` is empty draws the unspecified-target sentence; one whose target, resolved from the computation against the authored model, names no field draws the unresolved-target sentence; either is left out. A target naming the later of two fields of one name draws the duplicate-child sentence only. A target landing on a group, fixed, repeatable or its own (`..`), or on a rule draws the unresolved-target sentence; on kernel 31.1.1 a group target failed the build. A target walks through the technical model root as a condition's path does: from a computation in `/Order`, `../../Customer/Name` names the root `Customer`'s field and `../../Nope/Name` draws the unresolved-target sentence, while one climbing past the model root leaves no model.
- **A rule** is kept, and its error target resolves on the converted model: a target the converter left out draws `MVK_ERROR_FIELD_MISSING` and `MVK_MISSING_ERROR_FIELD`, measured on a blank-named error field.

A declaration left out draws none of its own classes, measured for a fractional count above its range and a minimum above the maximum, while every other declaration is still judged: a computation cycle and a rule naming no field draw their classes beside a blank-named field's sentence. Rule 6 still reads the authored model, so an empty name, an empty type-definition id and an empty computed-field path add its classes beside the converter's sentences.

**Two compositions leave no model.**

- A computation whose target names a field the converter left out, the field blank-named or inside a blank-named group.
- A root group whose `name` is written exactly `""` and that holds, at any depth, a rule, a computation, a group naming an index field, or a group with a sort entry, an empty error target, computed-field path, index-field name or sort-entry name included; on kernel 31.1.1 those empty references drew the root sentences only. The same root holding only fields, and a rule in a sibling root, draw the root sentences only, and on the measured rows an absent, `null` or blank but non-empty root name does not leave the model unbuilt.

Measured on kernel 31.1.1. The path of each sentence is the one stated; a sentence's position among rule 5's other notifications is not stated, rule 5 being unordered.

Sources: [31.3.1 Letter J](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §2 (computed targets through the model root), [inbound 2026-11-05d](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05d), [basic sentence order](../docs/sources/model-structure-and-declaration-probes.md#src-basic-sentence-order), [inbound 2026-10-29a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29a), [inbound 2026-10-29](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29), [model consistency checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-model-consistency-k17) and its [retained capture](../evidence/kernel-30.8.1/captures/model-consistency-2026-10-13/rows.json) (rows `a-ok`, `a-de-ok`), [executable declaration admission checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-executable-declaration-admission), [inbound 2026-09-26m error-target paths](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-error-target-paths), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27), [M1–M3 declarations adoption](../docs/sources/inbound-handbacks.md#src-m1m3-declarations-adoption).

### 1.3 Declaration generation classes

**Rule 5 of [§1.2](#12-model-consistency-rules) reports its `MVK_*` classes as an unordered collection.** Two models that author the same elements in opposite orders report the same notifications in the same order, and that order is neither the authored one nor a walk, so no order is claimed. A notification identical to another on the same element, same class and same parameters, is reported once. The rule reads the converted model of [§1.2](#the-validation-model-converter): a declaration the converter leaves out draws none of the classes below. A field typed by a type definition is judged on the definition's body, once per referencing field; a definition no field references draws nothing.

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
  - A `minValue` above `maxValue` draws `MVK_MIN_VALUE_BIGGER_THAN_MAX_VALUE`, comparing the bounds as printed for the runtime ([§5 §4](04-numbers-and-decimals.md#4-other-numeric-constraints)): `minValue: 1.4` beside `maxValue: 1` is admitted at no fractional digit and refused at one. The inversion class is withheld beside a bound whose printed form fails its own codeless check, a `-0` at no fractional digit or more than fifteen printed digits.
  - A bound may also be written as text in the decimal grammar of the DM-JSON reader, surrounding spaces trimmed, a sign, a point and an exponent each optional, so `"1e3"`, `"+5"` and `" 5"` are read; other text is a [read failure](#defects-that-leave-no-model).
- **Custom.** A `name` that is absent, empty or blank ([§3.3](#33-member-texts-of-rules-and-computations)) draws `CUSTOM_FIELD_TYPE_CODENAME_MISSING`; any other name with a character outside ASCII letters, digits and `_` draws a codeless notification, a digit or underscore leading included. The length laws read as for String, the inverted pair drawing the unprefixed `MIN_LENGTH_BIGGER_MAX_LENGTH`.
- **Temporal.**
  - A Date, Time, DateTime or DateFragment format outside the thirteen admitted ones of [§6](05-dates-and-time.md#the-format-vocabulary) draws one codeless notification, whatever the kind; an absent format is the kind's default.
  - A DateRange `(format, separator)` pair outside the twelve of [§6 §8.1](05-dates-and-time.md#81-declaration-and-stored-text) draws another, the separator defaulting to `/` and a missing format counting as outside, so `yyyy-MM-dd` alone is admitted and `dd.MM.yyyy` alone refused. Checked as written, without a host's expansion, the empty separator draws it beside `yyyy-MM-dd` and `dd.MM.yyyy`, measured on kernel 31.1.1; `MM` with the empty separator was admitted as written on 30.8.1 and is unmeasured as written on 31.1.1.
  - A partial `datePrecision` on a Date whose format, `yyyy-MM-dd` when absent, is not a complete pure date draws `MVK_OPTIONAL_DATE_TYPE_INVALID`, whose message parameter echoes the format as declared in `en_US` and `de_DE` alike (measured on `yyyy-MM`, `MM-dd` and `HH:mm:ss`; kernel 31.1.1 echoed it in German pattern letters in every locale); the pre-1900 check draws no class on any format, a yearless one included ([§6 §4.1](05-dates-and-time.md#41-the-pre-1900-check)).
  - A DateRange is judged on the format the Kernel composes as format, separator, format, an omitted format composing as the text `null` and an omitted separator as `/`. A composite that is empty after Java's `String.trim`, such as a blank format beside an empty or blank separator, draws `MVK_FORMAT_DATE_RANGE_MISSING` alone, except that a format and a separator both written `""` draw the range-format notification instead, as kernel 31.1.1 does where 30.8.1 drew `MVK_FORMAT_DATE_RANGE_MISSING`; an omitted format draws the invalid-format notification; and a separator other than `-` or `/` after trimming also draws the separator notification, while the pair allowlist reads the separator untrimmed. A supplementary character in either member draws the repertoire notification alone.
  - The temporal bodies' load and build failures are in [§1.2](#defects-that-leave-no-model).
- **`UnspecifiedType`** leaves no model ([§1.1](#member-binding)); kernel 30.8.1 drew `MVK_UNSPECIFIED_TYPE_NO_CODEGEN` for it.
- **Boolean and Confirm** bodies draw nothing.

#### Enumeration declarations

**An Enumeration declaration's laws read every value, label and category token after Java's `String.trim`, and a text carrying a supplementary character draws the repertoire notification in place of every coded class it would draw, the `sValue` included.** So `o\t` is admitted and `BASIC` beside `BASIC\t` draws `MVK_INTERNAL_VALUES_DUPLICATE`, while the charset check, a constant comparison and an index key read the text as written. Block 6 below is the exception to the trim: it compares stored values as written, so `BASIC` beside `BASIC\t` draws no block-6 notification. The repertoire substitution does not apply to notification blocks 1 and 6 below. An empty value is admitted.

- **Labels.** A value carries labels when it has a label in any locale, declared or not; kernel 30.8.1 counted a declared locale's label only. When some values carry labels and others do not, `MVK_COUNT_OF_VALUES_INVALID` is drawn once per declared locale. When a carrying value lacks a text, or has a blank one, for some declared locale, `MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES` is drawn once, so values labelled only for an undeclared locale draw it. Each text two values share in one declared locale draws `MVK_DISPLAY_VALUES_DUPLICATE`, case-sensitively; a label repeated only in an undeclared locale is admitted.
- **Separators.** A tab or `|` draws `MVK_INTERNAL_VALUE_INVALID` per distinct value, `MVK_DISPLAY_VALUE_INVALID` per distinct label text of a declared locale and `MVK_CATEGORY_VALUE_INVALID` per distinct category token; whether kernel 31.1.1 reads an undeclared locale's label for these classes is unmeasured (on 30.8.1 it did not). A line feed or carriage return in any of them draws one codeless notification for the field instead, that text drawing no tab class.
- **S-value.** An `sValue` that is not empty after Java's `String.trim` and equals no value so trimmed, case-sensitively, draws `MVK_S_VALUE_INVALID`: `" BASIC"` names `BASIC`, while a lone no-break space and `basic` name nothing. The runtime stages the default as written, so a padded `sValue` lands as text no value carries.
- **Category tokens pair with the values by position.** A category's `values` list is read entry by entry against the Enumeration's values, and a position holds a token when its entry is a non-blank text, a number or a boolean binding as its text: `[1, true]` beside two values is admitted. A value whose position holds no token, the entry missing, empty, Java-blank or JSON `null`, draws `MVK_MISSING_CATEGORY_VALUE`, so an empty or absent list draws it once per value rather than once for the declaration, and `["HIGH", ""]` draws it for the second value alone. A token past the last value entry, or at the position of an entry declaring no token, draws `MVK_MISSING_INTERNAL_VALUE` once per such token, so two surplus tokens draw it twice, while a blank surplus entry is admitted. An entry written as an object or an array leaves no model. Same-length tokens **disjoint** from the Enumeration's own values are admitted, which separates positional pairing from any set-membership reading, and a same-length reordering is admitted too. Repeated category tokens are admitted. A second category is judged independently of the first, and a body carrying no `categories` member is admitted. An Enumeration with no value entry, a [build failure](#defects-that-leave-no-model), raises no token class. How a category is read at runtime is [§8 B.2](06-strings-and-enumerations.md#b2-categories-via--)'s.
- **Value entries without a token.** A value entry whose `value` member is absent, or misspelled and so absent, declares no token and keeps its position; kernel 30.8.1 left such a model unread. One such entry beside a token, unlabelled, is admitted; at runtime, beside `A` and `C`, those two are valid, `Beta` and `X` draw the domain finding and `""` is absent, and whether the entry contributes any other stored value is unmeasured. When entries exist and none declares a token, `MVK_INTERNAL_VALUES_MISSING` is drawn once. Two or more such entries repeat the absent token: they draw the codeless repeated-value notification once and neither duplicate class. An entry without a token carrying a label draws `MVK_INTERNAL_VALUE_MISSING` beside `MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES`, and how often for two such entries is unmeasured, as is the repeated-value notification's multiplicity here. Its position takes no shortfall notification when a category token stands there; whether it draws one when none does is unmeasured. An empty token on an unlabelled entry beside `PLUS` is admitted. Labelled `None`, beside a labelled `PLUS`, it draws `MVK_INTERNAL_VALUE_MISSING` beside `MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES`; labelled with one declared-locale label whose text is empty, it fails the build ([defects that leave no model](#defects-that-leave-no-model)). Whether a label on another entry has the same effect, how two labelled empty tokens, a labelled empty token at a category position or several labels with one empty text are judged, and how a token-less entry with an empty label text is judged are unmeasured.
- **Category names.** A category whose `name` is absent, empty or Java-blank, an em space included, draws one `MVK_NAME_MISSING` at the field, and that category's tokens draw no class; the named categories are still judged. Its place among the blocks below is not stated. Two categories whose names are absent or empty share one name and fail the build ([§1.2](#defects-that-leave-no-model)), while two distinct blank names, a space and an em space, draw `MVK_NAME_MISSING`.

**An Enumeration field's declaration check collects its notifications rather than stopping at the first, so order and multiplicity are observable.** Every notification is an ERROR, and they arrive in seven blocks, in this order:

| Block | Notifications |
|---|---|
| 1 | Only under a restricted `supportedCharacters` list: one `MVK_ENUM_VALUE_WITH_INVALID_CHARACTER` per rejected UTF-16 code unit of each stored value, one per rejected index. |
| 2 | One codeless supplementary-plane notification for the whole field when any stored value or display label holds a supplementary-plane scalar, under every charset; BMP non-ASCII text does not raise it. |
| 3 | The category token classes, every category's `MVK_MISSING_CATEGORY_VALUE` notifications ahead of every category's `MVK_MISSING_INTERNAL_VALUE` notifications, whatever the category order. |
| 4 | One `MVK_CATEGORY_VALUE_DUPLICATE` per repeated stored value and category. |
| 5 | One `MVK_INTERNAL_VALUES_DUPLICATE` per repeated stored value. |
| 6 | One codeless repeated-value notification per repeated stored value, and one for two or more entries declaring no token. |
| 7 | One `MVK_INTERNAL_VALUES_MISSING` when no entry declares a token. Measured after block 3's `MVK_MISSING_INTERNAL_VALUE` notifications; its place relative to blocks 4–6 is unmeasured. |

- **A stored value holding a supplementary-plane scalar.** In block 1 its high surrogate is rejected even under a range numerically covering it, and its low surrogate is judged alone, rejected unless a declared range numerically covers it: under `A-Z` the scalar counts as two, under `U+0020–U+FFFD` as one, and two scalars sharing a high surrogate in one value under that range count once, while two values sharing it count once each. The one model measured declaring a supplementary range does not build. In block 3 such a value draws no shortfall notification, although its position still counts toward the arity; blocks 4 and 5 skip it, and block 6 does not.
- **Identical notifications collapse:** the same rejected unit twice in one value, or the same surplus token twice in one category, counts once, while equal notifications from different categories stay separate.
- The order of categories or values inside blocks 3 and 4 is not observable through class codes and is not stated.
- <a id="hash-map-order"></a>**Block 6 names each value in a Java `HashMap`'s iteration order**, the map filled by one `computeIfAbsent` call per occurrence of a value after its first, in declaration order, an entry declaring no token counting as the `null` key. The order is the JDK's: a key hashes by `String.hashCode` over UTF-16 code units, `null` by 0, spread as `h ^ (h >>> 16)`; the table opens at 16 buckets with a threshold of three quarters and doubles at the start of any call that finds its size above the threshold, a repeated call for a present key included, splitting each bucket into its low and high halves in order; a new key goes to the head of its bucket, and a new key joining a bucket that already holds seven keys doubles a table of fewer than 64 buckets; and the map iterates bucket by bucket. `OPEN`, `CLOSED`, `PENDING` declared and then repeated in reverse report `CLOSED`, `PENDING`, `OPEN`; `MONTHLY`, `QUARTERLY`, `ANNUAL`, `WEEKLY`, `ONCE` so repeated report `WEEKLY`, `QUARTERLY`, `ONCE`, `ANNUAL`, `MONTHLY`, `QUARTERLY` and `ONCE` sharing a bucket; and thirteen values so repeated cross the threshold, where one more occurrence of the first moves `TRAVEL` and `DENTAL` ahead of `AUTO`; and `PLAN_R1`, `PLAN_A0`, `PLAN_S2`, `PLAN_B1`, `PLAN_T3`, `PLAN_C2`, `PLAN_U4`, `PLAN_D3`, all in one bucket of sixteen, so repeated report `PLAN_U4`, `PLAN_T3`, `PLAN_S2`, `PLAN_R1`, `PLAN_D3`, `PLAN_C2`, `PLAN_B1`, `PLAN_A0`, the eighth key's resize splitting the bucket, while the first seven alone report newest first. A bucket of eight keys in a table of 64 or more becomes a tree, unmeasured; where the `null` key falls among stored values is unmeasured.

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
- **A rule's name** that is digit-initial or dotted produces a codeless consistency notification; an empty or blank rule name is left out by [the converter](#the-validation-model-converter), and an empty one also draws rule 6's empty-name class. An `xml` prefix on a rule is admitted. A computation's name: [§3.3](#33-member-texts-of-rules-and-computations).
- **A computed field's path.** A computed field whose path holds a dot or a colon, from its own name or from a group above it, draws `MVK_ERROR_INVALID_FIELDNAME` at the computation, after the computation's condition, target and index gates; the computed path meets the condition lexer first, so a character the lexer has no terminal for draws `MVK_LEXER_STANDARD_ERROR` there alone.
- **Groups.** An empty group, fixed, repeatable or root, draws nothing. A group's repeatability classes are [§1](#repeatability)'s.

#### Index and sort nomination admission

**A nomination keeps the last segment of its spelling joined to the group's own path, wherever that path lands, and judges that short name against the group's own direct children.** `..` steps up one level from the group itself and every other segment descends; an index nomination and a sort nomination answer alike, each under its own class:

- **A sort entry binds only as an object with both members.** Its `name` is a scalar, and its `order` binds as one of the constants `ASC` and `DESC`: the text `ASC`, `DESC`, `0` or `1` once characters at or below U+0020 are trimmed from both ends, or the integer `0` or `1`. Measured admitted: `" ASC"`, `"\tDESC"`, `"ASC "`, `"DESC\n"`, `"1"`, `" 1"`, `1`, `-0`. Measured leaving no model: an entry that is no object; an absent or `null` `order`; an absent, `null`, object or list `name`; and the orders `"asc"`, `"UP"`, `""`, `"ASC"` followed by an em space, `"01"`, `2`, `-1`, `1.0` and `true`.

| Spelling written in a group | Result |
|---|---|
| absolute (a leading `/`), or climbing above the model root | no model |
| a sort entry's empty name | `MVK_INVALID_SORT_FIELD` at the group, with a codeless unset-name notification |
| a short name no direct child field of the group carries: no element of that name, the parent's field, a rule of the group, a group (as a spelling landing on one does, `..` and a child group's name included), or the number `5` read as its text | `MVK_INVALID_INDEX_FIELD`; `MVK_INVALID_SORT_FIELD` for a sort nomination |
| a short name a direct child field carries, the spelling's landing aside: `../../Sku` and `Items/Sku` in `Items` | the field's own judgment below |
| that direct child field has value validation off | `MVK_INDEX_FIELD_NO_VALUE_VALIDATION`; `MVK_SORT_FIELD_NO_VALUE_VALIDATION` for a sort nomination |
| its kept short name fails the field-name alphabet | a codeless notification at the group |
| an index written `""`, whose short name is the group's own name | `MVK_INVALID_INDEX_FIELD`, beside rule 6's empty-index class |
| an index written blank but not empty | `MVK_INVALID_INDEX_FIELD` alone |
| a sort name written blank but not empty | `MVK_INVALID_SORT_FIELD`, and `MVK_SORT_INFO_MISSING` once for the group however many such entries it has |

- **The local declaration decides, not the referent's.** With `Items` nominating `../Key`, the local `Key` is asked; the parent's `Key` with value validation off changes nothing. Of two local fields both named `Key`, the converter keeps the first ([§1.2](#the-validation-model-converter)), so that one is asked; this is derived from the converter and unmeasured.
- **The alphabet gate reads the kept short name:** `../Items/Sku` draws nothing, and `Sk-u` draws the notification whether or not a field of that name exists. A blank spelling draws no alphabet notification. Only the three sort entries the model holds are judged.
- **Beside each other**, an unresolved index and a sort field with value validation off draw both members' classes. `noValueValidation` on a Number key is admitted.
- **The ordering gates are withheld whenever the model's entity walk refused anything:** the invalid and no-value-validation classes of either nomination are withheld then, measured beside a refused path and beside a count below one on kernel 30.8.1, and on 31.1.1 through the peer checker's agreement with the Kernel on those two rows, while `MVK_SORT_FIELD_DUPLICATE` skips only a refused name, measured on 30.8.1.
- **Every sort nomination is judged.** Two disqualified sort fields draw two classes, and an invalid nomination does not stop the later ones. Each distinct name reports its own class once over the whole list, and a field named more than once among the **first three** entries also draws `MVK_SORT_FIELD_DUPLICATE`, once however often it repeats, beside its own class.
- **The sort list holds at most three entries.** Every entry beyond the third draws its own codeless capacity notification whatever it names; a fourth entry repeating an earlier one draws no duplicate class, and an unresolved fourth still draws its own class.
- **A non-empty `sortFields` on a non-repeatable group**, root included, draws `MVK_INVALID_SORTINFO`.

Sources: [31.3.1 Letter J](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §1 (the inert pre-1900 check) and §3 (the sort entry and the group landing), [inbound 2026-11-05d](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05d), [basic sentence order](../docs/sources/model-structure-and-declaration-probes.md#src-basic-sentence-order), [field declaration notifications checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-field-declaration-notifications-k17), [Enumeration declaration notifications checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-enumeration-declaration-notifications), [declaration report withholding checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14), [sort list capacity checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity), [executable declaration admission checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-executable-declaration-admission), [parameter token versus group declaration alphabet checkpoint](../docs/sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet), [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [inbound 2026-09-26n field message gates](../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates), [inbound 2026-09-27a element paths](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-element-paths), [inbound 2026-09-27a index and sort lookup](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13), [inbound 2026-10-18](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-24a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-24a), [M1–M3 declarations adoption](../docs/sources/inbound-handbacks.md#src-m1m3-declarations-adoption), [M4–M6 condition-language adoption](../docs/sources/inbound-handbacks.md#src-m4m6-condition-language-adoption), [hash-map order adoption](../docs/sources/inbound-handbacks.md#src-hash-map-order-adoption).

### 1.4 Retired variant members

**A declaration's `variantFilter` and a rule's `variantErrorMessages` are read past in every shape, so a model carrying either checks, builds and evaluates exactly as the same model without it.** The DM schema retired both members. Measured on kernel 31.1.1 on a rule, a field and a computation, each beside a twin the model check admits and one it refuses: twelve filter shapes, `ONLY` with a variant, the default variant, an empty list or no list, `ALL_EXCEPT`, an unknown, absent, `null`, object or number `filterType`, JSON `null` and a text, and eight message shapes on a rule. At runtime a rule filtered `ONLY` fires on a document violating it. Kernel 30.8.1 removed a filtered declaration before code generation and refused some of these shapes; that account no longer holds.

Sources: [M1–M3 declarations adoption](../docs/sources/inbound-handbacks.md#src-m1m3-declarations-adoption).

### 1.5 Document uniqueness criteria

**A model may declare document uniqueness criteria: named lists of fields whose combined values no two stored documents may share, each with a per-locale error text. The model check admits a criterion only when it has a name unique among the model's criteria, at least one field, every field named by full path and admissible, and an error text for every declared locale whose parameters name only the criterion's own fields.** The member is `content.documentUniquenessCriteria`, a list of objects with `name`, `fields` (each `{"fullName": <path>}`) and `errorMessage` (each `{"locale", "text"}`). A model without the member, or with an empty list, is admitted. The fields are a set: an item without `fullName` is skipped, the other fields still deciding the criterion, and a field named twice is judged once. A path written with a `.value` suffix names no field. A text parameter is a `$`-delimited full path of one of the criterion's fields, written with or without the `.value` suffix. A text's locale is parsed before it is compared, so a text spelled `en-US` is the text of a model declaring `en_US`, as for a rule message.

A field is admissible when it exists as a field, is required with the requiredness mode `absoluteOrRelativeToNextRepAncestor`, is not transient, and has no repeatable group among its ancestors. Every declared locale needs a text; an empty text is no text, while a blank one is a text. Each refusal below is a notification of the model check that refuses the model; only the last two rows carry a class key:

| Defect, the rest of the criterion admissible | Refusal |
|---|---|
| an empty name | the missing-name refusal |
| an empty field list | the no-field refusal, naming the criterion |
| a field path naming nothing, naming a group, or written as a relative path | the field-not-found refusal, naming the criterion and the path as written |
| a field with no requiredness, or required with mode `relativeToParent` | the field-not-required refusal |
| a field inside a repeatable group | the repeatable-field refusal |
| a transient field | the transient-field refusal |
| no error text, or an empty one, for a declared locale | the missing-text refusal, naming the criterion and the locale |
| two criteria of one name | the duplicate-name refusal, once for each of the two |
| a text parameter naming a field outside the criterion, or naming the criterion's own field by a relative path | the invalid-parameter refusal, naming the criterion and the locale, once for each such parameter |
| an unterminated `$` parameter | the invalid-text refusal, naming the criterion and the locale, with the key `WRONG_NUMBER_OF_DOLLARS` |
| a text holding a line break, a lone surrogate or a control character | the invalid-text refusal with the key `INVALID_LINEBREAK`, `WRONG_ENCODING` or `INVALID_CHARACTERS`, once for the text and before its dollar count |

**The refusals come in a fixed order.** First every name two criteria share, once for each criterion carrying it; several distinct shared names come in the [iteration order](#hash-map-order) of a Java `HashMap` keyed by name and filled by one `computeIfAbsent` call per criterion in model order, so `ProductKey` authored before `PolicyKey` is stated after it. That pair is the one measured row; the map's order itself is measured on block 6's rows. Then, criterion by criterion in model order: the empty name, the empty field list, each field in turn with requiredness before transience, each declared locale with no text, and each stored text of a declared locale in turn with its first failing gate or else its parameter refusals. A text stored for an undeclared locale is unmeasured. A missing field draws only its own refusal and the next field is still judged.

A structure change that leaves a criterion's field missing, including removing the field or the group holding it, is refused like a missing field. **Expansion keeps only the entry model's criteria.** An entry criterion may name a field the entry reaches through an included model and is then admitted and kept. A criterion declared inside an included model is not kept after expansion, whether the include is mounted as a single group or at the model root, and an entry criterion sharing its name is kept over the entry's own fields only. The same included model checked alone is judged as an entry model, so criteria copied into it from a parent that name the parent's fields are refused there as missing fields, while the parent mounting it is admitted.

**Renaming or moving a field rewrites every criterion naming it, in both its field list and its text parameters**, keeping a parameter's `.value` suffix. This was measured for a field rename, a move into a group, and a root rename, through the Kernel's move support. Whether the rewritten model is then admitted was not observed.

**A criterion is a declaration only.** One model validated and computed over the same documents with and without a criterion gives the same messages and computed outcomes on both strategies, so no rule, computation or document validation evaluates it. The check of a model mounting an included one does not judge the included model's criterion, even over a missing field.

Measured scope: on kernel 31.1.1, through the Kernel's model check, on models declaring `en_US` alone and `en_US` with `de_DE`. The order of these refusals against the rules of [§1.2](#12-model-consistency-rules), the order of shared names beyond the one measured pair, the precedence between two text gates on one criterion text, which is measured on rule messages only, and the category keys of the refusals are unmeasured.

Sources: [inbound 2026-11-03a](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-03a), [inbound 2026-11-05](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05), [hash-map order adoption](../docs/sources/inbound-handbacks.md#src-hash-map-order-adoption).

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

- **An array holding a non-object element leaves the whole document unread.** The reader walks the root group's object, the object at every key it reads as a nonrepeatable group, and every row of a repeatable group. If any member of a walked object holds an array with a `null`, scalar or nested-array element, no document is read, whatever the model declares at that key: a repeatable group, a field and an undeclared member all refuse alike, and a row's member refuses as a fixed group's does. The object holding the root group is walked too: the document's own `id` beside the root group refuses the document when it holds such an array, `true` or `null`, and is read when it holds `{}`, `[]` or `[{}]`. An object at a field key or an undeclared key is not walked, so an array inside it is never inspected. A repeatable group's rows are its array's objects in order, at consecutive coordinates, an explicit `{}` included, independently under each parent. Field-valued `null` remains present-empty.
- **A member the model declares nothing for is dropped**, leaving no cell, no group and no validation finding, so a document carrying it validates exactly as the one without. Measured members: an undeclared string or object member of a fixed group; an undeclared string key inside a repeatable row; a boolean, `null`, number or array member of a fixed group; an object in a nested fixed group or inside a row; a string beside the root group. Unmeasured: an undeclared boolean, `null`, number or array member inside a row; an undeclared member of any kind other than a string at the document root; any notification the conversion raises for a dropped member.
- **A declared member whose JSON shape does not fit its declaration** is dropped as an undeclared member is, once the array rule above admits it. Measured members: a number or `null` where a repeatable group is declared; an object, an empty array or an array of objects where a field is declared. Unmeasured: an object where a repeatable group is declared, and an array or scalar where a fixed group is declared.
- **An unquoted document value must be a JSON number.** `abc`, `True`, `NaN`, `0x10`, `01`, `1.`, `.5` or `+1` leaves the whole document unread, while `-0`, `1E1` and `5` are read.
- **A native decimal number keeps its coefficient and signed decimal scale, trailing fractional zeros included.** Before field conversion the reader derives canonical decimal-node text: plain notation when the scale is nonnegative and the adjusted exponent (coefficient digit count minus one minus scale, counting zero as one digit) is at least −6; scientific notation otherwise. Thus native `10.50` supplies `10.50`, `1e3` supplies `1E+3`, and `0.0000001` supplies `1E-7`. A Number destination converts that text to its exact decimal identity; a String destination retains the node text. Quoted scalar text bypasses numeric-node formatting. Re-serializing a native negative-scale number in plain notation before ingestion changes its source identity even when its amount is unchanged. How quoted text reaching a Number destination converts is [§5](04-numbers-and-decimals.md#document-ingestion)'s.

Sources: [M7 runtime-values adoption](../docs/sources/inbound-handbacks.md#src-m7-runtime-values-adoption), [conversion checkpoint](../docs/sources/evaluation-and-application-routes.md#src-json-row-normalization), [undeclared-member checkpoint](../docs/sources/domain-ingestion-probes.md#src-undeclared-document-members), [inbound 2026-10-23](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-23) (KF1), [Number wire ingestion route](../docs/sources/cross-layer-routes.md#src-number-wire-ingestion), [Number ingress checkpoint](../docs/sources/domain-ingestion-probes.md#src-number-ingress-k16), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21).

---

## 3. Rules and computations

A model carries two families of behaviour, both written in the one shared language ([`12-concrete-syntax.md`](12-concrete-syntax.md)).

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
- **A path naming a rule or a computation names nothing in every slot measured.** As an error target it draws the pair above, as a computation's target the computed-field not-found refusal, as a condition operand `MVK_INVALID_ENTITY`, relative or absolute, and as a message parameter `INVALID_ENTITY`, not the unread-field `INVALID_FIELD` (kernel 31.1.1). A computation's path is unmeasured as an absolute operand and as a parameter.
- **A target naming a group is an ordinary declared entity:** with `../Items` as target and a condition reading only `Value`, the rule draws `MVK_ERROR_FIELD_NOT_REFERENCED`, which withholds the error text and gives way to an unresolved name.

**The declared path climbs from the rule element and takes `..` lexically.** From a rule in `/Order`, `../Code` names `/Order/Code`, while `Code` names a child of the rule element and draws `MVK_ERROR_FIELD_MISSING` with `MVK_MISSING_ERROR_FIELD`, beside an unparseable condition too, whose class it withholds. An up-step after a named segment is admitted, `../Meta/../Code` naming `/Order/Code`, where a condition reference refuses it as a token. Under a condition naming no group, a path landing on a group draws `MVK_ERROR_FIELD_NOT_REFERENCED` (`../Meta`, `../Meta/Ref/..`), except on the group the rule is declared in, where the model fails to build and no class is reported, by whichever spelling reaches it (`../Code/..`, `../../Order`); to a rule declared in `/Order/Meta` the root is an ordinary group (`../..`). The walk turns on the technical model root as a condition's does ([§10 §1](08-paths-and-references.md#1-absolute-relative-and-short-name-references)): from a rule in `/Order`, `../../Customer/Name` names a field of the root `Customer` and is admitted beside a condition reading it, and `../../Nope/Name` draws the absent error field's pair. A computation target naming a group is [the converter](#the-validation-model-converter)'s.

#### The referenced-entity inventory

**A rule's referenced-entity inventory is the set of entities its unexpanded condition names.** Each operator contributes by its class in [column Q of the operator reference](14-operator-reference.md#referenced-entity-inventory): a field operand names its field, and a group operand names the group under a `group` class and every field below it under a `fields` class. A starred group on the way to a field is not named, so `Sum(Lines*/Amount)` names `Lines/Amount` and not `Lines`. Beside the operators' contributions the inventory holds a `Having` body's operands; the index field a semantic index keys on, and a key written as a reference; and the join index field a parallel iteration adds. The possible-cause filter compares entity paths against it, and a message's possibly-causing groups read it with each entity's instances.

Measured scope: the field, group-operand, starred-iteration, `Having`-body, semantic-index and cross-root members through the possible-cause filter, and the selected-row index field, the join index field and the `group` class of `GroupNotFilled` and `NumberOfFilledGroups` through the possibly-causing groups; the other group-list quantifiers' and `SumOfTerms`' `group` class is the peer's account. A key written as a reference is unmeasured.

Sources: [31.3.1 Letter J](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §6 and §7.

#### The possible-cause filter

**A rule may restrict which entities its condition reads are offered as the cause of its message.** The DM-JSON member `filterForPossiblyCausingEntities` holds two lists, `entitiesEnabledAsPossibleCauseIfFilled` and `entitiesEnabledAsPossibleCauseIfNotFilled`, of entries `{"relativePath": …}`. Kernel 31.3.1 reads it; on 30.8.1 a model declaring the differently named member `customRefErrorEntitiesIfFilled` did not deserialize, and this member was not tried.

- **What the reader refuses leaves no model:** a filter that is a text, a list, a number or a Boolean; a list that is a text, an object or `null`; an entry that is a text, a number or `null`; an entry whose `relativePath` is absent, `null`, a list or an object; an absolute path; and a leading run of `..` steps climbing above the technical model root from the rule's group (`../..` from `/Policy`, `../../..` from `/Policy/Lines`). A `null` filter, an absent list, an unknown key and an extra member of an entry are read past, and a numeric `relativePath` is read as its text.
- **The spelling map.** Every comparison below first maps an entry: the empty path becomes `./`, and a path ending in `..` gains a trailing `/`, a name ending in `..` included, so `Premium..` and `Premium../` are one entry.
- **Duplicates.** A list holding one mapped entry twice draws `CUSTOM_REF_ERROR_ENTITY_IF_FILLED_DUPLICATE` or `CUSTOM_REF_ERROR_ENTITY_IF_NOT_FILLED_DUPLICATE`. No condition class and no model-check refusal withholds it: `["", "./"]`, `["Rider/..", "Rider/../"]` and `["Premium..", "Premium../"]` are repeats. Its multiplicity for several repeats in one list is unmeasured. An *if filled* list of 1 001 entries also draws a codeless capacity notification, and one of 1 000 entries does not; the *if not filled* list's bound is unmeasured.
- **References.** The model pass's last check refuses an entry that is not the shortest relative path from the rule's group to an entity the condition references, in the mapped spelling: `MVK_REF_ERROR_ENTITY_IF_FILLED_NOT_REFERENCED` or `MVK_REF_ERROR_ENTITY_IF_NOT_FILLED_NOT_REFERENCED`, once per list, naming every failing mapped entry in order, repeats included. The shortest path climbs one `..` for each level below the common ancestor, through the technical root to another root group (`../Agent/Name` from `/Policy`), and is `./` for the rule's own group. So `./Premium`, `Premium/`, ` Premium`, `../Policy/Premium`, `Lines/../Premium` and `Rider//Code` are refused beside a condition reading `Premium` from `/Policy`.
- **The candidates are [the referenced-entity inventory](#the-referenced-entity-inventory).** So `GroupFilled(Rider)` offers `Rider` and not `Rider/Code`, `Sum(Lines*/Amount)` offers `Lines/Amount` and not `Lines`, and `[Amount For "K1"]` in `/Policy/Lines` offers `Key`. Unmeasured for this check: a starred group operand, the field-list expansion of a group operand, a key written as a reference, and the join index field a parallel iteration adds.
- **When the reference check runs.** It does not run when the rule's own check draws a class (measured on an unresolved reference, an incomplete condition and an unreferenced error field), nor when an earlier check of the model pass refuses the model, measured on an invalid time zone and on a sort field naming nothing. A sort field named twice, the rule's own message parameter and another rule's unresolved reference do not withhold it. Which other model checks withhold it is unmeasured.
- **Order.** The reference class and the duplicate class are stated ahead of another rule's condition class, whatever the declaration order.

Sources: [31.3.1 Letter J](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §6, correcting the [error-target checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-error-target-declaration)'s 30.8.1 row.

#### The message and its two pointer channels

**Firing a rule against a repetition context yields either *no message* or a message.** The message carries the error field's `PartiallyKnownDocumentMultiPointer`, the severity, the computed **message type** (VALUE/OMISSION, [§12](10-validation-and-polarity.md)), the interpolated text, and two structured sets of the same message-pointer type. `referenced` reports the condition operands associated with the firing. For an OMISSION, `fillToFix` reports the kernel's omission-responsibility projection, which need not be a minimal set of empty cells whose literal filling alone repairs the rule; a VALUE message has no fill-to-fix pointers. An operator may define a more specific projection, such as the complete duplicate-peer expansion of [`RepetitionNotUnique`](07-repetition-and-iteration.md#6-repetitionnotunique-precisely-). These channels are sets, so no pointer order is specified. A partially known message address is not an exact pointer with a wider integer slot: wildcard/`UNKNOWN` coordinates and partial exact conversion are part of its type ([§2.1](#message-addresses)).

**Ordinary `referenced` pointers are a structural projection of the checked condition, not a trace of the values read during evaluation.** A later `FirstFilledValue` fallback stays referenced even when an earlier operand determined the value. An operator with its own projection, such as `RepetitionNotUnique`, may depend on the document instead.

**What `referenced` contains.**

- A starred *field* retains wildcard `0` at its reopened group context.
- An ordinary non-root *group* operand of either repetition shape expands recursively to its descendant field pointers rather than yielding a group pointer. The relation is identical in the single-operand presence, entity-list quantifier, and numeric filled-count positions, and it is what lets an error field inside the operand group satisfy the reference gate indirectly in all three.
- Root-group presence of either polarity (`GroupFilled`, `AtLeastOneGroupFilled` or `GroupNotFilled` over the root) contributes no fields to either channel beside a field target; on a rule reporting on the root, `GroupFilled` and `GroupNotFilled` over the root contribute none either.
- `Having` field operands and the selected starred value field are included; an unmarked candidate reference is wildcarded, while a `$` reference resolves at its concrete captured outer row.
- `CurrentRepetition` contributes no field pointer, and neither does a form that names no field: a literal, `True`, `False`, `Today`, `Now` or `BaseYear`.
- [The computation's implicit message](09-computations.md#6-the-implicit-validation-rule-precisely) carries each operand's own reach plus the computed target, and lists `fillToFix` by the ordinary omission projection of its generated condition.

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

Measured scope: presence-only operands excluded, an upward count comparison excluded on both sides with its filter operands retained, root-group presence of either polarity contributing no fields, and the `NumberOfFilledFields` rows above. The `presence withheld` and `upward count` members are the closed lists column O names. A connective's union is measured on `And`, where a leaf's contribution and a fired `FieldNotFilled`'s field stand together in the set, and on an `Or` that fires through its second branch while the set still holds the false first branch's field. The `ordinary` class is measured on `>` and `>=` over Number fields, a comparison over a filled field listing that field, and on `GroupNotFilled` and `NoFieldFilled`; that every other operator is `ordinary` is unmeasured.

#### The possibly-causing groups

**A fired message carries a third channel on kernel 31.3.1: a list of pointer sets naming the entities that may have caused it.** A rule's message builds two candidate sets from [its referenced-entity inventory](#the-referenced-entity-inventory), asks one question of each candidate at the firing row, and groups the answers by the message's type.

- **The candidate sets.** Without a filter, the *given* candidates are the whole inventory, and the *not-given* candidates are its omission-responsible subset, chosen as [`fillToFix`](#fill-to-fix-classes) chooses but with group operands kept as groups. With a [possible-cause filter](#the-possible-cause-filter) the given candidates are the inventory's entities its *if filled* list names and the not-given candidates those its *if not filled* list names, so an entity neither list names is in neither set. A filter whose two lists are both empty is not applied.
- **The instances asked.** A candidate is asked at the firing row: a starred level at every row, a level the rule binds at its own row, and a selected entity at the row its key selects. A key selecting no row leaves the entity no instance. A key field that is not check-relevant, formally invalid or irrelevant, leaves the entity in neither set.
- **Given** means at least one instance is filled. **Not given** means not every instance is filled, an aggregated level counted up to its declared capacity with absent rows included; so an aggregated group with fewer rows than its capacity is not given, where the rule-level `NotAllGroupsFilled(G*)` reads only the instantiated rows, and an aggregated root group is always not given, even filled to capacity. A root group at its one instance is not given whenever it is not known to be given, so a root outside a partial validation's relevant set is not given.
- **The groups.** An OMISSION message carries `[not given, given − not given]` and a VALUE message `[given ∪ not given]`. An aggregated level's coordinate is the wildcard `0`.
- **`RepetitionNotUnique`.** Its key cells are named for every row of the reported duplicate cluster, each by its own presence, so an empty key is not given; under a filter only the list naming the key admits them. When the message's polarity comes from another leaf, the cluster is not named.
- **A missed key is named once per key.** A selected entity whose key selects no row is named by a pointer that carries that key, typed as the index field is, so two keys missing the same group are two members of one set although both print the same unresolved coordinate.
- **Other messages.** A formal-check message, `mandatoryField` included, names its own cell as `[[cell]]`, and an evaluation fault names nothing, `[[]]`.

So, over `/Policy` with `Premium` 200 and five-row `Lines` whose rows 1 and 2 hold an `Amount`: `FieldNotFilled(Holder)` carries `[[Holder], []]`; `FieldFilled(Premium) And GroupNotFilled(Rider)` carries `[[Rider], [Premium]]`, where `fillToFix` names `Rider/Code`; `Sum(Lines*/Amount) < [Premium]` carries `[[Lines[0]/Amount], [Premium]]`, and with all five rows filled fires as VALUE carrying `[[Lines[0]/Amount, Premium]]`; and `Sum(Lines*/Amount Having [Note] == "x") < [Premium]`, with every `Amount` filled and no `Note`, carries `[[Lines[0]/Note], [Lines[0]/Amount, Premium]]`, since the filter does not narrow the instances asked about.

Measured on kernel 31.3.1 on both strategies, for every row above and the full validation and partial-validation rows of the source; a group-list quantifier other than `GroupNotFilled` and a `SumOfTerms` iteration as group candidates are the peer's account.

Sources: [31.3.1 Letter J](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §7.

#### Address coordinates

**A message's `referenced` and `fillToFix` entries are partially-known addresses, and one message routinely carries both kinds.** Each is a path plus one coordinate per path part.

**One rule decides a level's coordinate: whether the rule's own iteration bound that level.** A part carries its concrete **1-based** row wherever the rule's iteration bound that level, and every non-repeatable part carries `1`; a repeatable level the iteration left **unbound** carries `0` instead, and one address may carry several. So `0` marks an unbound iterated level and is not row zero: an address is byte-identical across documents holding two rows, two rows, and no rows at all. It is not decided by whether the operand was starred, expanded from a group, or deeper than the anchor: a fixed unstarred group operand reaching through a repeatable descendant produces the same address as a starred field's, a group expanding to non-repeatable fields only leaves nothing unbound, and two references inside a single `Having` differ by nothing but the `$` capture. A non-repeatable group context beneath a starred group's star still carries `1`: over a repeatable `Left` holding the fixed group `Seal`, `NoGroupFilled(Left*/Seal)` and `NoGroupFilled(Left*, Left*)` both reference `/Form[1]/Left[0]/Seal[1]/M`.

Consequences for group operands, by **one depth rule**: a repeatable level *above* the operand stays concrete at the firing row, and every repeatable level *at or below* it is wildcarded.

- For a starred group that boundary is its own star.
- For an unstarred group the boundary is the operand's own group, which the wildcard gate keeps non-repeatable, so the wildcarding begins at the first repeatable level inside the subtree: `/Shipment/Carrier` reaches `/Shipment[1]/Carrier[1]/Handoffs[0]/Site` beside `/Shipment[1]/Carrier[1]/Name`.
- The two forms therefore differ in **where** that boundary falls, not in whether one wildcards at all, and the expansion's wildcarded address is a different address of the same firing from the message's own anchor, which stays concrete throughout ([§9](07-repetition-and-iteration.md)).
- With a `max 2` repeatable ancestor above a fixed group operand, one document fires the rule twice and each firing's expansion carries that ancestor's own row — `/Probe[1]/Outer[1]/Flat[1]/Rows[0]/RowR` beside `/Probe[1]/Outer[2]/Flat[1]/Rows[0]/RowR` — while the wildcarding still begins at the first repeatable level inside the operand's subtree.

Measured scope: the at-or-below half on both forms; the concrete half on the **unstarred** form only, the **starred** form's concrete half being stated from the rule rather than from a witness; the `1` of a non-repeatable group context beneath a star on `AtLeastOneGroupFilled` and `NoGroupFilled` only, a fixed group directly beneath a capacity-two repeatable group's star, alone or beside a fixed or another starred operand, with deeper fixed nesting and other operators unmeasured.

**An address therefore either names exactly one cell or does not**, and a consumer must represent both kinds rather than one shape with an optional index — but it cannot recover the authored operand form from the address, which has to come from the checked condition.

**A12 owns a canonical string only for the exact form** — slashless, repetition one elided, as [§2.1](#21-repetition-contexts-the-iteration-environment) states — and defines neither parser nor renderer for the partially-known one. An observer that prints both kinds therefore chooses its own second form, and two differently-spelled addresses in one artifact may be that choice rather than anything the engine emitted; read the coordinates, not the spelling. The rendered message **text** is a further surface again, carrying a bracket-free declaration path and stating any offending index as a separate rendered number rather than inside the path.

> **Non-normative implementation note.** A faithful `Rule` is roughly `structure Rule where errorCond : Ast; errorField : Path; severity : Severity; text : Template`. There is deliberately no `polarity` or `assert` field — those are *derived* (polarity from the data; the error semantics from "condition true ⇒ invalid").

Sources: [31.3.1 Letter J](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §2 (error targets through the model root), [inbound 2026-11-05d](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05d), [inbound 2026-11-05b](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05b), [message construction route](../docs/sources/message-and-pointer-probes.md#src-message-construction-route), [address dialect checkpoint](../docs/sources/message-and-pointer-probes.md#src-address-dialect-selector), [declaration report withholding checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14), [sort list capacity supplement](../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity), [inbound 2026-09-26m error-target paths](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-error-target-paths), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27), [mixed group predicates](../docs/sources/group-count-topology.md#src-mixed-group-predicates).

### 3.2 Computations

A **computation rule** writes a value into a **computed field**. It has:

- a **target** (the computed field),
- an optional **common precondition**, then one or more **alternatives**. Each alternative contains its operation, an optional precondition, and an optional fixed `toleranceRangeOp`. Within one computation declaration only the sole alternative may omit its precondition, while every row of a multi-alternative declaration is guarded; several declarations for one field concatenate into one table that may hold unguarded rows from separate declarations ([the complete selection account](09-computations.md#53-selection-across-alternatives-and-declarations)). The tolerance metadata does not affect first-match selection or operation evaluation; it changes only that alternative's implicit generated mismatch from strict `!=` to the named fixed tolerance-band predicate ([the precise generated-rule account](09-computations.md#6-the-implicit-validation-rule-precisely)).
- an optional **`errorCode`** that codes the generated validation in place of the computation's name ([§3.3](#33-member-texts-of-rules-and-computations)), and an optional **suppression preamble**, the free text `additionalParserInformation` or the legacy `errorCodesToSuppress` list ([concrete syntax §4](12-concrete-syntax.md#4-directives-and-the-special-entities)).

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

An alternative's precondition written empty draws `MVK_UNEXPECTED_TOKEN` on kernel 31.1.1, while an absent one is admitted. A computation's operation and common precondition draw no missing class under any of the six measured characters.

**The error code's and the rule name's content laws judge the value after Java's `String.trim`.** So `Probe ` and `C\t` are admitted while an em space is kept and refused.

- **Error code.** It admits letters, digits, underscores and ASCII spaces, padding included (`A B`, ` A`), and refuses `A-B` and a no-break space. Beyond ASCII it admits only `Ä`, `Ö`, `Ü`, `ä`, `ö`, `ü` and `ß`, so `Cé`, `Ç`, `Cœ` and an Arabic-Indic digit are refused. A code written as a JSON number is judged as its text.
- **Rule name.** It admits no letter beyond ASCII. A computation's name meets the error-code alphabet as well as the name alphabet of [§1.3](#names-groups-and-texts), unless the computation declares an `errorCode`, which the error-code alphabet then judges in the name's place: `Prem.ium` beside the code `PREMIUM` draws the name's notification alone, and `Premium` beside `PREM-IUM` the code's.
- A supplementary character draws the repertoire notification in place of either content refusal ([§1.1](#the-models-own-texts-meet-the-default-charset)).

**Declaration notifications retain codeless findings as well as named classes.**

- An exactly empty rule error code has a codeless empty-code notification beside `MVK_ERROR_CODE_MISSING`; an ASCII-space-only or vertical-tab-only code has the missing-code class alone. An absent `errorCode` leaves no model ([§1.1](#member-binding)).
- A computation's `errorCode` is optional, and only an absent or `null` member falls back to the name. A string or number is read as its text, so `7` is admitted as the code `7`, while a list leaves no model. An empty or blank declared code draws `MVK_ERROR_CODE_MISSING` alone, with no empty-code notification, rather than falling back to the name. Measured members of the admitted codes: `PREMIUM_MISMATCH`, `PREMIUM MISMATCH`, `PRÄMIE`.
- Independent name and code findings coexist. A malformed rule-name shape, such as a dotted name, suppresses the reserved-prefix class even when the name begins with `vk_vk`; its codeless name notification still coexists with a missing-code finding.
- A member or name that leaves no model: [§1.2](#defects-that-leave-no-model).

Sources: [inbound 2026-09-24b lexer and blank text](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-lexer-and-blank-text), [executable declaration admission checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-executable-declaration-admission), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-11-07](../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07).

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
