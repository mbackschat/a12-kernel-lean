# 11 — Error-message interpolation and CustomCondition (§13 + §14)

Two small areas. Interpolation is a pure render step over an already-fired message; `CustomCondition` is the rule language's host-code predicate hook. The separate registered [custom field-type validator](06-strings-and-enumerations.md#a3-custom-field-type-validation) classifies stored cells during formal observation and is not a `CustomCondition`.

---

## Part A — §13 Error-message interpolation

The authored error text carries producer-specific tokens that are resolved against the evaluated document to produce the end-user message. Rule-owned and field-owned templates do not share one grammar.

- In a **rule-owned** error text, **`$Field$`** interpolates the referenced field's **name/label**, **`$Field.value$`** interpolates its **value**, and **`$$`** denotes one literal `$`. `Field` is a rule-relative field path rather than a fixed word.
- A rule-owned `$Field.value$` may be used **only if** the field is referenced in the condition at least once **without an asterisk**, and error-text paths **may not contain asterisks**.
- A rule-owned field reference may instead carry an Enumeration **category** suffix, **`$Field->Category$`**, which is an alternative to the value suffix rather than a further decoration of it. Three static gates apply, in this order: the arrow must be followed by a category name; the referenced field must be an **Enumeration** declaration; and the name must be one of that declaration's declared categories. Unlike the value suffix it requires neither a non-starred reference nor value validation.
- A rule-owned parameter may instead be the **Base Year** terminal — `BaseYear` in English, `Referenzjahr` in German — optionally followed by a signed integer offset, `$BaseYear+3$` or `$BaseYear-1$`. Its only static gate is that the model declares a Base Year; there is no bound on the offset. The interpolated text is the declared Base Year with that offset applied, and it depends on the model alone rather than on the document.
- The parameter grammar's terminals are **bilingual, and only four of them differ**: value/`Wert`, `For`/`Fuer`, `RuleGroup`/`RegelKontext`, and `RootGroup`/`LfdNr`, plus `BaseYear`/`Referenzjahr`. `index`, `Zeile`, `Usb`, `Vordruckzeile`, and `Vordruckname` are spelled the same in both, and `Zeile` and `Usb` are not permitted in an A12 model at all.
- A name that collides with one of the selected condition language's terminals is written in the parameter grammar's **single-quote** escape, and the quotes are erased before any lookup, so an unnecessary quote is transparent. The rule-message producer's requirement is **narrower** than the condition language's: the terminals for value, root-group index, line, USB, form-line, form-name, and `index` are accepted **unquoted** inside an entity name for historic reasons, so only the remaining terminals need the escape. A trailing value terminal is therefore never ambiguous with a name — that terminal is not one of the four a name may end with.
- For a missing or empty rule-owned display value, interpolation uses the referenced field format's exact default supplied by the actual presentation route; it is not inferred from the message locale or model configuration. On the current modern `DocumentV2` route, a Number's minimum fractional digits determine **`0`**, **`0.00`**, and so on, with `.` in the tested US-locale, German-locale, and comma-`decimalSeparator` model configurations; String supplies **`""`**. A distinct legacy or presentation-information route remains unclaimed until separately characterized.
- An `en_US` String pattern's own invalid-value text instead accepts exactly the fixed lowercase tokens **`$field$`** and **`$field.value$`**. The stylized `$Field$` and an actual field name such as `$Code$` are invalid parameters. `$$` is also invalid at this producer because its empty delimited parameter is rejected; it is not a literal-dollar escape.
- String-pattern field replacement is one-pass. With template `Value [$field.value$]` and stored invalid value `$field$`, the resolved text is exactly `Value [$field$]`; inserted bytes never become template syntax.
- Requiredness is a distinct field-owned producer. The measured `en_US` template `Cost $$ $field$` is valid and resolves to `Cost $$ Code` under the tested label-or-name profile, preserving the doubled dollar pair. This witness separates requiredness from String-pattern and rule-owned parsing; it does not establish the complete requiredness grammar.

What a fired message actually carries:

- The message's error text is the **interpolated end-user text** — tokens already resolved against the evaluated document (the authored template stays in the model). Only the runtime can produce it, because it depends on the data.
- A rule-owned **`$Field$` delegates to the runtime identifier-display policy.** On the public service route, an available label-provider result wins exactly, including `""`; otherwise a nonempty localized model label wins; otherwise the resolved identifier's path/index debug representation is used. A configured provider may itself choose label-or-name, but that is caller policy rather than the kernel's built-in fallback.
- A number's **unit trait** (amount / percent / permille) does **not** render into a rule-owned `$Field.value$` — the interpolation yields the bare number; the unit is a UI concern.

> **Non-normative implementation note.** Keep a producer-specific checked parser in front of one shared left-to-right renderer. For a rule-owned template, field-name input is `{ providerResult?, modelLabel?, debugDisplay }` and field-value input is `{ displayValue?, exactFormatDefault }`; a present provider result, including empty output, wins, only a nonempty model label beats the debug display, and a missing or empty display value selects the exact format default. For the measured String-pattern field producer, lower the already-selected owning-field name and value directly to opaque text; do not apply the rule path's lookup or empty-display default and do not admit its `$$` escape. Keep rendering entirely separate from firing or formal classification—the decision and cause are established first, and interpolation shapes only the text of that already-decided result.

---

## Part B — §14 CustomCondition — the escape hatch

When the language cannot express a check, **`CustomCondition <Name>`** delegates the decision to **host code that the consuming system registers**. The engine parses and places the rule like any other, but calls out to that implementation to decide whether it fires.

```
FieldFilled(id) And CustomCondition NotReverse
```

`<Name>` uses the `nameOhnePunkt` token grammar: one or more ASCII letters or digits, `_`, `:`, or `ÄÜÖäüöß`. An unquoted name may begin with a digit, `_`, or `:` and may consist only of digits. A reserved token such as `Today` must be single-quoted as `'Today'`; the quoted form begins with a non-digit name character and otherwise uses the same alphabet. Hyphen, dot, slash, and whitespace are not name characters.

Constraints and runtime behaviour:

- **Forbidden in computation rules** and **inside filter (`Having`) conditions**.
- Like any predicate it does **not** exempt the rule from the error-field rule ([§9](07-repetition-and-iteration.md)) — here the `FieldFilled(id)` conjunct references the error field. A **bare** `CustomCondition X` referencing no field is rejected (`MVK_ERROR_FIELD_NOT_REFERENCED`).
- When ordinary rule evaluation reaches `CustomCondition X`, the kernel invokes the registered callback with four inputs: the document/data view, the partial-validation relevant-entity set (or an all-relevant marker during full validation), the complete set of formally incorrect field instances, and the current rule error-field `PartiallyKnownDocumentMultiPointer` ([§2.1](01-data-model.md#21-repetition-contexts-the-iteration-environment)). Under parallel iteration it may carry `UNKNOWN` and then has no exact-pointer counterpart.
- Formal errors do **not** automatically suppress that invocation. Only the callback knows its hidden dependencies, so the callback contract requires it to inspect relevance and formal-invalid inputs and return `false` when one of its own necessary fields cannot be used. Unrelated formal errors need not decide it. A callback that returns `true` contributes a **VALUE** firing leaf; `false` contributes the kernel's collapsed non-firing/unknown leaf, after which normal `And`/`Or` composition and rule emission apply.
- Empty-row eligibility belongs to the complete condition, not to a callback-internal read set that the kernel cannot see. A `CustomCondition` leaf is structurally classified as able to fire on empty; the common `FieldFilled(id) And CustomCondition X` form is blocked on an empty row by its `FieldFilled` conjunct, while `CustomCondition X Or FieldFilled(id)` may reach the callback on that row.
- A missing registration is a validation integration error. A callback may also throw through the documented host failure route; neither case is silently converted into "did not fire".

**The extensibility surface is closed.** Custom **conditions** and [custom **field types**](06-strings-and-enumerations.md#a3-custom-field-type-validation) are the engine's *only* custom hooks — there is **no** custom *computation* or function. A custom field validator contributes a formal cell observation; `CustomCondition` contributes a rule-predicate result. A computation's operation vocabulary is closed, and `CustomCondition` (the one predicate hook that could otherwise reach a computation) is barred there.

> **Non-normative implementation note.** Introduce an explicit `CustomConditionInvocation` carrying the document/data view, full-versus-partial relevance, the formal-invalid address set, and the current error-field pointer, then parameterise the successful-result fragment by `customConditions : Name → CustomConditionInvocation → Bool`, separate from the custom-field-validator map in `World`. The row gate and surrounding condition decide whether the oracle is invoked; do not derive an `unknown` result merely from a nonempty formal-invalid set. Oracle `true` yields `.fired .value`, and `false` yields the non-firing leaf. Purity and totality are deliberate reproducibility restrictions of the Lean account, not properties enforced by the kernel's host runtime; a missing name is an elaboration/well-formedness error and a thrown host exception is an explicit out-of-theory integration failure. Purity alone does not imply locality or monotonicity, so whole-rule theorems must exclude custom conditions or require an explicit oracle contract. The operation vocabulary on the computation side remains closed.

---

## Checklist for §13 + §14

- [ ] Rule-owned interpolation is a **pure render step** after firing; field names use provider result → nonempty model label → debug priority, with a present empty provider result still winning.
- [ ] A missing or empty rule-owned field display uses the exact format-supplied default; display bytes are opaque, and message rendering neither reads nor renormalizes the evaluation cache. The current `DocumentV2` Number default follows minimum fractional digits and uses `.` in the tested locale/model-config cases; String supplies empty. A number's unit trait is not rendered.
- [ ] Rule-owned `$Field.value$` requires a non-starred reference; error-text paths are asterisk-free.
- [ ] Producer-specific field templates remain distinct: the measured `en_US` String-pattern grammar accepts only lowercase `$field$`/`$field.value$`, rejects `$$`, and inserts opaque bytes once; the measured requiredness witness preserves `$$` and is not generalized to a complete grammar.
- [ ] A reached `CustomCondition` receives document, relevance, formal-invalid addresses, and the current error pointer; its callback—not an evaluator pre-gate—decides its hidden dependencies. `true` is VALUE; whole-condition structure decides empty-row reach; the rule must reference the error field; the construct is **barred** in computations and filters. Lean deliberately admits a pure, total successful-result oracle and treats missing/throwing host callbacks as integration failures.
- [ ] A `CustomCondition` result is distinct from the declaration-driven custom-field formal observation owned by §7.
- [ ] Extensibility surface is **closed**: custom conditions + custom field types only; no custom computation/function.
