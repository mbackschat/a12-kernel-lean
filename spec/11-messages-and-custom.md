# 11 — Error-message interpolation and CustomCondition (§13 + §14)

Two small areas. Interpolation is a pure render step over an already-fired message; `CustomCondition` is the rule language's host-code predicate hook. The separate registered [custom field-type validator](06-strings-and-enumerations.md#a3-custom-field-type-validation) classifies stored cells during formal observation and is not a `CustomCondition`.

---

## Part A — §13 Error-message interpolation

The authored error text carries tokens that are resolved against the evaluated document to produce the end-user message.

- **`$Field$`** interpolates the field's **name/label**; **`$Field.value$`** interpolates its **value**. A literal `$` is written **`$$`**.
- For a **field** error text (as opposed to a **rule** error text), the tokens are literally `Field` and `Field.value`, **independent of the actual field name**.
- `$Field.value$` may be used **only if** the field is referenced in the condition at least once **without an asterisk**, and error-text paths **may not contain asterisks**.
- For a missing or empty display value, interpolation uses the referenced field format's exact default for the active presentation information and locale. Common externally differentiated defaults are **`0` for a scale-zero Number** and **`""` for String**; Number scale/locale and other formats are not collapsed to universal per-kind literals.

What a fired message actually carries:

- The message's error text is the **interpolated end-user text** — tokens already resolved against the evaluated document (the authored template stays in the model). Only the runtime can produce it, because it depends on the data.
- **`$Field$` delegates to the runtime identifier-display policy.** On the public service route, an available label-provider result wins exactly, including `""`; otherwise a nonempty localized model label wins; otherwise the resolved identifier's path/index debug representation is used. A configured provider may itself choose label-or-name, but that is caller policy rather than the kernel's built-in fallback.
- A number's **unit trait** (amount / percent / permille) does **not** render into `$Field.value$` — the interpolation yields the bare number; the unit is a UI concern.

> **Lean modelling note.** Model interpolation as a pure post-fire render over structured, already-resolved inputs. Field-name input is `{ providerResult?, modelLabel?, debugDisplay }`; field-value input is `{ displayValue?, exactFormatDefault }`. A present provider result, including empty output, wins; only a nonempty model label beats the debug display. A missing or empty display value selects the exact format default. Do not derive these display inputs from core `Value` or the normalized evaluation cache; replacement text is opaque and processed once. Keep rendering entirely separate from firing — the *decision* to fire is §1–§12; interpolation only shapes the text of an already-decided message. The `$Field.value$`-needs-a-non-starred-reference rule is a well-formedness check on the template against the condition.

---

## Part B — §14 CustomCondition — the escape hatch

When the language cannot express a check, **`CustomCondition <Name>`** delegates the decision to **host code that the consuming system registers**. The engine parses and places the rule like any other, but calls out to that implementation to decide whether it fires.

```
FieldFilled(id) And CustomCondition NotReverse
```

Constraints and runtime behaviour:

- **Forbidden in computation rules** and **inside filter (`Having`) conditions**.
- Like any predicate it does **not** exempt the rule from the error-field rule ([§9](07-repetition-and-iteration.md)) — here the `FieldFilled(id)` conjunct references the error field. A **bare** `CustomCondition X` referencing no field is rejected (`MVK_ERROR_FIELD_NOT_REFERENCED`).
- When ordinary rule evaluation reaches `CustomCondition X`, the kernel invokes the registered callback with four inputs: the document/data view, the partial-validation relevant-entity set (or an all-relevant marker during full validation), the complete set of formally incorrect field instances, and the current rule error-field pointer (possibly partially known under parallel iteration).
- Formal errors do **not** automatically suppress that invocation. Only the callback knows its hidden dependencies, so the callback contract requires it to inspect relevance and formal-invalid inputs and return `false` when one of its own necessary fields cannot be used. Unrelated formal errors need not decide it. A callback that returns `true` contributes a **VALUE** firing leaf; `false` contributes the kernel's collapsed non-firing/unknown leaf, after which normal `And`/`Or` composition and rule emission apply.
- Empty-row eligibility belongs to the complete condition, not to a callback-internal read set that the kernel cannot see. A `CustomCondition` leaf is structurally classified as able to fire on empty; the common `FieldFilled(id) And CustomCondition X` form is blocked on an empty row by its `FieldFilled` conjunct, while `CustomCondition X Or FieldFilled(id)` may reach the callback on that row.
- A missing registration is a validation integration error. A callback may also throw through the documented host failure route; neither case is silently converted into "did not fire".

**The extensibility surface is closed.** Custom **conditions** and [custom **field types**](06-strings-and-enumerations.md#a3-custom-field-type-validation) are the engine's *only* custom hooks — there is **no** custom *computation* or function. A custom field validator contributes a formal cell observation; `CustomCondition` contributes a rule-predicate result. A computation's operation vocabulary is closed, and `CustomCondition` (the one predicate hook that could otherwise reach a computation) is barred there.

> **Lean modelling note.** Introduce an explicit `CustomConditionInvocation` carrying the document/data view, full-versus-partial relevance, the formal-invalid address set, and the current error-field pointer, then parameterise the successful-result fragment by `customConditions : Name → CustomConditionInvocation → Bool`, separate from the custom-field-validator map in `World`. The row gate and surrounding condition decide whether the oracle is invoked; do not derive an `unknown` result merely from a nonempty formal-invalid set. Oracle `true` yields `.fired .value`, and `false` yields the non-firing leaf. Purity and totality are deliberate reproducibility restrictions of the Lean account, not properties enforced by the kernel's host runtime; a missing name is an elaboration/well-formedness error and a thrown host exception is an explicit out-of-theory integration failure. Purity alone does not imply locality or monotonicity, so whole-rule theorems must exclude custom conditions or require an explicit oracle contract. The operation vocabulary on the computation side remains closed.

---

## Checklist for §13 + §14

- [ ] Interpolation is a **pure render step** after firing; field names use provider result → nonempty model label → debug priority, with a present empty provider result still winning.
- [ ] A missing or empty field display uses the exact format-supplied default; display bytes are opaque, and message rendering neither reads nor renormalizes the evaluation cache. Scale-zero Number `0` and String empty are common differentiated instances, not a universal formatter; a number's unit trait is not rendered.
- [ ] `$Field.value$` requires a non-starred reference; error-text paths asterisk-free.
- [ ] A reached `CustomCondition` receives document, relevance, formal-invalid addresses, and the current error pointer; its callback—not an evaluator pre-gate—decides its hidden dependencies. `true` is VALUE; whole-condition structure decides empty-row reach; the rule must reference the error field; the construct is **barred** in computations and filters. Lean deliberately admits a pure, total successful-result oracle and treats missing/throwing host callbacks as integration failures.
- [ ] A `CustomCondition` result is distinct from the declaration-driven custom-field formal observation owned by §7.
- [ ] Extensibility surface is **closed**: custom conditions + custom field types only; no custom computation/function.
