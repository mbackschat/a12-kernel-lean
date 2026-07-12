# 11 — Error-message interpolation and CustomCondition (§13 + §14)

Two small areas. Interpolation is a pure render step over an already-fired message; CustomCondition is the language's one escape hatch to host code — an *opaque oracle* the evaluator is parameterised by.

---

## Part A — §13 Error-message interpolation

The authored error text carries tokens that are resolved against the evaluated document to produce the end-user message.

- **`$Field$`** interpolates the field's **name/label**; **`$Field.value$`** interpolates its **value**. A literal `$` is written **`$$`**.
- For a **field** error text (as opposed to a **rule** error text), the tokens are literally `Field` and `Field.value`, **independent of the actual field name**.
- `$Field.value$` may be used **only if** the field is referenced in the condition at least once **without an asterisk**, and error-text paths **may not contain asterisks**.
- For an **unspecified** value, the interpolation yields **`0` for numbers** and an **empty string** for other types.

What a fired message actually carries:

- The message's error text is the **interpolated end-user text** — tokens already resolved against the evaluated document (the authored template stays in the model). Only the runtime can produce it, because it depends on the data.
- **`$Field$` resolves through a caller-supplied label provider**, not a direct model-label read: a faithful provider returns the field's label for the locale, falling back to the name; with **no** provider configured the engine emits a path+index debug string (`fullName/idx.idx`). In practice surveyed models leave field labels empty, so the token resolves to the field **name**.
- A number's **unit trait** (amount / percent / permille) does **not** render into `$Field.value$` — the interpolation yields the bare number; the unit is a UI concern.

> **Lean modelling note.** Model interpolation as a pure `render : Template → ResolvedTokens → LabelProvider → String`, where `ResolvedTokens` is computed from the fired instance's data (so it lives *after* evaluation, not inside it) and `LabelProvider : FieldRef → Locale → Option String` is an injected parameter (default: fall back to the field name; absent: the debug string). Keep it entirely separate from firing — the *decision* to fire is §1–§12; interpolation only shapes the text of an already-decided message. The `$Field.value$`-needs-a-non-starred-reference rule is a well-formedness check on the template against the condition.

---

## Part B — §14 CustomCondition — the escape hatch

When the language cannot express a check, **`CustomCondition <Name>`** delegates the decision to **host code that the consuming system registers**. The engine parses and places the rule like any other, but calls out to that implementation to decide whether it fires.

```
FieldFilled(id) And CustomCondition NotReverse
```

Constraints and runtime behaviour:

- **Forbidden in computation rules** and **inside filter (`Having`) conditions**.
- Like any predicate it does **not** exempt the rule from the error-field rule ([§9](07-repetition-and-iteration.md)) — here the `FieldFilled(id)` conjunct references the error field. A **bare** `CustomCondition X` referencing no field is rejected (`MVK_ERROR_FIELD_NOT_REFERENCED`).
- At runtime, `CustomCondition X` fires **iff the registered implementation returns `true`**, on an **evaluated row only** ([§2](03-empty-and-required.md)'s row gate — it does *not* fire on an all-empty row), with **VALUE** polarity. A formal error on the fields the rule references **suppresses** it like any operator ([§3](02-logic-and-formal-errors.md)).

**The extensibility surface is closed.** Custom **conditions** and custom **field types** are the engine's *only* custom hooks — there is **no** custom *computation* or function. A computation's operation vocabulary is closed, and `CustomCondition` (the one hook that could reach a computation) is barred there.

> **Lean modelling note.** Parameterise the evaluator by an oracle map `custom : Name → (Env → Document → Bool)` — a total function per registered name. `CustomCondition X` evaluates to `firedValue` iff `custom X env doc = true` *and* the row gate + suppression allow it. For reproducible property tests, the oracles must be **pure and total** (no I/O, no clock); model a missing name as a well-formedness error, not a runtime failure. The "no custom computation/function" fact means the *operation* vocabulary is a fixed closed inductive — you never need an oracle on the compute side.

---

## Checklist for §13 + §14

- [ ] Interpolation is a **pure render step** after firing; `$Field$` via an injected label provider (fallback: name; absent: debug string); `$Field.value$` empty → `0`/empty string; unit trait not rendered.
- [ ] `$Field.value$` requires a non-starred reference; error-text paths asterisk-free.
- [ ] `CustomCondition` = injected **pure total oracle**; VALUE polarity; row-gated; suppressible; must reference the error field; **barred** in computations and filters.
- [ ] Extensibility surface is **closed**: custom conditions + custom field types only; no custom computation/function.
