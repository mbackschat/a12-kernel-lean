import A12Kernel.Elaboration.ErrorTargetDeclaration

/-! # Locks on the error-target declaration gates

The two cascade classes, the missing-declaration class, and the whole-rule reference class are
measured against the real Kernel; the other four are source-derived and honestly unwitnessed
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-error-target-declaration)). The matrix separates the two
declaration classes under lenience, the branch the overlapping reference roles decide, the cascade's
model split and internal order, and the accumulating custom gate against the first-match-wins gates
beside it.
-/

namespace A12Kernel.Conformance.ErrorTargetDeclaration

open A12Kernel

/-- A reference the condition makes to the error field itself. -/
private def directReference : ConditionReference := { sameEntity := true }

/-- A reference to the error field's root group. -/
private def formReference : ConditionReference :=
  { isGroup := true, isRootGroup := true, ancestorOrEqual := true }

/-- A reference to an intermediate group containing the error field. -/
private def containingReference : ConditionReference :=
  { isGroup := true, ancestorOrEqual := true }

/-- The error field is itself a non-root group, so one reference fills two roles at once. -/
private def groupErrorFieldReference : ConditionReference :=
  { sameEntity := true, isGroup := true, ancestorOrEqual := true }

private def formOnly (hModel : Bool) (profile : IterationProfile) : ErrorTargetInput :=
  { hModel, declaration := .declared true, references := [formReference], iteration := profile }

private def key? (input : ErrorTargetInput) : Option String :=
  (conditionSideRefusal input).map KernelStaticDiagnostic.kernelCode

/- **A missing error field hides everything the condition would say.** The same condition — no
   reference to the error field, an inner iteration, and a parallel iteration off the root level —
   reports three different classes as the declaration improves, and the two conditional classes
   appear only once the declaration is clear. -/
example :
    key? { declaration := .absent, iteration := { firstInnerLevel := some 1 } } =
        some "MVK_MISSING_ERROR_FIELD" ∧
      key? { declaration := .declared false, iteration := { firstInnerLevel := some 1 } } =
        some "MVK_ERROR_FIELD_NOT_VALID" ∧
      key? { declaration := .declared true, iteration := { firstInnerLevel := some 1 } } =
        some "MVK_ERROR_FIELD_NOT_REFERENCED" ∧
      key? (formOnly false { firstInnerLevel := some 1 }) =
        some "MVK_ERROR_FIELDGROUP_ITERATION4_INVALID" := by
  native_decide

/- **Lenience excuses the unknown name and not the missing one.** One flag changed on each of the two
   declarations, so the asymmetry cannot be read as lenience weakening the whole gate. -/
example :
    key? { lenient := true, declaration := .absent } = some "MVK_MISSING_ERROR_FIELD" ∧
      key? { lenient := true, declaration := .declared false, references := [directReference] } =
        none ∧
      key? { declaration := .declared false, references := [directReference] } =
        some "MVK_ERROR_FIELD_NOT_VALID" := by
  native_decide

/- **The cascade opens only when no direct and no containing reference exists.** Same iteration
   profile in all four rows; only the reference list moves. -/
example :
    key? (formOnly false { firstInnerLevel := some 2 }) =
        some "MVK_ERROR_FIELDGROUP_ITERATION4_INVALID" ∧
      key? { declaration := .declared true, references := [formReference, directReference],
             iteration := { firstInnerLevel := some 2 } } = none ∧
      key? { declaration := .declared true, references := [formReference, containingReference],
             iteration := { firstInnerLevel := some 2 } } = none ∧
      key? { declaration := .declared true, references := [groupErrorFieldReference],
             iteration := { firstInnerLevel := some 2 } } = none := by
  native_decide

/- **The sub-scope-count escape admits the unreferenced error field and still runs the cascade.** The
   pair differs in that flag alone, and the second row proves the escape is not an exemption. -/
example :
    key? { declaration := .declared true,
           iteration := { parallelIteration := true, indexFieldLevel := 1 } } =
        some "MVK_ERROR_FIELD_NOT_REFERENCED" ∧
      key? { declaration := .declared true, anzahlAngegebenerUsb := true,
             iteration := { parallelIteration := true, indexFieldLevel := 1 } } =
        some "MVK_ERROR_FIELDGROUP_ITERATION5_INVALID" := by
  native_decide

/- **Parallel iteration turns on the rule's index-field level, and the PARALLEL class decides first.**
   Four rows over one profile: the level guard both ways, then the order, then the parallel flag
   itself. The third row is the separator — a profile offending both classes answers with the
   parallel one, which the peer measured in both authored text orders precisely because a single
   order cannot distinguish that from "the later read wins"
   ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections)). -/
example :
    key? (formOnly false { parallelIteration := true, indexFieldLevel := 1 }) =
        some "MVK_ERROR_FIELDGROUP_ITERATION5_INVALID" ∧
      key? (formOnly false { parallelIteration := true, indexFieldLevel := 0 }) = none ∧
      key? (formOnly false
        { firstInnerLevel := some 1, parallelIteration := true, indexFieldLevel := 1 }) =
        some "MVK_ERROR_FIELDGROUP_ITERATION5_INVALID" ∧
      key? (formOnly false { parallelIteration := false, indexFieldLevel := 1 }) = none := by
  native_decide

/- **The cascade's three classes split across the two model kinds**, so no model produces all three.
   Each row pairs one profile against both kinds. -/
example :
    key? (formOnly true { rowIteration := true }) =
        some "MVK_ERROR_FIELD_AND_ZITERATION_INVALID" ∧
      key? (formOnly false { rowIteration := true }) = none ∧
      key? (formOnly true
        { firstInnerLevel := some 1, parallelIteration := true, indexFieldLevel := 1 }) = none := by
  native_decide

/- **The measured matrix, replayed one row for one row.** Four rules over two models, differing in
   one axis each: a form-only reference alone is admitted; the same reference with the rule's own
   group binding a deeper level draws the plain-iteration class; the same reference with a sibling
   indexed group instead draws the parallel one; and adding a direct reference to that last condition
   admits it, which is what identifies the branch rather than the iteration as the cause
   ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-error-target-declaration)). -/
example :
    key? (formOnly false {}) = none ∧
      key? (formOnly false { firstInnerLevel := some 1 }) =
        some "MVK_ERROR_FIELDGROUP_ITERATION4_INVALID" ∧
      key? (formOnly false { parallelIteration := true, indexFieldLevel := 1 }) =
        some "MVK_ERROR_FIELDGROUP_ITERATION5_INVALID" ∧
      key? { declaration := .declared true, references := [formReference, directReference],
             iteration := { parallelIteration := true, indexFieldLevel := 1 } } = none := by
  native_decide

private def customKeys (hModel conditionParsed : Bool) (fromCondition : List String)
    (declaration : CustomErrorEntityDeclaration) : List String :=
  (customErrorEntityRefusals hModel conditionParsed fromCondition declaration).map
    KernelStaticDiagnostic.kernelCode

/- **The custom gate accumulates and reports once per slot.** Three rows over one candidate set: one
   offending slot, both, and a slot offending three times over. -/
example :
    customKeys false true ["Rows/Qty"] { ifFilled := ["Rows/Missing"] } =
        ["MVK_REF_ERROR_ENTITY_IF_FILLED_NOT_REFERENCED"] ∧
      customKeys false true ["Rows/Qty"]
        { ifFilled := ["Rows/Missing"], ifNotFilled := ["Rows/Absent"] } =
        ["MVK_REF_ERROR_ENTITY_IF_FILLED_NOT_REFERENCED",
         "MVK_REF_ERROR_ENTITY_IF_NOT_FILLED_NOT_REFERENCED"] ∧
      customKeys false true ["Rows/Qty"]
        { ifFilled := ["Rows/A", "Rows/B", "Rows/C"] } =
        ["MVK_REF_ERROR_ENTITY_IF_FILLED_NOT_REFERENCED"] := by
  native_decide

/- **Membership is exact string equality, and an H model offers no candidates at all.** The same
   declared path is admitted against a matching candidate, refused against a near-miss spelling, and
   refused in an H model against the candidate that admitted it. -/
example :
    customKeys false true ["Rows/Qty"] { ifFilled := ["Rows/Qty"] } = [] ∧
      customKeys false true ["Rows/Qty"] { ifFilled := ["Rows/qty"] } =
        ["MVK_REF_ERROR_ENTITY_IF_FILLED_NOT_REFERENCED"] ∧
      customKeys true true ["Rows/Qty"] { ifFilled := ["Rows/Qty"] } =
        ["MVK_REF_ERROR_ENTITY_IF_FILLED_NOT_REFERENCED"] := by
  native_decide

/- **A condition that did not parse suppresses both classes**, and two empty slots never reach the
   parse at all — the second fact is the one that keeps an empty declaration from being read as an
   admitted one. -/
example :
    customKeys false false ["Rows/Qty"] { ifFilled := ["Rows/Missing"] } = [] ∧
      customKeys false true [] {} = [] ∧
      CustomErrorEntityDeclaration.parsesCondition {} = false ∧
      CustomErrorEntityDeclaration.parsesCondition { ifNotFilled := ["Rows/A"] } = true := by
  native_decide

end A12Kernel.Conformance.ErrorTargetDeclaration
