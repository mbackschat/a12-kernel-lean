import A12Kernel.Elaboration.EntityContainerIntegrity

/-! # Integrity-cascade laws

The family's content is the split between blocking and accumulating stages. Three results carry it: a
blocking failure yields exactly one class, it silences the entity's whole subtree however large, and
off the blocking stages the two remaining ones are independent so an entity can draw both.
-/

namespace A12Kernel

/-- A blocking failure yields exactly one class, so the accumulating stages are never seen beside it. -/
theorem entityIntegrityRefusals_blocking (shape : EntityShape) (refusal : EntityIntegrityRefusal)
    (h : blockingRefusal shape = some refusal) :
    entityIntegrityRefusals shape = [refusal] := by
  simp [entityIntegrityRefusals, h]

/-- Every class a blocking failure can produce is itself blocking, so the predicate and the cascade
agree rather than being two lists that could drift. -/
theorem blockingRefusal_isBlocking (shape : EntityShape) (refusal : EntityIntegrityRefusal)
    (h : blockingRefusal shape = some refusal) : refusal.isBlocking := by
  unfold blockingRefusal at h
  cases hp : shape.pathValid <;> cases hc : shape.pathConsistentWithParent <;>
    cases hf : shape.fieldContainsNothing <;> cases hq : shape.parentPresent <;>
    simp_all <;> subst h <;> rfl

/-- **The subtree is silenced.** A blocking failure at a node contributes one class and nothing else,
whatever the children are — which is the static counterpart of over-repetition's subtree suppression
and the reason the diagnostic set is not monotone in the model. -/
theorem treeIntegrityRefusals_blocking_hides_subtree (shape : EntityShape)
    (children : List EntityTree) (refusal : EntityIntegrityRefusal)
    (h : blockingRefusal shape = some refusal) :
    treeIntegrityRefusals (.node shape children) = [refusal] := by
  simp [treeIntegrityRefusals, entityIntegrityRefusals, visitsChildren, h]

/-- The same statement in the form a consumer checks: two containers differing only beneath a blocked
node report the same thing. -/
theorem treeIntegrityRefusals_subtree_irrelevant (shape : EntityShape)
    (left right : List EntityTree) (refusal : EntityIntegrityRefusal)
    (h : blockingRefusal shape = some refusal) :
    treeIntegrityRefusals (.node shape left) = treeIntegrityRefusals (.node shape right) := by
  rw [treeIntegrityRefusals_blocking_hides_subtree shape left refusal h,
    treeIntegrityRefusals_blocking_hides_subtree shape right refusal h]

/-- **The two accumulating stages are independent**, so an entity clear of the blocking stages draws
exactly the ones it fails — including both at once. -/
theorem entityIntegrityRefusals_accumulate (shape : EntityShape)
    (h : blockingRefusal shape = none) :
    entityIntegrityRefusals shape =
      (if shape.maxValid then [] else [.maxValuesInvalid]) ++
        (if shape.maxConsistentWithParent then [] else [.maxValuesInconsistent]) := by
  simp [entityIntegrityRefusals, h]

/-- An absent maximum draws both max classes, because the second stage repeats the first's test rather
than assuming it. -/
theorem absentMaximum_draws_both :
    entityIntegrityRefusals absentMaximumShape = [.maxValuesInvalid, .maxValuesInconsistent] := by
  decide

/-- A present non-positive maximum draws only the first, which is what the measured zero-repeatability
model reports. -/
theorem nonPositiveMaximum_draws_one :
    entityIntegrityRefusals nonPositiveMaximumShape = [.maxValuesInvalid] := by
  decide

/-- A well-formed entity draws nothing and its children are visited, which is what makes every law
above a statement about failure rather than an unconditional one. -/
theorem entityIntegrityRefusals_wellFormed :
    entityIntegrityRefusals {} = [] ∧ visitsChildren {} = true := by
  decide

end A12Kernel
