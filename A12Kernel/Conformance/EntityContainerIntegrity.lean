import A12Kernel.Elaboration.EntityContainerIntegrity

/-! # Locks on the integrity cascade

The max-value rows are measured on a model declaring repeatability zero; the stage ordering and the
blocking/accumulating split are read from the walk
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-entity-container-integrity)).
-/

namespace A12Kernel.Conformance.EntityContainerIntegrity

open A12Kernel

private def leaf (shape : EntityShape) : EntityTree := .node shape []

/-- A three-level container whose two lower levels are both broken in ways the walk would report. -/
private def brokenSubtree : List EntityTree :=
  [.node { maxValid := false } [leaf { pathValid := false }, leaf { parentPresent := false }]]

/- **The blocking stages are first-match-wins**, in the walk's order: an entity failing several draws
   only the earliest. Four rows, each adding one earlier failure to the last. -/
example :
    entityIntegrityRefusals { parentPresent := false } = [.parentEntityMissing] ∧
      entityIntegrityRefusals { fieldContainsNothing := false, parentPresent := false } =
        [.fieldWithContainedEntities] ∧
      entityIntegrityRefusals
        { pathConsistentWithParent := false, fieldContainsNothing := false,
          parentPresent := false } = [.pathsInconsistent] ∧
      entityIntegrityRefusals
        { pathValid := false, pathConsistentWithParent := false, fieldContainsNothing := false,
          parentPresent := false } = [.pathInvalid] := by
  native_decide

/- **A blocking failure also suppresses the two accumulating stages** on the same entity, which the
   ordering rows above cannot show because they never set a max flag. -/
example :
    entityIntegrityRefusals
      { pathValid := false, maxValid := false, maxConsistentWithParent := false } =
        [.pathInvalid] := by
  native_decide

/- **And it suppresses the whole subtree.** The same broken children report three classes under a
   clear parent and none under a blocked one — one document, one changed flag. -/
example :
    treeIntegrityRefusals (.node {} brokenSubtree) =
        [.maxValuesInvalid, .pathInvalid, .parentEntityMissing] ∧
      treeIntegrityRefusals (.node { pathValid := false } brokenSubtree) = [.pathInvalid] := by
  native_decide

/- **The two accumulating stages are independent**, so all four combinations are distinguishable —
   which is what makes them two checks rather than one reported twice. -/
example :
    entityIntegrityRefusals {} = [] ∧
      entityIntegrityRefusals nonPositiveMaximumShape = [.maxValuesInvalid] ∧
      entityIntegrityRefusals { maxConsistentWithParent := false } = [.maxValuesInconsistent] ∧
      entityIntegrityRefusals absentMaximumShape =
        [.maxValuesInvalid, .maxValuesInconsistent] := by
  native_decide

/- The measured model: a root group at repeatability zero draws the invalid-maximum class on every one
   of its eight entities and the inconsistency class on none, because a uniformly zero tree is still
   internally consistent. -/
example :
    treeIntegrityRefusals
      (.node nonPositiveMaximumShape (List.replicate 7 (leaf nonPositiveMaximumShape))) =
        List.replicate 8 EntityIntegrityRefusal.maxValuesInvalid := by
  native_decide

/- Ten keys, of which six are the per-entity cascade and exactly four of those are blocking. The
   container- and generator-level classes are outside the cascade, which is why they are listed
   separately rather than appended to it. -/
example :
    (EntityIntegrityRefusal.all.map (·.catalogKey)).eraseDups.length = 10 ∧
      EntityIntegrityRefusal.cascade.length = 6 ∧
      (EntityIntegrityRefusal.cascade.filter (·.isBlocking)).length = 4 ∧
      (EntityIntegrityRefusal.all.filter (·.isBlocking)).length = 4 := by
  native_decide

end A12Kernel.Conformance.EntityContainerIntegrity
