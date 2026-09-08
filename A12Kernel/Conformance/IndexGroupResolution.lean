import A12Kernel.Elaboration.IndexGroupResolution

/-! # Locks on the index-group walk

The two-groups class is measured against the real Kernel with two admitted controls; the several-names
and broken-name classes are source-derived, each with a measured reason why this project's carrier
cannot reach it ([checkpoint](../../docs/SOURCES.md#src-index-group-resolution)).
-/

namespace A12Kernel.Conformance.IndexGroupResolution

open A12Kernel

/-- A group carrying no index. Invisible to the walk. -/
private def plain : IndexDeclaringGroup := {}

/-- The ordinary index group: one name, and it resolves. -/
private def indexed : IndexDeclaringGroup := { declaredNames := 1 }

/-- An index group declaring three names. -/
private def overDeclared : IndexDeclaringGroup := { declaredNames := 3 }

/-- The boundary: exactly two declared names, the smallest count that is "several". -/
private def justOverDeclared : IndexDeclaringGroup := { declaredNames := 2 }

/-- An index group whose single declared name names nothing in it. -/
private def brokenName : IndexDeclaringGroup :=
  { declaredNames := 1, nameResolvesToField := false }

private def key? (path : List IndexDeclaringGroup) : Option String :=
  (indexResolutionRefusal path).map KernelStaticDiagnostic.kernelCode

/- **The measured triple.** A field two index-declaring groups deep draws the two-groups class under
   a parallel-iterating condition; the same condition against a field one index group deep is
   admitted; and a field two index groups deep under a condition that never runs the walk is admitted
   too. The third row is what shows the class belongs to the walk rather than to the model shape. -/
example :
    key? [indexed, plain, indexed] = some "MVK_MULTIPLE_INDEX_FIELDS" ∧
      key? [indexed, plain, plain] = none ∧
      key? [] = none := by
  native_decide

/- **Only the innermost index group's count is examined.** One nesting, two spellings, two classes —
   and the same two groups separated by a non-index group behave identically, so the adjacency plays
   no part. -/
example :
    key? [indexed, overDeclared] = some "MVK_MULTIPLE_INDEX_FIELDS" ∧
      key? [overDeclared, indexed] = some "MVK_MULTIPLE_INDEX_FIELDS2" ∧
      key? [indexed, plain, overDeclared] = some "MVK_MULTIPLE_INDEX_FIELDS" ∧
      key? [overDeclared, plain, indexed] = some "MVK_MULTIPLE_INDEX_FIELDS2" := by
  native_decide

/- **A sole over-declared group reports the several-names class**, so that class does not require a
   second index group and the pair above is an ordering rather than a coincidence. The middle pair
   pins the boundary at two rather than at three: one name is the admitted count and two is already
   "several", which a fixture declaring three cannot distinguish. -/
example :
    key? [overDeclared] = some "MVK_MULTIPLE_INDEX_FIELDS2" ∧
      key? [justOverDeclared] = some "MVK_MULTIPLE_INDEX_FIELDS2" ∧
      key? [indexed] = none ∧
      key? [plain, overDeclared, plain] = some "MVK_MULTIPLE_INDEX_FIELDS2" := by
  native_decide

/- **The name is resolved strictly after the walk.** A broken name alone reports its own class; the
   same broken name under any walk refusal is silent, and it is silent even when the broken group is
   the *outer* one the walk never settles on. -/
example :
    key? [brokenName] = some "MVK_INDEX_FIELD_INVALID" ∧
      key? [brokenName, indexed] = some "MVK_MULTIPLE_INDEX_FIELDS" ∧
      key? [indexed, brokenName] = some "MVK_MULTIPLE_INDEX_FIELDS" ∧
      key? [plain, brokenName, plain] = some "MVK_INDEX_FIELD_INVALID" := by
  native_decide

/- **Absence is not a refusal, and it is the ordinary model.** Any path of non-index groups resolves
   to nothing, and the sole well-formed index group resolves to itself — the two admitted shapes that
   keep this vocabulary off an ordinary model entirely. -/
example :
    resolvedIndexGroup? [plain, plain, plain] = none ∧
      key? [plain, plain, plain] = none ∧
      resolvedIndexGroup? [plain, indexed, plain] = some indexed ∧
      indexDeclaringGroups [plain, indexed, plain, overDeclared] = [indexed, overDeclared] := by
  native_decide

end A12Kernel.Conformance.IndexGroupResolution
