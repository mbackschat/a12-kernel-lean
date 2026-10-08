import A12Kernel.Elaboration.IterationLegality

/-! # Locks on iteration and semantic-index static legality

Each case fixes one reading a consumer would otherwise adopt: that a wildcard is local to its own level, that the refusal class names the defect, or that `RepetitionNotUnique` and parallel iteration are independently legal.

The ordinary-reference and parallel-iteration cases have measured witness rules and admitted controls: the parallel-iteration gate distinguishes a construct legal alone from its illegal combination ([checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-iteration-and-semantic-index-legality)).
-/

namespace A12Kernel.Conformance.IterationLegality

open A12Kernel

/-- Iterating a repeatable ancestor of the error field — the ordinary case, measured admitted. -/
private def ownAncestor : IndexedReference :=
  { levels := [{ marker := .iteration, relation := .aboveOrEqualErrorPath }] }

/-- The measured legal parallel iteration: a sibling group off the error path, matched by an
index field of the same name. -/
private def siblingParallel : IndexedReference :=
  { levels := [{ marker := .iteration, relation := .offPathParallelIterable }] }

/- The two admitted references. Neither is decoration: the second is the whole reason
   `offPathParallelIterable` exists as a relation distinct from `offPathNotParallelIterable`, and
   collapsing them would refuse a rule the Kernel accepts. -/
example :
    referenceRefusal ownAncestor = none ∧ referenceRefusal siblingParallel = none := by
  native_decide

/- Off the error path with no index field to match the walks, the same reference refuses — so the
   relation, not the marker, decides. -/
example :
    referenceRefusal { siblingParallel with
        levels := [{ marker := .iteration, relation := .offPathNotParallelIterable }] } =
      some .noWildcard ∧
      referenceRefusal { levels := [{ marker := .iteration, relation := .belowErrorPath }] } =
        some .noWildcard := by
  native_decide

/- A wildcard poisons the levels below it and nothing above. The same inner level is legal when the
   outer level is a fixed repetition and refused when it is a wildcard — one changed marker at a
   level the inner reference does not mention. -/
example :
    referenceRefusal { levels :=
        [{ marker := .fixed }, { marker := .iteration, relation := .aboveOrEqualErrorPath }] } =
      none ∧
      referenceRefusal { levels :=
        [{ marker := .wildcard }, { marker := .iteration, relation := .aboveOrEqualErrorPath }] } =
      some .noWildcard := by
  native_decide

/- The same for a semantic index, and this arm carries its own class: below a wildcard it is
   `semanticIndexBelowWildcard`, not the iteration class. The measured witness is a semantic index
   under a starred outer group. -/
example :
    referenceRefusal { levels := [{ marker := .fixed }, { marker := .semanticIndex }] } = none ∧
      referenceRefusal { levels := [{ marker := .wildcard }, { marker := .semanticIndex }] } =
        some .semanticIndexBelowWildcard := by
  native_decide

/- The rule's own iteration addresses the level above the index group where a star does not: from
   inside `Regions`, `Regions/Stores For "S1"` is admitted, while the starred `Regions*/Stores For
   "S1"` from the same rule is the lock above, the star's level carrying no relation the scan reads
   ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26c-star-above-index)). No row measures the
   other iterated relations, such as an off-path parallel level, which the scan also admits. -/
example :
    referenceRefusal { levels :=
        [{ marker := .iteration, relation := .aboveOrEqualErrorPath }, { marker := .semanticIndex }] } =
      none := by
  native_decide

/- Only an *outer* wildcard poisons: a wildcard at the last level, or after the iteration it would
   otherwise have poisoned, leaves the reference legal. The direction is what matters, and reversing
   the two levels of the second reference below is exactly the case above. -/
example :
    referenceRefusal { levels := [{ marker := .wildcard }] } = none ∧
      referenceRefusal { levels :=
        [{ marker := .iteration, relation := .aboveOrEqualErrorPath }, { marker := .wildcard }] } =
        none := by
  native_decide

/- The bit survives levels that neither set nor read it, so a wildcard reaches an iteration several
   levels below with inert levels in between. A consumer that recomputes the bit per level instead
   of carrying it admits this reference. -/
example :
    referenceRefusal { levels :=
        [{ marker := .wildcard }, { marker := .fixed },
         { marker := .iteration, relation := .aboveOrEqualErrorPath }] } = some .noWildcard ∧
      referenceRefusal { levels :=
        [{ marker := .fixed }, { marker := .fixed },
         { marker := .iteration, relation := .aboveOrEqualErrorPath }] } = none := by
  native_decide

/- The class follows the reference, not the defect. Two references break the *same* rule — an
   iteration below the error path — and report different classes because one is read inside a
   semantic index's key. A consumer switching on the code to decide what went wrong gets this
   backwards. -/
example :
    referenceRefusal { levels := [{ marker := .iteration, relation := .belowErrorPath }],
                       insideSemanticIndexKey := false } = some .noWildcard ∧
      referenceRefusal { levels := [{ marker := .iteration, relation := .belowErrorPath }],
                         insideSemanticIndexKey := true } = some .semanticIndexInvalidIter := by
  native_decide

/- The flag is where the reference stands, not whether it carries the index. From `/It/A`,
   `[/It/P/Q/QV For "q1"]` crosses the unindexed `P` above its index group and draws the wildcard
   class although it carries the index (`SIwild3`), while `[/It/L/V For /It/P/Q/QV]`, whose key makes
   the same crossing, draws the semantic-index class (`SIkeySI`, the case above). The peer's
   `Riders/Legs/Amount For "X"` beside `Claims/Amount For Riders/RiderRef` repeats the pair
   ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-key-addressing)). Deriving the flag from the
   index marker would give this keyed value the semantic-index class. -/
example :
    referenceRefusal { levels := [{ marker := .iteration, relation := .belowErrorPath },
                                  { marker := .semanticIndex }] } = some .noWildcard := by
  native_decide

/- First match wins across levels: the outermost illegal level answers, and a later level that
   would report a different class never gets to. -/
example :
    referenceRefusal
        { levels := [{ marker := .iteration, relation := .belowErrorPath },
                     { marker := .wildcard }, { marker := .semanticIndex }],
          insideSemanticIndexKey := false } = some .noWildcard := by
  native_decide

/- Markers that name no repetition walk are inert at every position, including below a wildcard —
   so the absorbing bit reaches iteration and the semantic index and nothing else. -/
example :
    referenceRefusal { levels :=
        [{ marker := .wildcard }, { marker := .fixed }, { marker := .unspecified }] } = none := by
  native_decide

/- The semantic index's own entity check is ordered, and its first arm is the one that fires on the
   measured witness: two index fields on the referenced path make the index ambiguous before the
   key's category reach is ever examined. -/
example :
    semanticIndexRefusal { ambiguousIndexPath := true, keyReachesCategory := true } =
        some .multipleIndexFields ∧
      semanticIndexRefusal { keyReachesCategory := true } = some .semanticIndexWithCategory ∧
      semanticIndexRefusal {} = none := by
  native_decide

/- The whole-condition gate's content is the combination, not either construct. `RepetitionNotUnique`
   alone is measured legal; parallel iteration alone is measured legal; together they refuse. -/
example :
    conditionRefusal { repetitionNotUnique := true } = none ∧
      conditionRefusal { parallelIteration := true } = none ∧
      conditionRefusal { parallelIteration := true, repetitionNotUnique := true } =
        some .parallelIterationNotAllowed := by
  native_decide

/- A parallel-iterated condition whose leaves are all negative refuses; one positive leaf clears it.
   Both are measured, and the pair is what shows the test is about leaf polarity rather than about
   the presence of a negative leaf. -/
example :
    conditionRefusal { parallelIteration := true, allLeavesNegative := true } =
        some .parallelIterationInvalid ∧
      conditionRefusal { parallelIteration := true, allLeavesNegative := false } = none := by
  native_decide

/- The gate is ordered: a condition breaking two of its tests reports the first, and the
   all-negative test is last, so it is masked by either earlier one. -/
example :
    conditionRefusal { parallelIteration := true, repetitionNotUnique := true,
                       filterIteratesOrIndexes := true, allLeavesNegative := true } =
        some .parallelIterationNotAllowed ∧
      conditionRefusal { parallelIteration := true, filterIteratesOrIndexes := true,
                         allLeavesNegative := true } =
        some .parallelIterationNotAllowed := by
  native_decide

/- Every catalog key is distinct, and the two that break the family's shared prefixes are the ones a
   consumer building a key by concatenation gets wrong: the iteration class carries no
   `SEMANTIC_INDEX_` prefix despite belonging to that arm, and the wildcard class carries no
   `ITERATION` in its name despite being the iteration test's other arm. -/
example :
    (IterationRefusal.all.map (·.catalogKey)).eraseDups.length = IterationRefusal.all.length ∧
      IterationRefusal.noWildcard.catalogKey = "MVK_NO_WILDCARD" ∧
      IterationRefusal.semanticIndexInvalidIter.catalogKey = "MVK_SEMANTIC_INDEX_INVALID_ITER" ∧
      IterationRefusal.all.length = 7 := by
  native_decide

/- The filter-walk cases below use spec/07 §3 and its parser/checker source account; they are
internal separators, not additional retained Kernel observations. -/
private def filterLevel (marker : IndexMarker) (onPath : Bool := true)
    (reopened : Bool := false) : FilterIndexLevel :=
  { marker, onFilteredPath := onPath, reopensFilteredLevel := reopened }

private def filterRead (levels : List FilterIndexLevel) (marked : Bool := false) : FilterIndexedReference :=
  { levels, marked }

example : filterBodyRefusal [filterRead [filterLevel .iteration true true]] false = none ∧
    filterBodyRefusal [filterRead [filterLevel .wildcard]] false = some .noIterationForWildcard ∧
    filterBodyRefusal [filterRead [filterLevel .iteration true true] true] false = some .noIterationForWildcard := by decide

example : filterBodyRefusal [filterRead [filterLevel .wildcard, filterLevel .iteration false]] false =
      some .invalidIterationInFilterCondition ∧
    filterBodyRefusal [filterRead [filterLevel .wildcard, filterLevel .iteration true true]] false =
      some .noWildcard ∧
    filterBodyRefusal [filterRead [filterLevel .iteration true true, filterLevel .semanticIndex]] false =
      some .semanticIndexNotAllowed := by decide

example : filterBodyRefusal [filterRead [filterLevel .semanticIndex] true,
      filterRead [filterLevel .iteration true true]] false = none ∧
    filterBodyRefusal [filterRead [filterLevel .semanticIndex] true,
      filterRead [filterLevel .iteration false]] false = some .invalidIterationInFilterCondition ∧
    filterBodyRefusal [filterRead [filterLevel .wildcard],
      filterRead [filterLevel .iteration true true]] false = none := by decide

example : filterBodyRefusal [filterRead [filterLevel .fixed, filterLevel .unspecified],
      filterRead [filterLevel .iteration true true]] false = none ∧
    filterBodyRefusal [filterRead [filterLevel .wildcard, filterLevel .semanticIndex]] false =
      some .semanticIndexNotAllowed ∧
    filterBodyRefusal [filterRead [filterLevel .wildcard false],
      filterRead [filterLevel .iteration true true]] false = none := by decide

example : filterBodyRefusal [filterRead [filterLevel .semanticIndex],
      filterRead [filterLevel .iteration false]] true = some .semanticIndexNotAllowed ∧
    filterBodyRefusal [filterRead [filterLevel .iteration false],
      filterRead [filterLevel .semanticIndex]] true = some .invalidIterationInFilterCondition ∧
    filterBodyRefusal [] true = some .noIterationForWildcard ∧
    filterBodyRefusal [filterRead [filterLevel .iteration true true]] true =
      some .disallowedConstructInFilterCondition := by decide

end A12Kernel.Conformance.IterationLegality
