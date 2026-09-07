/-! # Static legality of iteration, parallel iteration, and the semantic index

Three ways of naming a repetition share one static gate, and a consumer that treats them as independent features gets the refusals wrong. **Iteration** is the rule's own walk over its error field's repeatable ancestors. **Parallel iteration** happens when a condition also names a repeatable group that is neither above nor below the error field's path; the two walks are then matched by equal index-field values, which is why both groups must declare an index field of the same name. The **semantic index** names one repetition by its index field's *value* rather than by position.

The gate has two layers, and both are first-match-wins.

**Per reference, a left-to-right scan over the reference's index levels**, carrying one bit of state: whether some *outer* level was a wildcard. At each level the iteration test runs first, against the bit as it stood before this level; only then does the level update the bit or trip the semantic-index test. Two consequences a reimplementer misses. A wildcard poisons every level below it, so the same reference is legal above the wildcard and refused below. And the two arms of the iteration test report *different classes for the same defect* — a reference carrying a semantic index reports the semantic-index class where an ordinary one reports the wildcard class — so the class identifies the reference's shape, not the defect.

**Per condition, an ordered sequence of whole-condition tests** run after parsing. Parallel iteration combined with `RepetitionNotUnique` is refused; so is a filter condition that itself iterates in parallel or reaches through a semantic index; and a parallel-iterated condition all of whose leaves are negative is refused last, because such a rule would fire for every repetition that has no values at all. A negative leaf beside a positive one is admitted, which is the distinction that makes the last test worth stating precisely.

**The many-to-one to watch.** `parallelIterationNotAllowed` is raised at two sites with two different interpolated operand names — once for the `RepetitionNotUnique` combination and once for a filter condition that iterates in parallel — so the code alone does not say which. Measured witnesses exist for the first; the second is recorded as unmeasured below rather than assumed to behave like its twin.

**Evidence.** Six classes are measured against the real Kernel through `dmtool rule check` over one model carrying two sibling index-field groups, a nested indexed group, an un-indexed group above an indexed one, and an enumeration-typed index field ([checkpoint](../../docs/SOURCES.md#src-iteration-and-semantic-index-legality)). Admitted controls carry as much weight as the refusals here: `RepetitionNotUnique` alone is legal, and it is the *combination* with parallel iteration that refuses.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A refusal from the iteration and semantic-index static gate. Constructor names are local; `catalogKey` carries the identity a consumer compares against. -/
inductive IterationRefusal where
  /-- A reference iterates a level it may not: below a wildcard, below the error field's path, or
  off that path without a valid parallel iteration. Reported for an ordinary reference. -/
  | noWildcard
  /-- The same defect on a reference that carries a semantic index. Same cause, different class. -/
  | semanticIndexInvalidIter
  /-- A semantic index sits below a wildcard level. -/
  | semanticIndexBelowWildcard
  /-- The semantic index's key entity reaches through an enumeration category. -/
  | semanticIndexWithCategory
  /-- More than one index field lies on the referenced path, so the semantic index is ambiguous. -/
  | multipleIndexFields
  /-- Parallel iteration is combined with a construct that forbids it. Raised at two sites with
  different interpolated operand names, so the code does not identify which. -/
  | parallelIterationNotAllowed
  /-- Every leaf of a parallel-iterated condition is negative, so the rule would fire for a
  repetition that has no values at all. -/
  | parallelIterationInvalid
  deriving Repr, DecidableEq

namespace IterationRefusal

/-- The exact catalog key, which is also the code `rule check` surfaces. -/
def catalogKey : IterationRefusal → String
  | .noWildcard => "MVK_NO_WILDCARD"
  | .semanticIndexInvalidIter => "MVK_SEMANTIC_INDEX_INVALID_ITER"
  | .semanticIndexBelowWildcard => "MVK_SEMANTIC_INDEX_BELOW_WILDCARD"
  | .semanticIndexWithCategory => "MVK_SEMANTIC_INDEX_WITH_CATEGORY"
  | .multipleIndexFields => "MVK_MULTIPLE_INDEX_FIELDS"
  | .parallelIterationNotAllowed => "MVK_PARALLEL_ITERATION_NOT_ALLOWED"
  | .parallelIterationInvalid => "MVK_PARALLEL_ITERATION_INVALID"

/-- Every class this gate reports. -/
def all : List IterationRefusal :=
  [.noWildcard, .semanticIndexInvalidIter, .semanticIndexBelowWildcard,
   .semanticIndexWithCategory, .multipleIndexFields,
   .parallelIterationNotAllowed, .parallelIterationInvalid]

end IterationRefusal

/-- How one level of a reference's path names its repetition. The Kernel encodes these as sentinel
integers on one index array, which is why a single scan sees all of them. -/
inductive IndexMarker where
  /-- A literal repetition number. -/
  | fixed
  /-- `*` — set formation over the whole repetition list. -/
  | wildcard
  /-- The rule's own iteration over this level. -/
  | iteration
  /-- `For <key>` — the repetition whose index field carries the key's value. -/
  | semanticIndex
  /-- No index given at this level. -/
  | unspecified
  deriving Repr, DecidableEq

/-- Where a referenced repeatable group sits relative to the error field's own path. The iteration
test consults exactly this, so it is the whole model-dependent input the scan needs. -/
inductive GroupRelation where
  /-- The group contains the error field, or is it. Iterating it is the ordinary case. -/
  | aboveOrEqualErrorPath
  /-- The group lies strictly below the error field. -/
  | belowErrorPath
  /-- Off the error field's path, and a valid parallel iteration: both groups declare an index
  field of the same name and type. -/
  | offPathParallelIterable
  /-- Off the path with no valid parallel iteration available. -/
  | offPathNotParallelIterable
  deriving Repr, DecidableEq

/-- One level of a reference: how it names its repetition and where that group sits. -/
structure IndexLevel where
  marker : IndexMarker
  relation : GroupRelation := .aboveOrEqualErrorPath
  deriving Repr, DecidableEq

/-- A reference as the scan sees it: its levels outermost first, plus whether the reference as a
whole carries a semantic index — which selects *which class* an illegal iteration reports and is
therefore not derivable from the levels alone, since the key may sit on a different reference. -/
structure IndexedReference where
  levels : List IndexLevel
  carriesSemanticIndex : Bool := false
  deriving Repr, DecidableEq

/-- The iteration test at one level, against the wildcard bit as it stood *before* this level.

An iteration is illegal when an outer wildcard already reopened the list, when the group lies below
the error field, or when it lies off the path with no parallel iteration to match the two walks. The
class then depends on the reference, not on which of the three conditions fired. -/
def levelIterationRefusal (level : IndexLevel) (outerWildcard carriesSemanticIndex : Bool) :
    Option IterationRefusal :=
  if level.marker != .iteration then
    none
  else if outerWildcard || level.relation == .belowErrorPath
      || level.relation == .offPathNotParallelIterable then
    some (if carriesSemanticIndex then .semanticIndexInvalidIter else .noWildcard)
  else
    none

/-- Scan one reference's levels outermost first, carrying the outer-wildcard bit.

The order inside a level is observable: the iteration test runs against the bit as it stood before
this level, and only then does the level set the bit or trip the semantic-index test. -/
def indexScan (carriesSemanticIndex : Bool) : List IndexLevel → Bool → Option IterationRefusal
  | [], _ => none
  | level :: rest, outerWildcard =>
      match levelIterationRefusal level outerWildcard carriesSemanticIndex with
      | some refusal => some refusal
      | none =>
        match level.marker with
        | .wildcard => indexScan carriesSemanticIndex rest true
        | .semanticIndex =>
            if outerWildcard then some .semanticIndexBelowWildcard
            else indexScan carriesSemanticIndex rest outerWildcard
        | _ => indexScan carriesSemanticIndex rest outerWildcard

/-- The per-reference verdict: the first illegal level, or nothing. -/
def referenceRefusal (reference : IndexedReference) : Option IterationRefusal :=
  indexScan reference.carriesSemanticIndex reference.levels false

/-- What the semantic index's own entity check needs beyond the scan. Its two measured arms are
ordered: an ambiguous index path is refused before the key's category reach is looked at. -/
structure SemanticIndexUse where
  /-- More than one index field lies on the referenced path. -/
  ambiguousIndexPath : Bool := false
  /-- The key entity reaches through an enumeration category. -/
  keyReachesCategory : Bool := false
  deriving Repr, DecidableEq

/-- The semantic index's entity check, in its measured order. -/
def semanticIndexRefusal (use : SemanticIndexUse) : Option IterationRefusal :=
  if use.ambiguousIndexPath then some .multipleIndexFields
  else if use.keyReachesCategory then some .semanticIndexWithCategory
  else none

/-- A whole condition, reduced to what the post-parse gate tests. -/
structure ConditionShape where
  /-- Whether the condition iterates two repeatable groups neither of which contains the other. -/
  parallelIteration : Bool := false
  /-- Whether it uses `RepetitionNotUnique`. -/
  repetitionNotUnique : Bool := false
  /-- Whether a filter condition itself iterates in parallel or reaches through a semantic index. -/
  filterIteratesOrIndexes : Bool := false
  /-- Whether every leaf of the condition is negative. A single positive leaf clears it. -/
  allLeavesNegative : Bool := false
  deriving Repr, DecidableEq

/-- The whole-condition gate, first-match-wins in the order the parser runs it.

`parallelIterationInvalid` is last for a reason a consumer can act on: it is the only test whose
answer changes when a positive leaf is added, so it is the one a repair tool can clear without
restructuring the reference graph. -/
def conditionRefusal (shape : ConditionShape) : Option IterationRefusal :=
  if shape.parallelIteration && shape.repetitionNotUnique then
    some .parallelIterationNotAllowed
  else if shape.parallelIteration && shape.filterIteratesOrIndexes then
    some .parallelIterationNotAllowed
  else if shape.parallelIteration && shape.allLeavesNegative then
    some .parallelIterationInvalid
  else
    none

end A12Kernel
