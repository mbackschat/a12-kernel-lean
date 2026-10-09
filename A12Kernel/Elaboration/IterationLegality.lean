import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Elaboration.IterationGuard

/-! # Static legality of iteration, parallel iteration, and the semantic index

Three ways of naming a repetition share one static gate, and a consumer that treats them as independent features gets the refusals wrong. **Iteration** is the rule's own walk over its error field's repeatable ancestors. **Parallel iteration** happens when a condition also names a repeatable group that is neither above nor below the error field's path; the two walks are then matched by equal index-field values, which is why both groups must declare an index field of the same name. The **semantic index** names one repetition by its index field's *value* rather than by position.

The per-reference walk and whole-condition gate preserve their own first-match refusal order.

**Per reference, a left-to-right scan over the reference's index levels**, carrying one bit of state: whether some *outer* level was a wildcard. At each level the iteration test runs first, against the bit as it stood before this level; only then does the level update the bit or trip the semantic-index test. Two consequences a reimplementer misses. A wildcard poisons every level below it, so the same reference is legal above the wildcard and refused below. And the two arms of the iteration test report *different classes for the same defect*: a reference read inside a semantic index's key reports the semantic-index class, while any other reference, a keyed value included, reports the wildcard class. So the class identifies where the reference stands, not the defect ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-key-addressing)).

**Per condition, an ordered sequence of whole-condition tests** runs after parsing. The shared whole-rule facts distinguish uniqueness/parallel combinations, a parallel filtered owner, parallelism inside a filter body, semantic-index use inside a filter, repeated uniqueness, and raw Length. Filter-owned refusals do not require outer parallelism; these gates precede guard checking. The final gate retains connective structure: one referenced guarding conjunct suffices for `And`, while every `Or` branch must reference and guard the parallel level. A positive leaf alone therefore cannot summarize the whole condition (`IterationNotValidVisitor.visit(ICompositeCondition)`).

**The many-to-one to watch.** `parallelIterationNotAllowed` is raised at two sites with two different interpolated operand names — once for the `RepetitionNotUnique` combination and once for a filter condition that iterates in parallel — so the code alone does not say which. The original static checkpoint measures the first; the filter gate and its source/evidence scope have their own [implementation record](../../docs/implementation/cross-clause.md#cap-iteration-and-semantic-index-legality).

**Evidence.** Six classes are measured against the real Kernel through `dmtool rule check` over one model carrying two sibling index-field groups, a nested indexed group, an un-indexed group above an indexed one, and an enumeration-typed index field ([checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-iteration-and-semantic-index-legality)). Admitted controls carry as much weight as the refusals here: `RepetitionNotUnique` alone is legal, and it is the *combination* with parallel iteration that refuses.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A refusal from the per-reference iteration and semantic-index static gate. Constructor names are local; `catalogKey` carries the identity a consumer compares against. -/
inductive IterationRefusal where
  /-- A reference iterates a level it may not: below a wildcard, below the error field's path, or
  off that path in a group that declares no index field. Reported for every reference outside a
  semantic index's key, a keyed value included. -/
  | noWildcard
  /-- The same defect on a reference read inside a semantic index's key. Same cause, different
  class. -/
  | semanticIndexInvalidIter
  /-- A semantic index sits below a wildcard level. -/
  | semanticIndexBelowWildcard
  /-- The semantic index's key entity reaches through an enumeration category. -/
  | semanticIndexWithCategory
  /-- More than one index field lies on the referenced path, so the semantic index is ambiguous. -/
  | multipleIndexFields
  deriving Repr, DecidableEq

namespace IterationRefusal

/-- The exact catalog key, which is also the code `rule check` surfaces. -/
def catalogKey : IterationRefusal → String
  | .noWildcard => "MVK_NO_WILDCARD"
  | .semanticIndexInvalidIter => "MVK_SEMANTIC_INDEX_INVALID_ITER"
  | .semanticIndexBelowWildcard => "MVK_SEMANTIC_INDEX_BELOW_WILDCARD"
  | .semanticIndexWithCategory => "MVK_SEMANTIC_INDEX_WITH_CATEGORY"
  | .multipleIndexFields => "MVK_MULTIPLE_INDEX_FIELDS"

/-- Every class the per-reference gate reports. -/
def all : List IterationRefusal :=
  [.noWildcard, .semanticIndexInvalidIter, .semanticIndexBelowWildcard,
   .semanticIndexWithCategory, .multipleIndexFields]

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
  /-- Off the path in a group that declares no index field. A keyed group that fails its index gates
  draws those gates' own classes, which `UnboundOperandLevel.diagnostic?` owns
  ([`kf371`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371)). -/
  | offPathNotParallelIterable
  deriving Repr, DecidableEq

/-- One level of a reference: how it names its repetition and where that group sits. -/
structure IndexLevel where
  marker : IndexMarker
  relation : GroupRelation := .aboveOrEqualErrorPath
  deriving Repr, DecidableEq

/-- A reference as the scan sees it: its levels outermost first, plus whether it is read inside a
semantic index's key. That selects *which class* an illegal iteration reports, and it is not
derivable from the levels: a keyed value carries the semantic-index marker yet reports the wildcard
class, and the key that selects its row carries none yet reports the semantic-index class. A read in
a filter body that is not `$`-marked, a key's own filter included, is not scanned here: the filter's
own classes answer for it ([`spec/07`](../../spec/07-repetition-and-iteration.md)). -/
structure IndexedReference where
  levels : List IndexLevel
  insideSemanticIndexKey : Bool := false
  deriving Repr, DecidableEq

/-- The iteration test at one level, against the wildcard bit as it stood *before* this level.

An iteration is illegal when an outer wildcard already reopened the list, when the group lies below
the error field, or when it lies off the path in an unkeyed group. The class then depends on the
reference, not on which of the three conditions fired. -/
def levelIterationRefusal (level : IndexLevel) (outerWildcard insideSemanticIndexKey : Bool) :
    Option IterationRefusal :=
  if level.marker != .iteration then
    none
  else if outerWildcard || level.relation == .belowErrorPath
      || level.relation == .offPathNotParallelIterable then
    some (if insideSemanticIndexKey then .semanticIndexInvalidIter else .noWildcard)
  else
    none

/-- Scan one reference's levels outermost first, carrying the outer-wildcard bit.

The order inside a level is observable: the iteration test runs against the bit as it stood before
this level, and only then does the level set the bit or trip the semantic-index test. -/
def indexScan (insideSemanticIndexKey : Bool) : List IndexLevel → Bool → Option IterationRefusal
  | [], _ => none
  | level :: rest, outerWildcard =>
      match levelIterationRefusal level outerWildcard insideSemanticIndexKey with
      | some refusal => some refusal
      | none =>
        match level.marker with
        | .wildcard => indexScan insideSemanticIndexKey rest true
        | .semanticIndex =>
            if outerWildcard then some .semanticIndexBelowWildcard
            else indexScan insideSemanticIndexKey rest outerWildcard
        | _ => indexScan insideSemanticIndexKey rest outerWildcard

/-- The per-reference verdict: the first illegal level, or nothing. -/
def referenceRefusal (reference : IndexedReference) : Option IterationRefusal :=
  indexScan reference.insideSemanticIndexKey reference.levels false

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

/-- Whole-rule facts accumulated only after each authored read has passed. Filter containment
is syntactic: exiting a nested filter changes parser read mode, not AST membership
(ParserService.checkNormalRule; AnalyseService.isParallelIteration). -/
structure FilterRuleFacts where
  repetitionNotUniqueCount : Nat := 0
  parallelIteration : Bool := false
  parallelFilteredEntity : Bool := false
  parallelFilterBody : Bool := false
  filterUsesIndex : Bool := false
  rawLength : Bool := false
  deriving Repr, BEq, DecidableEq

/-- Computation fragments contribute to one generated rule's global checks (spec/09 §6). -/
def FilterRuleFacts.merge (left right : FilterRuleFacts) : FilterRuleFacts := {
  repetitionNotUniqueCount := left.repetitionNotUniqueCount + right.repetitionNotUniqueCount
  parallelIteration := left.parallelIteration || right.parallelIteration
  parallelFilteredEntity := left.parallelFilteredEntity || right.parallelFilteredEntity
  parallelFilterBody := left.parallelFilterBody || right.parallelFilterBody
  filterUsesIndex := left.filterUsesIndex || right.filterUsesIndex
  rawLength := left.rawLength || right.rawLength }

/-- These whole-rule refusals follow successful parsing and precede raw-Length/final iteration
checks. The filtered owner's parallelism is distinct from parallelism in its body
(ParserService.checkNormalRule; spec/07 §3). -/
def FilterRuleFacts.refusal? (facts : FilterRuleFacts) : Option KernelStaticDiagnostic :=
  if facts.repetitionNotUniqueCount > 0 && facts.parallelIteration then some .parallelIterationNotAllowed
  else if facts.parallelFilteredEntity then some .parallelIterationForFilteredEntityNotAllowed
  else if facts.parallelFilterBody then some .parallelIterationNotAllowed
  else if facts.filterUsesIndex then some .semanticIndexNotAllowed
  else if facts.repetitionNotUniqueCount > 1 then some .invalidCombinationOfRepetitionNotUnique
  else none

/-- Global construct-combination refusals precede the raw-Length check (`ParserService.checkNormalRule`). The reader has already classified whether the standalone limiter exception applies. -/
def FilterRuleFacts.beforeIterationRefusal? (facts : FilterRuleFacts) : Option KernelStaticDiagnostic :=
  match facts.refusal? with
  | some diagnostic => some diagnostic
  | none => if facts.rawLength then some .invalidLengthOfRawType else none

/-- Compose the shared pre-iteration gate with a settled parallel guard tree.

Each true leaf references and guards the parallel level; it is not a runtime verdict. Reference consistency and any separate row/ordinary-iteration gates remain caller obligations. Filter-body parallelism and semantic-index use do not depend on outer parallelism (`ParserService.checkNormalRule`). -/
def conditionRefusal (facts : FilterRuleFacts) (guards : ConditionTree Bool) : Option KernelStaticDiagnostic :=
  match facts.beforeIterationRefusal? with
  | some diagnostic => some diagnostic
  | none =>
      if facts.parallelIteration && !guards.iterationGuarded id then some .parallelIterationInvalid else none

/-- One resolved level in a filter body's reference walk. The two geometric facts are
independent: an iteration can lie on the filtered path without binding a level reopened by it
(spec/07 §3, CheckEntitySpecImpl.checkIndicesInFilterCondition). -/
structure FilterIndexLevel where
  marker : IndexMarker
  onFilteredPath : Bool := true
  reopensFilteredLevel : Bool := false
  deriving Repr, DecidableEq

/-- The filter walk skips a marked reference itself. Its key and filter descendants remain
separate entries in the authored walk; marking the parent does not suppress those entries. -/
structure FilterIndexedReference where
  levels : List FilterIndexLevel
  marked : Bool := false
  deriving Repr, DecidableEq

/-- Check one reference, retaining whether it binds a reopened filter level. Off-path iteration
precedes below-wildcard iteration; an index refusal occurs at its own authored level (spec/07 §3). -/
def filterIndexScan : List FilterIndexLevel → Bool → Except KernelStaticDiagnostic Bool
  | [], _ => .ok false
  | level :: rest, outerWildcard => do
      match level.marker with
      | .semanticIndex => throw .semanticIndexNotAllowed
      | .wildcard => filterIndexScan rest true
      | .iteration =>
          if !level.onFilteredPath then throw .invalidIterationInFilterCondition
          if outerWildcard then throw .noWildcard
          let later ← filterIndexScan rest outerWildcard
          pure (level.reopensFilteredLevel || later)
      | .fixed | .unspecified => filterIndexScan rest outerWildcard

/-- Read order determines the first refusal. Wildcard state belongs to one reference, while
reopened-level participation is accumulated over the whole body (spec/07 §3). -/
def filterReferenceWalk : List FilterIndexedReference → Except KernelStaticDiagnostic Bool
  | [] => .ok false
  | reference :: rest => do
      let here ← if reference.marked then pure false else filterIndexScan reference.levels false
      let later ← filterReferenceWalk rest
      pure (here || later)

/-- The body's reference walk finishes before its iteration demand or forbidden-construct gate.
Own read, key, comparison and operand checks must already have passed. This gate excludes the
post-parse marked-index refusal, whose later timing is part of spec/07 §3. -/
def filterBodyRefusal (references : List FilterIndexedReference) (forbiddenConstruct : Bool) :
    Option KernelStaticDiagnostic :=
  match filterReferenceWalk references with
  | .error diagnostic => some diagnostic
  | .ok false => some .noIterationForWildcard
  | .ok true => if forbiddenConstruct then some .disallowedConstructInFilterCondition else none

end A12Kernel
