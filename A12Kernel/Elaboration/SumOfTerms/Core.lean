import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.CandidateEnvironment
import A12Kernel.Elaboration.StarGroup
import A12Kernel.Elaboration.StaticDiagnostic

/-! # `SumOfTerms` operands and their checked form

`SumOfTerms(G*, t)` evaluates the Number term `t` once at each in-capacity row of the starred
repeatable group `G*`, optionally filtered by `Having`, and adds the results
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)). The Kernel reads the
term with the set-expression parser, so the term is an ordinary numeric expression over the filter
body's atom family, resolved in the same candidate and captured environments and refused by the same
environment gates, and the iteration entity is a starred group with the filter a starred field takes.
Neither is a new representation: a term is `AuthoredNumericExpr HavingNumericAtom` and the entity's
filter is the path-indexed certificate of any other filter. Nested `SumOfTerms` and a filtered
aggregate are absent from that atom family, which is why the term refuses them by construction.

This module owns the authored and checked forms, their admission and their static reads. Evaluation
is [`SumOfTerms.Evaluation`](Evaluation.lean).
-/

namespace A12Kernel

/-- One authored `SumOfTerms` operand pair: the starred group, its optional filter and the term. -/
structure SurfaceSumOfTerms where
  group : SurfaceStarGroupPath
  having : Option SurfaceCorrelatedHaving := none
  term : AuthoredNumericExpr SurfaceHavingNumericAtom

/-- Why a `SumOfTerms` operand failed to elaborate. The arms stay apart because a refused entity,
filter and term send an author to different halves of the call. -/
inductive SumOfTermsElabError where
  | entity (error : StarredGroupElabError)
  | having (error : CorrelationElabError)
  | term (error : CorrelationElabError)
  /-- A `$`-marked read in the term, which iterates nothing the set expression binds. -/
  | outerIteration
  /-- The term reads no field of the entity's lowest starred level, as a literal, `BaseYear` alone or
  a read of only the upper level of a two-star entity. -/
  | noIterationForLowestLevel
  | incoherentCore
  deriving Repr, DecidableEq

/-- The Kernel class of one refusal, through the projection of the part that raised it. The measured
rows behind each arm are the two tables of
[spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms). -/
def SumOfTermsElabError.diagnostic? : SumOfTermsElabError → Option KernelStaticDiagnostic
  | .entity error => error.diagnostic?
  | .term (.numericOperandFieldNotNumber _ _) => some .noNumber
  | .having error | .term error => error.diagnostic?
  | .outerIteration => some .invalidOuterIteration
  | .noIterationForLowestLevel => some .noIterationForLowestWildcard
  | .incoherentCore => none

/-- The static certificate of a resolved term: an admitted Number operation (shape, authoring limits
and a derivable scale), every read inside the candidate environment and none through `$`, and at least
one read of the entity's lowest starred level, the analogue of the filter's `reachesReopenedLevel`. -/
def sumOfTermsTermCertified (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (lowest : RepeatableLevel) (term : AuthoredNumericExpr HavingNumericAtom) : Bool :=
  term.isAdmittedResolvedNumericOperation &&
    term.numericOperationAuthoringCheck == .accepted &&
    (term.summary? HavingNumericAtom.summary).isSome &&
    term.lowerForEvaluation.isNumericOperation &&
    term.allAtoms (fun atom => atom.origins.all (· == .inner) &&
      HavingNumericAtom.wellFormedForEnvironments model candidateLevels outerLevels atom) &&
    term.anyAtom (HavingNumericAtom.reachesReopenedLevel model [lowest])

/-- One checked `SumOfTerms` operand. The filter is indexed by the entity's own star path and the
captured binding group, so it cannot be paired with another entity or lifted to another rule scope. -/
structure CheckedSumOfTerms (model : FlatModel) where
  private mk ::
  source : CheckedStarredGroupSource model
  bindingGroup : GroupPath
  filter : Option (CheckedPathHaving model source.path bindingGroup)
  term : AuthoredNumericExpr HavingNumericAtom
  termCertified : sumOfTermsTermCertified model (source.path.axes.map (·.level))
    (model.repeatableScopeForGroupPath bindingGroup) source.group.level term = true

/-- Elaborate one `SumOfTerms` operand. The entity gates answer first, then the filter, then the term:
its reads, its operation shape, a `$`-marked read and finally the read of the lowest starred level.
The relative order of the entity and term gates against each other is this project's choice where no
row measures a call failing both. -/
def elaborateSumOfTerms (model : FlatModel) (declaringGroup : GroupPath) (surface : SurfaceSumOfTerms)
    (bindingGroup : GroupPath := declaringGroup) :
    Except SumOfTermsElabError (CheckedSumOfTerms model) := do
  let source ← (elaborateStarredGroupSource model declaringGroup surface.group).mapError fun error =>
    .entity (error.placeBelowStar model declaringGroup bindingGroup)
  let candidateLevels := source.path.axes.map (·.level)
  let outerLevels := model.repeatableScopeForGroupPath bindingGroup
  let filter ← match surface.having with
    | none => pure none
    | some having => do
        having.requireOuterReferencesBound model declaringGroup bindingGroup outerLevels |>.mapError .having
        some <$> (elaboratePathHavingCore model declaringGroup source.path having bindingGroup).mapError .having
  let resolvers := havingLeafResolversAtLevels model declaringGroup candidateLevels
    (candidateLevels.drop source.path.firstStar) bindingGroup
  -- A term read of a level the entity does not iterate is asked as a filter's unmarked read is.
  if let some refusal := surface.term.atoms.findSome?
      (SurfaceHavingNumericAtom.candidateEnvironmentRefusal? model declaringGroup candidateLevels) then
    throw (.term refusal)
  let term ← (elaborateHavingNumericTermWith resolvers surface.term).mapError .term
  if !(term.isAdmittedResolvedNumericOperation && term.numericOperationAuthoringCheck == .accepted &&
      (term.summary? HavingNumericAtom.summary).isSome && term.lowerForEvaluation.isNumericOperation) then
    throw (.term .numericExpressionUnsupported)
  if !term.allAtoms (·.origins.all (· == .inner)) then throw .outerIteration
  if !term.allAtoms (HavingNumericAtom.wellFormedForEnvironments model candidateLevels outerLevels) then
    throw .incoherentCore
  if !term.anyAtom (HavingNumericAtom.reachesReopenedLevel model [source.group.level]) then
    throw .noIterationForLowestLevel
  if hCertified : sumOfTermsTermCertified model candidateLevels outerLevels source.group.level term = true then
    pure { source, bindingGroup, filter, term, termCertified := hCertified }
  else throw .incoherentCore

namespace CheckedSumOfTerms

/-- The repeatable levels strictly above the entity's first star, which the rule binds. -/
def bindingScope (checked : CheckedSumOfTerms model) : List RepeatableLevel :=
  checked.source.path.bindingScope

def hasHaving (checked : CheckedSumOfTerms model) : Bool := checked.filter.isSome

/-- The static scale of the sum, read off the term. The scale of a sum of terms is unmeasured
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)), so this is the
derived account that adding values of one scale keeps it. -/
def scaleSummary (checked : CheckedSumOfTerms model) : NumericScaleSummary :=
  (checked.term.summary? HavingNumericAtom.summary).getD (NumericScaleSummary.field 0)

/-- Whether the term holds a count. A count in the term lifts the empty-root gate on the small side, by
the `CNT`/`PLAIN` pair of a12-dmkits `SumOfTermsShapesRuntimeLawsTest` at `1124b523f`, kernel 31.1.1:
the two rules differ in nothing else, and only the count's runs on an empty root. Other nested
operations are unmeasured. -/
def holdsCount (checked : CheckedSumOfTerms model) : Bool :=
  checked.term.anyAtom fun | .groupCount _ | .collectionCount _ => true | _ => false

/-- Whether the term reads `field`, through any of its atoms. -/
def termReadsField (checked : CheckedSumOfTerms model) (field : FieldId) : Bool :=
  checked.term.anyAtom fun atom => atom.fieldOrigins.any (·.2 == field)

/-- Whether any read of the operand reaches `field`: the entity's group, the term and, as the
caller's `filterReads` decides, the filter. The error-field gate asks the narrower
[`referencesErrorField`](#A12Kernel.CheckedSumOfTerms.referencesErrorField). -/
def referencesWith (checked : CheckedSumOfTerms model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  (model.groupSubtreeFields checked.source.group.path).any (·.id == field) ||
    checked.termReadsField field || checked.filter.any (filterReads ·.condition)

def referencesField (checked : CheckedSumOfTerms model) (field : FieldId) : Bool :=
  checked.referencesWith field (·.referencesField field)

/-- The operand's reference to the rule's error field: the group it names at its lowest level, with
every field the group holds, and the filter's `$`-marked reads. A read in the term never references
it, and neither does a filter's unmarked read
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)). -/
def referencesErrorField (checked : CheckedSumOfTerms model) (field : FieldId) : Bool :=
  (model.groupSubtreeFields checked.source.group.path).any (·.id == field) ||
    checked.filter.any (CorrelatedHaving.referencesMarkedEntityField model ·.condition field)

end CheckedSumOfTerms

end A12Kernel
