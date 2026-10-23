import A12Kernel.Elaboration.ParallelFieldRule

namespace A12Kernel

namespace CheckedParallelFieldPair

/-- Partial dispatch compresses the error field's selectors before ordinary iteration bounds are checked. Concrete joined-row selectors conflict with a parallel bound; differing selectors compress to a wildcard. This is a dispatch envelope, not the leaf relevance set (Kernel partial-parallel gate capture, 2026-10-10). -/
def admitsPartialOuter (pair : CheckedParallelFieldPair model)
    (scope : ValidationRelevanceScope) (outer : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      let declaration := if pair.errorField == pair.leftDeclaration.id then
        pair.leftDeclaration else pair.rightDeclaration
      match ValidationRelevanceScope.compressedSelector? entities declaration.path with
      | none => false
      | some compressed =>
          let bounds := declaration.repeatableScope.dropLast
          let ordinary := bounds.any fun level => model.repeatableGroups.any fun group =>
            group.level == level && group.repeatability != some 1
          if !ordinary then true else
            compressed.matchesBoundSubtree model bounds outer &&
              compressed.wildcardsLevels model [if pair.errorField == pair.leftDeclaration.id then
                pair.groups.leftGroup.level else pair.groups.rightGroup.level]

end CheckedParallelFieldPair

namespace CheckedPartialPreliminary

/-- An unmatched reference requires wildcard relevance at the missing indexed level. Enumerating every current row is insufficient because it does not cover an unknown row (spec/10 partial parallel semantics). -/
def coversUnmatchedParallel (view : CheckedPartialPreliminary model)
    (group : RepeatableGroupDecl) (path : List String) (outer : Env) : Bool :=
  match view.relevance with
  | .full => true
  | .partialSet entities => entities.any fun entity =>
      match entity.projectOntoTarget? path with
      | none => false
      | some projected =>
          projected.matchesBoundSubtree model
            (model.repeatableScopeForGroupPath group.path).dropLast outer &&
          projected.wildcardsLevels model ((model.repeatableScopeForGroupPath path).filter fun level =>
            !(model.repeatableScopeForGroupPath group.path).dropLast.contains level)

private def missingParallelAvailable (view : CheckedPartialPreliminary model)
    (side : ResolvedParallelIndexSide) (outer : Env) : Bool :=
  match side.group.indexField.bind (fun id => (model.lookupUniqueId id).toOption) with
  | none => false
  | some index =>
      view.coversUnmatchedParallel side.group index.path outer &&
        !view.silentlyUnavailable.any (fun address =>
          address.field == index.id &&
            some address.path.dropLast == (outer.pathForScope index.repeatableScope.dropLast).toOption)

/-- Read matched rows through the call-local checked view; missing rows preserve formal column errors and separate silent relevance unavailability. No sentinel or invented formal finding enters the physical document. -/
private def readParallelField (view : CheckedPartialPreliminary model)
    (side : ResolvedParallelIndexSide) (outer : Env) (declaration : FlatFieldDecl) :
    Except ParallelPresenceRuleEvaluationError (Option CellObservation) := do
  match side.environment with
  | some environment =>
      let path ← environment.pathForScope declaration.repeatableScope |>.mapError (fun e => .join (.environment e))
      let address : CellAddr := { field := declaration.id, path }
      if !view.isAddressRelevant address then pure none else
        match ← view.readAuthoredValidation address |>.mapError .preliminary with
        | .silentlyUnavailable => pure none
        | .checked cell => pure (some (observeCell .validation cell))
  | none =>
      if !view.missingParallelAvailable side outer ||
          !view.coversUnmatchedParallel side.group declaration.path outer then pure none
      else pure (some side.missingObservation)

private def unmatchedGroupRelevance (view : CheckedPartialPreliminary model)
    (group : RepeatableGroupDecl) (path : GroupPath) (outer : Env) : GroupRelevance :=
  if view.coversUnmatchedParallel group path outer then .fullyRelevant else
    let descendants := model.fields.filter (path.isPrefixOf ·.groupPath)
    let covered := fun declaration => view.coversUnmatchedParallel group declaration.path outer
    if !descendants.isEmpty && descendants.all covered then .fullyRelevant
    else if descendants.any covered then .partlyRelevant else .noneRelevant

/-- Group reads retain the same partial group-content account as ordinary validation after resolving the joined side. An unavailable missing column cannot establish group absence. -/
private def parallelGroupState (view : CheckedPartialPreliminary model)
    (row : ResolvedParallelIndexRow) (outer : Env) (reference : ResolvedGroupReference) :
    Except ParallelPresenceRuleEvaluationError GroupPresenceState := do
  let side := if row.left.group.path.isPrefixOf reference.path then some row.left
    else if row.right.group.path.isPrefixOf reference.path then some row.right else none
  match side with
  | none => pure (← view.groupPresenceInput reference.path outer false |>.mapError .group).derive
  | some selected =>
      match selected.environment with
      | some environment =>
          pure (← view.groupPresenceInput reference.path environment false |>.mapError .group).derive
      | none =>
          let unavailable := selected.unavailableKey.isSome ||
            !view.missingParallelAvailable selected outer
          pure {
            content := false
            erroneous := false
            relevance := if unavailable then .noneRelevant else
              view.unmatchedGroupRelevance selected.group reference.path outer }

end CheckedPartialPreliminary

/-- Partial calls use the same checked join and condition tree, selecting keys from relevant index addresses while preserving the uncompressed relevance set for leaf reads. A custom callback receives that uncompressed set and the call's generated formal failures, as in the ordinary partial carrier. -/
def CheckedParallelFieldRule.evalPartialDocument (rule : CheckedParallelFieldRule model)
    (view : CheckedPartialPreliminary model) (messageCache : Option MessageIndexContext := none)
    (registry : CustomValidationRegistry model := {}) (world : Option World := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) := do
  -- A partial call reports no rule on a group, as the ordinary carrier skips one (KF603). No retained
  -- observation pins partial validation of an error field below the join.
  if rule.pair.errorGroup.isSome then return []
  if !rule.pair.innerScope.isEmpty then throw .unsupportedCondition
  let common := match rule.pair.groups.outerScopePlan with
    | .common shared | .framed _ shared _ => shared
  let environments ← if common.isEmpty then pure [[]]
    else view.index.base.inCapacityRowEnvironments common |>.mapError .rows
  ParallelRuleRowOutcome.untilCaught (fun outer =>
    rule.pair.evalWith rule.condition
      (fun rowOuter row _ =>
        let custom := rule.pair.customConditions registry view.index.base (.partialEntities view.relevance)
          view.generatedFormalFailures row rowOuter
        rule.condition.evalReached (fun leaf => ParallelFieldLeaf.evalWith rule.pair
          (fun field => do
            let declaration := rule.pair.declaration field
            if row.left.group.path.isPrefixOf declaration.groupPath then
              view.readParallelField row.left rowOuter declaration
            else if row.right.group.path.isPrefixOf declaration.groupPath then
              view.readParallelField row.right rowOuter declaration
            else
              let path ← rowOuter.pathForScope declaration.repeatableScope
                |>.mapError (fun error => .join (.environment error))
              let address : CellAddr := { field := declaration.id, path }
              if !view.isAddressRelevant address then pure none else
                match ← view.readAuthoredValidation address |>.mapError .preliminary with
                | .silentlyUnavailable => pure none
                | .checked cell => pure (some (observeCell .validation cell)))
          (view.parallelGroupState row rowOuter)
          (fun leaf => match ParallelFieldLeaf.ordinaryEnvironment? rule.pair view.index.base row rowOuter leaf with
            | none => pure .unknown
            | some (environment, _) => ParallelFieldLeaf.evalPartialOrdinary view environment world leaf)
          (fun carrier => do
            let some atom := carrier.orderedAtom? | throw .unsupportedCondition
            match ParallelFieldLeaf.ordinaryEnvironment? rule.pair view.index.base row rowOuter carrier with
            | none => pure (.error .silentlyUnavailable)
            | some (environment, _) =>
                (atom.resolveAddressed (view.addressedValidationContext environment world)).mapError .addressing)
          leaf custom world))
      view.index outer messageCache view.isAddressRelevant
      (rule.pair.admitsPartialOuter view.relevance) ParallelPresenceRuleEvaluationError.caughtByRule)
    environments

end A12Kernel
