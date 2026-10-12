import A12Kernel.Elaboration.StarPath
import A12Kernel.Elaboration.SingleGroup

namespace A12Kernel

inductive RepetitionNotUniqueElabError where
  /-- The model itself failed validation, kept apart from `resolve` so a model defect never reaches
  the key's resolver projection. -/
  | model (error : ResolveError)
  | resolve (error : ResolveError)
  | scope (error : SingleGroupElabError)
  /-- A key the reading-scope walk refuses. -/
  | keyReadRefused (path : List String) (unbound : UnboundOperandLevel)
  /-- The first key named twice: a field by its declaration, a group by its path. -/
  | duplicateKey (path : List String)
  /-- A group key holding another key of the list, the root beside any key included. -/
  | nestedGroupKey (group : GroupPath)
  | groupKey (group : GroupPath)
  | keyPathMismatch (expected actual : GroupPath)
  /-- Without a scope, two keys whose lowest repeatable groups lie on no one hierarchy path. -/
  | keysOffOnePath (left right : GroupPath)
  /-- Without a scope, a key whose group lies outside the rule group. -/
  | keyOutsideRuleGroup (keyPath : List String)
  /-- Under a scope, keys whose lowest repeatable groups are parallel, which a passing read means
  the rule iterates jointly. -/
  | keysIterateInParallel (left right : GroupPath)
  | unsupportedKeyKind (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | customStringRequiresPreparedChecking (path : List String)
  | missingReferenceGroup (keyPath : List String)
  /-- Without a scope, a key above the default reference group the deepest key selects. -/
  | keyOutsideDefaultReferenceGroup (referenceGroup keyGroup : GroupPath)
  | scopeIsField (path : List String)
  /-- A scope naming a group with no field anywhere in its subtree, once its walk has passed. -/
  | scopeIsEmpty (path : GroupPath)
  /-- A scope the reading-scope walk refuses. -/
  | scopeReadRefused (path : GroupPath) (unbound : UnboundOperandLevel)
  | referenceGroupNotRepeatable (path : GroupPath)
  | referenceGroupDoesNotContainKey (referenceGroup keyGroup : GroupPath)
  | path (error : StarPathElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace RepetitionNotUniqueElabError

/-- Project the measured `RepetitionNotUnique` key-admission classes. Every key and the `@From` scope are read first ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26k-paired-gates)), a key that does not resolve drawing the shared resolver's class ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)) and one the reading-scope walk refuses drawing the walk's; the list's duplicate gate comes next, a key named twice before a group holding another key ([`kf388`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf388)), then its own gates, each over the whole list, then exactly one branch: with `@From` the scope must be a group that repeats and holds every key, and keys in parallel repeatable groups then meet the ban on parallel iteration; without it the shared-path, rule-group and repeatable-group gates run ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26f-gate-order)).

Three shapes draw `MVK_REPEATABLE_GROUP_MISSING`: a second key in a nonrepeatable group, a sole key whose group is not repeatable, and a rule already placed at the repeated group, unless that group is a repeatable root holding every key directly, whose own rows are then compared. The walk's missing-star class is measured on a key and on a scope, keyed, index-free and empty, and its error-field class on either; its parallel index-gate classes are the shared read's, an assumption [SG9](../../docs/gaps/paths-and-groups.md#gap-sg9) records. The scope's walk answers before its emptiness, so an empty scope claims no class only once its walk has passed: the measured empty scopes whose read passes are a fixed group ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26h-empty-scope)) and a starred one ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26k-paired-gates)), which this surface cannot build or spell, and the empty repeatable group it can hold passes the walk only when the rule's error-field group lies inside it, which no Kernel model can author since it holds no field.

Every remaining form is named rather than caught by a wildcard, so a new refusal cannot be absorbed into this project's boundary without a decision. A custom String key needing prepared checking and an unsupported key kind are this theory's value-reading limits, not Kernel gates. `model` is routing rather than a key refusal, and `incoherentCore` is the unreachable-by-construction arm. The rest are Kernel refusals whose class this carrier has no evidence for. -/
def diagnostic? : RepetitionNotUniqueElabError → Option KernelStaticDiagnostic
  | .resolve error => error.diagnostic?
  | .keyReadRefused _ unbound | .scopeReadRefused _ unbound => unbound.diagnostic?
  | .duplicateKey _ => some .duplicateParam1
  | .nestedGroupKey _ => some .duplicateParam2
  | .groupKey _ => some .noGroupsAllowed
  | .rawStringValue _ => some .rawTypeOperandInvalid
  | .scopeIsField _ => some .noFieldsAllowed
  | .referenceGroupNotRepeatable _ => some .groupNotRepeatable
  | .referenceGroupDoesNotContainKey _ _ => some .entityNotInGroup
  | .keysOffOnePath _ _ => some .notInSamePath
  | .keysIterateInParallel _ _ => some .parallelIterationNotAllowed
  | .keyOutsideRuleGroup _ => some .notInRuleGroup
  | .keyPathMismatch _ _ | .missingReferenceGroup _ =>
      some .repeatableGroupMissing
  | .model _ | .scope _ | .scopeIsEmpty _
  | .keyOutsideDefaultReferenceGroup _ _
  | .unsupportedKeyKind _ _ | .customStringRequiresPreparedChecking _
  | .path _ | .incoherentCore => none

end RepetitionNotUniqueElabError

def FlatModel.terminalRepeatableGroupFor?
    (model : FlatModel) (declaration : FlatFieldDecl) :
    Option RepeatableGroupDecl :=
  declaration.repeatableScope.getLast?.bind model.repeatableGroupAtLevel?

/-- The first pair of keys whose lowest repeatable groups leave one hierarchy path. It keeps the
deepest such group so far, skipping a key under no repeatable group, and reports the first key whose
group neither extends nor lies on it. The Kernel's shared-path check compares these groups, read off
its source; the rows measure it on keys in two parallel repeatable groups and in sibling fixed
groups of one ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26k-paired-gates)). -/
def firstKeyOffSharedPath? (model : FlatModel) (declarations : List FlatFieldDecl) :
    Option (GroupPath × GroupPath) :=
  let rec walk (deepest : Option GroupPath) : List FlatFieldDecl → Option (GroupPath × GroupPath)
    | [] => none
    | declaration :: remaining =>
        match model.terminalRepeatableGroupFor? declaration with
        | none => walk deepest remaining
        | some group =>
            match deepest with
            | none => walk (some group.path) remaining
            | some path =>
                if path.isPrefixOf group.path then walk (some group.path) remaining
                else if group.path.isPrefixOf path then walk deepest remaining
                else some (path, group.path)
  walk none declarations

/-- Kernel reference-group admission, independent of key value support and executable row topology.
The default branch checks every key; `@From` instead checks group containment (spec/07 §6,
`CheckWiederholungBedingungImpl.check` and `CheckEntityListenUtils`). -/
def checkRepetitionReferenceAdmission (model : FlatModel) (ruleGroup : GroupPath)
    (declarations : List FlatFieldDecl) (scope : Option (GroupPath × Bool)) :
    Except RepetitionNotUniqueElabError (Option RepeatableGroupDecl) := do
  match scope with
  | some (path, isField) =>
      if isField then throw (.scopeIsField path)
      let group ← match model.lookupUniqueRepeatablePath path with
        | .ok group => pure group
        | .error (.unknownRepeatableGroup _) => throw (.referenceGroupNotRepeatable path)
        | .error error => throw (.resolve error)
      if let some key := declarations.find? (!group.path.isPrefixOf ·.groupPath) then
        throw (.referenceGroupDoesNotContainKey group.path key.groupPath)
      pure (some group)
  | none =>
      if let some (left, right) := firstKeyOffSharedPath? model declarations then
        throw (.keysOffOnePath left right)
      if let some outside := declarations.find? (!ruleGroup.isPrefixOf ·.groupPath) then
        throw (.keyOutsideRuleGroup outside.path)
      let repeatableRoot := ruleGroup.length == 1 &&
        model.repeatableGroups.any (·.path == ruleGroup) &&
        declarations.all (·.groupPath.length == 1)
      if !repeatableRoot then
        if let some key := declarations.find? (fun key =>
            !(model.repeatableGroups.any fun group =>
              ruleGroup.isPrefixOf group.path && group.path != ruleGroup &&
                group.path.isPrefixOf key.groupPath)) then
          throw (.missingReferenceGroup key.path)
      pure none

end A12Kernel
