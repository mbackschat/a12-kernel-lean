import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.RuleIterationDomain

namespace A12Kernel


namespace CheckedDocument

/-- Occupancy is coordinate-based across the document, not local to the rule's group.
Fixed group levels remain in the coordinates (iteration-domain grid, 2026-10-04).
Stored field content and explicit repeated rows contribute independently. -/
def validationOccupiedCoordinates (checked : CheckedDocument model) : List (List Nat) :=
  let rows := checked.source.instantiatedRows.filterMap fun row => do
    let group ← model.repeatableGroupAtLevel? row.group
    let scope := model.repeatableScopeForGroupPath group.path
    pure (model.groupCoordinates group.path (scope.zip row.path))
  let cells := checked.checkedCells.filterMap fun placement => do
    if !placement.cell.admitsGroupContent then none else do
      let declaration ← (model.lookupUniqueId placement.address.field).toOption
      pure (model.groupCoordinates declaration.groupPath
        (declaration.repeatableScope.zip placement.address.path) ++ [1])
  rows ++ cells

/-- Root-content dispatch includes explicit repeated rows and admitted stored fields. -/
def validationDispatchedRoots (checked : CheckedDocument model)
    (root : GroupPath) : List Nat :=
  let rows := checked.source.instantiatedRows.filterMap fun row => do
    let group ← model.repeatableGroupAtLevel? row.group
    if !root.isPrefixOf group.path then none else
      (model.groupCoordinates group.path
        ((model.repeatableScopeForGroupPath group.path).zip row.path)).head?
  let cells := checked.checkedCells.filterMap fun placement => do
    if !placement.cell.admitsGroupContent then none else do
      let declaration ← (model.lookupUniqueId placement.address.field).toOption
      if !root.isPrefixOf declaration.groupPath then none else
        (model.groupCoordinates declaration.groupPath
          (declaration.repeatableScope.zip placement.address.path)).head?
  rows ++ cells

/-- Full ordinary rule iteration uses model-declared bounds and the root dispatcher,
then projects the shared coordinate domain back onto named repeatable levels.
Physical encounter order followed by implicit coordinates preserves the native API's
existing deterministic order; the captures establish membership, not message order.
Staged native models without capacities retain their earlier physical-domain account;
the DM boundary always supplies capacities. A partial call walks the same domain `ungated`, since it
overrides the content gate (spec/10 §5).

An `ungated` rule, one evaluated without admitted content, runs under a nonrepeatable root that holds
none, as the Kernel's global rule bucket does
([KF507](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf507)): a negative, a small-side count or a
second root's read over a keyed level fires at its declared rows on a blank root
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-blank-root-dispatch-k06)).
A repeatable root keeps its dispatcher: every negative or small-side count measured over one is
refused statically, and the second-root rule measured there needs content beside it. -/
def fullValidationRowEnvironments (checked : CheckedDocument model)
    (scope : List RepeatableLevel) (ungated : Bool := false) :
    Except ActualRowEnvironmentError (List Env) := do
  let deepest ← match scope.reverse with
    | [] => throw .missingScope
    | deepest :: _ => pure deepest
  let group ← match model.repeatableGroupAtLevel? deepest with
    | none => throw (.unknownLevel deepest)
    | some group => pure group
  let expected := model.repeatableScopeForGroupPath group.path
  if scope != expected then throw (.incoherentScope scope expected)
  let bounds? := (List.range group.path.length).mapM fun depth =>
    match model.repeatableGroups.find? (·.path == group.path.take (depth + 1)) with
    | none => some 1
    | some group => group.repeatability
  match bounds? with
  | none => checked.validationRowEnvironments scope
  | some bounds =>
      let blankRoot := ungated && (model.repeatableScopeForGroupPath (group.path.take 1)).isEmpty
      let coordinates := RuleIterationDomain.coordinates bounds
        checked.validationOccupiedCoordinates
        (checked.validationDispatchedRoots (group.path.take 1) ++ if blankRoot then [1] else [])
      let environments ← coordinates.mapM fun path => scope.mapM fun level => do
        let declaration ← match model.repeatableGroupAtLevel? level with
          | none => throw (.unknownLevel level)
          | some declaration => pure declaration
        pure (level, path[declaration.path.length - 1]?.getD 1)
      let physical ← checked.actualRowEnvironments scope
      pure (physical.filter environments.contains ++ environments.filter (!physical.contains ·))

/-- The nested coordinates a parallel rule visits below its joined group at depth `joinedDepth`, inside
the joined row whose group coordinates are `stem`, for an error field in `errorGroup`. They follow the
ordinary capacity rule with the joined level counted once, and occupancy is document-wide with the
joined coordinate merged, so a nested row of another joined row, or of another group at the same
coordinate, counts; an unmatched joined side visits the same rows
([KF603](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf603);
[checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-nested-join-capacity)).
Each result is the coordinate suffix below the joined depth. `none` when a level declares no capacity. -/
def joinedInnerCoordinates (checked : CheckedDocument model) (errorGroup : GroupPath)
    (joinedDepth : Nat) (stem : List Nat) : Option (List (List Nat)) := do
  let bounds ← (List.range errorGroup.length).mapM fun depth =>
    match model.repeatableGroups.find? (·.path == errorGroup.take (depth + 1)) with
    | none => some 1
    | some group => group.repeatability
  let merged := fun (path : List Nat) => path.set joinedDepth 1
  let occupied := checked.validationOccupiedCoordinates.map merged
  let suffixes := RuleIterationDomain.descend (RuleIterationDomain.optimized (bounds.set joinedDepth 1))
    occupied ((merged stem).take (joinedDepth + 1)) (bounds.drop (joinedDepth + 1))
  pure (suffixes.map (·.drop (joinedDepth + 1)))

/-- Ordinary physical reads retain every check. Only a missing physical row which the
full-validation domain actually supplies can be read as an absent declared slot. The domain is the
ungated one: a slot under a blank root is reached only by an ungated rule, since the dispatcher keeps
every other rule off that root. -/
def fullValidationRead (checked : CheckedDocument model) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell :=
  match checked.read address with
  | .error (.missingRow row) =>
      let admitted := do
        let declaration ← (model.lookupUniqueId address.field).toOption
        let rows ← (checked.fullValidationRowEnvironments declaration.repeatableScope true).toOption
        pure (rows.contains (declaration.repeatableScope.zip address.path))
      if admitted == some true then checked.readDeclared address else .error (.missingRow row)
  | result => result

/-- The uniqueness relation always uses occupied prefixes and depth-wide document bounds,
even when its enclosing rule uses a small dense space. `RuntimeController`'s duplicate
iterator and the nested 2×2/2×3 RNU grid (2026-10-04) settle this distinction. -/
def repetitionKeyRowEnvironments (checked : CheckedDocument model)
    (scope : List RepeatableLevel) (bound : Env) :
    Except ActualRowEnvironmentError (List Env) := do
  let deepest ← match scope.reverse with
    | [] => throw .missingScope
    | level :: _ => pure level
  let group ← match model.repeatableGroupAtLevel? deepest with
    | none => throw (.unknownLevel deepest)
    | some group => pure group
  let expected := model.repeatableScopeForGroupPath group.path
  if scope != expected then throw (.incoherentScope scope expected)
  let firstOpen := scope[bound.length]?
  let firstDepth := firstOpen.bind (model.repeatableGroupAtLevel? ·) |>.map (·.path.length - 1)
  let depth := firstDepth.getD group.path.length
  let stem := model.groupCoordinates (group.path.take depth) bound
  let occupied := checked.validationOccupiedCoordinates
  let bounds := (List.range (group.path.length - depth)).map fun offset =>
    let index := depth + offset
    if model.repeatableGroups.any (·.path == group.path.take (index + 1)) then
      occupied.foldl (fun upper path => max upper (path[index]?.getD 1)) 1
    else 1
  let environments := (RuleIterationDomain.descend true occupied stem bounds).map fun path =>
    scope.map fun level =>
      let index := (model.repeatableGroupAtLevel? level).map (·.path.length - 1) |>.getD 0
      (level, path[index]?.getD 1)
  let physical ← checked.actualRowEnvironments scope
  pure (physical.filter environments.contains ++ environments.filter (!physical.contains ·))

end CheckedDocument
end A12Kernel
