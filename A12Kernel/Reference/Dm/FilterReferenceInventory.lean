import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Elaboration.IterationLegality

namespace A12Kernel.Dm

private abbrev Inventory := List FilterIndexedReference × Bool

private def joinInventory (left right : Inventory) : Inventory :=
  (left.1 ++ right.1, left.2 || right.2)

private def referenceLevels (model : FlatModel) (declaringGroup : GroupPath)
    (candidate reopened : List RepeatableLevel) (reference : Reference) : Lowering FilterIndexedReference := do
  let plain : Path := { reference.path with
    correlated := false
    segments := reference.path.segments.map fun segment => { segment with star := false } }
  let some field := plain.toFieldPath? | refuse "HavingWalk" "entity path"
  let path ← match model.resolveFieldDeclarationUnchecked declaringGroup field with
    | .ok declaration => pure declaration.path
    | .error error => match model.groupNamedBy? declaringGroup field with
        | some group => pure group
        | none => elaborated "HavingWalk" (.error error : Except ResolveError GroupPath)
  let indexed ← if reference.index.isSome then do
      let some group := model.semanticIndexGroupForPath? path | refuse "HavingWalk" "unresolved index group"
      pure (some group)
    else pure none
  let indexedLevel := indexed.bind (·.level?)
  -- Lexical resolution may supply an implicit prefix; authored stars still belong to their
  -- original named suffix. Index metadata remains separate throughout this phase (spec/07 §3).
  let offset := path.length - reference.path.segments.length
  let levels ← (model.repeatableScopeForGroupPath path).mapM fun level => do
    let some group := model.repeatableGroupAtLevel? level | refuse "HavingWalk" "unresolved repetition"
    let position := group.path.length - 1
    let starred := position >= offset &&
      (reference.path.segments[position - offset]?).any (·.star)
    let marker := if indexedLevel == some level then IndexMarker.semanticIndex
      else if starred then .wildcard else .iteration
    pure (group.path.length, ({
      marker
      onFilteredPath := candidate.contains level
      reopensFilteredLevel := reopened.contains level } : FilterIndexLevel))
  -- A root or fixed group's key selects no repetition level, so it takes its group's position among
  -- the levels: the Kernel refuses it in a filter body as a repeatable group's key
  -- (docs/sources/model-structure-and-declaration-probes.md#src-single-instance-key-filter-message-overcap).
  let levels := match indexed with
    | some (.single groupPath _) =>
        let (outer, inner) := levels.span (·.1 < groupPath.length)
        outer.map (·.2) ++ [{ marker := .semanticIndex }] ++ inner.map (·.2)
    | _ => levels.map (·.2)
  pure { levels, marked := reference.path.correlated }

mutual
private partial def expressionInventory (model : FlatModel) (group : GroupPath)
    (candidate reopened : List RepeatableLevel) : Expr → Lowering Inventory
  | .entity reference | .value reference => referenceInventory model group candidate reopened reference
  | .constant "RuleGroup" => referenceInventory model group candidate reopened {
      path := { absolute := true, segments := group.map fun name => { name, star := false } } }
  | .custom .. => pure ([], true)
  | .arith _ left right | .compare _ left right => do
      pure (joinInventory (← expressionInventory model group candidate reopened left)
        (← expressionInventory model group candidate reopened right))
  | .parens body | .braces body => expressionInventory model group candidate reopened body
  | .logic _ parts => do
      let inventories ← parts.mapM (expressionInventory model group candidate reopened)
      pure (inventories.foldl joinInventory ([], false))
  | .call name arguments listed scope => do
      let main ← argumentsInventory model group candidate reopened arguments
      let members ← argumentsInventory model group candidate reopened (listed.getD [])
      let scope ← match scope with
        | none => pure ([], false)
        | some reference => referenceInventory model group candidate reopened reference
      let combined := joinInventory (joinInventory main members) scope
      pure (combined.1, combined.2 || name == "RepetitionNotUnique")
  | _ => pure ([], false)

private partial def referenceInventory (model : FlatModel) (group : GroupPath)
    (candidate reopened : List RepeatableLevel) (reference : Reference) : Lowering Inventory := do
  let own ← referenceLevels model group candidate reopened reference
  let key ← match reference.index with
    | some (.reference child) => referenceInventory model group candidate reopened child
    | _ => pure ([], false)
  let body ← match reference.filter with
    | none => pure ([], false)
    | some expression => expressionInventory model group candidate reopened expression
  let children := joinInventory key body
  pure (own :: children.1, reference.filter.isSome || children.2)

private partial def argumentsInventory (model : FlatModel) (group : GroupPath)
    (candidate reopened : List RepeatableLevel) : List Argument → Lowering Inventory
  | [] => pure ([], false)
  | .mk first rangeEnd :: rest => do
      let first ← expressionInventory model group candidate reopened first
      let last ← match rangeEnd with
        | none => pure ([], false)
        | some expression => expressionInventory model group candidate reopened expression
      pure (joinInventory (joinInventory first last)
        (← argumentsInventory model group candidate reopened rest))
end

/-- Inventory a body's references before certifying its base star; key-filter body errors can
precede that base's star requirement (spec/07 §3). Own-read checks remain a precondition. -/
def filterBodyInventoryAtLevels (model : FlatModel) (declaringGroup : GroupPath)
    (candidate reopened : List RepeatableLevel) (expression : Expr) :
    Lowering (List FilterIndexedReference × Bool) :=
  expressionInventory model declaringGroup candidate reopened expression

/-- Recover the filter walk's authored reference order, including keys, scopes and nested bodies.
This is the post-read walk input, not whole-condition admission: own read/operator checks precede
it, and marked semantic-index refusal follows parsing (spec/07 §3). -/
def filterBodyInventory (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr) :
    Lowering (List FilterIndexedReference × Bool) :=
  let candidate := source.path.axes.map (·.level)
  filterBodyInventoryAtLevels model declaringGroup candidate (candidate.drop source.path.firstStar) expression

end A12Kernel.Dm
