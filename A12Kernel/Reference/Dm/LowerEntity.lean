import A12Kernel.Reference.Dm.LowerStringCore
import A12Kernel.Elaboration.FirstFilledFieldSource
import A12Kernel.Reference.Dm.LowerFlat
import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Reference.Dm.LowerHavingTemporal
import A12Kernel.Elaboration.IndexKeyShape
import A12Kernel.Semantics.NumericInput
import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Elaboration.NumericAggregate.Products
import A12Kernel.Elaboration.EnumerationFirstFilledComputation

import A12Kernel.Reference.Dm.HavingAdmission
import A12Kernel.Reference.Dm.RefusalClass

namespace A12Kernel.Dm

/-- Fixed and addressed Enumeration first-filled carriers retain the same calculation refusal identity; unclassified carrier errors keep their local detail. -/
def elaboratedEnumerationFirstFilled [Repr ε] (calculationRefusal : ε → Option CalculationRefusal) :
    Except ε α → Lowering α
  | .ok value => .ok value
  | .error error => .error {
      construct := "FirstFilledValue"
      detail := (calculationRefusal error).map (·.catalogKey) |>.getD (oneLine ((repr error).pretty 100000)) }

/-- Whether an unstarred path names a field of the model, read at the operator's group. -/
def namesField (model : FlatModel) (group : GroupPath) (path : SurfaceFieldPath) : Bool :=
  (model.resolveFieldDeclarationUnchecked group path).toOption.isSome

private def lowerIndexKey (index : FlatFieldDecl) (key : IndexKey) : Lowering SurfaceSemanticIndexKey := do
  let key ← match key with
    | .literal authored => do
        let spelling := normalizeLinebreaks authored
        if spelling.isEmpty then refuse "SemanticIndex" "empty key"
        let matcher : String → Bool ← match index.stringPatternSource with
          | none => pure (fun (_ : String) => true)
          | some pattern => match locallyExecutableStringPatternMatcher? pattern with
              | some matcher => pure matcher
              | none => refuse "SemanticIndex" "unsupported key pattern"
        if index.indexKeyFits? matcher authored != some true then
          refuse "SemanticIndex" "invalid key shape"
        let some token := index.semanticIndexLiteral? spelling | refuse "SemanticIndex" "numeric key"
        pure (SurfaceSemanticIndexKey.literal token (some spelling))
    | .reference { path := authored, index := none, category := none, filter := none } => do
        let some field := authored.toFieldPath? | refuse "SemanticIndex" "key path"
        pure (.field field)
    | .reference _ => refuse "SemanticIndex" "key modifiers"
  pure key

def lowerIndexedSource (model : FlatModel) (group : GroupPath)
    (path : Path) (key : IndexKey) : Lowering SurfaceSemanticIndex := do
  let some target := path.toFieldPath? | refuse "SemanticIndex" "target path"
  let declaration ← elaborated "SemanticIndex" (model.resolveFieldDeclarationUnchecked group target)
  let some selectedGroup := model.semanticIndexGroupForPath? declaration.groupPath
    | refuse "SemanticIndex" "missing index"
  let some indexId := selectedGroup.indexField | refuse "SemanticIndex" "missing index"
  let index ← elaborated "SemanticIndex" (model.lookupUniqueId indexId)
  pure { target, key := ← lowerIndexKey index key }

private def lowerKeyedExtent (model : FlatModel) (group : GroupPath)
    (path : Path) (key : IndexKey) : Lowering SurfaceKeyedEntityExtent := do
  if path.correlated then refuse "SemanticIndex" "correlated extent"
  let (target, targetGroup) ← if path.segments.any (·.star) then do
      let unstarred : Path := { path with segments := path.segments.map fun segment => { segment with star := false } }
      if unstarred.toFieldPath?.any (namesField model group) then
        let some star := path.toStarFieldPath? | refuse "SemanticIndex" "starred extent"
        let source ← elaborated "SemanticIndex" (elaborateStarFieldPath model group star)
        pure (SurfaceKeyedEntityTarget.star star, source.declaration.groupPath)
      else
        let target : SurfaceStarGroupPath := { base := path.base, groups := path.starGroups }
        let source ← elaborated "SemanticIndex" (elaborateStarredGroupOperandSource model group target)
        let resolved := match source with
          | .terminalRepeatable source => source.group.path
          | .terminalPresence source => source.groupPath
        pure (SurfaceKeyedEntityTarget.starredGroup target, resolved)
    else do
      let some target := path.toGroupPath? | refuse "SemanticIndex" "group extent"
      let resolved ← elaborated "SemanticIndex" (target.resolveAgainst group)
      pure (SurfaceKeyedEntityTarget.group target, resolved)
  let some selectedGroup := model.semanticIndexGroupForPath? targetGroup | refuse "SemanticIndex" "missing index"
  let some indexId := selectedGroup.indexField | refuse "SemanticIndex" "missing index"
  let index ← elaborated "SemanticIndex" (model.lookupUniqueId indexId)
  pure { target, key := ← lowerIndexKey index key }

/-- One entity-list operand. -/
def lowerEntityOperand (model : FlatModel) (group : GroupPath) (argument : Argument)
    (bindingGroup? : Option GroupPath := none) (suppress : Bool := false) : Lowering SurfaceFieldEntityOperand := do
  let authored ← lower argument
  if let some bindingGroup := bindingGroup? then
    discard <| (resolveFieldEntityOperandIn model group
      (model.repeatableScopeForGroupPath bindingGroup) authored (writtenGroup := bindingGroup)).mapError fun error => {
        construct := "EntityOperand"
        detail := error.diagnostic?.map (·.kernelCode) |>.getD (oneLine ((repr error).pretty 100000)) }
  pure authored
where
  lower : Argument → Lowering SurfaceFieldEntityOperand
    | .mk (.constant "RuleGroup") none => pure (.group (.ruleGroup false))
    | .mk (.entity { path, index := some key, category, filter := none }) none =>
        let form := match category with | some name => .projected name | none => .stored
        if path.toFieldPath?.any (namesField model group) then
          (.indexed · form) <$> lowerIndexedSource model group path key
        else (.keyed · form) <$> lowerKeyedExtent model group path key
    | .mk (.entity { path, index := none, category, filter }) none => do
        if path.correlated then refuse "EntityOperand" "correlated"
        let terminalStar := path.segments.getLast?.any (·.star)
        if terminalStar then
          if category.isSome then refuse "EntityOperand" "category on a group"
          if filter.isSome then refuse "EntityOperand" "filtered starred group"
          pure (.starredGroup { base := path.base, groups := path.starGroups })
        else if path.segments.any (·.star) then
          -- A starred path names a group below its star when its unstarred spelling names no field.
          let unstarred : Path := { path with segments := path.segments.map fun segment => { segment with star := false } }
          if (unstarred.toFieldPath?).all (!namesField model group ·) then
            if filter.isSome || category.isSome then refuse "EntityOperand" "filtered starred group"
            return .starredGroup { base := path.base, groups := path.starGroups }
          let some star := path.toStarFieldPath? | refuse "EntityOperand" "star path"
          let form := match category with | some name => .projected name | none => .stored
          match filter with
          | none => pure (.star star form)
          | some body => pure (.starHaving star (← lowerAdmittedHaving model group star body bindingGroup? suppress) form)
        else
          if filter.isSome then refuse "EntityOperand" "filter on an unstarred operand"
          match path.toFieldPath?, path.toGroupPath? with
          | some field, _ =>
              if namesField model group field then
                pure (.field field (match category with | some name => .projected name | none => .stored))
              else if category.isSome then refuse "EntityOperand" "category on a group"
              else match path.toGroupPath? with
                | some groupPath => pure (.group (.path groupPath))
                | none => refuse "EntityOperand" "path"
          | none, some groupPath =>
              if category.isSome then refuse "EntityOperand" "category on a group"
              pure (.group (.path groupPath))
          | none, none => refuse "EntityOperand" "path"
    | .mk expr _ => refuse "EntityOperand" expr.construct

def lowerEntitySource (model : FlatModel) (group : GroupPath) (arguments : List Argument)
    (bindingGroup? : Option GroupPath := none) (suppress : Bool := false) : Lowering SurfaceFieldEntitySource := do
  -- Each contextual read finishes before a later list can enter a filter (spec/07 §3).
  let first :: rest ← arguments.mapM (fun argument => lowerEntityOperand model group argument bindingGroup? suppress) | refuse "EntityOperand" "empty"
  pure { first, rest }

def lowerFirstFilledEntitySource (model : FlatModel) (group : GroupPath) (arguments : List Argument)
    (bindingGroup? : Option GroupPath := none) (suppress : Bool := false) : Lowering SurfaceFieldEntitySource := do
  if let some bindingGroup := bindingGroup? then
    for argument in arguments do
      if let .mk (.entity reference) none := argument then
        checkReferenceRead model group bindingGroup reference
  lowerEntitySource model group arguments bindingGroup? suppress

/-- One operand of a String or Enumeration value count, which keeps its category projection on a
starred read too. -/
def lowerProjectedTokenOperand (model : FlatModel) (group : GroupPath) (argument : Argument)
    (bindingGroup? : Option GroupPath := none) (suppress : Bool := false) :
    Lowering SurfaceProjectedTokenEntityOperand := do
  if let some bindingGroup := bindingGroup? then
    if let .mk (.entity reference) none := argument then
      checkReferenceRead model group bindingGroup reference
  match argument with
  | .mk (.entity { path, index := none, category, filter }) none =>
      let projection : EnumerationProjectionRef := match category with
        | some name => .category name
        | none => .stored
      if path.segments.any (·.star) then
        let some star := path.toStarFieldPath? | refuse "EntityOperand" "star path"
        match filter with
        | none => pure (.star star projection)
        | some body => pure (.starHaving star projection (← lowerFilter body (some (model, group)) suppress))
      else
        let some field := path.toFieldPath? | refuse "EntityOperand" "path"
        if filter.isSome then refuse "EntityOperand" "filter on an unstarred operand"
        pure (.field (match category with | some name => .category field name | none => .direct field))
  | _ => do
      let _ ← lowerEntityOperand model group argument bindingGroup? suppress
      refuse "EntityOperand" "group in a value count"

/-- An Enumeration `FirstFilledValue` source retains selected identity, direct/category projection,
and each ordinary star’s own filter. -/
def lowerEnumerationFirstFilledSource (model : FlatModel) (group : GroupPath) (arguments : List Argument)
    (bindingGroup? : Option GroupPath := none) (suppress : Bool := false) :
    Lowering SurfaceEnumerationFirstFilledSource := do
  let operand (argument : Argument) : Lowering SurfaceEnumerationFirstFilledOperand := do
    if let .mk (.entity reference@{ index := some _, filter := none, .. }) none := argument then
      if let some bindingGroup := bindingGroup? then
        checkReferenceRead model group bindingGroup reference
      match ← lowerEntityOperand model group argument bindingGroup? suppress with
      | .indexed source form => return .indexed source form
      | .keyed source form => return .keyed source form
      | _ => refuse "EntityOperand" "indexed source"
    match ← lowerProjectedTokenOperand model group argument bindingGroup? suppress with
    | .field source => pure (.field source)
    | .star source projection => pure (.star source projection)
    | .starHaving source projection having => pure (.star source projection (some having))
  let first :: rest ← arguments.mapM operand | refuse "EntityOperand" "empty"
  pure { first, rest }

/-- `SumOfProducts(left, right)` retains each starred field's key and optional filter for checked admission. -/
def lowerProductAggregate (model : FlatModel) (group : GroupPath) (arguments : List Argument)
    (bindingGroup? : Option GroupPath := none) (suppress : Bool := false) : Lowering SurfaceNumericProductAggregate := do
  if let some bindingGroup := bindingGroup? then
    for argument in arguments do
      if let .mk (.entity reference) none := argument then
        checkReferenceRead model group bindingGroup reference
  let [.mk (.entity { path := leftPath, index := leftIndex, category := none, filter := leftFilter }) none,
      .mk (.entity { path := rightPath, index := rightIndex, category := none, filter := rightFilter }) none] := arguments
    | refuse "SumOfProducts" "operands"
  let some left := leftPath.toStarFieldPath? | refuse "SumOfProducts" "operand"
  let some right := rightPath.toStarFieldPath? | refuse "SumOfProducts" "operand"
  pure { left, right, leftHaving := ← leftFilter.mapM (fun body => lowerFilter body (some (model, group)) suppress)
         rightHaving := ← rightFilter.mapM (fun body => lowerFilter body (some (model, group)) suppress)
         leftKey := ← leftIndex.mapM (fun key => (·.key) <$> lowerKeyedExtent model group leftPath key)
         rightKey := ← rightIndex.mapM (fun key => (·.key) <$> lowerKeyedExtent model group rightPath key) }

/-- A filled-group count operand: a starred group keeps its stars, anything else is a fixed group. -/
def lowerGroupCountOperand : Argument → Lowering SurfaceGroupCountOperand
  | .mk (.constant "RuleGroup") none => pure (.fixed (.ruleGroup false))
  | .mk (.entity { path, index := none, category := none, filter := none }) none =>
      if path.correlated then refuse "NumberOfFilledGroups" "correlated"
      else if path.segments.any (·.star) then
        pure (.starred { base := path.base, groups := path.starGroups })
      else match path.toGroupPath? with
        | some group => pure (.fixed (.path group))
        | none => refuse "NumberOfFilledGroups" "operand"
  | _ => refuse "NumberOfFilledGroups" "operand"

/-- The common authored source dispatch for fixed and row first-filled targets. A lone starred
operand takes the entity-list route too, as the Kernel admits it under two stars at a fixed target and
at six row placements, selecting parent-major
([fixed](../../../docs/sources/computation-placement-and-constant-probes.md#src-typed-first-filled-nested-stars),
[rows](../../../docs/sources/computation-placement-and-constant-probes.md#src-typed-first-filled-row-placements));
deeper nesting is assumed to follow the same list order. -/
def lowerFirstFilledSource (model : FlatModel) (group : GroupPath) (arguments : List Argument)
    (bindingGroup? : Option GroupPath := none) (suppress : Bool := false) : Lowering SurfaceFirstFilledSource :=
  (.list ·) <$> lowerFirstFilledEntitySource model group arguments bindingGroup? suppress

end A12Kernel.Dm
