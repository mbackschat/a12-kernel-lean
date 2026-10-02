import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Elaboration.NumericAggregate.Fields
import A12Kernel.Elaboration.EnumerationFirstFilledComputation

/-! # Lowering entity lists and row filters

An operator that ranges over fields, such as an aggregate, a count or `FirstFilledValue`, takes a
list of entity operands: a field, a starred field with an optional `Having` filter, a group or a
starred group. Whether an unstarred path names a field or a group is read off the model, the only
fact the surface does not carry. A filter body is the ordinary condition production over the
filtered row, `$` marking a read of the enclosing row (spec §9).
-/

namespace A12Kernel.Dm

/-- A filter operand's path without its `$`, and the origin the `$` selects. -/
def Path.havingField? (path : Path) : Option (HavingOrigin × SurfaceFieldPath) := do
  let field ← { path with correlated := false }.toFieldPath?
  pure (if path.correlated then .outer else .inner, field)

private def Path.havingGroup? (path : Path) : Option (HavingOrigin × SurfaceGroupReference) := do
  let group ← { path with correlated := false }.toGroupPath?
  pure (if path.correlated then .outer else .inner, .path group)

private def presencePolarity? : String → Option HavingPresencePolarity
  | "FieldFilled" => some .filled
  | "FieldNotFilled" => some .notFilled
  | _ => none

/-- A `Having` body (spec §9). Which comparison arm a read takes follows its right side: a quoted
literal compares a String, `CurrentRepetition` on both sides compares rows, and two field reads
compare Numbers. -/
partial def lowerHaving : Expr → Lowering SurfaceCorrelatedHaving
  | .parens body => lowerHaving body
  | .logic op (first :: rest) => do
      let join := match op with | .and => SurfaceCorrelatedHaving.and | .or => SurfaceCorrelatedHaving.or
      let mut result ← lowerHaving first
      for part in rest do result := join result (← lowerHaving part)
      pure result
  | .call id [.mk (.entity { path, index := none, category := none }) none none] none none =>
      match presencePolarity? id, path.havingField? with
      | some polarity, some (origin, field) => pure (.presence polarity { origin, field })
      | _, _ => refuse "Having" id
  | .compare op left right => do
      let some surfaceOp := op.toSurface? | refuse "Having" "operator"
      match left, right with
      | .value { path, index := none, category := none }, .string expected =>
          if isTemporalConstant expected then refuse "Having" "temporal constant" else
          match path.havingField?, surfaceOp with
          | some (origin, field), .equal => pure (.compareStrings .equal { origin, field } expected)
          | some (origin, field), .notEqual => pure (.compareStrings .notEqual { origin, field } expected)
          | _, _ => refuse "Having" "String comparison"
      | .value { path := leftPath, index := none, category := none },
          .value { path := rightPath, index := none, category := none } =>
          match leftPath.havingField?, rightPath.havingField? with
          | some (leftOrigin, leftField), some (rightOrigin, rightField) =>
              pure (.compareNumbers surfaceOp { origin := leftOrigin, field := leftField }
                { origin := rightOrigin, field := rightField })
          | _, _ => refuse "Having" "field comparison"
      | .call "CurrentRepetition" [.mk (.entity { path := leftPath, index := none, category := none })
            none none] none none,
          .call "CurrentRepetition" [.mk (.entity { path := rightPath, index := none, category := none })
            none none] none none =>
          match leftPath.havingGroup?, rightPath.havingGroup? with
          | some (leftOrigin, leftGroup), some (rightOrigin, rightGroup) =>
              pure (.compareRepetitions surfaceOp { origin := leftOrigin, group := leftGroup }
                { origin := rightOrigin, group := rightGroup })
          | _, _ => refuse "Having" "CurrentRepetition"
      | _, _ => refuse "Having" "comparison shape"
  | other => refuse "Having" other.construct

/-- Whether an unstarred path names a field of the model, read at the operator's group. -/
def namesField (model : FlatModel) (group : GroupPath) (path : SurfaceFieldPath) : Bool :=
  (model.resolveFieldDeclarationUnchecked group path).toOption.isSome

/-- One entity-list operand. -/
def lowerEntityOperand (model : FlatModel) (group : GroupPath) :
    Argument → Lowering SurfaceFieldEntityOperand
  | .mk (.constant "RuleGroup") none none => pure (.group (.ruleGroup false))
  | .mk (.entity { path, index := none, category }) none filter => do
      if path.correlated then refuse "EntityOperand" "correlated"
      let terminalStar := path.segments.getLast?.any (·.star)
      if terminalStar then
        if filter.isSome then refuse "EntityOperand" "filtered starred group"
        pure (.starredGroup { base := path.base, groups := path.starGroups })
      else if path.segments.any (·.star) then
        -- A starred path names a group below its star when its unstarred spelling names no field.
        let unstarred : Path := { path with segments := path.segments.map fun segment => { segment with star := false } }
        if (unstarred.toFieldPath?).all (!namesField model group ·) then
          if filter.isSome || category.isSome then refuse "EntityOperand" "filtered starred group"
          return .starredGroup { base := path.base, groups := path.starGroups }
        let some star := path.toStarFieldPath? | refuse "EntityOperand" "star path"
        if category.isSome then refuse "EntityOperand" "category on a star"
        match filter with
        | none => pure (.star star)
        | some body => pure (.starHaving star (← lowerHaving body))
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
  | .mk expr _ _ => refuse "EntityOperand" expr.construct

def lowerEntitySource (model : FlatModel) (group : GroupPath) (arguments : List Argument) :
    Lowering SurfaceFieldEntitySource := do
  let first :: rest ← arguments.mapM (lowerEntityOperand model group) | refuse "EntityOperand" "empty"
  pure { first, rest }

/-- One operand of a String or Enumeration value count, which keeps its category projection on a
starred read too. -/
def lowerProjectedTokenOperand (model : FlatModel) (group : GroupPath) (argument : Argument) :
    Lowering SurfaceProjectedTokenEntityOperand := do
  match argument with
  | .mk (.entity { path, index := none, category }) none filter =>
      let projection : EnumerationProjectionRef := match category with
        | some name => .category name
        | none => .stored
      if path.segments.any (·.star) then
        let some star := path.toStarFieldPath? | refuse "EntityOperand" "star path"
        match filter with
        | none => pure (.star star projection)
        | some body => pure (.starHaving star projection (← lowerHaving body))
      else
        let some field := path.toFieldPath? | refuse "EntityOperand" "path"
        if filter.isSome then refuse "EntityOperand" "filter on an unstarred operand"
        pure (.field (match category with | some name => .category field name | none => .direct field))
  | _ => do
      let _ ← lowerEntityOperand model group argument
      refuse "EntityOperand" "group in a value count"

/-- An Enumeration `FirstFilledValue` source: each operand a direct or starred field keeping its
category projection, a starred one its own filter. -/
def lowerEnumerationFirstFilledSource (model : FlatModel) (group : GroupPath) (arguments : List Argument) :
    Lowering SurfaceEnumerationFirstFilledSource := do
  let operand (argument : Argument) : Lowering SurfaceEnumerationFirstFilledOperand := do
    match ← lowerProjectedTokenOperand model group argument with
    | .field source => pure (.field source)
    | .star source projection => pure (.star source projection)
    | .starHaving source projection having => pure (.star source projection (some having))
  let first :: rest ← arguments.mapM operand | refuse "EntityOperand" "empty"
  pure { first, rest }

/-- `SumOfProducts(left, right)` over two starred fields, each with its own optional filter. -/
def lowerProductAggregate (arguments : List Argument) : Lowering SurfaceNumericProductAggregate := do
  let [.mk (.entity { path := leftPath, index := none, category := none }) none leftFilter,
      .mk (.entity { path := rightPath, index := none, category := none }) none rightFilter] := arguments
    | refuse "SumOfProducts" "operands"
  let some left := leftPath.toStarFieldPath? | refuse "SumOfProducts" "operand"
  let some right := rightPath.toStarFieldPath? | refuse "SumOfProducts" "operand"
  pure { left, right, leftHaving := ← leftFilter.mapM lowerHaving
         rightHaving := ← rightFilter.mapM lowerHaving }

/-- A filled-group count operand: a starred group keeps its stars, anything else is a fixed group. -/
def lowerGroupCountOperand : Argument → Lowering SurfaceGroupCountOperand
  | .mk (.constant "RuleGroup") none none => pure (.fixed (.ruleGroup false))
  | .mk (.entity { path, index := none, category := none }) none none =>
      if path.correlated then refuse "NumberOfFilledGroups" "correlated"
      else if path.segments.any (·.star) then
        pure (.starred { base := path.base, groups := path.starGroups })
      else match path.toGroupPath? with
        | some group => pure (.fixed (.path group))
        | none => refuse "NumberOfFilledGroups" "operand"
  | _ => refuse "NumberOfFilledGroups" "operand"

end A12Kernel.Dm
