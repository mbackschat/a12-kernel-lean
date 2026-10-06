import A12Kernel.Reference.Dm.LowerFlat
import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.IndexKeyShape
import A12Kernel.Semantics.NumericInput
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

def groupQuantifier? : String → Option GroupFillQuantifier
  | "AllGroupsFilled" => some .allGroupsFilled
  | "NoGroupFilled" => some .noGroupFilled
  | "AtLeastOneGroupFilled" => some .atLeastOneGroupFilled
  | "NotAllGroupsFilled" => some .notAllGroupsFilled
  | "GroupsNotCollectivelyFilled" => some .groupsNotCollectivelyFilled
  | _ => none

def fieldFillOp? : String → Option FieldFillQuantifier
  | "AllFieldsFilled" => some .allFieldsFilled
  | "NoFieldFilled" => some .noFieldFilled
  | "AtLeastOneFieldFilled" => some .atLeastOneFieldFilled
  | "MoreThanOneFieldFilled" => some .moreThanOneFieldFilled
  | "NotAllFieldsFilled" => some .notAllFieldsFilled
  | "NotExactlyOneFieldFilled" => some .notExactlyOneFieldFilled
  | "FieldsNotCollectivelyFilled" => some .fieldsNotCollectivelyFilled
  | _ => none


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

private def lowerHavingNumericAtom : Expr → Lowering SurfaceHavingNumericAtom
  | .call id arguments none none => if let some op := aggregateOp? id then do
      let sources ← arguments.mapM fun
        | .mk (.entity { path, index := none, category := none }) none none => do
            let some (origin, field) := path.havingField? | refuse "Having" "aggregate field"
            pure ({ origin, field } : SurfaceHavingNumberRef)
        | _ => refuse "Having" "aggregate operands"
      let first :: rest := sources | refuse "Having" "aggregate arity"
      pure (.aggregate op first rest)
    else lowerNonAggregateHavingNumericAtom (.call id arguments none none)
  | other => lowerNonAggregateHavingNumericAtom other
where
  lowerNonAggregateHavingNumericAtom : Expr → Lowering SurfaceHavingNumericAtom
    | .call id [.mk left none none, .mk right none none] none none => do
        let field : Expr → Option SurfaceHavingTemporalRef
          | .entity { path, index := none, category := none } => do
              let (origin, field) ← path.havingField?
              pure { origin, field }
          | _ => none
        if id == "DifferenceInDays" || (calendarUnit? id).isSome then
          let some left := dateDifferenceOperandWith? field left | refuse "Having" "difference left"
          let some right := dateDifferenceOperandWith? field right | refuse "Having" "difference right"
          if id == "DifferenceInDays" then return .dayDifference left right
          let some unit := calendarUnit? id | refuse "Having" "difference unit"
          return .dateDifference unit left right
        let some left := dateDifferenceOperandWith? field left | refuse "Having" "difference left"
        let some right := dateDifferenceOperandWith? field right | refuse "Having" "difference right"
        let some unit := subdayUnit? id | refuse "Having" "difference unit"
        pure (.dateTimeDifference unit left right)
    | .constant "BaseYear" => pure .baseYear
    | .call id [.mk (.constant "BaseYear") none none] none none => do
        let some part := datePart? id | refuse "Having" "BaseYear component"
        pure (.baseYearDatePart .direct part)
    | .call id [.mk (.call bound [.mk (.constant "BaseYear") none none] none none) none none] none none => do
        let some part := datePart? id | refuse "Having" "BaseYear component"
        let source ← match bound with
          | "StartOfDateRange" => pure (.range .start)
          | "EndOfDateRange" => pure (.range .finish)
          | _ => refuse "Having" "BaseYear endpoint"
        pure (.baseYearDatePart source part)
    | .call id [.mk (.call bound [.mk (.entity { path, index := none, category := none }) none none] none none) none none] none none => do
        let some part := datePart? id | refuse "Having" "DateRange component"
        let some (origin, field) := path.havingField? | refuse "Having" "DateRange field"
        let bound ← match bound with
          | "StartOfDateRange" => pure DateRangeBound.start
          | "EndOfDateRange" => pure DateRangeBound.finish
          | _ => refuse "Having" "DateRange endpoint"
        pure (.dateRangeBoundPart origin field bound part)
    | .call "FieldValueAsNumber" [.mk (.entity { path, index := none, category }) none none] none none => do
        let some (origin, field) := path.havingField? | refuse "Having" "conversion field"
        pure (.fieldValueAsNumber {
          origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored })
    | .call "Length" [.mk (.entity { path, index := none, category := none }) none none] none none =>
        match path.havingField? with
        | some (origin, field) => pure (.stringLength origin field)
        | none => refuse "Having" "Length field"
    | .value { path, index := none, category := none } =>
        match path.havingField? with
        | some (origin, field) => pure (.field { origin, field })
        | none => refuse "Having" "numeric field"
    | .call "CurrentRepetition" [.mk (.entity { path, index := none, category := none })
          none none] none none =>
        match path.havingGroup? with
        | some (origin, group) => pure (.repetition { origin, group })
        | none => refuse "Having" "CurrentRepetition"
    | .call "RangeAsNumber" [.mk (.entity { path, index := none, category := none }) none none,
          .mk (.number start) none none, .mk (.number finish) none none] none none => do
        let some (origin, field) := path.havingField? | refuse "Having" "range field"
        let some start := start.toNat? | refuse "Having" "range start"
        let some finish := finish.toNat? | refuse "Having" "range finish"
        pure (.stringRange origin field start finish)
    | .call id [.mk (.entity { path, index := none, category := none }) none none] none none => do
        let some (origin, field) := path.havingField? | refuse "Having" "temporal field"
        let some part := (datePart? id).map TemporalNumericPart.date |>.orElse
          (fun _ => (timePart? id).map TemporalNumericPart.time) | refuse "Having" "numeric source"
        pure (.temporalPart origin field part)
    | other => refuse "Having" other.construct
private def lowerHavingNumericField (source : Expr) : Lowering SurfaceHavingNumericAtom := do
  let reference ← numericFieldFormReference source
  lowerHavingNumericAtom (.value reference)

private def havingMember? : Expr → Option SurfaceHavingDirectFieldOperand
  | .value { path, index := none, category } => do
      let (origin, field) ← path.havingField?
      pure { origin, field, form := category.map FieldEntityReadForm.projected |>.getD .stored }
  | _ => none

private def havingEntity? : Expr → Option SurfaceHavingDirectFieldOperand
  | .entity reference => havingMember? (.value reference)
  | _ => none

private def havingMembers (expressions : List Expr) : Lowering SurfaceHavingDirectFieldSource := do
  let some (first :: rest) := expressions.mapM havingEntity? | refuse "Having" "direct membership fields"
  pure { first, rest }

/-- A filter comparison uses the shared numeric expression reader over correlated field and
repetition atoms. Typed field pairs, Boolean/text literals and presence retain their operand domains. -/
partial def lowerHaving : Expr → Lowering SurfaceCorrelatedHaving
  | .parens body => lowerHaving body
  | .logic op (first :: rest) => do
      let join := match op with | .and => SurfaceCorrelatedHaving.and | .or => SurfaceCorrelatedHaving.or
      let mut result ← lowerHaving first
      for part in rest do result := join result (← lowerHaving part)
      pure result
  | .call id arguments (some members) none => do
      let some operator := valueListQuantifier? id | refuse "Having" id
      let plain (arguments : List Argument) := arguments.mapM fun
        | .mk expression none none => pure expression
        | _ => refuse "Having" "direct membership fields"
      let subjects ← havingMembers (← plain arguments)
      let values ← plain members
      if let some literals := values.mapM (fun | .string value => some value | _ => none) then
        return .literalList operator subjects literals
      pure (.fieldMembership (.quantified operator) subjects (← havingMembers values))
  | .call id arguments none none => do
      if id == "FieldValueIncludedInValueList" || id == "FieldValueNotIncludedInValueList" then
        let operator := if id == "FieldValueIncludedInValueList" then ValueListMembershipOp.included else .notIncluded
        let .mk (.entity { path, index := none, category }) none none :: rest := arguments |
          refuse "Having" "membership subject"
        let some (origin, field) := path.havingField? | refuse "Having" "membership path"
        let values ← rest.mapM fun | .mk expression none none => pure expression | _ => refuse "Having" "membership member"
        let reference : SurfaceHavingStringRef := {
          origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored }
        if let some (first :: rest) := values.mapM havingMember? then
          return .fieldMembership (.scalar operator)
            { first := { origin, field, form := category.map FieldEntityReadForm.projected |>.getD .stored }, rest := [] }
            { first, rest }
        if let some strings := values.mapM (fun | .string value => some value | _ => none) then
          return .literalMembership operator reference (.inr strings)
        let integers ← values.mapM fun expression => do
          let .number text := expression | refuse "Having" "integer member"
          let some literal := decodeNumber? text | refuse "Having" "integer member"
          if literal.authoredScale == 0 then pure literal.value.num else refuse "Having" "integer member"
        return .literalMembership operator reference (.inl integers)
      if let some polarity := presencePolarity? id then
        match arguments with
        | [.mk (.entity { path, index := none, category := none }) none none] =>
            let some (origin, field) := path.havingField? | refuse "Having" "presence path"
            return .presence polarity { origin, field }
        | _ => refuse "Having" "presence arity"
      let some operator := fieldFillOp? id | refuse "Having" id
      let references ← arguments.mapM fun argument => match argument with
        | .mk (.entity { path, index := none, category := none }) none none =>
            match path.havingField? with
            | some (origin, field) => pure ({ origin, field } : SurfaceHavingDirectFieldOperand)
            | none => refuse "Having" "field-fill path"
        | _ => refuse "Having" "field-fill operand"
      let first :: rest := references | refuse "Having" "field-fill arity"
      pure (.fieldFill operator { first, rest })
  | .compare op@(.tolerance _) left right => do
      let some (.tolerance range) := op.toNumeric? | refuse "Having" "tolerance band"
      pure (.tolerance range
        (← lowerNumericExpr lowerHavingNumericAtom lowerHavingNumericField left)
        (← lowerNumericExpr lowerHavingNumericAtom lowerHavingNumericField right))
  | .compare op left right => do
      let some surfaceOp := op.toSurface? | refuse "Having" "operator"
      let temporal (field other : Expr) (position : SurfacePointInTimePosition) : Option SurfaceCorrelatedHaving := do
        let .value { path, index := none, category := none } := field | none
        let (origin, field) ← path.havingField?
        let source ← dateDifferenceOperandWith? (fun _ => (none : Option Empty)) other
        pure (.compareTemporal surfaceOp position { origin, field } source)
      if let some condition := (temporal left right .right).orElse (fun _ => temporal right left .left) then
        return condition
      match left, right with
      | .value { path, index := none, category := none }, .constant literal
      | .constant literal, .value { path, index := none, category := none } =>
          match path.havingField?, surfaceOp.toEquality?, literal with
          | some (origin, field), some equality, "True" =>
              pure (.compareBoolean equality { origin, field } true)
          | some (origin, field), some equality, "False" =>
              pure (.compareBoolean equality { origin, field } false)
          | _, _, _ => refuse "Having" "Boolean comparison"
      | .value { path := left, index := none, category := leftCategory },
          .value { path := right, index := none, category := rightCategory } =>
          match left.havingField?, right.havingField? with
          | some (leftOrigin, leftField), some (rightOrigin, rightField) =>
              pure (.compareFields surfaceOp
                {
                  origin := leftOrigin, field := leftField,
                  projectionRef := leftCategory.map EnumerationProjectionRef.category |>.getD .stored }
                {
                  origin := rightOrigin, field := rightField,
                  projectionRef := rightCategory.map EnumerationProjectionRef.category |>.getD .stored })
          | _, _ => refuse "Having" "field comparison"
      | .value { path, index := none, category }, .string expected
      | .string expected, .value { path, index := none, category } =>
          if isTemporalConstant expected then refuse "Having" "temporal constant" else
          match path.havingField?, surfaceOp with
          | some (origin, field), .equal => pure (.compareStrings .equal
              { origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored } expected)
          | some (origin, field), .notEqual => pure (.compareStrings .notEqual
              { origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored } expected)
          | _, _ => refuse "Having" "String comparison"
      | _, _ => pure (.numeric surfaceOp (← lowerNumericExpr lowerHavingNumericAtom lowerHavingNumericField left)
          (← lowerNumericExpr lowerHavingNumericAtom lowerHavingNumericField right))
  | other => refuse "Having" other.construct

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
        if index.indexKeyFits? matcher spelling != some true then
          refuse "SemanticIndex" "invalid key shape"
        let token ← match index.policy.kind with
          | .number _ => do
              let some decoded := parseNumericFormalRead? (spelling.replace "," ".")
                | refuse "SemanticIndex" "numeric key"
              pure (SemanticIndexKey.number decoded.value)
          | _ => pure (.text spelling)
        pure (SurfaceSemanticIndexKey.literal token (some spelling))
    | .path authored => do
        let some field := authored.toFieldPath? | refuse "SemanticIndex" "key path"
        pure (.field field)
  pure key

def lowerIndexedSource (model : FlatModel) (group : GroupPath)
    (path : Path) (key : IndexKey) : Lowering SurfaceSemanticIndex := do
  let some target := path.toFieldPath? | refuse "SemanticIndex" "target path"
  let declaration ← elaborated "SemanticIndex" (model.resolveFieldDeclarationUnchecked group target)
  let selectedGroup ← elaborated "SemanticIndex" (model.lookupUniqueRepeatablePath declaration.groupPath)
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
  let groups := (model.repeatableScopeForGroupPath targetGroup).filterMap fun level =>
    (model.repeatableGroupAtLevel? level).filter (·.indexField.isSome)
  let some selectedGroup := groups.getLast? | refuse "SemanticIndex" "missing index"
  let some indexId := selectedGroup.indexField | refuse "SemanticIndex" "missing index"
  let index ← elaborated "SemanticIndex" (model.lookupUniqueId indexId)
  pure { target, key := ← lowerIndexKey index key }

/-- One entity-list operand. -/
def lowerEntityOperand (model : FlatModel) (group : GroupPath) :
    Argument → Lowering SurfaceFieldEntityOperand
  | .mk (.constant "RuleGroup") none none => pure (.group (.ruleGroup false))
  | .mk (.entity { path, index := some key, category := none }) none none =>
      if path.toFieldPath?.any (namesField model group) then
        (.indexed ·) <$> lowerIndexedSource model group path key
      else (.keyed ·) <$> lowerKeyedExtent model group path key
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
