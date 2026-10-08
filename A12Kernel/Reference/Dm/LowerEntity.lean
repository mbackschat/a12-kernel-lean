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


private def presencePolarity? : String → Option HavingPresencePolarity
  | "FieldFilled" => some .filled
  | "FieldNotFilled" => some .notFilled
  | _ => none

private def lowerHavingGroupReference : Argument → Lowering (HavingOrigin × SurfaceGroupReference)
  | .mk (.entity { path, index := none, category := none }) none none =>
      match path.havingGroup? with
      | some reference => pure reference
      | none => refuse "Having" "group path"
  | .mk (.constant "RuleGroup") none none => pure (.inner, .ruleGroup false)
  | _ => refuse "Having" "group operand"

private def havingMember? : Expr → Option SurfaceHavingDirectFieldOperand
  | .value { path, index := none, category } => do
      let (origin, field) ← path.havingField?
      pure { origin, field, form := category.map FieldEntityReadForm.projected |>.getD .stored }
  | _ => none



private def lowerHavingNumericAtom : Expr → Lowering SurfaceHavingNumericAtom :=
  lowerHavingNumericAtomWith (lowerHavingTemporalExpression true)

private def lowerHavingNumericField (source : Expr) : Lowering SurfaceHavingNumericAtom := do
  let reference ← numericFieldFormReference source
  lowerHavingNumericAtom (.value reference)


private inductive HavingOperandClass where
  | number | temporal | text | boolean | dateRange | unsupported
  deriving DecidableEq

private def havingDeclarationClass (declaration : FlatFieldDecl) : HavingOperandClass :=
  match declaration.policy.kind with
  | .number _ => .number
  | .temporal _ _ => .temporal
  | .string | .enumeration => .text
  | .boolean => .boolean
  | .dateRange => .dateRange
  | .confirm => .unsupported

/-- Dispatch reads the leading expanded declaration; checked elaboration still owns shape,
whole-list agreement and scope (spec/04 extrema; spec/07 FirstFilledValue). -/
private partial def havingOperandClass? (typing : Option (FlatModel × GroupPath)) : Expr → Option HavingOperandClass
  | .constant "RuleGroup" => do
      let (model, group) ← typing
      havingDeclarationClass <$> (model.groupSubtreeFields group).head?
  | .entity { path, .. } | .value { path, .. } => do
      let (model, group) ← typing
      let path : Path := { path with
        correlated := false
        segments := path.segments.map fun (segment : Segment) => { segment with star := false } }
      let field ← path.toFieldPath?
      match (model.resolveFieldDeclarationUnchecked group field).toOption with
      | some declaration => some (havingDeclarationClass declaration)
      | none => do
          let path ← model.groupNamedBy? group field
          havingDeclarationClass <$> (model.groupSubtreeFields path).head?
  | .arith .add left right =>
      match havingOperandClass? typing left, havingOperandClass? typing right with
      | some .text, _ | _, some .text => some .text
      | some .number, some .number => some .number
      | _, _ => none
  | .braces source => havingOperandClass? typing source
  | .number _ => some .number
  | .string value => some (if isTemporalConstant value then .temporal else .text)
  | .constant "True" | .constant "False" => some .boolean
  | .constant "Now" | .constant "Today" => some .temporal
  | expression@(.call name arguments none none) =>
      if ["FirstFilledValue", "MinValue", "MaxValue", "Min", "Max"].contains name then
        arguments.findSome? fun | .mk source none none => havingOperandClass? typing source | _ => none
      else if ["FieldValueAsString", "RangeAsString"].contains name then some .text
      else if ["StartOfDateRange", "EndOfDateRange"].contains name || expression.havingTemporalConstructor then
        some .temporal else none
  | _ => none

private def temporalHavingSelection (typing : Option (FlatModel × GroupPath)) (arguments : List Argument) : Bool :=
  (arguments.findSome? fun | .mk source none none => havingOperandClass? typing source | _ => none) == some .temporal

private def selectedNonNumeric (typing : Option (FlatModel × GroupPath)) : Expr → Bool
  | .braces source => selectedNonNumeric typing source
  | expression@(.call "FirstFilledValue" _ none none) =>
      (havingOperandClass? typing expression).any fun kind => kind != .number && kind != .temporal
  | _ => false

private def lowerHavingSelectedOperand : Expr → Lowering SurfaceHavingSelectedOperand
  | .braces source => lowerHavingSelectedOperand source
  | .call "FirstFilledValue" arguments none none => .firstFilled <$> lowerHavingEntitySource arguments
  | .constant "True" => pure (.boolean true)
  | .constant "False" => pure (.boolean false)
  | .string value => if isTemporalConstant value then refuse "Having" "temporal token literal" else pure (.text value)
  | .value { path, index := none, category } => do
      let some (origin, field) := path.havingField? | refuse "Having" "selected comparison field"
      pure (.field { origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored })
  | _ => refuse "Having" "selected comparison operand"

private def lowerHavingStringExpression : Expr → Lowering (StringExpr SurfaceHavingSelectedOperand String) :=
  lowerStringExprWith (fun reference => do
    if reference.index.isSome then refuse "Having" "indexed String source"
    let some (origin, field) := reference.path.havingField? | refuse "Having" "String source path"
    pure (.field { origin, field })) lowerHavingSelectedOperand

private def lowerHavingRangeReference : Expr → Lowering SurfaceHavingPresenceRef
  | .entity { path, index := none, category := none } =>
      match path.havingField? with
      | some (origin, field) => pure { origin, field }
      | none => refuse "Having" "DateRange field path"
  | _ => refuse "Having" "direct DateRange entity"

private def lowerHavingRangeOperand : Expr → Lowering SurfaceHavingDateRangeOperand
  | .braces source => lowerHavingRangeOperand source
  | .call "DateRange" [.mk start none none, .mk finish none none] none none =>
      return .constructed (← lowerHavingRangeReference start) (← lowerHavingRangeReference finish)
  | .value { path, index := none, category := none } =>
      match path.havingField? with
      | some (origin, field) => pure (.stored { origin, field })
      | none => refuse "Having" "DateRange value path"
  | _ => refuse "Having" "DateRange comparison operand"

private def isRangeConstruction : Expr → Bool
  | .braces source => isRangeConstruction source
  | .call "DateRange" _ _ _ => true
  | _ => false

/-- A filter comparison uses the shared numeric expression reader over correlated field and
repetition atoms. Typed field pairs, Boolean/text literals and presence retain their operand domains. -/
partial def lowerHaving (expression : Expr) (typing : Option (FlatModel × GroupPath) := none) :
    Lowering SurfaceCorrelatedHaving := match expression with
  | .parens body => lowerHaving body typing
  | .logic op (first :: rest) => do
      let join := match op with | .and => SurfaceCorrelatedHaving.and | .or => SurfaceCorrelatedHaving.or
      let mut result ← lowerHaving first typing
      for part in rest do result := join result (← lowerHaving part typing)
      pure result
  | .call id arguments (some members) none => do
      if id == "AtLeastOneDateRangeOverlaps" then
        let [.mk scalar none none] := arguments | refuse "Having" "DateRange scalar"
        return .dateRange (.overlap (some (← lowerHavingRangeReference scalar)) (← lowerHavingEntitySource members))
      let some operator := valueListQuantifier? id | refuse "Having" id
      let plain (arguments : List Argument) := arguments.mapM fun
        | .mk expression none none => pure expression
        | _ => refuse "Having" "direct membership fields"
      let subjects ← lowerHavingEntitySource arguments
      let values ← plain members
      if let some literals := values.mapM (fun | .string value => some value | _ => none) then
        return .literalList operator subjects literals
      pure (.fieldMembership (.quantified operator) subjects (← lowerHavingEntitySource members))
  | .call id arguments none none => do
      if id == "DateRangesOverlap" then
        return .dateRange (.overlap none (← lowerHavingEntitySource arguments))
      if id == "FieldValuesNotUnique" then
        return .uniqueness (← lowerHavingEntitySource arguments)
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
            { first := .entity { origin, field, form := category.map FieldEntityReadForm.projected |>.getD .stored }, rest := [] }
            { first := .entity first, rest := rest.map .entity }
        if let some strings := values.mapM (fun | .string value => some value | _ => none) then
          return .literalMembership operator reference (.inr strings)
        let integers ← values.mapM fun expression => do
          let .number text := expression | refuse "Having" "integer member"
          let some literal := decodeNumber? text | refuse "Having" "integer member"
          if literal.authoredScale == 0 then pure literal.value.num else refuse "Having" "integer member"
        return .literalMembership operator reference (.inl integers)
      if id == "Valid" || id == "Invalid" then
        match arguments with
        | [.mk (.entity { path, index := none, category := none }) none none, .mk (.string name) none none] =>
            let some (origin, field) := path.havingField? | refuse "Having" "type-validity path"
            return .typeValidity (if id == "Valid" then .valid else .invalid) { origin, field } name
        | [.mk (.call "Date" arguments none none) none none] =>
            return .dateValidity (if id == "Valid" then .valid else .invalid) (← lowerHavingDateComponents arguments)
        | _ => refuse "Having" "type-validity shape"
      if id == "GroupFilled" || id == "GroupNotFilled" then
        let [argument] := arguments | refuse "Having" "group-presence arity"
        let (origin, reference) ← lowerHavingGroupReference argument
        return .groupPresence (if id == "GroupFilled" then .filled else .notFilled) origin reference
      if let some operator := groupQuantifier? id then
        let source ← lowerHavingEntitySource arguments
        return .groupFill operator source.first source.rest
      if let some polarity := presencePolarity? id then
        match arguments with
        | [.mk (.entity { path, index := none, category := none }) none none] =>
            let some (origin, field) := path.havingField? | refuse "Having" "presence path"
            return .presence polarity { origin, field }
        | _ => refuse "Having" "presence arity"
      let some operator := fieldFillOp? id | refuse "Having" id
      pure (.fieldFill operator (← lowerHavingEntitySource arguments))
  | .compare op@(.tolerance _) left right => do
      let some (.tolerance range) := op.toNumeric? | refuse "Having" "tolerance band"
      pure (.tolerance range
        (← lowerNumericExpr lowerHavingNumericAtom lowerHavingNumericField left)
        (← lowerNumericExpr lowerHavingNumericAtom lowerHavingNumericField right))
  | .compare op left right => do
      if op == .patternMatched || op == .patternViolated then
        let .value { path, index := none, category := none } := left | refuse "Having" "pattern field"
        let some (origin, field) := path.havingField? | refuse "Having" "pattern field path"
        let some source := right.patternConstant? | refuse "Having" "pattern constant"
        return .stringPattern (if op == .patternMatched then .matched else .violated) { origin, field } source
      let some surfaceOp := op.toSurface? | refuse "Having" "operator"
      if isRangeConstruction left || isRangeConstruction right then
        return .dateRange (.compare surfaceOp (← lowerHavingRangeOperand left) (← lowerHavingRangeOperand right))
      if left.havingTemporalConstructor (temporalHavingSelection typing) ||
          right.havingTemporalConstructor (temporalHavingSelection typing) then
        return .compareTemporalExpression surfaceOp
          (← lowerHavingTemporalExpression false left) (← lowerHavingTemporalExpression false right)
      let stringComparison := havingOperandClass? typing left == some .text ||
        havingOperandClass? typing right == some .text
      match lowerHavingStringExpression left, lowerHavingStringExpression right with
      | .ok left, .ok right =>
          if stringComparison && (isCompoundStringExpression left || isCompoundStringExpression right) then
            return .compareStringExpression surfaceOp left right
      | _, _ => pure ()
      if selectedNonNumeric typing left || selectedNonNumeric typing right then
        return .compareSelected surfaceOp (← lowerHavingSelectedOperand left) (← lowerHavingSelectedOperand right)
      let rec temporal : Expr → Option SurfaceHavingTemporalOperand
        | .value { path, index := none, category := none } => do
            let (origin, field) ← path.havingField?
            pure (.field { origin, field })
        | .braces source => .grouped <$> temporal source
        | expression =>
            match expression with
            | .string text => match dateTimeConstant? text, timeConstant? text with
                | some value, _ => some (.dateTimeLiteral value)
                | _, some value => some (.timeLiteral value)
                | _, _ => .constant <$> dateDifferenceOperandWith? (fun _ => (none : Option Empty)) expression
            | _ => .constant <$> dateDifferenceOperandWith? (fun _ => (none : Option Empty)) expression
      if let (some l, some r) := (temporal left, temporal right) then
        match l, r with
        | .field _, .field _ => pure ()
        | _, _ => return .compareTemporal surfaceOp l r
      match left, right with
      | .value { path, index := none, category }, .constant literal
      | .constant literal, .value { path, index := none, category } =>
          match path.havingField?, literal with
          | some (origin, field), "True" =>
              pure (.compareBoolean surfaceOp
                { origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored } true)
          | some (origin, field), "False" =>
              pure (.compareBoolean surfaceOp
                { origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored } false)
          | _, _ => refuse "Having" "Boolean comparison"
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
          match path.havingField? with
          | some (origin, field) => pure (.compareStrings surfaceOp
              { origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored } expected)
          | none => refuse "Having" "String comparison"
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
        | some body => pure (.starHaving star (← lowerHaving body (some (model, group))))
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
        | some body => pure (.starHaving star projection (← lowerHaving body (some (model, group))))
      else
        let some field := path.toFieldPath? | refuse "EntityOperand" "path"
        if filter.isSome then refuse "EntityOperand" "filter on an unstarred operand"
        pure (.field (match category with | some name => .category field name | none => .direct field))
  | _ => do
      let _ ← lowerEntityOperand model group argument
      refuse "EntityOperand" "group in a value count"

/-- An Enumeration `FirstFilledValue` source retains selected identity, direct/category projection,
and each ordinary star’s own filter. -/
def lowerEnumerationFirstFilledSource (model : FlatModel) (group : GroupPath) (arguments : List Argument) :
    Lowering SurfaceEnumerationFirstFilledSource := do
  let operand (argument : Argument) : Lowering SurfaceEnumerationFirstFilledOperand := do
    if let .mk (.entity { index := some _, .. }) none none := argument then
      match ← lowerEntityOperand model group argument with
      | .indexed source => return .indexed source
      | .keyed source => return .keyed source
      | _ => refuse "EntityOperand" "indexed source"
    match ← lowerProjectedTokenOperand model group argument with
    | .field source => pure (.field source)
    | .star source projection => pure (.star source projection)
    | .starHaving source projection having => pure (.star source projection (some having))
  let first :: rest ← arguments.mapM operand | refuse "EntityOperand" "empty"
  pure { first, rest }

/-- `SumOfProducts(left, right)` retains each starred field's key and optional filter for checked admission. -/
def lowerProductAggregate (model : FlatModel) (group : GroupPath) (arguments : List Argument) : Lowering SurfaceNumericProductAggregate := do
  let [.mk (.entity { path := leftPath, index := leftIndex, category := none }) none leftFilter,
      .mk (.entity { path := rightPath, index := rightIndex, category := none }) none rightFilter] := arguments
    | refuse "SumOfProducts" "operands"
  let some left := leftPath.toStarFieldPath? | refuse "SumOfProducts" "operand"
  let some right := rightPath.toStarFieldPath? | refuse "SumOfProducts" "operand"
  pure { left, right, leftHaving := ← leftFilter.mapM (fun body => lowerHaving body (some (model, group)))
         rightHaving := ← rightFilter.mapM (fun body => lowerHaving body (some (model, group)))
         leftKey := ← leftIndex.mapM (fun key => (·.key) <$> lowerKeyedExtent model group leftPath key)
         rightKey := ← rightIndex.mapM (fun key => (·.key) <$> lowerKeyedExtent model group rightPath key) }

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

/-- The common authored source dispatch for fixed and row first-filled targets. -/
def lowerFirstFilledSource (model : FlatModel) (group : GroupPath) (arguments : List Argument) :
    Lowering SurfaceFirstFilledSource :=
  match arguments with
  | [.mk (.entity { path, index := none, category := none }) none none] =>
      match path.segments.any (·.star), path.toStarFieldPath? with
      | true, some star => pure (.star star)
      | _, _ => (.list ·) <$> lowerEntitySource model group arguments
  | _ => (.list ·) <$> lowerEntitySource model group arguments

end A12Kernel.Dm
