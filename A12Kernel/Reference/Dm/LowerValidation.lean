import A12Kernel.Reference.Dm.LowerString
import A12Kernel.Reference.Dm.LowerFlat
import A12Kernel.Elaboration.BoundBooleanComparison
import A12Kernel.Elaboration.BoundScalarMembership
import A12Kernel.Elaboration.BoundTextComparison
import A12Kernel.Reference.Dm.LowerScalarTemporal
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.NumericValidation.EntityComparison
import A12Kernel.Elaboration.FieldFillRule
import A12Kernel.Elaboration.StringContext
import A12Kernel.Reference.Dm.RefusalClass

/-! # Lowering a rule condition onto the checked validation carriers

A condition whose every leaf has a flat form is elaborated whole by the flat carrier. Otherwise its
connectives are kept and each leaf is offered, in a fixed order, to the carriers that exist for it:
the flat leaf, scalar temporal and selected-token comparisons, repeatable field presence, group presence, the group-list quantifiers, the filled-group
numeric comparison, scalar, then addressed, then over entity lists, the starred filled-group count
against a literal, the field-fill quantifiers (filled-field counts use the shared numeric expression carrier),
typed entity-valued or token-literal value lists, the three checked uniqueness overloads, constructed-Date validity, named-type validity with the caller’s registry, and last the Boolean and Confirm comparisons. The first carrier that admits a leaf answers. A leaf none admits is refused with its construct, which is the replay ledger's cluster
key; when an elaborator itself refused, its error is kept as the detail.

Only public elaboration entry points are reached. A construct with a semantic evaluator but no rule
carrier is refused here rather than assembled
by hand, so the refusal measures the missing carrier instead of hiding it.
-/

namespace A12Kernel.Dm

private def presenceOp? : String → Option RepeatableFieldPresenceOperator
  | "FieldFilled" => some .filled
  | "FieldNotFilled" => some .notFilled
  | _ => none

private def groupPresenceOp? : String → Option GroupPresenceOperator
  | "GroupFilled" => some .filled
  | "GroupNotFilled" => some .notFilled
  | _ => none




private def plain : Argument → Option Expr
  | .mk expr none => some expr
  | _ => none

/-- A group-list operand: a field when the path resolves to one, otherwise a group, starred when any
segment carries the star. -/
private def groupListOperand? (model : FlatModel) (rowGroup : GroupPath) :
    Expr → Option SurfaceGroupListOperand
  | expression@(.entity { index := some _, filter := none, .. }) => do
      match ← (lowerEntityOperand model rowGroup (.mk expression none)).toOption with
      | .indexed source .stored => some (.indexed source)
      | .keyed source .stored => some (.keyed source)
      | _ => none
  | .entity { path, index := none, category := none, filter := none } =>
      if path.correlated then none
      else if path.segments.any (·.star) then
        some (.starredGroup { base := path.base, groups := path.starGroups })
      else match path.toFieldPath? with
        | some field =>
            if (model.resolveFieldDeclarationUnchecked rowGroup field).toOption.isSome then
              some (.field field)
            else (path.toGroupPath?).map (.group ∘ .path)
        | none => (path.toGroupPath?).map (.group ∘ .path)
  | .constant "RuleGroup" => some (.group (.ruleGroup false))
  | _ => none

/-- A comparison both of whose sides are numeric operations. -/
def lowerNumericComparison (model : FlatModel) (rowGroup : GroupPath) (op : CompareOp) (left right : Expr) (suppress : Bool) :
    Lowering SurfaceNumericComparison := do
  let some op := op.toNumeric? | refuse "Comparison" "operator"
  pure { op, left := ← lowerNumericExpr lowerValidationNumericAtom (lowerNumericFieldAtom model rowGroup lowerValidationNumericAtom) left
         right := ← lowerNumericExpr lowerValidationNumericAtom (lowerNumericFieldAtom model rowGroup lowerValidationNumericAtom) right
         suppressExactScaleWarning := suppress }

def lowerTokenComparisonOperand (model : FlatModel) (rowGroup : GroupPath)
    (bindingGroup? : Option GroupPath) (expression : Expr) (suppress : Bool := false) :
    Lowering SurfaceTokenComparisonOperand := do
  if let some bindingGroup := bindingGroup? then
    match expression with
    | .entity reference | .value reference => checkReferenceRead model rowGroup bindingGroup reference
    | _ => pure ()
  match expression with
  | .string value => pure (.literal value)
  | .call "FirstFilledValue" arguments none none =>
      (.firstFilled ·) <$> lowerFirstFilledEntitySource model rowGroup arguments bindingGroup? suppress
  | .value { path, index := some key, category := none, filter := none } =>
      (.indexed ·) <$> lowerIndexedSource model rowGroup path key
  | expression => match expression.fieldValue? with
      | some field => pure (.field field)
      | none => refuse "TokenComparison" expression.construct

def lowerFirstFilledComparisonOperand (model : FlatModel) (rowGroup : GroupPath)
    (bindingGroup? : Option GroupPath) (expression : Expr) (suppress : Bool := false) :
    Lowering SurfaceFirstFilledComparisonOperand := do
  if let some bindingGroup := bindingGroup? then
    match expression with
    | .entity reference | .value reference => checkReferenceRead model rowGroup bindingGroup reference
    | _ => pure ()
  match expression with
  | .value { path, index := some key, category := none, filter := none } =>
      (.indexed ·) <$> lowerIndexedSource model rowGroup path key
  | .call "FirstFilledValue" arguments none none =>
      (.firstFilled ·) <$> lowerFirstFilledEntitySource model rowGroup arguments bindingGroup? suppress
  | .constant "True" => pure (.boolean true)
  | .constant "False" => pure (.boolean false)
  | expression => match expression.fieldValue? with
      | some path => pure (.field path)
      | none => (.temporal ·) <$> lowerScalarTemporalExpression model rowGroup expression suppress

/-- The carriers tried for one leaf, in order; the first to admit it answers. -/
private def leafCarriers (model : FlatModel) (rowGroup : GroupPath) (world : World)
    (suppress : Bool) (leaf : Expr) (bindingGroup : GroupPath) :
    List (Lowering (CheckedValidationCondition model)) :=
  let filterBinding? := if leaf.hasHaving then some bindingGroup else none
  let range := match leaf with
    | .compare operator left right =>
        match lowerDateRangeComparison? model rowGroup operator left right with
        | none => []
        | some lowered => [do
            let (operator, source) ← lowered
            let checked ← elaborated "DateRangeComparison"
              (elaborateDateRangePredicate model rowGroup (model.repeatableScopeForGroupPath bindingGroup)
                (model.resolveFieldDeclarationUnchecked rowGroup)
                (fun path => checkFieldValueRead (model.resolveFieldDeclarationUnchecked rowGroup path)
                  (model.ruleGroupRead rowGroup bindingGroup path)) operator source)
            if h : model.validate.isOk = true then
              elaborated "DateRangeComparison" (CheckedValidationCondition.checkCore model bindingGroup
                (.leaf (.iteratedDateRange checked.toValidation)) h rowGroup)
            else refuse "DateRangeComparison" "invalid model"]
    | _ => []
  let flat := match lowerFlat model rowGroup leaf with
    | some surface => [do
        let checked ← elaborated "Flat" (elaborate model rowGroup surface)
        elaborated "Flat" (CheckedValidationCondition.fromFlat checked)]
    | none => []
  let temporal := match leaf with
    | .compare operator left right =>
        match operator.toSurface?, lowerScalarTemporalExpression model rowGroup left suppress,
            lowerScalarTemporalExpression model rowGroup right suppress with
        | some operator, .ok left, .ok right =>
            match elaborateScalarTemporalComparison model rowGroup operator.toTemporal left right (some bindingGroup) with
            | .error (.nonTemporal _) | .error (.extremum (.firstNotTemporal _ _)) => []
            | result => [do
                let comparison ← elaborated "TemporalComparison" result
                elaborated "TemporalComparison"
                  (CheckedValidationCondition.fromScalarTemporal bindingGroup comparison rowGroup)]
        -- A side that is no temporal expression leaves this carrier silent, except for a token
        -- defect, which `firstAdmitted` reports whichever carrier would have typed the text.
        | some _, .error refusal, _ | some _, .ok _, .error refusal =>
            if refusal.kernelClass? == some SyntaxErrorClass.unexpectedToken.code then [.error refusal] else []
        | _, _, _ => []
    | _ => []
  let stringExpression := match leaf with
    | .compare op left right =>
        let equality := match op with | .eq => some EqualityOp.equal | .ne => some .notEqual | _ => none
        match equality, lowerSelectedStringExpr model rowGroup left, lowerSelectedStringExpr model rowGroup right with
        | some op, .ok left, .ok right =>
            if isStringExpressionComparisonOperand left || isStringExpressionComparisonOperand right then [do
              let comparison ← elaborated "StringExpression" (elaborateSelectedStringExpressionComparison model rowGroup bindingGroup op left right)
              elaborated "StringExpression" (CheckedValidationCondition.fromStringExpression bindingGroup comparison rowGroup)] else []
        | _, _, _ => []
    | _ => []
  let selected : Expr → Bool
    | .call "FirstFilledValue" _ none none => true
    | _ => false
  let contextualReadRefusal {α : Type} (first second : Lowering α) :
      List (Lowering (CheckedValidationCondition model)) :=
    if filterBinding?.isNone then [] else
      let ownReadRefusal : Lowering α → Option Refusal
        | .error refusal => if refusal.construct == "Having" then some refusal else none
        | .ok _ => none
      match (ownReadRefusal first).orElse (fun _ => ownReadRefusal second) with
      | some refusal => [.error refusal]
      | none => []
  let token := match leaf with
    | .compare op left right =>
        let equality := match op with
          | .eq => some EqualityOp.equal
          | .ne => some EqualityOp.notEqual
          | _ => none
        match equality, lowerTokenComparisonOperand model rowGroup filterBinding? left suppress,
            lowerTokenComparisonOperand model rowGroup filterBinding? right suppress with
        | some op, .ok left, .ok right => [do
            let comparison ← elaborated "TokenComparison" (elaborateTokenComparison model rowGroup op left right bindingGroup)
            elaborated "TokenComparison" (CheckedValidationCondition.fromTokenComparison bindingGroup comparison rowGroup)]
        | _, first, second =>
            if selected left || selected right then contextualReadRefusal first second else []
    | _ => []
  let firstFilled := match leaf with
    | .compare op left right =>
        let indexed : Expr → Bool
          | .value { index := some _, .. } => true
          | _ => false
        if !selected left && !selected right && !indexed left && !indexed right then [] else
        match op.toSurface?, lowerFirstFilledComparisonOperand model rowGroup filterBinding? left suppress,
            lowerFirstFilledComparisonOperand model rowGroup filterBinding? right suppress with
        | some op, .ok left, .ok right => [do
            let comparison ← elaborated "FirstFilledComparison"
              (elaborateFirstFilledComparison model rowGroup bindingGroup op.toTemporal left right)
            elaborated "FirstFilledComparison"
              (CheckedValidationCondition.fromFirstFilledComparison bindingGroup comparison rowGroup)]
        | _, first, second => contextualReadRefusal first second
    | _ => []
  let validity := match leaf with
    | .call id [.mk (.call "Date" arguments none none) none] none none =>
        let operation := match id with
          | "Valid" => some ConstructedDateValidityOp.valid
          | "Invalid" => some .invalid
          | _ => none
        match operation with
        | some operation => [do
            let source ← lowerScalarDateComponents model rowGroup arguments suppress
            elaborated id (CheckedValidationCondition.fromConstructedDateValidity
              model rowGroup operation source bindingGroup)]
        | none => []
    | .call id [.mk field none, .mk (.string name) none] none none =>
        let operation := match id with
          | "Valid" => some CustomFieldValidityOp.valid
          | "Invalid" => some .invalid
          | _ => none
        match operation, field with
        | some operation, .entity { path, index := some key, category := none, filter := none } => [do
            let source ← lowerIndexedSource model rowGroup path key
            elaborated id (CheckedValidationCondition.fromIndexedCustomFieldValidity
              model rowGroup world source name operation bindingGroup)]
        | _, _ =>
          match operation, field.fieldEntity? with
          | some operation, some path => [do
              let declaration ← elaborated id (model.resolveFieldDeclarationUnchecked rowGroup path)
              elaborated id (CheckedValidationCondition.fromCustomFieldValidity
                model rowGroup world declaration.id name operation bindingGroup)]
          | _, _ => []
    | _ => []
  let uniqueness := match leaf with
    | .call "FieldValuesNotUnique" arguments none none =>
        let operands := lowerEntitySource model rowGroup arguments filterBinding? suppress
        [do
          let source ← elaborated "FieldValuesNotUnique"
            (elaborateNumberValuesNotUniqueSource model rowGroup (← operands)
              (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup))
          elaborated "FieldValuesNotUnique"
            (CheckedValidationCondition.fromValuesNotUnique bindingGroup (.number source) rowGroup),
         do
          let source ← elaborated "FieldValuesNotUnique"
            (elaborateTokenValuesNotUniqueSource model rowGroup (← operands)
              (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup))
          elaborated "FieldValuesNotUnique"
            (CheckedValidationCondition.fromValuesNotUnique bindingGroup (.token source) rowGroup),
         do
          let source ← elaborated "FieldValuesNotUnique"
            (elaborateTemporalValuesNotUniqueSource model rowGroup (← operands)
              (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup))
          elaborated "FieldValuesNotUnique"
            (CheckedValidationCondition.fromValuesNotUnique bindingGroup (.temporal source) rowGroup)]
    | _ => []
  let boundText := match leaf with
    | .compare .. => [do
        let some surface := lowerFlat model rowGroup leaf | refuse leaf.construct "direct text comparison"
        let condition ← elaborated leaf.construct (BoundTextComparison.elaborate model rowGroup bindingGroup surface)
        if hModel : model.validate.isOk = true then
          elaborated leaf.construct (CheckedValidationCondition.checkCore model bindingGroup (.leaf (.flat condition)) hModel rowGroup)
        else refuse leaf.construct "invalid model"]
    | _ => []
  let scalarMembership := match leaf with
    | .call "FieldValueIncludedInValueList" _ none none
    | .call "FieldValueNotIncludedInValueList" _ none none => [do
        let some surface := lowerFlat model rowGroup leaf | refuse leaf.construct "scalar membership operands"
        let condition ← elaborated leaf.construct (BoundScalarMembership.elaborate model rowGroup bindingGroup surface)
        if hModel : model.validate.isOk = true then
          elaborated leaf.construct (CheckedValidationCondition.checkCore model bindingGroup (.leaf (.flat condition)) hModel rowGroup)
        else refuse leaf.construct "invalid model"]
    | _ => []
  let valueLists := match leaf with
    | .call id arguments (some values) none =>
        match valueListQuantifier? id with
        | none => []
        | some quantifier =>
            let fields := lowerEntitySource model rowGroup arguments filterBinding? suppress
            let literals := values.mapM fun
              | .mk (.string value) none => some value
              | _ => none
            match literals with
            | some literals => [do
                let source ← elaborated id (elaborateTokenEntityStringLiteralValueListSource model rowGroup
                  { quantifier, fields := ← fields, values := literals }
                  (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup))
                elaborated id (CheckedValidationCondition.fromValueList bindingGroup (.literals source) rowGroup)]
            | none =>
                let values := lowerEntitySource model rowGroup values filterBinding? suppress
                [do
                  let source ← elaborated id (elaborateNumberEntityValueListSource model rowGroup
                    { quantifier, fields := ← fields, values := ← values }
                    (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup))
                  elaborated id (CheckedValidationCondition.fromValueList bindingGroup (.number source) rowGroup),
                 do
                  let source ← elaborated id (elaborateTokenEntityValueListSource model rowGroup
                    { quantifier, fields := ← fields, values := ← values }
                    (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup))
                  elaborated id (CheckedValidationCondition.fromValueList bindingGroup (.token source) rowGroup)]
    | _ => []
  let fieldFill := match leaf with
    | .call id arguments none none => match fieldFillOp? id with
        | some operator => [do
            let source ← lowerEntitySource model rowGroup arguments filterBinding? suppress
            elaborated id (CheckedValidationCondition.fromFieldFill model rowGroup operator source bindingGroup)]
        | none => []
    | _ => []
  let groupCount := match leaf with
    | .compare op (.call "NumberOfFilledGroups" arguments none none) (.number threshold) => [do
        let some (.ordinary numericOp) := op.toNumeric? | refuse "Comparison" "operator"
        let some threshold := decodeNumber? threshold | refuse "NumberOfFilledGroups" "threshold"
        -- A count compared with a fractional literal is unmeasured; the carrier takes an integral one.
        if threshold.authoredScale != 0 then refuse "NumberOfFilledGroups" "fractional threshold"
        let operands ← arguments.mapM lowerGroupCountOperand
        let checked ← elaborated "NumberOfFilledGroups"
          (elaborateMixedFilledGroupCountComparison model rowGroup operands numericOp threshold.value.num)
        elaborated "NumberOfFilledGroups" (CheckedValidationCondition.fromOrderedNumeric checked)]
    | _ => []
  let specific := match leaf with
    -- One arm for every call: a one-operand group-list quantifier such as `NoGroupFilled(Rows*)`
    -- must reach the group-list carrier, which a separate one-argument arm would shadow.
    | .call id arguments none none =>
        let presence := match arguments with
          | [.mk operand none] =>
              match presenceOp? id, groupPresenceOp? id, operand.fieldEntity?, operand.groupReference? with
              | some op, _, some path, _ =>
                  [elaborated id (CheckedValidationCondition.fromRepeatableFieldPresence model rowGroup op path)]
              | _, some op, _, some group =>
                  [elaborated id (CheckedValidationCondition.fromGroupPresence model rowGroup group op)]
              | _, _, _, _ => []
          | _ => []
        presence ++ match groupQuantifier? id,
            (arguments.mapM plain).bind (·.mapM (groupListOperand? model rowGroup)) with
        | some quantifier, some operands =>
            [elaborated id (CheckedValidationCondition.fromGroupList model rowGroup quantifier operands
              (writtenGroup := bindingGroup) (bindingGroup := bindingGroup))]
        | _, _ => []
    | .compare op left right =>
        -- Parenthesized so the entity-list attempt follows either outcome of scalar lowering: a
        -- star-free aggregate such as `NumberOfDifferentValues(Shell)` lowers to the scalar
        -- surface and must still reach the entity carrier when the scalar ones refuse it.
        (match lowerNumericComparison model rowGroup op left right suppress with
        | .ok surface =>
            -- The addressed carrier first: it reads under the rule's row environment, so a group
            -- count below a repeatable ancestor runs inside an iterating rule, where the scalar
            -- carrier, also admitting it, has no row to read at.
            [do let checked ← elaborated "NumericComparison"
                  (elaborateRepeatableNumericComparison model rowGroup surface)
                elaborated "NumericComparison" (CheckedValidationCondition.fromOrderedNumeric checked),
             do
                let scalar := do
                  let checked ← elaborated "NumericComparison"
                    (elaborateNumericComparison model rowGroup surface)
                  let mixed ← elaborated "NumericComparison"
                    (CheckedValidationCondition.fromNumeric checked)
                  elaborated "NumericComparison" (mixed.atBinding bindingGroup)
                match scalar with
                | .ok checked => pure checked
                | .error refusal =>
                    -- A bound-scope extension contributes successful cases only; rejected shapes
                    -- retain the scalar carrier's diagnostic (CrossRootValidationLocks).
                    match elaborateBoundNumericComparison model bindingGroup surface rowGroup with
                    | .ok checked =>
                        elaborated "NumericComparison"
                          (CheckedValidationCondition.fromOrderedNumeric checked rowGroup)
                    | .error _ => .error refusal]
        | .error refusal => [.error refusal])
      -- A comparison reading no entity list is not offered to the entity carrier, so the ordinary
      -- numeric carriers' own refusal is the one reported.
      ++ (match (do
            let some numericOp := op.toNumeric? | refuse "Comparison" "operator"
            let atom := fun expression => lowerCompleteComputationNumericAtom model rowGroup expression filterBinding? suppress
            match elaborateEntityNumericComparison model rowGroup numericOp
                (← lowerNumericExpr atom (lowerNumericFieldAtom model rowGroup atom) left) (← lowerNumericExpr atom (lowerNumericFieldAtom model rowGroup atom) right) suppress bindingGroup with
            | .error .readsNoList => pure none
            | result => do
                let checked ← elaborated "EntityComparison" result
                some <$> elaborated "EntityComparison" (CheckedValidationCondition.fromOrderedNumeric checked rowGroup)
          : Lowering (Option (CheckedValidationCondition model))) with
        | .ok none => []
        | .ok (some checked) => [pure checked]
        | .error refusal => [.error refusal])
    | _ => []
  let lowerOverlap (construct : String)
      (result : Except ValidationConditionAssemblyError (CheckedValidationCondition model))
      (yearless : Unit → Except ValidationConditionAssemblyError (CheckedValidationCondition model)) :=
    -- Both profile certificates enforce the complete admission gates; keep the exact route's
    -- refusal when neither applies, as the computation reader does (spec/07 §3).
    let result : Except ValidationConditionAssemblyError (CheckedValidationCondition model) := match result with
      | .ok checked => .ok checked
      | .error error => match yearless () with
          | .ok checked => .ok checked
          | .error _ => .error error
    result.mapError fun error => {
      construct
      detail := (match error with
        | .iteratedDateRange cause => cause.diagnostic?
        | _ => none).map KernelStaticDiagnostic.kernelCode |>.getD (oneLine ((repr error).pretty 100000)) }
  let overlap := match leaf with
    | .call "DateRangesOverlap" arguments none none => [do
        let source ← lowerEntitySource model rowGroup arguments filterBinding? suppress
        lowerOverlap "DateRangesOverlap"
          (CheckedValidationCondition.fromIteratedDateRangeOverlap model rowGroup source rowGroup (some bindingGroup))
          (fun _ => CheckedValidationCondition.fromIteratedYearlessDateRangeOverlap model rowGroup source rowGroup (some bindingGroup))]
    | .call "AtLeastOneDateRangeOverlaps" [scalar] (some values) none => [do
        let source := { scalar := ← lowerEntityOperand model rowGroup scalar (suppress := suppress)
                        list := ← lowerEntitySource model rowGroup values filterBinding? suppress }
        lowerOverlap "AtLeastOneDateRangeOverlaps"
          (CheckedValidationCondition.fromIteratedDateRangePluralOverlap model rowGroup source rowGroup (some bindingGroup))
          (fun _ => CheckedValidationCondition.fromIteratedYearlessDateRangePluralOverlap model rowGroup source rowGroup (some bindingGroup))]
    | _ => []
  let pattern := match leaf with
    | .compare op (.value { path, index, category := none, filter := none }) right =>
        let operation := match op with
          | .patternMatched => some StringPatternOp.matched
          | .patternViolated => some .violated
          | _ => none
        match operation, right.patternConstant? with
        | some op, some source =>
          let construct := match op with | .matched => "PatternMatched" | .violated => "PatternViolated"
          match index with
          | some key => [do
              let field ← lowerIndexedSource model rowGroup path key
              elaborated construct (CheckedValidationCondition.fromIndexedStringPattern model rowGroup
                builtinStringPatternCompiler { op, field, source } bindingGroup)]
          | none => match path.toFieldPath? with
            | some field => [elaborated construct (CheckedValidationCondition.fromStringPattern model rowGroup
                builtinStringPatternCompiler { op, field, source } bindingGroup)]
            | none => []
        | _, _ => []
    | _ => []
  -- Tried last, so that a refusal of the pair or literal arm is the one reported for a comparison naming
  -- a Boolean or Confirm field, instead of a numeric carrier's refusal of a kind it never owned.
  let booleanComparison := match leaf, lowerFlat model rowGroup leaf with
    | .compare .., some surface =>
        if BoundBooleanComparison.readsBooleanField model rowGroup surface then [do
          let condition ← elaborated "BooleanComparison"
            (BoundBooleanComparison.elaborate model rowGroup bindingGroup surface)
          if hModel : model.validate.isOk = true then
            elaborated "BooleanComparison"
              (CheckedValidationCondition.checkCore model bindingGroup (.leaf (.flat condition)) hModel rowGroup)
          else refuse "BooleanComparison" "invalid model"] else []
    | _, _ => []
  flat ++ boundText ++ range ++ firstFilled ++ temporal ++ stringExpression ++ token ++ specific ++ groupCount ++ fieldFill ++ pattern ++ scalarMembership ++ valueLists ++ uniqueness ++ validity ++ overlap ++ booleanComparison

/-- The first admitting carrier, or else the refusal of the last, the most general one tried. -/
private def firstAdmitted (construct : String) :
    List (Lowering (CheckedValidationCondition model)) → Lowering (CheckedValidationCondition model)
  | [] => refuse construct
  | attempts =>
      match attempts.find? (·.toOption.isSome) with
      | some admitted => admitted
      | none =>
          -- The Kernel parses before it types, so a token defect any carrier finds is the text's
          -- answer whichever carrier would have typed it (spec/12 §3); otherwise the last carrier's.
          let token? := attempts.find? fun
            | .error refusal => refusal.kernelClass? == some SyntaxErrorClass.unexpectedToken.code
            | .ok _ => false
          match token?.orElse fun _ => attempts.getLast? with
          | some (.error refusal) => .error { refusal with construct }
          | _ => refuse construct

/-- The first comparison whose sides' decimal places the exact-scale gate refuses, unless the
preamble suppresses it. The flat carrier has no scale gate of its own, so the gate runs here over
every comparison before any carrier admits one. -/
private partial def scaleRefusal? (model : FlatModel) (rowGroup : GroupPath) (suppress : Bool) :
    Expr → Option Refusal
  | .parens body => scaleRefusal? model rowGroup suppress body
  | .logic _ parts => parts.findSome? (scaleRefusal? model rowGroup suppress)
  | .compare op left right =>
      match lowerNumericComparison model rowGroup op left right suppress with
      | .ok surface => match elaborateNumericComparison model rowGroup surface with
          | .error error@(.exactScaleMismatch _ _) =>
              some { construct := "Comparison", detail := oneLine (repr error).pretty }
          | _ => none
      | .error _ => none
  | _ => none

private def lowerIndexedPresence (model : FlatModel) (rowGroup bindingGroup : GroupPath)
    (operator : RepeatableFieldPresenceOperator) (path : Path) (key : IndexKey) :
    Lowering (CheckedValidationCondition model) := do
  let source ← lowerIndexedSource model rowGroup path key
  -- The selection's group and a row-field key bind at the error field's rows, as the list route
  -- binds them ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04), rows s6–s8, d6).
  let checked ← elaborated "SemanticIndex" (elaborateSemanticIndexSource model rowGroup source
    (some (model.repeatableScopeForGroupPath bindingGroup)))
  elaborated "SemanticIndex" (CheckedValidationCondition.checkCore model bindingGroup
    (.leaf (.indexedFieldPresence operator checked)) checked.modelWellFormed rowGroup)

private def lowerKeyedGroupPresence (model : FlatModel) (rowGroup bindingGroup : GroupPath)
    (operator : GroupPresenceOperator) (argument : Argument) : Lowering (CheckedValidationCondition model) := do
  let .keyed source .stored ← lowerEntityOperand model rowGroup argument | refuse "SemanticIndex" "group operand"
  let checked ← elaborated "SemanticIndex" (elaborateKeyedEntityExtent model rowGroup source)
  if !checked.isGroup || checked.isStarredGroup then refuse "SemanticIndex" "unstarred group operand"
  elaborated "SemanticIndex" (CheckedValidationCondition.checkCore model bindingGroup
    (.leaf (.keyedGroupPresence operator checked)) checked.selection.indexSource.modelWellFormed rowGroup)

/-- Lower a rule condition at its rule group. `suppress` is the `@SuppressWarning` preamble. -/
partial def lowerCondition (model : FlatModel) (rowGroup : GroupPath) (suppress : Bool) (condition : Expr)
    (world : World := { now := { epochMillis := 0 } })
    (bindingGroup : GroupPath := rowGroup) :
    Lowering (CheckedValidationCondition model) :=
  match scaleRefusal? model rowGroup suppress condition with
  | some refusal => .error refusal
  | none =>
  let whole := (lowerFlat model rowGroup condition).bind fun surface =>
    (elaborate model rowGroup surface).toOption.bind fun checked =>
      ((CheckedValidationCondition.fromFlat checked).bind (·.atBinding bindingGroup)).toOption
  match whole, condition with
  | some checked, _ => pure checked
  | none, .call "RepetitionNotUnique" arguments none scope => do
      let keys ← arguments.mapM fun
        | .mk expression none => match expression.fieldEntity? with
          | some field => pure field
          | none => refuse "RepetitionNotUnique" "direct key required"
        | _ => refuse "RepetitionNotUnique" "key argument"
      let first :: rest := keys | refuse "RepetitionNotUnique" "empty key list"
      let reference ← scope.mapM fun entity =>
        match (Expr.entity entity).groupReference? with
        | some group => pure group
        | none => refuse "RepetitionNotUnique" "scope reference"
      elaborated "RepetitionNotUnique"
        (CheckedValidationCondition.fromRepetitionNotUnique model rowGroup {
          firstKey := first, restKeys := rest
          scope := reference.map SurfaceRepetitionNotUniqueScope.from |>.getD .default }
          bindingGroup (bindingGroup := bindingGroup))
  | none, .call "FieldFilled" [.mk (.entity { path, index := some key, category := none, filter := none }) none] none none =>
      lowerIndexedPresence model rowGroup bindingGroup .filled path key
  | none, .call "FieldNotFilled" [.mk (.entity { path, index := some key, category := none, filter := none }) none] none none =>
      lowerIndexedPresence model rowGroup bindingGroup .notFilled path key
  | none, .call "GroupFilled" [argument@(.mk (.entity { index := some _, filter := none, .. }) none)] none none =>
      lowerKeyedGroupPresence model rowGroup bindingGroup .filled argument
  | none, .call "GroupNotFilled" [argument@(.mk (.entity { index := some _, filter := none, .. }) none)] none none =>
      lowerKeyedGroupPresence model rowGroup bindingGroup .notFilled argument
  | none, .custom name quoted => do
      let spelling := if quoted then CustomConditionNameSpelling.quoted name else .unquoted name
      let some checkedName := checkCustomConditionName (fun _ => false) spelling
        | refuse "CustomCondition" "invalid name"
      if h : model.validate.isOk = true then
        elaborated "CustomCondition" (CheckedValidationCondition.checkCore model bindingGroup
          (.leaf (.customCondition checkedName)) h rowGroup)
      else refuse "CustomCondition" "invalid model"
  | none, .parens body => lowerCondition model rowGroup suppress body world bindingGroup
  | none, .logic op (first :: rest) => do
      let join := match op with
        | .and => CheckedValidationCondition.and
        | .or => CheckedValidationCondition.or
      let mut result ← lowerCondition model rowGroup suppress first world bindingGroup
      for part in rest do
        result ← elaborated "Connective" (join result (← lowerCondition model rowGroup suppress part world bindingGroup))
      pure result
  | none, leaf => do
      let construct := match leaf with
        | .compare _ _ _ => (leaf.leadingCall?.map ("Comparison/" ++ ·)).getD leaf.construct
        | _ => leaf.construct
      -- A field-fill predicate reads one field, and a second operand draws the arity class ahead of
      -- the slot's gates (spec/02; static-legality sweep row `P30`).
      if let .call id (_ :: _ :: _) none none := leaf then
        if id == "FieldFilled" || id == "FieldNotFilled" then
          refuse construct KernelStaticDiagnostic.paramSizeInvalid1.kernelCode
      firstAdmitted construct ((leafCarriers model rowGroup world suppress leaf bindingGroup).map fun attempt =>
        attempt.bind fun checked => elaborated construct (checked.atBinding bindingGroup))

end A12Kernel.Dm
