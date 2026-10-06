import A12Kernel.Reference.Dm.LowerString
import A12Kernel.Reference.Dm.LowerFlat
import A12Kernel.Reference.Dm.LowerScalarTemporal
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.NumericValidation.EntityComparison
import A12Kernel.Elaboration.FieldFillRule
import A12Kernel.Elaboration.StringContext

/-! # Lowering a rule condition onto the checked validation carriers

A condition whose every leaf has a flat form is elaborated whole by the flat carrier. Otherwise its
connectives are kept and each leaf is offered, in a fixed order, to the carriers that exist for it:
the flat leaf, scalar temporal and selected-token comparisons, repeatable field presence, group presence, the group-list quantifiers, the filled-group
numeric comparison, scalar, then addressed, then over entity lists, the starred filled-group count
against a literal, the field-fill quantifiers (filled-field counts use the shared numeric expression carrier),
typed entity-valued or token-literal value lists, the three checked uniqueness overloads, constructed-Date validity, and named-type validity with the caller’s registry. The first carrier that admits a leaf answers. A leaf none admits is refused with its construct, which is the replay ledger's cluster
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
  | .mk expr none none => some expr
  | _ => none

/-- A group-list operand: a field when the path resolves to one, otherwise a group, starred when any
segment carries the star. -/
private def groupListOperand? (model : FlatModel) (rowGroup : GroupPath) :
    Expr → Option SurfaceGroupListOperand
  | .entity { path, index := none, category := none } =>
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

private def lowerTokenComparisonOperand (model : FlatModel) (rowGroup : GroupPath) :
    Expr → Lowering SurfaceTokenComparisonOperand
  | .string value => pure (.literal value)
  | .call "FirstFilledValue" arguments none none =>
      (.firstFilled ·) <$> lowerEntitySource model rowGroup arguments
  | expression => match expression.fieldEntity? with
      | some field => pure (.field field)
      | none => refuse "TokenComparison" expression.construct

private def lowerFirstFilledComparisonOperand (model : FlatModel) (rowGroup : GroupPath) :
    Expr → Lowering SurfaceFirstFilledComparisonOperand
  | .call "FirstFilledValue" arguments none none =>
      (.firstFilled ·) <$> lowerEntitySource model rowGroup arguments
  | .constant "True" => pure (.boolean true)
  | .constant "False" => pure (.boolean false)
  | expression => match expression.fieldEntity? with
      | some path => pure (.field path)
      | none => (.temporal ·) <$> lowerScalarTemporalExpression model rowGroup expression

/-- The carriers tried for one leaf, in order; the first to admit it answers. -/
private def leafCarriers (model : FlatModel) (rowGroup : GroupPath) (world : World)
    (suppress : Bool) (leaf : Expr) (bindingGroup : GroupPath) :
    List (Lowering (CheckedValidationCondition model)) :=
  let flat := match lowerFlat model rowGroup leaf with
    | some surface => [do
        let checked ← elaborated "Flat" (elaborate model rowGroup surface)
        elaborated "Flat" (CheckedValidationCondition.fromFlat checked)]
    | none => []
  let temporal := match leaf with
    | .compare operator left right =>
        match operator.toSurface?, lowerScalarTemporalExpression model rowGroup left,
            lowerScalarTemporalExpression model rowGroup right with
        | some operator, .ok left, .ok right =>
            match elaborateScalarTemporalComparison model rowGroup operator.toTemporal left right (some bindingGroup) with
            | .error (.nonTemporal _) | .error (.extremum (.firstNotTemporal _ _)) => []
            | result => [do
                let comparison ← elaborated "TemporalComparison" result
                elaborated "TemporalComparison"
                  (CheckedValidationCondition.fromScalarTemporal bindingGroup comparison rowGroup)]
        | _, _, _ => []
    | _ => []
  let stringExpression := match leaf with
    | .compare op left right =>
        let equality := match op with | .eq => some EqualityOp.equal | .ne => some .notEqual | _ => none
        match equality, lowerStringExpr left, lowerStringExpr right with
        | some op, .ok left, .ok right =>
            if isCompoundStringExpression left || isCompoundStringExpression right then [do
              let comparison ← elaborated "StringExpression" (elaborateStringExpressionComparison model rowGroup rowGroup op left right)
              elaborated "StringExpression" (CheckedValidationCondition.fromStringExpression rowGroup comparison)] else []
        | _, _, _ => []
    | _ => []
  let token := match leaf with
    | .compare op left right =>
        let equality := match op with
          | .eq => some EqualityOp.equal
          | .ne => some EqualityOp.notEqual
          | _ => none
        match equality, lowerTokenComparisonOperand model rowGroup left,
            lowerTokenComparisonOperand model rowGroup right with
        | some op, .ok left, .ok right => [do
            let comparison ← elaborated "TokenComparison" (elaborateTokenComparison model rowGroup op left right bindingGroup)
            elaborated "TokenComparison" (CheckedValidationCondition.fromTokenComparison bindingGroup comparison rowGroup)]
        | _, _, _ => []
    | _ => []
  let selected : Expr → Bool
    | .call "FirstFilledValue" _ none none => true
    | _ => false
  let firstFilled := match leaf with
    | .compare op left right =>
        if !selected left && !selected right then [] else
        match op.toSurface?, lowerFirstFilledComparisonOperand model rowGroup left,
            lowerFirstFilledComparisonOperand model rowGroup right with
        | some op, .ok left, .ok right => [do
            let comparison ← elaborated "FirstFilledComparison"
              (elaborateFirstFilledComparison model rowGroup bindingGroup op.toTemporal left right)
            elaborated "FirstFilledComparison"
              (CheckedValidationCondition.fromFirstFilledComparison bindingGroup comparison rowGroup)]
        | _, _, _ => []
    | _ => []
  let validity := match leaf with
    | .call id [.mk (.call "Date" arguments none none) none none] none none =>
        let operation := match id with
          | "Valid" => some ConstructedDateValidityOp.valid
          | "Invalid" => some .invalid
          | _ => none
        match operation with
        | some operation => [do
            let source ← lowerDateComponents model rowGroup arguments
            elaborated id (CheckedValidationCondition.fromConstructedDateValidity
              model rowGroup operation source bindingGroup)]
        | none => []
    | .call id [.mk field none none, .mk (.string name) none none] none none =>
        let operation := match id with
          | "Valid" => some CustomFieldValidityOp.valid
          | "Invalid" => some .invalid
          | _ => none
        match operation, field.fieldEntity? with
        | some operation, some path => [do
            let declaration ← elaborated id (model.resolveFieldDeclarationUnchecked rowGroup path)
            elaborated id (CheckedValidationCondition.fromCustomFieldValidity
              model rowGroup world declaration.id name operation)]
        | _, _ => []
    | _ => []
  let uniqueness := match leaf with
    | .call "FieldValuesNotUnique" arguments none none =>
        let operands := lowerEntitySource model rowGroup arguments
        [do
          let source ← elaborated "FieldValuesNotUnique"
            (elaborateNumberValuesNotUniqueSource model rowGroup (← operands))
          elaborated "FieldValuesNotUnique"
            (CheckedValidationCondition.fromValuesNotUnique rowGroup (.number source)),
         do
          let source ← elaborated "FieldValuesNotUnique"
            (elaborateTokenValuesNotUniqueSource model rowGroup (← operands))
          elaborated "FieldValuesNotUnique"
            (CheckedValidationCondition.fromValuesNotUnique rowGroup (.token source)),
         do
          let source ← elaborated "FieldValuesNotUnique"
            (elaborateTemporalValuesNotUniqueSource model rowGroup (← operands))
          elaborated "FieldValuesNotUnique"
            (CheckedValidationCondition.fromValuesNotUnique rowGroup (.temporal source))]
    | _ => []
  let valueLists := match leaf with
    | .call id arguments (some values) none =>
        match valueListQuantifier? id with
        | none => []
        | some quantifier =>
            let fields := lowerEntitySource model rowGroup arguments
            let literals := values.mapM fun
              | .mk (.string value) none none => some value
              | _ => none
            match literals with
            | some literals => [do
                let source ← elaborated id (elaborateTokenEntityStringLiteralValueListSource model rowGroup
                  { quantifier, fields := ← fields, values := literals })
                elaborated id (CheckedValidationCondition.fromValueList rowGroup (.literals source))]
            | none =>
                let values := lowerEntitySource model rowGroup values
                [do
                  let source ← elaborated id (elaborateNumberEntityValueListSource model rowGroup
                    { quantifier, fields := ← fields, values := ← values })
                  elaborated id (CheckedValidationCondition.fromValueList rowGroup (.number source)),
                 do
                  let source ← elaborated id (elaborateTokenEntityValueListSource model rowGroup
                    { quantifier, fields := ← fields, values := ← values })
                  elaborated id (CheckedValidationCondition.fromValueList rowGroup (.token source))]
    | _ => []
  let fieldFill := match leaf with
    | .call id arguments none none => match fieldFillOp? id with
        | some operator => [do
            let source ← lowerEntitySource model rowGroup arguments
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
          | [.mk operand none none] =>
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
            [elaborated id (CheckedValidationCondition.fromGroupList model rowGroup quantifier operands)]
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
            let atom := lowerCompleteComputationNumericAtom model rowGroup
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
  let pattern := match leaf with
    | .compare op (.value { path, index := none, category := none }) right =>
        match right.patternConstant? with
        | none => []
        | some source =>
          match op, path.toFieldPath? with
          | .patternMatched, some field => [elaborated "PatternMatched"
            (CheckedValidationCondition.fromStringPattern model rowGroup builtinStringPatternCompiler
              { op := .matched, field, source } bindingGroup)]
          | .patternViolated, some field => [elaborated "PatternViolated"
            (CheckedValidationCondition.fromStringPattern model rowGroup builtinStringPatternCompiler
              { op := .violated, field, source } bindingGroup)]
          | _, _ => []
    | _ => []
  flat ++ firstFilled ++ temporal ++ stringExpression ++ token ++ specific ++ groupCount ++ fieldFill ++ pattern ++ valueLists ++ uniqueness ++ validity

/-- The first admitting carrier, or else the refusal of the last, the most general one tried. -/
private def firstAdmitted (construct : String) :
    List (Lowering (CheckedValidationCondition model)) → Lowering (CheckedValidationCondition model)
  | [] => refuse construct
  | attempts =>
      match attempts.find? (·.toOption.isSome) with
      | some admitted => admitted
      | none => match attempts.getLast? with
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
  | none, leaf =>
      let construct := match leaf with
        | .compare _ _ _ => (leaf.leadingCall?.map ("Comparison/" ++ ·)).getD leaf.construct
        | _ => leaf.construct
      firstAdmitted construct ((leafCarriers model rowGroup world suppress leaf bindingGroup).map fun attempt =>
        attempt.bind fun checked => elaborated construct (checked.atBinding bindingGroup))

end A12Kernel.Dm
