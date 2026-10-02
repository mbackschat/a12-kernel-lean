import A12Kernel.Reference.Dm.LowerFlat
import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.NumericValidation.EntityComparison
import A12Kernel.Elaboration.FieldFillRule

/-! # Lowering a rule condition onto the checked validation carriers

A condition whose every leaf has a flat form is elaborated whole by the flat carrier. Otherwise its
connectives are kept and each leaf is offered, in a fixed order, to the carriers that exist for it:
the flat leaf, repeatable field presence, group presence, the group-list quantifiers, the filled-group
numeric comparison, scalar, then addressed, then over entity lists, the starred filled-group count
against a literal, and the field-fill quantifiers and `NumberOfFilledFields` over an entity list. The first carrier that admits a
leaf answers. A leaf none admits is refused with its construct, which is the replay ledger's cluster
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

private def groupQuantifier? : String → Option GroupFillQuantifier
  | "AllGroupsFilled" => some .allGroupsFilled
  | "NoGroupFilled" => some .noGroupFilled
  | "AtLeastOneGroupFilled" => some .atLeastOneGroupFilled
  | "NotAllGroupsFilled" => some .notAllGroupsFilled
  | "GroupsNotCollectivelyFilled" => some .groupsNotCollectivelyFilled
  | _ => none

private def fieldFillOp? : String → Option FieldFillQuantifier
  | "AllFieldsFilled" => some .allFieldsFilled
  | "NoFieldFilled" => some .noFieldFilled
  | "AtLeastOneFieldFilled" => some .atLeastOneFieldFilled
  | "MoreThanOneFieldFilled" => some .moreThanOneFieldFilled
  | "NotAllFieldsFilled" => some .notAllFieldsFilled
  | "NotExactlyOneFieldFilled" => some .notExactlyOneFieldFilled
  | "FieldsNotCollectivelyFilled" => some .fieldsNotCollectivelyFilled
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
def lowerNumericComparison (op : CompareOp) (left right : Expr) (suppress : Bool) :
    Lowering SurfaceNumericComparison := do
  let some op := op.toNumeric? | refuse "Comparison" "operator"
  pure { op, left := ← lowerNumericExpr lowerValidationNumericAtom left
         right := ← lowerNumericExpr lowerValidationNumericAtom right
         suppressExactScaleWarning := suppress }

/-- The carriers tried for one leaf, in order; the first to admit it answers. -/
private def leafCarriers (model : FlatModel) (rowGroup : GroupPath) (suppress : Bool) (leaf : Expr) :
    List (Lowering (CheckedValidationCondition model)) :=
  let flat := match lowerFlat model rowGroup leaf with
    | some surface => [do
        let checked ← elaborated "Flat" (elaborate model rowGroup surface)
        elaborated "Flat" (CheckedValidationCondition.fromFlat checked)]
    | none => []
  let fieldFill := match leaf with
    | .call id arguments none none => match fieldFillOp? id with
        | some operator => [do
            let source ← lowerEntitySource model rowGroup arguments
            elaborated id (CheckedValidationCondition.fromFieldFill model rowGroup operator source)]
        | none => []
    | .compare op (.call "NumberOfFilledFields" arguments none none) (.number threshold) =>
        [do
          let some (.ordinary numericOp) := op.toNumeric? | refuse "Comparison" "operator"
          let some threshold := decodeNumber? threshold | refuse "NumberOfFilledFields" "threshold"
          let source ← lowerEntitySource model rowGroup arguments
          let checked ← elaborated "NumberOfFilledFields"
            (elaborateFilledFieldCountComparison model rowGroup source numericOp threshold.value)
          elaborated "NumberOfFilledFields" (CheckedValidationCondition.fromOrderedNumeric checked)]
    | _ => []
  let groupCount := match leaf with
    | .compare op (.call "NumberOfFilledGroups" arguments none none) (.number threshold) => [do
        let some (.ordinary numericOp) := op.toNumeric? | refuse "Comparison" "operator"
        let some threshold := decodeNumber? threshold | refuse "NumberOfFilledGroups" "threshold"
        let operands ← arguments.mapM lowerGroupCountOperand
        let checked ← elaborated "NumberOfFilledGroups"
          (elaborateMixedFilledGroupCountComparison model rowGroup operands numericOp threshold.value)
        elaborated "NumberOfFilledGroups" (CheckedValidationCondition.fromOrderedNumeric checked)]
    | _ => []
  let specific := match leaf with
    | .call id [.mk operand none none] none none =>
        match presenceOp? id, groupPresenceOp? id, operand.fieldEntity?, operand.groupReference? with
        | some op, _, some path, _ =>
            [elaborated id (CheckedValidationCondition.fromRepeatableFieldPresence model rowGroup op path)]
        | _, some op, _, some group =>
            [elaborated id (CheckedValidationCondition.fromGroupPresence model rowGroup group op)]
        | _, _, _, _ => []
    | .call id arguments none none =>
        match groupQuantifier? id, (arguments.mapM plain).bind (·.mapM (groupListOperand? model rowGroup)) with
        | some quantifier, some operands =>
            [elaborated id (CheckedValidationCondition.fromGroupList model rowGroup quantifier operands)]
        | _, _ => []
    | .compare op left right =>
        match lowerNumericComparison op left right suppress with
        | .ok surface =>
            [do let checked ← elaborated "NumericComparison"
                  (elaborateNumericComparison model rowGroup surface)
                elaborated "NumericComparison" (CheckedValidationCondition.fromNumeric checked),
             do let checked ← elaborated "NumericComparison"
                  (elaborateRepeatableNumericComparison model rowGroup surface)
                elaborated "NumericComparison" (CheckedValidationCondition.fromOrderedNumeric checked)]
        | .error refusal => [.error refusal]
      ++ [do
        let some numericOp := op.toNumeric? | refuse "Comparison" "operator"
        let atom := lowerComputationNumericAtom model rowGroup
        let checked ← elaborated "EntityComparison"
          (elaborateEntityNumericComparison model rowGroup numericOp (← lowerNumericExpr atom left)
            (← lowerNumericExpr atom right) suppress)
        elaborated "EntityComparison" (CheckedValidationCondition.fromOrderedNumeric checked)]
    | _ => []
  flat ++ specific ++ groupCount ++ fieldFill

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

/-- Lower a rule condition at its rule group. `suppress` is the `@SuppressWarning` preamble. -/
partial def lowerCondition (model : FlatModel) (rowGroup : GroupPath) (suppress : Bool) (condition : Expr) :
    Lowering (CheckedValidationCondition model) :=
  let whole := (lowerFlat model rowGroup condition).bind fun surface =>
    (elaborate model rowGroup surface).toOption.bind fun checked =>
      (CheckedValidationCondition.fromFlat checked).toOption
  match whole, condition with
  | some checked, _ => pure checked
  | none, .parens body => lowerCondition model rowGroup suppress body
  | none, .logic op (first :: rest) => do
      let join := match op with
        | .and => CheckedValidationCondition.and
        | .or => CheckedValidationCondition.or
      let mut result ← lowerCondition model rowGroup suppress first
      for part in rest do
        result ← elaborated "Connective" (join result (← lowerCondition model rowGroup suppress part))
      pure result
  | none, leaf =>
      let construct := match leaf with
        | .compare _ _ _ => (leaf.leadingCall?.map ("Comparison/" ++ ·)).getD leaf.construct
        | _ => leaf.construct
      firstAdmitted construct (leafCarriers model rowGroup suppress leaf)

end A12Kernel.Dm
