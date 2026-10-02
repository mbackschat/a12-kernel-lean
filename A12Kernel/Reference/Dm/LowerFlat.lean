import A12Kernel.Reference.Dm.LowerCore

/-! # Lowering a condition onto the flat surface

The flat `SurfaceCondition` is the established carrier for nonrepeatable rules over fill checks,
literal and field comparisons, `Today`, `Now`, `BaseYear`, enumeration categories, value lists and
`Length`. A condition every leaf of which has a flat form lowers here whole; `LowerValidation.lean`
tries the mixed carriers for whatever does not. Which flat arm a value list takes depends on the
declared kind of its first field, so this lowering reads the model, but it decides no admission: the
flat elaborator still checks every operand.
-/

namespace A12Kernel.Dm

private def literal? (model : FlatModel) : Expr → Option SurfaceLiteral
  | .number text => (decodeNumber? text).map (.number ·.value)
  | .constant "True" => some (.boolean true)
  | .constant "False" => some (.boolean false)
  -- A temporal literal the flat surface has no constant for is not read as its text.
  | .string text => (dateConstant? model text).orElse fun _ =>
      if isTemporalConstant text then none else some (.string text)
  | _ => none

private def textOperand? : Expr → Option SurfaceTextFieldOperand
  | .entity { path, index := none, category := none } => (path.toFieldPath?).map .direct
  | .entity { path, index := none, category := some name } =>
      (path.toFieldPath?).map (.category · name)
  | _ => none

private def kindOf (model : FlatModel) (rowGroup : GroupPath) (path : SurfaceFieldPath) :
    Option SurfaceScalarKind :=
  (model.resolveFieldDeclarationUnchecked rowGroup path).toOption.map (·.policy.kind.surfaceKind)

private def stringLiterals? (values : List Expr) : Option (List String) :=
  values.mapM fun | .string text => some text | _ => none

private def integers? (values : List Expr) : Option (List Int) :=
  values.mapM fun
    | .number text => (decodeNumber? text).bind fun literal =>
        if literal.authoredScale == 0 then some literal.value.num else none
    | _ => none

private def membershipOp? : String → Option ValueListMembershipOp
  | "FieldValueIncludedInValueList" => some .included
  | "FieldValueNotIncludedInValueList" => some .notIncluded
  | _ => none

private def quantifier? : String → Option ValueListQuantifier
  | "AtLeastOneFieldValueIncludedInValueList" => some .atLeastOne
  | "NoFieldValueIncludedInValueList" => some .no
  | "NotAllFieldValuesIncludedInValueList" => some .notAll
  | _ => none

private def plainExprs (arguments : List Argument) : Option (List Expr) :=
  arguments.mapM fun | .mk expr none none => some expr | _ => none

/-- `FieldValueIncludedInValueList(f, v1, v2)`: one field, then its values, each list by the field's
kind. -/
private def membership (model : FlatModel) (rowGroup : GroupPath) (op : ValueListMembershipOp)
    (arguments : List Argument) : Option SurfaceCondition := do
  let first :: values ← plainExprs arguments | none
  let operand ← textOperand? first
  let field := operand.reference
  match kindOf model rowGroup field, operand with
  | some .enumeration, _ =>
      match stringLiterals? values with
      | some literals => some (.enumerationValueMembership op operand literals)
      | none => (values.mapM textOperand?).map (.enumerationFieldValueMembership op operand)
  | some .string, .direct _ =>
      match stringLiterals? values with
      | some literals => some (.stringValueMembership op field literals)
      | none => (values.mapM Expr.fieldEntity?).map (.stringFieldValueMembership op field)
  | some .number, .direct _ =>
      match integers? values with
      | some numbers => some (.numberValueMembership op field numbers)
      | none => (values.mapM Expr.fieldEntity?).map (.numberFieldValueMembership op field)
  | _, _ => none

/-- `AtLeastOneFieldValueIncludedInValueList(f1, f2 In v1, v2)`: fields, then after `In` values. -/
private def quantified (model : FlatModel) (rowGroup : GroupPath) (quantifier : ValueListQuantifier)
    (fields values : List Argument) : Option SurfaceCondition := do
  let fields ← plainExprs fields
  let values ← plainExprs values
  let operands ← fields.mapM textOperand?
  let first ← operands.head?
  match kindOf model rowGroup first.reference with
  | some .enumeration =>
      match stringLiterals? values with
      | some literals => some (.enumerationValueList quantifier operands literals)
      | none => (values.mapM textOperand?).map (.enumerationFieldValueList quantifier operands)
  | some .string =>
      let paths ← fields.mapM Expr.fieldEntity?
      match stringLiterals? values with
      | some literals => some (.stringValueList quantifier paths literals)
      | none => (values.mapM Expr.fieldEntity?).map (.stringFieldValueList quantifier paths)
  | some .number =>
      let paths ← fields.mapM Expr.fieldEntity?
      (values.mapM Expr.fieldEntity?).map (.numberFieldValueList quantifier paths)
  | _ => none

/-- A comparison with a field read on one side. `mirrored` says the field was written on the right,
so the operator is read from the field's side. -/
private def fieldComparison (model : FlatModel) (op : SurfaceComparisonOp)
    (field : Reference) (other : Expr) (mirrored : Bool) : Option SurfaceCondition := do
  let fieldOp := if mirrored then mirrorComparison op else op
  let position : SurfacePointInTimePosition := if mirrored then .left else .right
  let path ← field.path.toFieldPath?
  if field.index.isSome then none
  match field.category, other with
  | some category, .string text => some (.compareEnumeration fieldOp path (.category category) text)
  | some _, _ => none
  | none, .constant "Today" => some (.compareToday op position path)
  | none, .constant "Now" => some (.compareNow op position path)
  | none, .constant "BaseYear" => some (.compareBaseYear op position path)
  | none, .value right =>
      if mirrored then none
      else
        let rightPath ← right.path.toFieldPath?
        if right.index.isSome then none
        match right.category with
        | none => some (.compareFields op path rightPath)
        | some name => some (.compareTextFields op (.direct path) (.category rightPath name))
  | none, other => (literal? model other).map (.compare fieldOp path ·)

/-- The flat form of a whole condition, or `none` when any part has none. -/
partial def lowerFlat (model : FlatModel) (rowGroup : GroupPath) : Expr → Option SurfaceCondition
  | .parens body => lowerFlat model rowGroup body
  | .logic op (first :: rest) => do
      let parts ← (first :: rest).mapM (lowerFlat model rowGroup)
      let join := match op with | .and => SurfaceCondition.and | .or => SurfaceCondition.or
      match parts with
      | head :: tail => some (tail.foldl join head)
      | [] => none
  | .call "FieldFilled" [.mk field none none] none none => (field.fieldEntity?).map .fieldFilled
  | .call "FieldNotFilled" [.mk field none none] none none => (field.fieldEntity?).map .fieldNotFilled
  | .call id arguments listed none =>
      match membershipOp? id, quantifier? id, listed with
      | some op, _, none => membership model rowGroup op arguments
      | _, some quantifier, some values => quantified model rowGroup quantifier arguments values
      | _, _, _ => none
  | .compare op left right => do
      let op ← op.toSurface?
      match left, right with
      | .value field, other => fieldComparison model op field other false
      | other, .value field => fieldComparison model op field other true
      | .call "Length" [.mk field none none] none none, .number text => do
          let literal ← decodeNumber? text
          pure (.lengthCompare op (← field.fieldEntity?) literal)
      | .number text, .call "Length" [.mk field none none] none none => do
          let literal ← decodeNumber? text
          pure (.literalCompareLength literal op (← field.fieldEntity?))
      | _, _ => none
  | _ => none

end A12Kernel.Dm
