import A12Kernel.Elaboration.Flat.Model

/-! # Checked flat-condition core admission -/

namespace A12Kernel

def FlatField.matchesDecl (field : FlatField) (declaration : FlatFieldDecl) : Bool :=
  declaration.toPresenceField == field

def FlatModel.admitsField (model : FlatModel) (field : FlatField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration => declaration.repeatableScope.isEmpty && field.matchesDecl declaration
  | .error _ => false

/-- Stronger than presence admission: the exact nonrepeatable declaration must expose an evaluated String value. -/
def FlatModel.admitsStringValueField (model : FlatModel)
    (field : FlatStringField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toStringValueField? == some field
  | .error _ => false

/-- Re-derive one direct textual operand's static profile from the exact model declaration retained by checked core admission. -/
def FlatModel.directComparableFor? (model : FlatModel)
    (operand : FlatTextFieldOperand) : Option DirectComparableField :=
  match model.lookupUniqueId operand.field.id with
  | .error _ => none
  | .ok declaration =>
      if declaration.repeatableScope.isEmpty &&
          operand.field.matchesDecl declaration then
        declaration.textComparisonProfileFor? operand
      else
        none

/-- Reconstruct the proof-bearing Enumeration projection retained by an operand whose reading scope binds every repeatable level of the exact model declaration. -/
def FlatModel.checkedEnumerationOperandIn? (model : FlatModel)
    (scope : List RepeatableLevel) (operand : FlatEnumerationOperand) :
    Option CheckedEnumerationProjection :=
  match model.lookupUniqueId operand.field.id with
  | .error _ => none
  | .ok declaration =>
      if declaration.repetitionBoundBy scope &&
          (FlatField.enumeration operand.field).matchesDecl declaration then
        match declaration.policy.kind, declaration.enumeration with
        | .enumeration, some source =>
            match elaborateEnumeration source with
            | .error _ => none
            | .ok checked =>
                match checkEnumerationProjection checked operand.projectionRef with
                | .error _ => none
                | .ok resolved => if resolved.projection == operand.projection then some resolved else none
        | _, _ => none
      else
        none

/-- The scalar instance of checked Enumeration projection reconstruction. -/
def FlatModel.checkedEnumerationOperand? (model : FlatModel)
    (operand : FlatEnumerationOperand) : Option CheckedEnumerationProjection :=
  model.checkedEnumerationOperandIn? [] operand

def FlatModel.enumerationLiteralAllowedByAny (model : FlatModel)
    (operands : List FlatTextFieldOperand) (value : String) : Bool :=
  operands.any fun operand =>
    match operand with
    | .enumeration enumeration =>
      match model.checkedEnumerationOperand? enumeration with
      | some checked =>
        checked.declaration.literalAllowed checked.projection value
      | none => false
    | .string _ => false

inductive FlatTokenOperandKind where
  | string
  | enumeration
  deriving Repr, DecidableEq

def FlatModel.tokenOperandKind? (model : FlatModel) :
    FlatTextFieldOperand → Option FlatTokenOperandKind
  | operand@(.string _) =>
      match model.directComparableFor? operand with
      | some .plainString => some .string
      | _ => none
  | .enumeration operand =>
      if (model.checkedEnumerationOperand? operand).isSome then
        some .enumeration
      else
        none

def tokenOperandListHasDuplicate : List FlatTextFieldOperand → Bool
  | [] => false
  | operand :: remaining =>
      remaining.contains operand || tokenOperandListHasDuplicate remaining

def FlatModel.tokenOperandListKind? (model : FlatModel)
    (operands : List FlatTextFieldOperand) : Option FlatTokenOperandKind :=
  match operands with
  | [] => none
  | first :: remaining => do
      let kind ← model.tokenOperandKind? first
      if !tokenOperandListHasDuplicate operands &&
          remaining.all (fun operand => model.tokenOperandKind? operand == some kind) then
        some kind
      else
        none

def numberOperandListHasDuplicate : List FlatNumberField → Bool
  | [] => false
  | operand :: remaining =>
      remaining.contains operand || numberOperandListHasDuplicate remaining

def FlatModel.admitsNumberOperandList (model : FlatModel)
    (operands : List FlatNumberField) : Bool :=
  !operands.isEmpty && !numberOperandListHasDuplicate operands &&
    operands.all fun operand => model.admitsField (.number operand)

def FlatModel.admitsComparison (model : FlatModel) (comparison : FlatComparison) : Bool :=
  match comparison with
  | .string _ field _ | .stringLength _ field _ =>
      model.admitsStringValueField field
  | .textFields _ left right =>
      match model.directComparableFor? left, model.directComparableFor? right with
      | some leftProfile, some rightProfile =>
          directFieldComparisonAllowed leftProfile rightProfile
      | _, _ => false
  | .enumeration _ operand expected =>
      match model.checkedEnumerationOperand? operand with
      | some checked =>
          checked.declaration.literalAllowed checked.projection expected
      | none => false
  | _ => !comparison.fields.isEmpty && comparison.fields.all model.admitsField

def FlatConditionLeaf.wellFormedBool (condition : FlatConditionLeaf) (model : FlatModel) : Bool :=
  match condition with
  | .compare comparison => model.admitsComparison comparison
  | .tokenValueList _ operands (.literals values) =>
      !values.isEmpty && match model.tokenOperandListKind? operands with
        | some .string => true
        | some .enumeration =>
            values.all (model.enumerationLiteralAllowedByAny operands)
        | none => false
  | .tokenValueList _ operands (.fields valueOperands) =>
      match model.tokenOperandListKind? operands,
          model.tokenOperandListKind? valueOperands with
      | some fieldKind, some valueKind =>
          fieldKind == valueKind &&
            !tokenOperandListHasDuplicate (operands ++ valueOperands)
      | _, _ => false
  | .numberValueList _ operands (.literals values) =>
      operands.length == 1 && model.admitsNumberOperandList operands && !values.isEmpty &&
        values.all fun value => value.den == 1
  | .numberValueList _ operands (.fields valueOperands) =>
      model.admitsNumberOperandList operands &&
        model.admitsNumberOperandList valueOperands &&
        !numberOperandListHasDuplicate (operands ++ valueOperands)
  | .fieldFilled field => model.admitsField field
  | .fieldNotFilled field => model.admitsField field

def FlatCondition.wellFormedBool (condition : FlatCondition) (model : FlatModel) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedBool model

def FlatCondition.WellFormed (condition : FlatCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

/-- The only source-to-core result accepted by later stages. -/
structure CheckedFlatCondition (model : FlatModel) where
  rowGroup : GroupPath
  core : FlatCondition
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- Certify a constructed core condition against an already-validated model. This is the shared boundary for ordinary surface lowering and semantic desugarings. -/
def FlatCondition.checkAgainstValidatedModel (condition : FlatCondition)
    (model : FlatModel) (rowGroup : GroupPath)
    (modelValid : model.validate = .ok ()) :
    Except ElabError (CheckedFlatCondition model) :=
  if hCore : condition.wellFormedBool model = true then
    .ok {
      rowGroup
      core := condition
      modelWellFormed := by
        rw [modelValid]
        rfl
      wellFormed := hCore
    }
  else
    .error .incoherentCore

end A12Kernel
