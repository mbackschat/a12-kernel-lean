import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Elaboration.DateRangeInput

/-! # Checked flat-condition core admission -/

namespace A12Kernel

def FlatField.matchesDecl (field : FlatField) (declaration : FlatFieldDecl) : Bool :=
  declaration.toPresenceField == field

def FlatModel.admitsField (model : FlatModel) (field : FlatField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration => declaration.repeatableScope.isEmpty && field.matchesDecl declaration
  | .error _ => false

/-- Whether one model declaration is exactly this field, at whatever repeatable scope. A construct
reading the field asks separately whether its own reading scope binds that declaration's levels. -/
def FlatModel.ownsField (model : FlatModel) (field : FlatField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration => field.matchesDecl declaration
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
def FlatModel.directComparableIn? (model : FlatModel) (scope : List RepeatableLevel)
    (operand : FlatTextFieldOperand) : Option DirectComparableField :=
  match model.lookupUniqueId operand.field.id with
  | .error _ => none
  | .ok declaration =>
      if declaration.repetitionBoundBy scope &&
          operand.field.matchesDecl declaration then
        declaration.textComparisonProfileFor? operand
      else
        none

/-- The nonrepeatable instance of direct textual comparison admission. -/
def FlatModel.directComparableFor? (model : FlatModel)
    (operand : FlatTextFieldOperand) : Option DirectComparableField :=
  model.directComparableIn? [] operand

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

/-- Text comparisons share one gate across fixed validation and target-bound computation guards.
Other comparison families have no admission through this gate. -/
def FlatModel.admitsTextComparisonIn (model : FlatModel) (scope : List RepeatableLevel) :
    FlatComparison → Bool
  | .string _ field _ => model.directComparableIn? scope (.string field) == some .plainString
  | .enumeration _ operand expected =>
      match model.checkedEnumerationOperandIn? scope operand with
      | some checked => checked.declaration.literalAllowed checked.projection expected
      | none => false
  | .textFields _ left right =>
      match model.directComparableIn? scope left, model.directComparableIn? scope right with
      | some leftProfile, some rightProfile => directFieldComparisonAllowed leftProfile rightProfile
      | _, _ => false
  | _ => false

/-- Reuse the stored-range input certificate and component-set gate for each independently scoped operand. -/
def FlatModel.dateRangeComparisonProfilesMatch (model : FlatModel)
    (left right : FlatDateRangeField) : Bool :=
  ((do
    let left ← (model.lookupUniqueId left.id).toOption
    let right ← (model.lookupUniqueId right.id).toOption
    let left ← (certifyDateRangeInputField left).toOption
    let right ← (certifyDateRangeInputField right).toOption
    pure (left.format.components == right.format.components)) : Option Bool).getD false

def FlatModel.admitsComparison (model : FlatModel) (comparison : FlatComparison) : Bool :=
  match comparison with
  | .booleanFields op left right =>
      (match left, right with
        | .boolean _, .boolean _ => true
        | .confirm _, .confirm _ => op == .notEqual
        | _, _ => false) && comparison.fields.all model.admitsField
  | .dateRange _ left right =>
      model.dateRangeComparisonProfilesMatch left right && comparison.fields.all model.admitsField
  | .stringLength _ field _ => model.admitsStringValueField field
  | .string .. | .textFields .. | .enumeration .. => model.admitsTextComparisonIn [] comparison
  | _ => !comparison.fields.isEmpty && comparison.fields.all model.admitsField

/-- Singular membership has one subject and two polarities; `No` belongs only to plural quantification (spec/06 §B.4). -/
def ValueListAuthoredForm.admits (form : ValueListAuthoredForm)
    (quantifier : ValueListQuantifier) (subjectCount : Nat) : Bool :=
  match form with
  | .membership => subjectCount == 1 && quantifier != .no
  | .quantifier => true

def FlatConditionLeaf.wellFormedBool (condition : FlatConditionLeaf) (model : FlatModel) : Bool :=
  match condition with
  | .compare comparison => model.admitsComparison comparison
  | .tokenValueList quantifier operands (.literals values) form =>
      form.admits quantifier operands.length && (
        !values.isEmpty && match model.tokenOperandListKind? operands with
          | some .string => true
          | some .enumeration =>
              values.all (model.enumerationLiteralAllowedByAny operands)
          | none => false)
  | .tokenValueList quantifier operands (.fields valueOperands) form =>
      form.admits quantifier operands.length && (
        match model.tokenOperandListKind? operands,
            model.tokenOperandListKind? valueOperands with
        | some fieldKind, some valueKind =>
            fieldKind == valueKind &&
              !tokenOperandListHasDuplicate (operands ++ valueOperands)
        | _, _ => false)
  | .numberValueList quantifier operands (.literals values) form =>
      form.admits quantifier operands.length && (
        operands.length == 1 && model.admitsNumberOperandList operands && !values.isEmpty &&
          values.all fun value => value.den == 1)
  | .numberValueList quantifier operands (.fields valueOperands) form =>
      form.admits quantifier operands.length && (
        model.admitsNumberOperandList operands &&
          model.admitsNumberOperandList valueOperands &&
          !numberOperandListHasDuplicate (operands ++ valueOperands))
  | .fieldFilled field => model.admitsField field
  | .fieldNotFilled field => model.admitsField field

def FlatCondition.wellFormedBool (condition : FlatCondition) (model : FlatModel) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedBool model

def FlatCondition.WellFormed (condition : FlatCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

/-- What static legality *means* for one flat leaf, stated from the canonical account in
    [`spec/06-strings-and-enumerations.md`](../../../../spec/06-strings-and-enumerations.md)
    rather than from `wellFormedBool`'s branch layout. Kind agreement appears here as one
    shared witness and literal admission as an explicit quantifier, so the bridge theorem can
    disagree with the checker instead of restating it. -/
inductive FlatConditionLeaf.Legal (model : FlatModel) : FlatConditionLeaf → Prop where
  | compare {comparison : FlatComparison} :
      model.admitsComparison comparison = true →
      FlatConditionLeaf.Legal model (.compare comparison)
  | tokenLiteralsString {quantifier operands values} :
      (form = .membership → operands.length = 1 ∧ quantifier ≠ .no) →
      values ≠ [] →
      model.tokenOperandListKind? operands = some .string →
      FlatConditionLeaf.Legal model (.tokenValueList quantifier operands (.literals values) form)
  | tokenLiteralsEnumeration {quantifier operands values} :
      (form = .membership → operands.length = 1 ∧ quantifier ≠ .no) →
      values ≠ [] →
      model.tokenOperandListKind? operands = some .enumeration →
      (∀ value ∈ values, model.enumerationLiteralAllowedByAny operands value = true) →
      FlatConditionLeaf.Legal model (.tokenValueList quantifier operands (.literals values) form)
  | tokenFields {quantifier operands valueOperands kind} :
      (form = .membership → operands.length = 1 ∧ quantifier ≠ .no) →
      model.tokenOperandListKind? operands = some kind →
      model.tokenOperandListKind? valueOperands = some kind →
      tokenOperandListHasDuplicate (operands ++ valueOperands) = false →
      FlatConditionLeaf.Legal model (.tokenValueList quantifier operands (.fields valueOperands) form)
  | numberLiterals {quantifier operands values} :
      (form = .membership → operands.length = 1 ∧ quantifier ≠ .no) →
      operands.length = 1 →
      model.admitsNumberOperandList operands = true →
      values ≠ [] →
      -- Integrality restates the linked clause's §B.4 "Number literals are grammar-level integers
      -- with an optional leading minus"; the single-operand bound above is its §B.3 "a multi-field
      -- Number form has no literal-list shape". Neither is a Lean-side narrowing.
      (∀ value ∈ values, value.den = 1) →
      FlatConditionLeaf.Legal model (.numberValueList quantifier operands (.literals values) form)
  | numberFields {quantifier operands valueOperands} :
      (form = .membership → operands.length = 1 ∧ quantifier ≠ .no) →
      model.admitsNumberOperandList operands = true →
      model.admitsNumberOperandList valueOperands = true →
      numberOperandListHasDuplicate (operands ++ valueOperands) = false →
      FlatConditionLeaf.Legal model (.numberValueList quantifier operands (.fields valueOperands) form)
  | fieldFilled {field} :
      model.admitsField field = true →
      FlatConditionLeaf.Legal model (.fieldFilled field)
  | fieldNotFilled {field} :
      model.admitsField field = true →
      FlatConditionLeaf.Legal model (.fieldNotFilled field)

/-- Connective shape does not weaken static admission, so tree legality is leafwise. -/
inductive FlatCondition.Legal (model : FlatModel) : FlatCondition → Prop where
  | leaf {value : FlatConditionLeaf} :
      value.Legal model → FlatCondition.Legal model (.leaf value)
  | and {left right : FlatCondition} :
      FlatCondition.Legal model left → FlatCondition.Legal model right →
      FlatCondition.Legal model (.and left right)
  | or {left right : FlatCondition} :
      FlatCondition.Legal model left → FlatCondition.Legal model right →
      FlatCondition.Legal model (.or left right)

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
