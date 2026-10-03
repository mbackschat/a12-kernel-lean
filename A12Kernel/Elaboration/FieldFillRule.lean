import A12Kernel.Elaboration.ValidationCondition.Assembly

/-! # Rule carriers for the field-fill quantifiers and `NumberOfFilledFields`

The field-fill list in `FieldFillList` answers the count and all seven field-fill quantifiers over an
entity list of direct fields, starred fields and groups, and the checked validation leaf and ordered
numeric atom read it on the addressed route. This module is their surface entry point: it elaborates
the authored list at the rule group and builds either the quantifier leaf or a count comparison
against a literal threshold. General numeric expressions reuse the same count atom through
`NumericValidation/EntityComparison`.

Filtered quantifiers retain their checked filter. Counts and category reads keep their own boundary.
-/

namespace A12Kernel

inductive FieldFillRuleElabError where
  | invalidModel (error : ResolveError)
  | source (error : FieldFillListElabError)
  | incoherent
  deriving Repr

namespace CheckedValidationCondition

/-- A field-fill quantifier over an entity list, at the rule group. -/
def fromFieldFill (model : FlatModel) (rowGroup : GroupPath) (operator : FieldFillQuantifier)
    (authored : SurfaceFieldEntitySource) (bindingGroup : GroupPath := rowGroup) :
    Except FieldFillRuleElabError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let source ← (elaborateFieldFillList model rowGroup authored bindingGroup .quantifier).mapError .source
      (checkCore model bindingGroup (.leaf (.fieldFill operator source)) (by rw [hModel]; rfl) rowGroup)
        |>.mapError fun _ => .incoherent

end CheckedValidationCondition

/-- `NumberOfFilledFields(list) op threshold` at the rule group. -/
def elaborateFilledFieldCountComparison (model : FlatModel) (rowGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) (op : NumericComparisonOp) (threshold : Int) :
    Except FieldFillRuleElabError (CheckedOrderedNumericComparison model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let source ← (elaborateFieldFillList model rowGroup authored).mapError .source
      let core : OrderedNumericComparison model := {
        op := .ordinary op
        left := .atom (.filledFieldCount source)
        right := .literal { value := (threshold : Rat), authoredScale := 0 } }
      if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
        pure { rowGroup, operandScope := .sameGroupAddressed, core
               modelWellFormed := by rw [hModel]; rfl, wellFormed := hCore }
      else throw .incoherent

end A12Kernel
