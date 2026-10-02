import A12Kernel.Elaboration.ValidationCondition.Assembly

/-! # Rule carriers for the field-fill quantifiers and `NumberOfFilledFields`

The checked group source in `FilledFieldGroupCount` answers the count and all seven field-fill
quantifiers over one fixed or starred group operand, and the checked validation leaf and ordered
numeric atom read it on the addressed route. This module is their surface entry point: it resolves
the authored group at the rule group and builds either the quantifier leaf or a count comparison
against a literal threshold, the one comparison shape the retained observations cover.

A list of explicit fields, a list mixing groups and fields, and the count inside arithmetic are not
represented here.
-/

namespace A12Kernel

/-- One authored group operand of a field-fill quantifier or `NumberOfFilledFields`. -/
inductive SurfaceFieldFillGroupOperand where
  | fixed (group : SurfaceGroupPath)
  | starred (group : SurfaceStarGroupPath)
  deriving Repr, DecidableEq

inductive FieldFillRuleElabError where
  | invalidModel (error : ResolveError)
  | source (error : FilledFieldCountGroupElabError)
  | incoherent
  deriving Repr

def elaborateFieldFillGroupSource (model : FlatModel) (rowGroup : GroupPath)
    (operand : SurfaceFieldFillGroupOperand) (writtenGroup : GroupPath := rowGroup) :
    Except FieldFillRuleElabError (CheckedFilledFieldCountGroupSource model) :=
  (match operand with
    | .fixed group =>
        elaborateFilledFieldCountFixedGroupValidationSource model rowGroup { group } writtenGroup
    | .starred group =>
        elaborateFilledFieldCountStarredGroupValidationSource model rowGroup { group } writtenGroup)
    |>.mapError .source

namespace CheckedValidationCondition

/-- A field-fill quantifier over one group operand, at the rule group. -/
def fromFieldFill (model : FlatModel) (rowGroup : GroupPath) (operator : FieldFillQuantifier)
    (operand : SurfaceFieldFillGroupOperand) (writtenGroup : GroupPath := rowGroup) :
    Except FieldFillRuleElabError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let source ← elaborateFieldFillGroupSource model rowGroup operand writtenGroup
      (checkCore model rowGroup (.leaf (.fieldFill operator source)) (by rw [hModel]; rfl))
        |>.mapError fun _ => .incoherent

end CheckedValidationCondition

/-- `NumberOfFilledFields(group) op threshold` at the rule group. -/
def elaborateFilledFieldCountComparison (model : FlatModel) (rowGroup : GroupPath)
    (operand : SurfaceFieldFillGroupOperand) (op : NumericComparisonOp) (threshold : Rat)
    (writtenGroup : GroupPath := rowGroup) :
    Except FieldFillRuleElabError (CheckedOrderedNumericComparison model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let source ← elaborateFieldFillGroupSource model rowGroup operand writtenGroup
      let core : OrderedNumericComparison model := {
        op := .ordinary op
        left := .atom (.filledFieldCount source)
        right := .literal { value := threshold, authoredScale := 0 } }
      if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
        pure { rowGroup, operandScope := .sameGroupAddressed, core
               modelWellFormed := by rw [hModel]; rfl, wellFormed := hCore }
      else throw .incoherent

end A12Kernel
