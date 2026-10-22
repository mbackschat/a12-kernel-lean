import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.FieldEntityAdmission
import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.NumericValidation.EntityComparison
import A12Kernel.Elaboration.ValidationCondition.Assembly
import A12Kernel.Elaboration.ValidationRule.AssemblyError

/-! # The Kernel class of a reader refusal

The reader reports an elaboration error with the class its owning projection settles. A wrapping error
reports only the class of a wrapped cause that already has one: a resolver miss, a group operand or an
entity list's shape, each projected where the cause is defined and measured to draw the same class on
every carrier ([resolver checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)).
Every other arm reports none, so a refusal never borrows a class its own carrier was not measured on.
-/

namespace A12Kernel.Dm

instance : StaticClassified ResolveError := ⟨ResolveError.diagnostic?⟩
instance : StaticClassified FlatRuleAssemblyError := ⟨FlatRuleAssemblyError.diagnostic?⟩
instance : StaticClassified FixedGroupReferenceError := ⟨FixedGroupReferenceError.diagnostic?⟩
instance : StaticClassified FieldEntityShapeElabError := ⟨FieldEntityShapeElabError.diagnostic?⟩

instance : StaticClassified NumericValidationElabError := ⟨fun
  | .resolve error => error.diagnostic?
  | .groupReference error => error.diagnostic?
  | _ => none⟩

instance : StaticClassified NumberEntityElabError := ⟨fun
  | .shape error => error.diagnostic?
  | _ => none⟩

instance : StaticClassified FilledFieldCountGroupElabError := ⟨fun
  | .shape error => error.diagnostic?
  | _ => none⟩

instance : StaticClassified FieldFillListElabError := ⟨fun
  | .shape error => error.diagnostic?
  | .group (.shape error) => error.diagnostic?
  | _ => none⟩

instance : StaticClassified EntityNumericComparisonElabError := ⟨fun
  | .ordinary (.resolve error) => error.diagnostic?
  | .ordinary (.groupReference error) => error.diagnostic?
  | .numberSource (.shape error) => error.diagnostic?
  | .fieldFillSource (.shape error) => error.diagnostic?
  | .fieldFillSource (.group (.shape error)) => error.diagnostic?
  | .productSource error => error.diagnostic?
  | _ => none⟩

instance : StaticClassified ValidationConditionAssemblyError := ⟨fun
  | .fieldReference error => error.diagnostic?
  | .groupReference error => error.diagnostic?
  -- Raised only by the three quantifiers needing two operands (spec/02; semantic-index entry row
  -- `vAllGroupsFilledAlias`).
  | .groupListNeedsMultipleOperands => some .paramSizeInvalid2
  | _ => none⟩

end A12Kernel.Dm
