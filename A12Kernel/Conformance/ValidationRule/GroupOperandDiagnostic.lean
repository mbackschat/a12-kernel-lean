import A12Kernel.Elaboration.ValidationRuleGroupOperand

/-! # Rule-owned unstarred repeatable group diagnostic matrix -/

namespace A12Kernel.Conformance.ValidationRule.GroupOperandDiagnostic

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Shipment"], name := "TrackingCode",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Shipment", "Destination"], name := "City",
        policy := { kind := .number unsigned } },
      { id := 3, groupPath := ["Shipment", "Parcels"], name := "Label",
        policy := { kind := .number unsigned }, repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Shipment", "Parcels"] }] }

private def nestedModel : FlatModel :=
  { fields := [
      { id := 3, groupPath := ["Shipment", "Parcels"], name := "Label",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 4, groupPath := ["Shipment", "Parcels", "Items"], name := "Code",
        policy := { kind := .number unsigned }, repeatableScope := [10, 20] }]
    repeatableGroups := [
      { level := 10, path := ["Shipment", "Parcels"] },
      { level := 20, path := ["Shipment", "Parcels", "Items"] }] }

private def group (groups : GroupPath) : SurfaceGroupReference :=
  .path { base := .absolute, groups }

private def groupOperand (groups : GroupPath) : SurfaceGroupListOperand :=
  .group (group groups)

private def ruleGroup : SurfaceGroupReference := .ruleGroup false

private def groupFilled (rowGroup : GroupPath) (errorField : FieldId) :=
  projectGroupFilledRuleAdmission model rowGroup errorField
    (group ["Shipment", "Parcels"])

private def groupList (rowGroup : GroupPath) (errorField : FieldId)
    (operator : GroupFillQuantifier) (operands : List SurfaceGroupListOperand) :=
  projectGroupListRuleAdmission model rowGroup errorField operator operands

private def groupCount (rowGroup : GroupPath) (errorField : FieldId)
    (groups : List SurfaceGroupReference) :=
  projectFilledGroupCountGreaterZeroRuleAdmission
    model rowGroup errorField groups

/- The error field is the sole moving discriminator for the same ordinary group reference. -/
example :
    groupFilled ["Shipment"] 1 =
        .rejected .noWildcard ∧
      groupFilled ["Shipment"] 3 = .admitted := by
  native_decide

/- The exact positive quantifier shapes follow the same locus rule. -/
example :
    groupList ["Shipment"] 1 .allGroupsFilled [
        groupOperand ["Shipment", "Parcels"],
        groupOperand ["Shipment", "Destination"]] =
      .rejected .noWildcard ∧
    groupList ["Shipment"] 3 .allGroupsFilled [
        groupOperand ["Shipment", "Parcels"],
        groupOperand ["Shipment", "Destination"]] = .admitted ∧
    groupList ["Shipment"] 1 .atLeastOneGroupFilled [
        groupOperand ["Shipment", "Parcels"]] =
      .rejected .noWildcard ∧
    groupList ["Shipment"] 3 .atLeastOneGroupFilled [
        groupOperand ["Shipment", "Parcels"]] = .admitted := by
  native_decide

/- Count multiplicity and the iteration gate remain distinct after the same locus is bound. -/
example :
    groupCount ["Shipment"] 1 [group ["Shipment", "Parcels"]] =
        .rejected .noWildcard ∧
      groupCount ["Shipment"] 3 [group ["Shipment", "Parcels"]] =
        .rejected .paramSizeInvalidGN ∧
      groupCount ["Shipment"] 1 [
          group ["Shipment", "Parcels"],
          group ["Shipment", "Destination"]] =
        .rejected .noWildcard ∧
      groupCount ["Shipment"] 3 [
          group ["Shipment", "Parcels"],
          group ["Shipment", "Destination"]] =
        .rejected .negativeConditionInIteration := by
  native_decide

/- Moving the rule group to the repeated group does not replace the error-locus discriminator. -/
example :
    groupCount ["Shipment", "Parcels"] 3 [
        group ["Shipment", "Parcels"]] =
      .rejected .paramSizeInvalidGN ∧
    groupList ["Shipment", "Parcels"] 3 .atLeastOneGroupFilled [
        groupOperand ["Shipment", "Parcels"]] = .admitted := by
  native_decide

/- Unmeasured carrier, operand-order, and nested-profile generalizations remain explicit. -/
example :
    groupList ["Shipment"] 3 .notAllGroupsFilled [
        groupOperand ["Shipment", "Parcels"],
        groupOperand ["Shipment", "Destination"]] = .unmapped ∧
    groupList ["Shipment"] 3 .allGroupsFilled [
        groupOperand ["Shipment", "Destination"],
        groupOperand ["Shipment", "Parcels"]] = .unmapped := by
  native_decide

/- `RuleGroup` is a valid fixed reference elsewhere, but is unmeasured in this paired matrix. -/
example :
    groupList ["Shipment", "Destination"] 3 .allGroupsFilled [
        groupOperand ["Shipment", "Parcels"], .group ruleGroup] = .unmapped ∧
      groupCount ["Shipment", "Destination"] 3 [
        group ["Shipment", "Parcels"], ruleGroup] = .unmapped := by
  native_decide

example :
    projectGroupFilledRuleAdmission nestedModel ["Shipment"] 4
        (group ["Shipment", "Parcels", "Items"]) = .unmapped ∧
      projectGroupFilledRuleAdmission model ["Shipment"] 99
        (group ["Shipment", "Parcels"]) = .unmapped := by
  native_decide

example :
    KernelStaticDiagnostic.kernelCode .negativeConditionInIteration =
      "MVK_NEG_CONDITION_IN_ITERATION" := by
  native_decide

end A12Kernel.Conformance.ValidationRule.GroupOperandDiagnostic
