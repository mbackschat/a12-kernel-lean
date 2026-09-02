import A12Kernel.Semantics.MandatoryInformation

/-! # Mandatory-information derivation laws -/

namespace A12Kernel

@[simp] theorem deriveCheckedMandatoryInformation_empty
    [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) :
    deriveCheckedMandatoryInformation rootOf [] = some {} := by
  rfl

/-- A root-only requirement cannot invent a mandatory field. -/
theorem deriveCheckedMandatoryInformation_groupNotFilled_has_no_fields
    (root : String) :
    deriveCheckedMandatoryInformation (fun _ : String => root)
      [.groupNotFilled root] = some { mandatory := [], mandatoryForRootGroup := [], mandatoryRootGroups := [root] } := by
  rfl

/-- A root premise is interpreted only by root-relative analysis until a global root seed exists. -/
theorem deriveCheckedMandatoryInformation_root_guard_requires_global_seed :
    deriveCheckedMandatoryInformation (fun _ : String => "Form")
      [.rootGuardedNotFilled "Form" "A"] = some { mandatory := [], mandatoryForRootGroup := ["A"], mandatoryRootGroups := [] } := by
  decide

/-- Adding the matching root requirement promotes a root-guarded target into the global field set. -/
theorem deriveCheckedMandatoryInformation_root_seed_promotes_target :
    deriveCheckedMandatoryInformation (fun _ : String => "Form")
      [.rootGuardedNotFilled "Form" "A", .groupNotFilled "Form"] = some {
        mandatory := ["A"], mandatoryForRootGroup := ["A"], mandatoryRootGroups := ["Form"] } := by
  decide

end A12Kernel
