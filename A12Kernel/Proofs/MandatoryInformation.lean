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

/-- An INFO negative field rule retains its authored identity without participating in mandatory derivation. -/
theorem deriveCheckedMandatoryInformation_ignores_info_severity :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
      .ignored (.infoFieldNotFilled "InfoField"),
      .fieldNotFilled "ErrorField"
    ] = some {
      mandatory := ["ErrorField"],
      mandatoryForRootGroup := ["ErrorField"],
      mandatoryRootGroups := ["Form"]
    } := by
  decide

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

/-- An isolated unconditional declaration requirement preserves the settled direct negative-field derivation. -/
theorem deriveCheckedMandatoryInformation_declared_always_matches_authored
    [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (field : Field) :
    deriveCheckedMandatoryInformation rootOf [
        .declaredFieldRequirement .always field
      ] =
      deriveCheckedMandatoryInformation rootOf [.fieldNotFilled field] := by
  rfl

/-- An isolated parent-present declaration requirement preserves the settled root-guarded derivation at the field's root. -/
theorem deriveCheckedMandatoryInformation_declared_parent_matches_root_guard :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .declaredFieldRequirement .ifParentPresent "DeclaredField"
      ] =
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .rootGuardedNotFilled "Form" "DeclaredField"
      ] := by
  decide

/-- A measured authored root seed promotes parent-present declaration requiredness through the settled root-guarded closure. -/
theorem deriveCheckedMandatoryInformation_declared_parent_closes_from_root_seed :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .groupNotFilled "Form",
        .declaredFieldRequirement .ifParentPresent "DeclaredField"
      ] =
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .groupNotFilled "Form",
        .rootGuardedNotFilled "Form" "DeclaredField"
      ] := by
  decide

/-- The measured semantic-indexed rule contributes nothing as a whole while an independent direct requirement remains visible. -/
theorem deriveCheckedMandatoryInformation_ignores_semantic_indexed_rule :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .ignored (.semanticIndexed ["Note", "Rows/Value"]),
        .fieldNotFilled "Control"
      ] =
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldNotFilled "Control"
      ] := by
  decide

/-- The measured parallel-iterated rule contributes nothing as a whole while an independent direct requirement remains visible. -/
theorem deriveCheckedMandatoryInformation_ignores_parallel_iterated_rule :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .ignored (.parallelIterated ["Demand/Note", "Capacity/Units"]),
        .fieldNotFilled "Control"
      ] =
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldNotFilled "Control"
      ] := by
  decide

/-- Existential and universal field-list guards reach their concrete successful fixed points in either authored order. -/
theorem deriveCheckedMandatoryInformation_field_list_guards_close_reverse_authored :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldListGuardedNotFilled ["A", "B"] .atLeastOneFilled "Target",
        .fieldNotFilled "A"
      ] = some {
        mandatory := ["A", "Target"],
        mandatoryForRootGroup := ["A", "Target"],
        mandatoryRootGroups := ["Form"]
      } ∧
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldNotFilled "A",
        .fieldListGuardedNotFilled ["A", "B"] .atLeastOneFilled "Target"
      ] = some {
        mandatory := ["A", "Target"],
        mandatoryForRootGroup := ["A", "Target"],
        mandatoryRootGroups := ["Form"]
      } ∧
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldListGuardedNotFilled ["A", "B"] .allFilled "Target",
        .fieldNotFilled "A",
        .fieldNotFilled "B"
      ] = some {
        mandatory := ["A", "B", "Target"],
        mandatoryForRootGroup := ["A", "B", "Target"],
        mandatoryRootGroups := ["Form"]
      } ∧
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .fieldListGuardedNotFilled ["A", "B"] .allFilled "Target"
      ] = some {
        mandatory := ["A", "B", "Target"],
        mandatoryForRootGroup := ["A", "B", "Target"],
        mandatoryRootGroups := ["Form"]
      } := by
  decide

/-- Filled-count and distinct-count standalone rules have the same checked root contribution for every retained threshold. -/
theorem deriveCheckedMandatoryInformation_count_root_operator_independent
    (threshold : Option CheckedMandatoryCountThreshold) :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .countLessThan ["A", "B"] threshold
      ] =
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .differentValuesLessThan ["A", "B"] threshold
      ] := by
  rfl

/-- The reversed strict spelling shares the count-on-left strict guard result while retaining a distinct authored identity. -/
theorem deriveCheckedMandatoryInformation_reversed_strict_count_guard
    (threshold : Option CheckedMandatoryCountThreshold) :
    deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .countGuardedNotFilled ["A", "B"] .countGreater threshold "Target"
      ] =
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .countGuardedNotFilled ["A", "B"] .literalLessThanCount threshold "Target"
      ] := by
  rfl

/-- Checked construction retains the authored literal and pairs it with exactly the shared host conversion. -/
theorem checkMandatoryCountThreshold_sound
    (authored : DecodedNumericLiteral)
    (threshold : CheckedMandatoryCountThreshold)
    (checked : checkMandatoryCountThreshold authored = some threshold) :
    threshold.authored = authored ∧
      authored.javaRoundedInt32? = some threshold.narrowed := by
  unfold checkMandatoryCountThreshold at checked
  cases converted : authored.javaRoundedInt32? with
  | none => simp [converted] at checked
  | some narrowed =>
      simp [converted] at checked
      subst threshold
      simp

end A12Kernel
