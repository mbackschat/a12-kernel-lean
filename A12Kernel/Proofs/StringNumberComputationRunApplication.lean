import A12Kernel.Elaboration.StringNumberComputationRunApplication

/-! # Family-separated String and Number application laws -/

namespace A12Kernel

/-- The String result is exactly the established String-family application. -/
@[simp] theorem stringNumberComputationRun_applyTo_string
    [DecidableEq Target]
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target)
    (stringDestination : StringComputationDestination Target)
    (numberDestination : NumericComputationDestination Target) :
    (view.applyTo stringDestination numberDestination).string =
      view.string.applyTo stringDestination := by
  rfl

/-- The Number result is exactly the established Number-family application. -/
@[simp] theorem stringNumberComputationRun_applyTo_number
    [DecidableEq Target]
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target)
    (stringDestination : StringComputationDestination Target)
    (numberDestination : NumericComputationDestination Target) :
    (view.applyTo stringDestination numberDestination).number =
      view.number.applyTo numberDestination := by
  rfl

/-- The String result cannot depend on the separately supplied Number destination. -/
theorem stringNumberComputationRun_applyTo_string_independent
    [DecidableEq Target]
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target)
    (stringDestination : StringComputationDestination Target)
    (firstNumberDestination secondNumberDestination :
      NumericComputationDestination Target) :
    (view.applyTo stringDestination firstNumberDestination).string =
      (view.applyTo stringDestination secondNumberDestination).string := by
  rfl

/-- The Number result cannot depend on the separately supplied String destination. -/
theorem stringNumberComputationRun_applyTo_number_independent
    [DecidableEq Target]
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target)
    (firstStringDestination secondStringDestination :
      StringComputationDestination Target)
    (numberDestination : NumericComputationDestination Target) :
    (view.applyTo firstStringDestination numberDestination).number =
      (view.applyTo secondStringDestination numberDestination).number := by
  rfl

end A12Kernel
