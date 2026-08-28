import A12Kernel.Elaboration.BooleanConstantComputation

/-! # Boolean and Confirm constant-computation target-admission law -/

namespace A12Kernel

/-- The checked gate accepts exactly both Boolean constants and the True-only Confirm case. -/
theorem checkBooleanConstantOperation_accepts_iff
    (targetKind : FieldKind) (value : Bool) :
    (checkBooleanConstantOperation targetKind value).isOk =
      (targetKind == .boolean || (targetKind == .confirm && value)) := by
  cases targetKind <;> cases value <;> rfl

end A12Kernel
