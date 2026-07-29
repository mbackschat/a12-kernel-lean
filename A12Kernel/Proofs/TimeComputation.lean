import A12Kernel.Elaboration.TimeComputation

/-! # Checked Time target laws -/

namespace A12Kernel

@[simp] theorem timeConstructionResult_value
    (time : TimeOfDay) :
    (TimeConstructionResult.value time).asTimeComputationResult =
      .value time := rfl

@[simp] theorem timeConstructionResult_unavailable
    (cause : FormalCause) :
    (TimeConstructionResult.unavailable cause).asTimeComputationResult =
      .poison cause := rfl

/-- Every selected clock is retained exactly through target rendering. -/
theorem timeTarget_evaluate_value
    (target : CheckedTimeTarget model) (time : TimeOfDay) :
    target.evaluate (.value time) =
      .accepted (target.format.render time) := rfl

end A12Kernel
