import A12Kernel.Elaboration.CustomField

/-! # A12Kernel.Proofs.CustomFieldEvaluation — checked custom full-evaluation laws -/

namespace A12Kernel

/-- Preparation fails before condition elaboration and preserves its exact integration error. -/
theorem elaborateAndEvalCustomFull_preparationError
    (model : FlatModel) (world : World) (locale : String)
    (declaringGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool) (condition : SurfaceCondition)
    (error : FlatCustomFieldPreparationError)
    (failed : prepareFlatCustomFields world model = .error error) :
    elaborateAndEvalCustomFull model world locale declaringGroup raw hasContent
      condition = .error (.preparation error) := by
  simp [elaborateAndEvalCustomFull, failed] <;> rfl

/-- After successful preparation, a condition error remains a distinct elaboration failure. -/
theorem elaborateAndEvalCustomFull_conditionError
    (model : FlatModel) (world : World) (locale : String)
    (declaringGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool) (condition : SurfaceCondition)
    (prepared : PreparedFlatCustomFields) (error : ElabError)
    (preparedOk : prepareFlatCustomFields world model = .ok prepared)
    (failed : elaborate model declaringGroup condition = .error error) :
    elaborateAndEvalCustomFull model world locale declaringGroup raw hasContent
      condition = .error (.condition error) := by
  simp [elaborateAndEvalCustomFull, preparedOk, failed] <;> rfl

/-- Successful composition evaluates the exact checked core over the exact prepared locale-aware context with the supplied world. -/
theorem elaborateAndEvalCustomFull_success
    (model : FlatModel) (world : World) (locale : String)
    (declaringGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool) (condition : SurfaceCondition)
    (prepared : PreparedFlatCustomFields)
    (checked : CheckedFlatCondition model)
    (preparedOk : prepareFlatCustomFields world model = .ok prepared)
    (elaborated : elaborate model declaringGroup condition = .ok checked) :
    elaborateAndEvalCustomFull model world locale declaringGroup raw hasContent
      condition = .ok (checked.core.evalFull
        ((prepared.checkContext locale raw).withWorld world) hasContent) := by
  simp [elaborateAndEvalCustomFull, preparedOk, elaborated] <;> rfl

end A12Kernel
