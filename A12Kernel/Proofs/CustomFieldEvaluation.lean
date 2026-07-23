import A12Kernel.Elaboration.StringContext

/-! # A12Kernel.Proofs.CustomFieldEvaluation — checked custom full-evaluation laws -/

namespace A12Kernel

/-- Preparation fails before condition elaboration and preserves its exact integration error. -/
theorem elaborateAndEvalStringContextFull_preparationError
    (compilePattern : StringPatternCompiler)
    (model : FlatModel) (world : World) (locale : String)
    (declaringGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool) (condition : SurfaceCondition)
    (error : FlatStringContextPreparationError)
    (failed :
      prepareFlatStringContext world compilePattern model = .error error) :
    elaborateAndEvalStringContextFull compilePattern model world locale
      declaringGroup raw hasContent
      condition = .error (.preparation error) := by
  simp [elaborateAndEvalStringContextFull, failed] <;> rfl

/-- After successful preparation, a condition error remains a distinct elaboration failure. -/
theorem elaborateAndEvalStringContextFull_conditionError
    (compilePattern : StringPatternCompiler)
    (model : FlatModel) (world : World) (locale : String)
    (declaringGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool) (condition : SurfaceCondition)
    (prepared : PreparedFlatStringContext model compilePattern)
    (error : ElabError)
    (preparedOk :
      prepareFlatStringContext world compilePattern model = .ok prepared)
    (failed : elaborate model declaringGroup condition = .error error) :
    elaborateAndEvalStringContextFull compilePattern model world locale
      declaringGroup raw hasContent
      condition = .error (.condition error) := by
  simp [elaborateAndEvalStringContextFull, preparedOk, failed] <;> rfl

/-- Successful composition evaluates the exact checked core over the exact prepared locale-aware context with the supplied world. -/
theorem elaborateAndEvalStringContextFull_success
    (compilePattern : StringPatternCompiler)
    (model : FlatModel) (world : World) (locale : String)
    (declaringGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool) (condition : SurfaceCondition)
    (prepared : PreparedFlatStringContext model compilePattern)
    (checked : CheckedFlatCondition model)
    (preparedOk :
      prepareFlatStringContext world compilePattern model = .ok prepared)
    (elaborated : elaborate model declaringGroup condition = .ok checked) :
    elaborateAndEvalStringContextFull compilePattern model world locale
      declaringGroup raw hasContent
      condition = .ok (checked.core.evalFull
        ((prepared.checkContext locale raw).withWorld world) hasContent) := by
  simp [elaborateAndEvalStringContextFull, preparedOk, elaborated] <;> rfl

end A12Kernel
