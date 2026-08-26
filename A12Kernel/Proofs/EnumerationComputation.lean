import A12Kernel.Elaboration.EnumerationComputation

/-! # Checked ordinary Enumeration computation laws -/

namespace A12Kernel

/-- A checked Enumeration computation target cannot name a field other than the exact model-owned operand that certifies its domain. -/
theorem checkedEnumerationComputationTarget_field_exact
    (target : CheckedEnumerationComputationTarget model) :
    target.field = target.targetOperand.field.id := by
  rfl

/-- Compatibility certifies the whole selected source domain, not merely the runtime token that happened to be read. -/
theorem enumerationCompatibility_coversSelectedDomain
    (source target : CheckedEnumerationProjection)
    (compatible : source.compatibleWithTarget target = true) :
    source.selectedTokens.all (fun token =>
      target.declaration.literalAllowed target.projection token) = true := by
  simp [CheckedEnumerationProjection.compatibleWithTarget] at compatible
  simpa using compatible.1

/-- A checked operation exposes the exact source-to-target compatibility certificate established before runtime. -/
theorem checkedEnumerationComputation_source_allowed
    (operation : CheckedEnumerationComputationOperation model) :
    operation.source.allowedFor operation.target.projection = true :=
  operation.sourceAllowed

/-- Checked Enumeration computation makes direct target self-reference unrepresentable. -/
theorem checkedEnumerationComputation_excludes_target_reference
    (operation : CheckedEnumerationComputationOperation model) :
    operation.source.referencesField operation.target.field = false :=
  operation.targetNotReferenced

/-- The checked wrapper adds no target-specific evaluator: it delegates to the model-owned checked token source and the shared target projection. -/
theorem checkedEnumerationComputation_evaluate
    (operation : CheckedEnumerationComputationOperation model)
    (raw : RawFlatContext) :
    operation.evaluate raw =
      (operation.source.evaluate (model.checkContext raw)).asExactStringTargetOutcome := by
  rfl

end A12Kernel
