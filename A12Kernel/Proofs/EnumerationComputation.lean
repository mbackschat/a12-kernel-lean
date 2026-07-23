import A12Kernel.Elaboration.EnumerationComputation

/-! # Checked ordinary Enumeration computation laws -/

namespace A12Kernel

/-- A nonempty exact token becomes the common accepted String-shaped target payload without rewriting its stored identity. -/
theorem nonemptyToken_asEnumerationTargetOutcome
    (token : String) (nonempty : token ≠ "") :
    (TokenComputationResult.value token).asEnumerationTargetOutcome =
      .accepted { text := token, nonempty } := by
  simp [TokenComputationResult.asEnumerationTargetOutcome, nonempty]

/-- Clean absence remains no-value at the Enumeration target rather than manufacturing an empty stored token. -/
theorem noValue_asEnumerationTargetOutcome :
    TokenComputationResult.noValue.asEnumerationTargetOutcome = .noValue := by
  rfl

/-- Formal unavailability retains its exact cause through the Enumeration target projection. -/
theorem poisonedToken_asEnumerationTargetOutcome (cause : FormalCause) :
    (TokenComputationResult.poison cause).asEnumerationTargetOutcome =
      .poison cause := by
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
      (operation.source.evaluate (model.checkContext raw)).asEnumerationTargetOutcome := by
  rfl

end A12Kernel
