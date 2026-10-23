import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.GeneratedComputationRule

/-! # The static verdict of one computation

A computation is also the validation rule it generates
([spec/09 §6](../../../spec/09-computations.md#6-the-implicit-validation-rule-precisely)), so a refusal
whose own carrier names no Kernel class takes the class that rule's check draws. Every retained
`computation add` row of the [rule-check projection](../../Evidence/RuleCheckProjection.lean) agrees
with this account, as of 2026-10-22. The order in which the Kernel applies the two checks is not
measured; a computation refusal that already has a class keeps it, except the index stage, which
source-read follows the condition read
([October 21 letter](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.11), so a
class the generated rule draws precedes it.
-/

namespace A12Kernel.Dm

/-- Lower `computation`, a refusal without a class taking its generated rule's. -/
def checkComputation (model : DmModel) (language : Language) (computation : DmComputation) :
    Lowering (FlatFieldDecl × LoweredComputation model.flat) :=
  match lowerComputation model.flat language computation with
  | .ok checked => .ok checked
  | .error refusal =>
      let indexStage := refusal.kernelClass? == some KernelStaticDiagnostic.errorIndexAsCalculatedField.kernelCode
      -- A group target has no generated rule to speak for it: its build fails without a class.
      if (refusal.kernelClass?.isSome && !indexStage) || refusal.construct == "GroupTarget" then .error refusal
      else match computation.generatedRule? language with
        | none => .error refusal
        | some rule => match checkValidationRule model language rule with
          | .error generated => .error (if generated.kernelClass?.isSome then generated else refusal)
          | .ok _ => .error refusal

end A12Kernel.Dm
