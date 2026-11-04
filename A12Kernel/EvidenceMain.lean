import A12Kernel.Evidence.DeclarationNotificationProjection
import A12Kernel.Evidence.NumberFormalProjection
import A12Kernel.Evidence.ObservationBundleTest
import A12Kernel.Evidence.RuleCheckProjection
import A12Kernel.Evidence.StringCascadeProjection
import A12Kernel.Evidence.StringCascadeProjectionTest
import A12Kernel.Evidence.StringComputationProjection
import A12Kernel.Evidence.StringComputationProjectionTest
import A12Kernel.Evidence.ValidationProjection
import A12Kernel.Evidence.ValidationProjectionTest

/-! IO-only retained-kernel-evidence replay. This executable boundary is absent from the library, conformance, and trusted theorem roots. -/

def main : IO Unit := do
  -- The frozen 30.8.1 root holds every input and the compact bundles of the retired producer, which
  -- cannot be re-run; the 31.1.1 root holds the re-captured observations of the same inputs.
  let root : System.FilePath := "evidence/kernel-30.8.1"
  let observed : System.FilePath := "evidence/kernel-31.1.1"
  A12Kernel.Evidence.ObservationBundleTest.checkIo
  let validationCount ← A12Kernel.Evidence.ValidationProjection.checkArtifacts root
  let stringCount ← A12Kernel.Evidence.StringComputationProjection.checkArtifacts root
  A12Kernel.Evidence.StringComputationProjectionTest.checkIo root
  let cascadeCount ← A12Kernel.Evidence.StringCascadeProjection.checkArtifacts
    (root / "captures/string-direct-cascade-v1")
  let (ruleCheckCount, ruleCheckSkipped) ← A12Kernel.Evidence.RuleCheckProjection.checkArtifacts root observed
  IO.println s!"rule-check observations: {ruleCheckCount} rows agree, {A12Kernel.Evidence.RuleCheckProjection.deferred.length} deferred, {ruleCheckSkipped} without a Kernel verdict"
  let (numberCount, numberCodes) ← A12Kernel.Evidence.NumberFormalProjection.checkArtifacts root observed
  IO.println s!"Number formal observations: {numberCount} engine observations agree through the reader on {numberCodes} field codes"
  let declarationCount ← A12Kernel.Evidence.DeclarationNotificationProjection.checkArtifacts root observed
  IO.println s!"declaration notifications: {declarationCount} rows agree through the reader"
  let total := validationCount + stringCount + cascadeCount
  IO.println s!"kernel evidence: {total}/{total} compact non-public projections agree; 25 public normalized associations are checked by checkReferenceProcess"
