import A12Kernel.Evidence.ObservationBundleTest
import A12Kernel.Evidence.StringCascadeProjection
import A12Kernel.Evidence.StringCascadeProjectionTest
import A12Kernel.Evidence.StringComputationProjection
import A12Kernel.Evidence.StringComputationProjectionTest
import A12Kernel.Evidence.ValidationProjection
import A12Kernel.Evidence.ValidationProjectionTest

/-! IO-only retained-kernel-evidence replay. This executable boundary is absent from the library, conformance, and trusted theorem roots. -/

def main : IO Unit := do
  let root : System.FilePath := "evidence/kernel-30.8.1"
  A12Kernel.Evidence.ObservationBundleTest.checkIo
  let validationCount ← A12Kernel.Evidence.ValidationProjection.checkArtifacts root
  let stringCount ← A12Kernel.Evidence.StringComputationProjection.checkArtifacts root
  A12Kernel.Evidence.StringComputationProjectionTest.checkIo root
  let cascadeCount ← A12Kernel.Evidence.StringCascadeProjection.checkArtifacts
    (root / "captures/string-direct-cascade-v1")
  let total := validationCount + stringCount + cascadeCount
  IO.println s!"kernel evidence: {total}/{total} compact non-public projections agree; 25 public normalized associations are checked by checkReferenceProcess"
