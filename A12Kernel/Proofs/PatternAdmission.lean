import A12Kernel.Elaboration.StringPattern
import A12Kernel.Proofs.StringPattern

/-! # A12Kernel.Proofs.PatternAdmission — two-stage admission laws -/

namespace A12Kernel

@[simp]
theorem classifyStringPattern_java_rejected (javaCompiles : String → Bool)
    (source : String) (rejected : javaCompiles source = false) :
    classifyStringPattern javaCompiles source = .rejected .javaSyntax := by
  simp [classifyStringPattern, rejected]

@[simp]
theorem classifyStringPattern_admitted_iff (javaCompiles : String → Bool)
    (source : String) :
    classifyStringPattern javaCompiles source = .admitted ↔
      javaCompiles source = true ∧ kernelPatternSourceAllowed source = true := by
  cases compiles : javaCompiles source <;>
    cases allowed : kernelPatternSourceAllowed source <;>
    simp [classifyStringPattern, compiles, allowed]

/-- Once both admission facts hold, the convenience boundary delegates exactly to the existing resolved matcher semantics. -/
theorem evalAdmittedStringPattern_success (javaCompiles : String → Bool)
    (source : String) (op : StringPatternOp) (wholeValueMatches : String → Bool)
    (operand : SimpleComparisonOperand String)
    (compiles : javaCompiles source = true)
    (allowed : kernelPatternSourceAllowed source = true) :
    evalAdmittedStringPattern javaCompiles source op wholeValueMatches operand =
      .ok (op.evalResolved wholeValueMatches operand) := by
  simp [evalAdmittedStringPattern, admitStringPattern, compiles, allowed,
    AdmittedStringPattern.evalResolved]

/-- Admission cannot introduce omission polarity; the admitted wrapper inherits the resolved consumer's stronger law. -/
theorem admittedStringPattern_fired_is_value
    (admitted : AdmittedStringPattern javaCompiles)
    (op : StringPatternOp) (wholeValueMatches : String → Bool)
    (operand : SimpleComparisonOperand String) (polarity : Polarity)
    (fired : admitted.evalResolved op wholeValueMatches operand = .fired polarity) :
    polarity = .value := by
  exact stringPattern_evalResolved_fired_is_value op wholeValueMatches operand polarity fired

end A12Kernel
