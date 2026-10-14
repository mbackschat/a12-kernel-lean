import A12Kernel.Elaboration.StringPattern
import A12Kernel.Proofs.StringPattern

/-! # A12Kernel.Proofs.PatternAdmission — two-stage admission laws -/

namespace A12Kernel

@[simp]
theorem classifyStringPattern_java_rejected (compilePattern : StringPatternCompiler)
    (source : String) (rejected : compilePattern source = .rejected) :
    classifyStringPattern compilePattern source = .rejected .javaSyntax := by
  simp [classifyStringPattern, rejected]

/-- A source beyond the supplied compiler stays a host limit, never Java's syntax verdict. -/
@[simp]
theorem classifyStringPattern_host_unsupported (compilePattern : StringPatternCompiler)
    (source : String) (unsupported : compilePattern source = .unsupported) :
    classifyStringPattern compilePattern source = .rejected .hostUnsupported := by
  simp [classifyStringPattern, unsupported]

@[simp]
theorem classifyStringPattern_admitted_iff (compilePattern : StringPatternCompiler)
    (source : String) :
    classifyStringPattern compilePattern source = .admitted ↔
      (∃ wholeValueMatches,
        compilePattern source = .compiled wholeValueMatches) ∧
        kernelPatternSourceAllowed source = true := by
  cases compiled : compilePattern source with
  | rejected | unsupported =>
      simp [classifyStringPattern, compiled]
  | compiled wholeValueMatches =>
      cases allowed : kernelPatternSourceAllowed source <;>
        simp [classifyStringPattern, compiled, allowed]

/-- Once both admission facts hold for a nonempty source, the convenience boundary delegates exactly to the existing resolved matcher semantics. -/
theorem evalAdmittedStringPattern_success (compilePattern : StringPatternCompiler)
    (source : String) (op : StringPatternOp) (wholeValueMatches : String → Bool)
    (operand : SimpleComparisonOperand String)
    (compiled : compilePattern source = .compiled wholeValueMatches)
    (allowed : kernelPatternSourceAllowed source = true)
    (nonempty : source.isEmpty = false) :
    evalAdmittedStringPattern compilePattern source op operand =
      .ok (op.evalResolved wholeValueMatches operand) := by
  let admitted : AdmittedStringPattern compilePattern := {
    source
    wholeValueMatches
    compiledSource := compiled
    kernelSourceAllowed := allowed
  }
  have admittedEq :
      admitStringPattern compilePattern source = .ok admitted := by
    unfold admitStringPattern
    split
    next hCompiled =>
      simp_all
    next hCompiled =>
      simp_all
    next matcher hCompiled =>
      have matcherEq : matcher = wholeValueMatches :=
        PatternCompilation.compiled.inj (hCompiled.symm.trans compiled)
      subst matcher
      simp [allowed, admitted]
  simp only [evalAdmittedStringPattern, admittedEq, admitted,
    AdmittedStringPattern.evalResolved, AdmittedStringPattern.checkExecution, nonempty, Bool.false_eq_true, ↓reduceIte, Except.mapError]

/-- Admission cannot introduce omission polarity; the admitted wrapper inherits the resolved consumer's stronger law. -/
theorem admittedStringPattern_fired_is_value
    (admitted : AdmittedStringPattern compilePattern)
    (op : StringPatternOp)
    (operand : SimpleComparisonOperand String) (polarity : Polarity)
    (fired : admitted.evalResolved op operand = .ok (.fired polarity)) :
    polarity = .value := by
  unfold AdmittedStringPattern.evalResolved AdmittedStringPattern.checkExecution at fired
  split at fired
  next => simp at fired
  next =>
    simp at fired
    exact stringPattern_evalResolved_fired_is_value op admitted.wholeValueMatches operand polarity fired

/-- Formal-input failure suppresses a computation call even when the authored source is empty. -/
@[simp]
theorem admittedStringPattern_computation_formal_precedence
    (admitted : AdmittedStringPattern compilePattern) (op : StringPatternOp) (cause : FormalCause) :
    admitted.evalComputationResolved op (.unknown cause) = .ok (.poison cause) := by
  rfl

/-- Java rejection and the Kernel's additional source gate retain their local
stage while projecting to the same measured external diagnostic class; a host limit projects to none. -/
@[simp]
theorem stringPatternCondition_pattern_diagnostic
    (error : PatternAdmissionError) (kernelStage : error ≠ .hostUnsupported) :
    StringPatternConditionElabError.diagnostic? (.pattern error) =
      some .invalidPattern := by
  cases error <;> simp_all [StringPatternConditionElabError.diagnostic?]

/-- Every non-String kind in the measured scalar matrix reaches one external diagnostic class. DateRange remains deliberately unmapped because that matrix did not measure it. -/
@[simp]
theorem stringPatternCondition_fieldKind_diagnostic
    (path : List String) (kind : SurfaceScalarKind)
    (notString : kind ≠ .string) (notDateRange : kind ≠ .dateRange) :
    StringPatternConditionElabError.diagnostic? (.fieldKind path kind) =
      some .invalidTypeForPatternComparison := by
  cases kind with
  | number | boolean | confirm | enumeration => rfl
  | string => contradiction
  | temporal temporalKind => cases temporalKind <;> rfl
  | dateRange => contradiction

end A12Kernel
