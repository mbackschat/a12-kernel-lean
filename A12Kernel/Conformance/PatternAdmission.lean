import A12Kernel.Elaboration.StringPattern

/-! # A12Kernel.Conformance.PatternAdmission — two-stage pattern admission locks

These examples inject only the Java-compilation decision. They lock the independently implemented finite kernel source gate, its observed uppercase-`\P` addition, rejection precedence, and delegation to the existing normalized whole-value matcher consumer.
-/

namespace A12Kernel.Conformance.PatternAdmission

open A12Kernel

private def exactA (value : String) : Bool := value == "A"

private def compilePattern (source : String) : Option (String → Bool) :=
  if source == "(" || source == "[" then none else some exactA

private def compileExactSource (source : String) : Option (String → Bool) :=
  some fun value => value == source

private def admittedVerdict? :
    Except PatternAdmissionError Verdict → Option Verdict
  | .error _ => none
  | .ok verdict => some verdict

example : classifyStringPattern compilePattern "(" =
    .rejected .javaSyntax := by native_decide

example : classifyStringPattern compilePattern "a++" =
    .rejected .kernelRestriction := by native_decide

example : ["a?+", "a++", "a}+", "a*+"].all
    (fun source => classifyStringPattern compilePattern source ==
      .rejected .kernelRestriction) = true := by native_decide

example : classifyStringPattern compilePattern "(?<=a)b" =
    .rejected .kernelRestriction := by native_decide

example : classifyStringPattern compilePattern "(?<name>a)" =
    .rejected .kernelRestriction := by native_decide

example : classifyStringPattern compilePattern "(?>a)" =
    .rejected .kernelRestriction := by native_decide

example : ["\\A", "\\G", "\\Z", "\\z", "\\a", "\\e", "\\p{L}", "\\Q", "\\E"].all
    (fun source => !kernelPatternSourceAllowed source) = true := by native_decide

example : classifyStringPattern compilePattern "\\P{L}" =
    .rejected .kernelRestriction := by native_decide

example : classifyStringPattern compilePattern "[a[b]c]" =
    .rejected .kernelRestriction := by native_decide

example : ["a+", "(?=a)a", "(?!a)b", "(?i)abc", "\\R", "\\h", "[a\\[b]", "[a][b]"].all
    (fun source => classifyStringPattern compilePattern source == .admitted) = true := by native_decide

/- The document-model branch admits the empty source; semantic empty input is still excluded by the resolved operand classifier. -/
example : classifyStringPattern compilePattern "" = .admitted := by native_decide

example : classifyStringPattern (fun _ => none) "a++" =
    .rejected .javaSyntax := by native_decide

/- The matcher is the exact capability returned for this source; evaluation cannot substitute a function compiled from another pattern. -/
example : evalAdmittedStringPattern compilePattern "A" .matched
    (.value "A" true) = .ok (.fired .value) := by rfl

example : evalAdmittedStringPattern compilePattern "a++" .matched
    (.value "A" true) = .error .kernelRestriction := by rfl

/- A second source predicts the old caller-supplied-matcher failure class: each admitted value retains its own compiler result. -/
example :
    admittedVerdict? (evalAdmittedStringPattern compileExactSource "A" .matched
        (.value "A" true)) = some (.fired .value) ∧
      admittedVerdict? (evalAdmittedStringPattern compileExactSource "B" .matched
        (.value "A" true)) = some .notFired := by
  native_decide

end A12Kernel.Conformance.PatternAdmission
