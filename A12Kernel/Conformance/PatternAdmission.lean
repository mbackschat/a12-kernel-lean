import A12Kernel.Elaboration.StringPattern

/-! # A12Kernel.Conformance.PatternAdmission — two-stage pattern admission locks

These examples inject only the Java-compilation decision. They lock the independently implemented finite kernel source gate, its observed uppercase-`\P` addition, rejection precedence, and delegation to the existing normalized whole-value matcher consumer.
-/

namespace A12Kernel.Conformance.PatternAdmission

open A12Kernel

private def javaCompiles (source : String) : Bool := source != "(" && source != "["

example : classifyStringPattern javaCompiles "(" =
    .rejected .javaSyntax := by native_decide

example : classifyStringPattern javaCompiles "a++" =
    .rejected .kernelRestriction := by native_decide

example : ["a?+", "a++", "a}+", "a*+"].all
    (fun source => classifyStringPattern javaCompiles source ==
      .rejected .kernelRestriction) = true := by native_decide

example : classifyStringPattern javaCompiles "(?<=a)b" =
    .rejected .kernelRestriction := by native_decide

example : classifyStringPattern javaCompiles "(?<name>a)" =
    .rejected .kernelRestriction := by native_decide

example : classifyStringPattern javaCompiles "(?>a)" =
    .rejected .kernelRestriction := by native_decide

example : ["\\A", "\\G", "\\Z", "\\z", "\\a", "\\e", "\\p{L}", "\\Q", "\\E"].all
    (fun source => !kernelPatternSourceAllowed source) = true := by native_decide

example : classifyStringPattern javaCompiles "\\P{L}" =
    .rejected .kernelRestriction := by native_decide

example : classifyStringPattern javaCompiles "[a[b]c]" =
    .rejected .kernelRestriction := by native_decide

example : ["a+", "(?=a)a", "(?!a)b", "(?i)abc", "\\R", "\\h", "[a\\[b]", "[a][b]"].all
    (fun source => classifyStringPattern javaCompiles source == .admitted) = true := by native_decide

example : classifyStringPattern (fun _ => false) "a++" =
    .rejected .javaSyntax := by native_decide

private def exactA (value : String) : Bool := value == "A"

example : evalAdmittedStringPattern javaCompiles "A" .matched exactA
    (.value "A" true) = .ok (.fired .value) := by rfl

example : evalAdmittedStringPattern javaCompiles "a++" .matched exactA
    (.value "A" true) = .error .kernelRestriction := by rfl

end A12Kernel.Conformance.PatternAdmission
