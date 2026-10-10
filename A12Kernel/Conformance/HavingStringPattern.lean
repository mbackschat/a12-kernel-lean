import A12Kernel.Semantics.Correlation

namespace A12Kernel.Conformance.HavingStringPattern
open A12Kernel

private def digits : CompiledStringPattern := {
  compilePattern := fun source => if source == asciiDigitsPatternSource then some matchesAsciiDigitsPattern else none
  pattern := {
    source := asciiDigitsPatternSource, wholeValueMatches := matchesAsciiDigitsPattern,
    compiledSource := rfl, kernelSourceAllowed := by decide } }

private def condition (op : StringPatternOp) (origin : HavingOrigin := .inner) : CorrelatedHaving :=
  .leaf (.stringPattern op { origin, field := 1 } digits)
private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def text (value : String) : CheckedCell := { rawPresent := true, parsed := some (.str value), findings := [] }
private def context (cell : CheckedCell) : CorrelationContext := {
  read := fun env field => if field == 2 then text "filled" else if env == frame.innerEnv then cell else text "abc" }
private def computation (tree : CorrelatedHaving) (cell : CheckedCell) : Sum CorrelationRuntimeFault ComputationConditionResult :=
  match tree.evalComputationIn (context cell) frame with
  | .ok value => .inr value
  | .error error => .inl error

example : (condition .matched).evalTruthIn (context (text "123")) frame = .tru ∧
    (condition .violated).evalTruthIn (context (text "123")) frame = .fls ∧
    (condition .matched .outer).evalTruthIn (context (text "123")) frame = .fls ∧
    (condition .violated .outer).evalTruthIn (context (text "123")) frame = .tru ∧
    (condition .matched).evalTruthIn (context (text "x123")) frame = .fls := by native_decide

example : [StringPatternOp.matched, .violated].all (fun op => decide (
    (condition op).evalTruthIn (context { rawPresent := false, parsed := none, findings := [] }) frame = .fls ∧
    computation (condition op) { rawPresent := false, parsed := none, findings := [] } = .inr .notTrue ∧
    (condition op).evalTruthIn (context { (text "123") with findings := [.malformed] }) frame = .unknown ∧
    computation (condition op) { (text "123") with findings := [.malformed] } = .inr (.poison .malformed))) = true := by native_decide

private def falseLeaf : CorrelatedHaving := .presence .notFilled { origin := .inner, field := 2 }
example : computation (.and falseLeaf (condition .matched)) { (text "123") with findings := [.malformed] } = .inr .notTrue ∧
    computation (.and (condition .matched) falseLeaf) { (text "123") with findings := [.malformed] } = .inr (.poison .malformed) := by native_decide

example : (condition .matched).fieldIds = [1] ∧
    (condition .matched).markedFieldIds = [] ∧
    (condition .violated .outer).fieldIds = [1] ∧
    (condition .violated .outer).markedFieldIds = [1] := by native_decide

private def emptyPattern : CompiledStringPattern := {
  compilePattern := fun _ => some String.isEmpty
  pattern := {
    source := "", wholeValueMatches := String.isEmpty,
    compiledSource := rfl, kernelSourceAllowed := by decide } }

private def emptyCondition (op : StringPatternOp) : CorrelatedHaving :=
  .leaf (.stringPattern op { origin := .inner, field := 1 } emptyPattern)

example : [StringPatternOp.matched, .violated].all (fun op =>
    [text "123", { rawPresent := false, parsed := none, findings := [] }].all (fun cell => decide (
      ((emptyCondition op).evalTruthInResolving (context cell).asResolving frame).toOption = none ∧
      computation (emptyCondition op) cell = .inl .valueFailure ∧
      computation (.and falseLeaf (emptyCondition op)) cell = .inr .notTrue ∧
      computation (.and (emptyCondition op) falseLeaf) cell = .inl .valueFailure))) = true := by
  native_decide

example : [StringPatternOp.matched, .violated].all (fun op => decide (
    computation (emptyCondition op) { (text "123") with findings := [.malformed] } = .inr (.poison .malformed) ∧
    ((emptyCondition op).evalTruthInResolving
      (context { (text "123") with findings := [.malformed] }).asResolving frame).toOption = none)) = true := by
  native_decide

end A12Kernel.Conformance.HavingStringPattern
