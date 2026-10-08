import A12Kernel.Elaboration.HavingSelectedComparison

namespace A12Kernel.Conformance.HavingSelectedComparison
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def falseCell : CheckedCell := { rawPresent := true, parsed := some (.bool false), findings := [] }
private def malformed : CheckedCell := { empty with rawPresent := true, findings := [.malformed] }
private def reference (field : FieldId) (origin : HavingOrigin := .inner) : HavingSelectedRef := .boolean origin { id := field }
private def source : HavingSelectedOperand := .firstFilled [.direct (reference 1), .direct (reference 2 .outer)]
private def context (cell : CheckedCell) : ResolvingCorrelationContext CorrelationRuntimeFault := {
  ({ read := fun _ _ => empty } : CorrelationContext).asResolving with
  read := fun env field => if field == 1 && env == frame.innerEnv then pure cell else .error .valueFailure }
private def observed (value : Except CorrelationRuntimeFault α) : Sum CorrelationRuntimeFault α :=
  match value with | .ok result => .inr result | .error error => .inl error
private def comparison : HavingSelectedComparison := { operator := .equal, left := source, right := .boolean false }

example : observed (comparison.evalValidationRead (context falseCell) frame) = .inr (.fired .value) ∧
    observed (comparison.evalComputationRead (context falseCell) frame) = .inr .holds ∧
    observed (source.evaluate .validation (context empty) frame) = .inl .valueFailure ∧
    observed (source.evaluate .validation (context malformed) frame) = .inr (.unknown .malformed) ∧
    observed ({ comparison with right := .field (reference 3) }.evalValidationRead (context malformed) frame) = .inl .valueFailure ∧
    observed ({ comparison with right := .field (reference 3) }.evalComputationRead (context malformed) frame) =
      .inr (.poison .malformed) := by native_decide

private def emptyPrefix : ResolvingCorrelationContext CorrelationRuntimeFault := { context empty with
  read := fun _ field => pure (if field == 1 then empty else falseCell) }
example : observed (source.evaluate .validation emptyPrefix frame) = .inr (.value (.bool false) false) ∧
    observed (comparison.evalValidationRead emptyPrefix frame) = .inr (.fired .omission) ∧
    observed (comparison.evalComputationRead emptyPrefix frame) = .inr .holds := by native_decide

private def enumField : FlatFieldDecl := {
  id := 1, name := "Token", groupPath := ["Form", "Values"]
  policy := { kind := .enumeration }
  enumeration := some { storedTokens := ["x"], categories := [{ name := "Label", tokens := ["y"] }] } }
private def enumModel : FlatModel := { fields := [enumField] }
private def enumRef (projected : Bool) : HavingSelectedRef := .text {
  origin := .inner
  operand := match enumField.toEnumerationTextFieldComparison?
    (if projected then .category "Label" else .stored) with
    | some (operand, _) => operand
    | none => .string { id := 1 } }
private def group : HavingEntityExtent := .group {
  path := ["Form", "Values"], origin := .path, boundRepeatableScope := [] }
private def groupComparison (projected : Bool) : HavingSelectedComparison := {
  operator := .equal, left := .firstFilled [.extent group [enumRef projected]], right := .text "x" }
example : (groupComparison false).wellFormed enumModel [] [] = true ∧
    (groupComparison true).wellFormed enumModel [] [] = false ∧
    ({ groupComparison false with left := .firstFilled [.direct (enumRef true), .direct (enumRef false)] }).wellFormed
      enumModel [] [] = true := by native_decide

end A12Kernel.Conformance.HavingSelectedComparison
