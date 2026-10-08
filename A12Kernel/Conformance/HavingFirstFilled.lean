import A12Kernel.Semantics.HavingFirstFilled

namespace A12Kernel.Conformance.HavingFirstFilled
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def number (value : Rat) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def reference (field : FieldId) (origin : HavingOrigin := .inner) : HavingNumberRef := {
  origin, field := { id := field, info := { scale := 0, signed := false } } }
private def direct : List (HavingFieldListSlot HavingNumberRef) := [
  .direct (reference 1), .direct (reference 2 .outer)]
private def extent : HavingEntityExtent := .starredGroup ["Form", "Rows"] {
  axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def context : ResolvingCorrelationContext CorrelationRuntimeFault := {
  ({ read := fun _ _ => empty } : CorrelationContext).asResolving with
  read := fun env field => if field == 1 && env == frame.innerEnv then pure (number 7)
    else .error .valueFailure }
private def result (phase : Phase) (context : ResolvingCorrelationContext CorrelationRuntimeFault)
    (slots : List (HavingFieldListSlot HavingNumberRef) := direct) : Sum CorrelationRuntimeFault NumericOperand :=
  match A12Kernel.HavingFirstFilled.number phase context frame slots with
  | .ok value => .inr value
  | .error error => .inl error

example : [Phase.validation, .computation].all (fun phase =>
    result phase context == .inr (.value 7 .fixed) &&
    result phase { context with read := fun _ field => if field == 1 then pure invalid else .error .valueFailure } ==
      .inr (.unknown .malformed) &&
    result phase { context with read := fun _ field => if field == 1 then pure empty else .error .valueFailure } ==
      .inl .valueFailure) = true := by native_decide

example : result .validation { context with
      read := fun env field =>
        if field == 1 then pure empty
        else if env == frame.outerEnv then pure (number 8) else .error .valueFailure } =
      .inr (.value 8 .both) ∧
    result .validation { context with read := fun _ _ => pure empty } = .inr (.value 0 .both) ∧
    result .validation { context with read := fun _ _ => pure { empty with findings := [.required] } } =
      .inr (.unknown .required) ∧
    result .computation { context with
      read := fun _ field => if field == 1 then
        pure { empty with findings := [.required] } else pure (number 8) } = .inr (.value 8 .both) := by native_decide

private def emptyFirstDeclaration : ResolvingCorrelationContext CorrelationRuntimeFault := { context with
  read := fun _ field => if field == 2 then pure (number 8) else .error .valueFailure
  groups := some {
    validation := fun _ _ => .error .valueFailure
    computation := fun _ _ => .error .valueFailure
    fieldExtent := fun _ env _ field => pure (if field == 1 then [] else [env], true) } }
example : result .validation emptyFirstDeclaration
      [.extent extent [reference 1, reference 2]] = .inr (.value 8 .fixed) ∧
    result .validation emptyFirstDeclaration
      [.extent extent [reference 1], .direct (reference 2 .outer)] = .inr (.value 8 .both) := by native_decide

private def prefixWins : ResolvingCorrelationContext CorrelationRuntimeFault := { context with
  groups := some {
    validation := fun _ _ => .error .valueFailure
    computation := fun _ _ => .error .valueFailure
    fieldExtent := fun _ env _ field => if field == 1 then pure ([env, frame.outerEnv], true)
      else .error .valueFailure } }
example : result .validation prefixWins [.extent extent [reference 1, reference 2]] =
    .inr (.value 7 .fixed) := by native_decide

end A12Kernel.Conformance.HavingFirstFilled
