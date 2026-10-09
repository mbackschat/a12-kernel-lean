import A12Kernel.Semantics.HavingTypeValidity
import A12Kernel.Semantics.HavingGroupPresence

namespace A12Kernel.Conformance.HavingTypeValidity
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def reference (origin : HavingOrigin := .inner) : HavingPresenceRef := { origin, field := 1 }
private def world (registered : Bool) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if registered && name == "Code" then some (fun value context =>
      if value == "kept" && context == explicitCustomFieldValidationContext then none
      else some { projectCode := "TYPE_REJECTED" }) else none }
private def context (cell : CheckedCell) (registered : Option Bool) : CorrelationContext := {
  read := fun env _ => if env == frame.innerEnv then cell else
    { rawPresent := true, parsed := some (.str "dropped"), findings := [] }
  world := registered.map world }
private def value : CheckedCell := { rawPresent := true, parsed := some (.str "kept"), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def malformed : CheckedCell := { value with findings := [.malformed] }

private def toOutcome : Except ε α → Sum ε α
  | .error error => .inl error
  | .ok value => .inr value

private def validation (op : CustomFieldValidityOp) (cell : CheckedCell)
    (registered : Option Bool) (origin : HavingOrigin := .inner) : Sum CorrelationRuntimeFault Verdict :=
  toOutcome (evalHavingTypeValidityValidation op (reference origin) "Code"
    (context cell registered).asResolving frame)
private def computation (op : CustomFieldValidityOp) (cell : CheckedCell)
    (registered : Option Bool) (origin : HavingOrigin := .inner) : Sum CorrelationRuntimeFault ComputationConditionResult :=
  toOutcome (evalHavingTypeValidityComputation op (reference origin) "Code"
    (context cell registered).asResolving frame)

example : validation .valid value (some true) = toOutcome (Except.ok (ε := CorrelationRuntimeFault) (Verdict.fired .value)) ∧
    validation .invalid value (some true) = toOutcome (Except.ok (ε := CorrelationRuntimeFault) Verdict.notFired) ∧
    validation .valid value (some true) .outer = toOutcome (Except.ok (ε := CorrelationRuntimeFault) Verdict.notFired) ∧
    validation .invalid value (some true) .outer = toOutcome (Except.ok (ε := CorrelationRuntimeFault) (Verdict.fired .value)) := by native_decide

example : [CustomFieldValidityOp.valid, .invalid].all (fun op => decide (
    validation op value (some false) = toOutcome (Except.error (α := Verdict) CorrelationRuntimeFault.typeValidityValueFailure) ∧
    computation op value (some false) = toOutcome (Except.error (α := ComputationConditionResult) CorrelationRuntimeFault.typeValidityValueFailure) ∧
    validation op empty none = toOutcome (Except.ok (ε := CorrelationRuntimeFault) Verdict.unknown) ∧
    computation op empty none = toOutcome (Except.ok (ε := CorrelationRuntimeFault) ComputationConditionResult.notTrue) ∧
    validation op malformed none = toOutcome (Except.ok (ε := CorrelationRuntimeFault) Verdict.unknown) ∧
    computation op malformed none = toOutcome (Except.ok (ε := CorrelationRuntimeFault) (ComputationConditionResult.poison .malformed)) ∧
    validation op value none = toOutcome (Except.error (α := Verdict) CorrelationRuntimeFault.worldUnavailable) ∧
    computation op value none = toOutcome (Except.error (α := ComputationConditionResult) CorrelationRuntimeFault.worldUnavailable))) = true := by native_decide

example : computation .valid value (some true) =
    toOutcome (Except.ok (ε := CorrelationRuntimeFault) ComputationConditionResult.holds) ∧
    computation .invalid value (some true) =
    toOutcome (Except.ok (ε := CorrelationRuntimeFault) ComputationConditionResult.notTrue) ∧
    validation .valid { value with parsed := some (.enum "kept") } (some true) = validation .valid value (some true) ∧
    computation .valid { value with parsed := some (.enum "kept") } (some true) = computation .valid value (some true) := by native_decide

end A12Kernel.Conformance.HavingTypeValidity
