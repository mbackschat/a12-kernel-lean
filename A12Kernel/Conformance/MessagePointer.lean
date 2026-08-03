import A12Kernel.Semantics.MessagePointer
import A12Kernel.Semantics.ValidationRule
import A12Kernel.Semantics.CustomFieldFormalMessage
import A12Kernel.Semantics.CustomCondition

/-! # Shared formal-message pointer locks -/

namespace A12Kernel.Conformance.MessagePointer

open A12Kernel

private def address : CellAddr :=
  { field := 7, path := [2, 4] }

private def partialPointer : A12Kernel.MessagePointer :=
  { field := 7, coordinates := [.unknown, .concrete 4] }

/- Exact field-instance addresses embed losslessly into the shared message-pointer domain. -/
example :
    (A12Kernel.MessagePointer.ofCellAddr address).toCellAddr? = some address := by
  native_decide

/- Validation and registered-field formal messages retain the same shared pointer, including partial coordinates. -/
example :
    let validation : FlatRuleMessage := {
      errorAddress := partialPointer
      errorCode := "VALIDATION"
      severity := .error
      messageType := .value
      text := { text := "validation" }
    }
    let customField : CustomFieldFormalMessage := {
      errorAddress := partialPointer
      errorCode := "CUSTOM"
      severity := .error
      messageType := .value
      text := { text := "custom" }
    }
    validation.errorAddress = customField.errorAddress := by
  native_decide

/- Custom-condition invocation fixes its error channel to the shared pointer instead of allowing an unrelated shape. -/
example :
    let invocation : CustomConditionInvocation Bool Unit Unit := {
      data := true
      relevance := .all
      formallyIncorrect := ()
      errorPointer := partialPointer
    }
    invocation.errorPointer = partialPointer := by
  native_decide

/- Wildcard and unknown coordinates remain distinct values and neither masquerades as an exact field instance. -/
example :
    let wildcard : A12Kernel.MessagePointer :=
      { field := 7, coordinates := [.wildcard, .concrete 4] }
    let unknown : A12Kernel.MessagePointer :=
      { field := 7, coordinates := [.unknown, .concrete 4] }
    wildcard != unknown ∧
      wildcard.toCellAddr? = none ∧
      unknown.toCellAddr? = none := by
  native_decide

end A12Kernel.Conformance.MessagePointer
