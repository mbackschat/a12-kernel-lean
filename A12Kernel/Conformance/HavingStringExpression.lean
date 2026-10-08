import A12Kernel.Elaboration.HavingStringExpression

namespace A12Kernel.Conformance.HavingStringExpression

private def bad : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def value (value : Value) : CheckedCell := { rawPresent := true, parsed := some value, findings := [] }
private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def ref (field : FieldId) (origin : HavingOrigin := .inner) : HavingStringSource := .field { origin, field }
private def source : StringExpr HavingStringSource := StringExpr.concat (.field (ref 1)) (.field (ref 2 .outer))
private def context (cell : CheckedCell) : ResolvingCorrelationContext String := {
  read := fun env field => if env == frame.innerEnv && field == 1 then .ok cell else .error "captured read"
  numberText := fun _ _ => some "1.5"
  storedText := fun _ _ => some "01.50"
  bindingError := fun _ => "binding"
  stringExpressionUnavailable := "String expression unavailable"
  unsupportedDateCalendar := "calendar"
  temporalValueFailure := "value"
  worldUnavailable := "world"
  typeValidityValueFailure := "type"
  groupUnavailable := fun _ => "extent"
  storedTextUnavailable := fun _ => "number text unavailable" }

private def observe (expression : StringExpr HavingStringSource) (phase : Phase)
    (ctx : ResolvingCorrelationContext String) : String ⊕ ((String × Bool) ⊕ Option FormalCause) :=
  match HavingStringComparison.operand expression phase ctx frame with
  | .error error => .inl error
  | .ok (.value text given) => .inr (.inl (text, given))
  | .ok .notEvaluated => .inr (.inr none)
  | .ok (.unknown cause) => .inr (.inr (some cause))

example : observe source .validation (context bad) = .inl "captured read" ∧
    observe source .computation (context bad) = .inr (.inr (some .malformed)) := by native_decide

private def comparison : HavingStringComparison := {
  operator := .equal, left := .field (ref 1), right := .field (ref 2 .outer) }

example : (comparison.evalValidationRead (context bad) frame).isOk = false ∧
    (comparison.evalComputationRead (context bad) frame).toOption.any
      (fun | .poison .malformed => true | _ => false) = true := by native_decide

example : [Phase.validation, .computation].all (fun phase =>
    observe (.fieldValueAsString (ref 1)) phase (context (value (.num (3/2)))) ==
      .inr (.inl ("1.5", true)) &&
    observe (.fieldValueAsString (ref 1)) phase
      { context (value (.num (3/2))) with numberText := fun _ _ => none } ==
      .inl "number text unavailable") = true := by native_decide

example : [Phase.validation, .computation].all (fun phase =>
    observe (.range (ref 1) 1 1) phase (context (value (.str "😀"))) ==
      .inl "String expression unavailable" &&
    observe (.range (ref 1) 1 2) phase (context (value (.str "😀"))) ==
      .inr (.inl ("😀", true))) = true := by native_decide

example : observe (.concat (.field (ref 1)) (.literal "x")) .computation
    (context { rawPresent := false, parsed := none, findings := [] }) = .inr (.inl ("x", false)) := by native_decide

end A12Kernel.Conformance.HavingStringExpression
