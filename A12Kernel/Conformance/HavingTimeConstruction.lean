import A12Kernel.Elaboration.CorrelationWellFormed

namespace A12Kernel.Conformance.HavingTimeConstruction

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def observed (value : Except CorrelationRuntimeFault α) : Sum CorrelationRuntimeFault α :=
  match value with | .ok result => .inr result | .error error => .inl error
private def number (value : Rat) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { emptyCell with rawPresent := true, findings := [.malformed] }
private def frame : CorrelationFrame := { outerEnv := [(10, 2)], innerEnv := [(10, 1)] }
private def numeric (id : FieldId) : ResolvedTimeConstructionSource := .number { id, info := { scale := 0, signed := false } }
private def expression (components : HavingTimeComponents := .hour (.direct .inner (numeric 1))) : HavingTemporalExpression := {
  core := .atom (.timeConstruction components), profile := .utc, baseYear := none }
private def context (hour : CheckedCell) : CorrelationContext := {
  read := fun env id => if id == 1 then hour else number (if env == frame.outerEnv then 30 else 45) }
private def hourPart : HavingNumericAtom := .temporalExpressionPart (.time .hour) expression

example : observed (expression.evaluate .validation (context (number 24)).asResolving frame) =
      .inr (.value .noValue true) ∧
    observed (expression.evaluate .validation (context emptyCell).asResolving frame) = .inr (.value .noValue false) ∧
    observed (hourPart.readComputationResolving (context (number 24)).asResolving frame) = .inr (.value 0) ∧
    observed (hourPart.readComputationResolving (context invalid).asResolving frame) = .inr (.poison .malformed) ∧
    observed ((expression .empty).evaluate .computation (context invalid).asResolving frame) =
      .inr (.value (.time { hour := 0, minute := 0, second := 0, valid := by decide }) true) := by native_decide

example : observed (hourPart.readValidationResolving (context (number 24)).asResolving frame) =
      .inr (.ok (.value 0 .fixed)) ∧
    observed (hourPart.readValidationResolving (context emptyCell).asResolving frame) =
      .inr (.ok (.value 0 .both)) := by native_decide

private def required : CheckedCell := { emptyCell with findings := [.required] }
example : observed (expression.evaluate .validation (context required).asResolving frame) = .inr (.unknown .required) ∧
    observed (expression.evaluate .computation (context required).asResolving frame) = .inr (.value .noValue false) ∧
    observed (expression.evaluate .computation (context (number (1/2))).asResolving frame) = .inr (.unknown .malformed) := by native_decide

private def conversion : HavingTimeComponents := .minute (.direct .inner (numeric 1)) (.direct .outer (.string { id := 2 }))
private def conversionContext (hour : CheckedCell := invalid) : CorrelationContext := {
  read := fun _ id => if id == 1 then hour else { rawPresent := true, parsed := some (.str "ab"), findings := [] } }
example : observed ((expression conversion).evaluate .validation (conversionContext).asResolving frame) = .inl .valueFailure ∧
    observed ((expression conversion).evaluate .computation (conversionContext).asResolving frame) = .inr (.unknown .malformed) ∧
    observed ((expression conversion).evaluate .computation (conversionContext emptyCell).asResolving frame) = .inl .valueFailure ∧
    observed ((expression (.second (.direct .inner (.constant 8)) (.direct .inner (numeric 1)) (.direct .outer (.string { id := 2 })))).evaluate
      .validation (conversionContext).asResolving frame) = .inl .valueFailure ∧
    observed ((expression (.second (.direct .inner (.constant 8)) (.direct .inner (numeric 1)) (.direct .outer (.string { id := 2 })))).evaluate
      .computation (conversionContext).asResolving frame) = .inr (.unknown .malformed) := by native_decide

private def clock : HavingTimeComponents := .minute (.direct .inner (numeric 1)) (.direct .inner (.nowExtractor .minute))
example : observed ((expression clock).evaluate .validation (context invalid).asResolving frame) = .inl .worldUnavailable ∧
    observed ((expression clock).evaluate .computation (context invalid).asResolving frame) = .inr (.unknown .malformed) ∧
    observed ((expression clock).evaluate .computation (context emptyCell).asResolving frame) = .inl .worldUnavailable := by native_decide

private def mixed : HavingTimeComponents := .second (.direct .inner (numeric 1)) (.direct .outer (numeric 2)) (.direct .inner (numeric 3))
private def collapsed : HavingTimeComponents := .second (.direct .inner (numeric 1)) (.direct .inner (numeric 2)) (.direct .inner (numeric 3))
example : observed ((expression mixed).evaluate .computation (context (number 8)).asResolving frame) =
      .inr (.value (.time { hour := 8, minute := 30, second := 45, valid := by decide }) true) ∧
    observed ((expression collapsed).evaluate .computation (context (number 8)).asResolving frame) =
      .inr (.value (.time { hour := 8, minute := 45, second := 45, valid := by decide }) true) ∧
    (HavingNumericAtom.temporalExpressionPart (.time .hour) (expression mixed)).fieldOrigins =
      [(.inner, 1), (.outer, 2), (.inner, 3)] := by native_decide

private def comparison : CorrelatedHaving := .leaf (.temporalExpression {
  operator := .equal, left := expression mixed, right := expression .empty })
example : comparison.fieldIds = [1, 2, 3] ∧ comparison.markedFieldIds = [2] := by native_decide

private def model : FlatModel := {
  fields := [1, 2, 3].map fun id => {
    id, name := toString id, groupPath := ["Rows"], repeatableScope := [10]
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maxStoredLength := some 2 } }
  repeatableGroups := [{ level := 10, path := ["Rows"], repeatability := some 2 }] }
example : (expression mixed).wellFormed model [10] [10] = true ∧
    (expression mixed).wellFormed model [10] [] = false ∧
    (expression mixed).wellFormed model [] [10] = false ∧
    (expression (.hour (.direct .inner (.number { id := 1, info := { scale := 1, signed := false } })))).wellFormed model [10] [] = false ∧
    (expression (.hour (.direct .inner (.constant 24)))).wellFormed model [] [] = false ∧
    (expression (.minute (.direct .inner (.constant 8)) (.direct .inner (.constant 60)))).wellFormed model [] [] = false ∧
    (expression (.hour (.direct .inner (.nowExtractor .minute)))).wellFormed model [] [] = false ∧
    ({ expression with profile := .europeBerlin }).wellFormed model [10] [] = false ∧
    (expression .empty).wellFormed model [] [] = true := by native_decide

private def nested (tail : Bool := false) : HavingTemporalExpression :=
  expression (if tail then .minute (.expression .hour expression.core) (.direct .outer (.string { id := 2 }))
    else .hour (.expression .hour expression.core))

example : observed (nested.evaluate .validation (context emptyCell).asResolving frame) = .inr (.value .noValue false) ∧
    observed (nested.evaluate .computation (context (number 24)).asResolving frame) =
      .inr (.value (.time { hour := 0, minute := 0, second := 0, valid := by decide }) true) ∧
    observed (nested.evaluate .validation (context required).asResolving frame) = .inr (.unknown .required) ∧
    observed (nested.evaluate .computation (context required).asResolving frame) = .inr (.value .noValue false) ∧
    observed ((nested true).evaluate .validation conversionContext.asResolving frame) = .inl .valueFailure ∧
    observed ((nested true).evaluate .computation conversionContext.asResolving frame) = .inr (.unknown .malformed) ∧
    observed ((nested true).evaluate .computation (conversionContext emptyCell).asResolving frame) = .inl .valueFailure := by native_decide

example : nested.wellFormed model [10] [] = true ∧
    (expression (.hour (.expression .minute expression.core))).wellFormed model [10] [] = false ∧
    (expression (.hour (.expression .hour (.atom (.timeLiteral { hour := 8, minute := 0, second := 0, valid := by decide }))))).wellFormed model [] [] = false ∧
    ((expression (.hour (.expression .hour (expression mixed).core))).references.map fun ref => (ref.origin, ref.fieldId)) =
      [(.inner, 1), (.outer, 2), (.inner, 3)] := by native_decide

example : (expression (.hour (.expression .hour (expression (.hour (.direct .inner (.constant 24)))).core))).wellFormed model [] [] = false := by native_decide

end A12Kernel.Conformance.HavingTimeConstruction
