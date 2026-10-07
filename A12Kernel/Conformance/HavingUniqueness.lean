import A12Kernel.Semantics.Correlation

namespace A12Kernel.Conformance.HavingUniqueness
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def number (value : Rat) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def numbers (ids : List FieldId) : A12Kernel.HavingUniqueness := .number (ids.map fun id => {
  origin := .inner, field := { id, info := { scale := if id == 2 then 2 else 0, signed := true } } })
private def cells (second : CheckedCell) : CorrelationContext := {
  read := fun _ id => if id == 2 then second else number 5 }
private def result (source : A12Kernel.HavingUniqueness) (phase : Phase) (context : CorrelationContext) :
    Sum CorrelationRuntimeFault ComputationConditionResult :=
  match source.evalRead phase context.asResolving frame with
  | .ok value => .inr value
  | .error error => .inl error

example : result (numbers [1, 2, 3]) .validation (cells invalid) = .inr .holds ∧
    result (numbers [1, 2, 3]) .computation (cells invalid) = .inr (.poison .malformed) ∧
    result (numbers [1, 2]) .validation (cells invalid) = .inr .notTrue ∧
    result (numbers [1, 2]) .validation { read := fun _ _ => invalid } = .inr .notTrue ∧
    result (numbers [1, 2, 3]) .computation (cells emptyCell) = .inr .holds ∧
    result (numbers [1, 2]) .computation (cells (number 5)) = .inr .holds := by native_decide

private def tokenSource : A12Kernel.HavingUniqueness := .token [
  { origin := .inner, operand := .string { id := 1 } },
  { origin := .outer, operand := .string { id := 2 } }]
private def tokenContext : CorrelationContext := {
  read := fun env id => {
    rawPresent := true, findings := []
    parsed := some (.str (if (env == frame.innerEnv && id == 1) || (env == frame.outerEnv && id == 2) then "same" else "other")) } }
example : result tokenSource .validation tokenContext = .inr .holds ∧
    result tokenSource .computation tokenContext = .inr .holds ∧
    CorrelatedHaving.fieldIds (.leaf (.uniqueness tokenSource)) = [1, 2] ∧
    CorrelatedHaving.markedFieldIds (.leaf (.uniqueness tokenSource)) = [2] := by native_decide

private def temporalSource (ids : List FieldId) : A12Kernel.HavingUniqueness := .temporal (ids.map fun id => {
  origin := .inner, field := { id, kind := .date, components := .fullDate } })
private def temporalContext (same : Bool) : CorrelationContext := {
  read := fun _ _ => { rawPresent := true, findings := [], parsed := some (.temporal (.date {
    instant := { epochMillis := 0 }, parts := { year := 1970, month := 1, day := 1 }, basis := .storedGregorian })) }
  storedText := fun _ id => if id == 3 then none else some (if same || id == 1 then "spelling A" else "spelling B") }

-- Synthetic spellings separate the representation's text identity from decoded equality;
-- spec/07 §5 does not establish that distinct same-value spellings can pass Kernel ingress.
example : [Phase.validation, .computation].all (fun phase => decide (
    result (temporalSource [1, 2]) phase (temporalContext false) = .inr .notTrue ∧
    result (temporalSource [1, 2]) phase (temporalContext true) = .inr .holds ∧
    result (temporalSource [1, 2, 3]) phase (temporalContext true) = .inr .holds ∧
    result (temporalSource [1, 3, 2]) phase (temporalContext true) = .inl (.storedTextUnavailable 3))) = true := by native_decide

private def prefixResult (ids : List FieldId) : Option ComputationConditionResult :=
  let context := { (cells (number 5)).asResolving with
    read := fun _ id => if id == 3 then .error (.storedTextUnavailable 3) else .ok (number 5) }
  ((numbers ids).evalRead .computation context frame).toOption
example : prefixResult [1, 2, 3] = some .holds ∧ prefixResult [1, 3, 2] = none := by native_decide

example : result (temporalSource [1, 2]) .validation { read := fun _ _ => invalid } = .inr .notTrue ∧
    result (temporalSource [1, 2]) .computation { read := fun _ _ => invalid } = .inr (.poison .malformed) ∧
    result (temporalSource [1, 2]) .computation { read := fun _ _ => emptyCell } = .inr .notTrue := by native_decide

end A12Kernel.Conformance.HavingUniqueness
