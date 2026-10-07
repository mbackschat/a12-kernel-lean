import A12Kernel.Semantics.Correlation

namespace A12Kernel.Conformance.HavingDateValidity

private def observed (value : Except CorrelationRuntimeFault α) : Sum CorrelationRuntimeFault α :=
  match value with | .ok result => .inr result | .error error => .inl error

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def number (value : Int) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def numeric (id : FieldId) : ResolvedConstructedDateSource := .numberField { id, info := { scale := 0, signed := false } }
private def source : HavingDateComponents := {
  day := (.inner, numeric 1), month := (.inner, numeric 2), year := .complete (.outer, numeric 3), profile := .utc }
private def context (day : CheckedCell) (year : Int := 2024) : CorrelationContext := {
  read := fun env id => if id == 1 then day else if id == 2 then number 2
    else number (if env == frame.outerEnv then year else 2023) }

example : observed (source.evalValidationRead .valid (context (number 29)).asResolving frame) = .inr (.fired .value) ∧
    observed (source.evalComputationRead .valid (context (number 29)).asResolving frame) = .inr .holds ∧
    observed (source.evalValidationRead .invalid (context emptyCell).asResolving frame) = .inr (.fired .omission) ∧
    observed (source.evalValidationRead .valid (context invalid).asResolving frame) = .inr .unknown ∧
    observed (source.evalComputationRead .invalid (context invalid).asResolving frame) = .inr (.poison .malformed) ∧
    observed (source.evalValidationRead .invalid (context (number 29) 2023).asResolving frame) = .inr (.fired .value) := by native_decide

private def conversion : HavingDateComponents := { source with month := (.inner, .stringField { id := 2 }) }
private def conversionContext : CorrelationContext := {
  read := fun _ id => if id == 1 then invalid else { rawPresent := true, parsed := some (.str "x"), findings := [] } }
example : observed (conversion.evalValidationRead .valid conversionContext.asResolving frame) = .inl .valueFailure ∧
    observed (conversion.evalComputationRead .valid conversionContext.asResolving frame) = .inr (.poison .malformed) := by native_decide

private def yearSource : HavingDateComponents := { source with
  year := .complete (.outer, .dateYearField { id := 3, kind := .time, components := TemporalComponents.ofFormat "yyyy" }) }
private def yearContext (stored : Option String) : CorrelationContext := {
  read := fun _ id => if id == 1 then number 29 else if id == 2 then number 2 else {
    rawPresent := true, findings := [], parsed := some (.temporal (.date {
      instant := { epochMillis := 0 }, parts := { year := 2024, month := 1, day := 1 }, basis := .storedGregorian })) }
  storedText := fun env _ => if env == frame.outerEnv then stored else some "2024" }
example : observed (yearSource.evalComputationRead .valid (yearContext (some "2023")).asResolving frame) = .inr .notTrue ∧
    observed (yearSource.evalComputationRead .valid (yearContext (some "2024")).asResolving frame) = .inr .holds ∧
    observed (yearSource.evalComputationRead .valid (yearContext none).asResolving frame) = .inl (.storedTextUnavailable 3) := by native_decide

private def failLeaf : CorrelatedHaving := .leaf (.dateValidity .valid conversion)
private def guardLeaf (filled : Bool) : CorrelatedHaving := .leaf (.presence (if filled then .filled else .notFilled) { origin := .inner, field := 4 })
private def guardContext : CorrelationContext := { conversionContext with
  read := fun env id => if id == 4 then number 1 else conversionContext.read env id }
example : observed (CorrelatedHaving.evalTruthInResolving (.and (guardLeaf false) failLeaf) guardContext.asResolving frame) = .inr .fls ∧
    observed (CorrelatedHaving.evalTruthInResolving (.or (guardLeaf true) failLeaf) guardContext.asResolving frame) = .inr .tru ∧
    observed (CorrelatedHaving.evalTruthInResolving (.and (guardLeaf true) failLeaf) guardContext.asResolving frame) = .inl .valueFailure := by native_decide

example : CorrelatedHaving.fieldIds (.leaf (.dateValidity .valid source)) = [1, 2, 3] ∧
    CorrelatedHaving.markedFieldIds (.leaf (.dateValidity .valid source)) = [3] := by native_decide

private def collapsedOrigin : HavingDateComponents := { source with year := .complete (.inner, numeric 3) }
example : observed (collapsedOrigin.evalComputationRead .valid (context (number 29)).asResolving frame) = .inr .notTrue ∧
    observed (source.evalComputationRead .valid (context (number 29)).asResolving frame) = .inr .holds := by native_decide

private def missingClock : HavingDateComponents := { source with
  month := (.inner, .pointInTimeExtractor .today .month "UTC" .utc) }
example : observed (missingClock.evalComputationRead .valid (context invalid).asResolving frame) = .inr (.poison .malformed) ∧
    observed (missingClock.evalValidationRead .valid (context invalid).asResolving frame) = .inl .worldUnavailable ∧
    observed (missingClock.evalComputationRead .valid (context (number 29)).asResolving frame) = .inl .worldUnavailable := by native_decide

private def split (century : Int) : HavingDateComponents := { source with
  year := .centuryAndShortYear (.inner, .constant century) (.outer, .constant 24) }
example : observed ((split 0).evalComputationRead .invalid (context (number 1)).asResolving frame) = .inr .holds ∧
    observed ((split 20).evalComputationRead .invalid (context (number 1)).asResolving frame) = .inr .notTrue := by native_decide

end A12Kernel.Conformance.HavingDateValidity
