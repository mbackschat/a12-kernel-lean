import A12Kernel.Elaboration.CorrelationWellFormed

namespace A12Kernel.Conformance.HavingDateValidity

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

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

private def dateExpression (components : HavingDateComponents := source) : HavingTemporalExpression := {
  core := .atom (.dateConstruction components), profile := components.profile, baseYear := none }
private def yearPart : HavingNumericAtom := .temporalExpressionPart (.date .year) dateExpression

example : observed (dateExpression.evaluate .validation (context (number 30)).asResolving frame) =
      .inr (.value .noValue true) ∧
    observed (dateExpression.evaluate .validation (context emptyCell).asResolving frame) =
      .inr (.value .noValue false) ∧
    observed (yearPart.readValidationResolving (context (number 30)).asResolving frame) =
      .inr (.ok (.value 0 .fixed)) ∧
    observed (yearPart.readValidationResolving (context emptyCell).asResolving frame) =
      .inr (.ok (.value 0 .both)) ∧
    observed (yearPart.readComputationResolving (context (number 30)).asResolving frame) = .inr (.value 0) ∧
    observed (yearPart.readComputationResolving (context invalid).asResolving frame) = .inr (.poison .malformed) := by native_decide

private def required : CheckedCell := { emptyCell with findings := [.required] }
example : observed (dateExpression.evaluate .validation (context required).asResolving frame) =
      .inr (.unknown .required) ∧
    observed (dateExpression.evaluate .computation (context required).asResolving frame) =
      .inr (.value .noValue false) ∧
    observed ((dateExpression conversion).evaluate .validation conversionContext.asResolving frame) = .inl .valueFailure ∧
    observed ((dateExpression conversion).evaluate .computation conversionContext.asResolving frame) = .inr (.unknown .malformed) ∧
    observed ((dateExpression conversion).evaluate .computation
      ({ conversionContext with read := fun env id => if id == 1 then emptyCell else conversionContext.read env id }).asResolving frame) =
      .inl .valueFailure ∧
    observed ((dateExpression missingClock).evaluate .validation (context invalid).asResolving frame) = .inl .worldUnavailable ∧
    observed ((dateExpression missingClock).evaluate .computation (context invalid).asResolving frame) = .inr (.unknown .malformed) := by native_decide

example : observed (dateExpression.evaluate .computation (context (number 29)).asResolving frame) =
      .inr (.value (.date {
        instant := { epochMillis := 1709164800000 }
        parts := { year := 2024, month := 2, day := 29 }, basis := .legacyHybrid }) true) ∧
    observed ((dateExpression { source with profile := .europeBerlin }).evaluate .computation (context (number 29)).asResolving frame) =
      .inr (.value (.date {
        instant := { epochMillis := 1709161200000 }
        parts := { year := 2024, month := 2, day := 29 }, basis := .legacyHybrid }) true) ∧
    observed ((dateExpression collapsedOrigin).evaluate .computation (context (number 29)).asResolving frame) =
      .inr (.value .noValue true) ∧
    yearPart.fieldOrigins = [(.inner, 1), (.inner, 2), (.outer, 3)] := by native_decide

private def valueComparison : CorrelatedHaving := .leaf (.temporalExpression {
  operator := .equal, left := dateExpression
  right := { core := .atom .today, profile := .utc, baseYear := none } })
example : valueComparison.fieldIds = [1, 2, 3] ∧ valueComparison.markedFieldIds = [3] := by native_decide

private def model : FlatModel := {
  fields := [(1, "Day", 31), (2, "Month", 12), (3, "Year", 9999)].map fun (id, name, maximum) => {
    id, name, groupPath := ["Rows"], repeatableScope := [10]
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maximum := some maximum } }
  repeatableGroups := [{ level := 10, path := ["Rows"], repeatability := some 2 }] }
private def constants : HavingDateComponents := {
  day := (.inner, .constant 29), month := (.inner, .constant 2)
  year := .complete (.inner, .constant 2024), profile := .utc }
example : dateExpression.wellFormed model [10] [10] = true ∧
    dateExpression.wellFormed model [10] [] = false ∧
    dateExpression.wellFormed model [] [10] = false ∧
    (dateExpression { source with month := source.day }).wellFormed model [10] [10] = false ∧
    (dateExpression { source with day := (.inner, .numberField { id := 1, info := { scale := 1, signed := false } }) }).wellFormed model [10] [10] = false ∧
    (dateExpression { source with profile := .europeBerlin }).wellFormed model [10] [10] = false ∧
    ({ dateExpression with core := .atom (.dateConstruction { source with profile := .europeBerlin }) }).wellFormed model [10] [10] = false ∧
    (dateExpression constants).wellFormed model [] [] = true ∧
    constants.wellFormedForEnvironments model [] [] = false ∧
    (dateExpression { constants with day := (.inner, .constant 32) }).wellFormed model [] [] = false ∧
    (dateExpression { source with year := .baseYear 2024 }).wellFormed model [10] [10] = false := by native_decide

end A12Kernel.Conformance.HavingDateValidity
