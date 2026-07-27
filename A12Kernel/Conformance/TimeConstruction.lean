import A12Kernel.Elaboration.ValueAsDate
import A12Kernel.Semantics.TimeConstruction

/-! # Checked-component `Time(...)` locks -/

namespace A12Kernel.Conformance.TimeConstruction

open A12Kernel

private def component (value : Int) : TimeConstructionComponent :=
  .value value

private def source : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "ApproxDate"
  policy := {
    kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy"
    partialMode := .yearOptional
    youngerThan1900Check := false } }

private def model : FlatModel := {
  fields := [source]
  timeZoneId := "Europe/Berlin" }

/- Omitted trailing components are fixed zeroes, including the zero-argument form. -/
example :
    TimeConstructionArity.zero.evaluate
        (component 99) (component 99) (component 99) =
        .value ((TimeOfDay.ofHms? 0 0 0).get (by native_decide)) ∧
      TimeConstructionArity.hour.evaluate
        (component 10) (component 99) (component 99) =
        .value ((TimeOfDay.ofHms? 10 0 0).get (by native_decide)) ∧
      TimeConstructionArity.minute.evaluate
        (component 10) (component 30) (component 99) =
        .value ((TimeOfDay.ofHms? 10 30 0).get (by native_decide)) := by
  native_decide

/- Formal unavailability dominates missingness in authored component order. -/
example :
    TimeConstructionArity.second.evaluate
        (.unavailable .malformed) .empty
        (.unavailable .declaredConstraint) =
        .unavailable .malformed ∧
      TimeConstructionArity.second.evaluate
        (component 10) .empty
        (.unavailable .declaredConstraint) =
        .unavailable .declaredConstraint := by
  native_decide

/- Reached non-relevance dominates ordinary missingness before clock reality. -/
example :
    TimeConstructionArity.second.evaluate
        (component 10) .empty .nonRelevant =
      .nonRelevant := by
  native_decide

/- Missing input and a fully present impossible clock are distinct no-value reasons. -/
example :
    TimeConstructionArity.second.evaluate
        (component 24) .empty (component 0) = .incomplete ∧
      TimeConstructionArity.second.evaluate
        (component 24) (component 0) (component 0) = .unreal ∧
      TimeConstructionResult.incomplete.asDateTimeOperand = .noValue true ∧
      TimeConstructionResult.unreal.asDateTimeOperand = .noValue false := by
  native_decide

/- A constructed Time reaches the existing partial-Date DateTime boundary as an exact wall label and instant. -/
example :
    let checked := (elaborateValueAsDateTime
      model 0 .lastDay).toOption.get (by native_decide)
    let time := TimeConstructionArity.second.evaluate
      (component 10) (component 30) (component 45)
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 10 30 45).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    checked.evaluateConstructionRaw .validation
        (.parsed "00.02.2024") time =
      .value expectedLocal expectedInstant false := by
  native_decide

end A12Kernel.Conformance.TimeConstruction
