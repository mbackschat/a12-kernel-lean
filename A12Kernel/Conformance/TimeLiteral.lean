import A12Kernel.Elaboration.TimeLiteral
import A12Kernel.Elaboration.ValueAsDate

/-! # Checked Time-literal locks -/

namespace A12Kernel.Conformance.TimeLiteral

open A12Kernel

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

/- Exact ASCII whole-second text is admitted at both range boundaries. -/
example :
    (elaborateTimeLiteral "00:00:00").toOption =
        TimeOfDay.ofHms? 0 0 0 ∧
      (elaborateTimeLiteral "23:59:59").toOption =
        TimeOfDay.ofHms? 23 59 59 := by
  native_decide

/- Component width is fixed; neither a short component nor trailing text is accepted. -/
example :
    (elaborateTimeLiteral "1:30:45").toOption = none ∧
      (elaborateTimeLiteral "10:30:45Z").toOption = none := by
  native_decide

/- Lexically shaped but impossible clocks are rejected before runtime evaluation. -/
example :
    (elaborateTimeLiteral "24:00:00").toOption = none ∧
      (elaborateTimeLiteral "23:60:00").toOption = none ∧
      (elaborateTimeLiteral "23:59:60").toOption = none := by
  native_decide

/- Locale-shaped punctuation and non-ASCII digits never become Time literals. -/
example :
    (elaborateTimeLiteral "10.30.45").toOption = none ∧
      (elaborateTimeLiteral "１０:３０:４５").toOption = none := by
  native_decide

/- The decoded literal reaches the existing partial-Date DateTime seam as one exact Berlin wall label and instant. -/
example :
    let checked := (elaborateValueAsDateTime
      model 0 .lastDay).toOption.get (by native_decide)
    let clock := (elaborateTimeLiteral "10:30:45").toOption.get
      (by native_decide)
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 10 30 45).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    checked.evaluateOperand .validation
        (checked.toCheckedValueAsDateSource.checkSourceRaw
          (.parsed "00.02.2024"))
        (.value clock) =
      .value expectedLocal expectedInstant := by
  native_decide

/- A valid literal cannot erase the partial Date's cause-free unknown-year non-relevance. -/
example :
    let checked := (elaborateValueAsDateTime
      model 0 .firstDay).toOption.get (by native_decide)
    let clock := (elaborateTimeLiteral "10:30:45").toOption.get
      (by native_decide)
    checked.evaluateOperand .validation
        (checked.toCheckedValueAsDateSource.checkSourceRaw
          (.parsed "00.00.0000"))
        (.value clock) =
      .nonRelevant := by
  native_decide

end A12Kernel.Conformance.TimeLiteral
