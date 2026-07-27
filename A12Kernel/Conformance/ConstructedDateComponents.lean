import A12Kernel.Elaboration.ConstructedDateComponents

/-! # Checked three-Number-field constructed-Date locks -/

namespace A12Kernel.Conformance.ConstructedDateComponents

open A12Kernel

private def componentField
    (id : FieldId) (constraints : NumericTargetConstraints)
    (info : NumField := { scale := 0, signed := false }) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"DateComponent{id}"
  policy := { kind := .number info }
  numericTargetConstraints := constraints
}

private def dateModel (zoneId : String := "UTC") : FlatModel := {
  fields := [
    componentField 1 { maximum := some 31 },
    componentField 2 { maximum := some 12 },
    componentField 3 { maxStoredLength := some 4 },
    componentField 4 { maximum := some 22 },
    componentField 5 { maximum := some 99 }]
  timeZoneId := zoneId
}

/- The exact Date declaration gate accepts the positional maximum or stored width, but
   not an integer-digit cap or a complete-year maximum below 1000. -/
example :
    let wrongWidth : FlatModel := {
      fields := [componentField 1 { maxIntegerDigits := some 2 }]
    }
    let shortYear : FlatModel := {
      fields := [componentField 3 { maximum := some 999 }]
    }
    let boundedYear : FlatModel := {
      fields := [componentField 3 { maximum := some 1000 }]
    }
    (elaborateConstructedDateNumberField wrongWidth .day 1).isOk = false ∧
      (elaborateConstructedDateNumberField shortYear .year 3).isOk = false ∧
      (elaborateConstructedDateNumberField boundedYear .year 3).isOk = true := by
  native_decide

/- A legal but unsupported model zone fails before any Date component is read. -/
example :
    (match elaborateConstructedDateComponents
        (dateModel "Pacific/Apia") 1 2 3 with
    | .error (.unsupportedZone zoneId) => zoneId == "Pacific/Apia"
    | _ => false) = true := by
  native_decide

/- The two-argument form requires an explicit model Base Year and retains it as a
   fixed checked component rather than fabricating a field read. -/
private def baseYearOf? (model : FlatModel) : Option Int :=
  match elaborateConstructedDateBaseYearComponents model 1 2 with
  | .ok checked =>
      match checked.year with
      | .baseYear year => some year
      | .field _ | .centuryAndShortYear _ _ => none
  | .error _ => none

example :
    baseYearOf? (dateModel "UTC") = none ∧
      baseYearOf? { dateModel "UTC" with baseYear := some 2024 } =
        some 2024 := by
  native_decide

/- Day admission precedes the missing-Base-Year rejection, matching the source checker. -/
example :
    (match elaborateConstructedDateBaseYearComponents
        (dateModel "UTC") 99 2 with
    | .error (.field .day _) => true
    | _ => false) = true := by
  native_decide

/- The split-year form admits the Century checker's flexible maximum but keeps the
   Short-Year maximum exact. -/
example :
    (elaborateConstructedDateCenturyComponents
      (dateModel "UTC") 1 2 4 5).isOk = true ∧
    (elaborateConstructedDateNumberField {
        dateModel "UTC" with
        fields := [componentField 4 { maximum := some 9 }]
      } .century 4).isOk = false ∧
    (elaborateConstructedDateNumberField {
        dateModel "UTC" with
        fields := [componentField 5 { maximum := some 98 }]
      } .shortYear 5).isOk = false := by
  native_decide

end A12Kernel.Conformance.ConstructedDateComponents
