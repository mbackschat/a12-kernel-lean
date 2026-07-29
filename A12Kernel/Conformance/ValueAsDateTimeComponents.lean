import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents

/-! # Partial-Date and checked `Time(...)` component locks -/

namespace A12Kernel.Conformance.ValueAsDateTimeComponents

open A12Kernel

private def componentField
    (id : FieldId) (constraints : NumericTargetConstraints)
    (info : NumField := { scale := 0, signed := false }) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"Component{id}"
  policy := { kind := .number info }
  numericTargetConstraints := constraints
}

private def partialDate : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "ApproxDate"
  policy := {
    kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy"
    partialMode := .yearOptional
    youngerThan1900Check := false } }

private def timeModel : FlatModel := {
  fields := [
    partialDate,
    componentField 1 { maxStoredLength := some 2 },
    componentField 2 { maxStoredLength := some 2 },
    componentField 3 { maxStoredLength := some 2 }]
  timeZoneId := "Europe/Berlin"
}

private def temporalComponentField (id : FieldId) (kind : TemporalKind)
    (components : TemporalComponents := TemporalComponents.now) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"TemporalComponent{id}"
  policy := { kind := .temporal kind components }
}

private def stringComponentField (id : FieldId) (pattern : String := "[0-9]+")
    (maximum : Nat := 2) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"StringComponent{id}"
  policy := { kind := .string }
  stringPolicy := { maxLength := some maximum }
  stringPatternSource := some pattern
}

private def mixedModel : FlatModel := {
  fields := timeModel.fields ++ [
    temporalComponentField 4 .time,
    temporalComponentField 5 .dateTime,
    stringComponentField 6]
  timeZoneId := "Europe/Berlin"
}

private def componentPath (name : String) : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order"]
  field := name }

private def shiftedHourAmount : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field (componentPath "Component1")))
    (.literal { value := 1, authoredScale := 0 })

private def invalidShiftAmount : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide
    (.atom (.field (componentPath "Component1")))
    (.literal { value := 0, authoredScale := 0 })

private def prepared? (model : FlatModel) :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption

private def document? (model : FlatModel)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) := do
  let prepared ← prepared? model
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  } |>.toOption

private def numberCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput :=
  let selectedStored := match raw with
    | .parsed (.num value) => toString value
    | .rejected .declaredConstraint => "100"
    | .presentEmpty => ""
    | _ => stored
  {
    address := { field, path := [] }
    stored := selectedStored
    raw
  }

private def temporalCell (field : FieldId) (stored : String)
    (value : TemporalValue) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw := .parsed (.temporal value)
}

private def stringCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

/- The checker recognizes exactly four unbounded digit sources and the two fixed-width
   sources derived from maximum length 2. A digit-shaped alternative and the wrong
   maximum remain rejected rather than being interpreted as equivalent regexes. -/
example :
    let admitted (pattern : String) (maximum : Nat := 2) :=
      let model : FlatModel := {
        fields := [stringComponentField 6 pattern maximum]
      }
      (elaborateTimeComponents model (.hour (.string 6))).isOk
    ["[0-9]+", "[0-9]*", "\\d+", "\\d*", "[0-9]{2}", "\\d{2}"].all
        admitted = true ∧
      admitted "[0-9]{1,2}" = false ∧
      admitted "[0-9]+" 3 = false := by
  native_decide

/- `Time(...)` checks the Number declaration's stored-length or exact-value bound; an
   integer-digit cap with the same numeral is not a substitute. -/
example :
    let storedLengthModel : FlatModel := {
      fields := [componentField 1 { maxStoredLength := some 2 }]
    }
    let integerDigitsModel : FlatModel := {
      fields := [componentField 1 { maxIntegerDigits := some 2 }]
    }
    (elaborateTimeComponents storedLengthModel
        (.hour (.number 1))).isOk = true ∧
      (elaborateTimeComponents integerDigitsModel
        (.hour (.number 1))).isOk = false := by
  native_decide

/- Fractional declarations and a position-specific maximum copied to the wrong slot are
   rejected before the document is read. -/
example :
    let fractional : FlatModel := {
      fields := [componentField 1 { maxStoredLength := some 2 }
        { scale := 1, signed := false }]
    }
    let hourBoundAtMinute : FlatModel := {
      fields := [componentField 1 { maximum := some 23 }]
    }
    (elaborateTimeComponents fractional
        (.hour (.number 1))).isOk = false ∧
      (elaborateTimeComponents hourBoundAtMinute
        (.minute (.number 1) (.number 1))).isOk = false := by
  native_decide

/- A signed declaration needs an explicit nonnegative minimum; the exact position maximum
   then remains a legal alternative to the stored-length bound. -/
example :
    let signedWithoutMinimum : FlatModel := {
      fields := [componentField 1 { maximum := some 23 }
        { scale := 0, signed := true }]
    }
    let signedWithMinimum : FlatModel := {
      fields := [componentField 1 { minimum := some 0, maximum := some 23 }
        { scale := 0, signed := true }]
    }
    (elaborateTimeComponents signedWithoutMinimum
        (.hour (.number 1))).isOk = false ∧
      (elaborateTimeComponents signedWithMinimum
        (.hour (.number 1))).isOk = true := by
  native_decide

/- A one-field prefix delegates trailing zeroes to the resolved constructor. A
   length-bounded field can still contain `24`, which is unreal rather than clamped. -/
example :
    let result (stored : String) (value : Rat) := do
      let checked ←
        (elaborateTimeComponents timeModel (.hour (.number 1))).toOption
      let input ← document? timeModel [
        numberCell 1 stored (.parsed (.num value))]
      checked.evaluate .validation input |>.toOption
    result "10" 10 = some (.value
        ((TimeOfDay.ofHms? 10 0 0).get (by native_decide))) ∧
      result "24" 24 = some .unreal := by
  native_decide

/- Empty and formal inputs retain distinct construction reasons, and the first formal
   component wins in authored order. -/
example :
    let result (cells : List ClassifiedCellInput) := do
      let checked ←
        (elaborateTimeComponents timeModel
          (.second (.number 1) (.number 2) (.number 3))).toOption
      let input ← document? timeModel cells
      checked.evaluate .computation input |>.toOption
    result [numberCell 1 "10" (.parsed (.num 10))] =
        some .incomplete ∧
      result [
        numberCell 1 "bad" (.rejected .malformed),
        numberCell 2 "100" (.rejected .declaredConstraint)] =
          some (.unavailable .malformed) := by
  native_decide

/- The checked payload classifier rejects a forged fractional Number instead of applying
   truncation that belongs only to other numeric operations. -/
example :
    let checked : CheckedTimeNumberField timeModel := {
      position := .hour
      source := { id := 1, info := { scale := 0, signed := false } }
      admitted := by native_decide
    }
    (match checked.classify (.value (.num (1 / 2))) with
    | .error (.nonIntegralPayload field value) =>
        field == 1 && value == (1 / 2)
    | _ => false) = true := by
  native_decide

/- A mixed String/Number/extractor prefix reaches the partial-Date DateTime constructor
   without reconstructing document values, conversion, extractor semantics, or zone
   policy. -/
example :
    let dateTimeClock := (TimeOfDay.ofHms? 8 44 45).get (by native_decide)
    let sourceDate : DateParts := { year := 2024, month := 6, day := 15 }
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 10 30 45).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    let result := do
      let time ←
        (elaborateTimeComponents mixedModel
          (.second (.string 6) (.number 2)
            (.extractor .second 5))).toOption
      let construction ←
        (elaborateValueAsDateTime mixedModel 0 .lastDay).toOption
      let input ← document? mixedModel [
        stringCell 6 "10" (.parsed (.str "10")),
        numberCell 2 "30" (.parsed (.num 30)),
        temporalCell 5 "2024-06-15T08:44:45"
          (.dateTime { epochMillis := 1718441085000 }
            sourceDate dateTimeClock .storedGregorian)]
      construction.evaluateComponentsRaw time .validation input
        (.parsed "00.02.2024") |>.toOption
    result = some (.value expectedLocal expectedInstant false) := by
  native_decide

/- Filled digit Strings convert as decimal integers. Empty and formal inputs retain
   distinct construction reasons, and a two-digit but impossible hour remains unreal. -/
example :
    let result (stored : String) (raw : RawCell) := do
      let checked ←
        (elaborateTimeComponents mixedModel (.hour (.string 6))).toOption
      let input ← document? mixedModel [stringCell 6 stored raw]
      checked.evaluate .computation input |>.toOption
    result "08" (.parsed (.str "08")) = some (.value
        ((TimeOfDay.ofHms? 8 0 0).get (by native_decide))) ∧
      result "24" (.parsed (.str "24")) = some .unreal ∧
      result "" .presentEmpty = some .incomplete ∧
      result "bad" (.rejected .declaredConstraint) =
        some (.unavailable .declaredConstraint) := by
  native_decide

/- An extractor token belongs only in the matching constructor position. -/
example :
    (elaborateTimeComponents mixedModel
      (.hour (.extractor .minute 4))).isOk = false := by
  native_decide

/- Field-backed extractors admit Time or DateTime only when the source declaration
   exposes the selected component. -/
example :
    let missingSecond := {
      TemporalComponents.now with second := false
    }
    let model : FlatModel := {
      fields := [
        temporalComponentField 4 .time,
        temporalComponentField 5 .dateTime,
        temporalComponentField 6 .date TemporalComponents.fullDate,
        temporalComponentField 7 .dateTime missingSecond]
    }
    (elaborateTimeComponents model
        (.hour (.extractor .hour 4))).isOk = true ∧
      (elaborateTimeComponents model
        (.minute (.extractor .hour 4) (.extractor .minute 5))).isOk = true ∧
      (elaborateTimeComponents model
        (.hour (.extractor .hour 6))).isOk = false ∧
      (elaborateTimeComponents model
        (.second (.extractor .hour 4) (.extractor .minute 5)
          (.extractor .second 7))).isOk = false := by
  native_decide

/- An empty extractor source carries the extractor's symmetric zero together with missing
   provenance, so the constructor remains incomplete; a formal source stays unavailable. -/
example :
    let result (cells : List ClassifiedCellInput) := do
      let checked ←
        (elaborateTimeComponents mixedModel
          (.hour (.extractor .hour 4))).toOption
      let input ← document? mixedModel cells
      checked.evaluate .computation input |>.toOption
    result [] = some .incomplete ∧
      result [{
        address := { field := 4, path := [] }
        stored := "bad"
        raw := .rejected .malformed
      }] = some (.unavailable .malformed) := by
  native_decide

/- A nonliteral extractor reuses exact-instant DateTime shifting before selecting its matching component. Berlin spring-forward therefore skips hour 2. A present-but-valueless shifted source projects to fixed zero, while a not-given source keeps the enclosing Time incomplete. -/
example :
    let sourceLocal := (LocalDateTime.ofYmdHms?
      2024 3 31 1 30 0).get (by native_decide)
    let sourceInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        sourceLocal).get (by native_decide)
    let evaluate
        (expression : AuthoredNumericExpr SurfaceNumericAtom)
        (source : Option (RawCell Value))
        (amount : Option (RawCell Value)) := do
      let component ←
        (elaborateShiftedTimeExtractorExpression mixedModel ["Order"]
          .hour .hour 5 .hours expression).toOption
      let sourceCell := source.toList.map fun raw => {
        address := { field := 5, path := [] }
        stored := "source"
        raw
      }
      let amountCell := amount.toList.map fun raw =>
        numberCell 1 "amount" raw
      let input ← document? mixedModel (sourceCell ++ amountCell)
      CheckedTimeComponents.evaluate
        (TimeComponentPrefix.hour component) .computation input |>.toOption
    let presentSource : RawCell Value := .parsed (.temporal
      (.dateTime sourceInstant sourceLocal.date.civil.parts
        sourceLocal.time .storedGregorian))
    evaluate shiftedHourAmount (some presentSource)
        (some (.parsed (.num 0))) =
        some (.value ((TimeOfDay.ofHms? 3 0 0).get (by native_decide))) ∧
      evaluate invalidShiftAmount (some presentSource)
        (some (.parsed (.num 3))) =
        some (.value ((TimeOfDay.ofHms? 0 0 0).get (by native_decide))) ∧
      evaluate invalidShiftAmount none (some (.parsed (.num 3))) =
        some .incomplete ∧
      (elaborateShiftedTimeExtractorLiteral mixedModel
        .hour .hour 5 .hours 1).isOk = true := by
  native_decide

/- The nested shift preserves source-before-amount formal order, and the component position must match the authored extractor token. -/
example :
    let evaluate (source : Option (RawCell Value))
        (amount : RawCell Value) := do
      let component ←
        (elaborateShiftedTimeExtractorExpression mixedModel ["Order"]
          .hour .hour 5 .hours shiftedHourAmount).toOption
      let sourceCell := source.toList.map fun raw => {
        address := { field := 5, path := [] }
        stored := "source"
        raw
      }
      let input ← document? mixedModel
        (sourceCell ++ [numberCell 1 "amount" amount])
      CheckedTimeComponents.evaluate
        (TimeComponentPrefix.hour component) .computation input |>.toOption
    evaluate (some (.rejected .malformed))
        (.rejected .declaredConstraint) =
        some (.unavailable .malformed) ∧
      evaluate none (.rejected .declaredConstraint) =
        some (.unavailable .declaredConstraint) ∧
      (elaborateShiftedTimeExtractorExpression mixedModel ["Order"]
        .hour .minute 5 .hours shiftedHourAmount).isOk = false := by
  native_decide

/- A dynamic nested extractor consumes the execution world before its checked amount and
   shifts the exact instant across the Berlin spring-forward transition. -/
example :
    let nowLocal := (LocalDateTime.ofYmdHms?
      2024 3 31 1 30 0).get (by native_decide)
    let now :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        nowLocal).get (by native_decide)
    let result := do
      let component ←
        (elaborateNowShiftedTimeExtractorExpression mixedModel ["Order"]
          .hour .hour .hours shiftedHourAmount).toOption
      let input ← document? mixedModel [
        numberCell 1 "0" (.parsed (.num 0))]
      CheckedWorldTimeComponents.evaluate
        (TimeComponentPrefix.hour component)
        .computation { now } input |>.toOption
    result =
        some (.value ((TimeOfDay.ofHms? 3 0 0).get (by native_decide))) ∧
      (elaborateNowShiftedTimeExtractorExpression mixedModel ["Order"]
        .hour .minute .hours shiftedHourAmount).isOk = false := by
  native_decide

/- A reached domain-invalid amount becomes fixed component zero, while a reached formal
   amount remains unavailable with its exact cause. -/
example :
    let evaluate (expression : AuthoredNumericExpr SurfaceNumericAtom)
        (amount : RawCell Value) := do
      let component ←
        (elaborateNowShiftedTimeExtractorExpression mixedModel ["Order"]
          .hour .hour .hours expression).toOption
      let input ← document? mixedModel [numberCell 1 "amount" amount]
      CheckedWorldTimeComponents.evaluate
        (TimeComponentPrefix.hour component)
        .computation { now := { epochMillis := 0 } } input |>.toOption
    evaluate invalidShiftAmount (.parsed (.num 3)) =
        some (.value ((TimeOfDay.ofHms? 0 0 0).get (by native_decide))) ∧
      evaluate shiftedHourAmount (.rejected .declaredConstraint) =
        some (.unavailable .declaredConstraint) := by
  native_decide

end A12Kernel.Conformance.ValueAsDateTimeComponents
