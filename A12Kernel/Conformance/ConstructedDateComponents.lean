import A12Kernel.Elaboration.ConstructedDateComponents

/-! # Checked constructed-Date component locks -/

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

private def temporalField (id : FieldId) (kind : TemporalKind)
    (components : TemporalComponents) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"TemporalComponent{id}"
  policy := { kind := .temporal kind components }
}

private def formattedTemporalField (id : FieldId) (kind : TemporalKind)
    (components : TemporalComponents) (format : String) : FlatFieldDecl := {
  temporalField id kind components with
  temporalTargetPolicy := some { format }
}

private def yearOnlyComponents : TemporalComponents := {
  year := true
  month := false
  day := false
  hour := false
  minute := false
  second := false
}

private def stringComponentField (id : FieldId) (maximum : Nat)
    (pattern : String := "[0-9]+") : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"StringComponent{id}"
  policy := { kind := .string }
  stringPolicy := { maxLength := some maximum }
  stringPatternSource := some pattern
}

private def extractorModel (baseYear : Option Int := none) : FlatModel :=
  let base := dateModel "UTC"
  { base with
    fields := base.fields ++ [
      temporalField 10 .date TemporalComponents.fullDate,
      temporalField 11 .dateTime TemporalComponents.now,
      temporalField 12 .date {
        year := false
        month := true
        day := true
        hour := false
        minute := false
        second := false },
      temporalField 13 .time {
        year := false
        month := false
        day := false
        hour := true
        minute := false
        second := false }]
    baseYear }

private def stringModel : FlatModel :=
  let base := extractorModel
  { base with
    fields := base.fields ++ [
      stringComponentField 20 2,
      stringComponentField 21 2 "\\d{2}",
      stringComponentField 22 4 "[0-9]{4}",
      stringComponentField 23 2,
      stringComponentField 24 2,
      formattedTemporalField 30 .date yearOnlyComponents "yyyy",
      formattedTemporalField 31 .date
        TemporalComponents.fullDate "dd.MM.yyyy",
      formattedTemporalField 32 .dateTime
        TemporalComponents.now "yyyy"] }

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
      | .complete _ | .centuryAndShortYear _ _ => none
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

private def extractorDateIsOk (model : FlatModel)
    (day month : SurfaceConstructedDateSource)
    (year : SurfaceConstructedDateYear) : Bool :=
  (elaborateConstructedDateSources model { day, month, year }).isOk

/- Direct component extractors are position-specific. Complete Year may use the model's
   Base Year supplement, while neither split-year position admits an extractor. -/
example :
    extractorDateIsOk extractorModel
        (.extractor .day 10) (.extractor .month 11)
        (.complete (.extractor .year 10)) = true ∧
      extractorDateIsOk extractorModel
        (.extractor .month 10) (.constant "6")
        (.complete (.constant "1963")) = false ∧
      extractorDateIsOk extractorModel
        (.extractor .quarter 10) (.constant "6")
        (.complete (.constant "1963")) = false ∧
      extractorDateIsOk extractorModel
        (.extractor .day 13) (.constant "6")
        (.complete (.constant "1963")) = false ∧
      extractorDateIsOk extractorModel
        (.constant "15") (.constant "6")
        (.complete (.extractor .year 12)) = false ∧
      extractorDateIsOk (extractorModel (some 2024))
        (.constant "15") (.constant "6")
        (.complete (.extractor .year 12)) = true ∧
      extractorDateIsOk extractorModel
        (.constant "15") (.constant "6")
        (.centuryAndShortYear
          (.extractor .year 10) (.constant "63")) = false := by
  native_decide

/- Base Year is a complete Date source for all three matching constructor positions.
   A mismatched extractor, either split-year position, and missing model configuration
   remain static rejections. -/
example :
    extractorDateIsOk (extractorModel (some 2024))
        (.baseYearExtractor .day) (.baseYearExtractor .month)
        (.complete (.baseYearExtractor .year)) = true ∧
      extractorDateIsOk (extractorModel (some 2024))
        (.baseYearExtractor .month) (.constant "6")
        (.complete (.constant "1963")) = false ∧
      extractorDateIsOk extractorModel
        (.baseYearExtractor .day) (.constant "6")
        (.complete (.constant "1963")) = false ∧
      extractorDateIsOk (extractorModel (some 2024))
        (.constant "15") (.constant "6")
        (.centuryAndShortYear
          (.baseYearExtractor .year) (.constant "63")) = false := by
  native_decide

/- Both selected Base-Year range endpoints are complete fixed Dates beneath ordinary
   extraction. They retain the same matching-position and split-year gates as direct
   Base-Year extraction. -/
example :
    extractorDateIsOk (extractorModel (some 2024))
        (.baseYearRangeExtractor .start .day)
        (.baseYearRangeExtractor .finish .month)
        (.complete (.baseYearRangeExtractor .finish .year)) = true ∧
      extractorDateIsOk (extractorModel (some 2024))
        (.baseYearRangeExtractor .finish .month)
        (.constant "6") (.complete (.constant "1963")) = false ∧
      extractorDateIsOk extractorModel
        (.baseYearRangeExtractor .start .day)
        (.constant "6") (.complete (.constant "1963")) = false ∧
      extractorDateIsOk (extractorModel (some 2024))
        (.constant "15") (.constant "6")
        (.centuryAndShortYear
          (.baseYearRangeExtractor .finish .year)
          (.constant "63")) = false := by
  native_decide

/- `Today` is a complete dynamic Date beneath ordinary extraction. The extracted part
   must match its outer constructor position, and split-year positions remain closed. -/
example :
    extractorDateIsOk extractorModel
        (.todayExtractor .day) (.todayExtractor .month)
        (.complete (.todayExtractor .year)) = true ∧
      extractorDateIsOk extractorModel
        (.todayExtractor .month) (.constant "6")
        (.complete (.constant "1963")) = false ∧
      extractorDateIsOk extractorModel
        (.constant "15") (.constant "6")
        (.centuryAndShortYear
          (.todayExtractor .year) (.constant "63")) = false := by
  native_decide

/- `Now` is a complete dynamic DateTime beneath ordinary extraction. Its matching
   components are legal, but mismatched and split-year placements remain closed. -/
example :
    extractorDateIsOk extractorModel
        (.nowExtractor .day) (.nowExtractor .month)
        (.complete (.nowExtractor .year)) = true ∧
      extractorDateIsOk extractorModel
        (.nowExtractor .month) (.constant "6")
        (.complete (.constant "1963")) = false ∧
      extractorDateIsOk extractorModel
        (.constant "15") (.constant "6")
        (.centuryAndShortYear
          (.nowExtractor .year) (.constant "63")) = false := by
  native_decide

/- Pattern-backed String fields reuse the six exact checker-recognized digit sources at
   the position's complete stored width. Regex equivalence and a wrong width do not pass. -/
example :
    let admitted (position : ConstructedDateComponentPosition)
        (maximum : Nat) (pattern : String) :=
      let model : FlatModel := {
        fields := [stringComponentField 20 maximum pattern]
      }
      (elaborateConstructedDateSource model position (.stringField 20)).isOk
    ["[0-9]+", "[0-9]*", "\\d+", "\\d*"].all
        (admitted .day 2) = true ∧
      admitted .day 2 "[0-9]{2}" = true ∧
      admitted .day 2 "\\d{2}" = true ∧
      admitted .year 4 "[0-9]{4}" = true ∧
      admitted .year 4 "\\d{4}" = true ∧
      admitted .day 2 "[0-9]{1,2}" = false ∧
      admitted .day 3 "[0-9]+" = false ∧
      admitted .year 2 "[0-9]+" = false := by
  native_decide

/- String sources mix with fixed and extractor sources, and both split-year positions
   accept their own two-character String declarations. -/
example :
    extractorDateIsOk stringModel
        (.stringField 20) (.constant "6")
        (.complete (.extractor .year 10)) = true ∧
      extractorDateIsOk stringModel
        (.constant "15") (.stringField 21)
        (.complete (.stringField 22)) = true ∧
      extractorDateIsOk stringModel
        (.constant "15") (.constant "6")
        (.centuryAndShortYear
          (.stringField 23) (.stringField 24)) = true := by
  native_decide

/- A direct Date field is a numeric constructor source only for complete Year and exact
   `yyyy`. Another format, DateTime, and every other position remain rejected. -/
example :
    let admitted (position : ConstructedDateComponentPosition)
        (field : FieldId) :=
      (elaborateConstructedDateSource stringModel position
        (.dateYearField field)).isOk
    admitted .year 30 = true ∧
      admitted .year 31 = false ∧
      admitted .year 32 = false ∧
      admitted .day 30 = false ∧
      admitted .month 30 = false ∧
      admitted .century 30 = false ∧
      admitted .shortYear 30 = false := by
  native_decide

private def constantDateIsOk (day month : String)
    (year : SurfaceConstructedDateYear) : Bool :=
  (elaborateConstructedDateSources (dateModel "UTC") {
    day := .constant day
    month := .constant month
    year
  }).isOk

/- Constant Day/Month have range but no width gate. Complete and split years retain
   their exact lexical widths and exclusive range ends. -/
example :
    constantDateIsOk "0001" "06" (.complete (.constant "1963")) = true ∧
      constantDateIsOk "١٥" "٦" (.complete (.constant "١٩٦٣")) = true ∧
      constantDateIsOk "15" "6"
        (.centuryAndShortYear (.constant "19") (.constant "63")) = true ∧
      constantDateIsOk "15" "6"
        (.centuryAndShortYear (.constant "19") (.constant "00")) = true ∧
      constantDateIsOk "𐒡" "6" (.complete (.constant "1963")) = false ∧
      constantDateIsOk "32" "6" (.complete (.constant "1963")) = false ∧
      constantDateIsOk "15" "13" (.complete (.constant "1963")) = false ∧
      constantDateIsOk "15" "6" (.complete (.constant "01963")) = false ∧
      constantDateIsOk "15" "6" (.complete (.constant "2200")) = false ∧
      constantDateIsOk "15" "6"
        (.centuryAndShortYear (.constant "22") (.constant "00")) = false ∧
      constantDateIsOk "15" "6"
        (.centuryAndShortYear (.constant "19") (.constant "0")) = false := by
  native_decide

end A12Kernel.Conformance.ConstructedDateComponents
