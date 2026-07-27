import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Checked constructed-Date execution locks -/

namespace A12Kernel.Conformance.ConstructedDateEvaluation

open A12Kernel

private def componentField
    (id : FieldId) (constraints : NumericTargetConstraints) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"DateComponent{id}"
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := constraints
}

private def shiftAmountField : FlatFieldDecl := {
  id := 4
  groupPath := ["Order"]
  name := "ShiftAmount"
  policy := { kind := .number { scale := 2, signed := true } }
}

private def dateModel (zoneId : String := "UTC") : FlatModel := {
  fields := [
    componentField 1 { maximum := some 31 },
    componentField 2 { maximum := some 12 },
    componentField 3 { maxStoredLength := some 4 },
    shiftAmountField,
    componentField 5 { maximum := some 31 },
    componentField 6 { maximum := some 12 },
    componentField 7 { maxStoredLength := some 4 },
    componentField 8 { maximum := some 22 },
    componentField 9 { maximum := some 99 }]
  timeZoneId := zoneId
}

private def temporalField (id : FieldId) (kind : TemporalKind)
    (components : TemporalComponents) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"TemporalComponent{id}"
  policy := { kind := .temporal kind components }
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

private def extractorDateModel : FlatModel :=
  let base := dateModel "UTC"
  { base with
    fields := base.fields ++ [
      temporalField 10 .dateTime TemporalComponents.now,
      temporalField 11 .date TemporalComponents.fullDate,
      stringComponentField 20 2,
      stringComponentField 21 4] }

private def documentFor? (model : FlatModel) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  } |>.toOption

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument (dateModel "UTC")) :=
  documentFor? (dateModel "UTC") cells

private def numberCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

private def stringCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

private def evaluate? (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluate .validation input |>.toOption

private def evaluateBaseYear? (cells : List ClassifiedCellInput) := do
  let model := { dateModel "UTC" with baseYear := some 2024 }
  let checked ←
    (elaborateConstructedDateBaseYearComponents model 1 2).toOption
  let input ← documentFor? model cells
  checked.evaluate .validation input |>.toOption

private def evaluateCentury? (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateCenturyComponents
      (dateModel "UTC") 1 2 8 9).toOption
  let input ← document? cells
  checked.evaluate .validation input |>.toOption

private def evaluateSources? (sources : SurfaceConstructedDateComponents)
    (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateSources (dateModel "UTC") sources).toOption
  let input ← document? cells
  checked.evaluate .validation input |>.toOption

private def evaluateExtractorSources? (sources : SurfaceConstructedDateComponents)
    (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateSources extractorDateModel sources).toOption
  let input ← documentFor? extractorDateModel cells
  checked.evaluate .validation input |>.toOption

private def validVerdict? (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluateValid .validation input |>.toOption

private def invalidVerdict? (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluateInvalid .validation input |>.toOption

private def numericPart? (part : DateNumericPart)
    (cells : List ClassifiedCellInput) := do
  let checked ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  checked.evaluateNumericPart part .validation input |>.toOption

private def amountPath : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order"]
  field := "ShiftAmount"
}

/- The model Base Year is a present fixed component: no Year cell is read, and an
   empty Day remains incomplete instead of acquiring a default Day. -/
example :
    evaluateBaseYear? [
        numberCell 1 "29" (.parsed (.num 29)),
        numberCell 2 "2" (.parsed (.num 2))] =
          some (.resolved (.real { year := 2024, month := 2, day := 29 })) ∧
      evaluateBaseYear? [
        numberCell 2 "2" (.parsed (.num 2))] =
          some (.resolved .incomplete) := by
  native_decide

/- The four-part form composes a full year only after both authored parts are reached.
   Fixed Short-Year zero is present; an absent part remains incomplete. -/
example :
    evaluateCentury? [
        numberCell 1 "15" (.parsed (.num 15)),
        numberCell 2 "6" (.parsed (.num 6)),
        numberCell 8 "19" (.parsed (.num 19)),
        numberCell 9 "63" (.parsed (.num 63))] =
          some (.resolved (.real { year := 1963, month := 6, day := 15 })) ∧
      evaluateCentury? [
        numberCell 1 "1" (.parsed (.num 1)),
        numberCell 2 "1" (.parsed (.num 1)),
        numberCell 8 "19" (.parsed (.num 19)),
        numberCell 9 "0" (.parsed (.num 0))] =
          some (.resolved (.real { year := 1900, month := 1, day := 1 })) ∧
      evaluateCentury? [
        numberCell 1 "15" (.parsed (.num 15)),
        numberCell 2 "6" (.parsed (.num 6)),
        numberCell 8 "19" (.parsed (.num 19))] =
          some (.resolved .incomplete) := by
  native_decide

/- A reached Century formal cause wins before Short-Year, and the full year is not the
   tempting sum of the two authored parts. -/
example :
    evaluateCentury? [
        numberCell 1 "15" (.parsed (.num 15)),
        numberCell 2 "6" (.parsed (.num 6)),
        numberCell 8 "bad-century" (.rejected .malformed),
        numberCell 9 "bad-year" (.rejected .declaredConstraint)] =
          some (.unavailable .malformed) ∧
      evaluateCentury? [
        numberCell 1 "15" (.parsed (.num 15)),
        numberCell 2 "6" (.parsed (.num 6)),
        numberCell 8 "19" (.parsed (.num 19)),
        numberCell 9 "63" (.parsed (.num 63))] ≠
          some (.resolved (.real { year := 82, month := 6, day := 15 })) := by
  native_decide

/- Checked constants are fixed inputs: they compose with a field component and do not
   consult unrelated document cells. -/
example :
    let sources : SurfaceConstructedDateComponents := {
      day := .numberField 1
      month := .constant "6"
      year := .centuryAndShortYear
        (.constant "19") (.constant "63") }
    evaluateSources? sources [
        numberCell 1 "15" (.parsed (.num 15))] =
          some (.resolved (.real { year := 1963, month := 6, day := 15 })) ∧
      evaluateSources? sources [
        numberCell 1 "15" (.parsed (.num 15)),
        numberCell 3 "bad-unread-year" (.rejected .malformed)] =
          some (.resolved (.real {
            year := 1963, month := 6, day := 15 })) ∧
      evaluateSources? {
        day := .constant "15"
        month := .constant "6"
        year := .centuryAndShortYear
          (.constant "19") (.constant "00")
      } [] =
        some (.resolved (.real {
          year := 1900, month := 6, day := 15 })) := by
  native_decide

private def temporalCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

private def dateValue (year : Int) (month day : Nat) : TemporalValue :=
  .date { epochMillis := 0 } { year, month, day } .storedGregorian

private def dateTimeValue (year : Int) (month day : Nat) : TemporalValue :=
  .dateTime { epochMillis := 0 } { year, month, day }
    ((TimeOfDay.ofHms? 12 0 0).get (by native_decide)) .storedGregorian

/- Matching field-backed extractors compose with fixed components. Empty extraction stays
   incomplete, and a formal Day retains precedence over a later formal Year. -/
example :
    let sources : SurfaceConstructedDateComponents := {
      day := .extractor .day 10
      month := .constant "6"
      year := .complete (.extractor .year 11) }
    evaluateExtractorSources? sources [
        temporalCell 10 "2024-06-15"
          (.parsed (.temporal (dateTimeValue 2024 6 15))),
        temporalCell 11 "1963-01-01"
          (.parsed (.temporal (dateValue 1963 1 1)))] =
          some (.resolved (.real { year := 1963, month := 6, day := 15 })) ∧
      evaluateExtractorSources? sources [
        temporalCell 11 "1963-01-01"
          (.parsed (.temporal (dateValue 1963 1 1)))] =
          some (.resolved .incomplete) ∧
      evaluateExtractorSources? sources [
        temporalCell 10 "bad-day" (.rejected .malformed),
        temporalCell 11 "bad-year" (.rejected .declaredConstraint)] =
          some (.unavailable .malformed) := by
  native_decide

/- Checked String components use exact decimal conversion but preserve constructor
   reasons: empty stays incomplete, formal state dominates, and a present 99 Day is
   unreal rather than clamped or treated as missing. -/
example :
    let sources : SurfaceConstructedDateComponents := {
      day := .stringField 20
      month := .constant "6"
      year := .complete (.stringField 21) }
    evaluateExtractorSources? sources [
        stringCell 20 "05" (.parsed (.str "05")),
        stringCell 21 "1963" (.parsed (.str "1963"))] =
          some (.resolved (.real { year := 1963, month := 6, day := 5 })) ∧
      evaluateExtractorSources? sources [
        stringCell 21 "1963" (.parsed (.str "1963"))] =
          some (.resolved .incomplete) ∧
      evaluateExtractorSources? sources [
        stringCell 20 "bad-day" (.rejected .malformed),
        stringCell 21 "bad-year" (.rejected .declaredConstraint)] =
          some (.unavailable .malformed) ∧
      evaluateExtractorSources? sources [
        stringCell 20 "99" (.parsed (.str "99")),
        stringCell 21 "1963" (.parsed (.str "1963"))] =
          some (.resolved .unreal) := by
  native_decide

private def amountOverZero : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide
    (.atom (.field amountPath))
    (.literal { value := 0, authoredScale := 0 })

private def shift? (unit : DateShiftUnit)
    (amount : CheckedTemporalShiftAmount (dateModel "UTC"))
    (cells : List ClassifiedCellInput) := do
  let source ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let input ← document? cells
  ({ source, unit, amount } :
      CheckedConstructedDateShift (dateModel "UTC")).evaluate
        .computation input |>.toOption

private inductive DifferenceObservation where
  | numeric (result : ConstructedDateNumericResult)
  | formal (cause : FormalCause)
  deriving Repr, DecidableEq

private def difference? (unit : DateShiftUnit)
    (cells : List ClassifiedCellInput) : Option DifferenceObservation := do
  let first ←
    (elaborateConstructedDateComponents (dateModel "UTC") 1 2 3).toOption
  let second ←
    (elaborateConstructedDateComponents (dateModel "UTC") 5 6 7).toOption
  let input ← document? cells
  match ({ first, second, unit } :
      CheckedConstructedDateDifference (dateModel "UTC")).evaluate
        .validation input with
  | .error _ => none
  | .ok (.error cause) => some (.formal cause)
  | .ok (.ok result) => some (.numeric result)

/- Checked execution preserves the default-cutover identity through all three literal
   calendar shifts. -/
example :
    let source := evaluate? [
      numberCell 1 "4" (.parsed (.num 4)),
      numberCell 2 "10" (.parsed (.num 10)),
      numberCell 3 "1582" (.parsed (.num 1582))]
    source.bind (·.addLegacyDays? 1) =
        some (.resolved (.real {
          year := 1582, month := 10, day := 15 })) ∧
      source.bind (·.addLegacyMonths? (-1)) =
        some (.resolved (.real {
          year := 1582, month := 9, day := 4 })) ∧
      source.bind (·.addLegacyYears? 1) =
        some (.resolved (.real {
          year := 1583, month := 10, day := 4 })) := by
  native_decide

/- A present cutover-hole label is unreal, while an empty component is incomplete. -/
example :
    evaluate? [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.resolved .unreal) ∧
      evaluate? [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.resolved .incomplete) := by
  native_decide

/- Formal failure retains the first authored component's exact cause. -/
example :
    evaluate? [
      numberCell 1 "bad" (.rejected .malformed),
      numberCell 2 "100" (.rejected .declaredConstraint)] =
        some (.unavailable .malformed) := by
  native_decide

/- Cause-free construction UNKNOWN cannot replace the checked wrapper: two formal causes
   remain distinguishable after the same shift. -/
example :
    ConstructedDateObservation.addLegacyDays? (.unavailable .malformed) 1 ≠
      ConstructedDateObservation.addLegacyDays?
        (.unavailable .declaredConstraint) 1 := by
  native_decide

/- Checked `Valid` and `Invalid` reuse the reason-bearing polarity table while retaining
   a formal component cause outside `Verdict`. -/
example :
    validVerdict? [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.fired .value)) ∧
      invalidVerdict? [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.fired .omission)) ∧
      invalidVerdict? [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.fired .value)) ∧
      validVerdict? [
        numberCell 1 "bad" (.rejected .malformed)] =
          some (.error .malformed) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/- Checked component extraction retains present versus fillable zero and the exact
   formal cause without adding a second numeric result family. -/
example :
    numericPart? .day [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.value 4 false)) ∧
      numericPart? .month [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.value 0 true)) ∧
      numericPart? .year [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582))] =
          some (.ok (.value 0 false)) ∧
      numericPart? .quarter [
        numberCell 1 "bad" (.rejected .declaredConstraint)] =
          some (.error .declaredConstraint) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/- A forged cause-free UNKNOWN is distinguishable from a checked formal cause. -/
example :
    ConstructedDateObservation.numericPart (.resolved .unknown) .day =
        .ok .unavailable ∧
      ConstructedDateObservation.numericPart
        (.unavailable .malformed) .day = .error .malformed := by
  constructor <;> rfl

/- Fractional and wrapped field amounts both use Java signed-32-bit narrowing before the
   legacy calendar shift. -/
example :
    let amount :=
      (elaborateTemporalFieldShiftAmount (dateModel "UTC") 4).toOption
    amount.bind (fun amount => shift? .days amount [
        numberCell 1 "31" (.parsed (.num 31)),
        numberCell 2 "1" (.parsed (.num 1)),
        numberCell 3 "2024" (.parsed (.num 2024)),
        numberCell 4 "1.5" (.parsed (.num (3 / 2)))]) =
          some (.value { year := 2024, month := 2, day := 1 } false) ∧
      amount.bind (fun amount => shift? .days amount [
        numberCell 1 "31" (.parsed (.num 31)),
        numberCell 2 "1" (.parsed (.num 1)),
        numberCell 3 "2024" (.parsed (.num 2024)),
        numberCell 4 "4294967297" (.parsed (.num 4294967297))]) =
          some (.value { year := 2024, month := 2, day := 1 } false) := by
  native_decide

/- Empty direct Number is a concrete zero shift with omission provenance; arithmetic
   domain failure is no-value and never becomes another zero shift. -/
example :
    let fieldAmount :=
      (elaborateTemporalFieldShiftAmount (dateModel "UTC") 4).toOption
    let expressionAmount :=
      (elaborateTemporalExpressionShiftAmount
        (dateModel "UTC") ["Order"] amountOverZero).toOption
    fieldAmount.bind (fun amount => shift? .months amount [
        numberCell 1 "31" (.parsed (.num 31)),
        numberCell 2 "1" (.parsed (.num 1)),
        numberCell 3 "2024" (.parsed (.num 2024))]) =
          some (.value { year := 2024, month := 1, day := 31 } true) ∧
      expressionAmount.bind (fun amount => shift? .months amount [
        numberCell 1 "31" (.parsed (.num 31)),
        numberCell 2 "1" (.parsed (.num 1)),
        numberCell 3 "2024" (.parsed (.num 2024)),
        numberCell 4 "1" (.parsed (.num 1))]) =
          some (.noValue false) := by
  native_decide

/- Generated source-before-amount evaluation retains the first source cause; once a real
   source is reached, the amount's exact formal cause becomes observable. -/
example :
    let amount :=
      (elaborateTemporalFieldShiftAmount (dateModel "UTC") 4).toOption
    amount.bind (fun amount => shift? .years amount [
        numberCell 1 "bad-day" (.rejected .malformed),
        numberCell 4 "bad-amount" (.rejected .declaredConstraint)]) =
          some (.unavailable .malformed) ∧
      amount.bind (fun amount => shift? .years amount [
        numberCell 1 "31" (.parsed (.num 31)),
        numberCell 2 "1" (.parsed (.num 1)),
        numberCell 3 "2024" (.parsed (.num 2024)),
        numberCell 4 "bad-amount" (.rejected .declaredConstraint)]) =
          some (.unavailable .declaredConstraint) := by
  native_decide

/- Checked day difference crosses the cutover hole as one step; month and year counting
   retain their established fresh-landing boundary. -/
example :
    difference? .days [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582)),
        numberCell 5 "15" (.parsed (.num 15)),
        numberCell 6 "10" (.parsed (.num 10)),
        numberCell 7 "1582" (.parsed (.num 1582))] =
          some (.numeric (.value 1 false)) ∧
      difference? .months [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "9" (.parsed (.num 9)),
        numberCell 3 "1582" (.parsed (.num 1582)),
        numberCell 5 "15" (.parsed (.num 15)),
        numberCell 6 "10" (.parsed (.num 10)),
        numberCell 7 "1582" (.parsed (.num 1582))] =
          some (.numeric (.value 0 false)) ∧
      difference? .years [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1581" (.parsed (.num 1581)),
        numberCell 5 "20" (.parsed (.num 20)),
        numberCell 6 "10" (.parsed (.num 10)),
        numberCell 7 "1582" (.parsed (.num 1582))] =
          some (.numeric (.value 1 false)) := by
  native_decide

/- Generated first-before-second evaluation preserves the first reached formal cause and
   exposes a second-source cause only after the first source resolves. -/
example :
    difference? .days [
        numberCell 1 "bad-first" (.rejected .malformed),
        numberCell 5 "bad-second" (.rejected .declaredConstraint)] =
          some (.formal .malformed) ∧
      difference? .days [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582)),
        numberCell 5 "bad-second" (.rejected .declaredConstraint)] =
          some (.formal .declaredConstraint) := by
  native_decide

/- Incomplete and present-but-unreal checked sources both yield zero through the shared
   numeric result, but retain omission versus fixed provenance. -/
example :
    difference? .months [
        numberCell 1 "4" (.parsed (.num 4)),
        numberCell 3 "1582" (.parsed (.num 1582)),
        numberCell 5 "20" (.parsed (.num 20)),
        numberCell 6 "10" (.parsed (.num 10)),
        numberCell 7 "1582" (.parsed (.num 1582))] =
          some (.numeric (.value 0 true)) ∧
      difference? .months [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "10" (.parsed (.num 10)),
        numberCell 3 "1582" (.parsed (.num 1582)),
        numberCell 5 "20" (.parsed (.num 20)),
        numberCell 6 "10" (.parsed (.num 10)),
        numberCell 7 "1582" (.parsed (.num 1582))] =
          some (.numeric (.value 0 false)) := by
  native_decide

end A12Kernel.Conformance.ConstructedDateEvaluation
