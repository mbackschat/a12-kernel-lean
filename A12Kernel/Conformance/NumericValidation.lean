import A12Kernel.Elaboration.NumericValidation

/-! # Checked numeric-validation integration locks -/

namespace A12Kernel.Conformance.NumericValidation

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }
private def signed : NumField := { scale := 0, signed := true }
private def scaleTwo : NumField := { scale := 2, signed := false }

private def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

private def dateTimeComponents : TemporalComponents :=
  { TemporalComponents.fullDate with
    hour := true, minute := true, second := true }

private def monthDayComponents : TemporalComponents :=
  { year := false, month := true, day := true,
    hour := false, minute := false, second := false }

private def model : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["Order"], name := "U",
        policy := { kind := .number unsigned } },
      { id := 1, groupPath := ["Order"], name := "V",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Order"], name := "Scale2",
        policy := { kind := .number scaleTwo } },
      { id := 3, groupPath := ["Order"], name := "Flag",
        policy := { kind := .boolean } },
      { id := 4, groupPath := ["Reference"], name := "Other",
        policy := { kind := .number unsigned } },
      { id := 5, groupPath := ["Order", "Items"], name := "Item",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 6, groupPath := ["Order"], name := "S",
        policy := { kind := .number signed } },
      { id := 8, groupPath := ["Order"], name := "Time",
        policy := { kind := .temporal .time timeComponents } },
      { id := 9, groupPath := ["Order"], name := "DateTime",
        policy := { kind := .temporal .dateTime dateTimeComponents } },
      { id := 11, groupPath := ["Order"], name := "NoYear",
        policy := { kind := .temporal .date monthDayComponents } },
      { id := 12, groupPath := ["Order"], name := "Code",
        policy := { kind := .string },
        stringPolicy := { lineBreaksPermitted := true } },
      { id := 13, groupPath := ["Order"], name := "NumericChoice",
        policy := { kind := .enumeration },
        enumeration := some {
          storedTokens := ["-1.50", "2", "03"]
          categories := [
            { name := "Factor", tokens := [".5", "2.25", "3"] },
            { name := "Whole", tokens := ["5", "225", "3"] }] } },
      { id := 14, groupPath := ["Order"], name := "MixedChoice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["1", "X"] } },
      { id := 15, groupPath := ["Order"], name := "BoundaryChoice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["-12345678901234.5"] } },
      { id := 16, groupPath := ["Order"], name := "WideChoice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["1234567890123456"] } }],
    repeatableGroups := [{ level := 10, path := ["Order", "Items"] }] }

private def baseYearModel : FlatModel := { model with baseYear := some 2020 }

private def path (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def atom (name : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (path ["Order"] name))

private def baseYear : AuthoredNumericExpr SurfaceNumericAtom := .atom .baseYear

private def baseYearDatePart (source : BaseYearDateSource)
    (part : DateNumericPart) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.baseYearDatePart source part)

private def dateFieldPart (name : String) (part : DateNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (path ["Order"] name) (.date part))

private def timeFieldPart (name : String) (part : TimeNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (path ["Order"] name) (.time part))

private def dateDifference (unit : DateDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateDifference unit left right)

private def stringRange (start finish : Nat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.stringRange (path ["Order"] "Code") start finish)

private def fieldValueAsNumber
    (source : SurfaceTextFieldOperand := .direct (path ["Order"] "NumericChoice")) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber source)

private def dateOperand (name : String) : SurfaceDateDifferenceOperand :=
  .field (path ["Order"] name)

private def literal (value : Rat) (authoredScale : Int) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale }

private def aggregate (op : NumericAggregateOp) (first : String)
    (rest : List String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.aggregate op {
    first := path ["Order"] first
    rest := rest.map (path ["Order"]) })

private def comparison (op : NumericComparisonOp)
    (left : AuthoredNumericExpr SurfaceNumericAtom)
    (rightValue : Rat) (rightScale : Int := 0) :
    SurfaceNumericComparison :=
  { op := .ordinary op, left, right := literal rightValue rightScale }

private def twoSided (op : NumericComparisonOp)
    (left right : AuthoredNumericExpr SurfaceNumericAtom) :
    SurfaceNumericComparison :=
  { op := .ordinary op, left, right }

private def raw (u v s scale2Value : RawCell := .empty) : RawFlatContext where
  read id :=
    if id == 0 then u else if id == 1 then v else if id == 2 then scale2Value
      else if id == 6 then s else .empty

private def temporalRaw (id : FieldId) (cell : RawCell) : RawFlatContext where
  read actual := if actual == id then cell else .empty

private def stringRaw (cell : RawCell) : RawFlatContext where
  read actual := if actual == 12 then cell else .empty

private def enumerationRaw (cell : RawCell) : RawFlatContext where
  read actual := if actual == 13 then cell else .empty

private def instant : Instant := { epochMillis := 1719292867000 }

private def dateParts : DateParts := { year := 2024, month := 6, day := 25 }

private def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def dateTimeValue : Value :=
  .temporal (.dateTime instant dateParts clock .storedGregorian)

private def dateValue (year : Int) (month day : Nat)
    (basis : DateCalendarBasis := .storedGregorian) : Value :=
  .temporal (.date instant { year, month, day } basis)

private def verdictOf (surface : SurfaceNumericComparison)
    (context : RawFlatContext := raw) (hasContent : Bool := true)
    (sourceModel : FlatModel := model) : Option Verdict :=
  (elaborateAndEvalNumericComparison sourceModel ["Order"] context hasContent surface).toOption

private def errorOf (surface : SurfaceNumericComparison)
    (sourceModel : FlatModel := model) :
    Option NumericValidationElabError :=
  match elaborateNumericComparison sourceModel ["Order"] surface with
  | .ok _ => none
  | .error error => some error

private def suppressScaleWarning
    (surface : SurfaceNumericComparison) : SurfaceNumericComparison :=
  { surface with suppressExactScaleWarning := true }

private def tolerance (range : NumericToleranceRange)
    (left right : AuthoredNumericExpr SurfaceNumericAtom) :
    SurfaceNumericComparison :=
  { op := .tolerance range, left, right }

private def dividedThird : AuthoredNumericExpr SurfaceNumericAtom :=
  .group (.binary .divide (literal 3 0) (literal 3 0))

/- The checked decimal-token parser preserves the admitted ASCII subset without accepting a leading plus, exponent syntax, trailing dots, or whitespace beyond the kernel source grammar. -/
example :
    (parseAsciiDecimalToken? "-1.50").map
        (fun token => (token.value, token.scale, token.digitCount)) =
      some ((-3 / 2 : Rat), 2, 3) ∧
    (parseAsciiDecimalToken? ".5").map (fun token => token.value) =
      some (1 / 2 : Rat) ∧
    parseAsciiDecimalToken? "1." = none ∧
    parseAsciiDecimalToken? "+1" = none ∧
    parseAsciiDecimalToken? "1e2" = none ∧
    parseAsciiDecimalToken? " 1" = none := by
  native_decide

/- `FieldValueAsNumber` projects stored or category tokens before exact rational conversion; a filled result is fixed. -/
example :
    verdictOf (comparison .equal (fieldValueAsNumber) 2 2)
        (enumerationRaw (.parsed (.enum "2"))) = some (.fired .value) ∧
      verdictOf (comparison .equal
        (fieldValueAsNumber (.category
          (path ["Order"] "NumericChoice") "Factor")) (1 / 2) 2)
        (enumerationRaw (.parsed (.enum "-1.50"))) = some (.fired .value) ∧
      verdictOf (comparison .equal (fieldValueAsNumber) 3 2)
        (enumerationRaw (.parsed (.enum "03"))) = some (.fired .value) ∧
      verdictOf (comparison .less (fieldValueAsNumber) 100)
        (enumerationRaw (.parsed (.enum "2"))) = some (.fired .value) := by
  native_decide

/- An absent convertible source denotes zero with both directional fill possibilities, while a reached formal cause remains unknown. -/
example :
    verdictOf (comparison .less (fieldValueAsNumber) 100)
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater (fieldValueAsNumber) (-100))
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .equal (fieldValueAsNumber) 0 2)
        (enumerationRaw (.rejected .declaredConstraint)) = some .unknown := by
  native_decide

/- Admission derives the selected-domain scale and preserves field resolution, category, and convertibility diagnostics. String conversion remains fail-closed until its exact pattern fact has a checked owner. -/
example :
    (elaborateNumericComparison model ["Order"]
      (twoSided .equal (fieldValueAsNumber) (atom "Scale2"))).isOk = true ∧
    (elaborateNumericComparison model ["Order"]
      (twoSided .equal
        (fieldValueAsNumber (.category
          (path ["Order"] "NumericChoice") "Whole")) (atom "U"))).isOk = true ∧
    (elaborateNumericComparison model ["Order"]
      (comparison .greater
        (fieldValueAsNumber (.direct
          (path ["Order"] "BoundaryChoice"))) 0)).isOk = true ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "Missing"))) 0) =
        some (.resolve (.invalidEntity (path ["Order"] "Missing"))) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "Code"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "Code"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "MixedChoice"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "MixedChoice"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "WideChoice"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "WideChoice"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.category
        (path ["Order"] "NumericChoice") "Missing")) 0) =
        some (.fieldValueAsNumberEnumeration ["Order", "NumericChoice"]
          (.unknownCategory "Missing")) := by
  native_decide

/- The operation-form rounding wrapper is legal over the converted numeric atom, uses the selected category token, replaces its static scale with the authored places, and preserves symmetric missing fillability. -/
example :
    verdictOf (comparison .equal
        (.round .halfUp omittedRoundingPlaces
          (fieldValueAsNumber (.category
            (path ["Order"] "NumericChoice") "Factor"))) 1)
        (enumerationRaw (.parsed (.enum "-1.50"))) = some (.fired .value) ∧
      verdictOf (comparison .less
        (.round .halfUp omittedRoundingPlaces fieldValueAsNumber) 100)
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater
        (.round .halfUp omittedRoundingPlaces fieldValueAsNumber) (-100))
        (enumerationRaw .empty) = some (.fired .omission) ∧
      (elaborateNumericComparison model ["Order"]
        (twoSided .equal
          (.round .halfUp omittedRoundingPlaces fieldValueAsNumber)
          (atom "U"))).isOk = true := by
  native_decide

/- Absolute value is independently legal over the conversion. It preserves the selected source scale, but at missing numeric zero it collapses the impossible shrinking-magnitude direction instead of copying symmetric source fillability. -/
example :
    verdictOf (comparison .equal (.abs fieldValueAsNumber) (3 / 2) 2)
        (enumerationRaw (.parsed (.enum "-1.50"))) = some (.fired .value) ∧
      verdictOf (comparison .less (.abs fieldValueAsNumber) 100)
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater (.abs fieldValueAsNumber) (-100))
        (enumerationRaw .empty) = some (.fired .value) ∧
      (elaborateNumericComparison model ["Order"]
        (twoSided .equal (.abs fieldValueAsNumber) (atom "Scale2"))).isOk = true ∧
      errorOf (comparison .equal (.abs (stringRange 1 2)) 0) =
        some .unsupportedExpression := by
  native_decide

/- `RangeAsNumber` parses only a complete ASCII digit slice; filled fallback zero is fixed. -/
example :
    verdictOf (comparison .equal (stringRange 1 2) 12)
        (stringRaw (.parsed (.str "12X"))) = some (.fired .value) ∧
      verdictOf (comparison .equal (stringRange 1 2) 0)
        (stringRaw (.parsed (.str "AB3"))) = some (.fired .value) ∧
      verdictOf (comparison .equal (stringRange 1 2) 0)
        (stringRaw (.parsed (.str "A"))) = some (.fired .value) := by
  native_decide

/- Only an absent source makes the nonnegative result growable; a present non-digit zero is fixed. -/
example :
    verdictOf (comparison .less (stringRange 1 2) 100)
        (stringRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater (stringRange 1 2) (-100))
        (stringRaw .empty) = some (.fired .value) ∧
      verdictOf (comparison .less (stringRange 1 2) 100)
        (stringRaw (.parsed (.str "AB"))) = some (.fired .value) := by
  native_decide

/- The checked String cache is normalized before slicing. -/
example :
    verdictOf (comparison .equal (stringRange 3 3) 2)
      (stringRaw (.parsed (.str "1\r\n2"))) = some (.fired .value) := by
  native_decide

/- A JVM half-surrogate slice has no scalar String representation in Lean and therefore follows the operation's ordinary numeric-zero fallback. -/
example :
    verdictOf (comparison .equal (stringRange 2 2) 0)
      (stringRaw (.parsed (.str "A😀B"))) = some (.fired .value) := by
  native_decide

/- Field shape resolves before the interval; the interval precedes kind admission. -/
example :
    errorOf (comparison .equal
      (.atom (.stringRange (path ["Order"] "Missing") 0 2)) 0) =
        some (.resolve (.invalidEntity (path ["Order"] "Missing"))) ∧
      errorOf (comparison .equal
        (.atom (.stringRange (path ["Order"] "U") 0 2)) 0) =
        some (.invalidStringRange 0 2) ∧
      errorOf (comparison .equal
        (.atom (.stringRange (path ["Order"] "U") 1 2)) 0) =
        some (.rangeOperandNotString ["Order", "U"]) := by
  native_decide

/- Checked tolerance bypasses exact-comparison scale agreement and preserves directional arithmetic fillability. -/
example : (elaborateNumericComparison model ["Order"]
    (tolerance .range1 (atom "U") (atom "Scale2"))).isOk = true := by
  native_decide

example :
    errorOf (twoSided .equal (atom "U") baseYear) =
      some .baseYearNotDeclared ∧
    errorOf (twoSided .equal (atom "Scale2") baseYear) baseYearModel =
      some (.exactScaleMismatch
        (NumericScaleSummary.field 2) (NumericScaleSummary.field 0)) ∧
    (elaborateNumericComparison baseYearModel ["Order"]
      (tolerance .range1 (atom "Scale2") baseYear)).isOk = true ∧
    errorOf (twoSided .equal (.abs baseYear) (atom "U")) baseYearModel =
      some .unsupportedExpression := by
  native_decide

example :
    verdictOf (tolerance .range1 (atom "U") baseYear)
        (raw (.parsed (.num 2022))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal (atom "U") baseYear)
        (raw (.parsed (.num 2020))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal
        (.binary .add baseYear (atom "U")) (literal 2021 0))
        (raw (.parsed (.num 1))) true baseYearModel = some (.fired .value) := by
  native_decide

example : errorOf (twoSided .equal baseYear (literal 2020 0)) baseYearModel =
    some .constantExpression := by
  native_decide

example :
    let directYear := baseYearDatePart .direct .year
    let finishDay := baseYearDatePart (.range .finish) .day
    let finishQuarter := baseYearDatePart (.range .finish) .quarter
    errorOf (twoSided .equal (atom "U") finishDay) =
        some .baseYearNotDeclared ∧
      verdictOf (twoSided .equal (atom "U") directYear)
        (raw (.parsed (.num 2020))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal (atom "U") finishDay)
        (raw (.parsed (.num 31))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal (atom "U") finishQuarter)
        (raw (.parsed (.num 4))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal
        (.binary .add (atom "U") finishDay) (literal 32 0))
        (raw (.parsed (.num 1))) true baseYearModel = some (.fired .value) := by
  native_decide

example :
    let finishDay := baseYearDatePart (.range .finish) .day
    errorOf (twoSided .equal finishDay (literal 31 0)) baseYearModel =
        some .constantExpression ∧
      errorOf (twoSided .equal (.abs finishDay) (atom "U")) baseYearModel =
        some .unsupportedExpression ∧
      errorOf (twoSided .equal (atom "Scale2") finishDay) baseYearModel =
        some (.exactScaleMismatch
          (NumericScaleSummary.field 2) (NumericScaleSummary.field 0)) := by
  native_decide

example : verdictOf
    (tolerance .range1
      (atom "U")
      (.binary .add (atom "V") (literal 2 0)))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (tolerance .range1
      (atom "U")
      (.binary .subtract (atom "V") (literal 2 0)))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- The closed band is not ordinary inequality: its exact endpoint remains quiet. -/
example : verdictOf
    (tolerance .range1 (atom "U") (literal 1 0))
    (raw (.parsed (.num 0))) = some .notFired := by
  native_decide

example : verdictOf
    (comparison .notEqual (atom "U") 1)
    (raw (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- The checked bridge keeps formal invalidity, pure arithmetic domain failure, and the row gate distinct. -/
example : verdictOf
    (tolerance .range1 (atom "U") (literal 5 0))
    (raw (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (tolerance .range1
      (.binary .divide (literal 1 0) (atom "U"))
      (literal 5 0)) = some .notFired := by
  native_decide

example : verdictOf
    (tolerance .range1 (atom "U") (literal 5 0))
    raw false = some .notFired := by
  native_decide

/- Tolerance shares the checked expression subset and still rejects constant-only trees. -/
example : errorOf
    (tolerance .range1 (literal 0 0) (literal 5 0)) =
      some .constantExpression := by
  native_decide

example : verdictOf
    (tolerance .range1 (.power (atom "U") (literal 2 0)) (literal 5 0))
    (raw (.parsed (.num 1))) = some (.fired .value) := by
  native_decide

/- The right operand's grow-only empty Number changes a true comparison from VALUE to OMISSION. -/
example : verdictOf
    (twoSided .greaterEqual (atom "V") (atom "U"))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (twoSided .greaterEqual (atom "V") (atom "U"))
    (raw (.parsed (.num 0)) (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- Right-side movement is directional, not a generic "some input was empty" bit. -/
example : verdictOf
    (twoSided .less
      (atom "V")
      (.binary .add (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (twoSided .less
      (atom "V")
      (.binary .subtract (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (twoSided .notEqual
      (atom "V")
      (.binary .add (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (twoSided .notEqual
      (atom "V")
      (.binary .subtract (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

/- In a content-bearing selected row, the runtime reads aliases independently; the fillability abstraction has no dependency deduplication. -/
example : verdictOf
    (twoSided .equal (atom "U") (atom "U")) =
      some (.fired .omission) := by
  native_decide

/- Equality-boundary cases separate the strict and inclusive operators. -/
example : verdictOf
    (twoSided .greater (atom "V") (atom "U"))
    (raw .empty (.parsed (.num 0))) = some .notFired := by
  native_decide

example : verdictOf
    (twoSided .lessEqual (atom "V") (atom "U"))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- This one case crosses checked paths, empty substitution, static ordering legality, arithmetic fillability, scale-19 comparison, polarity, and the row gate. -/
example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") dividedThird) 0) =
      some (.fired .value) := by
  native_decide

private def precisionAmplifier : Rat := 10 ^ 31

private def amplifiedThird : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .multiply
    (.binary .multiply
      (atom "U")
      (.group (.binary .divide (literal 1 0) (literal 3 0))))
    (literal precisionAmplifier (-31))

/- The checked consumer must use the one-pass lowered tree, not directly fold the authored tree. -/
example : verdictOf
    (comparison .greaterEqual amplifiedThird precisionAmplifier (-31))
    (raw (.parsed (.num 3))) = some (.fired .value) := by
  native_decide

/- The same lowering stage is independently required on the right comparison operand. -/
example : verdictOf
    (twoSided .less
      (literal (precisionAmplifier - 1 / (10 ^ 19)) 19)
      amplifiedThird)
    (raw (.parsed (.num 3))) = some (.fired .value) := by
  native_decide

/- Tolerance consumes the same one-pass lowered tree: the lowered gap is exactly the closed range-1 boundary. -/
example : verdictOf
    (tolerance .range1
      amplifiedThird
      (literal (precisionAmplifier + 1) 0))
    (raw (.parsed (.num 3))) = some .notFired := by
  native_decide

/- A counterfactual direct authored fold would retain a scale-19-visible gap beyond the band and fire. -/
example : NumericToleranceRange.range1.eval
    (.value (precisionAmplifier - 1 / (10 ^ 19)) .fixed)
    (.value (precisionAmplifier + 1) .fixed) = .fired .value := by
  native_decide

/- Both total binary branches are exercised through the integrated checked route. -/
example : verdictOf
    (comparison .equal
      (.binary .subtract
        (.binary .add (atom "U") (literal 3 0))
        (literal 1 0))
      7)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") dividedThird) 0)
    raw false = some .notFired := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") (literal (-4) 0)) (-100)) =
      some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") (literal (-4) 0)) (-100))
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") (literal (-4) 0)) (-100))
    (raw (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (comparison .less (.binary .divide (literal 1 0) (atom "U")) 100) =
      some .notFired := by
  native_decide

example : verdictOf
    (twoSided .less (literal 0 0) (atom "V"))
    (raw .empty (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (twoSided .less
      (literal 0 0)
      (.binary .divide (literal 1 0) (atom "U"))) =
      some .notFired := by
  native_decide

/- The Lean projection conservatively keeps formal invalidity unknown beside a domain failure; this mixed internal precedence is not a kernel-correspondence claim. -/
example : verdictOf
    (twoSided .less
      (.binary .divide (literal 1 0) (atom "U"))
      (atom "V"))
    (raw .empty (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (twoSided .less
      (atom "V")
      (.binary .divide (literal 1 0) (atom "U")))
    (raw .empty (.rejected .malformed)) = some .unknown := by
  native_decide

/- Exact comparison accepts padding only on the expandable, smaller-scale side. -/
example : (elaborateNumericComparison model ["Order"]
    (comparison .equal (atom "Scale2") 0)).isOk = true := by
  native_decide

example : errorOf (comparison .equal (atom "U") 0 2) =
    some (.exactScaleMismatch
      { scale := .exact 0, canExpandScale := false }
      { scale := .exact 2, canExpandScale := true }) := by
  native_decide

example : errorOf (comparison .notEqual (atom "U") 0 2) =
    some (.exactScaleMismatch
      { scale := .exact 0, canExpandScale := false }
      { scale := .exact 2, canExpandScale := true }) := by
  native_decide

example : errorOf (twoSided .equal (atom "U") (atom "Scale2")) =
    some (.exactScaleMismatch
      { scale := .exact 0, canExpandScale := false }
      { scale := .exact 2, canExpandScale := false }) := by
  native_decide

/- The one legal warning suppression bypasses exact scale rejection without changing the evaluated comparison. -/
example : verdictOf
    (suppressScaleWarning (comparison .equal (atom "U") 0 2))
    (raw (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (suppressScaleWarning
      (twoSided .notEqual (atom "U") (atom "Scale2")))
    (raw (.parsed (.num 0)) .empty .empty (.parsed (.num 1))) =
      some (.fired .value) := by
  native_decide

example : (elaborateNumericComparison model ["Order"]
    (twoSided .greater (atom "U") (atom "Scale2"))).isOk = true := by
  native_decide

/- Division has unknown derived scale: ordering admits it, exact comparison does not. -/
example : (elaborateNumericComparison model ["Order"]
    (comparison .less (.binary .divide (atom "U") (literal 2 0)) 0)).isOk = true := by
  native_decide

example : errorOf
    (comparison .equal (.binary .divide (atom "U") (literal 2 0)) 0) =
      some (.exactScaleMismatch
        { scale := .unknown, canExpandScale := false }
        { scale := .exact 0, canExpandScale := true }) := by
  native_decide

/- Suppression also admits the kernel's unknown derived scale rather than guessing a concrete scale. -/
example : verdictOf
    (suppressScaleWarning
      (comparison .equal
        (.binary .divide (atom "U") (literal 2 0)) 2))
    (raw (.parsed (.num 4))) = some (.fired .value) := by
  native_decide

/- Suppression is not a general authoring escape hatch. -/
example : errorOf
    (suppressScaleWarning
      (comparison .equal
        (.binary .divide
          (.binary .divide (atom "U") (literal 2 0))
          (literal 3 0))
        0)) = some (.authoring .tooManyDivisions) := by
  native_decide

/- Division-region legality resets at the comparison boundary, so one division on each side is accepted. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .less
      (.binary .divide (atom "U") (literal 2 0))
      (.binary .divide (atom "V") (literal 3 0)))).isOk = true := by
  native_decide

example : errorOf
    (comparison .less
      (.binary .divide
        (.binary .divide (atom "U") (literal 2 0))
        (literal 3 0))
      0) = some (.authoring .tooManyDivisions) := by
  native_decide

example : errorOf
    (twoSided .less
      (atom "U")
      (.binary .divide
        (.binary .divide (atom "V") (literal 2 0))
        (literal 3 0))) =
      some (.authoring .tooManyDivisions) := by
  native_decide

/- Checked power reuses authored scale, nesting, runtime value, and directional-fillability semantics. -/
example : verdictOf
    (comparison .equal (.power (atom "U") (literal 2 0)) 4)
    (raw (.parsed (.num 2))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .less (.power (atom "U") (literal 2 0)) 10) =
      some (.fired .omission) := by
  native_decide

/- Runtime-invalid integral regions project to quiet validation domain failure. -/
example : verdictOf
    (comparison .less (.power (atom "U") (literal (-1) 0)) 1)
    (raw (.parsed (.num 0))) = some .notFired := by
  native_decide

example : verdictOf
    (comparison .less (.power (atom "U") (literal 1001 0)) 1)
    (raw (.parsed (.num 2))) = some .notFired := by
  native_decide

/- Empty exponent polarity is not a generic given-bit: unsigned and signed zero exponents produce different directions at fixed base zero. -/
example : verdictOf
    (comparison .greaterEqual (.power (literal 0 0) (atom "U")) 1) =
      some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.power (literal 0 0) (atom "S")) 1) =
      some (.fired .value) := by
  native_decide

/- Fractional-scale exponents remain a static rejection before runtime. -/
example : errorOf
    (comparison .less
      (.power (atom "U") (literal ((1 : Rat) / 2) 1)) 1) =
      some .unsupportedExpression := by
  native_decide

/- Direct-left nested power is rejected, while grouping creates the legal fresh authoring region. -/
example : errorOf
    (comparison .less
      (.power (.power (atom "U") (literal 2 0)) (literal 3 0)) 100) =
      some (.authoring .directLeftNestedPower) := by
  native_decide

example : verdictOf
    (comparison .less
      (.power (.group (.power (atom "U") (literal 2 0))) (literal 3 0)) 100)
    (raw (.parsed (.num 2))) = some (.fired .value) := by
  native_decide

/- A source-confirmed root rounding operation is admitted without widening the unclosed wrapper traversal. -/
example : verdictOf
    (comparison .less (.round .halfUp omittedRoundingPlaces (atom "U")) 1) =
      some (.fired .omission) := by
  native_decide

/- The checked route retains the existing negative half-tie behavior. The mode-parametric delegation law covers all three modes without duplicating their pure matrix here. -/
example : verdictOf
    (comparison .equal (.round .halfUp omittedRoundingPlaces (atom "U")) (-3))
    (raw (.parsed (.num ((-25 : Rat) / 10)))) = some (.fired .value) := by
  native_decide

/- The independently traversed right operand uses the same admitted root-rounding seam. -/
example : verdictOf
    (twoSided .equal
      (literal 1 0)
      (.round .floor omittedRoundingPlaces (atom "U")))
    (raw (.parsed (.num ((16 : Rat) / 10)))) = some (.fired .value) := by
  native_decide

/- The rounded result's authored places, rather than the source field's scale, control exact-comparison admission. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal
      (.round .halfUp ⟨2, by decide⟩ (atom "U"))
      (atom "Scale2"))).isOk = true := by
  native_decide

/- Formal invalidity survives the wrapper instead of becoming a rounded zero. -/
example : verdictOf
    (comparison .less (.round .halfUp omittedRoundingPlaces (atom "U")) 1)
    (raw (.rejected .malformed)) = some .unknown := by
  native_decide

/- Nested wrapper/arithmetic authoring remains deliberately outside this checked fragment. -/
example : errorOf
    (comparison .less
      (.binary .add
        (.round .halfUp omittedRoundingPlaces (atom "U"))
        (literal 1 0))
      0) = some .unsupportedExpression := by
  native_decide

/- Root rounding over arithmetic is the opposite unclosed nesting direction and must not be mistaken for direct-field rounding. -/
example : errorOf
    (comparison .less
      (.round .halfUp omittedRoundingPlaces
        (.binary .add (atom "U") (literal 1 0)))
      0) = some .unsupportedExpression := by
  native_decide

/- Root absolute value is the second admitted numeric value function. Its sign-sensitive fillability is visible for signed empty input. -/
example : verdictOf (comparison .greaterEqual (.abs (atom "S")) 0) =
    some (.fired .value) := by
  native_decide

example : verdictOf (comparison .equal (.abs (atom "S")) 5)
    (raw .empty .empty (.parsed (.num (-5)))) = some (.fired .value) := by
  native_decide

/- The independently traversed right operand applies the same absolute-value seam. -/
example : verdictOf
    (twoSided .equal (literal 5 0) (.abs (atom "S")))
    (raw .empty .empty (.parsed (.num (-5)))) = some (.fired .value) := by
  native_decide

example : verdictOf (comparison .less (.abs (atom "S")) 1)
    (raw .empty .empty (.rejected .malformed)) = some .unknown := by
  native_decide

/- Absolute value preserves the operand's static scale. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal (.abs (atom "Scale2")) (atom "Scale2"))).isOk = true := by
  native_decide

/- Both wrapper/arithmetic nesting directions remain outside the checked boundary. -/
example : errorOf
    (comparison .less
      (.binary .add (.abs (atom "U")) (literal 1 0))
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (.abs (.binary .add (atom "U") (literal 1 0)))
      0) = some .unsupportedExpression := by
  native_decide

/- Checked multi-operand Min/Max use one root over direct same-group Number fields. Empty Number remains a directional zero competitor. -/
example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "V"]) 100)
    (raw .empty (.parsed (.num 4))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greater
      (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "V"]) (-100))
    (raw .empty (.parsed (.num 4))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .greater
      (AuthoredNumericExpr.extremumList .maximum (atom "S") [atom "V"]) (-100))
    (raw .empty (.parsed (.num (-4))) .empty) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [atom "V", atom "S"])
      100)
    (raw (.parsed (.num 2)) (.parsed (.num 4)) (.rejected .malformed)) =
      some .unknown := by
  native_decide

/- Min/Max derive the maximum operand scale for the ordinary equality gate. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal
      (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "Scale2"])
      (atom "Scale2"))).isOk = true := by
  native_decide

/- The checked root remains deliberately narrower than general wrapper traversal in either direction. -/
example : errorOf
    (comparison .less
      (.binary .add
        (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "V"])
        (literal 1 0))
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (.binary .add (atom "U") (literal 1 0))
        [atom "V"])
      0) = some .unsupportedExpression := by
  native_decide

/- One direct top-level constant may occur at any position in the canonical operand list. -/
example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum (literal 5 0) [atom "U"])
      10) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greater
      (AuthoredNumericExpr.extremumList .maximum
        (atom "U") [literal 5 0, atom "V"])
      4)
    (raw .empty (.parsed (.num 4))) = some (.fired .value) := by
  native_decide

/- The constant participates in the ordinary static summary without making the field-bearing fold a constant expression. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [literal 0 2])
      (atom "Scale2"))).isOk = true := by
  native_decide

/- Two constants, a grouped constant, and a noncanonical right-nested fold remain outside the admitted source shape. -/
example : errorOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [literal 1 0, literal 2 0])
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [.group (literal 1 0)])
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (.extremum .minimum (atom "U")
        (.extremum .minimum (atom "V") (literal 1 0)))
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (.extremum .minimum
        (.extremum .maximum (atom "U") (atom "V"))
        (atom "S"))
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf (comparison .equal (literal 0 0) 0) =
    some .constantExpression := by
  native_decide

example : errorOf (comparison .equal (atom "Flag") 0) =
    some (.fieldNotNumber ["Order", "Flag"]) := by
  native_decide

example : errorOf (twoSided .equal (atom "U") (atom "Flag")) =
    some (.fieldNotNumber ["Order", "Flag"]) := by
  native_decide

/- Direct temporal component functions enter the same checked scale-0 numeric tree. DateTime supplies either half, while empty remains the symmetric numeric zero. -/
example :
    verdictOf (comparison .equal (dateFieldPart "DateTime" .day) 25)
        (temporalRaw 9 (.parsed dateTimeValue)) = some (.fired .value) ∧
      verdictOf (comparison .equal (dateFieldPart "DateTime" .quarter) 2)
        (temporalRaw 9 (.parsed dateTimeValue)) = some (.fired .value) ∧
      verdictOf (comparison .equal (timeFieldPart "DateTime" .minute) 21)
        (temporalRaw 9 (.parsed dateTimeValue)) = some (.fired .value) ∧
      verdictOf (comparison .less (timeFieldPart "Time" .hour) 3)
        (temporalRaw 8 .empty) = some (.fired .omission) := by
  native_decide

/- Component presence, family compatibility, and the Base-Year year supplement are checked before runtime reads. -/
example :
    errorOf (comparison .equal (dateFieldPart "Time" .day) 1) =
        some (.incompatibleTemporalSource ["Order", "Time"]) ∧
      errorOf (comparison .equal (timeFieldPart "NoYear" .hour) 1) =
        some (.incompatibleTemporalSource ["Order", "NoYear"]) ∧
      errorOf (comparison .equal (dateFieldPart "NoYear" .year) 2024) =
        some (.incompatibleTemporalSource ["Order", "NoYear"]) ∧
      errorOf (comparison .equal (dateFieldPart "NoYear" .year) 2024)
        baseYearModel = none := by
  native_decide

/- Temporal component sources are field-bearing plain-arithmetic atoms; unsupported value-function wrappers stay fail-closed. -/
example :
    errorOf (comparison .equal (.abs (dateFieldPart "DateTime" .day)) 25) =
        some .unsupportedExpression ∧
      verdictOf (comparison .equal
        (.binary .add (dateFieldPart "DateTime" .day) (atom "U")) 26)
        (let context := temporalRaw 9 (.parsed dateTimeValue)
         { read := fun id => if id == 0 then .parsed (.num 1) else context.read id }) =
        some (.fired .value) := by
  native_decide

/- Field/Base-Year differences reuse the decoded Date payload and preserve symmetric empty-zero polarity; DateTime, legacy-hybrid payloads, and wrappers stay fail-closed. -/
example :
    let mixed := dateDifference .months (.baseYear .direct) (dateOperand "NoYear")
    errorOf (comparison .equal mixed 1) = some .baseYearNotDeclared ∧
      verdictOf (comparison .equal mixed 1)
        (temporalRaw 11 (.parsed (dateValue 2020 2 29))) true baseYearModel =
          some (.fired .value) ∧
      verdictOf (comparison .less mixed 3)
        (temporalRaw 11 .empty) true baseYearModel = some (.fired .omission) ∧
      verdictOf (comparison .less mixed 3)
        (temporalRaw 11 (.rejected .malformed)) true baseYearModel = some .unknown ∧
      errorOf (comparison .equal
        (dateDifference .years (dateOperand "DateTime") (.baseYear .direct)) 0)
        baseYearModel = some (.incompatibleTemporalSource ["Order", "DateTime"]) ∧
      verdictOf (comparison .equal mixed 1)
        (temporalRaw 11 (.parsed (dateValue 2020 2 29 .legacyHybrid))) true
        baseYearModel = some .unknown ∧
      errorOf (comparison .equal (.abs mixed) 1) baseYearModel =
        some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .equal (.atom (.field (path ["Order", "Items"] "Item"))) 0) =
      some (.resolve (.repeatableReference ["Order", "Items", "Item"])) := by
  native_decide

example : errorOf
    (comparison .equal (.atom (.field (path ["Reference"] "Other"))) 0) =
      some (.fieldOutsideRowGroup ["Reference", "Other"] ["Order"]) := by
  native_decide

/- Direct field-list aggregates are ordinary numeric-expression atoms: arithmetic and comparison polarity reuse the existing expression and aggregate evaluators. -/
example : verdictOf
    (comparison .greater
      (.binary .add (aggregate .sum "U" ["V"]) (literal 1 0)) 10)
    (raw (.parsed (.num 4)) (.parsed (.num 6))) =
      some (.fired .value) := by
  native_decide

example :
    verdictOf (comparison .less (aggregate .sum "U" ["V"]) 10)
        (raw (.parsed (.num 4))) = some (.fired .omission) ∧
      verdictOf (comparison .less (aggregate .sum "U" ["V"]) 1) =
        some (.fired .omission) ∧
      verdictOf (comparison .greater (aggregate .minimum "U" ["V"]) 10)
        (raw (.parsed (.num 20))) = some (.fired .omission) ∧
      verdictOf (comparison .less (aggregate .minimum "U" ["V"]) 10)
        (raw (.parsed (.num 20))) = some .notFired ∧
      verdictOf (comparison .greater (aggregate .maximum "U" ["V"]) 10)
        (raw (.parsed (.num 20)) (.rejected .declaredConstraint)) =
        some .unknown := by
  native_decide

/- Aggregate scale is the maximum declaration scale, without literal expansion capability. -/
example :
    (elaborateNumericComparison model ["Order"]
      (twoSided .equal (aggregate .sum "U" ["Scale2"])
        (atom "Scale2"))).isOk = true ∧
      errorOf (twoSided .equal (aggregate .sum "U" ["Scale2"])
        (atom "U")) = some (.exactScaleMismatch
          (NumericScaleSummary.field 2) (NumericScaleSummary.field 0)) := by
  native_decide

/- NumberOfDifferentValues is an integral aggregate independently of operand declarations, and its grow-only missing state reaches ordinary comparison polarity. -/
example :
    errorOf (twoSided .equal
      (aggregate .distinctCount "U" ["Scale2"]) (atom "U")) = none ∧
    verdictOf (comparison .equal
      (aggregate .distinctCount "U" ["V"]) 1)
      (raw (.parsed (.num 5)) (.parsed (.num 5))) =
        some (.fired .value) ∧
    verdictOf (comparison .less
      (aggregate .distinctCount "U" ["V"]) 1) =
        some (.fired .omission) := by
  native_decide

/- The aggregate owner retains wrong-kind and repeatable-source diagnostics rather than collapsing them into a generic expression rejection. -/
example :
    errorOf (comparison .greater (aggregate .sum "U" ["Flag"]) 0) =
        some (.aggregate (.fieldKindMismatch ["Order", "Flag"] .boolean)) := by
  native_decide

example :
    errorOf (comparison .greater
      (.atom (.aggregate .sum {
        first := path ["Order"] "U"
        rest := [path ["Reference"] "Other"] })) 0) =
      some (.fieldOutsideRowGroup ["Reference", "Other"] ["Order"]) := by
  native_decide

example :
    errorOf (comparison .greater
      (.atom (.aggregate .sum {
        first := path ["Order"] "U"
        rest := [path ["Order", "Items"] "Item"] })) 0) =
      some (.aggregate (.resolve (.repeatableReference
        ["Order", "Items", "Item"]))) := by
  native_decide

private def aggregateTraversal : Option (Bool × Bool × Bool × Bool) := do
  let checked ← (elaborateNumericComparison model ["Order"]
    (comparison .greater (aggregate .sum "U" ["V"]) 0)).toOption
  pure (checked.core.referencesField 0,
    checked.core.referencesField 1,
    checked.core.allRelevant (fun field => field == 0),
    checked.core.allRelevant (fun field => field == 0 || field == 1))

example : aggregateTraversal = some (true, true, false, true) := by
  native_decide

end A12Kernel.Conformance.NumericValidation
