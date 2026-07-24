import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Semantics.DateTimeDayDifference

/-! # Checked numeric-validation conformance support

Shared declarations and evaluators used by at least two focused numeric-validation conformance modules. Family-specific fixtures stay in their owning module.
-/

namespace A12Kernel.Conformance.NumericValidation.Support

open A12Kernel

def unsigned : NumField := { scale := 0, signed := false }
def signed : NumField := { scale := 0, signed := true }
def scaleTwo : NumField := { scale := 2, signed := false }

def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

def dateTimeComponents : TemporalComponents :=
  { TemporalComponents.fullDate with
    hour := true, minute := true, second := true }

def monthDayComponents : TemporalComponents :=
  { year := false, month := true, day := true,
    hour := false, minute := false, second := false }

def model : FlatModel :=
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
        enumeration := some { storedTokens := ["1234567890123456"] } },
      { id := 17, groupPath := ["Order"], name := "NumericCode",
        policy := { kind := .string },
        stringPatternSource := some "[0-9]+",
        stringPolicy := { maxLength := some 15 } },
      { id := 18, groupPath := ["Order"], name := "WrongPatternCode",
        policy := { kind := .string },
        stringPatternSource := some "[0-9]*",
        stringPolicy := { maxLength := some 15 } },
      { id := 19, groupPath := ["Order"], name := "UnboundedCode",
        policy := { kind := .string },
        stringPatternSource := some "[0-9]+" },
      { id := 20, groupPath := ["Order"], name := "WideCode",
        policy := { kind := .string },
        stringPatternSource := some "[0-9]+",
        stringPolicy := { maxLength := some 16 } },
      { id := 21, groupPath := ["Order"], name := "HostDigitChoice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["١٢.٥", "-３"] } },
      { id := 22, groupPath := ["Order"], name := "SupplementaryDigitChoice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["𐒠"] } },
      { id := 23, groupPath := ["Order"], name := "LaterDateTime",
        policy := { kind := .temporal .dateTime dateTimeComponents } }],
    repeatableGroups := [{ level := 10, path := ["Order", "Items"] }] }

def baseYearModel : FlatModel := { model with baseYear := some 2020 }
def berlinModel : FlatModel := { model with timeZoneId := "Europe/Berlin" }
def unsupportedZoneModel : FlatModel :=
  { model with timeZoneId := "Pacific/Apia" }

def path (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

def atom (name : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (path ["Order"] name))

def baseYear : AuthoredNumericExpr SurfaceNumericAtom := .atom .baseYear

def baseYearDatePart (source : BaseYearDateSource)
    (part : DateNumericPart) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.baseYearDatePart source part)

def dateFieldPart (name : String) (part : DateNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (path ["Order"] name) (.date part))

def timeFieldPart (name : String) (part : TimeNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (path ["Order"] name) (.time part))

def dateDifference (unit : DateDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateDifference unit left right)

def dateTimeDifference (unit : DateTimeDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateTimeDifference unit left right)

def dayDifference
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dayDifference left right)

def stringRange (start finish : Nat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.stringRange (path ["Order"] "Code") start finish)

def fieldValueAsNumber
    (source : SurfaceTextFieldOperand := .direct (path ["Order"] "NumericChoice")) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber source)

def dateOperand (name : String) : SurfaceDateDifferenceOperand :=
  .field (path ["Order"] name)

def literal (value : Rat) (authoredScale : Int) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale }

def aggregate (op : NumericAggregateOp) (first : String)
    (rest : List String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.aggregate op {
    first := path ["Order"] first
    rest := rest.map (path ["Order"]) })

def comparison (op : NumericComparisonOp)
    (left : AuthoredNumericExpr SurfaceNumericAtom)
    (rightValue : Rat) (rightScale : Int := 0) :
    SurfaceNumericComparison :=
  { op := .ordinary op, left, right := literal rightValue rightScale }

def twoSided (op : NumericComparisonOp)
    (left right : AuthoredNumericExpr SurfaceNumericAtom) :
    SurfaceNumericComparison :=
  { op := .ordinary op, left, right }

def raw (u v s scale2Value : RawCell := .empty) : RawFlatContext where
  read id :=
    if id == 0 then u else if id == 1 then v else if id == 2 then scale2Value
      else if id == 6 then s else .empty

def temporalRaw (id : FieldId) (cell : RawCell) : RawFlatContext where
  read actual := if actual == id then cell else .empty

def stringRaw (cell : RawCell) : RawFlatContext where
  read actual := if actual == 12 then cell else .empty

def enumerationRaw (cell : RawCell) : RawFlatContext where
  read actual := if actual == 13 then cell else .empty

def fieldRaw (id : FieldId) (cell : RawCell) : RawFlatContext where
  read actual := if actual == id then cell else .empty

def instant : Instant := { epochMillis := 1719292867000 }

def dateParts : DateParts := { year := 2024, month := 6, day := 25 }

def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

def dateTimeValue : Value :=
  .temporal (.dateTime instant dateParts clock .storedGregorian)

def dateTimeValueAt (epochMillis : Int) : Value :=
  .temporal (.dateTime { epochMillis } dateParts clock .storedGregorian)

def localDateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

def berlinDateTimeValue
    (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome)
    (resolved :
      (EuropeBerlinLegacyProfile.resolveLocal?
        (localDateTime year month day hour minute second admissible)).isSome) :
    Value :=
  let point := localDateTime year month day hour minute second admissible
  .temporal (.dateTime
    ((EuropeBerlinLegacyProfile.resolveLocal?
      (localDateTime year month day hour minute second admissible)).get resolved)
    point.date.civil.parts point.time .storedGregorian)

def berlinDaylightFoldValue : Value :=
  let point := localDateTime 2024 10 27 2 15 0 (by native_decide)
  let beforeFold := localDateTime 2024 10 27 1 15 0 (by native_decide)
  let daylightInstant :=
    (EuropeBerlinLegacyProfile.resolveLocal? beforeFold).get
      (by native_decide) |>.shiftHours 1
  .temporal (.dateTime daylightInstant point.date.civil.parts point.time
    .storedGregorian)

def dateValue (year : Int) (month day : Nat)
    (basis : DateCalendarBasis := .storedGregorian) : Value :=
  .temporal (.date instant { year, month, day } basis)

def temporalPairRaw (first second : RawCell) : RawFlatContext where
  read id :=
    if id == 9 then first
    else if id == 23 then second
    else .empty

def compileValidationPattern : StringPatternCompiler := fun source =>
  if source == asciiDigitsPatternSource then
    locallyExecutableStringPatternMatcher? source
  else if source == "[0-9]*" then
    some fun value =>
      value.toList.all fun character => '0' ≤ character && character ≤ '9'
  else
    none

def verdictOf (surface : SurfaceNumericComparison)
    (context : RawFlatContext := raw) (hasContent : Bool := true)
    (sourceModel : FlatModel := model) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      compileValidationPattern sourceModel).toOption
  (elaborateAndEvalNumericComparison prepared "en_US" ["Order"]
    context hasContent surface).toOption

def errorOf (surface : SurfaceNumericComparison)
    (sourceModel : FlatModel := model) :
    Option NumericValidationElabError :=
  match elaborateNumericComparison sourceModel ["Order"] surface with
  | .ok _ => none
  | .error error => some error

def suppressScaleWarning
    (surface : SurfaceNumericComparison) : SurfaceNumericComparison :=
  { surface with suppressExactScaleWarning := true }

def tolerance (range : NumericToleranceRange)
    (left right : AuthoredNumericExpr SurfaceNumericAtom) :
    SurfaceNumericComparison :=
  { op := .tolerance range, left, right }

def dividedThird : AuthoredNumericExpr SurfaceNumericAtom :=
  .group (.binary .divide (literal 3 0) (literal 3 0))

end A12Kernel.Conformance.NumericValidation.Support
