import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.ModelZone

/-! # Checked flat-elaboration conformance locks -/

namespace A12Kernel.Conformance.Elaboration

open A12Kernel

private def numberInfo : NumField := { scale := 2, signed := false }

private def quantityDecl : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Quantity",
    policy := { kind := .number numberInfo } }

private def expressDecl : FlatFieldDecl :=
  { id := 1, groupPath := ["Order"], name := "ExpressShipping",
    policy := { kind := .boolean } }

private def confirmDecl : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "TermsConfirmed",
    policy := { kind := .confirm } }

private def ancestorLimitDecl : FlatFieldDecl :=
  { id := 3, groupPath := ["Order"], name := "Limit",
    policy := { kind := .number { scale := 0, signed := true } } }

private def localLimitDecl : FlatFieldDecl :=
  { id := 4, groupPath := ["Order", "Details"], name := "Limit",
    policy := { kind := .number { scale := 1, signed := false } } }

private def externalCodeDecl : FlatFieldDecl :=
  { id := 5, groupPath := ["Reference"], name := "ExternalCode",
    policy := { kind := .boolean } }

private def repeatableCountDecl : FlatFieldDecl :=
  { id := 6, groupPath := ["Order", "Items"], name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

private def noteDecl : FlatFieldDecl :=
  { id := 7, groupPath := ["Order"], name := "Note",
    policy := { kind := .string } }

private def dispatchDateComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := false, minute := false, second := false }

private def dispatchDateDecl : FlatFieldDecl :=
  { id := 8, groupPath := ["Order"], name := "DispatchDate",
    policy := { kind := .temporal .date dispatchDateComponents } }

private def arrivalDateDecl : FlatFieldDecl :=
  { id := 9, groupPath := ["Order"], name := "ArrivalDate",
    policy := { kind := .temporal .date dispatchDateComponents } }

private def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

private def eventTimeDecl : FlatFieldDecl :=
  { id := 10, groupPath := ["Order"], name := "EventTime",
    policy := { kind := .temporal .time timeComponents } }

private def dateTimeComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := true, minute := true, second := true }

private def eventDateTimeDecl : FlatFieldDecl :=
  { id := 11, groupPath := ["Order"], name := "EventDateTime",
    policy := { kind := .temporal .dateTime dateTimeComponents } }

private def monthDayComponents : TemporalComponents :=
  { year := false, month := true, day := true,
    hour := false, minute := false, second := false }

private def recurringDateDecl : FlatFieldDecl :=
  { id := 12, groupPath := ["Order"], name := "RecurringDate",
    policy := { kind := .temporal .date monthDayComponents } }

private def repeatableItems : RepeatableGroupDecl :=
  { level := 10, path := ["Order", "Items"] }

private def model : FlatModel :=
  { fields := [quantityDecl, expressDecl, confirmDecl, ancestorLimitDecl,
      localLimitDecl, externalCodeDecl, repeatableCountDecl, noteDecl,
      dispatchDateDecl, arrivalDateDecl, eventTimeDecl, eventDateTimeDecl,
      recurringDateDecl],
    repeatableGroups := [repeatableItems],
    fieldRefByShortNameAllowed := true }

private def baseYearModel : FlatModel := { model with baseYear := some 2020 }

private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def relative (parents : Nat) (groups : List String)
    (field : String) : SurfaceFieldPath :=
  { base := .relative parents, groups, field }

private def bare (field : String) : SurfaceFieldPath := relative 0 [] field

private def compare (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
    (literal : SurfaceLiteral) : SurfaceCondition :=
  .compare op field literal

private def compareFields (op : SurfaceComparisonOp) (left right : String) :
    SurfaceCondition :=
  .compareFields op (absolute ["Order"] left) (absolute ["Order"] right)

private def compareNow (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
    (field : String) : SurfaceCondition :=
  .compareNow op position (absolute ["Order"] field)

private def compareToday (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
    (field : String) : SurfaceCondition :=
  .compareToday op position (absolute ["Order"] field)

private def compareBaseYear (op : SurfaceComparisonOp)
    (position : SurfacePointInTimePosition) (field : String) : SurfaceCondition :=
  .compareBaseYear op position (absolute ["Order"] field)

private def compareBaseYearRange (op : SurfaceComparisonOp)
    (position : SurfacePointInTimePosition) (endpoint : BaseYearRangeEndpoint)
    (field : String) : SurfaceCondition :=
  .compareBaseYearRange op position endpoint (absolute ["Order"] field)

private def dateLiteral (components : TemporalComponents) (millis : Int) :
    SurfaceLiteral :=
  .date components { epochMillis := millis }

private def coreOf {checkedModel : FlatModel}
    (result : Except ElabError (CheckedFlatCondition checkedModel)) :
    Option FlatCondition :=
  match result with
  | .ok checked => some checked.core
  | .error _ => none

private def valueOf : Except ε α → Option α
  | .ok value => some value
  | .error _ => none

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def resolvedIdOf (result : Except ResolveError FlatFieldDecl) : Option FieldId :=
  (valueOf result).map (·.id)

example : coreOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))) =
    some (.compare (.number (.ordinary .equal)
      { id := 0, info := numberInfo } 0)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.compare (.boolean .equal { id := 1 } false)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .notEqual (absolute ["Order"] "TermsConfirmed") (.boolean true))) =
    some (.compare (.confirm .notEqual { id := 2 })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.fieldNotFilled (absolute ["Order"] "Quantity"))) =
    some (.fieldNotFilled (.number { id := 0, info := numberInfo })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order"] "Note"))) =
    some (.fieldFilled (.string { id := 7 })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order"] "DispatchDate"))) =
    some (.fieldFilled (.temporal
      { id := 8, kind := .date, components := dispatchDateComponents })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compareFields .less "DispatchDate" "ArrivalDate")) =
    some (.compare (.temporal .before
      (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
      (.fieldValue { id := 9, kind := .date, components := dispatchDateComponents }))) := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compareFields .less "DispatchDate" "EventDateTime")) =
        some (.compare (.temporal .before
          (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
          (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) ∧
      errorOf (elaborate model ["Order"]
        (compareFields .equal "DispatchDate" "EventDateTime")) =
          some (.temporalFormatsIncompatible
            ["Order", "DispatchDate"] ["Order", "EventDateTime"]) := by
  native_decide

/-! The core admits field/literal in either operand position for later expression lowering, but never the kernel-forbidden constant/constant comparison. -/
example : model.admitsComparison
    (.temporal .equal
      (.literalValue { epochMillis := 100000 })
      (.literalValue { epochMillis := 100000 })) = false := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compare .less (absolute ["Order"] "DispatchDate")
        (dateLiteral dispatchDateComponents 101000))) =
      some (.compare (.temporal .before
        (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
        (.literalValue { epochMillis := 101000 }))) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compare .equal (absolute ["Order"] "EventDateTime")
        (dateLiteral dispatchDateComponents 101000))) =
        some (.temporalFormatsIncompatible
          ["Order", "EventDateTime"] ["<date-literal>"]) ∧
      (elaborate model ["Order"]
        (compare .less (absolute ["Order"] "EventDateTime")
          (dateLiteral dispatchDateComponents 101000))).isOk = true := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compare .less (absolute ["Order"] "RecurringDate")
        (dateLiteral monthDayComponents 101000))) =
        some (.temporalLiteralNeedsBaseYear ["<date-literal>"]) ∧
      (elaborate baseYearModel ["Order"]
        (compare .less (absolute ["Order"] "RecurringDate")
          (dateLiteral monthDayComponents 101000))).isOk = true := by
  native_decide

private def invalidDateLiteralComponents : TemporalComponents :=
  { year := true, month := false, day := true,
    hour := false, minute := false, second := false }

example :
    errorOf (elaborate model ["Order"]
      (compare .equal (absolute ["Order"] "DispatchDate")
        (dateLiteral invalidDateLiteralComponents 101000))) =
      some (.invalidTemporalLiteralComponents ["<date-literal>"]) := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compareNow .less .right "EventDateTime")) =
        some (.compare (.temporal .before
          (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents })
          .nowValue)) ∧
      coreOf (elaborate model ["Order"]
        (compareNow .greater .left "EventDateTime")) =
          some (.compare (.temporal .after .nowValue
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareNow .less .right "DispatchDate")) =
        some (.temporalNowRequiresTime ["Order", "DispatchDate"]) := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compareToday .equal .right "DispatchDate")) =
        some (.compare (.temporal .equal
          (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
          (.todayValue "UTC"))) ∧
      coreOf (elaborate model ["Order"]
        (compareToday .less .left "EventDateTime")) =
          some (.compare (.temporal .before (.todayValue "UTC")
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareToday .equal .right "EventDateTime")) =
        some (.temporalFormatsIncompatible ["Order", "EventDateTime"] ["<Today>"]) ∧
      errorOf (elaborate model ["Order"]
        (compareToday .less .right "EventTime")) =
          some (.temporalFormatsIncompatible ["Order", "EventTime"] ["<Today>"]) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareBaseYear .equal .right "DispatchDate")) =
        some .baseYearNotDeclared ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .equal .right "Limit")) =
          some (.compare (.number (.ordinary .equal)
            { id := 3, info := { scale := 0, signed := true } } 2020)) ∧
      errorOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .equal .right "Quantity")) =
          some (.baseYearScaleMismatch ["Order", "Quantity"] 2) := by
  native_decide

example :
    coreOf (elaborate baseYearModel ["Order"]
      (compareBaseYear .equal .right "DispatchDate")) =
        some (.compare (.temporal .equal
          (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
          (.baseYearValue "UTC" 2020))) ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .less .left "EventDateTime")) =
          some (.compare (.temporal .before (.baseYearValue "UTC" 2020)
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) ∧
      errorOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .equal .right "EventDateTime")) =
          some (.temporalFormatsIncompatible ["Order", "EventDateTime"] ["<BaseYear>"]) ∧
      errorOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .less .right "EventTime")) =
          some (.temporalFormatsIncompatible ["Order", "EventTime"] ["<BaseYear>"]) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareBaseYearRange .equal .right .start "DispatchDate")) =
        some .baseYearNotDeclared ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYearRange .equal .right .start "DispatchDate")) =
          some (.compare (.temporal .equal
            (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
            (.baseYearRangeValue "UTC" 2020 .start))) ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYearRange .less .left .finish "EventDateTime")) =
          some (.compare (.temporal .before
            (.baseYearRangeValue "UTC" 2020 .finish)
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) := by
  native_decide

example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareBaseYearRange .equal .right .finish "EventDateTime")) =
      some (.temporalFormatsIncompatible
        ["Order", "EventDateTime"] ["<EndOfDateRange(BaseYear)>"]) := by
  native_decide

example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareBaseYearRange .less .right .start "EventTime")) =
      some (.temporalFormatsIncompatible
        ["Order", "EventTime"] ["<StartOfDateRange(BaseYear)>"]) := by
  native_decide

/- Base Year can supply a missing year to a date fragment, but cannot turn a Time field into a date-bearing operand. -/
example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareFields .less "DispatchDate" "EventTime")) =
      some (.temporalFormatsIncompatible
        ["Order", "DispatchDate"] ["Order", "EventTime"]) := by
  native_decide

example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareBaseYearRange .equal .right .start "Limit")) =
      some (.temporalOperandKindMismatch
        ["Order", "Limit"] ["<StartOfDateRange(BaseYear)>"]
        .number (.temporal .date)) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareFields .less "DispatchDate" "EventTime")) =
        some (.temporalFormatsIncompatible
          ["Order", "DispatchDate"] ["Order", "EventTime"]) ∧
      errorOf (elaborate model ["Order"]
        (compareFields .equal "DispatchDate" "ExpressShipping")) =
          some (.temporalOperandKindMismatch
            ["Order", "DispatchDate"] ["Order", "ExpressShipping"]
            (.temporal .date) .boolean) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareFields .less "RecurringDate" "DispatchDate")) =
        some (.temporalFormatsIncompatible
          ["Order", "RecurringDate"] ["Order", "DispatchDate"]) ∧
      (elaborate baseYearModel ["Order"]
        (compareFields .less "RecurringDate" "DispatchDate")).isOk = true := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.and (.fieldFilled (absolute ["Order"] "ExpressShipping"))
      (compare .equal (absolute ["Order"] "Quantity") (.number 0)))) =
    some (.and (FlatCondition.fieldFilled (.boolean { id := 1 }))
      (FlatCondition.compare (.number (.ordinary .equal)
        { id := 0, info := numberInfo } 0))) := by
  native_decide

-- Bare resolution is declaring-group-first, then flag-gated unique model-wide.
example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "Limit")) = some 4 := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "Quantity")) = some 0 := by
  native_decide

-- Ancestors have no special tier: after a local miss, duplicate names are model-wide ambiguous.
example : errorOf (model.resolveField ["Order", "Details", "Deep"] (bare "Limit")) =
    some (.shortNameNotUnique "Limit") := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "ExternalCode")) = some 5 := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"]
    (relative 1 [] "Quantity")) = some 0 := by
  native_decide

example : errorOf (model.resolveField ["Order", "Details"]
    (relative 2 [] "Quantity")) = some (.aboveRoot 2) := by
  native_decide

private def ambiguousModel : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["One"], name := "Code", policy := { kind := .boolean } },
      { id := 1, groupPath := ["Two"], name := "Code", policy := { kind := .boolean } }],
    fieldRefByShortNameAllowed := true }

example : errorOf (ambiguousModel.resolveField ["Rule"] (bare "Code")) =
    some (.shortNameNotUnique "Code") := by
  native_decide

private def shortNamesDisabled : FlatModel :=
  { model with fieldRefByShortNameAllowed := false }

-- The declaring-group tier does not depend on the model-wide short-name flag.
example : resolvedIdOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "Limit")) = some 4 := by
  native_decide

-- There is no implicit ancestor walk when short-name fallback is disabled.
example : errorOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "Quantity")) = some (.invalidEntity (bare "Quantity")) := by
  native_decide

example : errorOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "ExternalCode")) = some (.invalidEntity (bare "ExternalCode")) := by
  native_decide

example : errorOf (model.resolveField ["Order"]
    (absolute ["Order"] "Missing")) =
    some (.invalidEntity (absolute ["Order"] "Missing")) := by
  native_decide

private def duplicateIdModel : FlatModel :=
  { fields := [quantityDecl, { expressDecl with id := 0 }] }

example : errorOf (elaborate duplicateIdModel ["Order"]
    (.fieldFilled (absolute ["Order"] "Quantity"))) =
    some (.resolve (.duplicateFieldId 0)) := by
  native_decide

private def duplicatePathModel : FlatModel :=
  { fields := [quantityDecl, { quantityDecl with id := 9 }] }

example : errorOf (elaborate duplicatePathModel ["Order"]
    (.fieldFilled (absolute ["Order"] "Quantity"))) =
    some (.resolve (.duplicateEntityPath ["Order", "Quantity"])) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order", "Items"] "Count"))) =
    some (.resolve (.repeatableReference ["Order", "Items", "Count"])) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.boolean true))) =
    some (.literalKindMismatch ["Order", "Quantity"] .number .boolean) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "TermsConfirmed") (.boolean false))) =
    some (.illegalConfirmLiteral ["Order", "TermsConfirmed"]) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .less (absolute ["Order"] "Quantity") (.number 10))) =
    some (.compare (.number (.ordinary .less)
      { id := 0, info := numberInfo } 10)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .greaterEqual (absolute ["Order"] "Quantity") (.number 0))) =
    some (.compare (.number (.ordinary .greaterEqual)
      { id := 0, info := numberInfo } 0)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .lessEqual (absolute ["Order"] "Quantity") (.number 10))) =
    some (.compare (.number (.ordinary .lessEqual)
      { id := 0, info := numberInfo } 10)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .greater (absolute ["Order"] "Quantity") (.number 10))) =
    some (.compare (.number (.ordinary .greater)
      { id := 0, info := numberInfo } 10)) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .lessEqual (absolute ["Order"] "Missing") (.number 10))) =
    some (.resolve (.invalidEntity (absolute ["Order"] "Missing"))) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .less (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.unsupportedOperator .less) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .less (absolute ["Order"] "ExpressShipping") (.number 10))) =
    some (.unsupportedOperator .less) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .greaterEqual (absolute ["Order"] "TermsConfirmed") (.boolean false))) =
    some (.unsupportedOperator .greaterEqual) := by
  native_decide

private def wrongKindRaw : RawFlatContext where
  read id := if id = 0 then .parsed (.bool true) else .empty

private def ordinaryRaw : RawFlatContext where
  read id :=
    if id = 0 then .parsed (.num 5)
    else if id = 1 then .parsed (.bool false)
    else if id = 2 then .parsed (.conf true)
    else .empty

private def temporalDateParts : DateParts :=
  { year := 2024, month := 6, day := 25 }

private def temporalClock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def temporalValue (kind : TemporalKind) (millis : Int) : Value :=
  let instant : Instant := { epochMillis := millis }
  match kind with
  | .date => .temporal (.date instant temporalDateParts .storedGregorian)
  | .time => .temporal (.time instant temporalClock)
  | .dateTime =>
      .temporal (.dateTime instant temporalDateParts temporalClock
        .storedGregorian)

private def temporalRaw (kind : TemporalKind) : RawFlatContext where
  read id :=
    if id = 8 then .parsed (temporalValue kind 100999)
    else .empty

private def temporalComparisonRaw (leftKind : TemporalKind) (left : Int)
    (rightKind : TemporalKind) (right : Option Int) : RawFlatContext where
  read id :=
    if id = 8 then .parsed (temporalValue leftKind left)
    else if id = 9 then
      match right with
      | some millis => .parsed (temporalValue rightKind millis)
      | none => .empty
    else .empty

private def eventDateTimeRaw (millis : Int) : RawFlatContext where
  read id :=
    if id = 11 then .parsed (temporalValue .dateTime millis)
    else .empty

private def worldAt (millis : Int) : World :=
  { now := { epochMillis := millis } }

private def dispatchDateRaw (millis : Int) : RawFlatContext where
  read id :=
    if id = 8 then .parsed (temporalValue .date millis)
    else .empty

private def baseYearRaw (limit : Rat) (dispatchMillis : Int) : RawFlatContext where
  read id :=
    if id == 0 || id == 3 then .parsed (.num limit)
    else if id = 8 then .parsed (temporalValue .date dispatchMillis)
    else .empty

private def utcInstant? (year : Int) (month day hour minute second : Nat) : Option Instant :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).map
    LocalDateTime.resolveUtc

example : valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] ordinaryRaw true
    (compare .equal (absolute ["Order"] "Quantity") (.number 5))) =
    some (.fired .value) := by
  native_decide

example : valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] ordinaryRaw true
    (compare .equal (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.fired .value) := by
  native_decide

example : valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] ordinaryRaw true
    (compare .notEqual (absolute ["Order"] "TermsConfirmed") (.boolean true))) =
    some .notFired := by
  native_decide

example : valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] { read := fun _ => .empty } false
    (.fieldNotFilled (absolute ["Order"] "Quantity"))) =
    some (.fired .omission) := by
  native_decide

example :
    valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] (temporalRaw .date) true
      (.fieldFilled (absolute ["Order"] "DispatchDate"))) =
        some (.fired .value) ∧
      valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] (temporalRaw .dateTime) true
        (.fieldFilled (absolute ["Order"] "DispatchDate"))) =
          some .unknown := by
  native_decide

example :
    valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"]
      (temporalComparisonRaw .date 100000 .date (some 101000)) true
      (compareFields .less "DispatchDate" "ArrivalDate")) =
        some (.fired .value) ∧
      valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"]
        (temporalComparisonRaw .date 100000 .date none) true
        (compareFields .less "DispatchDate" "ArrivalDate")) =
          some .notFired ∧
      valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"]
        (temporalComparisonRaw .date 100000 .dateTime (some 101000)) true
        (compareFields .less "DispatchDate" "ArrivalDate")) =
          some .unknown := by
  native_decide

example :
    valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"]
      (temporalComparisonRaw .date 100000 .date none) true
      (compare .less (absolute ["Order"] "DispatchDate")
        (dateLiteral dispatchDateComponents 101000))) =
        some (.fired .value) ∧
      valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"]
        (temporalComparisonRaw .date 100000 .date none) true
        (compare .greater (absolute ["Order"] "DispatchDate")
          (dateLiteral dispatchDateComponents 101000))) =
          some .notFired := by
  native_decide

example :
    valueOf (elaborateAndEvalFull model (worldAt 100999) ["Order"]
      (eventDateTimeRaw 100000) true
      (compareNow .equal .right "EventDateTime")) =
        some .notFired ∧
      valueOf (elaborateAndEvalFull model (worldAt 100999) ["Order"]
        (eventDateTimeRaw 100000) true
        (compareNow .less .right "EventDateTime")) =
          some (.fired .value) ∧
      valueOf (elaborateAndEvalFull model (worldAt 100999) ["Order"]
        (eventDateTimeRaw 100000) true
        (compareNow .greater .left "EventDateTime")) =
          some (.fired .value) := by
  native_decide

example : (do
    let now ← utcInstant? 2024 3 31 12 0 0
    let midnight ← utcInstant? 2024 3 31 0 0 0
    let world : World :=
      { now, modelZoneRules := ModelZone.concreteRules }
    pure (valueOf (elaborateAndEvalFull model world ["Order"]
      (dispatchDateRaw midnight.epochMillis) true
      (compareToday .equal .right "DispatchDate")) = some (.fired .value))) = some true := by
  native_decide

example : (do
    let start ← utcInstant? 2020 1 1 0 0 0
    let world : World :=
      { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
    pure (
      valueOf (elaborateAndEvalFull baseYearModel world ["Order"]
        (baseYearRaw 2020 start.epochMillis) true
        (compareBaseYear .equal .right "Limit")) = some (.fired .value) ∧
      valueOf (elaborateAndEvalFull baseYearModel world ["Order"]
        (baseYearRaw 2021 start.epochMillis) true
        (compareBaseYear .less .left "Quantity")) = some (.fired .value) ∧
      valueOf (elaborateAndEvalFull baseYearModel world ["Order"]
        (baseYearRaw 2020 start.epochMillis) true
        (compareBaseYear .equal .right "DispatchDate")) = some (.fired .value))) = some true := by
  native_decide

example : (do
    let start ← utcInstant? 2020 1 1 0 0 0
    let finish ← utcInstant? 2020 12 31 0 0 0
    let world : World :=
      { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
    pure (
      valueOf (elaborateAndEvalFull baseYearModel world ["Order"]
        (dispatchDateRaw start.epochMillis) true
        (compareBaseYearRange .equal .right .start "DispatchDate")) =
          some (.fired .value) ∧
      valueOf (elaborateAndEvalFull baseYearModel world ["Order"]
        (dispatchDateRaw finish.epochMillis) true
        (compareBaseYearRange .equal .right .finish "DispatchDate")) =
          some (.fired .value) ∧
      valueOf (elaborateAndEvalFull baseYearModel world ["Order"]
        (dispatchDateRaw start.epochMillis) true
        (compareBaseYearRange .equal .right .finish "DispatchDate")) =
          some .notFired)) = some true := by
  native_decide

example : (do
    let now ← utcInstant? 2024 3 31 12 0 0
    let midnight ← utcInstant? 2024 3 31 0 0 0
    let apiaModel : FlatModel := { model with timeZoneId := "Pacific/Apia" }
    let narrowWorld : World :=
      { now, modelZoneRules := ModelZone.concreteRules }
    let suppliedWorld : World :=
      { now,
        modelZoneRules :=
          { ModelZoneRules.unavailable with
            today? := fun zoneId _ =>
              if zoneId == "Pacific/Apia" then some midnight else none } }
    pure (
      valueOf (elaborateAndEvalFull apiaModel narrowWorld ["Order"]
        (dispatchDateRaw midnight.epochMillis) true
        (compareToday .equal .right "DispatchDate")) = some .unknown ∧
      valueOf (elaborateAndEvalFull apiaModel suppliedWorld ["Order"]
        (dispatchDateRaw midnight.epochMillis) true
        (compareToday .equal .right "DispatchDate")) = some (.fired .value))) = some true := by
  native_decide

-- Model-derived formal checking prevents an inconsistent runtime kind from entering eval.
example : valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] wrongKindRaw true
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))) = some .unknown := by
  native_decide

-- Static success does not imply a definite runtime verdict: malformed data remains unknown.
example : (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))).isOk = true ∧
    valueOf (elaborateAndEvalFull model (worldAt 0) ["Order"] wrongKindRaw true
      (compare .equal (absolute ["Order"] "Quantity") (.number 0))) = some .unknown := by
  native_decide

end A12Kernel.Conformance.Elaboration
