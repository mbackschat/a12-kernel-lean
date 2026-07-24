import A12Kernel.Conformance.Elaboration.Support

/-! # Checked flat-context and runtime evaluation locks -/

namespace A12Kernel.Conformance.Elaboration.Runtime

open A12Kernel
open A12Kernel.Conformance.Elaboration.Support

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

example : valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] ordinaryRaw true
    (compare .equal (absolute ["Order"] "Quantity") (.number 5))) =
    some (.fired .value) := by
  native_decide

example : valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] ordinaryRaw true
    (compare .equal (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.fired .value) := by
  native_decide

example : valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] ordinaryRaw true
    (compare .notEqual (absolute ["Order"] "TermsConfirmed") (.boolean true))) =
    some .notFired := by
  native_decide

example : valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] { read := fun _ => .empty } false
    (.fieldNotFilled (absolute ["Order"] "Quantity"))) =
    some (.fired .omission) := by
  native_decide

example :
    valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] (temporalRaw .date) true
      (.fieldFilled (absolute ["Order"] "DispatchDate"))) =
        some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] (temporalRaw .dateTime) true
        (.fieldFilled (absolute ["Order"] "DispatchDate"))) =
          some .unknown := by
  native_decide

example :
    valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"]
      (temporalComparisonRaw .date 100000 .date (some 101000)) true
      (compareFields .less "DispatchDate" "ArrivalDate")) =
        some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"]
        (temporalComparisonRaw .date 100000 .date none) true
        (compareFields .less "DispatchDate" "ArrivalDate")) =
          some .notFired ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"]
        (temporalComparisonRaw .date 100000 .dateTime (some 101000)) true
        (compareFields .less "DispatchDate" "ArrivalDate")) =
          some .unknown := by
  native_decide

example :
    valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"]
      (temporalComparisonRaw .date 100000 .date none) true
      (compare .less (absolute ["Order"] "DispatchDate")
        (dateLiteral dispatchDateComponents 101000))) =
        some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"]
        (temporalComparisonRaw .date 100000 .date none) true
        (compare .greater (absolute ["Order"] "DispatchDate")
          (dateLiteral dispatchDateComponents 101000))) =
          some .notFired := by
  native_decide

example :
    valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 100999) ["Order"]
      (eventDateTimeRaw 100000) true
      (compareNow .equal .right "EventDateTime")) =
        some .notFired ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 100999) ["Order"]
        (eventDateTimeRaw 100000) true
        (compareNow .less .right "EventDateTime")) =
          some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 100999) ["Order"]
        (eventDateTimeRaw 100000) true
        (compareNow .greater .left "EventDateTime")) =
          some (.fired .value) := by
  native_decide

example : (do
    let now ← utcInstant? 2024 3 31 12 0 0
    let midnight ← utcInstant? 2024 3 31 0 0 0
    let world : World :=
      { now, modelZoneRules := ModelZone.concreteRules }
    pure (valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model world ["Order"]
      (dispatchDateRaw midnight.epochMillis) true
      (compareToday .equal .right "DispatchDate")) = some (.fired .value))) = some true := by
  native_decide

example : (do
    let start ← utcInstant? 2020 1 1 0 0 0
    let world : World :=
      { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
    pure (
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" baseYearModel world ["Order"]
        (baseYearRaw 2020 start.epochMillis) true
        (compareBaseYear .equal .right "Limit")) = some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" baseYearModel world ["Order"]
        (baseYearRaw 2021 start.epochMillis) true
        (compareBaseYear .less .left "Quantity")) = some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" baseYearModel world ["Order"]
        (baseYearRaw 2020 start.epochMillis) true
        (compareBaseYear .equal .right "DispatchDate")) = some (.fired .value))) = some true := by
  native_decide

example : (do
    let start ← utcInstant? 2020 1 1 0 0 0
    let finish ← utcInstant? 2020 12 31 0 0 0
    let world : World :=
      { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
    pure (
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" baseYearModel world ["Order"]
        (dispatchDateRaw start.epochMillis) true
        (compareBaseYearRange .equal .right .start "DispatchDate")) =
          some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" baseYearModel world ["Order"]
        (dispatchDateRaw finish.epochMillis) true
        (compareBaseYearRange .equal .right .finish "DispatchDate")) =
          some (.fired .value) ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" baseYearModel world ["Order"]
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
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" apiaModel narrowWorld ["Order"]
        (dispatchDateRaw midnight.epochMillis) true
        (compareToday .equal .right "DispatchDate")) = some .unknown ∧
      valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" apiaModel suppliedWorld ["Order"]
        (dispatchDateRaw midnight.epochMillis) true
        (compareToday .equal .right "DispatchDate")) = some (.fired .value))) = some true := by
  native_decide

-- Model-derived formal checking prevents an inconsistent runtime kind from entering eval.
example : valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] wrongKindRaw true
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))) = some .unknown := by
  native_decide

-- Static success does not imply a definite runtime verdict: malformed data remains unknown.
example : (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))).isOk = true ∧
    valueOf (elaborateAndEvalFull builtinStringPatternCompiler "en_US" model (worldAt 0) ["Order"] wrongKindRaw true
      (compare .equal (absolute ["Order"] "Quantity") (.number 0))) = some .unknown := by
  native_decide


end A12Kernel.Conformance.Elaboration.Runtime
