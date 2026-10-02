import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Authored scalar plan locks: extractors, mixed shifts and list readers at a join

A day shift `MA = AddDays(M1, [P1])` feeds `TimeFromDateTime(MA)`, `DateFromDateTime(MA)` and both mixed
shifts, `AddHours(AddDays(MA, [PC]), [P1])` and `AddDays(AddHours(MA, [P1]), [PC])`, whose day amount
`PC = [P2] + 1` is computed too. A String, a Number and a Boolean `FirstFilledValue` over a direct list
feed a second `FirstFilledValue` or a `NumberOfValueInFields`, and every target is read by a
`FieldFilled` and a `FieldNotFilled` guard, every reader authored ahead of what it reads. The fixture is
the model of the [extractor join checkpoint](../../docs/sources/computation-scheduling-probes.md#src-extractor-join),
and every document row is the Kernel's, measured on both codegen strategies.

Computed targets are seeded with values no row computes, except the Boolean `BA`, left unseeded so a
computed value differs from its seed. A row projects every target to its value, or `-` where the Kernel
clears or writes nothing.

The rows separate a fresh read of `MA` from its seed (`r1`), a cleared upstream read as empty from one
read as poison (`r2`, `r3`), a poisoned computed amount that reaches only the mixed shifts from one that
reaches the extractors too (`r4`), and an exhausted Number `FirstFilledValue`, whose computed `0` is a
filled value its readers count, from an exhausted String one, which clears (`r2`, `r5`).
-/

namespace A12Kernel.Conformance.ScalarComputationPlanExtractor

open A12Kernel

private def names : List String :=
  ["M1", "MA", "MX", "MY", "P1", "P2", "PC", "TT", "DD", "S1", "S2", "S3", "SA", "SF",
    "Q1", "Q2", "Q3", "QA", "QF", "B1", "B2", "B3", "BA", "VN", "VS", "VB"] ++
  (["TT", "DD", "MX", "MY", "SF", "QF"].flatMap fun target => ["K" ++ target, "KN" ++ target])

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let base : FlatFieldDecl :=
    { id := idOf name, groupPath := ["Xj"], name, policy := { kind := .number { scale := 0, signed := true } } }
  if ["M1", "MA", "MX", "MY"].contains name then
    { base with
      policy := { kind := .temporal .dateTime TemporalComponents.now }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss", partialMode := .full } }
  else if name == "TT" then
    { base with
      policy := { kind := .temporal .time TemporalComponents.time }
      temporalTargetPolicy := some { format := "HH:mm:ss" } }
  else if name == "DD" then
    { base with
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full } }
  else if name.startsWith "S" then
    { base with policy := { kind := .string }, stringPolicy := { maxLength := some 3 } }
  else if name.startsWith "B" then
    { base with policy := { kind := .boolean } }
  else base

private def model : FlatModel :=
  { fields := names.map declaration, timeZoneId := "Europe/Berlin" }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def entities (first second : String) : SurfaceFieldEntitySource :=
  { first := .field (bare first), rest := [.field (bare second)] }

private def one : DecodedNumericLiteral := { value := 1, authoredScale := 0 }

private def numberStep? (target : String) (guard : Option ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateCompleteNumericTargetComputationTable model ["Xj"] (idOf target)
    [(guard, expression)]).toOption.map .number

private def guards (target : String) : List (Option (CheckedScalarComputationStep model)) :=
  [numberStep? ("K" ++ target) (some (.fieldFilled (idOf target))) (.literal one),
    numberStep? ("KN" ++ target) (some (.fieldNotFilled (idOf target))) (.literal one)]

private def amount? (name : String) : Option (CheckedTemporalShiftAmount model) :=
  (elaborateTemporalFieldShiftAmount model (idOf name)).toOption

private def document? (step : Option (CheckedDocumentComputationStep model)) :
    Option (CheckedScalarComputationStep model) :=
  step.map .document

/-- The grid's computations in its authored order, every reader ahead of what it reads. -/
private def authored : List (CheckedScalarComputationStep model) :=
  ((["TT", "DD", "MX", "MY", "SF", "QF"].flatMap guards) ++
    [document? do
        let day ← amount? "PC"
        let hours ← amount? "P1"
        let operation ← (elaborateDateTimeDayThenSubdayShiftComputation model (idOf "MA") day .hours
          hours (idOf "MX")).toOption
        pure (.ofDateTimeDayThenSubdayShift operation),
      document? do
        let hours ← amount? "P1"
        let day ← amount? "PC"
        let operation ← (elaborateDateTimeSubdayThenDayShiftComputation model (idOf "MA") .hours hours
          day (idOf "MY")).toOption
        pure (.ofDateTimeSubdayThenDayShift operation),
      document? ((elaborateTimeFromDateTimeComputation model (idOf "MA") (idOf "TT")).toOption.map
        .ofTimeFromDateTime),
      document? ((elaborateDateFromDateTimeComputation model (idOf "MA") (idOf "DD")).toOption.map
        .ofDateFromDateTime),
      document? ((checkStringFirstFilledComputation model ["Xj"] (idOf "SF")
        (.list (entities "SA" "S3"))).toOption.map .ofStringFirstFilled),
      numberStep? "QF" none (.atom (.firstFilled (entities "QA" "Q3"))),
      numberStep? "VN" none (.atom (.valueCount 5 (entities "QA" "Q3"))),
      numberStep? "VS" none (.atom (.tokenValueCount "AA"
        { first := .field (.direct (bare "SA")), rest := [.field (.direct (bare "S3"))] })),
      numberStep? "VB" none (.atom (.booleanValueCount true (entities "BA" "B3"))),
      document? do
        let days ← amount? "P1"
        let operation ← (elaborateDateTimeDayShiftComputation model (idOf "M1") days (idOf "MA")).toOption
        pure (.ofDateTimeDayShift operation),
      numberStep? "PC" none (.binary .add (.atom (.numeric (.field (bare "P2")))) (.literal one)),
      document? ((checkStringFirstFilledComputation model ["Xj"] (idOf "SA")
        (.list (entities "S1" "S2"))).toOption.map .ofStringFirstFilled),
      numberStep? "QA" none (.atom (.firstFilled (entities "Q1" "Q2"))),
      document? ((checkBooleanFirstFilledComputation model ["Xj"] (idOf "BA")
        (.list (entities "B1" "B2"))).toOption.map .ofBooleanFirstFilled)]).mapM id
    |>.get (by native_decide)

private def plan : CheckedScalarComputationPlan model :=
  (certifyScalarComputationPlan authored).toOption.get (by native_decide)

/-- The raw cell a document holding `text` carries for the named field, as its declaration's own
classifier reads it. -/
private def classified (name text : String) : RawCell :=
  let field := declaration name
  let fallback : RawCell := .rejected .dateFormat
  match field.policy.kind with
  | .temporal .dateTime _ => match certifyDateTimeInputField field with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD fallback
      | .error _ => fallback
  | .temporal .time _ => match certifyTimeInputField field with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD fallback
      | .error _ => fallback
  | .temporal .date _ => match certifyFullDateInputField field with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD fallback
      | .error _ => fallback
  | .boolean => classifyStoredBooleanText text
  | .string => .parsed (.str text)
  | _ => match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed

private def cell (name text : String) : ClassifiedCellInput :=
  { address := { field := idOf name, path := [] }, stored := text, raw := classified name text
    numericDecimal := if (declaration name).policy.kind matches .number _ then
      text.toInt?.map ({ unscaled := ·, scale := 0 }) else none }

/-- Every computed target seeded with a value no row computes; `BA` is left unseeded. -/
private def seeds : List (String × String) :=
  [("MA", "2020-01-01T01:02:03"), ("MX", "2020-01-01T01:02:03"), ("MY", "2020-01-01T01:02:03"),
    ("PC", "99"), ("TT", "01:02:03"), ("DD", "2020-01-01"), ("SA", "AAA"), ("SF", "AAA"), ("QA", "1"),
    ("QF", "2"), ("VN", "99"), ("VS", "99"), ("VB", "99")] ++
  (["TT", "DD", "MX", "MY", "SF", "QF"].flatMap fun target => [("K" ++ target, "99"), ("KN" ++ target, "99")])

/-- The sources of the grid's fresh row. -/
private def good : List (String × String) :=
  [("M1", "2026-05-04T08:30:00"), ("P1", "2"), ("P2", "2"), ("S1", "AA"), ("S3", "A"), ("Q1", "5"),
    ("Q3", "7"), ("B1", "true"), ("B3", "false")]

private def reported : List String :=
  ["MA", "MX", "MY", "PC", "TT", "DD", "SA", "SF", "QA", "QF", "BA", "VN", "VS", "VB"] ++
  (["TT", "DD", "MX", "MY", "SF", "QF"].flatMap fun target => ["K" ++ target, "KN" ++ target])

private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.dateTime (.accepted stored)) | .document target (.time (.accepted stored))
  | .document target (.fullDate (.accepted stored)) | .document target (.string (.accepted stored)) =>
      some (target, stored.text)
  | .document target (.boolean (.value value)) => some (target, toString value)
  | .document target (.dateTime .noValue) | .document target (.dateTime (.poison _))
  | .document target (.time .noValue) | .document target (.time (.poison _))
  | .document target (.fullDate .noValue) | .document target (.fullDate (.poison _))
  | .document target (.string .noValue) | .document target (.string (.poison _))
  | .document target (.boolean .noValue) | .document target (.boolean (.poison _)) => some (target, "-")
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ _
  | .document _ (.dateTime (.errored _ _)) | .document _ (.fullDate (.errored _ _))
  | .document _ (.string (.errored _ _)) | .document _ (.enumeration _) | .document _ (.dateRange _)
  | .document _ (.dateFragment _) => none

/-- Every reported target over one row: the fresh sources with `changes` applied, `none` removing one. -/
private def values? (changes : List (String × Option String)) : Option (List String) := do
  let sources := (good.filter fun (name, _) => !changes.any (·.1 == name)) ++
    changes.filterMap fun (name, text) => text.map (name, ·)
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := (seeds ++ sources).map fun (name, text) => cell name text }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  reported.mapM fun name => (found.find? (·.1 == idOf name)).map (·.2)

/- Row `r1`: every reader takes the fresh upstream rather than its seed; both mixed shifts land on May 9th
at 10:30, and each list reader counts or selects the fresh `AA`, `5` and `true`. -/
example :
    values? [] = some ["2026-05-06T08:30:00", "2026-05-09T10:30:00", "2026-05-09T10:30:00", "3",
      "08:30:00", "2026-05-06", "AA", "AA", "5", "5", "true", "1", "1", "1",
      "1", "-", "1", "-", "1", "-", "1", "-", "1", "-", "1", "-"] := by
  native_decide

/- Row `r2`: a cleared `MA` reaches its readers as empty, a cleared `SA` lets `SF` fall through, and the
exhausted `QA` computes `0`, a filled value `QF` takes and `VN` counts. -/
example :
    values? [("M1", none), ("S1", none), ("Q1", none), ("B1", none)] =
      some ["-", "-", "-", "3", "-", "-", "-", "A", "0", "0", "-", "0", "0", "0",
        "-", "1", "-", "1", "-", "1", "-", "1", "1", "-", "1", "-"] := by
  native_decide

/- Row `r3`: a malformed source poisons its upstream, which ends every scan and count reading it and
poisons both guards. -/
example :
    values? [("M1", some "x"), ("S1", some "BBBB"), ("Q1", some "abc"), ("B1", some "maybe")] =
      some ["-", "-", "-", "3", "-", "-", "-", "-", "-", "-", "-", "-", "-", "-",
        "-", "-", "-", "-", "-", "-", "-", "-", "-", "-", "-", "-"] := by
  native_decide

/- Row `r4`: a poisoned computed amount reaches only the mixed shifts, the extractors reading `MA`
alone, while a malformed second source is never reached by `SF` or `QF` and poisons the counts that
read every source. -/
example :
    values? [("P2", some "abc"), ("S3", some "BBBB"), ("Q3", some "abc")] =
      some ["2026-05-06T08:30:00", "-", "-", "-", "08:30:00", "2026-05-06", "AA", "AA", "5", "5",
        "true", "-", "-", "1", "1", "-", "1", "-", "-", "-", "-", "-", "1", "-", "1", "-"] := by
  native_decide

/- Row `r5`: with every DateTime, amount, String and Number source absent, the Number `QF` still
computes the exhausted `0` its guard reads filled, while the String `SF` clears. -/
example :
    values? [("M1", none), ("P1", none), ("P2", none), ("S1", none), ("S3", none), ("Q1", none),
        ("Q3", none)] =
      some ["-", "-", "-", "1", "-", "-", "-", "-", "0", "0", "true", "0", "0", "1",
        "-", "1", "-", "1", "-", "1", "-", "1", "-", "1", "1", "-"] := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanExtractor
