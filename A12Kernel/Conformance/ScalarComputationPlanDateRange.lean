import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Authored scalar plan locks: a DateRange construction at a join

A DateRange `DR = DateRange(DC, D1)` reads a computed full-Date copy `DC = [D0]`, and Number computations
read `DR` through the day of each endpoint and two fill guards, each reader authored ahead of what it
reads, beside the control `DR2 = DateRange(D0, D1)` over sources alone. Every computed target is seeded
with a value no row computes. The fixture is the model of the
[DateRange join checkpoint](../../docs/sources/computation-scheduling-probes.md#src-date-range-join),
and every document row is the Kernel's, measured on both codegen strategies.

The rows separate a fresh read of `DC` from its seed, a cleared range read as empty from one read as
poison, and an errored range, which the Kernel retains with its inverted rendering, from one read back
from that rendering: reading the retained text would give the endpoint days `1` and `20` and fire `KR`.
-/

namespace A12Kernel.Conformance.ScalarComputationPlanDateRange

open A12Kernel

private def d0Id : FieldId := 0
private def d1Id : FieldId := 1
private def dcId : FieldId := 2
private def drId : FieldId := 3
private def dr2Id : FieldId := 4
private def nsId : FieldId := 5
private def neId : FieldId := 6
private def krId : FieldId := 7
private def knrId : FieldId := 8

private def dateDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Drj"]
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full }

private def rangeDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Drj"]
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }

private def numberDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Drj"]
  name
  policy := { kind := .number { scale := 0, signed := true } }

private def model : FlatModel :=
  { fields := [
      dateDeclaration d0Id "D0", dateDeclaration d1Id "D1", dateDeclaration dcId "DC",
      rangeDeclaration drId "DR", rangeDeclaration dr2Id "DR2",
      numberDeclaration nsId "NS", numberDeclaration neId "NE",
      numberDeclaration krId "KR", numberDeclaration knrId "KNR"]
    timeZoneId := "Europe/Berlin" }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def numberStep? (target : FieldId) (guard : Option ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateNumericTargetComputationTable model ["Drj"] target [(guard, expression)]).toOption.map
    .number

private def rangeStep? (target start finish : FieldId) : Option (CheckedScalarComputationStep model) :=
  (elaborateDateRangeConstructionComputation model ["Drj"] target start finish).toOption.map
    fun operation => .document (.ofDateRangeConstruction operation)

private def dateCopy? : Option (CheckedScalarComputationStep model) :=
  (elaborateFullDateFieldComputation model d0Id dcId).toOption.map
    fun operation => .document (.ofFullDate operation)

private def endpointDay (bound : DateRangeBound) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateRangeBoundPart (bare "DR") bound .day)

private def one : AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value := 1, authoredScale := 0 }

/-- The model's computations in its authored order, every reader ahead of what it reads. -/
private def authored : List (CheckedScalarComputationStep model) :=
  ([numberStep? nsId none (endpointDay .start), numberStep? neId none (endpointDay .finish),
    numberStep? krId (some (.fieldFilled drId)) one,
    numberStep? knrId (some (.fieldNotFilled drId)) one,
    rangeStep? drId dcId d1Id, dateCopy?, rangeStep? dr2Id d0Id d1Id].mapM id).get (by native_decide)

private def plan : CheckedScalarComputationPlan model :=
  (certifyScalarComputationPlan authored).toOption.get (by native_decide)

/-- The raw cell the Date declaration classifies `text` into in the model's zone. -/
private def dateRaw (text : String) : RawCell :=
  match (certifyFullDateInputField (dateDeclaration d0Id "D0")).toOption with
  | none => .rejected .dateFormat
  | some checked =>
      match checked.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

private def dateCell (field : FieldId) (text : String) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := text, raw := dateRaw text }

private def rangeCell (field : FieldId) (text : String) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := text
    raw := (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
      { format := "yyyy-MM-dd", separator := "/" } text).toOption.getD (.rejected .dateFormat) }

private def numberCell (field : FieldId) (amount : Int) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := toString amount
    raw := .parsed (.num amount)
    numericDecimal := some { unscaled := amount, scale := 0 } }

/-- Every computed target seeded with a value no row computes, so a stale read would show. -/
private def seeds : List ClassifiedCellInput :=
  [dateCell dcId "2000-01-01", rangeCell drId "2000-01-01/2000-01-02",
    rangeCell dr2Id "2000-01-01/2000-01-02"] ++ [nsId, neId, krId, knrId].map (numberCell · 99)

private def reported : List FieldId := [dcId, drId, dr2Id, nsId, neId, krId, knrId]

/-- A computed value, `E ` before the attempted rendering of a target the Kernel retains as errored,
or `-` for one it reports cleared without an error at it. -/
private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.fullDate (.accepted stored)) => some (target, stored.text)
  | .document target (.fullDate .noValue) | .document target (.fullDate (.poison _)) =>
      some (target, "-")
  | .document target (.dateRange (.accepted stored)) => some (target, stored.text)
  | .document target (.dateRange (.errored attempted _)) => some (target, s!"E {attempted.text}")
  | .document target (.dateRange .noValue) | .document target (.dateRange (.poison _)) =>
      some (target, "-")
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ _
  | .document _ (.fullDate (.errored _ _)) | .document _ (.dateTime _) | .document _ (.time _)
  | .document _ (.enumeration _) | .document _ (.boolean _) | .document _ (.dateFragment _)
  | .document _ (.string _) => none

private def values? (cells : List ClassifiedCellInput) : Option (List String) := do
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := seeds ++ cells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  reported.mapM fun target => (found.find? (·.1 == target)).map (·.2)

/- Rows `r01` and `r03`: `DR` reads the fresh `DC`, not its seed, and its readers the fresh `DR`; a
malformed `D0` poisons the copy, both ranges, both endpoint days and both guards. -/
example :
    values? [dateCell d0Id "2024-03-10", dateCell d1Id "2024-04-20"] =
      some ["2024-03-10", "2024-03-10/2024-04-20", "2024-03-10/2024-04-20", "10", "20", "1", "-"] ∧
    values? [dateCell d0Id "x", dateCell d1Id "2024-04-20"] =
      some ["-", "-", "-", "-", "-", "-", "-"] := by
  native_decide

/- Rows `r02` and `r05`: an absent endpoint clears the range, which its readers read as empty: both
endpoint days `0` and only the unfilled guard fires. -/
example :
    values? [dateCell d1Id "2024-04-20"] = some ["-", "-", "-", "0", "0", "-", "1"] ∧
    values? [dateCell d0Id "2024-03-10"] = some ["2024-03-10", "-", "-", "0", "0", "-", "1"] := by
  native_decide

/- Row `r04`: an inverted range is retained errored with its rendering and reaches every reader as
poison, the guards included. -/
example :
    values? [dateCell d0Id "2024-05-01", dateCell d1Id "2024-04-20"] =
      some ["2024-05-01", "E 2024-05-01/2024-04-20", "E 2024-05-01/2024-04-20", "-", "-", "-", "-"] := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanDateRange
