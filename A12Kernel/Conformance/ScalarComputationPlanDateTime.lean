import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Authored scalar plan locks: DateTime steps at a join

A DateTime day shift reads a computed Number amount, a sub-day shift reads that computed DateTime, and
Number computations read the result through `DifferenceInHours` and two fill guards, each reader
authored ahead of what it reads. The fixture is the model of the
[DateTime join checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-datetime-join),
and every document row is the Kernel's, measured on both codegen strategies; the guarded `DTC` and its
reader `H2` are left out, since no DateTime carrier here takes a precondition.
-/

namespace A12Kernel.Conformance.ScalarComputationPlanDateTime

open A12Kernel

private def dt0Id : FieldId := 0
private def n0Id : FieldId := 1
private def n1Id : FieldId := 2
private def dtaId : FieldId := 3
private def dtbId : FieldId := 4
private def hId : FieldId := 5
private def kId : FieldId := 6
private def knId : FieldId := 7

private def dateTimeDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Mix"]
  name
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss", partialMode := .full }

private def numberDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Mix"]
  name
  policy := { kind := .number { scale := 0, signed := true } }

private def model : FlatModel :=
  { fields := [
      dateTimeDeclaration dt0Id "DT0", numberDeclaration n0Id "N0", numberDeclaration n1Id "N1",
      dateTimeDeclaration dtaId "DTA", dateTimeDeclaration dtbId "DTB",
      numberDeclaration hId "H", numberDeclaration kId "K", numberDeclaration knId "KN"]
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
  (elaborateNumericTargetComputationTable model ["Mix"] target [(guard, expression)]).toOption.map
    .number

private def dayShiftStep? : Option (CheckedScalarComputationStep model) := do
  let amount ← (elaborateTemporalFieldShiftAmount model n1Id).toOption
  let operation ← (elaborateDateTimeDayShiftComputation model dt0Id amount dtaId).toOption
  pure (.document (.ofDateTimeDayShift operation))

private def subdayShiftStep? : Option (CheckedScalarComputationStep model) := do
  let operation ←
    (elaborateDateTimeSubdayShiftComputation model dtaId .hours (.literal 2) dtbId).toOption
  pure (.document (.ofDateTimeSubdayShift operation))

/-- The model's computations in its authored order, every reader ahead of what it reads. -/
private def authored : List (CheckedScalarComputationStep model) :=
  ([numberStep? hId none (.atom (.dateTimeDifference .hours (.field (bare "DT0")) (.field (bare "DTB")))),
    numberStep? kId (some (.fieldFilled dtbId)) (.atom (.field (bare "N0"))),
    numberStep? knId (some (.fieldNotFilled dtbId)) (.atom (.field (bare "N0"))),
    subdayShiftStep?, dayShiftStep?,
    numberStep? n1Id none (.atom (.field (bare "N0")))].mapM id).get (by native_decide)

private def plan : CheckedScalarComputationPlan model :=
  (certifyScalarComputationPlan authored).toOption.get (by native_decide)

/-- The raw cell the DateTime declaration classifies `text` into in the model's zone, as a document
holding that text carries it. -/
private def dateTimeRaw (text : String) : RawCell :=
  match (certifyDateTimeInputField (dateTimeDeclaration dt0Id "DT0")).toOption with
  | none => .rejected .dateFormat
  | some checked =>
      match checked.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

private def dateTimeCell (field : FieldId) (text : String) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := text, raw := dateTimeRaw text }

private def numberCell (field : FieldId) (amount : Int) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := toString amount
    raw := .parsed (.num amount)
    numericDecimal := some { unscaled := amount, scale := 0 } }

private def malformedNumberCell (field : FieldId) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := "bad", raw := .rejected .malformed }

/-- Every computed target seeded with a value no row computes, so a stale read would show. -/
private def seeds : List ClassifiedCellInput :=
  [n1Id, hId, kId, knId].map (numberCell · 99) ++
    [dtaId, dtbId].map (dateTimeCell · "2000-01-01T00:00:00")

private def reported : List FieldId := [n1Id, dtaId, dtbId, hId, kId, knId]

/-- A computed value, `E` for a target the Kernel retains as errored, or `-` for one it reports cleared
without an error at it. -/
private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.dateTime (.accepted stored)) => some (target, stored.text)
  | .document target (.dateTime (.errored _ _)) => some (target, "E")
  | .document target (.dateTime .noValue) | .document target (.dateTime (.poison _)) =>
      some (target, "-")
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ _
  | .document _ (.fullDate _) | .document _ (.time _) | .document _ (.enumeration _) => none

private def values? (cells : List ClassifiedCellInput) : Option (List String) := do
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := seeds ++ cells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  reported.mapM fun target => (found.find? (·.1 == target)).map (·.2)

private def inputs (dt0 : Option ClassifiedCellInput := some (dateTimeCell dt0Id "2024-03-10T10:00:00"))
    (n0 : Option ClassifiedCellInput := some (numberCell n0Id 2)) : List ClassifiedCellInput :=
  [dt0, n0].filterMap id

/- Every source readable: the day shift reads the fresh `N1`, the sub-day shift the fresh `DTA`, and
the hour difference and both guards the fresh `DTB`. A malformed source clears every join reaching
it, the guards on the poisoned `DTB` included. -/
example :
    values? inputs =
      some ["2", "2024-03-12T10:00:00", "2024-03-12T12:00:00", "50", "2", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "bad"))) =
      some ["2", "-", "-", "-", "-", "-"] ∧
    values? (inputs (n0 := some (malformedNumberCell n0Id))) =
      some ["-", "-", "-", "-", "-", "-"] := by
  native_decide

/- An absent DateTime source clears both shifts, the cleared `DTB` reads empty for the difference,
which answers `0`, and for the guards. An absent Number source copies as `0`, which shifts by no day. -/
example :
    values? (inputs (dt0 := none)) = some ["2", "-", "-", "0", "-", "2"] ∧
    values? (inputs (n0 := none)) =
      some ["0", "2024-03-10T10:00:00", "2024-03-10T12:00:00", "2", "0", "-"] := by
  native_decide

/- Berlin's repeated hour on 2024-10-27. A computed DateTime crosses the join as its rendering read back
in the zone, where `02:30` is the second, standard-time occurrence: a sub-day shift landing on the first
`02:30` is read three hours after `00:30`, and a day shift landing there is shifted from the second.
Reading the exact instants would give `2` and `03:30` instead. A source `02:30` in the document is read
at the second occurrence too, and a spring-forward row is unaffected. -/
example :
    values? (inputs (dt0 := some (dateTimeCell dt0Id "2024-10-27T00:30:00")) (n0 := some (numberCell n0Id 0))) =
      some ["0", "2024-10-27T00:30:00", "2024-10-27T02:30:00", "3", "0", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "2024-10-26T02:30:00")) (n0 := some (numberCell n0Id 1))) =
      some ["1", "2024-10-27T02:30:00", "2024-10-27T04:30:00", "27", "1", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "2024-10-27T01:30:00")) (n0 := some (numberCell n0Id 0))) =
      some ["0", "2024-10-27T01:30:00", "2024-10-27T02:30:00", "2", "0", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "2024-10-27T02:30:00")) (n0 := some (numberCell n0Id 0))) =
      some ["0", "2024-10-27T02:30:00", "2024-10-27T04:30:00", "2", "0", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "2024-03-31T01:30:00")) (n0 := some (numberCell n0Id 0))) =
      some ["0", "2024-03-31T01:30:00", "2024-03-31T04:30:00", "2", "0", "-"] := by
  native_decide

/- A shifted DateTime whose rendering its own target would reject as stored text is retained as errored,
and its readers see poison: one day past `9999-12-31` and two hours past `9999-12-31T23:00` both render a
five-digit year. The row two days short of the ceiling is the control, and a shift landing on the
Gregorian floor is accepted. The Kernel also retains a landing one day below the floor as errored, which
is what separates this account from a year bound; that row is not locked, because the bounded zone
profile resolves no instant below the floor and the day shift refuses before its target is asked. -/
example :
    values? (inputs (dt0 := some (dateTimeCell dt0Id "9999-12-29T00:00:00"))) =
      some ["2", "9999-12-31T00:00:00", "9999-12-31T02:00:00", "50", "2", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "9999-12-31T00:00:00"))) =
      some ["2", "E", "-", "-", "-", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "9999-12-31T23:00:00")) (n0 := some (numberCell n0Id 0))) =
      some ["0", "9999-12-31T23:00:00", "E", "-", "-", "-"] ∧
    values? (inputs (dt0 := some (dateTimeCell dt0Id "1583-10-20T12:00:00")) (n0 := some (numberCell n0Id (-4)))) =
      some ["-4", "1583-10-16T12:00:00", "1583-10-16T14:00:00", "-94", "-4", "-"] := by
  native_decide

/- The String-and-Number result view composes no whole-document family, so it refuses a run that computed
one and names the first such target in execution order, `DTA`, rather than dropping it. -/
example :
    (do
      let input ← (checkDocument prepared "en_US"
        { instantiatedRows := [], cells := seeds ++ inputs }).toOption
      match plan.execution.executeResult (StringResidual := Unit) (NumberPayload := Unit) world
          prepared.patterns input (fun _ => ()) [] [] with
      | .error (.documentTarget target) => some target
      | _ => none) = some dtaId := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanDateTime
