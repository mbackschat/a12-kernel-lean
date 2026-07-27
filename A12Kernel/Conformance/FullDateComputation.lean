import A12Kernel.Elaboration.FullDateComputation

/-! # Checked full-Date computation locks -/

namespace A12Kernel.Conformance.FullDateComputation

open A12Kernel

private def fullDate : TemporalComponents := TemporalComponents.fullDate

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "SourceDate"
  policy := { kind := .temporal .date fullDate } }

private def target : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "TargetDate"
  policy := { kind := .temporal .date fullDate }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy"
    partialMode := .full } }

private def modelFor (zoneId : String) : FlatModel := {
  fields := [source, target]
  timeZoneId := zoneId }

private def prepared? (zoneId : String) :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (modelFor zoneId)).toOption

private def instant? (year : Int) (month day : Nat) : Option Instant :=
  (LocalDateTime.ofYmdHms? year month day 0 0 0).map (·.resolveUtc)

private def temporalRaw (year : Int) (month day : Nat) : RawCell :=
  match instant? year month day with
  | none => .rejected .malformed
  | some instant =>
      .parsed (.temporal (.date instant
        { year, month, day } .storedGregorian))

private def input (sourceStored targetStored : String)
    (sourceRaw targetRaw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [
    { address := { field := source.id, path := [] }
      stored := sourceStored
      raw := sourceRaw },
    { address := { field := target.id, path := [] }
      stored := targetStored
      raw := targetRaw }
  ] }

private def checked? (zoneId : String) (data : DocumentData) :
    Option (CheckedDocument (modelFor zoneId)) := do
  let prepared ← prepared? zoneId
  (checkDocument prepared "en_US" data).toOption

private def fieldOperation? :
    Option (CheckedFullDateComputation (modelFor "UTC")) :=
  (elaborateFullDateFieldComputation
    (modelFor "UTC") source.id target.id).toOption

private def todayOperation? (zoneId : String) :
    Option (CheckedFullDateComputation (modelFor zoneId)) :=
  (elaborateFullDateTodayComputation
    (modelFor zoneId) target.id).toOption

private def errorOf (result : Except FullDateComputationElabError value) :
    Option FullDateComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def faultOf (result : Except FullDateComputationFault value) :
    Option FullDateComputationFault :=
  match result with
  | .ok _ => none
  | .error error => some error

private def fieldView? (data : DocumentData) :
    Option (FullDateComputationRunView FormalCause) := do
  let checked ← checked? "UTC" data
  let operation ← fieldOperation?
  operation.executeResult
    { now := { epochMillis := 0 },
      modelZoneRules := ModelZone.concreteRules }
    checked [] |>.toOption

private def todayView? (zoneId : String) (now : Instant)
    (data : DocumentData) :
    Option (FullDateComputationRunView FormalCause) := do
  let checked ← checked? zoneId data
  let operation ← todayOperation? zoneId
  operation.executeResult
    { now, modelZoneRules := ModelZone.concreteRules }
    checked [] |>.toOption

private def destinationWith (state : FullDateTargetState) :
    FullDateComputationDestination :=
  fun field => if field == target.id then state else .absent

private def oldDate : StoredDate := ⟨"06.04.2024", by decide⟩
private def copiedDate : StoredDate := ⟨"07.04.2024", by decide⟩
private def oldRaw : RawCell := temporalRaw 2024 4 6
private def copiedRaw : RawCell := temporalRaw 2024 4 7

/- One checked copy preserves the source instant through target rendering, result classification, and destination application. -/
example : (do
    let view ← fieldView?
      (input "2024-04-07" oldDate.text copiedRaw oldRaw)
    let applied ← view.applyTo (destinationWith (.presentValue oldDate)) |>.toOption
    pure (view.withoutErrors, view.withChanges,
      applied target.id)) =
    some ([
      { targetField := target.id, value := copiedDate }
    ], [
      { targetField := target.id, value := copiedDate }
    ], .presentValue copiedDate) := by
  native_decide

/- A source-relative unchanged result remains public but is not re-applied. -/
example : (fieldView?
    (input "2024-04-07" copiedDate.text copiedRaw copiedRaw)).map
      (fun view => (view.withoutErrors, view.withChanges)) =
    some ([
      { targetField := target.id, value := copiedDate }
    ], []) := by
  native_decide

/- Clean source absence and reached formal invalidity remain distinct quiet target outcomes; both clear only the filled target. -/
example :
    (fieldView? (input "" oldDate.text .presentEmpty oldRaw)).map
      (fun view => (view.cleared, view.noErrorOccurred)) =
        some ([target.id], true) ∧
    (fieldView? (input "bad" oldDate.text (.rejected .malformed) oldRaw)).map
      (fun view => (view.cleared, view.noErrorOccurred)) =
        some ([target.id], true) := by
  native_decide

example :
    let selfModel : FlatModel := {
      fields := [target]
      timeZoneId := "UTC" }
    errorOf (elaborateFullDateFieldComputation selfModel
      target.id target.id) =
        some (.targetSelfReference target.id) := by
  native_decide

/- One retained instant denotes different local dates in UTC and Berlin. Target rendering therefore follows the checked model zone, not the host zone or an instant-wide fixed offset. -/
example : (do
    let now ← instant? 2024 3 30 |>.bind fun day =>
      some { epochMillis := day.epochMillis + 23 * 60 * 60 * 1000 +
        30 * 60 * 1000 }
    let utcView ← todayView? "UTC" now
      (input "ignored" oldDate.text copiedRaw oldRaw)
    let berlinView ← todayView? "Europe/Berlin" now
      (input "ignored" oldDate.text copiedRaw oldRaw)
    pure (
      utcView.withoutErrors.map (·.value.text),
      berlinView.withoutErrors.map (·.value.text))) =
    some (["30.03.2024"], ["31.03.2024"]) := by
  native_decide

/- The checked operation retains no clock sample: changing only the explicit world across UTC midnight changes `Today`. -/
example : (do
    let first ← instant? 2024 4 6
    let second := { first with
      epochMillis := first.epochMillis + 24 * 60 * 60 * 1000 }
    let firstView ← todayView? "UTC" first
      (input "ignored" oldDate.text copiedRaw oldRaw)
    let secondView ← todayView? "UTC" second
      (input "ignored" oldDate.text copiedRaw oldRaw)
    pure (
      firstView.withoutErrors.map (·.value.text),
      secondView.withoutErrors.map (·.value.text))) =
    some (["06.04.2024"], ["07.04.2024"]) := by
  native_decide

/- Missing model-zone rules fail structurally instead of treating `now` as `Today` or assuming UTC. -/
example : (do
    let now ← instant? 2024 4 6
    let checked ← checked? "UTC"
      (input "ignored" oldDate.text copiedRaw oldRaw)
    let operation ← todayOperation? "UTC"
    pure (faultOf (operation.executeResult { now } checked
      ([] : List FormalCause)))) =
    some (some (.todayUnavailable "UTC")) := by
  native_decide

end A12Kernel.Conformance.FullDateComputation
