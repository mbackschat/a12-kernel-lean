import A12Kernel.Elaboration.FullDateComputation

/-! # Checked full-Date field-copy locks -/

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

private def model : FlatModel := {
  fields := [source, target]
  timeZoneId := "UTC" }

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

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

private def checked? (data : DocumentData) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" data).toOption

private def operation? : Option (CheckedFullDateFieldCopy model) :=
  (elaborateFullDateFieldCopy model source.id target.id).toOption

private def errorOf (result : Except FullDateComputationElabError value) :
    Option FullDateComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def view? (data : DocumentData) :
    Option (FullDateComputationRunView FormalCause) := do
  let checked ← checked? data
  let operation ← operation?
  operation.executeResult checked [] |>.toOption

private def destinationWith (state : FullDateTargetState) :
    FullDateComputationDestination :=
  fun field => if field == target.id then state else .absent

private def oldDate : StoredDate := ⟨"06.04.2024", by decide⟩
private def copiedDate : StoredDate := ⟨"07.04.2024", by decide⟩
private def oldRaw : RawCell := temporalRaw 2024 4 6
private def copiedRaw : RawCell := temporalRaw 2024 4 7

/- One checked copy preserves the source instant through target rendering, result classification, and destination application. -/
example : (do
    let view ← view? (input "2024-04-07" oldDate.text copiedRaw oldRaw)
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
example : (view?
    (input "2024-04-07" copiedDate.text copiedRaw copiedRaw)).map
      (fun view => (view.withoutErrors, view.withChanges)) =
    some ([
      { targetField := target.id, value := copiedDate }
    ], []) := by
  native_decide

/- Clean source absence and reached formal invalidity remain distinct quiet target outcomes; both clear only the filled target. -/
example :
    (view? (input "" oldDate.text .presentEmpty oldRaw)).map
      (fun view => (view.cleared, view.noErrorOccurred)) =
        some ([target.id], true) ∧
    (view? (input "bad" oldDate.text (.rejected .malformed) oldRaw)).map
      (fun view => (view.cleared, view.noErrorOccurred)) =
        some ([target.id], true) := by
  native_decide

example :
    let selfModel : FlatModel := {
      fields := [target]
      timeZoneId := "UTC" }
    errorOf (elaborateFullDateFieldCopy selfModel
      target.id target.id) =
        some (.targetSelfReference target.id) := by
  native_decide

end A12Kernel.Conformance.FullDateComputation
