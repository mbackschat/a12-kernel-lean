import A12Kernel.Elaboration.DateTimeDayShiftComputation

/-! # Checked DateTime day-shift computation locks -/

namespace A12Kernel.Conformance.DateTimeDayShiftComputation

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "ScheduledAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now } }

private def target : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "CalculatedAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy'T'HH:mm:ss"
    partialMode := .full } }

private def model : FlatModel := {
  fields := [source, target]
  timeZoneId := "Europe/Berlin" }

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def sourceLocal : LocalDateTime :=
  (LocalDateTime.ofYmdHms? 1916 5 1 23 30 0).get (by native_decide)

private def instant : Instant :=
  (ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLocal)
    |>.get (by native_decide)

private def temporalRaw : RawCell :=
  .parsed (.temporal (.dateTime instant
    sourceLocal.date.civil.parts sourceLocal.time .storedGregorian))

private def sourceData (sourceStored targetStored : String)
    (sourceRaw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [
    { address := { field := source.id, path := [] }
      stored := sourceStored
      raw := sourceRaw },
    { address := { field := target.id, path := [] }
      stored := targetStored
      raw := temporalRaw }
  ] }

private def operation? :=
  (elaborateDateTimeDayShiftComputation
    model source.id (.literal (-1)) target.id).toOption

private def view? (input : DocumentData) :
    Option (DateTimeComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  let operation ← operation?
  operation.executeResult checked [] |>.toOption

private def destinationWith (state : DateTimeTargetState) :
    DateTimeComputationDestination :=
  fun field => if field == target.id then state else .absent

private def errorOf
    (result : Except DateTimeDayShiftComputationElabError value) :
    Option DateTimeDayShiftComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def old : StoredDateTime :=
  ⟨"01.05.1916T23:30:00", by decide⟩

private def shifted : StoredDateTime :=
  ⟨"30.04.1916T22:30:00", by decide⟩

/- The source-offset fallback preserves the target civil date before declaration-owned
   rendering; the changed value survives result classification and exact application. -/
example : (do
    let view ← view? (sourceData old.text old.text temporalRaw)
    let applied ← view.applyTo (destinationWith .absent) |>.toOption
    pure (view.withoutErrors, view.withChanges, view.cleared,
      applied target.id)) =
    some ([
      { targetField := target.id, value := shifted }
    ], [
      { targetField := target.id, value := shifted }
    ], [], .presentValue shifted) := by
  native_decide

/- An unchanged source-relative result remains public but is not re-applied against a
   different destination. -/
example : (do
    let view ← view? (sourceData old.text shifted.text temporalRaw)
    let applied ←
      view.applyTo (destinationWith (.presentValue old)) |>.toOption
    pure (view.withoutErrors, view.withChanges, applied target.id)) =
    some ([
      { targetField := target.id, value := shifted }
    ], [], .presentValue old) := by
  native_decide

/- Clean absence and reached formal poison both clear a source-filled target, but
   neither manufactures a DateTime computed-instance error or residual message. -/
example :
    (view? (sourceData "" old.text .presentEmpty)).map
        (fun view => (view.cleared, view.noErrorOccurred)) =
      some ([target.id], true) ∧
    (view? (sourceData "bad" old.text (.rejected .malformed))).map
        (fun view => (view.cleared, view.noErrorOccurred)) =
      some ([target.id], true) := by
  native_decide

/- A DateTime day shift cannot read the field that it computes. -/
example :
    let selfModel : FlatModel := {
      fields := [target]
      timeZoneId := "Europe/Berlin" }
    errorOf (elaborateDateTimeDayShiftComputation
      selfModel target.id (.literal 1) target.id) =
        some (.targetSelfReference target.id) := by
  native_decide

end A12Kernel.Conformance.DateTimeDayShiftComputation
