import A12Kernel.Elaboration.DateTimeSubdayShiftComputation

/-! # Checked DateTime sub-day computation locks -/

namespace A12Kernel.Conformance.DateTimeSubdayShiftComputation

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "ScheduledAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now } }

private def amount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "Offset"
  policy := { kind := .number { scale := 0, signed := true } } }

private def target : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "CalculatedAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy'T'HH:mm:ss"
    partialMode := .full } }

private def model : FlatModel := {
  fields := [source, amount, target]
  timeZoneId := "Europe/Berlin" }

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? (sourceLocal : LocalDateTime) (millisecond : Int)
    (sourceRaw : Option RawCell := none)
    (amountRaw : RawCell := .parsed (.num 0))
    (targetStored : String := "old") :
    Option (CheckedDocument model) := do
  let resolved ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLocal
  let instant : Instant := {
    epochMillis := resolved.epochMillis + millisecond
  }
  let generatedRaw : RawCell :=
    .parsed (.temporal (.dateTime instant
      sourceLocal.date.civil.parts sourceLocal.time .storedGregorian))
  let actualSourceRaw := sourceRaw.getD generatedRaw
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      { address := { field := source.id, path := [] }
        stored := "source"
        raw := actualSourceRaw },
      { address := { field := amount.id, path := [] }
        stored := "amount"
        raw := amountRaw },
      { address := { field := target.id, path := [] }
        stored := targetStored
        raw := generatedRaw }
    ]
  } |>.toOption

private def operation? (unit : DateTimeSubdayUnit) (value : Rat) :=
  (elaborateDateTimeSubdayShiftComputation
    model source.id unit (.literal value) target.id).toOption

private def errorOf
    (result : Except DateTimeSubdayShiftComputationElabError value) :
    Option DateTimeSubdayShiftComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def text? (unit : DateTimeSubdayUnit) (value : Rat)
    (sourceLocal : LocalDateTime) : Option String := do
  let input ← input? sourceLocal 777
  let operation ← operation? unit value
  let view ← operation.executeResult input ([] : List FormalCause) |>.toOption
  view.withoutErrors.head?.map (·.value.text)

/- All three field-backed sub-day units use exact instant arithmetic and preserve
   calendar carry before declaration-owned whole-second rendering. -/
example :
    let sourceLocal :=
      (LocalDateTime.ofYmdHms? 2024 6 15 23 59 30).get (by native_decide)
    [ text? .hours 2 sourceLocal
    , text? .minutes 2 sourceLocal
    , text? .seconds 45 sourceLocal ] =
      [ some "16.06.2024T01:59:30"
      , some "16.06.2024T00:01:30"
      , some "16.06.2024T00:00:15" ] := by
  native_decide

/- Milliseconds survive exact shifting until the target renderer deliberately drops
   them, and a changed success reaches the existing application path. -/
example : (do
    let sourceLocal ← LocalDateTime.ofYmdHms? 2024 6 15 23 59 30
    let input ← input? sourceLocal 777
    let operation ← operation? .hours 2
    let operand ← operation.evaluateOperand input |>.toOption
    let view ← operation.executeResult input ([] : List FormalCause) |>.toOption
    let applied ← view.applyTo (fun _ => .absent) |>.toOption
    pure (operand, applied target.id)) =
      some (.value { epochMillis := 1718495970777 },
        .presentValue ⟨"16.06.2024T01:59:30", by decide⟩) := by
  native_decide

/- A formal source stops before a different formal amount and remains target poison. -/
example : (do
    let sourceLocal ← LocalDateTime.ofYmdHms? 2024 6 15 23 59 30
    let input ← input? sourceLocal 0 (some (.rejected .malformed))
      (.rejected .declaredConstraint)
    let checkedAmount ←
      (elaborateValueAsDateTimeFieldShiftAmount model amount.id).toOption
    let operation ←
      (elaborateDateTimeSubdayShiftComputation
        model source.id .seconds checkedAmount target.id).toOption
    operation.evaluateOutcome input |>.toOption) =
      some (.poison .malformed) := by
  native_decide

/- A sub-day shift cannot read the DateTime field that it computes. -/
example :
    let selfModel : FlatModel := {
      fields := [target]
      timeZoneId := "Europe/Berlin" }
    errorOf (elaborateDateTimeSubdayShiftComputation
      selfModel target.id .hours (.literal 1) target.id) =
        some (.targetSelfReference target.id) := by
  native_decide

end A12Kernel.Conformance.DateTimeSubdayShiftComputation
