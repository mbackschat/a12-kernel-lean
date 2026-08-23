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
    format := "yyyy-MM-dd'T'HH:mm:ss"
    partialMode := .full } }

private def amount : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "Days"
  policy := { kind := .number { scale := 0, signed := true } } }

private def nextAmount : FlatFieldDecl := {
  id := 4
  groupPath := ["Order"]
  name := "MoreDays"
  policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [source, target, amount, nextAmount]
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

/-- The raw cell a certified DateTime declaration classifies `text` into, in the model's own zone.

Each target label below is load-bearing: it is what decides whether the computed result counts as a
change. So the label stays the parameter and its value follows from it, which also makes every document
here one `CheckedDocument.temporallyCoherent` accepts — a real cell's value is derived from its own text
rather than paired with an unrelated instant. Classification itself is locked in
[`Conformance/DateTimeInput.lean`](DateTimeInput.lean); this module's subject is the shift. -/
private def temporalRawOf (text : String) : RawCell :=
  match (certifyDateTimeInputField target).toOption with
  | none => .rejected .dateFormat
  | some checked =>
      match checked.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

private def amountStored : RawCell → String
  | .parsed (.num value) => toString value
  | .rejected .declaredConstraint => "0.1"
  | .presentEmpty => ""
  | _ => "bad"

private def sourceData (sourceStored targetStored : String)
    (sourceRaw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [
    { address := { field := source.id, path := [] }
      stored := sourceStored
      raw := sourceRaw },
    { address := { field := target.id, path := [] }
      stored := targetStored
      raw := temporalRawOf targetStored }
  ] }

private def dynamicData (targetStored : String) (amountRaw : RawCell) :
    DocumentData := {
  instantiatedRows := []
  cells := [
    { address := { field := target.id, path := [] }
      stored := targetStored
      raw := temporalRawOf targetStored },
    { address := { field := amount.id, path := [] }
      stored := amountStored amountRaw
      raw := amountRaw }
  ] }

private def twoDayData (targetStored : String)
    (firstRaw secondRaw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [
    { address := { field := target.id, path := [] }
      stored := targetStored
      raw := temporalRawOf targetStored },
    { address := { field := amount.id, path := [] }
      stored := amountStored firstRaw
      raw := firstRaw },
    { address := { field := nextAmount.id, path := [] }
      stored := amountStored secondRaw
      raw := secondRaw }
  ] }

private def fieldTwoDayData (sourceStored targetStored : String)
    (sourceRaw firstRaw secondRaw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [
    { address := { field := source.id, path := [] }
      stored := sourceStored
      raw := sourceRaw },
    { address := { field := target.id, path := [] }
      stored := targetStored
      raw := temporalRawOf targetStored },
    { address := { field := amount.id, path := [] }
      stored := amountStored firstRaw
      raw := firstRaw },
    { address := { field := nextAmount.id, path := [] }
      stored := amountStored secondRaw
      raw := secondRaw }
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
  ⟨"1916-05-01T23:30:00", by decide⟩

private def shifted : StoredDateTime :=
  ⟨"1916-04-30T22:30:00", by decide⟩

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

/- One checked dynamic computation consumes each supplied world independently, retains
   exact milliseconds through the day landing, and classifies declaration-owned text
   relative to the immutable source. -/
example : (do
    let checked ←
      (checkDocument prepared "en_US"
        (dynamicData old.text (.parsed (.num 1)))).toOption
    let operation ←
      (elaborateNowDateTimeDayShiftComputation
        model (.literal 1) target.id).toOption
    let firstLocal ← LocalDateTime.ofYmdHms? 2024 3 30 2 30 0
    let secondLocal ← LocalDateTime.ofYmdHms? 2024 10 26 2 30 0
    let firstNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? firstLocal
    let secondNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? secondLocal
    let firstOperand ←
      operation.evaluateOperand { now := {
        epochMillis := firstNow.epochMillis + 777 } } checked |>.toOption
    let firstView ←
      operation.executeResult { now := {
        epochMillis := firstNow.epochMillis + 777 } } checked
          ([] : List FormalCause) |>.toOption
    let firstApplied ←
      firstView.applyTo (destinationWith .absent) |>.toOption
    let secondView ←
      operation.executeResult { now := {
        epochMillis := secondNow.epochMillis + 333 } } checked
          ([] : List FormalCause) |>.toOption
    pure (firstOperand,
      firstView.withChanges.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text),
      firstApplied target.id,
      secondView.withChanges.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text))) =
    some (
      .value { epochMillis := 1711845000777 },
      ["2024-03-31T01:30:00"],
      .presentValue ⟨"2024-03-31T01:30:00", by decide⟩,
      ["2024-10-27T02:30:00"]) := by
  native_decide

/- Dynamic day target execution preserves the settled distinction between formal
   poison and arithmetic no-value. A reached formal cause remains poison and clears a
   filled source without becoming a target-local error. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let poisonedInput ←
      (checkDocument prepared "en_US"
        (dynamicData old.text (.rejected .declaredConstraint))).toOption
    let checkedAmount ←
      (elaborateValueAsDateTimeFieldShiftAmount model amount.id).toOption
    let poisoned ←
      (elaborateNowDateTimeDayShiftComputation
        model checkedAmount target.id).toOption
    let poisonOutcome ←
      poisoned.evaluateOutcome { now } poisonedInput |>.toOption
    let poisonView ←
      poisoned.executeResult { now } poisonedInput ([] : List FormalCause)
        |>.toOption
    pure (poisonOutcome, poisonView.cleared)) =
    some (.poison .declaredConstraint, [target.id]) := by
  native_decide

/- Arithmetic domain failure remains quiet no-value and clears a filled source without
   manufacturing any public error. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let input ←
      (checkDocument prepared "en_US"
        (dynamicData old.text (.parsed (.num 1)))).toOption
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount model ["Order"]
        (.binary .divide
          (.literal { value := 1, authoredScale := 0 })
          (.literal { value := 0, authoredScale := 0 }))).toOption
    let empty ←
      (elaborateNowDateTimeDayShiftComputation
        model domainAmount target.id).toOption
    let emptyView ←
      empty.executeResult { now } input ([] : List FormalCause)
        |>.toOption
    pure (emptyView.cleared, emptyView.noErrorOccurred)) =
    some ([target.id], true) := by
  native_decide

/- A successful value equal to the immutable source remains public but is not
   re-applied as a source-relative change. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let unchangedInput ←
      (checkDocument prepared "en_US"
        (dynamicData "2024-06-15T10:30:00" (.parsed (.num 0)))).toOption
    let unchanged ←
      (elaborateNowDateTimeDayShiftComputation
        model (.literal 0) target.id).toOption
    let unchangedView ←
      unchanged.executeResult { now } unchangedInput ([] : List FormalCause)
        |>.toOption
    pure (
      unchangedView.withoutErrors.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text),
      unchangedView.withChanges.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text))) =
    some (["2024-06-15T10:30:00"], ([] : List String)) := by
  native_decide

/- The bounded dynamic two-day computation retains exact milliseconds, samples each
   supplied world independently, and applies declaration-owned target text. -/
example : (do
    let checked ←
      (checkDocument prepared "en_US"
        (twoDayData old.text (.parsed (.num 1)) (.parsed (.num 1)))).toOption
    let operation ←
      (elaborateNowDateTimeTwoDayShiftComputation
        model (.literal 1) (.literal 1) target.id).toOption
    let firstLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let secondLocal ← LocalDateTime.ofYmdHms? 2024 6 16 10 30 0
    let firstNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? firstLocal
    let secondNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? secondLocal
    let firstOperand ←
      operation.evaluateOperand
        { now := { epochMillis := firstNow.epochMillis + 777 } } checked
        |>.toOption
    let firstView ←
      operation.executeResult
        { now := { epochMillis := firstNow.epochMillis + 777 } } checked
        ([] : List FormalCause) |>.toOption
    let applied ←
      firstView.applyTo (destinationWith .absent) |>.toOption
    let secondView ←
      operation.executeResult
        { now := { epochMillis := secondNow.epochMillis + 333 } } checked
        ([] : List FormalCause) |>.toOption
    pure (firstOperand, firstView.withChanges.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text),
      applied target.id, secondView.withChanges.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text))) =
    some (
      .value { epochMillis := 1718613000777 },
      ["2024-06-17T10:30:00"],
      .presentValue ⟨"2024-06-17T10:30:00", by decide⟩,
      ["2024-06-18T10:30:00"]) := by
  native_decide

/- Source-relative equality remains public without becoming a change. Quiet failure
   in either day amount clears a filled source without manufacturing an error. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let unchangedInput ←
      (checkDocument prepared "en_US"
        (twoDayData "2024-06-17T10:30:00"
          (.parsed (.num 1)) (.parsed (.num 1)))).toOption
    let unchanged ←
      (elaborateNowDateTimeTwoDayShiftComputation
        model (.literal 1) (.literal 1) target.id).toOption
    let unchangedView ←
      unchanged.executeResult { now } unchangedInput ([] : List FormalCause)
        |>.toOption
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount model ["Order"]
        (.binary .divide
          (.literal { value := 1, authoredScale := 0 })
          (.literal { value := 0, authoredScale := 0 }))).toOption
    let innerEmpty ←
      (elaborateNowDateTimeTwoDayShiftComputation
        model domainAmount (.literal 1) target.id).toOption
    let outerEmpty ←
      (elaborateNowDateTimeTwoDayShiftComputation
        model (.literal 1) domainAmount target.id).toOption
    let innerView ←
      innerEmpty.executeResult { now } unchangedInput
        ([] : List FormalCause) |>.toOption
    let outerView ←
      outerEmpty.executeResult { now } unchangedInput
        ([] : List FormalCause) |>.toOption
    pure (
      unchangedView.withoutErrors.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text),
      unchangedView.withChanges,
      innerView.cleared, outerView.cleared,
      innerView.noErrorOccurred && outerView.noErrorOccurred)) =
    some (
      ["2024-06-17T10:30:00"], [],
      [target.id], [target.id], true) := by
  native_decide

/- Inner and outer formal causes remain distinct rich poison outcomes and both clear a
   source-filled target through the shared result classifier. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let input ←
      (checkDocument prepared "en_US"
        (twoDayData old.text
          (.rejected .malformed)
          (.rejected .declaredConstraint))).toOption
    let firstField ←
      (elaborateValueAsDateTimeFieldShiftAmount model amount.id).toOption
    let secondField ←
      (elaborateValueAsDateTimeFieldShiftAmount model nextAmount.id).toOption
    let innerPoison ←
      (elaborateNowDateTimeTwoDayShiftComputation
        model firstField secondField target.id).toOption
    let outerPoison ←
      (elaborateNowDateTimeTwoDayShiftComputation
        model (.literal 1) secondField target.id).toOption
    let innerOutcome ←
      innerPoison.evaluateOutcome { now } input |>.toOption
    let outerOutcome ←
      outerPoison.evaluateOutcome { now } input |>.toOption
    let innerView ←
      innerPoison.executeResult { now } input ([] : List FormalCause)
        |>.toOption
    let outerView ←
      outerPoison.executeResult { now } input ([] : List FormalCause)
        |>.toOption
    pure (innerOutcome, outerOutcome, innerView.cleared, outerView.cleared)) =
    some (
      .poison .malformed,
      .poison .declaredConstraint,
      [target.id], [target.id]) := by
  native_decide

/- The checked field-backed two-day computation feeds both source-offset landings into
   the declaration-owned target, result view, and application path. -/
example : (do
    let sourceLabel ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let resolved ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
    let raw : RawCell :=
      .parsed (.temporal (.dateTime
        { epochMillis := resolved.epochMillis + 777 }
        sourceLabel.date.civil.parts sourceLabel.time .storedGregorian))
    let checked ←
      (checkDocument prepared "en_US"
        (fieldTwoDayData "2024-06-15T10:30:00" old.text raw
          (.parsed (.num 1)) (.parsed (.num 1)))).toOption
    let operation ←
      (elaborateDateTimeTwoDayShiftComputation
        model source.id (.literal 1) (.literal 1) target.id).toOption
    let operand ← operation.evaluateOperand checked |>.toOption
    let view ←
      operation.executeResult checked ([] : List FormalCause) |>.toOption
    let applied ← view.applyTo (destinationWith .absent) |>.toOption
    pure (operand, view.withChanges.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text),
      applied target.id)) =
    some (
      .value { epochMillis := 1718613000777 },
      ["2024-06-17T10:30:00"],
      .presentValue ⟨"2024-06-17T10:30:00", by decide⟩) := by
  native_decide

/- Source-relative equality remains public without becoming a change. Quiet failure
   in either day amount clears the existing target without manufacturing an error. -/
example : (do
    let sourceLabel ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let resolved ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
    let raw : RawCell :=
      .parsed (.temporal (.dateTime resolved
        sourceLabel.date.civil.parts sourceLabel.time .storedGregorian))
    let checked ←
      (checkDocument prepared "en_US"
        (fieldTwoDayData "2024-06-15T10:30:00"
          "2024-06-17T10:30:00" raw
          (.parsed (.num 1)) (.parsed (.num 1)))).toOption
    let unchanged ←
      (elaborateDateTimeTwoDayShiftComputation
        model source.id (.literal 1) (.literal 1) target.id).toOption
    let unchangedView ←
      unchanged.executeResult checked ([] : List FormalCause) |>.toOption
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount model ["Order"]
        (.binary .divide
          (.literal { value := 1, authoredScale := 0 })
          (.literal { value := 0, authoredScale := 0 }))).toOption
    let innerEmpty ←
      (elaborateDateTimeTwoDayShiftComputation
        model source.id domainAmount (.literal 1) target.id).toOption
    let outerEmpty ←
      (elaborateDateTimeTwoDayShiftComputation
        model source.id (.literal 1) domainAmount target.id).toOption
    let innerView ←
      innerEmpty.executeResult checked ([] : List FormalCause) |>.toOption
    let outerView ←
      outerEmpty.executeResult checked ([] : List FormalCause) |>.toOption
    pure (
      unchangedView.withoutErrors.map
        (fun (entry : DateTimeComputedInstance) => entry.value.text),
      unchangedView.withChanges,
      innerView.cleared, outerView.cleared,
      innerView.noErrorOccurred && outerView.noErrorOccurred)) =
    some (
      ["2024-06-17T10:30:00"], [],
      [target.id], [target.id], true) := by
  native_decide

/- Inner and outer formal causes stay distinct poison outcomes. The nested certificate
   still rejects a direct source equal to its DateTime target. -/
example : (do
    let innerInput ←
      (checkDocument prepared "en_US"
        (fieldTwoDayData "bad-source" old.text
          (.rejected .malformed)
          (.rejected .declaredConstraint)
          (.rejected .declaredConstraint))).toOption
    let outerInput ←
      (checkDocument prepared "en_US"
        (fieldTwoDayData old.text old.text temporalRaw
          (.parsed (.num 1))
          (.rejected .declaredConstraint))).toOption
    let firstField ←
      (elaborateValueAsDateTimeFieldShiftAmount model amount.id).toOption
    let secondField ←
      (elaborateValueAsDateTimeFieldShiftAmount model nextAmount.id).toOption
    let innerPoison ←
      (elaborateDateTimeTwoDayShiftComputation
        model source.id firstField secondField target.id).toOption
    let outerPoison ←
      (elaborateDateTimeTwoDayShiftComputation
        model source.id (.literal 1) secondField target.id).toOption
    let innerOutcome ← innerPoison.evaluateOutcome innerInput |>.toOption
    let outerOutcome ← outerPoison.evaluateOutcome outerInput |>.toOption
    pure (innerOutcome, outerOutcome)) =
    some (.poison .malformed, .poison .declaredConstraint) ∧
    (let selfModel : FlatModel := {
      fields := [target]
      timeZoneId := "Europe/Berlin" }
    errorOf (elaborateDateTimeTwoDayShiftComputation
      selfModel target.id (.literal 1) (.literal 1) target.id) =
        some (.targetSelfReference target.id)) := by
  native_decide

end A12Kernel.Conformance.DateTimeDayShiftComputation
