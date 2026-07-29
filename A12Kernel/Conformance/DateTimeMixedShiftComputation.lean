import A12Kernel.Elaboration.DateTimeMixedShiftComputation

/-! # Checked mixed DateTime shift computation locks -/

namespace A12Kernel.Conformance.DateTimeMixedShiftComputation

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1, groupPath := ["Order"], name := "ScheduledAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now } }

private def target : FlatFieldDecl := {
  id := 2, groupPath := ["Order"], name := "CalculatedAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy'T'HH:mm:ss", partialMode := .full } }

private def dayAmount : FlatFieldDecl := {
  id := 3, groupPath := ["Order"], name := "Days"
  policy := { kind := .number { scale := 0, signed := true } } }

private def subdayAmount : FlatFieldDecl := {
  id := 4, groupPath := ["Order"], name := "Subdays"
  policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [source, target, dayAmount, subdayAmount]
  timeZoneId := "Europe/Berlin" }

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? (sourceLabel : LocalDateTime) (millisecond : Int)
    (sourceRaw : Option RawCell) (dayRaw subdayRaw : RawCell)
    (targetStored : String) :
    Option (CheckedDocument model) := do
  let resolved ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      { address := { field := source.id, path := [] }
        stored := "source"
        raw := match sourceRaw with
          | none => .parsed (.temporal (.dateTime
              { epochMillis := resolved.epochMillis + millisecond }
              sourceLabel.date.civil.parts sourceLabel.time .storedGregorian))
          | some other => other },
      { address := { field := target.id, path := [] }
        stored := targetStored
        raw := .parsed (.temporal (.dateTime resolved
          sourceLabel.date.civil.parts sourceLabel.time .storedGregorian)) },
      { address := { field := dayAmount.id, path := [] }
        stored := "day", raw := dayRaw },
      { address := { field := subdayAmount.id, path := [] }
        stored := "subday", raw := subdayRaw }
    ] } |>.toOption

private def operation? (unit : DateTimeSubdayUnit)
    (days subdays : CheckedTemporalShiftAmount model) :=
  (elaborateDateTimeDayThenSubdayShiftComputation
    model source.id days unit subdays target.id).toOption

private def dynamicOperation? (unit : DateTimeSubdayUnit)
    (days subdays : CheckedTemporalShiftAmount model) :=
  (elaborateNowDateTimeDayThenSubdayShiftComputation
    model days unit subdays target.id).toOption

private def reverseOperation? (unit : DateTimeSubdayUnit)
    (subdays days : CheckedTemporalShiftAmount model) :=
  (elaborateDateTimeSubdayThenDayShiftComputation
    model source.id unit subdays days target.id).toOption

private def destination : DateTimeComputationDestination :=
  fun _ => .absent

private def domainAmount? :=
  (elaborateValueAsDateTimeExpressionShiftAmount model ["Order"]
    (.binary .divide
      (.literal { value := 1, authoredScale := 0 })
      (.literal { value := 0, authoredScale := 0 }))).toOption

private def errorOf
    (result : Except DateTimeDayShiftComputationElabError value) :
    Option DateTimeDayShiftComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

/- All elapsed units consume the exact calendar landing. The same carrier also keeps
   Berlin gap/overlap identity, milliseconds, target rendering, and application. -/
example : (do
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 23 30 0
    let spring ← LocalDateTime.ofYmdHms? 2024 3 30 1 30 0
    let autumn ← LocalDateTime.ofYmdHms? 2024 10 26 2 30 0
    let evaluate (label : LocalDateTime) (ms : Int)
        (unit : DateTimeSubdayUnit) (amount : Rat) := do
      let input ← input? label ms none (.parsed (.num 1))
        (.parsed (.num amount)) "old"
      let operation ← operation? unit (.literal 1) (.literal amount)
      let operand ← operation.evaluateOperand input |>.toOption
      let view ← operation.executeResult input ([] : List FormalCause) |>.toOption
      let epochMillis ← match operand with
        | .value instant => some instant.epochMillis
        | _ => none
      pure (epochMillis, view)
    let hours ← evaluate ordinary 777 .hours 2
    let minutes ← evaluate ordinary 777 .minutes 120
    let seconds ← evaluate ordinary 777 .seconds 7200
    let springResult ← evaluate spring 333 .hours 1
    let autumnResult ← evaluate autumn 444 .hours 1
    let applied ← hours.2.applyTo destination |>.toOption
    let appliedText ← match applied target.id with
      | .presentValue value => some value.text
      | _ => none
    pure ([hours.1, minutes.1, seconds.1, springResult.1, autumnResult.1],
      hours.2.withChanges.map (fun entry => entry.value.text),
      appliedText)) =
    some (
      [1718580600777, 1718580600777, 1718580600777,
        1711848600333, 1729992600444],
      ["17.06.2024T01:30:00"],
      "17.06.2024T01:30:00") := by
  native_decide

/- Quiet failure in either amount clears a filled target; reached inner and outer
   causes remain distinct poison outcomes and never become target-local errors. -/
example : (do
    let label ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let clean ← input? label 0 none (.parsed (.num 1))
      (.parsed (.num 1)) "filled"
    let malformed ← input? label 0 (some (.rejected .malformed))
      (.parsed (.num 1)) (.parsed (.num 1)) "filled"
    let outerRejected ← input? label 0 none (.parsed (.num 1))
      (.rejected .declaredConstraint) "filled"
    let domain ← domainAmount?
    let innerEmpty ← operation? .hours domain (.literal 1)
    let outerEmpty ← operation? .hours (.literal 1) domain
    let innerPoison ← operation? .hours (.literal 1) (.literal 1)
    let outerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model subdayAmount.id).toOption
    let outerPoison ← operation? .hours (.literal 1) outerField
    let innerView ← innerEmpty.executeResult clean
      ([] : List FormalCause) |>.toOption
    let outerView ← outerEmpty.executeResult clean
      ([] : List FormalCause) |>.toOption
    let innerOutcome ← innerPoison.evaluateOutcome malformed |>.toOption
    let outerOutcome ← outerPoison.evaluateOutcome outerRejected |>.toOption
    pure (innerView.cleared, outerView.cleared,
      innerView.noErrorOccurred && outerView.noErrorOccurred,
      innerOutcome, outerOutcome)) =
    some ([target.id], [target.id], true,
      .poison .malformed, .poison .declaredConstraint) := by
  native_decide

/- The direct DateTime source cannot also be the declaration-owned target. -/
example :
    let selfModel : FlatModel := {
      fields := [target], timeZoneId := "Europe/Berlin" }
    errorOf (elaborateDateTimeDayThenSubdayShiftComputation
      selfModel target.id (.literal 1) .hours (.literal 1) target.id) =
        some (.targetSelfReference target.id) := by
  native_decide

/- One dynamic carrier consumes each supplied world independently. All elapsed units
   preserve the inner day landing, including Berlin gap and overlap identity. -/
example : (do
    let documentLabel ← LocalDateTime.ofYmdHms? 2024 6 1 0 0 0
    let input ← input? documentLabel 0 none (.parsed (.num 1))
      (.parsed (.num 1)) "old"
    let evaluate (label : LocalDateTime) (ms : Int)
        (unit : DateTimeSubdayUnit) (amount : Rat) := do
      let instant ←
        ModelZone.ConcreteProfile.europeBerlin.resolveLocal? label
      let operation ← dynamicOperation? unit (.literal 1) (.literal amount)
      let result ← operation.evaluateOperand
        { now := { epochMillis := instant.epochMillis + ms } } input
        |>.toOption
      match result with
      | .value exact => some exact.epochMillis
      | _ => none
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 23 30 0
    let later ← LocalDateTime.ofYmdHms? 2024 6 16 23 30 0
    let spring ← LocalDateTime.ofYmdHms? 2024 3 30 1 30 0
    let autumn ← LocalDateTime.ofYmdHms? 2024 10 26 2 30 0
    let ordinaryInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? ordinary
    let operation ← dynamicOperation? .hours (.literal 1) (.literal 2)
    let view ← operation.executeResult
      { now := { epochMillis := ordinaryInstant.epochMillis + 777 } }
      input ([] : List FormalCause) |>.toOption
    let applied ← view.applyTo destination |>.toOption
    let appliedText ← match applied target.id with
      | .presentValue value => some value.text
      | _ => none
    pure ([
      ← evaluate ordinary 777 .hours 2,
      ← evaluate later 333 .hours 2,
      ← evaluate ordinary 777 .minutes 120,
      ← evaluate ordinary 777 .seconds 7200,
      ← evaluate spring 333 .hours 1,
      ← evaluate autumn 444 .hours 1],
      view.withChanges.map (fun entry => entry.value.text), appliedText)) =
    some ([
      1718580600777, 1718667000333, 1718580600777,
      1718580600777, 1711848600333, 1729992600444],
      ["17.06.2024T01:30:00"], "17.06.2024T01:30:00") := by
  native_decide

/- Dynamic quiet failure in either amount clears a filled target; the two checked
   amount positions retain their distinct formal causes. -/
example : (do
    let label ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let worldInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? label
    let world : World := { now := worldInstant }
    let clean ← input? label 0 none (.parsed (.num 1))
      (.parsed (.num 1)) "filled"
    let innerRejected ← input? label 0 none (.rejected .malformed)
      (.parsed (.num 1)) "filled"
    let outerRejected ← input? label 0 none (.parsed (.num 1))
      (.rejected .declaredConstraint) "filled"
    let domain ← domainAmount?
    let dayField ←
      (elaborateValueAsDateTimeFieldShiftAmount model dayAmount.id).toOption
    let subdayField ←
      (elaborateValueAsDateTimeFieldShiftAmount model subdayAmount.id).toOption
    let innerEmpty ← dynamicOperation? .hours domain (.literal 1)
    let outerEmpty ← dynamicOperation? .hours (.literal 1) domain
    let innerPoison ← dynamicOperation? .hours dayField (.literal 1)
    let outerPoison ← dynamicOperation? .hours (.literal 1) subdayField
    let innerView ← innerEmpty.executeResult world clean
      ([] : List FormalCause) |>.toOption
    let outerView ← outerEmpty.executeResult world clean
      ([] : List FormalCause) |>.toOption
    let innerOutcome ←
      innerPoison.evaluateOutcome world innerRejected |>.toOption
    let outerOutcome ←
      outerPoison.evaluateOutcome world outerRejected |>.toOption
    pure (innerView.cleared, outerView.cleared,
      innerView.noErrorOccurred && outerView.noErrorOccurred,
      innerOutcome, outerOutcome)) =
    some ([target.id], [target.id], true,
      .poison .malformed, .poison .declaredConstraint) := by
  native_decide

/- Reverse-order target execution preserves every inner elapsed unit and the distinct
   source-offset landings at Berlin's gap and overlap. -/
example : (do
    let evaluate (label : LocalDateTime) (ms : Int)
        (unit : DateTimeSubdayUnit) (amount : Rat) := do
      let input ← input? label ms none (.parsed (.num amount))
        (.parsed (.num 1)) "old"
      let operation ← reverseOperation? unit (.literal amount) (.literal 1)
      let operand ← operation.evaluateOperand input |>.toOption
      let view ← operation.executeResult input ([] : List FormalCause) |>.toOption
      let epoch ← match operand with
        | .value instant => some instant.epochMillis
        | _ => none
      pure (epoch, view)
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 23 30 0
    let spring ← LocalDateTime.ofYmdHms? 2024 3 30 1 30 0
    let autumn ← LocalDateTime.ofYmdHms? 2024 10 26 1 30 0
    let hours ← evaluate ordinary 777 .hours 2
    let minutes ← evaluate ordinary 777 .minutes 120
    let seconds ← evaluate ordinary 777 .seconds 7200
    let springResult ← evaluate spring 333 .hours 1
    let autumnResult ← evaluate autumn 444 .hours 1
    let applied ← hours.2.applyTo destination |>.toOption
    let appliedText ← match applied target.id with
      | .presentValue value => some value.text
      | _ => none
    pure ([hours.1, minutes.1, seconds.1, springResult.1, autumnResult.1],
      hours.2.withChanges.map (fun entry => entry.value.text), appliedText)) =
    some ([1718580600777, 1718580600777, 1718580600777,
      1711845000333, 1729989000444],
      ["17.06.2024T01:30:00"], "17.06.2024T01:30:00") := by
  native_decide

/- Reverse-order quiet failure clears a filled target; inner and outer formal causes
   stay distinct, and the direct source cannot also be the target. -/
example : (do
    let label ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let clean ← input? label 0 none (.parsed (.num 1))
      (.parsed (.num 1)) "filled"
    let innerRejected ← input? label 0 none (.rejected .malformed)
      (.parsed (.num 1)) "filled"
    let outerRejected ← input? label 0 none (.parsed (.num 1))
      (.rejected .declaredConstraint) "filled"
    let domain ← domainAmount?
    let innerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model dayAmount.id).toOption
    let outerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model subdayAmount.id).toOption
    let innerEmpty ← reverseOperation? .hours domain (.literal 1)
    let outerEmpty ← reverseOperation? .hours (.literal 1) domain
    let innerPoison ← reverseOperation? .hours innerField (.literal 1)
    let outerPoison ← reverseOperation? .hours (.literal 1) outerField
    let innerView ← innerEmpty.executeResult clean
      ([] : List FormalCause) |>.toOption
    let outerView ← outerEmpty.executeResult clean
      ([] : List FormalCause) |>.toOption
    let innerOutcome ← innerPoison.evaluateOutcome innerRejected |>.toOption
    let outerOutcome ← outerPoison.evaluateOutcome outerRejected |>.toOption
    pure (innerView.cleared, outerView.cleared,
      innerView.noErrorOccurred && outerView.noErrorOccurred,
      innerOutcome, outerOutcome)) =
    some ([target.id], [target.id], true,
      .poison .malformed, .poison .declaredConstraint) ∧
    (let selfModel : FlatModel := {
      fields := [target], timeZoneId := "Europe/Berlin" }
    errorOf (elaborateDateTimeSubdayThenDayShiftComputation
      selfModel target.id .hours (.literal 1) (.literal 1) target.id) =
        some (.targetSelfReference target.id)) := by
  native_decide

end A12Kernel.Conformance.DateTimeMixedShiftComputation
