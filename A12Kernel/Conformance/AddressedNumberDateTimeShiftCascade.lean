import A12Kernel.Elaboration.AddressedNumberDateTimeShiftCascade

/-! # Repeatable Number-to-DateTime shift cascade locks -/

namespace A12Kernel.Conformance.AddressedNumberDateTimeShiftCascade

open A12Kernel

private def numberField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def dateTimeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
}

private def baseHours :=
  numberField 1 "BaseHours" ["Order", "Projects"] [10]
private def computedHours :=
  numberField 2 "ComputedHours" ["Order", "Projects"] [10]
private def sourceStamp :=
  dateTimeField 3 "SourceStamp" ["Order", "Projects", "Tasks"] [10, 20]
private def targetStamp :=
  dateTimeField 4 "TargetStamp" ["Order", "Projects", "Tasks"] [10, 20]

private def model : FlatModel := {
  fields := [baseHours, computedHours, sourceStamp, targetStamp]
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 3,
      indexField := some baseHours.id },
    { level := 20, path := ["Order", "Projects", "Tasks"], repeatability := some 3 }
  ]
  timeZoneId := "UTC"
}

private def absolute (groups : GroupPath) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def producer? :=
  (checkAddressedNumberField model ["Order", "Projects"] computedHours.id
    (absolute ["Order", "Projects"] baseHours.name)).toOption

private def consumerWithAmount? (amountField : FlatFieldDecl) :=
  (checkAddressedDateTimeSubdayShiftComputation model
    ["Order", "Projects", "Tasks"] targetStamp.id
    (absolute ["Order", "Projects", "Tasks"] sourceStamp.name) .hours
    (.atom (.field (absolute amountField.groupPath amountField.name)))).toOption

private def consumer? := consumerWithAmount? computedHours

private def consumerWithWiderAmount? :=
  (checkAddressedDateTimeSubdayShiftComputation model
    ["Order", "Projects", "Tasks"] targetStamp.id
    (absolute ["Order", "Projects", "Tasks"] sourceStamp.name) .hours
    (.binary .add
      (.atom (.field (absolute computedHours.groupPath computedHours.name)))
      (.atom (.field (absolute baseHours.groupPath baseHours.name))))).toOption

private def plan? := do
  let producer ← producer?
  let consumer ← consumer?
  (certifyAddressedNumberDateTimeShiftCascade producer consumer).toOption

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def numberCell (field : FieldId) (path : List Nat) (value : Rat) :=
  cell field path (toString value) (.parsed (.num value))

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def dateTimeCell (field : FieldId) (path : List Nat)
    (text : String) (hour : Nat) (valid : hour < 24) :=
  cell field path text (.parsed (.temporal (.dateTime
    { epochMillis := hour * 3600000 }
    { year := 1970, month := 1, day := 1 }
    (clock hour 0 0 ⟨valid, by decide, by decide⟩) .storedGregorian)))

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows := [
  row 10 [1], row 10 [2],
  row 20 [1, 1], row 20 [1, 2], row 20 [2, 1], row 20 [2, 2]]

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows, cells }).toOption

private def input? := document? [
  numberCell baseHours.id [1] 2,
  cell baseHours.id [2] "bad" (.rejected .malformed),
  numberCell computedHours.id [1] 99,
  numberCell computedHours.id [2] 8,
  dateTimeCell sourceStamp.id [1, 1] "1970-01-01T05:00:00" 5 (by decide),
  cell sourceStamp.id [2, 1] "bad" (.rejected .dateFormat),
  dateTimeCell targetStamp.id [1, 1] "1970-01-01T07:00:00" 7 (by decide),
  dateTimeCell targetStamp.id [2, 2] "1970-01-01T09:00:00" 9 (by decide)]

private def duplicateProducerIndexInput? := document? [
  numberCell baseHours.id [1] 1,
  numberCell baseHours.id [2] 1,
  numberCell computedHours.id [1] 9,
  numberCell computedHours.id [2] 9,
  cell sourceStamp.id [1, 1] "bad" (.rejected .dateFormat),
  dateTimeCell sourceStamp.id [2, 1] "1970-01-01T05:00:00" 5 (by decide),
  dateTimeCell targetStamp.id [1, 1] "1970-01-01T06:00:00" 6 (by decide),
  dateTimeCell targetStamp.id [2, 1] "1970-01-01T06:00:00" 6 (by decide)]

private inductive ProducerSummary where
  | empty
  | value (text : String)
  | poisoned
  deriving Repr, DecidableEq

private def summarizeProducer
    (entry : SourcedNumericTargetOutcome CellAddr) :
    CellAddr × ProducerSummary :=
  (entry.targetField, match entry.outcome with
    | .noValue => .empty
    | .accepted value => .value value.render
    | .rejected _ _ | .invalidNoValue _ | .inheritedPoison _ => .poisoned)

private inductive DateTimeSummary where
  | empty
  | value (text : String)
  | poisoned (cause : FormalCause)
  deriving Repr, DecidableEq

private def summarizeConsumer
    (entry : AddressedDateTimeSubdayShiftComputationOutcome) :
    CellAddr × DateTimeSummary :=
  (entry.targetField, match entry.outcome with
    | .noValue => .empty
    | .accepted value => .value value.text
    | .poison cause => .poisoned cause)

private def duplicateProducerPreparedConsumer? : Option
    (List (CellAddr × ProducerSummary) ×
      List (CellAddr × DateTimeSummary)) := do
  let plan ← plan?
  let input ← duplicateProducerIndexInput?
  let inputPlan ← plan.formalInputPlan.toOption
  let prepared ← inputPlan.prepare input |>.toOption
  let producer ← plan.producer.executeWithRead input
    prepared.preliminary.readComputation |>.toOption
  let consumer ← plan.consumer.executeWithAmountRead input
    (plan.amountRead input producer) |>.toOption
  pure (producer.map summarizeProducer, consumer.map summarizeConsumer)

/- The selected producer source poisons before the transient overlay is built; the DateTime phase still reads its immutable source first at each row. -/
example : duplicateProducerPreparedConsumer? = some ([
    (address computedHours.id [1], ProducerSummary.poisoned),
    (address computedHours.id [2], ProducerSummary.poisoned)
  ], [
    (address targetStamp.id [1, 1], DateTimeSummary.poisoned .dateFormat),
    (address targetStamp.id [1, 2],
      DateTimeSummary.poisoned .computedDependency),
    (address targetStamp.id [2, 1],
      DateTimeSummary.poisoned .computedDependency),
    (address targetStamp.id [2, 2],
      DateTimeSummary.poisoned .computedDependency)
  ]) := by
  native_decide

private def duplicateProducerFormalInputSummary? : Option
    (List ComputationFormalInputFinding × List CellAddr × List CellAddr) := do
  let plan ← plan?
  let input ← duplicateProducerIndexInput?
  let view ← plan.executeResultWithFormalInputs input |>.toOption
  pure (view.formalErrorsInOperands, view.phases.number.cleared,
    view.phases.dateTime.dateTime.cleared)

/- Whole-call preparation retains cached source poison before both generated duplicate-index findings, then clears both source-filled family targets. -/
example : duplicateProducerFormalInputSummary? = some ([
    { address := address sourceStamp.id [1, 1], cause := .dateFormat },
    { address := address baseHours.id [1], cause := .duplicateIndex },
    { address := address baseHours.id [2], cause := .duplicateIndex }
  ], [
    address computedHours.id [1], address computedHours.id [2]
  ], [
    address targetStamp.id [1, 1], address targetStamp.id [2, 1]
  ]) := by
  native_decide

/- The completed outer Number phase hides stale targets and supplies exact amounts to inner DateTime rows. A formal DateTime source hides the poisoned Number dependency, while an empty source reaches it. -/
example :
    (do
      let plan ← plan?
      let input ← input?
      let outcomes ← plan.execute input |>.toOption
      pure (outcomes.producer.map summarizeProducer,
        outcomes.consumer.map summarizeConsumer)) = some ([
          (address computedHours.id [1], ProducerSummary.value "2"),
          (address computedHours.id [2], ProducerSummary.poisoned)
        ], [
          (address targetStamp.id [1, 1],
            DateTimeSummary.value "1970-01-01T07:00:00"),
          (address targetStamp.id [1, 2], DateTimeSummary.empty),
          (address targetStamp.id [2, 1],
            DateTimeSummary.poisoned .dateFormat),
          (address targetStamp.id [2, 2],
            DateTimeSummary.poisoned .computedDependency)
        ]) := by
  native_decide

/- The scheduling edge is independent of expression width: an already-checked direct-Number expression remains certified when it contains the producer beside another admitted amount source. -/
example :
    (do
      let producer ← producer?
      let consumer ← consumerWithWiderAmount?
      let plan ← certifyAddressedNumberDateTimeShiftCascade producer consumer
        |>.toOption
      pure plan.consumer.fieldDependencies) =
      some [sourceStamp.id, computedHours.id, baseHours.id] := by
  native_decide

/- A missing completion at a plan target is clean empty even when the immutable source still contains a stale value. -/
example :
    (do
      let plan ← plan?
      let input ← input?
      let available ← plan.amountRead input [] [(10, 1)] computedHours.id
        |>.toOption
      let cell ← available
      pure (observeCell .computation cell)) = some CellObservation.empty := by
  native_decide

/- A completed clean no-value outcome projects to the same empty amount observation without relying on the missing-completion branch. This locks the dependency domain, not reachability from the direct producer. -/
example :
    (do
      let plan ← plan?
      let input ← input?
      let completion : SourcedNumericTargetOutcome CellAddr := {
        targetField := address computedHours.id [1]
        outcome := .noValue
        source := .presentValue (.decimal ⟨99, 0⟩)
      }
      let available ← plan.amountRead input [completion]
        [(10, 1)] computedHours.id |>.toOption
      let cell ← available
      pure (observeCell .computation cell)) = some CellObservation.empty := by
  native_decide

private def storedDateTime (text : String) (nonempty : text ≠ "" := by decide) :
    StoredDateTime := { text, nonempty }

private structure ResultApplicationSummary where
  numberValues : List (CellAddr × String)
  numberChanges : List CellAddr
  numberCleared : List CellAddr
  dateTimeValues : List (CellAddr × String)
  dateTimeChanges : List CellAddr
  dateTimeCleared : List CellAddr
  numberApplied1 : NumericTargetState
  numberApplied2 : NumericTargetState
  dateTimeApplied11 : DateTimeTargetState
  dateTimeApplied12 : DateTimeTargetState
  dateTimeApplied21 : DateTimeTargetState
  dateTimeApplied22 : DateTimeTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let plan ← plan?
  let input ← input?
  let destination ← document? [
    numberCell computedHours.id [1] 77,
    dateTimeCell targetStamp.id [1, 1] "1970-01-01T20:00:00" 20 (by decide),
    dateTimeCell targetStamp.id [1, 2] "1970-01-01T04:00:00" 4 (by decide),
    dateTimeCell targetStamp.id [2, 1] "1970-01-01T06:00:00" 6 (by decide)]
  let view ← plan.executeResult input (fun _ => ())
    ([] : List (ComputationFormalMessage Unit))
    ([] : List FormalCause) |>.toOption
  let numberApplied ← view.number.applyToChecked destination |>.toOption
  let dateTimeApplied ← view.dateTime.applyToChecked destination |>.toOption
  pure {
    numberValues := view.number.withoutErrors.map fun item =>
      (item.targetField, item.value.render)
    numberChanges := view.number.withChanges.map (·.targetField)
    numberCleared := view.number.cleared
    dateTimeValues := view.dateTime.dateTime.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    dateTimeChanges := view.dateTime.dateTime.withChanges.map (·.targetField)
    dateTimeCleared := view.dateTime.dateTime.cleared
    numberApplied1 := numberApplied.stateAt (address computedHours.id [1])
    numberApplied2 := numberApplied.stateAt (address computedHours.id [2])
    dateTimeApplied11 := dateTimeApplied (address targetStamp.id [1, 1])
    dateTimeApplied12 := dateTimeApplied (address targetStamp.id [1, 2])
    dateTimeApplied21 := dateTimeApplied (address targetStamp.id [2, 1])
    dateTimeApplied22 := dateTimeApplied (address targetStamp.id [2, 2])
  }

/- Public result classification remains source-relative in each family, and the independent action sets do not reclassify against a conflicting destination. -/
example : resultApplicationSummary? = some {
    numberValues := [(address computedHours.id [1], "2")]
    numberChanges := [address computedHours.id [1]]
    numberCleared := [address computedHours.id [2]]
    dateTimeValues := [
      (address targetStamp.id [1, 1], "1970-01-01T07:00:00")]
    dateTimeChanges := []
    dateTimeCleared := [address targetStamp.id [2, 2]]
    numberApplied1 := .presentValue (.decimal ⟨2, 0⟩)
    numberApplied2 := .presentEmpty
    dateTimeApplied11 := .presentValue
      (storedDateTime "1970-01-01T20:00:00")
    dateTimeApplied12 := .presentValue
      (storedDateTime "1970-01-01T04:00:00")
    dateTimeApplied21 := .presentValue
      (storedDateTime "1970-01-01T06:00:00")
    dateTimeApplied22 := .presentEmpty
  } := by
  native_decide

/- One cross-family call retains exact direct Number and DateTime source findings globally. For this value-producing Number fixture neither typed phase adds an independently owned residual. -/
example :
    (do
      let plan ← plan?
      let input ← input?
      let view ← plan.executeResultWithFormalInputs input |>.toOption
      let findings := view.formalErrorsInOperands
      pure (findings.length,
        [findings.contains {
            address := address baseHours.id [2]
            cause := .malformed
          },
          findings.contains {
            address := address sourceStamp.id [2, 1]
            cause := .dateFormat
          },
          findings.any fun finding =>
            finding.address.field == computedHours.id,
          findings.any fun finding =>
            finding.address.field == targetStamp.id],
        view.phases.number.formalErrorsInOperands,
        view.phases.dateTime.dateTime.formalErrorsInOperands)) =
      some (2, [true, true, false, false], [], []) := by
  native_decide

/- Analyze retains both typed phases, the outer-to-inner edge, and authored source-first DateTime dependencies. -/
example : plan?.map CheckedAddressedNumberDateTimeShiftCascade.analyze = some {
    targetFields := [computedHours.id, targetStamp.id]
    fieldDependencies := [
      (computedHours.id, [baseHours.id]),
      (targetStamp.id, [sourceStamp.id, computedHours.id])]
  } := by
  native_decide

/- A different Number amount is not certified as the producer-consumer scheduling edge. -/
example :
    (do
      let producer ← producer?
      let consumer ← consumerWithAmount? baseHours
      pure (match certifyAddressedNumberDateTimeShiftCascade producer consumer with
        | .error .consumerAmountDoesNotReadProducer => true
        | .ok _ => false)) = some true := by
  native_decide

end A12Kernel.Conformance.AddressedNumberDateTimeShiftCascade
