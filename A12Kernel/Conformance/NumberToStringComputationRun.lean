import A12Kernel.Elaboration.NumberToStringComputationRun

/-! # Number-to-String computation-run locks

The matrix separates a completed Number's stored text from stale document text, clean clearing from poison, reached poison from an unread dependency, and the computed overlay from an ordinary Number formal read.
-/

namespace A12Kernel.Conformance.NumberToStringComputationRun

open A12Kernel

private def sourceId : FieldId := 0
private def producerId : FieldId := 1
private def consumerId : FieldId := 2
private def gateId : FieldId := 3

private def numberInfo : NumField := { scale := 2, signed := true }

private def numberDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .number numberInfo }
  numericTargetConstraints := { minFractionalDigits := 2 }

private def stringDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .string }

private def model : FlatModel :=
  { fields := [
      numberDeclaration sourceId "Source",
      numberDeclaration producerId "Producer",
      stringDeclaration consumerId "Consumer",
      stringDeclaration gateId "Gate"] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def literal (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def divisionByZero : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide (literal 1) (literal 0)

private def numberTable? (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : ComputationCondition := .fieldNotFilled gateId) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateNumericTargetComputationOperation
    model ["Form"] producerId expression true).toOption
  (certifyNumericComputationTable [{ precondition := guard, operation }]).toOption

private def stringOperation? (expression : StringExpr SurfaceFieldPath) :
    Option (CheckedStringComputationOperation model) :=
  (elaborateStringComputationOperation
    model ["Form"] consumerId expression).toOption

private def stringTable? (rows : List
    (ComputationCondition × StringExpr SurfaceFieldPath)) :
    Option (CheckedStringComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← stringOperation? expression
    pure ({ precondition := guard, operation } :
      ComputationAlternative (CheckedStringComputationOperation model))
  (certifyStringComputationTable alternatives).toOption

private def producerValue :=
  (numberTable? (literal 7)).get (by native_decide)

private def producerEmpty :=
  (numberTable? (literal 7) (.fieldFilled gateId)).get (by native_decide)

private def producerInvalid :=
  (numberTable? divisionByZero).get (by native_decide)

private def computedAndSource :=
  (stringTable? [(.fieldNotFilled gateId,
    .concat
      (.fieldValueAsString (bare "Producer"))
      (.concat (.literal "/") (.fieldValueAsString (bare "Source"))))]).get
    (by native_decide)

private def computedOnly :=
  (stringTable? [(.fieldNotFilled gateId,
    .fieldValueAsString (bare "Producer"))]).get (by native_decide)

private def unreadComputed :=
  (stringTable? [
    (.fieldNotFilled gateId, .literal "SAFE"),
    (.fieldNotFilled gateId, .fieldValueAsString (bare "Producer"))]).get
      (by native_decide)

private def decimalCell (field : FieldId) (stored : String)
    (unscaled : Int) (rawAmount : Rat) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored
    raw := .parsed (.num rawAmount)
    numericDecimal := some { unscaled, scale := 2 } }

private def stringCell (field : FieldId) (stored : String) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored
    raw := .parsed (.str stored) }

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption

private inductive StringOutcomeSummary
  | noValue
  | accepted (text : String)
  | errored (text : String) (cause : StringTargetError)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

private def StringOutcomeSummary.ofOutcome :
    StringTargetOutcome → StringOutcomeSummary
  | .noValue => .noValue
  | .accepted stored => .accepted stored.text
  | .errored attempted cause => .errored attempted.text cause
  | .poison cause => .poison cause

private structure OutcomeSummary where
  number : FieldId × NumericTargetOutcome
  string : FieldId × StringOutcomeSummary
  deriving Repr, DecidableEq

private def outcomes? (number : CheckedNumericComputationTable model)
    (string : CheckedStringComputationTable model)
    (cells : List ClassifiedCellInput := []) :
    Option OutcomeSummary := do
  let run ← (certifyNumberToStringComputationRun number string).toOption
  let input ← checkedDocument cells
  let outcomes ← (run.execute world prepared.patterns input).toOption
  pure {
    number := outcomes.number
    string := (outcomes.string.1,
      StringOutcomeSummary.ofOutcome outcomes.string.2)
  }

private structure ChangedSummary where
  numberWithoutErrors : List (FieldId × StoredNumber)
  numberWithChanges : List (FieldId × StoredNumber)
  stringWithoutErrors : List (FieldId × String)
  stringWithChanges : List (FieldId × String)
  deriving Repr, DecidableEq

private def changedSummary? : Option ChangedSummary := do
  let run ←
    (certifyNumberToStringComputationRun producerValue computedAndSource).toOption
  let input ← checkedDocument [
    decimalCell sourceId "3.50" 350 (7 / 2),
    decimalCell producerId "9.00" 900 9,
    stringCell consumerId "OLD"]
  let view ← (run.executeResult world prepared.patterns input
    (fun _ => ()) [] ([] : List Unit)).toOption
  pure {
    numberWithoutErrors :=
      view.number.withoutErrors.map fun item => (item.targetField, item.value)
    numberWithChanges :=
      view.number.withChanges.map fun item => (item.targetField, item.value)
    stringWithoutErrors :=
      view.string.withoutErrors.map fun item => (item.targetField, item.value.text)
    stringWithChanges :=
      view.string.withChanges.map fun item => (item.targetField, item.value.text)
  }

private def clearedSummary? :
    Option (List FieldId × List FieldId) := do
  let run ←
    (certifyNumberToStringComputationRun producerEmpty computedOnly).toOption
  let input ← checkedDocument [
    decimalCell producerId "9.00" 900 9,
    stringCell consumerId "OLD"]
  let view ← (run.executeResult world prepared.patterns input
    (fun _ => ()) [] ([] : List Unit)).toOption
  pure (view.number.cleared, view.string.cleared)

/- A completed Number exposes its canonical target text while an ordinary Number still follows the immutable document's formal-read route. Both family views retain the accepted values and classify their source-relative changes independently. -/
example :
    outcomes? producerValue computedAndSource [
      decimalCell sourceId "3.50" 350 (7 / 2),
      decimalCell producerId "9.00" 900 9,
      stringCell consumerId "OLD"] =
      some {
        number := (producerId, .accepted { unscaled := 700, scale := 2 })
        string := (consumerId, .accepted "7.00/3.50") } := by
  native_decide

example :
    changedSummary? =
    some {
      numberWithoutErrors :=
        [(producerId, { unscaled := 700, scale := 2 })]
      numberWithChanges :=
        [(producerId, { unscaled := 700, scale := 2 })]
      stringWithoutErrors := [(consumerId, "7.00/3.50")]
      stringWithChanges := [(consumerId, "7.00/3.50")]
    } := by
  native_decide

/- Clean no-selection hides stale Number source state and clears both source-filled targets. -/
example :
    outcomes? producerEmpty computedOnly [
      decimalCell producerId "9.00" 900 9,
      stringCell consumerId "OLD"] =
      some {
        number := (producerId, .noValue)
        string := (consumerId, .noValue) } ∧
    clearedSummary? = some ([producerId], [consumerId]) := by
  native_decide

/- A reached invalid Number poisons the String target, but a selected earlier row prevents the same syntactic dependency from being read. -/
example :
    outcomes? producerInvalid computedOnly =
      some {
        number := (producerId, .invalidNoValue .calculationValue)
        string := (consumerId, .poison .computedDependency) } ∧
    outcomes? producerInvalid unreadComputed =
      some {
        number := (producerId, .invalidNoValue .calculationValue)
        string := (consumerId, .accepted "SAFE") } := by
  native_decide

/- The bounded plan rejects a reverse read and a guard-only Number reference that never reaches `FieldValueAsString`. -/
example :
    (certifyNumberToStringComputationRun
      ((numberTable? (literal 7) (.fieldFilled consumerId)).get
        (by native_decide))
      computedOnly).toOption = none ∧
    (certifyNumberToStringComputationRun producerValue
      ((stringTable? [(.fieldFilled producerId, .literal "SAFE")]).get
        (by native_decide))).toOption = none := by
  native_decide

end A12Kernel.Conformance.NumberToStringComputationRun
