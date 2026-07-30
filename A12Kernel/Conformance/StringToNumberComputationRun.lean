import A12Kernel.Elaboration.StringToNumberComputationRun

/-! # String-to-Number computation-run locks

The matrix separates a completed String's checked stored text from stale document text, clean String no-value from numeric zero, reached poison from an unread dependency, and the computed overlay from an ordinary String `FieldValueAsNumber` read.
-/

namespace A12Kernel.Conformance.StringToNumberComputationRun

open A12Kernel

private def sourceId : FieldId := 0
private def producerId : FieldId := 1
private def consumerId : FieldId := 2
private def gateId : FieldId := 3

private def numericStringDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }
  stringPatternSource := some "[0-9]+"

private def numberDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .number { scale := 2, signed := true } }
  numericTargetConstraints := { minFractionalDigits := 2 }

private def plainStringDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .string }

private def model : FlatModel :=
  { fields := [
      numericStringDeclaration sourceId "Source",
      numericStringDeclaration producerId "Producer",
      numberDeclaration consumerId "Consumer",
      plainStringDeclaration gateId "Gate"] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def stringOperation? (expression : StringExpr SurfaceFieldPath) :
    Option (CheckedStringComputationOperation model) :=
  (elaborateStringComputationOperation
    model ["Form"] producerId expression).toOption

private def stringTable? (rows : List
    (ComputationCondition × StringExpr SurfaceFieldPath)) :
    Option (CheckedStringComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← stringOperation? expression
    pure ({ precondition := guard, operation } :
      ComputationAlternative (CheckedStringComputationOperation model))
  (certifyStringComputationTable alternatives).toOption

private def numberOperation?
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedNumericTargetComputationOperation model) :=
  (elaborateNumericTargetComputationOperation
    model ["Form"] consumerId expression true).toOption

private def numberTable? (rows : List
    (ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom)) :
    Option (CheckedNumericComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← numberOperation? expression
    pure ({ precondition := guard, operation } :
      ComputationAlternative
        (CheckedNumericTargetComputationOperation model))
  (certifyNumericComputationTable alternatives).toOption

private def literalNumber (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def asNumber (field : String) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber (.direct (bare field)))

private def producerValue :=
  (stringTable? [(.fieldNotFilled gateId, .literal "7")]).get
    (by native_decide)

private def producerEmpty :=
  (stringTable? [(.fieldFilled gateId, .literal "7")]).get
    (by native_decide)

private def producerInvalid :=
  (stringTable? [(.fieldNotFilled gateId, .literal "LONG")]).get
    (by native_decide)

private def computedAndSource :=
  (numberTable? [(.fieldNotFilled gateId,
    .binary .add (asNumber "Producer") (asNumber "Source"))]).get
      (by native_decide)

private def computedOnly :=
  (numberTable? [(.fieldNotFilled gateId, asNumber "Producer")]).get
    (by native_decide)

private def unreadComputed :=
  (numberTable? [
    (.fieldNotFilled gateId, literalNumber 3),
    (.fieldNotFilled gateId, asNumber "Producer")]).get
      (by native_decide)

private def stringCell (field : FieldId) (stored : String) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored
    raw := .parsed (.str stored) }

private def decimalCell (field : FieldId) (stored : String)
    (unscaled : Int) (rawAmount : Rat) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored
    raw := .parsed (.num rawAmount)
    numericDecimal := some { unscaled, scale := 2 } }

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
  string : FieldId × StringOutcomeSummary
  number : FieldId × NumericTargetOutcome
  deriving Repr, DecidableEq

private def outcomes? (string : CheckedStringComputationTable model)
    (number : CheckedNumericComputationTable model)
    (cells : List ClassifiedCellInput := []) :
    Option OutcomeSummary := do
  let run ← (certifyStringToNumberComputationRun string number).toOption
  let input ← checkedDocument cells
  let outcomes ← (run.execute world prepared.patterns input).toOption
  pure {
    string := (outcomes.string.1,
      StringOutcomeSummary.ofOutcome outcomes.string.2)
    number := outcomes.number
  }

private structure ChangedSummary where
  stringWithoutErrors : List (FieldId × String)
  stringWithChanges : List (FieldId × String)
  numberWithoutErrors : List (FieldId × StoredNumber)
  numberWithChanges : List (FieldId × StoredNumber)
  deriving Repr, DecidableEq

private def changedSummary? : Option ChangedSummary := do
  let run ←
    (certifyStringToNumberComputationRun
      producerValue computedAndSource).toOption
  let input ← checkedDocument [
    stringCell sourceId "2",
    stringCell producerId "9",
    decimalCell consumerId "90.00" 9000 90]
  let view ← (run.executeResult world prepared.patterns input
    (fun _ => ()) [] ([] : List Unit)).toOption
  pure {
    stringWithoutErrors :=
      view.string.withoutErrors.map fun item =>
        (item.targetField, item.value.text)
    stringWithChanges :=
      view.string.withChanges.map fun item =>
        (item.targetField, item.value.text)
    numberWithoutErrors :=
      view.number.withoutErrors.map fun item =>
        (item.targetField, item.value)
    numberWithChanges :=
      view.number.withChanges.map fun item =>
        (item.targetField, item.value)
  }

private structure NoValueSummary where
  stringCleared : List FieldId
  numberCleared : List FieldId
  numberValues : List (FieldId × StoredNumber)
  deriving Repr, DecidableEq

private def noValueSummary? : Option NoValueSummary := do
  let run ←
    (certifyStringToNumberComputationRun
      producerEmpty computedOnly).toOption
  let input ← checkedDocument [
    stringCell producerId "9",
    decimalCell consumerId "90.00" 9000 90]
  let view ← (run.executeResult world prepared.patterns input
    (fun _ => ()) [] ([] : List Unit)).toOption
  pure {
    stringCleared := view.string.cleared
    numberCleared := view.number.cleared
    numberValues := view.number.withoutErrors.map fun item =>
      (item.targetField, item.value)
  }

/- A completed String shadows stale source text for `FieldValueAsNumber`, while the ordinary String source keeps the immutable document route. Both family results retain their values and source-relative changes independently. -/
example :
    outcomes? producerValue computedAndSource [
      stringCell sourceId "2",
      stringCell producerId "9",
      decimalCell consumerId "90.00" 9000 90] =
      some {
        string := (producerId, .accepted "7")
        number := (consumerId,
          .accepted { unscaled := 900, scale := 2 }) } ∧
    changedSummary? =
      some {
        stringWithoutErrors := [(producerId, "7")]
        stringWithChanges := [(producerId, "7")]
        numberWithoutErrors :=
          [(consumerId, { unscaled := 900, scale := 2 })]
        numberWithChanges :=
          [(consumerId, { unscaled := 900, scale := 2 })]
      } := by
  native_decide

/- Clean String no-selection hides stale producer state but becomes numeric zero at the reached conversion. The producer clears while the Number consumer stores zero rather than clearing. -/
example :
    outcomes? producerEmpty computedOnly [
      stringCell producerId "9",
      decimalCell consumerId "90.00" 9000 90] =
      some {
        string := (producerId, .noValue)
        number := (consumerId,
          .accepted { unscaled := 0, scale := 2 }) } ∧
    noValueSummary? =
      some {
        stringCleared := [producerId]
        numberCleared := []
        numberValues :=
          [(consumerId, { unscaled := 0, scale := 2 })]
      } := by
  native_decide

/- A reached invalid String poisons the Number target, but an earlier selected Number row prevents the same syntactic dependency from being read. -/
example :
    outcomes? producerInvalid computedOnly =
      some {
        string := (producerId, .errored "LONG" .pattern)
        number := (consumerId,
          .inheritedPoison .computedDependency) } ∧
    outcomes? producerInvalid unreadComputed =
      some {
        string := (producerId, .errored "LONG" .pattern)
        number := (consumerId,
          .accepted { unscaled := 300, scale := 2 }) } := by
  native_decide

/- The bounded plan rejects a reverse read and a guard-only producer reference that never reaches `FieldValueAsNumber`. -/
example :
    (certifyStringToNumberComputationRun
      ((stringTable? [(.fieldFilled consumerId, .literal "7")]).get
        (by native_decide))
      computedOnly).toOption = none ∧
    (certifyStringToNumberComputationRun producerValue
      ((numberTable? [(.fieldFilled producerId, literalNumber 3)]).get
        (by native_decide))).toOption = none := by
  native_decide

end A12Kernel.Conformance.StringToNumberComputationRun
