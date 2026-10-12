import A12Kernel.Elaboration.RowComputationTable
import A12Kernel.Elaboration.RepeatableStringConstantComputation
import A12Kernel.Elaboration.RepeatableDateConstantComputation
import A12Kernel.Elaboration.RepeatableTimeConstantComputation
import A12Kernel.Elaboration.RepeatableDateTimeConstantComputation
import A12Kernel.Elaboration.BooleanConstantComputation
import A12Kernel.Elaboration.AddressedFieldValueAsString
import A12Kernel.Elaboration.StringFirstFilledComputation
import A12Kernel.Elaboration.TimeFirstFilledComputation
import A12Kernel.Elaboration.DateTimeFirstFilledComputation
import A12Kernel.Elaboration.FullDateFirstFilledComputation
import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation
import A12Kernel.Elaboration.AddressedDateFromDateTime
import A12Kernel.Elaboration.AddressedWorldTimeConstruction
import A12Kernel.Elaboration.DocumentComputationStep

/-! # Row computation steps

A **row step** is a checked non-Number computation over addressed target instances. Its carrier runs
once per instantiated row, or once at the empty address for a fixed Boolean/Confirm or temporal table. Read-back
uses the same typed cell as the stored result, so dependent steps observe the completed target.
Each row carrier supplies its operation reads, checked against its target here. A table also retains
its guard inventory: group membership may include the target, while the shared condition certificate
and producer-protection rule separately decide forbidden reads and scheduling dependencies.
-/

namespace A12Kernel

/-- Why a row step failed structurally. -/
inductive RowComputationStepFault where
  | table (cause : RowComputationTableFault)
  | readBack (cause : DocumentComputationStepFault)
  | stringConstant (cause : RepeatableStringConstantComputationFault)
  | dateConstant (cause : RepeatableDateConstantComputationFault)
  | timeConstant (cause : RepeatableTimeConstantComputationFault)
  | dateTimeConstant (cause : RepeatableDateTimeConstantComputationFault)
  /-- A DateTime constant whose label the model zone cannot resolve, which the carrier reports as a
  residual finding rather than an outcome; the lowering refuses it before any row is run. -/
  | dateTimeLabelUnresolved
  | booleanConstant (cause : RepeatableBooleanConstantComputationFault)
  | fieldValueAsString (cause : AddressedFieldValueAsStringFault)
  | stringFirstFilled (cause : StringFirstFilledComputationFault)
  | firstFilledSite (cause : FirstFilledSiteFault)
  | dateTimeFirstFilled (cause : DateTimeFirstFilledComputationFault)
  | fullDateFirstFilled (cause : FullDateFirstFilledComputationFault)
  | dateRangeFirstFilled (cause : DateRangeFirstFilledComputationFault)
  | enumerationFirstFilled (cause : AddressedEnumerationFirstFilledComputationFault)
  | dateFromDateTime (cause : AddressedDateFromDateTimeFault)
  | timeConstruction (cause : AddressedTimeConstructionFault)
  deriving Repr, DecidableEq

/-- One checked non-Number computation over its carrier-owned target instances. -/
structure CheckedRowComputationStep (model : FlatModel) (compilePattern : StringPatternCompiler) where
  private mk ::
  target : FieldId
  family : DocumentTargetFamily
  operationReferencesWith : FieldId → (CorrelatedHaving → Bool) → Bool
  excludesTarget : operationReferencesWith target (·.forbidsTarget target) = false
  protectionConditions : List (Option (CheckedComputationCondition model)) := [none]
  sourceTable? : Option (CheckedRowComputationTable model) := none
  run : World → PreparedFlatStringPatterns model compilePattern → CheckedDocument model →
    Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell))

namespace CheckedRowComputationStep

def operationReferencesField (step : CheckedRowComputationStep model compilePattern) (field : FieldId) : Bool :=
  step.operationReferencesWith field (·.referencesField field)

def referencesField (step : CheckedRowComputationStep model compilePattern) (field : FieldId) : Bool :=
  step.protectionConditions.any (fun guard => guard.any (·.referencesField field)) ||
    step.operationReferencesField field

def requiresProducer (step : CheckedRowComputationStep model compilePattern)
    (producerProtected : FieldId → ResolvedGroupReference → Bool) (field : FieldId) : Bool :=
  step.protectionConditions.any (fun guard =>
    guard.any (·.requiresProducer step.target field (producerProtected field))) ||
      step.operationReferencesWith field (fun having => having.requiresProducer step.target field (producerProtected field))

/-- Certify the operation's target-read restriction while retaining complete inventory and conditional producer queries for the scheduler (spec/09 §5). -/
private def checked? (target : FieldId) (family : DocumentTargetFamily) (reads : FieldId → (CorrelatedHaving → Bool) → Bool)
    (run : ∀ compilePattern, World → PreparedFlatStringPatterns model compilePattern →
      CheckedDocument model →
      Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell)))
    (guards : List (Option (CheckedComputationCondition model)) := [none])
    (sourceTable? : Option (CheckedRowComputationTable model) := none) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  if h : reads target (·.forbidsTarget target) = false then
    some fun compilePattern =>
      { target, family, operationReferencesWith := reads, excludesTarget := h,
        protectionConditions := guards, sourceTable?, run := run compilePattern }
  else none

/-- A table supplies its complete guard inventory to dependency analysis before execution. -/
def ofTable? (table : CheckedRowComputationTable model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? table.target table.family table.operationReferencesWith
    (fun _ world patterns document => (table.execute world patterns document).mapError .table)
    table.protectionConditions (some table)

/-- Consolidation reuses the retained table so a selected empty/poisoned operation cannot fall
through to another declaration merely because its public outcome has no value (spec/09 §2). -/
def appendSameTarget? (left right : CheckedRowComputationStep model compilePattern) :
    Option (CheckedRowComputationStep model compilePattern) := do
  let table ← (← left.sourceTable?).appendSameTarget? (← right.sourceTable?)
  let step ← ofTable? table
  pure (step compilePattern)

/-- A String constant written into every row of a repeatable String target. -/
def ofRepeatableStringConstant (operation : CheckedRepeatableStringConstantComputation model) :
    CheckedRowComputationStep model compilePattern where
  target := operation.checkedTarget.targetField
  family := .string
  operationReferencesWith _ _ := false
  excludesTarget := rfl
  run _ patterns document := do
    let outcomes ← (operation.execute patterns document).mapError .stringConstant
    outcomes.mapM fun entry => do
      let cell ← (DocumentComputationReadBack.string entry.outcome).mapError .readBack
      pure (entry.targetField, .string entry.outcome, cell)

/-- A Date constant written into every row of a repeatable Date target. -/
def ofRepeatableDateConstant (operation : CheckedRepeatableDateConstantComputation model) :
    CheckedRowComputationStep model compilePattern where
  target := operation.checkedTarget.targetField
  family := .fullDate
  operationReferencesWith _ _ := false
  excludesTarget := rfl
  run _ _ document := do
    let outcomes ← (operation.execute document).mapError .dateConstant
    outcomes.mapM fun entry => do
      let cell ← (DocumentComputationReadBack.dateConstant operation.dateTarget entry.outcome).mapError .readBack
      pure (entry.targetField, .fullDate entry.outcome, cell)

/-- Date literals share target rendering with fixed assignments and the established row-capacity
walk with the other constants; source year presence is retained by the checked operation. -/
def ofDateLiteral? (operation : CheckedDateLiteralComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  if operation.target.repeatableScope.isEmpty then none else
    some fun _ => {
      target := operation.target.id
      family := .fullDate
      operationReferencesWith _ _ := false
      excludesTarget := rfl
      run _ _ document := do
        let scope := operation.target.repeatableScope
        let atRow := fun outcome environment => do
          let path ← (environment.pathForScope scope).mapError
            (RowComputationStepFault.dateConstant ∘ RepeatableDateConstantComputationFault.targetEnvironment)
          let cell ← (DocumentComputationReadBack.dateConstant operation.dateTarget outcome).mapError .readBack
          pure ({ field := operation.target.id, path }, DocumentTargetOutcome.fullDate outcome, cell)
        document.computationRowOutcomes scope
          (RowComputationStepFault.dateConstant ∘ RepeatableDateConstantComputationFault.targetRows)
          (atRow .noValue) (atRow operation.outcome) }

/-- A Time constant written into every row of a repeatable Time target. -/
def ofRepeatableTimeConstant (operation : CheckedRepeatableTimeConstantComputation model) :
    CheckedRowComputationStep model compilePattern where
  target := operation.checkedTarget.targetField
  family := .time
  operationReferencesWith _ _ := false
  excludesTarget := rfl
  run _ _ document := do
    let outcomes ← (operation.execute document).mapError .timeConstant
    outcomes.mapM fun entry => do
      let cell ← (DocumentComputationReadBack.time model entry.targetField.field entry.outcome).mapError
        .readBack
      pure (entry.targetField, .time entry.outcome, cell)

/-- A DateTime constant written into every row of a repeatable DateTime target. -/
def ofRepeatableDateTimeConstant (operation : CheckedRepeatableDateTimeConstantComputation model) :
    CheckedRowComputationStep model compilePattern where
  target := operation.checkedTarget.targetField
  family := .dateTime
  operationReferencesWith _ _ := false
  excludesTarget := rfl
  run _ _ document := do
    let result ← (operation.execute document).mapError .dateTimeConstant
    if !result.formalErrorsInOperands.isEmpty then throw .dateTimeLabelUnresolved
    result.outcomes.mapM fun entry => do
      let cell ← (DocumentComputationReadBack.dateTime model entry.targetField.field entry.outcome).mapError
        .readBack
      pure (entry.targetField, .dateTime entry.outcome, cell)

/-- A Boolean or Confirm constant written into every row of a repeatable target of that kind. -/
def ofRepeatableBooleanConstant (operation : CheckedRepeatableBooleanConstantComputation model) :
    CheckedRowComputationStep model compilePattern where
  target := operation.checkedTarget.targetField
  family := .boolean
  operationReferencesWith _ _ := false
  excludesTarget := rfl
  run _ _ document := do
    let outcomes ← (operation.execute document).mapError .booleanConstant
    pure (outcomes.map fun entry =>
      (entry.targetField, .boolean entry.result, DocumentComputationReadBack.booleanConstant operation.operation.operation entry.result))

/-- The read-back of each addressed outcome, as a fixed target of the same family reads back. -/
private def readBack {Outcome : Type} (outcomes : List (CellAddr × Outcome))
    (wrap : Outcome → DocumentTargetOutcome)
    (cell : FieldId → Outcome → Except DocumentComputationStepFault CheckedCell) :
    Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell)) :=
  outcomes.mapM fun (address, outcome) => do
    pure (address, wrap outcome, ← (cell address.field outcome).mapError .readBack)

private def isFilterValueFailure : RowComputationStepFault → Bool
  | .stringFirstFilled (.source error)
  | .enumerationFirstFilled (.source error)
  | .firstFilledSite (.source error)
  | .dateTimeFirstFilled (.site (.source error))
  | .fullDateFirstFilled (.site (.source error))
  | .dateRangeFirstFilled (.site (.source error)) => error.isFilterValueFailure
  | _ => false

/-- A reached filter exception belongs to this target instance, like a failed computation guard
(spec/09). Keep the typed source error until the instance handler can retain its address. -/
private def firstFilledRows (target : FlatFieldDecl) (family : DocumentTargetFamily)
    (document : CheckedDocument model)
    (rowError : ActualRowEnvironmentError → RowComputationStepFault)
    (environmentError : EnvBindingError → RowComputationStepFault)
    (evaluate : CellAddr → Env → Except RowComputationStepFault (DocumentTargetOutcome × CheckedCell)) :
    Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell)) :=
  let atRow (clear : Bool) (environment : Env) := do
    let path ← (environment.pathForScope target.repeatableScope).mapError environmentError
    let address := { field := target.id, path }
    if clear then return (address, family.noValue, DocumentComputationReadBack.empty)
    match evaluate address environment with
    | .ok (outcome, cell) => pure (address, outcome, cell)
    | .error error =>
        if isFilterValueFailure error then
          pure (address, .valueError family, DocumentComputationReadBack.poison)
        else throw error
  document.computationTargetOutcomes target.repeatableScope rowError (atRow true) (atRow false)

/-- A per-row `FieldValueAsString` of a Number source. -/
def ofAddressedFieldValueAsString? (operation : CheckedAddressedFieldValueAsString model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .string (fun field _ => field == operation.sourceDeclaration.id) fun _ _ patterns document => do
    let outcomes ← (operation.execute patterns document).mapError .fieldValueAsString
    readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .string
      fun _ => DocumentComputationReadBack.string

private def firstFilledAlternativeFault : FirstFilledAlternativeFault → RowComputationStepFault
  | .string cause => .stringFirstFilled cause
  | .fixedEnumeration cause => .enumerationFirstFilled (.source cause)
  | .enumeration cause => .enumerationFirstFilled cause
  | .site cause => .firstFilledSite cause
  | .dateTime cause => .dateTimeFirstFilled cause
  | .fullDate cause => .fullDateFirstFilled cause
  | .dateRange cause => .dateRangeFirstFilled cause
  | .readBack cause => .readBack cause

private def firstFilledStep? (operation : CheckedFirstFilledAlternative model)
    (rowError : ActualRowEnvironmentError → RowComputationStepFault)
    (environmentError : EnvBindingError → RowComputationStepFault) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.target.id operation.family operation.referencesWith fun _ world patterns document =>
    firstFilledRows operation.target operation.family document rowError environmentError fun _ environment =>
      (operation.evaluateAt world patterns document environment).mapError firstFilledAlternativeFault

/-- A per-row Enumeration `FirstFilledValue`, its selected token checked as the target's stored
projection reads it. -/
def ofAddressedEnumerationFirstFilled? (operation : CheckedAddressedEnumerationFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  firstFilledStep? (.addressedEnumeration operation)
    (.enumerationFirstFilled ∘ .targetRows) (.enumerationFirstFilled ∘ .targetEnvironment)

/-- A per-row String `FirstFilledValue` over its entity-list source. -/
def ofStringFirstFilled? (operation : CheckedStringFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  firstFilledStep? (.string operation)
    (.stringFirstFilled ∘ .targetRows) (.stringFirstFilled ∘ .targetEnvironment)

/-- A per-row DateFragment `FirstFilledValue` over its checked source. -/
def ofDateFragmentFirstFilled? (operation : CheckedDateFragmentFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .dateFragment operation.referencesWith fun _ world _ document =>
    firstFilledRows operation.target .dateFragment document
      (.firstFilledSite ∘ .targetRows) (.firstFilledSite ∘ .targetEnvironment) fun target environment => do
        let entry ← (operation.evaluateAt (world := some world) document document.read target environment).mapError .firstFilledSite
        let outcome := entry.result.asExactStringTargetOutcome
        pure (.dateFragment outcome, ← (DocumentComputationReadBack.dateFragment model operation.targetField outcome).mapError .readBack)

/-- A per-row Custom `FirstFilledValue` over its checked source, read back as a String completion is. -/
def ofCustomFirstFilled? (operation : CheckedCustomFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .string operation.referencesWith fun _ world _ document =>
    firstFilledRows operation.target .string document
      (.firstFilledSite ∘ .targetRows) (.firstFilledSite ∘ .targetEnvironment) fun target environment => do
        let entry ← (operation.evaluateAt (world := some world) document document.read target environment).mapError .firstFilledSite
        let outcome := entry.outcome
        pure (.string outcome, ← (DocumentComputationReadBack.string outcome).mapError .readBack)

/-- A per-row Boolean `FirstFilledValue` over its checked source. -/
def ofBooleanFirstFilled? (operation : CheckedBooleanFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  firstFilledStep? (.boolean operation)
    (.firstFilledSite ∘ .targetRows) (.firstFilledSite ∘ .targetEnvironment)

/-- A per-row Time `FirstFilledValue` over its checked source. -/
def ofTimeFirstFilled? (operation : CheckedTimeFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  firstFilledStep? (.time operation)
    (.firstFilledSite ∘ .targetRows) (.firstFilledSite ∘ .targetEnvironment)

/-- A per-row DateTime `FirstFilledValue` over its checked source. -/
def ofDateTimeFirstFilled? (operation : CheckedDateTimeFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  firstFilledStep? (.dateTime operation)
    (.dateTimeFirstFilled ∘ .site ∘ .targetRows) (.dateTimeFirstFilled ∘ .site ∘ .targetEnvironment)

/-- A per-row full-Date `FirstFilledValue` over its checked source. -/
def ofFullDateFirstFilled? (operation : CheckedFullDateFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  firstFilledStep? (.fullDate operation)
    (.fullDateFirstFilled ∘ .site ∘ .targetRows) (.fullDateFirstFilled ∘ .site ∘ .targetEnvironment)

/-- A per-row DateRange `FirstFilledValue` over its checked source, read back through the target's own
declared range policy. -/
def ofDateRangeFirstFilled? (operation : CheckedDateRangeFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  firstFilledStep? (.dateRange operation)
    (.dateRangeFirstFilled ∘ .site ∘ .targetRows) (.dateRangeFirstFilled ∘ .site ∘ .targetEnvironment)

/-- A per-row `DateFromDateTime` of a source the target row binds. -/
def ofAddressedDateFromDateTime? (operation : CheckedAddressedDateFromDateTime model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.target.checked.target.id .fullDate (fun field _ => field == operation.sourceBinding.source.id)
    fun _ _ _ document => do
      let outcomes ← (operation.execute document).mapError .dateFromDateTime
      readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .fullDate
        (DocumentComputationReadBack.fullDate model)

/-- A per-row `Time(...)` construction over addressed and world components. -/
def ofAddressedTimeConstruction? (operation : CheckedAddressedWorldTimeConstructionComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.checkedTarget.targetField .time (fun field _ => operation.referencesField field) fun _ world _ document => do
    let outcomes ← (operation.execute world document).mapError .timeConstruction
    readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .time
      (DocumentComputationReadBack.time model)
end CheckedRowComputationStep

end A12Kernel
