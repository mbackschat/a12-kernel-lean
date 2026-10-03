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

A **row step** is a checked computation into a repeatable target of a kind other than Number, run once
per instantiated target row by its own carrier and read back per row as the whole-document steps
are, so a later step reads a completed row target through the cell a stored rendering of it reads as.
Its instances are the row carriers; each is one constructor, and the read set it declares is checked
against its target once, here, rather than proved per carrier.
-/

namespace A12Kernel

/-- Why a row step failed structurally. -/
inductive RowComputationStepFault where
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

/-- One checked computation into a repeatable non-Number target, run at every instantiated row. -/
structure CheckedRowComputationStep (model : FlatModel) (compilePattern : StringPatternCompiler) where
  private mk ::
  target : FieldId
  family : DocumentTargetFamily
  referencesField : FieldId → Bool
  excludesTarget : referencesField target = false
  run : World → PreparedFlatStringPatterns model compilePattern → CheckedDocument model →
    Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell))

namespace CheckedRowComputationStep

/-- A step reading `reads` for every pattern compiler, or `none` when that set reaches the target,
which the plan's order and the read overlay both exclude. The decision reads the operation alone. -/
private def checked? (target : FieldId) (family : DocumentTargetFamily) (reads : FieldId → Bool)
    (run : ∀ compilePattern, World → PreparedFlatStringPatterns model compilePattern →
      CheckedDocument model →
      Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell))) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  if h : reads target = false then
    some fun compilePattern =>
      { target, family, referencesField := reads, excludesTarget := h, run := run compilePattern }
  else none

/-- A String constant written into every row of a repeatable String target. -/
def ofRepeatableStringConstant (operation : CheckedRepeatableStringConstantComputation model) :
    CheckedRowComputationStep model compilePattern where
  target := operation.checkedTarget.targetField
  family := .string
  referencesField _ := false
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
  referencesField _ := false
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
      referencesField _ := false
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
  referencesField _ := false
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
  referencesField _ := false
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
  referencesField _ := false
  excludesTarget := rfl
  run _ _ document := do
    let outcomes ← (operation.execute document).mapError .booleanConstant
    pure (outcomes.map fun entry =>
      (entry.targetField, .boolean entry.result, DocumentComputationReadBack.boolean entry.result))

/-- The read-back of each addressed outcome, as a fixed target of the same family reads back. -/
private def readBack {Outcome : Type} (outcomes : List (CellAddr × Outcome))
    (wrap : Outcome → DocumentTargetOutcome)
    (cell : FieldId → Outcome → Except DocumentComputationStepFault CheckedCell) :
    Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell)) :=
  outcomes.mapM fun (address, outcome) => do
    pure (address, wrap outcome, ← (cell address.field outcome).mapError .readBack)

/-- A per-row `FieldValueAsString` of a Number source. -/
def ofAddressedFieldValueAsString? (operation : CheckedAddressedFieldValueAsString model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .string (· == operation.sourceDeclaration.id) fun _ _ patterns document => do
    let outcomes ← (operation.execute patterns document).mapError .fieldValueAsString
    readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .string
      fun _ => DocumentComputationReadBack.string

/-- A per-row Enumeration `FirstFilledValue`, its selected token checked as the target's stored
projection reads it. -/
def ofAddressedEnumerationFirstFilled? (operation : CheckedAddressedEnumerationFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.target.field .enumeration operation.source.referencesField fun _ _ _ document => do
    let outcomes ← (operation.execute document).mapError .enumerationFirstFilled
    readBack (outcomes.map fun entry => (entry.targetField, entry.result.asExactStringTargetOutcome))
      .enumeration fun _ outcome => pure (DocumentComputationReadBack.enumeration
        operation.target.projection outcome)

/-- A per-row String `FirstFilledValue` over its entity-list source. -/
def ofStringFirstFilled? (operation : CheckedStringFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .string operation.referencesField fun _ _ patterns document => do
    let outcomes ← (operation.execute patterns document).mapError .stringFirstFilled
    readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .string
      fun _ => DocumentComputationReadBack.string

/-- A per-row DateFragment `FirstFilledValue` over a sibling star. -/
def ofDateFragmentFirstFilled? (operation : CheckedDateFragmentFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .dateFragment operation.referencesField fun _ _ _ document => do
    let outcomes ← (operation.execute document).mapError .firstFilledSite
    readBack (outcomes.map fun entry => (entry.targetField, entry.result.asExactStringTargetOutcome))
      .dateFragment (DocumentComputationReadBack.dateFragment model)

/-- A per-row Custom `FirstFilledValue` over a sibling star, read back as a String completion is. -/
def ofCustomFirstFilled? (operation : CheckedCustomFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .string operation.referencesField fun _ _ _ document => do
    let outcomes ← (operation.execute document).mapError .firstFilledSite
    readBack (outcomes.map fun entry => (entry.targetField, entry.result.asExactStringTargetOutcome))
      .string fun _ => DocumentComputationReadBack.string

/-- A per-row Boolean `FirstFilledValue` over a sibling star. -/
def ofBooleanFirstFilled? (operation : CheckedBooleanFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .boolean operation.referencesField fun _ _ _ document => do
    let outcomes ← (operation.execute document).mapError .firstFilledSite
    readBack (outcomes.map fun entry => (entry.targetField, entry.result)) .boolean
      fun _ result => pure (DocumentComputationReadBack.boolean result)

/-- A per-row Time `FirstFilledValue` over a sibling star. -/
def ofTimeFirstFilled? (operation : CheckedTimeFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .time operation.referencesField
    fun _ _ _ document => do
      let outcomes ← (operation.execute document).mapError .firstFilledSite
      readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .time
        (DocumentComputationReadBack.time model)

/-- A per-row DateTime `FirstFilledValue` over a sibling star. -/
def ofDateTimeFirstFilled? (operation : CheckedDateTimeFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .dateTime operation.referencesField
    fun _ _ _ document => do
      let outcomes ← (operation.execute document).mapError .dateTimeFirstFilled
      readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .dateTime
        (DocumentComputationReadBack.dateTime model)

/-- A per-row full-Date `FirstFilledValue` over a sibling star. -/
def ofFullDateFirstFilled? (operation : CheckedFullDateFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .fullDate operation.referencesField
    fun _ _ _ document => do
      let outcomes ← (operation.execute document).mapError .fullDateFirstFilled
      readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .fullDate
        (DocumentComputationReadBack.fullDate model)

/-- A per-row DateRange `FirstFilledValue` over a sibling star, read back through the target's own
declared range policy. -/
def ofDateRangeFirstFilled? (operation : CheckedDateRangeFirstFilledComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.targetField .dateRange operation.referencesField
    fun _ _ _ document => do
      let outcomes ← (operation.execute document).mapError .dateRangeFirstFilled
      readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .dateRange fun target outcome => do
        let policy ← ((model.lookupUniqueId target).toOption.bind
          FlatFieldDecl.toDateRangeDeclarationPolicy?).getDM (throw .targetNotReadable)
        DocumentComputationReadBack.dateRange model policy outcome

/-- A per-row `DateFromDateTime` of a source the target row binds. -/
def ofAddressedDateFromDateTime? (operation : CheckedAddressedDateFromDateTime model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.target.checked.target.id .fullDate (· == operation.sourceBinding.source.id)
    fun _ _ _ document => do
      let outcomes ← (operation.execute document).mapError .dateFromDateTime
      readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .fullDate
        (DocumentComputationReadBack.fullDate model)

/-- A per-row `Time(...)` construction over addressed and world components. -/
def ofAddressedTimeConstruction? (operation : CheckedAddressedWorldTimeConstructionComputation model) :
    Option (∀ compilePattern, CheckedRowComputationStep model compilePattern) :=
  checked? operation.checkedTarget.targetField .time operation.referencesField fun _ world _ document => do
    let outcomes ← (operation.execute world document).mapError .timeConstruction
    readBack (outcomes.map fun entry => (entry.targetField, entry.outcome)) .time
      (DocumentComputationReadBack.time model)
end CheckedRowComputationStep

end A12Kernel
