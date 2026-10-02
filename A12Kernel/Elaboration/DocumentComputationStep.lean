import A12Kernel.Elaboration.BooleanFirstFilledComputation
import A12Kernel.Elaboration.CustomFirstFilledComputation
import A12Kernel.Elaboration.DateRangeConstructionComputation
import A12Kernel.Elaboration.DateFragmentFirstFilledComputation
import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Elaboration.DateTimeFirstFilledComputation
import A12Kernel.Elaboration.DateTimeDayShiftComputation
import A12Kernel.Elaboration.DateTimeInput
import A12Kernel.Elaboration.DateTimeSubdayShiftComputation
import A12Kernel.Elaboration.DateFromDateTime
import A12Kernel.Elaboration.DateTimeMixedShiftComputation
import A12Kernel.Elaboration.StringFirstFilledComputation
import A12Kernel.Elaboration.TimeFromDateTimeComputation
import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.EnumerationFirstFilledComputation
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.FullDateComputation
import A12Kernel.Elaboration.FullDateFirstFilledComputation
import A12Kernel.Elaboration.OmittingDateInput
import A12Kernel.Elaboration.TimeComputation
import A12Kernel.Elaboration.TimeFirstFilledComputation

/-! # Whole-document computation steps

A computation whose evaluator reads the whole document joins a scalar plan as one step. The step carries
its target, the fields it reads, a proof that it does not read its own target, and an evaluator returning
the target's outcome together with the cell a later computation reads for it. Day, sub-day and mixed
DateTime shifts, a full-Date computation, `TimeFromDateTime` and `DateFromDateTime`, a Time construction,
an Enumeration copy, a DateRange construction and the fixed-target `FirstFilledValue` over a Boolean,
String, Custom, DateFragment, Time, DateTime, full Date, DateRange or Enumeration are its instances; each is one
constructor here, and the plan's laws are stated once over the step rather than once per family. A
String target is checked against its prepared pattern, which the plan hands every step as the lookup
`StringTargetMatchers`.

The read-back cell is the rule every instance shares. A later computation reads a completed target as the
document would read its stored rendering, a cleared one as empty, and an errored or poisoned one as
computed-dependency poison, which is the projection String and Number targets already make. The rendering
read is what the Kernel shows on Berlin's repeated hour, where a dependent reads a computed DateTime at the
offset its text denotes rather than at the instant computed
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-datetime-join)); a pre-1900
Date the target retains as errored reaches its readers as poison under both presence tests
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-document-step-join)), and so does an
inverted DateRange the target retains as errored
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-date-range-join)). A
`FirstFilledValue` reading a cleared upstream target falls through to its next source, and one reading a
poisoned upstream ends its scan, on every kind measured at a join
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-first-filled-join)).

A completed Time is read back through `CheckedTimeInputField.classifyStoredForModel`, which anchors the
clock on one fixed day because a `Value` must carry an instant; that classifier names the readers
audited for never observing it. -/

namespace A12Kernel

/-- A completed whole-document target with its family retained. -/
inductive DocumentTargetOutcome where
  | dateTime (outcome : DateTimeTargetOutcome)
  | fullDate (outcome : FullDateTargetOutcome)
  | time (outcome : TimeTargetOutcome)
  | enumeration (outcome : StringTargetOutcome)
  | dateRange (outcome : DateRangeTargetOutcome)
  | boolean (outcome : BooleanComputationOutcome)
  | dateFragment (outcome : StringTargetOutcome)
  | string (outcome : StringTargetOutcome)
  deriving Repr, DecidableEq

/-- The rendering a completed target stores, which a reader pairs with its read-back cell; a cleared,
errored or poisoned target stores none. -/
def DocumentTargetOutcome.storedText? : DocumentTargetOutcome → Option String
  | .dateTime (.accepted stored) => some stored.text
  | .fullDate (.accepted stored) => some stored.text
  | .time (.accepted stored) => some stored.text
  | .enumeration (.accepted stored) => some stored.text
  | .dateRange (.accepted stored) => some stored.text
  | .boolean (.value value) => some (toString value)
  | .dateFragment (.accepted stored) => some stored.text
  | .string (.accepted stored) => some stored.text
  | .dateTime _ | .fullDate _ | .time _ | .enumeration _ | .dateRange _ | .boolean _
  | .dateFragment _ | .string _ => none

/-- The target family of a whole-document step: the family of the outcome it computes, and the outcome it
reports when a guard keeps it from running. It is not the target's declared kind, which a temporal
target admitted by its format rather than its kind may not share: a DATE-declared clock-format target
is a Time-family step. -/
inductive DocumentTargetFamily where
  | dateTime
  | fullDate
  | time
  | enumeration
  | dateRange
  | boolean
  | dateFragment
  | string
  deriving Repr, DecidableEq

namespace DocumentTargetFamily

def kind : DocumentTargetFamily → SurfaceScalarKind
  | .dateTime => .temporal .dateTime
  | .fullDate => .temporal .date
  | .time => .temporal .time
  | .enumeration => .enumeration
  | .dateRange => .dateRange
  | .boolean => .boolean
  | .dateFragment => .temporal .date
  | .string => .string

/-- The family's cleared outcome, for a step whose guard does not hold. -/
def noValue : DocumentTargetFamily → DocumentTargetOutcome
  | .dateTime => .dateTime .noValue
  | .fullDate => .fullDate .noValue
  | .time => .time .noValue
  | .enumeration => .enumeration .noValue
  | .dateRange => .dateRange .noValue
  | .boolean => .boolean .noValue
  | .dateFragment => .dateFragment .noValue
  | .string => .string .noValue

/-- The family's poisoned outcome, for a step whose guard reads poison. -/
def poison (cause : FormalCause) : DocumentTargetFamily → DocumentTargetOutcome
  | .dateTime => .dateTime (.poison cause)
  | .fullDate => .fullDate (.poison cause)
  | .time => .time (.poison cause)
  | .enumeration => .enumeration (.poison cause)
  | .dateRange => .dateRange (.poison cause)
  | .boolean => .boolean (.poison cause)
  | .dateFragment => .dateFragment (.poison cause)
  | .string => .string (.poison cause)

end DocumentTargetFamily

/-- A whole-document step's structural failure, or the model context its completed target cannot be read
back in. `targetNotReadable` fails closed where the checked target does not certify as an input field of
its family, and the two read faults carry the classifier's own context error. -/
inductive DocumentComputationStepFault where
  | dateTimeDayShift (cause : DateTimeDayShiftComputationFault)
  | dateTimeSubdayShift (cause : DateTimeSubdayShiftComputationFault)
  | fullDate (cause : FullDateComputationFault)
  | timeConstruction (cause : TimeComponentsFault)
  | dateRangeConstruction (cause : DateRangeConstructionComputationFault)
  | firstFilledSource (cause : CheckedStarDocumentError)
  | dateTimeFirstFilled (cause : DateTimeFirstFilledComputationFault)
  | fullDateFirstFilled (cause : FullDateFirstFilledComputationFault)
  | dateRangeFirstFilled (cause : DateRangeFirstFilledComputationFault)
  | enumerationFirstFilled (cause : CheckedAddressingError)
  | stringFirstFilled (cause : StringFirstFilledComputationFault)
  | dateFragmentFirstFilled (cause : DateFragmentFirstFilledComputationFault)
  | timeFromDateTime (cause : ValueAsDateTimeExtractionFault)
  | dateFromDateTime (cause : DateFromDateTimeComputationFault)
  | dateTimeDayThenSubdayShift (cause : DateTimeMixedShiftComputationFault)
  | dateTimeSubdayThenDayShift (cause : DateTimeReverseMixedShiftComputationFault)
  | dateTimeRead (cause : DateTimeInputError)
  | fullDateRead (cause : FullDateInputError)
  | timeRead (cause : TimeInputError)
  | stringRead (cause : StringDependencyFault)
  | dateRangeRead (cause : DateRangeInputError)
  | targetNotReadable
  deriving Repr, DecidableEq

namespace DocumentComputationReadBack

/-- A cleared target, read as the absent cell a pending one also reads as. -/
def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }

/-- An errored or poisoned target, read as the computed-dependency poison every family projects to. -/
def poison : CheckedCell := { rawPresent := true, parsed := none, findings := [.computedDependency] }

/-- Read one stored rendering back as the target's own input classifier reads a document cell. -/
private def storedText {Field Error : Type} (model : FlatModel) (target : FieldId)
    (certify : FlatFieldDecl → Option Field)
    (classify : Field → String → String → Except Error RawCell)
    (readFault : Error → DocumentComputationStepFault) (text : String) :
    Except DocumentComputationStepFault CheckedCell := do
  let declaration ← (model.lookupUniqueId target).toOption.getDM (throw .targetNotReadable)
  let field ← (certify declaration).getDM (throw .targetNotReadable)
  let raw ← (classify field model.timeZoneId text).mapError readFault
  pure (checkAdmittedRawCell raw)

/-- A completed DateTime target, read back from its rendering in the model zone. -/
def dateTime (model : FlatModel) (target : FieldId) :
    DateTimeTargetOutcome → Except DocumentComputationStepFault CheckedCell
  | .noValue => pure empty
  | .poison _ | .errored _ _ => pure poison
  | .accepted stored =>
      storedText model target (certifyDateTimeInputField · |>.toOption)
        CheckedDateTimeInputField.classifyStoredForModel .dateTimeRead stored.text

/-- A completed full-Date target, read back from its rendering in the model zone. -/
def fullDate (model : FlatModel) (target : FieldId) :
    FullDateTargetOutcome → Except DocumentComputationStepFault CheckedCell
  | .noValue => pure empty
  | .poison _ | .errored _ _ => pure poison
  | .accepted stored =>
      storedText model target (certifyFullDateInputField · |>.toOption)
        CheckedFullDateInputField.classifyStoredForModel .fullDateRead stored.text

/-- A completed Time target, read back from its rendering with the clock anchored in the model zone. -/
def time (model : FlatModel) (target : FieldId) :
    TimeTargetOutcome → Except DocumentComputationStepFault CheckedCell
  | .noValue => pure empty
  | .poison _ => pure poison
  | .accepted stored =>
      storedText model target (certifyTimeInputField · |>.toOption)
        CheckedTimeInputField.classifyStoredForModel .timeRead stored.text

/-- A completed Enumeration target, read as its declaration's stored projection reads the token. -/
def enumeration (projection : CheckedEnumerationProjection) :
    StringTargetOutcome → CheckedCell
  | .noValue => empty
  | .poison _ | .errored _ _ => poison
  | .accepted stored => projection.declaration.checkRaw (.parsed (.enum stored.text))

/-- A completed DateRange target, read back from its rendering as the document classifies a stored range. -/
def dateRange (model : FlatModel) (policy : DateRangeDeclarationPolicy) :
    DateRangeTargetOutcome → Except DocumentComputationStepFault CheckedCell
  | .noValue => pure empty
  | .poison _ | .errored _ _ => pure poison
  | .accepted stored => do
      let raw ← (classifyStoredDateRangeForModel model.timeZoneId model.baseYear policy stored.text).mapError
        .dateRangeRead
      pure (checkAdmittedRawCell raw)

/-- A completed Boolean target, read back from its rendering as the document classifies a stored
Boolean. -/
def boolean : BooleanComputationOutcome → CheckedCell
  | .noValue => empty
  | .poison _ => poison
  | .value value => checkAdmittedRawCell (classifyStoredBooleanText (toString value))

/-- A stored component-omitting Date rendering, read as the earliest date it denotes, the rule
`dateFragment` states. -/
def omittingDateText (model : FlatModel) (target : FieldId) (text : String) :
    Except DocumentComputationStepFault CheckedCell := do
  let declaration ← (model.lookupUniqueId target).toOption.getDM (throw .targetNotReadable)
  let field ← (certifyOmittingDateInputField declaration).toOption.getDM
    (throw .targetNotReadable)
  let profile ← (ModelZone.ConcreteProfile.ofId? model.timeZoneId).getDM
    (throw .targetNotReadable)
  let earliest : Option CivilDate :=
    match field.classifyStoredForModel model.baseYear text with
    | .admitted value => value.earliestCivil? model.baseYearOrDefault
    | .presentEmpty | .rejected _ => none
  let date ← earliest.getDM (throw .targetNotReadable)
  let value ← (profile.resolveStoredDate? date).getDM (throw .targetNotReadable)
  pure (checkAdmittedRawCell (.parsed (.temporal (.date value))))

/-- A completed DateFragment target, read as the earliest date it denotes, which is how the Kernel
completes a fragment at runtime: missing month and day become `01` and a missing year the Base Year,
measured by comparison against a full Date (the DateFragment runtime-completion supplement in
[`kf93`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf93)), and a computed `yyyy-MM` target compares
equal to its month's first day
([checkpoint](../../docs/sources/temporal-and-message-probes.md#src-partial-date-readers)). A yearless
fragment in a model declaring no Base Year is computed by the Kernel and completes to
`FlatModel.baseYearOrDefault`, whose leap-ness is measured and whose exact year has no witness. -/
def dateFragment (model : FlatModel) (target : FieldId) :
    StringTargetOutcome → Except DocumentComputationStepFault CheckedCell
  | .noValue => pure empty
  | .poison _ | .errored _ _ => pure poison
  | .accepted stored => omittingDateText model target stored.text

/-- A completed String target, read back as the cell a String table's completion places, so a reader
cannot tell a String `FirstFilledValue` from any other computed String. -/
def string (outcome : StringTargetOutcome) : Except DocumentComputationStepFault CheckedCell :=
  (StringDependencyCell.ofOutcome outcome).map (·.checked) |>.mapError .stringRead

end DocumentComputationReadBack

/-- The prepared pattern each String target is checked against, as
`PreparedFlatStringPatterns.targetMatcher?` recovers it: `none` for a target the preparation does not
own, `some none` for one declaring no pattern. -/
abbrev StringTargetMatchers := FieldId → Option (Option (String → Bool))

/-- One checked whole-document computation as a plan step. Only this module's instances construct one,
so every step's cell is the read-back of its own outcome. -/
structure CheckedDocumentComputationStep (model : FlatModel) where
  private mk ::
  target : FieldId
  family : DocumentTargetFamily
  referencesField : FieldId → Bool
  excludesTarget : referencesField target = false
  run : World → StringTargetMatchers → CheckedDocument model →
    Except DocumentComputationStepFault (DocumentTargetOutcome × CheckedCell)

namespace CheckedDocumentComputationStep

def targetKind (step : CheckedDocumentComputationStep model) : SurfaceScalarKind :=
  step.family.kind

/-- A field-backed DateTime day shift. -/
def ofDateTimeDayShift (operation : CheckedDateTimeDayShiftComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .dateTime
  referencesField field :=
    operation.shift.source.id == field || operation.shift.amount.referencesField field
  excludesTarget := by
    simp [operation.sourceDistinct, operation.amountExcludesTarget]
  run _ _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .dateTimeDayShift
    let cell ← DocumentComputationReadBack.dateTime model operation.target.checked.target.id outcome
    pure (.dateTime outcome, cell)

/-- A field-backed DateTime sub-day shift. -/
def ofDateTimeSubdayShift (operation : CheckedDateTimeSubdayShiftComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .dateTime
  referencesField field :=
    operation.shift.source.id == field || operation.shift.amount.referencesField field
  excludesTarget := by
    simp [operation.sourceDistinct, operation.amountExcludesTarget]
  run _ _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .dateTimeSubdayShift
    let cell ← DocumentComputationReadBack.dateTime model operation.target.checked.target.id outcome
    pure (.dateTime outcome, cell)

/-- A full-Date computation over a field, `Today`, or the Base Year. -/
def ofFullDate (operation : CheckedFullDateComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .fullDate
  referencesField field :=
    match operation.operand with
    | .fieldValue source => source.id == field
    | _ => false
  excludesTarget := by
    have admitted := operation.operandAdmitted
    revert admitted
    cases operation.operand <;>
      simp [FlatModel.admitsFullDateComputationOperand]
  run world _ document := do
    let outcome ← (operation.evaluateOutcome world document).mapError .fullDate
    let cell ← DocumentComputationReadBack.fullDate model operation.target.checked.target.id outcome
    pure (.fullDate outcome, cell)

/-- A Time construction from document-only components. -/
def ofTimeConstruction (operation : CheckedTimeConstructionComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .time
  referencesField := operation.components.referencesField
  excludesTarget := operation.targetNotReferenced
  run _ _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .timeConstruction
    let cell ← DocumentComputationReadBack.time model operation.target.checked.target.id outcome
    pure (.time outcome, cell)

/-- An Enumeration copy of a field or a literal, read from the document's checked cells. -/
def ofEnumeration (operation : CheckedEnumerationComputationOperation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.field
  family := .enumeration
  referencesField := operation.source.referencesField
  excludesTarget := operation.targetNotReferenced
  run _ _ document :=
    let outcome := (operation.source.evaluate document.flatContext).asExactStringTargetOutcome
    pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target.projection outcome)

/-- A DateRange construction over two Date fields. -/
def ofDateRangeConstruction (operation : CheckedDateRangeConstructionComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.source.id
  family := .dateRange
  referencesField field :=
    operation.construction.start.checked.target.id == field ||
      operation.construction.finish.checked.target.id == field
  excludesTarget := by
    simp [operation.startNotTarget, operation.finishNotTarget]
  run _ _ document := do
    let result ← (operation.execute document).mapError .dateRangeConstruction
    let cell ← DocumentComputationReadBack.dateRange model operation.target.policy result.outcome
    pure (.dateRange result.outcome, cell)

/-- A fixed-target Boolean `FirstFilledValue`. -/
def ofBooleanFirstFilled (operation : CheckedBooleanFirstFilledComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.id
  family := .boolean
  referencesField := operation.source.referencesField
  excludesTarget := operation.excludesTarget
  run _ _ document := do
    let outcome ← (operation.execute document).mapError .firstFilledSource
    pure (.boolean outcome, DocumentComputationReadBack.boolean outcome)

/-- A fixed-target Time `FirstFilledValue`. -/
def ofTimeFirstFilled (operation : CheckedTimeFirstFilledComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.shape.target.id
  family := .time
  referencesField := operation.shape.source.referencesField
  excludesTarget := operation.shape.excludesTarget
  run _ _ document := do
    let outcome ← (operation.execute document).mapError .firstFilledSource
    let cell ← DocumentComputationReadBack.time model operation.shape.target.id outcome
    pure (.time outcome, cell)

/-- A fixed-target DateTime `FirstFilledValue`. -/
def ofDateTimeFirstFilled (operation : CheckedDateTimeFirstFilledComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.shape.target.id
  family := .dateTime
  referencesField := operation.shape.source.referencesField
  excludesTarget := operation.shape.excludesTarget
  run _ _ document := do
    let outcome ← (operation.execute document).mapError .dateTimeFirstFilled
    let cell ← DocumentComputationReadBack.dateTime model operation.shape.target.id outcome
    pure (.dateTime outcome, cell)

/-- A fixed-target full-Date `FirstFilledValue`. -/
def ofFullDateFirstFilled (operation : CheckedFullDateFirstFilledComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.shape.targetField
  family := .fullDate
  referencesField := operation.shape.referencesField
  excludesTarget := operation.shape.excludesTarget
  run _ _ document := do
    let outcome ← (operation.execute document).mapError .fullDateFirstFilled
    let cell ← DocumentComputationReadBack.fullDate model operation.shape.targetField outcome
    pure (.fullDate outcome, cell)

/-- A fixed-target DateFragment `FirstFilledValue` at its single instance. -/
def ofDateFragmentFirstFilled (operation : CheckedDateFragmentFirstFilledComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.targetField
  family := .dateFragment
  referencesField := operation.referencesField
  excludesTarget := operation.excludesTarget
  run _ _ document := do
    let entry ← (operation.evaluateAt document document.read
      { field := operation.targetField, path := [] } []).mapError .dateFragmentFirstFilled
    let outcome := entry.result.asExactStringTargetOutcome
    let cell ← DocumentComputationReadBack.dateFragment model operation.targetField outcome
    pure (.dateFragment outcome, cell)

/-- A fixed-target DateRange `FirstFilledValue` over a direct field list. -/
def ofDateRangeFirstFilledDirect (operation : CheckedDateRangeFirstFilledDirectComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.source.id
  family := .dateRange
  referencesField field := operation.sources.any (·.direct.source.id == field)
  excludesTarget := by
    simp only [List.any_eq_false, beq_iff_eq]
    exact fun source _ => source.excludesTarget
  run _ _ document := do
    let outcome ← (operation.execute document).mapError .dateRangeFirstFilled
    let cell ← DocumentComputationReadBack.dateRange model operation.target.policy outcome
    pure (.dateRange outcome, cell)

/-- A fixed-target Enumeration `FirstFilledValue`, read from the document's checked cells. -/
def ofEnumerationFirstFilled (operation : CheckedEnumerationFirstFilledComputationOperation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.field
  family := .enumeration
  referencesField := operation.source.referencesField
  excludesTarget := operation.targetNotReferenced
  run _ _ document := do
    let selected ← (operation.source.evaluateCheckedDocument document []).mapError
      .enumerationFirstFilled
    let outcome := selected.asComputationResult.asExactStringTargetOutcome
    pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target.projection outcome)

/-- A fixed-target String `FirstFilledValue` at its single instance, checked against its target's
prepared pattern. -/
def ofStringFirstFilled (operation : CheckedStringFirstFilledComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.targetField
  family := .string
  referencesField := operation.referencesField
  excludesTarget := operation.excludesTarget
  run _ matchers document := do
    let matcher ← (matchers operation.targetField).getDM
      (throw (.stringFirstFilled (.targetPatternUnavailable operation.targetField)))
    let entry ← (operation.evaluateAt matcher document document.read []).mapError .stringFirstFilled
    let cell ← DocumentComputationReadBack.string entry.outcome
    pure (.string entry.outcome, cell)

/-- A fixed-target Custom `FirstFilledValue`, whose selected token its matching Custom declaration
accepts unchecked, read back as a String completion is. -/
def ofCustomFirstFilled (operation : CheckedCustomFirstFilledComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.id
  family := .string
  referencesField := operation.source.referencesField
  excludesTarget := operation.excludesTarget
  run _ _ document := do
    let outcome := (← (operation.execute document).mapError .firstFilledSource).asExactStringTargetOutcome
    let cell ← DocumentComputationReadBack.string outcome
    pure (.string outcome, cell)

/-- `TimeFromDateTime` over a field. -/
def ofTimeFromDateTime (operation : CheckedTimeFromDateTimeComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .time
  referencesField field := operation.source.source.id == field
  excludesTarget := by simp [operation.sourceDistinct]
  run _ _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .timeFromDateTime
    let cell ← DocumentComputationReadBack.time model operation.target.checked.target.id outcome
    pure (.time outcome, cell)

/-- `DateFromDateTime` over a field. -/
def ofDateFromDateTime (operation : CheckedDateFromDateTimeComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .fullDate
  referencesField field := operation.source.source.id == field
  excludesTarget := by simp [operation.sourceDistinct]
  run _ _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .dateFromDateTime
    let cell ← DocumentComputationReadBack.fullDate model operation.target.checked.target.id outcome
    pure (.fullDate outcome, cell)

/-- A field-backed calendar-day shift followed by a sub-day shift. -/
def ofDateTimeDayThenSubdayShift (operation : CheckedDateTimeDayThenSubdayShiftComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .dateTime
  referencesField field := operation.shift.source.id == field ||
    operation.shift.amount.referencesField field || operation.nextAmount.referencesField field
  excludesTarget := by
    have amounts := operation.amountsExcludeTarget
    simp only [Bool.or_eq_false_iff] at amounts
    simp [operation.sourceDistinct, amounts.1, amounts.2]
  run _ _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .dateTimeDayThenSubdayShift
    let cell ← DocumentComputationReadBack.dateTime model operation.target.checked.target.id outcome
    pure (.dateTime outcome, cell)

/-- A field-backed sub-day shift followed by a calendar-day shift. -/
def ofDateTimeSubdayThenDayShift (operation : CheckedDateTimeSubdayThenDayShiftComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  family := .dateTime
  referencesField field := operation.shift.source.id == field ||
    operation.shift.amount.referencesField field || operation.nextAmount.referencesField field
  excludesTarget := by
    have amounts := operation.amountsExcludeTarget
    simp only [Bool.or_eq_false_iff] at amounts
    simp [operation.sourceDistinct, amounts.1, amounts.2]
  run _ _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .dateTimeSubdayThenDayShift
    let cell ← DocumentComputationReadBack.dateTime model operation.target.checked.target.id outcome
    pure (.dateTime outcome, cell)

/-- A step under a presence guard read through the same overlaid document the step reads: a guard that
holds runs the step, one that does not clears the target, read as empty, and one that reads poison
poisons it, read as poison, both without running the step. The Kernel guards a DateTime shift, a
full-Date copy, a DateRange construction and an Enumeration copy that way, a guard on a computed Number
reading its completion
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-guarded-document-steps)). -/
def guarded (guard : ComputationCondition) (step : CheckedDocumentComputationStep model)
    (guardExcludesTarget : guard.referencesField step.target = false) :
    CheckedDocumentComputationStep model where
  target := step.target
  family := step.family
  referencesField field := guard.referencesField field || step.referencesField field
  excludesTarget := by simp [guardExcludesTarget, step.excludesTarget]
  run world matchers document :=
    match guard.eval (document.scalarComputationContext world) with
    | .holds => step.run world matchers document
    | .notTrue => pure (step.family.noValue, DocumentComputationReadBack.empty)
    | .poison cause => pure (step.family.poison cause, DocumentComputationReadBack.poison)

/-- Guard a step, refusing a guard that names a field the model does not own, as a Number table's
certifier does, or that reads the step's own target, which the Kernel refuses as a read of the target
anywhere in a computation. -/
def guard? (guard : ComputationCondition) (step : CheckedDocumentComputationStep model) :
    Option (CheckedDocumentComputationStep model) :=
  if !guard.wellFormedBool model then none
  else if h : guard.referencesField step.target = false then some (step.guarded guard h) else none

end CheckedDocumentComputationStep

end A12Kernel
