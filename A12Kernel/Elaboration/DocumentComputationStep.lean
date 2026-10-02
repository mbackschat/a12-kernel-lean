import A12Kernel.Elaboration.DateTimeDayShiftComputation
import A12Kernel.Elaboration.DateTimeInput
import A12Kernel.Elaboration.DateTimeSubdayShiftComputation
import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.FullDateComputation

/-! # Whole-document computation steps

A computation whose evaluator reads the whole document joins a scalar plan as one step. The step carries
its target, the fields it reads, a proof that it does not read its own target, and an evaluator returning
the target's outcome together with the cell a later computation reads for it. Day and sub-day DateTime
shifts, a full-Date computation and an Enumeration copy are its instances; each is one constructor here,
and the plan's laws are stated once over the step rather than once per family.

The read-back cell is the rule every instance shares. A later computation reads a completed target as the
document would read its stored rendering, a cleared one as empty, and an errored or poisoned one as
computed-dependency poison, which is the projection String and Number targets already make. The rendering
read is what the Kernel shows on Berlin's repeated hour, where a dependent reads a computed DateTime at the
offset its text denotes rather than at the instant computed
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-datetime-join)); a pre-1900
Date the target retains as errored reaches its readers as poison under both presence tests
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-document-step-join)).

A Time construction is not an instance yet. A clock declaration has no `Value` derivable from its stored
text (`CheckedDocument.temporallyCoherent`), so a read-back has to choose the instant a Time value
carries; no reader observes it, since date-free comparisons compare clocks. -/

namespace A12Kernel

/-- A completed whole-document target with its family retained. -/
inductive DocumentTargetOutcome where
  | dateTime (outcome : DateTimeTargetOutcome)
  | fullDate (outcome : FullDateTargetOutcome)
  | enumeration (outcome : StringTargetOutcome)
  deriving Repr, DecidableEq

/-- A whole-document step's structural failure, or the model context its completed target cannot be read
back in. `targetNotReadable` fails closed where the checked target does not certify as an input field of
its family, and the two read faults carry the classifier's own context error. -/
inductive DocumentComputationStepFault where
  | dateTimeDayShift (cause : DateTimeDayShiftComputationFault)
  | dateTimeSubdayShift (cause : DateTimeSubdayShiftComputationFault)
  | fullDate (cause : FullDateComputationFault)
  | dateTimeRead (cause : DateTimeInputError)
  | fullDateRead (cause : FullDateInputError)
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

/-- A completed Enumeration target, read as its declaration reads the stored token. -/
def enumeration (target : CheckedEnumerationComputationTarget model) :
    StringTargetOutcome → CheckedCell
  | .noValue => empty
  | .poison _ | .errored _ _ => poison
  | .accepted stored => target.projection.declaration.checkRaw (.parsed (.enum stored.text))

end DocumentComputationReadBack

/-- One checked whole-document computation as a plan step. Only this module's instances construct one,
so every step's cell is the read-back of its own outcome. -/
structure CheckedDocumentComputationStep (model : FlatModel) where
  private mk ::
  target : FieldId
  targetKind : SurfaceScalarKind
  referencesField : FieldId → Bool
  excludesTarget : referencesField target = false
  run : World → CheckedDocument model →
    Except DocumentComputationStepFault (DocumentTargetOutcome × CheckedCell)

namespace CheckedDocumentComputationStep

/-- A field-backed DateTime day shift. -/
def ofDateTimeDayShift (operation : CheckedDateTimeDayShiftComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  targetKind := .temporal .dateTime
  referencesField field :=
    operation.shift.source.id == field || operation.shift.amount.referencesField field
  excludesTarget := by
    simp [operation.sourceDistinct, operation.amountExcludesTarget]
  run _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .dateTimeDayShift
    let cell ← DocumentComputationReadBack.dateTime model operation.target.checked.target.id outcome
    pure (.dateTime outcome, cell)

/-- A field-backed DateTime sub-day shift. -/
def ofDateTimeSubdayShift (operation : CheckedDateTimeSubdayShiftComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  targetKind := .temporal .dateTime
  referencesField field :=
    operation.shift.source.id == field || operation.shift.amount.referencesField field
  excludesTarget := by
    simp [operation.sourceDistinct, operation.amountExcludesTarget]
  run _ document := do
    let outcome ← (operation.evaluateOutcome document).mapError .dateTimeSubdayShift
    let cell ← DocumentComputationReadBack.dateTime model operation.target.checked.target.id outcome
    pure (.dateTime outcome, cell)

/-- A full-Date computation over a field, `Today`, or the Base Year. -/
def ofFullDate (operation : CheckedFullDateComputation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.checked.target.id
  targetKind := .temporal .date
  referencesField field :=
    match operation.operand with
    | .fieldValue source => source.id == field
    | _ => false
  excludesTarget := by
    have admitted := operation.operandAdmitted
    revert admitted
    cases operation.operand <;>
      simp [FlatModel.admitsFullDateComputationOperand]
  run world document := do
    let outcome ← (operation.evaluateOutcome world document).mapError .fullDate
    let cell ← DocumentComputationReadBack.fullDate model operation.target.checked.target.id outcome
    pure (.fullDate outcome, cell)

/-- An Enumeration copy of a field or a literal, read from the document's checked cells. -/
def ofEnumeration (operation : CheckedEnumerationComputationOperation model) :
    CheckedDocumentComputationStep model where
  target := operation.target.field
  targetKind := .enumeration
  referencesField := operation.source.referencesField
  excludesTarget := operation.targetNotReferenced
  run _ document :=
    let outcome := (operation.source.evaluate document.flatContext).asExactStringTargetOutcome
    pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target outcome)

end CheckedDocumentComputationStep

end A12Kernel
