import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.ComputationMessage

/-! # DateTime constant computation into a repeatable target

The Kernel admits a bare DateTime constant into a repeatable target from the target's own group and
from any ancestor of it, with execution addressed from the target's row scope exactly as for the four
sibling constant families ([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)).

**The literal's spelling owes nothing to the format the target renders into.** `"05.03.2024T12:30:00"`
— the German date literal, `T`, and the clock literal concatenated — is admitted into a target whose
declared format is `yyyy-MM-dd'T'HH:mm:ss`, which is the only DateTime declaration format this
project's renderer admits ([checkpoint](../../docs/SOURCES.md#src-temporal-constant-literal-composition)).
Admission is static and the literal is upstream of this carrier, which takes an already-classified
`LocalDateTime`; `spec/12` owns the lexical rule.

The constant remains a wall label for storage, but the model zone still validates that label at
runtime. A resolvable label renders directly in the target format. A spring-forward gap produces no
computed outcome and one `berechnungsWertFehler` residual at each in-capacity target row. The static
model verdict has a separate host-zone dependency upstream of this carrier
([checkpoint](../../docs/SOURCES.md#src-datetime-constant-zone-split)).

Like the Time sibling this carrier reuses `CheckedDateTimeTarget`, which requires `kind = .dateTime`.
The measured family gate reads the declared **format string** and not the field's kind, so the carrier
is narrower than the Kernel wherever a non-DATETIME field declares a DateTime format. That narrowing
is a stated exclusion rather than a claim, and its refusal borrows no Kernel class.
-/

namespace A12Kernel

inductive RepeatableDateTimeConstantComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetNotDateTime (cause : DateTimeTargetElabError)
  deriving Repr, DecidableEq

namespace RepeatableDateTimeConstantComputationElabError

/-- Only the shared placement refusal carries a measured Kernel identity. A target this carrier
declines for its declared kind, component set, format, or zone is a stated exclusion of a shape whose
Kernel treatment is unmeasured, so it claims no class rather than borrowing a plausible one. -/
def diagnostic? :
    RepeatableDateTimeConstantComputationElabError → Option KernelStaticDiagnostic
  | .target (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .target (.target _) | .target (.targetNotRepeatable _)
  | .targetNotDateTime _ => none

end RepeatableDateTimeConstantComputationElabError

/-- One repeatable complete-DateTime target, contained in its declaring group, and the literal wall
label attempted at each in-capacity row. Target refinement owns static format admission; the model
zone validates the already-classified label at runtime. -/
structure CheckedRepeatableDateTimeConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  dateTimeTarget : CheckedDateTimeTarget model
  /-- The two certificates describe one field. Without this they could drift to different targets. -/
  sameTarget : dateTimeTarget.checked.target.id = checkedTarget.targetField
  constant : LocalDateTime

/-- Check carrier-neutral repeatable placement, then refine the target to the renderable complete
DateTime subset. Runtime model-zone validation remains in execution rather than this static gate. -/
def checkRepeatableDateTimeConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (constant : LocalDateTime) :
    Except RepeatableDateTimeConstantComputationElabError
      (CheckedRepeatableDateTimeConstantComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  let dateTimeTarget ←
    elaborateDateTimeTargetIn model checkedTarget.declaration.repeatableScope targetField
      |>.mapError .targetNotDateTime
  if hSame : dateTimeTarget.checked.target.id = checkedTarget.targetField then
    pure { checkedTarget, dateTimeTarget, sameTarget := hSame, constant }
  else
    throw (.targetNotDateTime
      (.targetKind targetField dateTimeTarget.checked.target.kind))

inductive RepeatableDateTimeConstantComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  deriving Repr, DecidableEq

/-- One target address whose constant label is invalid in the model zone. The public Kernel channel
reports this as the fixed `berechnungsWertFehler` code despite the computation having no operands. -/
structure RepeatableDateTimeConstantValueFinding where
  targetField : CellAddr
  deriving Repr, DecidableEq

namespace RepeatableDateTimeConstantValueFinding

def errorCode (_ : RepeatableDateTimeConstantValueFinding) : String :=
  berechnungsWertFehler

end RepeatableDateTimeConstantValueFinding

/-- One rendered constant retained under its exact target address. -/
structure RepeatableDateTimeConstantComputationOutcome where
  targetField : CellAddr
  outcome : DateTimeTargetOutcome
  deriving Repr, DecidableEq

private inductive RepeatableDateTimeConstantComputationAttempt where
  | outcome (value : RepeatableDateTimeConstantComputationOutcome)
  | invalidValue (finding : RepeatableDateTimeConstantValueFinding)

/-- The two public computation channels this carrier can populate. Invalid local labels have no
computed outcome and remain in the API-named residual channel. -/
structure RepeatableDateTimeConstantComputationRun where
  outcomes : List RepeatableDateTimeConstantComputationOutcome
  formalErrorsInOperands : List RepeatableDateTimeConstantValueFinding
  deriving Repr, DecidableEq

namespace CheckedRepeatableDateTimeConstantComputation

/-- Resolve the literal label in the model zone. A resolvable label stores in its authored local
components; a gap has no computed outcome and is reported separately by `execute`. -/
def outcome? (operation : CheckedRepeatableDateTimeConstantComputation model) :
    Option DateTimeTargetOutcome :=
  match operation.dateTimeTarget.profile.resolveLocal? operation.constant with
  | none => none
  | some _ =>
      some (.accepted
        (DateTimeTargetFormat.render operation.dateTimeTarget.format operation.constant))

/-- Attempt the constant once per **in-capacity** target row, in document order, and emit only a clear
at each over-limit row. A group with no instantiated row yields neither outcome nor residual. -/
def execute (operation : CheckedRepeatableDateTimeConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableDateTimeConstantComputationFault
      RepeatableDateTimeConstantComputationRun := do
  let field := operation.checkedTarget.targetField
  let scope := operation.checkedTarget.declaration.repeatableScope
  let addressAt? (environment : Env) :
      Except RepeatableDateTimeConstantComputationFault
        CellAddr :=
    match environment.pathForScope scope with
    | .error cause => .error (.targetEnvironment cause)
    | .ok path => .ok { field, path }
  let overCapacity (environment : Env) :
      Except RepeatableDateTimeConstantComputationFault
        RepeatableDateTimeConstantComputationAttempt := do
    let targetField ← addressAt? environment
    pure (RepeatableDateTimeConstantComputationAttempt.outcome
      { targetField, outcome := .noValue })
  let inCapacity (environment : Env) :
      Except RepeatableDateTimeConstantComputationFault
        RepeatableDateTimeConstantComputationAttempt := do
    let targetField ← addressAt? environment
    match operation.outcome? with
    | some outcome =>
        pure (RepeatableDateTimeConstantComputationAttempt.outcome
          { targetField, outcome })
    | none =>
        pure (RepeatableDateTimeConstantComputationAttempt.invalidValue
          { targetField })
  let attempts ←
    input.computationRowOutcomes scope .targetRows overCapacity inCapacity
  pure {
    outcomes := attempts.filterMap fun
      | RepeatableDateTimeConstantComputationAttempt.outcome outcome => some outcome
      | RepeatableDateTimeConstantComputationAttempt.invalidValue _ => none
    formalErrorsInOperands := attempts.filterMap fun
      | RepeatableDateTimeConstantComputationAttempt.outcome _ => none
      | RepeatableDateTimeConstantComputationAttempt.invalidValue finding => some finding
  }

end CheckedRepeatableDateTimeConstantComputation

end A12Kernel
