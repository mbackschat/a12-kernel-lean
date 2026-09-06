import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.ConstantAssignmentDiagnostic
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Time constant computation into a repeatable target

The Kernel admits a bare clock constant into a repeatable target from the target's own group and from
any ancestor of it, and writes it once per instantiated target row, exactly as the sibling constant
families do ([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)).

Like the Date sibling, this family's target is checked at **neither** time: the literal's own spelling
decides admission, and the store is a rendering. The literal is an exact `HH:mm:ss` clock — `"12:30"`
without seconds is not one — and every admitted clock passes the target's basic check, so
`TimeTargetOutcome` carries no error branch at all
([checkpoint](../../docs/SOURCES.md#src-constant-literal-family-gate)).

**What decides admission is the target's declared format string, and the Kernel does not read the
field's kind.** A DATE-declared field whose format is `HH:mm:ss` admits this constant and stores
`12:30:00`; a TIME-declared field whose format is `yyyy-MM-dd` refuses it and takes a date literal
instead. This carrier therefore takes `CheckedClockFormatTarget`, the certificate that reads the format and
not the kind, and is the one family entitled to it: the cross-kind cell is measured here and nowhere
else, so the sibling families keep the TIME-only `CheckedTimeTarget` until each earns its own row.
What survives as a refusal is the format gate, which claims no Kernel class.

A clock carries no date and no zone: it reaches the declared renderer directly, never an `Instant`,
so no model-zone decoding can move it.
-/

namespace A12Kernel

inductive RepeatableTimeConstantComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetNotTime (cause : TimeTargetElabError)
  deriving Repr, DecidableEq

namespace RepeatableTimeConstantComputationElabError

/-- Placement carries its own class, and every target refusal draws the shared assignment
ladder's `temporal` row.

That row is the ladder's inversion: a temporal constant reports its **own** family's class at every
target the ladder does not outrank, so a clock constant into a String or Number declaration draws
the date class rather than that target's. Only a Boolean or Confirm target outranks it. A target
refused for its declared **format** — a clock constant into a date-shaped declaration — draws the
same class, which is why the format and kind refusals need not be told apart here. -/
def diagnostic? :
    RepeatableTimeConstantComputationElabError → Option KernelStaticDiagnostic
  | .target (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .targetNotTime (.targetPolicy (.targetNotTemporal _ actual)) =>
      constantAssignmentDiagnostic? .temporal actual
  | .targetNotTime _ => some .invalidCompareToDate
  | .target (.target _) | .target (.targetNotRepeatable _) => none

end RepeatableTimeConstantComputationElabError

/-- One repeatable complete-clock target, contained in its declaring group, and the literal clock
every one of its physical rows receives. There is no admission gate between the two beyond the
target's own format, and no runtime check at all. -/
structure CheckedRepeatableTimeConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  timeTarget : CheckedClockFormatTarget model
  /-- The two certificates describe one field. Without this they could drift to different targets. -/
  sameTarget : timeTarget.checked.target.id = checkedTarget.targetField
  constant : TimeOfDay

/-- Check carrier-neutral repeatable placement, then refine the target to the renderable complete
clock subset. No third gate follows, because the Kernel applies none to the constant. -/
def checkRepeatableTimeConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (constant : TimeOfDay) :
    Except RepeatableTimeConstantComputationElabError
      (CheckedRepeatableTimeConstantComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  let timeTarget ←
    elaborateClockFormatTargetIn model checkedTarget.declaration.repeatableScope targetField
      |>.mapError .targetNotTime
  if hSame : timeTarget.checked.target.id = checkedTarget.targetField then
    pure { checkedTarget, timeTarget, sameTarget := hSame, constant }
  else
    throw (.targetNotTime (.targetKind targetField timeTarget.checked.target.kind))

inductive RepeatableTimeConstantComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  deriving Repr, DecidableEq

/-- One rendered constant retained under its exact target address. -/
structure RepeatableTimeConstantComputationOutcome where
  targetField : CellAddr
  outcome : TimeTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedRepeatableTimeConstantComputation

/-- The one row-independent outcome. Every admitted clock passes the target's basic check, so this is
always an acceptance and the family owns no rejection branch to get wrong. -/
def outcome (operation : CheckedRepeatableTimeConstantComputation model) :
    TimeTargetOutcome :=
  .accepted (TimeTargetFormat.render operation.timeTarget.format operation.constant)

/-- Write the constant once per **in-capacity** target row, in document order, and only a clear at each
over-limit row. A group with no instantiated row yields no outcome at all. -/
def execute (operation : CheckedRepeatableTimeConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableTimeConstantComputationFault
      (List RepeatableTimeConstantComputationOutcome) :=
  let field := operation.checkedTarget.targetField
  let scope := operation.checkedTarget.declaration.repeatableScope
  let at? (outcome : TimeTargetOutcome) (environment : Env) :
      Except RepeatableTimeConstantComputationFault
        RepeatableTimeConstantComputationOutcome :=
    match environment.pathForScope scope with
    | .error cause => .error (.targetEnvironment cause)
    | .ok path => .ok { targetField := { field, path }, outcome }
  input.computationRowOutcomes scope .targetRows (at? .noValue) (at? operation.outcome)

end CheckedRepeatableTimeConstantComputation

end A12Kernel
