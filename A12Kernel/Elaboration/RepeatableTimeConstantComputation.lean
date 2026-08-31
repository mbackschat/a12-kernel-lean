import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.NumericComputation.RunResult
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
instead. This carrier reuses `CheckedTimeTarget`, which additionally requires `kind = .time`, so it
is **strictly narrower than the Kernel** on exactly that cell. That narrowing is a deliberate stated
exclusion rather than a claim: widening the shared certificate would change every family built on it,
none of which has a measurement for the cross-kind cell. The refusal therefore claims no Kernel class.

A clock carries no date and no zone: it reaches the declared renderer directly, never an `Instant`,
so no model-zone decoding can move it.
-/

namespace A12Kernel

inductive RepeatableTimeConstantComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetNotTime (cause : TimeTargetElabError)
  deriving Repr, DecidableEq

namespace RepeatableTimeConstantComputationElabError

/-- Only the shared placement refusal carries a measured Kernel identity. A target this carrier
declines for its declared kind is a stated exclusion of a shape the Kernel admits, so it claims no
class rather than borrowing a plausible one. -/
def diagnostic? :
    RepeatableTimeConstantComputationElabError → Option KernelStaticDiagnostic
  | .target (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .target (.target _) | .target (.targetNotRepeatable _)
  | .targetNotTime _ => none

end RepeatableTimeConstantComputationElabError

/-- One repeatable complete-clock target, contained in its declaring group, and the literal clock
every one of its physical rows receives. There is no admission gate between the two beyond the
target's own format, and no runtime check at all. -/
structure CheckedRepeatableTimeConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  timeTarget : CheckedTimeTarget model
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
    elaborateTimeTargetIn model checkedTarget.declaration.repeatableScope targetField
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

/-- Write the constant once per physical target row, in document order. A group with no instantiated
row yields no outcome at all. -/
def execute (operation : CheckedRepeatableTimeConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableTimeConstantComputationFault
      (List RepeatableTimeConstantComputationOutcome) :=
  let field := operation.checkedTarget.targetField
  let scope := operation.checkedTarget.declaration.repeatableScope
  match input.actualRowEnvironments scope with
  | .error cause => .error (.targetRows cause)
  | .ok environments =>
      match environments.mapM fun environment => environment.pathForScope scope with
      | .error cause => .error (.targetEnvironment cause)
      | .ok paths => .ok (paths.map fun path => {
          targetField := { field, path }
          outcome := operation.outcome })

end CheckedRepeatableTimeConstantComputation

end A12Kernel
