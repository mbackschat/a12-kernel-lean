import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StaticDiagnostic

/-! # DateTime constant computation into a repeatable target

The Kernel admits a bare DateTime constant into a repeatable target from the target's own group and
from any ancestor of it, and writes it once per instantiated target row, exactly as the four sibling
constant families do ([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)).

**The literal's spelling owes nothing to the format the target renders into.** `"05.03.2024T12:30:00"`
— the German date literal, `T`, and the clock literal concatenated — is admitted into a target whose
declared format is `yyyy-MM-dd'T'HH:mm:ss`, which is the only DateTime declaration format this
project's renderer admits ([checkpoint](../../docs/SOURCES.md#src-temporal-constant-literal-composition)).
Admission is static and the literal is upstream of this carrier, which takes an already-classified
`LocalDateTime`; `spec/12` owns the lexical rule.

**A constant never becomes an `Instant`, so the model zone cannot reach it.** This is the whole
semantic content of the family and it is what separates it from the computed DateTime carriers, which
resolve an exact instant through `ConcreteProfile.localDateTime?` and can fail when no local label
exists. A constant arrives already a wall label: it reaches `DateTimeTargetFormat.render` directly, so
a label inside a spring-forward gap — one `ConcreteProfile.resolveLocal?` maps to no instant at all —
still stores. `DateTimeTargetOutcome` therefore carries no evaluation fault and no rejection branch on
this route.

The rendered text is `external evidence pending`: the composition checkpoint took static admission
only, and no runtime row places this constant in a store. The rendering claimed here is the declared
format's own, the same one the Date and Time siblings had measured for theirs, which is a reuse of a
mechanism across a carrier boundary rather than an observation of this one ([`LF116`](../../docs/LEAN-FINDINGS.md)).

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
label every one of its physical rows receives. There is no admission gate between the two beyond the
target's own format, and no runtime check at all. -/
structure CheckedRepeatableDateTimeConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  dateTimeTarget : CheckedDateTimeTarget model
  /-- The two certificates describe one field. Without this they could drift to different targets. -/
  sameTarget : dateTimeTarget.checked.target.id = checkedTarget.targetField
  constant : LocalDateTime

/-- Check carrier-neutral repeatable placement, then refine the target to the renderable complete
DateTime subset. No third gate follows, because the Kernel applies none to the constant. -/
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

/-- One rendered constant retained under its exact target address. -/
structure RepeatableDateTimeConstantComputationOutcome where
  targetField : CellAddr
  outcome : DateTimeTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedRepeatableDateTimeConstantComputation

/-- The one row-independent outcome. The constant is already a local label, so this bypasses the
zone resolution `CheckedDateTimeTarget.evaluate` performs for a computed instant and can neither fail
nor depend on the model's zone. -/
def outcome (operation : CheckedRepeatableDateTimeConstantComputation model) :
    DateTimeTargetOutcome :=
  .accepted
    (DateTimeTargetFormat.render operation.dateTimeTarget.format operation.constant)

/-- Write the constant once per **in-capacity** target row, in document order, and only a clear at
each over-limit row. A group with no instantiated row yields no outcome at all. -/
def execute (operation : CheckedRepeatableDateTimeConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableDateTimeConstantComputationFault
      (List RepeatableDateTimeConstantComputationOutcome) :=
  let field := operation.checkedTarget.targetField
  let scope := operation.checkedTarget.declaration.repeatableScope
  let at? (outcome : DateTimeTargetOutcome) (environment : Env) :
      Except RepeatableDateTimeConstantComputationFault
        RepeatableDateTimeConstantComputationOutcome :=
    match environment.pathForScope scope with
    | .error cause => .error (.targetEnvironment cause)
    | .ok path => .ok { targetField := { field, path }, outcome }
  input.computationRowOutcomes scope .targetRows (at? .noValue) (at? operation.outcome)

end CheckedRepeatableDateTimeConstantComputation

end A12Kernel
