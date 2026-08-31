import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Date constant computation into a repeatable target

The Kernel admits a bare Date constant into a repeatable target from the target's own group and from
any ancestor of it, and writes it once per instantiated target row, exactly as the three sibling
constant families do ([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)).

**This family's target is checked at neither time, which is a third timing rather than a variant of
the sibling two.** An ordinary String constant is checked entirely at runtime and a Number constant
splits its two grounds across authoring and runtime; a Date constant meets no target check on either
side. Nothing about the target's declared format participates in admission — one literal is admitted
into `dd.MM.yyyy`, `yyyy-MM-dd`, and `yyyy` targets alike — and nothing errors at runtime
([checkpoint](../../docs/SOURCES.md#src-date-constant-target-formatting)).

What decides admission is the **literal's own spelling**, upstream of this carrier: a token counts as
a Date constant only when it is a double-quoted, zero-padded, calendar-*real* `DD.MM.YYYY`, so
`29.02.2024` is a Date and `29.02.2023` is a String. The ISO spelling is never a Date literal, which
is the trap worth naming, because it is exactly the text an ISO-declared target stores. This carrier
therefore takes an already-classified `CivilDate` and owns no lexical gate; `spec/12` owns that rule.

The constant carries no zone and never becomes an `Instant`. It reaches the declaration's own
`evaluateCivil`, which renders it in the target's declared format and applies that declaration's
ordered pre-1900 and Gregorian-floor gates. A component-omitting target such as `yyyy` is a **stated
exclusion** rather than a refusal of the Kernel's: `FullDateTargetFormat.ofSource?` admits only the
two complete formats, and the Kernel stores `2024` there without complaint, so this carrier declines
a target it cannot render rather than claiming the Kernel refuses one.
-/

namespace A12Kernel

inductive RepeatableDateConstantComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetNotFullDate (cause : FullDateTargetElabError)
  deriving Repr, DecidableEq

namespace RepeatableDateConstantComputationElabError

/-- Only the shared placement refusal carries a measured Kernel identity here. A target this project
cannot render is its own routing and claims no class, because the Kernel admits it. -/
def diagnostic? :
    RepeatableDateConstantComputationElabError → Option KernelStaticDiagnostic
  | .target (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .target (.target _) | .target (.targetNotRepeatable _)
  | .targetNotFullDate _ => none

end RepeatableDateConstantComputationElabError

/-- One repeatable FULL Date target, contained in its declaring group, and the already-classified
calendar date every one of its physical rows receives. There is no admission gate between the two:
the constant is admitted whatever the target declares, and the format is a rendering rather than a
constraint. -/
structure CheckedRepeatableDateConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  dateTarget : CheckedFullDateTarget model
  /-- The two certificates describe one field. Without this they could drift to different targets. -/
  sameTarget : dateTarget.checked.target.id = checkedTarget.targetField
  constant : CivilDate

/-- Check carrier-neutral repeatable placement, then refine the target to the renderable FULL Date
subset. No third gate follows, because the Kernel applies none to the constant. -/
def checkRepeatableDateConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (constant : CivilDate) :
    Except RepeatableDateConstantComputationElabError
      (CheckedRepeatableDateConstantComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  let dateTarget ←
    elaborateFullDateTargetIn model checkedTarget.declaration.repeatableScope targetField
      |>.mapError .targetNotFullDate
  if hSame : dateTarget.checked.target.id = checkedTarget.targetField then
    pure { checkedTarget, dateTarget, sameTarget := hSame, constant }
  else
    throw (.targetNotFullDate (.targetKind targetField dateTarget.checked.target.kind))

inductive RepeatableDateConstantComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  deriving Repr, DecidableEq

/-- One target-checked constant retained under its exact target address. -/
structure RepeatableDateConstantComputationOutcome where
  targetField : CellAddr
  outcome : FullDateTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedRepeatableDateConstantComputation

/-- The one row-independent outcome: the declaration's own render-and-check on the literal date. A
constant carries no zone, so it reaches `evaluateCivil` directly and never becomes an `Instant` that
a model-zone decoding could move across a day boundary. -/
def outcome (operation : CheckedRepeatableDateConstantComputation model) :
    FullDateTargetOutcome :=
  operation.dateTarget.evaluateCivil operation.constant

/-- Write the constant once per physical target row, in document order. A group with no instantiated
row yields no outcome at all. -/
def execute (operation : CheckedRepeatableDateConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableDateConstantComputationFault
      (List RepeatableDateConstantComputationOutcome) :=
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

end CheckedRepeatableDateConstantComputation

end A12Kernel
