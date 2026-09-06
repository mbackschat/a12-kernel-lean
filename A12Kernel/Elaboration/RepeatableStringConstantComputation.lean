import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.StringFirstFilledComputation
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Ordinary String constant computation into a repeatable target

The Kernel admits a bare String constant into a repeatable target from the target's own group and
from any ancestor of it, and writes it once per instantiated target row; a group the target does not
lie below is refused `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)).

Unlike the Boolean and Confirm carrier this one has a **target-rejection** branch, because a String
target validates what is written to it. The Kernel admits an over-long constant statically and then,
per row, keeps the exact attempted payload with the row flagged rather than truncating, blanking, or
clearing it ([checkpoint](../../docs/SOURCES.md#src-repeatable-string-constant-target-check)). That
is what `StringTargetOutcome.errored` already means, so this family reuses the declaration-owned
target check rather than adding a branch of its own.

The empty literal is not a special case here either: `StringTerm.store` already makes final empty
text a no-value irrespective of where it came from, and reusing it keeps that rule in one place.
-/

namespace A12Kernel

inductive RepeatableStringConstantComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  /-- Carries the kind it refused, because the class the Kernel reports is decided by the
  (constant family, target kind) pair and not by this carrier alone. -/
  | targetNotOrdinaryString (path : List String) (actual : SurfaceScalarKind)
  deriving Repr, DecidableEq

namespace RepeatableStringConstantComputationElabError

/-- Containment carries its own measured identity, and a wrong-kind target draws the shared
literal-comparison ladder's `stringLike` row.

The ladder returns `none` for the two shapes this carrier still refuses without the Kernel
refusing them. A **raw** String target is one: it has the String kind and so passes every kind
gate, and it is declined here because a raw declaration closes the checked value-reading route,
not because the Kernel objects. An **Enumeration** target is the other, and there the Kernel gates
the literal rather than the kind — a declared token is admitted outright. Both are stated
representation boundaries tracked in [`SEMANTICS-GAPS.md`](../../docs/SEMANTICS-GAPS.md), not
unmeasured declines. -/
def diagnostic? :
    RepeatableStringConstantComputationElabError → Option KernelStaticDiagnostic
  | .target (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .targetNotOrdinaryString _ actual =>
      literalComparisonDiagnostic? .stringLike actual
  | .target (.target _) | .target (.targetNotRepeatable _) => none

end RepeatableStringConstantComputationElabError

/-- One repeatable ordinary String target, contained in its declaring group, and the literal every
one of its physical rows receives. -/
structure CheckedRepeatableStringConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  literal : String
  targetOrdinary :
    checkedTarget.declaration.isOrdinaryStringComputationCarrier = true

/-- Check carrier-neutral repeatable placement before the ordinary-String carrier policy. -/
def checkRepeatableStringConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (literal : String) :
    Except RepeatableStringConstantComputationElabError
      (CheckedRepeatableStringConstantComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  if hOrdinary :
      checkedTarget.declaration.isOrdinaryStringComputationCarrier = true then
    pure { checkedTarget, literal, targetOrdinary := hOrdinary }
  else
    throw (.targetNotOrdinaryString checkedTarget.declaration.path
      checkedTarget.declaration.policy.kind.surfaceKind)

inductive RepeatableStringConstantComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | targetPatternUnavailable (field : FieldId)
  deriving Repr, DecidableEq

/-- One target-checked constant retained under its exact target address. -/
structure RepeatableStringConstantComputationOutcome where
  targetField : CellAddr
  outcome : StringTargetOutcome
  deriving Repr, DecidableEq

/-- One checked repeatable String constant result backed by the shared typed String channels. -/
structure RepeatableStringConstantComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedRepeatableStringConstantComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedRepeatableStringConstantComputation

/-- The root write attempt every row makes, before that row's target check. Reusing
`StringTerm.store` is what keeps the empty-text rule owned in one place. -/
def store (operation : CheckedRepeatableStringConstantComputation model) :
    StringStore :=
  (StringTerm.text operation.literal).store

/-- Write the constant once per **in-capacity** target row, in document order, applying the declaration's
own target policy at each, and only a clear at each over-limit row. A group with no instantiated row
yields no outcome at all. -/
def execute (operation : CheckedRepeatableStringConstantComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except RepeatableStringConstantComputationFault
      (List RepeatableStringConstantComputationOutcome) :=
  let field := operation.checkedTarget.targetField
  let scope := operation.checkedTarget.declaration.repeatableScope
  match patterns.targetMatcher? field with
  | none => .error (.targetPatternUnavailable field)
  | some matcher =>
      let at? (outcome : StringTargetOutcome) (environment : Env) :
          Except RepeatableStringConstantComputationFault
            RepeatableStringConstantComputationOutcome :=
        match environment.pathForScope scope with
        | .error cause => .error (.targetEnvironment cause)
        | .ok path => .ok { targetField := { field, path }, outcome }
      input.computationRowOutcomes scope .targetRows (at? .noValue)
        (at? (StringFieldPolicy.checkTargetWithPattern
          operation.checkedTarget.declaration.stringPolicy matcher
          operation.store))

/-- Classify every exact row outcome against immutable source target state through the shared String
result owner. -/
def executeResult (operation : CheckedRepeatableStringConstantComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except RepeatableStringConstantComputationFault
      (RepeatableStringConstantComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute patterns input
  pure {
    operation
    string := StringComputationRunView.fromSourcedOutcomes residualMessages
      (outcomes.map fun entry => {
        targetField := entry.targetField
        outcome := entry.outcome
        source := input.sourceStringTargetStateAt entry.targetField })
  }

end CheckedRepeatableStringConstantComputation

namespace RepeatableStringConstantComputationRunView

/-- Apply only retained exact-address String actions to a separate same-model destination. -/
def applyToChecked
    (view : RepeatableStringConstantComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end RepeatableStringConstantComputationRunView

end A12Kernel
