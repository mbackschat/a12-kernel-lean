import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.BooleanComputationResult
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Elaboration.AddressedRepeatableTarget

/-! # Boolean and Confirm constant-computation checking, execution, and result application -/

namespace A12Kernel

inductive BooleanConstantOperation where
  | boolean (value : Bool)
  | confirmTrue
  deriving Repr, DecidableEq

namespace BooleanConstantOperation

def targetKind : BooleanConstantOperation → FieldKind
  | .boolean _ => .boolean
  | .confirmTrue => .confirm

def value : BooleanConstantOperation → Bool
  | .boolean value => value
  | .confirmTrue => true

end BooleanConstantOperation

/-- A Boolean constant operation whose constructor certifies the target-kind policy. Confirm has no False constructor because that authored combination is statically illegal. -/
structure CheckedBooleanConstantOperation (targetKind : FieldKind) where
  private mk ::
  operation : BooleanConstantOperation
  targetKindMatches : operation.targetKind = targetKind

inductive BooleanConstantOperationElabError where
  | targetKind (actual : SurfaceScalarKind)
  | falseConfirm
  deriving Repr, DecidableEq

namespace BooleanConstantOperationElabError

/-- Project only the measured Confirm/False refusal. Unsupported target kinds retain their local identity because no Kernel class has been established for them. -/
def diagnostic? : BooleanConstantOperationElabError → Option KernelStaticDiagnostic
  | .falseConfirm => some .invalidCompareToYes
  | .targetKind _ => none

end BooleanConstantOperationElabError

/-- Accept both Boolean constants but only True for a Confirm target. -/
def checkBooleanConstantOperation (targetKind : FieldKind) (value : Bool) :
    Except BooleanConstantOperationElabError
      (CheckedBooleanConstantOperation targetKind) :=
  match targetKind, value with
  | .boolean, value => .ok ⟨.boolean value, rfl⟩
  | .confirm, true => .ok ⟨.confirmTrue, rfl⟩
  | .confirm, false => .error .falseConfirm
  | actual, _ => .error (.targetKind actual.surfaceKind)

inductive BooleanConstantComputationElabError where
  | target (cause : ResolveError)
  | targetRepeatable (path : List String)
  | operation (path : List String) (cause : BooleanConstantOperationElabError)
  deriving Repr, DecidableEq

namespace BooleanConstantComputationElabError

/-- Preserve the operation's measured diagnostic without assigning Kernel identities to unmeasured target-placement failures. -/
def diagnostic? : BooleanConstantComputationElabError → Option KernelStaticDiagnostic
  | .operation _ cause => cause.diagnostic?
  | .target _ | .targetRepeatable _ => none

end BooleanConstantComputationElabError

/-- One fixed Boolean or Confirm target and its target-kind-certified constant operation. -/
structure CheckedBooleanConstantComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  declaringGroup : GroupPath
  operation : CheckedBooleanConstantOperation target.policy.kind
  targetFixed : target.repeatableScope = []

/-- Check one fixed target and retain the computation's declaration group separately. Target placement owns execution scope, so a fixed declaration group need not equal the fixed target group. -/
def checkBooleanConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (value : Bool) :
    Except BooleanConstantComputationElabError
      (CheckedBooleanConstantComputation model) := do
  if !GroupPath.isValid declaringGroup then
    throw (.target (.invalidRuleGroup declaringGroup))
  let target ← model.lookupUniqueId targetField |>.mapError .target
  if hFixed : target.repeatableScope = [] then
    let operation ← checkBooleanConstantOperation target.policy.kind value
      |>.mapError (.operation target.path)
    pure {
      target
      declaringGroup
      operation
      targetFixed := hFixed
    }
  else
    throw (.targetRepeatable target.path)

/-- One checked constant result retaining the target certificate beside the shared typed Boolean channels. -/
structure BooleanConstantComputationRunView (model : FlatModel) where
  private mk ::
  operation : CheckedBooleanConstantComputation model
  boolean : BooleanComputationRunView FormalCause FieldId

namespace CheckedBooleanConstantComputation

/-- Evaluate the already checked constant without introducing a runtime failure branch. -/
def execute (operation : CheckedBooleanConstantComputation model) :
    BooleanComputationOutcome :=
  .value operation.operation.operation.value

/-- Classify the constant against immutable source target identity through the shared Boolean result owner. -/
def executeResult (operation : CheckedBooleanConstantComputation model)
    (input : CheckedDocument model) :
    BooleanConstantComputationRunView model := {
  operation
  boolean := BooleanComputationRunView.fromSourcedOutcomes [] [(
    operation.target.id, operation.execute,
    input.sourceBooleanTargetState operation.target.id)]
}

end CheckedBooleanConstantComputation

namespace BooleanConstantComputationRunView

def withoutErrors (view : BooleanConstantComputationRunView model) :=
  view.boolean.withoutErrors

def withChanges (view : BooleanConstantComputationRunView model) :=
  view.boolean.withChanges

def withErrors (view : BooleanConstantComputationRunView model) :=
  view.boolean.withErrors

def cleared (view : BooleanConstantComputationRunView model) :=
  view.boolean.cleared

def formalErrorsInOperands (view : BooleanConstantComputationRunView model) :=
  view.boolean.formalErrorsInOperands

/-- The constant result has neither target errors nor operands that could contribute formal messages. -/
def noErrorOccurred (view : BooleanConstantComputationRunView model) : Bool :=
  view.boolean.noErrorOccurred

/-- Apply only immutable-source-classified changes to a separate checked destination of the same model. -/
def applyToChecked (view : BooleanConstantComputationRunView model)
    (destination : CheckedDocument model) : BooleanComputationDestination :=
  view.boolean.applyTo destination.sourceBooleanTargetState

end BooleanConstantComputationRunView

/-! ## Repeatable constant targets

The Kernel admits a bare constant into a **repeatable** target and computes one value per
instantiated target row, from the target's own group and from any ancestor of it alike, refusing
only a group the target does not lie below. That row count comes from the target's own repeatable
scope: a constant carries no operand, so no other source of iteration exists on this carrier
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)).

The fixed family above keeps its own certificate rather than being widened. The two differ in result
domain — one value under a `FieldId`, one per row under a `CellAddr` — so a shared carrier would
have to erase the distinction its consumers exist to read.
-/

inductive RepeatableBooleanConstantComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | operation (path : List String) (cause : BooleanConstantOperationElabError)
  deriving Repr, DecidableEq

namespace RepeatableBooleanConstantComputationElabError

/-- Carry the measured Kernel identity for both refusals this carrier can reach. Containment is
`MVK_ERROR_FIELD_NOT_IN_RULEGROUP` here because a repeatable target iterates with no operand; an
unresolvable target or a non-repeatable one is this project's own routing and claims no Kernel
class. -/
def diagnostic? :
    RepeatableBooleanConstantComputationElabError → Option KernelStaticDiagnostic
  | .operation _ cause => cause.diagnostic?
  | .target (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .target (.target _) | .target (.targetNotRepeatable _) => none

end RepeatableBooleanConstantComputationElabError

/-- One repeatable Boolean or Confirm target, contained in its declaring group, and its
target-kind-certified constant operation. -/
structure CheckedRepeatableBooleanConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  operation :
    CheckedBooleanConstantOperation checkedTarget.declaration.policy.kind

/-- Check carrier-neutral repeatable placement before the target-kind policy, so a fixed target is
routed away by the shared certificate rather than by a second local gate. -/
def checkRepeatableBooleanConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (value : Bool) :
    Except RepeatableBooleanConstantComputationElabError
      (CheckedRepeatableBooleanConstantComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  let operation ←
    checkBooleanConstantOperation checkedTarget.declaration.policy.kind value
      |>.mapError (.operation checkedTarget.declaration.path)
  pure { checkedTarget, operation }

inductive RepeatableBooleanConstantComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  deriving Repr, DecidableEq

/-- One constant retained under its exact target address. -/
structure RepeatableBooleanConstantComputationOutcome where
  targetField : CellAddr
  result : BooleanComputationOutcome
  deriving Repr, DecidableEq

/-- One checked repeatable constant result backed by the shared typed Boolean channels. -/
structure RepeatableBooleanConstantComputationRunView (model : FlatModel) where
  private mk ::
  operation : CheckedRepeatableBooleanConstantComputation model
  boolean : BooleanComputationRunView FormalCause CellAddr

namespace CheckedRepeatableBooleanConstantComputation

/-- The constant every physical target row receives. It does not vary by row, which is what makes
the row set the whole of this family's runtime content. -/
def value (operation : CheckedRepeatableBooleanConstantComputation model) : Bool :=
  operation.operation.operation.value

/-- Emit the constant once per physical target row, in document order. A group with no instantiated
row yields no outcome at all rather than one implicit instance, because the target repeats. -/
def execute (operation : CheckedRepeatableBooleanConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableBooleanConstantComputationFault
      (List RepeatableBooleanConstantComputationOutcome) :=
  let scope := operation.checkedTarget.declaration.repeatableScope
  match input.actualRowEnvironments scope with
  | .error cause => .error (.targetRows cause)
  | .ok environments =>
      match environments.mapM fun environment => environment.pathForScope scope with
      | .error cause => .error (.targetEnvironment cause)
      | .ok paths => .ok (paths.map fun path => {
          targetField := { field := operation.checkedTarget.targetField, path }
          result := .value operation.value })

/-- Classify every exact row outcome against immutable source target state through the shared
Boolean result owner. -/
def executeResult (operation : CheckedRepeatableBooleanConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableBooleanConstantComputationFault
      (RepeatableBooleanConstantComputationRunView model) := do
  let outcomes ← operation.execute input
  pure {
    operation
    boolean := BooleanComputationRunView.fromSourcedOutcomes []
      (outcomes.map fun entry =>
        (entry.targetField, entry.result,
          input.sourceBooleanTargetStateAt entry.targetField))
  }

end CheckedRepeatableBooleanConstantComputation

namespace RepeatableBooleanConstantComputationRunView

def withoutErrors (view : RepeatableBooleanConstantComputationRunView model) :=
  view.boolean.withoutErrors

def withChanges (view : RepeatableBooleanConstantComputationRunView model) :=
  view.boolean.withChanges

/-- A constant has no operand and no target-error channel, so both error channels stay empty on
every row; the family's only failure is structural, before any outcome exists. -/
def noErrorOccurred (view : RepeatableBooleanConstantComputationRunView model) :
    Bool :=
  view.boolean.noErrorOccurred

/-- Apply only retained exact-address changes to a separate same-model destination projection. -/
def applyToChecked (view : RepeatableBooleanConstantComputationRunView model)
    (destination : CheckedDocument model) :
    BooleanComputationDestination CellAddr :=
  view.boolean.applyTo destination.sourceBooleanTargetStateAt

end RepeatableBooleanConstantComputationRunView

end A12Kernel
