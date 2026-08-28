import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.BooleanComputationResult
import A12Kernel.Elaboration.StaticDiagnostic

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

end A12Kernel
