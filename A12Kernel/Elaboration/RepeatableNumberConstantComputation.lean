import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.NumericComputation.SourceTarget
import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Number constant computation into a repeatable target

The Kernel admits a bare Number constant into a repeatable target from the target's own group and
from any ancestor of it, and writes it once per instantiated target row
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)).

Its target refuses on two grounds and the Kernel checks them at **different times**, which is the
whole shape of this family. Decimal scale is an authoring gate: a literal carrying more fractional
digits than the target declares is refused `MVK_INVALID_COMPARE_DEC_PLACES`, so an over-scale
constant never reaches runtime and is unrepresentable here rather than a runtime branch. The declared
range is not a gate at all — an out-of-range constant is admitted and then errors on every row,
keeping the exact attempted value uncapped
([checkpoint](../../docs/SOURCES.md#src-repeatable-number-constant-target-check)).

Scale is read **twice, differently**, and that is the trap. The authoring gate compares the literal's
*authored* scale, trailing zeros included: `1.50` into a scale-0 target is refused, and the kernel's
own text says the right-hand side has two fractional digits. The store then strips those same zeros
and pads the result up to the target's `minFractionalDigits`, so `1.50` into a two-digit target keeps
`1.5` while `1.5` into a target that *requires* two digits becomes `1.50`. Stripping never feeds back
into the gate. The carrier therefore retains the authored constant for the gate and renders the store
through the shared computed-Number rendering every other Number operation uses.
-/

namespace A12Kernel

inductive RepeatableNumberConstantComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetNotNumber (path : List String)
  | constantScaleExceedsTarget (path : List String)
      (constantScale targetScale : Nat)
  deriving Repr, DecidableEq

namespace RepeatableNumberConstantComputationElabError

/-- Both refusals this carrier can reach carry a measured Kernel identity. A target this project
cannot resolve, or one that is not a repeatable Number, is its own routing and claims no class. -/
def diagnostic? :
    RepeatableNumberConstantComputationElabError → Option KernelStaticDiagnostic
  | .target (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .constantScaleExceedsTarget _ _ _ => some .invalidCompareDecimalPlaces
  | .target (.target _) | .target (.targetNotRepeatable _)
  | .targetNotNumber _ => none

end RepeatableNumberConstantComputationElabError

/-- One repeatable Number target, contained in its declaring group, and the constant every one of its
physical rows receives. The scale certificate is the separate static assignment-scale admission the
target check expects, so no runtime scale branch exists. -/
structure CheckedRepeatableNumberConstantComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  targetPolicy : NumericTargetPolicy
  policyOwned :
    checkedTarget.declaration.toNumericTargetPolicy? = some targetPolicy
  /-- The literal exactly as authored, trailing zeros included, because the static gate below reads
  this scale rather than the stripped one. The stored form is `storedConstant`, never this. -/
  constant : StoredNumber
  scaleFits : constant.scale ≤ targetPolicy.info.scale

/-- Check carrier-neutral repeatable placement, then the Number target policy, then the one static
gate the Kernel applies to a constant. -/
def checkRepeatableNumberConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (constant : StoredNumber) :
    Except RepeatableNumberConstantComputationElabError
      (CheckedRepeatableNumberConstantComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  match hPolicy : checkedTarget.declaration.toNumericTargetPolicy? with
  | none => throw (.targetNotNumber checkedTarget.declaration.path)
  | some targetPolicy =>
      if hScale : constant.scale ≤ targetPolicy.info.scale then
        pure {
          checkedTarget
          targetPolicy
          policyOwned := hPolicy
          constant
          scaleFits := hScale
        }
      else
        throw (.constantScaleExceedsTarget checkedTarget.declaration.path
          constant.scale targetPolicy.info.scale)

inductive RepeatableNumberConstantComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | targetState (cause : NumericSourceTargetError)
  deriving Repr, DecidableEq

/-- One target-checked constant retained under its exact target address. -/
structure RepeatableNumberConstantComputationOutcome where
  targetField : CellAddr
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

/-- One checked repeatable Number constant result backed by the shared typed Number channels. -/
structure RepeatableNumberConstantComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedRepeatableNumberConstantComputation model
  numeric : NumericComputationRunView ResidualMessage CellAddr

namespace CheckedRepeatableNumberConstantComputation

/-- The constant's stored decimal: the shared computed-Number rendering, which strips trailing zeros
and then pads to the target's required minimum. Reusing it is what keeps a constant from drifting
away from an operation that produces the same amount. -/
def storedConstant (operation : CheckedRepeatableNumberConstantComputation model) :
    StoredNumber :=
  (StoredNumber.fromComputed operation.constant.amount
    operation.targetPolicy.minFractionalDigits).2

/-- The one row-independent outcome: the declaration's own attempt check on the stored form. -/
def outcome (operation : CheckedRepeatableNumberConstantComputation model) :
    NumericTargetOutcome :=
  NumericTargetPolicy.checkAttempt operation.targetPolicy operation.storedConstant

/-- Write the constant once per physical target row, in document order, applying the declaration's
own attempt check at each. A group with no instantiated row yields no outcome at all. -/
def execute (operation : CheckedRepeatableNumberConstantComputation model)
    (input : CheckedDocument model) :
    Except RepeatableNumberConstantComputationFault
      (List RepeatableNumberConstantComputationOutcome) :=
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

/-- Classify every exact row outcome against immutable source target state through the shared Number
result owner. -/
def executeResult (operation : CheckedRepeatableNumberConstantComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except RepeatableNumberConstantComputationFault
      (RepeatableNumberConstantComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  let entries ← outcomes.mapM fun entry => do
    let source ← input.numericTargetStateAt entry.targetField
      |>.mapError .targetState
    pure { targetField := entry.targetField, outcome := entry.outcome, source }
  pure {
    operation
    numeric :=
      NumericComputationRunView.fromPartitionedSourceOutcomes residualMessages entries
  }

end CheckedRepeatableNumberConstantComputation

end A12Kernel
