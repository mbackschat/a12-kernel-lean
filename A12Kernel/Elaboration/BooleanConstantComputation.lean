import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Boolean and Confirm constant-computation target admission -/

namespace A12Kernel

inductive BooleanConstantOperation where
  | boolean (value : Bool)
  | confirmTrue
  deriving Repr, DecidableEq

namespace BooleanConstantOperation

def targetKind : BooleanConstantOperation → FieldKind
  | .boolean _ => .boolean
  | .confirmTrue => .confirm

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
  | targetGroup (actual expected : GroupPath)
  | targetRepeatable (path : List String)
  | operation (path : List String) (cause : BooleanConstantOperationElabError)
  deriving Repr, DecidableEq

namespace BooleanConstantComputationElabError

/-- Preserve the operation's measured diagnostic without assigning Kernel identities to unmeasured target-placement failures. -/
def diagnostic? : BooleanConstantComputationElabError → Option KernelStaticDiagnostic
  | .operation _ cause => cause.diagnostic?
  | .target _ | .targetGroup _ _ | .targetRepeatable _ => none

end BooleanConstantComputationElabError

/-- One fixed Boolean or Confirm target and its target-kind-certified constant operation. -/
structure CheckedBooleanConstantComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  targetGroup : GroupPath
  operation : CheckedBooleanConstantOperation target.policy.kind
  targetFixed : target.repeatableScope = []
  targetOwnedByGroup : target.groupPath = targetGroup

/-- Check the measured fixed-target constant shape. Runtime evaluation, alternatives, preconditions, and repeatable targets remain outside this boundary. -/
def checkBooleanConstantComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (value : Bool) :
    Except BooleanConstantComputationElabError
      (CheckedBooleanConstantComputation model) := do
  let target ← model.lookupUniqueId targetField |>.mapError .target
  if hGroup : target.groupPath = declaringGroup then
    if hFixed : target.repeatableScope = [] then
      let operation ← checkBooleanConstantOperation target.policy.kind value
        |>.mapError (.operation target.path)
      pure {
        target
        targetGroup := declaringGroup
        operation
        targetFixed := hFixed
        targetOwnedByGroup := hGroup
      }
    else
      throw (.targetRepeatable target.path)
  else
    throw (.targetGroup target.groupPath declaringGroup)

end A12Kernel
