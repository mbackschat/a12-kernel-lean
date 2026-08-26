import A12Kernel.Elaboration.DateFromDateTime
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked repeatable `TimeFromDateTime` placement

This capsule certifies one repeatable Time target and one complete-DateTime source whose repetition is bound by that target's exact reading scope. Execution, result projection, application, scheduling, and document reconstruction remain separate.
-/

namespace A12Kernel

inductive AddressedTimeFromDateTimeElabError where
  | targetLookup (cause : ResolveError)
  | target (cause : TimeTargetElabError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | source (cause : BoundCompleteDateTimeSourceElabError)
  deriving Repr, DecidableEq

/-- One repeatable Time extraction placement certified against a validated model. -/
structure CheckedAddressedTimeFromDateTime (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  target : CheckedTimeTarget model
  sourceBinding : CheckedBoundCompleteDateTimeSource model declaringGroup
    target.checked.declaration.repeatableScope
  targetInDeclaringGroup :
    target.checked.declaration.groupPath = declaringGroup
  targetRepeatable : target.checked.declaration.repeatableScope ≠ []

/-- Certify one complete-DateTime source whose repeatable levels the Time target's own scope binds. -/
def checkAddressedTimeFromDateTime
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedTimeFromDateTimeElabError
      (CheckedAddressedTimeFromDateTime model) := do
  let targetDeclaration ← model.lookupUniqueId targetField |>.mapError .targetLookup
  let checkedTarget ←
    elaborateTemporalTargetPolicyIn model targetDeclaration.repeatableScope targetField
      |>.mapError (fun cause => .target (.targetPolicy cause))
  let target ← checkedTarget.toTimeTarget |>.mapError .target
  if hGroup : target.checked.declaration.groupPath = declaringGroup then
    if hRepeatable : target.checked.declaration.repeatableScope.isEmpty then
      throw (.targetNotRepeatable target.checked.declaration.path)
    else
      let sourceBinding ← checkBoundCompleteDateTimeSource model declaringGroup
        target.checked.declaration.path
        target.checked.declaration.repeatableScope sourceReference
        |>.mapError .source
      pure {
        declaringGroup, target, sourceBinding
        targetInDeclaringGroup := hGroup
        targetRepeatable := by
          intro empty
          simp [empty] at hRepeatable
      }
  else
    throw (.targetOutsideDeclaringGroup
      target.checked.declaration.path declaringGroup)

end A12Kernel
