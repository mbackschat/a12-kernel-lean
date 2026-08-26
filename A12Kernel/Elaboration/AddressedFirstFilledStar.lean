import A12Kernel.Elaboration.StarPath

/-! # Shared exact-address first-filled star placement

This module owns the carrier-neutral placement certificates shared by exact-address Boolean and Custom first-filled computations. Carrier identity remains with each computation boundary so its diagnostic order and value domain stay explicit.
-/

namespace A12Kernel

inductive AddressedFirstFilledTargetElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  deriving Repr, DecidableEq

/-- One model-owned repeatable target in its declaring group, before any carrier-specific admission. -/
structure CheckedAddressedFirstFilledTarget (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  targetField : FieldId
  declaration : FlatFieldDecl
  owned : model.lookupUniqueId targetField = .ok declaration
  inDeclaringGroup : declaration.groupPath = declaringGroup
  repeatable : declaration.repeatableScope ≠ []

/-- Check the carrier-neutral target placement before a computation checks its own target kind. -/
def checkAddressedFirstFilledTarget
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Except AddressedFirstFilledTargetElabError
      (CheckedAddressedFirstFilledTarget model) :=
  match hTarget : model.lookupUniqueId targetField with
  | .error cause => .error (.target cause)
  | .ok declaration => do
    if hGroup : declaration.groupPath = declaringGroup then
      if hRepeatable : declaration.repeatableScope.isEmpty then
        throw (.targetNotRepeatable declaration.path)
      else
        pure {
          declaringGroup
          targetField
          declaration
          owned := hTarget
          inDeclaringGroup := hGroup
          repeatable := by
            intro empty
            simp [empty] at hRepeatable
        }
    else
      throw (.targetOutsideDeclaringGroup declaration.path declaringGroup)

inductive AddressedFirstFilledStarPlacementElabError where
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One single-axis star with a nonempty outer prefix supplied by the checked target scope and which cannot read that target. -/
structure CheckedAddressedFirstFilledStarPlacement (model : FlatModel)
    (target : CheckedAddressedFirstFilledTarget model)
    (source : CheckedStarFieldPath model) : Type where
  private mk ::
  sourceSingleReopenedAxis : source.reopenedScope.length = 1
  sourceBindingNonempty : source.bindingScope ≠ []
  sourceBindingBound :
    source.bindingScope.all target.declaration.repeatableScope.contains = true
  targetNotReferenced : source.declaration.id ≠ target.targetField

/-- Certify the carrier-neutral source placement after a computation has checked its source kind. -/
def checkAddressedFirstFilledStarPlacement
    (target : CheckedAddressedFirstFilledTarget model)
    (source : CheckedStarFieldPath model) :
    Except AddressedFirstFilledStarPlacementElabError
      (CheckedAddressedFirstFilledStarPlacement model target source) := do
  if hShape : source.reopenedScope.length = 1 then
    if hBindingEmpty : source.bindingScope.isEmpty then
      throw (.sourceScope source.declaration.path)
    else
      if hScope :
          source.bindingScope.all target.declaration.repeatableScope.contains = true then
        if hSelf : source.declaration.id = target.targetField then
          throw (.targetSelfReference target.targetField)
        else
          pure {
            sourceSingleReopenedAxis := hShape
            sourceBindingNonempty := by
              intro empty
              simp [empty] at hBindingEmpty
            sourceBindingBound := hScope
            targetNotReferenced := hSelf
          }
      else
        throw (.sourceScope source.declaration.path)
  else
    throw (.sourceShape source.declaration.path)

end A12Kernel
