import A12Kernel.Elaboration.StarPath

/-! # Shared exact-address first-filled star placement

This module owns the carrier-neutral placement certificates shared by exact-address first-filled computations. Carrier identity remains with each computation boundary so its diagnostic order and value domain stay explicit.
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

/-- One single-axis star with a nonempty outer prefix supplied by a model-owned target scope and which cannot read that target. The target carrier supplies only its already-checked identity and declaration, so Boolean, textual, temporal, and numeric targets share one placement account. -/
structure CheckedFirstFilledStarPlacement (model : FlatModel)
    (targetField : FieldId) (targetDeclaration : FlatFieldDecl)
    (source : CheckedStarFieldPath model) : Type where
  private mk ::
  targetOwned : model.lookupUniqueId targetField = .ok targetDeclaration
  targetRepeatable : targetDeclaration.repeatableScope ≠ []
  sourceSingleReopenedAxis : source.reopenedScope.length = 1
  sourceBindingNonempty : source.bindingScope ≠ []
  sourceBindingPrefix :
    source.bindingScope.isPrefixOf targetDeclaration.repeatableScope = true
  sourceBindingStrict : source.bindingScope ≠ targetDeclaration.repeatableScope
  sourceReopenedOutsideTarget :
    source.reopenedScope.all fun level =>
      !targetDeclaration.repeatableScope.contains level
  targetNotReferenced : source.declaration.id ≠ targetField

namespace CheckedFirstFilledStarPlacement

theorem sourceBindingBound
    (placement : CheckedFirstFilledStarPlacement model targetField
      targetDeclaration source) :
    source.bindingScope.all targetDeclaration.repeatableScope.contains = true := by
  rw [List.all_eq_true]
  intro level member
  rw [List.contains_iff_mem]
  exact (List.isPrefixOf_iff_prefix.mp
    placement.sourceBindingPrefix).subset member

end CheckedFirstFilledStarPlacement

/-- Compatibility specialization for the established carrier-neutral target certificate. -/
abbrev CheckedAddressedFirstFilledStarPlacement (model : FlatModel)
    (target : CheckedAddressedFirstFilledTarget model)
    (source : CheckedStarFieldPath model) : Type :=
  CheckedFirstFilledStarPlacement model target.targetField target.declaration source

/-- Certify the shared source placement from any already-checked target identity and declaration. Carrier-specific target admission remains outside this boundary. -/
def checkFirstFilledStarPlacement
    (targetField : FieldId) (targetDeclaration : FlatFieldDecl)
    (targetOwned : model.lookupUniqueId targetField = .ok targetDeclaration)
    (targetRepeatable : targetDeclaration.repeatableScope ≠ [])
    (source : CheckedStarFieldPath model) :
    Except AddressedFirstFilledStarPlacementElabError
      (CheckedFirstFilledStarPlacement model targetField targetDeclaration source) := do
  if hShape : source.reopenedScope.length = 1 then
    if hBindingEmpty : source.bindingScope.isEmpty then
      throw (.sourceScope source.declaration.path)
    else
      if hPrefix :
          source.bindingScope.isPrefixOf targetDeclaration.repeatableScope then
        if hStrict : source.bindingScope = targetDeclaration.repeatableScope then
          throw (.sourceScope source.declaration.path)
        else
          if hSelf : source.declaration.id = targetField then
            throw (.targetSelfReference targetField)
          else
            if hSibling : source.reopenedScope.all fun level =>
                !targetDeclaration.repeatableScope.contains level then
              pure {
                targetOwned
                targetRepeatable
                sourceSingleReopenedAxis := hShape
                sourceBindingNonempty := by
                  intro empty
                  simp [empty] at hBindingEmpty
                sourceBindingPrefix := hPrefix
                sourceBindingStrict := hStrict
                sourceReopenedOutsideTarget := hSibling
                targetNotReferenced := hSelf
              }
            else
              throw (.sourceScope source.declaration.path)
      else
        throw (.sourceScope source.declaration.path)
  else
    throw (.sourceShape source.declaration.path)

/-- Certify the carrier-neutral source placement after a computation has checked its source kind. -/
def checkAddressedFirstFilledStarPlacement
    (target : CheckedAddressedFirstFilledTarget model)
    (source : CheckedStarFieldPath model) :
    Except AddressedFirstFilledStarPlacementElabError
      (CheckedAddressedFirstFilledStarPlacement model target source) := do
  checkFirstFilledStarPlacement target.targetField target.declaration target.owned
    target.repeatable source

end A12Kernel
