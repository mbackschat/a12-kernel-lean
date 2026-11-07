import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.SuppressedEnumerationCalculation

/-! # A suppressed Enumeration calculation on a repeatable target

A repeatable Enumeration target computed from a direct field under the preamble that lifts
`MVK_ERROR_INVALID_ENUM_CALCULATION` ([spec/09 §4.3](../../spec/09-computations.md#43-number-string-enumeration-and-custom-targets)).
Each target row reads its own source cell and the target judges that token as a fixed target does
(`CheckedSuppressedEnumerationCalculation`), measured on kernel 31.3.1 from a String field source
([checkpoint](../../docs/sources/kernel-31-calibration-probes.md#src-suppressed-enum-calculation-shapes), row `r01`).

This is a separate operation from `CheckedAddressedEnumerationComputation`, whose `sourceAllowed`
certificate the proofs under `A12Kernel/Proofs/` rely on.
-/

namespace A12Kernel

/-- The Enumeration target of a suppressed calculation, placed and refused as its ordinary carrier places it:
a fixed target through the fixed target check, a repeatable one through the addressed one. -/
def elaborateSuppressedEnumerationTarget (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Except AddressedEnumerationComputationElabError (FlatFieldDecl × CheckedEnumerationProjection) := do
  let declaration ← (model.lookupUniqueId targetField).mapError fun cause => .ordinary (.resolve cause)
  if declaration.repeatableScope.isEmpty then
    let target ← (elaborateEnumerationComputationTarget model targetField).mapError .ordinary
    pure (declaration, target.projection)
  else
    let target ← checkAddressedEnumerationTarget model declaringGroup targetField
    pure (declaration, target.projection)

/-- A repeatable Enumeration target computed from a direct field whose tokens the target need not declare. -/
structure CheckedSuppressedAddressedEnumerationCalculation (model : FlatModel) where
  target : CheckedAddressedEnumerationTarget model
  sourceDeclaration : FlatFieldDecl
  source : FlatTextFieldOperand
  sourceOwned : sourceDeclaration.resolvesTextOperand source = true
  scopeBound : sourceDeclaration.repetitionBoundBy target.declaration.repeatableScope = true
  targetNotReferenced : (sourceDeclaration.id == target.field) = false

/-- Admit a direct String or Enumeration field source into a repeatable Enumeration target without the
domain check. The caller reaches this only after the ordinary elaboration refused the source with the
calculation's own class, so every gate that answers ahead of it, the generated comparison's, the read's
and the scope's included, has already passed. -/
def elaborateSuppressedAddressedEnumerationCalculation (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (authored : SurfaceTextFieldOperand) :
    Except AddressedEnumerationComputationElabError
      (CheckedSuppressedAddressedEnumerationCalculation model) := do
  let target ← checkAddressedEnumerationTarget model declaringGroup targetField
  let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup authored.reference).mapError
    fun cause => .ordinary (.source (.resolve cause))
  let operand? : Option FlatTextFieldOperand := match authored with
    | .direct _ => declaration.toTextFieldComparison?
    | .category _ name => declaration.toEnumerationTextFieldComparison? (.category name)
  let some source := operand?
    | throw (.ordinary (.source
        (.textFieldOperandKindMismatch declaration.path declaration.policy.kind.surfaceKind)))
  if hScope : declaration.repetitionBoundBy target.declaration.repeatableScope = true then
    if hOwned : declaration.resolvesTextOperand source = true then
      if hSelf : (declaration.id == target.field) = false then
        pure {
          target
          sourceDeclaration := declaration
          source
          sourceOwned := hOwned
          scopeBound := hScope
          targetNotReferenced := hSelf
        }
      else throw (.ordinary (.targetSelfReference target.field))
    else throw (.ordinary .incoherentCore)
  else throw (.scopeMismatch target.declaration.path declaration.path)

namespace CheckedSuppressedAddressedEnumerationCalculation

def referencesField (operation : CheckedSuppressedAddressedEnumerationCalculation model)
    (field : FieldId) : Bool :=
  operation.sourceDeclaration.id == field

/-- Judge the source cell the target row's environment places, through the caller's read view. -/
def evaluateAtWithRead (operation : CheckedSuppressedAddressedEnumerationCalculation model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env) :
    Except AddressedEnumerationComputationFault StringTargetOutcome := do
  let sourcePath ← environment.pathForScope operation.sourceDeclaration.repeatableScope
    |>.mapError .environment
  let cell ← read { field := operation.sourceDeclaration.id, path := sourcePath } |>.mapError .sourceRead
  pure (CheckedSuppressedEnumerationCalculation.judge operation.target.projection
    (operation.source.checkedValueListCellAt .computation cell))

end CheckedSuppressedAddressedEnumerationCalculation

end A12Kernel
