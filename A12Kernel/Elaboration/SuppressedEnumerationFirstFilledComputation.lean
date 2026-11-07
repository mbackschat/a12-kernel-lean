import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation
import A12Kernel.Elaboration.SuppressedEnumerationCalculation

/-! # A suppressed Enumeration calculation from `FirstFilledValue`

An Enumeration target, fixed or repeatable, computed from `FirstFilledValue` whose Enumeration or category
members leave the target's domain, under the preamble that lifts `MVK_ERROR_INVALID_ENUM_CALCULATION`
([spec/09 §4.3](../../spec/09-computations.md#43-number-string-enumeration-and-custom-targets)).
The ordinary scan selects the first filled token, an earlier member holding an undeclared token included,
and the target then judges that one token (`TokenComputationResult.judgedBy`); a rejected token never
falls through to a later member. The runtime is measured on a fixed target from a String field source
(a12-dmkits KF298, 31.3.1 Letter J §5); this carrier selects as the unsuppressed one does and judges as
that carrier does, derived and unmeasured. A String member keeps the calculation's refusal, since the
checked slot of this source carries Enumeration projections only.

This is a separate operation from the two ordinary Enumeration `FirstFilledValue` computations, whose
`sourceAllowed` certificates the proofs under `A12Kernel/Proofs/` rely on.
-/

namespace A12Kernel

/-- One Enumeration `FirstFilledValue` computation whose members the target need not declare, over a fixed
or a repeatable target. Only its elaborator builds one: `projection` is that of `target`. -/
structure CheckedSuppressedEnumerationFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  projection : CheckedEnumerationProjection
  source : CheckedEnumerationFirstFilledSource model target.repeatableScope
  targetNotReferenced : source.referencesWith target.id (·.forbidsTarget target.id) = false

/-- Admit the shared first-filled source into an Enumeration target without the domain check. The caller
reaches this only after the ordinary elaboration refused a member with the calculation's own class, so
every gate that answers ahead of it, the source's shape and the self-read's included, has already passed.
Each target kind places its refusals as its ordinary carrier does. -/
def elaborateSuppressedEnumerationFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceEnumerationFirstFilledSource) (arity : EntityListArity := .manyRequired) :
    Except AddressedEnumerationFirstFilledComputationElabError
      (CheckedSuppressedEnumerationFirstFilledComputation model) := do
  let declaration ← (model.lookupUniqueId targetField).mapError fun cause =>
    .target (.ordinary (.resolve cause))
  let (projection, targetGroup, bindingGroup) ←
    if declaration.repeatableScope.isEmpty then do
      let target ← (elaborateEnumerationComputationTarget model targetField).mapError
        fun cause => .target (.ordinary cause)
      pure (target.projection, target.path.dropLast, target.path.dropLast)
    else do
      let target ← (checkAddressedEnumerationTarget model declaringGroup targetField).mapError .target
      pure (target.projection, declaringGroup, target.declaration.groupPath)
  let source ← (elaborateEnumerationFirstFilledSource model declaringGroup declaration.repeatableScope
      authored targetGroup bindingGroup arity).mapError .source
  if h : source.referencesWith declaration.id (·.forbidsTarget declaration.id) = false then
    pure { target := declaration, projection, source, targetNotReferenced := h }
  else throw (.targetSelfReference declaration.id)

namespace CheckedSuppressedEnumerationFirstFilledComputation

def referencesWith (operation : CheckedSuppressedEnumerationFirstFilledComputation model)
    (field : FieldId) (filterReads : CorrelatedHaving → Bool) : Bool :=
  operation.source.referencesWith field filterReads

/-- Scan the members for the target instance `environment` names, as the ordinary computation does,
then judge the one token it selects. Filter failures stay with the caller's handler. -/
def evaluateAtWithRead (operation : CheckedSuppressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (world : Option World := none) :
    Except CheckedAddressingError StringTargetOutcome := do
  let selected ← operation.source.evaluateCheckedDocumentWithRead (world := world) input read environment
  pure (selected.asComputationResult.judgedBy operation.projection)

end CheckedSuppressedEnumerationFirstFilledComputation

end A12Kernel
