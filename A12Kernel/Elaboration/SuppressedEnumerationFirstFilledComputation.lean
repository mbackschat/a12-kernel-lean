import A12Kernel.Elaboration.SuppressedAddressedEnumerationCalculation
import A12Kernel.Elaboration.StringFirstFilledComputation

/-! # A suppressed Enumeration calculation from `FirstFilledValue`

An Enumeration target, fixed or repeatable, computed from `FirstFilledValue` whose members the calculation's
domain check refuses: a String member, an Enumeration or category member whose tokens leave the target's domain,
or a starred walk of either, under the preamble that lifts `MVK_ERROR_INVALID_ENUM_CALCULATION`
([spec/09 §4.3](../../spec/09-computations.md#43-number-string-enumeration-and-custom-targets)). The members
are scanned as a String target's `FirstFilledValue` scans them, so an Enumeration member offers its stored
token and an earlier member holding an undeclared token is still the one selected; the target then judges that
one token (`TokenComputationResult.judgedBy`), and a rejected token never falls through to a later member.
Kernel 31.3.1 measures this on fixed and repeatable targets over String members, a mixed String and
Enumeration list and a starred String walk
([checkpoint](../../docs/sources/kernel-31-calibration-probes.md#src-suppressed-enum-calculation-shapes)).

This is a separate operation from the two ordinary Enumeration `FirstFilledValue` computations, whose
`sourceAllowed` certificates the proofs under `A12Kernel/Proofs/` rely on.
-/

namespace A12Kernel

/-- One `FirstFilledValue` computation into an Enumeration target whose members the target need not declare,
over a fixed or a repeatable target. Only its elaborator builds one: `projection` is that of `target`. -/
structure CheckedSuppressedEnumerationFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  projection : CheckedEnumerationProjection
  source : CheckedTokenEntitySource model
  targetNotReferenced : source.referencesField target.id (fun having _ => having.forbidsTarget target.id) = false

inductive SuppressedEnumerationFirstFilledElabError where
  | target (cause : AddressedEnumerationComputationElabError)
  | source (cause : TokenEntityElabError)
  | unsupportedSourceCarrier (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- Admit a String-like member list into an Enumeration target without the domain check. The caller reaches
this only after the ordinary elaboration refused a member with the calculation's own class, so every gate that
answers ahead of it has already passed. Each target kind places its refusals as its ordinary carrier does, and
the members bind as a String target's do. -/
def elaborateSuppressedEnumerationFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceTokenEntitySource) (arity : EntityListArity := .manyRequired) :
    Except SuppressedEnumerationFirstFilledElabError
      (CheckedSuppressedEnumerationFirstFilledComputation model) := do
  let (declaration, projection) ←
    (elaborateSuppressedEnumerationTarget model declaringGroup targetField).mapError .target
  let source ← (elaborateTokenEntitySource model declaringGroup authored arity
      (fixedTargetGroup? := some declaration.groupPath) (admitRaw := true)).mapError .source
  if let some other := (source.operands.flatMap (·.declarations)).find? (!·.isStringFirstFilledSource) then
    throw (.unsupportedSourceCarrier other.path)
  if h : source.referencesField declaration.id (fun having _ => having.forbidsTarget declaration.id) = false then
    pure { target := declaration, projection, source, targetNotReferenced := h }
  else throw (.targetSelfReference declaration.id)

namespace CheckedSuppressedEnumerationFirstFilledComputation

def referencesWith (operation : CheckedSuppressedEnumerationFirstFilledComputation model)
    (field : FieldId) (filterReads : CorrelatedHaving → Bool) : Bool :=
  operation.source.referencesField field (fun having _ => filterReads having)

/-- Scan the members for the target instance `environment` names, as a String target's computation does,
then judge the one token it selects. Filter failures stay with the caller's handler. -/
def evaluateAtWithRead (operation : CheckedSuppressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (world : Option World := none) :
    Except StringFirstFilledComputationFault StringTargetOutcome := do
  let selected ← operation.source.computationFirstFilledToken input read environment world
  pure (selected.asComputationResult.judgedBy operation.projection)

end CheckedSuppressedEnumerationFirstFilledComputation

end A12Kernel
