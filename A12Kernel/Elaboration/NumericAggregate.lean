import A12Kernel.Elaboration.Correlation
import A12Kernel.Semantics.StarCompleteness

/-! # Checked nonrepeatable Number aggregate lowering

This capsule resolves one nonempty, unfiltered list of nonrepeatable Number fields into the existing aggregate sides. It preserves authored encounter order and declaration signedness, and classifies raw cells through the same validated flat model. Stars, group expansion, `Having`, partial relevance, comparisons, computation aggregates, and concrete syntax remain outside.
-/

namespace A12Kernel

/-- A parser-independent nonempty Number aggregate field list. -/
structure SurfaceNumericAggregateFields where
  first : SurfaceFieldPath
  rest : List SurfaceFieldPath
  deriving Repr, DecidableEq

/-- Fail-closed errors owned by this aggregate-field lowering boundary. -/
inductive NumericAggregateElabError where
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A nonempty resolved field list certified against one flat model. -/
structure CheckedNumericAggregateFields (model : FlatModel) where
  first : FlatNumberField
  rest : List FlatNumberField
  modelWellFormed : model.validate.isOk = true
  fieldsWellFormed :
    (model.admitsField (.number first) &&
      rest.all fun field => model.admitsField (.number field)) = true

namespace CheckedNumericAggregateFields

def fields (checked : CheckedNumericAggregateFields model) : List FlatNumberField :=
  checked.first :: checked.rest

end CheckedNumericAggregateFields

private def FlatModel.resolveNumericAggregateField (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except NumericAggregateElabError FlatNumberField := do
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
  match declaration.toNumberField? with
  | some field => pure field
  | none =>
      throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)

private def FlatModel.resolveNumericAggregateFields (model : FlatModel)
    (declaringGroup : GroupPath) :
    List SurfaceFieldPath → Except NumericAggregateElabError (List FlatNumberField)
  | [] => pure []
  | reference :: remaining => do
      pure ((← model.resolveNumericAggregateField declaringGroup reference) ::
        (← model.resolveNumericAggregateFields declaringGroup remaining))

/-- Validate the model once, resolve every source in authored order, and certify the complete nonempty Number list. -/
def elaborateNumericAggregateFields (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceNumericAggregateFields) :
    Except NumericAggregateElabError (CheckedNumericAggregateFields model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let first ← model.resolveNumericAggregateField declaringGroup authored.first
      let rest ← model.resolveNumericAggregateFields declaringGroup authored.rest
      if hFields :
          (model.admitsField (.number first) &&
            rest.all fun field => model.admitsField (.number field)) = true then
        pure {
          first
          rest
          modelWellFormed := by
            rw [hModel]
            rfl
          fieldsWellFormed := hFields
        }
      else
        throw .incoherentCore

namespace CheckedNumericAggregateFields

private def classify (context : FlatContext)
    (field : FlatNumberField) : ValueListCell .number :=
  match context.observeValidationAt field.id with
  | .empty => .empty
  | .value (.num amount) => .present amount
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- Construct the common resolved subset: explicit nonrepeatable cells in authored order, no uninstantiated source, and no filter. -/
def resolvedValueSide (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : ResolvedValueListSide .number :=
  let context := model.checkContext raw
  { cells := checked.fields.map fun field => classify context field
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Retain each source declaration's signedness for `Sum` polarity. -/
def resolvedSumSide (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : ResolvedNumericSumSide :=
  let context := model.checkContext raw
  { cells := checked.fields.map fun field =>
      { cell := classify context field
        declarationSigned := field.info.signed }
    uninstantiatedSignedness := []
    hasHaving := false }

/-- Evaluate `Sum` by delegating the constructed side to the existing per-declaration semantics. -/
def evaluateSum (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : NumericOperand :=
  evalDeclaredNumericSumAggregate (checked.resolvedSumSide raw)

/-- Evaluate direct `MinValue` or `MaxValue` by delegating the same checked sources to the existing extremum semantics. -/
def evaluateExtremum (checked : CheckedNumericAggregateFields model)
    (op : NumericExtremumOp) (raw : RawFlatContext) : NumericOperand :=
  evalNumericExtremumAggregate op (checked.resolvedValueSide raw)

end CheckedNumericAggregateFields

/-! ## One checked Number star -/

/-- Fail-closed errors owned by the one-star Number aggregate lowering boundary. -/
inductive NumericStarAggregateElabError where
  | star (error : CorrelationElabError)
  | repeatabilityUnavailable (path : GroupPath)
  | invalidRepeatability (path : GroupPath) (repeatability : Nat)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One Number star certified against its model declaration and finite capacity. -/
structure CheckedNumericStarAggregate (model : FlatModel) where
  group : RepeatableGroupDecl
  field : FlatNumberField
  repeatability : Nat
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  fieldOwned : model.admitsSingleGroupNumber group field = true
  repeatabilityOwned : group.repeatability = some repeatability
  repeatabilityValid : 0 < repeatability

/-- Validate the model once, bind the exact starred group and direct-child Number field, and require its declared finite capacity. -/
def elaborateNumericStarAggregate (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceSingleStarFieldPath) :
    Except NumericStarAggregateElabError (CheckedNumericStarAggregate model) :=
  match hModel : model.validate with
  | .error error => .error (.star (.resolve error))
  | .ok () => do
      let groupReference ← source.groupReference |>.mapError .star
      let groupPath ← groupReference.resolveAgainst declaringGroup |>.mapError .star
      let group ← model.lookupUniqueRepeatablePath groupPath |>.mapError (.star ∘ .resolve)
      let fieldReference : SurfaceFieldPath :=
        { base := .absolute, groups := group.path, field := source.field }
      let (_, field) ←
        model.resolveNumberFieldInGroup declaringGroup group fieldReference |>.mapError .star
      match hRepeatabilityOwned : group.repeatability with
      | none => throw (.repeatabilityUnavailable group.path)
      | some repeatability =>
          if hRepeatability : 0 < repeatability then
            if hGroup : model.repeatableGroups.contains group = true then
              if hField : model.admitsSingleGroupNumber group field = true then
                pure {
                  group
                  field
                  repeatability
                  modelWellFormed := by
                    rw [hModel]
                    rfl
                  groupOwned := hGroup
                  fieldOwned := hField
                  repeatabilityOwned := hRepeatabilityOwned
                  repeatabilityValid := hRepeatability
                }
              else
                throw .incoherentCore
            else
              throw .incoherentCore
          else
            throw (.invalidRepeatability group.path repeatability)

/-- Runtime topology errors at the checked finite one-star boundary. -/
inductive NumericStarContextError where
  | topology (error : SingleGroupContextError)
  | noncontiguousCandidates (candidates : List RowIndex)
  | exceedsRepeatability (actual repeatability : Nat)
  deriving Repr, DecidableEq

namespace CheckedNumericStarAggregate

private def expectedCandidates (count : Nat) : List RowIndex :=
  (List.range count).map (· + 1)

/-- Require the instantiated rows to be the unique 1-based prefix of the declared finite domain. -/
def validateContext (checked : CheckedNumericStarAggregate model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError Unit := do
  raw.validate |>.mapError .topology
  if raw.candidates.length > checked.repeatability then
    throw (.exceedsRepeatability raw.candidates.length checked.repeatability)
  if raw.candidates != expectedCandidates raw.candidates.length then
    throw (.noncontiguousCandidates raw.candidates)

/-- Represent the instantiated deepest rows of this one-level checked star. -/
def selectedRows : List RowIndex → ReopenedStarRows
  | [] => .nil
  | row :: rest => .cons row .selectedLeaf (selectedRows rest)

/-- Construct the common resolved side from checked row order, exact cell classification, and the model-owned omitted tail. -/
def resolvedValueSide (checked : CheckedNumericStarAggregate model)
    (raw : RawSingleGroupContext) : ResolvedValueListSide .number :=
  let context := model.checkSingleGroupContext checked.group raw
  let domain := ReopenedStarDomain.repeatable (some checked.repeatability)
    (selectedRows raw.candidates)
  domain.toResolvedSide
    (raw.candidates.map fun row => checked.field.valueListCell (context.atRow row))

/-- Evaluate one checked Number star through the existing declaration-signed Sum semantics. -/
def evaluateSum (checked : CheckedNumericStarAggregate model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError NumericOperand := do
  checked.validateContext raw
  pure (evalNumericSumAggregate checked.field.info.signed (checked.resolvedValueSide raw))

/-- Evaluate one checked Number star through the existing extremum semantics. -/
def evaluateExtremum (checked : CheckedNumericStarAggregate model)
    (op : NumericExtremumOp) (raw : RawSingleGroupContext) :
    Except NumericStarContextError NumericOperand := do
  checked.validateContext raw
  pure (evalNumericExtremumAggregate op (checked.resolvedValueSide raw))

end CheckedNumericStarAggregate

end A12Kernel
