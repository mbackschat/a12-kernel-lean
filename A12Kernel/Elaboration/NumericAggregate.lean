import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.NumericAggregate

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

end A12Kernel
