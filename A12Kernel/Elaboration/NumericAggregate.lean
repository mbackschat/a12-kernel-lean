import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.NumericAggregate

/-! # Checked nonrepeatable Number Sum lowering

This capsule resolves one nonempty, unfiltered list of nonrepeatable Number fields into the existing per-declaration Sum side. It preserves authored encounter order and declaration signedness, and classifies raw cells through the same validated flat model. Stars, group expansion, `Having`, partial relevance, comparisons, computation aggregates, and concrete syntax remain outside.
-/

namespace A12Kernel

/-- A parser-independent nonempty Number `Sum` field list. -/
structure SurfaceNumericSum where
  first : SurfaceFieldPath
  rest : List SurfaceFieldPath
  deriving Repr, DecidableEq

/-- Fail-closed errors owned by this aggregate lowering boundary. -/
inductive NumericSumElabError where
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A nonempty resolved field list certified against one flat model. -/
structure CheckedNumericSum (model : FlatModel) where
  first : FlatNumberField
  rest : List FlatNumberField
  modelWellFormed : model.validate.isOk = true
  fieldsWellFormed :
    (model.admitsField (.number first) &&
      rest.all fun field => model.admitsField (.number field)) = true

namespace CheckedNumericSum

def fields (sum : CheckedNumericSum model) : List FlatNumberField :=
  sum.first :: sum.rest

end CheckedNumericSum

private def FlatModel.resolveNumericSumField (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except NumericSumElabError FlatNumberField := do
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
  match declaration.toNumberField? with
  | some field => pure field
  | none =>
      throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)

private def FlatModel.resolveNumericSumFields (model : FlatModel)
    (declaringGroup : GroupPath) :
    List SurfaceFieldPath → Except NumericSumElabError (List FlatNumberField)
  | [] => pure []
  | reference :: remaining => do
      pure ((← model.resolveNumericSumField declaringGroup reference) ::
        (← model.resolveNumericSumFields declaringGroup remaining))

/-- Validate the model once, resolve every source in authored order, and certify the complete nonempty Number list. -/
def elaborateNumericSum (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceNumericSum) :
    Except NumericSumElabError (CheckedNumericSum model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let first ← model.resolveNumericSumField declaringGroup authored.first
      let rest ← model.resolveNumericSumFields declaringGroup authored.rest
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

namespace CheckedNumericSum

private def classify (context : FlatContext)
    (field : FlatNumberField) : ValueListCell .number :=
  match context.observeValidationAt field.id with
  | .empty => .empty
  | .value (.num amount) => .present amount
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- Construct the exact resolved subset: explicit nonrepeatable cells in authored order, no uninstantiated source, and no filter. -/
def resolvedSide (sum : CheckedNumericSum model)
    (raw : RawFlatContext) : ResolvedNumericSumSide :=
  let context := model.checkContext raw
  { cells := sum.fields.map fun field =>
      { cell := classify context field
        declarationSigned := field.info.signed }
    uninstantiatedSignedness := []
    hasHaving := false }

/-- Evaluate by delegating the constructed side to the existing per-declaration Sum semantics. -/
def evaluate (sum : CheckedNumericSum model)
    (raw : RawFlatContext) : NumericOperand :=
  evalDeclaredNumericSumAggregate (sum.resolvedSide raw)

end CheckedNumericSum

end A12Kernel
