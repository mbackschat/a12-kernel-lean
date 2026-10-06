import A12Kernel.Elaboration.StringExpression
import A12Kernel.Elaboration.StringContext

namespace A12Kernel

inductive ComputationStringPatternElabError where
  | field (error : StringComputationElabError)
  | pattern (error : PatternAdmissionError)
  deriving Repr, DecidableEq

/-- A direct String read and its exact admitted matcher share one checked target scope.
The private constructor preserves the pattern comparison's direct-field restriction
([entry gates](../../docs/sources/static-admission-and-class-probes.md#src-comparison-entry-gates)). -/
structure CheckedComputationStringPattern (model : FlatModel) where
  private mk ::
  source : CheckedBoundStringExpression model
  op : StringPatternOp
  compilePattern : StringPatternCompiler
  pattern : AdmittedStringPattern compilePattern

def elaborateComputationStringPattern (compilePattern : StringPatternCompiler)
    (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (surface : SurfaceStringPatternCondition) :
    Except ComputationStringPatternElabError (CheckedComputationStringPattern model) := do
  let source ← (elaborateBoundStringExpression model declaringGroup targetGroup
    (.field surface.field)).mapError .field
  let pattern ← (admitStringPattern compilePattern surface.source).mapError .pattern
  pure { source, op := surface.op, compilePattern, pattern }

def CheckedComputationStringPattern.eval (checked : CheckedComputationStringPattern model)
    (context : FlatContext) : Except StringComputationFault ComputationConditionResult := do
  let value ← checked.source.eval .computation context (fun _ => none)
  pure (checked.op.evalComputationResolved checked.pattern.wholeValueMatches value)

/-- Preserve the admitted matcher when the validation row binds the source. -/
def CheckedComputationStringPattern.toValidation?
    (checked : CheckedComputationStringPattern model) (rowGroup : GroupPath) :
    Option (CheckedStringPatternLeaf model) := do
  let .field (.inl fieldId) := checked.source.core | none
  let field : FlatStringField := { id := fieldId }
  if !(model.fieldRepeatableScope fieldId).isPrefixOf (model.repeatableScopeForGroupPath rowGroup) then none
  if hField : model.admitsStringPatternField field = true then
    some { compilePattern := checked.compilePattern, condition := {
      rowGroup, op := checked.op, field, pattern := checked.pattern
      modelWellFormed := checked.source.modelWellFormed, fieldWellFormed := hField } }
  else none

end A12Kernel
