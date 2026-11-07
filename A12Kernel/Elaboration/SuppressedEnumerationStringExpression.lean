import A12Kernel.Elaboration.SuppressedAddressedEnumerationCalculation
import A12Kernel.Elaboration.StringExpression

/-! # A suppressed Enumeration calculation from a String expression

The calculation's domain check reads one shape per alternative: it admits a declared constant, a plain read of
an Enumeration or category whose tokens the target declares, and a `FirstFilledValue` of such members, and it
refuses every other operation the generated comparison admits with `MVK_ERROR_INVALID_ENUM_CALCULATION`
([spec/09 §4.3](../../spec/09-computations.md#43-number-string-enumeration-and-custom-targets)). A
concatenation, `FieldValueAsString` or a keyed String column into an Enumeration target therefore needs the
preamble naming that class, and the target then judges the text the expression produces, exactly as it judges a
copied field: a declared token is stored, an empty text clears it, and any other text errors it
([checkpoint](../../docs/sources/kernel-31-calibration-probes.md#src-suppressed-enum-calculation-shapes),
kernel 31.3.1, fixed and repeatable targets).

The expression is the String target's own checked expression, so its reads, binding and empty-operand reading
are those a String target has; only the target's judgement differs.
-/

namespace A12Kernel

/-- The token a String store offers an Enumeration target: an empty store offers none. -/
def StringStore.asTokenResult : StringStore → TokenComputationResult
  | .noValue => .noValue
  | .poison cause => .poison cause
  | .produced value => .value value.text

/-- An Enumeration target, fixed or repeatable, computed from a checked String expression. Only its elaborator
builds one: `projection` is that of `target`. -/
structure CheckedSuppressedEnumerationStringExpression (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  projection : CheckedEnumerationProjection
  expression : CheckedBoundStringExpression model
  excludesTarget : expression.referencesField target.id = false

inductive SuppressedEnumerationStringExpressionElabError where
  | target (cause : AddressedEnumerationComputationElabError)
  | expression (cause : StringComputationElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- Admit a String expression into an Enumeration target without the domain check. Each target kind places its
refusals as its ordinary Enumeration carrier does; the expression binds at the target's group as a String
target's does. -/
def elaborateSuppressedEnumerationStringExpression (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (surface : SurfaceSelectedStringExpression) :
    Except SuppressedEnumerationStringExpressionElabError
      (CheckedSuppressedEnumerationStringExpression model) := do
  let (declaration, projection) ←
    (elaborateSuppressedEnumerationTarget model declaringGroup targetField).mapError .target
  let expression ← (elaborateSelectedBoundStringExpression model declaringGroup declaration.groupPath surface).mapError
    .expression
  if h : expression.referencesField declaration.id = false then
    pure { target := declaration, projection, expression, excludesTarget := h }
  else throw (.targetSelfReference declaration.id)

namespace CheckedSuppressedEnumerationStringExpression

def referencesField (operation : CheckedSuppressedEnumerationStringExpression model) (field : FieldId) : Bool :=
  operation.expression.referencesField field

/-- Evaluate the expression over `context`, as a String target would, then judge its text. The context alone
decides which cells the expression reads, so a key-joined caller supplies its own row binding. -/
def evaluateIn (operation : CheckedSuppressedEnumerationStringExpression model)
    (context : ScalarComputationContext) : Except StringComputationFault StringTargetOutcome := do
  let result ← operation.expression.eval .computation { read := context.read } context.numberText (some context)
  pure ((StringTerm.ofOperand result).store.asTokenResult.judgedBy operation.projection)

end CheckedSuppressedEnumerationStringExpression

end A12Kernel
