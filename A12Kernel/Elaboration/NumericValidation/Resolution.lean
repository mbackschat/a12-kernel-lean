import A12Kernel.Elaboration.NumericValidation.Ordered
import A12Kernel.Elaboration.NumericValidation.ScalarResolution

/-! # Addressed numeric-comparison assembly -/

namespace A12Kernel

/-- Resolve ordinary numeric operands at any scope bound by the rule group. Fixed fields in another
subgroup or root use the same declaration certificates and evaluator as repeatable addressed reads. -/
def elaborateBoundNumericComparison
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) (declaringGroup : GroupPath := rowGroup) :
    Except NumericValidationElabError
      (CheckedOrderedNumericComparison model) := do
  let checked ← elaborateAddressedNumericComparisonCore model rowGroup surface declaringGroup
  let core : OrderedNumericComparison model := {
    op := checked.core.op
    left := checked.core.left.map .ordinary
    right := checked.core.right.map .ordinary
    suppressExactScaleWarning := checked.core.suppressExactScaleWarning }
  if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
    pure {
      rowGroup
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := checked.modelWellFormed
      wellFormed := hCore }
  else
    throw .incoherentCore


/-- Preserve the addressed-only entry point for consumers selecting a repeatable interpretation. -/
def elaborateRepeatableNumericComparison
    (model : FlatModel) (rowGroup : GroupPath) (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError (CheckedOrderedNumericComparison model) := do
  let checked ← elaborateBoundNumericComparison model rowGroup surface
  if !checked.core.requiresAddressedValidation then throw .unsupportedExpression
  pure checked


/-- Admit one filled-group count whose operand list carries at least one star, as a comparison
against a literal threshold. This is the shape the Kernel admits and the scalar carrier refuses: a
bare repeatable member is refused `MVK_NO_WILDCARD` upstream, so the star is mandatory rather than
optional, and a starred member contributes its in-capacity instantiated row count
([checkpoint](../../../docs/SOURCES.md#src-group-count-list-extent)).

The fixed-only list keeps the established scalar atom untouched and is refused here, so widening
this operator costs the already-measured form nothing; a lone star is admitted. The duplicate gate reaches every member: any
containment refuses, and equal paths refuse unless both sides are starred, which the Kernel admits
and counts once per position. `writtenGroup` is the error field's group, defaulting to the rule
group; it places a walk refusal, a star's unstarred level below its first star included, as on the
other validation carriers. -/
def elaborateMixedFilledGroupCountComparison
    (model : FlatModel) (rowGroup : GroupPath)
    (operands : List SurfaceGroupCountOperand)
    (op : NumericComparisonOp) (threshold : Int) (writtenGroup : GroupPath := rowGroup) :
    Except NumericValidationElabError
      (CheckedOrderedNumericComparison model) := do
  if (SurfaceGroupCountOperand.fixedOnly? operands).isSome then
    throw .unsupportedExpression
  let checked ← operands.mapM fun operand =>
    match operand with
    | .fixed reference => do
        let resolved ← model.resolveFixedGroupReference rowGroup reference (some writtenGroup)
          |>.mapError NumericValidationElabError.groupReference
        pure (CheckedGroupCountOperand.fixed resolved)
    | .starred path =>
        match elaborateStarredGroupOperandSource model rowGroup path with
        | .error error =>
            throw (NumericValidationElabError.starredGroupCountPlan
              (error.placeBelowStar model rowGroup writtenGroup))
        | .ok (.terminalRepeatable source) =>
            pure (CheckedGroupCountOperand.starred source)
        | .ok (.terminalPresence source) =>
            pure (CheckedGroupCountOperand.starredPresence source)
  -- Some member is starred, so a short list is a lone star, which the Kernel admits as a complete
  -- list: the arity class belongs to a lone *fixed* operand.
  if !CheckedGroupCountOperand.admittedArity checked then
    throw .unsupportedExpression
  -- Containment runs **before** rootness, and the order is measured: a root beside its own
  -- descendant draws the overlap class in either operand order, while the root class is reserved for
  -- a root beside a disjoint operand. Reversed, this reports a root the author must remove where the
  -- Kernel reports an overlap they must resolve.
  match CheckedGroupCountOperand.firstDuplicate? checked with
  | some (left, right) => throw (.overlappingGroupCountOperands left right)
  | none =>
      match checked.find? CheckedGroupCountOperand.isRoot with
      | some operand => throw (.rootGroupInGroupCount operand.groupPath)
      | none =>
          -- The list is not fixed-only, so some member is a star and its own certificate carries
          -- the model proof. Searching for it rather than requiring one from the caller keeps the
          -- entry point free of a hypothesis the surface cannot supply.
          match CheckedGroupCountOperand.modelWellFormed? checked with
          | none =>
              throw NumericValidationElabError.unsupportedExpression
          | some ⟨modelWellFormed⟩ =>
              let core : OrderedNumericComparison model := {
                op := .ordinary op
                left := .atom (.filledGroupCountMixed checked)
                right := .literal { value := (threshold : Rat), authoredScale := 0 }
                suppressExactScaleWarning := false }
              if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
                pure {
                  rowGroup
                  operandScope := .sameGroupAddressed
                  core
                  modelWellFormed
                  wellFormed := hCore }
              else
                throw NumericValidationElabError.incoherentCore

end A12Kernel
