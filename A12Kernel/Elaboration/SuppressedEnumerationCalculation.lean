import A12Kernel.Elaboration.EnumerationComputation

/-! # A suppressed Enumeration calculation

A computation whose preamble names `MVK_ERROR_INVALID_ENUM_CALCULATION` lifts the static check that a
source's tokens lie in its Enumeration target's domain
([spec/09 §4.3](../../spec/09-computations.md#43-number-string-enumeration-and-custom-targets)). The target
then judges each attempted text at runtime: a token it declares is stored, an empty text clears it, and any
other text, a declared value's label included, leaves it errored without a message. That runtime is
measured for a String field source on both strategies (a12-dmkits KF298, 31.3.1 Letter J §5); an
Enumeration or category source whose tokens leave the target's domain is judged by the same target check,
derived and unmeasured.

This is a checked operation of its own rather than a weakening of
`CheckedEnumerationComputationOperation`, whose static domain certificate the exact-token projection and
its laws rely on.
-/

namespace A12Kernel

namespace TokenComputationResult

/-- The target's own judgement of one selected token once a preamble lifted the static domain check: a
token it declares is stored, an empty text clears it, and any other text, a declared value's label
included, leaves it errored. A rejected attempt's cause is never observed, since the Kernel reports no
message for it; it is recorded as the pattern class an unrecognized token draws where a document cell is
read. A poisoned selection poisons the target, as the ordinary projection has it. -/
def judgedBy (target : CheckedEnumerationProjection) : TokenComputationResult → StringTargetOutcome
  | .noValue => .noValue
  | .poison cause => .poison cause
  | .value token =>
      if nonempty : token ≠ "" then
        if target.declaration.literalAllowed target.projection token then .accepted { text := token, nonempty }
        else .errored { text := token, nonempty } .pattern
      else .noValue

end TokenComputationResult

/-- A fixed Enumeration target computed from a direct field whose tokens the target need not declare. -/
structure CheckedSuppressedEnumerationCalculation (model : FlatModel) where
  target : CheckedEnumerationComputationTarget model
  sourcePath : List String
  source : FlatTextFieldOperand
  targetNotReferenced : (source.field.id == target.field) = false

namespace CheckedSuppressedEnumerationCalculation

/-- Judge one computation-phase source cell against the target's declared domain. -/
def judge (target : CheckedEnumerationProjection) (cell : ValueListCell .token) : StringTargetOutcome :=
  let selected : TokenComputationResult := match cell with
    | .empty => .noValue
    | .unknown cause => .poison cause
    | .present token => .value token
  selected.judgedBy target

def evaluate (operation : CheckedSuppressedEnumerationCalculation model) (context : FlatContext) :
    StringTargetOutcome :=
  judge operation.target.projection
    (operation.source.checkedValueListCellAt .computation (context.read operation.source.field.id))

end CheckedSuppressedEnumerationCalculation

/-- Admit a direct String or Enumeration field source into a fixed Enumeration target without the domain
check. The caller reaches this only after the ordinary elaboration refused the source with the calculation's
own class, so every gate that answers ahead of it, the generated comparison's and self-reference
included, has already passed. -/
def elaborateSuppressedEnumerationCalculation (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (authored : SurfaceTextFieldOperand) :
    Except EnumerationComputationElabError (CheckedSuppressedEnumerationCalculation model) := do
  let target ← elaborateEnumerationComputationTarget model targetField
  let stringSource? : Option (List String × FlatTextFieldOperand) := match authored with
    | .direct reference =>
        match model.resolveProjectedFieldValueRead declaringGroup reference .stored with
        | .ok declaration => match declaration.toTextFieldComparison? with
            | some (.string field) => some (declaration.path, .string field)
            | _ => none
        | .error _ => none
    | .category .. => none
  let (sourcePath, source) ← match stringSource? with
    | some found => pure found
    | none => do
        let (path, _, operand) ←
          (elaborateEnumerationFieldOperand model declaringGroup authored).mapError .source
        pure (path, FlatTextFieldOperand.enumeration operand)
  if h : (source.field.id == target.field) = false then
    pure { target, sourcePath, source, targetNotReferenced := h }
  else throw (.targetSelfReference target.field)

end A12Kernel
