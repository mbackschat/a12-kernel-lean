import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.StringComputation

/-! # Checked String-computation expression lowering

This capsule resolves parser-independent field paths in copy/literal/concatenation expressions into the existing `StringExpr FieldId` runtime tree. It admits only nonrepeatable String declarations from one validated flat model. Target policy, computations and alternatives, concrete syntax, repeatable reads, and scheduling remain outside.
-/

namespace A12Kernel

/-- Fail-closed errors owned by checked String-computation expression lowering. Keeping this domain local avoids widening validation or public reference diagnostics. -/
inductive StringComputationElabError where
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | incoherentCore
  deriving Repr, DecidableEq

namespace StringExpr

/-- Check that every runtime leaf names the exact nonrepeatable String declaration in one model. -/
def wellFormedBool (model : FlatModel) : StringExpr FieldId → Bool
  | StringExpr.field fieldId =>
      match model.lookupUniqueId fieldId with
      | .ok declaration =>
          declaration.repeatableScope.isEmpty &&
            match declaration.policy.kind with
            | .string => true
            | .number _ | .boolean | .confirm | .temporal _ _ => false
      | .error _ => false
  | StringExpr.literal _ => true
  | StringExpr.concat left right =>
      left.wellFormedBool model && right.wellFormedBool model

def WellFormed (expression : StringExpr FieldId) (model : FlatModel) : Prop :=
  expression.wellFormedBool model = true

end StringExpr

/-- A lowered String expression certified against the same model used to resolve all of its leaves. -/
structure CheckedStringExpr (model : FlatModel) where
  core : StringExpr FieldId
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- Resolve one authored String-expression tree without evaluating or reordering it. The caller supplies a validated model; each field still passes through the shared nonrepeatable path resolver. -/
def elaborateStringExprCore (model : FlatModel) (declaringGroup : GroupPath) :
    StringExpr SurfaceFieldPath →
      Except StringComputationElabError (StringExpr FieldId)
  | StringExpr.field reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
      match declaration.policy.kind with
      | .string => pure (.field declaration.id)
      | fieldKind =>
          throw (.fieldKindMismatch declaration.path fieldKind.surfaceKind)
  | StringExpr.literal value => pure (.literal value)
  | StringExpr.concat left right => do
      pure (.concat
        (← elaborateStringExprCore model declaringGroup left)
        (← elaborateStringExprCore model declaringGroup right))

/-- Validate the flat model once, preserve the authored expression tree exactly, and certify every resolved runtime leaf before returning it to computation evaluation. -/
def elaborateStringExpr (model : FlatModel) (declaringGroup : GroupPath)
    (expression : StringExpr SurfaceFieldPath) :
    Except StringComputationElabError (CheckedStringExpr model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let core ← elaborateStringExprCore model declaringGroup expression
      if hCore : core.wellFormedBool model = true then
        pure {
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

namespace CheckedStringExpr

/-- Check raw cells with the same model that certified the expression, then run only the established String evaluator. -/
def evaluate (expression : CheckedStringExpr model)
    (raw : RawFlatContext) :
    Except StringComputationFault StringStore :=
  expression.core.evaluate { read := (model.checkContext raw).read }

end CheckedStringExpr

end A12Kernel
