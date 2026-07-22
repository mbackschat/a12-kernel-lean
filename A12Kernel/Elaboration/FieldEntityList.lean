import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.StarPath

/-! # Shared checked field entity-list shape

This boundary owns the kind-independent authoring shape shared by ordinary aggregate field lists. It resolves direct, plain-star, and filtered-star slots in authored order, rejects only repeated direct fields, and requires either multiple slots or one starred slot. Family-specific modules certify the resolved declarations and retain their own runtime semantics.
-/

namespace A12Kernel

/-- One parser-independent field entity-list slot. A filter belongs to its exact authored wildcard occurrence. -/
inductive SurfaceFieldEntityOperand where
  | field (path : SurfaceFieldPath)
  | star (path : SurfaceStarFieldPath)
  | starHaving (path : SurfaceStarFieldPath) (having : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

/-- A nonempty authored field entity list. Checked construction separately enforces that a sole operand is starred. -/
structure SurfaceFieldEntitySource where
  first : SurfaceFieldEntityOperand
  rest : List SurfaceFieldEntityOperand
  deriving Repr, DecidableEq

/-- One kind-neutral resolved slot. Family-specific certification occurs only after the complete list has passed duplicate and cardinality checks. -/
inductive ResolvedFieldEntityOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
  | star (source : CheckedStarFieldPath model)
  | starHaving (source : CheckedStarFieldPath model)
      (having : SurfaceCorrelatedHaving)

namespace ResolvedFieldEntityOperand

def isStar : ResolvedFieldEntityOperand model → Bool
  | .field _ => false
  | .star _ | .starHaving _ _ => true

def directFieldId? : ResolvedFieldEntityOperand model → Option FieldId
  | .field declaration => some declaration.id
  | .star _ | .starHaving _ _ => none

end ResolvedFieldEntityOperand

/-- The source-shape failures shared by every homogeneous aggregate family. -/
inductive FieldEntityShapeElabError where
  | resolve (error : ResolveError)
  | starPath (error : StarPathElabError)
  | tooFewFields
  | duplicateOperand (field : FieldId)
  deriving Repr, DecidableEq

def firstDuplicateDirectField? (directFieldId? : α → Option FieldId) :
    List α → Option FieldId
  | [] => none
  | operand :: remaining =>
      match directFieldId? operand with
      | none => firstDuplicateDirectField? directFieldId? remaining
      | some field =>
          if remaining.any fun candidate => directFieldId? candidate == some field then
            some field
          else
            firstDuplicateDirectField? directFieldId? remaining

def firstDuplicateResolvedDirectField? :
    List (ResolvedFieldEntityOperand model) → Option FieldId
  | operands => firstDuplicateDirectField?
      (fun operand => operand.directFieldId?) operands

/-- A resolved, model-owned entity-list shape before homogeneous family certification. -/
structure CheckedFieldEntityShape (model : FlatModel) where
  first : ResolvedFieldEntityOperand model
  rest : List (ResolvedFieldEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateResolvedDirectField? (first :: rest) = none

namespace CheckedFieldEntityShape

def operands (checked : CheckedFieldEntityShape model) :
    List (ResolvedFieldEntityOperand model) :=
  checked.first :: checked.rest

end CheckedFieldEntityShape

private def resolveFieldEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) : SurfaceFieldEntityOperand →
      Except FieldEntityShapeElabError (ResolvedFieldEntityOperand model)
  | .field path => do
      let declaration ← model.resolveNonrepeatableFieldUnchecked declaringGroup path
        |>.mapError .resolve
      pure (.field declaration)
  | .star path => do
      pure (.star (← elaborateStarFieldPath model declaringGroup path
        |>.mapError .starPath))
  | .starHaving path having => do
      pure (.starHaving
        (← elaborateStarFieldPath model declaringGroup path
          |>.mapError .starPath)
        having)

private def resolveFieldEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List SurfaceFieldEntityOperand →
      Except FieldEntityShapeElabError
        (List (ResolvedFieldEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolveFieldEntityOperand model declaringGroup operand) ::
        (← resolveFieldEntityOperands model declaringGroup remaining))

/-- Validate the common entity-list shape in kernel order: model, path resolution, repeated direct fields, then the multiple-fields-or-star cardinality gate. -/
def elaborateFieldEntityShape (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except FieldEntityShapeElabError (CheckedFieldEntityShape model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let first ← resolveFieldEntityOperand model declaringGroup authored.first
      let rest ← resolveFieldEntityOperands model declaringGroup authored.rest
      match hDuplicate : firstDuplicateResolvedDirectField? (first :: rest) with
      | some field => throw (.duplicateOperand field)
      | none =>
          if hMultiplicity : first.isStar || !rest.isEmpty then
            pure {
              first
              rest
              modelWellFormed := by rw [hModel]; rfl
              requiredMultiplicity := hMultiplicity
              uniqueDirectOperands := hDuplicate }
          else
            throw .tooFewFields

end A12Kernel
