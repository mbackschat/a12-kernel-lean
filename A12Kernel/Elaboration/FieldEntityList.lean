import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.StarPath

/-! # Shared checked field entity-list shape

This boundary owns the kind-independent authoring shape shared by ordinary aggregate field lists. It resolves direct, plain-star, and filtered-star slots in authored order, rejects only repeated direct fields, and requires either multiple slots or one starred slot. It also owns the shared `FieldValuesNotUnique` kind/category classification and whole-list scans, while family-specific modules choose a required category, certify the declarations, and retain their own runtime semantics.
-/

namespace A12Kernel

/-- How one direct slot reads its field. Most families can read a field only one way and leave every slot `.stored`; an Enumeration list may read one field both plainly and through a category projection. The Kernel counts those two reads as distinct operands rather than a repeated one, so this discriminator is part of operand identity and must survive path resolution. -/
inductive FieldEntityReadForm where
  | stored
  | projected (category : String)
  deriving Repr, DecidableEq

/-- One parser-independent field entity-list slot. A filter belongs to its exact authored wildcard occurrence. -/
inductive SurfaceFieldEntityOperand where
  | field (path : SurfaceFieldPath) (form : FieldEntityReadForm := .stored)
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
  | field (declaration : FlatFieldDecl) (form : FieldEntityReadForm)
  | star (source : CheckedStarFieldPath model)
  | starHaving (source : CheckedStarFieldPath model)
      (having : SurfaceCorrelatedHaving)

namespace ResolvedFieldEntityOperand

def isStar : ResolvedFieldEntityOperand model → Bool
  | .field .. => false
  | .star _ | .starHaving _ _ => true

def directFieldId? : ResolvedFieldEntityOperand model → Option FieldId
  | .field declaration _ => some declaration.id
  | .star _ | .starHaving _ _ => none

/-- The identity the repeated-operand gate compares. A star addresses a row set rather than one slot and never participates. -/
def operandIdentity? : ResolvedFieldEntityOperand model →
    Option (FieldId × FieldEntityReadForm)
  | .field declaration form => some (declaration.id, form)
  | .star _ | .starHaving _ _ => none

/-- The model declaration this slot reads, whatever its addressing form. Kind-neutral, so a family's admission gate can classify every slot without repeating the star/direct split. -/
def declaration : ResolvedFieldEntityOperand model → FlatFieldDecl
  | .field declaration _ => declaration
  | .star source | .starHaving source _ => source.declaration

end ResolvedFieldEntityOperand

/-- One comparability category admitted by the Kernel's field-list operators. String and Enumeration remain distinct even though both use the token runtime domain. -/
inductive FieldListComparabilityCategory where
  | string | enumeration | number | temporal
  deriving Repr, DecidableEq

/-- The kind-only admission stage: one comparability category, or refusal before category comparison. -/
inductive FieldListOperandAdmission where
  | category (value : FieldListComparabilityCategory)
  | refusedByKind
  deriving Repr, DecidableEq

/-- Classify every represented scalar kind for the shared `FieldValuesNotUnique` kind gate. BOOLEAN and CONFIRM are measured outright refusals; DATE_RANGE has no flat declaration form. -/
def SurfaceScalarKind.fieldListAdmission :
    SurfaceScalarKind → FieldListOperandAdmission
  | .string => .category .string
  | .enumeration => .category .enumeration
  | .number => .category .number
  | .temporal _ => .category .temporal
  | .boolean | .confirm => .refusedByKind

structure FieldListKindRefusal where
  path : List String
  actual : SurfaceScalarKind
  deriving Repr, DecidableEq

structure FieldListCategoryMismatch where
  path : List String
  actual : SurfaceScalarKind
  deriving Repr, DecidableEq

/-- Scan the complete operand list before category certification so a kind refusal preempts mixing in every authored order. -/
def firstFieldListKindRefusal? :
    List (ResolvedFieldEntityOperand model) → Option FieldListKindRefusal
  | [] => none
  | operand :: remaining =>
      let declaration := operand.declaration
      let actual := declaration.policy.kind.surfaceKind
      match actual.fieldListAdmission with
      | .refusedByKind => some { path := declaration.path, actual }
      | .category _ => firstFieldListKindRefusal? remaining

/-- After the complete kind scan succeeds, find the first operand outside `expected`. The `refusedByKind` arm keeps this helper total; checked entry points run the required kind scan first. -/
def firstFieldListCategoryMismatch?
    (expected : FieldListComparabilityCategory) :
    List (ResolvedFieldEntityOperand model) → Option FieldListCategoryMismatch
  | [] => none
  | operand :: remaining =>
      let declaration := operand.declaration
      let actual := declaration.policy.kind.surfaceKind
      match actual.fieldListAdmission with
      | .refusedByKind => firstFieldListCategoryMismatch? expected remaining
      | .category category =>
          if category == expected then firstFieldListCategoryMismatch? expected remaining
          else some { path := declaration.path, actual }

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

/-- Report the first repeated direct operand, comparing complete operand identity but naming the offending field. Two reads of one field in different forms are two operands, so only a repeat of the same field in the same form is reported. -/
def firstDuplicateResolvedDirectField? :
    List (ResolvedFieldEntityOperand model) → Option FieldId
  | [] => none
  | operand :: remaining =>
      match operand.operandIdentity? with
      | none => firstDuplicateResolvedDirectField? remaining
      | some identity =>
          if remaining.any fun candidate =>
              candidate.operandIdentity? == some identity then
            some identity.1
          else
            firstDuplicateResolvedDirectField? remaining

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
  | .field path form => do
      let declaration ← model.resolveNonrepeatableFieldUnchecked declaringGroup path
        |>.mapError .resolve
      pure (.field declaration form)
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
