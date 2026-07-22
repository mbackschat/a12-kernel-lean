import A12Kernel.Elaboration.NumericScale
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.StarNumber

/-! # Shared checked Number entity lists

This boundary owns the common authoring contract for Number-valued entity lists consumed by `FirstFilledValue`, `Sum`, `MinValue`, `MaxValue`, and Number-valued `NumberOfDifferentValues`. It resolves every direct, plain-star, and filtered-star slot in authored order, rejects only repeated direct fields, requires either multiple slots or one starred slot, and certifies every declaration as Number-valued. Runtime consumers retain their own scan semantics.
-/

namespace A12Kernel

/-- Number aggregate authors use the shared kind-independent entity-list syntax. -/
abbrev SurfaceNumberEntityOperand := SurfaceFieldEntityOperand

/-- Number aggregate authors use the shared nonempty entity-list source shape. -/
abbrev SurfaceNumberEntitySource := SurfaceFieldEntitySource

/-- One direct nonrepeatable Number declaration certified against the source model. -/
structure CheckedNumberEntityField (model : FlatModel) where
  declaration : FlatFieldDecl
  field : FlatNumberField
  admitted : model.admitsField (.number field) = true
  fieldOwned : declaration.toNumberField? = some field

/-- A checked Number slot retains exactly the owner needed by its direct, plain-star, or filtered-star runtime consumer. -/
inductive CheckedNumberEntityOperand (model : FlatModel) where
  | field (source : CheckedNumberEntityField model)
  | star (source : CheckedStarNumberSource model)
  | starHaving (source : CheckedStarNumberHavingSource model)

namespace CheckedNumberEntityOperand

def directFieldId? : CheckedNumberEntityOperand model → Option FieldId
  | .field source => some source.field.id
  | .star _ | .starHaving _ => none

def isStar : CheckedNumberEntityOperand model → Bool
  | .field _ => false
  | .star _ | .starHaving _ => true

def hasHaving : CheckedNumberEntityOperand model → Bool
  | .starHaving _ => true
  | .field _ | .star _ => false

def scaleSummary : CheckedNumberEntityOperand model → NumericScaleSummary
  | .field source => NumericScaleSummary.field source.field.info.scale
  | .star source => NumericScaleSummary.field source.field.info.scale
  | .starHaving source => NumericScaleSummary.field source.source.field.info.scale

def declarationSigned : CheckedNumberEntityOperand model → Bool
  | .field source => source.field.info.signed
  | .star source => source.field.info.signed
  | .starHaving source => source.source.field.info.signed

end CheckedNumberEntityOperand

def firstDuplicateDirectNumberEntityField? :
    List (CheckedNumberEntityOperand model) → Option FieldId
  | operands => firstDuplicateDirectField? (fun operand => operand.directFieldId?) operands

/-- A checked nonempty homogeneous Number entity list with kernel-valid cardinality and direct-reference uniqueness. Wildcarded occurrences remain independent authored slots. -/
structure CheckedNumberEntitySource (model : FlatModel) where
  first : CheckedNumberEntityOperand model
  rest : List (CheckedNumberEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectNumberEntityField? (first :: rest) = none

namespace CheckedNumberEntitySource

def operands (checked : CheckedNumberEntitySource model) :
    List (CheckedNumberEntityOperand model) :=
  checked.first :: checked.rest

/-- Whether this checked list contains a filtered wildcard slot. Partial validation uses this only as a rule-level early-skip discriminator; it never evaluates the filter. -/
def hasHaving (checked : CheckedNumberEntitySource model) : Bool :=
  checked.operands.any (fun operand => operand.hasHaving)

/-- Number entity-list operations derive the union/max scale of every authored declaration and gain no literal expansion capability. -/
def scaleSummary (checked : CheckedNumberEntitySource model) :
    NumericScaleSummary :=
  checked.rest.foldl
    (fun summary operand => summary.union operand.scaleSummary)
    checked.first.scaleSummary

end CheckedNumberEntitySource

inductive NumberEntityElabError where
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | star (error : StarNumberElabError)
  | tooFewFields
  | duplicateOperand (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

private def NumberEntityElabError.ofShape : FieldEntityShapeElabError →
    NumberEntityElabError
  | .resolve error => .resolve error
  | .starPath error => .star (.path error)
  | .tooFewFields => .tooFewFields
  | .duplicateOperand field => .duplicateOperand field

private def certifyStarNumber (source : CheckedStarFieldPath model) :
    Except NumberEntityElabError (CheckedStarNumberSource model) :=
  match hField : source.declaration.toNumberField? with
  | none => throw (.star (.fieldNotNumber source.declaration.path))
  | some field => pure { source, field, fieldOwned := hField }

private def certifyNumberEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except NumberEntityElabError (CheckedNumberEntityOperand model)
  | .field declaration =>
      match hField : declaration.toNumberField? with
      | none => throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)
      | some field =>
          if hAdmitted : model.admitsField (.number field) = true then
            pure (.field {
              declaration
              field
              admitted := hAdmitted
              fieldOwned := hField })
          else
            throw .incoherentCore
  | .star source => do
      pure (.star (← certifyStarNumber source))
  | .starHaving source having => do
      let numberSource ← certifyStarNumber source
      let filter ← elaborateStarHavingCore model declaringGroup numberSource.source having
        |>.mapError fun error => .star (.having error)
      pure (.starHaving { source := numberSource, declaringGroup, filter })

private def certifyNumberEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except NumberEntityElabError (List (CheckedNumberEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyNumberEntityOperand model declaringGroup operand) ::
        (← certifyNumberEntityOperands model declaringGroup remaining))

/-- Validate one Number entity list in kernel order: resolve all references, reject repeated direct fields, require multiple fields or a wildcard, then certify the common Number kind. Wildcarded occurrences are not deduplicated in an ordinary document model. -/
def elaborateNumberEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberEntitySource) :
    Except NumberEntityElabError (CheckedNumberEntitySource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError NumberEntityElabError.ofShape
  let first ← certifyNumberEntityOperand model declaringGroup shape.first
  let rest ← certifyNumberEntityOperands model declaringGroup shape.rest
  if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectNumberEntityField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none => pure {
        first
        rest
        modelWellFormed := shape.modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw .incoherentCore

end A12Kernel
