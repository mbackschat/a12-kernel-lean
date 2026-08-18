import A12Kernel.Elaboration.CheckedDocument

/-! # Checked direct DateRange bound extraction -/

namespace A12Kernel

/-- Static refusal before one bounded direct DateRange endpoint can be read. -/
inductive DateRangeBoundElabError where
  | source (error : ResolveError)
  | sourceNotDateRange (source : FieldId) (actual : SurfaceScalarKind)
  | unsupportedPolicy (source : FieldId) (format separator : String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether one resolved field is exactly a nonrepeatable DateRange source under a canonically supported stored-input policy. -/
def FlatModel.admitsDateRangeBoundSource
    (model : FlatModel) (source : FlatDateRangeField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toDateRangeField? == some source &&
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy => (DateRangeFormat.ofPolicy? policy).isSome
        | none => false

/-- One selected endpoint of a model-certified direct nonrepeatable DateRange field. -/
structure CheckedDateRangeBound (model : FlatModel) where
  private mk ::
  source : FlatDateRangeField
  bound : DateRangeBound
  sourceAdmitted : model.admitsDateRangeBoundSource source = true

/-- Resolve one direct field and accept only the two DateRange policies whose stored input is decoded by `CheckedDocument`. -/
def elaborateDateRangeBound (model : FlatModel) (sourceField : FieldId)
    (bound : DateRangeBound) :
    Except DateRangeBoundElabError (CheckedDateRangeBound model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById sourceField |>.mapError .source
  let source ← match declaration.toDateRangeField? with
    | some source => pure source
    | none => throw (.sourceNotDateRange sourceField
        declaration.policy.kind.surfaceKind)
  let policy ← match declaration.toDateRangeDeclarationPolicy? with
    | some policy => pure policy
    | none => throw .incoherentCore
  match DateRangeFormat.ofPolicy? policy with
  | none => throw (.unsupportedPolicy sourceField policy.format policy.separator)
  | some _ =>
      if hSource : model.admitsDateRangeBoundSource source = true then
        pure { source, bound, sourceAdmitted := hSource }
      else
        throw .incoherentCore

/-- Structural failure outside the phase-sensitive endpoint observation. -/
inductive DateRangeBoundFault where
  | document (error : CheckedDocumentError)
  | sourceValueKind (source : FieldId)
  deriving Repr, DecidableEq

namespace CheckedDateRangeBound

/-- Read one selected endpoint through the sole immutable checked-document route. Empty and exact formal unavailability retain their phase-specific observation constructors. -/
def evaluate (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) :
    Except DateRangeBoundFault (CellObservation DateValue) := do
  let cell ← input.read { field := operation.source.id, path := [] }
    |>.mapError .document
  match observeCell phase cell with
  | .empty => pure .empty
  | .value (.dateRange value) => pure (.value (value.select operation.bound))
  | .value _ => throw (.sourceValueKind operation.source.id)
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)

end CheckedDateRangeBound

end A12Kernel
