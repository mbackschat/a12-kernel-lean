import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.Correlation

namespace A12Kernel

/-- Keep certified operand identities and filters for phase-specific execution and generated
validation; the resolved primitive slot list cannot recover their validation polarity. -/
structure CheckedComputationFieldFill (model : FlatModel) where
  private mk ::
  source : CheckedFieldFillList model

namespace CheckedComputationFieldFill

open FieldFillQuantifier

/-- Resolve the common list once, retaining the certificates for both phases. -/
def elaborate (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (surface : SurfaceFieldEntitySource) : Except FieldFillListElabError (CheckedComputationFieldFill model) :=
  (fun source => ⟨source⟩) <$> elaborateComputationFieldFillList model declaringGroup targetGroup surface

def referencesField (source : CheckedComputationFieldFill model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  source.source.referencesField field filterReads

def rowBoundBool (source : CheckedComputationFieldFill model) (scope : List RepeatableLevel) : Bool :=
  source.source.rowBoundBool scope

private abbrev SearchResult := ComputationHavingScanResult Bool ScanResult

private def scanValues (kind : ScanKind) (read : slot → ComputationFillSlot)
    (slots : List slot) (seen : Bool) : SearchResult :=
  match scanRead kind read slots seen with
  | .inl next => .exhausted next
  | .inr result => .terminated result

private def scanSources
    (consume : Operand → Bool → Except Error SearchResult) :
    List Operand → Bool → Except Error SearchResult
  | [], seen => pure (.exhausted seen)
  | source :: rest, seen => do
      match ← consume source seen with
      | .exhausted next => scanSources consume rest next
      | .terminated result => pure (.terminated result)
      | .poison cause => pure (.poison cause)

private def observe (cell : CheckedCell) : ComputationFillSlot :=
  (observeCell .computation cell).asComputationFillSlot

private def addressed (context : ScalarComputationContext) :
    Except ComputationFillError ComputationFillContext :=
  match context.addressed with
  | some addressed => pure addressed
  | none => throw .contextRequired

/-- A missing declared row supplies empty fields without consulting the physical-only reader.
Existing rows still use the caller's overlay, including freshly computed filter producers. -/
private def declaredRead (model : FlatModel) (document : Document)
    (read : Env → FieldId → CheckedCell) (environment : Env) (field : FieldId) : CheckedCell :=
  match (model.lookupUniqueId field).toOption with
  | none => malformedCheckedCell
  | some declaration => match (environment.pathForScope declaration.repeatableScope).toOption with
      | none => malformedCheckedCell
      | some path =>
          if (repeatableAncestorRowsFor declaration.repeatableScope path).all document.instantiatedRows.contains
          then read environment field else checkAdmittedRawCell .empty

private def scanExpanded (kind : ScanKind) (context : ScalarComputationContext)
    (field : FieldId) (axes : List StarAxis) (boundCount : Nat) (seen : Bool) :
    Except ComputationFillError SearchResult := do
  let addressed ← addressed context
  let (rows, omitted) ← (StarAxes.resolveOperandExtent axes addressed.document context.row boundCount).mapError .addressing
  match scanValues kind (fun row => observe (addressed.read row field)) rows seen with
  | .exhausted next =>
      if omitted then pure (scanValues kind id [.uninstantiated] next) else pure (.exhausted next)
  | result => pure result

private def scanStar (kind : ScanKind) (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText : Env → FieldId → Option String) (source : CheckedFilledFieldStarSource model) (seen : Bool) :
    Except ComputationFillError SearchResult := do
  let path := source.source.path
  let field := source.source.declaration.id
  match source.filter with
  | none => scanExpanded kind context field path.axes path.firstStar seen
  | some filter =>
      let addressed ← addressed context
      let resolved ← (path.resolveInCapacity addressed.document context.row).mapError .addressing
      let candidates ← match kind with
        | .anyDeclaredEmpty => do
            let some rows ← (path.declaredEnvironments? context.row).mapError .addressing
              | throw .declaredCapacityRequired
            pure rows
        | _ => pure resolved.environments
      let read := match kind with
        | .anyDeclaredEmpty => declaredRead model addressed.document
        | _ => fun reader => reader
      filter.condition.scanComputationResolving
        (({
          read := fun row field => pure (read filterRead row field)
          storedText := filterStoredText
          world := context.world
          unsupportedDateCalendar := .addressing .unsupportedDateCalendar
          temporalValueFailure := .addressing .temporalValueFailure
          worldUnavailable := .addressing .worldUnavailable
          typeValidityValueFailure := .addressing .typeValidityValueFailure
          storedTextUnavailable := ComputationFillError.addressing ∘ StarAddressingError.storedTextUnavailable
          groupUnavailable := ComputationFillError.addressing ∘ StarAddressingError.unsupportedGroupOperand
          bindingError := fun error => .addressing error.toStarAddressingError } : ResolvingCorrelationContext ComputationFillError).withComputationGroups addressed.document)
        context.row (fun seen row => pure (step kind seen (observe (read addressed.read row field))))
        candidates seen

private def scanOperand (kind : ScanKind) (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText : Env → FieldId → Option String) :
    CheckedFieldFillOperand model → Bool → Except ComputationFillError SearchResult
  | .indexed _, _ | .keyed _, _ => throw .indexedOperandNotSupported
  | .field declaration, seen =>
      if (context.read declaration.id).findings.contains .overRepetition then pure (.exhausted seen)
      else pure (scanValues kind (fun _ => observe (context.read declaration.id)) [()] seen)
  | .star source, seen => scanStar kind context filterRead filterStoredText source seen
  | .group source, seen => scanSources (fun (declaration : FlatFieldDecl) seen => do
      if declaration.repeatableScope.isEmpty then
        pure (scanValues kind (fun _ => observe (context.read declaration.id)) [()] seen)
      else
        let some axes := model.repeatableAxesForScope? declaration.repeatableScope
          | throw .contextRequired
        scanExpanded kind context declaration.id axes source.source.boundLevelCount seen)
      source.declarations seen

/-- The indexed operand shares the scan continuation with ordinary operands, preserving
short-circuiting before lookup and phase-specific poison at a reached read (`spec/08` §4.2). -/
def evalCheckedWith (source : CheckedComputationFieldFill model) (operator : FieldFillQuantifier)
    (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (liftError : ComputationFillError → Error)
    (indexedRead : CheckedSemanticIndexSource model → Except Error CellObservation)
    (keyedRead : CheckedKeyedEntityExtent model → Except Error (List ComputationFillSlot))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none) :
    Except Error ComputationConditionResult :=
  operator.evalComputationUsing fun kind => do
    let consume operand seen := match operand with
      | .indexed indexed => do
          let observation ← indexedRead indexed
          pure (scanValues kind id [observation.asComputationFillSlot] seen)
      | .keyed keyed => do
          pure (scanValues kind id (← keyedRead keyed) seen)
      | operand => (scanOperand kind context filterRead filterStoredText operand seen).mapError liftError
    match ← scanSources consume source.source.operands false with
    | .exhausted _ => pure .exhausted
    | .terminated result => pure result
    | .poison cause => pure (.poison cause)

def evalChecked (source : CheckedComputationFieldFill model) (operator : FieldFillQuantifier)
    (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none) :
    Except ComputationFillError ComputationConditionResult :=
  source.evalCheckedWith operator context filterRead id (fun _ => .error .indexedOperandNotSupported)
    (fun _ => .error .indexedOperandNotSupported) (filterStoredText := filterStoredText)

end CheckedComputationFieldFill
end A12Kernel
