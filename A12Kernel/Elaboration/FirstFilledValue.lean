import A12Kernel.Elaboration.NumericStar
import A12Kernel.Elaboration.NumericScale
import A12Kernel.Elaboration.StarNumber
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked Number-star `FirstFilledValue` -/

namespace A12Kernel

/-- One parser-independent Number operand of an authored `FirstFilledValue`, retaining whether a star carries a filter at this exact slot. -/
inductive SurfaceFirstFilledNumberOperand where
  | field (path : SurfaceFieldPath)
  | star (path : SurfaceStarFieldPath)
  | starHaving (path : SurfaceStarFieldPath) (having : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

/-- A nonempty authored Number operand list. The checked boundary separately enforces that a sole operand is starred. -/
structure SurfaceFirstFilledNumberSource where
  first : SurfaceFirstFilledNumberOperand
  rest : List SurfaceFirstFilledNumberOperand
  deriving Repr, DecidableEq

/-- One direct nonrepeatable Number declaration certified against the source model. -/
structure CheckedFirstFilledNumberField (model : FlatModel) where
  declaration : FlatFieldDecl
  field : FlatNumberField
  admitted : model.admitsField (.number field) = true
  fieldOwned : declaration.toNumberField? = some field

/-- A checked Number operand retains exactly the owner needed by its direct, plain-star, or filtered-star runtime slot. -/
inductive CheckedFirstFilledNumberOperand (model : FlatModel) where
  | field (source : CheckedFirstFilledNumberField model)
  | star (source : CheckedStarNumberSource model)
  | starHaving (source : CheckedStarNumberHavingSource model)

private def firstDuplicateDirectField? (directFieldId? : α → Option FieldId) :
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

namespace CheckedFirstFilledNumberOperand

def directFieldId? : CheckedFirstFilledNumberOperand model → Option FieldId
  | .field source => some source.field.id
  | .star _ | .starHaving _ => none

def isStar : CheckedFirstFilledNumberOperand model → Bool
  | .field _ => false
  | .star _ | .starHaving _ => true

def scaleSummary : CheckedFirstFilledNumberOperand model → NumericScaleSummary
  | .field source => NumericScaleSummary.field source.field.info.scale
  | .star source => NumericScaleSummary.field source.field.info.scale
  | .starHaving source => NumericScaleSummary.field source.source.field.info.scale

end CheckedFirstFilledNumberOperand

def firstDuplicateDirectFirstFilledNumberField? :
    List (CheckedFirstFilledNumberOperand model) → Option FieldId
  | operands => firstDuplicateDirectField? (fun operand => operand.directFieldId?) operands

/-- A checked nonempty homogeneous Number operand list with kernel-valid cardinality and direct-reference uniqueness. Wildcarded operands remain repeatable authored slots. -/
structure CheckedFirstFilledNumberSource (model : FlatModel) where
  first : CheckedFirstFilledNumberOperand model
  rest : List (CheckedFirstFilledNumberOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectFirstFilledNumberField? (first :: rest) = none

namespace CheckedFirstFilledNumberSource

def operands (checked : CheckedFirstFilledNumberSource model) :
    List (CheckedFirstFilledNumberOperand model) :=
  checked.first :: checked.rest

/-- `FirstFilledValue` derives the union/max scale of every authored Number declaration while retaining no literal expansion capability. -/
def scaleSummary (checked : CheckedFirstFilledNumberSource model) :
    NumericScaleSummary :=
  checked.rest.foldl
    (fun summary operand => summary.union operand.scaleSummary)
    checked.first.scaleSummary

end CheckedFirstFilledNumberSource

inductive FirstFilledNumberElabError where
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | star (error : StarNumberElabError)
  | tooFewFields
  | duplicateOperand (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

private inductive ResolvedFirstFilledOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
  | star (source : CheckedStarFieldPath model)
  | starHaving (source : CheckedStarFieldPath model) (having : SurfaceCorrelatedHaving)

private def ResolvedFirstFilledOperand.isStar :
    ResolvedFirstFilledOperand model → Bool
  | .field _ => false
  | .star _ | .starHaving _ _ => true

private def ResolvedFirstFilledOperand.directFieldId? :
    ResolvedFirstFilledOperand model → Option FieldId
  | .field declaration => some declaration.id
  | .star _ | .starHaving _ _ => none

private def firstDuplicateResolvedFirstFilledDirectField? :
    List (ResolvedFirstFilledOperand model) → Option FieldId
  | operands => firstDuplicateDirectField? (fun operand => operand.directFieldId?) operands

private def resolveFirstFilledOperand (model : FlatModel)
    (declaringGroup : GroupPath) : SurfaceFirstFilledNumberOperand →
      Except FirstFilledNumberElabError (ResolvedFirstFilledOperand model)
  | .field path => do
      let declaration ←
        model.resolveNonrepeatableFieldUnchecked declaringGroup path |>.mapError .resolve
      pure (.field declaration)
  | .star path => do
      pure (.star (← elaborateStarFieldPath model declaringGroup path
        |>.mapError fun error => .star (.path error)))
  | .starHaving path having => do
      pure (.starHaving
        (← elaborateStarFieldPath model declaringGroup path
          |>.mapError fun error => .star (.path error))
        having)

private def resolveFirstFilledOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List SurfaceFirstFilledNumberOperand →
      Except FirstFilledNumberElabError (List (ResolvedFirstFilledOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolveFirstFilledOperand model declaringGroup operand) ::
        (← resolveFirstFilledOperands model declaringGroup remaining))

private def certifyFirstFilledStarNumber (source : CheckedStarFieldPath model) :
    Except FirstFilledNumberElabError (CheckedStarNumberSource model) :=
  match hField : source.declaration.toNumberField? with
  | none => throw (.star (.fieldNotNumber source.declaration.path))
  | some field => pure { source, field, fieldOwned := hField }

private def certifyFirstFilledNumberOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFirstFilledOperand model →
      Except FirstFilledNumberElabError (CheckedFirstFilledNumberOperand model)
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
      pure (.star (← certifyFirstFilledStarNumber source))
  | .starHaving source having => do
      let numberSource ← certifyFirstFilledStarNumber source
      let filter ← elaborateStarHavingCore model declaringGroup numberSource.source having
        |>.mapError fun error => .star (.having error)
      pure (.starHaving { source := numberSource, declaringGroup, filter })

private def certifyFirstFilledNumberOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFirstFilledOperand model) →
      Except FirstFilledNumberElabError
        (List (CheckedFirstFilledNumberOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyFirstFilledNumberOperand model declaringGroup operand) ::
        (← certifyFirstFilledNumberOperands model declaringGroup remaining))

/-- Validate one Number `FirstFilledValue` operand list in kernel order: resolve all references, reject repeated direct fields, require multiple fields or a wildcard, then certify the common Number kind. Wildcarded operands are not deduplicated in an ordinary document model. -/
def elaborateFirstFilledNumberSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFirstFilledNumberSource) :
    Except FirstFilledNumberElabError (CheckedFirstFilledNumberSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let resolvedFirst ← resolveFirstFilledOperand model declaringGroup authored.first
      let resolvedRest ← resolveFirstFilledOperands model declaringGroup authored.rest
      match firstDuplicateResolvedFirstFilledDirectField? (resolvedFirst :: resolvedRest) with
      | some field => throw (.duplicateOperand field)
      | none =>
          if resolvedFirst.isStar || !resolvedRest.isEmpty then
            let first ← certifyFirstFilledNumberOperand model declaringGroup resolvedFirst
            let rest ← certifyFirstFilledNumberOperands model declaringGroup resolvedRest
            if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
              match hDuplicate :
                  firstDuplicateDirectFirstFilledNumberField? (first :: rest) with
              | some _ => throw .incoherentCore
              | none => pure {
                  first
                  rest
                  modelWellFormed := by rw [hModel]; rfl
                  requiredMultiplicity := hMultiplicity
                  uniqueDirectOperands := hDuplicate }
            else
              throw .incoherentCore
          else
            throw .tooFewFields

/-- Partial validation keeps a reached nonrelevant cell distinct from both formal unavailability and an evaluated first-filled result. -/
inductive PartialValidationFirstFilledNumberResult where
  | nonRelevant
  | evaluated (result : FirstFilledNumberResult)
  deriving Repr, DecidableEq

namespace CheckedNumericStarSource

/-- Evaluate the checked ordered star through the existing prefix-terminating Number consumer. -/
def evaluateFirstFilled (checked : CheckedNumericStarSource model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError FirstFilledNumberResult := do
  checked.validateContext raw
  pure (evalFirstFilledNumber (checked.resolvedValueSide raw))

end CheckedNumericStarSource

namespace CheckedStarNumberSource

/-- Shared continuation-capable worker for one reached star slot. Falling through returns the accumulated scan state; a present, unavailable, or nonrelevant cell returns the terminal result. -/
def scanPartialValidationFirstFilledState (checked : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell)
    : List Env → FirstFilledNumberScanState →
      FirstFilledNumberScanState ⊕ PartialValidationFirstFilledNumberResult
  | [], state => .inl state
  | environment :: environments, state =>
      if checked.source.cellRelevant scope environment then
        match state.step (checked.valueListCell read environment) with
        | .continue next =>
            scanPartialValidationFirstFilledState checked scope read
              environments next
        | .done result => .inr (.evaluated result)
      else
        .inr .nonRelevant

/-- Finish one resolved star as a standalone partial-validation `FirstFilledValue` operand. -/
def scanPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell)
    (environments : List Env) (state : FirstFilledNumberScanState) :
    PartialValidationFirstFilledNumberResult :=
  match checked.scanPartialValidationFirstFilledState scope read environments state with
  | .inl next => .evaluated next.finish
  | .inr result => result

/-- Scan one already-resolved nested Number star in encounter order, checking each concrete cell's relevance immediately before its declaration-owned classification. A terminal value or formal unavailability hides every later relevance and target read. -/
def selectedPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (resolved : ResolvedStarTopology) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : PartialValidationFirstFilledNumberResult :=
  scanPartialValidationFirstFilled checked scope read resolved.environments
    (({} : FirstFilledNumberScanState).enterSelection
      resolved.environments.isEmpty resolved.domain.hasOpenTail false)

/-- Resolve the canonical nested topology once, then run the order-aware partial-validation first-filled scan. -/
def resolvedPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationFirstFilledNumberResult := do
  let resolved ← checked.source.path.resolve document outer
  pure (checked.selectedPartialValidationFirstFilled resolved scope read)

end CheckedStarNumberSource

private def scanCheckedFirstFilledNumberOperand
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) (state : FirstFilledNumberScanState) :
    CheckedFirstFilledNumberOperand model →
      Except StarAddressingError
        (FirstFilledNumberScanState ⊕ PartialValidationFirstFilledNumberResult)
  | .field source =>
      let relevant := scope.coversCell model source.declaration.path []
      if relevant then
        match state.step (source.field.valueListCell direct) with
        | .continue next => pure (.inl next)
        | .done result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      pure (source.scanPartialValidationFirstFilledState scope starRead
        resolved.environments (state.enterSelection resolved.environments.isEmpty
          resolved.domain.hasOpenTail false))
  | .starHaving source => do
      let resolved ← source.source.source.path.resolve document outer
      let selected := source.having.selectEnvironments { read := filterRead } outer
        resolved.environments
      pure (source.source.scanPartialValidationFirstFilledState scope starRead selected
        (state.enterSelection selected.isEmpty resolved.domain.hasOpenTail true))

private def scanCheckedFirstFilledNumberOperands
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    List (CheckedFirstFilledNumberOperand model) → FirstFilledNumberScanState →
      Except StarAddressingError PartialValidationFirstFilledNumberResult
  | [], state => pure (.evaluated state.finish)
  | operand :: remaining, state => do
      match ← scanCheckedFirstFilledNumberOperand document outer scope direct
          filterRead starRead state operand with
      | .inl next =>
          scanCheckedFirstFilledNumberOperands document outer scope direct
            filterRead starRead remaining next
      | .inr result => pure result

namespace CheckedFirstFilledNumberSource

/-- Evaluate checked direct and independently resolved star slots in authored order. Relevance and filters are sampled only after every earlier slot has fallen through; no later topology or reader is touched after a terminal result. -/
def evaluatePartialValidation (checked : CheckedFirstFilledNumberSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : RawFlatContext) (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationFirstFilledNumberResult :=
  scanCheckedFirstFilledNumberOperands document outer scope
    (model.checkContext directRead) filterRead starRead checked.operands {}

end CheckedFirstFilledNumberSource

end A12Kernel
