import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.NumericScale
import A12Kernel.Semantics.EnumerationValueList
import A12Kernel.Semantics.NumericAggregate

/-! # Checked String/Enumeration distinct counts

This boundary certifies one shared entity-list shape as the Kernel's String/ordinary stored-Enumeration family and evaluates `NumberOfDifferentValues` over caller-supplied checked cells. String and Enumeration may mix, category projection is unrepresentable, and a prepared custom String can participate because checking remains outside this aggregate. Date-like declarations use a separate temporal identity boundary and are not admitted here.
-/

namespace A12Kernel

/-- String/ordinary stored-Enumeration aggregate authors use the common field entity-list shape. -/
abbrev SurfaceTokenDistinctCountOperand := SurfaceFieldEntityOperand

/-- A nonempty authored token-family distinct-count source. -/
abbrev SurfaceTokenDistinctCountSource := SurfaceFieldEntitySource

/-- One direct nonrepeatable String or stored-Enumeration declaration. -/
structure CheckedTokenDistinctField (model : FlatModel) where
  declaration : FlatFieldDecl
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned : declaration.toTextFieldComparison? = some (operand, profile)
  admitted : model.admitsField operand.field = true

/-- One starred String or stored-Enumeration declaration with its exact optional checked filter. -/
structure CheckedTokenDistinctStarSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned : source.declaration.toTextFieldComparison? = some (operand, profile)
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)

/-- One checked token-family slot retains either its direct owner or its general starred owner. -/
inductive CheckedTokenDistinctOperand (model : FlatModel) where
  | field (source : CheckedTokenDistinctField model)
  | star (source : CheckedTokenDistinctStarSource model)

namespace CheckedTokenDistinctOperand

def directFieldId? : CheckedTokenDistinctOperand model → Option FieldId
  | .field source => some source.operand.field.id
  | .star _ => none

def isStar : CheckedTokenDistinctOperand model → Bool
  | .field _ => false
  | .star _ => true

def hasHaving : CheckedTokenDistinctOperand model → Bool
  | .field _ => false
  | .star source => source.filter.isSome

end CheckedTokenDistinctOperand

def firstDuplicateDirectTokenDistinctField? :
    List (CheckedTokenDistinctOperand model) → Option FieldId
  | operands => firstDuplicateDirectField?
      (fun operand => operand.directFieldId?) operands

/-- A checked homogeneous token-family list. Wildcard occurrences remain independent; only repeated direct references are excluded. -/
structure CheckedTokenDistinctSource (model : FlatModel) where
  first : CheckedTokenDistinctOperand model
  rest : List (CheckedTokenDistinctOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectTokenDistinctField? (first :: rest) = none

namespace CheckedTokenDistinctSource

def operands (checked : CheckedTokenDistinctSource model) :
    List (CheckedTokenDistinctOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedTokenDistinctSource model) : Bool :=
  checked.operands.any (fun operand => operand.hasHaving)

/-- `NumberOfDifferentValues` always has integral scale 0 and no literal-driven scale expansion. -/
def scaleSummary (_checked : CheckedTokenDistinctSource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

end CheckedTokenDistinctSource

inductive TokenDistinctCountElabError where
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

private def checkedTokenOperand?
    (declaration : FlatFieldDecl) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  declaration.toTextFieldComparison?

private def certifyDirectTokenOperand (model : FlatModel)
    (declaration : FlatFieldDecl) :
    Except TokenDistinctCountElabError (CheckedTokenDistinctField model) :=
  match hOperand : checkedTokenOperand? declaration with
  | none =>
      throw (.fieldKindMismatch declaration.path
        declaration.policy.kind.surfaceKind)
  | some (operand, profile) =>
      if hAdmitted : model.admitsField operand.field = true then
        pure {
          declaration
          operand
          profile
          operandOwned := hOperand
          admitted := hAdmitted }
      else
        throw .incoherentCore

private def certifyStarTokenOperand (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model)
    (having : Option SurfaceCorrelatedHaving) :
    Except TokenDistinctCountElabError
      (CheckedTokenDistinctStarSource model) :=
  match hOperand : checkedTokenOperand? source.declaration with
  | none =>
      throw (.fieldKindMismatch source.declaration.path
        source.declaration.policy.kind.surfaceKind)
  | some (operand, profile) => do
      let filter ← match having with
        | none => pure none
        | some authored =>
            pure (some (← elaborateStarHavingCore model declaringGroup source authored
              |>.mapError .having))
      pure {
        source
        operand
        profile
        operandOwned := hOperand
        declaringGroup
        filter }

private def certifyTokenDistinctOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except TokenDistinctCountElabError (CheckedTokenDistinctOperand model)
  | .field declaration =>
      do pure (.field (← certifyDirectTokenOperand model declaration))
  | .star source =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source none))
  | .starHaving source having =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source (some having)))

private def certifyTokenDistinctOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except TokenDistinctCountElabError
        (List (CheckedTokenDistinctOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyTokenDistinctOperand model declaringGroup operand) ::
        (← certifyTokenDistinctOperands model declaringGroup remaining))

/-- Resolve duplicate/cardinality shape before certifying the complete list as String/ordinary stored-Enumeration. -/
def elaborateTokenDistinctCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenDistinctCountSource) :
    Except TokenDistinctCountElabError (CheckedTokenDistinctSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let first ← certifyTokenDistinctOperand model declaringGroup shape.first
  let rest ← certifyTokenDistinctOperands model declaringGroup shape.rest
  if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectTokenDistinctField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none => pure {
        first
        rest
        modelWellFormed := shape.modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw .incoherentCore

private def stringObservationAsToken :
    CellObservation → ValueListCell .token
  | .empty => .empty
  | .value (.str value) =>
      if value.isEmpty then .empty else .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

private def FlatTextFieldOperand.checkedValueListCellAt
    (operand : FlatTextFieldOperand) (phase : Phase) (cell : CheckedCell) :
    ValueListCell .token :=
  match operand with
  | .string _ => stringObservationAsToken (observeCell phase cell)
  | FlatTextFieldOperand.enumeration enumOperand =>
      enumOperand.projection.asValueListCell (observeCell phase cell)

namespace CheckedTokenDistinctField

/-- Classify one caller-supplied checked direct cell; this permits prepared custom String checking without moving that host concern into the aggregate. -/
def valueListCellAt (checked : CheckedTokenDistinctField model)
    (phase : Phase) (read : FieldId → CheckedCell) : ValueListCell .token :=
  checked.operand.checkedValueListCellAt phase (read checked.operand.field.id)

def resolvedSideAt (checked : CheckedTokenDistinctField model)
    (phase : Phase) (read : FieldId → CheckedCell) :
    ResolvedValueListSide .token :=
  { cells := [checked.valueListCellAt phase read]
    hasUninstantiatedTail := false
    hasHaving := false }

end CheckedTokenDistinctField

namespace CheckedTokenDistinctStarSource

/-- Apply path-owned over-repetition to one caller-supplied checked leaf, then project its exact String/stored-Enumeration token. -/
def valueListCellAt (checked : CheckedTokenDistinctStarSource model)
    (phase : Phase) (read : Env → FieldId → CheckedCell)
    (environment : Env) : ValueListCell .token :=
  checked.operand.checkedValueListCellAt phase
    (checked.source.contextualizeCell environment
      (read environment checked.operand.field.id))

/-- Full validation resolves topology and its optional checked filter before classifying selected target cells. -/
def resolvedValidationSide (checked : CheckedTokenDistinctStarSource model)
    (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedOptionalValidationHavingValueListSide document outer
    checked.filter read (checked.valueListCellAt .validation read)

/-- Unfiltered phase-indexed resolution is the reusable boundary for a later computation consumer. Filtered computation remains deliberately unsupported. -/
def resolvedUnfilteredSideAt (checked : CheckedTokenDistinctStarSource model)
    (phase : Phase) (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedValueListSide document outer
    (checked.valueListCellAt phase read)

/-- Partial all-rows validation checks wildcard/ancestor extent before reading any selected target. -/
def resolvedPartialValidationSide
    (checked : CheckedTokenDistinctStarSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) Unit) := do
  let resolved ← checked.source.path.resolve document outer
  if checked.source.allRowsRelevant scope then
    pure (.inl (resolved.toResolvedSide
      (checked.valueListCellAt .validation read)))
  else
    pure (.inr ())

end CheckedTokenDistinctStarSource

namespace CheckedTokenDistinctOperand

def resolvedValidationSide (checked : CheckedTokenDistinctOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  match checked with
  | .field source => pure (source.resolvedSideAt .validation directRead)
  | .star source => source.resolvedValidationSide document outer starRead

def resolvedPartialValidationSide
    (checked : CheckedTokenDistinctOperand model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) PartialValidationAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        pure (.inl (source.resolvedSideAt .validation directRead))
      else
        pure (.inr .nonRelevant)
  | .star source =>
      if hUnfiltered : source.filter.isNone = true then do
        match ← source.resolvedPartialValidationSide document outer scope starRead
            hUnfiltered with
        | .inl side => pure (.inl side)
        | .inr () => pure (.inr .nonRelevant)
      else
        pure (.inr .skippedHaving)

end CheckedTokenDistinctOperand

namespace CheckedTokenDistinctSource

private def emptySide : ResolvedValueListSide .token :=
  { cells := [], hasUninstantiatedTail := false, hasHaving := false }

/-- Evaluate full validation in authored slot order. Every wildcard occurrence resolves independently, and the first unavailable reached cell stops before later topology or reads. -/
def evaluateValidation (checked : CheckedTokenDistinctSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueListSide .token) (terminal := NumericOperand)
      (fun operand => do
        pure (.inl (← operand.resolvedValidationSide document outer
          directRead starRead)))
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.append side)
      checked.operands emptySide with
  | .inl side => pure (evalDistinctCountAggregate side)
  | .inr result => pure result

/-- Partial validation skips a filtered rule before topology or reads. Otherwise direct slots require concrete relevance and every star requires wildcard/ancestor all-rows coverage. -/
def evaluatePartialValidation (checked : CheckedTokenDistinctSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError PartialValidationAggregateResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedValueListSide .token)
        (terminal := PartialValidationAggregateResult)
        (fun operand => operand.resolvedPartialValidationSide document outer scope
          directRead starRead)
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.append side)
        checked.operands emptySide with
    | .inl side => pure (.evaluated (evalDistinctCountAggregate side))
    | .inr result => pure result

end CheckedTokenDistinctSource

end A12Kernel
