import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.EnumerationValueList

/-! # Checked String/Enumeration entity lists

This boundary certifies the shared field entity-list shape as the Kernel's String/ordinary stored-Enumeration family. String and Enumeration may mix, category projection is unrepresentable, and caller-supplied checked cells let a prepared custom String participate without resampling its validator. Individual consumers retain their own evaluation, relevance, empty-result, and phase-projection rules.
-/

namespace A12Kernel

/-- String/ordinary stored-Enumeration consumers use the common field entity-list shape. -/
abbrev SurfaceTokenEntityOperand := SurfaceFieldEntityOperand

/-- A nonempty authored token-family entity-list source. -/
abbrev SurfaceTokenEntitySource := SurfaceFieldEntitySource

/-- One direct nonrepeatable String or stored-Enumeration declaration. -/
structure CheckedTokenField (model : FlatModel) where
  declaration : FlatFieldDecl
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned : declaration.toTextFieldComparison? = some (operand, profile)
  admitted : model.admitsField operand.field = true

/-- One starred String or stored-Enumeration declaration with its exact optional checked filter. -/
structure CheckedTokenStarSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned : source.declaration.toTextFieldComparison? = some (operand, profile)
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)

/-- One checked token-family slot retains either its direct owner or its general starred owner. -/
inductive CheckedTokenEntityOperand (model : FlatModel) where
  | field (source : CheckedTokenField model)
  | star (source : CheckedTokenStarSource model)

namespace CheckedTokenEntityOperand

def directFieldId? : CheckedTokenEntityOperand model → Option FieldId
  | .field source => some source.operand.field.id
  | .star _ => none

def isStar : CheckedTokenEntityOperand model → Bool
  | .field _ => false
  | .star _ => true

def hasHaving : CheckedTokenEntityOperand model → Bool
  | .field _ => false
  | .star source => source.filter.isSome

end CheckedTokenEntityOperand

def firstDuplicateDirectTokenField? :
    List (CheckedTokenEntityOperand model) → Option FieldId
  | operands => firstDuplicateDirectField?
      (fun operand => operand.directFieldId?) operands

/-- A checked homogeneous token-family list. Wildcard occurrences remain independent; only repeated direct references are excluded. -/
structure CheckedTokenEntitySource (model : FlatModel) where
  first : CheckedTokenEntityOperand model
  rest : List (CheckedTokenEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectTokenField? (first :: rest) = none

namespace CheckedTokenEntitySource

def operands (checked : CheckedTokenEntitySource model) :
    List (CheckedTokenEntityOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedTokenEntitySource model) : Bool :=
  checked.operands.any (fun operand => operand.hasHaving)

end CheckedTokenEntitySource

inductive TokenEntityElabError where
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

private def checkedTokenOperand?
    (declaration : FlatFieldDecl) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  declaration.toTextFieldComparison?

private def certifyDirectTokenOperand (model : FlatModel)
    (declaration : FlatFieldDecl) :
    Except TokenEntityElabError (CheckedTokenField model) :=
  match hOperand : checkedTokenOperand? declaration with
  | none =>
      if declaration.isRawString then
        throw (.rawStringValue declaration.path)
      else
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
    Except TokenEntityElabError
      (CheckedTokenStarSource model) :=
  match hOperand : checkedTokenOperand? source.declaration with
  | none =>
      if source.declaration.isRawString then
        throw (.rawStringValue source.declaration.path)
      else
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

private def certifyTokenEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except TokenEntityElabError (CheckedTokenEntityOperand model)
  | .field declaration =>
      do pure (.field (← certifyDirectTokenOperand model declaration))
  | .star source =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source none))
  | .starHaving source having =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source (some having)))

private def certifyTokenEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except TokenEntityElabError
        (List (CheckedTokenEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyTokenEntityOperand model declaringGroup operand) ::
        (← certifyTokenEntityOperands model declaringGroup remaining))

/-- Resolve duplicate/cardinality shape before certifying the complete list as String/ordinary stored-Enumeration. -/
def elaborateTokenEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenEntitySource) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let first ← certifyTokenEntityOperand model declaringGroup shape.first
  let rest ← certifyTokenEntityOperands model declaringGroup shape.rest
  if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectTokenField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none => pure {
        first
        rest
        modelWellFormed := shape.modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw .incoherentCore

namespace CheckedTokenField

/-- Classify one caller-supplied checked direct cell; this permits prepared custom String checking without moving that host concern into the aggregate. -/
def valueListCellAt (checked : CheckedTokenField model)
    (phase : Phase) (read : FieldId → CheckedCell) : ValueListCell .token :=
  checked.operand.checkedValueListCellAt phase (read checked.operand.field.id)

def resolvedSideAt (checked : CheckedTokenField model)
    (phase : Phase) (read : FieldId → CheckedCell) :
    ResolvedValueListSide .token :=
  { cells := [checked.valueListCellAt phase read]
    hasUninstantiatedTail := false
    hasHaving := false }

end CheckedTokenField

namespace CheckedTokenStarSource

/-- Apply path-owned over-repetition to one caller-supplied checked leaf, then project its exact String/stored-Enumeration token. -/
def valueListCellAt (checked : CheckedTokenStarSource model)
    (phase : Phase) (read : Env → FieldId → CheckedCell)
    (environment : Env) : ValueListCell .token :=
  checked.operand.checkedValueListCellAt phase
    (checked.source.contextualizeCell environment
      (read environment checked.operand.field.id))

/-- Unfiltered phase-indexed resolution is the reusable boundary for a later computation consumer. Filtered computation remains deliberately unsupported. -/
def resolvedUnfilteredSideAt (checked : CheckedTokenStarSource model)
    (phase : Phase) (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedValueListSide document outer
    (checked.valueListCellAt phase read)

end CheckedTokenStarSource

end A12Kernel
