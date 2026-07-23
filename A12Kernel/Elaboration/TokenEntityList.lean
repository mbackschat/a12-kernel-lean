import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.EnumerationValueList

/-! # Checked String/Enumeration entity lists

This boundary certifies the shared field entity-list shape as the Kernel's String/Enumeration token family. The common stored-only surface remains shared by distinct count and first-filled consumers, while the checked field/star representation can retain an exact category projection for a consumer whose syntax admits one. Caller-supplied checked cells let a prepared custom String participate without resampling its validator. Individual consumers retain their own authoring, evaluation, relevance, empty-result, and phase-projection rules.
-/

namespace A12Kernel

/-- String/ordinary stored-Enumeration consumers use the common field entity-list shape. -/
abbrev SurfaceTokenEntityOperand := SurfaceFieldEntityOperand

/-- A nonempty authored token-family entity-list source. -/
abbrev SurfaceTokenEntitySource := SurfaceFieldEntitySource

/-- Resolve the exact stored/category token projection selected by a token-family consumer. String supports only the stored/default selection. -/
def FlatFieldDecl.toTokenFieldComparison? (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  match projectionRef with
  | .stored => declaration.toTextFieldComparison?
  | .category _ =>
      declaration.toEnumerationTextFieldComparison? projectionRef

/-- One direct nonrepeatable String or stored/category Enumeration declaration. -/
structure CheckedTokenField (model : FlatModel) where
  declaration : FlatFieldDecl
  projectionRef : EnumerationProjectionRef
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned :
    declaration.toTokenFieldComparison? projectionRef = some (operand, profile)
  admitted : model.admitsField operand.field = true

/-- One starred String or stored/category Enumeration declaration with its exact optional checked filter. -/
structure CheckedTokenStarSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  projectionRef : EnumerationProjectionRef
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned :
    source.declaration.toTokenFieldComparison? projectionRef =
      some (operand, profile)
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)

/-- One checked token-family slot retains either its direct owner or its general starred owner. -/
inductive CheckedTokenEntityOperand (model : FlatModel) where
  | field (source : CheckedTokenField model)
  | star (source : CheckedTokenStarSource model)

namespace CheckedTokenEntityOperand

structure DirectReference where
  field : FieldId
  projection : Option EnumerationProjectionRef
  deriving Repr, DecidableEq

def directReference? : CheckedTokenEntityOperand model →
    Option DirectReference
  | .field source =>
      some {
        field := source.operand.field.id
        projection := match source.operand with
          | .string _ => none
          | .enumeration operand => some operand.projectionRef }
  | .star _ => none

def isStar : CheckedTokenEntityOperand model → Bool
  | .field _ => false
  | .star _ => true

def hasHaving : CheckedTokenEntityOperand model → Bool
  | .field _ => false
  | .star source => source.filter.isSome

def referencesField (checked : CheckedTokenEntityOperand model)
    (field : FieldId) : Bool :=
  match checked with
  | .field source => source.operand.field.id == field
  | .star source =>
      source.operand.field.id == field ||
        match source.filter with
        | none => false
        | some having => having.condition.referencesField field

end CheckedTokenEntityOperand

private def firstDuplicateDirectTokenReference? :
    List (CheckedTokenEntityOperand model) →
      Option CheckedTokenEntityOperand.DirectReference
  | [] => none
  | operand :: remaining =>
      match operand.directReference? with
      | none => firstDuplicateDirectTokenReference? remaining
      | some reference =>
          if remaining.any fun candidate =>
              candidate.directReference? == some reference then
            some reference
          else
            firstDuplicateDirectTokenReference? remaining

def firstDuplicateDirectTokenField? :
    List (CheckedTokenEntityOperand model) → Option FieldId
  | operands =>
      match firstDuplicateDirectTokenReference? operands with
      | some duplicate => some duplicate.field
      | none => none

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

def referencesField (checked : CheckedTokenEntitySource model)
    (field : FieldId) : Bool :=
  checked.operands.any (fun operand => operand.referencesField field)

end CheckedTokenEntitySource

inductive TokenEntityElabError where
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | enumerationOperand (path : List String) (error : EnumerationOperandError)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

private def checkedTokenOperand? (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  declaration.toTokenFieldComparison? projectionRef

def certifyDirectTokenOperand (model : FlatModel)
    (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef := .stored) :
    Except TokenEntityElabError (CheckedTokenField model) :=
  match hOperand : checkedTokenOperand? declaration projectionRef with
  | none =>
      match declaration.policy.kind, projectionRef with
      | .enumeration, .category name =>
          throw (.enumerationOperand declaration.path (.unknownCategory name))
      | _, _ =>
          if declaration.isRawString then
            throw (.rawStringValue declaration.path)
          else
            throw (.fieldKindMismatch declaration.path
              declaration.policy.kind.surfaceKind)
  | some (operand, profile) =>
      if hAdmitted : model.admitsField operand.field = true then
        pure {
          declaration
          projectionRef
          operand
          profile
          operandOwned := hOperand
          admitted := hAdmitted }
      else
        throw .incoherentCore

def certifyStarTokenOperand (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model)
    (having : Option SurfaceCorrelatedHaving)
    (projectionRef : EnumerationProjectionRef := .stored) :
    Except TokenEntityElabError
      (CheckedTokenStarSource model) :=
  match hOperand : checkedTokenOperand? source.declaration projectionRef with
  | none =>
      match source.declaration.policy.kind, projectionRef with
      | .enumeration, .category name =>
          throw (.enumerationOperand source.declaration.path
            (.unknownCategory name))
      | _, _ =>
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
        projectionRef
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

/-- Finish one checked token entity list after its consumer has resolved and certified every slot. Exact direct-reference identity retains category selection, while wildcard occurrences remain independent. -/
def assembleTokenEntitySource
    (modelWellFormed : model.validate.isOk = true)
    (first : CheckedTokenEntityOperand model)
    (rest : List (CheckedTokenEntityOperand model)) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) :=
  if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectTokenField? (first :: rest) with
    | some field => throw (.shape (.duplicateOperand field))
    | none => pure {
        first
        rest
        modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw (.shape .tooFewFields)

/-- Resolve duplicate/cardinality shape before certifying the complete list as String/ordinary stored-Enumeration. -/
def elaborateTokenEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenEntitySource) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let first ← certifyTokenEntityOperand model declaringGroup shape.first
  let rest ← certifyTokenEntityOperands model declaringGroup shape.rest
  assembleTokenEntitySource shape.modelWellFormed first rest

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

/-- Apply path-owned over-repetition to one caller-supplied checked leaf, then project its exact String/stored-or-category Enumeration token. -/
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

/-- Full validation resolves topology and its optional checked filter before classifying selected token cells. -/
def resolvedValidationSide (checked : CheckedTokenStarSource model)
    (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedOptionalValidationHavingValueListSide document outer
    checked.filter read (checked.valueListCellAt .validation read)

/-- Partial all-rows validation checks wildcard/ancestor extent before reading any selected target. Filtered rules are skipped by the owning whole-source consumer. -/
def resolvedPartialValidationSide
    (checked : CheckedTokenStarSource model)
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

end CheckedTokenStarSource

namespace CheckedTokenEntityOperand

/-- Resolve one direct or starred token slot for full validation through the shared declaration-owned classifier. -/
def resolvedValidationSide (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  match checked with
  | .field source => pure (source.resolvedSideAt .validation directRead)
  | .star source => source.resolvedValidationSide document outer starRead

/-- Resolve one unfiltered token slot under partial-validation relevance, preserving rule-level skip/nonrelevance outside the cell domain. -/
def resolvedPartialValidationSide
    (checked : CheckedTokenEntityOperand model)
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
        match ← source.resolvedPartialValidationSide document outer scope
            starRead hUnfiltered with
        | .inl side => pure (.inl side)
        | .inr () => pure (.inr .nonRelevant)
      else
        pure (.inr .skippedHaving)

end CheckedTokenEntityOperand

end A12Kernel
