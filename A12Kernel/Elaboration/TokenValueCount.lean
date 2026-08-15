import A12Kernel.Elaboration.TokenDistinctCount

/-! # Checked textual and Boolean/Confirm value counts

This consumer applies the common checked String/Enumeration entity list to `NumberOfValueInFields`. Its authored slots retain direct stored/category identity, while the decoded String constant is unrestricted for String fields and must belong to every selected Enumeration projection's exact domain. The generic value-count fold owns exact token equality and filter-sensitive movement; this module owns only its projection-bearing surface, static token-family admission, and phase-specific entity-list traversal.

The Boolean/Confirm companion reuses that same fold only after its distinct static family gate: `True` admits Boolean and Confirm, while `False` admits Boolean only. Direct, plain-star, and filtered-star operands project already-checked scalar values to fixed canonical tokens and never re-read stored text or model-declared display tokens.
-/

namespace A12Kernel

/-- A Boolean/Confirm value count uses the common direct/star field-list shape before applying its distinct kind gate. -/
abbrev SurfaceBooleanValueCountSource := SurfaceFieldEntitySource

/-- Static failures specific to the Boolean/Confirm value-count family. -/
inductive BooleanValueCountElabError where
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (expected : Bool)
      (actual : SurfaceScalarKind)
  | having (error : CorrelationElabError)
  /-- The shared checker admitted a group-scope slot that this family does not yet retain. Deliberately carries no diagnostic class: this carrier's own group verdict is unmeasured, so a refusal states only that the representation is missing. -/
  | groupOperandNotRepresented (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether one field kind is legal for the authored Boolean constant. `True` admits Boolean and Confirm; `False` admits only Boolean. -/
def booleanValueCountKindAllowed (expected : Bool) : FieldKind → Bool
  | .boolean => true
  | .confirm => expected
  | _ => false

/-- One checked direct Boolean/Confirm operand. -/
structure CheckedBooleanValueCountField (model : FlatModel)
    (expected : Bool) where
  declaration : FlatFieldDecl
  admitted :
    model.admitsField declaration.toPresenceField = true
  kindAllowed :
    booleanValueCountKindAllowed expected declaration.policy.kind = true

/-- One checked starred Boolean/Confirm operand with its exact optional filter. -/
structure CheckedBooleanValueCountStarSource (model : FlatModel)
    (expected : Bool) where
  source : CheckedStarFieldPath model
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)
  kindAllowed :
    booleanValueCountKindAllowed expected source.declaration.policy.kind = true

/-- One checked Boolean/Confirm entity-list operand. -/
inductive CheckedBooleanValueCountOperand (model : FlatModel)
    (expected : Bool) where
  | field (source : CheckedBooleanValueCountField model expected)
  | star (source : CheckedBooleanValueCountStarSource model expected)

namespace CheckedBooleanValueCountOperand

def declaration :
    CheckedBooleanValueCountOperand model expected → FlatFieldDecl
  | .field source => source.declaration
  | .star source => source.source.declaration

def directField? :
    CheckedBooleanValueCountOperand model expected → Option FlatFieldDecl
  | .field source => some source.declaration
  | .star _ => none

def directFieldId? :
    CheckedBooleanValueCountOperand model expected → Option FieldId
  | .field source => some source.declaration.id
  | .star _ => none

def isStar : CheckedBooleanValueCountOperand model expected → Bool
  | .field _ => false
  | .star _ => true

def hasHaving : CheckedBooleanValueCountOperand model expected → Bool
  | .field _ => false
  | .star source => source.filter.isSome

def referencesField (checked :
    CheckedBooleanValueCountOperand model expected) (field : FieldId) : Bool :=
  checked.declaration.id == field ||
    match checked with
    | .field _ => false
    | .star source =>
        match source.filter with
        | none => false
        | some having => having.condition.referencesField field

end CheckedBooleanValueCountOperand

def firstDuplicateDirectBooleanValueCountField? :
    List (CheckedBooleanValueCountOperand model expected) → Option FieldId
  | operands => firstDuplicateDirectField?
      (fun operand => operand.directFieldId?) operands

private def certifyBooleanValueCountOperand (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool) :
    ResolvedFieldEntityOperand model →
      Except BooleanValueCountElabError
        (CheckedBooleanValueCountOperand model expected)
  | .field declaration _ =>
      if hKind :
          booleanValueCountKindAllowed expected declaration.policy.kind = true then
        if hAdmitted :
            model.admitsField declaration.toPresenceField = true then
          pure (.field { declaration, admitted := hAdmitted, kindAllowed := hKind })
        else
          throw .incoherentCore
      else
        throw (.fieldKindMismatch declaration.path expected
          declaration.policy.kind.surfaceKind)
  | .star source =>
      if hKind :
          booleanValueCountKindAllowed expected source.declaration.policy.kind =
            true then do
        pure (.star {
          source
          declaringGroup
          filter := none
          kindAllowed := hKind })
      else
        throw (.fieldKindMismatch source.declaration.path expected
          source.declaration.policy.kind.surfaceKind)
  | .starHaving source having =>
      if hKind :
          booleanValueCountKindAllowed expected source.declaration.policy.kind =
            true then do
        let filter ←
          elaborateStarHavingCore model declaringGroup source having
            |>.mapError .having
        pure (.star {
          source
          declaringGroup
          filter := some filter
          kindAllowed := hKind })
      else
        throw (.fieldKindMismatch source.declaration.path expected
          source.declaration.policy.kind.surfaceKind)
  | .group reference => throw (.groupOperandNotRepresented reference.path)
  | .starredGroup source =>
      throw (.groupOperandNotRepresented source.group.path)

private def certifyBooleanValueCountOperands (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool) :
    List (ResolvedFieldEntityOperand model) →
      Except BooleanValueCountElabError
        (List (CheckedBooleanValueCountOperand model expected))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyBooleanValueCountOperand model declaringGroup expected operand) ::
        (← certifyBooleanValueCountOperands model declaringGroup expected remaining))

/-- A model-owned Boolean/Confirm `NumberOfValueInFields` source retaining direct/star order and optional per-star filters. -/
structure CheckedBooleanValueCountSource (model : FlatModel) where
  expected : Bool
  first : CheckedBooleanValueCountOperand model expected
  rest : List (CheckedBooleanValueCountOperand model expected)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectBooleanValueCountField? (first :: rest) = none

namespace CheckedBooleanValueCountSource

def operands (checked : CheckedBooleanValueCountSource model) :
    List (CheckedBooleanValueCountOperand model checked.expected) :=
  checked.first :: checked.rest

def directFields? (checked : CheckedBooleanValueCountSource model) :
    Option (List FlatFieldDecl) :=
  checked.operands.mapM CheckedBooleanValueCountOperand.directField?

def hasHaving (checked : CheckedBooleanValueCountSource model) : Bool :=
  checked.operands.any CheckedBooleanValueCountOperand.hasHaving

end CheckedBooleanValueCountSource

/-- Resolve the common direct/star entity-list shape and certify its constant-specific Boolean/Confirm family. -/
def elaborateBooleanValueCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :
    Except BooleanValueCountElabError
      (CheckedBooleanValueCountSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let first ←
    certifyBooleanValueCountOperand model declaringGroup expected shape.first
  let rest ←
    certifyBooleanValueCountOperands model declaringGroup expected shape.rest
  if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectBooleanValueCountField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none => pure {
        expected
        first
        rest
        modelWellFormed := shape.modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw .incoherentCore

/-- The fixed storage token selected by an authored Boolean constant. -/
def booleanValueCountToken (expected : Bool) : String :=
  if expected then "true" else "false"

/-- Project one already-checked Boolean/Confirm cell to the exact runtime token domain without consulting stored text. Empty remains unfilled; an impossible false Confirm fails closed. -/
def booleanValueCountCellAt (phase : Phase)
    (cell : CheckedCell) : ValueListCell .token :=
  match observeCell phase cell with
  | .empty => .empty
  | .value (.bool value) => .present (booleanValueCountToken value)
  | .value (.conf true) => .present (booleanValueCountToken true)
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

private def evaluateResolvedValueCountOperands
    (expected : String) (operands : List Operand)
    (resolve : Operand →
      Except Error
        (Sum (ResolvedValueListSide .token) NumericOperand)) :
    Except Error NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueCountSide .token) (terminal := NumericOperand)
      resolve
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.appendResolved side)
      operands .empty with
  | .inl side => pure (evalValueCountAggregate expected side)
  | .inr result => pure result

namespace CheckedBooleanValueCountSource

/-- Every Boolean/Confirm value count has the Kernel's fixed integral result scale. -/
def scaleSummary (_checked : CheckedBooleanValueCountSource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField (checked : CheckedBooleanValueCountSource model)
    (field : FieldId) : Bool :=
  checked.operands.any fun operand => operand.referencesField field

/-- Evaluate a direct-only checked Boolean/Confirm count without inventing repeatable topology. -/
def evaluateDirectAt? (checked : CheckedBooleanValueCountSource model)
    (phase : Phase) (read : FieldId → CheckedCell) :
    Option NumericOperand := do
  let fields ← checked.directFields?
  pure (evalValueCountAggregate
    (booleanValueCountToken checked.expected) {
      cells := fields.map fun field => {
        cell := booleanValueCountCellAt phase (read field.id)
        selectedByHaving := false }
      hasUninstantiatedTail := false
      hasHaving := false })

end CheckedBooleanValueCountSource

namespace CheckedBooleanValueCountOperand

private def directSideAt (source : CheckedBooleanValueCountField model expected)
    (phase : Phase) (read : FieldId → CheckedCell) :
    ResolvedValueListSide .token :=
  { cells := [
      booleanValueCountCellAt phase (read source.declaration.id)]
    hasUninstantiatedTail := false
    hasHaving := false }

private def starCellAt
    (source : CheckedBooleanValueCountStarSource model expected)
    (phase : Phase) (read : Env → FieldId → CheckedCell)
    (environment : Env) : ValueListCell .token :=
  booleanValueCountCellAt phase
    (source.source.contextualizeCell environment
      (read environment source.source.declaration.id))

/-- Resolve one Boolean/Confirm slot for full validation through the existing topology and optional checked filter. -/
def resolvedValidationSide
    (checked : CheckedBooleanValueCountOperand model expected)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  match checked with
  | .field source => pure (directSideAt source .validation directRead)
  | .star source =>
      source.source.resolvedOptionalValidationHavingValueListSide
        document outer source.filter starRead
        (starCellAt source .validation starRead)

/-- Resolve one Boolean/Confirm slot at computation phase. Filtered stars preserve one-kept-successor selection and stop on the first reached filter or value poison. -/
def resolvedComputationSide
    (checked : CheckedBooleanValueCountOperand model expected)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) NumericOperand) :=
  match checked with
  | .field source =>
      pure (.inl (directSideAt source .computation directRead))
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      match source.filter with
      | none =>
          pure (.inl (resolved.toResolvedSide
            (starCellAt source .computation starRead)))
      | some having =>
          let filterContext : CorrelationContext := { read := filterRead }
          let consume := fun cells environment =>
            match starCellAt source .computation starRead environment with
            | .unknown cause => .inr cause
            | cell => .inl (cell :: cells)
          match having.condition.scanComputation filterContext outer consume
              resolved.environments [] with
          | .exhausted reversed =>
              pure (.inl {
                cells := reversed.reverse
                hasUninstantiatedTail := resolved.domain.hasOpenTail
                hasHaving := true })
          | .terminated cause | .poison cause =>
              pure (.inr (.unknown cause))

/-- Resolve one Boolean/Confirm slot from the immutable checked document and project its addressed cells only after topology and filter selection succeed. -/
def resolvedCheckedValidationSide
    (checked : CheckedBooleanValueCountOperand model expected)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (ResolvedValueListSide .token) := do
  let core ← match checked with
    | .field source =>
        document.resolveCheckedDirectEntityOperandCore source.declaration.id
    | .star source =>
        source.source.resolveCheckedValidationEntityOperandCore document outer
          (source.filter.map (·.condition))
  pure {
    cells := core.addressedCells.map fun addressed =>
      booleanValueCountCellAt .validation addressed.cell
    hasUninstantiatedTail := core.hasUninstantiatedTail
    hasHaving := core.hasHaving
    hasNonRelevant := core.hasNonRelevant }

end CheckedBooleanValueCountOperand

namespace CheckedBooleanValueCountSource

/-- Full validation preserves authored slot order, omitted tails, and per-filter match provenance. -/
def evaluateValidation (checked : CheckedBooleanValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evaluateResolvedValueCountOperands
    (booleanValueCountToken checked.expected) checked.operands fun operand => do
      pure (.inl (← operand.resolvedValidationSide document outer
        directRead starRead))

/-- Full validation over the immutable checked document reuses the common addressed entity core before applying Boolean/Confirm classification. -/
def evaluateCheckedDocumentValidation
    (checked : CheckedBooleanValueCountSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  evaluateResolvedValueCountOperands
    (booleanValueCountToken checked.expected) checked.operands fun operand => do
      pure (.inl (←
        operand.resolvedCheckedValidationSide document outer))

/-- Computation uses the same checked source and tally while retaining computation-phase filter and value poison. -/
def evaluateComputation (checked : CheckedBooleanValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evaluateResolvedValueCountOperands
    (booleanValueCountToken checked.expected) checked.operands fun operand =>
      operand.resolvedComputationSide document outer directRead
        filterRead starRead

end CheckedBooleanValueCountSource

/-- Compatibility name for the shared projection-bearing token slot. -/
abbrev SurfaceTokenValueCountOperand :=
  SurfaceProjectedTokenEntityOperand

/-- Compatibility name for the shared projection-bearing token entity list. -/
abbrev SurfaceTokenValueCountSource :=
  SurfaceProjectedTokenEntitySource

namespace CheckedTokenField

/-- String accepts every decoded literal; Enumeration requires membership in its exact selected stored/category domain. -/
def allowsValueCountLiteral (checked : CheckedTokenField model)
    (expected : String) : Bool :=
  match checked.operand with
  | .string _ => true
  | .enumeration source =>
      match checked.declaration.enumeration with
      | some declaration =>
          match source.projection with
          | .stored => declaration.storedTokens.contains expected
          | .category mapping => mapping.categoryTokens.contains expected
      | none => false

end CheckedTokenField

namespace CheckedTokenStarSource

/-- Starred token operands retain the same declaration-owned literal gate as direct operands. -/
def allowsValueCountLiteral (checked : CheckedTokenStarSource model)
    (expected : String) : Bool :=
  match checked.operand with
  | .string _ => true
  | .enumeration source =>
      match checked.source.declaration.enumeration with
      | some declaration =>
          match source.projection with
          | .stored => declaration.storedTokens.contains expected
          | .category mapping => mapping.categoryTokens.contains expected
      | none => false

end CheckedTokenStarSource

namespace CheckedTokenEntityOperand

def path : CheckedTokenEntityOperand model → List String
  | .field source => source.declaration.path
  | .star source => source.source.declaration.path

def allowsValueCountLiteral (checked : CheckedTokenEntityOperand model)
    (expected : String) : Bool :=
  match checked with
  | .field source => source.allowsValueCountLiteral expected
  | .star source => source.allowsValueCountLiteral expected

def directField? : CheckedTokenEntityOperand model →
    Option (CheckedTokenField model)
  | .field source => some source
  | .star _ => none

end CheckedTokenEntityOperand

namespace CheckedTokenEntitySource

def allowsValueCountLiteral (checked : CheckedTokenEntitySource model)
    (expected : String) : Bool :=
  checked.operands.all (fun operand =>
    operand.allowsValueCountLiteral expected)

def directFields? (checked : CheckedTokenEntitySource model) :
    Option (List (CheckedTokenField model)) :=
  checked.operands.mapM CheckedTokenEntityOperand.directField?

end CheckedTokenEntitySource

inductive TokenValueCountElabError where
  | source (error : TokenEntityElabError)
  | literalOutsideEnumerationDomain (path : List String) (literal : String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked typed token count. The literal is retained with the complete source and its all-Enumeration domain certificate. -/
structure CheckedTokenValueCountSource (model : FlatModel) where
  expected : String
  source : CheckedTokenEntitySource model
  expectedAllowed : source.allowsValueCountLiteral expected = true

namespace CheckedTokenValueCountSource

/-- Every typed value count has the kernel's fixed integral result scale. -/
def scaleSummary (_checked : CheckedTokenValueCountSource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField (checked : CheckedTokenValueCountSource model)
    (field : FieldId) : Bool :=
  checked.source.referencesField field

end CheckedTokenValueCountSource

/-- Resolve the projection-bearing entity-list shape, certify String/Enumeration membership, and reject the first selected-domain mismatch in authored order. -/
def elaborateTokenValueCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : String)
    (authored : SurfaceTokenValueCountSource) :
    Except TokenValueCountElabError (CheckedTokenValueCountSource model) := do
  let source ← elaborateProjectedTokenEntitySource model declaringGroup authored
    |>.mapError .source
  if hAllowed : source.allowsValueCountLiteral expected = true then
    pure { expected, source, expectedAllowed := hAllowed }
  else
    match source.operands.find? fun operand =>
        !operand.allowsValueCountLiteral expected with
    | some operand =>
        throw (.literalOutsideEnumerationDomain operand.path expected)
    | none => throw .incoherentCore

namespace CheckedTokenEntityOperand

/-- Resolve one token slot at computation phase. Filtered stars reuse the shared one-kept-successor traversal and retain per-slot filter provenance for the value-count fold. -/
def resolvedValueCountComputationSide
    (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) NumericOperand) :=
  match checked with
  | .field source =>
      pure (.inl (source.resolvedSideAt .computation directRead))
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      match source.filter with
      | none =>
          pure (.inl (resolved.toResolvedSide
            (source.valueListCellAt .computation starRead)))
      | some having =>
          let filterContext : CorrelationContext := { read := filterRead }
          let consume := fun cells environment =>
            match source.valueListCellAt .computation starRead environment with
            | .unknown cause => .inr cause
            | cell => .inl (cell :: cells)
          match having.condition.scanComputation filterContext outer consume
              resolved.environments [] with
          | .exhausted reversed =>
              pure (.inl {
                cells := reversed.reverse
                hasUninstantiatedTail := resolved.domain.hasOpenTail
                hasHaving := true })
          | .terminated cause | .poison cause =>
              pure (.inr (.unknown cause))

end CheckedTokenEntityOperand

namespace CheckedTokenValueCountSource

/-- Evaluate a direct-only checked token count without inventing repeatable topology. -/
def evaluateDirectAt? (checked : CheckedTokenValueCountSource model)
    (phase : Phase) (read : FieldId → CheckedCell) :
    Option NumericOperand := do
  let fields ← checked.source.directFields?
  let side := fields.foldl (fun accumulated field =>
    accumulated.appendResolved (field.resolvedSideAt phase read))
    (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
  pure (evalValueCountAggregate checked.expected side)

/-- Full validation preserves authored slot order, exact token classification, omitted tails, and per-filter selected-match provenance. -/
def evaluateValidation (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evaluateResolvedValueCountOperands
    checked.expected checked.source.operands fun operand => do
      pure (.inl (← operand.resolvedValidationSide document outer
        directRead starRead))

/-- Full validation over the immutable checked document reuses the shared addressed token operand and retains per-slot filter provenance for the existing value-count fold. -/
def evaluateCheckedDocumentValidation
    (checked : CheckedTokenValueCountSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  evaluateResolvedValueCountOperands
    checked.expected checked.source.operands fun operand => do
      let resolved ←
        operand.resolveCheckedValidationOperand document outer
      pure (.inl (resolved.valueListSideAt .validation))

/-- Computation shares the same checked source and count fold while each filtered slot uses the computation iterator's one-kept-successor traversal. -/
def evaluateComputation (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evaluateResolvedValueCountOperands
    checked.expected checked.source.operands fun operand =>
      operand.resolvedValueCountComputationSide document outer directRead
        filterRead starRead

/-- Partial validation skips any filtered rule before topology or reads; otherwise it retains this unmeasured count family's one-covering-identifier star boundary and reuses the same count fold. -/
def evaluatePartialValidation
    (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError PartialValidationAggregateResult :=
  if checked.source.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedValueCountSide .token)
        (terminal := PartialValidationAggregateResult)
        (fun operand => operand.resolvedPartialValueCountSide document outer
          scope directRead starRead)
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.appendResolved side)
        checked.source.operands .empty with
    | .inl side =>
        pure (.evaluated (evalValueCountAggregate checked.expected side))
    | .inr result => pure result

end CheckedTokenValueCountSource

end A12Kernel
