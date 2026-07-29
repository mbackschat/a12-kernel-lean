import A12Kernel.Elaboration.TokenDistinctCount

/-! # Checked textual and Boolean/Confirm value counts

This consumer applies the common checked String/Enumeration entity list to `NumberOfValueInFields`. Its authored slots retain direct stored/category identity, while the decoded String constant is unrestricted for String fields and must belong to every selected Enumeration projection's exact domain. The generic value-count fold owns exact token equality and filter-sensitive movement; this module owns only its projection-bearing surface, static token-family admission, and phase-specific entity-list traversal.

The direct Boolean/Confirm companion reuses that same fold only after its distinct static family gate: `True` admits Boolean and Confirm, while `False` admits Boolean only. It projects already-checked scalar values to the fixed canonical tokens and never re-reads stored text or model-declared display tokens. Repeatable Boolean/Confirm lists remain explicitly outside this capsule.
-/

namespace A12Kernel

/-- A direct Boolean/Confirm value count uses the common field-list shape before applying its distinct kind gate. -/
abbrev SurfaceBooleanValueCountSource := SurfaceFieldEntitySource

/-- Static failures specific to the direct Boolean/Confirm value-count family. -/
inductive BooleanValueCountElabError where
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (expected : Bool)
      (actual : SurfaceScalarKind)
  | repeatableUnsupported (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether one field kind is legal for the authored Boolean constant. `True` admits Boolean and Confirm; `False` admits only Boolean. -/
def booleanValueCountKindAllowed (expected : Bool) : FieldKind → Bool
  | .boolean => true
  | .confirm => expected
  | _ => false

private def certifyBooleanValueCountFields (expected : Bool) :
    List (ResolvedFieldEntityOperand model) →
      Except BooleanValueCountElabError (List FlatFieldDecl)
  | [] => pure []
  | .field declaration :: remaining => do
      if booleanValueCountKindAllowed expected declaration.policy.kind then
        pure (declaration ::
          (← certifyBooleanValueCountFields expected remaining))
      else
        throw (.fieldKindMismatch declaration.path expected
          declaration.policy.kind.surfaceKind)
  | .star source :: _ | .starHaving source _ :: _ =>
      throw (.repeatableUnsupported source.declaration.path)

/-- A direct, model-owned Boolean/Confirm `NumberOfValueInFields` source. The common shape has already established cardinality and direct-reference uniqueness. -/
structure CheckedBooleanValueCountSource (model : FlatModel) where
  expected : Bool
  fields : List FlatFieldDecl
  modelWellFormed : model.validate.isOk = true
  fieldsOwned : fields.all model.fields.contains = true
  fieldKindsAllowed :
    fields.all (fun field =>
      booleanValueCountKindAllowed expected field.policy.kind) = true
  requiredMultiplicity : fields.length > 1
  uniqueFields :
    FieldId.firstDuplicate? (fields.map (·.id)) = none

/-- Resolve the common entity-list shape, reject every repeatable slot, and certify the constant-specific Boolean/Confirm family. -/
def elaborateBooleanValueCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :
    Except BooleanValueCountElabError
      (CheckedBooleanValueCountSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let fields ← certifyBooleanValueCountFields expected shape.operands
  if hOwned : fields.all model.fields.contains = true then
    if hKinds :
        fields.all (fun field =>
          booleanValueCountKindAllowed expected field.policy.kind) = true then
      if hMultiplicity : fields.length > 1 then
        match hUnique : FieldId.firstDuplicate? (fields.map (·.id)) with
        | none => pure {
            expected
            fields
            modelWellFormed := shape.modelWellFormed
            fieldsOwned := hOwned
            fieldKindsAllowed := hKinds
            requiredMultiplicity := hMultiplicity
            uniqueFields := hUnique }
        | some _ => throw .incoherentCore
      else
        throw .incoherentCore
    else
      throw .incoherentCore
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

namespace CheckedBooleanValueCountSource

/-- Every Boolean/Confirm value count has the Kernel's fixed integral result scale. -/
def scaleSummary (_checked : CheckedBooleanValueCountSource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField (checked : CheckedBooleanValueCountSource model)
    (field : FieldId) : Bool :=
  checked.fields.any fun declaration => declaration.id == field

/-- Evaluate the direct checked fields in authored order through the existing exact-token count fold. -/
def evaluateAt (checked : CheckedBooleanValueCountSource model)
    (phase : Phase) (read : FieldId → CheckedCell) : NumericOperand :=
  evalValueCountAggregate (booleanValueCountToken checked.expected) {
    cells := checked.fields.map fun field => {
      cell := booleanValueCountCellAt phase (read field.id)
      selectedByHaving := false }
    hasUninstantiatedTail := false
    hasHaving := false }

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
    Except StarAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueCountSide .token) (terminal := NumericOperand)
      (fun operand => do
        pure (.inl (← operand.resolvedValidationSide document outer
          directRead starRead)))
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.appendResolved side)
      checked.source.operands .empty with
  | .inl side => pure (evalValueCountAggregate checked.expected side)
  | .inr result => pure result

/-- Full validation over the immutable checked document reuses the shared addressed token operand and retains per-slot filter provenance for the existing value-count fold. -/
def evaluateCheckedDocumentValidation
    (checked : CheckedTokenValueCountSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueCountSide .token) (terminal := NumericOperand)
      (fun operand => do
        let resolved ←
          operand.resolveCheckedValidationOperand document outer
        pure (.inl (resolved.valueListSideAt .validation)))
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.appendResolved side)
      checked.source.operands .empty with
  | .inl side => pure (evalValueCountAggregate checked.expected side)
  | .inr result => pure result

/-- Computation shares the same checked source and count fold while each filtered slot uses the computation iterator's one-kept-successor traversal. -/
def evaluateComputation (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueCountSide .token) (terminal := NumericOperand)
      (fun operand =>
        operand.resolvedValueCountComputationSide document outer directRead
          filterRead starRead)
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.appendResolved side)
      checked.source.operands .empty with
  | .inl side => pure (evalValueCountAggregate checked.expected side)
  | .inr result => pure result

/-- Partial validation skips any filtered rule before topology or reads; otherwise it requires the common direct/all-rows relevance gates and reuses the same count fold. -/
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
        (fun operand => operand.resolvedPartialValidationSide document outer
          scope directRead starRead)
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.appendResolved side)
        checked.source.operands .empty with
    | .inl side =>
        pure (.evaluated (evalValueCountAggregate checked.expected side))
    | .inr result => pure result

end CheckedTokenValueCountSource

end A12Kernel
