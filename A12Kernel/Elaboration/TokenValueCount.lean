import A12Kernel.Elaboration.TokenDistinctCount

/-! # Checked String/Enumeration value counts

This consumer applies the common checked String/Enumeration entity list to `NumberOfValueInFields`. Its authored slots retain direct stored/category identity, while the decoded String constant is unrestricted for String fields and must belong to every selected Enumeration projection's exact domain. The generic value-count fold owns exact token equality and filter-sensitive movement; this module owns only its projection-bearing surface, static token-family admission, and phase-specific entity-list traversal.
-/

namespace A12Kernel

/-- One value-count slot retains the exact stored/category projection selected by its direct or starred field reference. -/
inductive SurfaceTokenValueCountOperand where
  | field (source : SurfaceTextFieldOperand)
  | star (source : SurfaceStarFieldPath)
      (projectionRef : EnumerationProjectionRef)
  | starHaving (source : SurfaceStarFieldPath)
      (projectionRef : EnumerationProjectionRef)
      (having : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

/-- A nonempty projection-bearing token value-count entity list. -/
structure SurfaceTokenValueCountSource where
  first : SurfaceTokenValueCountOperand
  rest : List SurfaceTokenValueCountOperand
  deriving Repr, DecidableEq

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

private inductive ResolvedTokenValueCountOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
      (projectionRef : EnumerationProjectionRef)
  | star (source : CheckedStarFieldPath model)
      (projectionRef : EnumerationProjectionRef)
      (having : Option SurfaceCorrelatedHaving)

namespace ResolvedTokenValueCountOperand

def isStar : ResolvedTokenValueCountOperand model → Bool
  | .field _ _ => false
  | .star _ _ _ => true

def directReference? : ResolvedTokenValueCountOperand model →
    Option (FieldId × EnumerationProjectionRef)
  | .field declaration projectionRef => some (declaration.id, projectionRef)
  | .star _ _ _ => none

end ResolvedTokenValueCountOperand

private def resolveTokenValueCountOperand (model : FlatModel)
    (declaringGroup : GroupPath) : SurfaceTokenValueCountOperand →
      Except TokenEntityElabError (ResolvedTokenValueCountOperand model)
  | .field source => do
      let reference := match source with
        | .direct field | .category field _ => field
      let projectionRef := match source with
        | .direct _ => EnumerationProjectionRef.stored
        | .category _ name => .category name
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError
          (fun error => .shape (.resolve error))
      pure (.field declaration projectionRef)
  | .star source projectionRef => do
      let checked ← elaborateStarFieldPath model declaringGroup source
        |>.mapError (fun error => .shape (.starPath error))
      pure (.star checked projectionRef none)
  | .starHaving source projectionRef having => do
      let checked ← elaborateStarFieldPath model declaringGroup source
        |>.mapError (fun error => .shape (.starPath error))
      pure (.star checked projectionRef (some having))

private def resolveTokenValueCountOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List SurfaceTokenValueCountOperand →
      Except TokenEntityElabError
        (List (ResolvedTokenValueCountOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolveTokenValueCountOperand model declaringGroup operand) ::
        (← resolveTokenValueCountOperands model declaringGroup remaining))

private def firstDuplicateResolvedTokenValueCountField? :
    List (ResolvedTokenValueCountOperand model) → Option FieldId
  | [] => none
  | operand :: remaining =>
      match operand.directReference? with
      | none => firstDuplicateResolvedTokenValueCountField? remaining
      | some reference =>
          if remaining.any fun candidate =>
              candidate.directReference? == some reference then
            some reference.1
          else
            firstDuplicateResolvedTokenValueCountField? remaining

private def certifyTokenValueCountOperand (model : FlatModel)
    (declaringGroup : GroupPath) :
    ResolvedTokenValueCountOperand model →
      Except TokenEntityElabError (CheckedTokenEntityOperand model)
  | .field declaration projectionRef => do
      pure (.field
        (← certifyDirectTokenOperand model declaration projectionRef))
  | .star source projectionRef having => do
      pure (.star
        (← certifyStarTokenOperand declaringGroup source having projectionRef))

private def certifyTokenValueCountOperands (model : FlatModel)
    (declaringGroup : GroupPath) :
    List (ResolvedTokenValueCountOperand model) →
      Except TokenEntityElabError
        (List (CheckedTokenEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyTokenValueCountOperand model declaringGroup operand) ::
        (← certifyTokenValueCountOperands model declaringGroup remaining))

/-- Resolve every path before exact-reference duplication and cardinality, then certify kind, category, and `Having` in authored order. -/
private def elaborateTokenValueCountEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenValueCountSource) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) :=
  match hModel : model.validate with
  | .error error => .error (.shape (.resolve error))
  | .ok () => do
      let first ←
        resolveTokenValueCountOperand model declaringGroup authored.first
      let rest ←
        resolveTokenValueCountOperands model declaringGroup authored.rest
      match firstDuplicateResolvedTokenValueCountField? (first :: rest) with
      | some field => throw (.shape (.duplicateOperand field))
      | none =>
          if first.isStar || !rest.isEmpty then
            let checkedFirst ←
              certifyTokenValueCountOperand model declaringGroup first
            let checkedRest ←
              certifyTokenValueCountOperands model declaringGroup rest
            assembleTokenEntitySource (by rw [hModel]; rfl)
              checkedFirst checkedRest
          else
            throw (.shape .tooFewFields)

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
  let source ← elaborateTokenValueCountEntitySource model declaringGroup authored
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
