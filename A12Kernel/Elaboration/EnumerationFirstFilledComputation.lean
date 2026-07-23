import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.StarEnumerationValueList
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked Enumeration-target `FirstFilledValue`

This capsule adds the aggregate source admitted by the ordinary closed-Enumeration target gate. The common field-list shape owns cardinality and direct-duplicate precedence; exact stored/category projections own domain and display compatibility; the shared first-filled scan owns value, empty, and target-poison behavior; and the computation-phase `Having` traversal preserves filter poison plus the runtime iterator's one-kept-candidate lookahead.
-/

namespace A12Kernel

/-- One direct or optionally filtered starred Enumeration/category source in an Enumeration-target `FirstFilledValue`. -/
inductive SurfaceEnumerationFirstFilledOperand where
  | field (operand : SurfaceTextFieldOperand)
  | star (path : SurfaceStarFieldPath)
      (projectionRef : EnumerationProjectionRef := .stored)
      (having : Option SurfaceCorrelatedHaving := none)
  deriving Repr, DecidableEq

/-- A nonempty authored Enumeration/category `FirstFilledValue` source. -/
structure SurfaceEnumerationFirstFilledSource where
  first : SurfaceEnumerationFirstFilledOperand
  rest : List SurfaceEnumerationFirstFilledOperand
  deriving Repr, DecidableEq

namespace SurfaceEnumerationFirstFilledOperand

def toFieldEntityOperand : SurfaceEnumerationFirstFilledOperand →
    SurfaceFieldEntityOperand
  | .field (.direct path) | .field (.category path _) => .field path
  | .star path _ none => .star path
  | .star path _ (some having) => .starHaving path having

end SurfaceEnumerationFirstFilledOperand

namespace SurfaceEnumerationFirstFilledSource

def toFieldEntitySource (source : SurfaceEnumerationFirstFilledSource) :
    SurfaceFieldEntitySource :=
  {
    first := source.first.toFieldEntityOperand
    rest := source.rest.map (·.toFieldEntityOperand)
  }

end SurfaceEnumerationFirstFilledSource

/-- One checked source slot tied to the exact validated model and selected Enumeration projection. -/
inductive CheckedEnumerationFirstFilledOperand (model : FlatModel) where
  | field (path : List String) (operand : FlatEnumerationOperand)
      (projection : CheckedEnumerationProjection)
      (owned : model.checkedEnumerationOperand? operand = some projection)
  | star (source : CheckedStarEnumerationSource model)

namespace CheckedEnumerationFirstFilledOperand

def directFieldId? : CheckedEnumerationFirstFilledOperand model →
    Option FieldId
  | .field _ operand _ _ => some operand.field.id
  | .star _ => none

def isStar : CheckedEnumerationFirstFilledOperand model → Bool
  | .field .. => false
  | .star _ => true

def path : CheckedEnumerationFirstFilledOperand model → List String
  | .field path _ _ _ => path
  | .star source => source.source.declaration.path

def projection : CheckedEnumerationFirstFilledOperand model →
    CheckedEnumerationProjection
  | .field _ _ projection _ => projection
  | .star source => source.operand

def referencesField (operand : CheckedEnumerationFirstFilledOperand model)
    (field : FieldId) : Bool :=
  match operand with
  | .field _ source _ _ => source.field.id == field
  | .star source => source.source.declaration.id == field

def allowedFor (operand : CheckedEnumerationFirstFilledOperand model)
    (target : CheckedEnumerationProjection) : Bool :=
  operand.projection.compatibleWithTarget target

end CheckedEnumerationFirstFilledOperand

def firstDuplicateDirectEnumerationFirstFilledField? :
    List (CheckedEnumerationFirstFilledOperand model) → Option FieldId
  | operands =>
      firstDuplicateDirectField? (fun operand => operand.directFieldId?) operands

/-- The checked source retains the common aggregate shape plus compatibility and target-reference certificates. -/
structure CheckedEnumerationFirstFilledSource (model : FlatModel) where
  first : CheckedEnumerationFirstFilledOperand model
  rest : List (CheckedEnumerationFirstFilledOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectEnumerationFirstFilledField? (first :: rest) = none

namespace CheckedEnumerationFirstFilledSource

def operands (source : CheckedEnumerationFirstFilledSource model) :
    List (CheckedEnumerationFirstFilledOperand model) :=
  source.first :: source.rest

def referencesField (source : CheckedEnumerationFirstFilledSource model)
    (field : FieldId) : Bool :=
  source.operands.any (fun operand => operand.referencesField field)

def allowedFor (source : CheckedEnumerationFirstFilledSource model)
    (target : CheckedEnumerationProjection) : Bool :=
  source.operands.all (fun operand => operand.allowedFor target)

end CheckedEnumerationFirstFilledSource

inductive EnumerationFirstFilledComputationElabError where
  | target (error : EnumerationComputationElabError)
  | shape (error : FieldEntityShapeElabError)
  | directSource (error : ElabError)
  | starSource (error : StarEnumerationValueListElabError)
  | sourceIncompatible (sourcePath targetPath : List String)
  | targetSelfReference (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

private def certifyDirectEnumerationFirstFilledOperand
    (model : FlatModel) (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Except EnumerationFirstFilledComputationElabError
      (CheckedEnumerationFirstFilledOperand model) :=
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .error _ => throw .incoherentCore
      | .ok checked =>
          match checkEnumerationProjection checked projectionRef with
          | .error error =>
              throw (.directSource (.enumerationOperand declaration.path error))
          | .ok projection =>
              let operand : FlatEnumerationOperand := {
                field := { id := declaration.id }
                projectionRef
                projection := projection.projection
              }
              match hOwned : model.checkedEnumerationOperand? operand with
              | none => throw .incoherentCore
              | some modelProjection =>
                  pure (.field declaration.path operand modelProjection hOwned)
  | actual, _ =>
      throw (.directSource
        (.textFieldOperandKindMismatch declaration.path actual.surfaceKind))

private def certifyEnumerationFirstFilledOperand
    (declaringGroup : GroupPath) :
    ResolvedFieldEntityOperand model → SurfaceEnumerationFirstFilledOperand →
      Except EnumerationFirstFilledComputationElabError
        (CheckedEnumerationFirstFilledOperand model)
  | .field declaration, .field authored =>
      let projectionRef := match authored with
        | .direct _ => .stored
        | .category _ category => .category category
      certifyDirectEnumerationFirstFilledOperand model declaration projectionRef
  | .star source, .star _ projectionRef _ =>
      do pure (.star (← certifyStarEnumerationSource declaringGroup source
        projectionRef none |>.mapError .starSource))
  | .starHaving source having, .star _ projectionRef _ =>
      do pure (.star (← certifyStarEnumerationSource declaringGroup source
        projectionRef (some having) |>.mapError .starSource))
  | _, _ => throw .incoherentCore

private def certifyEnumerationFirstFilledOperands
    (declaringGroup : GroupPath) :
    List (ResolvedFieldEntityOperand model) →
      List SurfaceEnumerationFirstFilledOperand →
      Except EnumerationFirstFilledComputationElabError
        (List (CheckedEnumerationFirstFilledOperand model))
  | [], [] => pure []
  | resolved :: resolvedRest, authored :: authoredRest => do
      pure ((← certifyEnumerationFirstFilledOperand declaringGroup resolved authored) ::
        (← certifyEnumerationFirstFilledOperands declaringGroup resolvedRest authoredRest))
  | _, _ => throw .incoherentCore

private def elaborateEnumerationFirstFilledSource
    (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceEnumerationFirstFilledSource) :
    Except EnumerationFirstFilledComputationElabError
      (CheckedEnumerationFirstFilledSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored.toFieldEntitySource
    |>.mapError .shape
  let first ← certifyEnumerationFirstFilledOperand declaringGroup shape.first authored.first
  let rest ← certifyEnumerationFirstFilledOperands declaringGroup shape.rest authored.rest
  if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectEnumerationFirstFilledField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none =>
        pure {
          first
          rest
          modelWellFormed := shape.modelWellFormed
          requiredMultiplicity := hMultiplicity
          uniqueDirectOperands := hDuplicate
        }
  else
    throw .incoherentCore

/-- One checked aggregate assignment into an ordinary closed-Enumeration target. -/
structure CheckedEnumerationFirstFilledComputationOperation
    (model : FlatModel) where
  target : CheckedEnumerationComputationTarget model
  source : CheckedEnumerationFirstFilledSource model
  sourceAllowed : source.allowedFor target.projection = true
  targetNotReferenced : source.referencesField target.field = false

/-- Check shape and exact Enumeration/category compatibility before runtime. -/
def elaborateEnumerationFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceEnumerationFirstFilledSource) :
    Except EnumerationFirstFilledComputationElabError
      (CheckedEnumerationFirstFilledComputationOperation model) := do
  let target ← elaborateEnumerationComputationTarget model targetField
    |>.mapError .target
  let source ← elaborateEnumerationFirstFilledSource model declaringGroup authored
  if hReference : source.referencesField target.field = true then
    throw (.targetSelfReference target.field)
  else if hAllowed : source.allowedFor target.projection = true then
    pure {
      target
      source
      sourceAllowed := hAllowed
      targetNotReferenced := by
        cases hValue : source.referencesField target.field with
        | false => rfl
        | true => exact False.elim (hReference hValue)
    }
  else
    match source.operands.find? fun operand =>
        !operand.allowedFor target.projection with
    | some operand =>
        throw (.sourceIncompatible operand.path target.path)
    | none => throw .incoherentCore

private def scanEnumerationFirstFilledStar
    (source : CheckedStarEnumerationSource model)
    (read : Env → FieldId → RawCell) (environments : List Env)
    (state : FirstFilledScanState) :
    FirstFilledScanState ⊕ FirstFilledTokenResult :=
  match scanFirstFilledItems (source.valueListCellAt .computation read)
      environments state with
  | .inl next => .inl next
  | .inr result => .inr result.asToken

/-- Consume a filtered star through the computation iterator's one-kept-candidate lookahead. Filter poison is terminal; target classification remains stop-at-first. -/
private def scanFilteredEnumerationFirstFilledStar
    (source : CheckedStarEnumerationSource model)
    (having : CheckedStarHaving model source.source source.declaringGroup)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) (outer : Env)
    (resolved : ResolvedStarTopology) (state : FirstFilledScanState) :
    FirstFilledScanState ⊕ FirstFilledTokenResult :=
  let filterContext : CorrelationContext := { read := filterRead }
  let entered := state.enter resolved.domain.hasOpenTail true
  let consume := fun current environment =>
    match current.step
        (source.valueListCellAt .computation starRead environment) with
    | .continue next => .inl next
    | .done result => .inr result.asToken
  match having.condition.scanComputation filterContext outer consume
      resolved.environments entered with
  | .exhausted next => .inl next
  | .terminated result => .inr result
  | .poison cause => .inr (.unavailable cause)

private def scanEnumerationFirstFilledOperand
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) (state : FirstFilledScanState) :
    CheckedEnumerationFirstFilledOperand model →
      Except StarAddressingError
        (FirstFilledScanState ⊕ FirstFilledTokenResult)
  | .field _ operand _ _ =>
      match state.step ((FlatTextFieldOperand.enumeration operand).checkedValueListCellAt
          .computation (direct.read operand.field.id)) with
      | .continue next => pure (.inl next)
      | .done result => pure (.inr result.asToken)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      match source.filter with
      | none =>
          pure (scanEnumerationFirstFilledStar source starRead resolved.environments
            (state.enterSelection resolved.environments.isEmpty
              resolved.domain.hasOpenTail false))
      | some having =>
          pure (scanFilteredEnumerationFirstFilledStar source having filterRead
            starRead outer resolved state)

private def scanEnumerationFirstFilledOperands
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    List (CheckedEnumerationFirstFilledOperand model) → FirstFilledScanState →
      Except StarAddressingError FirstFilledTokenResult
  | [], _ => pure .noValue
  | operand :: remaining, state => do
      match ← scanEnumerationFirstFilledOperand document outer direct filterRead
          starRead state operand with
      | .inl next =>
          scanEnumerationFirstFilledOperands document outer direct filterRead starRead
            remaining next
      | .inr result => pure result

namespace CheckedEnumerationFirstFilledSource

/-- Lazily resolve and scan checked operands in authored order at computation phase. -/
def evaluate (source : CheckedEnumerationFirstFilledSource model)
    (document : Document) (outer : Env) (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError FirstFilledTokenResult :=
  scanEnumerationFirstFilledOperands document outer (model.checkContext directRead)
    filterRead starRead source.operands {}

end CheckedEnumerationFirstFilledSource

namespace CheckedEnumerationFirstFilledComputationOperation

/-- Project the shared first-filled computation result into the common Enumeration target result. -/
def evaluate (operation : CheckedEnumerationFirstFilledComputationOperation model)
    (document : Document) (outer : Env) (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError StringTargetOutcome := do
  let selected ← operation.source.evaluate document outer directRead
    filterRead starRead
  pure selected.asComputationResult.asEnumerationTargetOutcome

end CheckedEnumerationFirstFilledComputationOperation

end A12Kernel
