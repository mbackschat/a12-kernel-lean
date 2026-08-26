import A12Kernel.Elaboration.EnumerationComputationResult
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Elaboration.StarEnumerationValueList
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked Enumeration-target `FirstFilledValue`

This capsule adds the aggregate source admitted by the ordinary closed-Enumeration target gate. The common field-list shape owns cardinality and repeated-operand precedence; exact stored/category projections own domain and display compatibility; the shared first-filled scan owns value, empty, and target-poison behavior; and the computation-phase `Having` traversal preserves filter poison plus the runtime iterator's one-kept-candidate lookahead.

A self-read is classified by its **reading mode** rather than by the authored shape around it. Measured compatible stored-direct lists of two or three fields project the ordinary Kernel self-reference class in every target position; a compatible two-entry list carrying a category projection of the target projects the distinct category-target class in either operand order, whatever the other entry reads — another projection, a plain read of a different field, or a plain read of the same field. Wider, incompatible, starred, and filtered shapes retain the local refusal without an external class.
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

/-- Lower one slot to the shared entity-list surface, retaining the reading form so the shared repeated-operand gate keeps a stored read and a category projection of one field apart. -/
def toFieldEntityOperand : SurfaceEnumerationFirstFilledOperand →
    SurfaceFieldEntityOperand
  | .field (.direct path) => .field path .stored
  | .field (.category path category) => .field path (.projected category)
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

/-- One checked source slot tied to the exact validated model, reading scope, and selected Enumeration projection. -/
inductive CheckedEnumerationFirstFilledOperand (model : FlatModel)
    (scope : List RepeatableLevel) where
  | field (path : List String) (operand : FlatEnumerationOperand)
      (projection : CheckedEnumerationProjection)
      (owned : model.checkedEnumerationOperandIn? scope operand = some projection)
  | star (source : CheckedStarEnumerationSource model)

namespace CheckedEnumerationFirstFilledOperand

def directFieldId? : CheckedEnumerationFirstFilledOperand model scope →
    Option FieldId
  | .field _ operand _ _ => some operand.field.id
  | .star _ => none

/-- The identity this family's repeated-operand rule compares. It matches the shared gate's identity: a stored read and a category projection of one field are two operands, so only a same-form repeat is a duplicate. -/
def operandIdentity? : CheckedEnumerationFirstFilledOperand model scope →
    Option (FieldId × EnumerationProjectionRef)
  | .field _ operand _ _ => some (operand.field.id, operand.projectionRef)
  | .star _ => none

def isStar : CheckedEnumerationFirstFilledOperand model scope → Bool
  | .field .. => false
  | .star _ => true

def path : CheckedEnumerationFirstFilledOperand model scope → List String
  | .field path _ _ _ => path
  | .star source => source.source.declaration.path

def projection : CheckedEnumerationFirstFilledOperand model scope →
    CheckedEnumerationProjection
  | .field _ _ projection _ => projection
  | .star source => source.operand

def referencesField (operand : CheckedEnumerationFirstFilledOperand model scope)
    (field : FieldId) : Bool :=
  match operand with
  | .field _ source _ _ => source.field.id == field
  | .star source => source.source.declaration.id == field

private def isStoredDirect : CheckedEnumerationFirstFilledOperand model scope → Bool
  | .field _ source _ _ =>
      match source.projectionRef with
      | .stored => true
      | .category _ => false
  | .star _ => false

private def isCategory : CheckedEnumerationFirstFilledOperand model scope → Bool
  | .field _ source _ _ =>
      match source.projectionRef with
      | .stored => false
      | .category _ => true
  | .star _ => false

def allowedFor (operand : CheckedEnumerationFirstFilledOperand model scope)
    (target : CheckedEnumerationProjection) : Bool :=
  operand.projection.compatibleWithTarget target

end CheckedEnumerationFirstFilledOperand

def firstDuplicateDirectEnumerationFirstFilledField? :
    List (CheckedEnumerationFirstFilledOperand model scope) → Option FieldId
  | [] => none
  | operand :: remaining =>
      match operand.operandIdentity? with
      | none => firstDuplicateDirectEnumerationFirstFilledField? remaining
      | some identity =>
          if remaining.any fun candidate =>
              candidate.operandIdentity? == some identity then
            some identity.1
          else
            firstDuplicateDirectEnumerationFirstFilledField? remaining

/-- How a computation reads its own computed field. The Kernel classifies a
target self-read by this **reading mode** rather than by the authored shape
around it, and a projected read pre-empts a plain one wherever both occur. -/
private inductive EnumerationTargetReadMode where
  /-- Every occurrence of the target reads its stored value directly. -/
  | plain
  /-- Some occurrence of the target reads it through a category projection. -/
  | projected
  deriving Repr, DecidableEq

/-- The checked source retains the common aggregate shape plus its reading scope, compatibility, and target-reference certificates. -/
structure CheckedEnumerationFirstFilledSource (model : FlatModel)
    (scope : List RepeatableLevel) where
  first : CheckedEnumerationFirstFilledOperand model scope
  rest : List (CheckedEnumerationFirstFilledOperand model scope)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectEnumerationFirstFilledField? (first :: rest) = none

namespace CheckedEnumerationFirstFilledSource

def operands (source : CheckedEnumerationFirstFilledSource model scope) :
    List (CheckedEnumerationFirstFilledOperand model scope) :=
  source.first :: source.rest

def referencesField (source : CheckedEnumerationFirstFilledSource model scope)
    (field : FieldId) : Bool :=
  source.operands.any (fun operand => operand.referencesField field)

def allowedFor (source : CheckedEnumerationFirstFilledSource model scope)
    (target : CheckedEnumerationProjection) : Bool :=
  source.operands.all (fun operand => operand.allowedFor target)

/-- Fold the reading mode over the operands that actually name the computed
field, then keep only the externally measured denominator around it.

The class is decided by *how* the target is read, so one category occurrence
selects the projected mode however the rest of the list reads. The surrounding
bound is the measured one and differs per mode: compatible stored-direct lists
were measured at length two and three, while a list carrying a projection was
measured at length two only. A star never contributes a mode, and an
incompatible source stays outside the denominator entirely.

Every two-entry pairing this fold classifies is externally measured, including
the one whose plain entry names a *different* field: such a read is inert for
this class, so the pair reports the projected class in either operand order.
That row exists because the composition it replaced, that an other-field read
contributes nothing and therefore only the projected self-read decides, reads as
settled without having been measured. -/
private def measuredTargetReadMode?
    (source : CheckedEnumerationFirstFilledSource model scope)
    (targetField : FieldId) (target : CheckedEnumerationProjection) :
    Option EnumerationTargetReadMode :=
  let operands := source.operands
  let selfReads := operands.filter fun operand => operand.referencesField targetField
  if !source.allowedFor target then
    none
  else if selfReads.any (fun operand => operand.isCategory) then
    if operands.length == 2 && operands.all (fun operand => !operand.isStar) then
      some .projected
    else
      none
  else if selfReads.any (fun operand => operand.isStoredDirect) then
    if (operands.length == 2 || operands.length == 3) &&
        operands.all (fun operand => operand.isStoredDirect) then
      some .plain
    else
      none
  else
    none

end CheckedEnumerationFirstFilledSource

inductive EnumerationFirstFilledComputationElabError where
  | target (error : EnumerationComputationElabError)
  | shape (error : FieldEntityShapeElabError)
  | directSource (error : ElabError)
  | starSource (error : StarEnumerationValueListElabError)
  | sourceIncompatible (sourcePath targetPath : List String)
  | targetSelfReference (field : FieldId)
  | targetSelfReferenceAtPlainRead (field : FieldId)
  | targetSelfReferenceAtProjectedRead (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

namespace EnumerationFirstFilledComputationElabError

/-- Project the two measured self-read modes to their distinct Kernel diagnostic
classes. A self-reference outside the measured denominator stays local. -/
def targetDiagnostic? :
    EnumerationFirstFilledComputationElabError →
      Option KernelStaticDiagnostic
  | .targetSelfReferenceAtPlainRead _ =>
      some .errorReferenceToCalculatedField
  | .targetSelfReferenceAtProjectedRead _ =>
      some .errorSemanticIndexOrCategoryForErrorField
  | _ => none

end EnumerationFirstFilledComputationElabError

private def certifyDirectEnumerationFirstFilledOperand
    (model : FlatModel) (scope : List RepeatableLevel)
    (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Except EnumerationFirstFilledComputationElabError
      (CheckedEnumerationFirstFilledOperand model scope) :=
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
              match hOwned : model.checkedEnumerationOperandIn? scope operand with
              | none => throw .incoherentCore
              | some modelProjection =>
                  pure (.field declaration.path operand modelProjection hOwned)
  | actual, _ =>
      throw (.directSource
        (.textFieldOperandKindMismatch declaration.path actual.surfaceKind))

private def certifyEnumerationFirstFilledOperand
    (declaringGroup : GroupPath) (scope : List RepeatableLevel) :
    ResolvedFieldEntityOperand model → SurfaceEnumerationFirstFilledOperand →
      Except EnumerationFirstFilledComputationElabError
        (CheckedEnumerationFirstFilledOperand model scope)
  | .field declaration form, .field _ =>
      certifyDirectEnumerationFirstFilledOperand model scope declaration
        (match form with
          | .stored => .stored
          | .projected category => .category category)
  | .star source, .star _ projectionRef _ =>
      do pure (.star (← certifyStarEnumerationSource declaringGroup source
        projectionRef none |>.mapError .starSource))
  | .starHaving source having, .star _ projectionRef _ =>
      do pure (.star (← certifyStarEnumerationSource declaringGroup source
        projectionRef (some having) |>.mapError .starSource))
  | _, _ => throw .incoherentCore

private def certifyEnumerationFirstFilledOperands
    (declaringGroup : GroupPath) (scope : List RepeatableLevel) :
    List (ResolvedFieldEntityOperand model) →
      List SurfaceEnumerationFirstFilledOperand →
      Except EnumerationFirstFilledComputationElabError
        (List (CheckedEnumerationFirstFilledOperand model scope))
  | [], [] => pure []
  | resolved :: resolvedRest, authored :: authoredRest => do
      pure ((← certifyEnumerationFirstFilledOperand declaringGroup scope resolved authored) ::
        (← certifyEnumerationFirstFilledOperands declaringGroup scope resolvedRest authoredRest))
  | _, _ => throw .incoherentCore

def elaborateEnumerationFirstFilledSource
    (model : FlatModel) (declaringGroup : GroupPath)
    (scope : List RepeatableLevel)
    (authored : SurfaceEnumerationFirstFilledSource) :
    Except EnumerationFirstFilledComputationElabError
      (CheckedEnumerationFirstFilledSource model scope) := do
  let shape ← elaborateFieldEntityShapeIn model declaringGroup scope
      authored.toFieldEntitySource
    |>.mapError .shape
  let first ← certifyEnumerationFirstFilledOperand declaringGroup scope shape.first authored.first
  let rest ← certifyEnumerationFirstFilledOperands declaringGroup scope shape.rest authored.rest
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
  source : CheckedEnumerationFirstFilledSource model []
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
  let source ← elaborateEnumerationFirstFilledSource model declaringGroup [] authored
  if hReference : source.referencesField target.field = true then
    match source.measuredTargetReadMode? target.field target.projection with
    | some .plain => throw (.targetSelfReferenceAtPlainRead target.field)
    | some .projected => throw (.targetSelfReferenceAtProjectedRead target.field)
    | none => throw (.targetSelfReference target.field)
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
  match scanFilteredComputationFirstFilled having.condition
      { read := filterRead } outer
      (source.valueListCellAt .computation starRead)
      resolved.environments resolved.domain.hasOpenTail state with
  | .inl next => .inl next
  | .inr result => .inr result.asToken

private def scanEnumerationFirstFilledOperand
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) (state : FirstFilledScanState) :
    CheckedEnumerationFirstFilledOperand model [] →
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
    List (CheckedEnumerationFirstFilledOperand model []) → FirstFilledScanState →
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
def evaluate (source : CheckedEnumerationFirstFilledSource model [])
    (document : Document) (outer : Env) (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError FirstFilledTokenResult :=
  scanEnumerationFirstFilledOperands document outer (model.checkContext directRead)
    filterRead starRead source.operands {}

private def checkedDirectCellAt (document : CheckedDocument model)
    (environment : Env) (operand : FlatEnumerationOperand) :
    Except CheckedAddressingError (ValueListCell .token) := do
  let addressed ← document.addressedCell environment operand.field.id
  pure ((FlatTextFieldOperand.enumeration operand).checkedValueListCellAt
    .computation addressed.cell)

private def checkedStarCellAt (document : CheckedDocument model)
    (environment : Env) (source : CheckedStarEnumerationSource model) :
    Except CheckedAddressingError (ValueListCell .token) := do
  let addressed ←
    document.addressedCell environment source.source.declaration.id
  pure (source.operand.projection.asValueListCell
    (observeCell .computation addressed.cell))

private def scanCheckedDocumentOperand
    (document : CheckedDocument model) (outer : Env)
    (state : FirstFilledScanState) :
    CheckedEnumerationFirstFilledOperand model scope →
      Except CheckedAddressingError
        (FirstFilledScanState ⊕ FirstFilledTokenResult)
  | .field _ operand _ _ => do
      match state.step (← checkedDirectCellAt document outer operand) with
      | .continue next => pure (.inl next)
      | .done result => pure (.inr result.asToken)
  | .star source => do
      let resolved ←
        (source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      match source.filter with
      | none =>
          match ← scanFirstFilledItemsResolving
              (fun environment => checkedStarCellAt document environment source)
              resolved.environments
              (state.enterSelection resolved.environments.isEmpty
                resolved.domain.hasOpenTail false) with
          | .inl next => pure (.inl next)
          | .inr result => pure (.inr result.asToken)
      | some having =>
          match ← scanFilteredComputationFirstFilledResolving having.condition
              document.resolvingCorrelationContext outer
              (fun environment => checkedStarCellAt document environment source)
              resolved.environments resolved.domain.hasOpenTail state with
          | .inl next => pure (.inl next)
          | .inr result => pure (.inr result.asToken)

private def scanCheckedDocumentOperands
    (document : CheckedDocument model) (outer : Env) :
    List (CheckedEnumerationFirstFilledOperand model scope) → FirstFilledScanState →
      Except CheckedAddressingError FirstFilledTokenResult
  | [], _ => pure .noValue
  | operand :: remaining, state => do
      match ← scanCheckedDocumentOperand document outer state operand with
      | .inl next => scanCheckedDocumentOperands document outer remaining next
      | .inr result => pure result

/-- Evaluate the checked Enumeration/category source against one immutable checked document. Exact addressed reads and resolving filters keep structural failure outside token poison while preserving the shared lazy first-filled scan. -/
def evaluateCheckedDocument
    (source : CheckedEnumerationFirstFilledSource model scope)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError FirstFilledTokenResult :=
  scanCheckedDocumentOperands document outer source.operands {}

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
  pure selected.asComputationResult.asExactStringTargetOutcome

/-- Execute the existing checked first-filled scan over the immutable source topology and caller-supplied computation overlay, then classify its exact token against that immutable source target through the established model-certified Enumeration result. Structural star-addressing failure remains outside the result. -/
def executeResult
    (operation : CheckedEnumerationFirstFilledComputationOperation model)
    (input : CheckedDocument model) (outer : Env)
    (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell)
    (residualMessages : List ResidualMessage) :
    Except StarAddressingError
      (EnumerationComputationRunView model ResidualMessage) := do
  let selected ← operation.source.evaluate input.source.toDocument outer
    directRead filterRead starRead
  pure (EnumerationComputationRunView.fromTokenResult operation.target input
    residualMessages selected.asComputationResult)

end CheckedEnumerationFirstFilledComputationOperation

end A12Kernel
