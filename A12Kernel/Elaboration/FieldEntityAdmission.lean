import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.KeyedEntityExtent
import A12Kernel.Elaboration.StarGroup
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.CorrelationInputs

/-! Kind-neutral entity-list admission and correlated direct-list certificates. -/

namespace A12Kernel

/-- How one direct slot reads its field. Most families can read a field only one way and leave every slot `.stored`; an Enumeration list may read one field both plainly and through a category projection. The Kernel counts those two reads as distinct operands rather than a repeated one, so this discriminator is part of operand identity and must survive path resolution. -/
inductive FieldEntityReadForm where
  | stored
  | projected (category : String)
  deriving Repr, DecidableEq

/-- One direct field operand authored inside a `Having` expression. The origin is part of the
    operand rather than ambient filter state because `$P` and `P` are different exact operands even
    when both paths resolve to the same declaration
    ([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-pr2-correlated-operand-identity)). -/
structure SurfaceHavingDirectFieldOperand where
  origin : HavingOrigin
  field : SurfaceFieldPath
  form : FieldEntityReadForm := .stored
  deriving Repr, DecidableEq

/-- A nonempty direct field list nested inside `Having`. Carrier-specific kind gates remain outside
    this shared authoring shape. -/
structure SurfaceHavingDirectFieldSource where
  first : SurfaceHavingDirectFieldOperand
  rest : List SurfaceHavingDirectFieldOperand
  deriving Repr, DecidableEq

/-- Entity-list syntax inside a filter preserves stars and origins before model lookup
(spec/07 §3 and §5). An unstarred entity may name a field or a group. -/
inductive SurfaceHavingEntityOperand where
  | entity (reference : SurfaceHavingDirectFieldOperand)
  | star (origin : HavingOrigin) (path : SurfaceStarGroupPath) (form : FieldEntityReadForm := .stored)
  | group (origin : HavingOrigin) (reference : SurfaceGroupReference)
  deriving Repr, DecidableEq

structure SurfaceHavingEntitySource where
  first : SurfaceHavingEntityOperand
  rest : List SurfaceHavingEntityOperand
  deriving Repr, DecidableEq

def SurfaceHavingEntityOperand.origin : SurfaceHavingEntityOperand → HavingOrigin
  | .entity reference => reference.origin
  | .star origin _ _ | .group origin _ => origin

/-- Only the authored unstarred prefix participates in the surrounding filter's binding gates;
a group's recursively expanded declarations do not create authored iteration reads (spec/07 §3). -/
def SurfaceHavingEntityOperand.bindingRead? (model : FlatModel) (declaringGroup : GroupPath) :
    SurfaceHavingEntityOperand → Option (GroupPath × List RepeatableLevel)
  | .entity reference =>
      match (model.resolveFieldDeclarationUnchecked declaringGroup reference.field).toOption with
      | some declaration => some (declaration.path, declaration.repeatableScope)
      | none => do
          let path ← model.groupNamedBy? declaringGroup reference.field
          pure (path, model.repeatableScopeForGroupPath path)
  | .group _ reference => do
      let resolved ← (reference.resolveAgainst declaringGroup).toOption
      pure (resolved.path, model.repeatableScopeForGroupPath resolved.path)
  | .star _ path _ => do
      let last ← path.groups.getLast?
      let field : SurfaceStarFieldPath := {
        base := path.base, groups := path.groups.dropLast, field := last.name }
      if !last.starred && (model.resolveFieldDeclarationUnchecked declaringGroup field.toFieldPath).isOk then
        let resolved ← (elaborateStarFieldPath model declaringGroup field).toOption
        pure (resolved.declaration.path, resolved.bindingScope)
      else
        let resolved ← (elaborateStarredGroupOperandSource model declaringGroup path).toOption
        match resolved with
        | .terminalRepeatable source => pure (source.group.path, source.path.bindingScope)
        | .terminalPresence source => pure (source.groupPath, source.path.bindingScope)

/-- The source-shape failures shared by every homogeneous aggregate family. -/
inductive FieldEntityShapeElabError where
  | keyed (error : KeyedEntityExtentError)
  | unsupportedIndexedOperand (path : List String)
  | semanticIndex (error : SemanticIndexElabError)
  | resolve (error : ResolveError)
  | starPath (error : StarPathElabError)
  | groupReference (error : FixedGroupReferenceError)
  | starredGroup (error : StarredGroupElabError)
  | tooFewFields
  | duplicateOperand (field : FieldId)
  | duplicateGroupOperand (path : GroupPath)
  | overlappingOperands (ancestor descendant : List String)
  /-- A fixed root group in a list that passed both duplicate scans. Every entity of a model lies
      under its root, so this arm is reached only by a root alone or beside another root's entities
      ([checkpoint](../../docs/sources/inbound-handbacks.md#inbound-2026-09-23-entity-list-root-group-gate)). -/
  | rootGroupOperand (path : GroupPath)
  /-- On a fixed-target arm, an operand leaves a repeatable level for its evaluation to bind. The
      whole list is judged before the duplicate scans, as the Kernel's missing-star bar is
      ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
  | unboundOperandLevel (unbound : UnboundOperandLevel)
  /-- An Enumeration's category in a list whose carrier asks the category gate. -/
  | categoryNotAllowed (path : List String)
  /-- A category the Enumeration does not declare, refused as the slot is read. -/
  | unknownCategory (path : List String) (category : String)
  deriving Repr, DecidableEq

/-- The gates this shared checker owns, projected once. The **classes** do not vary by carrier, and
a row measured at one carrier fixes the code everywhere.

**Whether a gate fires does vary, and the arity gate is measured to.** All three value-list
quantifiers accept a *sole unstarred field* operand, where the entity-list carriers refuse one with
`MVK_PARAMSIZE_INVALIDN`
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-value-list-quantifier-kind-gate-partitions-three-ways)), so
each carrier passes the `EntityListArity` it applies. -/
def FieldEntityShapeElabError.diagnostic? :
    FieldEntityShapeElabError → Option KernelStaticDiagnostic
  | .keyed (.index error) => error.diagnostic?
  | .keyed _ => none
  | .unsupportedIndexedOperand _ => none
  | .semanticIndex error => error.diagnostic?
  | .tooFewFields => some .paramSizeInvalidN
  | .duplicateOperand _ => some .duplicateParam1
  | .duplicateGroupOperand _ => some .duplicateParam1
  | .overlappingOperands _ _ => some .duplicateParam2
  | .rootGroupOperand _ => some .rootGroupReferenced
  | .categoryNotAllowed _ => some .categoryNotAllowed
  | .unknownCategory _ _ => some .categoryUnknown
  | .unboundOperandLevel unbound => unbound.diagnostic?
  | .resolve error => error.diagnostic?
  | .groupReference error => error.diagnostic?
  | .starredGroup error => error.diagnostic?
  | .starPath error => error.diagnostic?

/-- A category's read gates precede enclosing list gates, including duplicates and base type
(spec/06 §B.3 and the list-read account in docs/SOURCES.md#inbound-2026-09-26h-list-reads). -/
def FlatFieldDecl.checkEntityCategoryRead (declaration : FlatFieldDecl) (form : FieldEntityReadForm) :
    Except FieldEntityShapeElabError Unit :=
  match form, declaration.categoryReadRefusal? with
  | .projected _, some refusal => throw (.resolve refusal)
  | .projected category, none =>
      if declaration.enumeration.any (·.categories.any (·.name == category)) then pure ()
      else throw (.unknownCategory declaration.path category)
  | .stored, _ => pure ()

/-- Strict containment is the indirect list-duplicate relation; equal starred paths retain
separate authored slots (spec/07 §5 and spec/08 §4). -/
def entityListPathsOverlap (left right : List String) (leftGroup rightGroup : Bool) : Bool :=
  left != right && ((leftGroup && left.isPrefixOf right) || (rightGroup && right.isPrefixOf left))

/-- Report the first exact duplicate whose second occurrence completes in authored encounter order. -/
private def firstDuplicateInEncounterOrderFrom? [BEq β]
    (identity? : α → Option β) (seen : List β) : List α → Option β
  | [] => none
  | operand :: remaining =>
      match identity? operand with
      | none => firstDuplicateInEncounterOrderFrom? identity? seen remaining
      | some identity =>
          if seen.contains identity then some identity
          else firstDuplicateInEncounterOrderFrom? identity? (identity :: seen) remaining

/-- Report the identity whose repeated occurrence arrives first. Unlike a lookahead scan, this
    preserves authored encounter order when two different identities both repeat. -/
def firstDuplicateInEncounterOrder? [BEq β] (identity? : α → Option β)
    (operands : List α) : Option β :=
  firstDuplicateInEncounterOrderFrom? identity? [] operands

/-- One resolved direct `Having` operand with its authored environment identity. The resolved declaration,
    read form, and origin together are its exact authored identity. -/
structure ResolvedHavingDirectFieldOperand (model : FlatModel) where
  origin : HavingOrigin
  declaration : FlatFieldDecl
  form : FieldEntityReadForm
  deriving Repr, DecidableEq

structure HavingDirectFieldIdentity where
  origin : HavingOrigin
  field : FieldId
  form : FieldEntityReadForm
  deriving Repr, DecidableEq

def ResolvedHavingDirectFieldOperand.exactIdentity
    (operand : ResolvedHavingDirectFieldOperand model) : HavingDirectFieldIdentity :=
  { origin := operand.origin, field := operand.declaration.id, form := operand.form }

def firstDuplicateResolvedHavingDirectField? :
    List (ResolvedHavingDirectFieldOperand model) → Option HavingDirectFieldIdentity :=
  firstDuplicateInEncounterOrder? fun operand => some operand.exactIdentity

/-- A resolved direct list nested in `Having`. It retains both environment scopes for Analyze and
    Transform consumers while certifying model validity, list multiplicity, and exact uniqueness. -/
structure CheckedHavingDirectFieldSource (model : FlatModel) where
  first : ResolvedHavingDirectFieldOperand model
  rest : List (ResolvedHavingDirectFieldOperand model)
  candidateLevels : List RepeatableLevel
  capturedLevels : List RepeatableLevel
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (!rest.isEmpty) = true
  uniqueExactOperands :
    firstDuplicateResolvedHavingDirectField? (first :: rest) = none

namespace CheckedHavingDirectFieldSource

def operands (checked : CheckedHavingDirectFieldSource model) :
    List (ResolvedHavingDirectFieldOperand model) :=
  checked.first :: checked.rest

end CheckedHavingDirectFieldSource

/-- A filter checks its complete body before the candidate-iteration gate (spec/07 §3).
Captured reads retain ordinary immediate scope admission in either mode. -/
inductive HavingDirectScopeAdmission where
  | immediate
  | deferCandidate
  deriving Repr, DecidableEq

private def resolveHavingDirectFieldOperand (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels capturedLevels : List RepeatableLevel)
    (admission : HavingDirectScopeAdmission) (requireStored : Bool) (authored : SurfaceHavingDirectFieldOperand) :
    Except FieldEntityShapeElabError (ResolvedHavingDirectFieldOperand model) := do
  let resolved ← model.resolveFieldDeclarationUnchecked declaringGroup authored.field
    |>.mapError .resolve
  let declaration ← match admission, authored.origin with
    | .deferCandidate, .inner => pure resolved
    | _, _ =>
        (resolved.requireRepetitionBoundBy
          (authored.origin.availableLevels candidateLevels capturedLevels)).mapError .resolve
  if requireStored then declaration.checkEntityCategoryRead authored.form
  pure { origin := authored.origin, declaration, form := authored.form }

private def resolveHavingDirectFieldOperands (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels capturedLevels : List RepeatableLevel)
    (admission : HavingDirectScopeAdmission) (requireStored : Bool) :
    List SurfaceHavingDirectFieldOperand →
      Except FieldEntityShapeElabError
        (List (ResolvedHavingDirectFieldOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolveHavingDirectFieldOperand model declaringGroup candidateLevels
        capturedLevels admission requireStored operand) ::
        (← resolveHavingDirectFieldOperands model declaringGroup candidateLevels
          capturedLevels admission requireStored remaining))

/-- Check model ownership, multiplicity and exact operand identity for a direct filter list.
The default checks both scopes immediately; a complete filter defers candidate availability until
its body gates finish, then certifies that availability through the shared filter predicate. -/
def elaborateHavingDirectFieldSource (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels capturedLevels : List RepeatableLevel)
    (authored : SurfaceHavingDirectFieldSource)
    (admission : HavingDirectScopeAdmission := .immediate) (requireStored : Bool := false) :
    Except FieldEntityShapeElabError (CheckedHavingDirectFieldSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let first ← resolveHavingDirectFieldOperand model declaringGroup candidateLevels
        capturedLevels admission requireStored authored.first
      let rest ← resolveHavingDirectFieldOperands model declaringGroup candidateLevels
        capturedLevels admission requireStored authored.rest
      match hDuplicate :
          firstDuplicateResolvedHavingDirectField? (first :: rest) with
      | some identity => throw (.duplicateOperand identity.field)
      | none =>
          if requireStored then
            if let some operand := (first :: rest).find? (fun operand => operand.form != .stored) then
              throw (.categoryNotAllowed operand.declaration.path)
          if hMultiplicity : !rest.isEmpty then
            pure {
              first
              rest
              candidateLevels
              capturedLevels
              modelWellFormed := by rw [hModel]; rfl
              requiredMultiplicity := hMultiplicity
              uniqueExactOperands := hDuplicate }
          else
            throw .tooFewFields

/-- One comparability category admitted by the Kernel's field-list operators. String and Enumeration remain distinct even though both use the token runtime domain.

`temporal` collapses DATE, TIME, DATETIME and DATEFRAGMENT, and that collapse is **measured rather than assumed**. A cross-kind temporal pair whose formats also differ moves two variables and is answered by the prior format gate, so only a pair sharing one identical declared format asks this gate anything. Four such pairs are admitted: DATE beside DATEFRAGMENT at `yyyy`, TIME beside DATETIME at `HH:mm:ss`, and a DATE declared with that same clock format beside each of the clock kinds ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-22-temporal-category)).

**The last two pairs are what make this one category rather than two.** Two admitted same-shape pairs are equally what two categories each holding two kinds would produce, so the pairs alone cannot tell one category from two; the spanning edge leaves every kind one measured edge from the rest. [`Conformance/TemporalValuesNotUnique`](../Conformance/TemporalValuesNotUnique.lean) locks all four with the format-gate and category-mismatch controls that keep them readable. This estate's DATEFRAGMENT shares `.date`'s constructor, so the first pair varies nothing here and the matrix rests on the other three. -/
inductive FieldListComparabilityCategory where
  | string | enumeration | number | temporal
  deriving Repr, DecidableEq

/-- The kind-only admission stage: one comparability category, or refusal before category comparison. -/
inductive FieldListOperandAdmission where
  | category (value : FieldListComparabilityCategory)
  | refusedByKind
  deriving Repr, DecidableEq

/-- Classify every represented scalar kind for the shared `FieldValuesNotUnique` kind gate. BOOLEAN, CONFIRM, and DATE_RANGE are measured outright refusals. -/
def SurfaceScalarKind.fieldListAdmission :
    SurfaceScalarKind → FieldListOperandAdmission
  | .string => .category .string
  | .enumeration => .category .enumeration
  | .number => .category .number
  | .temporal _ => .category .temporal
  | .boolean | .confirm | .dateRange => .refusedByKind

structure FieldListKindRefusal where
  path : List String
  actual : SurfaceScalarKind
  deriving Repr, DecidableEq

structure FieldListCategoryMismatch where
  path : List String
  actual : SurfaceScalarKind
  deriving Repr, DecidableEq

/-- Scan one slot's expansion for the first outright-refused kind. Public because the whole-list law is proved through it. -/
def firstExpandedKindRefusal? :
    List FlatFieldDecl → Option FieldListKindRefusal
  | [] => none
  | declaration :: remaining =>
      let actual := declaration.policy.kind.surfaceKind
      match actual.fieldListAdmission with
      | .refusedByKind => some { path := declaration.path, actual }
      | .category _ => firstExpandedKindRefusal? remaining

/-- Scan one slot's expansion for the first declaration outside `expected`. -/
def firstExpandedCategoryMismatch?
    (expected : FieldListComparabilityCategory) :
    List FlatFieldDecl → Option FieldListCategoryMismatch
  | [] => none
  | declaration :: remaining =>
      let actual := declaration.policy.kind.surfaceKind
      match actual.fieldListAdmission with
      | .refusedByKind => firstExpandedCategoryMismatch? expected remaining
      | .category category =>
          if category == expected then
            firstExpandedCategoryMismatch? expected remaining
          else some { path := declaration.path, actual }

end A12Kernel
