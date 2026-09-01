import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarGroup
import A12Kernel.Elaboration.StarPath
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Shared checked field entity-list shape

This boundary owns the kind-independent authoring shape shared by ordinary aggregate field lists. It resolves direct, plain-star, filtered-star, and group-scope slots in authored order, applies the star, arity, and both duplicate gates, and requires either multiple slots or one already-many slot. It also owns the shared `FieldValuesNotUnique` kind/category classification and whole-list scans, while family-specific modules choose a required category, certify the declarations, and retain their own runtime semantics.

A group-scope operand makes the three gates visibly read three different things, which is why they are stated separately here rather than folded into one predicate. **Arity** reads the authored slots, so one group slot is already-many where its single expanded field authored alone is not. The **wildcard** gate reads the authored path and checks the operand at its own level only, which is what makes a group operand and its own written-out expansion two different models rather than two spellings of one. The **kind and category** scans read the group's recursive expansion, because a group declares no kind of its own.

Slot resolution admits the shape; a family's own certification decides whether that operator accepts a group at all, and no verdict there transfers between carriers.
-/

namespace A12Kernel

/-- How one direct slot reads its field. Most families can read a field only one way and leave every slot `.stored`; an Enumeration list may read one field both plainly and through a category projection. The Kernel counts those two reads as distinct operands rather than a repeated one, so this discriminator is part of operand identity and must survive path resolution. -/
inductive FieldEntityReadForm where
  | stored
  | projected (category : String)
  deriving Repr, DecidableEq

/-- One parser-independent field entity-list slot. A filter belongs to its exact authored wildcard occurrence, and a group slot retains its authored path rather than its expansion, because the wildcard gate reads the path that was written. -/
inductive SurfaceFieldEntityOperand where
  | field (path : SurfaceFieldPath) (form : FieldEntityReadForm := .stored)
  | star (path : SurfaceStarFieldPath)
  | starHaving (path : SurfaceStarFieldPath) (having : SurfaceCorrelatedHaving)
  | group (reference : SurfaceGroupReference)
  | starredGroup (reference : SurfaceStarGroupPath)
  deriving Repr, DecidableEq

/-- A nonempty authored field entity list. Checked construction separately enforces that a sole operand is starred. -/
structure SurfaceFieldEntitySource where
  first : SurfaceFieldEntityOperand
  rest : List SurfaceFieldEntityOperand
  deriving Repr, DecidableEq

/-- One direct field operand authored inside a `Having` expression. The origin is part of the
    operand rather than ambient filter state because `$P` and `P` are different exact operands even
    when both paths resolve to the same declaration
    ([checkpoint](../../docs/SOURCES.md#src-pr2-correlated-operand-identity)). -/
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

/-- One kind-neutral resolved slot. Family-specific certification occurs only after the complete list has passed the star, duplicate, and cardinality gates.

    A starred group retains the terminal-repeatable source only. A star above a nonrepeatable terminal is a third repetition shape that no retained observation covers on this carrier, so resolution refuses it without naming a class. -/
inductive ResolvedFieldEntityOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl) (form : FieldEntityReadForm)
  | star (source : CheckedStarFieldPath model)
  | starHaving (source : CheckedStarFieldPath model)
      (having : SurfaceCorrelatedHaving)
  | group (reference : ResolvedGroupReference)
  | starredGroup (source : CheckedStarredGroupSource model)
  | starredGroupPresence (source : CheckedStarredGroupPresenceSource model)

namespace ResolvedFieldEntityOperand

/-- Whether one authored slot already satisfies the multiple-operand requirement by itself. A star denotes a row set and a group denotes a field scope, so both are already-many; this is exactly why one group slot is admitted where its single expanded field authored alone reports `MVK_PARAMSIZE_INVALIDN`. -/
def isAlreadyMany : ResolvedFieldEntityOperand model → Bool
  | .field .. => false
  | .star _ | .starHaving _ _ | .group _ | .starredGroup _ |
      .starredGroupPresence _ => true

def directFieldId? : ResolvedFieldEntityOperand model → Option FieldId
  | .field declaration _ => some declaration.id
  | .star _ | .starHaving _ _ | .group _ | .starredGroup _ |
      .starredGroupPresence _ => none

/-- The group subtree a slot denotes, or `none` for a slot that denotes one field. Only the indirect duplicate arm and the expansion consult it. -/
def subtreePath? : ResolvedFieldEntityOperand model → Option GroupPath
  | .field .. | .star _ | .starHaving _ _ => none
  | .group reference => some reference.path
  | .starredGroup source => some source.group.path
  | .starredGroupPresence source => some source.groupPath

/-- The declarations this slot contributes to the kind and category gates. A field-denoting slot contributes its own declaration whatever its addressing form; a group contributes its recursive subtree, because a group declares no kind that could be classified instead. -/
def expansionDeclarations : ResolvedFieldEntityOperand model →
    List FlatFieldDecl
  | .field declaration _ => [declaration]
  | .star source | .starHaving source _ => [source.declaration]
  | .group reference => model.groupSubtreeFields reference.path
  | .starredGroup source => model.groupSubtreeFields source.group.path
  | .starredGroupPresence source => model.groupSubtreeFields source.groupPath

/-- The authored path each slot occupies for the indirect duplicate arm. -/
def entityPath : ResolvedFieldEntityOperand model → List String
  | .field declaration _ => declaration.path
  | .star source | .starHaving source _ => source.declaration.path
  | .group reference => reference.path
  | .starredGroup source => source.group.path
  | .starredGroupPresence source => source.groupPath

/-- The **indirect** duplicate arm. Two group operands overlap only by strict ancestry, so the same starred group written twice stays two independent authored occurrences while a starred group beside its own starred descendant is rejected. A group also overlaps any field-denoting slot inside it.

    Two field-denoting slots never reach this arm: a field path cannot be an ancestor of another, and their repetition belongs to the direct arm above, which skips wildcarded references. -/
def overlaps (left right : ResolvedFieldEntityOperand model) : Bool :=
  match left.subtreePath?, right.subtreePath? with
  | some leftPath, some rightPath =>
      leftPath != rightPath &&
        (leftPath.isPrefixOf rightPath || rightPath.isPrefixOf leftPath)
  | some leftPath, none =>
      match right with
      | .field declaration _ => leftPath.isPrefixOf declaration.groupPath
      | .star source | .starHaving source _ =>
          leftPath.isPrefixOf source.declaration.groupPath
      | .group _ | .starredGroup _ | .starredGroupPresence _ => false
  | none, some rightPath =>
      match left with
      | .field declaration _ => rightPath.isPrefixOf declaration.groupPath
      | .star source | .starHaving source _ =>
          rightPath.isPrefixOf source.declaration.groupPath
      | .group _ | .starredGroup _ | .starredGroupPresence _ => false
  | none, none => false

end ResolvedFieldEntityOperand

/-- The fixed and starred shapes an authored group-scope slot can take, shared by every carrier that retains one. A starred path preserves whether its terminal group is repeatable or ordinary. Every shape retains the **authored** reference: the wildcard gate reads the authored path, so a group operand and its written-out expansion are two different models and lowering one into the other can emit a model the Kernel refuses. -/
inductive CheckedEntityGroupSource (model : FlatModel) where
  | fixed (reference : ResolvedGroupReference)
  | starred (source : CheckedStarredGroupSource model)
  | starredPresence (source : CheckedStarredGroupPresenceSource model)

namespace CheckedEntityGroupSource

def groupPath : CheckedEntityGroupSource model → GroupPath
  | .fixed reference => reference.path
  | .starred source => source.group.path
  | .starredPresence source => source.groupPath

def isStarred : CheckedEntityGroupSource model → Bool
  | .fixed _ => false
  | .starred _ | .starredPresence _ => true

/-- Repeatable levels the surrounding rule environment must already bind. A fixed child retains the
exact scope certified by shared group resolution; either starred terminal shape binds only the
levels above its first star. -/
def bindingScope : CheckedEntityGroupSource model → List RepeatableLevel
  | .fixed reference => reference.boundRepeatableScope
  | .starred source => source.path.bindingScope
  | .starredPresence source => source.path.bindingScope

/-- **The operand's own depth**: how many of a reached declaration's repeatable levels stay fixed by the surrounding environment. Every level from here down is free, whatever the rule iterates.

    One quantity serves both of the operand's channels — the `(row × field)` extent it compares and the `referenced` set it publishes — and that is the point rather than a convenience. The two disagreeing about one operand's own extent is the cheapest available signal that one of them is wrong, and it is how a12-dmkits found the same defect in its own evaluator at `c1eb1614`, having fixed only the reference channel one commit earlier.

    Either starred terminal shape supplies its star plan's `firstStar`. A fixed group supplies the whole repeatable scope of its authored path; its own level is nonrepeatable under the wildcard gate, so that is the levels above it. -/
def boundLevelCount : CheckedEntityGroupSource model → Nat
  | .fixed reference =>
      (model.repeatableScopeForGroupPath reference.path).length
  | .starred source => source.path.firstStar
  | .starredPresence source => source.path.firstStar

end CheckedEntityGroupSource

/-- One comparability category admitted by the Kernel's field-list operators. String and Enumeration remain distinct even though both use the token runtime domain. -/
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

/-- The first expanded declaration of the whole list, whose comparability category the rest must match. A family that derives its expected category from the list itself reads it here rather than from the first *slot*, because a group slot carries no declaration of its own.

    `none` means no slot expanded to any declaration at all — a fieldless repeatable group is resolvable. The category gate then has nothing to compare and the caller's certification decides. -/
def firstFieldListDeclaration? :
    List (ResolvedFieldEntityOperand model) → Option FlatFieldDecl
  | [] => none
  | operand :: remaining =>
      match operand.expansionDeclarations with
      | [] => firstFieldListDeclaration? remaining
      | declaration :: _ => some declaration

/-- Scan the complete operand list before category certification so a kind refusal preempts mixing in every authored order.

    Every slot is scanned through its expansion, so a group is classified by the fields it reaches rather than by a declaration it does not have. The recursion matters: a group whose direct children are all admissible still reports the refusal a nested subgroup's field carries. -/
def firstFieldListKindRefusal? :
    List (ResolvedFieldEntityOperand model) → Option FieldListKindRefusal
  | [] => none
  | operand :: remaining =>
      match firstExpandedKindRefusal? operand.expansionDeclarations with
      | some refusal => some refusal
      | none => firstFieldListKindRefusal? remaining

/-- After the complete kind scan succeeds, find the first expanded declaration outside `expected`. The `refusedByKind` arm keeps this helper total; checked entry points run the required kind scan first. -/
def firstFieldListCategoryMismatch?
    (expected : FieldListComparabilityCategory) :
    List (ResolvedFieldEntityOperand model) → Option FieldListCategoryMismatch
  | [] => none
  | operand :: remaining =>
      match firstExpandedCategoryMismatch? expected operand.expansionDeclarations with
      | some mismatch => some mismatch
      | none => firstFieldListCategoryMismatch? expected remaining

/-- The source-shape failures shared by every homogeneous aggregate family. -/
inductive FieldEntityShapeElabError where
  | resolve (error : ResolveError)
  | starPath (error : StarPathElabError)
  | groupReference (error : FixedGroupReferenceError)
  | starredGroup (error : StarredGroupElabError)
  | tooFewFields
  | duplicateOperand (field : FieldId)
  | duplicateGroupOperand (path : GroupPath)
  | overlappingOperands (ancestor descendant : List String)
  deriving Repr, DecidableEq

/-- The gates this shared checker owns, projected once. Every carrier in the family routes through the same resolution, so these classes do not vary by carrier even where a row measured only one. -/
def FieldEntityShapeElabError.diagnostic? :
    FieldEntityShapeElabError → Option KernelStaticDiagnostic
  | .tooFewFields => some .paramSizeInvalidN
  | .duplicateOperand _ => some .duplicateParam1
  | .duplicateGroupOperand _ => some .duplicateParam1
  | .overlappingOperands _ _ => some .duplicateParam2
  | .resolve error => error.diagnostic?
  | .groupReference (.repeatableGroupRequiresAddress _) => some .noWildcard
  | .starredGroup (.path (.wildcardOnNonrepeatable _)) => some .invalidWildcard
  | .starPath (.iterationBelowWildcard _) => some .noWildcard
  | _ => none

def firstDuplicateOptionalIdentity? [BEq β] (identity? : α → Option β) :
    List α → Option β
  | [] => none
  | operand :: remaining =>
      match identity? operand with
      | none => firstDuplicateOptionalIdentity? identity? remaining
      | some identity =>
          if remaining.any fun candidate => identity? candidate == some identity then
            some identity
          else
            firstDuplicateOptionalIdentity? identity? remaining

def firstDuplicateDirectField? (directFieldId? : α → Option FieldId) :
    List α → Option FieldId :=
  firstDuplicateOptionalIdentity? directFieldId?

/-- One exact non-wildcard operand identity. Field reading form is semantic identity, while fixed
    groups identify by path. Starred occurrences intentionally have no exact identity. -/
inductive ResolvedFieldEntityIdentity where
  | field (identity : FieldId × FieldEntityReadForm)
  | fixedGroup (path : GroupPath)
  deriving Repr, DecidableEq

def ResolvedFieldEntityOperand.exactIdentity? :
    ResolvedFieldEntityOperand model → Option ResolvedFieldEntityIdentity
  | .field declaration form => some (.field (declaration.id, form))
  | .group reference => some (.fixedGroup reference.path)
  | .star _ | .starHaving _ _ | .starredGroup _ |
      .starredGroupPresence _ => none

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

def firstDuplicateResolvedEntityOperand? :
    List (ResolvedFieldEntityOperand model) → Option ResolvedFieldEntityIdentity :=
  firstDuplicateInEncounterOrder? ResolvedFieldEntityOperand.exactIdentity?

/-- Report the first authored ancestor/descendant pair, naming both paths in authored order. -/
def firstResolvedOperandOverlap? :
    List (ResolvedFieldEntityOperand model) →
      Option (List String × List String)
  | [] => none
  | operand :: remaining =>
      match remaining.find? (operand.overlaps ·) with
      | some overlapping => some (operand.entityPath, overlapping.entityPath)
      | none => firstResolvedOperandOverlap? remaining

/-- A resolved, model-owned entity-list shape before homogeneous family certification. -/
structure CheckedFieldEntityShape (model : FlatModel) where
  first : ResolvedFieldEntityOperand model
  rest : List (ResolvedFieldEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isAlreadyMany || !rest.isEmpty) = true
  uniqueExactOperands :
    firstDuplicateResolvedEntityOperand? (first :: rest) = none
  disjointOperands : firstResolvedOperandOverlap? (first :: rest) = none

namespace CheckedFieldEntityShape

def operands (checked : CheckedFieldEntityShape model) :
    List (ResolvedFieldEntityOperand model) :=
  checked.first :: checked.rest

end CheckedFieldEntityShape

/-- Resolve one field-entity operand after the caller has established model validity. Whole-list cardinality, duplicate, and overlap gates remain with `elaborateFieldEntityShape`.

    `scope` is the reading rule's own iteration scope. An unstarred field operand is accepted when
    that scope binds every repeatable level it crosses, so the empty scope is the scalar rule and a
    rule iterating a level may read an operand inside it. Starred and group operands carry their own
    topology and are unaffected. -/
def resolveFieldEntityOperandIn (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel) :
    SurfaceFieldEntityOperand →
      Except FieldEntityShapeElabError (ResolvedFieldEntityOperand model)
  | .field path form => do
      let resolved ←
        model.resolveFieldDeclarationUnchecked declaringGroup path
          |>.mapError .resolve
      let declaration ← resolved.requireRepetitionBoundBy scope
        |>.mapError .resolve
      pure (.field declaration form)
  | .star path => do
      pure (.star (← elaborateStarFieldPath model declaringGroup path
        |>.mapError .starPath))
  | .starHaving path having => do
      pure (.starHaving
        (← elaborateStarFieldPath model declaringGroup path
          |>.mapError .starPath)
        having)
  | .group reference => do
      pure (.group (← model.resolveFixedGroupReference declaringGroup reference
        |>.mapError .groupReference))
  | .starredGroup reference => do
      match ← elaborateStarredGroupOperandSource model declaringGroup reference
          |>.mapError .starredGroup with
      | .terminalRepeatable source => pure (.starredGroup source)
      | .terminalPresence source => pure (.starredGroupPresence source)

/-- The scalar instance: an operand read where no repeatable level is bound. -/
def resolveFieldEntityOperandUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntityOperand) :
    Except FieldEntityShapeElabError (ResolvedFieldEntityOperand model) :=
  resolveFieldEntityOperandIn model declaringGroup [] authored

private def resolveFieldEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel) :
    List SurfaceFieldEntityOperand →
      Except FieldEntityShapeElabError
        (List (ResolvedFieldEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolveFieldEntityOperandIn model declaringGroup scope operand) ::
        (← resolveFieldEntityOperands model declaringGroup scope remaining))

/-- Validate the common entity-list shape: model, path resolution and its star gate, exact duplicates in authored encounter order, ancestor/descendant overlap, then the multiple-slots-or-one-already-many cardinality gate.

    Path resolution precedes the whole-list gates and the kind scan follows them. Every exact non-wildcard identity shares one scan, independent of field/group class; strict ancestor overlap follows it. Cardinality is structurally separate on this typed surface: its singleton direct-field input cannot also contain a repeated or overlapping pair. -/
def elaborateFieldEntityShapeIn (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel)
    (authored : SurfaceFieldEntitySource) :
    Except FieldEntityShapeElabError (CheckedFieldEntityShape model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let first ←
        resolveFieldEntityOperandIn model declaringGroup scope authored.first
      let rest ← resolveFieldEntityOperands model declaringGroup scope authored.rest
      match hDuplicate : firstDuplicateResolvedEntityOperand? (first :: rest) with
      | some (.field (field, _)) => throw (.duplicateOperand field)
      | some (.fixedGroup path) => throw (.duplicateGroupOperand path)
      | none =>
          match hOverlap : firstResolvedOperandOverlap? (first :: rest) with
          | some (ancestor, descendant) =>
              throw (.overlappingOperands ancestor descendant)
          | none =>
              if hMultiplicity : first.isAlreadyMany || !rest.isEmpty then
                pure {
                  first
                  rest
                  modelWellFormed := by rw [hModel]; rfl
                  requiredMultiplicity := hMultiplicity
                  uniqueExactOperands := hDuplicate
                  disjointOperands := hOverlap }
              else
                throw .tooFewFields

/-- The scalar instance of the shared shape gates. -/
def elaborateFieldEntityShape (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except FieldEntityShapeElabError (CheckedFieldEntityShape model) :=
  elaborateFieldEntityShapeIn model declaringGroup [] authored

/-- One direct `Having` operand after origin-sensitive scope resolution. The resolved declaration,
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

private def resolveHavingDirectFieldOperand (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels capturedLevels : List RepeatableLevel)
    (authored : SurfaceHavingDirectFieldOperand) :
    Except FieldEntityShapeElabError (ResolvedHavingDirectFieldOperand model) := do
  let resolved ← model.resolveFieldDeclarationUnchecked declaringGroup authored.field
    |>.mapError .resolve
  let declaration ← resolved.requireRepetitionBoundBy
      (authored.origin.availableLevels candidateLevels capturedLevels)
    |>.mapError .resolve
  pure { origin := authored.origin, declaration, form := authored.form }

private def resolveHavingDirectFieldOperands (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels capturedLevels : List RepeatableLevel) :
    List SurfaceHavingDirectFieldOperand →
      Except FieldEntityShapeElabError
        (List (ResolvedHavingDirectFieldOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolveHavingDirectFieldOperand model declaringGroup candidateLevels
        capturedLevels operand) ::
        (← resolveHavingDirectFieldOperands model declaringGroup candidateLevels
          capturedLevels remaining))

/-- Check a direct field list nested inside `Having`. Resolution selects the candidate or captured
    scope per operand before one shared exact-identity scan; carrier-specific kind and runtime gates
    intentionally remain with the containing aggregate. -/
def elaborateHavingDirectFieldSource (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels capturedLevels : List RepeatableLevel)
    (authored : SurfaceHavingDirectFieldSource) :
    Except FieldEntityShapeElabError (CheckedHavingDirectFieldSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let first ← resolveHavingDirectFieldOperand model declaringGroup candidateLevels
        capturedLevels authored.first
      let rest ← resolveHavingDirectFieldOperands model declaringGroup candidateLevels
        capturedLevels authored.rest
      match hDuplicate :
          firstDuplicateResolvedHavingDirectField? (first :: rest) with
      | some identity => throw (.duplicateOperand identity.field)
      | none =>
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

/-- Every operand kind resolves only against a representable declaring group, so a checked
    entity-list shape certifies its declaring group without re-testing it.

    Each arm's guard belongs to that arm's own owner and is stated there; this composes the five
    rather than restating any. A family building a certificate over this shape can therefore carry
    `declaringGroup` with its validity attached instead of leaving it uncertified. -/
theorem resolveFieldEntityOperandIn_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath} {scope : List RepeatableLevel}
    {authored : SurfaceFieldEntityOperand} {resolved : ResolvedFieldEntityOperand model}
    (ok : resolveFieldEntityOperandIn model declaringGroup scope authored = .ok resolved) :
    GroupPath.isValid declaringGroup = true := by
  unfold resolveFieldEntityOperandIn at ok
  cases authored with
  | field path form =>
      cases hResolved :
        model.resolveFieldDeclarationUnchecked declaringGroup path with
      | error _ =>
          simp only [hResolved, bind, Except.bind, Except.mapError] at ok
          cases ok
      | ok declaration =>
          exact FlatModel.resolveFieldDeclarationUnchecked_declaringGroupValid hResolved
  | star path =>
      cases hStar : elaborateStarFieldPath model declaringGroup path with
      | error _ =>
          simp only [hStar, bind, Except.bind, Except.mapError] at ok
          cases ok
      | ok checked => exact elaborateStarFieldPath_declaringGroupValid hStar
  | starHaving path having =>
      cases hStar : elaborateStarFieldPath model declaringGroup path with
      | error _ =>
          simp only [hStar, bind, Except.bind, Except.mapError] at ok
          cases ok
      | ok checked => exact elaborateStarFieldPath_declaringGroupValid hStar
  | group reference =>
      cases hGroup : model.resolveFixedGroupReference declaringGroup reference with
      | error _ =>
          simp only [hGroup, bind, Except.bind, Except.mapError] at ok
          cases ok
      | ok resolvedGroup =>
          exact FlatModel.resolveFixedGroupReference_declaringGroupValid hGroup
  | starredGroup reference =>
      cases hSource :
        elaborateStarredGroupOperandSource model declaringGroup reference with
      | error _ =>
          simp only [hSource, bind, Except.bind, Except.mapError] at ok
          cases ok
      | ok source =>
          exact elaborateStarredGroupOperandSource_declaringGroupValid hSource

/-- A checked entity-list shape therefore certifies its declaring group: the list is nonempty by
    construction, so its first operand always reaches one of those guards. -/
theorem elaborateFieldEntityShapeIn_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath} {scope : List RepeatableLevel}
    {authored : SurfaceFieldEntitySource} {checked : CheckedFieldEntityShape model}
    (ok : elaborateFieldEntityShapeIn model declaringGroup scope authored = .ok checked) :
    GroupPath.isValid declaringGroup = true := by
  unfold elaborateFieldEntityShapeIn at ok
  split at ok
  · cases ok
  · cases hFirst :
      resolveFieldEntityOperandIn model declaringGroup scope authored.first with
    | error _ =>
        simp only [hFirst, bind, Except.bind] at ok
        cases ok
    | ok first => exact resolveFieldEntityOperandIn_declaringGroupValid hFirst

/-- The scalar specialization inherits it unchanged. -/
theorem elaborateFieldEntityShape_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath}
    {authored : SurfaceFieldEntitySource} {checked : CheckedFieldEntityShape model}
    (ok : elaborateFieldEntityShape model declaringGroup authored = .ok checked) :
    GroupPath.isValid declaringGroup = true :=
  elaborateFieldEntityShapeIn_declaringGroupValid ok

end A12Kernel
