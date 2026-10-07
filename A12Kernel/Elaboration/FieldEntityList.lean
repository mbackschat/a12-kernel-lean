import A12Kernel.Elaboration.FieldEntityAdmission
import A12Kernel.Elaboration.SemanticIndex
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

/-- One parser-independent field entity-list slot. A filter belongs to its exact authored wildcard occurrence, and a group slot retains its authored path rather than its expansion, because the wildcard gate reads the path that was written. -/
inductive SurfaceFieldEntityOperand where
  | field (path : SurfaceFieldPath) (form : FieldEntityReadForm := .stored)
  | indexed (source : SurfaceSemanticIndex)
  | keyed (source : SurfaceKeyedEntityExtent)
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

/-- One kind-neutral resolved slot. Family-specific certification occurs only after the complete list has passed the star, duplicate, and cardinality gates.

    A starred group retains the terminal-repeatable source only. A star above a nonrepeatable terminal is a third repetition shape that no retained observation covers on this carrier, so resolution refuses it without naming a class. -/
inductive ResolvedFieldEntityOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl) (form : FieldEntityReadForm)
  | indexed (source : CheckedSemanticIndexSource model)
  | keyed (source : CheckedKeyedEntityExtent model)
  | star (source : CheckedStarFieldPath model)
  | starHaving (source : CheckedStarFieldPath model)
      (having : SurfaceCorrelatedHaving)
  | group (reference : ResolvedGroupReference)
  | starredGroup (source : CheckedStarredGroupSource model)
  | starredGroupPresence (source : CheckedStarredGroupPresenceSource model)

namespace ResolvedFieldEntityOperand

/-- Whether one authored slot already satisfies the multiple-operand requirement by itself. A star denotes a row set and a group denotes a field scope, so both are already-many; this is exactly why one group slot is admitted where its single expanded field authored alone reports `MVK_PARAMSIZE_INVALIDN`. -/
def isAlreadyMany : ResolvedFieldEntityOperand model → Bool
  | .field .. | .indexed _ => false
  | .keyed _ | .star _ | .starHaving _ _ | .group _ | .starredGroup _ |
      .starredGroupPresence _ => true

def directFieldId? : ResolvedFieldEntityOperand model → Option FieldId
  | .field declaration _ => some declaration.id
  | .indexed _ | .keyed _ | .star _ | .starHaving _ _ | .group _ | .starredGroup _ |
      .starredGroupPresence _ => none

/-- The group subtree a slot denotes, or `none` for a slot that denotes one field. Only the indirect duplicate arm and the expansion consult it. -/
def subtreePath? : ResolvedFieldEntityOperand model → Option GroupPath
  | .field .. | .indexed _ | .star _ | .starHaving _ _ => none
  | .keyed source => match source.target with | .group path | .starredGroup path => some path | .star _ => none
  | .group reference => some reference.path
  | .starredGroup source => some source.group.path
  | .starredGroupPresence source => some source.groupPath

/-- The declarations this slot contributes to the kind and category gates. A field-denoting slot contributes its own declaration whatever its addressing form; a group contributes its recursive subtree, because a group declares no kind that could be classified instead. -/
def expansionDeclarations : ResolvedFieldEntityOperand model →
    List FlatFieldDecl
  | .field declaration _ => [declaration]
  | .indexed source => [source.targetDeclaration]
  | .keyed source => source.declarations
  | .star source | .starHaving source _ => [source.declaration]
  | .group reference => model.groupSubtreeFields reference.path
  | .starredGroup source => model.groupSubtreeFields source.group.path
  | .starredGroupPresence source => model.groupSubtreeFields source.groupPath

/-- The root a fixed group slot names, for the list-level root-group gate. Only the fixed form is
    measured; a starred root would need a repeatable root, and no row places one on an entity list. -/
def rootGroupPath? : ResolvedFieldEntityOperand model → Option GroupPath
  | .group reference => if reference.isRoot then some reference.path else none
  | .field .. | .indexed _ | .keyed _ | .star _ | .starHaving _ _ | .starredGroup _ |
      .starredGroupPresence _ => none

/-- The Enumeration a category slot reads, for a carrier's category gate. A category of a field
    declaring no Enumeration, or one its Enumeration does not declare, was already refused as the
    slot resolved, and a starred slot spells no category on this surface. -/
def categoryPath? : ResolvedFieldEntityOperand model → Option (List String)
  | .field declaration (.projected _) => some declaration.path
  | .field _ .stored | .indexed _ | .keyed _ | .star _ | .starHaving _ _ | .group _ | .starredGroup _ |
      .starredGroupPresence _ => none

/-- The authored path each slot occupies for the indirect duplicate arm. -/
def entityPath : ResolvedFieldEntityOperand model → List String
  | .field declaration _ => declaration.path
  | .indexed source => source.targetDeclaration.path
  | .keyed source => source.entityPath
  | .star source | .starHaving source _ => source.declaration.path
  | .group reference => reference.path
  | .starredGroup source => source.group.path
  | .starredGroupPresence source => source.groupPath

def indexIdentity? : ResolvedFieldEntityOperand model → Option (GroupPath × CheckedSemanticIndexKey)
  | .indexed source => some (source.group.path, source.key)
  | .keyed source => some (source.selection.group.path, source.selection.key)
  | _ => none

/-- The **indirect** duplicate arm. Two group operands overlap only by strict ancestry, so the same starred group written twice stays two independent authored occurrences while a starred group beside its own starred descendant is rejected. A group overlaps a field-denoting slot inside it only when both carry the same index identity, or neither carries one (`CheckEntityListenUtils.isEntityIndirectlyReferenced`, kernel 30.8.1; `spec/08` §4).

    Two field-denoting slots never reach this arm: a field path cannot be an ancestor of another, and their repetition belongs to the direct arm above, which skips wildcarded references. -/
def overlaps (left right : ResolvedFieldEntityOperand model) : Bool :=
  if left.indexIdentity? != right.indexIdentity? then false else
  match left.subtreePath?, right.subtreePath? with
  | some leftPath, some rightPath =>
      leftPath != rightPath &&
        (leftPath.isPrefixOf rightPath || rightPath.isPrefixOf leftPath)
  | some leftPath, none =>
      match right with
      | .field declaration _ => leftPath.isPrefixOf declaration.groupPath
      | .star source | .starHaving source _ =>
          leftPath.isPrefixOf source.declaration.groupPath
      | .indexed source => leftPath.isPrefixOf source.targetDeclaration.groupPath
      | .keyed source => leftPath.isPrefixOf source.groupPath
      | .group _ | .starredGroup _ | .starredGroupPresence _ => false
  | none, some rightPath =>
      match left with
      | .field declaration _ => rightPath.isPrefixOf declaration.groupPath
      | .star source | .starHaving source _ =>
          rightPath.isPrefixOf source.declaration.groupPath
      | .indexed source => rightPath.isPrefixOf source.targetDeclaration.groupPath
      | .keyed source => rightPath.isPrefixOf source.groupPath
      | .group _ | .starredGroup _ | .starredGroupPresence _ => false
  | none, none => false

/-- The repeatable levels this operand leaves for its evaluation to bind: a direct field's own
    scope, which resolution admitted only where the reading scope binds it unless a fixed-target
    list's gate judges it; a star's levels above its first star; and a fixed group's certified
    scope. -/
def bindingScope : ResolvedFieldEntityOperand model → List RepeatableLevel
  | .field declaration _ => declaration.repeatableScope
  | .indexed source => source.indexDeclaration.repeatableScope.dropLast
  | .keyed source => source.selection.indexDeclaration.repeatableScope.dropLast
  | .star source | .starHaving source _ => source.bindingScope
  | .group reference => reference.boundRepeatableScope
  | .starredGroup source => source.path.bindingScope
  | .starredGroupPresence source => source.path.bindingScope

/-- Dynamic keys retain their own binding demand beside the selected extent's parent. -/
def bindingScopes (operand : ResolvedFieldEntityOperand model) : List (List RepeatableLevel) :=
  match operand with
  | .indexed source => source.bindingScopes
  | .keyed source => source.bindingScopes
  | _ => [operand.bindingScope]

end ResolvedFieldEntityOperand

/-- The path of the first declaration whose base type differs from `expected`'s. The Kernel compares
    each declaration with the one before it, which finds the same first declaration here because
    sharing a base type is an equivalence. -/
def firstBaseTypeMismatch? (expected : SurfaceScalarKind) :
    List FlatFieldDecl → Option (List String)
  | [] => none
  | declaration :: remaining =>
      if expected.sharesValueListBaseType declaration.policy.kind.surfaceKind then
        firstBaseTypeMismatch? expected remaining
      else
        some declaration.path

/-- Every declaration the slots expand to, in authored order. A group slot contributes its
    subtree, so the base-type gate reads a group by the fields it reaches. -/
def expandedDeclarations (operands : List (ResolvedFieldEntityOperand model)) :
    List FlatFieldDecl :=
  operands.flatMap ResolvedFieldEntityOperand.expansionDeclarations

/-- The path of the first field-list declaration whose base type differs from the first one's. -/
def fieldListBaseTypeMismatch? (operands : List (ResolvedFieldEntityOperand model)) :
    Option (List String) :=
  match expandedDeclarations operands with
  | [] => none
  | first :: remaining => firstBaseTypeMismatch? first.policy.kind.surfaceKind remaining

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

/-- Whether every declaration of the operand's expansion passes a starred field's partial extent
    gate at its own path, bound and reopened levels split at the operand's own depth. Under partial
    validation a group operand's extent is known exactly when this holds for the gate its operator
    asks of a starred field: the group path is not the target, so field identifiers alone can settle
    it and an identifier on a descendant group covers the fields below it
    ([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-kf464-partial-group-extent)). -/
def everyDeclarationCovers (source : CheckedEntityGroupSource model)
    (declarations : List FlatFieldDecl)
    (covers : List String → List RepeatableLevel → List RepeatableLevel → Bool) : Bool :=
  declarations.all fun declaration =>
    covers declaration.path
      (declaration.repeatableScope.take source.boundLevelCount)
      (declaration.repeatableScope.drop source.boundLevelCount)

end CheckedEntityGroupSource

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

/-- Where an entity list's carrier asks the category gate against the list's repeat. The counts ask
    it ahead of the repeat and the other carriers that ask it behind the repeat, both measured, and
    those other carriers behind the root gate as well, which rests on the peer's source reading; a
    carrier outside the gate asks none
    ([inbound](../../docs/SOURCES.md#inbound-2026-09-26b-entity-list-category)). -/
inductive EntityListCategoryGate where
  | absent
  | aheadOfRepeat
  | behindRootGate
  deriving Repr, DecidableEq

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
    groups identify by path. An indexed field retains the key, including literal spelling. Starred occurrences intentionally have no exact identity. -/
inductive ResolvedFieldEntityIdentity where
  | field (identity : FieldId × FieldEntityReadForm)
  | indexed (identity : FieldId × CheckedSemanticIndexKey)
  | keyedGroup (path : GroupPath) (key : CheckedSemanticIndexKey)
  | fixedGroup (path : GroupPath)
  deriving Repr, DecidableEq

def ResolvedFieldEntityOperand.exactIdentity? :
    ResolvedFieldEntityOperand model → Option ResolvedFieldEntityIdentity
  | .field declaration form => some (.field (declaration.id, form))
  | .indexed source => some (.indexed (source.targetDeclaration.id, source.key))
  | .keyed source => match source.target with
    | .group path => some (.keyedGroup path source.selection.key)
    | .star _ | .starredGroup _ => none
  | .group reference => some (.fixedGroup reference.path)
  | .star _ | .starHaving _ _ | .starredGroup _ |
      .starredGroupPresence _ => none

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

/-- Whether a carrier's operand list may consist of one unstarred field.

**This is measured to be per carrier, and the two sides have a reason.** All three value-list
quantifiers accept a sole unstarred field, where `FieldValuesNotUnique` and `NumberOfDifferentValues`
refuse one with `MVK_PARAMSIZE_INVALIDN`
([checkpoint](../../docs/SOURCES.md#src-value-list-quantifier-kind-gate-partitions-three-ways)). A
value-list quantifier compares its fields against *literals*, so one field is a complete question; an
entity-list carrier compares them against *each other*, where one field asks nothing.

`manyRequired` is the default because it is the gate the shared checker has always applied, so an
unmeasured carrier keeps refusing — the loud direction — rather than silently widening. -/
inductive EntityListArity where
  | manyRequired
  | soleAllowed
  deriving Repr, DecidableEq

namespace EntityListArity

def allowsSole : EntityListArity → Bool
  | .soleAllowed => true
  | .manyRequired => false

end EntityListArity

/-- A resolved, model-owned entity-list shape before homogeneous family certification. -/
structure CheckedFieldEntityShape (model : FlatModel) where
  first : ResolvedFieldEntityOperand model
  rest : List (ResolvedFieldEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  /-- Which arity rule the carrier that built this shape applies. Retained rather than discharged so
  a consumer can tell a sole-operand list that was *admitted* from one that never occurred. -/
  arity : EntityListArity
  requiredMultiplicity :
    (arity.allowsSole || first.isAlreadyMany || !rest.isEmpty) = true
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
    topology and are unaffected.

    On a fixed-target list neither an unstarred field nor a fixed group is judged here: both keep
    their levels for the list's own unbound-level gate, which picks the class by where the target
    lies and by the outermost level. Judging the field here reported the missing star where an
    index-keyed level draws its index class ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
def resolveFieldEntityOperandIn (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel) (authored : SurfaceFieldEntityOperand)
    (fixedTargetGroup? : Option GroupPath := none) (writtenGroup : GroupPath)
    (groupReadScope : FixedGroupReadScope := .scalar) :
    Except FieldEntityShapeElabError (ResolvedFieldEntityOperand model) :=
  -- A computation's fixed target is the field it writes; a validation's error field otherwise.
  let written := fixedTargetGroup?.getD writtenGroup
  let star (path : SurfaceStarFieldPath) :=
    (elaborateStarFieldPath model declaringGroup path).mapError fun error =>
      .starPath (error.placeBelowStar model declaringGroup written)
  -- A category read of a field declaring no Enumeration draws the read's own class, after the walk
  -- as a bracketed category read does. It is measured inside `Sum`, the two DateRange overlaps,
  -- `FieldValuesNotUnique` and the value list, and every other list sharing this shape asks it on
  -- that account ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
  -- A fixed-target list asks its walk list-wide later, an order no row measures. A category its
  -- Enumeration does not declare draws `MVK_CATEGORY_UNKOWN` at the same read, ahead of every list
  -- gate: it is the second gate of the category check the non-Enumeration class opens
  -- ([`kf359`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf359)), and beside a Number in a value
  -- list it pre-empts the varying-types gate (the 2026-09-18 extension under
  -- [`kf106`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf106)). On an entity list it is
  -- measured on the value-list quantifier's field list, ahead of the duplicate gate
  -- ([inbound](../../docs/SOURCES.md#inbound-2026-09-26h-list-reads)); on the other carriers its
  -- position rests on the peer's source reading that the check answers wherever the operand's spec
  -- stands ([`kf482`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf482)).
  let categoryRead := FlatFieldDecl.checkEntityCategoryRead
  match authored with
  | .keyed source => (elaborateKeyedEntityExtent model declaringGroup source
      (some (model.repeatableScopeForGroupPath (fixedTargetGroup?.getD writtenGroup)))).map .keyed |>.mapError .keyed
  | .indexed source =>
      (elaborateSemanticIndexSource model declaringGroup source
        (some (model.repeatableScopeForGroupPath (fixedTargetGroup?.getD writtenGroup)))).map .indexed |>.mapError .semanticIndex
  | .field path form => do
      let resolved ←
        model.resolveFieldDeclarationUnchecked declaringGroup path
          |>.mapError .resolve
      if fixedTargetGroup?.isSome then
        categoryRead resolved form
        return .field resolved form
      -- The walk answers first: with the error field outside the rule group it refuses a level
      -- `scope` binds.
      if let some unbound :=
          model.unboundReadLevel? declaringGroup writtenGroup resolved.repeatableScope scope then
        throw (.resolve (.unboundOperandLevel resolved.path unbound))
      let declaration ← resolved.requireRepetitionBoundBy scope |>.mapError .resolve
      categoryRead declaration form
      pure (.field declaration form)
  | .star path => do
      pure (.star (← star path))
  | .starHaving path having => do
      let source ← star path
      if fixedTargetGroup?.isNone then
        -- The error-field binding augments the declaring row without relocating filter names
        -- (the reading-scope checkpoint and `ValidationBindingLocks`).
        if let some (path, unbound) := having.unboundOuterReference? model declaringGroup writtenGroup
            (model.repeatableScopeForGroupPath declaringGroup ++ scope) then
          throw (.resolve (.unboundOperandLevel path unbound))
      pure (.starHaving source having)
  | .group reference => do
      let resolved ← (if fixedTargetGroup?.isSome then
          model.resolveFixedTargetListGroupReference declaringGroup reference
        else groupReadScope.resolve model declaringGroup reference (some writtenGroup))
        |>.mapError .groupReference
      pure (.group resolved)
  | .starredGroup reference => do
      let source ← elaborateStarredGroupOperandSource model declaringGroup reference
        |>.mapError fun error => .starredGroup (error.placeBelowStar model declaringGroup written)
      match source with
      | .terminalRepeatable source => pure (.starredGroup source)
      | .terminalPresence source => pure (.starredGroupPresence source)

/-- The scalar instance: an operand read where no repeatable level is bound, beside an error field
    in the rule's own group. -/
def resolveFieldEntityOperandUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntityOperand) :
    Except FieldEntityShapeElabError (ResolvedFieldEntityOperand model) :=
  resolveFieldEntityOperandIn model declaringGroup [] authored (writtenGroup := declaringGroup)

/-- Read every operand in authored order, each through `resolveFieldEntityOperandIn`, so the first
    that cannot be read answers. A carrier with a gate of its own ahead of the shared list gates
    reads the list with this first. -/
def resolveFieldEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel) (fixedTargetGroup? : Option GroupPath)
    (writtenGroup : GroupPath) (authored : List SurfaceFieldEntityOperand)
    (groupReadScope : FixedGroupReadScope := .scalar) :
      Except FieldEntityShapeElabError
        (List (ResolvedFieldEntityOperand model)) :=
  match authored with
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolveFieldEntityOperandIn model declaringGroup scope operand fixedTargetGroup?
          writtenGroup groupReadScope) ::
        (← resolveFieldEntityOperands model declaringGroup scope fixedTargetGroup? writtenGroup
          remaining groupReadScope))

/-- Validate the common entity-list shape: model, path resolution and its star gate, on a fixed-target arm the list-wide unbound-level gate, the category gate where the carrier asks it ahead of the repeat, exact duplicates in authored encounter order, ancestor/descendant overlap, the root-group gate, the category gate where the carrier asks it behind that, then the multiple-slots-or-one-already-many cardinality gate.

    Path resolution precedes the whole-list gates and the kind scan follows them. Every exact non-wildcard identity shares one scan, independent of field/group class; strict ancestor overlap follows it. Cardinality is structurally separate on this typed surface: its singleton direct-field input cannot also contain a repeated or overlapping pair, and a root slot is already-many, so the root gate and cardinality never both fire.

    The root gate is measured on `Sum`, the extrema, `FirstFilledValue`, `NumberOfDifferentValues`, `FieldValuesNotUnique`, `DateRangesOverlap`, and `NumberOfValueInFields` on the validation arm ([checkpoint](../../docs/SOURCES.md#inbound-2026-09-23-entity-list-root-group-gate)), and on the value-list quantifier and a String-target computation `FirstFilledValue` ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers)), all three quantifiers and both value-list spellings ([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-dispositions)). `AtLeastOneDateRangeOverlaps` and the Enumeration and DateRange first-filled computations inherit it across a target-kind boundary no row crosses, which refuses rather than admits where no row decides — the same loud direction `EntityListArity` takes. -/
def elaborateFieldEntityShapeIn (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel)
    (authored : SurfaceFieldEntitySource)
    (arity : EntityListArity := .manyRequired) (fixedTargetGroup? : Option GroupPath := none)
    (writtenGroup : GroupPath) (categoryGate : EntityListCategoryGate := .absent)
    (groupReadScope : FixedGroupReadScope := .scalar) :
    Except FieldEntityShapeElabError (CheckedFieldEntityShape model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let first ←
        resolveFieldEntityOperandIn model declaringGroup scope authored.first fixedTargetGroup?
          writtenGroup groupReadScope
      let rest ←
        resolveFieldEntityOperands model declaringGroup scope fixedTargetGroup? writtenGroup
          authored.rest groupReadScope
      if let some targetGroup := fixedTargetGroup? then
        if let some unbound := model.firstUnboundComputationLevel? declaringGroup targetGroup
            ((first :: rest).flatMap ResolvedFieldEntityOperand.bindingScopes) then
          throw (.unboundOperandLevel unbound)
      if categoryGate == .aheadOfRepeat then
        if let some path := (first :: rest).findSome? ResolvedFieldEntityOperand.categoryPath? then
          throw (.categoryNotAllowed path)
      match hDuplicate : firstDuplicateResolvedEntityOperand? (first :: rest) with
      | some (.field (field, _)) | some (.indexed (field, _)) => throw (.duplicateOperand field)
      | some (.fixedGroup path) | some (.keyedGroup path _) => throw (.duplicateGroupOperand path)
      | none =>
          match hOverlap : firstResolvedOperandOverlap? (first :: rest) with
          | some (ancestor, descendant) =>
              throw (.overlappingOperands ancestor descendant)
          | none =>
              match (first :: rest).findSome? ResolvedFieldEntityOperand.rootGroupPath? with
              | some root => throw (.rootGroupOperand root)
              | none => do
                  if categoryGate == .behindRootGate then
                    if let some path :=
                        (first :: rest).findSome? ResolvedFieldEntityOperand.categoryPath? then
                      throw (.categoryNotAllowed path)
                  if hMultiplicity :
                      arity.allowsSole || first.isAlreadyMany || !rest.isEmpty then
                    pure {
                      first
                      rest
                      modelWellFormed := by rw [hModel]; rfl
                      arity
                      requiredMultiplicity := hMultiplicity
                      uniqueExactOperands := hDuplicate
                      disjointOperands := hOverlap }
                  else
                    throw .tooFewFields

/-- The scalar instance of the shared shape gates. -/
def elaborateFieldEntityShape (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource)
    (arity : EntityListArity := .manyRequired) (fixedTargetGroup? : Option GroupPath := none)
    (writtenGroup : GroupPath) (categoryGate : EntityListCategoryGate := .absent) :
    Except FieldEntityShapeElabError (CheckedFieldEntityShape model) :=
  elaborateFieldEntityShapeIn model declaringGroup [] authored arity fixedTargetGroup? writtenGroup
    categoryGate

/-- Every operand kind resolves only against a representable declaring group, so a checked
    entity-list shape certifies its declaring group without re-testing it.

    Each arm's guard belongs to that arm's own owner and is stated there; this composes the five
    rather than restating any. A family building a certificate over this shape can therefore carry
    `declaringGroup` with its validity attached instead of leaving it uncertified. -/
theorem resolveFieldEntityOperandIn_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath} {scope : List RepeatableLevel}
    {authored : SurfaceFieldEntityOperand} {fixedTargetGroup? : Option GroupPath}
    {writtenGroup : GroupPath} {groupReadScope : FixedGroupReadScope}
    {resolved : ResolvedFieldEntityOperand model}
    (ok : resolveFieldEntityOperandIn model declaringGroup scope authored fixedTargetGroup?
      writtenGroup groupReadScope = .ok resolved) :
    GroupPath.isValid declaringGroup = true := by
  unfold resolveFieldEntityOperandIn at ok
  cases authored with
  | keyed source =>
      by_cases valid : GroupPath.isValid declaringGroup = true
      · exact valid
      · simp [elaborateKeyedEntityExtent, valid, Except.map, Except.mapError, bind, Except.bind] at ok
  | indexed source =>
      cases hSource : elaborateSemanticIndexSource model declaringGroup source
        (some (model.repeatableScopeForGroupPath (fixedTargetGroup?.getD writtenGroup))) with
      | error error => simp [hSource, Except.map, Except.mapError] at ok
      | ok checked => exact elaborateSemanticIndexSource_declaringGroupValid hSource
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
      cases fixedTargetGroup? with
      | some targetGroup =>
          cases hGroup : model.resolveFixedTargetListGroupReference declaringGroup reference with
          | error _ =>
              simp only [hGroup, Option.isSome_some, if_true, bind, Except.bind,
                Except.mapError] at ok
              cases ok
          | ok resolvedGroup =>
              exact FlatModel.resolveFixedTargetListGroupReference_declaringGroupValid hGroup
      | none =>
          cases hGroup :
              groupReadScope.resolve model declaringGroup reference (some writtenGroup) with
          | error _ =>
              simp only [hGroup, Option.isSome_none, Bool.false_eq_true, if_false, bind,
                Except.bind, Except.mapError] at ok
              cases ok
          | ok resolvedGroup =>
              exact FixedGroupReadScope.resolve_declaringGroupValid hGroup
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
    {authored : SurfaceFieldEntitySource} {arity : EntityListArity}
    {fixedTargetGroup? : Option GroupPath} {writtenGroup : GroupPath}
    {groupReadScope : FixedGroupReadScope}
    {checked : CheckedFieldEntityShape model}
    (ok : elaborateFieldEntityShapeIn model declaringGroup scope authored arity fixedTargetGroup?
      writtenGroup .absent groupReadScope = .ok checked) :
    GroupPath.isValid declaringGroup = true := by
  unfold elaborateFieldEntityShapeIn at ok
  split at ok
  · cases ok
  · cases hFirst :
      resolveFieldEntityOperandIn model declaringGroup scope authored.first fixedTargetGroup?
        writtenGroup groupReadScope with
    | error _ =>
        simp only [hFirst, bind, Except.bind] at ok
        cases ok
    | ok first => exact resolveFieldEntityOperandIn_declaringGroupValid hFirst

/-- The scalar specialization inherits it unchanged. -/
theorem elaborateFieldEntityShape_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath}
    {authored : SurfaceFieldEntitySource} {arity : EntityListArity}
    {fixedTargetGroup? : Option GroupPath} {writtenGroup : GroupPath}
    {checked : CheckedFieldEntityShape model}
    (ok : elaborateFieldEntityShape model declaringGroup authored arity fixedTargetGroup?
      writtenGroup = .ok checked) :
    GroupPath.isValid declaringGroup = true :=
  elaborateFieldEntityShapeIn_declaringGroupValid ok

end A12Kernel
