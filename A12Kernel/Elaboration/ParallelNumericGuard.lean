import A12Kernel.Elaboration.ParallelInstanceView
import A12Kernel.Elaboration.ComputationNumericGuard
import A12Kernel.Elaboration.CheckedGroupPresence

/-! # Guards of a key-joined Number computation

A joined computation evaluates its guard once per target row, with the partner row its key matches
bound beside it. The guard is therefore checked against the instance view of the joined groups,
where the ordinary guard elaborators accept partner fields as fixed reads, and it evaluates over
the joined cells by field identity (spec/09 §5; parallel-guard capture, 2026-10-14).

A group that strictly contains a joined group is not part of the join, so its presence keeps the
model's own content: its fixed fields and every instantiated descendant row. That account is the
ordinary one at the common outer binding; the retained capture shows only rows where both accounts
hold, so it remains an assumption beside its evidence item in the gap register.
-/

namespace A12Kernel

/-- The only part of a guard computation scheduling consumes: each leaf's positive or negative
group reference, with the connective structure that decides protection. Every leaf becomes a
predicate leaf carrying that reference, so the scheduling queries read it back with `id`. -/
abbrev ComputationProtectionLeaf := Option (GroupPresenceOperator × ResolvedGroupReference)

abbrev ComputationProtectionView := ComputationConditionOf Empty ComputationProtectionLeaf

def CheckedComputationCondition.protectionView (condition : CheckedComputationCondition model) :
    ComputationProtectionView :=
  condition.map fun
    | .predicate source => .predicate source.groupReference?
    | leaf => .predicate leaf.groupReference?

/-- A guard checked against the instance view of the groups one joined row binds. -/
structure ParallelNumericGuard (model : FlatModel) where
  joined : List GroupPath
  condition : CheckedComputationCondition (model.parallelInstanceView joined)

namespace ParallelNumericGuard

/-- A model-checked guard that joins no group, such as one over target-row or common-frame fields. -/
def ofUnjoined (condition : CheckedComputationCondition model) : ParallelNumericGuard model :=
  { joined := [], condition }

def referencesField (guard : ParallelNumericGuard model) (field : FieldId) : Bool :=
  guard.condition.referencesField field

def forbidsTarget (guard : ParallelNumericGuard model) (field : FieldId) : Bool :=
  guard.condition.forbidsTarget field

def requiresProducer (guard : ParallelNumericGuard model) (consumer producer : FieldId)
    (producerProtected : ResolvedGroupReference → Bool) : Bool :=
  guard.condition.requiresProducer consumer producer producerProtected

/-- Whether `group` strictly contains a joined group, so that the join does not narrow it. -/
def _root_.A12Kernel.GroupPath.enclosesAny (group : GroupPath) (joined : List GroupPath) : Bool :=
  joined.any fun path => group.isPrefixOf path && group != path

def encloses (guard : ParallelNumericGuard model) (group : GroupPath) : Bool :=
  group.enclosesAny guard.joined

def protectionView (guard : ParallelNumericGuard model) : ComputationProtectionView :=
  guard.condition.protectionView

/-- Whether evaluation reads the field's cell. Group presence reads its content fields; its
complete member inventory stays a dependency of `referencesField` only. -/
def readsField (guard : ParallelNumericGuard model) (field : FieldId) : Bool :=
  guard.condition.anyLeaf fun
    | .groupPresence _ source => source.content.fields.contains field
    | leaf => CheckedComputationCondition.referencesField (.leaf leaf) field

/-- Every leaf reads direct cells only, each one admitted by `admits`. Starred, indexed, keyed and
filtered sources need an extent the joined row does not supply; group presence below a joined
group needs no row topology because the view has none there. The predicate set is the one the
capture measured: field-fill lists, temporal comparisons and scalar value lists. -/
def admitted (guard : ParallelNumericGuard model) (admits : FieldId → Bool) : Bool :=
  let reads := fun (leaf : ComputationConditionLeaf _ _) =>
    model.fields.all fun declaration =>
      !CheckedComputationCondition.referencesField (model := model.parallelInstanceView guard.joined)
        (.leaf leaf) declaration.id || admits declaration.id
  guard.condition.allLeaves fun leaf => match leaf with
    | .fieldFilled field | .fieldNotFilled field => admits field
    | .text comparison | .scalar comparison => comparison.fieldIds.all admits
    | .fieldFill _ sources => sources.all fun
        | .direct field => admits field
        | .expanded .. => false
    | .groupPresence _ source => source.starPath.isNone &&
        (source.content.rowLevels.isEmpty || guard.encloses source.reference.path) &&
        source.content.fields.all admits
    | .numeric comparison => reads leaf && (comparison.left.atoms ++ comparison.right.atoms).all fun
        | .numeric (.field _) | .numeric (.temporalFieldPart ..) | .numeric (.stringLength _)
        | .numeric (.aggregate ..) => true
        | _ => false
    | .predicate (.fieldFill _ source) => reads leaf && source.source.operands.all fun
        | .field _ => true
        | _ => false
    | .predicate (.temporal _) | .predicate (.scalarValueList ..) => reads leaf
    | .predicate _ => false

/-- Evaluate over one joined row. `read` supplies every admitted cell by identity; `document`
supplies only the row topology an enclosing group's presence consults. -/
def eval (guard : ParallelNumericGuard model) (context : ScalarComputationContext)
    (document : Document) (row : Env) :
    Except CheckedComputationConditionError ComputationConditionResult :=
  guard.condition.evalCheckedIn {
    scalar := { context with row }, document, outer := row
    filterRead := fun _ => context.read, starRead := fun _ => context.read }

end ParallelNumericGuard

/-- The groups one joined row of `target` binds: the target's innermost indexed group and every
other indexed repeatable group outside the target's enclosing frames. Which of them a guard may
read is decided afterwards by the checked routes, so the view only lifts their repetition. -/
def FlatModel.parallelJoinedGroups (model : FlatModel) (target : FlatFieldDecl) : List GroupPath :=
  let own := ((model.indexedAncestorGroups target).getLast?.map (·.path)).toList
  own ++ (model.repeatableGroups.filter fun group => group.indexField.isSome &&
    !group.path.isPrefixOf target.groupPath && !own.contains group.path).map (·.path)

/-- Check a guard against the instance view of `joined`. A group strictly containing a joined
group regains the model's content and members, which the view would have narrowed to one row. -/
def FlatModel.elaborateParallelNumericGuard (model : FlatModel) (joined : List GroupPath)
    (declaringGroup targetGroup : GroupPath)
    (surface : SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate) :
    Except CheckedComputationConditionElabError (CheckedComputationCondition (model.parallelInstanceView joined)) := do
  let view := model.parallelInstanceView joined
  let condition ← view.elaborateCheckedComputationCondition declaringGroup targetGroup surface
  pure (condition.map fun
    | .groupPresence operator source =>
        if source.reference.path.enclosesAny joined then
          .groupPresence operator { source with
            content := model.computationGroupSource source.reference.path
            members := (model.groupSubtreeFields source.reference.path).map (·.id) }
        else .groupPresence operator source
    | leaf => leaf)

end A12Kernel
