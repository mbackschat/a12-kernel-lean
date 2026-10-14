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

/-- Whether `group` strictly contains a joined group, so that the join does not narrow it. -/
def GroupPath.enclosesAny (group : GroupPath) (joined : List GroupPath) : Bool :=
  joined.any fun path => group.isPrefixOf path && group != path

/-- One authored guard leaf of a joined computation, kept with the model that certified it. -/
inductive ParallelNumericGuardPart (model : FlatModel) (joined : List GroupPath) where
  /-- Certified against the instance view, so a plain read of a joined group takes the partner row;
  it evaluates over the joined row's cells. -/
  | view (condition : CheckedComputationCondition (model.parallelInstanceView joined))
  /-- Certified against the model at the target row. A starred, keyed or filtered leaf, which the
  view cannot certify, keeps its ordinary meaning there and reads the whole document
  ([joined-carrier checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-joined-carrier-admission)). -/
  | ordinary (condition : CheckedComputationCondition model)
  /-- Certified against the model at a row of the joined partner `group`, as a leaf keyed by a
  partner field is; it evaluates at the partner row the target's key matches, or at a key-only row
  when none does (joined-carrier-limits capture, `Cp03`, 2026-10-14). -/
  | partner (group : GroupPath) (condition : CheckedComputationCondition model)

/-- The reads a joined guard evaluates over: the joined row's cells by field identity, the document
at the target row, which carries the world a clock-reading leaf needs in every part, and the
document at each joined partner group's row. -/
structure ParallelNumericGuardContext where
  joinedRead : FieldId → CheckedCell
  ordinary : NumericComputationEvaluationContext
  partnerAt : GroupPath → Option NumericComputationEvaluationContext := fun _ => none

/-- The joined row's cells under the document's world: the context a joined operation and a view
part read through. -/
def ParallelNumericGuardContext.joinedScalar (context : ParallelNumericGuardContext) :
    ScalarComputationContext :=
  { read := context.joinedRead, world := context.ordinary.scalar.world }

/-- The ordinary computation context at one target row of `document`, with its own world. -/
def CheckedDocument.parallelGuardContextAt (document : CheckedDocument model) (environment : Env) :
    NumericComputationEvaluationContext :=
  let reads := document.computationFillContext
  { scalar := document.computationContextAt environment, document := reads.document,
    outer := environment
    filterRead := reads.read, filterStoredText := reads.storedText, filterNumberText := reads.numberText
    starRead := reads.read, starStoredText := reads.storedText
    indexColumn? := some (document.resolveSemanticIndexColumnWith document.read) }

namespace ParallelNumericGuardPart

def referencesField : ParallelNumericGuardPart model joined → FieldId → Bool
  | .view condition, field => condition.referencesField field
  | .ordinary condition, field | .partner _ condition, field => condition.referencesField field

def forbidsTarget : ParallelNumericGuardPart model joined → FieldId → Bool
  | .view condition, field => condition.forbidsTarget field
  | .ordinary condition, field | .partner _ condition, field => condition.forbidsTarget field

def requiresProducer (part : ParallelNumericGuardPart model joined) (consumer producer : FieldId)
    (producerProtected : ResolvedGroupReference → Bool) : Bool :=
  match part with
  | .view condition => condition.requiresProducer consumer producer producerProtected
  | .ordinary condition | .partner _ condition =>
      condition.requiresProducer consumer producer producerProtected

def protectionView : ParallelNumericGuardPart model joined → ComputationProtectionView
  | .view condition => condition.protectionView
  | .ordinary condition | .partner _ condition => condition.protectionView

/-- Whether evaluation reads the field among the joined row's cells. Group presence reads its
content fields; its complete member inventory stays a dependency of `referencesField` only. An
ordinary part reads the document instead, so it adds no cell and no route to the join. -/
def readsJoinedField : ParallelNumericGuardPart model joined → FieldId → Bool
  | .view condition, field => condition.anyLeaf fun
      | .groupPresence _ source => source.content.fields.contains field
      | leaf => CheckedComputationCondition.referencesField (.leaf leaf) field
  | .ordinary _, _ | .partner .., _ => false

/-- A view part reads direct cells only, each one admitted by `admits`. Starred, indexed, keyed
and filtered sources need an extent the joined row does not supply; group presence below a joined
group needs no row topology because the view has none there. Its predicate set is the one the
parallel-guard capture measured: field-fill lists, temporal comparisons and scalar value lists. An
ordinary part was certified at the target row and needs nothing from the join; a partner part
needs its group joined, which a route admitting one of the group's own fields shows. -/
def admitted (part : ParallelNumericGuardPart model joined) (admits : FieldId → Bool) : Bool :=
  match part with
  | .ordinary _ => true
  | .partner group _ => model.fields.any fun declaration =>
      declaration.groupPath == group && admits declaration.id
  | .view condition =>
      let reads := fun (leaf : ComputationConditionLeaf _ _) =>
        model.fields.all fun declaration =>
          !CheckedComputationCondition.referencesField (model := model.parallelInstanceView joined)
            (.leaf leaf) declaration.id || admits declaration.id
      condition.allLeaves fun leaf => match leaf with
        | .fieldFilled field | .fieldNotFilled field => admits field
        | .text comparison | .scalar comparison => comparison.fieldIds.all admits
        | .fieldFill _ sources => sources.all fun
            | .direct field => admits field
            | .expanded .. => false
        | .groupPresence _ source => source.starPath.isNone &&
            (source.content.rowLevels.isEmpty || source.reference.path.enclosesAny joined) &&
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

/-- A view part sees only the joined row's cells, and the document only for the row topology an
enclosing group's presence consults. An ordinary part sees the document at the target row, a partner
part at its group's row; a partner group the execution bound no row for is a structural failure. -/
def eval (part : ParallelNumericGuardPart model joined) (context : ParallelNumericGuardContext) :
    Except CheckedComputationConditionError ComputationConditionResult :=
  match part with
  | .view condition =>
      let row := context.ordinary.outer
      condition.evalCheckedIn {
        scalar := { context.joinedScalar with row }
        document := context.ordinary.document, outer := row
        filterRead := fun _ => context.joinedRead, starRead := fun _ => context.joinedRead }
  | .ordinary condition => condition.evalCheckedIn context.ordinary
  | .partner group condition => match context.partnerAt group with
      | some partnerContext => condition.evalCheckedIn partnerContext
      | none => throw (.primitive .groupContextRequired)

end ParallelNumericGuardPart

private def graftProtection : ConditionTree (ParallelNumericGuardPart model joined) → ComputationProtectionView
  | .leaf part => part.protectionView
  | .and left right => .and (graftProtection left) (graftProtection right)
  | .or left right => .or (graftProtection left) (graftProtection right)

/-- A joined computation's guard: the authored connective tree over parts. -/
structure ParallelNumericGuard (model : FlatModel) where
  joined : List GroupPath
  condition : ConditionTree (ParallelNumericGuardPart model joined)

namespace ParallelNumericGuard

/-- A model-checked guard that joins no group, such as one over target-row or common-frame fields.
With nothing joined the view is the model itself, so the guard reads the joined cells as before. -/
def ofUnjoined (condition : CheckedComputationCondition model) : ParallelNumericGuard model :=
  { joined := [], condition := .leaf (.view condition) }

def referencesField (guard : ParallelNumericGuard model) (field : FieldId) : Bool :=
  guard.condition.anyLeaf (·.referencesField field)

def forbidsTarget (guard : ParallelNumericGuard model) (field : FieldId) : Bool :=
  guard.condition.anyLeaf (·.forbidsTarget field)

def requiresProducer (guard : ParallelNumericGuard model) (consumer producer : FieldId)
    (producerProtected : ResolvedGroupReference → Bool) : Bool :=
  guard.condition.anyLeaf (·.requiresProducer consumer producer producerProtected)

def protectionView (guard : ParallelNumericGuard model) : ComputationProtectionView :=
  graftProtection guard.condition

def readsField (guard : ParallelNumericGuard model) (field : FieldId) : Bool :=
  guard.condition.anyLeaf (·.readsJoinedField field)

def admitted (guard : ParallelNumericGuard model) (admits : FieldId → Bool) : Bool :=
  guard.condition.allLeaves (·.admitted admits)

def eval (guard : ParallelNumericGuard model) (context : ParallelNumericGuardContext) :
    Except CheckedComputationConditionError ComputationConditionResult :=
  guard.condition.evalComputationExcept (·.eval context)

end ParallelNumericGuard

/-- The groups one joined row of `target` binds: the target's innermost indexed group and every
other indexed repeatable group outside the target's enclosing frames. Which of them a guard may
read is decided afterwards by the checked routes, so the view only lifts their repetition. -/
def FlatModel.parallelJoinedGroups (model : FlatModel) (target : FlatFieldDecl) : List GroupPath :=
  let own := ((model.indexedAncestorGroups target).getLast?.map (·.path)).toList
  own ++ (model.repeatableGroups.filter fun group => group.indexField.isSome &&
    !group.path.isPrefixOf target.groupPath && !own.contains group.path).map (·.path)

/-- Check one guard leaf against the instance view of `joined`. A group strictly containing a
joined group regains the model's content and members, which the view would have narrowed to one row. -/
def FlatModel.elaborateParallelNumericGuardLeaf (model : FlatModel) (joined : List GroupPath)
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

/-- Choose one guard leaf's part from its checks. The view's reading wins when the joined row can
evaluate it. A leaf the view refuses, or certifies only as a kind the joined row cannot evaluate
such as a pattern, takes its ordinary reading at the target row when it has one, and otherwise
its reading at the first partner group's row that certifies it; failing all, the view's account
stands, so its refusal or its later route refusal is reported. -/
def ParallelNumericGuardPart.choose
    (view : Except ε (CheckedComputationCondition (model.parallelInstanceView joined)))
    (ordinary : Except ε (CheckedComputationCondition model))
    (partners : List (GroupPath × Except ε (CheckedComputationCondition model))) :
    Except ε (ParallelNumericGuardPart model joined) :=
  let fallback : Option (ParallelNumericGuardPart model joined) := match ordinary with
    | .ok checked => some (.ordinary checked)
    | .error _ => partners.findSome? fun
        | (group, .ok checked) => some (.partner group checked)
        | (_, .error _) => none
  match view with
  | .ok condition =>
      if (ParallelNumericGuardPart.view condition).admitted (fun _ => true) then .ok (.view condition)
      else .ok (fallback.getD (.view condition))
  | .error refusal => match fallback with
      | some part => .ok part
      | none => .error refusal

end A12Kernel
