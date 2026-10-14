import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.MessageGroupGuard
import A12Kernel.Elaboration.ParallelFieldRule

namespace A12Kernel

inductive MessageAuthoringCore (model : FlatModel) where
  | flat (condition : FlatCondition)
  | validation (condition : ValidationCondition model)
  | parallel (rule : CheckedParallelFieldRule model)

/-- Whether a parallel rule reads `field` other than through a keyed group read beside the join: a
pair leaf reads its operands, and a group leaf every field below its group. -/
def CheckedParallelFieldRule.pairReferencesField (rule : CheckedParallelFieldRule model)
    (field : FieldId) : Bool :=
  rule.condition.anyLeaf fun
    | .groupPresence _ reference => reference.referencesField model field
    | .keyed _ => false
    | leaf => leaf.fields.any fun operand => (rule.pair.declaration operand).id == field

/-- The keyed group reads beside the join, each as the ordinary one-leaf condition whose reference
queries already answer for it. -/
def CheckedParallelFieldRule.keyedConditions (rule : CheckedParallelFieldRule model) :
    List (ValidationCondition model) :=
  go rule.condition
where
  go : ParallelFieldCondition model → List (ValidationCondition model)
    | .leaf (.keyed keyed) => [.leaf keyed.leaf]
    | .leaf _ => []
    | .and left right | .or left right => go left ++ go right

def MessageAuthoringCore.referencesField : MessageAuthoringCore model → FieldId → Bool
  | .flat condition => condition.referencesField
  | .validation condition => condition.referencesField
  | .parallel rule => fun field =>
      rule.pairReferencesField field || rule.keyedConditions.any (·.referencesField field)

/-- Rule-owned parameters need the actual error declaration as well as the checked condition.
The flat entry point remains available for templates whose parameters do not inspect that path. -/
inductive ValidationMessageCondition (model : FlatModel) where
  | flat (condition : CheckedFlatCondition model)
  | rule (rule : CheckedResolvedValidationRule model)
  /-- A parallel rule beside the group it is declared in. The join binds every read to its row, so
  none is starred, selected or non-iterating, and the condition iterates in parallel
  ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates)). -/
  | parallel (rule : CheckedParallelFieldRule model) (declaringGroup : GroupPath)

instance : Coe (CheckedFlatCondition model) (ValidationMessageCondition model) := ⟨.flat⟩

namespace ValidationMessageCondition

def rowGroup : ValidationMessageCondition model → GroupPath
  | .flat condition => condition.rowGroup
  | .rule checkedRule => checkedRule.condition.declaringGroup
  | .parallel _ declaringGroup => declaringGroup

def core : ValidationMessageCondition model → MessageAuthoringCore model
  | .flat condition => .flat condition.core
  | .rule checkedRule => .validation checkedRule.condition.core
  | .parallel parallelRule _ => .parallel parallelRule

def errorDeclaration? : ValidationMessageCondition model → Option FlatFieldDecl
  | .flat _ => none
  | .rule checkedRule => some checkedRule.errorDeclaration
  | .parallel parallelRule _ =>
      let pair := parallelRule.pair
      some (if pair.errorField == pair.leftDeclaration.id then pair.leftDeclaration
        else pair.rightDeclaration)

/-- Whether the condition iterates two indexed groups in parallel. -/
def parallelIteration : ValidationMessageCondition model → Bool
  | .parallel _ _ => true
  | .flat _ | .rule _ => false

/-- Whether an unkeyed message parameter may name `field`: the condition reads it, and not only
through a semantic-index selection of it. A carrier whose reference metadata is unresolved keeps the
read alone, so this gate only ever narrows the condition's footprint. -/
def messageMember (condition : ValidationMessageCondition model) (field : FieldId) : Bool :=
  condition.core.referencesField field && match condition with
    | .flat _ => true
    | .parallel parallelRule _ => parallelRule.pairReferencesField field
    | .rule checkedRule => checkedRule.condition.core.messageUnselectedReference? field != some false

/-- Whether some read of `field` carries no wildcard. A flat condition writes none. -/
def messageUnstarred? (condition : ValidationMessageCondition model) (field : FieldId) : Option Bool :=
  match condition with
  | .flat _ | .parallel _ _ => some true
  | .rule checkedRule => checkedRule.condition.core.messageUnstarredReference? field

private def anyKnown (answers : List (Option Bool)) : Option Bool :=
  if answers.contains (some true) then some true
  else if answers.contains none then none else some false

private def declarationsUnder (model : FlatModel) (group : GroupPath) : List FlatFieldDecl :=
  model.fields.filter (fun declaration => group.isPrefixOf declaration.groupPath)

/-- Whether the condition reads a field below `group`, for carriers whose reads carry one mode. -/
private def readsUnder (condition : ValidationMessageCondition model) (group : GroupPath) : Bool :=
  (declarationsUnder model group).any (condition.core.referencesField ·.id)

/-- A parallel rule's answer: its pair reads carry one mode, and each keyed group read beside the
join answers as the ordinary carrier does. -/
private def parallelAnswer (rule : CheckedParallelFieldRule model) (group : GroupPath)
    (keyed : ValidationCondition model → FieldId → Option Bool) : Option Bool :=
  anyKnown (some ((declarationsUnder model group).any (rule.pairReferencesField ·.id)) ::
    rule.keyedConditions.flatMap fun condition =>
      (declarationsUnder model group).map (keyed condition ·.id))

/-- Ancestor index references inherit each authored entity's mode; querying non-iteration directly
retains a keyed/starred read even beside a plain read (ReferencedIdsUtil.createAllIndexFieldEntityIds). -/
def indexReferenced? (condition : ValidationMessageCondition model) (group : GroupPath) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageGroupReference? declaration.id group)
  | .parallel parallelRule _ => parallelAnswer parallelRule group fun keyed field =>
      keyed.messageGroupReference? field group

def indexNonIterating? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageNonIteratingReference? declaration.id group level)
  | .parallel parallelRule _ => anyKnown (parallelRule.keyedConditions.flatMap fun keyed =>
      (declarationsUnder model group).map fun declaration =>
        keyed.messageNonIteratingReference? declaration.id group level)

def selectedGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (key : Option CheckedSemanticIndexKey) : Option Bool :=
  match condition with
  | .flat _ => some false
  | .parallel parallelRule _ => anyKnown (parallelRule.keyedConditions.flatMap fun keyed =>
      (declarationsUnder model group).map fun declaration =>
        keyed.messageSelectedGroupReference? declaration.id group key)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageSelectedGroupReference? declaration.id group key)

def unkeyedGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageUnkeyedReference? declaration.id group level)
  | .parallel parallelRule _ => parallelAnswer parallelRule group fun keyed field =>
      keyed.messageUnkeyedReference? field group level

def nonWildcardGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageNonWildcardReference? declaration.id group level)
  | .parallel parallelRule _ => parallelAnswer parallelRule group fun keyed field =>
      keyed.messageNonWildcardReference? field group level

def anySelectedGroupReferenced? (condition : ValidationMessageCondition model) : Option Bool :=
  anyKnown (model.repeatableGroups.map fun group => condition.selectedGroupReferenced? group.path none)

def keyedGroupGuarded (condition : ValidationMessageCondition model)
    (group : GroupPath) (key : CheckedSemanticIndexKey) : Bool :=
  match condition with
  | .flat _ => false
  | .parallel parallelRule _ => parallelRule.condition.iterationGuarded fun
      | .keyed keyed => ValidationCondition.keyedMessageLeafGuard group key keyed.leaf
      | _ => false
  | .rule checkedRule => checkedRule.condition.core.keyedMessageGroupGuarded group key

/-- Whether a keyed message parameter may name `declaration` under `key`. The key belongs to the
field's nearest indexed group, and the condition must select that group by the same key: either
selecting this field, through a keyed field or a keyed group read containing it, or, for the group's
declared index field, selecting any field of the group. Another field of the group is refused although
the condition keys the group ([checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15)). -/
def messageKeyedMember? (condition : ValidationMessageCondition model) (declaration : FlatFieldDecl)
    (key : CheckedSemanticIndexKey) : Option Bool :=
  match model.semanticIndexGroupForPath? declaration.groupPath, condition with
  | none, _ | _, .flat _ => some false
  | some group, .parallel parallelRule _ =>
      if group.indexField == some declaration.id then
        condition.selectedGroupReferenced? group.path (some key)
      else anyKnown (parallelRule.keyedConditions.map
        (·.messageSelectedGroupReference? declaration.id group.path (some key)))
  | some group, .rule checkedRule =>
      if group.indexField == some declaration.id then
        condition.selectedGroupReferenced? group.path (some key)
      else
        checkedRule.condition.core.messageSelectedGroupReference? declaration.id group.path (some key)

/-- The membership a message field reference needs: the unkeyed gate, or the keyed one under its key. -/
def messageAdmits (condition : ValidationMessageCondition model) (declaration : FlatFieldDecl) :
    Option CheckedSemanticIndexKey → Option Bool
  | none => some (condition.messageMember declaration.id)
  | some key => condition.messageKeyedMember? declaration key

end ValidationMessageCondition
end A12Kernel
