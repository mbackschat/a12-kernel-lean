import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.MessageGroupGuard
import A12Kernel.Elaboration.ParallelFieldRule

namespace A12Kernel

inductive MessageAuthoringCore (model : FlatModel) where
  | flat (condition : FlatCondition)
  | validation (condition : ValidationCondition model)
  | parallel (rule : CheckedParallelFieldRule model)

/-- A parallel leaf reads its operands, and a group leaf every field below its group. -/
def MessageAuthoringCore.referencesField : MessageAuthoringCore model → FieldId → Bool
  | .flat condition => condition.referencesField
  | .validation condition => condition.referencesField
  | .parallel rule => fun field => rule.condition.anyLeaf fun
      | .groupPresence _ reference => reference.referencesField model field
      | leaf => leaf.fields.any fun operand => (rule.pair.declaration operand).id == field

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
    | .flat _ | .parallel _ _ => true
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

/-- Ancestor index references inherit each authored entity's mode; querying non-iteration directly
retains a keyed/starred read even beside a plain read (ReferencedIdsUtil.createAllIndexFieldEntityIds). -/
def indexReferenced? (condition : ValidationMessageCondition model) (group : GroupPath) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageGroupReference? declaration.id group)
  | .parallel _ _ => some (condition.readsUnder group)

def indexNonIterating? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageNonIteratingReference? declaration.id group level)
  | .parallel _ _ => some false

def selectedGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (key : Option CheckedSemanticIndexKey) : Option Bool :=
  match condition with
  | .flat _ | .parallel _ _ => some false
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageSelectedGroupReference? declaration.id group key)

def unkeyedGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageUnkeyedReference? declaration.id group level)
  | .parallel _ _ => some (condition.readsUnder group)

def nonWildcardGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat _ => some (condition.readsUnder group)
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageNonWildcardReference? declaration.id group level)
  | .parallel _ _ => some (condition.readsUnder group)

def anySelectedGroupReferenced? (condition : ValidationMessageCondition model) : Option Bool :=
  anyKnown (model.repeatableGroups.map fun group => condition.selectedGroupReferenced? group.path none)

def keyedGroupGuarded (condition : ValidationMessageCondition model)
    (group : GroupPath) (key : CheckedSemanticIndexKey) : Bool :=
  match condition with
  | .flat _ | .parallel _ _ => false
  | .rule checkedRule => checkedRule.condition.core.keyedMessageGroupGuarded group key

end ValidationMessageCondition
end A12Kernel
