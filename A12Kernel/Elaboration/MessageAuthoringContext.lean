import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.MessageGroupGuard

namespace A12Kernel

inductive MessageAuthoringCore (model : FlatModel) where
  | flat (condition : FlatCondition)
  | validation (condition : ValidationCondition model)

def MessageAuthoringCore.referencesField : MessageAuthoringCore model → FieldId → Bool
  | .flat condition => condition.referencesField
  | .validation condition => condition.referencesField

/-- Rule-owned parameters need the actual error declaration as well as the checked condition.
The flat entry point remains available for templates whose parameters do not inspect that path. -/
inductive ValidationMessageCondition (model : FlatModel) where
  | flat (condition : CheckedFlatCondition model)
  | rule (rule : CheckedResolvedValidationRule model)

instance : Coe (CheckedFlatCondition model) (ValidationMessageCondition model) := ⟨.flat⟩

namespace ValidationMessageCondition

def rowGroup : ValidationMessageCondition model → GroupPath
  | .flat condition => condition.rowGroup
  | .rule checkedRule => checkedRule.condition.declaringGroup

def core : ValidationMessageCondition model → MessageAuthoringCore model
  | .flat condition => .flat condition.core
  | .rule checkedRule => .validation checkedRule.condition.core

def errorDeclaration? : ValidationMessageCondition model → Option FlatFieldDecl
  | .flat _ => none
  | .rule checkedRule => some checkedRule.errorDeclaration

private def anyKnown (answers : List (Option Bool)) : Option Bool :=
  if answers.contains (some true) then some true
  else if answers.contains none then none else some false

private def declarationsUnder (model : FlatModel) (group : GroupPath) : List FlatFieldDecl :=
  model.fields.filter (fun declaration => group.isPrefixOf declaration.groupPath)

/-- Ancestor index references inherit each authored entity's mode; querying non-iteration directly
retains a keyed/starred read even beside a plain read (ReferencedIdsUtil.createAllIndexFieldEntityIds). -/
def indexReferenced? (condition : ValidationMessageCondition model) (group : GroupPath) : Option Bool :=
  match condition with
  | .flat checked => some ((declarationsUnder model group).any (checked.core.referencesField ·.id))
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageGroupReference? declaration.id group)

def indexNonIterating? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat checked => some ((declarationsUnder model group).any (checked.core.referencesField ·.id))
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageNonIteratingReference? declaration.id group level)

def selectedGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (key : Option CheckedSemanticIndexKey) : Option Bool :=
  match condition with
  | .flat _ => some false
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageSelectedGroupReference? declaration.id group key)

def unkeyedGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat checked => some ((declarationsUnder model group).any (checked.core.referencesField ·.id))
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageUnkeyedReference? declaration.id group level)

def nonWildcardGroupReferenced? (condition : ValidationMessageCondition model)
    (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  match condition with
  | .flat checked => some ((declarationsUnder model group).any (checked.core.referencesField ·.id))
  | .rule checkedRule => anyKnown ((declarationsUnder model group).map fun declaration =>
      checkedRule.condition.core.messageNonWildcardReference? declaration.id group level)

def anySelectedGroupReferenced? (condition : ValidationMessageCondition model) : Option Bool :=
  anyKnown (model.repeatableGroups.map fun group => condition.selectedGroupReferenced? group.path none)

def keyedGroupGuarded (condition : ValidationMessageCondition model)
    (group : GroupPath) (key : CheckedSemanticIndexKey) : Bool :=
  match condition with
  | .flat _ => false
  | .rule checkedRule => checkedRule.condition.core.keyedMessageGroupGuarded group key

end ValidationMessageCondition
end A12Kernel
