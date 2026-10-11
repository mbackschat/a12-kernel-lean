import A12Kernel.Elaboration.ValidationCondition.ErrorReferences
import A12Kernel.Elaboration.IterationGuard

namespace A12Kernel.ValidationCondition

private def selectionGuards (group : GroupPath) (key : CheckedSemanticIndexKey)
    (source : CheckedSemanticIndexSource model) : Bool :=
  source.group.path == group && sameMessageKey source.key key

private def fieldGuards (group : GroupPath) (key : CheckedSemanticIndexKey) :
    CheckedFieldFillOperand model → Bool
  | .indexed source => selectionGuards group key source
  | .keyed source => selectionGuards group key source.selection.indexSource
  | _ => false

private def groupGuards (group : GroupPath) (key : CheckedSemanticIndexKey) :
    ResolvedGroupListOperand model → Bool
  | .indexed source => selectionGuards group key source
  | .keyed source => selectionGuards group key source.selection.indexSource
  | _ => false

/-- A matching reference licenses lookup, but only positive presence guards license a keyed row
parameter. The all/any distinction is the entity-list rule of RuleErrorTextIterationParamVisitor. -/
private def keyedMessageLeafGuard (group : GroupPath) (key : CheckedSemanticIndexKey) :
    ValidationConditionLeaf model → Bool
  | .indexedFieldPresence .filled source => selectionGuards group key source
  | .keyedGroupPresence .filled source => selectionGuards group key source.selection.indexSource
  | .fieldFill operator source =>
      match operator with
      | .allFieldsFilled => source.operands.any (fieldGuards group key)
      | .atLeastOneFieldFilled | .moreThanOneFieldFilled =>
          !source.operands.isEmpty && source.operands.all (fieldGuards group key)
      | _ => false
  | .groupList operator operands =>
      match operator with
      | .allGroupsFilled => operands.any (groupGuards group key)
      | .atLeastOneGroupFilled => !operands.isEmpty && operands.all (groupGuards group key)
      | _ => false
  | _ => false

/-- One guarding conjunct suffices; every disjunct must supply a guard. This reuses the shared
structural guard algebra without treating arbitrary comparisons as presence guarantees. -/
def keyedMessageGroupGuarded (condition : ValidationCondition model)
    (group : GroupPath) (key : CheckedSemanticIndexKey) : Bool :=
  condition.iterationGuarded (keyedMessageLeafGuard group key)

end A12Kernel.ValidationCondition
