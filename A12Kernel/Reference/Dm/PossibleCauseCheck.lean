import A12Kernel.Elaboration.ErrorTargetDeclaration
import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Reference.Dm.ParallelValidation

/-! # A rule's possible-cause filter against the entities its condition names

Kernel 31.3.1 checks, as the last check of its model pass, that every entry of a rule's possible-cause
filter names an entity the condition references, by the shortest relative path from the rule's group
([spec/01 §3.1](../../../spec/01-data-model.md#the-possible-cause-filter), a12-dmkits KF682). The gate's
string-level account is [`customErrorEntityRefusals`](../../Elaboration/ErrorTargetDeclaration.lean); this
module supplies its two inputs from a DM rule: the candidate entities, read off the condition as written,
and whether the check runs at all.

**The candidates come from the unexpanded condition.** A field read names its field. A group operand stays
a group only where the operator reads it as one: the group-presence predicates, the group-list
quantifiers, the filled-group count and a `SumOfTerms` iteration; elsewhere it names every field below it.
A starred segment on the way to a field is not itself named. A `Having` body's references count, read from
the rule's group as every operand is, and so does the index field a semantic index keys on, with a key
written as a reference. `CurrentRepetition` names nothing. The join index field a parallel iteration adds
is not read here: no row of the filter measures it.
-/

namespace A12Kernel.Dm

open A12Kernel

/-- The operators whose group operand stays the group rather than naming its fields: the `group` cells of
[spec/14's Q column](../../../spec/14-operator-reference.md#referenced-entity-inventory). -/
private def groupReadingCalls : List String :=
  ["GroupFilled", "GroupNotFilled", "AllGroupsFilled", "NoGroupFilled", "AtLeastOneGroupFilled",
    "NotAllGroupsFilled", "GroupsNotCollectivelyFilled", "NumberOfFilledGroups", "SumOfTerms"]

/-- The declared entity a written path names from the rule's group, stars and the correlation mark set
aside: a field as `.inl`, a group as `.inr`, both as absolute name lists. -/
private def namedEntity (model : FlatModel) (group : GroupPath) (path : Path) :
    Option (List String ⊕ GroupPath) :=
  let plain : Path := { path with
    correlated := false
    segments := path.segments.map fun segment => { segment with star := false } }
  match plain.toFieldPath? with
  | none => if plain.segments.isEmpty then (GroupPath.walkUp group plain.ups).toOption.map .inr else none
  | some field =>
      match model.resolveFieldDeclarationUnchecked group field with
      | .ok declaration => some (.inl (declaration.groupPath ++ [declaration.name]))
      | .error _ => (model.groupNamedBy? group field).map .inr

/-- The fields below a group, in model order. -/
private def fieldsBelow (model : FlatModel) (group : GroupPath) : List (List String) :=
  (model.fields.filter fun field => group.isPrefixOf field.groupPath).map fun field =>
    field.groupPath ++ [field.name]

private def fieldPath? (model : FlatModel) (id : FieldId) : Option (List String) :=
  (model.fields.find? (·.id == id)).map fun field => field.groupPath ++ [field.name]

private def groupEntities (model : FlatModel) (asGroup : Bool) (group : GroupPath) : List (List String) :=
  if asGroup then [group] else fieldsBelow model group

mutual
private partial def expressionEntities (model : FlatModel) (group : GroupPath) (asGroup : Bool) :
    Expr → List (List String)
  | .value reference | .entity reference => referenceEntities model group asGroup reference
  | .constant "RuleGroup" => groupEntities model asGroup group
  | .call "CurrentRepetition" _ _ _ => []
  | .call id arguments listed scope =>
      let asGroup := groupReadingCalls.contains id
      argumentsEntities model group asGroup arguments ++
        argumentsEntities model group false (listed.getD []) ++
        (scope.map (referenceEntities model group true)).getD []
  | .arith _ left right | .compare _ left right =>
      expressionEntities model group false left ++ expressionEntities model group false right
  | .parens body | .braces body => expressionEntities model group asGroup body
  | .logic _ parts => parts.flatMap (expressionEntities model group false)
  | _ => []

private partial def referenceEntities (model : FlatModel) (group : GroupPath) (asGroup : Bool)
    (reference : Reference) : List (List String) :=
  let own := match namedEntity model group reference.path with
    | some (.inl field) => [field]
    | some (.inr named) => groupEntities model asGroup named
    | none => []
  -- A semantic index names the field it keys on, and a key written as a reference names its own entity.
  let indexed := match reference.index, namedEntity model group reference.path with
    | some key, some named =>
        let selected := match named with | .inl field => field.dropLast | .inr named => named
        let indexField := ((model.semanticIndexGroupForPath? selected).bind (·.indexField)).bind
          (fieldPath? model)
        indexField.toList ++ match key with
          | .reference child => referenceEntities model group false child
          | .literal _ => []
    | _, _ => []
  let body := (reference.filter.map (expressionEntities model group false)).getD []
  own ++ indexed ++ body

private partial def argumentsEntities (model : FlatModel) (group : GroupPath) (asGroup : Bool) :
    List Argument → List (List String)
  | [] => []
  | .mk first rangeEnd :: rest =>
      expressionEntities model group asGroup first ++
        ((rangeEnd.map (expressionEntities model group asGroup)).getD []) ++
        argumentsEntities model group asGroup rest
end

/-- The relative paths a rule's condition offers its possible-cause filter, spelled as the entries are
compared, or the syntax error that leaves the condition unread. -/
def possibleCauseCandidates (model : FlatModel) (language : Language) (rule : DmRule) :
    Except SyntaxError (List String) := do
  let text ← parseText language rule.condition
  pure ((expressionEntities model rule.group false text.body).map (possibleCauseRelPath rule.group)).eraseDups

/-- The observed labels of the index and sort refusals the Kernel's model pass raises before it judges
the filter: an index or sort field naming nothing, or one disqualified as a key. -/
private def orderingGateLabels : List String :=
  (RowFieldRefusal.all.filter (·.isOrderingGate)).map (·.label)

/-- **The reference classes of a rule's possible-cause filter**, in slot order, or the reason this
account cannot judge the rule. The check does not run when the rule's own check draws a class, nor when
an earlier check of the model pass refused the model: a refused index or sort nomination, read off the
model, or one the host reports through `earlierModelCheckRefused`, such as an invalid time zone, whose
legal set is the host's. A rule this account does not lower, without a class, is not judged. -/
def possibleCauseRefusals (model : DmModel) (language : Language) (rule : DmRule)
    (earlierModelCheckRefused : Bool := false) : Except String (List KernelStaticDiagnostic) := do
  let some filter := rule.possibleCauses | return []
  if !filter.parsesCondition then return []
  if earlierModelCheckRefused || model.refusals.any (orderingGateLabels.contains ·.2) then return []
  match checkValidationRule model language rule with
  | .error refusal =>
      if refusal.kernelClass?.isSome then return []
      throw s!"rule {rule.name} is not lowered: {refusal.detail}"
  | .ok _ =>
      let candidates ← (possibleCauseCandidates model.flat language rule).mapError
        fun error => s!"rule {rule.name} does not parse: {repr error}"
      pure (customErrorEntityRefusals false true candidates filter)

end A12Kernel.Dm
