import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.HavingNumericAtom
import A12Kernel.Elaboration.FieldEntityAdmission

/-! # The candidate-environment gate of unmarked filter reads

An unmarked read inside a filter is resolved in the candidate environment, and the Kernel asks
whether that environment holds its repeatable level only after the whole body has resolved. A
numeric expression read by the same set-expression parser, `SumOfTerms`' term, asks the same question
of each of its atoms, so the numeric-atom case is its own function.
-/

namespace A12Kernel

/-- The refusal for an unmarked entity read the candidate environment does not hold. -/
private def candidateEntityRefusal? (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels : List RepeatableLevel) (ref : SurfaceHavingEntityOperand) :
    Option CorrelationElabError := do
  guard (ref.origin == .inner)
  let (path, scope) ← ref.bindingRead? model declaringGroup
  guard !(repeatableScopeAvailable scope candidateLevels)
  pure (.fieldOutsideEnvironment .inner path candidateLevels scope)

private def candidateFieldRefusal? (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels : List RepeatableLevel) (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Option CorrelationElabError := do
  guard (origin == .inner)
  let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup reference).toOption
  guard !(repeatableScopeAvailable declaration.repeatableScope candidateLevels)
  pure (.fieldOutsideEnvironment .inner declaration.path candidateLevels declaration.repeatableScope)

private def candidateGroupRefusal? (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels : List RepeatableLevel) (origin : HavingOrigin) (reference : SurfaceGroupReference) :
    Option CorrelationElabError := do
  guard (origin == .inner)
  let resolved ← (reference.resolveAgainst declaringGroup).toOption
  let missing ← (model.repeatableScopeForGroupPath resolved.path).find? fun level =>
    !candidateLevels.contains level
  pure (.repetitionOutsideEnvironment .inner resolved.path candidateLevels missing)

/-- The refusal for one numeric filter atom reading a level its candidate environment does not hold. -/
def SurfaceHavingNumericAtom.candidateEnvironmentRefusal? (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels : List RepeatableLevel) :
    SurfaceHavingNumericAtom → Option CorrelationElabError :=
  let entity := candidateEntityRefusal? model declaringGroup candidateLevels
  let field := candidateFieldRefusal? model declaringGroup candidateLevels
  let group := candidateGroupRefusal? model declaringGroup candidateLevels
  fun
  | .collectionCount count => (count.source.first :: count.source.rest).findSome? entity
  | .firstFilled source | .groupCount source | .product source | .aggregate _ source => (source.first :: source.rest).findSome? entity
  | .dateDifference _ left right | .dayDifference left right =>
      (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .dateTimeDifference _ left right =>
      (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .temporalDifference _ left right => (left.fields ++ right.fields).findSome? fun ref => field ref.origin ref.field
  | .temporalExpressionPart _ source =>
      ((source.entitySources.flatMap fun source => source.first :: source.rest).findSome? entity).orElse fun _ =>
        source.fields.findSome? fun ref => field ref.origin ref.field
  | .baseYear | .baseYearDatePart _ _ | .clockPart _ _ => none
  | .fieldValueAsNumber reference => field reference.origin reference.field
  | .field reference => field reference.origin reference.field
  | .dateRangeBoundPart origin reference _ _ | .stringLength origin reference | .stringRange origin reference _ _ | .temporalPart origin reference _ => field origin reference
  | .repetition reference => group reference.origin reference.group

/-- The first **unmarked** reference of an authored filter, in authored order, whose level its
    candidate environment does not hold. The star route asks it once every leaf has resolved and
    passed its comparison's kind and scale gates, because the Kernel names a body's refused
    comparison ahead of the filter's iteration class, on a repetition the filter does not iterate
    too ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-filter-body)). -/
def SurfaceCorrelatedHaving.candidateEnvironmentRefusal? (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels : List RepeatableLevel) :
    SurfaceCorrelatedHaving → Option CorrelationElabError
  | .customCondition _ => none
  | .repetitionNotUnique keys scope => (keys.first :: keys.rest ++ scope.toList).findSome? entity
  | .numeric _ left right | .tolerance _ left right =>
      (left.atoms ++ right.atoms).findSome?
        (SurfaceHavingNumericAtom.candidateEnvironmentRefusal? model declaringGroup candidateLevels)
  | .compareFields _ left right =>
      (field left.origin left.field).orElse fun _ => field right.origin right.field
  | .compareBoolean _ reference _ | .compareStrings _ reference _ => field reference.origin reference.field
  | .dateRange source => source.entities.findSome? entity
  | .compareStringExpression _ left right =>
      ((left.fields ++ right.fields).flatMap SurfaceHavingSelectedOperand.entities).findSome? entity
  | .compareSelected _ left right => (left.entities ++ right.entities).findSome? entity
  | .compareTemporalExpression _ left right =>
      (((left.entitySources ++ right.entitySources).flatMap fun source => source.first :: source.rest).findSome? entity).orElse fun _ =>
        (left.fields ++ right.fields).findSome? fun ref => field ref.origin ref.field
  | .compareTemporal _ left right =>
      (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .literalMembership _ reference _ => field reference.origin reference.field
  | .fieldMembership _ subjects members =>
      (subjects.first :: subjects.rest ++ members.first :: members.rest).findSome? entity
  | .dateValidity _ source => source.references.findSome? fun ref => field ref.origin ref.field
  | .uniqueness source | .fieldFill _ source | .literalList _ source _ =>
      (source.first :: source.rest).findSome? entity
  | .presence _ reference | .typeValidity _ reference _ | .stringPattern _ reference _ => field reference.origin reference.field
  | .groupPresence _ origin reference => group origin reference
  | .groupFill _ first rest => (first :: rest).findSome? entity
  | .and left right | .or left right =>
      (left.candidateEnvironmentRefusal? model declaringGroup candidateLevels).orElse fun _ =>
        right.candidateEnvironmentRefusal? model declaringGroup candidateLevels
  | .scaleWarningSuppressed body => body.candidateEnvironmentRefusal? model declaringGroup candidateLevels
where
  entity (ref : SurfaceHavingEntityOperand) : Option CorrelationElabError :=
    candidateEntityRefusal? model declaringGroup candidateLevels ref
  field (origin : HavingOrigin) (reference : SurfaceFieldPath) : Option CorrelationElabError :=
    candidateFieldRefusal? model declaringGroup candidateLevels origin reference
  group (origin : HavingOrigin) (reference : SurfaceGroupReference) : Option CorrelationElabError :=
    candidateGroupRefusal? model declaringGroup candidateLevels origin reference

end A12Kernel
