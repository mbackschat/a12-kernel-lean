import A12Kernel.Elaboration.ValidationCondition.StaticIteration
import A12Kernel.Elaboration.ErrorTargetDeclaration

namespace A12Kernel

/-- Why a rule reporting on a group is refused. The Kernel classes are the field target's: a group
the condition does not reference, and a non-root iterated level no reference to the group binds
([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join),
`group-level`). `root`, `repeatable` and `unsupported` are Lean's own boundary: a root group target,
a flat scalar rule and a condition leaf whose reading at the unindexed level is unmeasured. -/
inductive GroupTargetRefusal where
  | unknown
  | root
  | repeatable
  | unsupported
  | notReferenced
  | iterationInvalid (level : RepeatableLevel)
  | scopeMismatch (expected actual : List RepeatableLevel)
  | unbound (unbound : UnboundOperandLevel)
  deriving Repr, DecidableEq

inductive FlatRuleAssemblyError where
  | errorField (error : ResolveError)
  | repeatableErrorField (field : FieldId)
  | iterationScope (error : ValidationCondition.RuleIterationScopeError)
  | iterationScopeMismatch (field : FieldId)
      (expected actual : List RepeatableLevel)
  | errorFieldNotReferenced (field : FieldId)
  | errorFieldIterationInvalid (field : FieldId) (level : RepeatableLevel)
  | formOnlyIteration (field : FieldId) (level : RepeatableLevel)
  | negativeConditionInIteration (level : RepeatableLevel)
  /-- The condition reads a repeatable level the error field does not bind; `unbound` is the
      outermost such level with the facts its class depends on. -/
  | unboundOperandLevel (field : FieldId) (unbound : UnboundOperandLevel)
  | groupErrorTarget (path : GroupPath) (refusal : GroupTargetRefusal)
  deriving Repr, DecidableEq

namespace FlatRuleAssemblyError

/-- The walk's refusal hidden in a scope mismatch. With the error field outside the rule group
    nothing binds a level, so the condition's outermost iterated level is refused with containment.
    Inside it the error field's scope must be a strict prefix of the condition's iteration: the
    condition then reads a level past it, and the first such level is the outermost one refused,
    with the index class for a keyed level parallel to the error field's group and the missing star
    otherwise ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-24d-star-containment)).

    The level is not attributed to the operand that derived it. The DateRange and marked-filter
    readers are measured to follow the walk
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)),
    and a repetition key's level is walked at the key itself, measured from a host outside it
    ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-26k-paired-gates)); an error field with
    repeatable levels of its own takes the class unmeasured
    ([SG9](../../../docs/SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)).
    An error field in a sibling repeatable scope inside the rule group is not a prefix and does not
    count. -/
def unboundLevel? (model : FlatModel) (ruleGroup : GroupPath) :
    FlatRuleAssemblyError → Option FlatRuleAssemblyError
  | .iterationScopeMismatch field derived errorScope =>
      match model.lookupUniqueId field with
      | .ok declaration =>
          (refusedLevel? declaration.groupPath derived errorScope).map fun level =>
            .unboundOperandLevel field (model.unboundOperandLevel ruleGroup declaration.groupPath level)
      | .error _ => none
  | .groupErrorTarget path (.scopeMismatch derived errorScope) =>
      (refusedLevel? path derived errorScope).map fun level =>
        .groupErrorTarget path (.unbound (model.unboundOperandLevel ruleGroup path level))
  | .errorField _ | .repeatableErrorField _ | .iterationScope _ | .errorFieldNotReferenced _
  | .formOnlyIteration _ _ | .negativeConditionInIteration _ | .unboundOperandLevel _ _ | .errorFieldIterationInvalid _ _
  | .groupErrorTarget _ _ => none
where
  refusedLevel? (errorGroup : GroupPath) (derived errorScope : List RepeatableLevel) :
      Option RepeatableLevel :=
    match WrittenFieldPlacement.of ruleGroup errorGroup with
    | .outside => derived.head?
    | .contained =>
        if errorScope.isPrefixOf derived && errorScope != derived then
          (derived.drop errorScope.length).head?
        else none

/-- Project the measured whole-rule gates. The error field's presence in its own condition is a Kernel-checked rule property, and it is measured as its own class: an operand list that names a sibling key rather than the error field draws it, while naming the error field among the keys is admitted. An unguarded negative group-presence condition in a repeatable scope has its own measured class, while a direct positive group guard admits the same negative leaf. An unbound operand level takes the walk's class. Every other assembly refusal returns `none`. -/
def diagnostic? : FlatRuleAssemblyError → Option KernelStaticDiagnostic
  | .errorFieldNotReferenced _ =>
      some KernelStaticDiagnostic.errorFieldNotReferenced
  | .negativeConditionInIteration _ =>
      some KernelStaticDiagnostic.negativeConditionInIteration
  | .errorFieldIterationInvalid _ _ => some .errorFieldIterationInvalid
  | .formOnlyIteration _ level => formOnlyIterationRefusal false { firstInnerLevel := some level }
  | .unboundOperandLevel _ unbound => unbound.diagnostic?
  | .groupErrorTarget _ refusal =>
      match refusal with
      | .notReferenced => some .errorFieldNotReferenced
      | .iterationInvalid _ => some .errorFieldIterationInvalid
      | .unbound unbound => unbound.diagnostic?
      | .unknown | .root | .repeatable | .unsupported | .scopeMismatch _ _ => none
  -- Named rather than wildcarded: a new assembly refusal must be classified, not absorbed. A scope
  -- mismatch the walk explains arrives as `unboundOperandLevel`; what remains is unmeasured.
  | .iterationScopeMismatch _ _ _ | .errorField _ | .repeatableErrorField _ | .iterationScope _ =>
      none

end FlatRuleAssemblyError

end A12Kernel
