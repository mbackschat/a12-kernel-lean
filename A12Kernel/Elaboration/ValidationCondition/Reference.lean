import A12Kernel.Elaboration.ValidationCondition.Core
import A12Kernel.Semantics.MessagePointer

/-! # A12Kernel.Elaboration.ValidationCondition.Reference — structural message references

A fired validation message carries the field instances its rule *refers to*, and that collection is a **structural projection of the checked condition**, never a trace of which cells were read. This module is that projection. It takes the condition and the firing environment and nothing else: it has no document, context, or verdict argument, so it cannot degenerate into a read trace even by accident.

Coordinate assignment follows one rule. A repeatable level fixed by the rule's iteration scope is concrete at the firing instance; a level the star reopened, and every axis below it, is wildcard. Both facts are Kernel-locked upstream at a12-dmkits `bbbbf48e`; [`SOURCES.md`](../../../docs/SOURCES.md) owns that provenance.

Two boundaries are deliberate. Membership is total over the fragment it classifies and **fails closed everywhere else**, so an unsupported operand can never be silently read as "no reference". And this projection is not attached to `FlatRuleMessage`: the emitted record still has no reference channel, because a caller that holds a fired outcome also holds the rule and its environment. [`SG10`](../../../docs/SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration) owns the remaining channel work, the filtered-star operand, and the pointer-shape exclusion.
-/

namespace A12Kernel

/-- Why one structural reference projection has no answer. No case means an empty reference set: the leaf, atom, or operand family is outside the current fragment, a filtered star's operand coordinates are unpinned, or the firing environment does not bind a level the reference needs.

    There is deliberately no unresolvable-field case. Every membership route starts from the model's own declarations rather than from a bare identifier, so a reference either has a declaration or is not reported at all. -/
inductive ReferenceProjectionError where
  | unclassifiedLeaf
  | unclassifiedAtom
  | unclassifiedOperand
  | filteredStarOperand
  | unreopenedReference (field : FieldId)
  | binding (error : EnvBindingError)
  deriving Repr, DecidableEq

/-- Every repeatable level of an unstarred reference is fixed by the rule's iteration scope, so its pointer is the concrete instance the rule is evaluating. -/
def concreteFieldPointer (declaration : FlatFieldDecl) (environment : Env) :
    Except ReferenceProjectionError MessagePointer :=
  match environment.pathForScope declaration.repeatableScope with
  | .error error => .error (.binding error)
  | .ok path => .ok (MessagePointer.ofCellAddr { field := declaration.id, path })

/-- One reopened reference: the first `boundCount` levels of the field's **own** repeatable scope are concrete, and every level from there down is wildcard. Reading the concrete prefix out of that scope rather than out of the star's axes is what lets one rule serve a starred field and a starred group's deeper descendant alike, and it makes the coordinate positions structural instead of assuming that two level lists agree.

    A reference with no reopened level is refused rather than silently projected as an exact address: that would be [`concreteFieldPointer`](A12Kernel.concreteFieldPointer)'s job, and reaching it here means the caller's star and its declaration disagree. -/
def reopenedFieldPointer (declaration : FlatFieldDecl) (boundCount : Nat)
    (environment : Env) : Except ReferenceProjectionError MessagePointer :=
  if declaration.repeatableScope.length ≤ boundCount then
    .error (.unreopenedReference declaration.id)
  else
    match environment.pathForScope (declaration.repeatableScope.take boundCount) with
    | .error error => .error (.binding error)
    | .ok bound => .ok {
        field := declaration.id
        coordinates := bound.map .concrete ++
          List.replicate (declaration.repeatableScope.length - boundCount) .wildcard }

/-- A starred field reference reopens from its own `firstStar`. The certificate's `ancestryOwned` and `firstStarWithin` obligations make its refusal branch unreachable. -/
def starFieldPointer (checked : CheckedStarFieldPath model) (environment : Env) :
    Except ReferenceProjectionError MessagePointer :=
  reopenedFieldPointer checked.declaration checked.path.firstStar environment

/-- Membership by *sieving* the model's declarations through a family's own reference predicate, rather than by traversing its operands.

    This is sound exactly when the family cannot carry a starred operand and its predicate is exhaustive over the family's constructors with no catch-all: the sieve then inherits precisely that predicate's coverage and can neither miss a reference it reports nor invent one. The same shortcut would be wrong for a starred family, because the predicate reports the starred field while its coordinates are not concrete.

    Every pointer it emits therefore comes from [`concreteFieldPointer`](A12Kernel.concreteFieldPointer) and is an exact instance address; `sievedFieldPointers_exact` proves that. A reference the firing environment does not bind — a subtree field below a repeatable level deeper than the rule's own scope — fails the whole projection at that exact level instead of being dropped or wildcarded. -/
def sievedFieldPointers (model : FlatModel)
    (references : FlatFieldDecl → Bool) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (model.fields.filter references).mapM (concreteFieldPointer · environment)

/-- Whether one scalar numeric atom's share of a leaf's membership predicate may be sieved.

    Sieving reuses a family's whole `referencesField`, so it adopts the scope claim of *every* arm at once. Ten atoms name resolved fields or fixed Number field lists directly, and adopting those is adopting field identity. The fixed group count is different in kind: its operands are group references, and its arm of the predicate reports **every field in the counted subtree** — a meaning established for the static error-field reference gate, not for this pointer channel. Whether the Kernel expands a *fixed* group into descendant field pointers is unmeasured; [`spec/01`](../../../spec/01-data-model.md) specifies that expansion only for a *starred* group, and the same open question already refuses the group-list leaf's unstarred group operand. So it is refused here too, on the same terms rather than by parity with the starred arm.

    Written as an exhaustive match so that a new atom constructor must choose rather than default into the sieve. -/
def NumericValidationAtom.sievableReference : NumericValidationAtom → Bool
  | .field _ | .baseYear _ | .baseYearDatePart _ _ _ | .temporalFieldPart _ _
  | .stringLength _ | .stringRange _ _ _ | .fieldValueAsNumber _
  | .dateDifference _ _ _ | .dateTimeDifference _ _ _ | .dayDifference _ _ _
  | .aggregate _ _ => true
  | .filledGroupCount _ => false

/-- A filtered star is refused rather than projected. Its own field pointer would be the plain starred one, but the measured account pins only that its `Having` operands *join* the set, not which coordinates they carry, and inventing them would make an incomplete set look complete. -/
def CheckedNumberEntityOperand.referencePointer (environment : Env) :
    CheckedNumberEntityOperand model →
      Except ReferenceProjectionError MessagePointer
  | .field source => concreteFieldPointer source.declaration environment
  | .star source => starFieldPointer source.source environment
  | .starHaving _ => .error .filteredStarOperand

/-- Every authored slot contributes, in authored order, whether or not a runtime scan would reach it. -/
def CheckedNumberEntitySource.referencePointers
    (source : CheckedNumberEntitySource model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  source.operands.mapM (CheckedNumberEntityOperand.referencePointer environment)

/-- The classified atom fragment. Entity-list aggregates share one operand projection, and every delegated scalar atom is sieved on the same terms as the scalar leaf — including its refusal of the fixed group count. Under addressed admission a delegated declaration may be repeatable but is bound by the rule's own iteration scope, so it projects concretely; nothing here reopens a level. The leaf's own checked value-count and row-product sources fail closed. -/
def OrderedNumericValidationAtom.referencePointers (environment : Env) :
    OrderedNumericValidationAtom model →
      Except ReferenceProjectionError (List MessagePointer)
  | .ordinary source =>
      if NumericValidationAtom.sievableReference source then
        sievedFieldPointers model
          (fun declaration => source.referencesField model declaration.id)
          environment
      else
        .error .unclassifiedAtom
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.referencePointers environment
  | _ => .error .unclassifiedAtom

/-- Traverse one authored operand expression left to right. Literals reference nothing; a failing atom fails the whole projection. -/
private def expressionPointers (environment : Env) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Except ReferenceProjectionError (List MessagePointer)
  | .atom atom => atom.referencePointers environment
  | .literal _ => pure []
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      expressionPointers environment body
  | .binary _ left right | .power left right | .extremum _ left right => do
      pure ((← expressionPointers environment left) ++
        (← expressionPointers environment right))

/-- A starred group contributes its **descendant fields**, never a pointer to the group. Expansion is recursive by construction: every declaration whose group path extends the starred one participates, however deep, and each reopens from the star's own `firstStar` against its own scope. A field declared below a deeper repeatable descendant therefore gains extra wildcards without the projection knowing that group exists.

    Declaration order is retained for determinism only, on the same terms as the whole projection. -/
def starredGroupPointers (model : FlatModel) (groupPath : GroupPath)
    (boundCount : Nat) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (model.fields.filter fun declaration =>
      groupPath.isPrefixOf declaration.groupPath).mapM
    (reopenedFieldPointer · boundCount environment)

/-- An unstarred group operand is refused. It has no field pointer of its own, and whether the kernel expands it the way it expands a starred group is unmeasured. -/
def ResolvedGroupListOperand.referencePointers (environment : Env) :
    ResolvedGroupListOperand model →
      Except ReferenceProjectionError (List MessagePointer)
  | .field declaration =>
      (concreteFieldPointer declaration environment).map ([·])
  | .starredGroup source =>
      starredGroupPointers model source.group.path source.path.firstStar environment
  | .starredGroupPresence source =>
      starredGroupPointers model source.groupPath source.path.firstStar environment
  | .group _ => .error .unclassifiedOperand

/-- Two membership strategies, chosen by whether a family can carry a starred operand.

    A family that can must be traversed explicitly, so that each operand reaches the coordinate rule that fits it. A family that cannot is sieved instead, on the terms [`sievedFieldPointers`](A12Kernel.sievedFieldPointers) states. Both sieved families qualify structurally: the flat fragment's leaves and the scalar numeric fragment's atoms each hold resolved single-field declarations, fixed Number field lists, or fixed group references whose resolution rejects both the starred `RuleGroup` and a repeatable ordinary path, and each family's `referencesField` covers every constructor with no catch-all.

    Star-freedom licenses the *coordinate* rule but not every arm's *membership* meaning, so the numeric leaf is sieved only once every atom passes [`NumericValidationAtom.sievableReference`](A12Kernel.NumericValidationAtom.sievableReference). A single refused atom refuses the whole leaf, because a sieve cannot report part of a predicate.

    A consequence is that the two strategies retain different orders — authored for traversal, declaration for sieving. That is admissible only because the result carries no ordering claim at all. -/
def ValidationConditionLeaf.referencePointers (environment : Env) :
    ValidationConditionLeaf model →
      Except ReferenceProjectionError (List MessagePointer)
  | .orderedNumeric _ comparison => do
      pure ((← expressionPointers environment comparison.left) ++
        (← expressionPointers environment comparison.right))
  | .groupList _ operands =>
      (·.flatten) <$>
        operands.mapM (ResolvedGroupListOperand.referencePointers environment)
  | .repeatableFieldPresence _ declaration =>
      (concreteFieldPointer declaration environment).map ([·])
  | .flat condition =>
      sievedFieldPointers model
        (fun declaration => condition.referencesField declaration.id) environment
  | .numeric _ comparison =>
      if comparison.left.allAtoms NumericValidationAtom.sievableReference &&
          comparison.right.allAtoms NumericValidationAtom.sievableReference then
        sievedFieldPointers model
          (fun declaration => comparison.referencesField model declaration.id)
          environment
      else
        .error .unclassifiedAtom
  | _ => .error .unclassifiedLeaf

private def treePointers (environment : Env) :
    ValidationCondition model →
      Except ReferenceProjectionError (List MessagePointer)
  | .leaf value => value.referencePointers environment
  | .and left right | .or left right => do
      pure ((← treePointers environment left) ++
        (← treePointers environment right))

/-- The rule's structural reference set at one firing environment. Both connectives contribute every branch, because a reference exists by being authored rather than by being decisive.

    Duplicates are removed once. The retained order is authored traversal order and is **not** a kernel claim: the engine's own collection is a hash set whose iteration order is incidental, so a consumer may compare membership but never position. -/
def ValidationCondition.referencePointers (condition : ValidationCondition model)
    (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (treePointers environment condition).map List.eraseDups

end A12Kernel
