import A12Kernel.Elaboration.ValidationCondition.Evaluation
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

/-- A group operand contributes the fields of its **whole subtree**, recursively and never a pointer to the group. The extent itself is [`FlatModel.groupSubtreeFields`](A12Kernel.FlatModel.groupSubtreeFields), shared with the entity list's group slot so that one site cannot disagree with another about how far a group reaches.

    **One depth rule serves both repetition shapes**, which is why they share this function rather than each owning a projection: repeatable levels **above** `boundCount` stay concrete at the firing row, and every repeatable level at or below it is **wildcarded**. The starred form supplies its star's own `firstStar`; the unstarred form supplies its authored path's own repeatable scope, and `fixedGroupPointers` below states why that is the whole scope rather than the levels strictly above it. Measured at a12-dmkits `bffe9cca`: an unstarred `/Shipment/Carrier` reaches `/Shipment[1]/Carrier[1]/Handoffs[0]/Site`, wildcarding the nested repeatable level while the message's own anchor stays concrete throughout. The two channels are different addresses of the same firing.

    A member with **nothing** reopened below `boundCount` is the ordinary case here rather than the disagreement [`reopenedFieldPointer`](A12Kernel.reopenedFieldPointer) refuses — a group's direct non-repeatable field has no level to wildcard, and the same measured set carries it as `/Shipment[1]/Carrier[1]/Name` with no coordinates at all. It is projected concretely, which is the same answer the depth rule gives with an empty wildcard suffix.

    Declaration order is retained for determinism only, on the same terms as the whole projection. -/
def groupExpansionPointers (model : FlatModel) (groupPath : GroupPath)
    (boundCount : Nat) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (model.groupSubtreeFields groupPath).mapM fun declaration =>
    if declaration.repeatableScope.length ≤ boundCount then
      concreteFieldPointer declaration environment
    else
      reopenedFieldPointer declaration boundCount environment

/-- An unstarred group operand's expansion. The subtree-reaching half is measured on a nonrepeatable model, where the deeper descendant group's field joins the set and refutes direct-child expansion; the coordinate half is measured at `bffe9cca`. The relation is identical in the presence, entity-list, and count positions.

    The depth is the **whole** repeatable scope of the authored path, its own level included, rather than the levels strictly above it. On every measured row those agree, because the wildcard gate keeps an unstarred entity-list operand's own group nonrepeatable and the wildcarding therefore begins strictly inside the subtree. They diverge only for a *repeatable* operand, which the presence carrier accepts unstarred and which no row covers; taking the whole scope leaves that shape failing closed at the unbound level instead of inventing a coordinate for it. -/
def fixedGroupPointers (model : FlatModel) (reference : ResolvedGroupReference)
    (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  groupExpansionPointers model reference.path
    (model.repeatableScopeForGroupPath reference.path).length environment

/-- A starred group contributes its **descendant fields**, never a pointer to the group, reopening from the star's own `firstStar`. -/
def starredGroupPointers (model : FlatModel) (groupPath : GroupPath)
    (boundCount : Nat) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  groupExpansionPointers model groupPath boundCount environment

/-- One authored group slot's whole expansion, in whichever repetition shape it was authored. Every carrier that retains a group slot projects through this one function, so no two can disagree about how far a group reaches or which coordinates its fields carry. -/
def CheckedEntityGroupSource.referencePointers
    (source : CheckedEntityGroupSource model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  match source with
  | .fixed reference => fixedGroupPointers model reference environment
  | .starred terminal =>
      starredGroupPointers model terminal.group.path terminal.path.firstStar
        environment
  | .starredPresence terminal =>
      starredGroupPointers model terminal.groupPath terminal.path.firstStar environment

/-- A filtered star is refused rather than projected. Its own field pointer would be the plain starred one, but the measured account pins only that its `Having` operands *join* the set, not which coordinates they carry, and inventing them would make an incomplete set look complete. -/
def CheckedNumberEntityOperand.referencePointers (environment : Env) :
    CheckedNumberEntityOperand model →
      Except ReferenceProjectionError (List MessagePointer)
  | .field source => (concreteFieldPointer source.declaration environment).map ([·])
  | .star source => (starFieldPointer source.source environment).map ([·])
  | .starHaving _ => .error .filteredStarOperand
  | .group slot => slot.source.referencePointers environment

/-- Every authored slot contributes, in authored order, whether or not a runtime scan would reach it. A slot contributes **one** pointer or, for a group, its whole expansion, which is why this flattens rather than pairing one pointer per slot. -/
def CheckedNumberEntitySource.referencePointers
    (source : CheckedNumberEntitySource model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$>
    source.operands.mapM (CheckedNumberEntityOperand.referencePointers environment)

/-- A projection-bearing token operand references its **declaring** field. The stored-versus-category choice is not part of a reference: `MessagePointer` has no projection slot, and the channel reports field instances.

    The filter lives in an `Option` field rather than its own constructor here, so the filtered-star refusal has to be made explicitly instead of falling out of the match. It is the same refusal, for the same unwitnessed-coordinates reason.

    A group slot contributes its whole recursive expansion through the shared projection, which is why this is list-valued where a field-denoting slot contributes exactly one pointer. -/
def CheckedTokenEntityOperand.referencePointers (environment : Env) :
    CheckedTokenEntityOperand model →
      Except ReferenceProjectionError (List MessagePointer)
  | .field source =>
      (concreteFieldPointer source.declaration environment).map ([·])
  | .star source =>
      if source.filter.isSome then .error .filteredStarOperand
      else (starFieldPointer source.source environment).map ([·])
  | .group slot => slot.source.referencePointers environment

def CheckedTokenValueCountSource.referencePointers
    (checked : CheckedTokenValueCountSource model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> checked.source.operands.mapM
    (CheckedTokenEntityOperand.referencePointers environment)

/-- The Boolean/Confirm companion carries the identical operand shape, including the optional
    filter and group slot, so it makes the identical decision. Its fixed canonical-token
    projection is invisible here for the same reason the token projection is. -/
def CheckedBooleanValueCountOperand.referencePointers (environment : Env) :
    CheckedBooleanValueCountOperand model expected →
      Except ReferenceProjectionError (List MessagePointer)
  | .field source =>
      (concreteFieldPointer source.declaration environment).map ([·])
  | .star source =>
      if source.filter.isSome then .error .filteredStarOperand
      else (starFieldPointer source.source environment).map ([·])
  | .group source => source.source.referencePointers environment

def CheckedBooleanValueCountSource.referencePointers
    (checked : CheckedBooleanValueCountSource model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> checked.operands.mapM
    (CheckedBooleanValueCountOperand.referencePointers environment)

/-- A row-paired product references both starred value fields and carries no filter at all. Its certificate forces one shared star path, so the two pointers differ only in field identity — which is why this needs no pairing notion of its own. -/
def CheckedNumericProductAggregate.referencePointers
    (checked : CheckedNumericProductAggregate model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) := do
  pure [← starFieldPointer checked.left.source environment,
    ← starFieldPointer checked.right.source environment]

/-- The complete ordered atom family. Every constructor is classified, so the only refusals reaching a caller from here are the sievability gate's fixed group count and a filtered star; there is no catch-all, and a new atom must state its own projection.

    Number entity lists share one operand projection; each token-family source keeps its own, because their operand types are distinct and their filter is an optional field rather than a constructor. Every delegated scalar atom is sieved on the same terms as the scalar leaf, including its refusal of the fixed group count. Under addressed admission a delegated declaration may be repeatable but is bound by the rule's own iteration scope, so it projects concretely; nothing in the delegated arm reopens a level. -/
def OrderedNumericValidationAtom.referencePointers (environment : Env) :
    OrderedNumericValidationAtom model →
      Except ReferenceProjectionError (List MessagePointer)
  | .ordinary source =>
      sievedFieldPointers model
        (fun declaration => source.referencesField model declaration.id)
        environment
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.referencePointers environment
  | .tokenValueCount source => source.referencePointers environment
  | .booleanValueCount source => source.referencePointers environment
  | .sumOfProducts source => source.referencePointers environment

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

/-- Both group operand forms expand to descendant fields and neither yields a group pointer; they differ only in coordinates, which is exactly the starred-versus-unstarred split. -/
def ResolvedGroupListOperand.referencePointers (environment : Env) :
    ResolvedGroupListOperand model →
      Except ReferenceProjectionError (List MessagePointer)
  | .field declaration =>
      (concreteFieldPointer declaration environment).map ([·])
  | .starredGroup source =>
      starredGroupPointers model source.group.path source.path.firstStar environment
  | .starredGroupPresence source =>
      starredGroupPointers model source.groupPath source.path.firstStar environment
  | .group reference => fixedGroupPointers model reference environment

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
      sievedFieldPointers model
        (fun declaration => comparison.referencesField model declaration.id)
        environment
  | .groupPresence _ reference => fixedGroupPointers model reference environment
  | .guardedRootCurrentRepetition guard _ _ =>
      (concreteFieldPointer guard environment).map ([·])
  | .guardedRepeatableCurrentRepetition guard _ _ =>
      (concreteFieldPointer guard environment).map ([·])
  | .iteratedDateRangeEquality comparison => do
      pure [← concreteFieldPointer comparison.left.declaration environment,
        ← concreteFieldPointer comparison.right.declaration environment]
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
