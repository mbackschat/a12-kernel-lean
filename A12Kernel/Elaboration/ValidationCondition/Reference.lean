import A12Kernel.Elaboration.ValidationCondition.Evaluation
import A12Kernel.Semantics.MessageIndex

/-! # A12Kernel.Elaboration.ValidationCondition.Reference — structural message references

A fired validation message carries the field instances its rule *refers to*, and that collection is a **structural projection of the checked condition**, never a trace of which cells were read. Selected operands additionally need admitted index-cache insertions and normalized query keys; this projection has no payload reader or verdict argument. The [selected-reference checkpoint](../../../docs/sources/message-and-pointer-probes.md#src-selected-message-reference-resolution) separates cache lookup from duplicate-excluding value evaluation.

For ordinary and starred operands, coordinate assignment follows one rule. A repeatable level fixed by the rule's iteration scope is concrete at the firing instance; a level the star reopened, and every axis below it, is wildcard. Both facts are Kernel-locked upstream at a12-dmkits `bbbbf48e`; [`SOURCES.md`](../../../docs/SOURCES.md) owns that provenance.

Two boundaries are deliberate. Membership is total over the fragment it classifies and **fails closed everywhere else**, so an unsupported operand can never be silently read as "no reference". And this projection is not attached to `FlatRuleMessage`: the emitted record still has no reference channel, because a caller that holds a fired outcome also holds the rule and its environment. [`SG10`](../../../docs/SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration) owns the remaining channel work, the Number and Boolean/Confirm filtered-star carriers, and the pointer-shape exclusion.
-/

namespace A12Kernel

/-- Why one structural reference projection has no answer. No case means an empty reference set: the leaf, atom, or operand family is outside the current fragment, a filtered star's operand coordinates are unpinned, or the firing environment does not bind a level the reference needs.

    `incoherentHavingField` is fail-closed protection for the one route whose checked representation retains a resolved Number field rather than its declaration. [`CheckedStarHaving.wellFormed`](A12Kernel.CheckedStarHaving.wellFormed) makes it unreachable for an elaborated filter. -/
inductive ReferenceProjectionError where
  | unclassifiedLeaf
  | unclassifiedAtom
  | unclassifiedOperand
  | filteredStarOperand
  | incoherentHavingField (field : FieldId)
  | unreopenedReference (field : FieldId)
  | missingIndexContext
  | binding (error : EnvBindingError)
  deriving Repr, DecidableEq

/-- Inputs owned by cache admission, independently of payload validity or evaluation phase. Cache population order is supplied rather than inferred from document rows. -/
structure MessageReferenceInputs where
  cache : MessageIndexCache
  keyAt : CellAddr → Option SemanticIndexKey

/-- Every repeatable level of an unstarred reference is fixed by the rule's iteration scope, so its pointer is the concrete instance the rule is evaluating. -/
def concreteFieldPointer (declaration : FlatFieldDecl) (environment : Env) :
    Except ReferenceProjectionError MessagePointer :=
  match environment.pathForScope declaration.repeatableScope with
  | .error error => .error (.binding error)
  | .ok path => .ok (MessagePointer.ofCellAddr { field := declaration.id, path })

/-- Index selection owns one coordinate; every deeper repeatable payload level remains wildcard. Dynamic key scopes must be fully bound, even when cache lookup has no association. -/
private def selectedReferencePointers (group : RepeatableGroupDecl)
    (indexDeclaration : FlatFieldDecl) (key : CheckedSemanticIndexKey)
    (payloads : List FlatFieldDecl) (environment : Env)
    (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := do
  let some inputs := inputs | throw .missingIndexContext
  let parent ← (environment.pathForScope indexDeclaration.repeatableScope.dropLast).mapError .binding
  let (key, keyPointers) ← match key with
    | .literal token _ => pure (some token, [])
    | .field declaration => do
        let path ← (environment.pathForScope declaration.repeatableScope).mapError .binding
        let address : CellAddr := { field := declaration.id, path }
        pure (inputs.keyAt address, [MessagePointer.ofCellAddr address])
  let coordinate := inputs.cache.lookup group.level parent key
  let selectedPrefix := parent.map MessageRepetitionCoordinate.concrete ++ [coordinate]
  pure (keyPointers ++ (indexDeclaration :: payloads).map fun declaration => {
    field := declaration.id
    coordinates := selectedPrefix ++ List.replicate
      (declaration.repeatableScope.length - indexDeclaration.repeatableScope.length) .wildcard })

def CheckedSemanticIndexSource.referencePointers (source : CheckedSemanticIndexSource model)
    (environment : Env) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  selectedReferencePointers source.group source.indexDeclaration source.key
    [source.targetDeclaration] environment inputs

def CheckedKeyedEntityExtent.referencePointers (source : CheckedKeyedEntityExtent model)
    (environment : Env) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  selectedReferencePointers source.selection.group source.selection.indexDeclaration
    source.selection.key source.declarations environment inputs

private def selectedEntityPointers
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (environment : Env) (inputs : Option MessageReferenceInputs) :
    Except ReferenceProjectionError (List MessagePointer) :=
  match source with
  | .inl source => source.referencePointers environment inputs
  | .inr source => source.referencePointers environment inputs

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
def CheckedNumberEntityOperand.referencePointers (environment : Env)
    (operand : CheckedNumberEntityOperand model) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match operand with
  | .field source => (concreteFieldPointer source.declaration environment).map ([·])
  | .star source => (starFieldPointer source.source environment).map ([·])
  | .selected source => selectedEntityPointers source.source environment inputs
  | .starHaving _ => .error .filteredStarOperand
  | .group slot => slot.source.referencePointers environment

/-- Every authored slot contributes, in authored order, whether or not a runtime scan would reach it. A slot contributes its field or group expansion, plus any selected index and dynamic key; flattening preserves every dependency. -/
def CheckedNumberEntitySource.referencePointers
    (source : CheckedNumberEntitySource model) (environment : Env)
    (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$>
    source.operands.mapM (fun operand => operand.referencePointers environment inputs)

/-- Choose the pointer spelling for one filter reference, from the origin and the declaration's own
    scope depth against the operand's first star.

    Kind-independence is a property of *this function* — no branch reads the policy — and not a
    measured claim about the Kernel's pointer spelling for the newer leaves, which is unmeasured.
    The String and presence leaves reuse this spelling because they reuse the mechanism; if a
    measurement ever separates a carrier here, the divergence belongs in a per-kind branch rather
    than in a second pointer builder. -/
private def havingFieldPointerFor (source : CheckedStarFieldPath model)
    (environment : Env) (declaration : FlatFieldDecl) (origin : HavingOrigin) :
    Except ReferenceProjectionError MessagePointer :=
  match origin with
  | .outer => concreteFieldPointer declaration environment
  | .inner =>
      if declaration.repeatableScope.length ≤ source.path.firstStar then
        concreteFieldPointer declaration environment
      else
        reopenedFieldPointer declaration source.path.firstStar environment

private def havingNumberReferencePointer (source : CheckedStarFieldPath model)
    (environment : Env) (reference : HavingNumberRef) :
    Except ReferenceProjectionError MessagePointer := do
  let declaration ← match model.lookupUniqueId reference.field.id with
    | .ok declaration =>
        if declaration.toNumberField? == some reference.field then
          pure declaration
        else
          throw (.incoherentHavingField reference.field.id)
    | .error _ => throw (.incoherentHavingField reference.field.id)
  havingFieldPointerFor source environment declaration reference.origin

/-- The text counterpart. Only the coherence projection differs from the numeric reference, so
    the pointer choice itself stays in one place. -/
private def havingStringReferencePointer (source : CheckedStarFieldPath model)
    (environment : Env) (reference : HavingStringRef) :
    Except ReferenceProjectionError MessagePointer := do
  let declaration ← match model.lookupUniqueId reference.field.id with
    | .ok declaration =>
        if (declaration.textComparisonProfileFor? reference.operand).isSome then
          pure declaration
        else
          throw (.incoherentHavingField reference.field.id)
    | .error _ => throw (.incoherentHavingField reference.field.id)
  havingFieldPointerFor source environment declaration reference.origin

private def havingGroupReferencePointers (source : CheckedStarFieldPath model)
    (environment : Env) (origin : HavingOrigin) (reference : ResolvedGroupReference) :
    Except ReferenceProjectionError (List MessagePointer) :=
  let groupDepth := (model.repeatableScopeForGroupPath reference.path).length
  groupExpansionPointers model reference.path
    (match origin with | .outer => groupDepth | .inner => min groupDepth source.path.firstStar) environment

private def havingEntityListReferencePointers (source : CheckedStarFieldPath model)
    (environment : Env) (operands : List (HavingFieldListSlot HavingPresenceRef)) :
    Except ReferenceProjectionError (List MessagePointer) := do
  let slots ← operands.mapM fun slot => slot.references.mapM fun ref => do
    let declaration ← (model.lookupUniqueId ref.field).mapError fun _ => .incoherentHavingField ref.field
    match slot with
    | .direct _ => havingFieldPointerFor source environment declaration ref.origin
    | .extent extent _ =>
        let bound := if ref.origin == .outer then extent.boundCount
          else min source.path.firstStar extent.boundCount
        if declaration.repeatableScope.length ≤ bound then concreteFieldPointer declaration environment
        else reopenedFieldPointer declaration bound environment
  pure slots.flatten

private def correlatedHavingReferencePointers (source : CheckedStarFieldPath model)
    (environment : Env) : CorrelatedHaving →
    Except ReferenceProjectionError (List MessagePointer)
  | .leaf (.numeric comparison) => do
      let pointers ← (comparison.left.atoms ++ comparison.right.atoms).mapM fun
        | .aggregate _ slots => havingEntityListReferencePointers source environment (HavingNumberAggregate.presenceSlots slots)
        | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).mapM fun reference => do
            let declaration ← (model.lookupUniqueId reference.field.id).mapError (fun _ => .incoherentHavingField reference.field.id)
            if declaration.toTemporalField? != some reference.field then throw (.incoherentHavingField reference.field.id)
            havingFieldPointerFor source environment declaration reference.origin
        | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).mapM fun reference => do
            let declaration ← (model.lookupUniqueId reference.field.id).mapError (fun _ => .incoherentHavingField reference.field.id)
            if declaration.toTemporalField? != some reference.field then throw (.incoherentHavingField reference.field.id)
            havingFieldPointerFor source environment declaration reference.origin
        | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => pure []
        | .fieldValueAsNumber origin converted => do
            pure [← havingStringReferencePointer source environment { origin, operand := converted.operand }]
        | .field reference => do pure [← havingNumberReferencePointer source environment reference]
        | .stringLength origin field | .stringRange origin field _ _ => do
            pure [← havingStringReferencePointer source environment { origin, operand := .string field }]
        | .dateRangeBoundPart origin field _ part => do
            if !model.exposesDateRangeBoundPart field part then throw (.incoherentHavingField field.id)
            let declaration ← (model.lookupUniqueId field.id).mapError (fun _ => .incoherentHavingField field.id)
            pure [← havingFieldPointerFor source environment declaration origin]
        | .temporalExpressionPart _ expression => expression.references.mapM fun reference => do
            let declaration ← (model.lookupUniqueId reference.field.id).mapError (fun _ => .incoherentHavingField reference.field.id)
            if declaration.toTemporalField? != some reference.field then throw (.incoherentHavingField reference.field.id)
            havingFieldPointerFor source environment declaration reference.origin
        | .temporalPart origin field _ => do
            let declaration ← match model.lookupUniqueId field.id with
              | .ok declaration =>
                  if declaration.toTemporalField? == some field then pure declaration
                  else throw (.incoherentHavingField field.id)
              | .error _ => throw (.incoherentHavingField field.id)
            pure [← havingFieldPointerFor source environment declaration origin]
        | .repetition _ => pure []
      pure pointers.flatten
  | .leaf (.temporalExpression comparison) => comparison.references.mapM fun reference => do
      let declaration ← (model.lookupUniqueId reference.field.id).mapError (fun _ => .incoherentHavingField reference.field.id)
      if declaration.toTemporalField? != some reference.field then throw (.incoherentHavingField reference.field.id)
      havingFieldPointerFor source environment declaration reference.origin
  | .leaf (.simpleComparison left right comparison) => do
      let pointers ← [(left, comparison.inputFields.1), (right, comparison.inputFields.2)].mapM fun (origin, fields) =>
        fields.mapM fun field => do
          let declaration ← match model.lookupUniqueId field.id with
            | .ok declaration =>
                if field.matchesDecl declaration then pure declaration
                else throw (.incoherentHavingField field.id)
            | .error _ => throw (.incoherentHavingField field.id)
          havingFieldPointerFor source environment declaration origin
      pure pointers.flatten
  | .leaf (.compareStringLiteral _ reference _) => do
      pure [← havingStringReferencePointer source environment reference]
  | .leaf (.literalMembership origin _ membership) => do
      let declaration ← (model.lookupUniqueId membership.field.id).mapError fun _ => .incoherentHavingField membership.field.id
      pure [← havingFieldPointerFor source environment declaration origin]
  | .leaf (.dateValidity _ components) => components.references.mapM fun ref => do
      let declaration ← (model.lookupUniqueId ref.field).mapError fun _ => .incoherentHavingField ref.field
      havingFieldPointerFor source environment declaration ref.origin
  | .leaf (.uniqueness uniqueness) =>
      havingEntityListReferencePointers source environment uniqueness.presenceSlots
  | .leaf (.fieldMembership _ membership) =>
      havingEntityListReferencePointers source environment membership.presenceSlots
  | .leaf (.fieldFill _ references) =>
      havingEntityListReferencePointers source environment references
  | .leaf (.presence _ reference) => do
      -- Presence names any declared field, so its coherence check is existence alone.
      let declaration ← match model.lookupUniqueId reference.field with
        | .ok declaration => pure declaration
        | .error _ => throw (.incoherentHavingField reference.field)
      pure [← havingFieldPointerFor source environment declaration reference.origin]
  | .leaf (.typeValidity _ reference _) | .leaf (.stringPattern _ reference _) => do
      let declaration ← (model.lookupUniqueId reference.field).mapError fun _ =>
        .incoherentHavingField reference.field
      pure [← havingFieldPointerFor source environment declaration reference.origin]
  | .leaf (.groupPresence _ origin group) =>
      havingGroupReferencePointers source environment origin group.reference
  | .leaf (.groupFill _ first rest) => do
      let pointers ← (first :: rest).mapM fun
        | .group origin group => havingGroupReferencePointers source environment origin group.reference
        | .field reference => do
            let declaration ← (model.lookupUniqueId reference.field).mapError fun _ => .incoherentHavingField reference.field
            pure [← havingFieldPointerFor source environment declaration reference.origin]
      pure pointers.flatten
  | .and left right | .or left right => do
      pure ((← correlatedHavingReferencePointers source environment left) ++
        (← correlatedHavingReferencePointers source environment right))

/- Project the field dependencies of one checked token filter. Keeping this operation at the token source makes its carrier boundary type-enforced: Number and Boolean/Confirm sources cannot call it merely because they also contain a `CheckedStarHaving`. -/
private def tokenFilterReferencePointers
    (source : CheckedTokenStarSource model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  match source.filter with
  | none => pure []
  | some having =>
      correlatedHavingReferencePointers source.source environment having.condition

/-- A token star retains its selected source whether or not a filter adds dependencies. -/
def CheckedTokenStarSource.referencePointers (source : CheckedTokenStarSource model)
    (environment : Env) : Except ReferenceProjectionError (List MessagePointer) := do
  let selected ← starFieldPointer source.source environment
  pure (selected :: (← tokenFilterReferencePointers source environment))

/-- A projection-bearing token operand references its **declaring** field. The stored-versus-category choice is not part of a reference: `MessagePointer` has no projection slot, and the channel reports field instances.

    A measured filtered star adds the filter's field operands. Unmarked references at or below the reopened level keep the candidate wildcard, while `$` references use the captured firing environment and stay concrete. Repetition-only leaves contribute no field pointer. This is intentionally token-specific: the Number and Boolean/Confirm carriers remain refused until their own observations establish that the same assignment crosses those representation boundaries.

    A group slot contributes its whole recursive expansion through the shared projection, which is why this is list-valued where a field-denoting slot contributes exactly one pointer. -/
def CheckedTokenEntityOperand.referencePointers (environment : Env)
    (operand : CheckedTokenEntityOperand model) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match operand with
  | .selected source => selectedEntityPointers source.source environment inputs
  | .field source =>
      (concreteFieldPointer source.declaration environment).map ([·])
  | .star source => source.referencePointers environment
  | .group slot => slot.source.referencePointers environment

def CheckedTokenValueCountSource.referencePointers
    (checked : CheckedTokenValueCountSource model) (environment : Env)
    (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> checked.source.operands.mapM
    (fun operand => operand.referencePointers environment inputs)

/-- Temporal predicates and counts share the certified slot's references. Filter coordinates
remain refused until temporal-carrier observations establish their projection. -/
def CheckedTemporalUniquenessOperand.referencePointers (environment : Env)
    (operand : CheckedTemporalUniquenessOperand model) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match operand with
  | .selected source _ => selectedEntityPointers source.source environment inputs
  | .field source => (concreteFieldPointer source.declaration environment).map ([·])
  | .star path _ none => (starFieldPointer path environment).map ([·])
  | .star _ _ (some _) => .error .filteredStarOperand
  | .group source => source.source.referencePointers environment

def CheckedTemporalDistinctCountOperand.referencePointers (environment : Env)
    (operand : CheckedTemporalDistinctCountOperand model) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match operand with
  | .selected source _ => selectedEntityPointers source.source environment inputs
  | .slot source => source.referencePointers environment inputs
  | .group source => source.source.referencePointers environment

/-- The Boolean/Confirm companion has the same optional-filter shape, but it does not inherit the token carrier's measured coordinate account and therefore still refuses a filter. Its fixed canonical-token projection is invisible here for the same reason the token projection is. -/
def CheckedBooleanValueCountOperand.referencePointers (environment : Env)
    (operand : CheckedBooleanValueCountOperand model expected) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match operand with
  | .selected source => selectedEntityPointers source.source environment inputs
  | .field source =>
      (concreteFieldPointer source.declaration environment).map ([·])
  | .star source =>
      if source.filter.isSome then .error .filteredStarOperand
      else (starFieldPointer source.source environment).map ([·])
  | .group source => source.source.referencePointers environment

def CheckedBooleanValueCountSource.referencePointers
    (checked : CheckedBooleanValueCountSource model) (environment : Env)
    (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> checked.operands.mapM
    (fun operand => operand.referencePointers environment inputs)

/-- Each selected product operand keeps its own key and cache coordinate; an unkeyed product retains both shared-path stars. -/
def CheckedNumericProductAggregate.referencePointers
    (checked : CheckedNumericProductAggregate model) (environment : Env)
    (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := do
  match checked with
  | .selected source => pure ((← source.left.source.referencePointers environment inputs) ++
      (← source.right.source.referencePointers environment inputs))
  | .row checked => pure [← starFieldPointer checked.left.source environment,
      ← starFieldPointer checked.right.source environment]

/-- Field-fill lists retain operand shape: expanded descendants and starred fields need the
existing wildcard projection, not the direct-field sieve. Filter coordinates remain unclassified. -/
def CheckedFieldFillList.referencePointers (source : CheckedFieldFillList model)
    (environment : Env) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  if source.hasHaving then .error .filteredStarOperand else
  (·.flatten) <$> source.operands.mapM fun
    | .indexed source => source.referencePointers environment inputs
    | .keyed source => source.referencePointers environment inputs
    | .field declaration => (concreteFieldPointer declaration environment).map ([·])
    | .star star => (starFieldPointer star.source environment).map ([·])
    | .group group => group.source.referencePointers environment

private def resolvedFieldPointers {model : FlatModel} (field : FieldId) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) := do
  let declaration ← (model.lookupUniqueId field).mapError (fun _ => .unclassifiedOperand)
  pure [← concreteFieldPointer declaration environment]

private def temporalEntityPointers (source : CheckedTemporalExtremumOperands model)
    (environment : Env) (inputs : Option MessageReferenceInputs) :
    Except ReferenceProjectionError (List MessagePointer) :=
  if source.filters.any Option.isSome then .error .filteredStarOperand else
  (·.flatten) <$> source.shape.operands.mapM fun
    | .field declaration _ => (concreteFieldPointer declaration environment).map ([·])
    | .indexed source => source.referencePointers environment inputs
    | .keyed source => source.referencePointers environment inputs
    | .star source => (starFieldPointer source environment).map ([·])
    | .starHaving _ _ => throw .filteredStarOperand
    | .group reference => fixedGroupPointers model reference environment
    | .starredGroup source => starredGroupPointers model source.group.path source.path.firstStar environment
    | .starredGroupPresence source => starredGroupPointers model source.groupPath source.path.firstStar environment

private def temporalExpressionPointers (source : ScalarTemporalExpression model)
    (environment : Env) (inputs : Option MessageReferenceInputs) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> (source.dependenciesWith
    (fun field => [resolvedFieldPointers (model := model) field environment])
    (fun source => [temporalEntityPointers source environment inputs])
    (fun source => [source.referencePointers environment inputs])).mapM id

private def firstFilledComparisonPointers (operand : CheckedFirstFilledComparisonOperand model)
    (environment : Env) (inputs : Option MessageReferenceInputs) :
    Except ReferenceProjectionError (List MessagePointer) :=
  match operand with
  | .firstFilled source => source.source.referencePointers environment inputs
  | .field declaration _ => (concreteFieldPointer declaration environment).map ([·])
  | .boolean _ => pure []
  | .temporal source => temporalExpressionPointers source.core environment inputs

private def tokenComparisonPointers (operand : CheckedTokenComparisonOperand model)
    (environment : Env) (inputs : Option MessageReferenceInputs) :
    Except ReferenceProjectionError (List MessagePointer) :=
  match operand with
  | .literal _ => pure []
  | .field source => (concreteFieldPointer source.declaration environment).map ([·])
  | .firstFilled source _ => (·.flatten) <$> source.operands.mapM
      (fun operand => operand.referencePointers environment inputs)

/-- The complete ordered atom family. Every constructor is classified, so the only refusals reaching a caller from here are an unsupported sieve shape and a filtered star; there is no catch-all, and a new atom must state its own projection.

    Number entity lists share one operand projection; each token-family source keeps its own, because their operand types are distinct and their filter is an optional field rather than a constructor. The fixed group count traverses each retained group explicitly, preserving a concrete bound ancestor and wildcarding deeper reopened levels. Other ordinary scalar atoms are sieved on the same terms as the scalar leaf. Under addressed admission a delegated declaration may be repeatable but is bound by the rule's own iteration scope, so it projects concretely; nothing else in the delegated arm reopens a level. -/
def OrderedNumericValidationAtom.referencePointers (environment : Env)
    (atom : OrderedNumericValidationAtom model) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match atom with
  | .indexed source => source.toCheckedSemanticIndexSource.referencePointers environment inputs
  | .indexedString source => source.selection.referencePointers environment inputs
  | .temporalPart source =>
      temporalExpressionPointers source.source.core environment inputs
  | .ordinary (.filledGroupCount groups) =>
      (·.flatten) <$> groups.mapM fun reference =>
        fixedGroupPointers model reference environment
  | .ordinary source =>
      sievedFieldPointers model
        (fun declaration => source.referencesField model declaration.id)
        environment
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.referencePointers environment inputs
  | .tokenValueCount source => source.referencePointers environment inputs
  -- The token filter coordinates are measured for `NumberOfValueInFields` and do not cross to the
  -- distinct count unmeasured, so a filtered star is refused as the temporal arm refuses it.
  | .tokenDistinctCount source =>
      if source.hasHaving then .error .filteredStarOperand
      else (·.flatten) <$> source.operands.mapM (fun operand => operand.referencePointers environment inputs)
  | .temporalDistinctCount run =>
      (·.flatten) <$> run.source.operands.mapM (fun operand => operand.referencePointers environment inputs)
  | .booleanValueCount source => source.referencePointers environment inputs
  | .sumOfProducts source => source.referencePointers environment inputs
  | .filledFieldCount source => source.referencePointers environment inputs
  | .filledGroupCountMixed operands =>
      -- Routed through the same sieve as the scalar group count, so a star in the list cannot
      -- change which references a message may project.
      sievedFieldPointers model
        (fun declaration =>
          operands.any fun operand => operand.referencesField model declaration.id)
        environment

/-- Traverse one authored operand expression left to right. Literals reference nothing; a failing atom fails the whole projection. -/
private def expressionPointers (environment : Env) (inputs : Option MessageReferenceInputs) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Except ReferenceProjectionError (List MessagePointer)
  | .atom atom => atom.referencePointers environment inputs
  | .literal _ => pure []
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      expressionPointers environment inputs body
  | .binary _ left right | .power left right | .extremum _ left right => do
      pure ((← expressionPointers environment inputs left) ++
        (← expressionPointers environment inputs right))

/-- Both group operand forms expand to descendant fields and neither yields a group pointer; they differ only in coordinates, which is exactly the starred-versus-unstarred split. -/
def ResolvedGroupListOperand.referencePointers (environment : Env)
    (operand : ResolvedGroupListOperand model) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match operand with
  | .indexed source => source.referencePointers environment inputs
  | .keyed source => source.referencePointers environment inputs
  | .field declaration =>
      (concreteFieldPointer declaration environment).map ([·])
  | .starredGroup source =>
      starredGroupPointers model source.group.path source.path.firstStar environment
  | .starredGroupPresence source =>
      starredGroupPointers model source.groupPath source.path.firstStar environment
  | .group reference => fixedGroupPointers model reference environment

/-- Two membership strategies, chosen by whether a family can carry a starred operand.

    A family that can must be traversed explicitly, so that each operand reaches the coordinate rule that fits it. A family that cannot is sieved instead, on the terms [`sievedFieldPointers`](A12Kernel.sievedFieldPointers) states. Both sieved families qualify structurally: the flat fragment's leaves and the scalar numeric fragment's atoms each hold resolved single-field declarations, fixed Number field lists, or scalar fixed group references, and each family's `referencesField` covers every constructor with no catch-all. The addressed ordered fixed-group count above traverses its operands explicitly because its bound ancestor is concrete while a deeper repeatable descendant remains wildcarded.

    The scalar numeric predicate reports the whole counted subtree for a fixed group count. A missing binding refuses the whole projection rather than returning a partial reference set.

    A consequence is that the two strategies retain different orders — authored for traversal, declaration for sieving. That is admissible only because the result carries no ordering claim at all. -/
def ValidationConditionLeaf.referencePointers (environment : Env)
    (leaf : ValidationConditionLeaf model) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) := match leaf with
  | .orderedNumeric _ comparison => do
      pure ((← expressionPointers environment inputs comparison.left) ++
        (← expressionPointers environment inputs comparison.right))
  | .groupList _ operands =>
      (·.flatten) <$>
        operands.mapM (fun operand => operand.referencePointers environment inputs)
  | .keyedGroupPresence _ source => source.referencePointers environment inputs
  | .indexedFieldPresence _ source => source.referencePointers environment inputs
  | .repeatableFieldPresence _ declaration =>
      (concreteFieldPointer declaration environment).map ([·])
  | .stringExpression comparison => do
      let pointers ← (comparison.left.core.fields ++ comparison.right.core.fields).mapM fun
        | .inl field => resolvedFieldPointers (model := model) field environment
        | .inr source => source.referencePointers environment inputs
      pure pointers.flatten
  | .scalarTemporal comparison => do
      pure ((← temporalExpressionPointers comparison.left.core environment inputs) ++
        (← temporalExpressionPointers comparison.right.core environment inputs))
  | .firstFilledComparison comparison => do
      pure ((← firstFilledComparisonPointers comparison.left environment inputs) ++
        (← firstFilledComparisonPointers comparison.right environment inputs))
  | .tokenComparison comparison => do
      pure ((← tokenComparisonPointers comparison.left environment inputs) ++
        (← tokenComparisonPointers comparison.right environment inputs))
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
  | .iteratedDateRange condition =>
      condition.operandDeclarations.mapM fun declaration =>
        concreteFieldPointer declaration environment
  | .constructedDateValidity _ source =>
      temporalExpressionPointers source.scalarCore environment inputs
  | .indexedCustomFieldValidity source => source.source.selection.referencePointers environment inputs
  | .indexedStringPattern source => source.selection.referencePointers environment inputs
  | .customCondition _ => pure []
  | .customFieldValidity leaf =>
      (concreteFieldPointer leaf.operand.declaration environment).map ([·])
  | .stringPattern leaf =>
      match model.lookupUniqueId leaf.condition.field.id with
      | .ok declaration => (concreteFieldPointer declaration environment).map ([·])
      | .error _ => .error .unclassifiedLeaf
  | .valuesNotUnique source =>
      match source with
      | .number source => source.referencePointers environment inputs
      | .token source => (·.flatten) <$> source.source.operands.mapM
          (fun operand => operand.referencePointers environment inputs)
      | .temporal source => (·.flatten) <$> source.operands.mapM
          (fun operand => operand.referencePointers environment inputs)
  | .valueList source =>
      match source with
      | .number source => do
          pure ((← source.fields.referencePointers environment inputs) ++
            (← source.values.referencePointers environment inputs))
      | .token source =>
          (·.flatten) <$> (source.fields.operands ++ source.values.operands).mapM
            (fun operand => operand.referencePointers environment inputs)
      | .literals source =>
          (·.flatten) <$> source.fields.operands.mapM
            (fun operand => operand.referencePointers environment inputs)
  | .fieldFill _ source => source.referencePointers environment inputs
  | _ => .error .unclassifiedLeaf

private def treePointers (environment : Env) (inputs : Option MessageReferenceInputs) :
    ValidationCondition model →
      Except ReferenceProjectionError (List MessagePointer)
  | .leaf value => value.referencePointers environment inputs
  | .and left right | .or left right => do
      pure ((← treePointers environment inputs left) ++
        (← treePointers environment inputs right))

/-- The rule's structural reference set at one firing environment. Both connectives contribute every branch, because a reference exists by being authored rather than by being decisive.

    Duplicates are removed once. The retained order is authored traversal order and is **not** a kernel claim: the engine's own collection is a hash set whose iteration order is incidental, so a consumer may compare membership but never position. -/
def ValidationCondition.referencePointers (condition : ValidationCondition model)
    (environment : Env) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (treePointers environment inputs condition).map List.eraseDups

end A12Kernel
