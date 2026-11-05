import A12Kernel.Elaboration.ValidationCondition.Evaluation
import A12Kernel.Semantics.MessageIndex
import A12Kernel.Elaboration.CheckedMessageCache

/-! # A12Kernel.Elaboration.ValidationCondition.ReferenceCoordinates — the pointer coordinate rule

This module owns the coordinate rule every structural message reference shares and the filter-read projection built on it. [`Reference`](Reference.lean) assembles the per-operand and per-leaf projections from these pieces.

For ordinary and starred operands, coordinate assignment follows one rule. A repeatable level fixed by the rule's iteration scope is concrete at the firing instance; a level the star reopened, and every axis below it, is wildcard. Both facts are Kernel-locked upstream at a12-dmkits `bbbbf48e`; [`SOURCES.md`](../../../docs/SOURCES.md) owns that provenance.
-/

namespace A12Kernel

/-- Why one structural reference projection has no answer. No case means an empty reference set: the leaf or operand family is outside the current fragment, a filtered star's operand coordinates are unpinned, or the firing environment does not bind a level the reference needs.

    `incoherentHavingField` is fail-closed protection for the one route whose checked representation retains a resolved Number field rather than its declaration. [`CheckedStarHaving.wellFormed`](A12Kernel.CheckedStarHaving.wellFormed) makes it unreachable for an elaborated filter. -/
inductive ReferenceProjectionError where
  | unclassifiedLeaf
  | unclassifiedOperand
  | filteredStarOperand
  | incoherentHavingField (field : FieldId)
  | unreopenedReference (field : FieldId)
  | missingIndexContext
  | hostOrder (error : MessageCacheOrderError)
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

/-- Whether the firing environment binds every repeatable level of the declaration's own scope. -/
def Env.bindsScope (environment : Env) (declaration : FlatFieldDecl) : Bool :=
  declaration.repeatableScope.all fun level => (environment.bindingAt level).toOption.isSome

/-- One sieved reference. A declaration the firing environment binds is its exact instance; a subtree
field below a repeatable level the rule does not bind keeps the bound prefix and wildcards that level
and every deeper one, as the retained Kernel messages of a fixed group count over such a subtree report
it (generated self-validation replay, docs/sources/model-structure-and-declaration-probes.md#src-generated-self-validation-k14). -/
def sievedFieldPointer (declaration : FlatFieldDecl) (environment : Env) :
    Except ReferenceProjectionError MessagePointer :=
  if environment.bindsScope declaration then concreteFieldPointer declaration environment
  else reopenedFieldPointer declaration
    (declaration.repeatableScope.takeWhile fun level => (environment.bindingAt level).toOption.isSome).length
    environment

/-- Membership by *sieving* the model's declarations through a family's own reference predicate, rather than by traversing its operands.

    This is sound exactly when the family cannot carry a starred operand and its predicate is exhaustive over the family's constructors with no catch-all: the sieve then inherits precisely that predicate's coverage and can neither miss a reference it reports nor invent one. The same shortcut would be wrong for a starred family, because the predicate reports the starred field while its coordinates are not concrete.

    Each pointer comes from [`sievedFieldPointer`](A12Kernel.sievedFieldPointer): exact wherever the firing environment binds the declaration, which `sievedFieldPointers_exact_of_bound` proves, and wildcarded below a level it does not bind. -/
def sievedFieldPointers (model : FlatModel)
    (references : FlatFieldDecl → Bool) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (model.fields.filter references).mapM (sievedFieldPointer · environment)

/-- An extent member is exact when its whole scope is bound and reopened below its bound levels otherwise. -/
def extentMemberPointer (declaration : FlatFieldDecl) (bound : Nat) (environment : Env) :
    Except ReferenceProjectionError MessagePointer :=
  if declaration.repeatableScope.length ≤ bound then concreteFieldPointer declaration environment
  else reopenedFieldPointer declaration bound environment

/-- A group operand contributes the fields of its **whole subtree**, recursively and never a pointer to the group. The extent itself is [`FlatModel.groupSubtreeFields`](A12Kernel.FlatModel.groupSubtreeFields), shared with the entity list's group slot so that one site cannot disagree with another about how far a group reaches.

    **One depth rule serves both repetition shapes**, which is why they share this function rather than each owning a projection: repeatable levels **above** `boundCount` stay concrete at the firing row, and every repeatable level at or below it is **wildcarded**. The starred form supplies its star's own `firstStar`; the unstarred form supplies its authored path's own repeatable scope, and `fixedGroupPointers` below states why that is the whole scope rather than the levels strictly above it. Measured at a12-dmkits `bffe9cca`: an unstarred `/Shipment/Carrier` reaches `/Shipment[1]/Carrier[1]/Handoffs[0]/Site`, wildcarding the nested repeatable level while the message's own anchor stays concrete throughout. The two channels are different addresses of the same firing.

    A member with **nothing** reopened below `boundCount` is the ordinary case here rather than the disagreement [`reopenedFieldPointer`](A12Kernel.reopenedFieldPointer) refuses — a group's direct non-repeatable field has no level to wildcard, and the same measured set carries it as `/Shipment[1]/Carrier[1]/Name` with no coordinates at all. It is projected concretely, which is the same answer the depth rule gives with an empty wildcard suffix.

    Declaration order is retained for determinism only, on the same terms as the whole projection. -/
def groupExpansionPointers (model : FlatModel) (groupPath : GroupPath)
    (boundCount : Nat) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (model.groupSubtreeFields groupPath).mapM (extentMemberPointer · boundCount environment)

/-- An unstarred group operand's expansion. The subtree-reaching half is measured on a nonrepeatable model, where the deeper descendant group's field joins the set and refutes direct-child expansion; the coordinate half is measured at `bffe9cca`. The relation is identical in the presence, entity-list, and count positions.

    The depth is the **whole** repeatable scope of the authored path, its own level included, rather than the levels strictly above it. On every measured row those agree, because the wildcard gate keeps an unstarred entity-list operand's own group nonrepeatable and the wildcarding therefore begins strictly inside the subtree. They diverge only for a *repeatable* operand, which the presence carrier accepts unstarred only where the rule iterates it: the Kernel refuses the form elsewhere and reports the iterated row concrete with deeper levels wildcarded (message-references-2026-10-14, rule `c02`), which the whole scope yields because that level is bound. An unbound level still fails closed instead of inventing a coordinate. -/
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

/-- Choose the pointer spelling for one filter reference, from the origin and the declaration's own
    scope depth against the operand's first star.

    Kind-independence is a property of *this function* — no branch reads the policy — and not a
    measured claim about the Kernel's pointer spelling for the newer leaves, which is unmeasured.
    The String and presence leaves reuse this spelling because they reuse the mechanism; if a
    measurement ever separates a carrier here, the divergence belongs in a per-kind branch rather
    than in a second pointer builder. -/
private def havingFieldPointerFor (firstStar : Nat)
    (environment : Env) (declaration : FlatFieldDecl) (origin : HavingOrigin) :
    Except ReferenceProjectionError MessagePointer :=
  match origin with
  | .outer => concreteFieldPointer declaration environment
  | .inner => extentMemberPointer declaration firstStar environment

private def havingNumberReferencePointer (model : FlatModel) (firstStar : Nat)
    (environment : Env) (reference : HavingNumberRef) :
    Except ReferenceProjectionError MessagePointer := do
  let declaration ← match model.lookupUniqueId reference.field.id with
    | .ok declaration =>
        if declaration.toNumberField? == some reference.field then
          pure declaration
        else
          throw (.incoherentHavingField reference.field.id)
    | .error _ => throw (.incoherentHavingField reference.field.id)
  havingFieldPointerFor firstStar environment declaration reference.origin

/-- The text counterpart. Only the coherence projection differs from the numeric reference, so
    the pointer choice itself stays in one place. -/
private def havingStringReferencePointer (model : FlatModel) (firstStar : Nat)
    (environment : Env) (reference : HavingStringRef) :
    Except ReferenceProjectionError MessagePointer := do
  let declaration ← match model.lookupUniqueId reference.field.id with
    | .ok declaration =>
        if declaration.resolvesTextOperand reference.operand then
          pure declaration
        else
          throw (.incoherentHavingField reference.field.id)
    | .error _ => throw (.incoherentHavingField reference.field.id)
  havingFieldPointerFor firstStar environment declaration reference.origin

private def havingGroupReferencePointers (model : FlatModel) (firstStar : Nat)
    (environment : Env) (origin : HavingOrigin) (reference : ResolvedGroupReference) :
    Except ReferenceProjectionError (List MessagePointer) :=
  let groupDepth := (model.repeatableScopeForGroupPath reference.path).length
  groupExpansionPointers model reference.path
    (match origin with | .outer => groupDepth | .inner => min groupDepth firstStar) environment

private def havingEntityListReferencePointers (model : FlatModel) (firstStar : Nat)
    (environment : Env) (operands : List (HavingFieldListSlot HavingPresenceRef)) :
    Except ReferenceProjectionError (List MessagePointer) := do
  let slots ← operands.mapM fun slot => slot.references.mapM fun ref => do
    let declaration ← (model.lookupUniqueId ref.field).mapError fun _ => .incoherentHavingField ref.field
    match slot with
    | .direct _ => havingFieldPointerFor firstStar environment declaration ref.origin
    | .extent extent _ =>
        extentMemberPointer declaration (if ref.origin == .outer then extent.boundCount
          else min firstStar extent.boundCount) environment
  pure slots.flatten

/-- The reads of one filter-body Number atom, which a filter comparison and the term of a `SumOfTerms` share. `firstStar` is the first reopened level of the iterating star, and decides which levels a candidate read leaves concrete. -/
def HavingNumericAtom.referencePointersAt (model : FlatModel) (firstStar : Nat) (environment : Env) :
    HavingNumericAtom → Except ReferenceProjectionError (List MessagePointer)
  | .groupCount operands => havingEntityListReferencePointers model firstStar environment (operands.map (·.presenceSlot))
  | .product product => havingEntityListReferencePointers model firstStar environment product.presenceSlots
  | .collectionCount count => havingEntityListReferencePointers model firstStar environment count.presenceSlots
  | .firstFilled slots | .aggregate _ slots => havingEntityListReferencePointers model firstStar environment (HavingNumberAggregate.presenceSlots slots)
  | .dateDifference _ _ left right | .dayDifference _ left right => (left.fields ++ right.fields).mapM fun reference => do
      let declaration ← (model.lookupUniqueId reference.field.id).mapError (fun _ => .incoherentHavingField reference.field.id)
      if declaration.toTemporalField? != some reference.field then throw (.incoherentHavingField reference.field.id)
      havingFieldPointerFor firstStar environment declaration reference.origin
  | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).mapM fun reference => do
      let declaration ← (model.lookupUniqueId reference.field.id).mapError (fun _ => .incoherentHavingField reference.field.id)
      if declaration.toTemporalField? != some reference.field then throw (.incoherentHavingField reference.field.id)
      havingFieldPointerFor firstStar environment declaration reference.origin
  | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => pure []
  | .fieldValueAsNumber origin converted => do
      pure [← havingStringReferencePointer model firstStar environment { origin, operand := converted.operand }]
  | .field reference => do pure [← havingNumberReferencePointer model firstStar environment reference]
  | .stringLength origin field | .stringRange origin field _ _ => do
      pure [← havingStringReferencePointer model firstStar environment { origin, operand := .string field }]
  | .dateRangeBoundPart origin field _ part => do
      if !model.exposesDateRangeBoundPart field part then throw (.incoherentHavingField field.id)
      let declaration ← (model.lookupUniqueId field.id).mapError (fun _ => .incoherentHavingField field.id)
      pure [← havingFieldPointerFor firstStar environment declaration origin]
  | .temporalDifference _ left right => do
      for reference in left.references ++ right.references do
        if !reference.matchesModel model then throw (.incoherentHavingField reference.fieldId)
      havingEntityListReferencePointers model firstStar environment (left.presenceSlots ++ right.presenceSlots)
  | .temporalExpressionPart _ expression => do
      for reference in expression.references do
        if !reference.matchesModel model then throw (.incoherentHavingField reference.fieldId)
      havingEntityListReferencePointers model firstStar environment expression.presenceSlots
  | .temporalPart origin field _ _ => do
      let declaration ← match model.lookupUniqueId field.id with
        | .ok declaration =>
            if declaration.toTemporalField? == some field then pure declaration
            else throw (.incoherentHavingField field.id)
        | .error _ => throw (.incoherentHavingField field.id)
      pure [← havingFieldPointerFor firstStar environment declaration origin]
  | .repetition _ => pure []

/-- Every authored filter read retains its candidate or captured coordinate, independently of
    whether its filtered operand contributes omission responsibility (KF522). `firstStar` is the first level the iterating star reopens. -/
def CorrelatedHaving.referencePointersAt (model : FlatModel) (firstStar : Nat)
    (environment : Env) : CorrelatedHaving →
    Except ReferenceProjectionError (List MessagePointer)
  | .leaf (.numeric comparison) => do
      let pointers ← (comparison.left.atoms ++ comparison.right.atoms).mapM
        (HavingNumericAtom.referencePointersAt model firstStar environment)
      pure pointers.flatten
  | .leaf (.stringExpression comparison) =>
      havingEntityListReferencePointers model firstStar environment comparison.presenceSlots
  | .leaf (.selectedComparison comparison) =>
      havingEntityListReferencePointers model firstStar environment comparison.presenceSlots
  | .leaf (.temporalExpression comparison) => do
      for reference in comparison.references do
        if !reference.matchesModel model then throw (.incoherentHavingField reference.fieldId)
      havingEntityListReferencePointers model firstStar environment comparison.presenceSlots
  | .leaf (.simpleComparison left right comparison) => do
      let pointers ← [(left, comparison.inputFields.1), (right, comparison.inputFields.2)].mapM fun (origin, fields) =>
        fields.mapM fun field => do
          let declaration ← match model.lookupUniqueId field.id with
            | .ok declaration =>
                if field.matchesDecl declaration then pure declaration
                else throw (.incoherentHavingField field.id)
            | .error _ => throw (.incoherentHavingField field.id)
          havingFieldPointerFor firstStar environment declaration origin
      pure pointers.flatten
  | .leaf (.compareStringLiteral _ reference _) => do
      pure [← havingStringReferencePointer model firstStar environment reference]
  | .leaf (.literalMembership origin _ membership) => do
      let declaration ← (model.lookupUniqueId membership.field.id).mapError fun _ => .incoherentHavingField membership.field.id
      pure [← havingFieldPointerFor firstStar environment declaration origin]
  | .leaf (.dateValidity _ components) => components.references.mapM fun ref => do
      let declaration ← (model.lookupUniqueId ref.field).mapError fun _ => .incoherentHavingField ref.field
      havingFieldPointerFor firstStar environment declaration ref.origin
  | .leaf (.dateRange range) =>
      havingEntityListReferencePointers model firstStar environment range.presenceSlots
  | .leaf (.uniqueness uniqueness) =>
      havingEntityListReferencePointers model firstStar environment uniqueness.presenceSlots
  | .leaf (.fieldMembership _ membership) =>
      havingEntityListReferencePointers model firstStar environment membership.presenceSlots
  | .leaf (.fieldFill _ references) =>
      havingEntityListReferencePointers model firstStar environment references
  | .leaf (.presence _ reference) => do
      -- Presence names any declared field, so its coherence check is existence alone.
      let declaration ← match model.lookupUniqueId reference.field with
        | .ok declaration => pure declaration
        | .error _ => throw (.incoherentHavingField reference.field)
      pure [← havingFieldPointerFor firstStar environment declaration reference.origin]
  | .leaf (.typeValidity _ reference _) | .leaf (.stringPattern _ reference _) => do
      let declaration ← (model.lookupUniqueId reference.field).mapError fun _ =>
        .incoherentHavingField reference.field
      pure [← havingFieldPointerFor firstStar environment declaration reference.origin]
  | .leaf (.groupPresence _ origin group) =>
      havingGroupReferencePointers model firstStar environment origin group.reference
  | .leaf (.groupFill _ first rest) =>
      havingEntityListReferencePointers model firstStar environment ((first :: rest).map (·.presenceSlot))
  | .and left right | .or left right => do
      pure ((← CorrelatedHaving.referencePointersAt model firstStar environment left) ++
        (← CorrelatedHaving.referencePointersAt model firstStar environment right))

/-- A starred field's filter reads, at that star's own first reopened level. -/
def CheckedStarFieldPath.filterReferencePointers (source : CheckedStarFieldPath model)
    (environment : Env) : CorrelatedHaving →
    Except ReferenceProjectionError (List MessagePointer) :=
  CorrelatedHaving.referencePointersAt model source.path.firstStar environment

/-- A term sum's term reads. Each sits at the iteration's any-row index, a field of a non-repeatable group at its own index, and a field of the entity's row that no term reads is named nowhere, so the group is not expanded the way a starred group operand is
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms), a12-dmkits `SumOfTermsRuntimeLawsTest` at `1124b523f`, kernel 31.1.1). -/
def CheckedSumOfTerms.termReferencePointers (checked : CheckedSumOfTerms model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> checked.term.atoms.mapM
    (HavingNumericAtom.referencePointersAt model checked.source.path.firstStar environment)

/-- The reads of a term sum's entity filter, at the entity's own first reopened level; a `$`-marked read keeps its captured coordinate. -/
def CheckedSumOfTerms.filterReferencePointers (checked : CheckedSumOfTerms model) (environment : Env) :
    Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> checked.filter.toList.mapM fun having =>
    CorrelatedHaving.referencePointersAt model checked.source.path.firstStar environment having.condition

end A12Kernel
