import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.FilledFieldStarCount
import A12Kernel.Elaboration.StarNumberValueList
import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.StarStringValueList
import A12Kernel.Elaboration.StarEnumerationValueList
import A12Kernel.Elaboration.AtLeastOneDateRangeOverlap
import A12Kernel.Elaboration.TemporalExtremumOperands
import A12Kernel.Elaboration.TemporalDistinctCount
import A12Kernel.Elaboration.TemporalValuesNotUnique
import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TokenValuesNotUnique
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Elaboration.TokenEntityValueList
import A12Kernel.Elaboration.NumericAggregate.Products

/-! # A group operand's repetition walk

A group operand is walked like a field, its own repeatable level included: an unstarred repeatable
group read from outside it draws the walk's class on every carrier, ahead of each carrier's own
gates, while the rule that sits in a repeatable root passes the walk and meets the root classes.
The first rows are the peer's whole rules, `FieldFilled(<error field>) And <carrier>`, from the
second `-24c` table's two models ([inbound](../../docs/SOURCES.md#inbound-2026-09-24c-group-operand-walk)).
The later rows lock carriers at their own entry with the error field's group supplied: its position
places the class, containment from a rule group it lies outside
([inbound](../../docs/SOURCES.md#inbound-2026-09-24d-star-containment), `kf371`, and the
[validation checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement)).
-/

namespace A12Kernel.Conformance.GroupOperandRepetitionWalk

open A12Kernel

private def number : FieldPolicy := { kind := .number { scale := 0, signed := false } }
private def text : FieldPolicy := { kind := .string }

private def policyModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Policy"], name := "Holder", policy := text },
      { id := 2, groupPath := ["Policy", "Insured"], name := "Remark", policy := text },
      { id := 3, groupPath := ["Policy", "Insured"], name := "Age", policy := number },
      { id := 4, groupPath := ["Policy", "Broker"], name := "BrokerName", policy := text },
      { id := 5, groupPath := ["Policy", "Claims"], name := "ClaimRef", policy := text,
        repeatableScope := [10] },
      { id := 6, groupPath := ["Policy", "Claims"], name := "Remark", policy := text,
        repeatableScope := [10] },
      { id := 7, groupPath := ["Policy", "Claims"], name := "Amount", policy := number,
        repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Policy", "Claims"], repeatability := some 20 }]
    fieldRefByShortNameAllowed := true }

private def storefrontModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Storefront"], name := "OrderRef", policy := text },
      { id := 2, groupPath := ["Storefront", "Billing"], name := "Payer", policy := text },
      { id := 3, groupPath := ["Storefront", "Billing", "Card"], name := "Last4", policy := text },
      { id := 4, groupPath := ["Storefront", "Delivery"], name := "City", policy := text },
      { id := 5, groupPath := ["Storefront", "Lines"], name := "Sku", policy := text,
        repeatableScope := [10] },
      { id := 6, groupPath := ["Storefront", "Lines"], name := "Qty", policy := number,
        repeatableScope := [10] },
      { id := 7, groupPath := ["Warehouse"], name := "Bay", policy := text },
      { id := 8, groupPath := ["Batches"], name := "BatchCode", policy := text,
        repeatableScope := [20] }]
    repeatableGroups := [
      { level := 10, path := ["Storefront", "Lines"], repeatability := some 40 },
      { level := 20, path := ["Batches"], repeatability := some 6 }]
    fieldRefByShortNameAllowed := true }

private def rel (groups : List String) : SurfaceGroupReference :=
  .path { base := .relative 0, groups }

private def abs (groups : List String) : SurfaceGroupReference :=
  .path { base := .absolute, groups }

private def starAbs (groups : List (String × Bool)) : SurfaceStarGroupPath :=
  { base := .absolute, groups := groups.map fun (name, starred) => { name, starred } }

/-- A carrier's checked condition, or the Kernel class its own refusal projects. -/
private abbrev Carrier (model : FlatModel) :=
  Except (Option KernelStaticDiagnostic) (CheckedValidationCondition model)

private def list (model : FlatModel) (rowGroup : GroupPath) (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) (writtenGroup : GroupPath := rowGroup) :
    Carrier model :=
  (CheckedValidationCondition.fromGroupList model rowGroup operator operands writtenGroup).mapError
    (·.groupListDiagnostic?)

private def presence (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceGroupReference) (operator : GroupPresenceOperator) : Carrier model :=
  (CheckedValidationCondition.fromGroupPresence model rowGroup reference operator).mapError
    (·.groupListDiagnostic?)

private def count (model : FlatModel) (rowGroup : GroupPath)
    (operands : List SurfaceGroupReference) (writtenGroup : GroupPath := rowGroup) :
    Carrier model :=
  let surface : SurfaceNumericComparison :=
    { op := .ordinary .greater
      left := .atom (.filledGroupCount (operands.map .fixed))
      right := .literal { value := 0, authoredScale := 0 } }
  match elaborateNumericComparison model rowGroup surface writtenGroup with
  | .ok comparison =>
      (CheckedValidationCondition.fromNumeric comparison).mapError (·.groupListDiagnostic?)
  | .error error => .error error.groupCountDiagnostic?

/-- A group count whose list carries a star, through the mixed carrier. -/
private def mixedCount (model : FlatModel) (rowGroup : GroupPath)
    (operands : List SurfaceGroupCountOperand) : Carrier model :=
  match elaborateMixedFilledGroupCountComparison model rowGroup operands .greater 0 with
  | .ok comparison =>
      (CheckedValidationCondition.fromOrderedNumeric comparison).mapError (·.groupListDiagnostic?)
  | .error error => .error error.groupCountDiagnostic?

/-- The peer's whole rule, `FieldFilled(<error field>) And <carrier>`: `none` admitted, otherwise
    the Kernel class of the first refusal, `some none` when that refusal projects none. -/
private def ruleClass (model : FlatModel) (rowGroup : GroupPath) (errorPath : SurfaceFieldPath)
    (errorField : FieldId) (carrier : Carrier model) : Option (Option KernelStaticDiagnostic) :=
  match carrier with
  | .error diagnostic => some diagnostic
  | .ok condition =>
      let flatGuard := (elaborate model rowGroup (.fieldFilled errorPath)).toOption.bind
        fun guard => (CheckedValidationCondition.fromFlat guard).toOption
      -- A repeatable error field is read by the addressed presence carrier instead.
      let repeatableGuard := (CheckedValidationCondition.fromRepeatableFieldPresence model rowGroup
        .filled errorPath).toOption
      match flatGuard.orElse fun _ => repeatableGuard with
      | none => some none
      | some guard =>
          match guard.and condition with
          | .error _ => some none
          | .ok whole =>
              match assembleResolvedValidationRule model whole errorField "WALK" .error
                  { parts := [] } with
              | .ok _ => none
              | .error error => some error.diagnostic?

private def claims := rel ["Claims"]
private def insured := rel ["Insured"]
private def upClaims : SurfaceGroupReference := .path { base := .relative 1, groups := ["Claims"] }
private def noWildcard : Option (Option KernelStaticDiagnostic) := some (some .noWildcard)

/-- A rule at `/Policy` whose error field is `Holder`. -/
private def atPolicy (carrier : Carrier policyModel) :=
  ruleClass policyModel ["Policy"] { base := .relative 0, groups := [], field := "Holder" } 1 carrier

/-- A rule at `/Policy/Insured` whose error field is the Insured's own `Remark`. -/
private def atInsured (carrier : Carrier policyModel) :=
  ruleClass policyModel ["Policy", "Insured"]
    { base := .relative 0, groups := [], field := "Remark" } 2 carrier

/- An unstarred repeatable group read from outside it draws the missing-star class on every carrier
   ahead of each carrier's own gates: the group presence pair, the lone and paired quantifiers, and
   the count, whose arity gate a lone fixed operand would otherwise draw. The fixed twins pass. -/
example :
    [atPolicy (presence policyModel ["Policy"] claims .filled),
      atPolicy (presence policyModel ["Policy"] claims .notFilled),
      atPolicy (list policyModel ["Policy"] .atLeastOneGroupFilled [.group claims]),
      atPolicy (count policyModel ["Policy"] [claims])] = List.replicate 4 noWildcard ∧
    [GroupFillQuantifier.atLeastOneGroupFilled, .allGroupsFilled, .noGroupFilled,
      .notAllGroupsFilled, .groupsNotCollectivelyFilled].map (fun operator =>
        atPolicy (list policyModel ["Policy"] operator [.group claims, .group insured])) =
      List.replicate 5 noWildcard ∧
    atPolicy (presence policyModel ["Policy"] insured .filled) = none ∧
    atPolicy (list policyModel ["Policy"] .notAllGroupsFilled
      [.group insured, .group (rel ["Broker"])]) = none := by
  native_decide

/- A nested rule reaching the same group by an up-step draws the same class. -/
example :
    atInsured (presence policyModel ["Policy", "Insured"] upClaims .filled) = noWildcard ∧
    atInsured (list policyModel ["Policy", "Insured"] .atLeastOneGroupFilled [.group upClaims]) =
      noWildcard := by
  native_decide

private def batches := abs ["Batches"]
private def batchesStar := starAbs [("Batches", true)]

/-- A rule at `/Storefront` whose error field is `OrderRef`. -/
private def atStorefront (carrier : Carrier storefrontModel) :=
  ruleClass storefrontModel ["Storefront"]
    { base := .relative 0, groups := [], field := "OrderRef" } 1 carrier

/-- A rule at `/Batches` whose error field is `BatchCode`. -/
private def atBatches (carrier : Carrier storefrontModel) :=
  ruleClass storefrontModel ["Batches"]
    { base := .relative 0, groups := [], field := "BatchCode" } 8 carrier

/- A repeatable root is walked like any other group. Read from the other root it draws the
   missing-star class alone; from a rule inside it the walk passes and each carrier answers as it does
   for a fixed root; starred, the root class answers wherever the carrier refuses a root, ahead of the
   star gate. -/
example :
    [atStorefront (list storefrontModel ["Storefront"] .allGroupsFilled [.group batches]),
      atStorefront (list storefrontModel ["Storefront"] .atLeastOneGroupFilled [.group batches]),
      atStorefront (list storefrontModel ["Storefront"] .atLeastOneGroupFilled
        [.group batches, .group (rel ["Billing"])]),
      atStorefront (presence storefrontModel ["Storefront"] batches .filled),
      atStorefront (count storefrontModel ["Storefront"] [batches]),
      atStorefront (list storefrontModel ["Storefront"] .noGroupFilled [.group batches]),
      atStorefront (presence storefrontModel ["Storefront"] batches .notFilled),
      atStorefront (count storefrontModel ["Storefront"] [batches, rel ["Billing"]])] =
      List.replicate 8 noWildcard ∧
    [atBatches (list storefrontModel ["Batches"] .allGroupsFilled [.group batches]),
      atBatches (list storefrontModel ["Batches"] .atLeastOneGroupFilled [.group batches]),
      atBatches (list storefrontModel ["Batches"] .atLeastOneGroupFilled
        [.group batches, .group (abs ["Warehouse"])]),
      atBatches (presence storefrontModel ["Batches"] batches .filled),
      atBatches (count storefrontModel ["Batches"] [batches])] =
      [some (some .rootGroupReferenced), none, some (some .rootGroupWithOtherParameters), none,
        some (some .paramSizeInvalidGN)] ∧
    [atStorefront (list storefrontModel ["Storefront"] .allGroupsFilled [.starredGroup batchesStar]),
      atStorefront (list storefrontModel ["Storefront"] .atLeastOneGroupFilled
        [.starredGroup batchesStar]),
      atStorefront (list storefrontModel ["Storefront"] .atLeastOneGroupFilled
        [.starredGroup batchesStar, .group (rel ["Billing"])])] =
      [some (some .rootGroupReferenced), none, some (some .rootGroupWithOtherParameters)] := by
  native_decide

/- Beside another operand a starred root still draws its root class ahead of the star gate, in
   either position, and the mixed count answers the class it gives any root beside a disjoint
   operand. -/
example :
    [atStorefront (list storefrontModel ["Storefront"] .allGroupsFilled
        [.starredGroup batchesStar, .group (rel ["Billing"])]),
      atStorefront (list storefrontModel ["Storefront"] .allGroupsFilled
        [.group (abs ["Warehouse"]), .starredGroup batchesStar]),
      atStorefront (mixedCount storefrontModel ["Storefront"]
        [.starred batchesStar, .fixed (rel ["Billing"])])] =
      [some (some .rootGroupReferenced), some (some .rootGroupReferenced),
        some (some .rootGroupWithOtherParameters)] := by
  native_decide

/- The entity-list carriers read the same operand through the shared resolver, so their own gates
   never answer first: `Sum` over the pair and over the sole group, the filled-field group source
   behind the field-fill quantifiers, and `CurrentRepetition`, whose group is its only operand. -/
example :
    (match elaborateNumberEntitySource policyModel ["Policy"]
        { first := .group claims, rest := [.group insured] } with
      | .ok _ => none
      | .error error => NumberEntityElabError.aggregateDiagnostic? .sum error) = some .noWildcard ∧
    (match elaborateNumberEntitySource policyModel ["Policy"] { first := .group claims, rest := [] } with
      | .ok _ => none
      | .error error => NumberEntityElabError.aggregateDiagnostic? .sum error) = some .noWildcard ∧
    (match elaborateFilledFieldCountFixedGroupValidationSource policyModel ["Policy"]
        { group := { base := .relative 0, groups := ["Claims"] } } with
      | .error (.shape error) => error.diagnostic?
      | _ => none) = some .noWildcard ∧
    (match elaborateNumericComparison policyModel ["Policy"]
        { op := .ordinary .greater
          left := .atom (.currentRepetition { base := .relative 0, groups := ["Claims"] })
          right := .literal { value := 1, authoredScale := 0 } } with
      | .ok _ => none
      | .error error => error.repetitionScopeDiagnostic?) = some .noWildcard := by
  native_decide

/-! ## The scalar field slot

`FieldFilled` and `FieldNotFilled` naming a group meet the walk first, then a root's own class, then
the kind gate. The starred spellings, the `.*` suffix and the two-operand arity rows have no flat
surface here ([inbound](../../docs/SOURCES.md#inbound-2026-09-24c-field-slot)). -/

private def fieldSlot (model : FlatModel) (rowGroup : GroupPath) (filled : Bool)
    (path : SurfaceFieldPath) (writtenGroup : GroupPath := rowGroup) : Carrier model :=
  match elaborate model rowGroup (if filled then .fieldFilled path else .fieldNotFilled path)
      writtenGroup with
  | .ok flat => (CheckedValidationCondition.fromFlat flat).mapError (·.groupListDiagnostic?)
  | .error (.resolve error) => .error error.diagnostic?
  | .error _ => .error none

private def named (base : PathBase) (groups : List String) (field : String) : SurfaceFieldPath :=
  { base, groups, field }

/- The unbound repeatable group and a field inside it draw the missing star, from the rule's own
   group and by an up-step, and so does the other root; a fixed group meets the kind gate; and the
   repeatable root a rule sits in passes the walk and draws its root class, as a fixed root does.
   The Kernel's fixed-root row spells the root `..` from `/Policy/Insured`, which no flat path
   spells, so this lock reads the same group by its absolute name. -/
example :
    [atPolicy (fieldSlot policyModel ["Policy"] true (named (.relative 0) [] "Claims")),
      atPolicy (fieldSlot policyModel ["Policy"] false (named (.relative 0) [] "Claims")),
      atPolicy (fieldSlot policyModel ["Policy"] true (named (.relative 0) ["Claims"] "Amount")),
      atInsured (fieldSlot policyModel ["Policy", "Insured"] true (named (.relative 1) [] "Claims")),
      atStorefront (fieldSlot storefrontModel ["Storefront"] true (named .absolute [] "Batches")),
      atStorefront (fieldSlot storefrontModel ["Storefront"] true
        (named .absolute ["Batches"] "BatchCode"))] =
      List.replicate 6 noWildcard ∧
    atPolicy (fieldSlot policyModel ["Policy"] true (named (.relative 0) [] "Insured")) =
      some (some .noGroupsAllowed) ∧
    atBatches (fieldSlot storefrontModel ["Batches"] true (named .absolute [] "Batches")) =
      some (some .rootGroupReferenced) ∧
    atInsured (fieldSlot policyModel ["Policy", "Insured"] true (named .absolute [] "Policy")) =
      some (some .rootGroupReferenced) := by
  native_decide

/- Only a miss on the reference is displaced by the group it names: an invalid rule group still
   answers first, and so does an absolute path's turning point, a spelling defect. -/
example :
    (match elaborate policyModel [] (.fieldFilled (named .absolute ["Policy"] "Claims")) with
      | .error (.resolve (.invalidRuleGroup [])) => true
      | _ => false) = true ∧
    (match elaborate policyModel ["Policy"] (.fieldFilled
        { base := .absolute, turningPoint := some "Policy", groups := ["Policy"], field := "Claims" })
      with
      | .error (.resolve (.invalidReference _)) => true
      | _ => false) = true := by
  native_decide

/-! ## Where the error field lies

The walk's class depends on the error field. Outside the rule group the containment class answers
first, whatever the level's index declaration. Inside it an index-keyed level beside the error
field's group draws the index class and a level below that group the missing star
([inbound](../../docs/SOURCES.md#inbound-2026-09-24d-star-containment)). -/

/-- The policy model with `ClaimRef` declared the index field of `Claims` and nothing else moved. -/
private def keyedPolicyModel : FlatModel :=
  { policyModel with
    repeatableGroups := [
      { level := 10, path := ["Policy", "Claims"], repeatability := some 20, indexField := some 5 }] }

private def noIndex : Option (Option KernelStaticDiagnostic) := some (some .errorFieldNoIndex)
private def containment : Option (Option KernelStaticDiagnostic) := some (some .fieldNotInRuleGroup)

private def atPolicyWith (model : FlatModel) (errorPath : SurfaceFieldPath) (errorField : FieldId)
    (carrier : Carrier model) :=
  ruleClass model ["Policy"] errorPath errorField carrier

private def remark : SurfaceFieldPath := { base := .relative 0, groups := ["Insured"], field := "Remark" }
private def holder : SurfaceFieldPath := { base := .relative 0, groups := [], field := "Holder" }

/-- The eleven of the peer's twenty-two group carriers the rule surface represents, naming `Claims`
    unstarred from a rule at `/Policy` whose error field lies in `writtenGroup`. The presence pair
    meets the walk at rule assembly; the others while their condition elaborates, told the error
    field's group. -/
private def claimsCarriers (model : FlatModel) (writtenGroup : GroupPath) : List (Carrier model) :=
  [fieldSlot model ["Policy"] true (named (.relative 0) [] "Claims") writtenGroup,
    fieldSlot model ["Policy"] false (named (.relative 0) [] "Claims") writtenGroup,
    presence model ["Policy"] claims .filled, presence model ["Policy"] claims .notFilled,
    list model ["Policy"] .atLeastOneGroupFilled [.group claims] writtenGroup] ++
  [GroupFillQuantifier.atLeastOneGroupFilled, .allGroupsFilled, .noGroupFilled,
      .notAllGroupsFilled, .groupsNotCollectivelyFilled].map (fun operator =>
    list model ["Policy"] operator [.group claims, .group insured] writtenGroup) ++
  [count model ["Policy"] [claims] writtenGroup]

/- With the error field `Insured/Remark`, `Claims` lies beside its group and the index declaration
   alone moves the class on every carrier; with the root `Holder`, `Claims` lies below its group and
   stays the missing star under the key
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-24d-star-containment)). -/
example :
    (claimsCarriers keyedPolicyModel ["Policy", "Insured"]).map
        (atPolicyWith keyedPolicyModel remark 2) = List.replicate 11 noIndex ∧
    (claimsCarriers policyModel ["Policy", "Insured"]).map
        (atPolicyWith policyModel remark 2) = List.replicate 11 noWildcard ∧
    (claimsCarriers keyedPolicyModel ["Policy"]).map
        (atPolicyWith keyedPolicyModel holder 1) = List.replicate 11 noWildcard := by
  native_decide

/- A rule in `Insured` reporting on its own `Remark` reaches the keyed `Claims` by an up-step, beside
   its group, and draws the index class on four carriers where the unkeyed twin draws the missing
   star. -/
example :
    let insuredCarriers (model : FlatModel) : List (Carrier model) :=
      [fieldSlot model ["Policy", "Insured"] true (named (.relative 1) [] "Claims"),
        presence model ["Policy", "Insured"] upClaims .filled,
        list model ["Policy", "Insured"] .atLeastOneGroupFilled [.group upClaims],
        count model ["Policy", "Insured"] [upClaims]]
    (insuredCarriers keyedPolicyModel).map (ruleClass keyedPolicyModel ["Policy", "Insured"]
        { base := .relative 0, groups := [], field := "Remark" } 2) = List.replicate 4 noIndex ∧
    (insuredCarriers policyModel).map (atInsured) = List.replicate 4 noWildcard := by
  native_decide

/- The operand-level sources place the same refusal, told the error field's group: `Sum` over the
   pair, whose checked source `FirstFilledValue` and `NumberOfValueInFields` share, the filled-field
   group source behind the field-fill quantifiers and `NumberOfFilledFields`, and `CurrentRepetition`.
   These are source reads rather than whole rules, so no carrier's own gate is exercised. -/
example :
    let sources (model : FlatModel) (writtenGroup : GroupPath) : List (Option KernelStaticDiagnostic) :=
      [match elaborateNumberEntitySource model ["Policy"]
            { first := .group claims, rest := [.group insured] } (writtenGroup := writtenGroup) with
          | .ok _ => none
          | .error error => NumberEntityElabError.aggregateDiagnostic? .sum error,
        match elaborateFilledFieldCountFixedGroupValidationSource model ["Policy"]
            { group := { base := .relative 0, groups := ["Claims"] } } writtenGroup with
          | .error (.shape error) => error.diagnostic?
          | _ => none,
        match elaborateNumericComparison model ["Policy"]
            { op := .ordinary .greater
              left := .atom (.currentRepetition { base := .relative 0, groups := ["Claims"] })
              right := .literal { value := 1, authoredScale := 0 } } writtenGroup with
          | .ok _ => none
          | .error error => error.repetitionScopeDiagnostic?]
    sources keyedPolicyModel ["Policy", "Insured"] = List.replicate 3 (some .errorFieldNoIndex) ∧
      sources policyModel ["Policy", "Insured"] = List.replicate 3 (some .noWildcard) ∧
      sources keyedPolicyModel ["Policy"] = List.replicate 3 (some .noWildcard) := by
  native_decide

/-- A keyed `Batches` holding a fixed `Seal` beside a keyed `Boxes`. -/
private def keyedChainModel (batchesKeyed : Bool) : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Batches"], name := "Code", policy := text, repeatableScope := [1] },
      { id := 2, groupPath := ["Batches", "Seal"], name := "Mark", policy := text,
        repeatableScope := [1] },
      { id := 3, groupPath := ["Batches", "Boxes"], name := "Tag", policy := text,
        repeatableScope := [1, 2] }]
    repeatableGroups := [
      { level := 1, path := ["Batches"], indexField := if batchesKeyed then some 1 else none },
      { level := 2, path := ["Batches", "Boxes"], indexField := some 3 }] }

/- `Boxes` lies beside `Seal`. With nothing keyed on the written field's chain it draws the index
   class; with `Batches` keyed too, a keyed group both chains share, no row measures the gate, so the
   walk claims no class ([`kf371`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371)). -/
example :
    ((keyedChainModel false).unboundOperandLevel ["Batches"] ["Batches", "Seal"] 2).diagnostic? =
        some .errorFieldNoIndex ∧
      ((keyedChainModel true).unboundOperandLevel ["Batches"] ["Batches", "Seal"] 2).diagnostic? =
        none := by
  native_decide

/- A rule in the repeatable `Claims` reporting on the root `Holder`, outside its group, reads
   `Amount` per row and draws containment, index-keyed or not
   ([`kf212`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf212)). -/
example :
    [policyModel, keyedPolicyModel].map (fun model =>
      ruleClass model ["Policy", "Claims"] { base := .relative 1, groups := [], field := "Holder" } 1
        ((CheckedValidationCondition.fromRepeatableFieldPresence model ["Policy", "Claims"] .filled
          { base := .relative 0, groups := [], field := "Amount" }).mapError
            (·.groupListDiagnostic?))) =
      [containment, containment] := by
  native_decide

/-- The peer's fulfilment sheet: a fixed `Summary` and `Ledger`, and a repeatable `Shipments`
    holding a repeatable `Parcels` with a fixed `Seal`. -/
private def fulfilmentModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Fulfilment", "Summary"], name := "Result", policy := number },
      { id := 2, groupPath := ["Fulfilment", "Ledger"], name := "Total", policy := number },
      { id := 3, groupPath := ["Fulfilment", "Shipments", "Parcels"], name := "Weight",
        policy := number, repeatableScope := [1, 2] },
      { id := 4, groupPath := ["Fulfilment", "Shipments", "Parcels", "Seal"], name := "SealCode",
        policy := text, repeatableScope := [1, 2] },
      { id := 5, groupPath := ["Fulfilment", "Shipments", "Parcels"], name := "Code",
        policy := text, repeatableScope := [1, 2] }]
    repeatableGroups := [
      { level := 1, path := ["Fulfilment", "Shipments"] },
      { level := 2, path := ["Fulfilment", "Shipments", "Parcels"] }] }

/- Below the first star the error field places the refusal too. With it in `Summary`, outside the
   rule group, `Parcels` left unstarred under `Shipments*` draws containment from `Ledger` and from
   `Shipments`, on `Sum`'s source and on the group count; with the rule in `Summary` it stays the
   missing star ([inbound](../../docs/SOURCES.md#inbound-2026-09-24d-star-containment)). -/
example :
    let summary := ["Fulfilment", "Summary"]
    let belowStar : List SurfaceStarGroupSegment :=
      [{ name := "Fulfilment" }, { name := "Shipments", starred := true }, { name := "Parcels" }]
    let sum (rowGroup : GroupPath) : Option KernelStaticDiagnostic :=
      match elaborateNumberEntitySource fulfilmentModel rowGroup
          { first := .star { base := .absolute, groups := belowStar, field := "Weight" }, rest := [] }
          (writtenGroup := summary) with
      | .ok _ => none
      | .error error => NumberEntityElabError.aggregateDiagnostic? .sum error
    let count (rowGroup : GroupPath) : Option KernelStaticDiagnostic :=
      match elaborateMixedFilledGroupCountComparison fulfilmentModel rowGroup
          [.starred { base := .absolute, groups := belowStar ++ [{ name := "Seal" }] }] .greater 0
          (writtenGroup := summary) with
      | .ok _ => none
      | .error error => error.groupCountDiagnostic?
    [sum ["Fulfilment", "Ledger"], sum ["Fulfilment", "Shipments"], sum summary,
      count ["Fulfilment", "Ledger"], count ["Fulfilment", "Shipments"], count summary] =
    [some .fieldNotInRuleGroup, some .fieldNotInRuleGroup, some .noWildcard,
      some .fieldNotInRuleGroup, some .fieldNotInRuleGroup, some .noWildcard] := by
  native_decide

/-- The fulfilment path with `Shipments` starred and `Parcels` starred only when `starLast`. -/
private def fulfilmentPath (starLast : Bool) : List SurfaceStarGroupSegment :=
  [{ name := "Fulfilment" }, { name := "Shipments", starred := true },
    { name := "Parcels", starred := starLast }]

private def fulfilmentField (starLast : Bool) (name : String) : SurfaceStarFieldPath :=
  { base := .absolute, groups := fulfilmentPath starLast, field := name }

private def fulfilmentSeal (starLast : Bool) : SurfaceStarGroupPath :=
  { base := .absolute, groups := fulfilmentPath starLast ++ [{ name := "Seal" }] }

/-- Each measured carrier at its own entry, `none` when it is admitted. -/
private def fulfilmentCarriers (starLast : Bool) (rowGroup : GroupPath) :
    List (Option (Option KernelStaticDiagnostic)) :=
  let summary := ["Fulfilment", "Summary"]
  [match elaborateNumberValuesNotUniqueSource fulfilmentModel rowGroup
      { first := .star (fulfilmentField starLast "Weight"), rest := [] } (writtenGroup := summary) with
    | .error error => some error.diagnostic?
    | .ok _ => none,
   match elaborateStarStringValueListSource fulfilmentModel rowGroup
      { quantifier := .atLeastOne, fields := fulfilmentField starLast "Code", values := ["x"] }
      (writtenGroup := summary) with
    | .error (.path error) => some error.diagnostic?
    | .error _ => some none
    | .ok _ => none,
   match elaborateFilledFieldStarSource fulfilmentModel rowGroup (fulfilmentField starLast "Weight")
      none (writtenGroup := summary) with
    | .error (.path error) => some error.diagnostic?
    | .error _ => some none
    | .ok _ => none,
   match elaborateFilledFieldCountStarredGroupValidationSource fulfilmentModel rowGroup
      { group := fulfilmentSeal starLast } summary with
    | .error (.shape (.starredGroup error)) => some error.diagnostic?
    | .error _ => some none
    | .ok _ => none,
   match list fulfilmentModel rowGroup .atLeastOneGroupFilled [.starredGroup (fulfilmentSeal starLast)]
      summary with
    | .error diagnostic => some diagnostic
    | .ok _ => none]

/- Every measured carrier takes the error field's group at its own entry: `FieldValuesNotUnique`,
   the String value list, the filled-field star behind `NumberOfFilledFields` and the field-fill
   quantifiers, the filled-field starred group source and a starred group-list operand each draw
   containment from `Ledger` and `Shipments` and the missing star from `Summary`, and each is
   admitted with both levels starred
   ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement)).
   The starred group source's rows, `NumberOfFilledFields` and `AtLeastOneFieldFilled` over `Seal`,
   are the later grid's ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement-kinds)). -/
example :
    [fulfilmentCarriers false ["Fulfilment", "Ledger"], fulfilmentCarriers false ["Fulfilment", "Shipments"],
      fulfilmentCarriers false ["Fulfilment", "Summary"], fulfilmentCarriers true ["Fulfilment", "Ledger"],
      fulfilmentCarriers true ["Fulfilment", "Shipments"]] =
    [List.replicate 5 containment, List.replicate 5 containment, List.replicate 5 noWildcard,
      List.replicate 5 none, List.replicate 5 none] := by
  native_decide

/- `AllGroupsFilled`, `NotAllGroupsFilled` and `GroupsNotCollectivelyFilled` forbid a star, yet below
   it they draw the placed class alone, ahead of the bar the fully starred operand meets
   ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement), [inbound](../../docs/SOURCES.md#inbound-2026-09-25-bare-group-placement)). -/
example :
    [GroupFillQuantifier.allGroupsFilled, .notAllGroupsFilled, .groupsNotCollectivelyFilled].flatMap (fun operator =>
      [false, true].map fun starLast =>
        match list fulfilmentModel ["Fulfilment", "Ledger"] operator
            [.starredGroup (fulfilmentSeal starLast)] ["Fulfilment", "Summary"] with
        | .error diagnostic => some diagnostic
        | .ok _ => none) =
    (List.replicate 3 [containment, some (some .noWildcardsGAllowed)]).flatten := by
  native_decide

/- The Number value list read against a field, `Weight In /Fulfilment/Ledger/Total`, is placed the
   same way and admitted with both levels starred ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement-kinds)). -/
example :
    [(false, ["Fulfilment", "Ledger"]), (false, ["Fulfilment", "Shipments"]),
      (false, ["Fulfilment", "Summary"]), (true, ["Fulfilment", "Ledger"]),
      (true, ["Fulfilment", "Shipments"])].map (fun (starLast, rowGroup) =>
      match elaborateStarNumberValueListSource fulfilmentModel rowGroup
          { quantifier := .atLeastOne, fields := .star (fulfilmentField starLast "Weight"),
            firstValue := { base := .absolute, groups := ["Fulfilment", "Ledger"], field := "Total" },
            restValues := [] } (writtenGroup := ["Fulfilment", "Summary"]) with
      | .error (.fields (.path error)) => some error.diagnostic?
      | .error _ => some none
      | .ok _ => none) =
    [containment, containment, noWildcard, none, none] := by
  native_decide

/-- The fulfilment sheet with the other kinds the later grids read: in `Ledger` a Date, a DateRange
    with a year and one without, a String and an Enumeration; in `Parcels` a second Number, a Date,
    both DateRanges, a Boolean and an Enumeration. -/
private def fulfilmentKindsModel : FlatModel :=
  let ledger := ["Fulfilment", "Ledger"]
  let parcels := ["Fulfilment", "Shipments", "Parcels"]
  let date : FieldPolicy := { kind := .temporal .date TemporalComponents.fullDate }
  let dateFormat := some { format := "yyyy-MM-dd" }
  let range (format : String) : Option DateRangeDeclarationPolicy :=
    some { format, separator := "-" }
  { fulfilmentModel with
    fields := fulfilmentModel.fields ++ [
      { id := 6, groupPath := ledger, name := "LedgerDate", policy := date,
        temporalTargetPolicy := dateFormat },
      { id := 7, groupPath := ledger, name := "Window", policy := { kind := .dateRange },
        dateRangePolicy := range "dd.MM.yyyy" },
      { id := 8, groupPath := ledger, name := "LCode", policy := text },
      { id := 9, groupPath := ledger, name := "LSeason", policy := { kind := .dateRange },
        dateRangePolicy := range "dd.MM" },
      { id := 10, groupPath := parcels, name := "Qty", policy := number, repeatableScope := [1, 2] },
      { id := 11, groupPath := parcels, name := "ShipDate", policy := date,
        temporalTargetPolicy := dateFormat, repeatableScope := [1, 2] },
      { id := 12, groupPath := parcels, name := "Cover", policy := { kind := .dateRange },
        dateRangePolicy := range "dd.MM.yyyy", repeatableScope := [1, 2] },
      { id := 13, groupPath := parcels, name := "Flag", policy := { kind := .boolean },
        repeatableScope := [1, 2] },
      { id := 14, groupPath := parcels, name := "Tier", policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"] }, repeatableScope := [1, 2] },
      { id := 15, groupPath := parcels, name := "Season", policy := { kind := .dateRange },
        dateRangePolicy := range "dd.MM", repeatableScope := [1, 2] },
      { id := 16, groupPath := ledger, name := "LTier", policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"] } }] }

/-- A carrier's verdict: `none` when it is admitted, otherwise the class its refusal projects. -/
private def verdict (result : Except ε α) (class? : ε → Option KernelStaticDiagnostic) :
    Option (Option KernelStaticDiagnostic) :=
  match result with
  | .ok _ => none
  | .error error => some (class? error)

/-- Each further grid carrier at its own entry, beside the error field in `Summary`. A DateRange
    carrier reads at the rule group's own scope, the one its rule assembly supplies. `MinValue`
    shares `MaxValue`'s entry, so one row stands for both. -/
private def fulfilmentKindCarriers (starLast : Bool) (rowGroup : GroupPath) :
    List (Option (Option KernelStaticDiagnostic)) :=
  let summary := ["Fulfilment", "Summary"]
  let model := fulfilmentKindsModel
  let scope := model.repeatableScopeForGroupPath rowGroup
  let starred (name : String) := fulfilmentField starLast name
  let list (name : String) : SurfaceFieldEntitySource := { first := .star (starred name), rest := [] }
  let ledger (name : String) : SurfaceFieldPath :=
    { base := .absolute, groups := ["Fulfilment", "Ledger"], field := name }
  let shape := FieldEntityShapeElabError.diagnostic?
  [verdict (elaborateFirstFilledTokenSource model rowGroup (list "Code") summary)
      fun | .source (.shape error) => shape error | _ => none,
   verdict (elaborateTokenDistinctCountSource model rowGroup (list "Code") summary)
      fun | .source (.shape error) => shape error | _ => none,
   verdict (elaborateTokenValuesNotUniqueSource model rowGroup (list "Code") summary)
      fun | .source (.shape error) => shape error | _ => none,
   verdict (TemporalExtremumOperands.elaborate model rowGroup (list "ShipDate") summary)
      fun | .shape error => shape error | _ => none,
   verdict (elaborateTemporalDistinctCountSource model rowGroup (list "ShipDate") summary)
      fun | .slot (.shape error) => shape error | _ => none,
   verdict (elaborateTemporalValuesNotUniqueSource model rowGroup (list "ShipDate") summary)
      fun | .shape error => shape error | _ => none,
   verdict (elaborateAtLeastOneDateRangeOverlapsSourceIn model rowGroup scope
        { scalar := .field (ledger "Window"), list := list "Cover" } summary)
      fun | .shape error => shape error | _ => none,
   verdict (elaborateDateRangesOverlapSourceIn model rowGroup scope
        { first := .field (ledger "Window"), rest := [.star (starred "Cover")] } summary)
      fun | .shape error => shape error | _ => none,
   verdict (elaborateBooleanValueCountSource model rowGroup true (list "Flag")
        (writtenGroup := summary))
      fun | .shape error => shape error | _ => none,
   verdict (elaborateStarEnumerationValueListSource model rowGroup
        { quantifier := .atLeastOne, fields := starred "Tier", values := ["A"] } summary)
      fun | .path error => error.diagnostic? | _ => none,
   verdict (elaborateNumericProductAggregate model rowGroup
        { left := starred "Weight", right := starred "Qty" } summary)
      NumericProductAggregateElabError.diagnostic?,
   verdict (elaborateTokenValueCountSource model rowGroup "x"
        { first := .star (starred "Code") .stored, rest := [] } (writtenGroup := summary))
      fun | .source (.shape error) => shape error | _ => none,
   verdict (elaborateTokenEntityStringLiteralValueListSource model rowGroup
        { quantifier := .atLeastOne, values := ["x"],
          fields := { first := .star (starred "Code"), rest := [.field (ledger "LCode")] } } summary)
      fun | .shape error => shape error | _ => none,
   verdict (elaborateTokenEntityValueListSource model rowGroup
        { quantifier := .atLeastOne, fields := list "Code",
          values := { first := .field (ledger "LCode"), rest := [] } } summary)
      fun | .fields (.shape error) => shape error | _ => none,
   verdict (elaborateYearlessDateRangesOverlapSourceIn model rowGroup scope
        { first := .field (ledger "LSeason"), rest := [.star (starred "Season")] } summary)
      fun | .source (.shape error) => shape error | _ => none,
   verdict (elaborateYearlessAtLeastOneDateRangeOverlapsSourceIn model rowGroup scope
        { scalar := .field (ledger "LSeason"), list := list "Season" } summary)
      fun | .source (.shape error) => shape error | _ => none]

/- The placement reaches the token, temporal, DateRange and yearless DateRange entity lists, the
   Boolean and String value counts, the Enumeration and both String value lists, and
   `SumOfProducts`: each draws containment from `Ledger` and `Shipments` and the missing star from
   `Summary`, and each is admitted with both levels starred, except `SumOfProducts`, whose own bar
   refuses a star above the lowest level ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement-kinds)). -/
example :
    [fulfilmentKindCarriers false ["Fulfilment", "Ledger"],
      fulfilmentKindCarriers false ["Fulfilment", "Shipments"],
      fulfilmentKindCarriers false ["Fulfilment", "Summary"],
      fulfilmentKindCarriers true ["Fulfilment", "Ledger"],
      fulfilmentKindCarriers true ["Fulfilment", "Shipments"]] =
    let starBar := [some (some KernelStaticDiagnostic.wildcardOnlyAtLowestLevelAllowed)]
    [List.replicate 16 containment, List.replicate 16 containment, List.replicate 16 noWildcard,
      List.replicate 10 none ++ starBar ++ List.replicate 5 none,
      List.replicate 10 none ++ starBar ++ List.replicate 5 none] := by
  native_decide

/-- The star on a value list's values side, and a filtered star, each at its own entry beside the
    error field in `Summary`. The filter compares two fields of the candidate row, the only
    comparison the correlated filter surface holds. -/
private def fulfilmentValuesAndFilterCarriers (starLast : Bool) (rowGroup : GroupPath) :
    List (Option (Option KernelStaticDiagnostic)) :=
  let summary := ["Fulfilment", "Summary"]
  let model := fulfilmentKindsModel
  let starred (name : String) := fulfilmentField starLast name
  let ledger (name : String) : SurfaceFieldPath :=
    { base := .absolute, groups := ["Fulfilment", "Ledger"], field := name }
  let parcels := ["Fulfilment", "Shipments", "Parcels"]
  let parcel (name : String) : SurfaceHavingNumberRef :=
    { origin := .inner, field := { base := .absolute, groups := parcels, field := name } }
  let having : SurfaceCorrelatedHaving := .compareNumbers .equal (parcel "Qty") (parcel "Weight")
  [verdict (elaborateStringValueListStarValuesSource model rowGroup
        { quantifier := .atLeastOne, field := ledger "LCode", values := starred "Code" } summary)
      fun | .path error => error.diagnostic? | _ => none,
   verdict (elaborateEnumerationValueListStarValuesSource model rowGroup
        { quantifier := .atLeastOne, field := .direct (ledger "LTier"), values := starred "Tier" }
        summary)
      fun | .path error => error.diagnostic? | _ => none,
   verdict (elaborateNumberEntitySource model rowGroup
        { first := .starHaving (starred "Weight") having, rest := [] } (writtenGroup := summary))
      (NumberEntityElabError.aggregateDiagnostic? .sum),
   verdict (elaborateFilledFieldStarSource model rowGroup (starred "Weight") (some having)
        (writtenGroup := summary))
      fun | .path error => error.diagnostic? | _ => none]

/- It reaches the star on the values side of the String and Enumeration value lists, and a
   filtered star under `Sum` and `NumberOfFilledFields`: the same placed classes, and each admitted
   with both levels starred ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement-kinds)). -/
example :
    [fulfilmentValuesAndFilterCarriers false ["Fulfilment", "Ledger"],
      fulfilmentValuesAndFilterCarriers false ["Fulfilment", "Shipments"],
      fulfilmentValuesAndFilterCarriers false ["Fulfilment", "Summary"],
      fulfilmentValuesAndFilterCarriers true ["Fulfilment", "Ledger"],
      fulfilmentValuesAndFilterCarriers true ["Fulfilment", "Shipments"]] =
    [List.replicate 4 containment, List.replicate 4 containment, List.replicate 4 noWildcard,
      List.replicate 4 none, List.replicate 4 none] := by
  native_decide

/-! ## A level beside the error field's group, keyed on both chains

The walk asks each level it crosses on its own declaration. A level beside the error field's group
that declares an index field, with the error field's path declaring one too, meets the index gates:
another name draws `MVK_ERROR_FIELD_INVALID_INDEX`, the same name under another type
`MVK_ERROR_FIELD_INVALID_INDEX_TYPE`, a second index field on the operand's own parallel chain
`MVK_MULTIPLE_INDEX_FIELDS`, and the same name and type is a legal parallel iteration the Kernel
admits. Each row is the peer's rule `FieldFilled(<error field>) And [<operand>] > 0`, declared in the
error field's group unless it says otherwise ([`kf371`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371),
[`kf255`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf255)). -/

/-- The peer's route model: a keyed `Shipments` holding an unkeyed `Parcels`, a keyed `Invoices`
    under the same key name, an unkeyed `Returns` carrying the key field undeclared, a keyed
    `Credits` under the same name holding a keyed `Lines`, a keyed `Refunds` under another name, and
    a keyed `Adjustments` under the same name as a Number. -/
private def routeModel : FlatModel :=
  let row (id : FieldId) (groups : List String) (name : String) (policy : FieldPolicy)
      (scope : List RepeatableLevel) : FlatFieldDecl :=
    { id, groupPath := "Fulfilment" :: groups, name, policy, repeatableScope := scope }
  { fields := [
      row 1 [] "OrderTotal" number [],
      row 2 ["Shipments"] "ShipmentKey" text [1], row 3 ["Shipments"] "ShipmentCost" number [1],
      row 4 ["Shipments", "Parcels"] "ParcelWeight" number [1, 2],
      row 5 ["Invoices"] "ShipmentKey" text [3], row 6 ["Invoices"] "InvoiceAmount" number [3],
      row 7 ["Returns"] "ShipmentKey" text [4], row 8 ["Returns"] "ReturnAmount" number [4],
      row 9 ["Credits"] "ShipmentKey" text [5], row 10 ["Credits", "Lines"] "LineKey" text [5, 6],
      row 11 ["Credits", "Lines"] "LineAmount" number [5, 6],
      row 12 ["Refunds"] "RefundKey" text [7], row 13 ["Refunds"] "RefundAmount" number [7],
      row 14 ["Adjustments"] "ShipmentKey" number [8],
      row 15 ["Adjustments"] "AdjustmentAmount" number [8]]
    repeatableGroups := [
      { level := 1, path := ["Fulfilment", "Shipments"], indexField := some 2 },
      { level := 2, path := ["Fulfilment", "Shipments", "Parcels"] },
      { level := 3, path := ["Fulfilment", "Invoices"], indexField := some 5 },
      { level := 4, path := ["Fulfilment", "Returns"] },
      { level := 5, path := ["Fulfilment", "Credits"], indexField := some 9 },
      { level := 6, path := ["Fulfilment", "Credits", "Lines"], indexField := some 10 },
      { level := 7, path := ["Fulfilment", "Refunds"], indexField := some 12 },
      { level := 8, path := ["Fulfilment", "Adjustments"], indexField := some 14 }] }

private def routeComparison (groups : List String) (field : String) : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.field { base := .absolute, groups := "Fulfilment" :: groups, field })
    right := .literal { value := 0, authoredScale := 0 } }

/-- `[<operand>] > 0` read from `rowGroup` beside an error field in `writtenGroup`: `none` when it
    resolves, otherwise the class of its refusal. The flat comparison refuses a field outside its row
    group as a fragment boundary, so the table's form-level control has no row here. -/
private def routeRead (rowGroup : List String) (groups : List String) (field : String)
    (writtenGroup : List String := rowGroup) : Option (Option KernelStaticDiagnostic) :=
  match elaborateNumericComparison routeModel ("Fulfilment" :: rowGroup) (routeComparison groups field)
      ("Fulfilment" :: writtenGroup) with
  | .ok _ => none
  | .error (.resolve error) => some error.diagnostic?
  | .error _ => some none

/-- The index gate the refused level met, for a read the walk refuses. -/
private def routeGate (rowGroup : List String) (groups : List String) (field : String) :
    Option ParallelIndexGate :=
  match elaborateNumericComparison routeModel ("Fulfilment" :: rowGroup) (routeComparison groups field) with
  | .error (.resolve (.unboundOperandLevel _ unbound)) => some unbound.parallelGate
  | _ => none

/- The route table's rows. Below the admitted keyed parallel level an unkeyed level is refused on
   its own declaration and a keyed one meets the multiple-index gate, while into the unkeyed `Returns`
   the outer level already draws the index class; the sibling cells follow, then a level below the
   error field's own and the sibling read from a rule at the root. -/
example :
    [routeRead ["Invoices"] ["Shipments", "Parcels"] "ParcelWeight",
      routeRead ["Invoices"] ["Credits", "Lines"] "LineAmount",
      routeRead ["Returns"] ["Credits", "Lines"] "LineAmount",
      routeRead ["Returns"] ["Shipments"] "ShipmentCost",
      routeRead ["Invoices"] ["Refunds"] "RefundAmount",
      routeRead ["Invoices"] ["Returns"] "ReturnAmount",
      routeRead ["Invoices"] ["Adjustments"] "AdjustmentAmount",
      routeRead ["Shipments"] ["Shipments", "Parcels"] "ParcelWeight",
      routeRead [] ["Refunds"] "RefundAmount" ["Invoices"]] =
    [noWildcard, some (some .multipleIndexFields), noIndex, noIndex,
      some (some .errorFieldInvalidIndex), noWildcard, some (some .errorFieldInvalidIndexType),
      noWildcard, some (some .errorFieldInvalidIndex)] := by
  native_decide

/- The keyed parallel level alone is a legal parallel iteration: the Kernel admits it, and this
   route, which joins no parallel iteration, refuses it claiming no class. Its sibling under another
   name meets the name gate, a separate outcome from the same walk. -/
example :
    [routeGate ["Invoices"] ["Shipments"] "ShipmentCost", routeGate ["Invoices"] ["Refunds"] "RefundAmount"] =
      [some .legal, some .differentName] ∧
    routeRead ["Invoices"] ["Shipments"] "ShipmentCost" = some none := by
  native_decide

/-- The policy model with a repeatable `Recoveries` whose `Note` is the error field, declaring `key`
    as its index field when given. -/
private def recoveriesModel (key : Option (String × FieldPolicy)) : FlatModel :=
  let row (id : FieldId) (name : String) (policy : FieldPolicy) : FlatFieldDecl :=
    { id, groupPath := ["Policy", "Recoveries"], name, policy, repeatableScope := [30] }
  let recoveries : RepeatableGroupDecl :=
    { level := 30, path := ["Policy", "Recoveries"], indexField := key.map fun _ => 20 }
  { keyedPolicyModel with
    fields := keyedPolicyModel.fields ++ (key.map fun (name, policy) => row 20 name policy).toList ++
      [row 21 "Note" text]
    repeatableGroups := keyedPolicyModel.repeatableGroups ++ [recoveries] }

/- A keyed group operand beside a keyed error field meets the whole index table on every carrier
   that takes the error field's group at its entry, the presence pair aside: no index field, another
   name, and the same name under another type draw their three classes. The same name and type is a
   legal parallel iteration, where the field slot meets its kind gate and the other carriers, which
   join no parallel iteration, refuse claiming no class
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-25-parallel-index-gates)). -/
example :
    let entryCarriers (key : Option (String × FieldPolicy)) :=
      let carriers := claimsCarriers (recoveriesModel key) ["Policy", "Recoveries"]
      (carriers.take 2 ++ carriers.drop 4).map fun | .ok _ => none | .error class? => some class?
    [entryCarriers none, entryCarriers (some ("RecoveryRef", text)),
      entryCarriers (some ("ClaimRef", number)), entryCarriers (some ("ClaimRef", text))] =
    [List.replicate 9 noIndex, List.replicate 9 (some (some .errorFieldInvalidIndex)),
      List.replicate 9 (some (some .errorFieldInvalidIndexType)),
      List.replicate 2 (some (some .noGroupsAllowed)) ++ List.replicate 7 (some none)] := by
  native_decide

/- A bare repeatable group operand places its refusal as a field read does: `Shipments` draws
   containment from `Ledger` and from `Shipments` and the missing star from `Summary`, in the field
   slot, the sole and paired quantifiers and the group count
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-25-bare-group-placement)). -/
example :
    let summary := ["Fulfilment", "Summary"]
    let shipments : SurfaceGroupReference := .path { base := .absolute, groups := ["Fulfilment", "Shipments"] }
    let summaryRef : SurfaceGroupReference := .path { base := .absolute, groups := summary }
    [["Fulfilment", "Ledger"], ["Fulfilment", "Shipments"], summary].map (fun rowGroup =>
      [fieldSlot fulfilmentModel rowGroup true (named .absolute ["Fulfilment"] "Shipments") summary,
        list fulfilmentModel rowGroup .atLeastOneGroupFilled [.group shipments] summary,
        list fulfilmentModel rowGroup .allGroupsFilled [.group shipments, .group summaryRef] summary,
        count fulfilmentModel rowGroup [shipments] summary].map
          fun | .ok _ => none | .error class? => some class?) =
    [List.replicate 4 containment, List.replicate 4 containment, List.replicate 4 noWildcard] := by
  native_decide

/- A list's own gates wait for its operands to be read: the star bar under `AllGroupsFilled` with
   `Shipments` unstarred above the star, the root gate, and the exact and nested duplicate each give
   way to the read's placed class ([inbound](../../docs/SOURCES.md#inbound-2026-09-25-operator-gates-wait)). -/
example :
    let summary := ["Fulfilment", "Summary"]
    let sealPath (shipments parcels : Bool) : SurfaceStarGroupPath :=
      { base := .absolute, groups := [{ name := "Fulfilment" }, { name := "Shipments", starred := shipments },
          { name := "Parcels", starred := parcels }, { name := "Seal" }] }
    let sealRef : SurfaceGroupReference := .path { base := .absolute, groups := sealPath false false |>.groups.map (·.name) }
    let root : SurfaceGroupReference := .path { base := .absolute, groups := ["Fulfilment"] }
    [["Fulfilment", "Ledger"], summary].map (fun rowGroup =>
      [list fulfilmentModel rowGroup .allGroupsFilled [.starredGroup (sealPath false true)] summary,
        list fulfilmentModel rowGroup .allGroupsFilled [.starredGroup (sealPath true false), .group root] summary,
        list fulfilmentModel rowGroup .allGroupsFilled [.group sealRef, .group sealRef] summary,
        list fulfilmentModel rowGroup .atLeastOneGroupFilled [.group root, .group sealRef] summary].map
          fun | .ok _ => none | .error class? => some class?) =
    [List.replicate 4 containment, List.replicate 4 noWildcard] := by
  native_decide

end A12Kernel.Conformance.GroupOperandRepetitionWalk
