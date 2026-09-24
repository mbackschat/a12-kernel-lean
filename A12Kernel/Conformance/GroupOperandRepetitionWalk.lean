import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.FilledFieldGroupCount

/-! # A group operand's repetition walk

A group operand is walked like a field, its own repeatable level included: an unstarred repeatable
group read from outside it draws the missing-star class on every carrier, ahead of each carrier's
own gates, while the rule that sits in a repeatable root passes the walk and meets the root classes.
Every row is the peer's whole rule, `FieldFilled(<error field>) And <carrier>`, from the second
`-24c` table's two models ([inbound](../../docs/SOURCES.md#inbound-2026-09-24c-group-operand-walk)).
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
   answers first. -/
example :
    (match elaborate policyModel [] (.fieldFilled (named .absolute ["Policy"] "Claims")) with
      | .error (.resolve (.invalidRuleGroup [])) => true
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

end A12Kernel.Conformance.GroupOperandRepetitionWalk
