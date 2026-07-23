import A12Kernel.Elaboration.ValidationCondition

/-! # Shared resolved validation-condition locks -/

namespace A12Kernel.Conformance.ValidationCondition

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def u : FlatNumberField := { id := 1, info := unsigned }
private def v : FlatNumberField := { id := 2, info := unsigned }
private def w : FlatNumberField := { id := 3, info := unsigned }
private def x : FlatNumberField := { id := 4, info := unsigned }
private def d : FlatNumberField := { id := 5, info := unsigned }
private def p : FlatNumberField := { id := 6, info := unsigned }

private def model : FlatModel :=
  { fields := [
      { id := u.id, groupPath := ["Order"], name := "U",
        policy := { kind := .number unsigned } },
      { id := v.id, groupPath := ["Order"], name := "V",
        policy := { kind := .number unsigned } },
      { id := w.id, groupPath := ["Other"], name := "W",
        policy := { kind := .number unsigned } },
      { id := x.id, groupPath := ["Order", "Items"], name := "X",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := d.id, groupPath := ["Order", "Details"], name := "D",
        policy := { kind := .number unsigned } },
      { id := p.id, groupPath := ["Order", "Preferences"], name := "P",
        policy := { kind := .number unsigned } }]
    repeatableGroups := [{ level := 10, path := ["Order", "Items"] }] }

private def fieldPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def numericSurface : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.field (fieldPath "V"))
    right := .literal { value := 0, authoredScale := 0 } }

private def numericSurfaceIn (group field : String) : SurfaceNumericComparison :=
  { numericSurface with left := .atom (.field {
      base := .absolute, groups := [group], field }) }

private def condition? : Option ValidationCondition := do
  let checked ← (elaborateNumericComparison model ["Order"] numericSurface).toOption
  pure (.and
    (ValidationCondition.flat (.fieldFilled (.number u)))
    (ValidationCondition.numeric checked.core))

private def raw (uCell vCell : RawCell) : RawFlatContext where
  read id := if id == u.id then uCell else if id == v.id then vCell else .empty

private def verdictOf (uCell vCell : RawCell)
    (relevant : FieldId → Bool := fun _ => true) : Option Verdict := do
  let condition ← condition?
  pure (condition.evalSelected {
    fields := model.checkContext (raw uCell vCell)
    groups := GroupPresenceContext.unavailable
  } relevant)

private def checkedMixed? : Option (CheckedValidationCondition model) := do
  let flat ← (elaborate model ["Order"]
    (.fieldFilled (fieldPath "U"))).toOption
  let numeric ← (elaborateNumericComparison model ["Order"] numericSurface).toOption
  let flatCondition ← (CheckedValidationCondition.fromFlat flat).toOption
  let numericCondition ← (CheckedValidationCondition.fromNumeric numeric).toOption
  (flatCondition.and numericCondition).toOption

private def mismatchedGroupError? : Option ValidationConditionAssemblyError := do
  let order ← (elaborateNumericComparison model ["Order"]
    (numericSurfaceIn "Order" "V")).toOption
  let other ← (elaborateNumericComparison model ["Other"]
    (numericSurfaceIn "Other" "W")).toOption
  let orderCondition ← (CheckedValidationCondition.fromNumeric order).toOption
  let otherCondition ← (CheckedValidationCondition.fromNumeric other).toOption
  match orderCondition.and otherCondition with
  | .ok _ => none
  | .error error => some error

private def groupState (content erroneous : Bool)
    (relevance : GroupRelevance := .fullyRelevant) : GroupPresenceState :=
  { content, erroneous, relevance }

private def groupContext (path : GroupPath) (state : GroupPresenceState) :
    GroupPresenceContext :=
  fun candidate => if candidate == path then some state else none

private def checkedRuleGroup? (operator : GroupPresenceOperator) :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromGroupPresence model ["Order"]
    (.ruleGroup false) operator).toOption

private def checkedOtherGroup? : Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromGroupPresence model ["Order"]
    (.path { base := .absolute, groups := ["Other"] }) .filled).toOption

private def wildcardRuleGroupError? : Option ValidationConditionAssemblyError :=
  match CheckedValidationCondition.fromGroupPresence model ["Order"]
      (.ruleGroup true) .filled with
  | .ok _ => none
  | .error error => some error

private def repeatablePathError? : Option ValidationConditionAssemblyError :=
  match CheckedValidationCondition.fromGroupPresence model ["Order"]
      (.path { base := .absolute, groups := ["Order", "Items"] }) .filled with
  | .ok _ => none
  | .error error => some error

private def groupOperand (groups : GroupPath) : SurfaceGroupListOperand :=
  .group (.path { base := .absolute, groups })

private def groupList? (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromGroupList model ["Order"] operator operands).toOption

private def mixedGroupList? : Option (CheckedValidationCondition model) :=
  groupList? .groupsNotCollectivelyFilled [
    .field (fieldPath "U"),
    groupOperand ["Order", "Details"]]

private def positiveGroupList? : Option (CheckedValidationCondition model) :=
  groupList? .atLeastOneGroupFilled [
    .field (fieldPath "U"),
    groupOperand ["Order", "Details"]]

private def groupListError? (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) :
    Option ValidationConditionAssemblyError :=
  match CheckedValidationCondition.fromGroupList model ["Order"] operator operands with
  | .ok _ => none
  | .error error => some error

/- A mixed tree combines an ordinary presence leaf with a checked numeric-expression leaf through the same connective semantics. -/
example : verdictOf (.parsed (.num 1)) (.parsed (.num 2)) =
    some (.fired .value) := by
  native_decide

/- Flat-left false short-circuits the numeric leaf, while a reached out-of-set numeric reference remains UNKNOWN. -/
example :
    verdictOf .presentEmpty (.rejected .malformed) (fun id => id == u.id) =
        some .notFired ∧
    verdictOf (.parsed (.num 1)) (.parsed (.num 2)) (fun id => id == u.id) =
        some .unknown := by
  native_decide

/- One reference traversal sees both leaf families. -/
example : condition?.map (fun condition =>
    condition.referencesField model u.id &&
      condition.referencesField model v.id) = some true := by
  native_decide

/- Checked composition retains both certificates and the exact common row group. -/
example : checkedMixed?.map (fun checked =>
    (checked.rowGroup, checked.core.referencesField model u.id,
      checked.core.referencesField model v.id)) =
    some (["Order"], true, true) := by
  native_decide

/- Numeric leaves checked for different rule-instance groups cannot enter one mixed condition. -/
example : mismatchedGroupError? =
    some (.rowGroupMismatch ["Order"] ["Other"]) := by
  native_decide

/- `RuleGroup` retains its authored origin, resolves to the declaring group, and statically references exactly that group's field subtree. -/
example : (checkedRuleGroup? .filled).map (fun checked =>
    match checked.core with
    | .leaf (.groupPresence operator reference) =>
        operator == .filled && reference.origin == .ruleGroup &&
          reference.path == ["Order"] &&
          checked.core.referencesField model u.id &&
          checked.core.referencesField model v.id &&
          !checked.core.referencesField model w.id
    | _ => false) = some true := by
  native_decide

/- An instantiated repeatable row is admitted content even when all of its scalar descendants are empty. The shared leaf consumes that already-resolved state rather than re-traversing a document. -/
example : (checkedRuleGroup? .filled).map (fun checked =>
    checked.core.evalFull {
      fields := model.checkContext (raw .empty .empty)
      groups := groupContext ["Order"]
        ({ descendantCells := [], hasInstantiatedRow := true,
           structuralError := false, relevance := .fullyRelevant } :
          ResolvedGroupPresenceInput).derive
    } true) = some (.fired .value) := by
  native_decide

/- `GroupNotFilled` fires only for a fully visible clean empty group; a formal group error makes the reached leaf unknown. -/
example : (checkedRuleGroup? .notFilled).map (fun checked =>
    (checked.core.evalFull {
      fields := model.checkContext (raw .empty .empty)
      groups := groupContext ["Order"] (groupState false false)
    } false,
    checked.core.evalFull {
      fields := model.checkContext (raw .empty .empty)
      groups := groupContext ["Order"] (groupState false true)
    } false)) = some (.fired .omission, .unknown) := by
  native_decide

/- Ordinary resolved group paths use the same leaf mechanism, while missing resolved runtime state is unavailable rather than false. -/
example : checkedOtherGroup?.map (fun checked =>
    (checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := groupContext ["Other"] (groupState true false)
    },
    checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := GroupPresenceContext.unavailable
    })) = some (.fired .value, .unknown) := by
  native_decide

/- The reserved keyword's wildcard is rejected at checked elaboration before it can be erased into an ordinary path. -/
example : wildcardRuleGroupError? =
    some (.groupReference .wildcardOnRuleGroup) := by
  native_decide

/- An ordinary repeatable path has no concrete row at this boundary; only `RuleGroup` may consume the already-selected rule instance. -/
example : repeatablePathError? =
    some (.repeatableGroupRequiresAddress ["Order", "Items"]) := by
  native_decide

/- Fixed group-list conditions accept fields and groups through one resolved entity-presence tally. The error-field traversal retains the exact field operand and every field in the group subtree. -/
example : mixedGroupList?.map (fun checked =>
    checked.core.referencesField model u.id &&
      checked.core.referencesField model d.id &&
      !checked.core.referencesField model p.id) = some true := by
  native_decide

/- A filled field and a clean-empty group establish the mixed predicate. Replacing the field by a formal error leaves it unavailable and therefore cannot establish either required bucket. -/
example : mixedGroupList?.map (fun checked =>
    (checked.core.evalSelected {
      fields := model.checkContext (raw (.parsed (.num 1)) .empty)
      groups := groupContext ["Order", "Details"] (groupState false false)
    },
    checked.core.evalSelected {
      fields := model.checkContext (raw (.rejected .malformed) .empty)
      groups := groupContext ["Order", "Details"] (groupState false false)
    })) = some (.fired .omission, .unknown) := by
  native_decide

/- Field relevance and group-state availability are classified independently. Either known filled operand decides `AtLeastOneGroupFilled`; when both operands are unavailable, the collapsed leaf remains unknown. -/
example : positiveGroupList?.map (fun checked =>
    (checked.core.evalSelected {
      fields := model.checkContext (raw (.rejected .malformed) .empty)
      groups := groupContext ["Order", "Details"] (groupState true false)
    } (fun id => id != u.id),
    checked.core.evalSelected {
      fields := model.checkContext (raw (.parsed (.num 1)) .empty)
      groups := GroupPresenceContext.unavailable
    },
    checked.core.evalSelected {
      fields := model.checkContext (raw (.rejected .malformed) .empty)
      groups := GroupPresenceContext.unavailable
    } (fun id => id != u.id))) =
      some (.fired .value, .fired .value, .unknown) := by
  native_decide

/- A collapsed non-fire embeds as least-information `unknown`; an independent VALUE branch in the existing positive tree still decides the complete `Or`. -/
example : mixedGroupList?.map (fun checked =>
    ValidationCondition.evalSelected (ConditionTree.or checked.core
      (ValidationCondition.flat (.fieldFilled (.number v)))) {
        fields := model.checkContext (raw (.rejected .malformed) (.parsed (.num 2)))
        groups := groupContext ["Order", "Details"] (groupState false false)
      }) = some (Verdict.fired .value) := by
  native_decide

/- The three multi-entity operators require at least two operands and reject every root-group operand. The count-zero/count-positive pair permits a sole root but no root beside another entity. -/
example :
    groupListError? .allGroupsFilled [groupOperand ["Order", "Details"]] =
      some .groupListNeedsMultipleOperands ∧
    groupListError? .notAllGroupsFilled [
      groupOperand ["Other"], groupOperand ["Order", "Details"]] =
      some (.rootGroupInGroupList ["Other"]) ∧
    groupListError? .atLeastOneGroupFilled [
      groupOperand ["Other"], .field (fieldPath "U")] =
      some (.rootGroupRequiresSoleOperand ["Other"]) ∧
    (groupList? .noGroupFilled [groupOperand ["Other"]]).isSome = true := by
  native_decide

/- Fixed singletons reuse the existing scalar owners, so checked construction cannot create a second representation of the same field/group presence predicate. -/
example :
    (groupList? .atLeastOneGroupFilled [
      .field (fieldPath "U")]).map (fun checked =>
        checked.core ==
          ValidationCondition.flat (.fieldFilled (.number u))) = some true ∧
    (groupList? .noGroupFilled [
      groupOperand ["Other"]]).map (fun checked =>
        match checked.core with
        | .leaf (.groupPresence .notFilled reference) =>
            reference.path == ["Other"]
        | _ => false) = some true := by
  native_decide

/- Direct duplicates and group/descendant overlaps are rejected before they can be counted twice. -/
example :
    groupListError? .atLeastOneGroupFilled [
      .field (fieldPath "U"), .field (fieldPath "U")] =
      some (.overlappingGroupListOperands ["Order", "U"] ["Order", "U"]) ∧
    groupListError? .groupsNotCollectivelyFilled [
      groupOperand ["Order", "Details"],
      .field { base := .absolute, groups := ["Order", "Details"], field := "D" }] =
      some (.overlappingGroupListOperands
        ["Order", "Details"] ["Order", "Details", "D"]) := by
  native_decide

/- Empty and unaddressed ordinary-repeatable operand lists fail before a core leaf exists. -/
example :
    groupListError? .noGroupFilled [] = some .emptyGroupList ∧
    groupListError? .atLeastOneGroupFilled [
      groupOperand ["Order", "Items"],
      groupOperand ["Order", "Details"]] =
      some (.repeatableGroupRequiresAddress ["Order", "Items"]) := by
  native_decide

end A12Kernel.Conformance.ValidationCondition
