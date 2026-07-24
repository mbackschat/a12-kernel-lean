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

private def nestedValue : FlatFieldDecl :=
  { id := 7, groupPath := ["Order", "Items", "Lines"], name := "Z",
    policy := { kind := .number unsigned }, repeatableScope := [10, 20] }

private def otherRowValue : FlatFieldDecl :=
  { id := 8, groupPath := ["Order", "OtherRows"], name := "Y",
    policy := { kind := .number unsigned }, repeatableScope := [30] }

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
        policy := { kind := .number unsigned } },
      nestedValue,
      otherRowValue]
    repeatableGroups := [
      { level := 10, path := ["Order", "Items"] },
      { level := 20, path := ["Order", "Items", "Lines"] },
      { level := 30, path := ["Order", "OtherRows"] }] }

private def fieldPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def numericSurface : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.field (fieldPath "V"))
    right := .literal { value := 0, authoredScale := 0 } }

private def numericSurfaceIn (group field : String) : SurfaceNumericComparison :=
  { numericSurface with left := .atom (.field {
      base := .absolute, groups := [group], field }) }

private def nestedStarPath (outerStar : Bool) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Order" },
      { name := "Items", starred := outerStar },
      { name := "Lines", starred := true }]
    field := "Z" }

private def nestedStarSource (outerStar : Bool) : SurfaceNumberEntitySource :=
  { first := .star (nestedStarPath outerStar)
    rest := [] }

private def nestedStarHavingSource
    (outerStar : Bool) : SurfaceNumberEntitySource :=
  { first := .starHaving (nestedStarPath outerStar)
      (.compareNumbers .equal
        { origin := .inner
          field := {
            base := .absolute
            groups := ["Order", "Items", "Lines"]
            field := "Z" } }
        { origin := .outer
          field := {
            base := .absolute
            groups := ["Order", "Items"]
            field := "X" } })
    rest := [] }

private def nestedStarHavingRepetitionSource :
    SurfaceNumberEntitySource :=
  { first := .starHaving (nestedStarPath true)
      (.compareRepetitions .equal
        { origin := .inner
          group := .path {
            base := .absolute
            groups := ["Order", "Items", "Lines"] } }
        { origin := .outer
          group := .path {
            base := .absolute
            groups := ["Order", "Items"] } })
    rest := [] }

private def checkedAggregateCondition?
    (authored : SurfaceNumberEntitySource) :
    Option (ValidationCondition model) := do
  let source ←
    (elaborateNumberEntitySource model ["Order", "Items"]
      authored).toOption
  let comparison : OrderedNumericComparison model := {
    op := .ordinary .greater
    left := .atom (.aggregate .sum source)
    right := .literal { value := 0, authoredScale := 0 } }
  pure (ValidationCondition.orderedNumericIn
    .modelWideCheckedComputation comparison)

private def checkedStarAggregateCondition?
    (outerStar : Bool) (having : Bool := false) :
    Option (ValidationCondition model) :=
  checkedAggregateCondition?
    (if having then nestedStarHavingSource outerStar
      else nestedStarSource outerStar)

private def checkedStarRepetitionHavingCondition? :
    Option (ValidationCondition model) :=
  checkedAggregateCondition? nestedStarHavingRepetitionSource

private def starAggregateIterationScope
    (outerStar : Bool) (having : Bool := false) :
    Option (Except ValidationCondition.RuleIterationScopeError
      (Option (List RepeatableLevel))) :=
  checkedStarAggregateCondition? outerStar having
    |>.map (·.ordinaryIterationScope)

private def incompatibleStarAndOrdinaryScope :
    Option (Except ValidationCondition.RuleIterationScopeError
      (Option (List RepeatableLevel))) := do
  let star ← checkedStarAggregateCondition? false
  let ordinary := ValidationCondition.repeatableFieldPresence
    (model := model) .filled otherRowValue
  pure (ValidationCondition.ordinaryIterationScope
    (ConditionTree.and star ordinary))

private def hasStarAggregateIterationScope
    (outerStar : Bool) (expected : Option (List RepeatableLevel))
    (having : Bool := false) : Bool :=
  match starAggregateIterationScope outerStar having with
  | some (.ok actual) => actual == expected
  | _ => false

private def hasIncompatibleStarAndOrdinaryScope : Bool :=
  match incompatibleStarAndOrdinaryScope with
  | some (.error (.incompatibleScopes left right)) =>
      left == [10] && right == [30]
  | _ => false

private def hasOuterRepetitionIterationScope : Bool :=
  match checkedStarRepetitionHavingCondition? with
  | some condition =>
      match condition.ordinaryIterationScope with
      | .ok actual => actual == some [10]
      | .error _ => false
  | _ => false

private def condition? : Option (ValidationCondition model) := do
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

private def twoGroupContext
    (firstPath : GroupPath) (firstState : GroupPresenceState)
    (secondPath : GroupPath) (secondState : GroupPresenceState) :
    GroupPresenceContext :=
  fun candidate =>
    if candidate == firstPath then some firstState
    else if candidate == secondPath then some secondState
    else none

private def fixedGroupCount
    (groups : List GroupPath := [
      ["Order", "Details"], ["Order", "Preferences"]]) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.filledGroupCount (groups.map fun path =>
    .path { base := .absolute, groups := path }))

private def groupCountComparison
    (groups : List GroupPath := [
      ["Order", "Details"], ["Order", "Preferences"]])
    (op : NumericComparisonOp := .greater)
    (expected : Rat := 0) : SurfaceNumericComparison :=
  { op := .ordinary op
    left := fixedGroupCount groups
    right := .literal { value := expected, authoredScale := 0 } }

private def checkedGroupCount?
    (surface : SurfaceNumericComparison := groupCountComparison) :
    Option (CheckedValidationCondition model) := do
  let numeric ← (elaborateNumericComparison model ["Order"] surface).toOption
  (CheckedValidationCondition.fromNumeric numeric).toOption

private def groupCountError?
    (surface : SurfaceNumericComparison) : Option NumericValidationElabError :=
  match elaborateNumericComparison model ["Order"] surface with
  | .ok _ => none
  | .error error => some error

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

private def checkedRepeatableGroupPath? :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromGroupPresence model ["Order"]
    (.path { base := .absolute, groups := ["Order", "Items"] })
    .filled).toOption

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
    condition.referencesField u.id &&
      condition.referencesField v.id) = some true := by
  native_decide

/- Checked composition retains both certificates and the exact common row group. -/
example : checkedMixed?.map (fun checked =>
    (checked.rowGroup, checked.core.referencesField u.id,
      checked.core.referencesField v.id)) =
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
          checked.core.referencesField u.id &&
          checked.core.referencesField v.id &&
          !checked.core.referencesField w.id
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

/- An ordinary group path beneath a repeatable level retains that exact resolved entity and declares its need for the addressed rule route. Fixed group-list construction remains the separate owner that rejects the same path without a row environment. -/
example :
    (match checkedRepeatableGroupPath? with
    | some checked =>
        (match checked.core.ordinaryIterationScope with
        | .ok (some scope) => scope == [10]
        | _ => false) &&
          checked.core.requiresAddressedValidation &&
          match checked.core with
          | .leaf (.groupPresence .filled reference) =>
              reference.path == ["Order", "Items"] &&
                reference.origin == .path
          | _ => false
    | none => false) = true := by
  native_decide

/- Fixed group-list conditions accept fields and groups through one resolved entity-presence tally. The error-field traversal retains the exact field operand and every field in the group subtree. -/
example : mixedGroupList?.map (fun checked =>
    checked.core.referencesField u.id &&
      checked.core.referencesField d.id &&
      !checked.core.referencesField p.id) = some true := by
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
      (ValidationCondition.flat (model := model)
        (.fieldFilled (.number v)))) {
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
        match checked.core with
        | .leaf (.flat (.fieldFilled (.number field))) => field == u
        | _ => false) = some true ∧
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

/- The plain fixed group count is a scale-0 numeric source in the shared checked expression tree. It counts admitted content only after every operand is fully relevant and error-free, and composes with ordinary arithmetic. -/
example : checkedGroupCount?.map (fun checked =>
    (checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := twoGroupContext
        ["Order", "Details"] (groupState true false)
        ["Order", "Preferences"] (groupState false false)
    },
    checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := twoGroupContext
        ["Order", "Details"] (groupState true false)
        ["Order", "Preferences"] (groupState true false)
    })) = some (.fired .value, .fired .value) ∧
  (checkedGroupCount? (groupCountComparison
      (op := .equal) (expected := 2))).map (fun checked =>
    checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := twoGroupContext
        ["Order", "Details"] (groupState true false)
        ["Order", "Preferences"] (groupState true false)
    }) = some (.fired .value) ∧
  (checkedGroupCount? {
      op := .ordinary .equal
      left := .binary .add fixedGroupCount
        (.literal { value := 1, authoredScale := 0 })
      right := .literal { value := 2, authoredScale := 0 }
    }).map (fun checked =>
      checked.core.evalSelected {
        fields := model.checkContext (raw .empty .empty)
        groups := twoGroupContext
          ["Order", "Details"] (groupState true false)
          ["Order", "Preferences"] (groupState false false)
      }) = some (.fired .omission) := by
  native_decide

/- Zero is a real count, not numeric absence. Because either clean-empty group may later fill, `0 < 1` is a firing whose error is repairable by filling. -/
example : (checkedGroupCount? (groupCountComparison
    (op := .less) (expected := 1))).map (fun checked =>
  checked.core.evalSelected {
    fields := model.checkContext (raw .empty .empty)
    groups := twoGroupContext
      ["Order", "Details"] (groupState false false)
      ["Order", "Preferences"] (groupState false false)
  }) = some (.fired .omission) := by
  native_decide

/- A formal group error, partial relevance, or missing resolved state makes the complete numeric source unavailable rather than inventing a partial count or a `FormalCause`. -/
example : checkedGroupCount?.map (fun checked =>
    (checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := twoGroupContext
        ["Order", "Details"] (groupState true true)
        ["Order", "Preferences"] (groupState true false)
    },
    checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := twoGroupContext
        ["Order", "Details"] (groupState true false .partlyRelevant)
        ["Order", "Preferences"] (groupState true false)
    },
    checked.core.evalSelected {
      fields := model.checkContext (raw .empty .empty)
      groups := groupContext
        ["Order", "Details"] (groupState true false)
    })) = some (.unknown, .unknown, .unknown) := by
  native_decide

/- Fixed group counts require at least two distinct non-root, nonrepeatable groups. The checked source also retains each group subtree for whole-rule reference validation. -/
example :
    groupCountError? (groupCountComparison
      [["Order", "Details"]]) = some .groupCountNeedsMultipleOperands ∧
    groupCountError? (groupCountComparison
      [["Other"], ["Order", "Details"]]) =
        some (.rootGroupInGroupCount ["Other"]) ∧
    groupCountError? (groupCountComparison
      [["Order", "Details"], ["Order", "Details"]]) =
        some (.overlappingGroupCountOperands
          ["Order", "Details"] ["Order", "Details"]) ∧
    groupCountError? (groupCountComparison
      [["Order", "Items"], ["Order", "Details"]]) =
        some (.repeatableGroupCountRequiresStar ["Order", "Items"]) ∧
    groupCountError? (groupCountComparison
      [["Order", "Missing"], ["Order", "Details"]]) =
        some (.unknownGroupInCount ["Order", "Missing"]) ∧
    checkedGroupCount?.map (fun checked =>
      checked.core.referencesField d.id &&
        checked.core.referencesField p.id &&
        !checked.core.referencesField u.id) = some true := by
  native_decide

/- A starred numeric operand contributes its nonempty checked binding prefix above the first star. Candidate-local filter references remain operand-local, but checked `$` Number and repetition references contribute their captured outer scope. An unrelated ordinary scope is rejected rather than positional-joined. -/
example :
    hasStarAggregateIterationScope false (some [10]) = true ∧
      hasStarAggregateIterationScope true none = true ∧
      hasStarAggregateIterationScope true (some [10]) true = true ∧
      hasOuterRepetitionIterationScope = true ∧
      hasIncompatibleStarAndOrdinaryScope = true := by
  native_decide

end A12Kernel.Conformance.ValidationCondition
