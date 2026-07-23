import A12Kernel.Elaboration.Correlation

/-! # Checked single-group correlation-elaboration conformance locks -/

namespace A12Kernel.Conformance.CorrelationElaboration

open A12Kernel

private def items : RepeatableGroupDecl := { level := 10, path := ["Order", "Items"] }
private def other : RepeatableGroupDecl := { level := 20, path := ["Order", "Other"] }
private def nestedItems : RepeatableGroupDecl :=
  { level := 30, path := ["Order", "Items", "Nested"] }

private def countDecl : FlatFieldDecl :=
  { id := 0, groupPath := items.path, name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [items.level] }

private def weightDecl : FlatFieldDecl :=
  { id := 1, groupPath := items.path, name := "Weight",
    policy := { kind := .number { scale := 2, signed := false } },
    repeatableScope := [items.level] }

private def flagDecl : FlatFieldDecl :=
  { id := 2, groupPath := items.path, name := "Flag",
    policy := { kind := .boolean }, repeatableScope := [items.level] }

private def otherCountDecl : FlatFieldDecl :=
  { id := 3, groupPath := other.path, name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [other.level] }

private def nestedCountDecl : FlatFieldDecl :=
  { id := 4, groupPath := nestedItems.path, name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [items.level, nestedItems.level] }

private def fakeScopedDecl : FlatFieldDecl :=
  { id := 5, groupPath := ["Order", "Fake"], name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [items.level] }

private def secondGuardDecl : FlatFieldDecl :=
  { id := 6, groupPath := items.path, name := "SecondGuard",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [items.level] }

private def wrongScopeDecl : FlatFieldDecl :=
  { id := 7, groupPath := items.path, name := "WrongScope",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [other.level] }

private def model : FlatModel :=
  { fields := [countDecl, weightDecl, flagDecl, otherCountDecl, nestedCountDecl,
      secondGuardDecl],
    repeatableGroups := [items, other, nestedItems] }

private def nestedFalseSingletonDecl : FlatFieldDecl :=
  { id := 40, groupPath := nestedItems.path, name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [nestedItems.level] }

private def nestedFalseSingletonModel : FlatModel :=
  { fields := [nestedFalseSingletonDecl], repeatableGroups := [items, nestedItems] }

private def siblingRepeatableModel : FlatModel :=
  { fields := [countDecl, otherCountDecl], repeatableGroups := [items, other] }

private def collidingItemsField : FlatFieldDecl :=
  { id := 50, groupPath := ["Order"], name := "Items",
    policy := { kind := .boolean } }

private def repeatableHierarchyCollisionModel : FlatModel :=
  { fields := [collidingItemsField, countDecl], repeatableGroups := [items] }

private def collidingDetailsField : FlatFieldDecl :=
  { id := 51, groupPath := ["Order"], name := "Details",
    policy := { kind := .boolean } }

private def nestedOrdinaryField : FlatFieldDecl :=
  { id := 52, groupPath := ["Order", "Details"], name := "Name",
    policy := { kind := .boolean } }

private def ordinaryHierarchyCollisionModel : FlatModel :=
  { fields := [collidingDetailsField, nestedOrdinaryField] }

private def wrongScopeModel : FlatModel :=
  { model with fields := model.fields ++ [wrongScopeDecl] }

private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def relative (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups, field }

private def absoluteGroup (groups : List String) : SurfaceGroupPath :=
  { base := .absolute, groups }

private def relativeGroup (groups : List String) : SurfaceGroupPath :=
  { base := .relative 0, groups }

private def absoluteStar (before : List String) (group field : String) :
    SurfaceSingleStarFieldPath :=
  { base := .absolute, groupsBeforeStar := before, starredGroup := group, field }

private def relativeStar (before : List String) (group field : String) :
    SurfaceSingleStarFieldPath :=
  { base := .relative 0, groupsBeforeStar := before, starredGroup := group, field }

private def parentNavigatingStar : SurfaceSingleStarFieldPath :=
  { base := .relative 1, groupsBeforeStar := [], starredGroup := "Items",
    field := "Weight" }

private def numberRef (origin : HavingOrigin) (field : SurfaceFieldPath) :
    SurfaceHavingNumberRef := { origin, field }

private def repetitionRef (origin : HavingOrigin) (group : SurfaceGroupPath) :
    SurfaceHavingRepetitionRef := { origin, group }

private def absoluteRule (having : SurfaceCorrelatedHaving) : SurfaceSingleCorrelatedRule :=
  { errorField := absolute items.path "Count"
    guardField := absolute items.path "Count"
    valueField := absoluteStar ["Order"] "Items" "Weight"
    having }

private def relativeRule (having : SurfaceCorrelatedHaving) : SurfaceSingleCorrelatedRule :=
  { errorField := relative ["Items"] "Count"
    guardField := relative ["Items"] "Count"
    valueField := relativeStar [] "Items" "Weight"
    having }

private def equalCount (left right : HavingOrigin) : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    (numberRef left (absolute items.path "Count"))
    (numberRef right (absolute items.path "Count"))

private def shapeOf (result : Except CorrelationElabError (CheckedSingleCorrelatedRule model)) :
    Option (RepeatableGroupDecl × FlatNumberField × FlatNumberField ×
      FlatNumberField × CorrelatedHaving) :=
  match result with
  | .error _ => none
  | .ok checked => some (checked.core.group, checked.core.errorField,
      checked.core.guardField, checked.core.star.valueField,
      checked.core.star.having.condition)

private def havingOf
    (result : Except CorrelationElabError (CheckedSingleCorrelatedRule model)) :
    Option CorrelatedHaving :=
  match result with
  | .error _ => none
  | .ok checked => some checked.core.star.having.condition

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def resolvedGroupOf : Except SingleGroupElabError GroupPath → Option GroupPath
  | .ok path => some path
  | .error _ => none

private def namedParentGroup : SurfaceGroupPath :=
  { base := .relative 1, turningPoint := some "Order", groups := ["Items"] }

private def mismatchedParentGroup : SurfaceGroupPath :=
  { namedParentGroup with turningPoint := some "Other" }

/- Group-valued references use the same named-turning-point account as field references. -/
example : resolvedGroupOf
    (namedParentGroup.resolveAgainst ["Order", "Details"]) =
      some ["Order", "Items"] := by
  native_decide

example : errorOf (mismatchedParentGroup.resolveAgainst ["Order", "Details"]) =
    some (.invalidGroupReference mismatchedParentGroup) := by
  native_decide

example : errorOf nestedFalseSingletonModel.validate =
    some (.repeatableScopeMismatch nestedFalseSingletonDecl.path
      [items.level, nestedItems.level] [nestedItems.level]) := by
  native_decide

example : siblingRepeatableModel.validate.isOk = true := by
  native_decide

example : errorOf repeatableHierarchyCollisionModel.validate =
    some (.entityHierarchyCollision collidingItemsField.path items.path) := by
  native_decide

example : errorOf ordinaryHierarchyCollisionModel.validate =
    some (.entityHierarchyCollision collidingDetailsField.path
      nestedOrdinaryField.groupPath) := by
  native_decide

private def expectedShape : RepeatableGroupDecl × FlatNumberField ×
    FlatNumberField × FlatNumberField × CorrelatedHaving :=
  (items,
    { id := 0, info := { scale := 0, signed := false } },
    { id := 0, info := { scale := 0, signed := false } },
    { id := 1, info := { scale := 2, signed := false } },
    .compareNumbers .equal
      { origin := .inner, field := { id := 0, info := { scale := 0, signed := false } } }
      { origin := .outer, field := { id := 0, info := { scale := 0, signed := false } } })

private def forgedOrRule : ResolvedSingleCorrelatedRule :=
  let count : FlatNumberField :=
    { id := 0, info := { scale := 0, signed := false } }
  let weight : FlatNumberField :=
    { id := 1, info := { scale := 2, signed := false } }
  let inner : HavingNumberRef := { origin := .inner, field := count }
  let outer : HavingNumberRef := { origin := .outer, field := count }
  let condition : CorrelatedHaving := .or
    (CorrelatedHaving.compareNumbers .equal inner outer)
    (CorrelatedHaving.compareNumbers .notEqual inner outer)
  let having : OriginCheckedCorrelatedHaving :=
    { condition, usesInner := by decide, usesOuter := by decide }
  { group := items, errorField := count, guardField := count,
    star := { valueField := weight, having } }

/- Resolved `Or` remains executable, but cannot be presented as a checked result of the conjunction-only authored route. -/
example : forgedOrRule.wellFormedBool model = false := by
  native_decide

-- Absolute and relative authoring forms lower to the same checked core.
example : shapeOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (equalCount .inner .outer))) = some expectedShape := by
  native_decide

example : shapeOf (elaborateSingleCorrelatedRule model ["Order"]
    (relativeRule (.compareNumbers .equal
      (numberRef .inner (relative ["Items"] "Count"))
      (numberRef .outer (relative ["Items"] "Count"))))) = some expectedShape := by
  native_decide

example : havingOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.compareRepetitions .equal
      (repetitionRef .inner (absoluteGroup items.path))
      (repetitionRef .outer (absoluteGroup items.path))))) =
    some (.compareRepetitions .equal
      { origin := .inner, level := items.level }
      { origin := .outer, level := items.level }) := by
  native_decide

-- Equality and inequality are scale-gated; ordering over the same pair is not.
private def mismatched (op : SurfaceComparisonOp) : SurfaceCorrelatedHaving :=
  .compareNumbers op
    (numberRef .inner (absolute items.path "Count"))
    (numberRef .outer (absolute items.path "Weight"))

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (mismatched .equal))) =
    some (.equalityScaleMismatch countDecl.path 0 weightDecl.path 2) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (mismatched .notEqual))) =
    some (.equalityScaleMismatch countDecl.path 0 weightDecl.path 2) := by
  native_decide

example : (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (mismatched .less))).isOk = true := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.compareNumbers .greater
      (numberRef .inner (absolute items.path "Count"))
      (numberRef .outer (absolute items.path "Count"))))) =
    some (.unsupportedOperator .greater) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.compareNumbers .equal
      (numberRef .inner (absolute items.path "Flag"))
      (numberRef .outer (absolute items.path "Count"))))) =
    some (.fieldNotNumber flagDecl.path) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.compareNumbers .equal
      (numberRef .inner (absolute other.path "Count"))
      (numberRef .outer (absolute items.path "Count"))))) =
    some (.fieldOutsideGroup .inner otherCountDecl.path items.path) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule wrongScopeModel ["Order"]
    (absoluteRule (.compareNumbers .equal
      (numberRef .inner (absolute items.path "WrongScope"))
      (numberRef .outer (absolute items.path "Count"))))) =
    some (.resolve (.repeatableScopeMismatch wrongScopeDecl.path
      [items.level] [other.level])) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    { absoluteRule (equalCount .inner .outer) with
      valueField := absoluteStar ["Order", "Items"] "Nested" "Count" }) =
    some (.fieldScopeMismatch nestedCountDecl.path [nestedItems.level]
      [items.level, nestedItems.level]) := by
  native_decide

-- Scope IDs cannot make an undeclared path segment repeatable.
example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    { absoluteRule (equalCount .inner .outer) with
      valueField := absoluteStar ["Order"] "Fake" "Count" }) =
    some (.resolve (.unknownRepeatableGroup ["Order", "Fake"])) := by
  native_decide

example : errorOf ({ model with fields := model.fields ++ [fakeScopedDecl] }).validate =
    some (.repeatableScopeMismatch fakeScopedDecl.path [] [items.level]) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    { absoluteRule (equalCount .inner .outer) with
      valueField := parentNavigatingStar }) = some (.wildcardWithParentNavigation 1) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.compareRepetitions .equal
      (repetitionRef .inner (absoluteGroup other.path))
      (repetitionRef .outer (absoluteGroup items.path))))) =
    some (.repetitionGroupMismatch items.path other.path) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (equalCount .outer .outer))) = some .missingInner := by
  native_decide

-- All-inner Having is kernel-valid uncorrelated syntax, but outside this correlated route.
example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (equalCount .inner .inner))) = some .missingOuter := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    { absoluteRule (equalCount .inner .outer) with
      errorField := absolute items.path "SecondGuard" }) =
    some (.errorGuardMismatch secondGuardDecl.path countDecl.path) := by
  native_decide

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    { absoluteRule (equalCount .inner .outer) with
      guardField := absolute items.path "Missing" }) =
    some (.resolve (.invalidEntity (absolute items.path "Missing"))) := by
  native_decide

example : errorOf ({ model with repeatableGroups := [{ level := 30, path := [] }] }).validate =
    some (.invalidRepeatableGroupPath []) := by
  native_decide

example : errorOf ({ model with repeatableGroups :=
    [items, { level := other.level, path := items.path }] }).validate =
    some (.duplicateRepeatableGroupPath items.path) := by
  native_decide

example : errorOf ({ model with repeatableGroups :=
    [items, { level := items.level, path := other.path }] }).validate =
    some (.duplicateRepeatableLevel items.level) := by
  native_decide

private def wrongKindRaw : RawSingleGroupContext where
  candidates := [1]
  read row id := if row = 1 && id = 0 then .parsed (.bool true) else .empty

-- Runtime cells are checked with the same declaration policy used by static lowering.
example : (model.checkSingleGroupContext items wrongKindRaw).read 1 0 = malformedCheckedCell := by
  native_decide

example : ((model.checkSingleGroupContext items wrongKindRaw).atRow 1).observeValidationAt 0 =
    .unknown .malformed := by
  native_decide

private def emptyRaw (candidates : List RowIndex) : RawSingleGroupContext where
  candidates := candidates
  read _ _ := .empty

example : (model.checkSingleGroupContext items (emptyRaw [1])).read 1 999 =
    malformedCheckedCell := by
  native_decide

example : (model.checkSingleGroupContext items (emptyRaw [1])).read 1 otherCountDecl.id =
    malformedCheckedCell := by
  native_decide

-- The low-level compiler remains fail-closed when called defensively on an unchecked model.
example : (wrongScopeModel.checkSingleGroupContext items (emptyRaw [1])).read 1
    wrongScopeDecl.id =
    malformedCheckedCell := by
  native_decide

private def firingRowsFor (raw : RawSingleGroupContext) :
    Option (Except SingleGroupContextError (List RowIndex)) :=
  match elaborateSingleCorrelatedRule model ["Order"]
      (absoluteRule (equalCount .inner .outer)) with
  | .ok checked => some (checked.firingRows raw)
  | .error _ => none

private def firingErrorFor (raw : RawSingleGroupContext) : Option SingleGroupContextError :=
  match firingRowsFor raw with
  | some (.error error) => some error
  | _ => none

private def successfulFiringRowsFor (raw : RawSingleGroupContext) : Option (List RowIndex) :=
  match firingRowsFor raw with
  | some (.ok rows) => some rows
  | _ => none

example : firingErrorFor (emptyRaw [0]) = some (.zeroCandidate 0) := by
  native_decide

example : firingErrorFor (emptyRaw [1, 1]) = some (.duplicateCandidate 1) := by
  native_decide

example : successfulFiringRowsFor (emptyRaw [1]) = some [] := by
  native_decide

end A12Kernel.Conformance.CorrelationElaboration
