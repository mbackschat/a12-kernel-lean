import A12Kernel.Elaboration.FieldEntityList

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
    SurfaceHavingRepetitionRef := { origin, group := .path group }

private def ruleGroupRef (origin : HavingOrigin) (starred : Bool := false) :
    SurfaceHavingRepetitionRef :=
  { origin, group := .ruleGroup starred }

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

private def havingDirectRef (origin : HavingOrigin) (field : SurfaceFieldPath) :
    SurfaceHavingDirectFieldOperand :=
  { origin, field }

private def havingDirectSource (first second : SurfaceHavingDirectFieldOperand) :
    SurfaceHavingDirectFieldSource :=
  { first, rest := [second] }

private def elaborateHavingDirectPair (firstOrigin secondOrigin : HavingOrigin)
    (firstField : String := "Count") (secondField : String := "Count") :=
  elaborateHavingDirectFieldSource model ["Order"] [items.level] [items.level]
    (havingDirectSource
      (havingDirectRef firstOrigin (absolute items.path firstField))
      (havingDirectRef secondOrigin (absolute items.path secondField)))

private def havingDirectPairSnapshot
    (result : Except FieldEntityShapeElabError
      (CheckedHavingDirectFieldSource model)) :
    Option (List (HavingOrigin × FieldId × FieldEntityReadForm)) := do
  let checked ← result.toOption
  pure (checked.operands.map fun operand =>
    (operand.origin, operand.declaration.id, operand.form))

/- The reviewed Kernel separator retains different exact identities after both paths resolve to the
   same declaration ([checkpoint](../../docs/SOURCES.md#src-pr2-correlated-operand-identity)). -/
example : havingDirectPairSnapshot
    (elaborateHavingDirectPair .outer .inner) =
      some [(.outer, countDecl.id, .stored), (.inner, countDecl.id, .stored)] := by
  native_decide

/- Removing only `$` turns the same authored pair into the shared direct-duplicate class. -/
example : errorOf (elaborateHavingDirectPair .inner .inner) =
    some (.duplicateOperand countDecl.id) ∧
    (errorOf (elaborateHavingDirectPair .inner .inner)).bind
      FieldEntityShapeElabError.diagnostic? = some .duplicateParam1 := by
  native_decide

/- Typed-surface controls retain identity independently of slot order, while equal outer origins
   remain a duplicate. Kernel correspondence for these two controls is intentionally unclaimed. -/
example : (elaborateHavingDirectPair .inner .outer).isOk = true ∧
    errorOf (elaborateHavingDirectPair .outer .outer) =
      some (.duplicateOperand countDecl.id) := by
  native_decide

/- Origin is one identity component rather than the whole identity: two current-row declarations
   remain distinct. -/
example : (elaborateHavingDirectPair .inner .inner "Count" "Weight").isOk = true := by
  native_decide

private def resolvedGroupOf : Except SingleGroupElabError GroupPath → Option GroupPath
  | .ok path => some path
  | .error _ => none

private def namedParentGroup : SurfaceGroupPath :=
  { base := .relative 1, turningPoint := some "Order", groups := ["Items"] }

private def mismatchedParentGroup : SurfaceGroupPath :=
  { namedParentGroup with turningPoint := some "Other" }

private def ruleGroupSnapshot :
    Option (GroupReferenceOrigin × GroupPath × Bool × Bool × Bool) := do
  let resolved ← ((.ruleGroup false : SurfaceGroupReference).resolveAgainst
    items.path).toOption
  pure (resolved.origin, resolved.path,
    resolved.referencesField model countDecl.id,
    resolved.referencesField model nestedCountDecl.id,
    resolved.referencesField model otherCountDecl.id)

/- Group-valued references use the same named-turning-point account as field references. -/
example : resolvedGroupOf
    (namedParentGroup.resolveAgainst ["Order", "Details"]) =
      some ["Order", "Items"] := by
  native_decide

example : errorOf (mismatchedParentGroup.resolveAgainst ["Order", "Details"]) =
    some (.invalidGroupReference mismatchedParentGroup) := by
  native_decide

/- The checked keyword retains its origin and counts same-group or descendant fields, but not a sibling field, as referenced. -/
example : ruleGroupSnapshot = some
    (.ruleGroup, items.path, true, true, false) := by
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

/- `RuleGroup` retains its keyword origin while both current-repetition operands resolve to the rule's own repeatable level. -/
example : havingOf (elaborateSingleCorrelatedRule model items.path
    (absoluteRule (.compareRepetitions .notEqual
      (ruleGroupRef .inner) (ruleGroupRef .outer)))) =
    some (.compareRepetitions .notEqual
      { origin := .inner, level := items.level }
      { origin := .outer, level := items.level }) := by
  native_decide

/- A star written on `RuleGroup` reaches the keyword-specific diagnostic before repetition matching. -/
example : errorOf (elaborateSingleCorrelatedRule model items.path
    (absoluteRule (.compareRepetitions .equal
      (ruleGroupRef .inner true) (ruleGroupRef .outer)))) =
    some .wildcardOnRuleGroup := by
  native_decide

/- The legacy one-group route's three refusals. It admits the numeric and repetition leaves joined
   by conjunction and nothing else, and each newer form fails closed at its own arm rather than
   being reshaped: without these cases the route's narrowness rests on reading the code. The kernel
   admits all three inside a filter, so the narrowness is this route's, not the kernel's. -/

example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.compareStrings .equal
      { origin := .inner, field := absolute items.path "Count" } "K"))) =
    some .stringLeafOutsideStarRoute := by
  native_decide

/-- The presence leaf reports through the same arm, whose name predates it. -/
example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.presence .filled
      { origin := .inner, field := absolute items.path "Count" }))) =
    some .stringLeafOutsideStarRoute := by
  native_decide

/-- Disjunction is refused at its own arm, so the cause is named rather than surfacing later as an
    unexplained incoherence. Both operands are leaves this route otherwise admits, which is what
    makes the connective the whole difference. -/
example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.or
      (.compareNumbers .equal (numberRef .inner (absolute items.path "Count"))
        (numberRef .outer (absolute items.path "Count")))
      (.compareNumbers .equal (numberRef .inner (absolute items.path "Count"))
        (numberRef .outer (absolute items.path "Count")))))) =
    some .disjunctionOutsideStarRoute := by
  native_decide

/-- The control: the identical pair under `And` is admitted, so the refusal above is the
    connective's and not the operands'. -/
example : errorOf (elaborateSingleCorrelatedRule model ["Order"]
    (absoluteRule (.and
      (.compareNumbers .equal (numberRef .inner (absolute items.path "Count"))
        (numberRef .outer (absolute items.path "Count")))
      (.compareNumbers .equal (numberRef .inner (absolute items.path "Count"))
        (numberRef .outer (absolute items.path "Count")))))) = none := by
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
    some (.fieldNotNumber flagDecl.path .boolean) := by
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

/-! ## Repetition-reference binding sources

`CurrentRepetition` has **two** binding sources and the marker selects which one must carry the
coordinate: an unmarked reference reads the candidate environment, which an operand's own star
populates, while a `$`-marked one reads the captured host environment. The cases below hold the
level fixed at a star-reopened one and vary only the origins and whether the host binds it.
-/

private def repetitionAdmitted (candidateLevels outerLevels : List RepeatableLevel)
    (left right : HavingOrigin) : Bool :=
  CorrelatedHavingLeaf.wellFormedForEnvironments { fields := [] }
    candidateLevels outerLevels
    (.compareRepetitions .notEqual
      { origin := left, level := 7 } { origin := right, level := 7 })

/- **An operand's star binds an unmarked reference on its own**, so a filter carries one even when
the host binds nothing; the marked spelling in the identical shape is refused, and is admitted once
the host does bind the level. Measured against the Kernel at a12-dmkits `eded8263` from a rule at a
nonrepeatable locus, where the aggregate collapses rows and the host therefore does not iterate. -/
example :
    repetitionAdmitted [7] [] .inner .inner = true ∧
      repetitionAdmitted [7] [] .outer .outer = false ∧
      repetitionAdmitted [7] [7] .outer .outer = true := by
  native_decide

/- **The self-exclusion pair's "both reopened and host-bound" requirement is a consequence, not a
rule.** The comparison carries one reference of each kind, so it needs both sources at once: refused
where the host binds nothing and admitted where it does, with the candidate side unchanged. Nothing
in the clause encodes the conjunction — it falls out of the two sources above, which is why this pair
is locked beside them rather than as a separate account. -/
example :
    repetitionAdmitted [7] [] .inner .outer = false ∧
      repetitionAdmitted [7] [7] .inner .outer = true := by
  native_decide

private def repetitionAdmittedAt (candidateLevels outerLevels : List RepeatableLevel)
    (level : RepeatableLevel) (origin : HavingOrigin) : Bool :=
  CorrelatedHavingLeaf.wellFormedForEnvironments { fields := [] }
    candidateLevels outerLevels
    (.compareRepetitions .notEqual
      { origin, level } { origin, level })

/- **The two sources compose at two levels, and the marker only matters on a reopened one.** A host
that iterates the outer level over an operand starring only the inner one gives a candidate
environment of both levels — the inner reopened, the outer inherited — against a captured
environment of the outer alone. So on the **inner** level the marker decides admission, while on the
**outer** level *both* spellings are admitted, which is the redundant-marker rule
[`SPEC-2026-09-03-07`](../../docs/A12-DMKITS-SPEC-SYNC-LEDGER.md) established for field references
now holding for a repetition one. Measured as a full 2x2 against the Kernel at a12-dmkits `eded8263`,
every row carrying the in-scope conjunct the filter's scope gate demands — without it the outer rows
collapse to `MVK_NO_ITERATION_FOR_WILDCARD` and establish nothing about binding. -/
example :
    (repetitionAdmittedAt [1, 2] [1] 2 .inner = true ∧
        repetitionAdmittedAt [1, 2] [1] 2 .outer = false) ∧
      (repetitionAdmittedAt [1, 2] [1] 1 .inner = true ∧
        repetitionAdmittedAt [1, 2] [1] 1 .outer = true) := by
  native_decide

end A12Kernel.Conformance.CorrelationElaboration
