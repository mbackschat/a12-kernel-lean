import A12Kernel.Elaboration.ValidationCondition.Assembly

/-! # Checked terminal-repeatable group-star locks -/

namespace A12Kernel.Conformance.StarGroupElaboration

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Catalog", "Sections", "Items"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10, 20] }

private def sections : RepeatableGroupDecl :=
  { level := 10, path := ["Shop", "Catalog", "Sections"], repeatability := some 2 }

private def items : RepeatableGroupDecl :=
  { level := 20, path := ["Shop", "Catalog", "Sections", "Items"], repeatability := some 3 }

private def model : FlatModel :=
  { fields := [amount], repeatableGroups := [items, sections] }

/-- A repeatable group carrying **no field anywhere in its subtree**. The Kernel admits such a group in
a model and reports the model valid, then refuses every operand that names it. -/
private def hollow : RepeatableGroupDecl :=
  { level := 30, path := ["Shop", "Catalog", "Hollow"], repeatability := some 2 }

private def hollowModel : FlatModel :=
  { fields := [amount], repeatableGroups := [items, sections, hollow] }

private def segment (name : String) (starred : Bool := false) : SurfaceStarGroupSegment :=
  { name, starred }

private def absoluteSource (catalogStar outerStar innerStar : Bool) : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [segment "Shop", segment "Catalog" catalogStar,
      segment "Sections" outerStar, segment "Items" innerStar] }

private def relativeSource (outerStar innerStar : Bool) : SurfaceStarGroupPath :=
  { base := .relative 2
    groups := [segment "Sections" outerStar, segment "Items" innerStar] }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def checkedOf (source : SurfaceStarGroupPath) (targetModel : FlatModel := model) :=
  elaborateStarredGroupSource targetModel amount.groupPath source

private def errorOfStarredGroup
    (result : Except StarredGroupElabError (CheckedStarredGroupSource hollowModel)) :
    Option StarredGroupElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def resultOf (source : SurfaceStarGroupPath) :=
  match checkedOf source with
  | .ok checked => some (checked.group.level, checked.path)
  | .error _ => none

private def errorOf (source : SurfaceStarGroupPath) (targetModel : FlatModel := model) :=
  match checkedOf source targetModel with
  | .ok _ => none
  | .error error => some error

private def errorFromDeclaringGroup (declaringGroup : GroupPath)
    (source : SurfaceStarGroupPath) :=
  match elaborateStarredGroupSource model declaringGroup source with
  | .ok _ => none
  | .error error => some error

private def countOf (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option Nat :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.rowCount (document rows) outer with
      | .ok count => some count
      | .error _ => none

private def outcomeOf (operator : StarredGroupFillQuantifier)
    (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option ValidationFillOutcome :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateFull operator (document rows) outer with
      | .ok outcome => some outcome
      | .error _ => none

private def repeatedOutcomeOf (operator : GroupFillQuantifier)
    (rows : List RowAddr) : Option (Nat × Verdict) := do
  let operand : SurfaceGroupListOperand :=
    .starredGroup (absoluteSource false true true)
  let checked ←
    (CheckedValidationCondition.fromGroupList
      model amount.groupPath operator [operand, operand]).toOption
  let scalar := model.checkContext { read := fun _ => .empty }
  let occurrences := match checked.core with
    | .leaf (.groupList _ operands) => operands.length
    | _ => 0
  match checked.core.evalAddressed {
      scalar := {
        fields := scalar
        groups := GroupPresenceContext.unavailable }
      outer := []
      input := .legacy (document rows) (fun _ field => scalar.read field)
    } with
  | .ok verdict => some (occurrences, verdict)
  | .error _ => none

private def partialOutcomeOf (operator : GroupFillQuantifier)
    (rows : List RowAddr) (scope : ValidationRelevanceScope) : Option Verdict := do
  let operand : SurfaceGroupListOperand :=
    .starredGroup (absoluteSource false true true)
  let checked ←
    (CheckedValidationCondition.fromGroupList
      model amount.groupPath operator [operand]).toOption
  let leaf ← match checked.core with
    | .leaf leaf => some leaf
    | _ => none
  let scalar := model.checkContext { read := fun _ => .empty }
  let result ← leaf.evalAddressedPartial? {
      scalar := {
        fields := scalar
        groups := GroupPresenceContext.unavailable }
      outer := []
      input := .legacy (document rows) (fun _ field => scalar.read field)
    } scope (fun _ => true)
      (fun _ _ => .error (.checkedDocumentRequired [])) none
  result.toOption

private def countResultOf (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option FilledGroupCount :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.numberOfFilledGroups (document rows) outer with
      | .ok result => some result
      | .error _ => none

private def contextErrorOf (source : SurfaceStarGroupPath) (rows : List RowAddr)
    (outer : Env := []) : Option StarAddressingError :=
  match checkedOf source with
  | .error _ => none
  | .ok checked =>
      match checked.rowCount (document rows) outer with
      | .ok _ => none
      | .error error => some error

private def oneEmptyItem : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 20, path := [1, 1] }]

private def nestedRows : List RowAddr :=
  [{ group := 20, path := [2, 1] }, { group := 10, path := [2] },
    { group := 20, path := [1, 2] }, { group := 10, path := [1] },
    { group := 20, path := [1, 1] }]

private def fourItemRows : List RowAddr :=
  [{ group := 10, path := [1] },
    { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
    { group := 20, path := [1, 3] }, { group := 20, path := [1, 4] }]

private def onlyItem (row : Nat) : ValidationRelevanceScope :=
  .partialSet [{
    path := items.path
    indices := [.all, .all, .concrete 1, .concrete row]
  }]

/- Checked lowering retains the terminal group and the exact first-star plan. -/
example :
    resultOf (relativeSource false true) = some (20,
      { axes := [{ level := 10, repeatability := some 2 },
          { level := 20, repeatability := some 3 }], firstStar := 1 }) ∧
    resultOf (relativeSource true true) = some (20,
      { axes := [{ level := 10, repeatability := some 2 },
          { level := 20, repeatability := some 3 }], firstStar := 0 }) := by
  native_decide

/- Partial validation restricts the threshold pair to relevant in-capacity rows. A selected
   in-capacity empty row is structural content; selecting only the over-limit row or no group row
   leaves the operand unavailable rather than turning the empty-domain predicate on. -/
example :
    partialOutcomeOf .atLeastOneGroupFilled fourItemRows (onlyItem 2) =
      some (.fired .value) ∧
    partialOutcomeOf .noGroupFilled fourItemRows (onlyItem 2) =
      some .unknown ∧
    partialOutcomeOf .atLeastOneGroupFilled fourItemRows (onlyItem 4) =
      some .unknown ∧
    partialOutcomeOf .noGroupFilled fourItemRows (onlyItem 4) =
      some .unknown ∧
    partialOutcomeOf .atLeastOneGroupFilled fourItemRows (.partialSet []) =
      some .unknown ∧
    partialOutcomeOf .noGroupFilled fourItemRows (.partialSet []) =
      some .unknown := by
  native_decide

/- A created-but-empty terminal row is structural content: no cell read is involved. -/
example :
    countOf (absoluteSource false true true) [] = some 0 ∧
    countOf (absoluteSource false true true) oneEmptyItem = some 1 ∧
    outcomeOf .noGroupFilled (absoluteSource false true true) [] =
      some (.fired .omission) ∧
    outcomeOf .noGroupFilled (absoluteSource false true true) oneEmptyItem =
      some .falseOrUnknown ∧
    outcomeOf .atLeastOneGroupFilled (absoluteSource false true true) [] =
      some .falseOrUnknown ∧
    outcomeOf .atLeastOneGroupFilled (absoluteSource false true true) oneEmptyItem =
      some (.fired .value) := by
  native_decide

/- Repeated starred operands remain two authored occurrences. Truth is idempotent, but
   zero-row `NoGroupFilled` still fires with OMISSION while the positive form stays
   UNKNOWN; a created row makes the positive form fire with VALUE. -/
example :
    repeatedOutcomeOf .noGroupFilled [] =
        some (2, .fired .omission) ∧
      repeatedOutcomeOf .atLeastOneGroupFilled [] =
        some (2, .unknown) ∧
      repeatedOutcomeOf .atLeastOneGroupFilled oneEmptyItem =
        some (2, .fired .value) := by
  native_decide

/- The numeric consumer agrees with the structural row count in the in-capacity zero- and one-row cases. -/
example :
    countResultOf (absoluteSource false true true) [] = some (.value 0) ∧
    countResultOf (absoluteSource false true true) oneEmptyItem = some (.value 1) := by
  native_decide

/- Reopening both levels counts every terminal row in canonical topology, independent of storage order. -/
example :
    countOf (absoluteSource false true true) nestedRows = some 3 ∧
    countResultOf (absoluteSource false true true) nestedRows = some (.value 3) := by
  native_decide

/- Binding the outer level before reopening the terminal group counts only that parent's rows. -/
example :
    countOf (relativeSource false true) nestedRows [(10, 1)] = some 2 ∧
    countOf (relativeSource false true) nestedRows [(10, 2)] = some 1 := by
  native_decide

/- The physical topology retains sequential over-limit rows, while the semantic count excludes them from its evaluation domain. -/
example :
    let rows := [{ group := 10, path := [1] },
      { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
      { group := 20, path := [1, 3] }, { group := 20, path := [1, 4] }]
    countOf (absoluteSource false true true) rows = some 4 ∧
      countResultOf (absoluteSource false true true) rows = some (.value 3) := by
  native_decide

/- A terminal repeatable row cannot separate the capacity accounts through a sparse topology:
   instantiated rows at one level must form a prefix. The independently measured descendant-only
   carrier in `StarredGroupPresence` settles the semantic extent without weakening this invariant. -/
example :
    let onlyOverLimitRow := [{ group := 10, path := [1] }, { group := 20, path := [1, 4] }]
    contextErrorOf (absoluteSource false true true) onlyOverLimitRow =
      some (.nonprefixRows 20 [1] [4]) := by
  native_decide

/- Static and runtime topology failures remain fail-closed at their existing owners. -/
example :
    errorOf (absoluteSource true true true) =
      some (.path (.wildcardOnNonrepeatable ["Shop", "Catalog"])) ∧
    errorOf (relativeSource true false) =
      some (.path (.iterationBelowWildcard ["Shop", "Catalog", "Sections", "Items"])) ∧
    errorOf (relativeSource false false) =
      some (.path (.missingWildcard items.path)) ∧
    errorOf (absoluteSource false false true)
      { fields := [], repeatableGroups := [sections] } =
      some (.resolve (.unknownRepeatableGroup items.path)) := by
  native_decide

/- The two dead-branch theorems are not vacuous claims that lowering always succeeds: base
   resolution still rejects an empty group reference and an unnamed segment, and those
   rejections are the only shapes it can produce. -/
example :
    errorOf { base := .absolute, groups := [] } =
      some (.invalidGroupReference { base := .absolute, groups := [] }) ∧
    errorOf { base := .absolute, groups := [segment "Shop", segment ""] } =
      some (.invalidGroupReference
        { base := .absolute, groups := [segment "Shop", segment ""] }) := by
  native_decide

/- Caller-context invalidity remains distinct from an invalid group operand for both path bases. -/
example :
    errorFromDeclaringGroup [] (absoluteSource false true true) =
      some (.resolve (.invalidRuleGroup [])) ∧
    errorFromDeclaringGroup [] (relativeSource true true) =
      some (.resolve (.invalidRuleGroup [])) := by
  native_decide

example :
    let rows := [{ group := 10, path := [1] }, { group := 20, path := [1, 2] }]
    contextErrorOf (absoluteSource false true true) rows =
      some (.nonprefixRows 20 [1] [2]) := by
  native_decide

/- A group operand naming a group whose **subtree contains no field** is refused. The Kernel admits the
empty group in the model, then reports `MVK_GROUP_IS_EMPTY` for every operand that names it; only a
repeatable one is expressible here, because `FlatModel` represents a nonrepeatable group solely through
its fields. The populated sibling is the control that keeps the refusal from being an artifact of the
model rather than of the group. -/
example :
    (elaborateStarredGroupSource hollowModel amount.groupPath
        { base := .absolute
          groups := [segment "Shop", segment "Catalog", segment "Hollow" true] }
      |> errorOfStarredGroup) = some (.groupHasNoFields ["Shop", "Catalog", "Hollow"]) ∧
      (elaborateStarredGroupSource hollowModel amount.groupPath
          (absoluteSource false true true)).toOption.isSome = true := by
  native_decide

end A12Kernel.Conformance.StarGroupElaboration
