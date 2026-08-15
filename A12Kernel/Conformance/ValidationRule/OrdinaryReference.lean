import A12Kernel.Conformance.ValidationRule.OrdinarySupport
import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # A12Kernel.Conformance.ValidationRule.OrdinaryReference — structural reference locks

The separating axis is **coordinate assignment**: one condition holds an unstarred operand bound
by the rule's iteration scope beside a starred operand that reopens a deeper level, so a rule that
wildcarded everything and a rule that wildcarded nothing both fail here. The retained list order is
authored traversal order and carries no kernel claim.
-/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryReference

open A12Kernel A12Kernel.Conformance.ValidationRule.OrdinarySupport

/-- `OuterAmount + Sum(/Order/Sections/Items*/InnerAmount) > 5`, iterating `/Order/Sections`. -/
private def mixedReferences? (environment : Env) :
    Option (List MessagePointer) := do
  let rule ← outerWithInnerAggregateRule?
  (rule.condition.core.referencePointers environment).toOption

private def mixedReferenceError? (environment : Env) :
    Option ReferenceProjectionError := do
  let rule ← outerWithInnerAggregateRule?
  match rule.condition.core.referencePointers environment with
  | .error error => some error
  | .ok _ => none

/- The bound level stays concrete on both operands; only the level the star reopened is wildcard. -/
example :
    mixedReferences? [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- The concrete coordinate tracks the firing row, so the projection is per-instance rather than
   per-declaration. -/
example :
    mixedReferences? [(10, 1)] = some [
      { field := outerAmount.id, coordinates := [.concrete 1] },
      { field := innerAmount.id, coordinates := [.concrete 1, .wildcard] }] := by
  native_decide

/- An environment that does not bind the rule's own level fails closed at that exact level instead
   of inventing an unknown or first-row coordinate. -/
example : mixedReferenceError? [] = some (.binding (.missingBinding 10)) := by
  native_decide

private def conditionReferences?
    (condition : Option (CheckedValidationCondition ordinaryIterationModel))
    (environment : Env) : Option (List MessagePointer) := do
  let checked ← condition
  (checked.core.referencePointers environment).toOption

private def conditionReferenceError?
    (condition : Option (CheckedValidationCondition ordinaryIterationModel))
    (environment : Env) : Option ReferenceProjectionError := do
  let checked ← condition
  match checked.core.referencePointers environment with
  | .error error => some error
  | .ok _ => none

private def comparisonCondition?
    (comparison : Option (CheckedOrderedNumericComparison ordinaryIterationModel)) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let checked ← comparison
  (CheckedValidationCondition.fromOrderedNumeric checked).toOption

/- `FirstFilledValue` references every authored slot. The projection has no document argument at
   all, so no operand can be dropped for having been superseded at runtime. -/
example :
    conditionReferences? (comparisonCondition? outerWithInnerFirstFilledComparison?)
        [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- A nonrepeatable reference beside a starred one carries no coordinates rather than a padded or
   wildcarded slot. -/
example :
    (mixedDirectStarNumberSource?.bind fun source =>
      conditionReferences?
        (comparisonCondition? (outerWithInnerEntityComparison? (.aggregate .sum source) 5))
        [(10, 2)]) = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := baseAmount.id, coordinates := [] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- A reached filter refuses the whole projection instead of returning the star pointer alone. An
   incomplete set that looks complete is the failure this boundary exists to prevent. -/
example :
    conditionReferenceError?
        (comparisonCondition? outerWithFilteredInnerFirstFilledComparison?) [(10, 2)] =
      some .filteredStarOperand := by
  native_decide

/- Both connectives contribute every branch and the union is deduplicated once, so a repeated
   operand does not repeat its pointer. -/
example :
    conditionReferences?
        (do
          let condition ← comparisonCondition? outerWithInnerAggregateComparison?
          (condition.and condition).toOption)
        [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/-! ## Starred group operands

A starred group never yields a group pointer. It expands to its descendant fields, and the same one
coordinate rule applies to each: concrete for the levels the rule's iteration scope bound, wildcard
from the reopened level down. Both terminals are exercised because the two carry different scope
lengths, and each chosen group has exactly one descendant field so the expected set stays exact.
-/

/-- `/Order/Sections/Notes*` — repeatable terminal, one descendant field at scope `[10, 30]`. -/
private def notesGroupStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections" },
      { name := "Notes", starred := true }] }

/-- `/Order/Sections*/Details` — nonrepeatable terminal below the outermost star, one descendant
    field at scope `[10]`. -/
private def detailsGroupStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections", starred := true },
      { name := "Details" }] }

private def groupListCondition? (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromGroupList ordinaryIterationModel ["Order"]
    operator operands).toOption

example :
    conditionReferences? (groupListCondition? .atLeastOneGroupFilled [notesGroupStar])
      [(10, 2)] = some [
      { field := siblingDate.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- A star at the outermost repeatable level leaves nothing concrete, and the nonrepeatable terminal
   contributes no coordinate of its own. -/
example :
    conditionReferences? (groupListCondition? .atLeastOneGroupFilled [detailsGroupStar])
      [] = some [{ field := sectionDetail.id, coordinates := [.wildcard] }] := by
  native_decide

/- A fixed field beside a starred group keeps its own concrete projection. `AllGroupsFilled` is not
   available here: the accepted operator-sensitivity rule rejects a starred operand under it. -/
example :
    conditionReferences? (groupListCondition? .atLeastOneGroupFilled
        [.field (ordinaryPath ["Order"] "BaseAmount"), notesGroupStar]) [(10, 2)] = some [
      { field := baseAmount.id, coordinates := [] },
      { field := siblingDate.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/-- `/Order/Sections*` — the recursion witness. Its descendants span three deeper groups, two of
    them repeatable, so direct-child expansion and recursive expansion disagree here. -/
private def sectionsGroupStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [{ name := "Order" }, { name := "Sections", starred := true }] }

/- Expansion is recursive, and each descendant's coordinate count comes from its **own** scope: a
   field declared in the starred group carries one wildcard, one declared in a deeper repeatable
   descendant carries two. The exact cardinality pins that nothing beyond the subtree joins. -/
example :
    (conditionReferences? (groupListCondition? .atLeastOneGroupFilled [sectionsGroupStar])
      []).map (fun pointers =>
        (pointers.contains { field := outerAmount.id, coordinates := [.wildcard] },
          pointers.contains
            { field := siblingDate.id, coordinates := [.wildcard, .wildcard] },
          pointers.length)) = some (true, true, 14) := by
  native_decide

/-- A presence guard on the iterating row's own field: an ordinary leaf this fragment does not
    classify. -/
private def outerPresenceGuard? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order", "Sections"] .filled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

/- An ordinary non-starred repeatable presence reference is bound by the rule's iteration scope, so
   it is concrete at the firing row. -/
example :
    conditionReferences? outerPresenceGuard? [(10, 2)] =
      some [{ field := outerAmount.id, coordinates := [.concrete 2] }] := by
  native_decide

/- The guard's reference merges with the guarded leaf's rather than appearing twice: this is the
   standard iteration-guard rule shape, projected end to end. -/
example :
    conditionReferences?
        (do
          let guard ← outerPresenceGuard?
          let aggregate ← comparisonCondition? outerWithInnerAggregateComparison?
          (guard.and aggregate).toOption)
        [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/-! ## Flat leaves

The flat fragment carries no starred operand, so its own exhaustive `referencesField` can supply
membership and every reference is concretely addressed by the rule's environment. -/

private def flatCondition? (condition : SurfaceCondition) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let checked ← (elaborate ordinaryIterationModel ["Order"] condition).toOption
  (CheckedValidationCondition.fromFlat checked).toOption

/- Both connective branches and both presence polarities contribute; nonrepeatable references carry
   no coordinates. -/
example :
    conditionReferences?
        (flatCondition? (.and (.fieldFilled (ordinaryPath ["Order"] "BaseAmount"))
          (.fieldNotFilled (ordinaryPath ["Order"] "BaseToken")))) [] = some [
      { field := baseAmount.id, coordinates := [] },
      { field := baseToken.id, coordinates := [] }] := by
  native_decide

/- A group presence operand over a *repeatable* group is classified, but its subtree fields need a
   level the rule does not bind, and the projection fails closed at that exact level. This is the
   arm the wildcard rule below does **not** reach, and the distinction is the operand's own level:
   every measured row has a nonrepeatable operand, so the wildcarding begins strictly inside its
   subtree. Whether a *repeatable* operand's own level wildcards instead of binding has no witness,
   so the depth stays at the whole scope of the authored path and this shape keeps failing closed
   rather than gaining an invented coordinate. -/
example :
    conditionReferenceError? innerGroupFilledCondition? [(10, 2)] =
      some (.binding (.missingBinding 20)) := by
  native_decide

/-! ## Scalar atoms inside the addressed numeric leaf

The model-indexed leaf delegates every scalar atom unchanged, so the same sievability test applies
to it — but under addressed admission a delegated declaration may be **repeatable**, bound by the
rule's own iteration scope rather than nonrepeatable. These are the first classified numeric
references that carry a coordinate at all. -/

/- One UTF-16 `Length` atom over a doubly nested declaration: both levels are fixed by the rule's
   scope, so both coordinates are concrete and neither is wildcard. -/
example :
    conditionReferences? (repeatableStringLengthCondition? (.ordinary .equal) 3)
      [(10, 2), (20, 1)] =
      some [{ field := innerToken.id, coordinates := [.concrete 2, .concrete 1] }] := by
  native_decide

/- A two-field atom contributes both operands. Their authored order is reversed here, so this also
   pins that sieved membership retains declaration order and claims nothing about position. -/
example :
    conditionReferences?
        (repeatableDateDifferenceCondition? .months "InnerEarlierDate" "InnerDate"
          (.ordinary .equal) 1) [(10, 2), (20, 1)] = some [
      { field := innerDate.id, coordinates := [.concrete 2, .concrete 1] },
      { field := innerEarlierDate.id, coordinates := [.concrete 2, .concrete 1] }] := by
  native_decide

/- A category-projected conversion references the **declaring** field, not a projection-specific
   identity: the atom's own predicate supplies membership, so no second addressing notion appears. -/
example :
    conditionReferences?
        (repeatableFieldValueAsNumberCondition? repeatableNumericFactor
          (.ordinary .equal) 15) [(10, 2), (20, 1)] =
      some [{
        field := innerNumericChoice.id
        coordinates := [.concrete 2, .concrete 1] }] := by
  native_decide

/-! ### The leaf's own checked sources

Each retains its own operand type rather than the Number entity operand, and two of the three carry
their filter as an `Option` field instead of a distinct constructor — so the filtered-star refusal
has to be made again per family, not inherited. -/

private def tokenValueCountCondition?
    (source? : Option (CheckedTokenValueCountSource ordinaryIterationModel)) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let source ← source?
  let comparison ← checkedOuterEntityComparison? {
    op := .ordinary .greater
    left := .atom (.tokenValueCount source)
    right := .literal { value := 2, authoredScale := 0 } }
  (CheckedValidationCondition.fromOrderedNumeric comparison).toOption

/- A projection-bearing token operand references its **declaring** field: `MessagePointer` has no
   projection slot, and the channel reports field instances. -/
example :
    conditionReferences? (tokenValueCountCondition? plainStarTokenValueCountSource?)
      [(10, 2)] =
      some [{ field := innerToken.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- A direct operand beside a starred one keeps the split assignment inside this family too. -/
example :
    conditionReferences? (tokenValueCountCondition? mixedTokenValueCountSource?)
      [(10, 2)] = some [
      { field := baseToken.id, coordinates := [] },
      { field := innerToken.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

private def filteredTokenValueCountSource? :
    Option (CheckedTokenValueCountSource ordinaryIterationModel) :=
  (elaborateTokenValueCountSource ordinaryIterationModel ["Order", "Sections"] "A" {
    first := .starHaving deeperInnerTokenStar .stored innerAmountSelfHaving
    rest := [] }).toOption

/- The optional-filter representation must not let a filtered star through where the Number entity
   operand's distinct constructor is refused. Both refuse. -/
example :
    conditionReferenceError? (tokenValueCountCondition? filteredTokenValueCountSource?)
      [(10, 2)] = some .filteredStarOperand := by
  native_decide

/- A row-paired product references both starred value fields. Its certificate forces one shared
   path, so the two pointers differ only in field identity. -/
example :
    conditionReferences? (plainStarProductCondition? (.ordinary .greater) 5)
      [(10, 2)] = some [
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] },
      { field := innerPrice.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/-! ## Non-model-indexed numeric leaves

The scalar numeric fragment carries no starred operand either — every field-bearing atom holds a
resolved single-field declaration, a fixed Number field list, or a fixed group reference whose
resolution rejects both the starred `RuleGroup` and a repeatable ordinary path — so it is sieved
through its own exhaustive `referencesField` on the same terms as the flat fragment. -/

private def numericCondition? (surface : SurfaceNumericComparison) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let checked ←
    (elaborateNumericComparison ordinaryIterationModel ["Order"] surface).toOption
  (CheckedValidationCondition.fromNumeric checked).toOption

/- Both comparison sides contribute and two different atom kinds reach the same membership
   predicate. The retained order is **declaration** order, which the authored order reverses here:
   sieving cannot preserve authored position, and the projection claims none. -/
example :
    conditionReferences?
        (numericCondition? {
          op := .ordinary .greater
          left := .atom (.stringLength (ordinaryPath ["Order"] "BaseToken"))
          right := .atom (.field (ordinaryPath ["Order"] "BaseAmount")) }) [] = some [
      { field := baseAmount.id, coordinates := [] },
      { field := baseToken.id, coordinates := [] }] := by
  native_decide

/- A context-free atom neither contributes a reference nor refuses the projection. `BaseYear` reads
   no cell, so the sieve must report exactly the one field atom beside it. -/
example :
    conditionReferences?
        (numericCondition? {
          op := .ordinary .greater
          left := .atom (.field (ordinaryPath ["Order"] "BaseAmount"))
          right := .atom (.baseYear) }) [] =
      some [{ field := baseAmount.id, coordinates := [] }] := by
  native_decide

/-! ### Shapes the shared iteration model cannot express

`ordinaryIterationModel` cannot author a fixed group count, because every group there is either the
model root or inside a repeatable scope while a count needs at least two non-root operands of which
at most one may be the `RuleGroup` keyword; it declares no Boolean field, so the Boolean value count
has no operand; and it has no nonrepeatable group at all, so no unstarred group operand can be
exercised. This fixture supplies all three. Its group shape deliberately mirrors the measured kernel
model: one fixed group holding two fields plus a **deeper** nonrepeatable descendant group, and a
disjoint second fixed group. -/

private def fixedAmount : FlatFieldDecl :=
  { id := 60
    groupPath := ["Count", "Fixed"]
    name := "FixedAmount"
    policy := { kind := .number { scale := 0, signed := true } } }

/-- Declared inside a repeatable group, which is what makes the refusal load-bearing: `RuleGroup` is
    the one count operand that may bind a *repeatable* instance, so adopting the count's arm of the
    predicate would have projected a concrete coordinate for a subtree expansion no measurement
    covers. -/
private def rowAmount : FlatFieldDecl :=
  { id := 61
    groupPath := ["Count", "Rows"]
    name := "RowAmount"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [50] }

private def rowFlag : FlatFieldDecl :=
  { id := 62
    groupPath := ["Count", "Rows"]
    name := "RowFlag"
    policy := { kind := .boolean }
    repeatableScope := [50] }

/-- The recursion witness: declared one nonrepeatable group deeper than the counted one, so
    direct-child expansion and recursive expansion disagree on this field alone. -/
private def deepAmount : FlatFieldDecl :=
  { id := 63
    groupPath := ["Count", "Fixed", "Deep"]
    name := "DeepAmount"
    policy := { kind := .number { scale := 0, signed := true } } }

private def otherAmount : FlatFieldDecl :=
  { id := 64
    groupPath := ["Count", "Other"]
    name := "OtherAmount"
    policy := { kind := .number { scale := 0, signed := true } } }

/-- The coordinate witness: a **nonrepeatable** group operand holding one direct field and a
    *repeatable* subgroup. Nothing in a condition over it is starred, so whatever coordinate its
    nested field carries is a property of the model's repeatability alone. This is the shape the
    kernel measurement uses, and the only one that separates the two coordinate accounts. -/
private def nestAmount : FlatFieldDecl :=
  { id := 65
    groupPath := ["Count", "Nest"]
    name := "NestAmount"
    policy := { kind := .number { scale := 0, signed := true } } }

private def runAmount : FlatFieldDecl :=
  { id := 66
    groupPath := ["Count", "Nest", "Runs"]
    name := "RunAmount"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [51] }

private def countModel : FlatModel :=
  { fields := [fixedAmount, rowAmount, rowFlag, deepAmount, otherAmount,
      nestAmount, runAmount]
    repeatableGroups := [
      { level := 50, path := ["Count", "Rows"], repeatability := some 2 },
      { level := 51, path := ["Count", "Nest", "Runs"], repeatability := some 2 }] }

/-- `NumberOfFilledGroups(RuleGroup, /Count/Fixed) > 0` at the repeatable `/Count/Rows`. -/
private def ruleGroupCountSurface : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.filledGroupCount [
      .ruleGroup false,
      .path { base := .absolute, groups := ["Count", "Fixed"] }])
    right := .literal { value := 0, authoredScale := 0 } }

private def countReferences? (environment : Env) :
    Option (List MessagePointer) := do
  let checked ←
    (elaborateNumericComparison countModel ["Count", "Rows"]
      ruleGroupCountSurface).toOption
  let condition ← (CheckedValidationCondition.fromNumeric checked).toOption
  (condition.core.referencePointers environment).toOption

/- Each counted subtree contributes every field below it, and the shared coordinate rule still reads
   each reference's own scope: the repeatable `RuleGroup` subtree is concrete at the firing row while
   the fixed co-operand's fields carry no coordinate. `DeepAmount` is the recursion witness. -/
example :
    countReferences? [(50, 2)] = some [
      { field := fixedAmount.id, coordinates := [] },
      { field := rowAmount.id, coordinates := [.concrete 2] },
      { field := rowFlag.id, coordinates := [.concrete 2] },
      { field := deepAmount.id, coordinates := [] }] := by
  native_decide

/-! ### Unstarred group operands

Measured recursive expansion, identical in the presence, entity-list, and count positions. One depth
rule serves both repetition shapes: repeatable levels **above** the operand stay concrete at the
firing row, every level at or below it is **wildcarded**. An unstarred operand's own level is
non-repeatable by the wildcard gate, so what the two forms actually differ in is where that boundary
falls, not whether one wildcards at all.

The `/Count/Nest` rows are the separating ones — a nonrepeatable operand whose subtree crosses a
repeatable level. Measured at a12-dmkits `bffe9cca`, where `/Shipment/Carrier` reaches
`/Shipment[1]/Carrier[1]/Handoffs[0]/Site` beside `/Shipment[1]/Carrier[1]/Name`: one wildcard, one
bare. Before that row this projection failed closed at the crossed level rather than choosing between
a wildcard and a pin. -/

private def groupPresenceReferences? (groups : GroupPath) (rowGroup : GroupPath)
    (environment : Env) : Option (List MessagePointer) := do
  let condition ← (CheckedValidationCondition.fromGroupPresence countModel rowGroup
    (.path { base := .absolute, groups }) .filled).toOption
  (condition.core.referencePointers environment).toOption

/- The single-operand presence position expands recursively and never yields a group pointer. -/
example :
    groupPresenceReferences? ["Count", "Fixed"] ["Count"] [] = some [
      { field := fixedAmount.id, coordinates := [] },
      { field := deepAmount.id, coordinates := [] }] := by
  native_decide

/- The separating row: the direct field carries no coordinate while the field below the repeatable
   subgroup carries a wildcard, from one operand and one projection. The empty environment is the
   point — a concrete account would have to read a level the rule does not bind. -/
example :
    groupPresenceReferences? ["Count", "Nest"] ["Count"] [] = some [
      { field := nestAmount.id, coordinates := [] },
      { field := runAmount.id, coordinates := [.wildcard] }] := by
  native_decide

private def fixedGroupListReferences? (environment : Env) :
    Option (List MessagePointer) := do
  let condition ← (CheckedValidationCondition.fromGroupList countModel ["Count"]
    .atLeastOneGroupFilled [
      .group (.path { base := .absolute, groups := ["Count", "Fixed"] }),
      .group (.path { base := .absolute, groups := ["Count", "Other"] })]).toOption
  (condition.core.referencePointers environment).toOption

private def nestedGroupListReferences? (environment : Env) :
    Option (List MessagePointer) := do
  let condition ← (CheckedValidationCondition.fromGroupList countModel ["Count"]
    .atLeastOneGroupFilled [
      .group (.path { base := .absolute, groups := ["Count", "Nest"] }),
      .group (.path { base := .absolute, groups := ["Count", "Other"] })]).toOption
  (condition.core.referencePointers environment).toOption

/- The entity-list position adds the disjoint operand's subtree and nothing else. -/
example :
    fixedGroupListReferences? [] = some [
      { field := fixedAmount.id, coordinates := [] },
      { field := deepAmount.id, coordinates := [] },
      { field := otherAmount.id, coordinates := [] }] := by
  native_decide

/- The same depth rule in the entity-list position, which is what "identical in all three positions"
   has to mean if it means anything: swapping the disjoint operand for the nested one changes the
   coordinate and nothing else. -/
example :
    nestedGroupListReferences? [] = some [
      { field := nestAmount.id, coordinates := [] },
      { field := runAmount.id, coordinates := [.wildcard] },
      { field := otherAmount.id, coordinates := [] }] := by
  native_decide

/-- `RepetitionNotUnique` is the one leaf family still outside the fragment, so it carries the
    refusal guard that a classified `groupPresence` no longer can. -/
private def countRepetitionNotUniqueError? (environment : Env) :
    Option ReferenceProjectionError := do
  let condition ← (CheckedValidationCondition.fromRepetitionNotUnique countModel
    ["Count"] {
      firstKey := {
        base := .absolute
        groups := ["Count", "Rows"]
        field := "RowAmount" }
      restKeys := [] }).toOption
  match condition.core.referencePointers environment with
  | .error error => some error
  | .ok _ => none

/- An unclassified leaf still fails the whole rule's projection. Silence would be read as "this rule
   references nothing", which no rule can be. -/
example : countRepetitionNotUniqueError? [] = some .unclassifiedLeaf := by
  native_decide

/- A nonrepeatable group *inside* a repeatable scope is concrete at the firing row, which is the
   measured account's discriminator against wildcarding an unstarred operand. -/
example :
    conditionReferences?
        ((CheckedValidationCondition.fromGroupPresence ordinaryIterationModel ["Order"]
          (.path { base := .absolute, groups := ["Order", "Sections", "Details"] })
          .filled).toOption) [(10, 2)] =
      some [{ field := sectionDetail.id, coordinates := [.concrete 2] }] := by
  native_decide

/-- `NumberOfTrueValues(/Count/Rows*/RowFlag) > 0`, iterating the model root. -/
private def booleanCountReferences? (environment : Env) :
    Option (List MessagePointer) := do
  let source ← (elaborateBooleanValueCountSource countModel ["Count"] true {
    first := .star {
      base := .absolute
      groups := [{ name := "Count" }, { name := "Rows", starred := true }]
      field := "RowFlag" }
    rest := [] }).toOption
  let core : OrderedNumericComparison countModel := {
    op := .ordinary .greater
    left := .atom (.booleanValueCount source)
    right := .literal { value := 0, authoredScale := 0 } }
  if hCore : core.wellFormedInBool ["Count"] .sameGroupAddressed = true then do
    let condition ← (CheckedValidationCondition.fromOrderedNumeric {
      rowGroup := ["Count"]
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := by native_decide
      wellFormed := hCore }).toOption
    (condition.core.referencePointers environment).toOption
  else
    none

/- The Boolean companion's fixed canonical-token projection is as invisible to a reference as the
   token projection is: only the declaring field instance is reported. -/
example :
    booleanCountReferences? [] =
      some [{ field := rowFlag.id, coordinates := [.wildcard] }] := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryReference
