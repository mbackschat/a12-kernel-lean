import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.RepeatableNumberFixedGroupCountComputation
import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Elaboration.ValidationRule

/-! # Fixed groups below a bound repeatable ancestor

These cases mirror the retained Kernel carrier matrix. One checked scope certificate feeds the
group-scope filled-field count, group-list predicate, numeric validation count, and repeatable
Number computation; the two documents swap the full operand set between enclosing rows and reject a
cross-row union.
-/

namespace A12Kernel.Conformance.FixedGroupRepeatableAncestorCarriers

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def flatA : FlatFieldDecl := {
  id := 1
  groupPath := ["Probe", "Outer", "Flat"]
  name := "FlatA"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def rowR : FlatFieldDecl := {
  id := 2
  groupPath := ["Probe", "Outer", "Flat", "Rows"]
  name := "RowR"
  policy := { kind := .string }
  repeatableScope := [10, 20]
}

private def peerA : FlatFieldDecl := {
  id := 3
  groupPath := ["Probe", "Outer", "Peer"]
  name := "PeerA"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def marker : FlatFieldDecl := {
  id := 4
  groupPath := ["Probe", "Outer"]
  name := "Marker"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def countTarget : FlatFieldDecl := {
  id := 5
  groupPath := ["Probe", "Outer"]
  name := "CountTarget"
  policy := { kind := .number unsigned }
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [flatA, rowR, peerA, marker, countTarget]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Outer"], repeatability := some 2 },
    { level := 20, path := ["Probe", "Outer", "Flat", "Rows"],
      repeatability := some 2 }]
}

private def scalarA : FlatFieldDecl := {
  id := 6
  groupPath := ["Probe", "Scalar"]
  name := "ScalarA"
  policy := { kind := .string }
}

private def deepA : FlatFieldDecl := {
  id := 7
  groupPath := ["Probe", "Outer", "Flat", "Rows", "Deep"]
  name := "DeepA"
  policy := { kind := .string }
  repeatableScope := [10, 20]
}

private def boundaryModel : FlatModel := {
  fields := model.fields ++ [scalarA, deepA]
  repeatableGroups := model.repeatableGroups
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def fixedGroup (path : GroupPath) : SurfaceGroupReference :=
  .path { base := .absolute, groups := path }

private def flat : SurfaceGroupReference :=
  fixedGroup ["Probe", "Outer", "Flat"]

private def peer : SurfaceGroupReference :=
  fixedGroup ["Probe", "Outer", "Peer"]

private def surfaces : List SurfaceGroupReference := [flat, peer]

private def groupList? : Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromGroupList model ["Probe", "Outer"]
    .allGroupsFilled
    (surfaces.map fun reference => SurfaceGroupListOperand.group reference)).toOption

private def countComparison : SurfaceNumericComparison := {
  op := .ordinary .equal
  left := .atom (.filledGroupCount
    (surfaces.map SurfaceGroupCountOperand.fixed))
  right := .literal { value := 2, authoredScale := 0 }
}

private def numericCount? : Option (CheckedValidationCondition model) := do
  let checked ←
    (elaborateRepeatableNumericComparison model ["Probe", "Outer"]
      countComparison).toOption
  (CheckedValidationCondition.fromOrderedNumeric checked).toOption

private def groupListRule? : Option (CheckedResolvedValidationRule model) := do
  let condition ← groupList?
  (assembleResolvedValidationRule model condition flatA.id "fixedAncestor" .error
    { parts := [] }).toOption

private def scalarGroupListRuleEvalRefused : Bool :=
  match groupListRule? with
  | none => false
  | some rule =>
      match rule.evalFull prepared "en_US" { read := fun _ => .empty }
          GroupPresenceContext.unavailable true with
      | .error .addressedContextRequired => true
      | _ => false

private def fieldCount? : Option (CheckedFilledFieldCountGroupSource model) :=
  (elaborateFilledFieldCountFixedGroupValidationSource model ["Probe", "Outer"] {
    group := { base := .absolute, groups := ["Probe", "Outer", "Flat"] }
  }).toOption

private def computation? :
    Option (CheckedRepeatableNumberFixedGroupCountComputation model) :=
  (checkRepeatableNumberFixedGroupCountComputation model ["Probe", "Outer"]
    countTarget.id surfaces).toOption

private def refusesAt (declaringGroup path : GroupPath) : Bool :=
  match model.resolveRuleBoundFixedGroupReference declaringGroup (fixedGroup path) with
  | .error (.repeatableGroupRequiresAddress actual) => actual == path
  | _ => false

private def boundaryRefusesAt (declaringGroup path : GroupPath) : Bool :=
  match boundaryModel.resolveRuleBoundFixedGroupReference declaringGroup
      (fixedGroup path) with
  | .error (.repeatableGroupRequiresAddress actual) => actual == path
  | _ => false

private def scalarScope? : Option (List RepeatableLevel) := do
  let reference ← (boundaryModel.resolveRuleBoundFixedGroupReference
    ["Probe", "Outer"] (fixedGroup ["Probe", "Scalar"])).toOption
  pure reference.boundRepeatableScope

private def defaultResolverRefusesBoundChild : Bool :=
  match model.resolveFixedGroupReference ["Probe", "Outer"] flat with
  | .error (.repeatableGroupRequiresAddress path) =>
      path == ["Probe", "Outer", "Flat"]
  | _ => false

private def scalarComputationRefused : Bool :=
  match checkRepeatableNumberFixedGroupCountComputation boundaryModel
      ["Probe", "Outer"] countTarget.id
      [flat, fixedGroup ["Probe", "Scalar"]] with
  | .error _ => true
  | .ok _ => false

/- Every carrier retains the same exact enclosing scope. A caller outside that scope still receives
the established addressed-group refusal, and the repeatable terminal itself still requires a star. -/
example :
    (fieldCount?.map (·.source.bindingScope),
      groupList?.bind fun checked => checked.core.ordinaryIterationScope.toOption,
      numericCount?.bind fun checked => checked.core.ordinaryIterationScope.toOption,
      computation?.map fun checked => checked.groups.map (·.boundRepeatableScope),
      groupList?.map (·.core.requiresAddressedValidation),
      numericCount?.map fun checked =>
        checked.core.allLeaves ValidationConditionLeaf.supportsAddressedPartial) ==
        (some [10], some (some [10]), some (some [10]), some [[10], [10]],
          some true, some false) &&
      scalarScope? == some [] &&
      refusesAt ["Probe"] ["Probe", "Outer", "Flat"] &&
      refusesAt ["Probe", "Outer"] ["Probe", "Outer"] &&
      boundaryRefusesAt ["Probe", "Outer"]
        ["Probe", "Outer", "Flat", "Rows", "Deep"] &&
      defaultResolverRefusesBoundChild && scalarComputationRefused &&
      scalarGroupListRuleEvalRefused = true := by
  native_decide

private def cell (field : FieldId) (path : List Nat) (stored : String) :
    ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.str stored)
}

private def firstDocument? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] },
      { group := 10, path := [2] }]
    cells := [
      cell flatA.id [1] "f1",
      cell rowR.id [1, 1] "r1",
      cell peerA.id [1] "p1",
      cell flatA.id [2] "f2"]
  }).toOption

private def secondDocument? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 20, path := [2, 1] }]
    cells := [
      cell flatA.id [1] "f1",
      cell flatA.id [2] "f2",
      cell rowR.id [2, 1] "r2",
      cell peerA.id [2] "p2"]
  }).toOption

private def verdicts? (condition : CheckedValidationCondition model)
    (document : CheckedDocument model) : Option (List Verdict) :=
  [[(10, 1)], [(10, 2)]].mapM fun environment =>
    (condition.core.evalAddressedFull {
      scalar := {
        fields := document.flatContext
        groups := GroupPresenceContext.unavailable }
      outer := environment
      input := .checked document
    } true).toOption

private def fieldCounts? (document : CheckedDocument model) :
    Option (List FilledFieldCount) := do
  let checked ← fieldCount?
  [[(10, 1)], [(10, 2)]].mapM fun environment =>
    (checked.evaluateCheckedDocumentValidation document environment).toOption

private def computationOutcomes? (document : CheckedDocument model) :
    Option (List RepeatableNumberFixedGroupCountOutcome) := do
  let checked ← computation?
  (checked.execute document).toOption

private def expectedFirst : List RepeatableNumberFixedGroupCountOutcome := [
  { targetField := { field := countTarget.id, path := [1] }
    outcome := .accepted { unscaled := 2, scale := 0 } },
  { targetField := { field := countTarget.id, path := [2] }
    outcome := .accepted { unscaled := 1, scale := 0 } }]

private def expectedSecond : List RepeatableNumberFixedGroupCountOutcome := [
  { targetField := { field := countTarget.id, path := [1] }
    outcome := .accepted { unscaled := 1, scale := 0 } },
  { targetField := { field := countTarget.id, path := [2] }
    outcome := .accepted { unscaled := 2, scale := 0 } }]

/- Moving the peer content and the nested row between enclosing rows moves both validation messages
and computation values with it. A cross-row union would fire twice and compute `[2, 2]` in both
documents; the field-count pair separately locks the fixed group slot's row-local expansion. -/
example : ((do
    let groupList ← groupList?
    let numericCount ← numericCount?
    let first ← firstDocument?
    let second ← secondDocument?
    pure (verdicts? groupList first, verdicts? groupList second,
      verdicts? numericCount first, verdicts? numericCount second,
      fieldCounts? first, fieldCounts? second,
      computationOutcomes? first, computationOutcomes? second)) ==
    some (some [.fired .value, .unknown], some [.unknown, .fired .value],
      some [.fired .value, .notFired], some [.notFired, .fired .value],
      some [.value 2, .value 1], some [.value 1, .value 2],
      some expectedFirst, some expectedSecond)) = true := by
  native_decide

private def pointers? (environment : Env) : Option (List MessagePointer) := do
  let checked ← groupList?
  (checked.core.referencePointers environment).toOption

private def numericPointers? (environment : Env) : Option (List MessagePointer) := do
  let checked ← numericCount?
  (checked.core.referencePointers environment).toOption

/- Explain sees the same current outer row, while the nested descendant remains wildcarded below
the fixed child's bound scope. -/
example : (pointers? [(10, 1)], pointers? [(10, 2)]) =
    (some [
      { field := flatA.id, coordinates := [.concrete 1] },
      { field := rowR.id, coordinates := [.concrete 1, .wildcard] },
      { field := peerA.id, coordinates := [.concrete 1] }],
    some [
      { field := flatA.id, coordinates := [.concrete 2] },
      { field := rowR.id, coordinates := [.concrete 2, .wildcard] },
      { field := peerA.id, coordinates := [.concrete 2] }]) := by
  native_decide

/- The numeric-count leaf uses the same fixed-group projection, including the nested wildcard. -/
example : (numericPointers? [(10, 1)], numericPointers? [(10, 2)]) =
    (pointers? [(10, 1)], pointers? [(10, 2)]) := by
  native_decide

end A12Kernel.Conformance.FixedGroupRepeatableAncestorCarriers
