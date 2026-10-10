import A12Kernel.Elaboration.ValidationRule

namespace A12Kernel.Conformance.PartialGroupList

open A12Kernel

private def model (capacity : Nat) : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form"], name := "Anchor", policy := { kind := .string } },
      { id := 2, groupPath := ["Form", "Fixed"], name := "N", policy := { kind := .number { scale := 0, signed := false } } },
      { id := 3, groupPath := ["Form", "Left", "Seal"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10] },
      { id := 4, groupPath := ["Form", "Left", "Seal"], name := "M",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10] },
      { id := 5, groupPath := ["Form"], name := "Key", policy := { kind := .string } },
      { id := 6, groupPath := ["Form", "Rows"], name := "Code", policy := { kind := .string },
        repeatableScope := [20] },
      { id := 7, groupPath := ["Form", "Rows"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20] },
      { id := 8, groupPath := ["Form", "Rows", "Details"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20] },
      { id := 9, groupPath := ["Form", "Rows", "Details"], name := "M",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20] },
      { id := 10, groupPath := ["Form", "Rows", "Children"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20, 30] },
      { id := 11, groupPath := ["Form"], name := "Direct",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 12, groupPath := ["Form", "Rows", "Children", "Seal"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20, 30] },
      { id := 13, groupPath := ["Form", "Rows", "Children", "Seal"], name := "M",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20, 30] },
      { id := 14, groupPath := ["Form", "Rows", "Children", "Parts"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20, 30, 40] },
      { id := 15, groupPath := ["Form", "Rows", "Children", "Parts", "Seal"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [20, 30, 40] }]
    repeatableGroups := [
      { level := 10, path := ["Form", "Left"], repeatability := some capacity },
      { level := 20, path := ["Form", "Rows"], repeatability := some 2, indexField := some 6 },
      { level := 30, path := ["Form", "Rows", "Children"], repeatability := some 2 },
      { level := 40, path := ["Form", "Rows", "Children", "Parts"], repeatability := some 2 }] }

private def fixed : SurfaceGroupListOperand :=
  .group (.path { base := .absolute, groups := ["Form", "Fixed"] })

private def starred (terminal : Bool) : SurfaceGroupListOperand :=
  .starredGroup { base := .absolute, groups :=
    [{ name := "Form" }, { name := "Left", starred := true }] ++
      if terminal then [] else [{ name := "Seal" }] }

private def every (path : GroupPath) : RelevantEntityPattern :=
  { path, indices := path.map fun _ => .all }

private def row (coordinate : Nat) : RelevantEntityPattern :=
  { path := ["Form", "Left"], indices := [.all, .concrete coordinate] }

private def numberCell (field : FieldId) (path : List Nat) (bad : Bool) : ClassifiedCellInput :=
  { address := { field, path }, stored := if bad then "bad" else "1"
    raw := if bad then .rejected .malformed else .parsed (.num 1) }

private def document (rows : Nat) (cells : List ClassifiedCellInput) : DocumentData :=
  { instantiatedRows := (List.range rows).map fun i => { group := 10, path := [i + 1] }
    cells := { address := { field := 1, path := [] }, stored := "on", raw := .parsed (.str "on") } :: cells }

private def evaluateOutcomeAtCapacity (capacity : Nat) (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) (data : DocumentData) (entities : List RelevantEntityPattern) :
    Option (Except OrdinaryRepeatableRuleEvaluationError PartialRuleOutcome) := do
  let model := model capacity
  let guard ← (elaborate model ["Form"] (.fieldFilled {
    base := .absolute, groups := ["Form"], field := "Anchor" })).toOption
  let guard ← (CheckedValidationCondition.fromFlat guard).toOption
  let predicate ← (CheckedValidationCondition.fromGroupList model ["Form"] operator operands).toOption
  let condition ← (guard.and predicate).toOption
  let rule ← (assembleResolvedValidationRule model condition 1 "probe" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  pure (rule.evalAddressedPartial checked (.partialSet (every ["Form", "Anchor"] :: entities)))

private def evaluateAtCapacity (capacity : Nat) (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) (data : DocumentData)
    (entities : List RelevantEntityPattern) : Option Verdict := do
  let .evaluated outcome ← (← evaluateOutcomeAtCapacity capacity operator operands data entities).toOption
    | none
  pure outcome.verdict

private def evaluate := evaluateAtCapacity 2

private def both (operands : List SurfaceGroupListOperand) (data : DocumentData)
    (entities : List RelevantEntityPattern) : List (Option Verdict) :=
  [.atLeastOneGroupFilled, .noGroupFilled].map fun operator => evaluate operator operands data entities

private def unknownPair : List (Option Verdict) := [some .unknown, some .unknown]
private def filledPair : List (Option Verdict) := [some (.fired .value), some .unknown]
private def emptyPair : List (Option Verdict) := [some .unknown, some (.fired .omission)]

private def direct : SurfaceGroupListOperand :=
  .field { base := .absolute, groups := ["Form"], field := "Anchor" }

private def predicates : List GroupFillQuantifier :=
  [.allGroupsFilled, .noGroupFilled, .atLeastOneGroupFilled,
    .notAllGroupsFilled, .groupsNotCollectivelyFilled]

example : predicates.map (fun operator => evaluate operator [direct, fixed]
    (document 0 [numberCell 2 [] false]) [every ["Form"]]) =
      [some (.fired .value), some .unknown, some (.fired .value),
        some .unknown, some .unknown] := by native_decide

example : predicates.map (fun operator => evaluate operator [direct, fixed]
    (document 0 []) [every ["Form"]]) =
      [some .unknown, some .unknown, some (.fired .value),
        some (.fired .omission), some (.fired .omission)] := by native_decide

example : both [starred false] (document 0 []) [] = unknownPair := by native_decide
example : both [starred false] (document 0 []) [every ["Form"]] = emptyPair := by native_decide
example : both [starred false] (document 1 []) [row 1] = unknownPair := by native_decide

example : [false, true].map (fun terminal =>
    both [starred terminal, starred terminal] (document 0 []) []) =
      [unknownPair, unknownPair] := by native_decide

example : [false, true].map (fun terminal =>
    both [starred terminal, starred terminal] (document 0 []) [every ["Form"]]) =
      [emptyPair, emptyPair] := by native_decide

example : both [starred true] (document 1 []) [every ["Form", "Left", "Seal", "N"]] =
    filledPair := by native_decide

example : [[fixed, starred false], [starred false, fixed]].map (fun operands =>
    both operands (document 1 [numberCell 2 [] false]) [every ["Form", "Fixed"]]) =
      [filledPair, filledPair] := by native_decide

example : [[fixed, starred false], [starred false, fixed]].map (fun operands =>
    both operands (document 1 [numberCell 2 [] true]) [every ["Form", "Fixed"]]) =
      [unknownPair, unknownPair] := by native_decide

example : both [starred false, starred false]
    (document 2 [numberCell 3 [1] true, numberCell 3 [2] false])
    [every ["Form"]] = filledPair := by native_decide

example : both [starred false, starred false]
    (document 2 [numberCell 3 [1] true]) [every ["Form"]] = unknownPair := by native_decide

example : both [starred false, starred false]
    (document 3 [numberCell 3 [3] false]) [every ["Form"]] = emptyPair := by native_decide

example : evaluateAtCapacity 1999999999 .atLeastOneGroupFilled [starred false]
    (document 1 [numberCell 3 [1] false]) [every ["Form", "Left", "Seal", "N"]] =
      some (.fired .value) := by native_decide

example : evaluateAtCapacity 1999999999 .noGroupFilled [starred false]
    (document 0 []) [] = some .unknown := by native_decide

example : [[fixed, starred false], [starred false, fixed]].map (fun operands =>
    evaluateAtCapacity 1999999999 .atLeastOneGroupFilled operands
      (document 0 [numberCell 2 [] false]) [every ["Form"]]) =
        [some (.fired .value), some (.fired .value)] := by native_decide

example : ValidationConditionLeaf.evalPartialGroupReaders .atLeastOneGroupFilled
    [fun () => .ok [.filled], fun () => .error (.checkedDocumentRequired [])] =
      .ok (.fired .value) := by rfl

example : ValidationConditionLeaf.evalPartialGroupReaders .noGroupFilled
    [fun () => .ok [.unavailable], fun () => .error (.checkedDocumentRequired [])] =
      .ok .unknown := by rfl

private def fieldKey : SurfaceSemanticIndexKey :=
  .field { base := .absolute, groups := ["Form"], field := "Key" }

private def indexed (key : SurfaceSemanticIndexKey := fieldKey) : SurfaceGroupListOperand :=
  .indexed { target := { base := .absolute, groups := ["Form", "Rows"], field := "N" }, key }

private def keyedFixed (key : SurfaceSemanticIndexKey := fieldKey) : SurfaceGroupListOperand :=
  .keyed { target := .group { base := .absolute, groups := ["Form", "Rows", "Details"] }, key }

private def keyedLowerStar (nested terminal : Bool) : SurfaceGroupListOperand :=
  .keyed { target := .starredGroup { base := .absolute, groups :=
    [{ name := "Form" }, { name := "Rows" }, { name := "Children", starred := true }] ++
      (if nested then [{ name := "Parts", starred := true }] else []) ++
      (if terminal then [] else [{ name := "Seal" }]) }, key := fieldKey }

private def keyedStar := keyedLowerStar false true

private def textCell (field : FieldId) (path : List Nat) (value : String) : ClassifiedCellInput :=
  { address := { field, path }, stored := value, raw := if value.isEmpty then .presentEmpty else .parsed (.str value) }

private def selectedDocument (keys : List String) (cells : List ClassifiedCellInput)
    (key : String := "A") : DocumentData :=
  { instantiatedRows := keys.zipIdx.map fun (_, i) => { group := 20, path := [i + 1] }
    cells := textCell 1 [] "on" :: textCell 5 [] key ::
      (keys.zipIdx.map fun (value, i) => textCell 6 [i + 1] value) ++ cells }

private def selectedRow (path : GroupPath) : RelevantEntityPattern :=
  { path, indices := [.all, .concrete 1] ++ (path.drop 2).map fun _ => .all }

private def keyRelevant := every ["Form", "Key"]
private def indexRelevant := every ["Form", "Rows", "Code"]
private def targetRelevant := every ["Form", "Rows", "N"]
private def detailsRelevant := every ["Form", "Rows", "Details"]
private def fixedRelevant := every ["Form", "Fixed"]

private def selectedOrders (operand : SurfaceGroupListOperand) (data : DocumentData)
    (entities : List RelevantEntityPattern) : List (List (Option Verdict)) :=
  [[operand, fixed], [fixed, operand]].map fun operands =>
    predicates.map fun operator => evaluate operator operands data entities

private def allFilled : List (Option Verdict) :=
  [some (.fired .value), some .unknown, some (.fired .value), some .unknown, some .unknown]

private def allEmpty : List (Option Verdict) :=
  [some .unknown, some (.fired .omission), some .unknown,
    some (.fired .omission), some .unknown]

private def mixed : List (Option Verdict) :=
  [some .unknown, some .unknown, some (.fired .value),
    some (.fired .omission), some (.fired .omission)]

private def unknownWithFilled : List (Option Verdict) :=
  [some .unknown, some .unknown, some (.fired .value), some .unknown, some .unknown]

private def unknownWithEmpty : List (Option Verdict) :=
  [some .unknown, some .unknown, some .unknown, some (.fired .omission), some .unknown]

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 2 [] false, numberCell 7 [1] false, numberCell 8 [1] false])
    [every ["Form"]]) = [[allFilled, allFilled], [allFilled, allFilled]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] []) [every ["Form"]]) =
      [[allEmpty, allEmpty], [allEmpty, allEmpty]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 7 [1] false, numberCell 8 [1] false]) [every ["Form"]]) =
      [[mixed, mixed], [mixed, mixed]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 2 [] false]) [every ["Form"]]) =
      [[mixed, mixed], [mixed, mixed]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 2 [] false, numberCell 7 [1] false, numberCell 8 [1] false])
    [indexRelevant, targetRelevant, detailsRelevant, fixedRelevant]) =
      [[unknownWithFilled, unknownWithFilled], [unknownWithFilled, unknownWithFilled]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 7 [1] false, numberCell 8 [1] false])
    [indexRelevant, targetRelevant, detailsRelevant, fixedRelevant]) =
      [[unknownWithEmpty, unknownWithEmpty], [unknownWithEmpty, unknownWithEmpty]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 2 [] false, numberCell 7 [1] false, numberCell 8 [1] false])
    [keyRelevant, targetRelevant, detailsRelevant, fixedRelevant]) =
      [[unknownWithFilled, unknownWithFilled], [unknownWithFilled, unknownWithFilled]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 2 [] false, numberCell 7 [1] false, numberCell 8 [1] false])
    [keyRelevant, indexRelevant, fixedRelevant]) =
      [[unknownWithFilled, unknownWithFilled], [unknownWithFilled, unknownWithFilled]] := by native_decide

example : selectedOrders indexed
    (selectedDocument ["A"] [numberCell 2 [] false] "C")
    [keyRelevant, indexRelevant, targetRelevant, fixedRelevant] = [mixed, mixed] ∧
    selectedOrders keyedFixed (selectedDocument ["A"] [numberCell 2 [] false] "C")
    [keyRelevant, indexRelevant, detailsRelevant, fixedRelevant] = [mixed, mixed] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 2 [] false] "C")
    [keyRelevant, indexRelevant, fixedRelevant]) =
      [[unknownWithFilled, unknownWithFilled], [unknownWithFilled, unknownWithFilled]] := by native_decide

example : selectedOrders indexed (selectedDocument ["A"] [numberCell 2 [] false] "C")
    [keyRelevant, selectedRow ["Form", "Rows", "Code"], targetRelevant, fixedRelevant] =
      [unknownWithFilled, unknownWithFilled] ∧
    selectedOrders indexed (selectedDocument ["A"] [numberCell 2 [] false] "C")
    [keyRelevant, indexRelevant, selectedRow ["Form", "Rows", "N"], fixedRelevant] =
      [unknownWithFilled, unknownWithFilled] := by native_decide

example : selectedOrders keyedFixed (selectedDocument ["A"] [numberCell 2 [] false] "C")
    [keyRelevant, selectedRow ["Form", "Rows", "Code"], detailsRelevant, fixedRelevant] =
      [unknownWithFilled, unknownWithFilled] ∧
    selectedOrders keyedFixed (selectedDocument ["A"] [numberCell 2 [] false] "C")
    [keyRelevant, indexRelevant, selectedRow ["Form", "Rows", "Details"], fixedRelevant] =
      [unknownWithFilled, unknownWithFilled] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A"] [numberCell 7 [1] true, numberCell 8 [1] true]) [every ["Form"]]) =
      [[unknownWithEmpty, unknownWithEmpty], [unknownWithEmpty, unknownWithEmpty]] := by native_decide

example : selectedOrders indexed
    (selectedDocument ["A"] [numberCell 7 [1] true, numberCell 8 [1] true, numberCell 9 [1] false])
    [every ["Form"]] = [unknownWithEmpty, unknownWithEmpty] ∧
    selectedOrders keyedFixed
    (selectedDocument ["A"] [numberCell 7 [1] true, numberCell 8 [1] true, numberCell 9 [1] false])
    [every ["Form"]] = [mixed, mixed] := by native_decide

-- Duplicate keys make selection unavailable rather than choosing the first row
-- (selected-group-predicates matrix, duplicate-root, 2026-10-10).
example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A", "A"] [numberCell 7 [1] false, numberCell 8 [1] false]) [every ["Form"]]) =
      [[unknownWithEmpty, unknownWithEmpty], [unknownWithEmpty, unknownWithEmpty]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A", "B"] [numberCell 7 [2] false, numberCell 8 [2] false]) [every ["Form"]]) =
      [[allEmpty, allEmpty], [allEmpty, allEmpty]] := by native_decide

example : [indexed, keyedFixed].map (fun operand => selectedOrders operand
    (selectedDocument ["A", "B"] [numberCell 7 [2] false, numberCell 8 [2] false] "B") [every ["Form"]]) =
      [[mixed, mixed], [mixed, mixed]] := by native_decide

example : [indexed (.literal (.text "A")), keyedFixed (.literal (.text "A"))].map
    (fun operand => selectedOrders operand
      (selectedDocument ["A"] [numberCell 7 [1] false, numberCell 8 [1] false])
      [indexRelevant, targetRelevant, detailsRelevant, fixedRelevant]) =
        [[mixed, mixed], [mixed, mixed]] := by native_decide

example : both [keyedStar, fixed] (selectedDocument ["A"] []) [every ["Form"]] =
    emptyPair := by native_decide

example : both [keyedStar, fixed] (selectedDocument ["A"] []) [keyRelevant, indexRelevant] =
    unknownPair := by native_decide

example : [indexed, keyedFixed].map (fun operand =>
    [[operand, starred true], [starred true, operand]].map fun operands =>
      both operands (selectedDocument ["A"] [numberCell 7 [1] false, numberCell 8 [1] false])
        [keyRelevant, indexRelevant, targetRelevant, detailsRelevant]) =
      [[filledPair, filledPair], [filledPair, filledPair]] := by native_decide

private def directNumber : SurfaceGroupListOperand :=
  .field { base := .absolute, groups := ["Form"], field := "Direct" }

example : [[directNumber, starred true], [starred true, directNumber]].map (fun operands =>
    [both operands (document 0 [numberCell 11 [] false]) [every ["Form"]],
      both operands (document 0 []) [every ["Form"]],
      both operands (document 0 []) [every ["Form", "Left"]],
      both operands (document 1 []) [every ["Form", "Left"]]]) =
      [[filledPair, emptyPair, unknownPair, filledPair],
        [filledPair, emptyPair, unknownPair, filledPair]] := by native_decide

example : [GroupFillQuantifier.allGroupsFilled, .noGroupFilled].map
    (fun operator => ValidationConditionLeaf.evalPartialGroupReaders operator
      [fun () => .ok [.unavailable], fun () => .error (.checkedDocumentRequired [])]) =
        [.ok .unknown, .ok .unknown] := by rfl

example : ValidationConditionLeaf.evalPartialGroupReaders .allGroupsFilled
    [fun () => .ok [.filled], fun () => .error (.checkedDocumentRequired [])] =
      .error (.checkedDocumentRequired []) ∧
    ValidationConditionLeaf.evalPartialGroupReaders .notAllGroupsFilled
      [fun () => .ok [.empty], fun () => .error (.checkedDocumentRequired [])] =
        .ok (.fired .omission) := by exact ⟨rfl, rfl⟩

example : ValidationConditionLeaf.evalPartialGroupReaders .notAllGroupsFilled
    [fun () => .ok [.unavailable], fun () => .ok [.empty],
      fun () => .error (.checkedDocumentRequired [])] = .ok (.fired .omission) ∧
    ValidationConditionLeaf.evalPartialGroupReaders .notAllGroupsFilled
      [fun () => .ok [.filled], fun () => .error (.checkedDocumentRequired [])] =
        .error (.checkedDocumentRequired []) := by exact ⟨rfl, rfl⟩

example : ValidationConditionLeaf.evalPartialGroupReaders .groupsNotCollectivelyFilled
    [fun () => .ok [.empty], fun () => .error (.checkedDocumentRequired [])] =
      .error (.checkedDocumentRequired []) ∧
    ValidationConditionLeaf.evalPartialGroupReaders .groupsNotCollectivelyFilled
      [fun () => .ok [.unavailable], fun () => .ok [.filled], fun () => .ok [.empty],
        fun () => .error (.checkedDocumentRequired [])] = .ok (.fired .omission) := by exact ⟨rfl, rfl⟩

example : ValidationConditionLeaf.evalPartialGroupReaders .groupsNotCollectivelyFilled
    [fun () => .ok [.filled], fun () => .error (.checkedDocumentRequired [])] =
      .error (.checkedDocumentRequired []) ∧
    ValidationConditionLeaf.evalPartialGroupReaders .groupsNotCollectivelyFilled
      [fun () => .ok [.unavailable], fun () => .ok [.empty]] = .ok .unknown := by exact ⟨rfl, rfl⟩

example : ((ValidationRelevanceScope.partialSet [every ["Form"]]).coversDeclaredFieldExtent
    (model 1999999999) ["Form", "Left", "Seal", "N"] [10] []).toOption = some true := by native_decide

private def coveragePatterns : List RelevantEntityPattern :=
  [RelevanceIndex.all, .concrete 1, .concrete 2].flatMap fun parent =>
    [RelevanceIndex.all, .concrete 1, .concrete 2].map fun child =>
      { path := ["Form", "Rows", "Children"], indices := [.all, parent, child] }

private def coverageSubsets : List (List RelevantEntityPattern) :=
  coveragePatterns.foldl (fun subsets pattern => subsets ++ subsets.map (pattern :: ·)) [[]]

example : coverageSubsets.all (fun entities =>
    ((ValidationRelevanceScope.partialSet entities).coversDeclaredFieldExtent
        (model 2) ["Form", "Rows", "Children", "N"] [20, 30] []).toOption ==
      some ([1, 2].all fun parent => [1, 2].all fun child => entities.any fun entity =>
        (entity.projectOntoTarget? ["Form", "Rows", "Children", "N"]).any fun projected =>
          projected.encompasses { path := ["Form", "Rows", "Children", "N"], indices := [.concrete 1, .concrete parent, .concrete child, .concrete 1] })) = true := by native_decide

private def lowerStars : List SurfaceGroupListOperand :=
  [keyedStar, keyedLowerStar false false, keyedLowerStar true true, keyedLowerStar true false]

private def lowerDocument (keys : List String) (children parts : List (List Nat))
    (cells : List ClassifiedCellInput) (key : String := "A") (leftRows : Nat := 0) : DocumentData :=
  let data := selectedDocument keys cells key
  { data with instantiatedRows := data.instantiatedRows ++
      children.map (fun path => { group := 30, path }) ++
      parts.map (fun path => { group := 40, path }) ++
      (List.range leftRows).map (fun i => { group := 10, path := [i + 1] }) }

private def childPattern (parent : RelevanceIndex) (child : Nat) : RelevantEntityPattern :=
  { path := ["Form", "Rows", "Children"], indices := [.all, parent, .concrete child] }

private def completeChildren (parent : RelevanceIndex) : List RelevantEntityPattern :=
  [1, 2].map (childPattern parent)

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A"] [[1, 1]] [] []) [every ["Form"]]) =
      [filledPair, emptyPair, emptyPair, emptyPair] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]]
      [numberCell 12 [1, 1] false, numberCell 15 [1, 1, 1] false]) [every ["Form"]]) =
      [filledPair, filledPair, filledPair, filledPair] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A", "B"] [[2, 1]] [[2, 1, 1]]
      [numberCell 12 [2, 1] false, numberCell 15 [2, 1, 1] false]) [every ["Form"]]) =
      [emptyPair, emptyPair, emptyPair, emptyPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A", "B"] [[2, 1]] [[2, 1, 1]]
        [numberCell 12 [2, 1] false, numberCell 15 [2, 1, 1] false] "B") [every ["Form"]]) =
      [filledPair, filledPair, filledPair, filledPair] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A"] [[1, 1], [1, 2]] [[1, 2, 1], [1, 2, 2]]
      [numberCell 12 [1, 2] false, numberCell 15 [1, 2, 2] false])
    [keyRelevant, indexRelevant, childPattern (.concrete 1) 1]) =
      [filledPair, unknownPair, unknownPair, unknownPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [[1, 1], [1, 2]] [[1, 2, 1], [1, 2, 2]]
        [numberCell 12 [1, 2] false, numberCell 15 [1, 2, 2] false])
      (keyRelevant :: indexRelevant :: completeChildren (.concrete 1))) =
      [filledPair, filledPair, filledPair, filledPair] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A"] [] [] [])
    [keyRelevant, indexRelevant, childPattern (.concrete 1) 1]) =
      [unknownPair, unknownPair, unknownPair, unknownPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [] [] [])
      (keyRelevant :: indexRelevant :: completeChildren (.concrete 1))) =
      [emptyPair, emptyPair, emptyPair, emptyPair] := by native_decide

example : ["C", ""].map (fun key => lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]]
      [numberCell 12 [1, 1] false, numberCell 15 [1, 1, 1] false] key) [every ["Form"]])) =
      [[emptyPair, emptyPair, emptyPair, emptyPair],
        [emptyPair, emptyPair, emptyPair, emptyPair]] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A", "A"] [[1, 1]] [[1, 1, 1]]
      [numberCell 12 [1, 1] false, numberCell 15 [1, 1, 1] false]) [every ["Form"]]) =
      [unknownPair, unknownPair, unknownPair, unknownPair] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]] [] "C")
    (keyRelevant :: indexRelevant :: completeChildren .all)) =
      [emptyPair, emptyPair, emptyPair, emptyPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]] [] "C")
      (keyRelevant :: indexRelevant :: completeChildren (.concrete 1))) =
      [unknownPair, unknownPair, unknownPair, unknownPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]] [] "C")
      [keyRelevant, indexRelevant, childPattern .all 1]) =
      [unknownPair, unknownPair, unknownPair, unknownPair] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]]
      [numberCell 10 [1, 1] true, numberCell 12 [1, 1] true,
        numberCell 14 [1, 1, 1] true, numberCell 15 [1, 1, 1] true]) [every ["Form"]]) =
      [filledPair, unknownPair, filledPair, unknownPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]]
        [numberCell 10 [1, 1] true, numberCell 12 [1, 1] true, numberCell 13 [1, 1] false,
          numberCell 14 [1, 1, 1] true, numberCell 15 [1, 1, 1] false]) [every ["Form"]]) =
      [filledPair, filledPair, filledPair, filledPair] := by native_decide

example : lowerStars.map (fun operand => [[operand, fixed], [fixed, operand]].map (fun operands =>
    [both operands (lowerDocument ["A"] [] [] [numberCell 2 [] false]) [every ["Form"]],
      both operands (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]]
        [numberCell 12 [1, 1] false, numberCell 15 [1, 1, 1] false]) [every ["Form"]],
      both operands (lowerDocument ["A"] [] [] []) [every ["Form"]],
      both operands (lowerDocument ["A"] [] [] [numberCell 2 [] false]) [fixedRelevant]])) =
      List.replicate 4 [[filledPair, filledPair, emptyPair, filledPair],
        [filledPair, filledPair, emptyPair, filledPair]] := by native_decide

example : lowerStars.map (fun operand => [[operand, starred true], [starred true, operand]].map
    (fun operands =>
      [both operands (lowerDocument ["A"] [] [] [] "A" 1) [every ["Form"]],
        both operands (lowerDocument ["A"] [[1, 1]] [[1, 1, 1]]
          [numberCell 12 [1, 1] false, numberCell 15 [1, 1, 1] false])
          [keyRelevant, indexRelevant, every ["Form", "Rows", "Children"]],
        both operands (lowerDocument ["A"] [] [] []) [every ["Form"]],
        both operands (lowerDocument ["A"] [] [] [] "C") [keyRelevant, indexRelevant]])) =
      List.replicate 4 [[filledPair, filledPair, emptyPair, unknownPair],
        [filledPair, filledPair, emptyPair, unknownPair]] := by native_decide

example : lowerStars.map (fun operand => both [operand]
    (lowerDocument ["A", "B", "C"] [[3, 1]] [] [numberCell 12 [3, 1] false] "C")
    [every ["Form"]]) = [emptyPair, emptyPair, emptyPair, emptyPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [[1, 1], [1, 2], [1, 3]] [[1, 3, 1]]
        [numberCell 12 [1, 3] false, numberCell 15 [1, 3, 1] false]) [every ["Form"]]) =
      [filledPair, emptyPair, emptyPair, emptyPair] ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [[1, 1]] [[1, 1, 1], [1, 1, 2], [1, 1, 3]]
        [numberCell 15 [1, 1, 3] false]) [every ["Form"]]) =
      [filledPair, emptyPair, filledPair, emptyPair] := by native_decide

example : [GroupFillQuantifier.allGroupsFilled, .notAllGroupsFilled, .groupsNotCollectivelyFilled].all
    (fun operator => lowerStars.all (fun operand =>
      match CheckedValidationCondition.fromGroupList (model 2) ["Form"] operator [operand, fixed] with
      | .error (.starredGroupNotAllowed refused) => refused == operator
      | _ => false)) = true ∧
    lowerStars.map (fun operand => both [operand]
      (lowerDocument ["A"] [] [] []) [every ["Form"]]) =
      [emptyPair, emptyPair, emptyPair, emptyPair] := by native_decide

example : ((ValidationRelevanceScope.partialSet (completeChildren .all)).coversDeclaredFieldExtent
    (model 2) ["Form", "Rows", "Children", "N"] [20, 30] [] (some 20)).toOption = some true ∧
    ((ValidationRelevanceScope.partialSet
      (completeChildren (.concrete 1) ++ completeChildren (.concrete 2))).coversDeclaredFieldExtent
      (model 2) ["Form", "Rows", "Children", "N"] [20, 30] [] (some 20)).toOption = some false := by native_decide

example : [1, 2].map (fun parent =>
    ((ValidationRelevanceScope.partialSet (completeChildren (.concrete 1))).coversDeclaredFieldExtent
      (model 2) ["Form", "Rows", "Children", "N"] [30] [(20, parent)]).toOption) =
      [some true, some false] := by native_decide

example :
    let unbounded := { model 2 with repeatableGroups := (model 2).repeatableGroups.map fun group =>
      if group.level == 30 then { group with repeatability := none } else group }
    [completeChildren (.concrete 1), [selectedRow ["Form", "Rows", "Children"]]].map
      (fun entities => ((ValidationRelevanceScope.partialSet entities).coversDeclaredFieldExtent
        unbounded ["Form", "Rows", "Children", "N"] [30] [(20, 1)]).toOption) =
      [some false, some true] := by native_decide

example :
    let maximum := { model 2 with repeatableGroups := (model 2).repeatableGroups.map fun group =>
      if group.level == 30 then { group with repeatability := some 1999999999 } else group }
    ((ValidationRelevanceScope.partialSet (completeChildren (.concrete 1))).coversDeclaredFieldExtent
      maximum ["Form", "Rows", "Children", "N"] [30] [(20, 1)]).toOption = some false := by native_decide

end A12Kernel.Conformance.PartialGroupList
