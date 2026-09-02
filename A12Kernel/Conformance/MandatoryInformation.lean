import A12Kernel.Semantics.MandatoryInformation

/-! # Mandatory-information derivation locks

These cases cover the measured flat, nonrepeatable ERROR-rule fragment plus the measured whole-rule rejection for one filtered shape and the bounded filled-count and distinct-count slices. They deliberately exclude repetition, indices, filter internals, generated rules, and cross-root references. -/

namespace A12Kernel.Conformance.MandatoryInformation

open A12Kernel

private def rootOf (_ : String) : String := "Form"
private def splitRoot (field : String) : String := if field == "A" then "First" else "Second"
private def countSplitRoot (field : String) : String := if field == "Target" then "Second" else "First"

private def derive (rules : List (MandatoryRule String String)) :
    Option (MandatoryInformation String String) :=
  deriveCheckedMandatoryInformation rootOf rules

private def result (mandatory mandatoryForRootGroup mandatoryRootGroups :
    List String) : Option (MandatoryInformation String String) :=
  some { mandatory, mandatoryForRootGroup, mandatoryRootGroups }

private def ignoredRules : List (MandatoryRule String String) := [
  .ignored (.fieldFilled "A"),
  .ignored (.fieldsNotCollectivelyFilled ["A", "B"]),
  .ignored (.atLeastOneFieldFilled ["A", "B"]),
  .ignored (.allFieldsFilled ["A", "B"]),
  .ignored (.groupFilled "Form"),
  .ignored (.warningFieldNotFilled "A"),
  .ignored (.filtered ["A"])
]

private def measuredCases : List (List (MandatoryRule String String) ×
    Option (MandatoryInformation String String)) := [
  ([.fieldNotFilled "A"], result ["A"] ["A"] ["Form"]),
  ([.disjoinedFieldNotFilled ["A", "B"]], result ["A", "B"] ["A", "B"] ["Form"]),
  ([.notAllFieldsFilled ["A", "B"]], result ["A", "B"] ["A", "B"] ["Form"]),
  ([.conjoinedFieldNotFilled ["A", "B"]], result [] [] ["Form"]),
  ([.noFieldFilled ["A", "B"]], result [] [] ["Form"]),
  ([.notExactlyOneFieldFilled ["A", "B"]], result [] [] ["Form"]),
  ([.groupNotFilled "Form"], result [] [] ["Form"]),
  (ignoredRules, result [] [] []),
  ([.fieldGuardedNotFilled "A" "B"], result [] [] []),
  ([.fieldNotFilled "A", .fieldGuardedNotFilled "A" "B"], result ["A", "B"] ["A", "B"] ["Form"]),
  ([.fieldGuardedNotFilled "A" "B", .fieldNotFilled "A"], result ["A", "B"] ["A", "B"] ["Form"]),
  ([.fieldGuardedNotFilled "B" "C", .fieldGuardedNotFilled "A" "B", .fieldNotFilled "A"], result ["A", "B", "C"] ["A", "B", "C"] ["Form"]),
  ([.fieldGuardedNotFilled "C" "B", .fieldNotFilled "A"], result ["A"] ["A"] ["Form"]),
  ([.rootGuardedNotFilled "Form" "A"], result [] ["A"] []),
  ([.rootGuardedNotFilled "Form" "A", .groupNotFilled "Form"], result ["A"] ["A"] ["Form"])
]

/- One finite decision table locks field, root-only, ignored, closure, and guard branches. -/
example : measuredCases.all (fun (rules, expected) => derive rules == expected) := by
  native_decide

/- The two field sets are not interchangeable, even in this smallest measured fragment. -/
example :
    (derive [.rootGuardedNotFilled "Form" "A"]).map
        MandatoryInformation.mandatory ≠
      (derive [.rootGuardedNotFilled "Form" "A"]).map
        MandatoryInformation.mandatoryForRootGroup := by
  native_decide

/- Cycles, wider root topology, cross-root guards, and empty multi-field forms fail closed. -/
example :
    deriveCheckedMandatoryInformation rootOf
        [.fieldGuardedNotFilled "A" "B", .fieldGuardedNotFilled "B" "A", .fieldNotFilled "A"] = none ∧
      deriveCheckedMandatoryInformation splitRoot
        [.fieldNotFilled "A", .fieldNotFilled "B"] = none ∧
      deriveCheckedMandatoryInformation splitRoot
        [.fieldGuardedNotFilled "A" "B"] = none ∧
      deriveCheckedMandatoryInformation (fun _ : String => "Second") [.rootGuardedNotFilled "First" "A"] = none ∧
      derive [.notAllFieldsFilled []] = none := by
  native_decide

private def fieldListGuardCases : List (List (MandatoryRule String String) ×
    Option (MandatoryInformation String String)) := [
  ([
      .fieldListGuardedNotFilled ["A", "B"] .atLeastOneFilled "Target",
      .fieldNotFilled "A"
    ], result ["A", "Target"] ["A", "Target"] ["Form"]),
  ([
      .fieldListGuardedNotFilled ["A", "B"] .allFilled "Target",
      .fieldNotFilled "A",
      .fieldNotFilled "B"
    ], result ["A", "B", "Target"] ["A", "B", "Target"] ["Form"]),
  ([
      .fieldNotFilled "A",
      .fieldListGuardedNotFilled ["A", "B"] .atLeastOneFilled "Target"
    ], result ["A", "Target"] ["A", "Target"] ["Form"]),
  ([
      .fieldNotFilled "A",
      .fieldListGuardedNotFilled ["A", "B"] .allFilled "Target"
    ], result ["A"] ["A"] ["Form"]),
  ([
      .fieldNotFilled "C",
      .fieldListGuardedNotFilled ["A", "B"] .atLeastOneFilled "Target"
    ], result ["C"] ["C"] ["Form"])
]

/- The flat existential and universal list guards close in either authored order and remain distinct when only one premise is mandatory. -/
example :
    fieldListGuardCases.all (fun (rules, expected) => derive rules == expected) ∧
      derive [
        .fieldNotFilled "A",
        .fieldListGuardedNotFilled ["A", "B"] .atLeastOneFilled "Target"
      ] ≠ derive [
        .fieldNotFilled "A",
        .fieldListGuardedNotFilled ["A", "B"] .allFilled "Target"
      ] := by
  native_decide

/- The retained Kernel batch keeps both guard identities and both truth values in one reverse-authored ruleset. -/
example :
    derive [
      .fieldListGuardedNotFilled ["A1", "B1"] .atLeastOneFilled "TAnyTrue",
      .fieldListGuardedNotFilled ["A3", "B3"] .allFilled "TAllTrue",
      .fieldListGuardedNotFilled ["A4", "B4"] .allFilled "TAllFalse",
      .fieldListGuardedNotFilled ["A2", "B2"] .atLeastOneFilled "TAnyFalse",
      .fieldNotFilled "A1",
      .fieldNotFilled "A3",
      .fieldNotFilled "B3",
      .fieldNotFilled "A4"
    ] = result
      ["A1", "A3", "B3", "A4", "TAnyTrue", "TAllTrue"]
      ["A1", "A3", "B3", "A4", "TAnyTrue", "TAllTrue"]
      ["Form"] := by
  native_decide

/- Empty or duplicate lists, cyclic field-list dependencies, and cross-root targets remain outside the checked flat slice. -/
example :
    derive [.fieldListGuardedNotFilled [] .atLeastOneFilled "Target"] = none ∧
      derive [.fieldListGuardedNotFilled ["A", "A"] .allFilled "Target"] = none ∧
      derive [
        .fieldListGuardedNotFilled ["B"] .atLeastOneFilled "A",
        .fieldGuardedNotFilled "A" "B"
      ] = none ∧
      deriveCheckedMandatoryInformation splitRoot [
        .fieldNotFilled "A",
        .fieldListGuardedNotFilled ["A"] .atLeastOneFilled "B"
      ] = none := by
  native_decide

private def checkedThreshold? (value : Rat) (authoredScale : Int := 0) :
    Option CheckedMandatoryCountThreshold :=
  checkMandatoryCountThreshold { value, authoredScale }

private def deriveCountLess? (value : Rat) (authoredScale : Int := 0) :
    Option (MandatoryInformation String String) := do
  let threshold ← checkedThreshold? value authoredScale
  derive [.countLessThan ["A", "B"] (some threshold)]

private def deriveCountGuard? (comparison : MandatoryCountGuardComparison)
    (value : Rat) (target : String) :
    Option (MandatoryInformation String String) := do
  let threshold ← checkedThreshold? value
  derive [
    .fieldNotFilled "A",
    .fieldNotFilled "B",
    .countGuardedNotFilled ["A", "B"] comparison (some threshold) target
  ]

private def deriveDifferentValuesLess? (value : Rat) :
    Option (MandatoryInformation String String) := do
  let threshold ← checkedThreshold? value
  derive [.differentValuesLessThan ["A", "B"] (some threshold)]

private def deriveDifferentValuesGuard? (value : Rat) (target : String) :
    Option (MandatoryInformation String String) := do
  let threshold ← checkedThreshold? value
  derive [
    .fieldNotFilled "A",
    .fieldNotFilled "B",
    .differentValuesGuardedNotFilled ["A", "B"] .countGreaterEqual
      (some threshold) target
  ]

private def deriveDistinctCountKernelBatch? :
    Option (MandatoryInformation String String) := do
  let rootThreshold ← checkedThreshold? 1
  let guardThreshold ← checkedThreshold? 2
  derive [
    .differentValuesGuardedNotFilled ["A", "B"] .countGreaterEqual
      (some guardThreshold) "DistinctTarget",
    .countGuardedNotFilled ["A", "B"] .countGreaterEqual
      (some guardThreshold) "FilledTarget",
    .differentValuesLessThan ["A", "B"] (some rootThreshold),
    .countLessThan ["A", "B"] (some rootThreshold),
    .fieldNotFilled "A",
    .fieldNotFilled "B"
  ]

private def deriveCrossRootDifferentValuesGuard? :
    Option (MandatoryInformation String String) := do
  let threshold ← checkedThreshold? 2
  deriveCheckedMandatoryInformation countSplitRoot [
    .fieldNotFilled "A",
    .fieldNotFilled "B",
    .differentValuesGuardedNotFilled ["A", "B"] .countGreaterEqual
      (some threshold) "Target"
  ]

private def deriveWithThreshold? (value : Rat)
    (rules : CheckedMandatoryCountThreshold →
      List (MandatoryRule String String)) :
    Option (MandatoryInformation String String) := do
  let threshold ← checkedThreshold? value
  derive (rules threshold)

/- The checked threshold retains the authored literal even when host narrowing produces the same `-1` used for no numeric bound. -/
example :
    (checkedThreshold? 4294967295).map (fun threshold =>
      (threshold.authored, threshold.narrowed)) =
        some ({ value := 4294967295, authoredScale := 0 }, -1) := by
  native_decide

/- Standalone count-root contribution follows the narrowed host value's positive partition, not exact mathematical magnitude. -/
example :
    deriveCountLess? 1 = result [] [] ["Form"] ∧
      deriveCountLess? 3 = result [] [] ["Form"] ∧
      deriveCountLess? 0 = result [] [] [] ∧
      deriveCountLess? (-1) = result [] [] [] ∧
      deriveCountLess? 4294967295 = result [] [] [] ∧
      deriveCountLess? 4294967296 = result [] [] [] ∧
      deriveCountLess? 4294967297 = result [] [] ["Form"] ∧
      deriveCountLess? 4294967299 = result [] [] ["Form"] ∧
      deriveCountLess? (-6 / 10) 1 = result [] [] [] := by
  native_decide

/- Filled-count and distinct-count rules share standalone root contribution, but only the filled-count comparison can enable a mandatory target in this checked slice. -/
example :
    deriveCountLess? 1 = deriveDifferentValuesLess? 1 ∧
      deriveCountGuard? .countGreaterEqual 2 "FilledTarget" =
        result ["A", "B", "FilledTarget"] ["A", "B", "FilledTarget"] ["Form"] ∧
      deriveDifferentValuesGuard? 2 "DistinctTarget" =
        result ["A", "B"] ["A", "B"] ["Form"] ∧
      deriveDistinctCountKernelBatch? =
        result ["A", "B", "FilledTarget"] ["A", "B", "FilledTarget"] ["Form"] := by
  native_decide

/- The distinct-count guard admits only the exact duplicate-free, direct-seed, isolated-target, non-sentinel true-comparison shape measured by the batch. -/
example :
    derive [.differentValuesLessThan ["A", "A"] none] = none ∧
      derive [.differentValuesLessThan [] none] = none ∧
      deriveDifferentValuesGuard? (-1) "SentinelTarget" = none ∧
      deriveDifferentValuesGuard? 3 "FalseTarget" = none ∧
      derive [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .differentValuesGuardedNotFilled ["A", "B"] .countGreaterEqual
          none "AbsentTarget"
      ] = none ∧
      deriveWithThreshold? 2 (fun threshold => [
        .differentValuesGuardedNotFilled ["A", "B"] .countGreaterEqual
          (some threshold) "Target"
      ]) = none ∧
      deriveWithThreshold? 2 (fun threshold => [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .differentValuesGuardedNotFilled ["A", "A"] .countGreaterEqual
          (some threshold) "Target"
      ]) = none ∧
      deriveWithThreshold? 2 (fun threshold => [
        .fieldNotFilled "Seed",
        .fieldGuardedNotFilled "Seed" "A",
        .fieldNotFilled "B",
        .differentValuesGuardedNotFilled ["A", "B"] .countGreaterEqual
          (some threshold) "Target"
      ]) = none ∧
      deriveWithThreshold? 2 (fun threshold => [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .differentValuesGuardedNotFilled ["A", "B"] .countGreaterEqual
          (some threshold) "Target",
        .ignored (.fieldFilled "Target")
      ]) = none ∧
      deriveCrossRootDifferentValuesGuard? = none := by
  native_decide

/- Every measured count-guard spelling admits a true guard except when the checked threshold carries the `-1` sentinel. -/
example :
    deriveCountGuard? .countGreaterEqual 0 "GeZero" =
        result ["A", "B", "GeZero"] ["A", "B", "GeZero"] ["Form"] ∧
      deriveCountGuard? .countGreater (-2) "GtMinusTwo" =
        result ["A", "B", "GtMinusTwo"] ["A", "B", "GtMinusTwo"] ["Form"] ∧
      deriveCountGuard? .literalLessEqualCount 0 "ReverseZero" =
        result ["A", "B", "ReverseZero"] ["A", "B", "ReverseZero"] ["Form"] ∧
      deriveCountGuard? .countGreaterEqual (-1) "GeMinusOne" =
        result ["A", "B"] ["A", "B"] ["Form"] ∧
      deriveCountGuard? .countGreater (-1) "GtMinusOne" =
        result ["A", "B"] ["A", "B"] ["Form"] ∧
      deriveCountGuard? .literalLessEqualCount (-1) "ReverseMinusOne" =
        result ["A", "B"] ["A", "B"] ["Form"] ∧
      deriveCountGuard? .countGreaterEqual 4294967297 "NarrowOne" =
        result ["A", "B", "NarrowOne"] ["A", "B", "NarrowOne"] ["Form"] ∧
      deriveCountGuard? .countGreaterEqual 4294967295 "NarrowMinusOne" =
        result ["A", "B"] ["A", "B"] ["Form"] := by
  native_decide

/- No bound shares the evaluator sentinel outcome without sharing the checked authored-literal identity; unseeded or malformed count guards fail closed. -/
example :
    derive [.countLessThan ["A", "B"] none] = result [] [] [] ∧
      derive [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .countGuardedNotFilled ["A", "B"] .countGreaterEqual none "Target"
      ] = result ["A", "B"] ["A", "B"] ["Form"] ∧
      deriveCheckedMandatoryInformation rootOf [
        .countGuardedNotFilled ["A", "B"] .countGreaterEqual none "Target"
      ] = none ∧
      deriveCountGuard? .countGreater 3 "FalseGuard" = none ∧
      deriveCountGuard? .countGreaterEqual 3 "FalseInclusive" = none ∧
      deriveCountGuard? .literalLessEqualCount 3 "FalseReverse" = none ∧
      derive [.countLessThan ["A", "A"] none] = none ∧
      derive [.countLessThan [] none] = none ∧
      derive [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .countGuardedNotFilled ["A", "A"] .countGreaterEqual none "Target"
      ] = none ∧
      derive [
        .countGuardedNotFilled [] .countGreaterEqual none "Target"
      ] = none ∧
      derive [
        .fieldNotFilled "A",
        .countGuardedNotFilled ["A", "B"] .countGreaterEqual none "Target"
      ] = none ∧
      derive [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .countGuardedNotFilled ["A", "B"] .countGreaterEqual none "A"
      ] = none ∧
      deriveCheckedMandatoryInformation splitRoot [
        .countLessThan ["A", "B"] none
      ] = none ∧
      deriveCheckedMandatoryInformation countSplitRoot [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .countGuardedNotFilled ["A", "B"] .countGreaterEqual none "Target"
      ] = none ∧
      checkedThreshold? (2 / 5) 0 = none := by
  native_decide

/- A measured count target is neither produced elsewhere nor an input to wider dependency closure. -/
example :
    deriveWithThreshold? (-1) (fun threshold => [
      .fieldNotFilled "A",
      .fieldNotFilled "B",
      .disjoinedFieldNotFilled ["Target", "C"],
      .countGuardedNotFilled ["A", "B"] .countGreaterEqual
        (some threshold) "Target"
    ]) = none ∧
      deriveWithThreshold? 0 (fun threshold => [
        .fieldNotFilled "A",
        .fieldNotFilled "B",
        .fieldGuardedNotFilled "Target" "Dependent",
        .countGuardedNotFilled ["A", "B"] .countGreaterEqual
          (some threshold) "Target"
      ]) = none := by
  native_decide

end A12Kernel.Conformance.MandatoryInformation
