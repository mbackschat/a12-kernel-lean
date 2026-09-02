import A12Kernel.Semantics.MandatoryInformation

/-! # Mandatory-information derivation locks

These cases cover the measured flat, nonrepeatable ERROR-rule fragment plus the measured whole-rule rejection for one filtered shape. They deliberately exclude count thresholds, repetition, indices, filter internals, generated rules, and cross-root references. -/

namespace A12Kernel.Conformance.MandatoryInformation

open A12Kernel

private def rootOf (_ : String) : String := "Form"
private def splitRoot (field : String) : String := if field == "A" then "First" else "Second"

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

end A12Kernel.Conformance.MandatoryInformation
