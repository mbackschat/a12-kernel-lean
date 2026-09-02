import A12Kernel.Semantics.MandatoryInformation

/-! # Mandatory-information count-chain locks

These cases cover the exact measured two-stage filled-count target-to-operand chain and keep every cross-role alias and differently ordered shape fail-closed.
-/

namespace A12Kernel.Conformance.MandatoryInformationCountChain

open A12Kernel

private def rootOf (_ : String) : String := "Form"

private def derive (rules : List (MandatoryRule String String)) :
    Option (MandatoryInformation String String) :=
  deriveCheckedMandatoryInformation rootOf rules

private def result (mandatory mandatoryForRootGroup mandatoryRootGroups :
    List String) : Option (MandatoryInformation String String) :=
  some { mandatory, mandatoryForRootGroup, mandatoryRootGroups }

private def checkedThreshold? (value : Rat) :
    Option CheckedMandatoryCountThreshold :=
  checkMandatoryCountThreshold { value, authoredScale := 0 }

private def deriveCountTargetOperandChain? (downstreamBound : Rat)
    (includeSecondSeed : Bool) (downstreamOther : String := "OneB")
    (downstreamTarget : String := "OneTarget")
    (downstreamFirst : Bool := true) : Option (MandatoryInformation String String) := do
  let oneOrTwo ← checkedThreshold? downstreamBound
  let two ← checkedThreshold? 2
  let seeds : List (MandatoryRule String String) :=
    if includeSecondSeed then [.fieldNotFilled "TwoA", .fieldNotFilled "TwoB"]
    else [.fieldNotFilled "TwoA"]
  let downstream := .countGuardedNotFilled ["ZeroTarget", downstreamOther]
    .countGreaterEqual (some oneOrTwo) downstreamTarget
  let upstream := .countGuardedNotFilled ["TwoA", "TwoB"]
    .countGreaterEqual (some two) "ZeroTarget"
  let rules : List (MandatoryRule String String) :=
    if downstreamFirst then [downstream] ++ seeds ++ [upstream]
    else [upstream] ++ seeds ++ [downstream]
  derive rules

/- The measured reverse-authored count target may feed one downstream count; each missing threshold premise suppresses only its dependent suffix. -/
example :
    deriveCountTargetOperandChain? 1 true =
        result ["TwoA", "TwoB", "ZeroTarget", "OneTarget"]
          ["TwoA", "TwoB", "ZeroTarget", "OneTarget"] ["Form"] ∧
      deriveCountTargetOperandChain? 2 true =
        result ["TwoA", "TwoB", "ZeroTarget"]
          ["TwoA", "TwoB", "ZeroTarget"] ["Form"] ∧
      deriveCountTargetOperandChain? 1 false =
        result ["TwoA"] ["TwoA"] ["Form"] ∧
      deriveCountTargetOperandChain? 1 true "OneTarget" = none ∧
      deriveCountTargetOperandChain? 1 true (downstreamTarget := "ZeroTarget") = none ∧
      deriveCountTargetOperandChain? 1 true (downstreamTarget := "TwoA") = none ∧
      deriveCountTargetOperandChain? 1 true "TwoA" = none ∧
      deriveCountTargetOperandChain? 1 true (downstreamFirst := false) = none := by
  native_decide

end A12Kernel.Conformance.MandatoryInformationCountChain
