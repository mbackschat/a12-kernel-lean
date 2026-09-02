import A12Kernel.Semantics.MandatoryInformation

/-! # Mandatory-information count-chain locks

These cases cover the exact measured two-stage filled-count target-to-operand chain across all six count/contiguous-seed category orders and keep cross-role aliases, seed interleaving, seed reversal, and wider shapes fail-closed.

The retained calibration basis is the [count-chain order checkpoint](../../docs/sources/rule-set-meta-information.md#src-mandatory-information-count-chain-orders).
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

private inductive CountChainOrder
  | downstreamSeedsUpstream
  | downstreamUpstreamSeeds
  | seedsDownstreamUpstream
  | seedsUpstreamDownstream
  | upstreamDownstreamSeeds
  | upstreamSeedsDownstream
  | interleavedSeeds
  | swappedSeeds
  | noSeeds
  | greaterDownstream
  | distinctDownstream
  | longerChain
  | branchingChain

private def measuredOrders : List CountChainOrder := [
  .downstreamSeedsUpstream,
  .downstreamUpstreamSeeds,
  .seedsDownstreamUpstream,
  .seedsUpstreamDownstream,
  .upstreamDownstreamSeeds,
  .upstreamSeedsDownstream
]

private def thresholdOneOnlyOrders : List CountChainOrder := [
  .downstreamUpstreamSeeds,
  .seedsDownstreamUpstream,
  .seedsUpstreamDownstream,
  .upstreamDownstreamSeeds,
  .upstreamSeedsDownstream
]

private def deriveCountTargetOperandChain? (downstreamBound : Rat)
    (includeSecondSeed : Bool) (downstreamOther : String := "OneB")
    (downstreamTarget : String := "OneTarget")
    (order : CountChainOrder := .downstreamSeedsUpstream) :
    Option (MandatoryInformation String String) := do
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
    match order with
    | .downstreamSeedsUpstream => [downstream] ++ seeds ++ [upstream]
    | .downstreamUpstreamSeeds => [downstream, upstream] ++ seeds
    | .seedsDownstreamUpstream => seeds ++ [downstream, upstream]
    | .seedsUpstreamDownstream => seeds ++ [upstream, downstream]
    | .upstreamDownstreamSeeds => [upstream, downstream] ++ seeds
    | .upstreamSeedsDownstream => [upstream] ++ seeds ++ [downstream]
    | .interleavedSeeds =>
        [downstream, .fieldNotFilled "TwoA", upstream, .fieldNotFilled "TwoB"]
    | .swappedSeeds =>
        [downstream, .fieldNotFilled "TwoB", .fieldNotFilled "TwoA", upstream]
    | .noSeeds => [downstream, upstream]
    | .greaterDownstream =>
        [.countGuardedNotFilled ["ZeroTarget", "OneB"] .countGreater
            (some oneOrTwo) "OneTarget"] ++ seeds ++ [upstream]
    | .distinctDownstream =>
        [.differentValuesGuardedNotFilled ["ZeroTarget", "OneB"]
            .countGreaterEqual (some oneOrTwo) "OneTarget"] ++ seeds ++ [upstream]
    | .longerChain =>
        [downstream] ++ seeds ++ [upstream,
          .countGuardedNotFilled ["OneTarget", "FinalB"] .countGreaterEqual
            (some oneOrTwo) "FinalTarget"]
    | .branchingChain =>
        [downstream] ++ seeds ++ [upstream,
          .countGuardedNotFilled ["ZeroTarget", "OtherB"] .countGreaterEqual
            (some oneOrTwo) "OtherTarget"]
  derive rules

private def allOrderResultsMatch (includeSecondSeed : Bool)
    (expected : Option (MandatoryInformation String String)) : Bool :=
  measuredOrders.all fun order =>
    deriveCountTargetOperandChain? 1 includeSecondSeed (order := order) == expected

private def allThresholdOneOnlyOrdersRefuseTwo : Bool :=
  thresholdOneOnlyOrders.all fun order =>
    deriveCountTargetOperandChain? 2 true (order := order) == none &&
      deriveCountTargetOperandChain? 2 false (order := order) == none

/- The measured category orders preserve both the complete closure and the one-seed suffix; each missing threshold premise suppresses only its dependent suffix. -/
example :
    allOrderResultsMatch true
        (result ["TwoA", "TwoB", "ZeroTarget", "OneTarget"]
          ["TwoA", "TwoB", "ZeroTarget", "OneTarget"] ["Form"]) = true ∧
      allOrderResultsMatch false
        (result ["TwoA"] ["TwoA"] ["Form"]) = true ∧
      deriveCountTargetOperandChain? 2 true =
        result ["TwoA", "TwoB", "ZeroTarget"]
          ["TwoA", "TwoB", "ZeroTarget"] ["Form"] ∧
      deriveCountTargetOperandChain? 2 false =
        result ["TwoA"] ["TwoA"] ["Form"] ∧
      allThresholdOneOnlyOrdersRefuseTwo = true ∧
      deriveCountTargetOperandChain? 1 true "OneTarget" = none ∧
      deriveCountTargetOperandChain? 1 true (downstreamTarget := "ZeroTarget") = none ∧
      deriveCountTargetOperandChain? 1 true (downstreamTarget := "TwoA") = none ∧
      deriveCountTargetOperandChain? 1 true "TwoA" = none ∧
      deriveCountTargetOperandChain? 1 true (order := .interleavedSeeds) = none ∧
      deriveCountTargetOperandChain? 1 true (order := .swappedSeeds) = none ∧
      deriveCountTargetOperandChain? 1 true (order := .noSeeds) = none ∧
      deriveCountTargetOperandChain? 1 true (order := .greaterDownstream) = none ∧
      deriveCountTargetOperandChain? 1 true (order := .distinctDownstream) = none ∧
      deriveCountTargetOperandChain? 1 true (order := .longerChain) = none ∧
      deriveCountTargetOperandChain? 1 true (order := .branchingChain) = none := by
  native_decide

end A12Kernel.Conformance.MandatoryInformationCountChain
