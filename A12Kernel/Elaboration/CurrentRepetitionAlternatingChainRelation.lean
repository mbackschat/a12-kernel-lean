import A12Kernel.Elaboration.CurrentRepetitionAlternatingChain

/-! # CurrentRepetition alternating-chain transition relation

This purpose-specific relation exposes the existing complete Number, dependent String, and final Number phases without introducing a generic repeatable scheduler or trace framework. Exact row selection, target execution, dependency projection, and rich outcomes remain owned by the checked chain.
-/

namespace A12Kernel

/-- Successful-transition state for the fixed alternating chain. Each later completion retains the phases it consumed. -/
structure CurrentRepetitionAlternatingChainState where
  number : Option CurrentRepetitionNumberToStringNumberPhase := none
  string : Option (List (SourcedStringTargetOutcome CellAddr)) := none
  third : Option (List (SourcedNumericTargetOutcome CellAddr)) := none
  deriving Repr, DecidableEq

/-- One successful target-family phase of the fixed alternating repeatable chain. -/
inductive CurrentRepetitionAlternatingChainTransition
    (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    CurrentRepetitionAlternatingChainState →
      CurrentRepetitionAlternatingChainState → Prop where
  | number
      (phase : CurrentRepetitionNumberToStringNumberPhase)
      (executed : plan.numberToString.executeNumberPhaseWithRead input input.read =
        .ok phase) :
      CurrentRepetitionAlternatingChainTransition plan patterns input
        {} { number := some phase }
  | string
      (number : CurrentRepetitionNumberToStringNumberPhase)
      (outcomes : List (SourcedStringTargetOutcome CellAddr))
      (executed : plan.numberToString.executeStringPhase patterns input number =
        .ok outcomes) :
      CurrentRepetitionAlternatingChainTransition plan patterns input
        { number := some number }
        { number := some number, string := some outcomes }
  | third
      (number : CurrentRepetitionNumberToStringNumberPhase)
      (string : List (SourcedStringTargetOutcome CellAddr))
      (outcomes : List (SourcedNumericTargetOutcome CellAddr))
      (executed : plan.executeThirdPhase input string = .ok outcomes) :
      CurrentRepetitionAlternatingChainTransition plan patterns input
        { number := some number, string := some string }
        { number := some number, string := some string, third := some outcomes }

end A12Kernel
