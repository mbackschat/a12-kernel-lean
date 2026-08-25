import A12Kernel.Elaboration.CurrentRepetitionStringToNumber

/-! # CurrentRepetition String-to-Number transition relation

This purpose-specific relation exposes the existing complete String phase and dependent Number phase without introducing a generic repeatable scheduler. Dependency-cell conversion remains at the Number-phase boundary, where the executable owner already places it.
-/

namespace A12Kernel

/-- Private successful-transition state. A Number completion can exist only beside the String phase it consumed. -/
structure CurrentRepetitionStringToNumberState where
  string : Option CurrentRepetitionStringToNumberStringPhase := none
  number : Option (List (SourcedNumericTargetOutcome CellAddr)) := none
  deriving Repr, DecidableEq

/-- One successful target-family phase of the fixed inverse repeatable cascade. -/
inductive CurrentRepetitionStringToNumberTransition
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    CurrentRepetitionStringToNumberState →
      CurrentRepetitionStringToNumberState → Prop where
  | string
      (phase : CurrentRepetitionStringToNumberStringPhase)
      (executed : plan.executeStringPhase patterns input = .ok phase) :
      CurrentRepetitionStringToNumberTransition plan patterns input
        {} { string := some phase }
  | number
      (string : CurrentRepetitionStringToNumberStringPhase)
      (outcomes : List (SourcedNumericTargetOutcome CellAddr))
      (executed : plan.executeNumberPhase input string = .ok outcomes) :
      CurrentRepetitionStringToNumberTransition plan patterns input
        { string := some string }
        { string := some string, number := some outcomes }

end A12Kernel
