import A12Kernel.Elaboration.CurrentRepetitionNumberToString

/-! # CurrentRepetition Number-to-String transition relation

This purpose-specific relation exposes the existing complete Number phase and dependent String phase without turning the fixed repeatable cascade into a generic scheduler. Exact row selection, target execution, dependency projection, and rich outcomes remain owned by the checked cascade.
-/

namespace A12Kernel

/-- Private successful-transition state. A String completion can exist only beside the Number phase it consumed. -/
structure CurrentRepetitionNumberToStringState where
  number : Option CurrentRepetitionNumberToStringNumberPhase := none
  string : Option (List (SourcedStringTargetOutcome CellAddr)) := none
  deriving Repr, DecidableEq

/-- One successful target-family phase of the fixed repeatable cascade. -/
inductive CurrentRepetitionNumberToStringTransition
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    CurrentRepetitionNumberToStringState →
      CurrentRepetitionNumberToStringState → Prop where
  | number
      (phase : CurrentRepetitionNumberToStringNumberPhase)
      (executed : plan.executeNumberPhaseWithRead input read = .ok phase) :
      CurrentRepetitionNumberToStringTransition plan patterns input read
        {} { number := some phase }
  | string
      (number : CurrentRepetitionNumberToStringNumberPhase)
      (outcomes : List (SourcedStringTargetOutcome CellAddr))
      (executed : plan.executeStringPhase patterns input number = .ok outcomes) :
      CurrentRepetitionNumberToStringTransition plan patterns input read
        { number := some number }
        { number := some number, string := some outcomes }

end A12Kernel
