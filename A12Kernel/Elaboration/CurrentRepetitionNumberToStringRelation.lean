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

/-- One structural phase fault of the fixed repeatable cascade. The failed
phase does not advance state; rich Number and String outcomes remain successful
phase results rather than entering this relation. -/
inductive CurrentRepetitionNumberToStringFailureTransition
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    CurrentRepetitionNumberToStringState →
      CurrentRepetitionNumberToStringFault → Prop where
  | number
      (fault : CurrentRepetitionNumberToStringFault)
      (executed : plan.executeNumberPhaseWithRead input read = .error fault) :
      CurrentRepetitionNumberToStringFailureTransition
        plan patterns input read {} fault
  | string
      (number : CurrentRepetitionNumberToStringNumberPhase)
      (fault : CurrentRepetitionNumberToStringFault)
      (executed : plan.executeStringPhase patterns input number = .error fault) :
      CurrentRepetitionNumberToStringFailureTransition plan patterns input read
        { number := some number } fault

/-- The fixed cascade either fails before any phase completes or after its exact
complete Number phase. The indexed state is the unchanged successful prefix. -/
inductive CurrentRepetitionNumberToStringFailureTrace
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    CurrentRepetitionNumberToStringState →
      CurrentRepetitionNumberToStringFault → Prop where
  | number
      (failure : CurrentRepetitionNumberToStringFailureTransition
        plan patterns input read {} fault) :
      CurrentRepetitionNumberToStringFailureTrace
        plan patterns input read {} fault
  | string
      (success : CurrentRepetitionNumberToStringTransition
        plan patterns input read {} { number := some number })
      (failure : CurrentRepetitionNumberToStringFailureTransition
        plan patterns input read { number := some number } fault) :
      CurrentRepetitionNumberToStringFailureTrace plan patterns input read
        { number := some number } fault

end A12Kernel
