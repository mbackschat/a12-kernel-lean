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

/-- One structural phase fault of the fixed inverse cascade. The failed phase
does not advance state; rich String and Number outcomes remain successful phase
results rather than entering this relation. -/
inductive CurrentRepetitionStringToNumberFailureTransition
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    CurrentRepetitionStringToNumberState →
      CurrentRepetitionStringToNumberFault → Prop where
  | string
      (fault : CurrentRepetitionStringToNumberFault)
      (executed : plan.executeStringPhase patterns input = .error fault) :
      CurrentRepetitionStringToNumberFailureTransition plan patterns input
        {} fault
  | number
      (string : CurrentRepetitionStringToNumberStringPhase)
      (fault : CurrentRepetitionStringToNumberFault)
      (executed : plan.executeNumberPhase input string = .error fault) :
      CurrentRepetitionStringToNumberFailureTransition plan patterns input
        { string := some string } fault

/-- The fixed cascade either fails before any phase completes or after its exact
complete String phase. The indexed state is the unchanged successful prefix. -/
inductive CurrentRepetitionStringToNumberFailureTrace
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    CurrentRepetitionStringToNumberState →
      CurrentRepetitionStringToNumberFault → Prop where
  | string
      (failure : CurrentRepetitionStringToNumberFailureTransition
        plan patterns input {} fault) :
      CurrentRepetitionStringToNumberFailureTrace plan patterns input {} fault
  | number
      (success : CurrentRepetitionStringToNumberTransition plan patterns input
        {} { string := some string })
      (failure : CurrentRepetitionStringToNumberFailureTransition
        plan patterns input { string := some string } fault) :
      CurrentRepetitionStringToNumberFailureTrace plan patterns input
        { string := some string } fault

end A12Kernel
