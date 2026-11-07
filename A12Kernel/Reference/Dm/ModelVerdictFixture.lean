import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.ModelConsistencyRead
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.PossibleCauseCheck

/-! # What the readers and static checks make of one model, compared whole

Two lock modules state their rows as an equality between a model and its twin: the retired variant
members and the reader binding laws. The comparator lives here once, so a row means the same thing in
both. -/

namespace A12Kernel.Dm

open Lean A12Kernel

/-- Everything the readers and the static checks make of a model, rendered so that `==` compares it whole:
the model with its declaration admission, the consistency outcome, the declaration notifications, each
rule's and computation's static verdict, and the possible-cause reference classes of each rule drawing one. -/
structure ModelVerdict where
  built : String
  consistency : String
  declarations : String
  statics : List String
  possibleCauses : List String
  deriving BEq, Repr

private def staticVerdict {α} : Lowering α → String
  | .ok _ => "ok"
  | .error refusal => s!"refused {refusal.construct} {refusal.kernelClass?.getD "-"}"

/-- The verdict of `json` across the three readers and the rule, computation and possible-cause checks. -/
def modelVerdict (json : Json) : ModelVerdict :=
  let built := readModelWithAdmission json
  { built := reprStr built
    consistency := reprStr (checkModelConsistency json)
    declarations := reprStr (fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true)
    statics := match built with
      | .ok dm => dm.rules.map (staticVerdict <| checkValidationRule dm .english ·) ++
          dm.computations.map (staticVerdict <| checkComputation dm .english ·)
      | .error _ => []
    possibleCauses := match built with
      | .ok dm => dm.rules.filterMap fun rule => match possibleCauseRefusals dm .english rule with
          | .ok [] => none
          | .ok refusals => some s!"{rule.name}: {refusals.map (·.kernelCode)}"
          | .error reason => some s!"{rule.name}: unjudged: {reason}"
      | .error _ => [] }

end A12Kernel.Dm
