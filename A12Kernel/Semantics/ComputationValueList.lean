import A12Kernel.Semantics.ValueList
import A12Kernel.Semantics.ComputationCondition

namespace A12Kernel

namespace ValueListCell

/-- Computation existential scans stop before a deciding cell's suffix; unlike the full
collector, an unreached malformed cell cannot poison the result. -/
def anyComputation (predicate : ValueListAtom kind → Bool) :
    List (ValueListCell kind) → Except FormalCause Bool
  | [] => .ok false
  | .empty :: rest => anyComputation predicate rest
  | .unknown cause :: _ => .error cause
  | .present value :: rest =>
      if predicate value then .ok true else anyComputation predicate rest

end ValueListCell

namespace ValueListQuantifier

private def anyOperands {operand error : Type} {kind : ValueListKind}
    (resolve : operand → Except error (ResolvedValueListSide kind))
    (predicate : ValueListAtom kind → Bool) : List operand → Except error (Except FormalCause Bool)
  | [] => pure (.ok false)
  | source :: rest => do
      let side ← resolve source
      match ValueListCell.anyComputation predicate side.cells with
      | .error cause => pure (.error cause)
      | .ok true => pure (.ok true)
      | .ok false => anyOperands resolve predicate rest

private def collectOperands {operand error : Type} {kind : ValueListKind}
    (resolve : operand → Except error (ResolvedValueListSide kind)) :
    List operand → List (ValueListAtom kind) → Except error (Except FormalCause (List (ValueListAtom kind)))
  | [], accumulated => pure (.ok accumulated)
  | source :: rest, accumulated => do
      let side ← resolve source
      match ValueListCell.scanPresent (fun acc value => value :: acc) side.cells accumulated with
      | .error cause => pure (.error cause)
      | .ok values => collectOperands resolve rest values

private def result (outcome : Except FormalCause Bool) : ComputationConditionResult :=
  match outcome with
  | .error cause => .poison cause
  | .ok true => .holds
  | .ok false => .notTrue

/-- Computation membership owns its phase-specific reduction: values are collected before the
membership scan, while NotAll first establishes a present field and then restarts that field scan.
Operand resolution remains lazy so deciding prefixes also avoid later structural errors. -/
def evalComputationWith {field value error : Type} {kind : ValueListKind}
    (operator : ValueListQuantifier)
    (resolveField : field → Except error (ResolvedValueListSide kind))
    (resolveValue : value → Except error (ResolvedValueListSide kind))
    (fields : List field) (values : List value) : Except error ComputationConditionResult := do
  if operator == .notAll then
    match ← anyOperands resolveField (fun _ => true) fields with
    | .error cause => return .poison cause
    | .ok false => return .notTrue
    | .ok true => pure ()
  match ← collectOperands resolveValue values [] with
  | .error cause => pure (.poison cause)
  | .ok members =>
      let contains := fun candidate => members.any (ValueListAtom.equal candidate)
      match operator with
      | .atLeastOne =>
          if members.isEmpty then pure .notTrue
          else result <$> anyOperands resolveField contains fields
      | .no =>
          result <$> (Except.map (!·) <$> anyOperands resolveField contains fields)
      | .notAll => result <$> anyOperands resolveField (fun candidate => !contains candidate) fields

def evalComputation (operator : ValueListQuantifier)
    (fields values : List (ResolvedValueListSide kind)) : ComputationConditionResult :=
  match operator.evalComputationWith (error := Empty) Except.ok Except.ok fields values with
  | .ok outcome => outcome
  | .error impossible => nomatch impossible

end ValueListQuantifier
end A12Kernel
