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

/-- Resolve only the operands reached before an existential decision. -/
def anyOperands {operand error : Type} {kind : ValueListKind}
    (resolve : operand → Except error (ResolvedValueListSide kind))
    (predicate : ValueListAtom kind → Bool) : List operand → Except error (Except FormalCause Bool)
  | [] => pure (.ok false)
  | source :: rest => do
      let side ← resolve source
      match ValueListCell.anyComputation predicate side.cells with
      | .error cause => pure (.error cause)
      | .ok true => pure (.ok true)
      | .ok false => anyOperands resolve predicate rest

/-- Collect every member value in operand order, preserving reached failures. -/
def collectOperands {operand error : Type} {kind : ValueListKind}
    (resolve : operand → Except error (ResolvedValueListSide kind)) :
    List operand → List (ValueListAtom kind) → Except error (Except FormalCause (List (ValueListAtom kind)))
  | [], accumulated => pure (.ok accumulated)
  | source :: rest, accumulated => do
      let side ← resolve source
      match ValueListCell.scanPresent (fun acc value => value :: acc) side.cells accumulated with
      | .error cause => pure (.error cause)
      | .ok values => collectOperands resolve rest values

end ValueListQuantifier

/-- Authored scalar and plural membership share equality and scans, but only plural forms
have the prepasses that can leave a whole side unread (spec/06 §B.5). -/
inductive ComputationValueListOperator where
  | scalar (operator : ValueListMembershipOp)
  | quantified (operator : ValueListQuantifier)
  deriving Repr, DecidableEq

namespace ComputationValueListOperator

private def result (outcome : Except FormalCause Bool) : ComputationConditionResult :=
  match outcome with
  | .error cause => .poison cause
  | .ok true => .holds
  | .ok false => .notTrue

/-- Select traversal phases over caller-owned scans. Keeping scans callable preserves
short-circuiting and lets a filtered stream retain its lookahead without eager flattening. -/
def evalUsing {error : Type} {kind : ValueListKind}
    (operator : ComputationValueListOperator)
    (collectMembers : Unit → Except error (Except FormalCause (List (ValueListAtom kind))))
    (anySubject : (ValueListAtom kind → Bool) → Except error (Except FormalCause Bool)) :
    Except error ComputationConditionResult := do
  if operator == .quantified .notAll then
    match ← anySubject (fun _ => true) with
    | .error cause => return .poison cause
    | .ok false => return .notTrue
    | .ok true => pure ()
  match ← collectMembers () with
  | .error cause => pure (.poison cause)
  | .ok members =>
      let contains := fun candidate => members.any (ValueListAtom.equal candidate)
      match operator with
      | .quantified .atLeastOne =>
          if members.isEmpty then pure .notTrue
          else result <$> anySubject contains
      | .quantified .no => result <$> (Except.map (!·) <$> anySubject contains)
      | .quantified .notAll | .scalar .notIncluded =>
          result <$> anySubject (fun candidate => !contains candidate)
      | .scalar .included => result <$> anySubject contains

end ComputationValueListOperator

namespace ValueListQuantifier

/-- The materialized-side specialization; stream readers call the same phase selector. -/
def evalComputationWith {field value error : Type} {kind : ValueListKind}
    (operator : ValueListQuantifier)
    (resolveField : field → Except error (ResolvedValueListSide kind))
    (resolveValue : value → Except error (ResolvedValueListSide kind))
    (fields : List field) (values : List value) : Except error ComputationConditionResult :=
  (ComputationValueListOperator.quantified operator).evalUsing
    (fun _ => collectOperands resolveValue values [])
    (fun predicate => anyOperands resolveField predicate fields)

def evalComputation (operator : ValueListQuantifier)
    (fields values : List (ResolvedValueListSide kind)) : ComputationConditionResult :=
  match operator.evalComputationWith (error := Empty) Except.ok Except.ok fields values with
  | .ok outcome => outcome
  | .error impossible => nomatch impossible

end ValueListQuantifier
namespace ValueListMembershipOp

/-- Scalar membership shares the collector and existential scan, without plural prepasses. -/
def evalComputationWith {field value error : Type} {kind : ValueListKind}
    (operator : ValueListMembershipOp)
    (resolveField : field → Except error (ResolvedValueListSide kind))
    (resolveValue : value → Except error (ResolvedValueListSide kind))
    (fields : List field) (values : List value) : Except error ComputationConditionResult :=
  (ComputationValueListOperator.scalar operator).evalUsing
    (fun _ => ValueListQuantifier.collectOperands resolveValue values [])
    (fun predicate => ValueListQuantifier.anyOperands resolveField predicate fields)

def evalComputation (operator : ValueListMembershipOp)
    (fields values : List (ResolvedValueListSide kind)) : ComputationConditionResult :=
  match operator.evalComputationWith (error := Empty) Except.ok Except.ok fields values with
  | .ok outcome => outcome
  | .error impossible => nomatch impossible

end ValueListMembershipOp

end A12Kernel
