import A12Kernel.Semantics.ComputationCondition

/-! # Authored computation-alternative admission

Number and String tables share the two-stage refusal walk: non-target-read admission in authored
order, then each alternative's own guardedness and target reads. This selector reports the first
refusal; occurrence counts remain outside the checked-table error domain
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-self-read-alternative-walk)).
-/

namespace A12Kernel

inductive ComputationAlternativeAdmissionError (GuardError OperationError : Type) where
  | precondition (alternative : Nat) (error : GuardError)
  | operation (alternative : Nat) (error : OperationError)
  | guardNotAdmitted (alternative : Nat)
  | unguardedAlternative (alternative : Nat)
  | guardTargetReference (alternative : Nat)
  deriving Repr, DecidableEq

namespace ComputationAlternative

/-- Select a refusal from resolved own guards and attempted operation elaborations. `guardAdmitted`
checks the joined guard, while `guardReadsTarget` checks only the own guard. A common guard's target
read is judged at the first otherwise-judged alternative, and no missing own guard bypasses the
non-target-read admission stage
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)). -/
def admissionRefusal? {Guard Operation GuardError OperationError : Type}
    (alternatives : List (Except GuardError (Option Guard) × Except OperationError Operation))
    (guardAdmitted : Option Guard → Bool) (guardReadsTarget : Guard → Bool)
    (operationIsTargetRead : OperationError → Bool) (commonReadsTarget : Bool) :
    Option (ComputationAlternativeAdmissionError GuardError OperationError) :=
  let indexed := alternatives.zipIdx
  let otherRefusal? := indexed.findSome? fun ((guard, result), index) =>
    match guard with
    | .error error => some (.precondition (index + 1) error)
    | .ok precondition =>
        if !guardAdmitted precondition then some (.guardNotAdmitted (index + 1)) else
          match result with
          | .error error =>
              if operationIsTargetRead error then none else some (.operation (index + 1) error)
          | .ok _ => none
  let several := alternatives.length > 1
  let firstJudged := indexed.find? fun ((guard, _), _) =>
    match guard with
    | .ok own => !(several && own.isNone)
    | .error _ => true
  let alternativeRefusal? := indexed.findSome? fun ((guard, result), index) =>
    let commonRefusal :=
      if commonReadsTarget && firstJudged.map (·.2) == some index then
        some (.guardTargetReference (index + 1))
      else none
    match guard with
    | .error error => some (.precondition (index + 1) error)
    | .ok none => if several then some (.unguardedAlternative (index + 1)) else
        commonRefusal <|> match result with
          | .error error => some (.operation (index + 1) error)
          | .ok _ => none
    | .ok (some precondition) =>
        commonRefusal <|>
          if guardReadsTarget precondition then some (.guardTargetReference (index + 1)) else
            match result with
            | .error error => some (.operation (index + 1) error)
            | .ok _ => none
  otherRefusal? <|> alternativeRefusal?

end ComputationAlternative

end A12Kernel
