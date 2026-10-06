import A12Kernel.Semantics.CustomCondition
import A12Kernel.Semantics.Condition

/-! # Resolved `CustomCondition` executable locks

These cases exercise a successfully resolved, pure callback after ordinary rule and row gating has reached the leaf. The concrete data, relevance, and formal-address payloads remain test witnesses, while the error channel uses the shared message-pointer representation.
-/

namespace A12Kernel.Conformance.CustomCondition

open A12Kernel

private abbrev Invocation :=
  CustomConditionInvocation Bool (List Nat) (List Nat)

private def partiallyKnownPointer : MessagePointer :=
  { field := 11, coordinates := [.unknown] }

private def knownPointer : MessagePointer :=
  MessagePointer.ofCellAddr { field := 11, path := [2] }

private def invocation : Invocation :=
  {
    data := true
    relevance := .partialEntities [2, 4]
    formallyIncorrect := [7]
    errorPointer := partiallyKnownPointer
  }

/- Callback truth is returned as VALUE, even with a nonempty formal-invalid payload. -/
example :
    evalReachedCustomCondition (fun input : Invocation =>
      input.data && input.formallyIncorrect == [7]) invocation =
      .fired .value := by
  native_decide

/- Callback false remains non-firing rather than becoming UNKNOWN or OMISSION. -/
example :
    evalReachedCustomCondition (fun _ : Invocation => false) invocation =
      .notFired := by
  native_decide

/- Full relevance is distinct from a partial request whose entity container is empty. -/
example :
    evalReachedCustomCondition
        (fun input : Invocation =>
          match input.relevance with
          | .all => true
          | .partialEntities _ => false)
        { invocation with relevance := .all } =
      .fired .value ∧
    evalReachedCustomCondition
        (fun input : Invocation =>
          match input.relevance with
          | .all => true
          | .partialEntities _ => false)
        { invocation with relevance := .partialEntities [] } =
      .notFired := by
  native_decide

/- The oracle observes the exact formal-invalid payload supplied by orchestration. -/
example :
    evalReachedCustomCondition
        (fun input : Invocation => input.formallyIncorrect == [7, 9])
        { invocation with formallyIncorrect := [7, 9] } =
      .fired .value := by
  native_decide

/- A partially-known current error pointer is not collapsed to a known pointer. -/
example :
    evalReachedCustomCondition
        (fun input : Invocation => input.errorPointer == partiallyKnownPointer)
        invocation =
      .fired .value ∧
    evalReachedCustomCondition
        (fun input : Invocation => input.errorPointer == partiallyKnownPointer)
        { invocation with errorPointer := knownPointer } =
      .notFired := by
  native_decide

/- The effective data view is passed unchanged and remains callback-owned. -/
example :
    evalReachedCustomCondition (fun input : Invocation => input.data) invocation =
      .fired .value ∧
    evalReachedCustomCondition
        (fun input : Invocation => input.data)
        { invocation with data := false } =
      .notFired := by
  native_decide

/- The leaf is structurally eligible on an empty row; surrounding condition structure still controls whether it is reached. -/
example : customConditionCanFireOnEmpty = true := by
  native_decide

private def yes : Invocation → Bool := fun _ => true
private def no : Invocation → Bool := fun _ => false
private def factory (name : String) (callback : Invocation → Bool) :
    String → Option (Invocation → Bool) := fun key => if key == name then some callback else none

example : (match CustomConditionRegistry.invoke {
    configured := some (factory "Own" no)
    fallback := [factory "Other" yes] } "Other" invocation with
      | .error (.missingRegistration "Other") => true | _ => false) = true := by native_decide

example : (CustomConditionRegistry.invoke {
    fallback := [factory "Other" no, factory "Other" yes] } "Other" invocation).toOption =
      some .notFired := by native_decide

example : (CustomConditionRegistry.invoke {
    fallback := [factory "Absent" no, factory "Other" yes] } "Other" invocation).toOption =
      some (.fired .value) := by native_decide

private def callOrder (classify : Bool) (tree : ConditionTree String) (answer : Bool) :
    Verdict × List String :=
  let read (name : String) : StateM (List String) Verdict := do
    modify (· ++ [name])
    pure (if name == "A" && answer then .fired .value else .notFired)
  (tree.evalObservedM classify read).run []

example : callOrder false (.and (.leaf "A") (.leaf "B")) false = (.notFired, ["A"]) ∧
    callOrder false (.or (.leaf "A") (.leaf "B")) true = (.fired .value, ["A"]) ∧
    callOrder true (.or (.leaf "A") (.leaf "B")) true = (.fired .value, ["A", "A", "B"]) := by native_decide

end A12Kernel.Conformance.CustomCondition
