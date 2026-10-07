import A12Kernel.Semantics.HavingFieldFill
import A12Kernel.Semantics.HavingGroupPresence

namespace A12Kernel.Conformance.HavingFieldFillExtent
open A12Kernel

private def operators : List FieldFillQuantifier :=
  [.allFieldsFilled, .noFieldFilled, .atLeastOneFieldFilled, .moreThanOneFieldFilled,
    .notAllFieldsFilled, .notExactlyOneFieldFilled, .fieldsNotCollectivelyFilled]
private def filled : CheckedCell := { rawPresent := true, parsed := some (.num 5), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def reference (field : FieldId) (origin : HavingOrigin := .inner) : HavingPresenceRef := { field, origin }
private def extent : HavingEntityExtent := .starredGroup ["Form", "Rows"] {
  axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def boundExtent : HavingEntityExtent := .group {
  path := ["Form", "Rows"], origin := .path, boundRepeatableScope := [10] }
private def oneDeclaration : List (HavingFieldListSlot HavingPresenceRef) := [.extent extent [reference 1]]
private def twoDeclarations : List (HavingFieldListSlot HavingPresenceRef) := [.extent extent [reference 1, reference 2]]
private def base : ResolvingCorrelationContext CorrelationRuntimeFault :=
  ({ read := fun _ _ => filled } : CorrelationContext).asResolving
private def context (cells : List CheckedCell) (tail : Bool := false) :
    ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with
    read := fun env field => do
      if field != 1 then return invalid
      let some row := env.uniqueRowAt? 10 | throw .valueFailure
      pure (cells[row - 1]?.getD empty)
    groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun _ env depth field => pure (
        if depth == 1 || field != 1 then ([env], false)
        else ((List.range cells.length).map (fun index => [(10, index + 1)]), tail)) } }
private def validationSignature (operator : FieldFillQuantifier)
    (slots : List (HavingFieldListSlot HavingPresenceRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) : Option Char :=
  (A12Kernel.HavingFieldFill.evalValidationRead operator slots context frame).toOption.map fun verdict =>
    match verdict with | .fired .value => 'V' | .fired .omission => 'O' | .unknown => 'U' | .notFired => 'F'
private def computationSignature (operator : FieldFillQuantifier)
    (slots : List (HavingFieldListSlot HavingPresenceRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) : Option Char :=
  (A12Kernel.HavingFieldFill.evalComputationRead operator slots context frame).toOption.map fun result =>
    match result with | .holds => 'T' | .notTrue => 'F' | .poison _ => 'P'
private def signatures (context : ResolvingCorrelationContext CorrelationRuntimeFault)
    (slots : List (HavingFieldListSlot HavingPresenceRef) := oneDeclaration) : Option (String × String) := do
  let validation ← operators.mapM (fun operator => validationSignature operator slots context)
  let computation ← operators.mapM (fun operator => computationSignature operator slots context)
  pure (String.ofList validation, String.ofList computation)

example : [
    signatures (context [filled, filled]),
    signatures (context [filled] true),
    signatures (context [] true),
    signatures (context [filled, empty]),
    signatures (context [invalid]),
    signatures (context [invalid] true),
    signatures (context [empty, filled, invalid])] = [
      some ("VUVVUVU", "TFTTFTF"), some ("UUVUOUO", "FFTFTFT"),
      some ("UOUUOOU", "FTFFTTF"), some ("UUVUOUO", "FFTFTFT"),
      some ("UUUUUUU", "PPPPPPP"), some ("UUUUOUU", "PPPPPPP"),
      some ("UUVUOUO", "FFTPTPT")] := by
  native_decide

example : signatures (context [filled] true) twoDeclarations = some ("UUVUOUO", "FFTPTPT") ∧
    signatures (context [filled]) twoDeclarations = some ("UUVUUUU", "PFTPPPP") ∧
    signatures (context [filled] true) [.extent extent [reference 2, reference 1]] =
      some ("UUVUOUO", "PPPPPPP") := by
  native_decide

private def faultContext (acquisition : Bool) : ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with
    read := fun _ field => if field == 1 then pure filled else .error (.storedTextUnavailable field)
    groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun path env _ field => if acquisition && field != 1 then .error (.groupUnavailable path)
        else pure ([env], false) } }
private def validationFails (operator : FieldFillQuantifier)
    (slots : List (HavingFieldListSlot HavingPresenceRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) (expected : CorrelationRuntimeFault) : Bool :=
  match A12Kernel.HavingFieldFill.evalValidationRead operator slots context frame with
  | .error actual => actual == expected
  | .ok _ => false
private def computationFails (operator : FieldFillQuantifier)
    (slots : List (HavingFieldListSlot HavingPresenceRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) (expected : CorrelationRuntimeFault) : Bool :=
  match A12Kernel.HavingFieldFill.evalComputationRead operator slots context frame with
  | .error actual => actual == expected
  | .ok _ => false

example : [false, true].all (fun acquisition =>
    let context := faultContext acquisition
    validationFails .atLeastOneFieldFilled twoDeclarations context
      (if acquisition then .groupUnavailable extent.groupPath else .storedTextUnavailable 2) &&
    decide ((A12Kernel.HavingFieldFill.evalComputationRead .atLeastOneFieldFilled twoDeclarations context frame).toOption =
      some .holds)) = true ∧
    validationFails .atLeastOneFieldFilled [.direct (reference 1), .direct (reference 2)]
      (faultContext false) (.storedTextUnavailable 2) = true ∧
    (A12Kernel.HavingFieldFill.evalComputationRead .atLeastOneFieldFilled
      [.direct (reference 1), .direct (reference 2)] (faultContext false) frame).toOption = some .holds := by
  native_decide

example : (A12Kernel.HavingFieldFill.evalValidationRead .notAllFieldsFilled oneDeclaration (context [invalid]) frame).toOption =
      some .unknown ∧
    (A12Kernel.HavingFieldFill.evalValidationRead .notAllFieldsFilled oneDeclaration (context [invalid] true) frame).toOption =
      some (.fired .omission) ∧
    (A12Kernel.HavingFieldFill.evalComputationRead .fieldsNotCollectivelyFilled oneDeclaration
      (context [empty, filled, invalid]) frame).toOption = some .holds ∧
    (A12Kernel.HavingFieldFill.evalComputationRead .moreThanOneFieldFilled twoDeclarations
      (context [filled] true) frame).toOption = some (.poison .malformed) := by
  native_decide

example : signatures (context [filled, empty]) [.extent boundExtent [reference 1]] =
      some ("VUVUUUU", "TFTFFFF") ∧
    signatures (context [filled, empty]) [.extent boundExtent [reference 1 .outer]] =
      some ("UOUUOOU", "FTFFTTF") := by
  native_decide

example : operators.all (fun operator =>
    validationFails operator oneDeclaration base (.groupUnavailable extent.groupPath) &&
    computationFails operator oneDeclaration base (.groupUnavailable extent.groupPath)) = true := by
  native_decide

end A12Kernel.Conformance.HavingFieldFillExtent
