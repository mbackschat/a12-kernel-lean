import A12Kernel.Semantics.Correlation
import A12Kernel.Elaboration.HavingCollectionCount

namespace A12Kernel.Conformance.HavingCollectionCount
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def filled : CheckedCell := { rawPresent := true, parsed := some (.num 7), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def refs : List (HavingFieldListSlot HavingPresenceRef) := [
  .direct { origin := .inner, field := 1 }, .direct { origin := .outer, field := 2 }]
private def extent : HavingEntityExtent := .starredGroup ["Form", "Rows"] {
  axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def variants (slots : List (HavingFieldListSlot HavingPresenceRef)) : List A12Kernel.HavingCollectionCount := [
  .filledFields slots (some 6),
  .numberValue 7 (slots.map (·.map fun ref => { origin := ref.origin, field := { id := ref.field, info := { scale := 0, signed := false } } })),
  .tokenValue "keep" (slots.map (·.map fun ref => { origin := ref.origin, operand := .string { id := ref.field } })),
  .tokenDistinct (slots.map (·.map fun ref => { origin := ref.origin, operand := .string { id := ref.field } })),
  .booleanValue true slots,
  .temporalDistinct none .fullDate (slots.map (·.map fun ref => {
    origin := ref.origin, field := { id := ref.field, kind := .date, components := .fullDate } }))]
private def base : ResolvingCorrelationContext CorrelationRuntimeFault :=
  ({ read := fun _ _ => filled } : CorrelationContext).asResolving
private def outcome (phase : Phase) (context : ResolvingCorrelationContext CorrelationRuntimeFault)
    (source : A12Kernel.HavingCollectionCount) : Sum CorrelationRuntimeFault (Option NumericOperand) :=
  match source.evaluate phase context frame with
  | .ok value => .inr value
  | .error error => .inl error

private def unavailablePrefix : ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  read := fun env field => if field == 1 && env == frame.innerEnv then pure invalid else .error .valueFailure
  groups := some {
    validation := fun _ source => .error (.groupUnavailable source.path)
    computation := fun _ source => .error (.groupUnavailable source.reference.path)
    fieldExtent := fun path env _ field => if field == 1 then pure ([env, frame.outerEnv], false)
      else .error (.groupUnavailable path) } }

example : [Phase.validation, .computation].all (fun phase =>
    (variants refs ++ variants [.extent extent [{ origin := .inner, field := 1 }, { origin := .inner, field := 2 }]]).all
      (fun source => outcome phase unavailablePrefix source == .inr (some (.unknown .malformed)))) = true := by native_decide

example : [Phase.validation, .computation].all (fun phase => (variants refs).all fun source =>
    outcome phase { unavailablePrefix with read := fun _ _ => .error .valueFailure } source ==
      .inl .valueFailure) = true := by native_decide

private def omitted : ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  read := fun _ _ => .error .valueFailure
  groups := some {
    validation := fun _ source => .error (.groupUnavailable source.path)
    computation := fun _ source => .error (.groupUnavailable source.reference.path)
    fieldExtent := fun _ _ _ _ => pure ([], true) } }

example : (variants [.extent extent [{ origin := .inner, field := 1 }]]).all (fun source =>
    outcome .validation omitted source == .inr (some (.value 0 .growOnly))) = true := by native_decide

example : outcome .validation base (.filledFields refs (some 2)) = .inr (some (.value 2 .fixed)) ∧
    outcome .validation base (.filledFields refs (some 6)) = .inr (some (.value 2 .growOnly)) ∧
    outcome .validation base (.filledFields refs none) = .inr none ∧
    outcome .computation base (.filledFields refs none) = .inr (some (.value 2 .fixed)) := by native_decide

example : (variants refs).all (fun source =>
    outcome .validation { base with read := fun _ _ => pure { empty with findings := [.required] } } source ==
      .inr (some (.unknown .required))) = true ∧
    outcome .computation { base with read := fun _ _ => pure { empty with findings := [.required] } }
      (.filledFields refs (some 2)) = .inr (some (.value 0 .fixed)) := by native_decide

example : (variants refs).all (fun source =>
    (HavingNumericAtom.collectionCount source).origins == [.inner, .outer] &&
    (HavingNumericAtom.collectionCount source).fieldOrigins == [(.inner, 1), (.outer, 2)]) = true := by native_decide

private def enumDecl : FlatFieldDecl := {
  id := 1, name := "Code", groupPath := ["Form", "Pair"]
  policy := { kind := .enumeration }, enumeration := some {
    storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["keep", "other"] }] } }
private def enumModel : FlatModel := { fields := [enumDecl] }
private def projected : HavingStringRef := {
  origin := .inner
  operand := (enumDecl.toEnumerationTextFieldComparison? (.category "Label")).getD
    (.string { id := 1 }, .plainString) |>.1 }
private def stored : HavingStringRef := {
  projected with operand := (enumDecl.toTextFieldComparison?).getD (.string { id := 1 }, .plainString) |>.1 }
private def tokenWellFormed (source : A12Kernel.HavingCollectionCount) := source.wellFormed enumModel [] []
example : tokenWellFormed (.tokenValue "keep" [.direct stored, .direct projected]) = true ∧
    tokenWellFormed (.tokenValue "keep" [.direct projected, .direct projected]) = false ∧
    tokenWellFormed (.tokenDistinct [.direct stored, .direct projected]) = false ∧
    tokenWellFormed (.tokenValue "keep" [.extent (.group { path := ["Form", "Pair"], origin := .path }) [projected]]) = false := by native_decide

end A12Kernel.Conformance.HavingCollectionCount
