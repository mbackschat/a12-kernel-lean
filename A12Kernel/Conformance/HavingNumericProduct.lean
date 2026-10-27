import A12Kernel.Elaboration.HavingNumericProduct

namespace A12Kernel.Conformance.HavingNumericProduct
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def number (value : Rat) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def source : A12Kernel.HavingNumericProduct := {
  groupPath := ["Form", "Rows"], path := { axes := [{ level := 10, repeatability := some 2 }], firstStar := 0 }
  left := { origin := .inner, field := { id := 1, info := { scale := 2, signed := false } } }
  right := { origin := .outer, field := { id := 2, info := { scale := 3, signed := true } } } }
private def base : ResolvingCorrelationContext CorrelationRuntimeFault :=
  ({ read := fun _ _ => number 0 } : CorrelationContext).asResolving
private def context (tail : Bool := false) : ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  read := fun env field => pure (number (if field == 1 then
    if env == frame.innerEnv then 2 else 3
    else if env == frame.outerEnv then 5 else 7))
  groups := some {
    validation := fun _ group => .error (.groupUnavailable group.path)
    computation := fun _ group => .error (.groupUnavailable group.reference.path)
    fieldExtent := fun _ env _ _ => pure ([env, if env == frame.innerEnv then frame.outerEnv else frame.innerEnv], tail) } }
private def run (context : ResolvingCorrelationContext CorrelationRuntimeFault) (phase : Phase := .validation)
    (product : A12Kernel.HavingNumericProduct := source) : Sum CorrelationRuntimeFault NumericOperand :=
  match product.evaluate phase context frame with
  | .ok result => .inr result
  | .error error => .inl error

example : run (context) = .inr (.value 31 .fixed) ∧
    run (context true) = .inr (.value 31 .both) ∧
    source.summary = .field 5 ∧
    (HavingNumericAtom.product source).fieldOrigins = [(.inner, 1), (.outer, 2)] := by native_decide

example : [Phase.validation, .computation].all (fun phase =>
    run { (context) with read := fun _ field => if field == 1 then pure invalid else .error .valueFailure } phase ==
      .inr (.unknown .malformed) &&
    run { (context) with read := fun _ field => if field == 1 then pure empty else pure invalid } phase ==
      .inr (.unknown .malformed)) = true := by native_decide

example : run { (context) with read := fun _ _ => pure { empty with findings := [.required] } } =
      .inr (.unknown .required) ∧
    run { (context) with read := fun _ _ => pure { empty with findings := [.required] } } .computation =
      .inr (.value 0 .both) ∧
    run base = .inl (.groupUnavailable source.groupPath) := by native_decide

private def unequal : ResolvingCorrelationContext CorrelationRuntimeFault := { (context) with
  read := fun env field => if field == 1 && env == frame.outerEnv then .error .valueFailure else pure (number 2)
  groups := some {
    validation := fun _ group => .error (.groupUnavailable group.path)
    computation := fun _ group => .error (.groupUnavailable group.reference.path)
    fieldExtent := fun _ env _ field => pure (if field == 1 then [env, frame.outerEnv] else [env], false) } }

-- Unlike independently keyed products (spec/07 §3.8), these unfiltered iterators reach only
-- paired rows (`RuntimeController.summeVonProdukten`); the unpaired suffix is not a value read.
example : run unequal = .inr (.value 4 .fixed) ∧
    run { unequal with read := fun _ _ => .error .valueFailure } = .inl .valueFailure := by native_decide

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Left", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .number { scale := 2, signed := false } } },
    { id := 2, name := "Right", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .number { scale := 3, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
example : source.wellFormed model [10] [10] = true ∧
    { source with groupPath := ["Form"] }.wellFormed model [10] [10] = false ∧
    { source with right := { source.right with field := { source.right.field with id := 1 } } }.wellFormed model [10] [10] = false ∧
    { source with path := { source.path with firstStar := 1 } }.wellFormed model [10] [10] = false ∧
    { source with path := { source.path with axes := [{ level := 10, repeatability := some 3 }] } }.wellFormed model [10] [10] = false := by native_decide

end A12Kernel.Conformance.HavingNumericProduct
