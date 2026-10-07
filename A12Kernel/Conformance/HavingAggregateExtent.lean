import A12Kernel.Semantics.Correlation
import A12Kernel.Elaboration.HavingNumberAggregate

namespace A12Kernel.Conformance.HavingAggregateExtent
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def number (value : Rat) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def ref (id : FieldId) (signed : Bool := true) (origin : HavingOrigin := .inner) : HavingNumberRef :=
  { origin, field := { id, info := { scale := 0, signed } } }
private def selection : StarPath := { axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def extent : HavingEntityExtent := .starredGroup ["Form", "Rows"] selection
private def slots : List (HavingFieldListSlot HavingNumberRef) := [.extent extent [ref 1, ref 2 false]]
private def base : ResolvingCorrelationContext CorrelationRuntimeFault :=
  ({ read := fun _ _ => number 7 } : CorrelationContext).asResolving
private def context (omitted : List FieldId := []) (absent : List FieldId := []) :
    ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  groups := some {
    validation := fun _ source => .error (.groupUnavailable source.path)
    computation := fun _ source => .error (.groupUnavailable source.reference.path)
    fieldExtent := fun _ env _ field => pure (if absent.contains field then [] else [env], omitted.contains field) } }
private def evaluate (op : NumericAggregateOp) (context : ResolvingCorrelationContext CorrelationRuntimeFault)
    (source : List (HavingFieldListSlot HavingNumberRef) := slots) (phase : Phase := .validation) :=
  HavingNumberAggregate.evaluate phase context frame op source

example : evaluate .sum (context [2] [2]) = .ok (.value 7 .growOnly) ∧
    evaluate .sum (context [1] [1]) = .ok (.value 7 .both) ∧
    evaluate .sum (context) = .ok (.value 14 .fixed) ∧
    evaluate .minimum (context [2] [2]) = .ok (.value 7 .shrinkOnly) ∧
    evaluate .maximum (context [2] [2]) = .ok (.value 7 .growOnly) ∧
    evaluate .distinctCount (context [2] [2]) = .ok (.value 1 .growOnly) := by native_decide

example : [NumericAggregateOp.sum, .minimum, .maximum, .distinctCount].all (fun op => decide (
    evaluate op (context) [] = .ok (.value 0 .fixed) ∧
    evaluate op (context [1, 2] [1, 2]) =
      .ok (.value 0 (if op == .distinctCount then .growOnly else .both)) ∧
    evaluate op { (context) with read := fun _ _ => pure empty } =
      .ok (.value 0 (if op == .distinctCount then .growOnly else .both)) ∧
    evaluate op { (context) with read := fun _ _ => pure invalid } = .ok (.unknown .malformed))) = true := by
  native_decide

private def required : CheckedCell := { empty with findings := [.required] }
example : [NumericAggregateOp.sum, .minimum, .maximum, .distinctCount].all (fun op => decide (
    evaluate op { (context) with read := fun _ _ => pure required } = .ok (.unknown .required) ∧
    evaluate op { (context) with read := fun _ _ => pure required } slots .computation =
      .ok (.value 0 (if op == .distinctCount then .growOnly else .both)))) = true := by native_decide

private inductive FaultSite where | row | read | acquisition deriving DecidableEq
private def unavailableFirst (site : FaultSite) : ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with
    read := fun env field =>
      if field != 1 || (site == .row && env == frame.outerEnv) then .error (.storedTextUnavailable field)
      else pure invalid
    groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun path env _ field =>
        if site == .acquisition && field != 1 then .error (.groupUnavailable path)
        else pure (if site == .row then [env, frame.outerEnv] else [env], false) } }

example : [NumericAggregateOp.sum, .minimum, .maximum, .distinctCount].all (fun op =>
    [FaultSite.row, .read, .acquisition].all fun site => decide (
      evaluate op (unavailableFirst site) = .ok (.unknown .malformed) ∧
      evaluate op (unavailableFirst site) slots .computation = .ok (.unknown .malformed) ∧
      evaluate op { (unavailableFirst site) with read := fun _ _ => .error .valueFailure } =
        .error .valueFailure)) = true := by native_decide

private def groupAtom : HavingNumericAtom := .aggregate .sum slots
private def groupLeaf : CorrelatedHavingLeaf := .numeric {
  op := .ordinary .equal, left := .atom groupAtom, right := .literal { value := 14, authoredScale := 0 } }
private def groupCondition : CorrelatedHaving := .leaf groupLeaf
example : groupAtom.readComputationIn { read := fun _ _ => number 7 } frame =
      .error (.groupUnavailable extent.groupPath) ∧
    groupCondition.evalComputationIn { read := fun _ _ => number 7 } frame =
      .error (.groupUnavailable extent.groupPath) ∧
    groupCondition.evalComputationIn { read := fun _ _ => invalid, groups := (context).groups } frame =
      .ok (.poison .malformed) ∧
    groupLeaf.evalTruthInResolving { (context) with read := fun _ _ => pure invalid } frame =
      .ok .unknown ∧
    groupCondition.evalTruthInResolving { (context) with read := fun _ _ => pure invalid } frame =
      .ok .fls := by native_decide

private def ordered : ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  read := fun env field => pure (number (if field == 1 then
    if env == frame.innerEnv then 10 ^ 50 else -(10 ^ 50)
    else 3 / 5))
  groups := some {
    validation := fun _ source => .error (.groupUnavailable source.path)
    computation := fun _ source => .error (.groupUnavailable source.reference.path)
    fieldExtent := fun _ _ _ field => pure (if field == 1 then [frame.innerEnv, frame.outerEnv] else [frame.innerEnv], false) } }

-- Row-major traversal rounds the middle 3/5 away; declaration-major order retains it (spec/04 Sum).
example : evaluate .sum ordered = .ok (.value (3 / 5) .fixed) ∧
    evaluate .sum ordered [.extent extent [ref 2 false, ref 1]] = .ok (.value 0 .fixed) := by native_decide

example : evaluate .distinctCount { ordered with read := fun env field => pure (number (
    if field == 2 then 1 else if env == frame.innerEnv then 0 else 1 / 10 ^ 20)) } =
      .ok (.value 2 .fixed) := by native_decide

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form", "Rows"], name := "A", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form", "Rows"], name := "B", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
private def certified (source : List (HavingFieldListSlot HavingNumberRef)) :=
  HavingNumberAggregate.wellFormed model [10] [10] source

example : certified slots = true ∧
    certified [.extent extent [ref 1]] = false ∧
    certified [.extent extent [ref 2 false, ref 1]] = false ∧
    certified [.extent extent [ref 1 false, ref 2 false]] = false ∧
    certified [.extent (.starredGroup ["Form", "Rows"] { selection with
      axes := [{ level := 10, repeatability := some 4 }] }) [ref 1, ref 2 false]] = false ∧
    certified [.extent (.starredGroup ["Form", "Rows"] { selection with firstStar := 1 })
      [ref 1, ref 2 false]] = false := by native_decide

private def bound (levels : List RepeatableLevel) : HavingEntityExtent := .group {
  path := ["Form", "Rows"], origin := .path, boundRepeatableScope := levels }
example : certified [.extent (bound [10]) [ref 1, ref 2 false]] = true ∧
    certified [.extent (bound []) [ref 1, ref 2 false]] = false ∧
    HavingNumberAggregate.wellFormed model [] [] [.extent (bound [10]) [ref 1, ref 2 false]] = false ∧
    certified [.direct (ref 1), .direct (ref 1 true .outer)] = true ∧
    certified [.direct (ref 1), .direct (ref 1)] = false ∧
    certified [.direct (ref 1)] = false ∧
    certified [.extent (bound [10]) [ref 1, ref 2 false], .direct (ref 1)] = false := by native_decide

end A12Kernel.Conformance.HavingAggregateExtent
