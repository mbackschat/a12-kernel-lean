import A12Kernel.Semantics.HavingMembershipStream
import A12Kernel.Semantics.HavingFieldValueList
import A12Kernel.Semantics.HavingGroupPresence
import A12Kernel.Elaboration.HavingFieldValueList

namespace A12Kernel.Conformance.HavingMembershipExtent
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def rows : List Env := [frame.outerEnv, frame.innerEnv]
private def number (value : Rat) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def ref (field : FieldId) (origin : HavingOrigin := .inner) : HavingNumberRef :=
  { origin, field := { id := field, info := { scale := 0, signed := true } } }
private def extent : HavingEntityExtent := .starredGroup ["Form", "Rows"] {
  axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def boundExtent : HavingEntityExtent := .group {
  path := ["Form", "Rows"], origin := .path, boundRepeatableScope := [10] }
private def base : ResolvingCorrelationContext CorrelationRuntimeFault :=
  ({ read := fun _ _ => number 5 } : CorrelationContext).asResolving
private def context : ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with
    read := fun env field => do
      let some row := env.uniqueRowAt? 10 | throw .valueFailure
      pure (number (field * 10 + row))
    groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun _ env depth field => pure (
        if depth == 1 then ([env], false)
        else if field == 6 then ([], true) else (rows, field == 1)) } }
private def readNumber (phase : Phase) (context : ResolvingCorrelationContext CorrelationRuntimeFault)
    (environment : Env) (reference : HavingNumberRef) : Except CorrelationRuntimeFault (ValueListCell .number) :=
  reference.readValueListCell phase (fun _ => context.read environment)
private def resolve (slots : List (HavingFieldListSlot HavingNumberRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) :=
  HavingMembershipStream.resolveSlots (·.origin) (·.field.id) (readNumber .validation context) context frame slots
private def collect (slots : List (HavingFieldListSlot HavingNumberRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) :=
  HavingMembershipStream.collectSlots (·.origin) (·.field.id) (readNumber .computation context) context frame slots
private def any (slots : List (HavingFieldListSlot HavingNumberRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) (predicate : Rat → Bool) :=
  HavingMembershipStream.anySlots (·.origin) (·.field.id) (readNumber .computation context) context frame slots predicate
private def cellView : ValueListCell .number → Option Rat
  | .present value => some value
  | .empty | .unknown _ => none
private def view (slots : List (HavingFieldListSlot HavingNumberRef))
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) :=
  (resolve slots context).map fun sides => sides.map fun side =>
    (side.cells.map cellView, side.hasUninstantiatedTail, side.hasHaving)
private def mixed : List (HavingFieldListSlot HavingNumberRef) := [
  .direct (ref 3 .outer), .extent extent [ref 1, ref 2],
  .extent boundExtent [ref 4 .outer], .extent extent [ref 6]]

example : view mixed context = .ok [
    ([some 32], false, false),
    ([some 12, some 11, some 22, some 21], true, false),
    ([some 42], false, false), ([], true, false)] ∧
    collect mixed context = .ok (.ok [42, 21, 22, 11, 12, 32]) := by native_decide

example : view [.extent boundExtent [ref 4], .extent boundExtent [ref 4 .outer]] context =
    .ok [([some 41], false, false), ([some 42], false, false)] ∧
    view [.extent extent []] context = .ok [([], false, false)] := by native_decide

private inductive FaultSite where | row | read | acquisition deriving DecidableEq
private def faultContext (site : FaultSite) : ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with
    read := fun env field =>
      if field != 1 || (site == .row && env == frame.innerEnv) then .error (.storedTextUnavailable field)
      else pure (number 5)
    groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun path env _ field =>
        if site == .acquisition && field != 1 then .error (.groupUnavailable path)
        else pure (if site == .row then (rows, false) else ([env], false)) } }
private def deciding : List (HavingFieldListSlot HavingNumberRef) := [
  .extent extent [ref 1, ref 2], .direct (ref 3)]

example : [FaultSite.row, .read, .acquisition].all (fun site => decide (
    (resolve deciding (faultContext site)).toOption = none ∧
    any deciding (faultContext site) (· == 5) = .ok (.ok true) ∧
    collect deciding (faultContext site) = .error (match site with
      | .row => .storedTextUnavailable 1
      | .read => .storedTextUnavailable 2
      | .acquisition => .groupUnavailable extent.groupPath))) = true := by native_decide

private def poisonContext (atRow : Bool := false) : ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with
    read := fun env field =>
      if field == 1 then pure (if atRow && env == frame.innerEnv then invalid else number 5)
      else if field == 2 then pure invalid else .error (.storedTextUnavailable field)
    groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun path env _ field => if field == 3 then .error (.groupUnavailable path)
        else pure (if atRow then rows else [env], true) } }

example : [false, true].all (fun atRow => decide (
    collect [.extent extent [ref 1, ref 2, ref 3]] (poisonContext atRow) = .ok (.error .malformed) ∧
    any [.extent extent [ref 1, ref 2, ref 3]] (poisonContext atRow) (· == 5) = .ok (.ok true) ∧
    any [.extent extent [ref 1, ref 2, ref 3]] (poisonContext atRow) (fun _ => false) =
      .ok (.error .malformed))) = true := by native_decide

private def selectorContext : ResolvingCorrelationContext CorrelationRuntimeFault :=
  { context with
    read := fun _ field => if field == 1 then pure (number 5)
      else if field == 2 then pure invalid else if field == 7 then pure empty
      else .error (.storedTextUnavailable field) }
private def evaluate (operator : ComputationValueListOperator)
    (subjects members : List (HavingFieldListSlot HavingNumberRef)) :=
  operator.evalUsing (fun _ => collect members selectorContext) (any subjects selectorContext)

example : evaluate (.quantified .atLeastOne) [.direct (ref 3)] [.extent extent [ref 6], .direct (ref 7)] =
      .ok .notTrue ∧
    evaluate (.quantified .no) [.direct (ref 3)] [.extent extent [ref 6]] = .error (.storedTextUnavailable 3) ∧
    evaluate (.scalar .included) [.direct (ref 3)] [.direct (ref 7)] = .error (.storedTextUnavailable 3) := by
  native_decide

example : evaluate (.quantified .notAll) [.extent extent [ref 6], .direct (ref 7)] [.direct (ref 3)] =
      .ok .notTrue ∧
    evaluate (.quantified .notAll) [.direct (ref 2)] [.direct (ref 3)] = .ok (.poison .malformed) ∧
    evaluate (.quantified .notAll) [.direct (ref 1), .direct (ref 3)] [.direct (ref 2)] =
      .ok (.poison .malformed) ∧
    evaluate (.quantified .notAll) [.direct (ref 1), .direct (ref 3)] [.direct (ref 7)] = .ok .holds ∧
    evaluate (.quantified .notAll) [.direct (ref 1), .direct (ref 3)] [.direct (ref 1)] =
      .error (.storedTextUnavailable 3) := by native_decide

private def validation (quantifier : ValueListQuantifier)
    (subjects members : List (HavingFieldListSlot HavingNumberRef)) := do
  let (subjects, members) ← quantifier.resolveSidesOrdered
    (fun _ => resolve subjects context) (fun _ => resolve members context)
  pure (quantifier.evalOrdered subjects members)

example : validation .no [.extent extent [ref 6]] [.direct (ref 3)] = .ok (.fired .omission) ∧
    validation .atLeastOne [.direct (ref 3), .extent extent [ref 6]] [.direct (ref 3)] =
      .ok (.fired .value) := by native_decide

private def tokenRead (environment : Env) (_ : HavingNumberRef) :
    Except CorrelationRuntimeFault (ValueListCell .token) :=
  pure (.present (if environment == frame.outerEnv then "A" else "a"))
private def tokenSlots : List (HavingFieldListSlot HavingNumberRef) := [
  .extent boundExtent [ref 1 .outer], .direct (ref 2)]

example : HavingMembershipStream.collectSlots (·.origin) (·.field.id) tokenRead context frame tokenSlots =
      .ok (.ok ["a", "A"]) ∧
    HavingMembershipStream.anySlots (·.origin) (·.field.id) tokenRead context frame tokenSlots (· == "A") =
      .ok (.ok true) := by native_decide

example : (view mixed base) = .error (.groupUnavailable extent.groupPath) ∧
    collect mixed base = .error (.groupUnavailable extent.groupPath) ∧
    any [.extent extent [ref 1]] base (fun _ => true) = .error (.groupUnavailable extent.groupPath) := by
  native_decide

private def certificateModel : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form", "Allowed"], name := "A", policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["x"], categories := [{ name := "Label", tokens := ["y"] }] } },
    { id := 2, groupPath := ["Form", "Rows"], name := "Enum", repeatableScope := [10], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["x"], categories := [{ name := "Label", tokens := ["y"] }] } },
    { id := 3, groupPath := ["Form"], name := "Outside", policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["x"], categories := [{ name := "Label", tokens := ["y"] }] } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
private def certificate (shape : Nat) (projected literalMembers : Bool) : Option Bool := do
  let declaration ← (certificateModel.lookupUniqueId (if shape == 0 then 1 else 2)).toOption
  let (operand, _) ← declaration.toEnumerationTextFieldComparison? (if projected then .category "Label" else .stored)
  let reference : HavingStringRef := { origin := .inner, operand }
  let selection : StarPath := { axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
  let slot := match shape with
    | 0 => HavingFieldListSlot.extent (.group { path := ["Form", "Allowed"], origin := .path, boundRepeatableScope := [] }) [reference]
    | 1 => .extent (.starField ["Form", "Rows"] selection) [reference]
    | 2 => .extent (.starredGroup ["Form", "Rows"] selection) [reference]
    | _ => .direct reference
  let outside ← (certificateModel.lookupUniqueId 3).toOption
  let (member, _) ← outside.toEnumerationTextFieldComparison? .stored
  let source := if literalMembers then HavingFieldValueList.tokenLiterals [slot] [if projected then "y" else "x"]
    else .token [slot] [.direct { origin := .inner, operand := member }]
  pure (source.wellFormedForEnvironments (.quantified .atLeastOne) certificateModel [10] [])

example : [0, 1, 2].all (fun shape => [false, true].all (fun literals => decide (
    certificate shape false literals = some true ∧ certificate shape true literals = some (shape == 1)))) = true ∧
    certificate 3 true true = some true ∧ certificate 3 true false = some true := by native_decide

end A12Kernel.Conformance.HavingMembershipExtent
