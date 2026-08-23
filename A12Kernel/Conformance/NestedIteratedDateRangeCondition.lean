import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.ValidationCondition.Assembly

/-! # A DateRange condition at a two-level iterating locus

A rule iterating a nested repeatable group binds **both** levels, so it admits an operand at the
root, at the enclosing row, or at the leaf, and each operand is read at its own path inside the
current leaf. The correlating case is the middle-level operand: it must reach its own enclosing
row's cell and not row one's, which the runtime rows separate by giving two enclosing rows
different values so a borrowed row-one read inverts the verdict pattern instead of merely shifting
it.

The refusal direction stays the shared locus class: a **leaf** operand read from a rule that
iterates only the enclosing row crosses a level that locus does not bind.
-/

namespace A12Kernel.Conformance.NestedIteratedDateRangeCondition

open A12Kernel

private def rangeField (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
}

private def rootRange := rangeField 1 "RootRange" ["Form"] []
private def rowRange := rangeField 2 "RowRange" ["Form", "Rows"] [10]
private def leafRange :=
  rangeField 3 "LeafRange" ["Form", "Rows", "Inner"] [10, 20]

private def model : FlatModel := {
  fields := [rootRange, rowRange, leafRange]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3 },
    { level := 20, path := ["Form", "Rows", "Inner"], repeatability := some 3 }]
}

private def path (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def rootPath := path ["Form"] "RootRange"
private def rowPath := path ["Form", "Rows"] "RowRange"
private def leafPath := path ["Form", "Rows", "Inner"] "LeafRange"

private def leafGroup : GroupPath := ["Form", "Rows", "Inner"]

private def condition? (rowGroup : GroupPath) (left right : SurfaceFieldPath)
    (op : EqualityOp := .equal) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  CheckedValidationCondition.fromIteratedDateRangeEquality model rowGroup
    op left right

/-- The locus class travels on the shared field-reference resolver, which is where the
missing-wildcard diagnostic lives. -/
private def refusal? (rowGroup : GroupPath) (left right : SurfaceFieldPath) :
    Option KernelStaticDiagnostic :=
  match condition? rowGroup left right with
  | .error (.fieldReference error) => error.diagnostic?
  | _ => none

/- The two-level locus binds both levels, so it admits an operand at any of the three scopes in
either authored slot. -/
example :
    (condition? leafGroup leafPath rowPath).isOk = true ∧
      (condition? leafGroup rowPath leafPath).isOk = true ∧
      (condition? leafGroup leafPath rootPath).isOk = true ∧
      (condition? leafGroup leafPath leafPath).isOk = true := by
  native_decide

/- A leaf operand read from a rule that iterates only the enclosing row is refused with the shared
locus class, and so is a middle operand read from the nonrepeatable root. -/
example :
    refusal? ["Form", "Rows"] rowPath leafPath = some .noWildcard ∧
      refusal? ["Form"] rootPath rowPath = some .noWildcard ∧
      (condition? ["Form", "Rows"] rowPath rootPath).isOk = true := by
  native_decide

/- The leaf-locus condition derives the whole two-level scope and requires the addressed evaluator,
so nothing silently reads leaf one of row one. -/
example :
    (match (condition? leafGroup leafPath rowPath).toOption with
      | some checked =>
          (match checked.core.ordinaryIterationScope with
            | .ok (some scope) => scope == [10, 20]
            | _ => false) && checked.core.requiresAddressedValidation
      | none => false) = true := by
  native_decide

private def storedCell (field : FieldId) (path : List Nat) (stored : String) :
    ClassifiedCellInput := {
  address := { field, path }
  stored
  raw :=
    match model.lookupUniqueId field with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
              policy stored).toOption.getD .empty
        | none => .empty
    | .error _ => .empty
}

private def june := "2024-06-01/2024-06-30"
private def july := "2024-07-01/2024-07-31"

/-- Two enclosing rows carry **different** ranges, and each row's two leaves are arranged so that a
read of row one's cell would invert the verdict pattern on the second row rather than shift it. -/
private def correlatedData : DocumentData := {
  instantiatedRows :=
    [{ group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
      { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]
  cells := [
    storedCell rowRange.id [1] june,
    storedCell rowRange.id [2] july,
    storedCell leafRange.id [1, 1] june,
    storedCell leafRange.id [1, 2] july,
    storedCell leafRange.id [2, 1] july,
    storedCell leafRange.id [2, 2] june]
}

private def leafVerdicts? (op : EqualityOp) (data : DocumentData) :
    Option (List (Env × Verdict)) := do
  let checked ← (condition? leafGroup leafPath rowPath op).toOption
  let rule ← (assembleResolvedValidationRule model checked leafRange.id
    "nestedIteratedDateRangeEquality" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

/- Each leaf is judged against **its own** enclosing row's range. Row one's matching leaf fires and
its differing leaf does not; row two's matching leaf is the one holding July, so a read of row one's
June cell would have fired on the other leaf of that row instead. -/
example :
    leafVerdicts? .equal correlatedData = some [
      ([(10, 1), (20, 1)], .fired .value),
      ([(10, 1), (20, 2)], .notFired),
      ([(10, 2), (20, 1)], .fired .value),
      ([(10, 2), (20, 2)], .notFired)
    ] := by
  native_decide

/- The complementary direction inverts every leaf, which keeps the polarity account separate from
the addressing one. -/
example :
    leafVerdicts? .notEqual correlatedData = some [
      ([(10, 1), (20, 1)], .notFired),
      ([(10, 1), (20, 2)], .fired .value),
      ([(10, 2), (20, 1)], .notFired),
      ([(10, 2), (20, 2)], .fired .value)
    ] := by
  native_decide

/- An enclosing operand that is absent leaves every leaf beneath it unfired at both polarities,
while the sibling row's leaves still decide on their own cells. -/
example :
    leafVerdicts? .equal {
      correlatedData with
        cells := correlatedData.cells.filter fun cell =>
          cell.address != { field := rowRange.id, path := [1] } } = some [
      ([(10, 1), (20, 1)], .notFired),
      ([(10, 1), (20, 2)], .notFired),
      ([(10, 2), (20, 1)], .fired .value),
      ([(10, 2), (20, 2)], .notFired)
    ] := by
  native_decide

end A12Kernel.Conformance.NestedIteratedDateRangeCondition
