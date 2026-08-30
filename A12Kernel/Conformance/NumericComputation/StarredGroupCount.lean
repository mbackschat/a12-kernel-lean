import A12Kernel.Elaboration.NumericComputation

/-! # Static admission of a starred group-count operand in the computation arm

`NumberOfFilledGroups` admits a starred repeatable operand, alone or beside a fixed one, and the
arity gate is conditional on the star: one operand is legal exactly when it is starred, while the
two-operand minimum governs the unstarred form. All four rows are measured on both Kernel codegen
strategies at the [starred group-count
checkpoint](../../../docs/SOURCES.md#src-starred-group-count-computation) through
`computation add --dry-run`, each `verification: KERNEL_CONFIRMED`.

The runtime half is locked here too, against the same checkpoint's counted rows. The starred operand's contribution is a row count, whose
fold is owned by `numberOfFilledGroupsForComputationOperands` and locked at the clause in
`Conformance/StarredGroupCountComputation.lean`; what these cases add is that a checked operand list
reaches it over a real document. The scalar route has no row topology and refuses, which is correct
rather than incomplete.
-/

namespace A12Kernel.Conformance.NumericComputation.StarredGroupCount

open A12Kernel

private def flatValueId : FieldId := 0
private def rowValueId : FieldId := 1
private def targetId : FieldId := 2
private def otherValueId : FieldId := 3

private def numberPolicy : FieldPolicy := { kind := .number { scale := 0, signed := true } }

private def numberIn (id : FieldId) (groupPath : GroupPath) (name : String) : FlatFieldDecl where
  id
  groupPath
  name
  policy := numberPolicy

private def rowsLevel : RepeatableLevel := 10

/-- One fixed group beside a repeatable one, both under the declaring root, mirroring the shape of
    the model the checkpoint above measured. -/
private def model : FlatModel :=
  { fields :=
      [ numberIn flatValueId ["Probe", "Flat"] "FlatValue"
      , numberIn otherValueId ["Probe", "Other"] "OtherValue"
      , { numberIn rowValueId ["Probe", "Rows"] "RowValue" with
            repeatableScope := [rowsLevel] }
      , numberIn targetId ["Probe"] "Target" ]
    repeatableGroups :=
      [{ level := rowsLevel, path := ["Probe", "Rows"], repeatability := some 5 }] }

private def fixedOperand (path : GroupPath) : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := path })

/-- `Rows*` — the wildcard sits on the terminal group. -/
private def starredOperand : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "Rows"] }

/-- `Rows` without its star, which the Kernel refuses. -/
private def unstarredRepeatable : SurfaceGroupCountOperand :=
  fixedOperand ["Probe", "Rows"]

private def admissionOf (operands : List SurfaceGroupCountOperand) :
    Except NumericComputationElabError Unit :=
  (elaborateNumericComputationOperation model ["Probe"] targetId
    (.atom (.filledGroupCount operands))).map fun _ => ()

private def admitted (operands : List SurfaceGroupCountOperand) : Bool :=
  (admissionOf operands).toOption.isSome

/- A single starred operand is a complete list. This is the row that shows the arity gate is not
   an operand count: the same group unstarred is refused below, and a lone fixed operand is too. -/
example : admitted [starredOperand] = true := by
  native_decide

/- The mixed list, admitted. Its two operands contribute unlike quantities at runtime. -/
example : admitted [fixedOperand ["Probe", "Flat"], starredOperand] = true := by
  native_decide

/- A repeatable operand written without its star is refused. Measured `MVK_NO_WILDCARD`. -/
example : admitted [unstarredRepeatable] = false := by
  native_decide

/- A lone fixed operand is refused for a different reason — measured `MVK_PARAMSIZE_INVALIDGN`,
   *"There must be more than one group"* — which is what makes the first row a statement about
   the star rather than about arity. -/
example : admitted [fixedOperand ["Probe", "Flat"]] = false := by
  native_decide

/- The established fixed pair still elaborates, so admitting the starred form widened the operand
   list without disturbing the form that was already there. -/
example : admitted [fixedOperand ["Probe", "Flat"], fixedOperand ["Probe", "Other"]] = true := by
  native_decide

/-! ## Runtime -/

private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }

private def filledNumber : CheckedCell :=
  { rawPresent := true, parsed := some (.num 1), findings := [] }

/-- `n` instantiated rows of the repeatable group, none of them carrying a cell. -/
private def documentWith (rows : Nat) : Document :=
  { instantiatedRows := (List.range rows).map fun index =>
      { group := rowsLevel, path := [index + 1] }
    rawCells := fun _ => none }

private def evaluationContext (flatFilled : Bool) (rows : Nat) :
    NumericComputationEvaluationContext :=
  { scalar := { read := fun id => if id == flatValueId && flatFilled then filledNumber else emptyCell }
    document := documentWith rows
    outer := []
    filterRead := fun _ _ => emptyCell
    starRead := fun _ _ => emptyCell }

private def countOf (operands : List SurfaceGroupCountOperand)
    (flatFilled : Bool) (rows : Nat) : Option NumericComputationResult :=
  match elaborateNumericComputationOperation model ["Probe"] targetId
      (.atom (.filledGroupCount operands)) with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom atom =>
          ((evaluationContext flatFilled rows).readCheckedNumericComputationAtom atom).toOption
      | _ => none


private def mixedList : List SurfaceGroupCountOperand :=
  [fixedOperand ["Probe", "Flat"], starredOperand]

private def scalarCountOf (operands : List SurfaceGroupCountOperand) :
    Option NumericComputationFault :=
  match elaborateNumericComputationOperation model ["Probe"] targetId
      (.atom (.filledGroupCount operands)) with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom atom =>
          match ScalarComputationContext.readCheckedNumericComputationAtom
              { read := fun _ => emptyCell } atom with
          | .error fault => some fault
          | .ok _ => none
      | _ => none

/- The starred operand alone contributes the instantiated row count. No row here carries a cell at
   all, so three rows counting three is the discriminator: a presence account answers one. -/
example :
    [countOf [starredOperand] true 0, countOf [starredOperand] true 1,
      countOf [starredOperand] true 2, countOf [starredOperand] true 3] =
      [some (.value 0), some (.value 1), some (.value 2), some (.value 3)] := by
  native_decide

/- The mixed list, in the arithmetic a12-dmkits measured independently on its own model: the fixed
   operand's zero-or-one plus the starred operand's cardinality, into one sum. Row two is the
   separator — emptying the fixed group drops the total by exactly one while every row still
   counts, so the two contributions are independent and unlike. -/
example :
    [countOf mixedList true 3, countOf mixedList false 3,
      countOf mixedList true 0, countOf mixedList false 0] =
      [some (.value 4), some (.value 3), some (.value 1), some (.value 0)] := by
  native_decide

/- The scalar route refuses the same checked atom rather than answering a fixed-only count for it.
   Its whole input is a cell read, so this is a correct refusal and not a missing case. -/
example : scalarCountOf mixedList = some .repeatableContextRequired := by
  native_decide

end A12Kernel.Conformance.NumericComputation.StarredGroupCount
