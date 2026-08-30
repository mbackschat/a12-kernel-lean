import A12Kernel.Elaboration.NumericComputation

/-! # Static admission of a starred group-count operand in the computation arm

`NumberOfFilledGroups` admits a starred repeatable operand, alone or beside a fixed one, and the
arity gate is conditional on the star: one operand is legal exactly when it is starred, while the
two-operand minimum governs the unstarred form. All four rows are measured on both Kernel codegen
strategies at the [starred group-count
checkpoint](../../../docs/SOURCES.md#src-starred-group-count-computation) through
`computation add --dry-run`, each `verification: KERNEL_CONFIRMED`.

These cases lock **admission only**. The starred operand's contribution is a row count, whose
meaning is owned by `numberOfFilledGroupsForComputationOperands` and locked separately in
`Conformance/StarredGroupCountComputation.lean`; evaluating one needs the document's row topology,
which the scalar route does not carry and refuses for.
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

end A12Kernel.Conformance.NumericComputation.StarredGroupCount
