import A12Kernel.Elaboration.CheckedDocument

/-! # Checked direct-field computation formal-input inventory

This boundary checks one finite union of direct operand and computed-target fields, then projects every cached finding at selected non-computed operand placements. Collection is eager over the immutable checked document and remains separate from runtime reads, scheduling, message rendering, generated index findings, and group expansion.
-/

namespace A12Kernel

/-- Static failure while binding a direct-field formal-input selection to one checked model. -/
inductive ComputationFormalInputPlanError where
  | operandField (field : FieldId) (cause : ResolveError)
  | computedField (field : FieldId) (cause : ResolveError)
  deriving Repr, DecidableEq

/-- One exact checked operand finding before message rendering. -/
structure ComputationFormalInputFinding where
  address : CellAddr
  cause : FormalCause
  deriving Repr, DecidableEq

/-- One model-checked direct-field inventory. Fields are extensional sets represented as duplicate-free lists. -/
structure CheckedComputationFormalInputPlan (model : FlatModel) where
  private mk ::
  operandFields : List FieldId
  computedFields : List FieldId

/-- Resolve both field sets against one model and discard duplicate authored references before collection. -/
def checkComputationFormalInputPlan (model : FlatModel)
    (operandFields computedFields : List FieldId) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) := do
  let operands := operandFields.eraseDups
  let computed := computedFields.eraseDups
  let _ ← operands.mapM fun field =>
    model.lookupUniqueId field |>.mapError (.operandField field)
  let _ ← computed.mapM fun field =>
    model.lookupUniqueId field |>.mapError (.computedField field)
  pure {
    operandFields := operands
    computedFields := computed
  }

/-- Build the direct-field union and computed-target exclusion set from ordered `(target, dependencies)` operation analyses. -/
def checkComputationFormalInputOperations (model : FlatModel)
    (operations : List (FieldId × List FieldId)) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    (operations.flatMap Prod.snd) (operations.map Prod.fst)

namespace CheckedComputationFormalInputPlan

/-- Whether one declaration belongs to the checked operand union after computed-target exclusion. -/
def includesField (plan : CheckedComputationFormalInputPlan model)
    (field : FieldId) : Bool :=
  plan.operandFields.contains field && !plan.computedFields.contains field

/-- Collect every cached finding at an included exact placement. Physical placement order is retained internally, but consumers compare this inventory extensionally. -/
def findings (plan : CheckedComputationFormalInputPlan model)
    (input : CheckedDocument model) : List ComputationFormalInputFinding :=
  input.checkedCells.flatMap fun placement =>
    if plan.includesField placement.address.field then
      placement.cell.findings.map fun cause => {
        address := placement.address
        cause
      }
    else
      []

end CheckedComputationFormalInputPlan

end A12Kernel
