import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Elaboration.ComputationGroupDependency

/-! # Checked direct-field computation formal-input inventory

This boundary checks one finite union of direct operand and computed-target fields, projects every cached finding at selected non-computed operand placements, and composes the selected generated index-preliminary findings after full-call default staging. Collection is eager over the immutable checked document and remains separate from runtime reads, scheduling, message rendering, and group expansion.
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

/-- One computation-call input preparation. The preliminary view supplies transient index defaults to execution while the finding inventory remains a separate eager public channel. -/
structure ComputationFormalInputPreparation (model : FlatModel) where
  private mk ::
  preliminary : CheckedIndexPreliminary model
  formalErrorsInOperands : List ComputationFormalInputFinding

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

/-- Bind a call whose computations have no explicit group profile suppressing their implicit row
guards. Specialized operation carriers use this boundary; guarded tables supply their expanded
inventory to `checkComputationFormalInputPlan` instead (`spec/09` formal-input scope). -/
def checkImplicitGuardFormalInputPlan (model : FlatModel)
    (operandFields computedFields : List FieldId) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  let implicitFields := model.fields.filter fun field => computedFields.any fun target =>
    model.computationImplicitOperand target (fun (_ : Unit) => none) [] field.id
  checkComputationFormalInputPlan model
    (operandFields ++ implicitFields.map (·.id)) computedFields

/-- Union specialized operations with unsuppressed implicit row guards before excluding targets. -/
def checkImplicitGuardFormalInputOperations (model : FlatModel)
    (operations : List (FieldId × List FieldId)) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkImplicitGuardFormalInputPlan model (operations.flatMap Prod.snd) (operations.map Prod.fst)

namespace CheckedComputationFormalInputPlan

/-- Whether one declaration belongs to the checked operand union after computed-target exclusion. -/
def includesField (plan : CheckedComputationFormalInputPlan model)
    (field : FieldId) : Bool :=
  plan.operandFields.contains field && !plan.computedFields.contains field

/-- The duplicate-free operand fields that survive computed-target exclusion. -/
def selectedFields (plan : CheckedComputationFormalInputPlan model) :
    List FieldId :=
  plan.operandFields.filter fun field => !plan.computedFields.contains field

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

/-- Project generated mandatory and uniqueness findings only at selected noncomputed operand indexes. -/
def preliminaryFindings (plan : CheckedComputationFormalInputPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    List ComputationFormalInputFinding :=
  preliminary.findings.filterMap fun finding =>
    if plan.includesField finding.address.field then
      some {
        address := finding.address
        cause := finding.kind.cause
      }
    else
      none

/-- Combine eager cached input findings with selected generated preliminary findings. The inventory remains independent of subsequent runtime reachability. -/
def findingsIncludingPreliminary
    (plan : CheckedComputationFormalInputPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    List ComputationFormalInputFinding :=
  plan.findings preliminary.base ++ plan.preliminaryFindings preliminary

/-- Prepare one computation call by collecting cached findings first, staging full-call index defaults, and running preliminary rules only for selected index operands. -/
def prepare (plan : CheckedComputationFormalInputPlan model)
    (input : CheckedDocument model) :
    Except CheckedIndexPreliminaryError
      (ComputationFormalInputPreparation model) := do
  let cached := plan.findings input
  let preliminary ←
    input.applySelectedFullIndexPreliminary plan.selectedFields
  pure {
    preliminary
    formalErrorsInOperands := cached ++ plan.preliminaryFindings preliminary
  }

end CheckedComputationFormalInputPlan

/-- Failure of a computation run composed with its selected formal-input preparation: the plan, the
preparation, or the run, the last beside the eager findings it was handed. -/
inductive ComputationFormalInputRunFault (Cause : Type) where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding) (cause : Cause)
  deriving Repr, DecidableEq

/-- Prepare a plan's selected sources once, retain every eager finding, and run lazily through the
prepared read, so a run fault keeps the findings it was handed. -/
def runWithFormalInputs {Cause Result : Type}
    (planned : Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model))
    (input : CheckedDocument model)
    (run : (CellAddr → Except CheckedDocumentError CheckedCell) →
      List ComputationFormalInputFinding → Except Cause Result) :
    Except (ComputationFormalInputRunFault Cause) Result := do
  let plan ← planned |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match run prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause => .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end A12Kernel
