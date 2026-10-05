import A12Kernel.Semantics.CorrelationInputs
import A12Kernel.Semantics.ComputationValueList

namespace A12Kernel

/-- Direct field-valued membership retains each operand's origin and checked value domain.
Category identity remains in the token operand, independently of its physical field ID (spec/06 §B.4). -/
inductive HavingFieldValueList where
  | number (subjects members : List HavingNumberRef)
  | token (subjects members : List HavingStringRef)
  deriving Repr, DecidableEq

namespace HavingFieldValueList

def references : HavingFieldValueList → List HavingPresenceRef
  | .number subjects members => (subjects ++ members).map fun ref => { origin := ref.origin, field := ref.field.id }
  | .token subjects members => (subjects ++ members).map fun ref => { origin := ref.origin, field := ref.field.id }

/-- The common selector owns traversal; this fold supplies typed, origin-sensitive singleton reads
without materializing an operand before the selector asks for it (spec/06 §B.5). -/
def foldOperands (source : HavingFieldValueList) (phase : Phase)
    (read : HavingOrigin → FieldId → Except Error CheckedCell)
    (consume : {kind : ValueListKind} → {ref : Type} →
      (ref → Except Error (ResolvedValueListSide kind)) → List ref → List ref → Except Error Result) :
    Except Error Result :=
  match source with
  | .number subjects members => consume (fun (ref : HavingNumberRef) => do
      let cell ← read ref.origin ref.field.id
      pure {
        cells := [ref.field.valueListCellAt phase { read := fun _ => cell }],
        hasUninstantiatedTail := false, hasHaving := false }) subjects members
  | .token subjects members => consume (fun (ref : HavingStringRef) => do
      let cell ← read ref.origin ref.field.id
      pure {
        cells := [ref.operand.checkedValueListCellAt phase cell],
        hasUninstantiatedTail := false, hasHaving := false }) subjects members

def evalValidationRead (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (read : HavingOrigin → FieldId → Except Error CheckedCell) : Except Error Verdict :=
  source.foldOperands .validation read fun resolve subjects members => do
    let quantifier := match operator with | .scalar op => op.quantifier | .quantified op => op
    let (subjects, members) ← quantifier.resolveSidesOrdered
      (fun _ => subjects.mapM resolve) (fun _ => members.mapM resolve)
    pure (quantifier.evalOrdered subjects members)

def evalComputationRead (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (read : HavingOrigin → FieldId → Except Error CheckedCell) : Except Error ComputationConditionResult :=
  source.foldOperands .computation read fun resolve subjects members =>
    operator.evalUsing (fun _ => ValueListQuantifier.collectOperands resolve members [])
      (fun predicate => ValueListQuantifier.anyOperands resolve predicate subjects)

def evalValidation (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (read : HavingOrigin → FieldId → CheckedCell) : Verdict :=
  match source.evalValidationRead operator (fun origin field => Except.ok (ε := Empty) (read origin field)) with
  | .ok result => result
  | .error impossible => nomatch impossible

def evalComputation (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (read : HavingOrigin → FieldId → CheckedCell) : ComputationConditionResult :=
  match source.evalComputationRead operator (fun origin field => Except.ok (ε := Empty) (read origin field)) with
  | .ok result => result
  | .error impossible => nomatch impossible

end HavingFieldValueList
end A12Kernel
