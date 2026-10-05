import A12Kernel.Semantics.CorrelationInputs
import A12Kernel.Semantics.ComputationValueList

namespace A12Kernel

/-- Membership over direct fields retains each operand's origin and checked value domain.
Category identity remains in the token operand, independently of its physical field ID (spec/06 §B.4). -/
inductive HavingFieldValueList where
  | number (subjects members : List HavingNumberRef)
  | token (subjects members : List HavingStringRef)
  | tokenLiterals (subjects : List HavingStringRef) (members : List String)
  deriving Repr, DecidableEq

namespace HavingFieldValueList

def references : HavingFieldValueList → List HavingPresenceRef
  | .number subjects members => (subjects ++ members).map fun ref => { origin := ref.origin, field := ref.field.id }
  | .token subjects members => (subjects ++ members).map fun ref => { origin := ref.origin, field := ref.field.id }
  | .tokenLiterals subjects _ => subjects.map fun ref => { origin := ref.origin, field := ref.field.id }

/-- The common selector owns traversal; this fold supplies typed, origin-sensitive singleton reads
without materializing an operand before the selector asks for it (spec/06 §B.5). -/
def foldOperands (source : HavingFieldValueList) (phase : Phase)
    (read : HavingOrigin → FieldId → Except Error CheckedCell)
    (consume : {kind : ValueListKind} → {subject member : Type} →
      (subject → Except Error (ResolvedValueListSide kind)) →
      (member → Except Error (ResolvedValueListSide kind)) →
      List subject → List member → Except Error Result) : Except Error Result :=
  let number (ref : HavingNumberRef) : Except Error (ResolvedValueListSide .number) := do
    let cell ← read ref.origin ref.field.id
    pure {
      cells := [ref.field.valueListCellAt phase { read := fun _ => cell }],
      hasUninstantiatedTail := false, hasHaving := false }
  let token (ref : HavingStringRef) : Except Error (ResolvedValueListSide .token) := do
    let cell ← read ref.origin ref.field.id
    pure {
      cells := [ref.operand.checkedValueListCellAt phase cell],
      hasUninstantiatedTail := false, hasHaving := false }
  match source with
  | .number subjects members => consume number number subjects members
  | .token subjects members => consume token token subjects members
  | .tokenLiterals subjects members => consume token (fun value => pure {
      cells := [.present value], hasUninstantiatedTail := false, hasHaving := false }) subjects members

def evalValidationRead (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (read : HavingOrigin → FieldId → Except Error CheckedCell) : Except Error Verdict :=
  source.foldOperands .validation read fun resolveSubject resolveMember subjects members => do
    let quantifier := match operator with | .scalar op => op.quantifier | .quantified op => op
    let (subjects, members) ← quantifier.resolveSidesOrdered
      (fun _ => subjects.mapM resolveSubject) (fun _ => members.mapM resolveMember)
    pure (quantifier.evalOrdered subjects members)

def evalComputationRead (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (read : HavingOrigin → FieldId → Except Error CheckedCell) : Except Error ComputationConditionResult :=
  source.foldOperands .computation read fun resolveSubject resolveMember subjects members =>
    operator.evalUsing (fun _ => ValueListQuantifier.collectOperands resolveMember members [])
      (fun predicate => ValueListQuantifier.anyOperands resolveSubject predicate subjects)

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
