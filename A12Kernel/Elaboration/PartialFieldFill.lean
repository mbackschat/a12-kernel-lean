import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.DeclaredPartialFields

namespace A12Kernel

private def unavailableFill : ValidationFillTally :=
  { filled := 0, empty := 0, unknown := 1, uninstantiated := 0 }

private def emptyFill : ValidationFillTally :=
  { filled := 0, empty := 0, unknown := 0, uninstantiated := 0 }

private def partialFillFields (model : FlatModel) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (fields : DeclaredPartialFields) : Except CheckedAddressingError ValidationFillTally :=
  fields.addresses.foldlM (fun tally (declaration, row) => do
    let some cell ← fields.readCell? model scope read declaration row
      | return tally.combine unavailableFill
    pure (tally.combine (observeCell .validation cell).asValidationFillTally)) emptyFill

private def partialSelectedFill
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError ValidationFillTally := do
  match ← resolveDeclaredPartialSelected source document scope outer read with
  | none | some (.unknown _) | some (.poison _) => pure unavailableFill
  | some .empty => pure { emptyFill with empty := 1 }
  | some (.value fields) => partialFillFields model scope read fields

private def CheckedFieldFillOperand.partialFillTally (operand : CheckedFieldFillOperand model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError ValidationFillTally := do
  match operand with
  | .indexed source => partialSelectedFill (.inl source) document scope outer read
  | .keyed source => partialSelectedFill (.inr source) document scope outer read
  | .field declaration => partialFillFields model scope read { addresses := [(declaration, outer)] }
  | .star source =>
      let some rows ← source.source.path.declaredEnvironments? outer |>.mapError .addressing
        | return unavailableFill
      partialFillFields model scope read { addresses := rows.map (source.source.declaration, ·) }
  | .group source =>
      let some fields ← declaredPartialFields? model source.declarations source.source.boundLevelCount outer
        | return unavailableFill
      partialFillFields model scope read fields

/-- Unfiltered partial fill retains each declared slot's relevance, including missing rows.
The seven quantifiers share the existing tally laws: unavailable cells neither witness presence
nor absence, but do prevent a universal conclusion (KF527, spec/10 §5). The supplied call-local
reader preserves silent preliminary unavailability; no document row is materialized. -/
def CheckedFieldFillList.evaluatePartialFill (list : CheckedFieldFillList model)
    (operator : FieldFillQuantifier) (document : CheckedDocument model)
    (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError Verdict := do
  if list.hasHaving then return .unknown
  let tally ← list.operands.foldlM (fun tally operand => do
    pure (tally.combine (← operand.partialFillTally document scope outer read))) emptyFill
  pure (operator.evalValidation tally).asConservativeVerdict

end A12Kernel
