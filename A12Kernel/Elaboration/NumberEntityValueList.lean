import A12Kernel.Elaboration.NumberEntityList

/-! # Checked mixed Number entity-list value lists

This boundary joins two already-certified Number entity lists to the immutable checked document. Each resolved operand retains its checked declaration, canonical topology, complete selected environments and addresses, exact stored payload, hierarchical tail, filter marker, and positional partial-relevance fact. Quantifier truth and polarity remain exclusively with `ValueListQuantifier.evalOrdered`.
-/

namespace A12Kernel

/-- Both authored sides use the common direct/plain-star/filtered-star Number entity-list shape. -/
structure SurfaceNumberEntityValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceNumberEntitySource
  values : SurfaceNumberEntitySource
  deriving Repr, DecidableEq

/-- A checked two-sided Number value list. Direct-reference uniqueness spans both authored sides; wildcard occurrences remain independent. -/
structure CheckedNumberEntityValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  fields : CheckedNumberEntitySource model
  values : CheckedNumberEntitySource model
  uniqueDirectOperands :
    firstDuplicateDirectNumberEntityField?
      (fields.operands ++ values.operands) = none

inductive NumberEntityValueListElabError where
  | fields (error : NumberEntityElabError)
  | values (error : NumberEntityElabError)
  | duplicateOperand (field : FieldId)
  deriving Repr, DecidableEq

/-- Check both ordinary entity-list shapes, then apply the parser's combined direct-reference uniqueness gate. -/
def elaborateNumberEntityValueListSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceNumberEntityValueListSource) :
    Except NumberEntityValueListElabError
      (CheckedNumberEntityValueListSource model) := do
  let fields ← elaborateNumberEntitySource model declaringGroup authored.fields
    |>.mapError .fields
  let values ← elaborateNumberEntitySource model declaringGroup authored.values
    |>.mapError .values
  match hUnique : firstDuplicateDirectNumberEntityField?
      (fields.operands ++ values.operands) with
  | some field => throw (.duplicateOperand field)
  | none => pure {
      quantifier := authored.quantifier
      fields
      values
      uniqueDirectOperands := hUnique }

/-- The rich two-sided addressed stream consumed by Execute/Transform/Explain clients. -/
structure ResolvedCheckedNumberEntityValueList (model : FlatModel) where
  quantifier : ValueListQuantifier
  fields : List (ResolvedCheckedNumberEntityOperand model)
  values : List (ResolvedCheckedNumberEntityOperand model)

namespace ResolvedCheckedNumberEntityValueList

/-- Execute through the sole encounter-ordered quantifier evaluator. -/
def evaluate (resolved : ResolvedCheckedNumberEntityValueList model) : Verdict :=
  resolved.quantifier.evalOrdered
    (resolved.fields.map (·.valueListSideAt .validation))
    (resolved.values.map (·.valueListSideAt .validation))

end ResolvedCheckedNumberEntityValueList

namespace CheckedNumberEntityValueListSource

def hasHaving (checked : CheckedNumberEntityValueListSource model) : Bool :=
  checked.fields.hasHaving || checked.values.hasHaving

private def resolveFullFields
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  checked.fields.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand document outer

private def resolveFullValues
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  checked.values.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand document outer

/-- Construct both rich sides in the kernel's operator-specific side order, without flattening authored operand boundaries. -/
def resolveFull (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityValueList model) := do
  let (fields, values) ← checked.quantifier.resolveSidesOrdered
    (fun () => checked.resolveFullFields document outer)
    (fun () => checked.resolveFullValues document outer)
  pure { quantifier := checked.quantifier, fields, values }

/-- Resolve and execute full validation while retaining structural addressing failure outside the semantic verdict. -/
def evaluateFull (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError Verdict := do
  pure (← checked.resolveFull document outer).evaluate

private def resolvePartialFields
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :=
  checked.fields.operands.mapM fun operand =>
    operand.resolveCheckedPartialValidationOperand document outer scope

private def resolvePartialValues
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :=
  checked.values.operands.mapM fun operand =>
    operand.resolveCheckedPartialValidationOperand document outer scope

/-- Partial validation skips a rule containing any filter before topology, relevance, or target reads; otherwise it constructs the same rich ordered operands with positional nonrelevance. -/
def evaluatePartial (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialHavingValueListResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    let (fields, values) ← checked.quantifier.resolveSidesOrdered
      (fun () => checked.resolvePartialFields document outer scope)
      (fun () => checked.resolvePartialValues document outer scope)
    pure (.evaluated (checked.quantifier.evalOrdered
      (fields.map (·.valueListSideAt .validation))
      (values.map (·.valueListSideAt .validation))))

end CheckedNumberEntityValueListSource

end A12Kernel
