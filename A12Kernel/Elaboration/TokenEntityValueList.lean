import A12Kernel.Elaboration.TokenEntityList

/-! # Checked mixed String/Enumeration entity-list value lists

This boundary joins two already-certified homogeneous token entity lists to the immutable checked document. Each resolved operand retains its exact String or stored/category Enumeration declaration projection beside the shared canonical topology, addressed payload, hierarchical extent, filter provenance, and positional relevance. Quantifier truth and polarity remain exclusively with `ValueListQuantifier.evalOrdered`.
-/

namespace A12Kernel

inductive TokenEntityValueListFamily where
  | string
  | enumeration
  deriving Repr, DecidableEq

namespace CheckedTokenEntityOperand

def valueListFamily :
    CheckedTokenEntityOperand model → TokenEntityValueListFamily
  | .field source =>
      match source.operand with
      | .string _ => .string
      | .enumeration _ => .enumeration
  | .star source =>
      match source.operand with
      | .string _ => .string
      | .enumeration _ => .enumeration

end CheckedTokenEntityOperand

namespace CheckedTokenEntitySource

/-- A field-valued token-list side is homogeneous at the kernel base-family boundary. Different Enumeration declarations and stored/category projections remain compatible members of the Enumeration family. -/
def valueListFamily? (checked : CheckedTokenEntitySource model) :
    Option TokenEntityValueListFamily :=
  let family := checked.first.valueListFamily
  if checked.rest.all (fun operand => operand.valueListFamily == family) then
    some family
  else
    none

end CheckedTokenEntitySource

/-- The established token entity-list syntax currently checks direct and starred stored projections. Projection-bearing checked sources can enter through `assembleTokenEntityValueListSource` without weakening their certificates. -/
structure SurfaceTokenEntityValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceTokenEntitySource
  values : SurfaceTokenEntitySource
  deriving Repr, DecidableEq

/-- A checked two-sided String or Enumeration value list. Both sides share one base family, and exact direct-reference uniqueness spans the complete authored operation. -/
structure CheckedTokenEntityValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  family : TokenEntityValueListFamily
  fields : CheckedTokenEntitySource model
  values : CheckedTokenEntitySource model
  fieldsFamily : fields.valueListFamily? = some family
  valuesFamily : values.valueListFamily? = some family
  uniqueDirectOperands :
    firstDuplicateDirectTokenField?
      (fields.operands ++ values.operands) = none

inductive TokenEntityValueListElabError where
  | fields (error : TokenEntityElabError)
  | values (error : TokenEntityElabError)
  | mixedFamily
  | duplicateOperand (field : FieldId)
  deriving Repr, DecidableEq

/-- Join two already-checked token sides without reconstructing declarations or erasing Enumeration projection identity. -/
def assembleTokenEntityValueListSource
    (quantifier : ValueListQuantifier)
    (fields values : CheckedTokenEntitySource model) :
    Except TokenEntityValueListElabError
      (CheckedTokenEntityValueListSource model) :=
  match hFields : fields.valueListFamily?,
      hValues : values.valueListFamily? with
  | some fieldsFamily, some valuesFamily =>
      if hFamily : fieldsFamily = valuesFamily then
        match hUnique :
            firstDuplicateDirectTokenField?
              (fields.operands ++ values.operands) with
        | some field => throw (.duplicateOperand field)
        | none =>
            pure {
              quantifier
              family := fieldsFamily
              fields
              values
              fieldsFamily := hFields
              valuesFamily := by simpa [hFamily] using hValues
              uniqueDirectOperands := hUnique
            }
      else
        throw .mixedFamily
  | _, _ => throw .mixedFamily

/-- Check both stored-projection entity-list sides, then apply the operation-wide family and exact-reference gates. -/
def elaborateTokenEntityValueListSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceTokenEntityValueListSource) :
    Except TokenEntityValueListElabError
      (CheckedTokenEntityValueListSource model) := do
  let fields ← elaborateTokenEntitySource model declaringGroup authored.fields
    |>.mapError .fields
  let values ← elaborateTokenEntitySource model declaringGroup authored.values
    |>.mapError .values
  assembleTokenEntityValueListSource authored.quantifier fields values

/-- The rich two-sided addressed token stream consumed by Execute/Transform/Explain clients. -/
structure ResolvedCheckedTokenEntityValueList (model : FlatModel) where
  quantifier : ValueListQuantifier
  family : TokenEntityValueListFamily
  fields : List (ResolvedCheckedTokenEntityOperand model)
  values : List (ResolvedCheckedTokenEntityOperand model)

namespace ResolvedCheckedTokenEntityValueList

/-- Execute through the sole encounter-ordered quantifier evaluator. -/
def evaluate (resolved : ResolvedCheckedTokenEntityValueList model) : Verdict :=
  resolved.quantifier.evalOrdered
    (resolved.fields.map (·.valueListSideAt .validation))
    (resolved.values.map (·.valueListSideAt .validation))

end ResolvedCheckedTokenEntityValueList

namespace CheckedTokenEntityValueListSource

def hasHaving (checked : CheckedTokenEntityValueListSource model) : Bool :=
  checked.fields.hasHaving || checked.values.hasHaving

private def resolveFullFields
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  checked.fields.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand document outer

private def resolveFullValues
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  checked.values.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand document outer

/-- Construct both rich sides in the kernel's operator-specific side order without flattening authored operand boundaries or projection certificates. -/
def resolveFull (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (ResolvedCheckedTokenEntityValueList model) := do
  let (fields, values) ← checked.quantifier.resolveSidesOrdered
    (fun () => checked.resolveFullFields document outer)
    (fun () => checked.resolveFullValues document outer)
  pure {
    quantifier := checked.quantifier
    family := checked.family
    fields
    values
  }

def evaluateFull (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError Verdict := do
  pure (← checked.resolveFull document outer).evaluate

private def resolvePartialFields
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :=
  checked.fields.operands.mapM fun operand =>
    operand.resolveCheckedPartialValidationOperand document outer scope

private def resolvePartialValues
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :=
  checked.values.operands.mapM fun operand =>
    operand.resolveCheckedPartialValidationOperand document outer scope

/-- Partial validation skips a rule containing any filter before topology, relevance, or target reads; otherwise it constructs the same rich ordered operands with positional nonrelevance. -/
def evaluatePartial (checked : CheckedTokenEntityValueListSource model)
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

end CheckedTokenEntityValueListSource

end A12Kernel
