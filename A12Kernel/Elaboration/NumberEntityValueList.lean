import A12Kernel.Elaboration.NumberEntityList

/-! # Checked mixed Number entity-list value lists

This boundary joins two already-certified Number entity lists to the immutable checked document. Each resolved operand retains its checked declaration, canonical topology, complete selected environments and addresses, exact stored payload, hierarchical tail, filter marker, and positional partial-relevance fact. Full validation uses the restartable `ValueListQuantifier.evalValidationUsing`; materialized and partial views retain `evalOrdered`.
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
  | crossListRepeat (error : FieldEntityShapeElabError)
  deriving Repr, DecidableEq

/-- Check both nonempty, sole-allowed entity-list sides before the combined duplicate/ancestor
gate. Each side keeps its original shape and Number-certification order. -/
def elaborateNumberEntityValueListSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceNumberEntityValueListSource) (targetGroup? : Option GroupPath := none)
    (writtenGroup : GroupPath := declaringGroup) (bindingGroup? : Option GroupPath := none) :
    Except NumberEntityValueListElabError
      (CheckedNumberEntityValueListSource model) := do
  let bindingGroup? := bindingGroup?.or targetGroup?
  let scope := bindingGroup?.map model.repeatableScopeForGroupPath |>.getD []
  let groupReadScope : FixedGroupReadScope :=
    if bindingGroup?.isSome && targetGroup?.isNone then .ruleBound else .scalar
  let fieldsShape ← elaborateFieldEntityShapeIn model declaringGroup scope authored.fields
      .soleAllowed targetGroup? (writtenGroup := targetGroup?.getD writtenGroup)
      (groupReadScope := groupReadScope)
    |>.mapError (.fields ∘ .shape)
  let fields ← certifyNumberEntityShape model declaringGroup fieldsShape
      (bindingGroup?.getD declaringGroup) |>.mapError .fields
  let valuesShape ← elaborateFieldEntityShapeIn model declaringGroup scope authored.values
      .soleAllowed targetGroup? (writtenGroup := targetGroup?.getD writtenGroup)
      (groupReadScope := groupReadScope)
    |>.mapError (.values ∘ .shape)
  let values ← certifyNumberEntityShape model declaringGroup valuesShape
      (bindingGroup?.getD declaringGroup) |>.mapError .values
  match hUnique : firstDuplicateDirectNumberEntityField?
      (fields.operands ++ values.operands) with
  | some field => throw (.duplicateOperand field)
  | none =>
      if let some error := crossFieldEntityListRepeat? (fieldsShape.operands ++ valuesShape.operands) then
        throw (.crossListRepeat error)
      else pure {
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

/-- Number membership streams preserve the consumer's stopping point inside a filtered
operand as well as between authored operands. Only AtLeastOne opts into sparse traversal. -/
def CheckedNumberEntitySource.scanValidationMembership
    (source : CheckedNumberEntitySource model) (quantifier : ValueListQuantifier)
    (document : CheckedDocument model) (outer : Env) (world : Option World := none) :
    ValidationValueListScanner .number CheckedAddressingError := fun _ _ consume state =>
  scanValidationValueListOperands (fun operand state => do
    match operand with
    | .starHaving filtered =>
        match consume state (.operand true) with
        | .inr result => pure (.inr result)
        | .inl next =>
            filtered.source.source.scanValidationCells filtered.having document outer
              (fun state cell => consume state (.cell true ((observeCell .validation cell.cell).asNumberValueListCell)))
              next (if quantifier == .atLeastOne then .sparse else .dense) world
    | _ =>
        let side ← operand.checkedValidationSide (world := world) (missingStarIsOmitted := true) document outer
        pure (side.scanValidationMembership consume state)) source.operands state

namespace CheckedNumberEntityValueListSource

def hasHaving (checked : CheckedNumberEntityValueListSource model) : Bool :=
  checked.fields.hasHaving || checked.values.hasHaving

private def resolveFullFields
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :=
  checked.fields.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand (world := world) document outer

private def resolveFullValues
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :=
  checked.values.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand (world := world) document outer

/-- Construct both rich sides in the kernel's operator-specific side order, without flattening authored operand boundaries. -/
def resolveFull (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityValueList model) := do
  let (fields, values) ← checked.quantifier.resolveSidesOrdered
    (fun () => checked.resolveFullFields (world := world) document outer)
    (fun () => checked.resolveFullValues (world := world) document outer)
  pure { quantifier := checked.quantifier, fields, values }

/-- Resolve and execute full validation while retaining structural addressing failure outside the semantic verdict. -/
def evaluateFull (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError Verdict := do
  checked.quantifier.evalValidationUsing
    (checked.fields.scanValidationMembership checked.quantifier document outer world)
    (checked.values.scanValidationMembership checked.quantifier document outer world)

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
