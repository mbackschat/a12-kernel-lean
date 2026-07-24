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

/-- One authored Number operand resolved against the immutable checked input. The source retains declaration/filter metadata; the optional topology retains every canonical candidate environment, while `addressedCells` retains exactly the relevant or filter-selected cells that were read. -/
structure ResolvedCheckedNumberEntityOperand (model : FlatModel) where
  private mk ::
  source : CheckedNumberEntityOperand model
  topology : Option ResolvedStarTopology
  addressedCells : List CheckedAddressedCell
  hasUninstantiatedTail : Bool
  hasHaving : Bool
  hasNonRelevant : Bool

namespace ResolvedCheckedNumberEntityOperand

/-- Project the rich addressed operand to the existing semantic side without losing its operand-local structural metadata. -/
def valueListSideAt (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) : ResolvedValueListSide .number :=
  { cells := resolved.addressedCells.map fun addressed =>
      (observeCell phase addressed.cell).asNumberValueListCell
    hasUninstantiatedTail := resolved.hasUninstantiatedTail
    hasHaving := resolved.hasHaving
    hasNonRelevant := resolved.hasNonRelevant }

end ResolvedCheckedNumberEntityOperand

private def addressNumberEnvironments (document : CheckedDocument model)
    (field : FlatNumberField) (environments : List Env) :
    Except CheckedAddressingError (List CheckedAddressedCell) :=
  environments.mapM fun environment =>
    document.addressedCell environment field.id

namespace CheckedNumberEntityOperand

/-- Resolve one full-validation operand through the sole checked topology, filter, and addressed-cell owners. -/
def resolveCheckedValueListOperand
    (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityOperand model) :=
  match source with
  | .field direct => do
      let addressed ← document.addressedCell [] direct.field.id
      pure {
        source
        topology := none
        addressedCells := [addressed]
        hasUninstantiatedTail := false
        hasHaving := false
        hasNonRelevant := false }
  | .star starSource => do
      let topology ←
        (starSource.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      let addressedCells ←
        addressNumberEnvironments document starSource.field topology.environments
      pure {
        source
        topology := some topology
        addressedCells
        hasUninstantiatedTail := topology.domain.hasOpenTail
        hasHaving := false
        hasNonRelevant := false }
  | .starHaving filtered => do
      let topology ←
        (filtered.source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      let selected ← filtered.having.selectEnvironmentsResolving
        document.resolvingCorrelationContext outer topology.environments
      let addressedCells ←
        addressNumberEnvironments document filtered.source.field selected
      pure {
        source
        topology := some topology
        addressedCells
        hasUninstantiatedTail := topology.domain.hasOpenTail
        hasHaving := true
        hasNonRelevant := false }

/-- Resolve one unfiltered partial-validation operand. Direct masking precedes its read; a star retains canonical topology, reads only relevant concrete cells, and records incomplete extent on that exact authored operand. -/
def resolveCheckedPartialValueListOperand
    (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityOperand model) :=
  match source with
  | .field direct =>
      if scope.coversCell model direct.declaration.path [] then do
        let addressed ← document.addressedCell [] direct.field.id
        pure {
          source
          topology := none
          addressedCells := [addressed]
          hasUninstantiatedTail := false
          hasHaving := false
          hasNonRelevant := false }
      else
        pure {
          source
          topology := none
          addressedCells := []
          hasUninstantiatedTail := false
          hasHaving := false
          hasNonRelevant := true }
  | .star starSource => do
      let topology ←
        (starSource.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      let relevant := topology.environments.filter fun environment =>
        starSource.source.cellRelevant scope environment
      let addressedCells ←
        addressNumberEnvironments document starSource.field relevant
      pure {
        source
        topology := some topology
        addressedCells
        hasUninstantiatedTail := topology.domain.hasOpenTail
        hasHaving := false
        hasNonRelevant := !starSource.source.allRowsRelevant scope }
  | .starHaving _ =>
      -- The owning rule checks `hasHaving` and skips before any operand resolver.
      pure {
        source
        topology := none
        addressedCells := []
        hasUninstantiatedTail := false
        hasHaving := true
        hasNonRelevant := false }

end CheckedNumberEntityOperand

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

private def resolveNumberValueListOperands
    (resolve : CheckedNumberEntityOperand model →
      Except CheckedAddressingError
        (ResolvedCheckedNumberEntityOperand model)) :
    List (CheckedNumberEntityOperand model) →
      Except CheckedAddressingError
        (List (ResolvedCheckedNumberEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← resolve operand) ::
        (← resolveNumberValueListOperands resolve remaining))

namespace CheckedNumberEntityValueListSource

def hasHaving (checked : CheckedNumberEntityValueListSource model) : Bool :=
  checked.fields.hasHaving || checked.values.hasHaving

private def resolveFullFields
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  resolveNumberValueListOperands
    (fun operand => operand.resolveCheckedValueListOperand document outer)
    checked.fields.operands

private def resolveFullValues
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  resolveNumberValueListOperands
    (fun operand => operand.resolveCheckedValueListOperand document outer)
    checked.values.operands

/-- Construct both rich sides in the kernel's operator-specific side order, without flattening authored operand boundaries. -/
def resolveFull (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityValueList model) :=
  match checked.quantifier with
  | .notAll => do
      let fields ← checked.resolveFullFields document outer
      let values ← checked.resolveFullValues document outer
      pure { quantifier := checked.quantifier, fields, values }
  | .atLeastOne | .no => do
      let values ← checked.resolveFullValues document outer
      let fields ← checked.resolveFullFields document outer
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
  resolveNumberValueListOperands
    (fun operand =>
      operand.resolveCheckedPartialValueListOperand document outer scope)
    checked.fields.operands

private def resolvePartialValues
    (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :=
  resolveNumberValueListOperands
    (fun operand =>
      operand.resolveCheckedPartialValueListOperand document outer scope)
    checked.values.operands

/-- Partial validation skips a rule containing any filter before topology, relevance, or target reads; otherwise it constructs the same rich ordered operands with positional nonrelevance. -/
def evaluatePartial (checked : CheckedNumberEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialHavingValueListResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else
    match checked.quantifier with
    | .notAll => do
        let fields ← checked.resolvePartialFields document outer scope
        let values ← checked.resolvePartialValues document outer scope
        pure (.evaluated (checked.quantifier.evalOrdered
          (fields.map (·.valueListSideAt .validation))
          (values.map (·.valueListSideAt .validation))))
    | .atLeastOne | .no => do
        let values ← checked.resolvePartialValues document outer scope
        let fields ← checked.resolvePartialFields document outer scope
        pure (.evaluated (checked.quantifier.evalOrdered
          (fields.map (·.valueListSideAt .validation))
          (values.map (·.valueListSideAt .validation))))

end CheckedNumberEntityValueListSource

end A12Kernel
