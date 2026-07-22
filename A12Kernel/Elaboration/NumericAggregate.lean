import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.NumericStar
import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Semantics.NumericAggregate

/-! # Checked Number aggregate lowering

The established direct route resolves one unfiltered list of at least two distinct nonrepeatable Number fields into the aggregate atom used by checked numeric expressions. The ordinary entity-list route reuses the shared checked direct/plain-star/filtered-star source, resolves each slot lazily in authored order, and delegates the resulting cells to the same aggregate folds. Group operands, partial repeatable relevance, whole-expression integration for repeatable sources, and concrete syntax remain outside.
-/

namespace A12Kernel

/-- Fail-closed errors owned by this aggregate-field lowering boundary. -/
inductive NumericAggregateElabError where
  | resolve (error : ResolveError)
  | tooFewFields
  | duplicateField (field : FieldId)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A nonempty resolved field list certified against one flat model. -/
structure CheckedNumericAggregateFields (model : FlatModel) where
  first : FlatNumberField
  rest : List FlatNumberField
  hasMultipleFields : rest.isEmpty = false
  uniqueFields : ({ first, rest : ResolvedNumericAggregateFields }).hasUniqueFields = true
  modelWellFormed : model.validate.isOk = true
  fieldsWellFormed :
    (model.admitsField (.number first) &&
      rest.all fun field => model.admitsField (.number field)) = true

namespace CheckedNumericAggregateFields

def fields (checked : CheckedNumericAggregateFields model) : List FlatNumberField :=
  checked.first :: checked.rest

def resolvedFields (checked : CheckedNumericAggregateFields model) :
    ResolvedNumericAggregateFields :=
  { first := checked.first, rest := checked.rest }

end CheckedNumericAggregateFields

namespace ResolvedNumericAggregateFields

private def classifyObservation : CellObservation → ValueListCell .number
  | .empty => .empty
  | .value (.num amount) => .present amount
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- Construct the common resolved subset from one phase-specific cell observer, preserving authored field order. -/
def resolvedValueSide (source : ResolvedNumericAggregateFields)
    (observe : FieldId → CellObservation) : ResolvedValueListSide .number :=
  { cells := source.fields.map fun field => classifyObservation (observe field.id)
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Retain every source declaration's signedness over the same phase-specific observations. -/
def resolvedSumSide (source : ResolvedNumericAggregateFields)
    (observe : FieldId → CellObservation) : ResolvedNumericSumSide :=
  { cells := source.fields.map fun field =>
      { cell := classifyObservation (observe field.id)
        declarationSigned := field.info.signed }
    uninstantiatedSignedness := []
    hasHaving := false }

/-- Evaluate one resolved direct field-list aggregate through the established aggregate folds. -/
def evaluate (source : ResolvedNumericAggregateFields) (op : NumericAggregateOp)
    (observe : FieldId → CellObservation) : NumericOperand :=
  match op with
  | .sum => evalDeclaredNumericSumAggregate (source.resolvedSumSide observe)
  | .minimum => evalNumericExtremumAggregate .minimum
      (source.resolvedValueSide observe)
  | .maximum => evalNumericExtremumAggregate .maximum
      (source.resolvedValueSide observe)

def referencesField (source : ResolvedNumericAggregateFields)
    (field : FieldId) : Bool :=
  source.fields.any fun candidate => candidate.id == field

def allRelevant (source : ResolvedNumericAggregateFields)
    (isRelevant : FlatRelevance) : Bool :=
  source.fields.all fun field => isRelevant field.id

end ResolvedNumericAggregateFields

private def FlatModel.resolveNumericAggregateDeclaration (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except NumericAggregateElabError FlatFieldDecl :=
  (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve

private def numericAggregateField (declaration : FlatFieldDecl) :
    Except NumericAggregateElabError FlatNumberField :=
  match declaration.toNumberField? with
  | some field => pure field
  | none =>
      throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)

private def FlatModel.resolveNumericAggregateDeclarations (model : FlatModel)
    (declaringGroup : GroupPath) :
    List SurfaceFieldPath → Except NumericAggregateElabError (List FlatFieldDecl)
  | [] => pure []
  | reference :: remaining => do
      pure ((← model.resolveNumericAggregateDeclaration declaringGroup reference) ::
        (← model.resolveNumericAggregateDeclarations declaringGroup remaining))

private def numericAggregateFields :
    List FlatFieldDecl → Except NumericAggregateElabError (List FlatNumberField)
  | [] => pure []
  | declaration :: remaining => do
      pure ((← numericAggregateField declaration) ::
        (← numericAggregateFields remaining))

/-- Validate the model once, require at least two direct fields, resolve every source in authored order, and certify the complete Number list. -/
def elaborateNumericAggregateFields (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceNumericAggregateFields) :
    Except NumericAggregateElabError (CheckedNumericAggregateFields model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () =>
      match authored.rest with
      | [] => .error .tooFewFields
      | secondReference :: remainingReferences => do
          let firstDeclaration ←
            model.resolveNumericAggregateDeclaration declaringGroup authored.first
          let secondDeclaration ←
            model.resolveNumericAggregateDeclaration declaringGroup secondReference
          let remainingDeclarations ← model.resolveNumericAggregateDeclarations declaringGroup
            remainingReferences
          let restDeclarations := secondDeclaration :: remainingDeclarations
          match ResolvedNumericAggregateFields.firstDuplicateFieldId?
              ((firstDeclaration :: restDeclarations).map (·.id)) with
          | some field => throw (.duplicateField field)
          | none => do
              let first ← numericAggregateField firstDeclaration
              let second ← numericAggregateField secondDeclaration
              let remaining ← numericAggregateFields remainingDeclarations
              let rest := second :: remaining
              let resolved : ResolvedNumericAggregateFields := { first, rest }
              if hUnique : resolved.hasUniqueFields = true then
                if hFields :
                    (model.admitsField (.number first) &&
                      rest.all fun field => model.admitsField (.number field)) = true then
                  pure {
                    first
                    rest
                    hasMultipleFields := rfl
                    uniqueFields := hUnique
                    modelWellFormed := by
                      rw [hModel]
                      rfl
                    fieldsWellFormed := hFields
                  }
                else
                  throw .incoherentCore
              else
                throw .incoherentCore

namespace CheckedNumericAggregateFields

/-- Construct the common resolved subset: explicit nonrepeatable cells in authored order, no uninstantiated source, and no filter. -/
def resolvedValueSide (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : ResolvedValueListSide .number :=
  let context := model.checkContext raw
  checked.resolvedFields.resolvedValueSide context.observeValidationAt

/-- Retain each source declaration's signedness for `Sum` polarity. -/
def resolvedSumSide (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : ResolvedNumericSumSide :=
  let context := model.checkContext raw
  checked.resolvedFields.resolvedSumSide context.observeValidationAt

/-- Evaluate `Sum` through the shared phase-parameterized aggregate dispatcher. -/
def evaluateSum (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : NumericOperand :=
  let context := model.checkContext raw
  checked.resolvedFields.evaluate .sum context.observeValidationAt

/-- Evaluate direct `MinValue` or `MaxValue` through the same aggregate dispatcher. -/
def evaluateExtremum (checked : CheckedNumericAggregateFields model)
    (op : NumericExtremumOp) (raw : RawFlatContext) : NumericOperand :=
  let context := model.checkContext raw
  match op with
  | .minimum => checked.resolvedFields.evaluate .minimum context.observeValidationAt
  | .maximum => checked.resolvedFields.evaluate .maximum context.observeValidationAt

end CheckedNumericAggregateFields

namespace CheckedNumericStarSource

/-- Evaluate one checked Number star through the existing declaration-signed Sum semantics. -/
def evaluateSum (checked : CheckedNumericStarSource model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError NumericOperand := do
  checked.validateContext raw
  pure (evalNumericSumAggregate checked.field.info.signed (checked.resolvedValueSide raw))

/-- Evaluate one checked Number star through the existing extremum semantics. -/
def evaluateExtremum (checked : CheckedNumericStarSource model)
    (op : NumericExtremumOp) (raw : RawSingleGroupContext) :
    Except NumericStarContextError NumericOperand := do
  checked.validateContext raw
  pure (evalNumericExtremumAggregate op (checked.resolvedValueSide raw))

end CheckedNumericStarSource

private def appendNumericAggregateSide
    (left right : ResolvedValueListSide .number) :
    ResolvedValueListSide .number :=
  { cells := left.cells ++ right.cells
    hasUninstantiatedTail :=
      left.hasUninstantiatedTail || right.hasUninstantiatedTail
    hasHaving := left.hasHaving || right.hasHaving }

private def appendNumericSumSide
    (left right : ResolvedNumericSumSide) : ResolvedNumericSumSide :=
  { cells := left.cells ++ right.cells
    uninstantiatedSignedness :=
      left.uninstantiatedSignedness ++ right.uninstantiatedSignedness
    hasHaving := left.hasHaving || right.hasHaving }

private def numericAggregateSideAvailable
    (side : ResolvedValueListSide .number) : Except FormalCause Unit :=
  ValueListCell.scanPresent (kind := .number) (fun _ _ => ()) side.cells ()

namespace CheckedNumberEntityField

/-- Classify one checked direct slot through the same declaration-owned Number reader used by every aggregate source. -/
def resolvedAggregateSide (checked : CheckedNumberEntityField model)
    (context : FlatContext) : ResolvedValueListSide .number :=
  { cells := [checked.field.valueListCell context]
    hasUninstantiatedTail := false
    hasHaving := false }

end CheckedNumberEntityField

namespace CheckedNumberEntityOperand

/-- Resolve exactly one authored slot. Plain and filtered stars reuse the general checked topology and filter owners; direct fields reuse the checked flat Number reader. -/
def resolvedAggregateSide (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .field source => pure (source.resolvedAggregateSide direct)
  | .star source => source.resolvedValueSide document outer starRead
  | .starHaving source =>
      source.resolvedValueSide document outer filterRead starRead

end CheckedNumberEntityOperand

namespace CheckedNumberEntitySource

/-- Evaluate a checked ordinary Number entity-list aggregate in authored slot order. Each wildcard occurrence resolves independently. A formally unavailable reached cell returns immediately, so no later star topology, filter, or target reader is sampled. -/
def evaluateAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError NumericOperand :=
  let direct := model.checkContext directRead
  let rec evaluateExtremum
      (extremum : NumericExtremumOp)
      (operands : List (CheckedNumberEntityOperand model))
      (accumulated : ResolvedValueListSide .number) :
      Except StarAddressingError NumericOperand := do
    match operands with
    | [] => pure (evalNumericExtremumAggregate extremum accumulated)
    | operand :: remaining =>
        let side ← operand.resolvedAggregateSide document outer direct
          filterRead starRead
        match numericAggregateSideAvailable side with
        | .error cause => pure (NumericOperand.unknown cause)
        | .ok () =>
            evaluateExtremum extremum remaining (appendNumericAggregateSide accumulated side)
  let rec evaluateSum
      (operands : List (CheckedNumberEntityOperand model))
      (accumulated : ResolvedNumericSumSide) :
      Except StarAddressingError NumericOperand := do
    match operands with
    | [] => pure (evalDeclaredNumericSumAggregate accumulated)
    | operand :: remaining =>
        let side ← operand.resolvedAggregateSide document outer direct
          filterRead starRead
        match numericAggregateSideAvailable side with
        | .error cause => pure (NumericOperand.unknown cause)
        | .ok () =>
            let declared := side.toNumericSumSide operand.declarationSigned
            evaluateSum remaining (appendNumericSumSide accumulated declared)
  match op with
  | .sum => evaluateSum checked.operands {
      cells := [], uninstantiatedSignedness := [], hasHaving := false }
  | .minimum => evaluateExtremum .minimum checked.operands {
      cells := [], hasUninstantiatedTail := false, hasHaving := false }
  | .maximum => evaluateExtremum .maximum checked.operands {
      cells := [], hasUninstantiatedTail := false, hasHaving := false }

end CheckedNumberEntitySource

end A12Kernel
