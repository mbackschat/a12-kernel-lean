import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenValuesNotUnique
import A12Kernel.Elaboration.TemporalValuesNotUnique

/-! # Checked uniqueness sources for compositional conditions

Each overload keeps its own certificate and comparison identity. The condition adapter delegates
to those evaluators, including their unavailable-cell skip and positional filter polarity.
-/

namespace A12Kernel

inductive CheckedValuesNotUniqueCondition (model : FlatModel) where
  | number (source : CheckedNumberValuesNotUniqueSource model)
  | token (source : CheckedTokenValuesNotUniqueSource model)
  | temporal (source : CheckedTemporalValuesNotUniqueSource model)

namespace CheckedValuesNotUniqueCondition

def modelWellFormed (source : CheckedValuesNotUniqueCondition model) :
    model.validate.isOk = true :=
  match source with
  | .number source => source.modelWellFormed
  | .token source => source.source.modelWellFormed
  | .temporal source => source.shape.modelWellFormed

def hasHaving : CheckedValuesNotUniqueCondition model → Bool
  | .number source => source.hasHaving
  | .token source => source.source.hasHaving
  | .temporal source => source.operands.any (·.hasHaving)

def referencesField (source : CheckedValuesNotUniqueCondition model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  match source with
  | .number source => source.referencesField field filterReads
  | .token source => source.source.referencesField field filterReads
  | .temporal source => source.operands.any fun
      | .field source => source.declaration.id == field
      | .star _ source filter => source.declaration.id == field ||
          filter.any (filterReads · field)
      | .group source => source.declarations.any (·.id == field)

def bindingScopes : CheckedValuesNotUniqueCondition model → List (List RepeatableLevel)
  | .number source => source.bindingScopes
  | .token source => source.source.bindingScopes
  | .temporal source => source.shape.operands.map (·.bindingScope)

/-- The Number certificate is shared with sole-field value lists; uniqueness keeps the
many-required rule that its owning elaborator checks. Token and temporal certificates are sealed. -/
def admittedMultiplicity : CheckedValuesNotUniqueCondition model → Bool
  | .number source => source.first.isAlreadyMany || !source.rest.isEmpty
  | .token _ | .temporal _ => true

def evaluateFull (source : CheckedValuesNotUniqueCondition model)
    (document : CheckedDocument model) (outer : Env) : Except CheckedAddressingError Verdict :=
  match source with
  | .number source => CheckedNumberValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique source document outer
  | .token source => source.evaluateCheckedDocumentValuesNotUnique document outer
  | .temporal source => source.evaluateCheckedDocumentValuesNotUnique document outer

end CheckedValuesNotUniqueCondition

end A12Kernel
