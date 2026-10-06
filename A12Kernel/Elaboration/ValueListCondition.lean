import A12Kernel.Elaboration.NumberEntityValueList
import A12Kernel.Elaboration.TokenEntityValueList

/-! # Checked value-list sources for compositional conditions

The condition tree retains the owning family's certificate. Number, token and literal-token sides
keep their distinct admission contracts; evaluation delegates to the encounter-ordered quantifier.
-/

namespace A12Kernel

inductive CheckedValueListCondition (model : FlatModel) where
  | number (source : CheckedNumberEntityValueListSource model)
  | token (source : CheckedTokenEntityValueListSource model)
  | literals (source : CheckedTokenEntityStringLiteralValueListSource model)

namespace CheckedValueListCondition

def quantifier : CheckedValueListCondition model → ValueListQuantifier
  | .number source => source.quantifier
  | .token source => source.quantifier
  | .literals source => source.quantifier

def modelWellFormed (source : CheckedValueListCondition model) : model.validate.isOk = true :=
  match source with
  | .number source => source.fields.modelWellFormed
  | .token source => source.fields.modelWellFormed
  | .literals source => source.fields.modelWellFormed

def hasHaving : CheckedValueListCondition model → Bool
  | .number source => source.hasHaving
  | .token source => source.hasHaving
  | .literals source => source.fields.hasHaving

def referencesField (source : CheckedValueListCondition model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  match source with
  | .number source => source.fields.referencesField field filterReads ||
      source.values.referencesField field filterReads
  | .token source => source.fields.referencesField field filterReads ||
      source.values.referencesField field filterReads
  | .literals source => source.fields.referencesField field filterReads

def bindingScopes : CheckedValueListCondition model → List (List RepeatableLevel)
  | .number source => source.fields.bindingScopes ++ source.values.bindingScopes
  | .token source => source.fields.bindingScopes ++ source.values.bindingScopes
  | .literals source => source.fields.bindingScopes

/-- Evaluate the certified sides through the shared ordered quantifier. Literal values form one
fully known operand and carry no document addresses. -/
def evaluateFull (source : CheckedValueListCondition model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) : Except CheckedAddressingError Verdict :=
  match source with
  | .number source => source.evaluateFull (world := world) document outer
  | .token source => source.evaluateFull (world := world) document outer
  | .literals source => do
      let fields ← source.fields.operands.mapM (·.checkedValidationSide (world := world) document outer)
      pure (source.quantifier.evalOrdered fields
        [{ cells := (source.firstValue :: source.restValues).map (ValueListCell.present (kind := .token)),
           hasUninstantiatedTail := false, hasHaving := false }])

end CheckedValueListCondition

end A12Kernel
