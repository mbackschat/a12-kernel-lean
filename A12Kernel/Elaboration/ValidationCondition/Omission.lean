import A12Kernel.Elaboration.ValidationCondition.Reference
import A12Kernel.Semantics.ValidationRule

/-! # Structural omission responsibility

The [message-construction source](../../../docs/sources/message-and-pointer-probes.md#src-message-construction-route)
and peer KF522 distinguish every referenced field from the fields whose filling could repair an
omission. Selection depends on the authored condition, independently of its verdict or cell values.
Pruning a presence construct or upward count comparison keeps every filter dependency; the shared
reference projector retains their candidate and captured coordinates.
-/

namespace A12Kernel

private def scalarOmissionCount : NumericValidationAtom → Bool
  | .filledGroupCount _ | .aggregate .distinctCount _ => true
  | _ => false

private def temporalAmountOmissionCount : HavingNumericAtomOf Temporal → Bool
  | .groupCount _ | .aggregate .distinctCount _
  | .collectionCount (.filledFields ..) | .collectionCount (.tokenDistinct ..)
  | .collectionCount (.temporalDistinct ..) => true
  | _ => false

/-- Counts inside shifts and constructed components still belong to the authored comparison
(FeldOperationUtil's count search); filter bodies are a separate reference channel. -/
private def temporalOmissionCount (source : ScalarTemporalExpression model) : Bool :=
  (source.dependenciesWith (fun _ => []) (fun _ => []) (fun _ => [])
    (fun atom => [temporalAmountOmissionCount atom])).any id

private def orderedOmissionCount : OrderedNumericValidationAtom model → Bool
  | .ordinary atom => scalarOmissionCount atom
  | .temporalExpression source => match source.core with
      | .temporal operation => operation.sources.any (temporalOmissionCount ∘ (·.core))
      | .storedProjection _ => false
  | .filledFieldCount _ | .filledGroupCountMixed _ | .aggregate .distinctCount _
  | .tokenDistinctCount _ | .temporalDistinctCount _ => true
  | _ => false

def upwardOmissionCount (isCount : Atom → Bool)
    (comparison : NumericComparisonOf Atom) : Bool :=
  let left := comparison.left.anyAtom isCount
  let right := comparison.right.anyAtom isCount
  if left == right then false else match comparison.op with
    | .ordinary .greater | .ordinary .greaterEqual => left
    | .ordinary .less | .ordinary .lessEqual => right
    | .ordinary .equal | .ordinary .notEqual | .tolerance _ => false

private def upwardTemporalOmissionCount (operator : TemporalComparisonOp)
    (left right : Bool) : Bool :=
  if left == right then false else match operator with
    | .after | .afterOrEqual => left
    | .before | .beforeOrEqual => right
    | .equal | .notEqual => false

private def numberFilterPointers (source : CheckedNumberEntitySource model)
    (environment : Env) : Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> source.operands.mapM fun
    | .starHaving source =>
        source.source.source.filterReferencePointers environment source.having
    | _ => pure []

private def tokenFilterPointers (source : CheckedTokenEntitySource model)
    (environment : Env) : Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> source.operands.mapM fun
    | .star source => (·.flatten) <$> source.filter.toList.mapM fun having =>
        source.source.filterReferencePointers environment having.condition
    | _ => pure []

private def temporalDistinctFilterPointers (run : CheckedTemporalDistinctCountRun model)
    (environment : Env) : Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> run.source.operands.mapM fun
    | .slot (.star path _ (some filter)) => path.filterReferencePointers environment filter
    | _ => pure []

private def booleanFilterPointers (source : CheckedBooleanValueCountSource model)
    (environment : Env) : Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> source.operands.mapM fun
    | .star source => (·.flatten) <$> source.filter.toList.mapM fun having =>
        source.source.filterReferencePointers environment having.condition
    | _ => pure []

private def fieldFillFilterPointers (source : CheckedFieldFillList model)
    (environment : Env) : Except ReferenceProjectionError (List MessagePointer) :=
  (·.flatten) <$> source.operands.mapM fun
    | .star source => (·.flatten) <$> source.filter.toList.mapM fun having =>
        source.source.filterReferencePointers environment having.condition
    | _ => pure []

private def orderedFilterPointers (atom : OrderedNumericValidationAtom model)
    (environment : Env) : Except ReferenceProjectionError (List MessagePointer) :=
  if !atom.hasHaving then pure [] else match atom with
    | .firstFilled source | .valueCount _ source | .aggregate _ source =>
        numberFilterPointers source environment
    | .tokenValueCount source => tokenFilterPointers source.source environment
    | .tokenDistinctCount source => tokenFilterPointers source environment
    | .temporalDistinctCount run => temporalDistinctFilterPointers run environment
    | .booleanValueCount source => booleanFilterPointers source environment
    | .filledFieldCount source => fieldFillFilterPointers source environment
    | _ => throw .filteredStarOperand

private def omissionLeafPointers (leaf : ValidationConditionLeaf model)
    (environment : Env) (inputs : Option MessageReferenceInputs) :
    Except ReferenceProjectionError (List MessagePointer) :=
  match leaf with
  | .flat (.fieldFilled _) | .repeatableFieldPresence .filled _
  | .indexedFieldPresence .filled _ | .keyedGroupPresence .filled _
  | .groupPresence .filled _
  | .groupList .allGroupsFilled _ | .groupList .atLeastOneGroupFilled _ => pure []
  | .fieldFill .allFieldsFilled source | .fieldFill .atLeastOneFieldFilled source
  | .fieldFill .moreThanOneFieldFilled source => fieldFillFilterPointers source environment
  | .numeric _ comparison =>
      if upwardOmissionCount scalarOmissionCount comparison then pure []
      else leaf.referencePointers environment inputs
  | .orderedNumeric _ comparison =>
      if upwardOmissionCount orderedOmissionCount comparison then
        (·.flatten) <$> (comparison.left.atoms ++ comparison.right.atoms).mapM
          (orderedFilterPointers · environment)
      else leaf.referencePointers environment inputs
  | .scalarTemporal comparison =>
      if upwardTemporalOmissionCount comparison.operator
          (temporalOmissionCount comparison.left.core) (temporalOmissionCount comparison.right.core) then
        if comparison.left.core.hasHaving || comparison.right.core.hasHaving then
          throw .filteredStarOperand
        else pure []
      else leaf.referencePointers environment inputs
  -- A VALUE firing's cluster can repair nothing by filling, so only an OMISSION firing counts.
  | .repetitionNotUnique source => source.firingPointers environment inputs (· == .omission)
  | _ => leaf.referencePointers environment inputs

/-- The omission-responsible subset at one firing environment. Both connectives contribute every
authored branch; unsupported filter projections fail closed even inside a pruned comparison. -/
def ValidationCondition.omissionPointers (condition : ValidationCondition model)
    (environment : Env) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError (List MessagePointer) :=
  let rec project : ValidationCondition model → Except ReferenceProjectionError (List MessagePointer)
    | .leaf leaf => omissionLeafPointers leaf environment inputs
    | .and left right | .or left right => do
        pure ((← project left) ++ (← project right))
  (project condition).map List.eraseDups

/-- The two field-reference channels have different roles. Value errors have no fill-to-fix set;
omission errors use the authored selector (KF522 and the retained Having caller messages). -/
structure ValidationMessageReferences where
  referenced : List MessagePointer
  fillToFix : List MessagePointer
  deriving Repr, DecidableEq

def ValidationCondition.messageReferences (condition : ValidationCondition model)
    (message : FlatRuleMessage) (environment : Env) (inputs : Option MessageReferenceInputs := none) :
    Except ReferenceProjectionError ValidationMessageReferences := do
  if message.origin == .runtimeFailure then return { referenced := [], fillToFix := [] }
  let referenced ← condition.referencePointers environment inputs
  let fillToFix ← match message.messageType with
    | .value => pure []
    | .omission => condition.omissionPointers environment inputs
  pure { referenced, fillToFix }

end A12Kernel
