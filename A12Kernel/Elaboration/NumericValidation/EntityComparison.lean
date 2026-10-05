import A12Kernel.Elaboration.NumericValidation.Resolution
import A12Kernel.Elaboration.NumericComputation.Atom
import A12Kernel.Elaboration.BooleanValueCount
import A12Kernel.Elaboration.NumericValidation.Ordered

/-! # Validation comparisons over entity-list operands

A rule may compare an operation over an entity list, such as `Sum(Items*/Count) > 100`,
`FirstFilledValue(Rows*/A) > 10`, `NumberOfValueInFields(0 In Rows*/N) > 0` or
`SumOfProducts(Rows*/P, Rows*/Q) != [T]`. The ordered validation atom has carried these operands and
their addressed evaluation for some time; this module is the surface-level entry point that builds
them, so a rule reaches them without a hand-assembled comparison.

The authored operand surface is the one computations already use, `SurfaceNumericComputationAtom`,
since the authoring forms are the same. What differs on this arm is the reading scope, and it is
the entity-list elaborators' own: Number lists receive the rule's available row binding while
paths still resolve at its lexical declaring group. The same split applies to ordinary numeric
operands and to captured references in a filter; a descendant error field does not relocate names.

Three forms keep the carriers that already own them, so none acquires a second representation. A
comparison reading no entity list at all belongs to the ordinary numeric comparisons. Direct-list
aggregates keep their scalar owner; FirstFilledValue additionally retains caller-bound direct lists
because selection must read each field at the rule's current row.
The filled-group count belongs to `elaborateNumericComparison` and
`elaborateMixedFilledGroupCountComparison`.

`NumberOfDifferentValues` is one operator over three checked carriers, Number, String/Enumeration
and temporal, tried in that order on the same authored list.
-/

namespace A12Kernel

inductive EntityNumericComparisonElabError where
  | temporalExpression (error : TemporalNumericExpressionError)
  | ordinary (error : NumericValidationElabError)
  | numberSource (error : NumberEntityElabError)
  | tokenSource (error : TokenValueCountElabError)
  | booleanSource (error : BooleanValueCountElabError)
  | productSource (error : NumericProductAggregateElabError)
  | fieldFillSource (error : FieldFillListElabError)
  /-- A filled-group count, which its own carriers own. -/
  | groupCount
  /-- A comparison reading no entity list, which the scalar carriers own. -/
  | readsNoList
  | incoherent
  deriving Repr

/-- The same atom read over a plain direct field list, when it reads no entity list. -/
private def SurfaceNumericAtom.ofEntityAtom? :
    SurfaceNumericAtom SurfaceNumberEntitySource → Option SurfaceNumericAtom
  | .field path => some (.field path)
  | .currentRepetition path => some (.currentRepetition path)
  | .baseYear => some .baseYear
  | .baseYearDatePart source part => some (.baseYearDatePart source part)
  | .temporalFieldPart path part => some (.temporalFieldPart path part)
  | .dateRangeBoundPart path bound part => some (.dateRangeBoundPart path bound part)
  | .stringLength path => some (.stringLength path)
  | .stringRange path start finish => some (.stringRange path start finish)
  | .fieldValueAsNumber source => some (.fieldValueAsNumber source)
  | .dateDifference unit left right => some (.dateDifference unit left right)
  | .dateTimeDifference unit left right => some (.dateTimeDifference unit left right)
  | .dayDifference left right => some (.dayDifference left right)
  | .aggregate _ _ | .filledGroupCount _ => none

private def resolveEntityAtom (model : FlatModel) (rowGroup bindingGroup : GroupPath) :
    SurfaceNumericComputationAtom →
      Except EntityNumericComparisonElabError (OrderedNumericValidationAtom model)
  | .temporalPart source part =>
      (elaborateTemporalNumericExpression model rowGroup source part (some bindingGroup)).map .temporalPart
        |>.mapError .temporalExpression
  | .numeric (.aggregate .distinctCount source) => do
      match ← (elaborateDistinctCountSource model rowGroup source (bindingGroup? := some bindingGroup)).mapError .numberSource with
      | .number checked => pure (.aggregate .distinctCount checked)
      | .token checked => pure (.tokenDistinctCount checked)
      | .temporal run => pure (.temporalDistinctCount run)
  | .numeric (.aggregate op source) =>
      (elaborateNumberEntitySource model rowGroup source
        (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup)).map (.aggregate op) |>.mapError .numberSource
  | .numeric (.filledGroupCount _) => throw .groupCount
  | .numeric atom => match SurfaceNumericAtom.ofEntityAtom? atom with
      | some ordinary =>
          (resolveAddressedNumericValidationAtom model bindingGroup ordinary rowGroup).map .ordinary
            |>.mapError .ordinary
      | none => throw .incoherent
  | .filledFieldCount source =>
      (elaborateFieldFillList model rowGroup source bindingGroup).map .filledFieldCount |>.mapError .fieldFillSource
  | .firstFilled source =>
      (elaborateNumberEntitySource model rowGroup source
        (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup)).map .firstFilled |>.mapError .numberSource
  | .valueCount expected source =>
      (elaborateNumberEntitySource model rowGroup source
        (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup)).map (.valueCount expected)
        |>.mapError .numberSource
  | .tokenValueCount expected source =>
      (elaborateTokenValueCountSource model rowGroup expected source).map .tokenValueCount
        |>.mapError .tokenSource
  | .tokenEntityValueCount expected source =>
      (elaborateTokenEntityValueCountSource model rowGroup expected source).map .tokenValueCount
        |>.mapError .tokenSource
  | .booleanValueCount expected source =>
      (elaborateBooleanValueCountSource model rowGroup expected source).map .booleanValueCount
        |>.mapError .booleanSource
  | .sumOfProducts source =>
      (elaborateNumericProductAggregate model rowGroup source).map .sumOfProducts
        |>.mapError .productSource

/-- Elaborate a rule comparison whose operations read entity lists, at the rule group. -/
def elaborateEntityNumericComparison (model : FlatModel) (rowGroup : GroupPath)
    (op : NumericValidationOp) (left right : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (suppressExactScaleWarning : Bool := false) (bindingGroup : GroupPath := rowGroup) :
    Except EntityNumericComparisonElabError (CheckedOrderedNumericComparison model) :=
  match hModel : model.validate with
  | .error error => .error (.ordinary (.resolve error))
  | .ok () => do
      -- A comparison reading no entity list belongs to the ordinary carriers, so this carrier never
      -- answers in their place. A group count passes on to its own refusal, which names its carriers.
      let readsList : SurfaceNumericComputationAtom → Bool
        | .numeric (.aggregate _ _) | .numeric (.filledGroupCount _) => true
        | .numeric _ => false
        | _ => true
      if !(left.anyAtom readsList || right.anyAtom readsList) then throw .readsNoList
      let core : OrderedNumericComparison model := {
        op, suppressExactScaleWarning
        left := ← left.mapM (resolveEntityAtom model rowGroup bindingGroup)
        right := ← right.mapM (resolveEntityAtom model rowGroup bindingGroup) }
      if hCore : core.wellFormedInBool bindingGroup .sameGroupAddressed = true then
        pure { rowGroup := bindingGroup, operandScope := .sameGroupAddressed, core
               modelWellFormed := by rw [hModel]; rfl, wellFormed := hCore }
      else throw .incoherent

end A12Kernel
