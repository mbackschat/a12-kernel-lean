import A12Kernel.Elaboration.NumericValidation.Resolution
import A12Kernel.Elaboration.NumericComputation.Atom
import A12Kernel.Elaboration.BooleanValueCount

/-! # Validation comparisons over entity-list operands

A rule may compare an operation over an entity list, such as `Sum(Items*/Count) > 100`,
`FirstFilledValue(Rows*/A) > 10`, `NumberOfValueInFields(0 In Rows*/N) > 0` or
`SumOfProducts(Rows*/P, Rows*/Q) != [T]`. The ordered validation atom has carried these operands and
their addressed evaluation for some time; this module is the surface-level entry point that builds
them, so a rule reaches them without a hand-assembled comparison.

The authored operand surface is the one computations already use, `SurfaceNumericComputationAtom`,
since the authoring forms are the same. What differs on this arm is the reading scope, and it is
the entity-list elaborators' own: called with no target group they bind no level, which is how a
rule reads an entity list (`elaborateNumberEntitySource`). Ordinary operands resolve as
`elaborateRepeatableNumericComparison` resolves them.

Two forms keep the carriers that already own them, so neither acquires a second representation. A
list of plain fields only belongs to the scalar comparison, and the addressed scope admits it in
neither atom form, so it is refused as incoherent. The filled-group count belongs to
`elaborateNumericComparison` and `elaborateMixedFilledGroupCountComparison`.
-/

namespace A12Kernel

inductive EntityNumericComparisonElabError where
  | ordinary (error : NumericValidationElabError)
  | numberSource (error : NumberEntityElabError)
  | tokenSource (error : TokenValueCountElabError)
  | booleanSource (error : BooleanValueCountElabError)
  | productSource (error : NumericProductAggregateElabError)
  /-- A filled-group count, which its own carriers own. -/
  | groupCount
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

private def resolveEntityAtom (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceNumericComputationAtom →
      Except EntityNumericComparisonElabError (OrderedNumericValidationAtom model)
  | .numeric (.aggregate op source) =>
      (elaborateNumberEntitySource model rowGroup source).map (.aggregate op) |>.mapError .numberSource
  | .numeric (.filledGroupCount _) => throw .groupCount
  | .numeric atom => match SurfaceNumericAtom.ofEntityAtom? atom with
      | some ordinary =>
          (resolveAddressedNumericValidationAtom model rowGroup ordinary).map .ordinary
            |>.mapError .ordinary
      | none => throw .incoherent
  | .firstFilled source =>
      (elaborateNumberEntitySource model rowGroup source).map .firstFilled |>.mapError .numberSource
  | .valueCount expected source =>
      (elaborateNumberEntitySource model rowGroup source).map (.valueCount expected)
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
    (suppressExactScaleWarning : Bool := false) :
    Except EntityNumericComparisonElabError (CheckedOrderedNumericComparison model) :=
  match hModel : model.validate with
  | .error error => .error (.ordinary (.resolve error))
  | .ok () => do
      let core : OrderedNumericComparison model := {
        op, suppressExactScaleWarning
        left := ← left.mapM (resolveEntityAtom model rowGroup)
        right := ← right.mapM (resolveEntityAtom model rowGroup) }
      if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
        pure { rowGroup, operandScope := .sameGroupAddressed, core
               modelWellFormed := by rw [hModel]; rfl, wellFormed := hCore }
      else throw .incoherent

end A12Kernel
