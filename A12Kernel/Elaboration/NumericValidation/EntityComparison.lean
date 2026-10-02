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
the entity-list elaborators' own: called with no target group they bind no level, which is how a
rule reads an entity list (`elaborateNumberEntitySource`). Ordinary operands resolve as
`elaborateRepeatableNumericComparison` resolves them.

Three forms keep the carriers that already own them, so none acquires a second representation. A
comparison reading no entity list at all belongs to the scalar comparisons, including one they
refuse, such as a read of a second root. A list of plain fields only belongs to the scalar
comparison, and the addressed scope admits it in neither atom form, so it is refused as incoherent.
The filled-group count belongs to `elaborateNumericComparison` and
`elaborateMixedFilledGroupCountComparison`.

`NumberOfDifferentValues` is one operator over three checked carriers, Number, String/Enumeration
and temporal, tried in that order on the same authored list.
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
  -- `NumberOfDifferentValues` is one operator over three carriers: a list the Number one refuses is
  -- offered to the String/Enumeration one, then to the temporal one, and a list all refuse keeps
  -- the Number refusal.
  | .numeric (.aggregate .distinctCount source) =>
      match elaborateNumberEntitySource model rowGroup source with
      | .ok checked => pure (.aggregate .distinctCount checked)
      | .error error =>
          match elaborateTokenDistinctCountSource model rowGroup source with
          | .ok checked => pure (.tokenDistinctCount checked)
          | .error _ =>
              match (elaborateTemporalDistinctCountSource model rowGroup source).toOption.bind
                  fun temporal => (checkTemporalDistinctCountRun temporal).toOption with
              | some run => pure (.temporalDistinctCount run)
              | none => throw (.numberSource error)
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
      -- A comparison reading no entity list is the scalar carriers' even when they refuse it, such
      -- as a second root's field, so this carrier never answers in their place. A group count passes
      -- on to its own refusal, which names the carriers owning it.
      let readsList : SurfaceNumericComputationAtom → Bool
        | .numeric (.aggregate _ _) | .numeric (.filledGroupCount _) => true
        | .numeric _ => false
        | _ => true
      if !(left.anyAtom readsList || right.anyAtom readsList) then throw .incoherent
      let core : OrderedNumericComparison model := {
        op, suppressExactScaleWarning
        left := ← left.mapM (resolveEntityAtom model rowGroup)
        right := ← right.mapM (resolveEntityAtom model rowGroup) }
      if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
        pure { rowGroup, operandScope := .sameGroupAddressed, core
               modelWellFormed := by rw [hModel]; rfl, wellFormed := hCore }
      else throw .incoherent

end A12Kernel
