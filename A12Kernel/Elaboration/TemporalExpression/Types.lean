import A12Kernel.Semantics.ScalarTemporalValue
import A12Kernel.Elaboration.ConstructedDateEvaluation
import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Elaboration.TemporalExtremumStream
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents
import A12Kernel.Elaboration.DateRangeBoundComparison

/-! # Scalar temporal expression types

Fields, clocks, typed literals and constructors share the expression tree with extrema, projections
and elapsed or calendar shifts. Date values retain exact instants and calendar provenance through
composition; yearless comparisons additionally retain their declared component key. Storage limits
are applied by the target, after arithmetic (spec/05 and calendar-expression grid, 2026-10-04).
-/

namespace A12Kernel

inductive SurfaceScalarTemporalExpression where
  | field (reference : SurfaceFieldPath)
  | indexed (source : SurfaceSemanticIndex)
  | group (source : SurfaceScalarTemporalExpression)
  | extremum (operator : TemporalExtremumOp) (source : SurfaceFieldEntitySource)
  | combine (operator : TemporalExtremumOp)
      (first : SurfaceScalarTemporalExpression) (rest : List SurfaceScalarTemporalExpression)
  | now
  | today
  | dateLiteral (value : FullDate) (yearPresent : Bool := true)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | rangeBound (reference : SurfaceFieldPath) (bound : DateRangeBound)
  | baseYearBound (bound : BaseYearRangeEndpoint)
  | dateTimeConstruction (date time : SurfaceScalarTemporalExpression)
  | valueAsDate (reference : SurfaceFieldPath) (endpoint : ValueAsDateEndpoint)
  | indexedValueAsDate (selection : SurfaceSemanticIndex) (endpoint : ValueAsDateEndpoint)
  | dateConstruction (components : SurfaceConstructedDateComponents
      (Sum (Sum SurfaceConstructedDateSource SurfaceSemanticIndex) (DateNumericPart × SurfaceScalarTemporalExpression)))
  | calendarShift (unit : DateShiftUnit) (source : SurfaceScalarTemporalExpression)
      (amount : AuthoredNumericExpr (SurfaceHavingNumericAtomOf SurfaceScalarTemporalExpression))
  | timeConstruction (components : TimeComponentPrefix (Sum (Sum SurfaceTimeComponent SurfaceSemanticIndex) (TimeNumericPart × SurfaceScalarTemporalExpression)))
  | dateFromDateTime (source : SurfaceScalarTemporalExpression)
  | timeFromDateTime (source : SurfaceScalarTemporalExpression)
  | subdayShift (unit : DateTimeSubdayUnit) (source : SurfaceScalarTemporalExpression)
      (amount : AuthoredNumericExpr (SurfaceHavingNumericAtomOf SurfaceScalarTemporalExpression))

abbrev SurfaceScalarDateComponent :=
  Sum (Sum SurfaceConstructedDateSource SurfaceSemanticIndex) (DateNumericPart × SurfaceScalarTemporalExpression)

abbrev SurfaceScalarTimeComponent :=
  Sum (Sum SurfaceTimeComponent SurfaceSemanticIndex) (TimeNumericPart × SurfaceScalarTemporalExpression)

/-- `datumAngabe2` adds partial-Date interpretation to the ordinary `datumAngabe` source slot
(GrammarOnly_ConditionParser.g4, rules at lines 479–492; spec/05 §§3,6). -/
inductive TemporalSourceSlot where
  | ordinary
  | withPartialDate
  deriving Repr, DecidableEq

/-- Each nested operation owns its grammar slot; admitting a wrapper does not widen its operand's
slot (GrammarOnly_ConditionParser.g4, extractor and constructor rules at lines 416 and 444). -/
def SurfaceScalarTemporalExpression.admittedSourceSlot (source : SurfaceScalarTemporalExpression)
    (slot : TemporalSourceSlot := .withPartialDate) : Bool :=
  match source with
  | .group _ | .extremum _ _ | .combine _ _ _ => false
  | .valueAsDate _ _ | .indexedValueAsDate _ _ =>
      match slot with
      | .ordinary => false
      | .withPartialDate => true
  | .field _ | .indexed _ | .now | .today | .dateLiteral _ _ | .timeLiteral _ | .dateTimeLiteral _
  | .dateTimeConstruction _ _ | .rangeBound _ _ | .baseYearBound _ | .dateConstruction _ | .calendarShift _ _ _
  | .timeConstruction _ | .dateFromDateTime _ | .timeFromDateTime _ | .subdayShift _ _ _ => true

inductive ScalarTemporalExpressionError where
  | model (error : ResolveError)
  | read (error : ResolveError)
  | indexed (error : SemanticIndexElabError)
  | extremum (error : TemporalExtremumOperandElabError)
  | amount (error : TemporalShiftAmountElabError)
  | numeric (error : CorrelationElabError)
  | dateComponents (error : ConstructedDateComponentsElabError)
  | timeComponents (error : TimeComponentsElabError)
  | rangeBound (error : YearlessDateRangeBoundElabError)
  | partialDate (error : ValueAsDateZonedElabError)
  | temporalPartPrecision (path : List String) (part : TemporalNumericPart)
  | nonTemporal (path : List String)
  | unsupportedSource
  | incompatibleFormats
  deriving Repr, DecidableEq

def ScalarTemporalExpressionError.dateValidityDiagnostic? : ScalarTemporalExpressionError → Option KernelStaticDiagnostic
  | .dateComponents .onlyConstantsUsed => some .onlyConstantsUsed
  | _ => none

inductive ScalarTemporalEvaluationFault where
  | indexedOperandNotSupported
  | dateTimeLabelUnresolved
  | componentNumberInvalid
  | calendarUnavailable
  | addressing (error : CheckedAddressingError)
  deriving Repr, DecidableEq

def ScalarTemporalEvaluationFault.separateAddressing : ScalarTemporalEvaluationFault →
    Sum CheckedAddressingError ScalarTemporalEvaluationFault
  | .addressing error => .inl error
  | fault => .inr fault

def ScalarTemporalEvaluationFault.toAddressing : ScalarTemporalEvaluationFault → CheckedAddressingError
  | .addressing error => error
  | _ => .temporalUnavailable

/-- Index selection retains the same declaration-certified partial-Date endpoint and model profile
as a direct read; the selected row cannot substitute another field's policy (spec/08 §4). -/
structure CheckedIndexedValueAsDateSource (model : FlatModel) where
  selection : CheckedSemanticIndexSource model
  source : CheckedZonedValueAsDateSource model
  sameTarget : source.source.target.id = selection.targetDeclaration.id

/-- Selection and the position-specific component certificate must identify the same declaration
(spec/05 §3 and spec/08 §4). -/
structure CheckedIndexedDateComponent (model : FlatModel) where
  selection : CheckedSemanticIndexSource model
  source : CheckedConstructedDateSource model
  sameTarget : source.fieldId? = some selection.targetDeclaration.id

/-- Indexed Time components keep the same position-specific field certificate as direct reads
and identify the selected declaration (spec/05 §3 and spec/08 §4). -/
structure CheckedIndexedTimeComponent (model : FlatModel) where
  selection : CheckedSemanticIndexSource model
  source : CheckedTimeComponent model
  sameTarget : source.fieldDependencies = [selection.targetDeclaration.id]

mutual
inductive ScalarTemporalAtom (model : FlatModel) where
  | field (source : FlatTemporalField)
  | indexed (source : CheckedSemanticIndexSource model)
  | entityExtremum (operator : TemporalExtremumOp) (source : CheckedTemporalExtremumOperands model)
  | fixed (value : ScalarTemporalValue)
  | now
  | today (profile : ModelZone.ConcreteProfile)
  /-- Authored year presence survives effective Base-Year supplementation (spec/05 §1). -/
  | dateLiteral (profile : ModelZone.ConcreteProfile) (value : FullDate) (yearPresent : Bool := true)
  | dateTimeLiteral (profile : ModelZone.ConcreteProfile) (value : LocalDateTime)
  | dateConstruction (components : CheckedConstructedDateComponents model
      (Sum (Sum (CheckedConstructedDateSource model) (CheckedIndexedDateComponent model)) (ScalarTemporalNumericAtom model)))
  | timeConstruction (components : TimeComponentPrefix (Sum (Sum (CheckedTimeComponent model) (CheckedIndexedTimeComponent model)) (ScalarTemporalNumericAtom model)))
  | valueAsDate (source : CheckedZonedValueAsDateSource model)
  | indexedValueAsDate (source : CheckedIndexedValueAsDateSource model)
  | rangeBound (profile : ModelZone.ConcreteProfile) (source : CheckedDateRangeBoundOperand model)
  | baseYearBound (profile : ModelZone.ConcreteProfile) (year : Int) (bound : BaseYearRangeEndpoint)

inductive ScalarTemporalTransform (model : FlatModel) where
  | extremum (operator : TemporalExtremumOp)
  | dateTime (profile : ModelZone.ConcreteProfile)
  | calendarShift (profile : ModelZone.ConcreteProfile)
      (unit : DateShiftUnit) (amount : AuthoredNumericExpr (ScalarTemporalNumericAtom model))
  | dateFromDateTime (profile : ModelZone.ConcreteProfile)
  | timeFromDateTime (profile : ModelZone.ConcreteProfile)
  | subdayShift (profile : ModelZone.ConcreteProfile)
      (unit : DateTimeSubdayUnit) (amount : AuthoredNumericExpr (ScalarTemporalNumericAtom model))

inductive ScalarTemporalNumericAtom (model : FlatModel) where
  | numeric (source : HavingNumericAtomOf (TemporalExpressionOf (ScalarTemporalAtom model) (ScalarTemporalTransform model)))
  | indexedPart (selection : CheckedSemanticIndexSource model) (part : TemporalNumericPart)
      (partialFormat : Option FullDateTargetFormat)
  | ordinary (source : CheckedTemporalShiftAmount model)
  | projection (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile)
      (source : TemporalExpressionOf (ScalarTemporalAtom model) (ScalarTemporalTransform model))
end

abbrev ScalarTimeComponent (model : FlatModel) :=
  Sum (Sum (CheckedTimeComponent model) (CheckedIndexedTimeComponent model)) (ScalarTemporalNumericAtom model)

abbrev ScalarTemporalExpression (model : FlatModel) :=
  TemporalExpressionOf (ScalarTemporalAtom model) (ScalarTemporalTransform model)

/-- Extractor admission follows the source's component set, including its Base Year completion
(spec/05 and the numeric-extractor branch of CheckDatumExtractOpImpl). -/
def ScalarTemporalPrimitiveFault.toEvaluation : ScalarTemporalPrimitiveFault → ScalarTemporalEvaluationFault
  | .calendarUnavailable => .calendarUnavailable
  | .dateTimeLabelUnresolved => .dateTimeLabelUnresolved

def TemporalNumericPart.projectScalar (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile)
    (value : ScalarTemporalValue) : Except ScalarTemporalEvaluationFault Rat :=
  (part.projectScalarCore profile value).mapError ScalarTemporalPrimitiveFault.toEvaluation

def TemporalNumericPart.observeScalar (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile)
    (source : SimpleComparisonOperand ScalarTemporalValue) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
  (part.observeScalarCore profile source NumericValidationUnavailable.formal .nonRelevant).mapError ScalarTemporalPrimitiveFault.toEvaluation

end A12Kernel
