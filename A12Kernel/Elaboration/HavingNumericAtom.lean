import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.HavingGroupCount
import A12Kernel.Elaboration.HavingNumericProduct
import A12Kernel.Elaboration.HavingCollectionCount
import A12Kernel.Elaboration.DateRangeBoundComponent
import A12Kernel.Elaboration.TemporalNumericInput
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.ConstructedDateComponents

namespace A12Kernel

/-- Date differences retain the complete-field source boundary of the temporal expression
owners; component atoms carry their own declaration precision certificate (spec/05 §3). -/
def HavingNumericAtomOf.admitsTemporalAmountSources (model : FlatModel)
    (atom : HavingNumericAtomOf Temporal) : Bool :=
  let fields := match atom with
    | .dateDifference .. | .dayDifference .. | .dateTimeDifference .. =>
        atom.fieldOriginsWith (fun _ => [])
    | _ => []
  fields.all fun (_, fieldId) => (model.lookupUniqueId fieldId).toOption.any fun declaration =>
    declaration.fieldValueReadRefusal?.isNone &&
      !(declaration.toTemporalTargetPolicy?.any (·.partialMode != .full))

structure ResolvedHavingNumberRef where
  declaration : FlatFieldDecl
  core : HavingNumberRef

structure HavingNumericResolvers where
  firstFilled : SurfaceHavingEntitySource → Except CorrelationElabError (List (HavingFieldListSlot HavingNumberRef)) := fun _ => throw .numericExpressionUnsupported
  groupCount : SurfaceHavingEntitySource → Except CorrelationElabError (List HavingGroupCountOperand) := fun _ => throw .numericExpressionUnsupported
  product : SurfaceHavingEntitySource → Except CorrelationElabError HavingNumericProduct := fun _ => throw .numericExpressionUnsupported
  collectionCount : SurfaceHavingCollectionCount → Except CorrelationElabError HavingCollectionCount := fun _ => throw .numericExpressionUnsupported
  aggregate : NumericAggregateOp → SurfaceHavingEntitySource → Except CorrelationElabError (HavingNumericAtomOf Empty) := fun _ _ => throw .numericExpressionUnsupported
  baseYear : Except CorrelationElabError Int := throw .numericExpressionUnsupported
  clockPart : HavingClockSource → TemporalNumericPart → Except CorrelationElabError (HavingNumericAtomOf Empty) := fun _ _ => throw .numericExpressionUnsupported
  fieldValueAsNumber : SurfaceHavingStringRef → Except CorrelationElabError ResolvedFieldValueAsNumberSource := fun _ => throw .numericExpressionUnsupported
  stringValue : HavingOrigin → SurfaceFieldPath → Except CorrelationElabError FlatStringField := fun _ _ => throw .numericExpressionUnsupported
  dateDifference : DateDifferenceUnit → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → Except CorrelationElabError (HavingNumericAtomOf Empty) := fun _ _ _ => throw .numericExpressionUnsupported
  dayDifference : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → Except CorrelationElabError (HavingNumericAtomOf Empty) := fun _ _ => throw .numericExpressionUnsupported
  dateTimeDifference : DateTimeSubdayUnit → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → Except CorrelationElabError (HavingNumericAtomOf Empty) := fun _ _ _ => throw .numericExpressionUnsupported
  dateRangeBoundPart : HavingOrigin → SurfaceFieldPath → DateNumericPart → Except CorrelationElabError FlatDateRangeField := fun _ _ _ => throw .numericExpressionUnsupported
  temporalPart : HavingOrigin → SurfaceFieldPath → TemporalNumericPart → Except CorrelationElabError (FlatTemporalField × Option FullDateTargetFormat) := fun _ _ _ => throw .numericExpressionUnsupported
  number : HavingOrigin → SurfaceFieldPath →
    Except CorrelationElabError ResolvedHavingNumberRef := fun _ _ => throw .numericExpressionUnsupported
  repetition : HavingOrigin → SurfaceGroupReference →
    Except CorrelationElabError HavingRepetitionRef := fun _ _ => throw .numericExpressionUnsupported

def HavingNumericResolvers.resolveWith [SizeOf Source] (resolvers : HavingNumericResolvers)
    (atom : SurfaceHavingNumericAtomOf Source)
    (difference : TemporalOperationUnit → (left right : Source) → sizeOf left < sizeOf atom → sizeOf right < sizeOf atom → Except CorrelationElabError (HavingNumericAtomOf Target))
    (projection : TemporalNumericPart → (source : Source) → sizeOf source < sizeOf atom → Except CorrelationElabError (HavingNumericAtomOf Target)) :
    Except CorrelationElabError (HavingNumericAtomOf Target) :=
  match atom with
  | .firstFilled source => HavingNumericAtomOf.firstFilled <$> resolvers.firstFilled source
  | .groupCount source => HavingNumericAtomOf.groupCount <$> resolvers.groupCount source
  | .product source => HavingNumericAtomOf.product <$> resolvers.product source
  | .collectionCount source => HavingNumericAtomOf.collectionCount <$> resolvers.collectionCount source
  | .aggregate op source => (fun atom => atom.mapTemporal Empty.elim) <$> resolvers.aggregate op source
  | .dateDifference unit left right => (fun atom => atom.mapTemporal Empty.elim) <$> resolvers.dateDifference unit left right
  | .dayDifference left right => (fun atom => atom.mapTemporal Empty.elim) <$> resolvers.dayDifference left right
  | .dateTimeDifference unit left right => (fun atom => atom.mapTemporal Empty.elim) <$> resolvers.dateTimeDifference unit left right
  | .baseYear => HavingNumericAtomOf.baseYear <$> resolvers.baseYear
  | .baseYearDatePart source part => (fun year => .baseYearDatePart year source part) <$> resolvers.baseYear
  | .clockPart source part => (fun atom => atom.mapTemporal Empty.elim) <$> resolvers.clockPart source part
  | .fieldValueAsNumber reference => (.fieldValueAsNumber reference.origin ·) <$> resolvers.fieldValueAsNumber reference
  | .stringLength origin reference => (.stringLength origin ·) <$> resolvers.stringValue origin reference
  | .stringRange origin reference start finish => do
      let source ← (resolvers.stringValue origin reference).mapError fun
        | .text (.lengthOperandKindMismatch _ _) => .numericExpressionUnsupported
        | error => error
      if !validStringRange start finish then throw .numericExpressionUnsupported
      pure (.stringRange origin source start finish)
  | .dateRangeBoundPart origin reference bound part =>
      (fun source => .dateRangeBoundPart origin source bound part) <$> resolvers.dateRangeBoundPart origin reference part
  | .temporalDifference unit left right => difference unit left right (by simp; omega) (by simp; omega)
  | .temporalExpressionPart part source => projection part source (by simp; omega)
  | .temporalPart origin reference part =>
      (fun (source, format) => .temporalPart origin source part format) <$> resolvers.temporalPart origin reference part
  | .field reference => do
      let resolved ← (resolvers.number reference.origin reference.field).mapError fun
        | .fieldNotNumber path actual => .numericOperandFieldNotNumber path actual
        | error => error
      pure (.field resolved.core)
  | .repetition reference =>
      (.repetition ·) <$> resolvers.repetition reference.origin reference.group

def repeatableScopeAvailable (required available : List RepeatableLevel) : Bool :=
  required.isPrefixOf available

/-- Resolve the complete binding scope from the model, including fixed-group ancestry.
    A forged fixed reference to a repeatable group cannot certify a constant index. -/
def HavingRepetitionRef.scope? (reference : HavingRepetitionRef) (model : FlatModel) :
    Option (List RepeatableLevel) :=
  match reference.source with
  | .repeatable level =>
      (model.repeatableGroupAtLevel? level).map fun group =>
        model.repeatableScopeForGroupPath group.path
  | .fixed path =>
      if model.hasGroupPath path && !model.repeatableGroups.any (fun group => group.path == path)
      then some (model.repeatableScopeForGroupPath path)
      else none

def HavingRepetitionRef.availableIn (reference : HavingRepetitionRef) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  (reference.scope? model).any fun scope =>
    repeatableScopeAvailable scope (reference.origin.availableLevels candidateLevels outerLevels)

private def FlatModel.admitsHavingNumberInEnvironment (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel)
    (reference : HavingNumberRef) : Bool :=
  match model.lookupUniqueId reference.field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toNumberField? == some reference.field &&
        repeatableScopeAvailable declaration.repeatableScope
          (reference.origin.availableLevels candidateLevels outerLevels)

private def calendarSourceAdmitted (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) :
    ResolvedDateDifferenceOperand HavingTemporalRef → Bool
  | .literal source anchorYear => source.admittedIn model anchorYear
  | .baseYear year _ => model.baseYear == some year
  | .today profile => ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile
  | .field reference => (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
      declaration.toTemporalField? == some reference.field &&
        repeatableScopeAvailable declaration.repeatableScope (reference.origin.availableLevels candidateLevels outerLevels)

def HavingNumericAtomOf.wellFormedWith (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (difference : TemporalOperationUnit → Temporal → Temporal → Bool)
    (projection : TemporalNumericPart → Temporal → Bool) : HavingNumericAtomOf Temporal → Bool
  | .groupCount operands => HavingGroupCount.wellFormed operands model candidateLevels outerLevels
  | .product source => source.wellFormed model candidateLevels outerLevels
  | .collectionCount source => source.wellFormed model candidateLevels outerLevels
  | .firstFilled slots | .aggregate _ slots => HavingNumberAggregate.wellFormed model candidateLevels outerLevels slots
  | .dateDifference unit left right => unit.compatible model.hasBaseYear
      (left.componentsWith (·.field.components)) (right.componentsWith (·.field.components)) &&
      [left, right].all (calendarSourceAdmitted model candidateLevels outerLevels)
  | .dayDifference profile left right => ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile &&
      CalendarDayDifference.admittedBy (left.componentsWith (·.field.components)) &&
      CalendarDayDifference.admittedBy (right.componentsWith (·.field.components)) &&
      CalendarDayDifference.yearCompatible model.hasBaseYear
        (left.componentsWith (·.field.components)) (right.componentsWith (·.field.components)) &&
      [left, right].all (calendarSourceAdmitted model candidateLevels outerLevels)
  | .dateTimeDifference unit left right =>
      (left.dateTimeDifferenceComponentsWith? (·.field.components)).any fun first =>
        (right.dateTimeDifferenceComponentsWith? (·.field.components)).any fun second =>
          unit.compatible first second &&
            (left.fieldValues ++ right.fieldValues).all fun reference =>
              (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
                declaration.toTemporalField? == some reference.field &&
                  repeatableScopeAvailable declaration.repeatableScope (reference.origin.availableLevels candidateLevels outerLevels)
  | .baseYear year | .baseYearDatePart year _ _ => model.baseYear == some year
  | .clockPart source profile part => source.admits part &&
      ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile
  | .fieldValueAsNumber origin source => (model.certifiedFieldValueAsNumberDeclaration? source).any fun declaration =>
      repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
  | .field reference => model.admitsHavingNumberInEnvironment candidateLevels outerLevels reference
  | .stringLength origin fld => (model.lookupUniqueId fld.id).toOption.any fun declaration =>
      declaration.toStringValueField? == some fld && declaration.fieldValueReadRefusal?.isNone &&
        repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
  | .stringRange origin fld start finish => validStringRange start finish &&
      (model.lookupUniqueId fld.id).toOption.any fun declaration =>
        declaration.toStringValueField? == some fld && declaration.fieldValueReadRefusal?.isNone &&
          repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
  | .dateRangeBoundPart origin fld _ part => model.exposesDateRangeBoundPart fld part &&
      (model.lookupUniqueId fld.id).toOption.any fun declaration =>
        repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
  | .temporalDifference unit left right => difference unit left right
  | .temporalExpressionPart part source => projection part source
  | .temporalPart origin fld part format => model.admitsTemporalNumericPart fld part format &&
      (model.lookupUniqueId fld.id).toOption.any fun declaration =>
        declaration.toTemporalField? == some fld &&
          repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
  | .repetition reference => reference.availableIn model candidateLevels outerLevels

end A12Kernel
