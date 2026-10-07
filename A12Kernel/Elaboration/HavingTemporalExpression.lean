import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.DateRangeBound

namespace A12Kernel

def HavingTemporalExpressionRef.matchesModel (reference : HavingTemporalExpressionRef) (model : FlatModel) : Bool :=
  match reference.source with
  | .inl field => (model.lookupUniqueId field.id).toOption.any fun declaration =>
      declaration.toTemporalField? == some field && declaration.fieldValueReadRefusal?.isNone &&
        !(declaration.toTemporalTargetPolicy?.any (·.partialMode != .full))
  | .inr (field, components) => (model.dateRangeSourceProfile field).any fun (_, _, format) =>
      format.components == components

namespace HavingTemporalExpression

def wellFormed (source : HavingTemporalExpression) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.baseYear == model.baseYear && ModelZone.ConcreteProfile.ofId? model.timeZoneId == some source.profile &&
    source.components?.isSome && source.references.all (fun reference =>
      reference.matchesModel model && (model.lookupUniqueId reference.fieldId).toOption.any fun declaration =>
        declaration.repeatableScope.isPrefixOf (reference.origin.availableLevels candidateLevels outerLevels)) &&
    source.core.atoms.all fun
      | .dateLiteral value false =>
          let authored : AuthoredDateLiteral := { year := none, month := value.civil.parts.month, day := value.civil.parts.day }
          ((authored.completedDate? model).bind FullDate.ofCivil?) == some value
      | .baseYearBound _ => model.hasBaseYear
      | _ => true

private def resolveCore (model : FlatModel)
    (resolve : SurfaceHavingTemporalRef → Except CorrelationElabError HavingTemporalRef)
    (resolveRange : SurfaceHavingTemporalRef → Except CorrelationElabError (FlatDateRangeField × TemporalComponents)) :
    SurfaceHavingTemporalExpression → Except CorrelationElabError
      (TemporalExpressionOf HavingTemporalAtom ScalarTemporalConstructorOp)
  | .field reference => (fun reference => .atom (.field reference)) <$> resolve reference
  | .rangeBound reference bound => do
      let (field, components) ← resolveRange reference
      pure (.atom (.rangeBound reference.origin field components bound))
  | .dateLiteral authored => do
      let some value := (authored.completedDate? model).bind FullDate.ofCivil? | throw .numericExpressionUnsupported
      pure (.atom (.dateLiteral value authored.year.isSome))
  | .timeLiteral value => pure (.atom (.timeLiteral value))
  | .dateTimeLiteral value => pure (.atom (.dateTimeLiteral value))
  | .today => pure (.atom .today)
  | .now => pure (.atom .now)
  | .baseYearBound bound =>
      if model.hasBaseYear then pure (.atom (.baseYearBound bound)) else throw .numericExpressionUnsupported
  | .grouped _ => throw .numericExpressionUnsupported
  | .dateTime date time => do
      pure (.apply .dateTime (← resolveCore model resolve resolveRange date) [← resolveCore model resolve resolveRange time])
  | .dateFromDateTime source => do pure (.apply .dateFromDateTime (← resolveCore model resolve resolveRange source) [])
  | .timeFromDateTime source => do pure (.apply .timeFromDateTime (← resolveCore model resolve resolveRange source) [])

def elaborate (model : FlatModel)
    (resolve : SurfaceHavingTemporalRef → Except CorrelationElabError HavingTemporalRef)
    (resolveRange : SurfaceHavingTemporalRef → Except CorrelationElabError (FlatDateRangeField × TemporalComponents))
    (source : SurfaceHavingTemporalExpression) : Except CorrelationElabError HavingTemporalExpression := do
  let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .numericExpressionUnsupported
  let rec strip : SurfaceHavingTemporalExpression → SurfaceHavingTemporalExpression
    | .grouped source => strip source
    | source => source
  let grouped := match source with | .grouped _ => true | _ => false
  let core ← resolveCore model resolve resolveRange (strip source)
  let result : HavingTemporalExpression := { core, profile, baseYear := model.baseYear, grouped }
  if result.components?.isNone then throw .numericExpressionUnsupported
  pure result

def isConstant (source : HavingTemporalExpression) : Bool :=
  match source.core with
  | .atom (.dateLiteral _ _) | .atom (.timeLiteral _) | .atom (.dateTimeLiteral _) | .atom .now | .atom .today => true
  | _ => false

def isNow (source : HavingTemporalExpression) : Bool :=
  match source.core with | .atom .now => true | _ => false

private def ungroupedClock (source : HavingTemporalExpression) : Bool :=
  !source.grouped && match source.core with | .atom .now | .atom .today => true | _ => false

def comparisonAdmitted (operator : TemporalComparisonOp) (left right : HavingTemporalExpression) : Bool :=
  !(left.isConstant && right.isConstant && left.ungroupedClock == right.ungroupedClock) &&
    (left.components?).any fun first => (right.components?).any fun second =>
      operator.admitsFormats left.baseYear.isSome first second &&
        (!left.isNow || operator.admitsNow left.baseYear.isSome second) &&
        (!right.isNow || operator.admitsNow left.baseYear.isSome first) &&
        [first, second].all fun components =>
          !components.hasTime || components == TemporalComponents.now || components == TemporalComponents.time

end HavingTemporalExpression

end A12Kernel
