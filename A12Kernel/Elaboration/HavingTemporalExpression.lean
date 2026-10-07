import A12Kernel.Elaboration.CorrelationSurface

namespace A12Kernel

namespace HavingTemporalExpression

def wellFormed (source : HavingTemporalExpression) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.baseYear == model.baseYear && ModelZone.ConcreteProfile.ofId? model.timeZoneId == some source.profile &&
    source.components?.isSome && source.core.atoms.all fun
      | .field reference => (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
          declaration.toTemporalField? == some reference.field && declaration.fieldValueReadRefusal?.isNone &&
            !(declaration.toTemporalTargetPolicy?.any (·.partialMode != .full)) &&
            declaration.repeatableScope.isPrefixOf (reference.origin.availableLevels candidateLevels outerLevels)
      | .dateLiteral value false =>
          let authored : AuthoredDateLiteral := { year := none, month := value.civil.parts.month, day := value.civil.parts.day }
          ((authored.completedDate? model).bind FullDate.ofCivil?) == some value
      | .baseYearBound _ => model.hasBaseYear
      | _ => true

private def resolveCore (model : FlatModel)
    (resolve : SurfaceHavingTemporalRef → Except CorrelationElabError HavingTemporalRef) :
    SurfaceHavingTemporalExpression → Except CorrelationElabError
      (TemporalExpressionOf HavingTemporalAtom ScalarTemporalConstructorOp)
  | .field reference => (fun reference => .atom (.field reference)) <$> resolve reference
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
      pure (.apply .dateTime (← resolveCore model resolve date) [← resolveCore model resolve time])
  | .dateFromDateTime source => do pure (.apply .dateFromDateTime (← resolveCore model resolve source) [])
  | .timeFromDateTime source => do pure (.apply .timeFromDateTime (← resolveCore model resolve source) [])

def elaborate (model : FlatModel)
    (resolve : SurfaceHavingTemporalRef → Except CorrelationElabError HavingTemporalRef)
    (source : SurfaceHavingTemporalExpression) : Except CorrelationElabError HavingTemporalExpression := do
  let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .numericExpressionUnsupported
  let rec strip : SurfaceHavingTemporalExpression → SurfaceHavingTemporalExpression
    | .grouped source => strip source
    | source => source
  let grouped := match source with | .grouped _ => true | _ => false
  let core ← resolveCore model resolve (strip source)
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
