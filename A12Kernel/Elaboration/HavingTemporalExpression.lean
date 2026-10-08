import A12Kernel.Elaboration.TimeComponentAdmission
import A12Kernel.Elaboration.HavingDateValidity
import A12Kernel.Elaboration.DateRangeBound

namespace A12Kernel

def HavingTemporalExpressionRef.matchesModel (reference : HavingTemporalExpressionRef) (model : FlatModel) : Bool :=
  match reference.source with
  | .temporal field => (model.lookupUniqueId field.id).toOption.any fun declaration =>
      declaration.toTemporalField? == some field
  | .number field => (model.lookupUniqueId field.id).toOption.any fun declaration =>
      declaration.toNumberField? == some field
  | .string field => (model.lookupUniqueId field.id).toOption.any fun declaration =>
      declaration.toStringValueField? == some field
  | .range field components => (model.dateRangeSourceProfile field).any fun (_, _, format) =>
      format.components == components

private def elaborateHavingTimeComponents (model : FlatModel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (source : SurfaceHavingTimeComponents) : Except CorrelationElabError HavingTimeComponents :=
  source.mapM fun position component => do
    match component with
    | .nowExtractor part =>
        if position.extractor != part then throw .numericExpressionUnsupported
        pure (.inner, .nowExtractor part)
    | .constant text =>
        let some value := position.decodeConstant? text | throw .numericExpressionUnsupported
        pure (.inner, .constant value)
    | .field reference =>
        let declaration ← resolve reference
        match declaration.policy.kind.surfaceKind with
        | .number =>
            let some field := declaration.toNumberField? | throw .numericExpressionUnsupported
            if !model.admitsTimeNumberField position field declaration.repeatableScope then throw .numericExpressionUnsupported
            pure (reference.origin, .number field)
        | .string =>
            let some field := declaration.toStringValueField? | throw .numericExpressionUnsupported
            if !model.admitsTimeStringField field declaration.repeatableScope then throw .numericExpressionUnsupported
            pure (reference.origin, .string field)
        | _ => throw .numericExpressionUnsupported
    | .extractor part reference =>
        let declaration ← resolve reference
        let some field := declaration.toTemporalField? | throw .numericExpressionUnsupported
        if !model.admitsTimeExtractorField position part field declaration.repeatableScope then throw .numericExpressionUnsupported
        pure (reference.origin, .extractor field part)

private def HavingTimeComponents.wellFormed (source : HavingTimeComponents) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.allWithPosition fun position (origin, component) =>
    let scope := origin.availableLevels candidateLevels outerLevels
    match component with
    | .number field => model.admitsTimeNumberField position field scope
    | .string field => model.admitsTimeStringField field scope
    | .extractor field part => model.admitsTimeExtractorField position part field scope
    | .constant value => position.decodeConstant? (toString value) == some value
    | .nowExtractor part => position.extractor == part

namespace HavingTemporalExpression

def wellFormed (source : HavingTemporalExpression) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.baseYear == model.baseYear && ModelZone.ConcreteProfile.ofId? model.timeZoneId == some source.profile &&
    source.components?.isSome && source.references.all (fun reference =>
      reference.matchesModel model && (model.lookupUniqueId reference.fieldId).toOption.any fun declaration =>
        declaration.repeatableScope.isPrefixOf (reference.origin.availableLevels candidateLevels outerLevels)) &&
    source.core.atoms.all fun
      | .field reference => (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
          declaration.fieldValueReadRefusal?.isNone && !(declaration.toTemporalTargetPolicy?.any (·.partialMode != .full))
      | .timeConstruction components => components.wellFormed model candidateLevels outerLevels
      | .dateConstruction components => components.wellFormedForEnvironments model candidateLevels outerLevels false
      | .dateLiteral value false =>
          let authored : AuthoredDateLiteral := { year := none, month := value.civil.parts.month, day := value.civil.parts.day }
          ((authored.completedDate? model).bind FullDate.ofCivil?) == some value
      | .baseYearBound _ => model.hasBaseYear
      | _ => true

private def resolveCore (model : FlatModel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl) :
    SurfaceHavingTemporalExpression → Except CorrelationElabError
      (TemporalExpressionOf HavingTemporalAtom ScalarTemporalConstructorOp)
  | .field reference => do
      let declaration ← resolve { origin := reference.origin, field := reference.field }
      let some field := declaration.toTemporalField? | throw .numericExpressionUnsupported
      pure (.atom (.field { origin := reference.origin, field }))
  | .rangeBound reference bound => do
      let declaration ← resolve { origin := reference.origin, field := reference.field }
      let field : FlatDateRangeField := { id := declaration.id }
      let some (_, _, format) := model.dateRangeSourceProfile field | throw .numericExpressionUnsupported
      pure (.atom (.rangeBound reference.origin field format.components bound))
  | .timeConstruction components => do
      pure (.atom (.timeConstruction (← elaborateHavingTimeComponents model resolve components)))
  | .dateConstruction components => do
      pure (.atom (.dateConstruction (← elaborateHavingDateComponents model resolve components false)))
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
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
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
