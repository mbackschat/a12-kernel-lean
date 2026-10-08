import A12Kernel.Elaboration.TimeComponentAdmission
import A12Kernel.Elaboration.HavingDateValidity
import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.HavingTemporalSelection

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

private def elaborateHavingTimeComponent (model : FlatModel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (position : TimeComponentPosition) (component : SurfaceHavingTimeComponent Temporal) :
    Except CorrelationElabError (HavingOrigin × ResolvedTimeConstructionSource) := do
    match component with
    | .expression _ _ => throw .numericExpressionUnsupported
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

private def havingTimeComponentWellFormed (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) (position : TimeComponentPosition)
    (origin : HavingOrigin) (component : ResolvedTimeConstructionSource) : Bool :=
  let scope := origin.availableLevels candidateLevels outerLevels
  match component with
  | .number field => model.admitsTimeNumberField position field scope
  | .string field => model.admitsTimeStringField field scope
  | .extractor field part => model.admitsTimeExtractorField position part field scope
  | .constant value => position.decodeConstant? (toString value) == some value
  | .nowExtractor part => position.extractor == part

namespace HavingTemporalExpression

private def projectionAdmitted (model : FlatModel) (part : TemporalNumericPart) (core : HavingTemporalCore) : Bool :=
  let literal := match core with
    | .atom (.dateLiteral _ _) | .atom (.timeLiteral _) | .atom (.dateTimeLiteral _) => true
    | _ => false
  !literal && coreAdmittedSourceSlot core &&
    (componentsWith model.baseYear core).any (part.admitsComponents · model.hasBaseYear)

private def dateComponentsWellFormed (source : HavingDateComponents) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  let component (position : ConstructedDateComponentPosition) : HavingDateComponent → Bool
    | .direct origin source => havingDateComponentWellFormed model position (origin.availableLevels candidateLevels outerLevels) source
    | .expression part source => position.extractor? == some part && projectionAdmitted model (.date part) source
  ModelZone.ConcreteProfile.ofId? model.timeZoneId == some source.profile &&
    component .day source.day && component .month source.month && match source.year with
      | .complete year => component .year year
      | .baseYear year => model.baseYear == some year
      | .centuryAndShortYear century shortYear => component .century century && component .shortYear shortYear

private def timeComponentsWellFormed (source : HavingTimeComponents) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.allWithPosition fun position component => match component with
    | .direct origin source => havingTimeComponentWellFormed model candidateLevels outerLevels position origin source
    | .expression part source => position.extractor == part && projectionAdmitted model (.time part) source

def wellFormed (source : HavingTemporalExpression) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.baseYear == model.baseYear && ModelZone.ConcreteProfile.ofId? model.timeZoneId == some source.profile &&
    source.components?.isSome && source.references.all (·.matchesModel model) &&
    source.presenceSlots.all (·.wellFormedForEnvironments model candidateLevels outerLevels) &&
    (HavingTemporalCore.allAtoms source.core).all fun
      | .shift _ _ amount =>
          amount.allAtoms (fun | .inl _ => true | .inr (part, core) => projectionAdmitted model part core) &&
            (amount.summary? (fun | .inl reference => .field reference.field.info.scale | .inr _ => .field 0)).isSome
      | .partialDate source => (model.lookupUniqueId source.reference.field.id).toOption.any fun declaration =>
          (certifyPartialDateInputField declaration).toOption.any fun checked =>
            checked.field == source.reference.field && checked.format == source.format &&
              checked.mode == source.mode && checked.policy.youngerThan1900Check == source.youngerThan1900Check
      | .selection kind slots => kind.wellFormed model candidateLevels outerLevels slots
      | .field reference => (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
          declaration.fieldValueReadRefusal?.isNone && !(declaration.toTemporalTargetPolicy?.any (·.partialMode != .full))
      | .timeConstruction components => timeComponentsWellFormed components model candidateLevels outerLevels
      | .dateConstruction components => dateComponentsWellFormed components model candidateLevels outerLevels
      | .dateLiteral value false =>
          let authored : AuthoredDateLiteral := { year := none, month := value.civil.parts.month, day := value.civil.parts.day }
          ((authored.completedDate? model).bind FullDate.ofCivil?) == some value
      | .baseYearBound _ => model.hasBaseYear
      | _ => true

mutual
private def resolveCore (model : FlatModel)
    (resolveSelection : HavingTemporalSelection → SurfaceHavingEntitySource →
      Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)))
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl) :
    SurfaceHavingTemporalExpression → Except CorrelationElabError
      (TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation)
  | .selection kind source => do pure (.atom (.selection kind (← resolveSelection kind source)))
  | .shift unit source amount => do
      if !source.admittedSourceSlot true then throw .numericExpressionUnsupported
      let source ← resolveCore model resolveSelection resolve source
      let amount ← resolveAmount model resolveSelection resolve amount
      pure (.atom (.shift unit source amount))
  | .partialDate reference endpoint => do
      let declaration ← resolve { origin := reference.origin, field := reference.field }
      let .ok checked := certifyPartialDateInputField declaration | throw .numericExpressionUnsupported
      pure (.atom (.partialDate {
        reference := { origin := reference.origin, field := checked.field }
        format := checked.format, mode := checked.mode, youngerThan1900Check := checked.policy.youngerThan1900Check, endpoint }))
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
      pure (.atom (.timeConstruction (← resolveTimeComponents model resolveSelection resolve components)))
  | .dateConstruction components => do
      pure (.atom (.dateConstruction (← resolveDateComponents model resolveSelection resolve components)))
  | .dateLiteral authored => do
      let some value := (authored.completedDate? model).bind FullDate.ofCivil? | throw .numericExpressionUnsupported
      pure (.atom (.dateLiteral value authored.year.isSome))
  | .timeLiteral value => pure (.atom (.timeLiteral value))
  | .dateTimeLiteral value => pure (.atom (.dateTimeLiteral value))
  | .today => pure (.atom .today)
  | .now => pure (.atom .now)
  | .baseYearBound bound =>
      if model.hasBaseYear then pure (.atom (.baseYearBound bound)) else throw .numericExpressionUnsupported
  | .grouped source => resolveCore model resolveSelection resolve source
  | .combine operator first rest => do
      let first ← resolveCore model resolveSelection resolve first
      let rest ← rest.mapM (resolveCore model resolveSelection resolve)
      pure (.apply (.extremum operator) first rest)
  | .dateTime date time => do
      if !date.admittedSourceSlot true || !time.admittedSourceSlot then throw .numericExpressionUnsupported
      pure (.apply (.constructor .dateTime) (← resolveCore model resolveSelection resolve date) [← resolveCore model resolveSelection resolve time])
  | .dateFromDateTime source => do
      if !source.admittedSourceSlot then throw .numericExpressionUnsupported
      pure (.apply (.constructor .dateFromDateTime) (← resolveCore model resolveSelection resolve source) [])
  | .timeFromDateTime source => do
      if !source.admittedSourceSlot then throw .numericExpressionUnsupported
      pure (.apply (.constructor .timeFromDateTime) (← resolveCore model resolveSelection resolve source) [])

private def resolveAmount (model : FlatModel)
    (resolveSelection : HavingTemporalSelection → SurfaceHavingEntitySource →
      Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)))
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (amount : SurfaceHavingTemporalAmount) : Except CorrelationElabError HavingTemporalAmount := do
  let result ← amount.mapMSubterm fun source _hNumericSource => do
    match _hSource : source with
    | .inl reference =>
        let declaration ← resolve { origin := reference.origin, field := reference.field }
        let some field := declaration.toNumberField? | throw .numericExpressionUnsupported
        pure (.inl { origin := reference.origin, field })
    | .inr (part, source) =>
        if !source.admittedSourceSlot then throw .numericExpressionUnsupported
        let core ← resolveCore model resolveSelection resolve source
        if !projectionAdmitted model part core then throw .numericExpressionUnsupported
        pure (.inr (part, core))
  if !result.isAdmittedResolvedNumericOperation || result.numericOperationAuthoringCheck != .accepted ||
      (result.summary? (fun | .inl reference => .field reference.field.info.scale | .inr _ => .field 0)).isNone then
    throw .numericExpressionUnsupported
  pure result
decreasing_by all_goals simp_all +arith <;> omega

private def resolveDateOperand (model : FlatModel)
    (resolveSelection : HavingTemporalSelection → SurfaceHavingEntitySource → Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)))
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (position : ConstructedDateComponentPosition) : SurfaceHavingDateComponent SurfaceHavingTemporalExpression → Except CorrelationElabError HavingDateComponent
  | .expression part source => do
      if position.extractor? != some part || !source.admittedSourceSlot then throw .numericExpressionUnsupported
      let core ← resolveCore model resolveSelection resolve source
      if !projectionAdmitted model (.date part) core then throw .numericExpressionUnsupported
      pure (.expression part core)
  | component => do
      let (origin, source) ← elaborateHavingDateComponent model resolve position component
      pure (.direct origin source)

private def resolveTimeOperand (model : FlatModel)
    (resolveSelection : HavingTemporalSelection → SurfaceHavingEntitySource → Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)))
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (position : TimeComponentPosition) : SurfaceHavingTimeComponent SurfaceHavingTemporalExpression → Except CorrelationElabError HavingTimeComponent
  | .expression part source => do
      if position.extractor != part || !source.admittedSourceSlot then throw .numericExpressionUnsupported
      let core ← resolveCore model resolveSelection resolve source
      if !projectionAdmitted model (.time part) core then throw .numericExpressionUnsupported
      pure (.expression part core)
  | component => do
      let (origin, source) ← elaborateHavingTimeComponent model resolve position component
      pure (.direct origin source)

private def resolveDateComponents (model : FlatModel)
    (resolveSelection : HavingTemporalSelection → SurfaceHavingEntitySource → Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)))
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl) : SurfaceHavingDateComponents → Except CorrelationElabError HavingDateComponents
  | ⟨day, month, year⟩ => do
      let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId |
        throw (.dateComponents (.unsupportedZone model.timeZoneId))
      let day ← resolveDateOperand model resolveSelection resolve .day day
      let month ← resolveDateOperand model resolveSelection resolve .month month
      let year ← match year with
        | .complete source => .complete <$> resolveDateOperand model resolveSelection resolve .year source
        | .baseYear => match model.baseYear with
            | some year => pure (.baseYear year)
            | none => throw (.dateComponents .missingBaseYear)
        | .centuryAndShortYear century shortYear => do
            pure (.centuryAndShortYear
              (← resolveDateOperand model resolveSelection resolve .century century)
              (← resolveDateOperand model resolveSelection resolve .shortYear shortYear))
      pure { day, month, year, profile }
private def resolveTimeComponents (model : FlatModel)
    (resolveSelection : HavingTemporalSelection → SurfaceHavingEntitySource → Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)))
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl) : SurfaceHavingTimeComponents → Except CorrelationElabError HavingTimeComponents
  | .empty => pure .empty
  | .hour hour => .hour <$> resolveTimeOperand model resolveSelection resolve .hour hour
  | .minute hour minute => do
      pure (.minute (← resolveTimeOperand model resolveSelection resolve .hour hour)
        (← resolveTimeOperand model resolveSelection resolve .minute minute))
  | .second hour minute second => do
      pure (.second (← resolveTimeOperand model resolveSelection resolve .hour hour)
        (← resolveTimeOperand model resolveSelection resolve .minute minute)
        (← resolveTimeOperand model resolveSelection resolve .second second))
end

def elaborate (model : FlatModel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (source : SurfaceHavingTemporalExpression)
    (resolveSelection : HavingTemporalSelection → SurfaceHavingEntitySource →
      Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)) := fun _ _ => throw .numericExpressionUnsupported) :
    Except CorrelationElabError HavingTemporalExpression := do
  let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .numericExpressionUnsupported
  let rec strip : SurfaceHavingTemporalExpression → SurfaceHavingTemporalExpression
    | .grouped source => strip source
    | source => source
  let grouped := match source with | .grouped _ => true | _ => false
  let core ← resolveCore model resolveSelection resolve (strip source)
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

def HavingConstructedDate.wellFormedForEnvironments (source : HavingConstructedDate) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) (requireEntity : Bool := true) : Bool :=
  source.asTemporal.wellFormed model candidateLevels outerLevels &&
    (!requireEntity || source.components.sources.any fun
      | .direct _ (.numberField _) | .direct _ (.stringField _) | .direct _ (.dateYearField _) => true
      | _ => false)

def elaborateHavingDateComponents (model : FlatModel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (source : SurfaceHavingDateComponents) (requireEntity : Bool := true) : Except CorrelationElabError HavingConstructedDate := do
  let components ← HavingTemporalExpression.resolveDateComponents model (fun _ _ => throw .numericExpressionUnsupported) resolve source
  if requireEntity && !source.sources.any (fun | .field _ => true | _ => false) then
    throw (.dateComponents .onlyConstantsUsed)
  pure { components, baseYear := model.baseYear }

end A12Kernel
