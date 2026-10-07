import A12Kernel.Elaboration.CorrelationSurface

namespace A12Kernel

/-- Resolve direct components through the ordinary positional admission gates. Each reference
uses its own environment; candidate availability remains the enclosing filter's final gate. -/
def elaborateHavingDateComponents (model : FlatModel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (source : SurfaceHavingDateComponents) (requireEntity : Bool := true) : Except CorrelationElabError HavingDateComponents := do
  let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId |
    throw (.dateComponents (.unsupportedZone model.timeZoneId))
  let component (position : ConstructedDateComponentPosition) (source : SurfaceHavingDateComponent) := do
    let (origin, input, scope) ← match source with
      | .field reference => do
          let declaration ← resolve reference
          let input ← match declaration.policy.kind.surfaceKind with
            | .number => pure (.numberField declaration.id)
            | .string => pure (.stringField declaration.id)
            | .temporal _ => pure (.dateYearField declaration.id)
            | _ => throw (.dateComponents (.sourceKind position declaration.id))
          pure (reference.origin, input, declaration.repeatableScope)
      | .extractor part reference => do
          let declaration ← resolve reference
          pure (reference.origin, .extractor part declaration.id, declaration.repeatableScope)
      | .constant text => pure (.inner, .constant text, [])
      | .baseYearExtractor .direct part => pure (.inner, .baseYearExtractor part, [])
      | .baseYearExtractor (.range endpoint) part => pure (.inner, .baseYearRangeExtractor endpoint part, [])
      | .clockExtractor .today part => pure (.inner, .todayExtractor part, [])
      | .clockExtractor .now part => pure (.inner, .nowExtractor part, [])
    let checked ← (elaborateConstructedDateSource model position input scope).mapError .dateComponents
    pure (origin, checked.resolved)
  let day ← component .day source.day
  let month ← component .month source.month
  let year ← match source.year with
    | .complete year => ResolvedConstructedDateYear.complete <$> component .year year
    | .baseYear => match model.baseYear with
        | some year => pure (.baseYear year)
        | none => throw (.dateComponents .missingBaseYear)
    | .centuryAndShortYear century shortYear => do
        pure (.centuryAndShortYear (← component .century century) (← component .shortYear shortYear))
  if requireEntity && !source.sources.any (fun | .field _ => true | _ => false) then
    throw (.dateComponents .onlyConstantsUsed)
  pure { day, month, year, profile }

private def componentWellFormed (model : FlatModel) (position : ConstructedDateComponentPosition)
    (scope : List RepeatableLevel) : ResolvedConstructedDateSource → Bool
  | .numberField source => model.admitsConstructedDateNumberField position source scope
  | .stringField source => model.admitsConstructedDateStringField position source scope
  | .dateYearField source => (model.lookupUniqueId source.id).toOption.any fun declaration =>
      declaration.toTemporalTargetPolicy?.any fun policy =>
        model.admitsConstructedDateYearField position source policy scope
  | .extractor source part partialFormat => model.admitsConstructedDateExtractorField position part source scope &&
      partialFormat == model.constructedDateExtractorPartialFormat source.id
  | .constant value =>
      let text := toString value
      let text := String.ofList (List.replicate (position.storedWidth - text.length) '0') ++ text
      position.decodeConstant? text == some value
  | .baseYearExtractor year _ part => model.baseYear == some year && position.extractor? == some part
  | .pointInTimeExtractor _ part zone profile => zone == model.timeZoneId &&
      ModelZone.ConcreteProfile.ofId? zone == some profile && position.extractor? == some part

def HavingDateComponents.wellFormedForEnvironments (source : HavingDateComponents) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) (requireEntity : Bool := true) : Bool :=
  let component (position : ConstructedDateComponentPosition) (operand : HavingOrigin × ResolvedConstructedDateSource) :=
    componentWellFormed model position (operand.1.availableLevels candidateLevels outerLevels) operand.2
  ModelZone.ConcreteProfile.ofId? model.timeZoneId == some source.profile &&
    (!requireEntity || source.sources.any (fun (_, operand) => match operand with
      | .numberField _ | .stringField _ | .dateYearField _ => true | _ => false)) &&
    component .day source.day && component .month source.month && match source.year with
      | .complete year => component .year year
      | .baseYear year => model.baseYear == some year
      | .centuryAndShortYear century shortYear => component .century century && component .shortYear shortYear

end A12Kernel
