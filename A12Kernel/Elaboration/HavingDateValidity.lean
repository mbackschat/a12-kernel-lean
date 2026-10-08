import A12Kernel.Elaboration.CorrelationSurface

namespace A12Kernel

/-- Resolve one direct component through the ordinary positional declaration gate. -/
def elaborateHavingDateComponent (model : FlatModel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (position : ConstructedDateComponentPosition) (source : SurfaceHavingDateComponent Temporal) :
    Except CorrelationElabError (HavingOrigin × ResolvedConstructedDateSource) := do
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
    | .expression _ _ => throw .numericExpressionUnsupported
  let checked ← (elaborateConstructedDateSource model position input scope).mapError .dateComponents
  pure (origin, checked.resolved)

def havingDateComponentWellFormed (model : FlatModel) (position : ConstructedDateComponentPosition)
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


end A12Kernel
