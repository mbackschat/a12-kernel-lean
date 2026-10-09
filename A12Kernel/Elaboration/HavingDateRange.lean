import A12Kernel.Elaboration.HavingEntityList
import A12Kernel.Elaboration.DateRangeConstructionComparison

namespace A12Kernel

/-- Overlap's declaration walk precedes its year gate. Within each authored expansion the
format spelling must agree; across slots only year presence agrees, unless BaseYear supplies it
(CheckEntityListenUtils.checkDateRangeConsistentRegardingYear; spec/05 §8). -/
def checkHavingOverlapDeclarations (model : FlatModel) (expansions : List (List FlatFieldDecl)) :
    Except CorrelationElabError Unit := do
  for declaration in expansions.flatten do
    if declaration.policy.kind != .dateRange then throw (.dateRange .noDateRange)
    if declaration.toDateRangeDeclarationPolicy?.any (·.interpretationOfYear.isSome) then
      throw (.dateRange .invalidDateRangeFormat)
  if model.hasBaseYear then return
  let mut year : Option Bool := none
  for declarations in expansions do
    let first :: rest := declarations | throw .incoherentCore
    let some policy := first.toDateRangeDeclarationPolicy? | throw .incoherentCore
    if rest.any (fun declaration => declaration.toDateRangeDeclarationPolicy?.all (·.format != policy.format)) then
      throw (.dateRange .dateWithAndWithoutYear)
    let hasYear := policy.format.contains 'y'
    if year.any (· != hasYear) then throw (.dateRange .dateWithAndWithoutYear)
    year := some hasYear

private def rangeFormat (model : FlatModel) (reference : HavingPresenceRef) : Option DateRangeInputFormat := do
  let declaration ← (model.lookupUniqueId reference.field).toOption
  (certifyDateRangeInputField declaration).toOption.map (·.format)

private def operandComponents (model : FlatModel) : HavingDateRangeOperand → Option TemporalComponents
  | .stored reference => (rangeFormat model reference).map (·.components)
  | .constructed start finish =>
      if start.format.sameComponents finish.format then some start.format.components else none

private def operandWellFormed (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (source : HavingDateRangeOperand) : Bool :=
  source.references.all (fun ref => (HavingFieldListSlot.direct ref).wellFormedForEnvironments model candidateLevels outerLevels) &&
    match source with
    | .stored reference => (rangeFormat model reference).isSome
    | .constructed start finish =>
      start.format.sameComponents finish.format && [start, finish].all fun endpoint =>
        (elaborateDateRangeEndpointIn model (endpoint.reference.origin.availableLevels candidateLevels outerLevels)
          endpoint.reference.field).toOption.any fun checked => checked.format == endpoint.format && checked.profile == endpoint.profile

/-- Agreement uses each authored expansion's format spelling before comparing year classes
(spec/05 §8, inbound-2026-09-21b-corrections); flattening slots loses that first gate. -/
private def overlapProfilesAdmitted (model : FlatModel)
    (slots : List (HavingFieldListSlot HavingPresenceRef)) : Bool :=
  let references := slots.flatMap (·.references)
  let expansions := slots.map fun slot => slot.references.filterMap fun ref =>
    (model.lookupUniqueId ref.field).toOption
  expansions.flatten.length == references.length &&
    references.all (fun ref => (rangeFormat model ref).isSome) &&
    (checkHavingOverlapDeclarations model expansions).isOk

def HavingDateRangePredicate.wellFormedForEnvironments (source : HavingDateRangePredicate)
    (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  match source with
  | .compare _ left right =>
      operandWellFormed model candidateLevels outerLevels left && operandWellFormed model candidateLevels outerLevels right &&
        (operandComponents model left).isSome && operandComponents model left == operandComponents model right
  | .overlap scalar slots =>
      !slots.isEmpty && havingEntityListWellFormed model candidateLevels outerLevels source.presenceSlots &&
        (scalar.isSome || slots.all fun | .extent (.group _) _ | .extent (.starredGroup _ _) _ => false | _ => true) &&
        overlapProfilesAdmitted model source.presenceSlots

/-- Endpoint format/profile certification is shared with ordinary construction. Each authored
reference resolves in its own environment before the cross-operand component gate (spec/05 §8). -/
def elaborateHavingDateRange (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel)
    (resolve : SurfaceHavingPresenceRef → Except CorrelationElabError FlatFieldDecl)
    (source : SurfaceHavingDateRangePredicate) : Except CorrelationElabError HavingDateRangePredicate := do
  let reference (ref : SurfaceHavingPresenceRef) := do
    let declaration ← resolve ref
    pure ({ origin := ref.origin, field := declaration.id } : HavingPresenceRef)
  let endpoint (ref : SurfaceHavingPresenceRef) := do
    let declaration ← resolve ref
    let checked ← (elaborateDateRangeEndpointIn model declaration.repeatableScope declaration.id).mapError fun error =>
      match error.diagnostic? with | some diagnostic => .dateRange diagnostic | none => .incoherentCore
    pure ({ reference := { origin := ref.origin, field := declaration.id }, format := checked.format, profile := checked.profile } : HavingDateRangeEndpoint)
  let operand : SurfaceHavingDateRangeOperand → Except CorrelationElabError HavingDateRangeOperand
    | .stored ref => do
        let ref ← reference ref
        if (rangeFormat model ref).isNone then throw (.dateRange .wrongDateFormatForOp)
        pure (.stored ref)
    | .constructed start finish => do
        let start ← endpoint start
        let finish ← endpoint finish
        if !start.format.sameComponents finish.format then throw (.dateRange .wrongDateFormatForOp)
        pure (.constructed start finish)
  match source with
  | .compare operator left right =>
      let left ← operand left
      let right ← operand right
      discard <| (checkComparisonEntry (if operator.toEquality?.isSome then .equality else .ordering)
        (.expression .dateRange) (.expression .dateRange)).mapError .comparisonEntry
      let some equality := operator.toEquality? | throw .incoherentCore
      if operandComponents model left != operandComponents model right then throw (.dateRange .invalidCompareToDateRange)
      pure (.compare equality left right)
  | .overlap scalar source =>
      let combined : SurfaceHavingEntitySource := match scalar with
        | none => source
        | some ref => { first := .entity { origin := ref.origin, field := ref.field }, rest := source.first :: source.rest }
      let operands ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels combined
      if scalar.isNone then
        checkHavingEntityDuplicates operands
        checkHavingEntityRoots operands
        if let some path := operands.findSome? (·.categoryPath?) then
          throw (.fieldFill (.categoryNotAllowed path))
        if operands.any (fun read => match read.operand with
            | .group _ | .starredGroup _ | .starredGroupPresence _ => true | _ => false) then
          throw (.dateRange .noGroupsAllowed)
        if operands.length < 2 && !operands.any (fun read => read.operand.isAlreadyMany) then
          throw (.dateRange .paramSizeInvalidFN)
      else
        let subject :: members := operands | throw .incoherentCore
        let fields := subject.operand.expansionDeclarations
        let first :: _ := fields | throw .incoherentCore
        let base (declarations : List FlatFieldDecl) : Except CorrelationElabError Unit := do
          if let some mismatch := declarations.find? (fun declaration =>
              !first.policy.kind.surfaceKind.sharesValueListBaseType declaration.policy.kind.surfaceKind) then
            throw (.membershipBaseType mismatch.path)
        let valueValidation (declarations : List FlatFieldDecl) : Except CorrelationElabError Unit := do
          if let some raw := declarations.find? (·.isRawString) then throw (.resolve (.rawFieldValueRead raw.path))
        checkHavingEntityRoots [subject]
        base fields
        if !(match subject.operand with | .field _ _ => true | _ => false) then
          throw (.dateRange .invalidParameterForDateRangeComparison)
        valueValidation fields
        checkHavingEntityDuplicates members
        checkHavingEntityRoots members
        let values := members.flatMap (·.operand.expansionDeclarations)
        base values
        checkHavingEntityDuplicates operands
        valueValidation values
      checkHavingOverlapDeclarations model (operands.map (·.operand.expansionDeclarations))
      let slots ← havingResolvedEntitySlots operands
      let slots := slots.map (·.map fun ref => ({ origin := ref.origin, field := ref.declaration.id } : HavingPresenceRef))
      let references := slots.flatMap (·.references)
      if !(references.all fun ref => (rangeFormat model ref).isSome) then throw .incoherentCore
      if !overlapProfilesAdmitted model slots then throw (.dateRange .dateWithAndWithoutYear)
      match scalar, slots with
      | none, _ => pure (.overlap none slots)
      | some _, .direct ref :: rest => pure (.overlap (some ref) rest)
      | _, _ => throw .incoherentCore

end A12Kernel
