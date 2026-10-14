import A12Kernel.Elaboration.PartialSemanticIndex
import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.FilledFieldStarCount

/-! # The field-fill operand list

The seven field-fill quantifiers and `NumberOfFilledFields` take an entity list: direct fields,
starred fields and groups, mixed ([`spec/02`](../../spec/02-logic-and-formal-errors.md) §A.4). The
count and quantifiers also support index-selected fields through their shared phase-aware lookup. Each
operand keeps the source that already owns its reading: a direct field reads its cell at the rule's
row, a starred field its in-capacity rows, and a group the checked group source's in-capacity
subtree. The list concatenates their validation observations, so the count's rule (an invalid cell
makes it unavailable) and the quantifiers' tally apply to the whole list exactly as to one operand.

Each operand also contributes its declared slots: a direct field one, a starred field the product of
the maxima its star reopens, a group its subtree's capacity. The declared-range quantifiers read the
list's missing tail from their sum. Filtered quantifiers select their missing slots and retain
operand order for polarity. Counts move against declared capacity, with shrinkability added only
when a filtered operand contributes filled content. Computation guards keep the list certificates for their own ordered scans. Category reads are refused here.

The unfiltered, materialized computation projection reads the same checked addresses with computation observations and places
one open-tail marker after each declaration. `FieldFillQuantifier.evalComputation_omittedRun` proves
that one marker represents any nonempty omitted run; moving it behind another declaration is not
valid, as the retained field-fill guard grid separates. This projection retains the legacy unfiltered
boundary; ordinary computation guards preserve the checked source through `CheckedComputationFieldFill`
and its ordered scans, including filtered operands.
-/

namespace A12Kernel

/-- One operand of a field-fill list, by the source that owns its reading. -/
inductive CheckedFieldFillOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
  | indexed (source : CheckedSemanticIndexSource model)
  | keyed (source : CheckedKeyedEntityExtent model)
  | star (source : CheckedFilledFieldStarSource model)
  | group (source : CheckedFilledFieldCountGroupSource model)

/-- A checked, nonempty field-fill list whose list-level gates passed. -/
structure CheckedFieldFillList (model : FlatModel) where
  operands : List (CheckedFieldFillOperand model)

inductive FieldFillListElabError where
  | shape (error : FieldEntityShapeElabError)
  | group (error : FilledFieldCountGroupElabError)
  | having (error : CorrelationElabError)
  /-- An operand outside the selected consumer, a category read, or the rule group. -/
  | unsupportedOperand
  deriving Repr, DecidableEq

/-- Keep consumer identity through admission so indexed or filtered support for one carrier
cannot silently widen another carrier's contract (spec/02 and spec/07). -/
inductive FieldFillListConsumer where
  | quantifier
  | count
  deriving DecidableEq

namespace CheckedFieldFillOperand

def declarations : CheckedFieldFillOperand model → List FlatFieldDecl
  | .field declaration => [declaration]
  | .indexed source => [source.targetDeclaration]
  | .keyed source => source.declarations
  | .star source => [source.source.declaration]
  | .group source => source.declarations

/-- The group the operand is written over: a field's own group, or the group operand's. -/
def groupPath : CheckedFieldFillOperand model → GroupPath
  | .field declaration => declaration.groupPath
  | .indexed source => source.targetDeclaration.groupPath
  | .keyed source => source.groupPath
  | .star source => source.source.declaration.groupPath
  | .group source => source.source.groupPath

/-- Each unstarred prefix and captured reference contributes its own scope, preserving parallel
scope conflicts for the ordinary iteration merger. -/
def bindingScopes : CheckedFieldFillOperand model → List (List RepeatableLevel)
  | .field declaration => [declaration.repeatableScope]
  | .indexed source => source.bindingScopes
  | .keyed source => source.bindingScopes
  | .star source => source.source.bindingScope ::
      (source.filter.toList.flatMap fun filter =>
        (CorrelatedHaving.outerIterationScopes model filter.condition).filterMap id)
  | .group source => [source.source.bindingScope]

def bindingScope (operand : CheckedFieldFillOperand model) : List RepeatableLevel :=
  operand.bindingScopes.flatten.eraseDups

def hasHaving : CheckedFieldFillOperand model → Bool
  | .star source => source.hasHaving
  | _ => false

def referencesField (operand : CheckedFieldFillOperand model) (field : FieldId)
    (havingReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  operand.declarations.any (·.id == field) || match operand with
    | .keyed source => source.referencesField field
    | .indexed source => source.indexDeclaration.id == field ||
        match source.key with
        | .field declaration => declaration.id == field
        | .literal _ _ => false
    | .star source => source.filter.any fun filter => havingReads filter.condition field
    | _ => false


private def keyedValidationSelection (source : CheckedKeyedEntityExtent model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (CellObservation Env) :=
  source.selectWith .validation (document.resolveSemanticIndexColumnWith document.read) outer
    (document.computationContextAt outer).read (document.computationContextAt outer).storedText

def observations (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .requireSmall) :
    CheckedFieldFillOperand model → Except CheckedAddressingError (List CellObservation)
  | .indexed source => List.singleton <$> source.observeDocument document outer .validation
  | .keyed source => do
      let selected ← keyedValidationSelection source document outer
      source.observationsWith .validation document.source.toDocument selected document.computationFillContext.read
  | .field declaration => do
      -- EntityUtil.resolveIterations retains the bound singleton; RuntimeController's
      -- isWertAngegeben observes its formal state rather than treating it as a reopened extent.
      let addressed ← document.fullValidationAddressedCell outer declaration.id
      pure [observeCell .validation addressed.cell]
  | .star source => do
      let core ← source.source.resolveCheckedValidationEntityOperandCore (world := world) (traversalMode := traversalMode) document outer
        (source.filter.map (·.condition))
      pure (core.inCapacityAddressedCells.map fun addressed => observeCell .validation addressed.cell)
  | .group source => source.observations document outer

def fillCapacity? : CheckedFieldFillOperand model → Option Nat
  | .indexed _ => some 1
  | .keyed source => source.capacity?
  | .field declaration => model.declarationSlots? declaration.repeatableScope.length declaration
  | .star source => if source.hasHaving then none else
      model.declarationSlots? source.source.path.firstStar source.source.declaration
  | .group source => source.fillCapacity?

/-- The declared slots this operand contributes at validation. A keyed operand whose selection is
undecided by a duplicated key reads as its one unknown observation: no declared extent
is left to be missing, so `NotAllFieldsFilled` stays silent over it (spec/08 §4.1, `q04` and `w02` of the
[semantic-index capture](../../docs/sources/model-structure-and-declaration-probes.md#src-semantic-index-reads)). -/
def validationFillCapacity? (document : CheckedDocument model) (outer : Env) :
    CheckedFieldFillOperand model → Except CheckedAddressingError (Option Nat)
  | .keyed source => do
      match ← keyedValidationSelection source document outer with
      | .unknown _ | .poison _ => pure (some 1)
      | .empty | .value _ => pure source.capacity?
  | operand => pure operand.fillCapacity?

def countCapacity? : CheckedFieldFillOperand model → Option Nat
  | .group source => source.countCapacity?
  | .star source => model.declarationSlots? source.source.path.firstStar source.source.declaration
  | operand => operand.fillCapacity?

/-- Computation observes each addressed cell in order and records an open declared tail once.
The seven scans cannot distinguish adjacent omitted slots (`evalComputation_omittedRun`). -/
private def computationCoreSlots (core : ResolvedCheckedEntityOperandCore) :
    List ComputationFillSlot :=
  (core.inCapacityAddressedCells.map fun addressed =>
    (observeCell .computation addressed.cell).asComputationFillSlot) ++
      if core.hasUninstantiatedTail then [.uninstantiated] else []

/-- Preserve each field's missing tail before visiting the next declaration, as separated by
[the guard grid](../../docs/sources/computation-scheduling-probes.md#src-field-fill-computation-guards);
the validation tally's total tail cannot preserve this order. -/
def computationSlots (document : CheckedDocument model) (outer : Env) :
    CheckedFieldFillOperand model → Except CheckedAddressingError (List ComputationFillSlot)
  | .indexed source => do
      pure [(← source.observeDocument document outer .computation).asComputationFillSlot]
  | .keyed source => do
      let selected ← source.selectWith .computation (document.resolveSemanticIndexColumnWith document.read) outer
        (document.computationContextAt outer).read (document.computationContextAt outer).storedText
      source.computationSlotsWith document.source.toDocument selected document.computationFillContext.read
  | .field declaration =>
      computationCoreSlots <$> document.resolveCheckedDirectEntityOperandCoreAt outer declaration.id
  | .star source => do
      if source.hasHaving then throw .filteredFieldFillComputation
      computationCoreSlots <$> source.source.resolveCheckedValidationEntityOperandCore document outer none
  | .group source => do
      let declarations ← source.declarations.mapM fun declaration =>
        computationCoreSlots <$> document.resolveCheckedGroupEntityOperandCore outer
          source.source.boundLevelCount [declaration]
      pure declarations.flatten

/-- Produce one operand range for the shared validation fold. A declared-range filter evaluates
the unvisited declared tail separately; subtracting selected cells from unfiltered capacity would
count dropped rows as omissions (the filtered field-fill grid, 2026-10-03). -/
def validationRange? (operand : CheckedFieldFillOperand model) (declared : Bool)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError (Option ValidationFillRange) := do
  let observations ← operand.observations (world := world) document outer
  let tally : ValidationFillTally := observations.foldl (fun total cell => total.combine cell.asValidationFillTally)
    { filled := 0, empty := 0, unknown := 0, uninstantiated := 0 }
  let missing? ← if !declared then pure (some 0) else match operand with
    | .star source => source.selectedMissingCount? (world := world) document outer
    | _ => pure ((← operand.validationFillCapacity? document outer).map (· - observations.length))
  pure (missing?.map fun missing =>
    { tally := { tally with uninstantiated := missing }, hasHaving := operand.hasHaving })

end CheckedFieldFillOperand

/-- Count call-local observations in order. Kernel 30.8.1's
`RuntimeController.anzahlAngegebenerEntities` stops at the first unavailable cell;
in particular a later addressing failure must not replace that result. -/
def countPartialFieldReads
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    List (Env × FieldId) → Except CheckedAddressingError PartialValidationFilledFieldCountResult
  | [] => pure (.evaluated (.value 0))
  | (environment, field) :: rest => do
      match ← read environment field with
      | none => pure .silentlyUnavailable
      | some cell =>
          match numberOfFilledFields [observeCell .validation cell] with
          | .unknown => pure (.evaluated .unknown)
          | .value count =>
              match ← countPartialFieldReads read rest with
              | .evaluated (.value remaining) => pure (.evaluated (.value (count + remaining)))
              | result => pure result

/-- Selected counts use the same complete-extent test as ordinary counts (spec/10 §5), then
reuse the ordered cell fold so unavailable keys and payloads cannot inspect the suffix. -/
private def countPartialSelectedFields
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialValidationFilledFieldCountResult := do
  match ← resolvePartialSelectedAddresses source document scope outer read
      (fun declaration bound reopened environment =>
        scope.coversAggregateExtent model declaration.path bound reopened environment) with
  | none => pure .nonRelevant
  | some (.unknown _) | some (.poison _) => pure (.evaluated .unknown)
  | some .empty => pure (.evaluated (.value 0))
  | some (.value (addresses, _)) =>
      countPartialFieldReads read (addresses.map fun (field, row) => (row, field.id))

private def CheckedFieldFillOperand.partialCount
    (operand : CheckedFieldFillOperand model) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option PartialValidationFilledFieldCountResult) := do
  let rows ← match operand with
    | .indexed source => return some (← countPartialSelectedFields (.inl source) document outer scope read)
    | .keyed source => return some (← countPartialSelectedFields (.inr source) document outer scope read)
    | .field declaration =>
        if !scope.coversAggregateExtent model declaration.path declaration.repeatableScope [] outer then
          return some .nonRelevant
        pure [(outer, declaration.id)]
    | .star source => do
        if source.hasHaving then return some .skippedHaving
        if !source.source.allRowsRelevant scope outer then return some .nonRelevant
        let resolved ← (source.source.path.resolveInCapacity document.source.toDocument outer)
          |>.mapError .addressing
        pure (resolved.environments.map (·, source.source.declaration.id))
    | .group source => do
        if !source.source.everyDeclarationCovers source.declarations
            (fun path bound reopened => scope.coversAggregateExtent model path bound reopened outer) then
          return some .nonRelevant
        let rows ← model.groupOperandRows document.source.toDocument outer
          source.source.boundLevelCount source.declarations (·.repeatableScope)
          |>.mapError .addressing
        pure (rows.map fun (declaration, environment) => (environment, declaration.id))
  some <$> countPartialFieldReads read rows

namespace CheckedFieldFillList

def declarations (list : CheckedFieldFillList model) : List FlatFieldDecl :=
  list.operands.flatMap (·.declarations)

def bindingScope (list : CheckedFieldFillList model) : List RepeatableLevel :=
  (list.operands.flatMap (·.bindingScope)).eraseDups

def rowBoundBool (list : CheckedFieldFillList model) (scope : List RepeatableLevel) : Bool :=
  list.operands.all fun operand => operand.bindingScopes.all (·.isPrefixOf scope)

def hasIndexed (list : CheckedFieldFillList model) : Bool :=
  list.operands.any fun operand => match operand with
    | .indexed _ | .keyed _ => true
    | _ => false

def hasHaving (list : CheckedFieldFillList model) : Bool :=
  list.operands.any (·.hasHaving)

/-- Structural support is separate from an admitted count's relevance or cell availability. -/
def supportsPartialCount (list : CheckedFieldFillList model) : Bool :=
  !list.hasHaving

/-- Partial counts preserve each operand's complete declared extent and read the call-local
preliminary view, including the selected extent's complete-coverage gate (spec/10 §5).
Filtered rules retain their rule-owned skip. A reached unavailable operand stops the authored suffix. -/
def evaluatePartialCount (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option PartialValidationFilledFieldCountResult) :=
  if list.hasHaving then pure (some .skippedHaving)
  else go list.operands
where
  go : List (CheckedFieldFillOperand model) →
      Except CheckedAddressingError (Option PartialValidationFilledFieldCountResult)
    | [] => pure (some (.evaluated (.value 0)))
    | operand :: rest => do
        match ← operand.partialCount document outer scope read with
        | some (.evaluated (.value count)) =>
            match ← go rest with
            | some (.evaluated (.value remaining)) =>
                pure (some (.evaluated (.value (count + remaining))))
            | result => pure result
        | result => pure result

def referencesField (list : CheckedFieldFillList model) (field : FieldId)
    (havingReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  list.operands.any (·.referencesField field havingReads)

def sum? (capacities : List (Option Nat)) : Option Nat :=
  capacities.foldl (init := some 0) fun total capacity => total.bind fun t => capacity.map (t + ·)

/-- The declared slots the declared-range quantifiers read, summed over the operands. -/
def fillCapacity? (list : CheckedFieldFillList model) : Option Nat :=
  sum? (list.operands.map (·.fillCapacity?))

/-- The declared slots the count's movement runs against, summed over the operands. -/
def countCapacity? (list : CheckedFieldFillList model) : Option Nat :=
  sum? (list.operands.map (·.countCapacity?))

def observations (list : CheckedFieldFillList model) (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError (List CellObservation) :=
  (·.flatten) <$> list.operands.mapM (·.observations (world := world) document outer)

/-- Resolve computation slots in authored operand and declaration order. -/
def computationSlots (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError (List ComputationFillSlot) :=
  (·.flatten) <$> list.operands.mapM (·.computationSlots document outer)

/-- Erase model certificates while retaining each declaration's identity, axes and bound depth
for the model-independent computation guard. -/
def computationSources (list : CheckedFieldFillList model) :
    Except FieldFillListElabError (List ComputationFillSource) := do
  let sources ← list.operands.mapM fun
    | .indexed _ | .keyed _ => throw .unsupportedOperand
    | .field declaration => pure [ComputationFillSource.direct declaration.id]
    | .star source => do
        if source.hasHaving then throw .unsupportedOperand
        pure [.expanded source.source.declaration.id source.source.path.axes source.source.path.firstStar]
    | .group source => source.declarations.mapM fun declaration => do
        if declaration.repeatableScope.isEmpty then return .direct declaration.id
        let some axes := model.repeatableAxesForScope? declaration.repeatableScope
          | throw .unsupportedOperand
        pure (.expanded declaration.id axes source.source.boundLevelCount)
  pure sources.flatten

/-- The extensional validation tally of the list's in-capacity extent.

`uninstantiated` is `0` in the visited stream; a reached virtual filter coordinate contributes an
empty observation (KF528). Declared-range quantifiers supply only the remaining missing tail; counting
a formally unknown cell as missing would turn the undecided all-full case into a false omission. -/
def validationFillTally (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env)
    (world : Option World := none) : Except CheckedAddressingError ValidationFillTally := do
  pure ((← list.observations (world := world) document outer).foldl
    (init := ({ filled := 0, empty := 0, unknown := 0, uninstantiated := 0 } : ValidationFillTally))
    fun tally observation => tally.combine observation.asValidationFillTally)

private def fillScanDecided (operator : FieldFillQuantifier) (ranges : List ValidationFillRange) : Bool :=
  let tally := ValidationFillRange.total ranges
  match operator with
  | .allFieldsFilled => 0 < tally.empty + tally.uninstantiated + tally.unknown
  | .noFieldFilled => 0 < tally.filled + tally.unknown
  | .atLeastOneFieldFilled => 0 < tally.filled
  | .moreThanOneFieldFilled => 1 < tally.filled
  | .notAllFieldsFilled => 0 < tally.empty + tally.uninstantiated
  | .notExactlyOneFieldFilled | .fieldsNotCollectivelyFilled => false

private def scanValidationFill (operator : FieldFillQuantifier)
    (document : CheckedDocument model) (outer : Env) (world : Option World)
    (operands : List (CheckedFieldFillOperand model)) (ranges : List ValidationFillRange) :
    Except CheckedAddressingError (Option ValidationFillOutcome) := do
  match operands with
  | [] => pure (some (operator.evalValidationRanges ranges.reverse))
  | operand :: rest =>
      let declared := operator == .allFieldsFilled || operator == .notAllFieldsFilled
      let done ranges := if fillScanDecided operator ranges then
        Sum.inr (operator.evalValidationRanges ranges.reverse) else Sum.inl ranges
      let ordinary (_ : Unit) : Except CheckedAddressingError
          (Option (ComputationHavingScanResult (List ValidationFillRange) ValidationFillOutcome)) := do
        let some range ← operand.validationRange? (world := world) declared document outer | return none
        pure (some (match done (range :: ranges) with
          | .inl next => .exhausted next
          | .inr result => .terminated result))
      let result? ← match operand with
        | .star source => match source.filter with
          | some filter => do
              let traversal? : Option FilterTraversal ← if declared then do
                pure ((← source.source.declaredEnvironments? document outer).map fun candidates => { candidates })
              else some <$> source.source.filterTraversal document outer (if operator == .atLeastOneFieldFilled then .sparse else .dense)
              let some traversal := traversal? | return none
              let initial : ValidationFillRange := {
                tally := { filled := 0, empty := 0, unknown := 0, uninstantiated := 0 }
                hasHaving := true }
              let result ← filter.condition.scanValidationResolving
                (document.resolvingCorrelationContextWithRead document.readDeclared world) outer
                (fun (current : ValidationFillRange) row => do
                  let cell ← document.addressedCellWithRead document.readDeclared row source.source.declaration.id
                  let next := { current with
                    tally := current.tally.combine (observeCell .validation cell.cell).asValidationFillTally }
                  pure (if fillScanDecided operator (next :: ranges) then
                    .inr (operator.evalValidationRanges (next :: ranges).reverse) else .inl next))
                traversal.candidates initial traversal.occupancy
              pure (some (match result with
                | .exhausted current => .exhausted (current :: ranges)
                | .terminated result => .terminated result
                | .poison cause => .poison cause))
          | none => ordinary ()
        | _ => ordinary ()
      let some result := result? | return none
      match result with
      | .exhausted next => scanValidationFill operator document outer world rest next
      | .terminated result => pure (some result)
      | .poison _ => pure none

private def evaluateFilteredFill (list : CheckedFieldFillList model) (operator : FieldFillQuantifier)
    (document : CheckedDocument model) (outer : Env) (world : Option World) :
    Except CheckedAddressingError (Option ValidationFillOutcome) := do
  let scan op := scanValidationFill op document outer world list.operands []
  match operator with
  | .notExactlyOneFieldFilled =>
      match ← scan .noFieldFilled with
      | none => pure none
      | some (.fired polarity) => pure (some (.fired polarity))
      | some .falseOrUnknown => scan .moreThanOneFieldFilled
  | .fieldsNotCollectivelyFilled =>
      match ← scan .atLeastOneFieldFilled with
      | none => pure none
      | some .falseOrUnknown => pure (some .falseOrUnknown)
      | some (.fired _) => scan .notAllFieldsFilled
  | operator => scan operator

/-- A field-fill quantifier over the list's in-capacity extent and declared tail.

This is not a projection of the count: the count is unavailable as soon as one cell is formally
invalid, while `AtLeastOneFieldFilled` still fires on a filled sibling, so the two disagree on a
document holding both, deliberately. `none` when a declared-range quantifier needs a maximum the
model does not retain. -/
def evaluateFill? (list : CheckedFieldFillList model) (operator : FieldFillQuantifier)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError (Option ValidationFillOutcome) := do
  if list.hasHaving then
    evaluateFilteredFill list operator document outer world
  else do
    let tally ← list.validationFillTally (world := world) document outer
    match operator with
    | .allFieldsFilled | .notAllFieldsFilled | .fieldsNotCollectivelyFilled =>
        let capacity? := sum? (← list.operands.mapM (·.validationFillCapacity? document outer))
        pure (capacity?.map fun capacity =>
          operator.evalValidation { tally with
            uninstantiated := capacity - (tally.filled + tally.empty + tally.unknown) })
    | .noFieldFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled
        | .notExactlyOneFieldFilled => pure (some (operator.evalValidation tally))

/-- Count movement retains whether filled content came from a filtered operand, rather than
whether a filter was merely authored (`RuntimeController.anzahlAngegebenerEntities`, kernel 30.8.1). -/
def evaluateCountOperand? (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env)
    (world : Option World := none) : Except CheckedAddressingError (Option NumericOperand) := do
  let contributions ← list.operands.mapM fun operand => do
    pure (operand.hasHaving, numberOfFilledFields (← operand.observations (world := world) (traversalMode := .sparse) document outer))
  let available := contributions.foldlM (m := Option) (init := ((0 : Nat), false)) fun (total, filtered) (having, count) =>
    match count with
    | .unknown => none
    | .value amount => some (total + amount, filtered || (having && amount > 0))
  pure (available.bind fun (total, filtered) =>
    if filtered then some (.value total .both)
    else list.countCapacity?.bind fun capacity =>
      ((FilledFieldCount.value total).availableWithFillability? capacity).map fun available =>
        .value available.1 available.2)

end CheckedFieldFillList

/-- A group source as the one-operand list, so a group operand is evaluated by the list's code. -/
def CheckedFilledFieldCountGroupSource.asFieldFillList
    (checked : CheckedFilledFieldCountGroupSource model) : CheckedFieldFillList model :=
  { operands := [.group checked] }

/-- Elaborate a field-fill list at the rule group. The shared entity-list shape runs the list gates,
duplicates, containment and arity, with the rule's iteration binding its unstarred levels; each
group operand is then elaborated by the group source, which owns its rule-bound reference. -/
def elaborateFieldFillList (model : FlatModel) (rowGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) (bindingGroup : GroupPath := rowGroup)
    (consumer : FieldFillListConsumer := .count) :
    Except FieldFillListElabError (CheckedFieldFillList model) := do
  -- Keep the sole-group source's existing admission and error projection; mixed lists run the
  -- shared duplicate and overlap gates with the same rule-bound resolution.
  match authored with
  | { first := .group (.path group), rest := [] } =>
      return { operands := [.group (← (elaborateFilledFieldCountFixedGroupValidationSource model
        rowGroup { group } bindingGroup).mapError .group)] }
  | { first := .starredGroup group, rest := [] } =>
      return { operands := [.group (← (elaborateFilledFieldCountStarredGroupValidationSource model
        rowGroup { group } bindingGroup).mapError .group)] }
  | _ => pure ()
  let shape ← (elaborateFieldEntityShapeIn model rowGroup (model.repeatableScopeForGroupPath bindingGroup)
    authored .manyRequired none bindingGroup
    (categoryGate := if consumer == .quantifier then .behindRootGate else .aheadOfRepeat)
    (groupReadScope := .ruleBound)).mapError .shape
  let operands ← ((authored.first :: authored.rest).zip shape.operands).mapM fun
    | (_, .indexed source .stored) => pure (.indexed source)
    | (_, .keyed source .stored) => pure (.keyed source)
    | (_, .field declaration .stored) => pure (.field declaration)
    | (_, .star source .stored) => pure (.star (.plain rowGroup source))
    | (_, .starHaving source having .stored) => do
        pure (.star (← (CheckedFilledFieldStarSource.withHaving model rowGroup bindingGroup
          source having).mapError .having))
    | (.group (.path _), .group reference) =>
        (CheckedFieldFillOperand.group <$>
          CheckedFilledFieldCountGroupSource.ofResolved model (.fixed reference)).mapError .group
    | (.starredGroup group, _) =>
        (CheckedFieldFillOperand.group <$>
          elaborateFilledFieldCountStarredGroupValidationSource model rowGroup { group } bindingGroup).mapError .group
    | _ => throw .unsupportedOperand
  pure { operands }

/-- Computation list admission uses the target scope, through the shared entity-list binding
and multiplicity gates (`spec/09` §5). Resolved group expansions retain that binding instead of
re-entering validation's rule-group resolver. -/
def elaborateComputationFieldFillList (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (authored : SurfaceFieldEntitySource)
    (_consumer : FieldFillListConsumer := .quantifier) :
    Except FieldFillListElabError (CheckedFieldFillList model) := do
  let shape ← (elaborateFieldEntityShapeIn model declaringGroup
    (model.repeatableScopeForGroupPath targetGroup) authored .manyRequired
    (some targetGroup) targetGroup (categoryGate := .behindRootGate)).mapError .shape
  let group (source : CheckedEntityGroupSource model) :=
    (CheckedFieldFillOperand.group <$>
      CheckedFilledFieldCountGroupSource.ofResolved model source).mapError FieldFillListElabError.group
  let operands ← shape.operands.mapM fun
    | .field declaration .stored => pure (.field declaration)
    | .star source .stored => pure (.star (.plain declaringGroup source))
    | .group reference => group (.fixed reference)
    | .starredGroup source => group (.starred source)
    | .starredGroupPresence source => group (.starredPresence source)
    | .starHaving source having .stored => do
        pure (.star (← (CheckedFilledFieldStarSource.withHaving model declaringGroup targetGroup
          source having targetGroup).mapError .having))
    | .indexed source .stored => pure (.indexed source)
    | .keyed source .stored => pure (.keyed source)
    | .field _ (.projected _) | .indexed _ (.projected _) | .keyed _ (.projected _) | .star _ (.projected _)
      | .starHaving _ _ (.projected _) =>
        throw .unsupportedOperand
  pure { operands }

end A12Kernel
