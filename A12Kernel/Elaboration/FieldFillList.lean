import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.FilledFieldStarCount

/-! # The field-fill operand list

The seven field-fill quantifiers and `NumberOfFilledFields` take an entity list: direct fields,
starred fields and groups, mixed ([`spec/02`](../../spec/02-logic-and-formal-errors.md) §A.4). The
count additionally admits index-selected fields; indexed quantifiers remain explicitly unsupported. Each
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
  | .star source => [source.source.declaration]
  | .group source => source.declarations

/-- The group the operand is written over: a field's own group, or the group operand's. -/
def groupPath : CheckedFieldFillOperand model → GroupPath
  | .field declaration => declaration.groupPath
  | .indexed source => source.targetDeclaration.groupPath
  | .star source => source.source.declaration.groupPath
  | .group source => source.source.groupPath

/-- Each unstarred prefix and captured reference contributes its own scope, preserving parallel
scope conflicts for the ordinary iteration merger. -/
def bindingScopes : CheckedFieldFillOperand model → List (List RepeatableLevel)
  | .field declaration => [declaration.repeatableScope]
  | .indexed _ => [[]]
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
    | .indexed source => source.indexDeclaration.id == field ||
        match source.key with
        | .field declaration => declaration.id == field
        | .literal _ _ => false
    | .star source => source.filter.any fun filter => havingReads filter.condition field
    | _ => false

private def indexedObservation (document : CheckedDocument model) (outer : Env)
    (source : CheckedSemanticIndexSource model) (phase : Phase) :
    Except CheckedAddressingError CellObservation := do
  let preliminary ← (document.applySelectedFullIndexPreliminary [source.indexDeclaration.id])
    |>.mapError .indexPreliminary
  let column ← source.resolvePreliminaryColumn preliminary outer |>.mapError .semanticIndex
  let key ← source.observeCurrentKey phase
    (document.computationCellAt preliminary.readAuthoredValidation [])
    (document.storedTextIn []) |>.mapError .semanticIndex
  pure (column.lookupObservationForIndex phase source.numericIndex key)

def observations (document : CheckedDocument model) (outer : Env) :
    CheckedFieldFillOperand model → Except CheckedAddressingError (List CellObservation)
  | .indexed source => List.singleton <$> indexedObservation document outer source .validation
  | .field declaration => do
      let core ← document.resolveCheckedDirectEntityOperandCoreAt outer declaration.id
      pure (core.inCapacityAddressedCells.map fun addressed => observeCell .validation addressed.cell)
  | .star source => do
      let core ← source.source.resolveCheckedValidationEntityOperandCore document outer
        (source.filter.map (·.condition))
      pure (core.inCapacityAddressedCells.map fun addressed => observeCell .validation addressed.cell)
  | .group source => source.observations document outer

def fillCapacity? : CheckedFieldFillOperand model → Option Nat
  | .indexed _ => some 1
  | .field declaration => model.declarationSlots? declaration.repeatableScope.length declaration
  | .star source => if source.hasHaving then none else
      model.declarationSlots? source.source.path.firstStar source.source.declaration
  | .group source => source.fillCapacity?

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
      pure [(← indexedObservation document outer source .computation).asComputationFillSlot]
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
missing slots separately; subtracting selected instantiated cells from unfiltered capacity would
count dropped rows as omissions (the filtered field-fill grid, 2026-10-03). -/
def validationRange? (operand : CheckedFieldFillOperand model) (declared : Bool)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option ValidationFillRange) := do
  let observations ← operand.observations document outer
  let tally : ValidationFillTally := observations.foldl (fun total cell => total.combine cell.asValidationFillTally)
    { filled := 0, empty := 0, unknown := 0, uninstantiated := 0 }
  let missing? ← if !declared then pure (some 0) else match operand with
    | .star source => source.selectedMissingCount? document outer
    | _ => pure (operand.fillCapacity?.map (· - observations.length))
  pure (missing?.map fun missing =>
    { tally := { tally with uninstantiated := missing }, hasHaving := operand.hasHaving })

end CheckedFieldFillOperand

namespace CheckedFieldFillList

def declarations (list : CheckedFieldFillList model) : List FlatFieldDecl :=
  list.operands.flatMap (·.declarations)

def bindingScope (list : CheckedFieldFillList model) : List RepeatableLevel :=
  (list.operands.flatMap (·.bindingScope)).eraseDups

def rowBoundBool (list : CheckedFieldFillList model) (scope : List RepeatableLevel) : Bool :=
  list.operands.all fun operand => operand.bindingScopes.all (·.isPrefixOf scope)

def hasIndexed (list : CheckedFieldFillList model) : Bool :=
  list.operands.any fun operand => match operand with
    | .indexed _ => true
    | _ => false

def hasHaving (list : CheckedFieldFillList model) : Bool :=
  list.operands.any (·.hasHaving)

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

def observations (list : CheckedFieldFillList model) (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (List CellObservation) :=
  (·.flatten) <$> list.operands.mapM (·.observations document outer)

/-- Resolve computation slots in authored operand and declaration order. -/
def computationSlots (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError (List ComputationFillSlot) :=
  (·.flatten) <$> list.operands.mapM (·.computationSlots document outer)

/-- Erase model certificates while retaining each declaration's identity, axes and bound depth
for the model-independent computation guard. -/
def computationSources (list : CheckedFieldFillList model) :
    Except FieldFillListElabError (List ComputationFillSource) := do
  let sources ← list.operands.mapM fun
    | .indexed _ => throw .unsupportedOperand
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

`uninstantiated` is `0`, because every operand enumerates instantiated rows only. The declared-range
quantifiers supply the missing tail separately; counting a formally unknown instantiated cell as
missing would turn the undecided all-full case into a false omission. -/
def validationFillTally (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError ValidationFillTally := do
  pure ((← list.observations document outer).foldl
    (init := ({ filled := 0, empty := 0, unknown := 0, uninstantiated := 0 } : ValidationFillTally))
    fun tally observation => tally.combine observation.asValidationFillTally)

/-- A field-fill quantifier over the list's in-capacity extent and declared tail.

This is not a projection of the count: the count is unavailable as soon as one cell is formally
invalid, while `AtLeastOneFieldFilled` still fires on a filled sibling, so the two disagree on a
document holding both, deliberately. `none` when a declared-range quantifier needs a maximum the
model does not retain. -/
def evaluateFill? (list : CheckedFieldFillList model) (operator : FieldFillQuantifier)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option ValidationFillOutcome) := do
  if list.hasIndexed then throw .unsupportedIndexedFillQuantifier
  if list.hasHaving then
    let declared := match operator with
      | .allFieldsFilled | .notAllFieldsFilled | .fieldsNotCollectivelyFilled => true
      | _ => false
    let ranges ← list.operands.mapM (·.validationRange? declared document outer)
    pure ((ranges.mapM id).map operator.evalValidationRanges)
  else do
    let tally ← list.validationFillTally document outer
    match operator with
    | .allFieldsFilled | .notAllFieldsFilled | .fieldsNotCollectivelyFilled =>
        pure (list.fillCapacity?.map fun capacity =>
          operator.evalValidation { tally with
            uninstantiated := capacity - (tally.filled + tally.empty + tally.unknown) })
    | .noFieldFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled
        | .notExactlyOneFieldFilled => pure (some (operator.evalValidation tally))

/-- Count movement retains whether filled content came from a filtered operand, rather than
whether a filter was merely authored (`RuntimeController.anzahlAngegebenerEntities`, kernel 30.8.1). -/
def evaluateCountOperand? (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError (Option NumericOperand) := do
  let contributions ← list.operands.mapM fun operand => do
    pure (operand.hasHaving, numberOfFilledFields (← operand.observations document outer))
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
    (categoryGate := if consumer == .quantifier then .behindRootGate else .absent)
    (groupReadScope := .ruleBound)).mapError .shape
  let operands ← ((authored.first :: authored.rest).zip shape.operands).mapM fun
    | (_, .indexed source) =>
        if consumer == .count then pure (.indexed source) else throw .unsupportedOperand
    | (_, .field declaration .stored) => pure (.field declaration)
    | (_, .star source) => pure (.star (.plain rowGroup source))
    | (_, .starHaving source having) => do
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
    (consumer : FieldFillListConsumer := .quantifier) :
    Except FieldFillListElabError (CheckedFieldFillList model) := do
  let shape ← (elaborateFieldEntityShapeIn model declaringGroup
    (model.repeatableScopeForGroupPath targetGroup) authored .manyRequired
    (some targetGroup) targetGroup (categoryGate := .behindRootGate)).mapError .shape
  let group (source : CheckedEntityGroupSource model) :=
    (CheckedFieldFillOperand.group <$>
      CheckedFilledFieldCountGroupSource.ofResolved model source).mapError FieldFillListElabError.group
  let operands ← shape.operands.mapM fun
    | .field declaration .stored => pure (.field declaration)
    | .star source => pure (.star (.plain declaringGroup source))
    | .group reference => group (.fixed reference)
    | .starredGroup source => group (.starred source)
    | .starredGroupPresence source => group (.starredPresence source)
    | .starHaving source having => do
        pure (.star (← (CheckedFilledFieldStarSource.withHaving model declaringGroup targetGroup
          source having targetGroup).mapError .having))
    | .indexed source =>
        if consumer == .count then pure (.indexed source) else throw .unsupportedOperand
    | .field _ (.projected _) => throw .unsupportedOperand
  pure { operands }

end A12Kernel
