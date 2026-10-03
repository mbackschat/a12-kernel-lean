import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Elaboration.FilledFieldGroupCount
import A12Kernel.Elaboration.FilledFieldStarCount

/-! # The field-fill operand list

The seven field-fill quantifiers and `NumberOfFilledFields` take an entity list: direct fields,
starred fields and groups, mixed ([`spec/02`](../../spec/02-logic-and-formal-errors.md) §A.4). Each
operand keeps the source that already owns its reading: a direct field reads its cell at the rule's
row, a starred field its in-capacity rows, and a group the checked group source's in-capacity
subtree. The list concatenates their validation observations, so the count's rule (an invalid cell
makes it unavailable) and the quantifiers' tally apply to the whole list exactly as to one operand.

Each operand also contributes its declared slots: a direct field one, a starred field the product of
the maxima its star reopens, a group its subtree's capacity. The declared-range quantifiers read the
list's missing tail from their sum, and the count's movement runs against it. A filtered operand and
a category read are refused here.

The computation projection reads the same checked addresses with computation observations and places
one open-tail marker after each declaration. `FieldFillQuantifier.evalComputation_omittedRun` proves
that one marker represents any nonempty omitted run; moving it behind another declaration is not
valid, as the retained field-fill guard grid separates. Guard authoring and scheduling are consumers
of this projection, not responsibilities of the list.
-/

namespace A12Kernel

/-- One operand of a field-fill list, by the source that owns its reading. -/
inductive CheckedFieldFillOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
  | star (source : CheckedStarFieldPath model)
  | group (source : CheckedFilledFieldCountGroupSource model)

/-- A checked, nonempty field-fill list whose list-level gates passed. -/
structure CheckedFieldFillList (model : FlatModel) where
  operands : List (CheckedFieldFillOperand model)

inductive FieldFillListElabError where
  | shape (error : FieldEntityShapeElabError)
  | group (error : FilledFieldCountGroupElabError)
  /-- A filtered operand, a category read, or the rule group as an operand. -/
  | unsupportedOperand
  deriving Repr, DecidableEq

namespace CheckedFieldFillOperand

def declarations : CheckedFieldFillOperand model → List FlatFieldDecl
  | .field declaration => [declaration]
  | .star source => [source.declaration]
  | .group source => source.declarations

/-- The group the operand is written over: a field's own group, or the group operand's. -/
def groupPath : CheckedFieldFillOperand model → GroupPath
  | .field declaration => declaration.groupPath
  | .star source => source.declaration.groupPath
  | .group source => source.source.groupPath

/-- The repeatable levels the reading rule's row must bind. -/
def bindingScope : CheckedFieldFillOperand model → List RepeatableLevel
  | .field declaration => declaration.repeatableScope
  | .star source => source.bindingScope
  | .group source => source.source.bindingScope

def observations (document : CheckedDocument model) (outer : Env) :
    CheckedFieldFillOperand model → Except CheckedAddressingError (List CellObservation)
  | .field declaration => do
      let core ← document.resolveCheckedDirectEntityOperandCoreAt outer declaration.id
      pure (core.inCapacityAddressedCells.map fun addressed => observeCell .validation addressed.cell)
  | .star source => do
      let core ← source.resolveCheckedValidationEntityOperandCore document outer none
      pure (core.inCapacityAddressedCells.map fun addressed => observeCell .validation addressed.cell)
  | .group source => source.observations document outer

def fillCapacity? : CheckedFieldFillOperand model → Option Nat
  | .field declaration => model.declarationSlots? declaration.repeatableScope.length declaration
  | .star source => model.declarationSlots? source.path.firstStar source.declaration
  | .group source => source.fillCapacity?

def countCapacity? : CheckedFieldFillOperand model → Option Nat
  | .group source => source.countCapacity?
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
  | .field declaration =>
      computationCoreSlots <$> document.resolveCheckedDirectEntityOperandCoreAt outer declaration.id
  | .star source =>
      computationCoreSlots <$> source.resolveCheckedValidationEntityOperandCore document outer none
  | .group source => do
      let declarations ← source.declarations.mapM fun declaration =>
        computationCoreSlots <$> document.resolveCheckedGroupEntityOperandCore outer
          source.source.boundLevelCount [declaration]
      pure declarations.flatten

end CheckedFieldFillOperand

namespace CheckedFieldFillList

def declarations (list : CheckedFieldFillList model) : List FlatFieldDecl :=
  list.operands.flatMap (·.declarations)

def bindingScope (list : CheckedFieldFillList model) : List RepeatableLevel :=
  (list.operands.flatMap (·.bindingScope)).eraseDups

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
    | .field declaration => pure [ComputationFillSource.direct declaration.id]
    | .star source => pure [.expanded source.declaration.id source.path.axes source.path.firstStar]
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
  let tally ← list.validationFillTally document outer
  match operator with
  | .allFieldsFilled | .notAllFieldsFilled | .fieldsNotCollectivelyFilled =>
      pure (list.fillCapacity?.map fun capacity =>
        operator.evalValidation { tally with
          uninstantiated := capacity - (tally.filled + tally.empty + tally.unknown) })
  | .noFieldFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled
      | .notExactlyOneFieldFilled => pure (some (operator.evalValidation tally))

/-- `NumberOfFilledFields` over the list, with its movement against the list's declared slots. -/
def evaluateCountOperand? (list : CheckedFieldFillList model) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError (Option NumericOperand) := do
  let count := numberOfFilledFields (← list.observations document outer)
  pure (list.countCapacity?.bind fun capacity =>
    (count.availableWithFillability? capacity).map fun available => .value available.1 available.2)

end CheckedFieldFillList

/-- A group source as the one-operand list, so a group operand is evaluated by the list's code. -/
def CheckedFilledFieldCountGroupSource.asFieldFillList
    (checked : CheckedFilledFieldCountGroupSource model) : CheckedFieldFillList model :=
  { operands := [.group checked] }

/-- Elaborate a field-fill list at the rule group. The shared entity-list shape runs the list gates,
duplicates, containment and arity, with the rule's iteration binding its unstarred levels; each
group operand is then elaborated by the group source, which owns its rule-bound reference. -/
def elaborateFieldFillList (model : FlatModel) (rowGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) :
    Except FieldFillListElabError (CheckedFieldFillList model) := do
  -- A sole group keeps the group source's rule-bound reference, which the shared shape's scalar
  -- group resolution would refuse below a bound repeatable ancestor.
  match authored with
  | { first := .group (.path group), rest := [] } =>
      return { operands := [.group (← (elaborateFilledFieldCountFixedGroupValidationSource model
        rowGroup { group }).mapError .group)] }
  | { first := .starredGroup group, rest := [] } =>
      return { operands := [.group (← (elaborateFilledFieldCountStarredGroupValidationSource model
        rowGroup { group }).mapError .group)] }
  | _ => pure ()
  let shape ← (elaborateFieldEntityShapeIn model rowGroup (model.repeatableScopeForGroupPath rowGroup)
    authored .manyRequired none rowGroup).mapError .shape
  let operands ← ((authored.first :: authored.rest).zip shape.operands).mapM fun
    | (_, .field declaration .stored) => pure (.field declaration)
    | (_, .star source) => pure (.star source)
    | (.group (.path group), .group _) =>
        (CheckedFieldFillOperand.group <$>
          elaborateFilledFieldCountFixedGroupValidationSource model rowGroup { group }).mapError .group
    | (.starredGroup group, _) =>
        (CheckedFieldFillOperand.group <$>
          elaborateFilledFieldCountStarredGroupValidationSource model rowGroup { group }).mapError .group
    | _ => throw .unsupportedOperand
  pure { operands }

/-- Computation list admission uses the target scope, through the shared entity-list binding
and multiplicity gates (`spec/09` §5). Resolved group expansions retain that binding instead of
re-entering validation's rule-group resolver. -/
def elaborateComputationFieldFillList (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except FieldFillListElabError (CheckedFieldFillList model) := do
  let shape ← (elaborateFieldEntityShapeIn model declaringGroup
    (model.repeatableScopeForGroupPath targetGroup) authored .manyRequired
    (some targetGroup) targetGroup).mapError .shape
  let group (source : CheckedEntityGroupSource model) :=
    (CheckedFieldFillOperand.group <$>
      CheckedFilledFieldCountGroupSource.ofResolved model source).mapError FieldFillListElabError.group
  let operands ← shape.operands.mapM fun
    | .field declaration .stored => pure (.field declaration)
    | .star source => pure (.star source)
    | .group reference => group (.fixed reference)
    | .starredGroup source => group (.starred source)
    | .starredGroupPresence source => group (.starredPresence source)
    | .field _ (.projected _) | .starHaving _ _ => throw .unsupportedOperand
  pure { operands }

end A12Kernel
