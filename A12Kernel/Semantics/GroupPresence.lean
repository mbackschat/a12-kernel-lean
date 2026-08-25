import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.NumericFillability
import A12Kernel.Semantics.ValidationFillQuantifier

/-! # Resolved group presence in both evaluation arms

This capsule begins after model paths, concrete group instances, descendant scope, and
partial-validation coverage have been resolved. It derives one group's validation-stage
product state from checked descendant cells plus separately resolved repeat-row content
and structural errors, and it owns the separate computation-arm presence projection that
reads the same descendant cells with the opposite answer on formal invalidity. It does not
traverse `Document` or infer group relevance.
-/

namespace A12Kernel

/-- How much of one concrete group instance is visible to the validation call. -/
inductive GroupRelevance where
  | noneRelevant
  | partlyRelevant
  | fullyRelevant
  deriving Repr, DecidableEq

/-- The independent dimensions consumed by every validation group-presence operator. -/
structure GroupPresenceState where
  content : Bool
  erroneous : Bool
  relevance : GroupRelevance
  deriving Repr, DecidableEq

/-- A resolved group slice. `hasInstantiatedRow` includes the concrete group row itself
    when repeatable and any instantiated repeatable descendant row that supplies content
    to an ancestor. `structuralError` includes over-limit row diagnostics. -/
structure ResolvedGroupPresenceInput where
  descendantCells : List CheckedCell
  hasInstantiatedRow : Bool
  structuralError : Bool
  /-- A call-local unavailable descendant may make the group erroneous without manufacturing a formal finding. -/
  silentError : Bool := false
  relevance : GroupRelevance
  deriving Repr, DecidableEq

/-- Only duplicate-index marking preserves a previously admitted scalar value. Other
    findings reject that scalar as a source of group content. Row content is independent. -/
def FormalCause.preservesGroupAdmission : FormalCause → Bool
  | .duplicateIndex => true
  | _ => false

def CheckedCell.admitsGroupContent (cell : CheckedCell) : Bool :=
  cell.parsed.isSome && cell.findings.all FormalCause.preservesGroupAdmission

def CheckedCell.hasGroupError (cell : CheckedCell) : Bool :=
  !cell.findings.isEmpty

/-- Fold already checked descendants and structural row facts into the product state. -/
def ResolvedGroupPresenceInput.derive (input : ResolvedGroupPresenceInput) : GroupPresenceState :=
  { content := input.hasInstantiatedRow || input.descendantCells.any CheckedCell.admitsGroupContent
    erroneous := input.structuralError || input.silentError ||
      input.descendantCells.any CheckedCell.hasGroupError
    relevance := input.relevance }

def GroupPresenceState.definitelyFilled (state : GroupPresenceState) : Bool :=
  !(state.relevance == .noneRelevant) && state.content

def GroupPresenceState.definitelyEmpty (state : GroupPresenceState) : Bool :=
  state.relevance == .fullyRelevant && !state.content && !state.erroneous

/-- `GroupFilled`: any visible admitted content decides positively; visible absence is
    false even when an independent formal error prevents proving `GroupNotFilled`. -/
def GroupPresenceState.groupFilled (state : GroupPresenceState) : Verdict :=
  if state.relevance == .noneRelevant then .unknown
  else if state.content then .fired .value
  else .notFired

/-- `GroupNotFilled`: absence is positive only under full, clean coverage. -/
def GroupPresenceState.groupNotFilled (state : GroupPresenceState) : Verdict :=
  if state.erroneous || state.relevance == .noneRelevant then .unknown
  else if state.content then .notFired
  else if state.relevance == .fullyRelevant then .fired .omission
  else .unknown

/-- The two scalar group-presence predicates share one checked-condition leaf family. -/
inductive GroupPresenceOperator where
  | filled
  | notFilled
  deriving Repr, DecidableEq

def GroupPresenceOperator.canFireOnEmpty : GroupPresenceOperator → Bool
  | .filled => false
  | .notFilled => true

def GroupPresenceOperator.eval (operator : GroupPresenceOperator)
    (state : GroupPresenceState) : Verdict :=
  match operator with
  | .filled => state.groupFilled
  | .notFilled => state.groupNotFilled

/-- Parent-filled requiredness uses the same positive admitted-content projection. -/
def GroupPresenceState.activatesRelativeRequiredness (state : GroupPresenceState) : Bool :=
  state.definitelyFilled

/-- The five group-list predicates admitted by the resolved validation capsule. -/
inductive GroupFillQuantifier where
  | allGroupsFilled
  | noGroupFilled
  | atLeastOneGroupFilled
  | notAllGroupsFilled
  | groupsNotCollectivelyFilled
  deriving Repr, DecidableEq

def GroupFillQuantifier.requiresMultipleOperands : GroupFillQuantifier → Bool
  | .allGroupsFilled | .notAllGroupsFilled | .groupsNotCollectivelyFilled => true
  | .noGroupFilled | .atLeastOneGroupFilled => false

def GroupFillQuantifier.canFireOnEmpty : GroupFillQuantifier → Bool
  | .noGroupFilled | .notAllGroupsFilled => true
  | .allGroupsFilled | .atLeastOneGroupFilled
  | .groupsNotCollectivelyFilled => false

/-- One resolved operand of a group-list predicate after either a field observation or a group product state has supplied its presence classification. -/
inductive GroupListPresenceState where
  | filled
  | empty
  | unavailable
  deriving Repr, DecidableEq

namespace CellObservation

/-- A field operand contributes to the same three buckets as a group operand. Formal unavailability is neither filled nor empty. -/
def asGroupListPresence : CellObservation → GroupListPresenceState
  | .empty => .empty
  | .value _ => .filled
  | .unknown _ | .poison _ => .unavailable

/-- Computation-phase presence of one descendant cell. This is a coarsening of
    `asGroupListPresence`, not its inverse: the two agree that a read value is present and
    an absent read is absent, and differ only in that formal unavailability counts as
    present here where validation keeps it in a third bucket. Only a cell the phase read
    reports as absent is absent, which keeps the validation-scoped required finding out of
    the computation count.

    The `.unknown` branch is unreachable from `observeCell .computation`, which yields
    `.poison` for a finding; it is answered the same way to keep the function total. -/
def presentForComputation : CellObservation → Bool
  | .empty => false
  | .value _ => true
  | .unknown _ => true
  | .poison _ => true

end CellObservation

def GroupPresenceState.asGroupListPresence
    (state : GroupPresenceState) : GroupListPresenceState :=
  if state.definitelyFilled then .filled
  else if state.definitelyEmpty then .empty
  else .unavailable

/-- Extensional group-list classification. Unavailable field or group operands are neither filled nor empty. -/
structure GroupListPresenceTally where
  filled : Nat
  empty : Nat
  unavailable : Nat
  deriving Repr, DecidableEq

namespace GroupListPresenceTally

def filledOnly (count : Nat) : GroupListPresenceTally := { filled := count, empty := 0, unavailable := 0 }

def add (left right : GroupListPresenceTally) : GroupListPresenceTally :=
  { filled := left.filled + right.filled
    empty := left.empty + right.empty
    unavailable := left.unavailable + right.unavailable }

def ofStates :
    List GroupListPresenceState → GroupListPresenceTally
  | [] => { filled := 0, empty := 0, unavailable := 0 }
  | state :: rest =>
      let tally := ofStates rest
      match state with
      | .filled => { tally with filled := tally.filled + 1 }
      | .empty => { tally with empty := tally.empty + 1 }
      | .unavailable => { tally with unavailable := tally.unavailable + 1 }

def ofGroupStates (states : List GroupPresenceState) :
    GroupListPresenceTally :=
  ofStates (states.map GroupPresenceState.asGroupListPresence)

end GroupListPresenceTally

/-- Evaluate the shared group-presence tally. Resolved fixed lists and starred structural row counts supply different classifications to this one operator table. -/
def GroupFillQuantifier.evalTally (operator : GroupFillQuantifier)
    (tally : GroupListPresenceTally) : ValidationFillOutcome :=
  match operator with
  | .allGroupsFilled =>
      if tally.empty == 0 && tally.unavailable == 0 then .fired .value else .falseOrUnknown
  | .noGroupFilled =>
      if tally.filled == 0 && tally.unavailable == 0 then .fired .omission else .falseOrUnknown
  | .atLeastOneGroupFilled =>
      if 0 < tally.filled then .fired .value else .falseOrUnknown
  | .notAllGroupsFilled =>
      if 0 < tally.empty then .fired .omission else .falseOrUnknown
  | .groupsNotCollectivelyFilled =>
      if 0 < tally.filled && 0 < tally.empty then .fired .omission else .falseOrUnknown

/-- Group-list validation retains the same collapsed non-fire observable as field-list validation. Independent filled or empty witnesses may decide despite unavailable peers. -/
def GroupFillQuantifier.evalPresence (operator : GroupFillQuantifier)
    (states : List GroupListPresenceState) : ValidationFillOutcome :=
  operator.evalTally (GroupListPresenceTally.ofStates states)

/-- Preserve the established group-only resolved entry point as a specialization of the field/group presence classifier. -/
def GroupFillQuantifier.evalValidation (operator : GroupFillQuantifier)
    (states : List GroupPresenceState) : ValidationFillOutcome :=
  operator.evalPresence (states.map GroupPresenceState.asGroupListPresence)

/-- The plain multi-group numeric count in the **validation** arm is unavailable unless every
    operand group is fully relevant and error-free; unlike group-list predicates it cannot
    skip unknowns. The computation arm has no such state and is counted separately below. -/
inductive FilledGroupCount where
  | value (count : Nat)
  | unknown
  deriving Repr, DecidableEq

namespace FilledGroupCount

/-- Pair an available group count with its movement against the declared entity extent. Unused
    declared entities make the count grow-only; exhausting the extent makes it fixed independently
    of descendant cell content. Cause-free group-state unavailability remains absent. -/
def availableWithFillability? (result : FilledGroupCount)
    (declaredExtent : Nat) : Option (Nat × NumericFillability) :=
  match result with
  | .unknown => none
  | .value count =>
      some (count,
        if count < declaredExtent then .growOnly else .fixed)

end FilledGroupCount

def numberOfFilledGroups (states : List GroupPresenceState) : FilledGroupCount :=
  if states.any (fun state => state.erroneous || !(state.relevance == .fullyRelevant)) then .unknown
  else .value (states.countP fun state => state.content)

/-- One group's computation-phase presence, decided by its own descendant reads rather than
    by a separately supplied state, so it cannot disagree with the cells the computation
    itself reads. -/
def groupPresentForComputation (cells : List CellObservation) : Bool :=
  cells.any CellObservation.presentForComputation

/-- The plain multi-group numeric count in the computation arm. Deliberately **not** a
    `FilledGroupCount`: unlike the validation projection above it cannot answer unknown,
    because a formally invalid descendant makes its group count as filled instead of making
    the count unavailable. Only a group with no compute-present descendant is skipped.

    The two projections must stay separate rather than share a phase flag. This one consumes
    descendant reads only; it does not consume the validation state's repeat-row, structural,
    or relevance dimensions, none of which the retained observation covers. The proved
    relation between the arms is confined to descendant content: see the monotonicity and
    clean-agreement laws in the trusted proof root. -/
def numberOfFilledGroupsForComputation (groups : List (List CellObservation)) : Nat :=
  groups.countP groupPresentForComputation

end A12Kernel
