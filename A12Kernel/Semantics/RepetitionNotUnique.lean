import A12Kernel.Semantics.Iteration
import A12Kernel.Semantics.ValueList

/-! # Resolved `RepetitionNotUnique`

This capsule begins after reference-scope selection, path expansion, and validation-phase key-cell classification. It defines the duplicate relation over an ordered explicit scope, then exposes one verdict per row.

Kernel 30.8.1 externally collapses a unique row and an invalid/excluded current row into `FALSE_OR_UNKNOWN`. This theory retains the pre-collapse distinction: a clean unique row is `notFired`, while an invalid current key is `unknown`. External correspondence can establish only authored-message suppression for either result.

Checked default/explicit `@From` resolution, topology, same-path/key-schema checking, partial relevance, model legality (including one RNU leaf and iteration/filter/parallel restrictions), message pointers, and whole-rule orchestration remain separate.
-/

namespace A12Kernel

/-- The heterogeneous comparable atoms admitted by this first resolved RNU capsule. Number equality delegates to the shared scale-19 boundary; canonical tokens compare exactly. -/
inductive RepetitionKeyAtom where
  | number (value : Rat)
  | token (value : String)
  deriving Repr, DecidableEq

namespace RepetitionKeyAtom

def equal : RepetitionKeyAtom → RepetitionKeyAtom → Bool
  | .number left, .number right =>
      ValueListAtom.equal (kind := .number) left right
  | .token left, .token right =>
      ValueListAtom.equal (kind := .token) left right
  | _, _ => false

end RepetitionKeyAtom

/-- One already-classified key component. Optional empty is a valid tuple component; UNKNOWN includes required-empty and every other formal invalidity. -/
inductive RepetitionKeyComponent where
  | present (value : RepetitionKeyAtom)
  | empty
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

namespace RepetitionKeyComponent

/-- Classify one validation-phase String observation as an RNU token component. Formal unavailability preserves its exact cause; optional empty remains a matchable empty component. -/
def ofTokenObservation : CellObservation String → RepetitionKeyComponent
  | .value value => .present (.token value)
  | .empty => .empty
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Project an already-checked String cell into a key component without repeating formal or custom validation. -/
def ofCheckedTokenCell (cell : CheckedCell String) : RepetitionKeyComponent :=
  ofTokenObservation (observeCell .validation cell)

/-- Reuse the checked token value-list classification when constructing an exact-text RNU key. -/
def ofTokenValueListCell : ValueListCell .token → RepetitionKeyComponent
  | .present value => .present (.token value)
  | .empty => .empty
  | .unknown cause => .unknown cause

/-- Reuse the checked Number value-list classification when constructing a typed RNU key. Number emptiness stays an optional empty tuple component rather than becoming zero. -/
def ofNumberValueListCell : ValueListCell .number → RepetitionKeyComponent
  | .present value => .present (.number value)
  | .empty => .empty
  | .unknown cause => .unknown cause

def isPresent : RepetitionKeyComponent → Bool
  | .present _ => true
  | .empty | .unknown _ => false

def isEmpty : RepetitionKeyComponent → Bool
  | .empty => true
  | .present _ | .unknown _ => false

def isUnknown : RepetitionKeyComponent → Bool
  | .unknown _ => true
  | .present _ | .empty => false

/-- Tuple-component equality for eligible rows. Optional empties match; an UNKNOWN component never participates in equality. -/
def equal : RepetitionKeyComponent → RepetitionKeyComponent → Bool
  | .present left, .present right => left.equal right
  | .empty, .empty => true
  | _, _ => false

end RepetitionKeyComponent

/-- Ordered tuple equality. Component order and tuple length are semantic. -/
def repetitionKeyEqual :
    List RepetitionKeyComponent → List RepetitionKeyComponent → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.equal right && repetitionKeyEqual leftRest rightRest
  | _, _ => false

/-- One explicit row in the already-selected uniqueness scope. The complete environment distinguishes equal local indices beneath different outer rows. The upstream checked topology supplies canonical environments with positive coordinates and unique identities; this resolved evaluator remains total outside that obligation. -/
structure ResolvedRepetitionKeyRow where
  row : Env
  key : List RepetitionKeyComponent
  deriving Repr, DecidableEq

namespace ResolvedRepetitionKeyRow

def hasPresent (row : ResolvedRepetitionKeyRow) : Bool :=
  row.key.any RepetitionKeyComponent.isPresent

def hasEmpty (row : ResolvedRepetitionKeyRow) : Bool :=
  row.key.any RepetitionKeyComponent.isEmpty

def hasUnknown (row : ResolvedRepetitionKeyRow) : Bool :=
  row.key.any RepetitionKeyComponent.isUnknown

/-- Eligible rows have a complete known key and at least one present component. This drops invalid rows and skips the all-empty tuple. -/
def eligible (row : ResolvedRepetitionKeyRow) : Bool :=
  !row.hasUnknown && row.hasPresent

def sameKey (left right : ResolvedRepetitionKeyRow) : Bool :=
  repetitionKeyEqual left.key right.key

end ResolvedRepetitionKeyRow

/-- The minimum structural obligation needed for peer reasoning at this resolved boundary. Checked topology must additionally establish canonical, positive, level-unique environments and a common key schema. -/
def ResolvedRepetitionKeyRows.WellFormed
    (rows : List ResolvedRepetitionKeyRow) : Prop :=
  (rows.map (·.row)).Nodup

/-- Every eligible row in scope with the target's exact typed composite key, in scope order. This order is the direct evaluator's deterministic representation, not a future message-pointer ordering contract. The target itself is included when it came from a well-formed supplied scope. -/
def repetitionDuplicateCluster
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow) :
    List ResolvedRepetitionKeyRow :=
  if target.eligible then
    rows.filter fun candidate =>
      candidate.eligible && target.sameKey candidate
  else
    []

/-- The per-row RNU observation. `cluster` is populated only for a firing and contains the complete duplicate cluster in scope order. For the whole-scope evaluator, or under the explicit target-in-scope obligation, it includes the current row. -/
structure RepetitionNotUniqueResult where
  row : Env
  verdict : Verdict
  cluster : List Env
  deriving Repr, DecidableEq

/-- Evaluate one row against the branch-independent duplicate relation. An invalid current key maps its pre-collapse UNKNOWN classification to Lean `Verdict.unknown`; this is a documented refinement of the kernel's externally collapsed non-firing result. -/
def evalRepetitionNotUniqueRow
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow) :
    RepetitionNotUniqueResult :=
  if target.hasUnknown then
    { row := target.row, verdict := .unknown, cluster := [] }
  else if !target.hasPresent then
    { row := target.row, verdict := .notFired, cluster := [] }
  else
    let cluster := repetitionDuplicateCluster rows target
    if 2 ≤ cluster.length then
      {
        row := target.row
        verdict := .fired (if target.hasEmpty then .omission else .value)
        cluster := cluster.map (·.row)
      }
    else
      { row := target.row, verdict := .notFired, cluster := [] }

/-- Evaluate every explicit row against the same branch-independent relation without consulting a surrounding Boolean branch. This direct definition recomputes the extensional cluster per target; an optimized cache is a later refinement target. Ordinary `Verdict.conj`/`disj` composition happens only afterward. -/
def evalRepetitionNotUnique
    (rows : List ResolvedRepetitionKeyRow) :
    List RepetitionNotUniqueResult :=
  rows.map (evalRepetitionNotUniqueRow rows)

end A12Kernel
