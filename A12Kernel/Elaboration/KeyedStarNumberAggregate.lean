import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.CheckedIndexColumn

/-! # A Number aggregate over a star below a keyed row

`Sum(Packages/Items*/Weight For "P1")` names one `Packages` row by its index field and aggregates the
`Items` rows inside it: **the key selects the row and the star expands within it**, as a rule
iterating `Packages` would read `Items*` at that row
([`spec/08`](../../spec/08-paths-and-references.md),
[inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-keyed-parent-stars)). This module adds no
aggregate: it selects the row through the shared index column and hands its environment to the
ordinary starred Number source as the outer binding.

The measured shape is one text key on the index group directly above the star. A star at or above
the index group, a Number index, a level between the two, and a filter are refused here without a
class; the Kernel's classes for the first are carrier-specific and unmeasured on this operator.

A key naming no clean row is UNKNOWN when the column holds an unavailable key, a duplicate of the
requested one included, as the scalar keyed read's miss is. Otherwise the star is read in no row, so
the aggregate folds no cell and is a fixed zero, where the scalar read returns an empty cell. Both
are unmeasured at validation; the peer measures the duplicated key's `Sum` only on the computation
arm, which this module does not carry.
-/

namespace A12Kernel

/-- One keyed lower-star Number operand as authored. -/
structure SurfaceKeyedStarNumberSource where
  target : SurfaceStarFieldPath
  token : String
  deriving Repr, DecidableEq

inductive KeyedStarNumberElabError where
  | entity (error : NumberEntityElabError)
  /-- No group on the target's chain declares an index field. -/
  | noIndexGroup (path : List String)
  /-- The first star is not on the level directly below the index group. -/
  | starNotDirectlyBelowIndexGroup (path : List String)
  /-- A Number index compares keys numerically, which a text token does not carry. -/
  | numberIndex (path : List String)
  | unsupportedOperand
  deriving Repr, DecidableEq

/-- A starred Number source whose first star lies directly below its chain's innermost index group,
with the literal token that selects that group's row. -/
structure CheckedKeyedStarNumberSource (model : FlatModel) where
  indexGroup : RepeatableGroupDecl
  token : String
  star : CheckedNumberEntitySource model

/-- Resolve the ordinary starred source, then find the index group the key addresses: the innermost
repeatable level on the target's chain whose group declares an index field. -/
def elaborateKeyedStarNumberSource (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceKeyedStarNumberSource) :
    Except KeyedStarNumberElabError (CheckedKeyedStarNumberSource model) := do
  let star ← elaborateNumberEntitySource model declaringGroup
    { first := .star authored.target, rest := [] } |>.mapError .entity
  let path ← match star.first, star.rest with
    | .star source, [] => pure source.source
    | _, _ => throw .unsupportedOperand
  let axes := path.path.axes.map (·.level)
  let indexed := (axes.zipIdx).filterMap fun (level, position) =>
    (model.repeatableGroupAtLevel? level).bind fun group =>
      group.indexField.map fun _ => (group, position)
  let (indexGroup, position) ← match indexed.getLast? with
    | some found => pure found
    | none => throw (.noIndexGroup path.declaration.path)
  if path.path.firstStar != position + 1 then
    throw (.starNotDirectlyBelowIndexGroup path.declaration.path)
  let indexKind ← match indexGroup.indexField.bind fun id => (model.lookupUniqueId id).toOption with
    | some declaration => pure declaration.policy.kind
    | none => throw (.noIndexGroup path.declaration.path)
  if let .number _ := indexKind then throw (.numberIndex path.declaration.path)
  pure { indexGroup, token := authored.token, star }

inductive KeyedStarNumberContextError where
  | column (error : CheckedIndexColumnError)
  | addressing (error : CheckedAddressingError)
  deriving Repr, DecidableEq

namespace CheckedKeyedStarNumberSource

/-- Evaluate one aggregate at full validation: select the keyed row among the index group's rows
under `outer`, then fold the star inside it. -/
def evaluateValidation (checked : CheckedKeyedStarNumberSource model)
    (op : NumericAggregateOp) (preliminary : CheckedIndexPreliminary model) (outer : Env := []) :
    Except KeyedStarNumberContextError NumericOperand := do
  let column ← preliminary.resolveIndexColumn checked.indexGroup outer |>.mapError .column
  let resolved ← column.toSemanticIndexColumn preliminary column.indexDeclaration.id |>.mapError .column
  match resolved.lookupEnvironment .validation false (.value (.str checked.token)) with
  | .value (some environment) =>
      checked.star.evaluateCheckedDocumentValidationAggregate op preliminary.base
        environment |>.mapError .addressing
  | .value none => throw (.addressing (.checkedDocumentRequired checked.indexGroup.path))
  | .empty => pure op.overNoCells
  | .unknown cause | .poison cause => pure (.unknown cause)

end CheckedKeyedStarNumberSource

end A12Kernel
