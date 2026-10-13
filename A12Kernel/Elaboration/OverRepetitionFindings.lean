import A12Kernel.Elaboration.AddressFormalLegality
import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.ValidationRelevance

/-! # The over-repetition structural finding set and its validation and computation channels

A row instantiated beyond its group's declared repeatability does not merely lose its computed
values ([`CheckedDocument.computationRowOutcomes`](CheckedDocument.lean)); it makes the document
report a countable set of structural findings. This module owns that set and its two projections.

**One per-node rule.** The Kernel index-checks every entity the document writes — each repeatable
row, each nonrepeatable group instance, and each present cell, a present-empty one included — against
that entity's own repeatable ancestry (`CheckCommand.formalePruefung` →
`FormalChecker.checkIndices`). A node draws one finding when some level of its own scope exceeds its
cap, coded by the **first** such level's container depth through
[`AddressFormalLegality`](AddressFormalLegality.lean)'s positional rule: the row whose own level is
violated draws `zuGrosseZeile`, every node beneath draws `zuGrosseKontextnummer`, and a violated
repeatable root group draws `zuGrosseLfdNummer` throughout. The familiar "one row code plus one
context code per written node beneath it" count, the absorption of nested violations
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-absorption-depth)) and the
serial-root case ([checkpoint](../../docs/sources/over-repetition-probes.md#src-address-index-position-classes))
all follow from it; an absent cell and an unwritten declaration draw nothing
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)).

**The channels differ by scope, never by code.** Validation reports the whole set, unless a partial
call's selection is empty. A computation reports only the nodes its prepared data retains: uncomputed
operand cells and the ancestor groups of operand and computed fields
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-repetition-occurrence-scope)).

The Kernel's emission order is not reproduced; the retained observations are compared as sets.
-/

namespace A12Kernel

/-- The structural codes an over-limit row draws. Kept as a closed enumeration rather than as strings,
because their *addresses* differ in kind and a consumer dispatches on that. -/
inductive OverRepetitionCode where
  /-- `zuGrosseLfdNummer` — the violated level is a **root group**, so it occupies position 0 of every
  address that names it and this one code covers the row and its whole subtree. -/
  | serialNumberTooLarge
  /-- `zuGrosseZeile` — the violated row itself, when its group is deeper than the root. Its rendered
  text carries no parameter. -/
  | rowNumberTooLarge
  /-- `zuGrosseKontextnummer` — a node written beneath a violated row whose group is deeper than the
  root. Its rendered text names the violated *group*, with the offending index and the cap as separate
  numbers, and carries no coordinate
  ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-address-dialects)). -/
  | contextNumberTooLarge
  deriving Repr, DecidableEq

/-- The code a coordinate position draws. The single point where this family's vocabulary meets the
shared positional rule, so that neither can drift from the other. -/
def OverRepetitionCode.ofPosition : IndexPosition → OverRepetitionCode
  | .serial => .serialNumberTooLarge
  | .row => .rowNumberTooLarge
  | .context => .contextNumberTooLarge

/-- A node the document writes: a repeatable row, a nonrepeatable group instance, or a placed cell.
The finding set names all three, so a consumer cannot collapse them without losing the per-node
multiplicity. -/
inductive OverRepetitionNode where
  | row (address : RowAddr)
  | group (occurrence : GroupOccurrence)
  | cell (address : CellAddr)
  deriving Repr, DecidableEq

structure OverRepetitionFinding where
  code : OverRepetitionCode
  node : OverRepetitionNode
  deriving Repr, DecidableEq

namespace OverRepetitionNode

/-- The node's own repeatable scope and coordinates. A node whose declaration the model does not
resolve has none and so draws nothing, which keeps an unresolvable node out of the finding set
instead of putting a guess into it. -/
def scope? (model : FlatModel) : OverRepetitionNode → Option (List RepeatableLevel × List Nat)
  | .row address => do
      let declared ← model.repeatableGroupAtLevel? address.group
      pure (model.repeatableScopeForGroupPath declared.path, address.path)
  | .group occurrence =>
      some (model.repeatableScopeForGroupPath occurrence.path, occurrence.coordinates)
  | .cell address => do
      let declaration ← model.fields.find? (·.id == address.field)
      pure (declaration.repeatableScope, address.path)

/-- The first repeatable level of the node's **own** scope whose coordinate exceeds its cap,
outermost first: the level the Kernel's positional scan stops at. Each node is judged against its own
ancestry, never by coordinate-prefix containment in another row, so a sibling group's node at the
same coordinates as an over-capacity row is untouched
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-repetition-occurrence-scope)). -/
def violatedAxis? (model : FlatModel) (node : OverRepetitionNode) : Option StarAxis := do
  let (scope, path) ← node.scope? model
  let axes ← model.repeatableAxesForScope? scope
  let violated ← (axes.zip (scope.zip path)).find? fun pair => pair.1.bindingOverLimit pair.2
  pure violated.1

/-- Whether a level is the node's own last position. Only a row occupies its own repeatable level;
a nonrepeatable group or a cell always sits strictly beneath every repeatable level it reports. -/
def ownsLevel (node : OverRepetitionNode) (level : RepeatableLevel) : Bool :=
  match node with
  | .row address => address.group == level
  | .group _ | .cell _ => false

/-- The finding one written node draws, if any. The code follows the violated level's container
depth through the shared positional rule; absorption is that rule's first-match-wins, because an
inner over-capacity row whose ancestor is also violated reports the ancestor's position. -/
def finding? (model : FlatModel) (node : OverRepetitionNode) : Option OverRepetitionFinding := do
  let axis ← node.violatedAxis? model
  let declared ← model.repeatableGroupAtLevel? axis.level
  let depth := declared.path.length
  let position := if node.ownsLevel axis.level then violatedLevelOwnPosition depth
    else violatedLevelDescendantPosition depth
  pure { code := .ofPosition position, node }

/-- Whether a computation call's prepared data retains the node. The Kernel filters the document
before its formal check to the uncomputed operand fields plus every ancestor group of an operand or
computed field (`CalculationCommand.getEntityFullNamesNotRemovedFromData`), so an unread sibling
field and an unread nonrepeatable subtree draw nothing while the target's own ancestry does
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-repetition-occurrence-scope)). -/
def retainedFor (model : FlatModel) (operandFields anchorFields : List FieldId) :
    OverRepetitionNode → Bool
  | .cell address => operandFields.contains address.field
  | .row address => match model.repeatableGroupAtLevel? address.group with
      | some declared => anchors declared.path
      | none => false
  | .group occurrence => anchors occurrence.path
where
  anchors (path : GroupPath) : Bool := anchorFields.any fun field =>
    match model.fields.find? (·.id == field) with
    | some declaration => path.isPrefixOf declaration.groupPath
    | none => false

end OverRepetitionNode

namespace CheckedDocument

/-- Every node the document writes: rows, then nonrepeatable group instances, then cells, each in
document order. Present-empty cells are written nodes; absent ones are not. -/
def writtenNodes (checked : CheckedDocument model) : List OverRepetitionNode :=
  checked.source.instantiatedRows.map .row ++ checked.source.groupOccurrences.map .group ++
    checked.source.cells.map (.cell ·.address)

/-- The complete structural finding set full validation reports. Order is **not** claimed: no
retained observation fixes an emission order, so compare this as a set. -/
def overRepetitionFindings (checked : CheckedDocument model) : List OverRepetitionFinding :=
  checked.writtenNodes.filterMap (·.finding? model)

/-- The structural finding set one validation call reports. The index check runs before relevance
is consulted, so every nonempty partial selection reports the full set, while an empty selection
ends the call before any check (`ValidationCommand.processPartlyValidation`) and reports nothing
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-repetition-occurrence-scope)). -/
def overRepetitionFindingsUnder (checked : CheckedDocument model) :
    ValidationRelevanceScope → List OverRepetitionFinding
  | .full => checked.overRepetitionFindings
  | .partialSet [] => []
  | .partialSet (_ :: _) => checked.overRepetitionFindings

/-- The over-repetition findings a **computation** reports in its operand channel: the validation
set restricted to the nodes its prepared data retains. `operandFields` are the uncomputed operand
fields, after group-operand and implicit-guard expansion; `anchorFields` are every operand and
computed field whose ancestor groups the call retains. -/
def computationOverRepetitionFindings (checked : CheckedDocument model)
    (operandFields anchorFields : List FieldId) : List OverRepetitionFinding :=
  checked.overRepetitionFindings.filter (·.node.retainedFor model operandFields anchorFields)

end CheckedDocument

/-- The structural part of one computation call's `formalErrorsInOperands` channel, scoped by the
same checked plan whose cell findings form the rest of that channel. The plan's coarse
`.overRepetition` cell entries name the same over-capacity operand cells; these findings carry their
Kernel codes and add the retained ancestor rows and group instances. -/
def CheckedComputationFormalInputPlan.structuralFindings
    (plan : CheckedComputationFormalInputPlan model) (input : CheckedDocument model) :
    List OverRepetitionFinding :=
  input.computationOverRepetitionFindings plan.selectedFields
    (plan.operandFields ++ plan.computedFields)


end A12Kernel
