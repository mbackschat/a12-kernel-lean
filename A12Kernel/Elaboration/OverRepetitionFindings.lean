import A12Kernel.Elaboration.AddressFormalLegality
import A12Kernel.Elaboration.CheckedDocument

/-! # The over-repetition finding set a document draws **under full validation**

A row instantiated beyond its group's declared repeatability does not merely lose its computed
values ([`CheckedDocument.computationRowOutcomes`](CheckedDocument.lean)); it makes the document
report a specific, countable set of structural findings. This module owns that set and nothing else:
which nodes are named, with which of the two codes, and how a nested violation is absorbed.

**The arm is part of the claim.** Everything below is the full-validation channel. A computation
reports its own over-repetition errors through a **second, narrower** channel scoped to what its
operands reach, and the two disagree on documents this project already holds: in the multiplicity
capture's own artifact the nested document draws **ten** validation findings and **zero** operand
errors, and the two-independent document draws eight against four
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)).
So this set must not be read as what a computation sees. That channel is owned separately below, by
[`computationOverRepetitionFindings`](#A12Kernel.CheckedDocument.computationOverRepetitionFindings),
as a projection of this set rather than as a second traversal.

**One rule replaces the special cases.** An over-limit row draws one row-level code on itself, plus
one context-level code for every node the document instantiates beneath it, at any depth
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)). A
node is a descendant row or a placed cell, and the multiplicity counts **cells, not groups**: one
descendant row writing two cell keys contributes three findings, not one.

**Which codes those are is decided by the violated level's depth, not by the row/descendant split**,
and this module consumes [`AddressFormalLegality`](AddressFormalLegality.lean)'s positional rule rather
than restating it. A container level sits at the last position of its own group's address and at an
interior position of every deeper one, which is where `zuGrosseZeile` and `zuGrosseKontextnummer` come
from — **except at container depth one, where that same position is also position 0 and the serial
class wins throughout.** So an over-instantiated repeatable **root group** draws `zuGrosseLfdNummer` on
the row *and* on every node beneath it, and no row or context code anywhere; the familiar pair is the
deeper-than-root case rather than the whole rule
([checkpoint](../../docs/SOURCES.md#src-address-index-position-classes)).

**The outermost violation absorbs every nested one, not only its immediate child**
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-absorption-depth)), and that
absorption is the positional scan's first-match-wins rather than a rule of its own: every address
reports its own earliest violating position, which is the outermost violated level. Three nested
over-limit levels therefore draw exactly one row-level code, on the outermost, and the inner rows are
named with the context code like any other descendant.

Two boundaries this module does **not** claim. The Kernel's emission order is not reproduced — the
retained observations are compared as sets, because nothing measured fixes an order. And a cell is
counted when the document places it, which the retained rows cannot separate from "declared by the
model", since every measured document writes every declared key of the rows it instantiates.
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
  ([checkpoint](../../docs/SOURCES.md#src-message-address-dialects)). -/
  | contextNumberTooLarge
  deriving Repr, DecidableEq

/-- The code a coordinate position draws. The single point where this family's vocabulary meets the
shared positional rule, so that neither can drift from the other. -/
def OverRepetitionCode.ofPosition : IndexPosition → OverRepetitionCode
  | .serial => .serialNumberTooLarge
  | .row => .rowNumberTooLarge
  | .context => .contextNumberTooLarge

/-- A node the document writes: a row or a placed cell. The finding set names both, so a consumer
cannot collapse them without losing the per-cell multiplicity. -/
inductive OverRepetitionNode where
  | row (address : RowAddr)
  | cell (address : CellAddr)
  deriving Repr, DecidableEq

structure OverRepetitionFinding where
  code : OverRepetitionCode
  node : OverRepetitionNode
  deriving Repr, DecidableEq

namespace CheckedDocument

/-- The repeatable scope of one instantiated row's own group, or none when the model declares no
such level. A row whose group is unknown cannot be placed in the capacity order and is skipped. -/
private def rowScope? (model : FlatModel) (row : RowAddr) : Option (List RepeatableLevel) := do
  let group ← model.repeatableGroupAtLevel? row.group
  pure (model.repeatableScopeForGroupPath group.path)

/-- Whether a node at `innerPath` lies strictly beneath the row `outer` in the written tree: its
coordinates extend `outer`'s and it is not `outer` itself. Scope containment is not consulted
separately because the coordinate prefix already carries it — a deeper row's path is longer by
exactly its extra levels. Exposed because the absorption law below is stated in terms of it. -/
def extendsRow (outer : RowAddr) (innerPath : List Nat) : Bool :=
  innerPath.length > outer.path.length && innerPath.take outer.path.length == outer.path

/-- Whether a cell placed at `cellPath` lies within the row `outer`.

**Equality counts here where it does not for a descendant row.** A cell's coordinate vector is its
declaring group's repeatable scope, so a cell of the violated row *itself* has a vector of exactly the
row's length — and the Kernel names it like any other node beneath the row. Requiring strict extension
drops precisely the cells a field declared directly in the violated group contributes, measured on a
repeatable root group whose direct field is reported alongside its nested one
([checkpoint](../../docs/SOURCES.md#src-address-index-position-classes)). -/
def cellWithinRow (outer : RowAddr) (cellPath : List Nat) : Bool :=
  cellPath.length ≥ outer.path.length && cellPath.take outer.path.length == outer.path

/-- Whether one instantiated row exceeds its group's declared repeatability on any of its axes. An
unknown scope answers false, matching `rowScope?`. -/
def rowOverLimit (checked : CheckedDocument model) (row : RowAddr) : Bool :=
  let _ := checked
  match rowScope? model row with
  | none => false
  | some scope => model.addressOverLimit? scope row.path == some true

/-- The violated rows that are not themselves beneath another violated row. This is the absorption:
only an outermost violation draws `zuGrosseZeile`, and an inner one is named with the context code
like any other written node. -/
def outermostOverLimitRows (checked : CheckedDocument model) : List RowAddr :=
  let violated := checked.source.instantiatedRows.filter (checked.rowOverLimit ·)
  violated.filter fun row =>
    !violated.any fun other => extendsRow other row.path

/-- The container depth of the first repeatable level of a row's own scope whose coordinate exceeds
its cap, outermost first — that is, the length of that level's declared group path.

It is the level the Kernel's positional scan stops at, and its depth is what selects the codes. Only
repeatable levels are examined because a nonrepeatable level's coordinate is always its cap, so it
never stops the scan even though it occupies a position. -/
def violatedContainerDepth? (checked : CheckedDocument model) (row : RowAddr) : Option Nat := do
  let _ := checked
  let scope ← rowScope? model row
  let axes ← model.repeatableAxesForScope? scope
  let violated ← (axes.zip (scope.zip row.path)).find? fun pair => pair.1.bindingOverLimit pair.2
  let group ← model.repeatableGroupAtLevel? violated.1.level
  pure group.path.length

/-- Every axis a resolved scope produces names a level the model declares, because the resolution
itself is what looked that level up. Stated so the depth lookup below can be shown total on a violated
row rather than defaulted. -/
private theorem repeatableGroup_isSome_of_mem_axes (model : FlatModel) (scope : List RepeatableLevel) :
    ∀ (axes : List StarAxis), model.repeatableAxesForScope? scope = some axes →
      ∀ axis ∈ axes, (model.repeatableGroupAtLevel? axis.level).isSome := by
  induction scope with
  | nil =>
    intro axes h axis hmem
    simp only [FlatModel.repeatableAxesForScope?, Option.some.injEq] at h
    subst h; simp at hmem
  | cons level levels ih =>
    intro axes h axis hmem
    unfold FlatModel.repeatableAxesForScope? at h
    cases hgroup : model.repeatableGroupAtLevel? level with
    | none => simp [hgroup] at h
    | some group =>
      cases hrest : model.repeatableAxesForScope? levels with
      | none => simp [hgroup, hrest] at h
      | some rest =>
        simp only [hgroup, hrest, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact Option.isSome_of_eq_some hgroup
        · exact ih rest hrest axis hmem'

/-- **The depth lookup is total on a violated row**, so the finding builder's unresolved arm is
unreachable from a checked document. Over-limit already required the scope to resolve and some axis to
be exceeded, and a resolved scope's axes all name declared levels — so the three lookups the depth
needs are exactly the ones over-limit already made. -/
theorem violatedContainerDepth?_isSome (checked : CheckedDocument model) (row : RowAddr)
    (h : checked.rowOverLimit row = true) : (checked.violatedContainerDepth? row).isSome := by
  unfold rowOverLimit at h
  cases hscope : rowScope? model row with
  | none => simp [hscope] at h
  | some scope =>
    simp only [hscope] at h
    unfold FlatModel.addressOverLimit? at h
    cases haxes : model.repeatableAxesForScope? scope with
    | none => simp [haxes] at h
    | some axes =>
      simp only [haxes, bind, Option.bind, pure, beq_iff_eq, Option.some.injEq] at h
      unfold violatedContainerDepth?
      simp only [hscope, haxes, bind, Option.bind, pure]
      have hexists : ((axes.zip (scope.zip row.path)).find? fun pair =>
          pair.1.bindingOverLimit pair.2).isSome := by
        rw [List.find?_isSome]
        exact List.any_eq_true.mp h
      cases hfind : (axes.zip (scope.zip row.path)).find? fun pair =>
          pair.1.bindingOverLimit pair.2 with
      | none => rw [hfind] at hexists; simp at hexists
      | some violated =>
        have hmem : violated.1 ∈ axes :=
          List.of_mem_zip (List.mem_of_find?_eq_some hfind) |>.1
        have hgroup := repeatableGroup_isSome_of_mem_axes model scope axes haxes violated.1 hmem
        cases hlookup : model.repeatableGroupAtLevel? violated.1.level with
        | none => rw [hlookup] at hgroup; simp at hgroup
        | some group => simp [hlookup]

/-- A named outermost row is over its limit, which is the filter that produced it. -/
theorem rowOverLimit_of_mem_outermost (checked : CheckedDocument model) (row : RowAddr)
    (h : row ∈ checked.outermostOverLimitRows) : checked.rowOverLimit row = true := by
  unfold outermostOverLimitRows at h
  exact (List.mem_filter.mp (List.mem_filter.mp h).1).2

/-- Every node the document writes beneath one row, rows before cells, each in document order. -/
private def writtenBeneath (checked : CheckedDocument model) (row : RowAddr) :
    List OverRepetitionNode :=
  (checked.source.instantiatedRows.filter (extendsRow row ·.path)).map .row ++
    (checked.source.cells.filter (cellWithinRow row ·.address.path)).map (.cell ·.address)

/-- The complete structural finding set one document draws for over-repetition.

Order is **not** claimed: no retained observation fixes an emission order, so compare this as a set.

A row whose violated level cannot be resolved contributes nothing rather than a defaulted code, which
keeps an unresolvable model out of the finding set instead of putting a guess into it. `rowOverLimit`
already answers false for such a row, so the arm is unreachable from a checked document. -/
def overRepetitionFindings (checked : CheckedDocument model) :
    List OverRepetitionFinding :=
  checked.outermostOverLimitRows.flatMap fun row =>
    match checked.violatedContainerDepth? row with
    | none => []
    | some depth =>
      { code := .ofPosition (violatedLevelOwnPosition depth), node := .row row } ::
        (checked.writtenBeneath row).map fun node =>
          { code := .ofPosition (violatedLevelDescendantPosition depth), node }

/-- The group path a finding's node belongs to: a row's own declared group, or a cell's declaring
group. A node whose owner the model does not declare has no path and is therefore outside every
operand's scope, which keeps an unresolvable node out of the narrower channel rather than into it. -/
private def nodeGroupPath? (model : FlatModel) : OverRepetitionNode → Option GroupPath
  | .row address => (model.repeatableGroupAtLevel? address.group).map (·.path)
  | .cell address => (model.fields.find? (·.id == address.field)).map (·.groupPath)

/-- Whether two group paths lie on one root-to-leaf line: either may be the ancestor. -/
private def comparableGroupPath (left right : GroupPath) : Bool :=
  left.isPrefixOf right || right.isPrefixOf left

/-- The over-repetition findings a **computation** reports, which is not the set the document draws.

    Full validation reports every over-limit row in the document
    ([`overRepetitionFindings`](#A12Kernel.CheckedDocument.overRepetitionFindings)); a computation
    reports only what its own operands reach, so the two differ whenever a violated subtree is
    unread. In this project's retained multiplicity artifact the nested document draws ten validation
    findings and **zero** operand errors, and the two-independent document eight against four
    ([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)).

    **The scope is comparability, and its two halves have different provenance.** A finding at or
    beneath an operand is measured here: that artifact's probe model names `/Probe/ShellDeep`,
    `/Probe/ShellDeep/Mid*`, and `/Probe/ShellOne` and no operand names `/Probe/Tri`, so one document
    holding both an over-limit `Mid[4]` and an over-limit `A[3]` reports the first and not the
    second. A finding **strictly above** an operand is a12-dmkits' measurement rather than this
    project's
    ([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-starred-field-operand-peer-reproduction)):
    an operand two repetition levels down under an over-limit outer row draws three messages. Both
    halves are one comparability test, so the clause is stated once; only its evidence is split.

    Takes the operand group paths rather than a checked computation, so that it stays a projection
    over the finding set instead of a consumer of one. For a group-count computation the supply is
    already settled and needs nothing new: `CheckedGroupCountOperand.groupPath` gives one path per
    operand for both the fixed and the starred form, and is the same accessor the containment and
    rootness gates read. What no atom yet exposes is a path list for an *arbitrary* checked
    computation expression, whose field operands would each contribute their declaring group. -/
def computationOverRepetitionFindings (checked : CheckedDocument model)
    (operandGroupPaths : List GroupPath) : List OverRepetitionFinding :=
  checked.overRepetitionFindings.filter fun finding =>
    match nodeGroupPath? model finding.node with
    | none => false
    | some path => operandGroupPaths.any (comparableGroupPath path ·)

end CheckedDocument

end A12Kernel
