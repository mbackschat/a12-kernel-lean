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
So this set must not be read as what a computation sees. That channel has no owner here; it is
recorded as an obligation in [SG4](../../docs/SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition)
rather than approximated by this one.

**One rule replaces the special cases.** An over-limit row draws one `zuGrosseZeile` on itself, plus
one `zuGrosseKontextnummer` for every node the document instantiates beneath it, at any depth
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)). A
node is a descendant row or a placed cell, and the multiplicity counts **cells, not groups**: one
descendant row writing two cell keys contributes three findings, not one.

**The outermost violation absorbs every nested one, not only its immediate child**
([checkpoint](../../docs/sources/over-repetition-probes.md#src-over-limit-absorption-depth)). Three
nested over-limit levels draw exactly one `zuGrosseZeile`, on the outermost, and the inner rows are
named with the context code like any other descendant.

Two boundaries this module does **not** claim. The Kernel's emission order is not reproduced — the
retained observations are compared as sets, because nothing measured fixes an order. And a cell is
counted when the document places it, which the retained rows cannot separate from "declared by the
model", since every measured document writes every declared key of the rows it instantiates.
-/

namespace A12Kernel

/-- The two structural codes an over-limit row draws. Kept as a closed enumeration rather than as
strings, because their *addresses* differ in kind and a consumer dispatches on that. -/
inductive OverRepetitionCode where
  /-- `zuGrosseZeile` — the violated row itself. Its rendered text carries no parameter. -/
  | rowNumberTooLarge
  /-- `zuGrosseKontextnummer` — a node written beneath a violated row. Its rendered text names the
  violated *group*, with the offending index and the cap as separate numbers, and carries no
  coordinate ([checkpoint](../../docs/SOURCES.md#src-message-address-dialects)). -/
  | contextNumberTooLarge
  deriving Repr, DecidableEq

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

/-- Every node the document writes beneath one row, rows before cells, each in document order. -/
private def writtenBeneath (checked : CheckedDocument model) (row : RowAddr) :
    List OverRepetitionNode :=
  (checked.source.instantiatedRows.filter (extendsRow row ·.path)).map .row ++
    (checked.source.cells.filter (extendsRow row ·.address.path)).map (.cell ·.address)

/-- The complete structural finding set one document draws for over-repetition.

Order is **not** claimed: no retained observation fixes an emission order, so compare this as a set.
-/
def overRepetitionFindings (checked : CheckedDocument model) :
    List OverRepetitionFinding :=
  checked.outermostOverLimitRows.flatMap fun row =>
    { code := .rowNumberTooLarge, node := .row row } ::
      (checked.writtenBeneath row).map fun node =>
        { code := .contextNumberTooLarge, node }

end CheckedDocument

end A12Kernel
