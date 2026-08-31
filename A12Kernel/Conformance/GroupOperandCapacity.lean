import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.CheckedDocument

/-! # A fixed group operand's declared-capacity extent

Kernel 30.8.1 excludes a row beyond its group's declared repeatability from the **extent** a fixed
group operand denotes, rather than admitting the row and classifying its cell as unavailable. The two
accounts agree on every document whose over-limit cell is well formed — both predict a definite
answer that ignores it — and separate on a document whose over-limit cell is malformed: an excluded
row contributes nothing, while an admitted-and-unavailable one would poison the whole aggregate.

Measured at the [inbound extent checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-group-operand-capacity-consumer-sweep)
on the four Number aggregate carriers, each against an in-capacity control differing only in the
offending index. The Number **value count** shares this resolver and is not itself measured; its two
sibling kinds are, and the record says so rather than implying a row exists.
-/

namespace A12Kernel.Conformance.GroupOperandCapacity

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

/-- A nonrepeatable shell owning one repeatable subgroup capped at two, so index 3 is over-limit
while the operand itself stays the fixed group form the checkpoint measures. -/
private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form", "Shell", "Charges"], name := "Fee",
        policy := { kind := .number unsigned }, repeatableScope := [30] }]
    repeatableGroups := [
      { level := 30, path := ["Form", "Shell", "Charges"], repeatability := some 2 }] }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def source? : Option (CheckedNumberEntitySource model) :=
  (elaborateNumberEntitySource model ["Form"]
    { first := .group (.path { base := .absolute, groups := ["Form", "Shell"] }),
      rest := [] }).toOption

private def fee (row : List Nat) (value : Nat) : ClassifiedCellInput :=
  { address := { field := 1, path := row }, stored := toString value,
    raw := .parsed (.num value) }

private def malformedFee (row : List Nat) : ClassifiedCellInput :=
  { address := { field := 1, path := row }, stored := "?", raw := .rejected .malformed }

private def rows (count : Nat) : List RowAddr :=
  (List.range count).map fun index => { group := 30, path := [index + 1] }

private def aggregate? (op : NumericAggregateOp) (rowCount : Nat)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let source ← source?
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows rowCount
    cells }).toOption
  (source.evaluateCheckedDocumentValidationAggregate op document []).toOption

/- The three carriers whose in-capacity value differs from the whole-extent one. Each control holds
   the same two values one index lower, so the pair separates the capacity projection from a general
   failure to read the third row. -/
example :
    (aggregate? .sum 3 [fee [1] 5, fee [3] 7],
     aggregate? .sum 2 [fee [1] 5, fee [2] 7],
     aggregate? .maximum 3 [fee [1] 5, fee [3] 7],
     aggregate? .maximum 2 [fee [1] 5, fee [2] 7]) =
    (some (.value 5 { canGrow := true, canShrink := false }),
     some (.value 12 { canGrow := false, canShrink := false }),
     some (.value 5 { canGrow := true, canShrink := false }),
     some (.value 7 { canGrow := false, canShrink := false })) := by
  native_decide

/- `MinValue` needs the reversed document to discriminate: with the smaller value in capacity it
   would answer `5` under either account. Here the in-capacity value is the larger one, so an extent
   that reached the over-limit row would answer `5` instead of `7`. Its movement is the mirror of the
   others': the empty in-capacity row can only pull a minimum down, so the operand can shrink where
   `Sum`, `MaxValue`, and the distinct count can grow. -/
example :
    (aggregate? .minimum 3 [fee [1] 7, fee [3] 5],
     aggregate? .minimum 2 [fee [1] 7, fee [2] 5],
     aggregate? .distinctCount 3 [fee [1] 5, fee [3] 7],
     aggregate? .distinctCount 2 [fee [1] 5, fee [2] 7]) =
    (some (.value 7 { canGrow := false, canShrink := true }),
     some (.value 5 { canGrow := false, canShrink := false }),
     some (.value 1 { canGrow := true, canShrink := false }),
     some (.value 2 { canGrow := false, canShrink := false })) := by
  native_decide

/- The separating pair. The same malformed cell one index apart decides whether the aggregate is
   evaluable at all: over limit it is not in the domain being classified, in capacity it is and its
   unavailability propagates. A definite answer on a well-formed over-limit document is consistent
   with both accounts, so without this pair the rows above lock the value and not the mechanism. -/
example :
    (aggregate? .sum 3 [fee [1] 5, malformedFee [3]],
     aggregate? .sum 2 [fee [1] 5, malformedFee [2]]) =
    (some (.value 5 { canGrow := true, canShrink := false }),
     some (.unknown .malformed)) := by
  native_decide

/- The exclusion is the operand's own extent rather than a document-level erasure: the over-limit
   cell is still there, and reading the same document through the complete formal-cell view still
   reports it. Without this the cases above would also pass on an implementation that dropped the
   row when the document was checked. -/
example :
    ((do
      let document ← (checkDocument prepared "en_US" {
        instantiatedRows := rows 3
        cells := [fee [1] 5, fee [3] 7] }).toOption
      let cell ← (document.read { field := 1, path := [3] }).toOption
      pure (observeCell .validation cell)) =
      some (.unknown .overRepetition)) := by
  native_decide

end A12Kernel.Conformance.GroupOperandCapacity
