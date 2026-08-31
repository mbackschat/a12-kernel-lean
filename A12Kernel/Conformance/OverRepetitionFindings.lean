import A12Kernel.Elaboration.OverRepetitionFindings

/-! # Over-repetition finding-set locks

The rows behind these cases are the [multiplicity](../../docs/sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)
and [absorption-depth](../../docs/sources/over-repetition-probes.md#src-over-limit-absorption-depth)
checkpoints, both taken on the same probe model this fixture reproduces: `Mid` declared `max 3`
carrying `Rows`, and an independent `A`/`B`/`C` chain each declared `max 2`.

Findings are compared as **sets**: nothing measured fixes the Kernel's emission order, so a case that
pinned one would claim more than the observation supports.

Every count here is the **full-validation** channel's. The same artifacts carry a second, narrower
operand-scoped channel that a computation sees, and it answers differently on these very documents,
so none of these numbers may be reused for it.
-/

namespace A12Kernel.Conformance.OverRepetitionFindings

open A12Kernel

private def deepValue : FlatFieldDecl := {
  id := 1, groupPath := ["Probe", "ShellDeep", "Mid", "Rows"], name := "DeepValue"
  policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10, 20]
}

private def deepValue2 : FlatFieldDecl := { deepValue with id := 2, name := "DeepValue2" }

private def triValue : FlatFieldDecl := {
  id := 3, groupPath := ["Probe", "Tri", "A", "B", "C"], name := "TriValue"
  policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [30, 40, 50]
}

private def model : FlatModel := {
  fields := [deepValue, deepValue2, triValue]
  repeatableGroups := [
    { level := 10, path := ["Probe", "ShellDeep", "Mid"], repeatability := some 3 },
    { level := 20, path := ["Probe", "ShellDeep", "Mid", "Rows"], repeatability := some 5 },
    { level := 30, path := ["Probe", "Tri", "A"], repeatability := some 2 },
    { level := 40, path := ["Probe", "Tri", "A", "B"], repeatability := some 2 },
    { level := 50, path := ["Probe", "Tri", "A", "B", "C"], repeatability := some 2 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def emptyCell (field : FieldId) (path : List Nat) : ClassifiedCellInput :=
  { address := { field, path }, stored := "", raw := .presentEmpty }

private def findings? (rows : List RowAddr) (cells : List ClassifiedCellInput) :
    Option (List OverRepetitionFinding) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption.map
    (·.overRepetitionFindings)

private def sorted (findings : Option (List OverRepetitionFinding)) :
    Option (List (OverRepetitionCode × List Nat)) :=
  findings.map fun entries => (entries.map fun entry =>
    (entry.code, match entry.node with
      | .row address => address.path
      | .cell address => address.path)).mergeSort
      fun left right => decide (left.2.length ≤ right.2.length)

/- **The chain's own rows, in capacity, draw nothing.** The control that makes every finding below a
   consequence of the excess row rather than of the shape. -/
example : findings?
    [{ group := 30, path := [1] }, { group := 40, path := [1, 1] },
     { group := 50, path := [1, 1, 1] }]
    [emptyCell triValue.id [1, 1, 1]] = some [] := by
  native_decide

/- **One `zuGrosseZeile` on the excess row plus one `zuGrosseKontextnummer` per node written beneath
   it, at any depth.** `A[3]` exceeds `max 2`; its own `B` and `C` rows are in capacity and are still
   named, together with the leaf cell. Four findings for one violation. -/
example : sorted (findings?
    [{ group := 30, path := [1] },
     { group := 40, path := [1, 1] },
     { group := 50, path := [1, 1, 1] },
     { group := 30, path := [2] },
     { group := 40, path := [2, 1] },
     { group := 50, path := [2, 1, 1] },
     { group := 30, path := [3] },
     { group := 40, path := [3, 1] },
     { group := 50, path := [3, 1, 1] }]
    [emptyCell triValue.id [1, 1, 1], emptyCell triValue.id [2, 1, 1], emptyCell triValue.id [3, 1, 1]]) =
    some [(.rowNumberTooLarge, [3]), (.contextNumberTooLarge, [3, 1]),
          (.contextNumberTooLarge, [3, 1, 1]), (.contextNumberTooLarge, [3, 1, 1])] := by
  native_decide

/- **An excess row writing nothing beneath it draws the row code alone.** The separator that keeps the
   context code tied to written nodes rather than to declared ones: the same violation, one finding. -/
example : findings?
    [{ group := 30, path := [1] }, { group := 40, path := [1, 1] },
     { group := 50, path := [1, 1, 1] },
     { group := 30, path := [2] }, { group := 40, path := [2, 1] },
     { group := 50, path := [2, 1, 1] },
     { group := 30, path := [3] }]
    [emptyCell triValue.id [1, 1, 1], emptyCell triValue.id [2, 1, 1]] =
    some [{ code := .rowNumberTooLarge, node := .row { group := 30, path := [3] } }] := by
  native_decide

/- **The multiplicity counts cells, not groups.** One excess `Mid[4]` row whose single descendant row
   writes two cell keys reports four findings, not three: the row, the descendant, and each cell. -/
example : sorted (findings?
    [{ group := 10, path := [1] }, { group := 20, path := [1, 1] },
     { group := 10, path := [2] }, { group := 20, path := [2, 1] },
     { group := 10, path := [3] }, { group := 20, path := [3, 1] },
     { group := 10, path := [4] }, { group := 20, path := [4, 1] }]
    [emptyCell deepValue.id [1, 1], emptyCell deepValue2.id [1, 1],
     emptyCell deepValue.id [2, 1], emptyCell deepValue2.id [2, 1],
     emptyCell deepValue.id [3, 1], emptyCell deepValue2.id [3, 1],
     emptyCell deepValue.id [4, 1], emptyCell deepValue2.id [4, 1]]) =
    some [(.rowNumberTooLarge, [4]), (.contextNumberTooLarge, [4, 1]),
          (.contextNumberTooLarge, [4, 1]), (.contextNumberTooLarge, [4, 1])] := by
  native_decide

/- **The outermost violation absorbs every nested one, not only its immediate child.** `A[3]`, its
   `B[3]`, and that row's `C[3]` are each beyond their own capacity of two, and the document draws
   exactly one row code — on `A[3]` — with the inner violations named like any other written node. -/
example : sorted (findings?
    [{ group := 30, path := [1] },
     { group := 40, path := [1, 1] },
     { group := 50, path := [1, 1, 1] },
     { group := 30, path := [2] },
     { group := 40, path := [2, 1] },
     { group := 50, path := [2, 1, 1] },
     { group := 30, path := [3] },
     { group := 40, path := [3, 1] },
     { group := 50, path := [3, 1, 1] },
     { group := 40, path := [3, 2] },
     { group := 50, path := [3, 2, 1] },
     { group := 40, path := [3, 3] },
     { group := 50, path := [3, 3, 1] },
     { group := 50, path := [3, 3, 2] },
     { group := 50, path := [3, 3, 3] }]
    []) =
    some [(.rowNumberTooLarge, [3]),
          (.contextNumberTooLarge, [3, 1]), (.contextNumberTooLarge, [3, 2]),
          (.contextNumberTooLarge, [3, 3]),
          (.contextNumberTooLarge, [3, 1, 1]), (.contextNumberTooLarge, [3, 2, 1]),
          (.contextNumberTooLarge, [3, 3, 1]), (.contextNumberTooLarge, [3, 3, 2]),
          (.contextNumberTooLarge, [3, 3, 3])] := by
  native_decide

/- Two disjoint violations stay independent: each draws its own row code and stamps only its own
   subtree, so absorption is containment rather than a document-wide single finding. -/
example : sorted (findings?
    [{ group := 30, path := [1] },
     { group := 30, path := [2] },
     { group := 30, path := [3] },
     { group := 40, path := [3, 1] },
     { group := 10, path := [1] },
     { group := 10, path := [2] },
     { group := 10, path := [3] },
     { group := 10, path := [4] },
     { group := 20, path := [4, 1] }]
    [emptyCell deepValue.id [4, 1]]) =
    some [(.rowNumberTooLarge, [3]), (.rowNumberTooLarge, [4]),
          (.contextNumberTooLarge, [3, 1]), (.contextNumberTooLarge, [4, 1]),
          (.contextNumberTooLarge, [4, 1])] := by
  native_decide

private def scoped? (operands : List (List String)) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (List (OverRepetitionCode × List Nat)) :=
  sorted ((checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption.map
    (·.computationOverRepetitionFindings operands))

/- The document above, read through the **computation** channel instead of the validation one. It is
   the separating shape: two over-limit subtrees, and a computation whose operands name only one of
   them. Kernel-measured on the retained multiplicity artifact, where the probe model's three
   computations name `/Probe/ShellDeep`, `/Probe/ShellDeep/Mid*`, and `/Probe/ShellOne` and none
   names `/Probe/Tri` — so `Mid[4]` draws its four operand errors and `A[3]` draws nothing, in one
   document. Reading only a single-subtree document would leave a document-wide account fitting every
   row, which is how the validation set came to stand in for this one. -/
private def bothViolatedRows : List RowAddr :=
  [{ group := 30, path := [1] },
   { group := 30, path := [2] },
   { group := 30, path := [3] },
   { group := 40, path := [3, 1] },
   { group := 10, path := [1] },
   { group := 10, path := [2] },
   { group := 10, path := [3] },
   { group := 10, path := [4] },
   { group := 20, path := [4, 1] }]

example :
    scoped? [["Probe", "ShellDeep"]] bothViolatedRows [emptyCell deepValue.id [4, 1]] =
      some [(.rowNumberTooLarge, [4]), (.contextNumberTooLarge, [4, 1]),
            (.contextNumberTooLarge, [4, 1])] ∧
    scoped? [["Probe", "Tri"]] bothViolatedRows [emptyCell deepValue.id [4, 1]] =
      some [(.rowNumberTooLarge, [3]), (.contextNumberTooLarge, [3, 1])] ∧
    scoped? [] bothViolatedRows [emptyCell deepValue.id [4, 1]] = some [] := by
  native_decide

/- An operand **beneath** the violated row keeps it: the scope is comparability with the operand's
   path, not containment of the finding within it. The `Mid*` operand of the probe model is exactly
   this shape — the violated row is `Mid[4]` itself — and an over-limit row strictly above an operand
   is the peer's measured half rather than this project's, so it is stated in the clause and not
   locked by a row here. -/
example :
    scoped? [["Probe", "ShellDeep", "Mid", "Rows"]] bothViolatedRows
        [emptyCell deepValue.id [4, 1]] =
      some [(.rowNumberTooLarge, [4]), (.contextNumberTooLarge, [4, 1]),
            (.contextNumberTooLarge, [4, 1])] := by
  native_decide

end A12Kernel.Conformance.OverRepetitionFindings
