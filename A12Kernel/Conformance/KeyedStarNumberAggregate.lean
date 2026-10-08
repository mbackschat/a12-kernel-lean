import A12Kernel.Elaboration.KeyedStarNumberAggregate

/-! # Locks on a Number aggregate over a star below a keyed row

The fixture is the peer's `KeyedGroupFieldListDiffTest` model: a keyed repeatable `Packages` holding a
repeatable `Items`, with `P1` holding two item rows weighing 2 and 5 and `P2` its key alone
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-keyed-parent-stars)). Its `Sum`, `MaxValue` and
`MinValue` over `P1` are Kernel-measured. The measured rows cannot tell a keyed selection from a star
over every package, because `P2` has no item, so one variant gives `P2` items of its own: the
selected row's rows alone contribute, which the measured `FirstFilledValue` and `NoGroupFilled` rows
on the same operand establish for their carriers and this one inherits.
-/

namespace A12Kernel.Conformance.KeyedStarNumberAggregate

open A12Kernel

private def code : FlatFieldDecl :=
  { id := 1, groupPath := ["Order", "Packages"], name := "Code", policy := { kind := .string }
    repeatableScope := [10] }

private def weight : FlatFieldDecl :=
  { id := 2, groupPath := ["Order", "Packages", "Items"], name := "Weight"
    policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10, 20] }

private def reference : FlatFieldDecl :=
  { id := 3, groupPath := ["Order"], name := "Reference", policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [code, weight, reference]
    repeatableGroups := [
      { level := 10, path := ["Order", "Packages"], repeatability := some 5, indexField := some 1 },
      { level := 20, path := ["Order", "Packages", "Items"], repeatability := some 3 }] }

private def segments (starred : List Bool) : List SurfaceStarGroupSegment :=
  (["Order", "Packages", "Items"].zip starred).map fun (name, starred) => { name, starred }

private def keyed (token : String) (starred : List Bool := [false, false, true]) :
    SurfaceKeyedStarNumberSource :=
  { target := { base := .absolute, groups := segments starred, field := "Weight" }, token }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def text (field : FieldId) (path : List Nat) (value : String) : ClassifiedCellInput :=
  { address := { field, path }, stored := value, raw := .parsed (.str value) }

private def number (field : FieldId) (path : List Nat) (value : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored := toString value, raw := .parsed (.num value)
    numericDecimal := some { unscaled := value, scale := 0 } }

/-- One package: its key and its item weights. -/
private def document (packages : List (String × List Int)) : Option (CheckedIndexPreliminary model) := do
  let indexed := packages.zipIdx.map fun (package, index) => (package, index + 1)
  let rows := indexed.flatMap fun ((_, weights), row) =>
    { group := 10, path := [row] } ::
      (List.range weights.length).map fun item => { group := 20, path := [row, item + 1] }
  let cells := indexed.flatMap fun ((key, weights), row) =>
    text code.id [row] key ::
      weights.zipIdx.map fun (value, item) => number weight.id [row, item + 1] value
  let checked ← (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption
  checked.applyFullIndexPreliminary.toOption

private def aggregate (op : NumericAggregateOp) (token : String)
    (packages : List (String × List Int)) : Option NumericOperand := do
  let source ← (elaborateKeyedStarNumberSource model ["Order"] (keyed token)).toOption
  (source.evaluateValidation op (← document packages)).toOption

private def standard : List (String × List Int) := [("P1", [2, 5]), ("P2", [])]

private def value (amount : Rat) (canGrow canShrink : Bool) : Option NumericOperand :=
  some (.value amount { canGrow, canShrink })

/- The measured rows: `P1`'s two item weights, summed and at both extremes. -/
example : [NumericAggregateOp.sum, .maximum, .minimum].map (aggregate · "P1" standard) =
    [value 7 true false, value 5 true false, value 2 false true] := by
  native_decide

/- The separating variant: with `P2` carrying items of its own, each key reads its own row's items
   only. A star over every package would give 17 for both. -/
example :
    let both := [("P1", [2, 5]), ("P2", [4, 6])]
    aggregate .sum "P1" both = value 7 true false ∧ aggregate .sum "P2" both = value 10 true false := by
  native_decide

/- The chosen account where no clean row carries the key, unmeasured on this carrier: a duplicated
   key reads UNKNOWN, and a key no row carries folds no cell, a fixed zero on every aggregate, where the
   key-only `P2` reads an empty star whose unfilled item capacity can still grow the sum. -/
example :
    aggregate .sum "P1" [("P1", [2, 5]), ("P1", [1])] = some (.unknown .duplicateIndex) ∧
    [NumericAggregateOp.sum, .maximum, .minimum].map (aggregate · "P3" standard) =
      [value 0 false false, value 0 false false, value 0 false false] ∧
    aggregate .sum "P2" standard = value 0 true true := by
  native_decide

/- The operand's three boundaries, each refused without a class: a star on the index group's own
   level, a Number index, whose keys compare numerically, and a chain with no index group. -/
example :
    let numberIndexed : FlatModel := { model with
      fields := [{ code with policy := { kind := .number { scale := 0, signed := false } } }, weight,
        reference] }
    let unindexed : FlatModel := { model with
      repeatableGroups := model.repeatableGroups.map ({ · with indexField := none }) }
    (match elaborateKeyedStarNumberSource model ["Order"] (keyed "P1" [false, true, true]) with
      | .error (.starNotDirectlyBelowIndexGroup _) => true
      | _ => false) &&
    (match elaborateKeyedStarNumberSource numberIndexed ["Order"] (keyed "P1") with
      | .error (.numberIndex _) => true
      | _ => false) &&
    (match elaborateKeyedStarNumberSource unindexed ["Order"] (keyed "P1") with
      | .error (.noIndexGroup _) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.KeyedStarNumberAggregate
