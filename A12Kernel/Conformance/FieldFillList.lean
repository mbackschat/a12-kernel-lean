import A12Kernel.Elaboration.FieldFillList

/-! # Field-fill list conformance

A field-fill list concatenates its operands' observations, so the count and the quantifiers read one
stream while keeping their own rules for an invalid cell, and a starred field contributes its declared
slots to the declared-range quantifiers. The fixture is the model of the
[negation pair grid](../../evidence/kernel-30.8.1/captures/negation-pair-grid-2026-10-02/request.json):
three direct Number fields and one Number field in a `max 2` repeatable group.
-/

namespace A12Kernel

private def listModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe"], name := "A", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 2, groupPath := ["Probe"], name := "B", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, groupPath := ["Probe"], name := "C", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 4, groupPath := ["Probe", "Rows"], name := "R",
        policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [4] }]
    repeatableGroups := [{ level := 4, path := ["Probe", "Rows"], repeatability := some 2 }] }

private def listPrepared : PreparedFlatStringContext listModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler listModel).toOption.get (by native_decide)

private def direct (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }

private def directList : SurfaceFieldEntitySource :=
  { first := direct "A", rest := [direct "B", direct "C"] }

private def starredR : SurfaceFieldEntitySource :=
  { first := .star { base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "R" },
    rest := [] }

private def cell (field : FieldId) (path : List Nat) (value : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored := toString value, raw := .parsed (.num value) }

/-- A Number cell whose text no Number reading admits. -/
private def invalid (field : FieldId) (path : List Nat) : ClassifiedCellInput :=
  { address := { field, path }, stored := "x", raw := .rejected .malformed }

private def document? (rows : List RowAddr) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument listModel) :=
  (checkDocument listPrepared "en_US" { instantiatedRows := rows, cells }).toOption

private def fill (source : SurfaceFieldEntitySource) (operator : FieldFillQuantifier)
    (rows : List RowAddr) (cells : List ClassifiedCellInput) : Option ValidationFillOutcome := do
  let list ← (elaborateFieldFillList listModel ["Probe"] source).toOption
  (list.evaluateFill? operator (← document? rows cells) []).toOption.join

private def count (source : SurfaceFieldEntitySource) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let list ← (elaborateFieldFillList listModel ["Probe"] source).toOption
  (list.evaluateCountOperand? (← document? rows cells) []).toOption.join

/- One invalid cell beside one filled sibling: `AtLeastOneFieldFilled(A, B, C)` fires with VALUE while
the count over the same list is unavailable, so `NumberOfFilledFields(A, B, C) == 1` stays silent. A
count that skipped the invalid cell would read 1 and fire. The Kernel reports exactly this on the
grid's `invalid-one-filled` row. -/
example :
    fill directList .atLeastOneFieldFilled [] [invalid 1 [], cell 2 [] 7] = some (.fired .value) ∧
    count directList [] [invalid 1 [], cell 2 [] 7] = none := by
  native_decide

/- With no row instantiated, the starred field's two declared slots are the missing tail, so
`NotAllFieldsFilled(Rows*/R)` fires with OMISSION and `AllFieldsFilled(Rows*/R)` does not, as on the
grid's `rows-none-a` row. Reading only instantiated rows would make the list empty and vacuously
all-filled. -/
example :
    fill starredR .notAllFieldsFilled [] [] = some (.fired .omission) ∧
    fill starredR .allFieldsFilled [] [] = some .falseOrUnknown := by
  native_decide

end A12Kernel
