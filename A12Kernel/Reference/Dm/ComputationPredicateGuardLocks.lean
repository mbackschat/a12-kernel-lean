import A12Kernel.Reference.Dm.Compute

/-! # Computation predicate guard composition

The reader and scheduler must preserve target binding and phase-specific reads after a predicate
is admitted. Malformed seeds separate fresh computed overlays from immutable source reads.
-/

namespace A12Kernel.Dm.ComputationPredicateGuardLocks

private def model (kind : FieldKind := .boolean) : FlatModel := {
  fields := [
    { id := 1, name := "Flag", groupPath := ["Form"], policy := { kind } },
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "A", groupPath := ["Form", "Left"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "B", groupPath := ["Form", "Right"], policy := { kind := .number { scale := 0, signed := true } } }] }

private def run (guard : String) (kind : FieldKind) (flag : RawCell)
    (left right : RawCell := .empty) (producer : Bool := false)
    (producerOperation : String := "True") : Option (List String) := do
  let model := model kind
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let cell (id : FieldId) (raw : RawCell) : Option ClassifiedCellInput :=
    match raw with
    | .empty => none
    | raw =>
        let stored := match raw with
          | .parsed (.num value) => toString value.num
          | .parsed (.bool value) | .parsed (.conf value) => if value then "true" else "false"
          | .parsed (.str value) | .parsed (.enum value) => value
          | .presentEmpty => ""
          | _ => "bad"
        some { address := { field := id, path := [] }, raw, stored }
  let input ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := ([cell 1 flag, cell 2 (.parsed (.num 9)), cell 3 left, cell 4 right].filterMap id) }).toOption
  let consumer : DmComputation := {
    name := "Consumer", group := ["Form"], targetRelPath := "../Out"
    commonPrecondition := some guard, alternatives := [{ precondition := none, operation := "2" }]
    errorCodesToSuppress := [] }
  let produce : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Flag"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := producerOperation }]
    errorCodesToSuppress := [] }
  let authored := [consumer] ++ if producer then [produce] else []
  let lowered ← authored.mapM fun definition => (lowerComputation model .english definition).toOption
  let results ← (runComputations world prepared input (lowered.map (·.2))).toOption
  pure (results.map (·.outcome))


example : run "[Flag] != True" .boolean .empty = some ["cleared"] ∧
    run "[Flag] != True" .confirm .empty = some ["value 2"] ∧
    run "[Flag] == False" .confirm .empty = none := by native_decide

example : run "[Flag] == True" .boolean (.rejected .booleanToken) .empty .empty true =
    some ["value true", "value 2"] := by native_decide

example :
    ["AllGroupsFilled", "NoGroupFilled", "AtLeastOneGroupFilled", "NotAllGroupsFilled", "GroupsNotCollectivelyFilled"].map
      (fun name => run (name ++ "(Left, Right)") .boolean .empty .empty (.rejected .malformed)) =
      [some ["cleared"], some ["cleared"], some ["value 2"], some ["value 2"], some ["value 2"]] := by
  native_decide

example : run "AtLeastOneGroupFilled(Left/A, Right)" .boolean .empty (.rejected .malformed)
    (.parsed (.num 1)) = some ["cleared"] ∧
    run "AtLeastOneGroupFilled(Right, Left/A)" .boolean .empty (.rejected .malformed)
      (.parsed (.num 1)) = some ["value 2"] := by native_decide

private def numericKind : FieldKind := .number { scale := 0, signed := true }

example : run "AtLeastOneFieldValueIncludedInValueList(Left/A, Right/B In Flag)" numericKind
    (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["value 2"] ∧
    run "AtLeastOneFieldValueIncludedInValueList(Right/B, Left/A In Flag)" numericKind
      (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["cleared"] := by native_decide

example : run "NoFieldValueIncludedInValueList(Left/A, Right/B In Flag)" numericKind
    (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["cleared"] ∧
    run "NotAllFieldValuesIncludedInValueList(Left/A, Right/B In Flag)" numericKind
      (.parsed (.num 9)) (.parsed (.num 1)) (.rejected .malformed) = some ["value 2"] := by native_decide

example : run "AtLeastOneFieldValueIncludedInValueList(Left/A In Flag)" numericKind
    (.rejected .malformed) (.parsed (.num 1)) .empty true "1" = some ["value 1", "value 2"] := by
  native_decide

/-- Scalar membership is calibrated on the same family grid as plural membership, but keeps
its eager member reads even with an empty subject. -/
example : run "FieldValueIncludedInValueList(Flag, 1, 2)" numericKind (.parsed (.num 1)) =
    some ["value 2"] ∧
    run "FieldValueNotIncludedInValueList(Flag, 1, 2)" numericKind (.parsed (.num 3)) =
      some ["value 2"] ∧
    run "FieldValueIncludedInValueList(Flag, [Left/A], [Right/B])" numericKind
      (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["cleared"] ∧
    run "FieldValueNotIncludedInValueList(Flag, [Left/A])" numericKind
      .empty (.rejected .malformed) = some ["cleared"] ∧
    run "FieldValueIncludedInValueList(Flag, \"x\", \"y\")" .string (.parsed (.str "x")) =
      some ["value 2"] := by native_decide

example : run "FieldValueIncludedInValueList([Flag], 1)" numericKind (.parsed (.num 1)) = none ∧
    run "FieldValueIncludedInValueList(Flag, Left/A)" numericKind (.parsed (.num 1)) = none ∧
    run "FieldValueIncludedInValueList(Flag, 1.0)" numericKind (.parsed (.num 1)) = none ∧
    run "FieldValueIncludedInValueList(Flag, [Flag])" numericKind (.parsed (.num 1)) = none := by
  native_decide

end A12Kernel.Dm.ComputationPredicateGuardLocks
