import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! # Group guards through nested row scheduling

Group content keeps each parent's row binding and consumes fresh producer results independently of
the target kind. Malformed stored members are content; failed computed members are not (spec/09).
-/

namespace A12Kernel.Dm.GroupGuardLocks

private inductive TargetKind where
  | number | string | boolean | confirm

private def run (condition : String) (kind : TargetKind) (producer : Bool := false) : Option String := do
  let group := ["Form", "Batches", "Rows"]
  let number : FieldKind := .number { scale := 0, signed := true }
  let targetKind : FieldKind := match kind with
    | .number => number | .string => .string | .boolean => .boolean | .confirm => .confirm
  let model : FlatModel := {
    fields := [
      { id := 1, groupPath := group ++ ["Box"], name := "Gate", repeatableScope := [10,20], policy := { kind := number } },
      { id := 2, groupPath := group ++ ["Spare"], name := "Gate", repeatableScope := [10,20], policy := { kind := .boolean } },
      { id := 3, groupPath := group, name := "Out", repeatableScope := [10,20], policy := { kind := targetKind } },
      { id := 4, groupPath := group, name := "After", repeatableScope := [10,20], policy := { kind := number } }]
    repeatableGroups := [
      { level := 10, path := ["Form", "Batches"], repeatability := some 2 },
      { level := 20, path := group, repeatability := some 2 }] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let row (box spare : String) := Lean.Json.mkObj [
    ("Box", .mkObj [("Gate", .str box)]), ("Spare", .mkObj [("Gate", .str spare)]), ("Out", .str "bad"), ("After", .str "99")]
  let data := Lean.Json.mkObj [("Form", .mkObj [("Batches", .arr #[
    .mkObj [("Rows", .arr #[row "" "true"])], .mkObj [("Rows", .arr #[row "bad" ""])]] )])]
  let input ← (readDocument dm data).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let consumer : DmComputation := {
    name := "Consumer", group := ["Form"], targetRelPath := "../Batches/Rows/Out"
    commonPrecondition := some condition
    alternatives := [{ precondition := none, operation := match kind with
      | .number => "1" | .string => "\"x\"" | .boolean | .confirm => "True" }], errorCodesToSuppress := [] }
  let after : DmComputation := {
    name := "After", group := ["Form"], targetRelPath := "../Batches/Rows/After"
    commonPrecondition := some "FieldFilled(Batches/Rows/Out) Or FieldNotFilled(Batches/Rows/Out)"
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
  let producerDefinition : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Batches/Rows/Box/Gate"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
  let steps ← ([after, consumer] ++ if producer then [producerDefinition] else []).mapM fun computation =>
    (lowerComputation model .english computation).toOption
  let results ← (runComputations world prepared checked (steps.map (·.2))).toOption
  let signature (suffix : String) := String.ofList ((results.filter (·.pointer.endsWith suffix)).map fun result =>
    if result.outcome == "cleared" then 'F' else if result.outcome.startsWith "value " then 'T' else '?')
  pure (signature "/Out" ++ "/" ++ signature "/After")

private def box := "Batches/Rows/Box"
private def spare := "Batches/Rows/Spare"
private def conditions := ["GroupFilled(" ++ box ++ ")", "GroupNotFilled(" ++ box ++ ")"] ++
  ["AllGroupsFilled", "NoGroupFilled", "AtLeastOneGroupFilled", "NotAllGroupsFilled", "GroupsNotCollectivelyFilled"].map
    (fun op => op ++ "(" ++ box ++ "," ++ spare ++ ")")

example : [TargetKind.number, .string, .boolean, .confirm].all (fun kind =>
    conditions.mapM (fun condition => run condition kind) ==
      some ["FT/TT", "TF/TT", "FF/TT", "FF/TT", "TT/TT", "TT/TT", "TT/TT"]) = true := by native_decide

example : [TargetKind.number, .string, .boolean, .confirm].all (fun kind =>
    run ("GroupFilled(" ++ box ++ ")") kind true == some "TT/TT") = true := by native_decide

example : [TargetKind.number, .string, .boolean, .confirm].all (fun kind =>
    run "GroupFilled(Batches/Rows)" kind == some "TT/TT" &&
    run "GroupNotFilled(Batches/Rows)" kind == none &&
    run "FieldFilled(Batches/Rows/Out)" kind == none) = true := by native_decide

example : [TargetKind.boolean, .confirm].all (fun kind =>
    run "FieldFilled(Batches/Rows/Box/Gate)" kind == some "FF/TF" &&
    run "GroupFilled(Batches/Rows/Box) Or FieldFilled(Batches/Rows/Box/Gate)" kind == some "FT/TT") = true := by native_decide

end A12Kernel.Dm.GroupGuardLocks
