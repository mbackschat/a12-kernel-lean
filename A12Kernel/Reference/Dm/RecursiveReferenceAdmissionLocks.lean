import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.RecursiveReferenceAdmissionLocks
open A12Kernel

private def ordinaryAdmissions (body : String) : Bool × Bool :=
  let model := HavingFixture.model
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let condition := "FieldFilled(Error) And " ++ body
  ((checkRule dm .english {
    group := ["Form"], name := "Read", errorCode := "READ", errorEntityRelPath := "../Error",
    condition, severity := "ERROR" }).isOk,
   (lowerComputation model .english {
    group := ["Form"], name := "Read", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := some condition, operation := "1" }], errorCodesToSuppress := [] }).isOk)

example : ["[Expected] == \"keep\"", "\"keep\" == [Expected]", "[Expected] == [Error]"].all
    (fun body => ordinaryAdmissions body == (true, true)) = true := by native_decide

example : [
    "[Expected Having FieldFilled(Error)] == \"keep\"",
    "\"keep\" == [Expected Having FieldFilled(Error)]",
    "[Expected] == [Error Having FieldFilled(Expected)]",
    "[Expected Having FieldFilled(Error)] == [Error]"].all
    (fun body => ordinaryAdmissions body == (false, false)) = true := by native_decide

example : HavingFixture.admissions HavingFixture.model "FieldFilled(Rows/N)" = (true, true) ∧
    HavingFixture.admissions HavingFixture.model "[Rows/Tag] == \"keep\"" = (true, true) := by native_decide

example : [
    "FieldFilled(Rows/N Having [Rows/N] > 0)",
    "[Rows/N Having [Rows/N] > 0] > 0",
    "[Rows/Tag Having [Rows/N] > 0] == \"keep\"",
    "Abs(Rows/N Having [Rows/N] > 0) > 0",
    "FieldValueAsString(Rows/Tag Having [Rows/N] > 0) == \"keep\""].all
    (fun body => HavingFixture.admissions HavingFixture.model body == (false, false)) = true := by native_decide

private def indexed : FlatModel := { HavingFixture.model with
  repeatableGroups := HavingFixture.model.repeatableGroups.map fun group => { group with indexField := some 3 } }

private def run (operation : String) :=
  HavingFixture.runModel indexed "FieldFilled(Rows/N)" false "drop" "keep" "drop"
    (extra := [("Out", .str "99")])
    (rowsOverride := some #[Lean.Json.mkObj [("Tag", .str "drop"), ("N", .str "5")]])
    (operationOverride := some operation) (ruleExpected := "5")

example : indexed.validate.isOk = true ∧
    run "[Rows/N For \"drop\"]" = some (.fired .value, ["value 5"]) ∧
    run "[Rows/N For Expected]" = some (.fired .value, ["value 5"]) := by native_decide

example : [
    "[Rows/N For Expected Having [Rows/N] > 0]",
    "[Rows/N For Expected -> Label]",
    "[Rows/N For Expected For \"drop\"]"].all (fun source => (run source).isNone) = true := by native_decide

end A12Kernel.Dm.RecursiveReferenceAdmissionLocks
