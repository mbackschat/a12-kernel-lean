import A12Kernel.Reference.Dm.Validate

/-! # The Kernel class a reader refusal leads with

Rule-level rows the a12-dmkits response of 2026-10-18 measured on its own order model, a repeatable
`Items` with the Numbers `Count` and `UnitWeight` beside a String `Code`
([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18)). Each refusal must lead with the
operator's own class, which the rule-check projection compares on retained captures only. -/

namespace A12Kernel.Dm.RefusalClassLocks

open A12Kernel

private def model : DmModel := {
  flat := {
    fields := [
      { id := 1, groupPath := ["Order"], name := "Code", policy := { kind := .string } },
      { id := 2, groupPath := ["Order", "Items"], name := "Count", repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, groupPath := ["Order", "Items"], name := "UnitWeight", repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Order", "Items"], repeatability := some 5 }] }
  rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- The class a rule's refusal leads with, `"admitted"` for an admitted rule. -/
private def classOf (group : List String) (target condition : String) : String :=
  let rule : DmRule :=
    { group, name := "R", errorCode := "R", errorEntityRelPath := target, condition, severity := "ERROR" }
  match checkRule model .english rule with
  | .ok _ => "admitted"
  | .error refusal => (refusal.kernelClass?).getD s!"unclassed {refusal.construct}"

/- An unstarred operand on a level the rule binds, by its error field or its declaring group, draws
the lowest-star class; an error field outside `Items` leaves the missing star. -/
example :
    classOf ["Order"] "../Items/Count" "SumOfProducts(Items/Count, Items*/UnitWeight) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order"] "../Items/Count" "SumOfProducts(Items/Count, Items/UnitWeight) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order", "Items"] "../Count" "SumOfProducts(Count, UnitWeight) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order"] "../Code" "SumOfProducts(Items/Count, Items*/UnitWeight) > 0" =
        "MVK_NO_WILDCARD" ∧
      classOf ["Order"] "../Items/Count" "SumOfProducts(Items*/Count, Items*/UnitWeight) > 0" =
        "admitted" := by
  native_decide

/- Validity takes a field and one type name, so a third operand is a token defect where the
two-operand form is admitted. -/
example :
    classOf ["Order"] "../Code" "Valid(Code, \"EMail\", \"IBAN\")" = "MVK_UNEXPECTED_TOKEN" ∧
      classOf ["Order"] "../Code" "Invalid(Code, \"EMail\", \"IBAN\")" = "MVK_UNEXPECTED_TOKEN" ∧
      classOf ["Order"] "../Code" "Valid(Code, \"EMail\")" = "admitted" := by
  native_decide

end A12Kernel.Dm.RefusalClassLocks
