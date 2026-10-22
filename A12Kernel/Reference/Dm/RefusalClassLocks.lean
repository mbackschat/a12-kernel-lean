import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute

/-! # The Kernel class a reader refusal leads with

Rule-level and computation-level rows the a12-dmkits response of 2026-10-18 measured on its own order
model, a repeatable `Items` with the Numbers `Count` and `UnitWeight` beside a String `Code`
([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18)), and two bracketed
temporal operands this project measured
([checkpoint](../../../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year),
[checkpoint](../../../docs/sources/temporal-and-message-probes.md#src-date-from-datetime)). Each refusal
must lead with the operator's own class, which the rule-check projection compares on retained
captures only. -/

namespace A12Kernel.Dm.RefusalClassLocks

open A12Kernel

private def number (id : Nat) (group : List String) (name : String) : FlatFieldDecl :=
  { id, groupPath := group, name, repeatableScope := if group.length > 1 then [10] else [],
    policy := { kind := .number { scale := 0, signed := true } } }

private def model : DmModel := {
  flat := {
    fields := [
      { id := 1, groupPath := ["Order"], name := "Code", policy := { kind := .string } },
      number 2 ["Order", "Items"] "Count", number 3 ["Order", "Items"] "UnitWeight",
      number 4 ["Order", "Items"] "StockQty", number 5 ["Order"] "Quantity", number 6 ["Order"] "UnitPrice",
      number 7 ["Order"] "LineTotal",
      { id := 8, groupPath := ["Order"], name := "Due", policy := { kind := .temporal .date .fullDate } },
      { id := 9, groupPath := ["Order"], name := "Signed", policy := { kind := .temporal .date .fullDate } },
      { id := 10, groupPath := ["Order"], name := "Moment", policy := { kind := .temporal .dateTime .now } }]
    repeatableGroups := [{ level := 10, path := ["Order", "Items"], repeatability := some 5 }] }
  rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def classOfRefusal : Lowering α → String
  | .ok _ => "admitted"
  | .error refusal => (refusal.kernelClass?).getD s!"unclassed {refusal.construct}"

/-- The class a rule's refusal leads with, `"admitted"` for an admitted rule. -/
private def classOf (group : List String) (target condition : String) : String :=
  let rule : DmRule :=
    { group, name := "R", errorCode := "R", errorEntityRelPath := target, condition, severity := "ERROR" }
  classOfRefusal (checkRule model .english rule)

/-- The class a one-alternative Number computation's refusal leads with. -/
private def computationClassOf (group : List String) (target operation : String) : String :=
  let computation : DmComputation := {
    group, name := "C", targetRelPath := target, commonPrecondition := none,
    alternatives := [{ operation, precondition := none }], errorCodesToSuppress := [] }
  classOfRefusal (lowerComputation model.flat .english computation)

/- An unstarred operand on a level the rule binds, by its error field or its declaring group, draws
the lowest-star class; an error field outside `Items` leaves the missing star. -/
example :
    classOf ["Order"] "../Items/Count" "SumOfProducts(Items/Count, Items*/UnitWeight) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order"] "../Items/Count" "SumOfProducts(Items*/UnitWeight, Items/Count) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order"] "../Items/Count" "SumOfProducts(Items/Count, Items/UnitWeight) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order", "Items"] "../Count" "SumOfProducts(Count, /Order/Items*/UnitWeight) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order", "Items"] "../Count" "SumOfProducts(Count, UnitWeight) > 0" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      classOf ["Order"] "../Code" "SumOfProducts(Items/Count, Items*/UnitWeight) > 0" =
        "MVK_NO_WILDCARD" ∧
      classOf ["Order"] "../Items/Count" "SumOfProducts(Items*/Count, Items*/UnitWeight) > 0" =
        "admitted" ∧
      classOf ["Order", "Items"] "../Count"
          "SumOfProducts(/Order/Items*/Count, /Order/Items*/UnitWeight) > 0" = "admitted" := by
  native_decide

/- The pair's other gates keep their classes beside a bound level: owning groups that differ, and a
pair with no repeatable level reporting on a fixed field. -/
example :
    classOf ["Order"] "../Items/Count" "SumOfProducts(Items/Count, Quantity) > 0" = "MVK_DIFFERENT_GROUPS" ∧
      classOf ["Order"] "../Quantity" "SumOfProducts(Quantity, UnitPrice) > 0" =
        "MVK_REPEATABLE_LEVEL_REQUIRED" := by
  native_decide

/- A computation target binds the level as an error field does: inside `Items`, declared at the root
or in `Items`, the lowest-star class; at `/Order/LineTotal`, the missing star. -/
example :
    computationClassOf ["Order"] "../Items/StockQty" "SumOfProducts(Items/Count, Items*/UnitWeight)" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      computationClassOf ["Order", "Items"] "../StockQty" "SumOfProducts(Count, /Order/Items*/UnitWeight)" =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      computationClassOf ["Order"] "../LineTotal" "SumOfProducts(Items/Count, Items*/UnitWeight)" =
        "MVK_NO_WILDCARD" := by
  native_decide

/- An error field that resolves to nothing binds no level, so the lexical attempt's missing star stands
rather than the error field's own refusal. Which of the two the Kernel leads with is unmeasured; this
locks the chosen account. -/
example : classOf ["Order"] "../Items/Nope" "[Items/Count] > 0" = "MVK_NO_WILDCARD" := by
  native_decide

/- Validity takes a field and one type name, so a third operand is a token defect where the
two-operand form is admitted. -/
example :
    classOf ["Order"] "../Code" "Valid(Code, \"EMail\", \"IBAN\")" = "MVK_UNEXPECTED_TOKEN" ∧
      classOf ["Order"] "../Code" "Invalid(Code, \"EMail\", \"IBAN\")" = "MVK_UNEXPECTED_TOKEN" ∧
      classOf ["Order"] "../Code" "Valid(Code, \"EMail\")" = "admitted" := by
  native_decide

/- A temporal source slot takes a bare path, so a bracket there is a token defect beside the admitted
bare spelling. -/
example :
    classOf ["Order"] "../Due" "DifferenceInDays([/Order/Due], Signed) > 1" = "MVK_UNEXPECTED_TOKEN" ∧
      classOf ["Order"] "../Due" "DifferenceInDays(Due, Signed) > 1" = "admitted" ∧
      classOf ["Order"] "../Due" "DateFromDateTime([Moment]) == [Due]" = "MVK_UNEXPECTED_TOKEN" ∧
      classOf ["Order"] "../Due" "DateFromDateTime(Moment) == [Due]" = "admitted" := by
  native_decide

end A12Kernel.Dm.RefusalClassLocks
