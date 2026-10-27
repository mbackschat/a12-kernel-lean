import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.ParallelValidation

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
  classOfRefusal (checkComputation model .english computation)

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

/-! ### A `-1` maximum is an unknown static scale

One premium form declares `Rate` and `Rate2` as Number `(minFractionalDigits 2, maxFractionalDigits -1)`,
`Fee` as `(2, 2)` and `MinOpen` as `(-1, 2)`; the rows replay the rule and computation checks of
`CheckerUnknownMaximumScaleAgreementTest` at a12-dmkits `fecf8552`
([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27)). `Whole` is `(0, -1)`:
its exponent row is no Kernel row but the same gate applied to a scale that is exactly zero unless
unknown, so it is the only exponent row that separates the unknown scale from the minimum. -/

private def scaleNumber (id : Nat) (name : String) (scale : Nat) (unknownScale : Bool := false) :
    FlatFieldDecl :=
  { id, groupPath := ["Premium"], name,
    policy := { kind := .number { scale, signed := true, staticScaleUnknown := unknownScale } } }

/-- `unknownScale := false` is the twin whose `Rate`, `Rate2` and `Whole` keep an ordinary pair with
the same minimum, so only the unknown scale separates the two models. -/
private def scaleModel (unknownScale : Bool) : DmModel := {
  flat := { fields := [scaleNumber 1 "Count" 0, scaleNumber 2 "Rate" 2 unknownScale,
    scaleNumber 3 "Rate2" 2 unknownScale, scaleNumber 4 "Fee" 2, scaleNumber 5 "MinOpen" 2,
    scaleNumber 6 "Whole" 0 unknownScale] }
  rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- The class the rule-check route leads with for a rule reporting on `target`. -/
private def scaleRuleClass (dm : DmModel) (target condition : String) : String :=
  classOfRefusal (checkValidationRule dm .english
    { group := ["Premium"], name := "R", errorCode := "R", errorEntityRelPath := "../" ++ target,
      condition, severity := "ERROR" })

/-- The class a one-alternative Number computation into `target` leads with. -/
private def scaleComputationClass (dm : DmModel) (target operation : String) : String :=
  classOfRefusal (checkComputation dm .english
    { group := ["Premium"], name := "C", targetRelPath := "../" ++ target, commonPrecondition := none
      alternatives := [{ operation, precondition := none }], errorCodesToSuppress := [] })

private def decimalPlaces : String := "MVK_INVALID_COMPARE_DEC_PLACES"

/- Equality and inequality refuse on an unknown scale, even a field against itself; ordering is
scale-exempt and a `-1` minimum is an ordinary exact scale. -/
example :
    scaleRuleClass (scaleModel true) "Rate" "[Rate] == [Rate]" = decimalPlaces ∧
      scaleRuleClass (scaleModel true) "Rate" "[Rate] == [Rate2]" = decimalPlaces ∧
      scaleRuleClass (scaleModel true) "Rate" "[Rate] != [Fee]" = decimalPlaces ∧
      scaleRuleClass (scaleModel true) "Rate" "[Rate] > [Fee]" = "admitted" ∧
      scaleRuleClass (scaleModel true) "Fee" "[MinOpen] == [Fee]" = "admitted" := by
  native_decide

/- The twin without the `-1` maximum admits the same equalities, so the unknown scale is their cause. -/
example :
    scaleRuleClass (scaleModel false) "Rate" "[Rate] == [Rate]" = "admitted" ∧
      scaleRuleClass (scaleModel false) "Rate" "[Rate] == [Rate2]" = "admitted" ∧
      scaleRuleClass (scaleModel false) "Rate" "[Rate] != [Fee]" = "admitted" := by
  native_decide

/- A computation refuses an unknown scale as source and as target, and an explicit rounding to the
target's places fixes the scale. -/
example :
    scaleComputationClass (scaleModel true) "Fee" "[Rate]" = decimalPlaces ∧
      scaleComputationClass (scaleModel true) "Rate" "[Fee]" = decimalPlaces ∧
      scaleComputationClass (scaleModel true) "Fee" "RoundAccounting([Rate], 2)" = "admitted" ∧
      scaleComputationClass (scaleModel false) "Fee" "[Rate]" = "admitted" ∧
      scaleComputationClass (scaleModel false) "Rate" "[Fee]" = "admitted" := by
  native_decide

/- An exponent with an unknown scale is refused with the exponent class. -/
example :
    scaleComputationClass (scaleModel true) "Fee" "[Count] ^ [Rate]" = "MVK_INVALID_NUMBER_FOR_EXP" ∧
      scaleRuleClass (scaleModel true) "Rate" "[Count] ^ [Rate] > 1" = "MVK_INVALID_NUMBER_FOR_EXP" ∧
      scaleComputationClass (scaleModel true) "Fee" "[Count] ^ [Whole]" = "MVK_INVALID_NUMBER_FOR_EXP" ∧
      scaleRuleClass (scaleModel true) "Whole" "[Count] ^ [Whole] > 1" = "MVK_INVALID_NUMBER_FOR_EXP" ∧
      scaleRuleClass (scaleModel false) "Whole" "[Count] ^ [Whole] > 1" = "admitted" := by
  native_decide

end A12Kernel.Dm.RefusalClassLocks
