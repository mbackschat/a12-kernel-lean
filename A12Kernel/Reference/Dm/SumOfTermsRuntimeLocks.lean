import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! # `SumOfTerms` evaluation through the reader

Which rules fire over a document, and as VALUE or OMISSION, and what a computation assigns, for the
document tables of a12-dmkits' two `SumOfTerms` runtime tests, each read as the rules that fire and
the computed value ([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)).
A fired rule reads `code|V` or `code|O`, with `@n` for the repetition a per-row rule fired at. The
messages' referenced and fill-to-fix pointers and the partial-validation rows are not compared here.
-/

namespace A12Kernel.Dm.SumOfTermsRuntimeLocks

private def number (scale : Nat) : FieldKind := .number { scale, signed := true }

/-- The union of the two peer models: a policy with a claim list of four holding a nested list of
three, a vehicle list of two, an address and the target `Total`. -/
private def model : FlatModel := {
  fields := [
    { id := 1, name := "Holder", groupPath := ["Policy"], policy := { kind := .string } },
    { id := 2, name := "Total", groupPath := ["Policy"], policy := { kind := number 2 } },
    { id := 3, name := "Threshold", groupPath := ["Policy"], policy := { kind := number 2 } },
    { id := 4, name := "Zip", groupPath := ["Policy", "Address"], policy := { kind := number 0 } },
    { id := 5, name := "Value", groupPath := ["Policy", "Vehicles"], repeatableScope := [30], policy := { kind := number 0 } },
    { id := 6, name := "Status", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := .string } },
    { id := 7, name := "Amount", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := number 2 } },
    { id := 8, name := "Reserve", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := number 2 } },
    { id := 9, name := "Deductible", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := number 2 } },
    { id := 10, name := "Qty", groupPath := ["Policy", "Claims", "Parts"], repeatableScope := [10, 20], policy := { kind := number 0 } }]
  repeatableGroups := [
    { level := 10, path := ["Policy", "Claims"], repeatability := some 4 },
    { level := 20, path := ["Policy", "Claims", "Parts"], repeatability := some 3 },
    { level := 30, path := ["Policy", "Vehicles"], repeatability := some 2 }] }

private def world : World := { now := { epochMillis := 0 } }

private def dm : DmModel :=
  { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- One claim; an empty spelling leaves its field absent. -/
private structure Claim where
  status : String := ""
  amount : String := ""
  reserve : String := ""
  deductible : String := ""
  parts : List String := []

private def claim (amount reserve : String) (status : String := "") (parts : List String := []) : Claim :=
  { amount, reserve, status, parts }

open Lean in
private def claimJson (claim : Claim) : Json :=
  let field (name value : String) : List (String × Json) := if value.isEmpty then [] else [(name, .str value)]
  Json.mkObj (field "Status" claim.status ++ field "Amount" claim.amount ++ field "Reserve" claim.reserve ++
    field "Deductible" claim.deductible ++
    (if claim.parts.isEmpty then []
     else [("Parts", .arr (claim.parts.map (fun qty => Json.mkObj [("Qty", .str qty)])).toArray)]))

open Lean in
/-- A policy held by `Ada`; an empty spelling leaves a field or group absent. -/
private def policy (claims : List Claim) (total threshold zip : String := "") (vehicles : List String := []) : Json :=
  let field (name value : String) : List (String × Json) := if value.isEmpty then [] else [(name, .str value)]
  Json.mkObj [("Policy", Json.mkObj (field "Holder" "Ada" ++ field "Total" total ++ field "Threshold" threshold ++
    (if zip.isEmpty then [] else [("Address", Json.mkObj [("Zip", .str zip)])]) ++
    (if vehicles.isEmpty then []
     else [("Vehicles", .arr (vehicles.map (fun value => Json.mkObj [("Value", .str value)])).toArray)]) ++
    (if claims.isEmpty then [] else [("Claims", .arr (claims.map claimJson).toArray)])))]

private def checked (json : Lean.Json) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument dm json).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  pure (prepared, document)

/-- The rule set a table runs: code, error field path and condition, all at the policy root. -/
private abbrev Rules := List (String × String × String)

/-- The rules that fire over the document, in the order of the rule list. A rule the reader refuses or
a run that fails reads as its own entry, which no row expects. -/
private def fired (rules : Rules) (json : Lean.Json) : List String :=
  match checked json with
  | none => ["no document"]
  | some (_, document) => rules.flatMap fun (code, errorPath, condition) =>
    let rule : DmRule := {
      group := ["Policy"], name := code, errorCode := code,
      errorEntityRelPath := "../" ++ errorPath, condition := condition, severity := "ERROR" }
    match checkRule dm .english rule with
    | .error _ => [code ++ " refused"]
    | .ok rule =>
      match runRuleAt world document rule with
      | .error _ => [code ++ " failed"]
      | .ok rows => rows.map fun (environment, message) =>
          code ++ "|" ++ (match message.messageType with | .value => "V" | .omission => "O") ++
            ((environment.map fun (_, row) => "@" ++ toString row).foldl (· ++ ·) "")

/-- The values a computation of `Total` leaves, as the replay reports them. -/
private def computed (operation : String) (json : Lean.Json) : List String :=
  match checked json with
  | none => ["no document"]
  | some (prepared, document) =>
    let computation : DmComputation := {
      name := "TotalComp", group := ["Policy"], targetRelPath := "../Total",
      commonPrecondition := none, alternatives := [{ precondition := none, operation := operation }],
      errorCodesToSuppress := [] }
    match lowerComputation model .english computation with
    | .error _ => ["refused"]
    | .ok step =>
      match runComputations world prepared document [step.2] with
      | .error _ => ["failed"]
      | .ok outcomes => outcomes.map (·.outcome)

private def term := "SumOfTerms(Claims*, [Claims/Amount] + [Claims/Reserve])"

private def holder (condition : String) : String := "FieldFilled(Holder) And " ++ condition

/-- Whether every document of a table fires exactly the expected rules. -/
private def rulesHold (rules : Rules) (rows : List (Lean.Json × List String)) : Bool :=
  rows.all fun (json, expected) => fired rules json == expected

/-- Whether a computation leaves the expected values over every document of a table. -/
private def computedHold (operation : String) (rows : List (Lean.Json × List String)) : Bool :=
  rows.all fun (json, expected) => computed operation json == expected

/-- `SumOfTermsRuntimeLawsTest`'s rules: one term over several comparisons, a filtered entity, a
nested entity and a per-row rule. -/
private def lawRules : Rules := [
  ("GT", "Holder", holder (term ++ " > 100")),
  ("LT", "Holder", holder (term ++ " < 50")),
  ("EQ0", "Holder", holder "SumOfTerms(Claims*, [Claims/Amount]) == 0"),
  ("DIV", "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] / [Claims/Reserve]) > 1"),
  ("FILT", "Holder", holder "SumOfTerms(Claims* Having [Claims/Status] == \"open\", [Claims/Amount]) > 100"),
  ("NEST", "Holder", holder "SumOfTerms(Claims*/Parts*, [Claims/Parts/Qty]) > 5"),
  ("ROW", "Claims/Amount", "FieldFilled(Claims/Amount) And SumOfTerms(Claims/Parts*, [Claims/Parts/Qty]) > 5")]

private def full (amount reserve : String) (status : String := "") : List Claim :=
  (List.range 4).map fun _ => claim amount reserve status

-- Locked: a12-dmkits SumOfTermsRuntimeLawsTest at 1124b523f, kernel 31.1.1
-- (`aTermSumOverRowsComparesAndAssigns`). A firing is VALUE only when every declared row of the
-- entity is instantiated, passes the filter, is filled and has a term value. An empty read counts as
-- zero with its fillability, so its row still adds its other reads; a division by zero leaves the row
-- no term value and adds nothing, and keeps the firing OMISSION.
example : rulesHold lawRules [
    (policy [claim "30" "10", claim "50" "20"], ["GT|O", "DIV|O"]),
    (policy (full "30" "10"), ["GT|V", "DIV|V"]),
    (policy ((full "30" "10").take 3 ++ [claim "30" ""]), ["GT|O", "DIV|O"]),
    (policy ((full "30" "10").take 3 ++ [claim "50" "0"]), ["GT|V", "DIV|O"]),
    (policy (full "30" "0" "open"), ["GT|V", "FILT|V"]),
    (policy ((full "50" "0" "open").take 3 ++ [claim "50" "0" "closed"]), ["GT|V", "FILT|O"]),
    (policy ((List.range 4).map fun _ => claim "1" "0" (parts := ["1", "1", "1"])), ["LT|V", "NEST|V"]),
    (policy [], ["LT|O", "EQ0|O"]),
    (policy [claim "30" ""], ["LT|O"]),
    (policy [claim "30" "10", claim "abc" "20"], []),
    (policy [claim "30" "10", { amount := "50", reserve := "20", deductible := "abc" }], ["GT|O", "DIV|O"]),
    (policy [claim "30" "10", { status := "open" }], ["LT|O", "DIV|O"]),
    (policy [claim "30" "10", claim "50" "0"], ["DIV|O"]),
    (policy [claim "150" "0" "open", claim "10" "0" "closed"], ["GT|O", "FILT|O"]),
    (policy [claim "1" "0" (parts := ["2", "4"]), claim "1" "0" (parts := ["4"])],
      ["LT|O", "NEST|O", "ROW|O@1"])] = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsRuntimeLawsTest at 1124b523f, kernel 31.1.1 (`aComputedTermSum`).
-- Every document stores a total, so a cleared target differs from an unassigned one.
example : computedHold term [
    (policy [claim "30" "10", claim "50" "20.5"] (total := "5"), ["value 110.5"]),
    (policy [] (total := "5"), ["value 0"]),
    (policy [claim "30" "10", claim "abc" "20"] (total := "5"), ["cleared"])] = true := by
  native_decide

private def shapeTerm := "SumOfTerms(Claims*, [Claims/Amount] + NumberOfFilledFields(Vehicles*/Value))"

/-- `SumOfTermsShapesRuntimeLawsTest`'s rules: a count in the term and in the filter, an aggregate and
a non-repeatable read in the term, a `$` read in the filter, a filter reading a field the term does
not, and an error field inside the iteration group. -/
private def shapeRules : Rules := [
  ("CNT", "Holder", "FieldNotFilled(Holder) And " ++ shapeTerm ++ " < 2"),
  ("PLAIN", "Holder", "FieldNotFilled(Holder) And SumOfTerms(Claims*, [Claims/Amount]) < 2"),
  ("CNTF", "Holder", "FieldNotFilled(Holder) And SumOfTerms(Claims* Having NumberOfFilledFields(Vehicles*/Value) < [Claims/Amount], [Claims/Amount]) < 2"),
  ("UP", "Holder", holder (shapeTerm ++ " > 100")),
  ("AGG", "Holder", holder "SumOfTerms(Claims*, Sum(Claims/Parts*/Qty)) > 8"),
  ("ZIP", "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + [Address/Zip]) > 150"),
  ("OUT", "Holder", holder "SumOfTerms(Claims* Having [Claims/Amount] > [$Threshold], [Claims/Amount]) > 175"),
  ("OUTX", "Holder", holder "SumOfTerms(Claims* Having [Claims/Amount] > [$Threshold], [Claims/Amount]) > 185"),
  ("DED", "Holder", holder "SumOfTerms(Claims* Having [Claims/Deductible] > 0, [Claims/Amount]) > 100"),
  ("DEDK", "Holder", holder "SumOfTerms(Claims* Having [Claims/Deductible] > 0, [Claims/Amount]) > 155"),
  ("GT", "Holder", holder (term ++ " > 100")),
  ("INROW", "Claims/Status", "SumOfTerms(Claims*, [Claims/Amount]) > 100"),
  ("ROW", "Claims/Amount", "FieldFilled(Claims/Amount) And SumOfTerms(Claims/Parts*, [Claims/Parts/Qty]) > 5")]

private def emptyRoot : Lean.Json := Lean.Json.mkObj [("Policy", Lean.Json.mkObj [])]

private def shapeDocuments : List (Lean.Json × List String × List String) := [
  (emptyRoot, ["CNT|O"], ["value 0"]),
  (policy [claim "1" "" (parts := ["2", "2", "2"])], ["ROW|V@1"], ["value 1"]),
  (policy [claim "1" "" (parts := ["4", "3"]), claim "1" "" (parts := ["4"])], ["AGG|O", "ROW|O@1"], ["value 2"]),
  (policy [claim "30" "", claim "40" ""] (zip := "50"), ["ZIP|O"], ["value 70"]),
  (policy [claim "30" "", claim "150" "", claim "10" ""] (threshold := "20"),
    ["UP|O", "ZIP|O", "OUT|O", "GT|O", "INROW|O@1"], ["value 190"]),
  (policy [claim "150" "" "open", claim "10" "" "x"], ["UP|O", "ZIP|O", "GT|O", "INROW|O@1"], ["value 160"]),
  (policy [claim "120" "10", { deductible := "abc" }], ["UP|O", "GT|O", "INROW|O@1"], ["value 130"]),
  (policy [{ amount := "150", deductible := "1" }, { amount := "10", deductible := "abc" }],
    ["UP|O", "ZIP|O", "DED|O", "GT|O", "INROW|O@1"], ["value 160"]),
  (policy [claim "30" "10", claim "abc" "20"], [], []),
  (policy [claim "150" ""] (vehicles := ["7"]), ["UP|O", "GT|O", "INROW|O@1"], ["value 150"]),
  (policy ((List.range 5).map fun _ => claim "30" "0"), ["UP|V", "GT|V", "INROW|V@1"], ["value 120"])]

-- Locked: a12-dmkits SumOfTermsShapesRuntimeLawsTest at 1124b523f, kernel 31.1.1 (`whatGroovyReports`,
-- the rules' types and the computation's outcome per document). A count in the term lifts the empty-root
-- gate on its small side (`CNT` against `PLAIN`); a count beside a filled amount leaves a sum only
-- growing, which a lower bound keeps VALUE (`UP` over five claims). The fifth claim beyond the capacity
-- of four is no row of the sum.
example : shapeDocuments.all (fun (json, rules, _) => fired shapeRules json == rules) = true := by
  native_decide

example : shapeDocuments.all (fun (json, _, outcomes) => computed term json == outcomes) = true := by
  native_decide

end A12Kernel.Dm.SumOfTermsRuntimeLocks
