import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Replay

/-! # `SumOfTerms` evaluation through the reader

Which rules fire over a document, and as VALUE or OMISSION, and what a computation assigns, for the
document tables of a12-dmkits' two `SumOfTerms` runtime tests, each read as the rules that fire and
the computed value ([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)).
A fired rule reads `code|V` or `code|O`, with `@n` for the repetition a per-row rule fired at. The
messages' referenced and fill-to-fix pointers are read per fired rule too, each channel sorted as the
peer sorts it, and a partial-validation call reads the rules it fires over a relevance set.
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

/-- The checked document of a JSON one, `adjust` reshaping the read data first. -/
private def checkedWith (adjust : DocumentData → DocumentData) (json : Lean.Json) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument dm json).toOption
  let document ← (checkDocument prepared "en_US" (adjust data.data)).toOption
  pure (prepared, document)

private def checked (json : Lean.Json) := checkedWith id json

/-- The rule set a table runs: code, error field path and condition, all at the policy root. -/
private abbrev Rules := List (String × String × String)

private def dmRule (code errorPath condition : String) : DmRule :=
  { group := ["Policy"], name := code, errorCode := code,
    errorEntityRelPath := "../" ++ errorPath, condition := condition, severity := "ERROR" }

/-- One entry per message the rules fire over the document, in the order of the rule list, as `describe`
reads the rule's code, its checked form, the environment it fired at and the message. A rule the reader
refuses or a run that fails reads as its own entry, which no row expects. -/
private def firings (rules : Rules) (json : Lean.Json)
    (describe : String → CheckedResolvedValidationRule model → Env → FlatRuleMessage → String) :
    List String :=
  match checked json with
  | none => ["no document"]
  | some (_, document) => rules.flatMap fun (code, errorPath, condition) =>
    match checkRule dm .english (dmRule code errorPath condition) with
    | .error _ => [code ++ " refused"]
    | .ok rule =>
      match runRuleAt world document rule with
      | .error _ => [code ++ " failed"]
      | .ok rows => rows.map fun (environment, message) => describe code rule environment message

/-- The rules that fire over the document, in the order of the rule list. -/
private def fired (rules : Rules) (json : Lean.Json) : List String :=
  firings rules json fun code _ environment message =>
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

/-! ### Referenced and fill-to-fix pointers

A fired message names the term's reads and the filter's reads at the entity's any-row index, a
non-repeatable read at its own index and a `$`-marked filter read at its captured coordinate. A row
field no term reads is named nowhere. Each expectation is written in the peer's spelling, relative to
`/Policy[1]/`, and compared the way the peer compares: each channel sorted, the message order that of
the rule list. -/

/-- The peer's spelling of a pointer in the house form a message reference renders
([`renderPointer`](A12Kernel.Dm.renderPointer)): a pointer holding a wildcard level carries its
instances, any other drops them and names the first row bare. -/
private def house (peer : String) : String :=
  if (peer.splitOn "[0]").length > 1 then "/Policy[1]/" ++ peer else "Policy/" ++ peer.replace "[1]" ""

private def channel (pointers : List String) : String := ", ".intercalate pointers.mergeSort

/-- One message's reference channels in the peer's spelling, as `code|referenced|fillToFix`. -/
private def entry (code : String) (referenced fillToFix : List String) : String :=
  code ++ "|" ++ channel (referenced.map house) ++ "|" ++ channel (fillToFix.map house)

/-- Each fired message's reference channels over the document, in the order of the rule list. -/
private def named (rules : Rules) (json : Lean.Json) : List String :=
  firings rules json fun code rule environment message =>
    match rule.condition.core.messageReferences message environment with
    | .error _ => code ++ " unprojected"
    | .ok references =>
        let render (pointers : List MessagePointer) := channel (pointers.map (renderFieldPointer model))
        code ++ "|" ++ render references.referenced ++ "|" ++ render references.fillToFix

private def namingRules : Rules := lawRules ++ [("CTRL", "Holder", holder "Sum(Claims*/Amount) > 50")]

-- Locked: a12-dmkits SumOfTermsRuntimeLawsTest at 1124b523f, kernel 31.1.1
-- (`aTermSumMessageNamesItsOperands`). `Deductible`, a field of every row no term reads, is named
-- nowhere; `CTRL`, a plain `Sum`, is the control that expands the starred field alone.
example : named namingRules (policy [claim "30" "10" "open" ["4", "3"], claim "80" "20" "open"]) = [
    entry "GT" ["Claims[0]/Amount", "Claims[0]/Reserve", "Holder"] ["Claims[0]/Amount", "Claims[0]/Reserve"],
    entry "DIV" ["Claims[0]/Amount", "Claims[0]/Reserve", "Holder"] ["Claims[0]/Amount", "Claims[0]/Reserve"],
    entry "FILT" ["Claims[0]/Amount", "Claims[0]/Status", "Holder"] ["Claims[0]/Amount", "Claims[0]/Status"],
    entry "NEST" ["Claims[0]/Parts[0]/Qty", "Holder"] ["Claims[0]/Parts[0]/Qty"],
    entry "ROW" ["Claims[1]/Amount", "Claims[1]/Parts[0]/Qty"] ["Claims[1]/Parts[0]/Qty"],
    entry "CTRL" ["Claims[0]/Amount", "Holder"] ["Claims[0]/Amount"]] := by
  native_decide

private def upEntry := entry "UP" ["Claims[0]/Amount", "Holder", "Vehicles[0]/Value"] []
private def zipEntry :=
  entry "ZIP" ["Address[1]/Zip", "Claims[0]/Amount", "Holder"] ["Address[1]/Zip", "Claims[0]/Amount"]
private def gtOmission :=
  entry "GT" ["Claims[0]/Amount", "Claims[0]/Reserve", "Holder"] ["Claims[0]/Amount", "Claims[0]/Reserve"]
private def gtValue := entry "GT" ["Claims[0]/Amount", "Claims[0]/Reserve", "Holder"] []
private def inRowOmission := entry "INROW" ["Claims[0]/Amount"] ["Claims[0]/Amount"]
private def inRowValue := entry "INROW" ["Claims[0]/Amount"] []
private def rowOmission :=
  entry "ROW" ["Claims[1]/Amount", "Claims[1]/Parts[0]/Qty"] ["Claims[1]/Parts[0]/Qty"]

/-- `shapeDocuments`' messages, in the same order, with their reference channels. -/
private def shapeReferences : List (List String) := [
  [entry "CNT" ["Claims[0]/Amount", "Holder", "Vehicles[0]/Value"] ["Claims[0]/Amount", "Holder", "Vehicles[0]/Value"]],
  [entry "ROW" ["Claims[1]/Amount", "Claims[1]/Parts[0]/Qty"] []],
  [entry "AGG" ["Claims[0]/Parts[0]/Qty", "Holder"] ["Claims[0]/Parts[0]/Qty"], rowOmission],
  [zipEntry],
  [upEntry, zipEntry, entry "OUT" ["Claims[0]/Amount", "Holder", "Threshold"] ["Claims[0]/Amount", "Threshold"],
    gtOmission, inRowOmission],
  [upEntry, zipEntry, gtOmission, inRowOmission],
  [upEntry, gtOmission, inRowOmission],
  [upEntry, zipEntry, entry "DED" ["Claims[0]/Amount", "Claims[0]/Deductible", "Holder"]
    ["Claims[0]/Amount", "Claims[0]/Deductible"], gtOmission, inRowOmission],
  [],
  [upEntry, gtOmission, inRowOmission],
  [upEntry, gtValue, inRowValue]]

-- Locked: a12-dmkits SumOfTermsShapesRuntimeLawsTest at 1124b523f, kernel 31.1.1 (`whatGroovyReports`,
-- the reference channels per document). An upward count in the term withholds every ordinary operand
-- from fill-to-fix (`UP`, `CNT` against its count-free `PLAIN`); a non-repeatable read stays at its own
-- index (`ZIP`); a `$`-marked filter read keeps its coordinate (`OUT`); the filter's unmarked read is
-- named with the term's (`DED`); a VALUE firing has no fill-to-fix (`GT`, `INROW` over five claims).
example : shapeDocuments.length == shapeReferences.length &&
    (shapeDocuments.zip shapeReferences).all (fun ((json, _, _), expected) => named shapeRules json == expected)
    = true := by
  native_decide

/-! ### Partial validation -/

/-- A relevance entry in the peer's spelling: one index per path part below `Policy`, `0` for every instance. -/
private def relevant (path : List String) (reps : List Nat) : RelevantEntityPattern :=
  { path := "Policy" :: path, indices := reps.map fun n => if n == 0 then .all else .concrete n }

/-- The rules that fire in a partial call over `coverage`, as `code|type`, sorted. -/
private def partialFired (rules : Rules) (coverage : List RelevantEntityPattern) (json : Lean.Json)
    (adjust : DocumentData → DocumentData := id) : List String :=
  match checkedWith adjust json with
  | none => ["no document"]
  | some (_, document) => (rules.flatMap fun (code, errorPath, condition) =>
    match checkValidationRule dm .english (dmRule code errorPath condition) world with
    | .error _ => [code ++ " refused"]
    | .ok rule =>
      match runRulePartial world document coverage rule with
      | .error _ => [code ++ " failed"]
      | .ok messages => messages.map fun message =>
          code ++ "|" ++ (match message.messageType with | .value => "V" | .omission => "O")).mergeSort

private def partialRules : Rules := [
  ("GT", "Holder", holder (term ++ " > 100")),
  ("CTRL", "Holder", holder "Sum(Claims*/Amount) > 50"),
  ("FILT", "Holder", holder "SumOfTerms(Claims* Having [Claims/Status] == \"open\", [Claims/Amount]) > 100")]

private def holderRelevant := relevant ["Holder"] [1, 1]
private def groupRows (rows : List Nat) : List RelevantEntityPattern := rows.map fun row => relevant ["Claims"] [1, row]
private def cells (field : String) (rows : List Nat) : List RelevantEntityPattern :=
  rows.map fun row => relevant ["Claims", field] [1, row, 1]
private def partsRelevant := [relevant ["Claims", "Parts", "Qty"] [1, 0, 0, 1]]

-- Locked: a12-dmkits SumOfTermsRuntimeLawsTest at 1124b523f, kernel 31.1.1
-- (`partialValidationNeedsEveryRowOfTheCapacityRelevantAsAWhole`). `CTRL`, a plain `Sum` over a term
-- field, is the liveness control decided by that field alone, so a row where it fires and `GT` does
-- not is the term sum's own relevance rule: the group at any row or at every declared row, or every
-- field the group holds, decides it; the term's own fields do not, nor two filled rows of four.
example : [
    (groupRows [0], ["CTRL|O", "GT|O"]),
    (groupRows [1, 2, 3, 4], ["GT|O"]),
    (groupRows [1, 2], []),
    (cells "Amount" [0] ++ cells "Reserve" [0] ++ cells "Status" [0] ++ cells "Deductible" [0] ++ partsRelevant,
      ["CTRL|O", "GT|O"]),
    (cells "Amount" [0] ++ cells "Reserve" [0] ++ cells "Status" [0] ++ partsRelevant, ["CTRL|O"]),
    (cells "Amount" [0] ++ cells "Reserve" [0], ["CTRL|O"]),
    (cells "Amount" [0], ["CTRL|O"]),
    (cells "Amount" [1, 2, 3, 4] ++ cells "Reserve" [1, 2, 3, 4], [])].all
      (fun (coverage, expected) =>
        partialFired (partialRules.take 2) (holderRelevant :: coverage) (policy [claim "30" "10", claim "50" "20"]) == expected)
    = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsRuntimeLawsTest at 1124b523f, kernel 31.1.1
-- (`partialValidationNeedsAnErrorFreeFirstInstance`). A malformed field in row 1, one `GT` never
-- reads, leaves it undecided; the same field in row 2 does not.
example : [
    (policy [{ amount := "30", reserve := "10", deductible := "abc" }, claim "50" "20"], ["CTRL|O"]),
    (policy [claim "30" "10", { amount := "50", reserve := "20", deductible := "abc" }], ["CTRL|O", "GT|O"])].all
      (fun (json, expected) =>
        partialFired (partialRules.take 2) [holderRelevant, relevant ["Claims"] [1, 0]] json == expected)
    = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsRuntimeLawsTest at 1124b523f, kernel 31.1.1
-- (`partialValidationSkipsAFilteredTermSum`). Both rules fire in full validation over this document.
example : partialFired [partialRules[0]!, partialRules[2]!] [holderRelevant, relevant ["Claims"] [1, 0]]
    (policy [claim "150" "0" "open", claim "10" "0" "closed"]) = ["GT|O"] := by
  native_decide

-- Locked: a12-dmkits SumOfTermsShapesRuntimeLawsTest at 1124b523f, kernel 31.1.1
-- (`partialValidationWithoutAFirstRow`). The peer places claims 2 and 3 alone; validation converts that
-- placement to the V2-effective structure, which pads row 1 as an empty instantiated row
-- ([spec/01 §2.3](../../../spec/01-data-model.md#23-reading-a-document-from-json)), so the reader's
-- `{}` first row is the same document. The gate asks of that index-1 row, which is error-free, and a
-- malformed field in row 2 or 3 blocks nothing.
example : [none, some 2, some 3].all (fun erroneous =>
    let row (index : Nat) : Claim :=
      { amount := "80", reserve := "10", deductible := if erroneous == some index then "abc" else "" }
    partialFired [partialRules[0]!] [holderRelevant, relevant ["Claims"] [1, 0]]
      (policy [{}, row 2, row 3]) == ["GT|O"]) = true := by
  native_decide

end A12Kernel.Dm.SumOfTermsRuntimeLocks
