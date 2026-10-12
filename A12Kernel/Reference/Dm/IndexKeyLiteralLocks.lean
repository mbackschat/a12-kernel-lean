import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.IndexKeyLiteralLocks

open Lean

private def model (minimum maximum : Nat) (custom : Bool := false) : FlatModel := {
  fields := [
    { id := 1, name := "Error", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, name := "Key", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string },
      stringPolicy := if custom then {} else {
        lineBreaksPermitted := true,
        minLength := if minimum == 0 then none else some minimum,
        maxLength := if maximum == 0 then none else some maximum },
      customType := if custom then some {
        name := "Code",
        minLength := if minimum == 0 then none else some minimum,
        maxLength := if maximum == 0 then none else some maximum } else none },
    { id := 3, name := "Amount", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 4, indexField := some 2 }] }

private def diagnostic (minimum maximum : Nat) (key : String) (ordered : Bool)
    (custom : Bool := false) : Option String :=
  let selected := "Rows/Amount For \"" ++ key ++ "\""
  let expression := if ordered then "FirstFilledValue(" ++ selected ++ ", Error)" else "[" ++ selected ++ "]"
  match checkRule { flat := model minimum maximum custom, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      group := ["Form"], name := "KeyLiteral", errorCode := "KEY", errorEntityRelPath := "../Error",
      severity := "ERROR", condition := "FieldFilled(Error) And " ++ expression ++ " > 0" } with
  | .ok _ => none
  | .error error => some (error.construct ++ ": " ++ error.detail)

private def admitted (minimum maximum : Nat) (key : String) (ordered : Bool)
    (custom : Bool := false) : Bool :=
  (diagnostic minimum maximum key ordered custom).isNone

example : [false, true].all (fun custom =>
    [(0, 0), (4, 0), (0, 3), (0, 4)].all (fun (minimum, maximum) =>
      (model minimum maximum custom).validate.isOk)) = true := by native_decide

-- KF542 and IndexKeyNormalizationPopulation.literalDecodingRows measure one authored pass;
-- repeated CR distinguishes it from a second pass on both sides of the length bound.
example : [false, true].all (fun custom => [false, true].all (fun ordered =>
    admitted 4 0 "A\r\r\nB" ordered custom &&
    !admitted 0 3 "A\r\r\nB" ordered custom &&
    admitted 0 3 "A\r\nB" ordered custom &&
    !admitted 4 0 "A\r\nB" ordered custom &&
    admitted 0 4 "A\r\r\nB" ordered custom)) = true := by native_decide

example : [false, true].all (fun custom => [false, true].all (fun ordered =>
    ["AB", "A\rB", "A\nB"].all (fun key =>
      admitted 0 0 key ordered custom &&
      !admitted 4 0 key ordered custom &&
      admitted 0 3 key ordered custom))) = true := by native_decide

example : [false, true].all (fun custom =>
    diagnostic 0 3 "A\r\r\nB" true custom == some "Having: MVK_INDEX_VALUE_INVALID" &&
    diagnostic 4 0 "A\r\nB" true custom == some "Having: MVK_INDEX_VALUE_INVALID" &&
    diagnostic 4 0 "AB" true custom == some "Having: MVK_INDEX_VALUE_INVALID" &&
    diagnostic 0 4 "A\r\r\nB" true custom == none) = true := by native_decide

private def readCustom (minimum maximum : Option Nat) : Option CustomFieldTypeDeclaration :=
  let body := Json.mkObj ([("name", toJson "Code")] ++
    minimum.toList.map (fun bound => ("minLength", toJson bound)) ++
    maximum.toList.map (fun bound => ("maxLength", toJson bound)))
  let field := Json.mkObj [("fieldType", Json.mkObj [
    ("type", toJson "CustomFieldType"), ("CustomFieldType", body)])]
  (readFieldType 2 ["Form", "Rows"] "Key" [10] field).toOption.bind (·.customType)

example : [(none, none), (some 0, some 0), (some 4, none), (none, some 3), (some 4, some 4)].all
    (fun (minimum, maximum) => readCustom minimum maximum ==
      some { name := "Code", minLength := minimum, maxLength := maximum }) = true := by
  native_decide

private def runtime (key : String) (expected : Nat) (custom dynamic rejectStored : Bool) :
    Option (List String × List String) := do
  let fixture := { model 0 0 custom with fields := (model 0 0 custom).fields ++ [
    { id := 4, name := "Request", groupPath := ["Form"], policy := { kind := .string },
      stringPolicy := { lineBreaksPermitted := true } }] }
  let world : World := {
    now := { epochMillis := 0 }
    customFieldValidator? := fun name => if name == "Code" then some (fun raw _ =>
      if rejectStored && raw == "A\r\r\nB" then some { projectCode := "REJECTED_KEY" } else none) else none }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let raw ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Error", .str "99"), ("Request", .str key),
    ("Rows", .arr (([("A\nB", "11"), ("A\r\r\nB", "22"), ("A\rB", "33")].map fun (key, amount) =>
      Json.mkObj [("Key", .str key), ("Amount", .str amount)]).toArray))])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" raw.data).toOption
  let selected := "[Rows/Amount For " ++ (if dynamic then "Request" else "\"" ++ key ++ "\"") ++ "]"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../Error",
    severity := "ERROR", condition := "FieldFilled(Error) And " ++ selected ++ " == " ++ toString expected } world).toOption
  let messages ← (runRule world document rule).toOption
  let computation ← (lowerComputation fixture .english {
    group := ["Form"], name := "Selected", targetRelPath := "../Error", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := selected }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation.2]).toOption
  pure (messages.map (fun message => (observe fixture message).code), outcomes.map (·.outcome))

-- KF542 separates literal decoding from stored String ingestion; the custom and computation
-- compositions below are internal controls over the same checked key observation.
example : [false, true].all (fun custom => [false, true].all fun dynamic =>
    [("A\nB", 11), ("A\r\nB", 11), ("A\r\r\nB", 22), ("A\rB", 33)].all fun (key, expected) =>
      runtime key expected custom dynamic false ==
        some (["SELECTED"], ["value " ++ toString expected])) = true := by native_decide

example : [false, true].all (fun dynamic =>
    runtime "A\r\r\nB" 22 true dynamic true == some ([], ["cleared"])) = true := by native_decide

example : (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (model 0 0 true)).isOk = false := by native_decide

private def onceErrorCoordinates (condition : String) (keys : List String)
    (partialCall : Bool) (numericKey : Bool := false) : Option (List MessageRepetitionCoordinate) := do
  let fixture := { model 0 0 with fields := (model 0 0).fields.map fun field =>
    if numericKey && field.id == 2 then { field with policy := { kind := .number { scale := 2, signed := true } }, stringPolicy := {} }
    else field }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let world : World := { now := { epochMillis := 0 } }
  let raw ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Error", .str "1"), ("Rows", .arr (keys.map fun key =>
      Json.mkObj [("Key", .str key), ("Amount", .str "5")]).toArray)])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" raw.data).toOption
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "SelectedError", errorCode := "SELECTED_ERROR", errorEntityRelPath := "../Rows/Amount",
    severity := "ERROR", condition } world).toOption
  let outcome ← if partialCall then do
    let .evaluated _ outcome ← (rule.evalOrdinaryOncePartial document
      (.partialSet [RelevantEntityPattern.allInstances ["Form"]]) (some world)).toOption | none
    pure outcome
    else do
      let (_, outcome) ← (rule.evalOrdinaryOnceFull document (some world)).toOption
      pure outcome
  pure (← outcome.message?).errorAddress.coordinates

example : [false, true].all (fun partialCall =>
    onceErrorCoordinates "FieldFilled(Error) Or FieldFilled(Rows/Amount For \"b\")" ["a", "b"] partialCall ==
      some [.concrete 2] &&
    onceErrorCoordinates "FieldFilled(Error) Or FieldFilled(Rows/Amount For \"missing\")" ["a", "b"] partialCall ==
      some [.unknown]) = true := by native_decide

example : [false, true].all (fun partialCall =>
    onceErrorCoordinates "FieldFilled(Error) Or [Rows/Amount For \"5\"] > 0" ["4", "5"] partialCall true ==
      some [.concrete 2] &&
    onceErrorCoordinates "FieldFilled(Error) Or [Rows/Amount For \"5.00\"] > 0" ["4", "5"] partialCall true ==
      some [.concrete 2] &&
    onceErrorCoordinates "FieldFilled(Error) Or [Rows/Amount For \"5\"] > 0 Or [Rows/Amount For \"5.00\"] > 0"
      ["4", "5"] partialCall true == some [.concrete 1] &&
    onceErrorCoordinates "FieldFilled(Error) Or [Rows/Amount For \"-0\"] > 0" ["4", "0"] partialCall true ==
      some [.concrete 2] &&
    onceErrorCoordinates "FieldFilled(Error) Or [Rows/Amount For \"-0\"] > 0 Or [Rows/Amount For \"0\"] > 0"
      ["4", "0"] partialCall true == some [.concrete 1]) = true := by native_decide

end A12Kernel.Dm.IndexKeyLiteralLocks
