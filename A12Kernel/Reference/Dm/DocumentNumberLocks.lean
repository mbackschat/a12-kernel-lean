import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.DocumentNumberLocks
open Lean A12Kernel

private def numberText (token : String) : Option String :=
  (Json.parse token).toOption.bind storedText?

example :
    [("10.50", "10.50"), ("2.0", "2.0"), ("-0.00", "0.00"),
     ("1.00e-7", "1.00E-7"), ("0.000001", "0.000001"),
     ("0.0000001", "1E-7")].all (fun (token, expected) =>
       numberText token == some expected) := by native_decide

private def amount : FlatFieldDecl := {
  id := 0, groupPath := ["Order"], name := "Amount"
  policy := { kind := .number { scale := 2, signed := true } } }

private def dm : DmModel := {
  flat := { fields := [amount] }, rules := [], computations := []
  conditionLanguage := "en_US", refusals := [] }

private def fileCell (token : String) : Option ClassifiedCellInput := do
  let json ← (parseDocumentJson ("{\"Order\":{\"Amount\":" ++ token ++ "}}")).toOption
  let document ← (readDocument dm json).toOption
  document.data.cells.head?

example :
    [("10.50", 1050, 2), ("1e3", 1, -3), ("1.0e3", 10, -2),
     ("0e3", 0, -3), ("1e+3", 1, -3), ("-0.00", 0, 2), ("\"1e3\"", 1, -3)].all (fun (token, coefficient, scale) =>
       ((fileCell token).bind (·.numericDecimal)) ==
         some { unscaled := coefficient, scale }) := by native_decide

/- JSON spelling and node text differ, but quoted text is untouched (including escapes). -/
example :
    [("1.0e3", "1.0E+3"), ("-1e3", "-1E+3"),
     ("0.00e-7", "0E-9"), ("123456789012345678901", "123456789012345678901")].all
       (fun (token, expected) =>
         (parseDocumentJson token).toOption == some (.str expected)) := by native_decide

/- An unquoted cell that is no JSON number leaves the document unread, beside the three tokens the
a12-dmkits letter of 2026-10-21 (§1.14) measured read. -/
example :
    ["01", "1.", "1e", "1e+-3", "+1", "{1:2}", "[1,]", "[1 2]", "1e100001", "abc", "True", "NaN",
      "0x10", ".5"].all (fun text => !(parseDocumentJson text).isOk) ∧
    ["-0", "1E1", "5"].all (fun text => (parseDocumentJson text).isOk) := by native_decide

/- Only an object of root groups is a document: well-formed JSON of any other shape is refused by
the reader, not read as an empty document. -/
example :
    ["[]", "null", "\"x\"", "1", "true"].all (fun text =>
      match parseDocumentJson text with
      | .ok json => !(readDocument dm json).isOk
      | .error _ => false) &&
    ((parseDocumentJson "{}").toOption.bind (readDocument dm · |>.toOption)).isSome := by
  native_decide

example :
    ["null", "true", "false", "\"1e3\"", "\"10.50\"", "\"a\\\"1e3\\\\2.0\""].all
      (fun text => (Json.parse text).isOk &&
        (parseDocumentJson text).toOption == (Json.parse text).toOption) := by native_decide

example :
    (parseDocumentJson "{\"1e3\":[10.50,{\"n\":-1e3},true,null]}").toOption ==
      (Json.parse "{\"1e3\":[\"10.50\",{\"n\":\"-1E+3\"},true,null]}").toOption := by native_decide

private def checked (inline : Bool) (declaration : FlatFieldDecl) (token : String) :
    Option (CheckedDocument { fields := [declaration] }) := do
  let text := "{\"Order\":{\"Amount\":" ++ token ++ "}}"
  let json ← (if inline then Json.parse text else parseDocumentJson text).toOption
  let model := { dm with flat := { fields := [declaration] } }
  let document ← (readDocument model json).toOption
  if !document.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model.flat).toOption
  (checkDocument prepared "en_US" document.data).toOption

private def identity (inline : Bool) (token : String) : Option NumericSourceIdentity := do
  let input ← checked inline amount token
  let cell ← input.checkedCells.head?
  (cell.numericInput.map (·.sourceIdentity))

/- Probe inline reserialization expands negative scale; file bytes and quoted values preserve it. -/
example :
    [identity false "1e3" == some .nonComputedForm,
     identity true "1e3" == some (.decimal { unscaled := 1000, scale := 0 }),
     identity true "\"1e3\"" == some .nonComputedForm,
     identity false "10.50" == some (.decimal { unscaled := 1050, scale := 2 }),
     identity true "10.50" == identity false "10.50"].all id := by native_decide

/- Validation and computation read the same declaration-adjusted text, independently of identity. -/
example : [false, true].all (fun inline =>
    ["10.50", "\"10.50\""].all (fun token =>
      let input := checked inline { amount with
        numericTargetConstraints := { minFractionalDigits := 2 } } token
      [.validation, .computation].all (fun phase =>
        (input.bind fun doc => (doc.observeNumberFormalRead phase { field := 0, path := [] }).toOption)
          == some (.value "10.50")))) := by native_decide

/- A String destination observes canonical node spelling, not Number formal-read projection. -/
example :
    [(false, "1e3", "1E+3"), (true, "1e3", "1000"),
     (false, "10.50", "10.50"), (false, "1e-7", "1E-7"),
     (false, "\"1e3\"", "1e3")].all (fun (inline, token, expected) =>
      ((checked inline { amount with policy := { kind := .string } } token).bind
        (fun doc => doc.storedTextAt { field := 0, path := [] })) == some expected) := by native_decide

/- The profile bound is on retained scale, independent of canonical exponent spelling. -/
example : [("10e1000", 10, -1000), ("100e999", 100, -999)].all
    (fun (token, coefficient, scale) =>
      ((fileCell token).bind (·.numericDecimal)) == some { unscaled := coefficient, scale }) := by
  native_decide

private def exactInput (inline : Bool) (token : String) : Option NumericStoredInput := do
  let input ← checked inline amount token
  let cell ← input.checkedCells.head?
  cell.numericInput

example :
    [exactInput false "1e3" == some (.decimal { unscaled := 1, scale := -3 }),
     exactInput true "1e3" == some (.decimal { unscaled := 1000, scale := 0 }),
     exactInput true "\"1e3\"" == some (.decimal { unscaled := 1, scale := -3 })].all id := by
  native_decide

example : [false, true].all (fun inline =>
    ["1e3", "\"1e3\""].all (fun token =>
      [.validation, .computation].all (fun phase =>
        ((checked inline amount token).bind fun doc =>
          (doc.observeNumberFormalRead phase { field := 0, path := [] }).toOption)
            == some (.value "1000")))) := by native_decide

example : [0, 1, -1, 10, 100, -100, 123400].all (fun coefficient =>
    [-1000, -999, -3, 0, 2, 6, 7, 999, 1000].all (fun scale =>
      let value : NumericInputDecimal := { unscaled := coefficient, scale }
      convertDocumentNumber value.wireText == .decimal value)) := by native_decide

private def representationCoherent (representation : SourceRepresentation)
    (decimal : Bool) : Option Bool := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler dm.flat).toOption
  let cell ← fileCell "7.00"
  let cell := { cell with
    sourceRepresentation := representation
    numericDecimal := if decimal then cell.numericDecimal else none }
  pure (checkDocument prepared "en_US" { instantiatedRows := [], cells := [cell] }).isOk

example :
    representationCoherent .classified true = some true ∧
    representationCoherent .unconvertedText false = some true ∧
    representationCoherent .unconvertedText true = some false := by native_decide

end A12Kernel.Dm.DocumentNumberLocks
