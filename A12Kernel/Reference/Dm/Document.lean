import A12Kernel.Reference.Dm.Model
import A12Kernel.Semantics.NumericWire
import A12Kernel.Elaboration.CheckedDocument

/-! # Reading a Kernel document against a DM model

A Kernel document in a `kernelProbe` request is nested JSON: an object per group, keyed by element
name, a repeatable group as an array of its rows in index order, and a field as its stored scalar. This
reader turns one into `DocumentData` for `checkDocument`, deriving every cell's parsed value from its
stored text through the model's own classifiers. A JSON boolean stores the Kernel's `true` or `false`
token and a JSON number its scale-preserving decimal-node text. A JSON `null` is a field present without a value, as
a12-dmkits' `document-instance.schema.json` reads the Kernel's document format, and a missing key is an
absent field.

A field the model reader refused, a key or object the model declares nothing for, an out-of-profile
numeric scale, or a temporal text no classifier owns is reported in `DmDocument.refusals` rather than placed, so a replay row depending on it is refused
as unrepresented instead of evaluated against a guess.
-/

namespace A12Kernel.Dm

open Lean

structure DmDocument where
  data : DocumentData
  refusals : List (List String × String)
  deriving Repr

/-- Scalar node text before field conversion. Parsed numbers represent the probe's plain-serialized
inline route; raw document bytes must use `parseDocumentJson` to retain negative decimal scale. -/
def storedText? : Json → Option String
  | .str text => some text
  | .bool true => some "true"
  | .bool false => some "false"
  | .num number =>
      if number.exponent > 1000 then none
      else some (NumericInputDecimal.wireText { unscaled := number.mantissa, scale := number.exponent })
  | .null => some ""
  | _ => none

/-- The decimal the Kernel's document conversion makes of a Number text: Java `BigDecimal`'s string
grammar, an optional sign, digits around an optional point and an optional exponent, with at least
one digit. A decimal scale outside the bounded conversion profile is left as text, as an
unparseable value is. The bound follows scale rather than exponent spelling because canonical
scientific text moves the point without changing decimal identity. -/
def convertedDecimal? (text : String) : Option NumericInputDecimal := do
  let chars := text.toList
  let (negative, chars) := match chars with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, chars)
  let (mantissa, exponent) := match chars.splitOn 'e', chars.splitOn 'E' with
    | [mantissa, exponent], _ => (mantissa, some exponent)
    | _, [mantissa, exponent] => (mantissa, some exponent)
    | _, _ => (chars, none)
  let exponent ← match exponent with
    | none => pure (0 : Int)
    | some ('+' :: digits) => (String.ofList digits).toNat? |>.map Int.ofNat
    | some digits => (String.ofList digits).toInt?
  let (integer, fraction) ← match mantissa.splitOn '.' with
    | [integer] => pure (integer, [])
    | [integer, fraction] => pure (integer, fraction)
    | _ => none
  let scale : Int := fraction.length - exponent
  if scale.natAbs > 1000 then none
  let digits := integer ++ fraction
  if digits.isEmpty || !digits.all Char.isDigit then none
  let magnitude ← (String.ofList digits).toNat?
  pure { unscaled := if negative then -(magnitude : Int) else magnitude
         scale }

private inductive DocumentLexState where
  | plain | quoted | escaped | number

private def numberTokenText (token : String) : Except String String := do
  let some value := convertedDecimal? token
    | throw "native JSON number exceeds the represented decimal conversion profile"
  pure ("\"" ++ value.wireText ++ "\"")

/-- Parse raw document bytes without erasing native negative decimal scale. Validate JSON before
replacing numeric value tokens by their node text, so quoting cannot admit malformed JSON or numeric
object keys. The existing field converter consumes the same text as Kernel `ValueNode.asText`. -/
def parseDocumentJson (text : String) : Except String Json := do
  let _ ← Json.parse text
  let mut state := DocumentLexState.plain
  let mut token := ""
  let mut output := ""
  for char in text.toList do
    match state with
    | .quoted =>
        output := output.push char
        if char == '\\' then state := .escaped
        else if char == '"' then state := .plain
    | .escaped =>
        output := output.push char
        state := .quoted
    | .plain =>
        if char.isDigit || char == '-' then
          token := String.singleton char
          state := .number
        else
          output := output.push char
          if char == '"' then state := .quoted
    | .number =>
        if char.isDigit || char == '.' || char == 'e' || char == 'E' ||
            char == '+' || char == '-' then
          token := token.push char
        else
          output := output ++ (← numberTokenText token)
          output := output.push char
          state := if char == '"' then .quoted else .plain
  match state with
  | .number => output := output ++ (← numberTokenText token)
  | _ => pure ()
  Json.parse output

private def hasLeadingZeros (text : String) : Bool :=
  match (text.toList.dropWhile (fun c => c == '+' || c == '-')) with
  | '0' :: next :: _ => next.isDigit
  | _ => false

/-- The cell one declaration takes for its stored text, or the reason none is derivable. A Number
text the document conversion parses is decimal-valued and every other filled Number text keeps the
String-valued regime, as does a leading-zero value on a field allowing leading zeros (spec §4,
storage regimes); a Boolean or Confirm token is read regardless of case. -/
def classifyStored (model : FlatModel) (declaration : FlatFieldDecl) (address : CellAddr)
    (stored : String) : Except String ClassifiedCellInput := do
  let cell (raw : RawCell) : ClassifiedCellInput := { address, stored, raw }
  if stored.isEmpty then return cell .presentEmpty
  match declaration.policy.kind with
  | .number info =>
      let constraints := declaration.numericTargetConstraints
      let decimal := if constraints.leadingZerosAllowed && hasLeadingZeros stored then none
        else convertedDecimal? stored
      match decimal with
      | some value =>
          let input := NumericStoredInput.decimal value
          pure { address, stored := input.storedText, raw := constraints.classifyFormalRead info input
                 numericDecimal := some value }
      | none => pure (cell (constraints.classifyFormalRead info (.text stored)))
  | .boolean =>
      let token := match stored.toLower with | "true" => "true" | "false" => "false" | _ => stored
      pure { address, stored := token, raw := classifyStoredBooleanText token }
  | .confirm =>
      let token := if stored.toLower == "true" then "true" else stored
      pure { address, stored := token, raw := classifyStoredConfirmText token }
  | .string => pure (cell (.parsed (.str stored)))
  | .enumeration => pure (cell (.parsed (.enum stored)))
  | .dateRange =>
      match declaration.toDateRangeDeclarationPolicy? with
      | none => throw "date range without policy"
      | some policy =>
          let runtimeText ← (model.dateRangeRuntimeText policy stored).mapError
            (fun error => s!"date range conversion: {repr error}")
          match model.classifyRuntimeDateRange policy runtimeText with
          | .ok raw => pure { address, stored := runtimeText, raw }
          | .error error => throw s!"date range text: {repr error}"
  | .temporal _ _ =>
      match CheckedDocument.canonicalTemporalCell? model declaration stored with
      | some (some raw) => pure (cell raw)
      | some none => throw "temporal text resolves to no instant"
      | none => throw "temporal format without a classifier"

private structure DocumentState where
  rows : Array RowAddr := #[]
  cells : Array ClassifiedCellInput := #[]
  refusals : Array (List String × String) := #[]

private def refuse (path : List String) (reason : String) : StateM DocumentState Unit :=
  modify fun state => { state with refusals := state.refusals.push (path, reason) }

/-- Read one group instance's members at `group`, `path` holding the indices of every enclosing
repeatable level. -/
private partial def readInstance (model : DmModel) (group : GroupPath) (path : List Nat)
    (members : List (String × Json)) : StateM DocumentState Unit := do
  for (name, value) in members do
    let childPath := group ++ [name]
    match model.flat.fields.find? fun field => field.groupPath == group && field.name == name with
    | some declaration =>
        match storedText? value with
        | none => refuse childPath "field value is no scalar, or its numeric scale exceeds the represented profile"
        | some stored =>
            match classifyStored model.flat declaration { field := declaration.id, path } stored with
            | .ok cell => modify fun state => { state with cells := state.cells.push cell }
            | .error reason => refuse childPath reason
    | none =>
        match model.flat.repeatableGroups.find? (·.path == childPath), value with
        | some repeatable, .arr instances =>
            -- JSON conversion discards non-object rows before assigning coordinates; V1 placement padding is a separate route (spec/07 §1).
            let objects := instances.toList.filterMap fun
              | .obj members => some members.toList
              | _ => none
            for (members, index) in objects.zipIdx do
              let rowPath := path ++ [index + 1]
              modify fun state => { state with rows := state.rows.push { group := repeatable.level, path := rowPath } }
              readInstance model childPath rowPath members
        | none, .obj members =>
            if model.refusals.any (·.1 == childPath) then refuse childPath "declaration refused by the model reader"
            -- A nonrepeatable group is known by the fields declared below it.
            else if model.flat.fields.any (childPath.isPrefixOf ·.groupPath) then
              readInstance model childPath path members.toList
            else refuse childPath "member the model does not declare"
        | _, _ =>
            if model.refusals.any (·.1 == childPath) then refuse childPath "declaration refused by the model reader"
            else refuse childPath "member the model does not declare"

/-- Read one document, given as the object holding its root groups. -/
def readDocument (model : DmModel) (json : Json) : Except String DmDocument := do
  let .obj roots := json | throw "document is no object"
  let ((), state) := (readInstance model [] [] roots.toList).run {}
  pure { data := { instantiatedRows := state.rows.toList, cells := state.cells.toList }
         refusals := state.refusals.toList }

end A12Kernel.Dm
