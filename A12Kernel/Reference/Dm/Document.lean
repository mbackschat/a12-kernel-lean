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

The Kernel's document conversion drops a string or object member of a fixed group and a string key of
a repeatable row that the model declares nothing for: both strategies report a document carrying them
exactly as the one without ([undeclared-member checkpoint](../../../docs/sources/domain-ingestion-probes.md#src-undeclared-document-members)),
so this reader drops them too. An undeclared boolean, `null`, number or array member of a fixed group,
an object in a nested fixed group or a repeatable row, and a string at the document root drop alike
([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-23)), so this reader drops
an undeclared member of every kind, assuming without measurement that a boolean, `null`, number or
array member of a row and a non-string member at the root drop alike. A field the model reader refused, an out-of-profile numeric scale,
or a temporal text no classifier owns is reported in `DmDocument.refusals` rather than placed, so a
replay row depending on it is refused as unrepresented instead of evaluated against a guess.
-/

namespace A12Kernel.Dm

open Lean

structure DmDocument where
  data : DocumentData
  refusals : List (List String × String)
  deriving Repr

/-- The scale the document conversion profile represents. The Kernel converts quoted and native
values out to `1e±100000` and reports them by their digit count (K16 rows `e07`, `e08`, `e10`), but
an extreme `int` scale faults validation (row `e03`) or exhausts the host's memory, with no threshold
known, so this profile refuses a wider scale instead of answering it. A scale outside `int` is not
converted at all (`javaIntScale`). -/
def documentNumberScaleBound : Nat := 100000

/-- Scalar node text before field conversion. Parsed numbers represent the probe's plain-serialized
inline route; raw document bytes must use `parseDocumentJson` to retain negative decimal scale. -/
def storedText? : Json → Option String
  | .str text => some text
  | .bool true => some "true"
  | .bool false => some "false"
  | .num number =>
      if number.exponent > documentNumberScaleBound then none
      else some (NumericInputDecimal.wireText { unscaled := number.mantissa, scale := number.exponent })
  | .null => some ""
  | _ => none

/-- What the Kernel's document conversion makes of one Number text. -/
inductive DocumentNumberConversion where
  /-- The text parses, so the cell is decimal-valued. -/
  | decimal (value : NumericInputDecimal)
  /-- The text does not parse, so the cell keeps it verbatim. -/
  | text
  /-- The text parses to a scale beyond `documentNumberScaleBound` that the host still converts. -/
  | beyondProfile
  deriving Repr, DecidableEq

/-- Whether a scale fits Java's `int`, outside which the host decimal constructor refuses the text,
so the cell keeps it verbatim (K16 rows `e11`, `e12`). -/
def javaIntScale (scale : Int) : Bool :=
  -2147483648 ≤ scale && scale ≤ 2147483647

/-- The Kernel's document Number conversion, Java `BigDecimal`'s string grammar: an optional sign,
digits around at most one point with at least one digit, and an optional `e` or `E` exponent with an
optional sign and at least one digit. Digits on both sides are Java's BMP decimal digits, so `٣.٥`
converts to `3.5` (K16 row `d01`). The scale is the written fraction less the exponent and must fit
`javaIntScale`. -/
def convertDocumentNumber (text : String) : DocumentNumberConversion :=
  let (negative, characters) := match text.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  let (mantissa, exponentPart) := characters.span fun character => character != 'e' && character != 'E'
  let exponent? : Option Int := match exponentPart with
    | [] => some 0
    | _ :: written =>
        let (negativeExponent, digits) := match written with
          | '-' :: rest => (true, rest)
          | '+' :: rest => (false, rest)
          | rest => (false, rest)
        (parseJava21BmpNatural? (String.ofList digits)).map fun magnitude =>
          if negativeExponent then -(magnitude : Int) else magnitude
  let (integer, afterPoint) := mantissa.span (· != '.')
  let fraction? := match afterPoint with
    | [] => some []
    | _ :: fraction => if fraction.contains '.' then none else some fraction
  match exponent?, fraction?, parseJava21BmpNatural? (String.ofList (integer ++ (fraction?.getD []))) with
  | some exponent, some fraction, some magnitude =>
      let scale : Int := fraction.length - exponent
      if !javaIntScale scale then .text
      else if documentNumberScaleBound < scale.natAbs then .beyondProfile
      else .decimal { unscaled := if negative then -(magnitude : Int) else magnitude, scale }
  | _, _, _ => .text

private inductive DocumentLexState where
  | plain | quoted | escaped | number

private def numberTokenText (token : String) : Except String String := do
  let .decimal value := convertDocumentNumber token
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

/-- The Kernel's leading-zero test on a text it parsed: after one optional sign, a `0` followed by any
character but the point. So `0e5` has leading zeros while `٠٣`, led by another zero digit, does not
(K16 rows `d04`, `d01`). -/
private def hasLeadingZeros (text : String) : Bool :=
  let unsigned := match text.toList with
    | '+' :: rest | '-' :: rest => rest
    | rest => rest
  match unsigned with
  | '0' :: next :: _ => next != '.'
  | _ => false

/-- Java's `equalsIgnoreCase` against an ASCII word: equal per character after upper-casing, or after
lower-casing the upper-cased character. Beyond ASCII case it identifies exactly the four characters
whose Java case mapping lands on an ASCII letter: the long s (U+017F, measured, 2026-10-21 §1.13), the
dotless and dotted i (U+0131, U+0130) and the Kelvin sign (U+212A), the last three read from Java's
`Character` mappings and unmeasured. -/
private def javaEqualsIgnoreCase (text word : String) : Bool :=
  let fold (character : Char) : Char := match character.toNat with
    | 0x017F => 's'
    | 0x0131 | 0x0130 => 'i'
    | 0x212A => 'k'
    | _ => character.toLower
  text.length == word.length && (text.toList.zip word.toList).all fun (left, right) => fold left == fold right

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
      let verbatim := cell (constraints.classifyFormalRead info (.text stored))
      match convertDocumentNumber stored with
      | .text => pure verbatim
      | conversion =>
          if constraints.leadingZerosAllowed && hasLeadingZeros stored then pure verbatim else
          match conversion with
          | .decimal value =>
              let input := NumericStoredInput.decimal value
              pure { address, stored := input.storedText, raw := constraints.classifyFormalRead info input
                     numericDecimal := some value }
          | _ => throw s!"Number text {stored} exceeds the represented decimal conversion profile"
  | .boolean =>
      let token := if javaEqualsIgnoreCase stored "true" then "true"
        else if javaEqualsIgnoreCase stored "false" then "false" else stored
      pure { address, stored := token, raw := classifyStoredBooleanText token }
  | .confirm =>
      let token := if javaEqualsIgnoreCase stored "true" then "true" else stored
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
  groups : Array GroupOccurrence := #[]
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
            else if model.flat.fields.any (childPath.isPrefixOf ·.groupPath) then do
              modify fun state => { state with groups := state.groups.push { path := childPath, coordinates := path } }
              readInstance model childPath path members.toList
            -- Nothing can read a declared empty group, and an undeclared object is dropped.
            else pure ()
        | _, _ =>
            if model.refusals.any (·.1 == childPath) then refuse childPath "declaration refused by the model reader"
            else if model.flat.repeatableGroups.any (·.path == childPath) ||
                model.flat.fields.any (childPath.isPrefixOf ·.groupPath) ||
                model.flat.declaresEmptyGroup childPath then
              refuse childPath "group value of the wrong JSON kind"
            else pure ()

/-- Read one document, given as the object holding its root groups. -/
def readDocument (model : DmModel) (json : Json) : Except String DmDocument := do
  let .obj roots := json | throw "document is no object"
  let ((), state) := (readInstance model [] [] roots.toList).run {}
  pure { data := { instantiatedRows := state.rows.toList, cells := state.cells.toList,
                    groupOccurrences := state.groups.toList }
         refusals := state.refusals.toList }

end A12Kernel.Dm
