import A12Kernel.Reference.Dm.Model
import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.TimeInput

/-! # Reading a Kernel document against a DM model

A Kernel document in a `kernelProbe` request is nested JSON: an object per group, keyed by element
name, a repeatable group as an array of its rows in index order, and a field as its stored scalar. This
reader turns one into `DocumentData` for `checkDocument`, deriving every cell's parsed value from its
stored text through the model's own classifiers. A JSON boolean stores the Kernel's `true` or `false`
token and a JSON number its decimal spelling, unless that spelling ends its fraction in zeros. A JSON `null` is a field present without a value, as
a12-dmkits' `document-instance.schema.json` reads the Kernel's document format, and a missing key is an
absent field.

A field the model reader refused, a key or object the model declares nothing for, a JSON number whose
written scale its rendering would drop, or a temporal text no classifier owns is reported in `DmDocument.refusals` rather than placed, so a replay row depending on it is refused
as unrepresented instead of evaluated against a guess.
-/

namespace A12Kernel.Dm

open Lean

structure DmDocument where
  data : DocumentData
  refusals : List (List String × String)
  deriving Repr

/-- The text the Kernel stores for one scalar JSON value. A JSON number whose written fraction ends
in zeros, such as `10.50`, has no text here: rendering drops the zeros, and whether the Kernel's
reading keeps that scale is unmeasured, since a fraction-digit limit accepts both spellings alike. -/
def storedText? : Json → Option String
  | .str text => some text
  | .bool true => some "true"
  | .bool false => some "false"
  | .num number =>
      if number.exponent > 0 && number.mantissa % 10 == 0 then none else some number.toString
  | .null => some ""
  | _ => none

/-- The decimal the Kernel's document conversion makes of a Number text: Java `BigDecimal`'s string
grammar, an optional sign, digits around an optional point and an optional exponent, with at least
one digit. An exponent too large to expand is left as text, as an unparseable value is. -/
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
    | some digits => (String.ofList digits).toInt?
  if exponent.natAbs > 1000 then none
  let (integer, fraction) ← match mantissa.splitOn '.' with
    | [integer] => pure (integer, [])
    | [integer, fraction] => pure (integer, fraction)
    | _ => none
  let digits := integer ++ fraction
  if digits.isEmpty || !digits.all Char.isDigit then none
  let magnitude ← (String.ofList digits).toNat?
  pure { unscaled := if negative then -(magnitude : Int) else magnitude
         scale := fraction.length - exponent }

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
          match classifyStoredDateRangeForModel model.timeZoneId model.baseYear policy stored with
          | .ok raw => pure (cell raw)
          | .error error => throw s!"date range text: {repr error}"
  | .temporal kind _ =>
      match CheckedDocument.canonicalTemporalCell? model declaration stored with
      | some (some raw) => pure (cell raw)
      | some none => throw "temporal text resolves to no instant"
      | none =>
          match kind, certifyTimeInputField declaration with
          | .time, .ok owner =>
              match owner.classifyStoredForModel model.timeZoneId stored with
              | .ok raw => pure (cell raw)
              | .error error => throw s!"time text: {repr error}"
          | _, _ => throw "temporal format without a classifier"

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
        | none => refuse childPath "field value is no scalar, or a number whose written scale is unmeasured"
        | some stored =>
            match classifyStored model.flat declaration { field := declaration.id, path } stored with
            | .ok cell => modify fun state => { state with cells := state.cells.push cell }
            | .error reason => refuse childPath reason
    | none =>
        match model.flat.repeatableGroups.find? (·.path == childPath), value with
        | some repeatable, .arr instances =>
            for (row, index) in instances.toList.zipIdx do
              let rowPath := path ++ [index + 1]
              modify fun state => { state with rows := state.rows.push { group := repeatable.level, path := rowPath } }
              match row with
              | .obj members => readInstance model childPath rowPath members.toList
              | _ => refuse childPath "repeatable row is no object"
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
