import Lean.Data.Json.Parser

/-! # Strict JSON parsing

Lean's JSON parser accepts duplicate object members by retaining one value. This transport guard rejects ambiguous duplicate members and bounds the syntax before Lean's ordinary parser can allocate from hostile numeric exponents or unbounded nesting. Protocol v1 has only canonical non-negative structural integers on the JSON-number channel; exact A12 decimal values are strings decoded separately.
-/

namespace A12Kernel.Reference.StrictJson

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def maxNesting : Nat := 128

def maxNumberCharacters : Nat := 16

inductive Limit where
  | nesting
  | numberCharacters
  deriving Repr, DecidableEq

namespace Limit

def tag : Limit → String
  | .nesting => "jsonNesting"
  | .numberCharacters => "jsonNumberCharacters"

def maximum : Limit → Nat
  | .nesting => maxNesting
  | .numberCharacters => maxNumberCharacters

end Limit

inductive Error where
  | invalidJson (message : String)
  | duplicateMember (name : String)
  | nonCanonicalNumber
  | resourceLimit (limit : Limit)
  deriving Repr, DecidableEq

private def isDigit (character : Char) : Bool :=
  '0' <= character && character <= '9'

private def isUnsafeNumberContinuation (character : Char) : Bool :=
  character == '.' || character == 'e' || character == 'E' ||
    character == '+' || character == '-'

private partial def scanNaturalToken (characters : List Char) (digits : Nat) :
    Except Error (List Char) := do
  match characters with
  | character :: rest =>
      if isDigit character then
        let digits := digits + 1
        if digits > maxNumberCharacters then
          throw (.resourceLimit .numberCharacters)
        scanNaturalToken rest digits
      else if isUnsafeNumberContinuation character then
        throw .nonCanonicalNumber
      else
        pure characters
  | [] => pure []

private partial def safetyScan (allowNegativeIntegers : Bool) (characters : List Char)
    (inString escaped : Bool)
    (nesting : Nat) : Except Error Unit := do
  match characters with
  | [] => pure ()
  | character :: rest =>
      if inString then
        if escaped then
          safetyScan allowNegativeIntegers rest true false nesting
        else if character == '\\' then
          safetyScan allowNegativeIntegers rest true true nesting
        else if character == '"' then
          safetyScan allowNegativeIntegers rest false false nesting
        else
          safetyScan allowNegativeIntegers rest true false nesting
      else if character == '"' then
        safetyScan allowNegativeIntegers rest true false nesting
      else if character == '{' || character == '[' then
        let nesting := nesting + 1
        if nesting > maxNesting then
          throw (.resourceLimit .nesting)
        safetyScan allowNegativeIntegers rest false false nesting
      else if character == '}' || character == ']' then
        safetyScan allowNegativeIntegers rest false false nesting.pred
      else if character == '-' then
        match rest with
        | next :: tail =>
            if isDigit next then
              if !allowNegativeIntegers then throw .nonCanonicalNumber
              else if next == '0' then throw .nonCanonicalNumber
              else
                let remaining ← scanNaturalToken tail 1
                safetyScan allowNegativeIntegers remaining false false nesting
            else safetyScan allowNegativeIntegers rest false false nesting
        | [] => safetyScan allowNegativeIntegers rest false false nesting
      else if isDigit character then
        if character == '0' then
          match rest with
          | next :: _ =>
              if isDigit next then throw .nonCanonicalNumber
              else
                let remaining ← scanNaturalToken rest 1
                safetyScan allowNegativeIntegers remaining false false nesting
          | [] => pure ()
        else
          let remaining ← scanNaturalToken rest 1
          safetyScan allowNegativeIntegers remaining false false nesting
      else
        safetyScan allowNegativeIntegers rest false false nesting

private def safetyPreflight (allowNegativeIntegers : Bool) (input : String) : Except Error Unit :=
  safetyScan allowNegativeIntegers input.toList false false 0

private def firstDuplicate (earlier later : Option String) : Option String :=
  match earlier with
  | some name => some name
  | none => later

private abbrev MemberSet := Std.TreeMap.Raw String Unit compare

mutual

  private partial def preflightArrayCore (duplicate : Option String) : Parser (Option String) := do
    let nestedDuplicate ← preflightValue
    let duplicate := firstDuplicate duplicate nestedDuplicate
    let separator ← any
    if separator == ']' then
      ws
      pure duplicate
    else if separator == ',' then
      ws
      preflightArrayCore duplicate
    else
      fail "unexpected character in array"

  private partial def preflightObjectCore (seen : MemberSet)
      (duplicate : Option String) : Parser (Option String) := do
    Lean.Json.Parser.lookahead (fun character => character == '"') "\""
    skip
    let name ← Lean.Json.Parser.str
    ws
    let memberDuplicate := if seen.contains name then some name else none
    let seen := seen.insert name ()
    Lean.Json.Parser.lookahead (fun character => character == ':') ":"
    skip
    ws
    let nestedDuplicate ← preflightValue
    let duplicate := firstDuplicate duplicate (firstDuplicate memberDuplicate nestedDuplicate)
    let separator ← any
    if separator == '}' then
      ws
      pure duplicate
    else if separator == ',' then
      ws
      preflightObjectCore seen duplicate
    else
      fail "unexpected character in object"

  private partial def preflightValue : Parser (Option String) := do
    let character ← peek!
    if character == '[' then
      skip
      ws
      let character ← peek!
      if character == ']' then
        skip
        ws
        pure none
      else
        preflightArrayCore none
    else if character == '{' then
      skip
      ws
      let character ← peek!
      if character == '}' then
        skip
        ws
        pure none
      else
        preflightObjectCore ∅ none
    else if character == '"' then
      skip
      discard Lean.Json.Parser.str
      ws
      pure none
    else if character == 'f' then
      skipString "false"
      ws
      pure none
    else if character == 't' then
      skipString "true"
      ws
      pure none
    else if character == 'n' then
      skipString "null"
      ws
      pure none
    else if character == '-' || ('0' <= character && character <= '9') then
      discard Lean.Json.Parser.num
      ws
      pure none
    else
      fail "unexpected input"

end

private def preflight : Parser (Option String) := do
  ws
  let duplicate ← preflightValue
  eof
  pure duplicate

private def duplicateMember? (input : String) : Except String (Option String) :=
  Parser.run preflight input

private def parseAfterSafety (input : String) : Except Error Lean.Json :=
  match Lean.Json.parse input with
  | .error message => .error (.invalidJson message)
  | .ok json =>
      match duplicateMember? input with
      | .error message => .error (.invalidJson message)
      | .ok (some name) => .error (.duplicateMember name)
      | .ok none => .ok json

def parse (input : String) : Except Error Lean.Json := do
  safetyPreflight false input
  parseAfterSafety input

/-- Parse retained, trusted evidence JSON with the same duplicate, nesting, and numeric
resource guards as normalized protocol JSON, while additionally admitting canonical signed
integers. Evidence projections may contain typed negative operands; protocol v1 transports
exact A12 decimals as strings and therefore continues to reject every signed JSON number. -/
def parseEvidence (input : String) : Except Error Lean.Json := do
  safetyPreflight true input
  parseAfterSafety input

private def duplicateOf : Except Error Lean.Json → Option String
  | .error (.duplicateMember name) => some name
  | .error (.invalidJson _) | .error .nonCanonicalNumber |
      .error (.resourceLimit _) | .ok _ => none

private def isInvalidJson : Except Error Lean.Json → Bool
  | .error (.invalidJson _) => true
  | .error (.duplicateMember _) | .error .nonCanonicalNumber |
      .error (.resourceLimit _) | .ok _ => false

private def errorOf : Except Error Lean.Json → Option Error
  | .error error => some error
  | .ok _ => none

example : (parse "{\"outer\":{\"items\":[1,true,null,{\"name\":\"ok\"}]}}").isOk = true := by
  native_decide

example : isInvalidJson (parse "{\"missing\":}") = true := by
  native_decide

example : duplicateOf (parse "{\"name\":1,\"name\":2}") = some "name" := by
  native_decide

example : duplicateOf (parse "{\"outer\":{\"name\":1,\"name\":2}}") = some "name" := by
  native_decide

example : (parse "[{\"name\":1},{\"name\":2}]").isOk = true := by
  native_decide

example : errorOf (parse "{\"value\":1e100000000}") = some .nonCanonicalNumber := by
  native_decide

example : (parseEvidence "{\"value\":-1}").isOk = true := by
  native_decide

example : errorOf (parseEvidence "{\"value\":-0}") = some .nonCanonicalNumber := by
  native_decide

example : duplicateOf (parseEvidence "{\"value\":-1,\"value\":-2}") = some "value" := by
  native_decide

example : errorOf (parseEvidence "{\"value\":-1e100000000}") = some .nonCanonicalNumber := by
  native_decide

example : errorOf (parse "{\"value\":12345678901234567}") =
    some (.resourceLimit .numberCharacters) := by
  native_decide

example : errorOf (parse (String.ofList (List.replicate (maxNesting + 1) '[') ++ "0" ++
    String.ofList (List.replicate (maxNesting + 1) ']'))) =
    some (.resourceLimit .nesting) := by
  native_decide

example : (parse "{\"text\":\"1e100000000 [[[[\"}").isOk = true := by
  native_decide

end A12Kernel.Reference.StrictJson
