import A12Kernel.Elaboration.Flat.Types
import A12Kernel.Elaboration.SemanticIndexAdmission
import A12Kernel.Semantics.ValueFormalCheck

/-! # Whether a constant semantic-index key fits its index field

`[A For "k"]` names a row by a constant, and code generation first asks whether the index field's
type would accept that constant, refusing it `MVK_INDEX_VALUE_INVALID` otherwise. The test is a
**shape, one rule per kind**, not a value check: a Date key `2020-13-45` fits `yyyy-MM-dd`, and a
Number key's integer digits are not counted ([`spec/08`](../../spec/08-paths-and-references.md),
[inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26-index-key-shape)). The semantic-index admission
cascade takes the answer as its constant arm's input, and this module derives it from the
declaration.

**A String key is judged after its line terminators are collapsed**, CRLF to LF with a lone CR kept,
by the declared length bounds and the declared pattern over the whole key, and by nothing else: a key
carrying a line feed fits a field that permits no line breaks
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-key-dialect)). The pattern is Java's and is
injected as a whole-value matcher, as [`StringPattern`](../Semantics/StringPattern.lean) injects it;
the matcher receives a Lean `String`, so it counts code points, which is how the Kernel counts them
here ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-index-key-pattern)). The length bounds reuse
the stored value's UTF-16 count, an assumption: no row measures a key whose two counts differ.

The empty key is not this module's business. The cascade refuses it by a separate disjunct whatever
the type answers.
-/

namespace A12Kernel

/-- A Number key: an optional minus, digits, and a fraction after `.` or `,` whose digit count lies
within the declared bounds, no fraction counting as none. A plus sign is refused. A key with no
integer digit or an empty fraction is refused here too, which no row measures. -/
def numberIndexKeyFits (minFraction maxFraction : Nat) (key : String) : Bool :=
  let body := match key.toList with
    | '-' :: rest => rest
    | characters => characters
  let (integer, rest) := body.span Char.isDigit
  !integer.isEmpty &&
    match rest with
    | [] => minFraction == 0
    | separator :: fraction =>
        (separator == '.' || separator == ',') && !fraction.isEmpty &&
          fraction.all Char.isDigit &&
          minFraction ≤ fraction.length && fraction.length ≤ maxFraction

/-- The characters a temporal format admits, one entry per key character: a component letter admits
any ASCII digit, and a quoted run or any other character admits itself. The admitted formats use
only `y`, `M`, `d`, `H`, `m` and `s`, and a quoted `T`. -/
private def temporalShape : List Char → Bool → List (Option Char)
  | [], _ => []
  | '\'' :: rest, quoted => temporalShape rest !quoted
  | character :: rest, quoted =>
      (if !quoted && character.isAlpha then none else some character) :: temporalShape rest quoted

private def matchesShape : List (Option Char) → List Char → Bool
  | [], [] => true
  | none :: shape, character :: key => character.isDigit && matchesShape shape key
  | some expected :: shape, character :: key => character == expected && matchesShape shape key
  | _, _ => false

/-- A temporal key matches its format one digit per component letter, so no calendar is asked. -/
def temporalIndexKeyFits (format key : String) : Bool :=
  matchesShape (temporalShape format.toList false) key.toList

/-- A date-range key is two dates of the range's format around its separator. -/
def dateRangeIndexKeyFits (format separator key : String) : Bool :=
  let shape := temporalShape format.toList false
  let characters := key.toList
  matchesShape shape (characters.take shape.length) &&
    (characters.drop shape.length).take separator.length == separator.toList &&
    matchesShape shape ((characters.drop shape.length).drop separator.length)

/-- Whether the index field's type accepts a constant key, or `none` where the declaration lacks the
policy its kind needs: a temporal field without its format, a date range without its format pair,
an Enumeration without its tokens, and a String with a custom type, whose own validity would decide
and is not modelled for keys. `patternMatches` is the declared pattern's whole-value matcher and is
read only when a pattern is declared. A Number key's sign is not asked, a signed and an unsigned
field answering alike, which no row separates. -/
def FlatFieldDecl.indexKeyFits? (declaration : FlatFieldDecl)
    (patternMatches : String → Bool) (key : String) : Option Bool :=
  match declaration.policy.kind with
  | .string =>
      if declaration.customType.isSome then none
      else
        let normalized := normalizeLinebreaks key
        some ((declaration.stringPolicy.checkNormalizedLength normalized).toBool &&
          (declaration.stringPatternSource.isNone || patternMatches normalized))
  | .number config =>
      some (numberIndexKeyFits declaration.numericTargetConstraints.minFractionalDigits
        config.scale key)
  | .boolean => some (key == "true" || key == "false")
  | .confirm => some (key == "true")
  | .enumeration => declaration.enumeration.map (·.storedTokens.contains key)
  | .temporal _ _ => declaration.temporalTargetPolicy.map (temporalIndexKeyFits ·.format key)
  | .dateRange => declaration.dateRangePolicy.map fun policy =>
      dateRangeIndexKeyFits policy.format policy.separator key

/-- The admission cascade's constant key, its fit derived from the index field's declaration. -/
def SemanticIndexAdmissionKey.constantFor? (indexField : FlatFieldDecl)
    (patternMatches : String → Bool) (key : String) : Option SemanticIndexAdmissionKey :=
  (indexField.indexKeyFits? patternMatches key).map (.constant key)

end A12Kernel
