import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.LegalCharset — supported-character definitions and scanning

This capsule models the pure full-formal-check charset boundary. Java-compatible Unicode grapheme clustering is injected only while a model definition is admitted; the resulting bounded singleton/range and atomic-entry representation is platform-independent. Computed-target basic checks deliberately do not call this boundary.
-/

namespace A12Kernel

/-- One admitted inclusive BMP singleton or range. Checked construction establishes endpoint order. -/
structure LegalCharRange where
  first : Char
  last : Char
  deriving Repr, DecidableEq

/-- Every admitted combined entry is surrogate-free and exactly two or three UTF-16 units. Encoding that bound in the constructors makes zero progress and unbounded matching unrepresentable. -/
inductive LegalCharAtom where
  | pair (first second : Char)
  | triple (first second third : Char)
  deriving Repr, DecidableEq

namespace LegalCharAtom

def characters : LegalCharAtom → List Char
  | .pair first second => [first, second]
  | .triple first second third => [first, second, third]

def length : LegalCharAtom → Nat
  | .pair _ _ => 2
  | .triple _ _ _ => 3

end LegalCharAtom

/-- The absent/empty model definition is semantically distinct from an explicitly restricted set. -/
inductive LegalCharset where
  | defaultBmp
  | restricted (ranges : List LegalCharRange) (atoms : List LegalCharAtom)
  deriving Repr, DecidableEq

def isBmpScalar (character : Char) : Bool :=
  character.toNat < 0x10000

def LegalCharRange.contains (range : LegalCharRange) (character : Char) : Bool :=
  range.first.toNat ≤ character.toNat && character.toNat ≤ range.last.toNat

def startsWithCharacters (input leading : List Char) : Bool :=
  input.take leading.length == leading

private def LegalCharAtom.matchesPrefix (atom : LegalCharAtom) (input : List Char) : Bool :=
  startsWithCharacters input atom.characters

private def chooseLongerMatchingAtom (input : List Char)
    (selected : Option LegalCharAtom) (candidate : LegalCharAtom) :
    Option LegalCharAtom :=
  if candidate.matchesPrefix input then
    match selected with
    | none => some candidate
    | some previous =>
        if previous.length < candidate.length then some candidate else selected
  else
    selected

private def longestMatchingAtom? (atoms : List LegalCharAtom)
    (input : List Char) : Option LegalCharAtom :=
  atoms.foldl (chooseLongerMatchingAtom input) none

def restrictedAllows (ranges : List LegalCharRange) (character : Char) : Bool :=
  ranges.any (·.contains character)

/-- A fuel-bounded left-to-right scan. Checked atomic constructors consume two or three characters, while the fallback consumes exactly one, so input length is sufficient fuel and every successful step advances. -/
private def scanRestricted (ranges : List LegalCharRange)
    (atoms : List LegalCharAtom) : Nat → List Char → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | _ + 1, [] => true
  | fuel + 1, input@(leading :: remaining) =>
      match longestMatchingAtom? atoms input with
      | some atom => scanRestricted ranges atoms fuel (input.drop atom.length)
      | none =>
          if restrictedAllows ranges leading then
            scanRestricted ranges atoms fuel remaining
          else
            false

namespace LegalCharset

/-- Whether the complete input can be consumed. The default rejects supplementary-plane scalars; a restricted set first consumes the longest complete configured atom, then falls back to one leading singleton/range character. -/
def accepts (charset : LegalCharset) (value : String) : Bool :=
  match charset with
  | .defaultBmp => value.toList.all isBmpScalar
  | .restricted ranges atoms =>
      scanRestricted ranges atoms value.toList.length value.toList

/-- Apply the full-input charset baseline at the shared checked-cell boundary. This stage retains admitted raw text for later scalar parsing/normalization and emits the ordinary formal cause on failure. -/
def checkRawText (charset : LegalCharset) (raw : RawCell String) : CheckedCell String :=
  checkRawCellWith (fun text =>
    if charset.accepts text then .ok (some text)
    else .error .unsupportedCharacter) raw

end LegalCharset

end A12Kernel
