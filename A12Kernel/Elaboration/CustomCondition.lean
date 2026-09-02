import A12Kernel.Semantics.CustomCondition

/-! # Checked `CustomCondition` names

This module checks the two normalized `nameOhnePunkt` token alternatives used by [`CustomCondition`](../../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch). The lexer supplies an unquoted or quote-escaped spelling after removing quote delimiters. Locale-specific reserved terminals remain an explicit caller-owned predicate; the checked result retains both the normalized callback key and whether quoting escaped that terminal classification.

Raw tokenization, the locale's terminal inventory, callback registration, host failures, and rule orchestration remain outside this boundary.
-/

namespace A12Kernel

/-- The two lexer-distinguished ways to author one normalized custom-condition name. -/
inductive CustomConditionNameSpelling where
  | unquoted (value : String)
  | quoted (value : String)
  deriving Repr, DecidableEq

namespace CustomConditionNameSpelling

def value : CustomConditionNameSpelling → String
  | .unquoted value | .quoted value => value

def wasQuoted : CustomConditionNameSpelling → Bool
  | .unquoted _ => false
  | .quoted _ => true

end CustomConditionNameSpelling

/-- One lexer-normalized name whose character and reservation constraints have been checked. -/
structure CheckedCustomConditionName where
  private mk ::
  spelling : CustomConditionNameSpelling
  deriving Repr, DecidableEq

namespace CheckedCustomConditionName

/-- The normalized key supplied to callback registration lookup. -/
def value (name : CheckedCustomConditionName) : String :=
  name.spelling.value

/-- Whether single quotes escaped locale-specific terminal classification. -/
def wasQuoted (name : CheckedCustomConditionName) : Bool :=
  name.spelling.wasQuoted

end CheckedCustomConditionName

private def isAsciiLetter (character : Char) : Bool :=
  decide (character.toNat >= 'a'.toNat && character.toNat <= 'z'.toNat) ||
    decide (character.toNat >= 'A'.toNat && character.toNat <= 'Z'.toNat)

private def isAsciiDigit (character : Char) : Bool :=
  decide (character.toNat >= '0'.toNat && character.toNat <= '9'.toNat)

private def isNameNonDigit (character : Char) : Bool :=
  isAsciiLetter character || character == '_' || character == ':' ||
    character == 'Ä' || character == 'Ü' || character == 'Ö' ||
    character == 'ä' || character == 'ü' || character == 'ö' ||
    character == 'ß'

private def isNameCharacter (character : Char) : Bool :=
  isNameNonDigit character || isAsciiDigit character

private def isUnquotedName (value : String) : Bool :=
  !value.isEmpty && value.toList.all isNameCharacter

private def isQuotedName (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest => isNameNonDigit first && rest.all isNameCharacter

/-- Check one lexer-normalized spelling. Unquoted locale terminals are refused; quoting bypasses only terminal classification and still enforces the narrower non-digit first character. -/
def checkCustomConditionName (isReserved : String → Bool)
    (spelling : CustomConditionNameSpelling) :
    Option CheckedCustomConditionName :=
  match spelling with
  | .unquoted value =>
      if isUnquotedName value && !isReserved value then
        some ⟨spelling⟩
      else
        none
  | .quoted value =>
      if isQuotedName value then some ⟨spelling⟩ else none

end A12Kernel
