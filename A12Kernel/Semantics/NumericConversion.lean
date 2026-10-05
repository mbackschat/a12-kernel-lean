import A12Kernel.Semantics.FlatValidation

/-! Certified text-source representation and exact decimal conversion shared by numeric consumers. -/

namespace A12Kernel

/-- Kernel 30.8.1's authored Number digit budget for String/Enumeration conversion. Dot and leading minus do not consume the budget. -/
def maxFieldValueAsNumberDigits : Nat := 15

/-- One exactly parsed Java-host decimal token together with the static facts used by `FieldValueAsNumber` admission. Leading zeros and negative zero are retained only through digit count/scale; numeric evaluation observes their exact rational amount. -/
structure ParsedJavaDecimalToken where
  value : Rat
  scale : Nat
  digitCount : Nat
  deriving Repr, DecidableEq

private def parseJavaDecimalDigitsAllowEmpty
    (characters : List Char) : Option Nat :=
  if characters.isEmpty then some 0
  else parseJava21BmpNatural? (String.ofList characters)

/-- Parse exactly the Java 21 `NumberUtils.isParsable` decimal fragment consumed by ordinary numeric Enumeration values: optional leading minus, at most one dot, at least one digit, and no trailing dot. A leading dot is legal. Digit-budget admission remains a separate model check. -/
def parseJavaDecimalToken? (input : String) : Option ParsedJavaDecimalToken := do
  let (negative, characters) := match input.toList with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  let (wholeCharacters, suffix) := characters.span (· != '.')
  let (fractionCharacters, scale) ← match suffix with
    | [] => some ([], 0)
    | '.' :: fraction =>
        if fraction.isEmpty then none else some (fraction, fraction.length)
    | _ => none
  if wholeCharacters.isEmpty && fractionCharacters.isEmpty then
    none
  else
    let whole ← parseJavaDecimalDigitsAllowEmpty wholeCharacters
    let fraction ← parseJavaDecimalDigitsAllowEmpty fractionCharacters
    let factor := 10 ^ scale
    let magnitude : Rat := whole + (fraction : Rat) / factor
    some {
      value := if negative then -magnitude else magnitude
      scale
      digitCount := wholeCharacters.length + fractionCharacters.length }

/-- Derive the conversion result scale only when every selected token belongs to the pinned Java-host decimal profile and stays within the kernel digit budget. -/
def CheckedEnumerationProjection.numericScale?
    (checked : CheckedEnumerationProjection) : Option Nat := do
  let parsed ← checked.selectedTokens.mapM parseJavaDecimalToken?
  if parsed.all (fun token => token.digitCount ≤ maxFieldValueAsNumberDigits) then
    some (parsed.foldl (fun scale token => max scale token.scale) 0)
  else
    none

/-- One ordinary String or closed Enumeration/category source statically certified for `FieldValueAsNumber`. The source reuses the shared textual operand and keeps its derived non-expandable scale alongside it. -/
structure ResolvedFieldValueAsNumberSource where
  operand : FlatTextFieldOperand
  scale : Nat
  deriving Repr, DecidableEq

namespace ResolvedFieldValueAsNumberSource

def fieldId (source : ResolvedFieldValueAsNumberSource) : FieldId :=
  source.operand.field.id

def projectionRef (source : ResolvedFieldValueAsNumberSource) :
    EnumerationProjectionRef :=
  match source.operand with
  | .string _ => .stored
  | .enumeration operand => operand.projectionRef

/-- Project the exact checked String or stored/category Enumeration token without introducing a conversion-specific text operand. -/
def tokenForValue? (source : ResolvedFieldValueAsNumberSource) :
    Value → Option String
  | .str token =>
      match source.operand with
      | .string _ =>
          if matchesAsciiDigitsPattern token then some token else none
      | .enumeration _ => none
  | .enum stored =>
      match source.operand with
      | .string _ => none
      | .enumeration operand => operand.projection.tokenFor? stored
  | _ => none

def valueFor? (source : ResolvedFieldValueAsNumberSource)
    (value : Value) : Option Rat := do
  let token ← source.tokenForValue? value
  let parsed ← parseJavaDecimalToken? token
  pure parsed.value

end ResolvedFieldValueAsNumberSource

/-- Empty conversion supplies symmetric zero; reached malformed tokens remain unavailable (spec/04). -/
def ResolvedFieldValueAsNumberSource.observeOperand (source : ResolvedFieldValueAsNumberSource) :
    CellObservation → NumericOperand
  | .empty => .value 0 .both
  | .value value =>
      match source.valueFor? value with
      | some amount => .value amount .fixed
      | none => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

end A12Kernel
