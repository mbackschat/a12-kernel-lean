import A12Kernel.Elaboration.CheckedDocument

/-! # Stored Number input and formal-read locks -/

namespace A12Kernel.Conformance.NumericInput

open A12Kernel

private def ordinaryNumber : NumField := { scale := 2, signed := true }

/- Decimal-valued input strips trailing fractional zeroes and then applies the declared minimum scale; String-valued input stays verbatim. The selected text does not replace exact decimal source identity. -/
example :
    let decimal : NumericStoredInput :=
      .decimal { unscaled := 25000, scale := 2 }
    decimal.formalReadText 0 = "250" ∧
      decimal.formalReadText 2 = "250.00" ∧
      decimal.sourceIdentity =
        .decimal { unscaled := 25000, scale := 2 } ∧
      (NumericStoredInput.text "250.00").formalReadText 0 = "250.00" ∧
      (NumericStoredInput.text "250.00").sourceIdentity =
        .nonComputedForm := by
  native_decide

/- Negative decimal scale is retained as exact input identity even though plain storage and formal-read text expand it without exponent notation. It cannot equal canonical computed output. -/
example :
    let decimal : NumericStoredInput :=
      .decimal { unscaled := 1, scale := -5 }
    decimal.storedText = "100000" ∧
      decimal.formalReadText 0 = "100000" ∧
      decimal.sourceIdentity = .nonComputedForm := by
  native_decide

/- Length is applied after regime selection. These two pairs distinguish strip-and-minimum-scale projection from unconditional use of either stored spelling or parsed amount. -/
example :
    let strips : NumericTargetConstraints := {
      minStoredLength := some 4
    }
    let pads : NumericTargetConstraints := {
      minFractionalDigits := 2
      maxStoredLength := some 5
    }
    (match strips.checkFormalRead ordinaryNumber
        (.decimal { unscaled := 25000, scale := 2 }) with
      | .error .textTooShort => true
      | _ => false) &&
    (match strips.checkFormalRead ordinaryNumber (.text "250.00") with
      | .ok ("250.00", 250) => true
      | _ => false) &&
    (match pads.checkFormalRead ordinaryNumber
        (.decimal { unscaled := 250, scale := 0 }) with
      | .error .textTooLong => true
      | _ => false) &&
    (match pads.checkFormalRead ordinaryNumber (.text "250") with
      | .error .decimalSeparatorRequired => true
      | _ => false) = true := by
  native_decide

/- String-valued leading zeroes remain lexical input: the declaration decides whether they are admitted. Decimal-valued input cannot manufacture that spelling. -/
example :
    let forbidden : NumericTargetConstraints := {}
    let allowed : NumericTargetConstraints := {
      leadingZerosAllowed := true
    }
    (match forbidden.checkFormalRead ordinaryNumber (.text "0250") with
      | .error .leadingZerosNotAllowed => true
      | _ => false) &&
    (match allowed.checkFormalRead ordinaryNumber (.text "0250") with
      | .ok ("0250", 250) => true
      | _ => false) = true := by
  native_decide

/- The formal-read grammar is the ordinary dot-decimal channel, not host parsing: plus, exponent, whitespace, comma, a missing integer part, and a trailing separator are rejected. -/
example :
    ["+1", "1e2", " 1", "1 ", "1,0", ".5", "1."].all
      (parseNumericFormalRead? · |>.isNone) = true := by
  native_decide

private def verbatimFailure (constraints : NumericTargetConstraints) (info : NumField)
    (text : String) : Option NumericFormalReadError :=
  match constraints.checkFormalRead info (.text text) with
  | .error error => some error
  | .ok _ => none

/- The plus-signed number is refused before it is read, while any other plus-led text is unreadable.
A minus on a zero is the sign class on an unsigned field, except on a zero-forbidding amount field,
which reports the zero class; `-5.00` there keeps the sign class (peer kf276; K16 rows `d02`, `d03`). -/
example :
    let unsigned : NumField := { scale := 2, signed := false }
    let money : NumericTargetConstraints := { zeroAllowed := false, amount := true }
    let noZero : NumericTargetConstraints := { zeroAllowed := false }
    verbatimFailure {} ordinaryNumber "+007" = some .leadingPlus ∧
      verbatimFailure {} ordinaryNumber "+00.00" = some .leadingPlus ∧
      verbatimFailure {} ordinaryNumber "+1,5" = some .malformed ∧
      verbatimFailure {} ordinaryNumber "+" = some .malformed ∧
      verbatimFailure {} ordinaryNumber "-00" = some .signedZero ∧
      verbatimFailure money unsigned "-0.00" = some .zeroNotAllowed ∧
      verbatimFailure noZero unsigned "-0.00" = some .negativeNotAllowed ∧
      verbatimFailure money unsigned "-5.00" = some .negativeNotAllowed ∧
      NumericFormalReadError.leadingPlus.errorCode = "zahlMitPlus" ∧
      NumericFormalReadError.decimalSeparatorRequired.errorCode = "zahlOhneDezimalTrenner" := by
  native_decide

private def decimalFailure (constraints : NumericTargetConstraints) (info : NumField)
    (unscaled : Int) (scale : Int) : Option NumericFormalReadError :=
  match constraints.checkFormalRead info (.decimal { unscaled, scale }) with
  | .error error => some error
  | .ok _ => none

/-- The `FormalNum` capture's `MC`: four constraints that let a single value choose between them. -/
private def moneyCents : NumericTargetConstraints := {
  minFractionalDigits := 2, maxIntegerDigits := some 4, zeroAllowed := false, amount := true
  minStoredLength := some 4, maxStoredLength := some 8, minimum := some 1, maximum := some 5000 }

private def capped : NumericTargetConstraints := { minimum := some 10, maximum := some 20 }

/- The cascade's order decides which of several violated constraints is reported. The fifteen-digit
ceiling outranks the integer cap, length and maximum the same value also violates; an unsigned
declaration reports the sign before the bound; the integer cap outranks the maximum; and the
maximum alone decides once nothing earlier fails. -/
example :
    let unsignedInteger : NumField := { scale := 0, signed := false }
    decimalFailure moneyCents ordinaryNumber 1234567890123456 0 = some .totalDigitsTooLong ∧
      decimalFailure capped unsignedInteger (-5) 0 = some .negativeNotAllowed ∧
      decimalFailure capped { unsignedInteger with signed := true } (-5) 0 = some .belowMinimum ∧
      decimalFailure moneyCents ordinaryNumber 9999900 2 = some .integerDigitsTooLong ∧
      decimalFailure capped { unsignedInteger with signed := true } 25 0 = some .aboveMaximum ∧
      decimalFailure moneyCents ordinaryNumber 150000 2 = none := by
  native_decide

/- A separator is refused outright only when no fractional place is declared; a declared range is a
range with both ends admitted. Decimal input reaches zero at the declared scale, so a two-place
zero-forbidding field reports zero, while the same zero kept as text lacks its separator. -/
example :
    let integer : NumField := { scale := 0, signed := true }
    let range : NumericTargetConstraints := { minFractionalDigits := 1 }
    let threePlaces : NumField := { scale := 3, signed := true }
    decimalFailure {} integer 15 1 = some .decimalSeparatorForbidden ∧
      decimalFailure moneyCents ordinaryNumber 51234 4 = some .fractionalDigitsOutOfRange ∧
      decimalFailure range threePlaces 12345 3 = none ∧
      decimalFailure range threePlaces 51234 4 = some .fractionalDigitsOutOfRange ∧
      decimalFailure moneyCents ordinaryNumber 0 0 = some .zeroNotAllowed ∧
      verbatimFailure moneyCents ordinaryNumber "0" = some .decimalSeparatorRequired := by
  native_decide

/- Length counts the selected text rather than the digits, so the same magnitude passes the minimum
once it carries a sign (the `FormalNum` capture's `ZNoZero`). -/
example :
    let integer : NumField := { scale := 0, signed := true }
    let noZero : NumericTargetConstraints :=
      { zeroAllowed := false, minStoredLength := some 2, maxStoredLength := some 4 }
    decimalFailure noZero integer 5 0 = some .textTooShort ∧
      decimalFailure noZero integer (-5) 0 = none ∧
      decimalFailure noZero integer 123456 0 = some .textTooLong := by
  native_decide

private def numberField (id : FieldId) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"Number{id}"
  policy := { kind := .number ordinaryNumber }
}

private def model : FlatModel := {
  fields := [numberField 1, numberField 2]
}

private def checked? : Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      {
        address := { field := 1, path := [] }
        stored := "250.00"
        raw := .parsed (.num 250)
        numericDecimal := some { unscaled := 25000, scale := 2 }
      },
      {
        address := { field := 2, path := [] }
        stored := "250.00"
        raw := .parsed (.num 250)
      }
    ]
  } |>.toOption

/- One checked document retains equal parsed amounts together with the independently observable formal-read texts required by `FieldValueAsString`. -/
example : (do
    let checked ← checked?
    let decimal ←
      checked.observeNumberFormalRead .validation { field := 1, path := [] }
        |>.toOption
    let text ←
      checked.observeNumberFormalRead .validation { field := 2, path := [] }
        |>.toOption
    pure (decimal, text)) =
      some (.value "250", .value "250.00") := by
  native_decide

end A12Kernel.Conformance.NumericInput
