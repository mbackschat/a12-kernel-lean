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
