import A12Kernel.Semantics.NumericInput

/-! # Decimal-node text at the document ingestion boundary -/

namespace A12Kernel.NumericInputDecimal

/-- Canonical decimal-node text before field conversion. The typed document reader uses
BigDecimal's scale-preserving notation (spec §4); unconditional plain rendering loses negative scale. -/
def wireText (value : NumericInputDecimal) : String :=
  let digits := toString value.unscaled.natAbs
  let adjusted : Int := (digits.length : Int) - 1 - value.scale
  if value.scale >= 0 && adjusted >= -6 then value.storedText
  else
    let coefficient := String.ofList (digits.toList.take 1) ++
      (if digits.length > 1 then "." ++ String.ofList (digits.toList.drop 1) else "")
    (if value.unscaled < 0 then "-" else "") ++ coefficient ++ "E" ++
      (if adjusted >= 0 then "+" else "") ++ toString adjusted

end A12Kernel.NumericInputDecimal
