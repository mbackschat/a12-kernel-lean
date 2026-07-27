import A12Kernel.Elaboration.ValueAsDateTimeNumberFields

/-! # Partial-Date and Number-field `Time(...)` locks -/

namespace A12Kernel.Conformance.ValueAsDateTimeNumberFields

open A12Kernel

private def componentField
    (id : FieldId) (constraints : NumericTargetConstraints)
    (info : NumField := { scale := 0, signed := false }) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"Component{id}"
  policy := { kind := .number info }
  numericTargetConstraints := constraints
}

/- `Time(...)` checks the Number declaration's stored-length or exact-value bound; an
   integer-digit cap with the same numeral is not a substitute. -/
example :
    let storedLengthModel : FlatModel := {
      fields := [componentField 1 { maxStoredLength := some 2 }]
    }
    let integerDigitsModel : FlatModel := {
      fields := [componentField 1 { maxIntegerDigits := some 2 }]
    }
    (elaborateTimeNumberFields storedLengthModel
        (.hour 1)).isOk = true ∧
      (elaborateTimeNumberFields integerDigitsModel
        (.hour 1)).isOk = false := by
  native_decide

/- Fractional declarations and a position-specific maximum copied to the wrong slot are
   rejected before the document is read. -/
example :
    let fractional : FlatModel := {
      fields := [componentField 1 { maxStoredLength := some 2 }
        { scale := 1, signed := false }]
    }
    let hourBoundAtMinute : FlatModel := {
      fields := [componentField 1 { maximum := some 23 }]
    }
    (elaborateTimeNumberFields fractional (.hour 1)).isOk = false ∧
      (elaborateTimeNumberFields hourBoundAtMinute (.minute 1 1)).isOk = false := by
  native_decide

/- A signed declaration needs an explicit nonnegative minimum; the exact position maximum
   then remains a legal alternative to the stored-length bound. -/
example :
    let signedWithoutMinimum : FlatModel := {
      fields := [componentField 1 { maximum := some 23 }
        { scale := 0, signed := true }]
    }
    let signedWithMinimum : FlatModel := {
      fields := [componentField 1 { minimum := some 0, maximum := some 23 }
        { scale := 0, signed := true }]
    }
    (elaborateTimeNumberFields signedWithoutMinimum (.hour 1)).isOk = false ∧
      (elaborateTimeNumberFields signedWithMinimum (.hour 1)).isOk = true := by
  native_decide

end A12Kernel.Conformance.ValueAsDateTimeNumberFields
