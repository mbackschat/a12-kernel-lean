import A12Kernel.Reference.Dm.Document

/-! # Locks for the DM-JSON document reader

The reader stands where the Kernel's document conversion stands, so it owns the conversion's choices:
a Number text the conversion parses becomes decimal-valued and is read through the runtime rendering
(spec §4, storage regimes), a leading-zero value on a field allowing leading zeros stays text, a
Boolean token is read regardless of case, and a JSON `null` is a field present without a value. Each
case pins one choice against the reading that treats the document's text as user input.
-/

namespace A12Kernel.Dm.ReaderLocks

open Lean A12Kernel A12Kernel.Dm

/- The conversion grammar is Java `BigDecimal`'s: a sign, an exponent and a bare point are accepted,
and the scale is the written fraction less the exponent. -/
example :
    [convertedDecimal? "30" == some { unscaled := 30, scale := 0 },
     convertedDecimal? "+5" == some { unscaled := 5, scale := 0 },
     convertedDecimal? "-2.50" == some { unscaled := -250, scale := 2 },
     convertedDecimal? "1e5" == some { unscaled := 1, scale := -5 },
     convertedDecimal? ".5" == some { unscaled := 5, scale := 1 },
     convertedDecimal? "12a" == none,
     convertedDecimal? "" == none].all id := by
  native_decide

private def amount (constraints : NumericTargetConstraints) : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Amount", numericTargetConstraints := constraints
    policy := { kind := .number { scale := 2, signed := true } } }

private def model (declaration : FlatFieldDecl) : FlatModel := { fields := [declaration] }

private def classified (declaration : FlatFieldDecl) (stored : String) : Option ClassifiedCellInput :=
  (classifyStored (model declaration) declaration { field := 0, path := [] } stored).toOption

/- `30` on a field declaring two minimum fraction digits is read as `30.00` and is clean, where the
same text taken as user input lacks its separator; a leading-zero value on a field allowing leading
zeros keeps the text regime. -/
example :
    [(classified (amount { minFractionalDigits := 2 }) "30").map (·.raw) ==
       some (.parsed (.num 30)),
     (classified (amount { minFractionalDigits := 2 }) "30").bind (·.numericDecimal) ==
       some { unscaled := 30, scale := 0 },
     (classified (amount { leadingZerosAllowed := true }) "007").bind (·.numericDecimal) == none].all id := by
  native_decide

private def flag : FlatFieldDecl := { id := 0, groupPath := ["Order"], name := "Flag", policy := { kind := .boolean } }

/- A Boolean token is read regardless of case. -/
example :
    (classified flag "TRUE").map (·.stored) = some "true" := by
  native_decide

/- A JSON `null` places the field present and empty; a missing key places nothing. -/
example :
    let dm : DmModel := { flat := model flag, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    [((readDocument dm (Json.mkObj [("Order", Json.mkObj [("Flag", Json.null)])])).toOption.map
        (·.data.cells.map (·.raw))) == some [.presentEmpty],
     ((readDocument dm (Json.mkObj [("Order", Json.mkObj [])])).toOption.map
        (·.data.cells.length)) == some 0].all id := by
  native_decide

end A12Kernel.Dm.ReaderLocks
