import A12Kernel.Conformance.NumericValidation.Support

/-! # Checked numeric-validation conversion locks -/

namespace A12Kernel.Conformance.NumericValidation.Conversion

open A12Kernel
open A12Kernel.Conformance.NumericValidation.Support

/- The checked decimal-token parser follows Java 21's UTF-16 `Character.isDigit(char)` profile without widening it to supplementary-plane decimal code points. -/
example :
    (parseJavaDecimalToken? "-1.50").map
        (fun token => (token.value, token.scale, token.digitCount)) =
      some ((-3 / 2 : Rat), 2, 3) ∧
    (parseJavaDecimalToken? ".5").map (fun token => token.value) =
      some (1 / 2 : Rat) ∧
    (parseJavaDecimalToken? "١٢.٥").map
        (fun token => (token.value, token.scale, token.digitCount)) =
      some ((25 / 2 : Rat), 1, 3) ∧
    (parseJavaDecimalToken? "-３").map (fun token => token.value) =
      some (-3 : Rat) ∧
    parseJavaDecimalToken? "𐒠" = none ∧
    parseJavaDecimalToken? "1." = none ∧
    parseJavaDecimalToken? "+1" = none ∧
    parseJavaDecimalToken? "1e2" = none ∧
    parseJavaDecimalToken? " 1" = none := by
  native_decide

/- `FieldValueAsNumber` projects stored or category tokens before exact rational conversion; a filled result is fixed. -/
example :
    verdictOf (comparison .equal (fieldValueAsNumber) 2 2)
        (enumerationRaw (.parsed (.enum "2"))) = some (.fired .value) ∧
      verdictOf (comparison .equal
        (fieldValueAsNumber (.category
          (path ["Order"] "NumericChoice") "Factor")) (1 / 2) 2)
        (enumerationRaw (.parsed (.enum "-1.50"))) = some (.fired .value) ∧
      verdictOf (comparison .equal (fieldValueAsNumber) 3 2)
        (enumerationRaw (.parsed (.enum "03"))) = some (.fired .value) ∧
      verdictOf (comparison .less (fieldValueAsNumber) 100)
        (enumerationRaw (.parsed (.enum "2"))) = some (.fired .value) := by
  native_decide

/- The same checked conversion accepts the exact bounded value-validating String profile and the host-decimal Enumeration domain. -/
example :
    verdictOf (comparison .equal
        (fieldValueAsNumber (.direct (path ["Order"] "NumericCode"))) 123)
        (fieldRaw 17 (.parsed (.str "123"))) = some (.fired .value) ∧
      verdictOf (comparison .less
        (fieldValueAsNumber (.direct (path ["Order"] "NumericCode"))) 100)
        (fieldRaw 17 .empty) = some (.fired .omission) ∧
      verdictOf (comparison .equal
        (fieldValueAsNumber (.direct (path ["Order"] "NumericCode"))) 0)
        (fieldRaw 17 (.parsed (.str "12A"))) = some .unknown ∧
      verdictOf (comparison .equal
        (fieldValueAsNumber (.direct (path ["Order"] "NumericCode"))) 12)
        (fieldRaw 17 (.parsed (.str "١٢"))) = some .unknown ∧
      verdictOf (comparison .equal
        (fieldValueAsNumber (.direct (path ["Order"] "HostDigitChoice")))
        (25 / 2) 1)
        (fieldRaw 21 (.parsed (.enum "١٢.٥"))) = some (.fired .value) := by
  native_decide

/- An absent convertible source denotes zero with both directional fill possibilities, while a reached formal cause remains unknown. -/
example :
    verdictOf (comparison .less (fieldValueAsNumber) 100)
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater (fieldValueAsNumber) (-100))
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .equal (fieldValueAsNumber) 0 2)
        (enumerationRaw (.rejected .declaredConstraint)) = some .unknown := by
  native_decide

/- Admission derives the selected-domain scale and preserves the exact String pattern/length and Enumeration-domain gates. -/
example :
    (elaborateNumericComparison model ["Order"]
      (twoSided .equal (fieldValueAsNumber) (atom "Scale2"))).isOk = true ∧
    (elaborateNumericComparison model ["Order"]
      (twoSided .equal
        (fieldValueAsNumber (.category
          (path ["Order"] "NumericChoice") "Whole")) (atom "U"))).isOk = true ∧
    (elaborateNumericComparison model ["Order"]
      (comparison .greater
        (fieldValueAsNumber (.direct
          (path ["Order"] "BoundaryChoice"))) 0)).isOk = true ∧
    (elaborateNumericComparison model ["Order"]
      (comparison .greater
        (fieldValueAsNumber (.direct
          (path ["Order"] "NumericCode"))) 0)).isOk = true ∧
    (elaborateNumericComparison model ["Order"]
      (comparison .equal
        (fieldValueAsNumber (.direct
          (path ["Order"] "HostDigitChoice"))) (25 / 2) 1)).isOk = true ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "Missing"))) 0) =
        some (.resolve (.invalidEntity (path ["Order"] "Missing"))) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "Code"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "Code"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "MixedChoice"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "MixedChoice"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "WideChoice"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "WideChoice"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "WrongPatternCode"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "WrongPatternCode"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "UnboundedCode"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "UnboundedCode"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct (path ["Order"] "WideCode"))) 0) =
        some (.fieldValueAsNumberNotConvertible ["Order", "WideCode"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.direct
        (path ["Order"] "SupplementaryDigitChoice"))) 0) =
        some (.fieldValueAsNumberNotConvertible
          ["Order", "SupplementaryDigitChoice"]) ∧
    errorOf (comparison .equal
      (fieldValueAsNumber (.category
        (path ["Order"] "NumericChoice") "Missing")) 0) =
        some (.fieldValueAsNumberEnumeration ["Order", "NumericChoice"]
          (.unknownCategory "Missing")) := by
  native_decide

/- The operation-form rounding wrapper is legal over the converted numeric atom, uses the selected category token, replaces its static scale with the authored places, and preserves symmetric missing fillability. -/
example :
    verdictOf (comparison .equal
        (.round .halfUp omittedRoundingPlaces
          (fieldValueAsNumber (.category
            (path ["Order"] "NumericChoice") "Factor"))) 1)
        (enumerationRaw (.parsed (.enum "-1.50"))) = some (.fired .value) ∧
      verdictOf (comparison .less
        (.round .halfUp omittedRoundingPlaces fieldValueAsNumber) 100)
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater
        (.round .halfUp omittedRoundingPlaces fieldValueAsNumber) (-100))
        (enumerationRaw .empty) = some (.fired .omission) ∧
      (elaborateNumericComparison model ["Order"]
        (twoSided .equal
          (.round .halfUp omittedRoundingPlaces fieldValueAsNumber)
          (atom "U"))).isOk = true := by
  native_decide

/- Absolute value is independently legal over the conversion. It preserves the selected source scale, but at missing numeric zero it collapses the impossible shrinking-magnitude direction instead of copying symmetric source fillability. -/
example :
    verdictOf (comparison .equal (.abs fieldValueAsNumber) (3 / 2) 2)
        (enumerationRaw (.parsed (.enum "-1.50"))) = some (.fired .value) ∧
      verdictOf (comparison .less (.abs fieldValueAsNumber) 100)
        (enumerationRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater (.abs fieldValueAsNumber) (-100))
        (enumerationRaw .empty) = some (.fired .value) ∧
      (elaborateNumericComparison model ["Order"]
        (twoSided .equal (.abs fieldValueAsNumber) (atom "Scale2"))).isOk = true := by
  native_decide

/- `RangeAsNumber` parses only a complete ASCII digit slice; filled fallback zero is fixed. -/
example :
    verdictOf (comparison .equal (stringRange 1 2) 12)
        (stringRaw (.parsed (.str "12X"))) = some (.fired .value) ∧
      verdictOf (comparison .equal (stringRange 1 2) 0)
        (stringRaw (.parsed (.str "AB3"))) = some (.fired .value) ∧
      verdictOf (comparison .equal (stringRange 1 2) 0)
        (stringRaw (.parsed (.str "A"))) = some (.fired .value) := by
  native_decide

/- Only an absent source makes the nonnegative result growable; a present non-digit zero is fixed. -/
example :
    verdictOf (comparison .less (stringRange 1 2) 100)
        (stringRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater (stringRange 1 2) (-100))
        (stringRaw .empty) = some (.fired .value) ∧
      verdictOf (comparison .less (stringRange 1 2) 100)
        (stringRaw (.parsed (.str "AB"))) = some (.fired .value) := by
  native_decide

/- Both operation-form wrappers admit the nonliteral number-like range source. Rounding and absolute value retain its grow-only missing zero, while ordinary filled selections remain fixed and nonnegative. -/
example :
    verdictOf (comparison .equal
        (.round .halfUp omittedRoundingPlaces (stringRange 1 2)) 12)
        (stringRaw (.parsed (.str "12X"))) = some (.fired .value) ∧
      verdictOf (comparison .less
        (.round .halfUp omittedRoundingPlaces (stringRange 1 2)) 100)
        (stringRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater
        (.round .halfUp omittedRoundingPlaces (stringRange 1 2)) (-100))
        (stringRaw .empty) = some (.fired .value) ∧
      verdictOf (comparison .equal (.abs (stringRange 1 2)) 12)
        (stringRaw (.parsed (.str "12X"))) = some (.fired .value) ∧
      verdictOf (comparison .less (.abs (stringRange 1 2)) 100)
        (stringRaw .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greater (.abs (stringRange 1 2)) (-100))
        (stringRaw .empty) = some (.fired .value) ∧
      (elaborateNumericComparison model ["Order"]
        (twoSided .equal
          (.round .halfUp ⟨2, by decide⟩ (stringRange 1 2))
          (atom "Scale2"))).isOk = true := by
  native_decide

/- The checked String cache is normalized before slicing. -/
example :
    verdictOf (comparison .equal (stringRange 3 3) 2)
      (stringRaw (.parsed (.str "1\r\n2"))) = some (.fired .value) := by
  native_decide

/- A JVM half-surrogate slice has no scalar String representation in Lean and therefore follows the operation's ordinary numeric-zero fallback. -/
example :
    verdictOf (comparison .equal (stringRange 2 2) 0)
      (stringRaw (.parsed (.str "A😀B"))) = some (.fired .value) := by
  native_decide

/- Field shape resolves before the interval; the interval precedes kind admission. -/
example :
    errorOf (comparison .equal
      (.atom (.stringRange (path ["Order"] "Missing") 0 2)) 0) =
        some (.resolve (.invalidEntity (path ["Order"] "Missing"))) ∧
      errorOf (comparison .equal
        (.atom (.stringRange (path ["Order"] "U") 0 2)) 0) =
        some (.invalidStringRange 0 2) ∧
      errorOf (comparison .equal
        (.atom (.stringRange (path ["Order"] "U") 1 2)) 0) =
        some (.rangeOperandNotString ["Order", "U"]) := by
  native_decide


end A12Kernel.Conformance.NumericValidation.Conversion
