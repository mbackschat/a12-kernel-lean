import A12Kernel.Conformance.NumericComputation.Support

/-! # Numeric-computation conversion locks -/

namespace A12Kernel.Conformance.NumericComputation.Conversion

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

/- `FieldValueAsNumber` uses the checked stored/category projection in computation, preserves exact values, and maps clean absence to zero. -/
example :
    checkedResultOf (surfaceFieldValueAsNumber)
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "2")))) = some (.value 2) ∧
      checkedResultOf
        (surfaceFieldValueAsNumber (.category
          (surfacePath ["Root"] "NumericChoice") "Factor"))
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-150")))) = some (.value 5) ∧
      checkedResultOf (surfaceFieldValueAsNumber) = some (.value 0) ∧
      checkedResultOf (surfaceFieldValueAsNumber)
        (context (choice := formalCheck { kind := .enumeration }
          (.rejected .declaredConstraint))) = some (.poison .declaredConstraint) := by
  native_decide

/- `SumOfProducts` is another ordinary numeric atom after its distinct row-aligned source has been checked: the shared expression stages the pair fold before surrounding arithmetic. -/
example :
    let rows := cells3
      (checkedNumber (.parsed (.num 1)))
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 5)))
    let negativeRows := cells3
      (checkedNumber (.parsed (.num (-1))))
      (checkedNumber (.parsed (.num (-3))))
      (checkedNumber (.parsed (.num (-5))))
    let input := repeatableContext (checkedNumber .empty) rows
    checkedCompleteResultOf
        (.binary .add surfaceProductAggregate
          (.literal { value := 1, authoredScale := 0 }))
        input =
        some (.value 45) ∧
      checkedCompleteTargetResultOf
        (.binary .add surfaceProductAggregate
          (.literal { value := 1, authoredScale := 0 }))
        input =
        some (.supported (.accepted { unscaled := 45, scale := 0 })) ∧
      checkedCompleteResultOf (.abs surfaceProductAggregate)
        (repeatableContext (checkedNumber .empty) negativeRows) =
        some (.value 44) := by
  native_decide

/- The product atom cannot cross the scalar compatibility boundary, and malformed common-row topology remains an explicit addressing fault. -/
example :
    let malformedDocument : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    let input := {
      repeatableContext (checkedNumber .empty)
        (fun _ => checkedNumber .empty) with
      document := malformedDocument }
    checkedCompleteScalarFaultOf surfaceProductAggregate =
        some .repeatableContextRequired ∧
      checkedCompleteFaultOf surfaceProductAggregate input =
        some (.repeatableAddressing (.invalidRowDepth 10 [1, 2] 1)) := by
  native_decide

/- String and non-ASCII host-decimal sources enter the same checked computation atom and preserve exact pattern poison. -/
example :
    checkedResultOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "NumericCode")))
        (context (numericCode := numericString.checkRaw
          (.parsed (.str "123")))) = some (.value 123) ∧
      checkedResultOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "NumericCode")))
        (context (numericCode := numericString.checkRaw
          (.parsed (.str "12A")))) = some (.poison .declaredConstraint) ∧
      checkedResultOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "HostDigitChoice")))
        (context (hostDigitChoice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-３")))) = some (.value (-3)) := by
  native_decide

/- The converted atom composes through shared arithmetic and target checking without a conversion-specific write path. -/
example :
    let input := context (checkedNumber (.parsed (.num 3)))
      (choice := formalCheck { kind := .enumeration } (.parsed (.enum "2")))
    checkedResultOf
        (.binary .add (surfaceFieldValueAsNumber)
          (surfaceField ["Root"] "Source")) input = some (.value 5) ∧
      checkedTargetResultOf (surfaceFieldValueAsNumber) false targetPolicy input =
        some (.supported (.accepted { unscaled := 2, scale := 0 })) := by
  native_decide

/- The checked operation-form wrappers consume the converted source through the shared numeric evaluator. Rounding uses the selected category token; absolute value and both wrappers preserve clean zero or exact poison. -/
example :
    let rounded := .round .halfUp omittedRoundingPlaces
      (surfaceFieldValueAsNumber (.category
        (surfacePath ["Root"] "NumericChoice") "Fraction"))
    let absolute := .abs surfaceFieldValueAsNumber
    checkedResultOf rounded
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-150")))) = some (.value 1) ∧
      checkedResultOf absolute
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-150")))) = some (.value 150) ∧
      checkedResultOf rounded = some (.value 0) ∧
      checkedResultOf absolute = some (.value 0) ∧
      checkedResultOf absolute
        (context (choice := formalCheck { kind := .enumeration }
          (.rejected .declaredConstraint))) =
        some (.poison .declaredConstraint) := by
  native_decide

/- Conversion diagnostics preserve resolved source identity and exact category rejection. -/
example :
    checkedErrorOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "Missing"))) =
      some (.resolve (.invalidEntity (surfacePath ["Root"] "Missing"))) ∧
    checkedErrorOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "Wrong"))) =
      some (.fieldValueAsNumberNotConvertible ["Root", "Wrong"]) ∧
    checkedErrorOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "NumericCode"))) = none ∧
    checkedErrorOf
        (surfaceFieldValueAsNumber (.category
          (surfacePath ["Root"] "NumericChoice") "Missing")) =
      some (.fieldValueAsNumberEnumeration ["Root", "NumericChoice"]
        (.unknownCategory "Missing")) := by
  native_decide

/- Numeric computation consumes the same digits-only normalized range and maps every clean fallback to zero. -/
example :
    checkedResultOf (surfaceStringRange 1 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "12X")))) = some (.value 12) ∧
      checkedResultOf (surfaceStringRange 1 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "AB3")))) = some (.value 0) ∧
      checkedResultOf (surfaceStringRange 1 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "A")))) = some (.value 0) ∧
      checkedResultOf (surfaceStringRange 1 2) = some (.value 0) := by
  native_decide

/- Normalization precedes selection, and a malformed source preserves computation poison. -/
example :
    checkedResultOf (surfaceStringRange 3 3)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "1\r\n2")))) = some (.value 2) ∧
      checkedResultOf (surfaceStringRange 2 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "A😀B")))) = some (.value 0) ∧
      checkedResultOf (surfaceStringRange 1 1)
        (context (code := formalCheck { kind := .string }
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Direct rounding and absolute value reuse the range source and ordinary numeric wrapper evaluator, including clean missing zero and exact poison. -/
example :
    let rounded := .round .halfUp omittedRoundingPlaces (surfaceStringRange 1 2)
    let absolute := .abs (surfaceStringRange 1 2)
    let filled := context (code := formalCheck { kind := .string }
      (.parsed (.str "12X")))
    let malformed := context (code := formalCheck { kind := .string }
      (.rejected .malformed))
    checkedResultOf rounded filled = some (.value 12) ∧
      checkedResultOf absolute filled = some (.value 12) ∧
      checkedResultOf rounded = some (.value 0) ∧
      checkedResultOf absolute = some (.value 0) ∧
      checkedResultOf rounded malformed = some (.poison .malformed) ∧
      checkedResultOf absolute malformed = some (.poison .malformed) := by
  native_decide

/- The checked atom is an ordinary numeric-expression source and reaches the existing target checker without a range-specific write path. -/
example :
    let input := context
      (checkedNumber (.parsed (.num 3)))
      (code := formalCheck { kind := .string } (.parsed (.str "12X")))
    checkedResultOf
        (.binary .add (surfaceStringRange 1 2)
          (surfaceField ["Root"] "Source")) input = some (.value 15) ∧
      checkedTargetResultOf (surfaceStringRange 1 2) false targetPolicy input =
        some (.supported (.accepted { unscaled := 12, scale := 0 })) := by
  native_decide

/- Static range diagnostics preserve field-shape → interval → String-kind precedence. -/
example :
    checkedErrorOf
        (.atom (.stringRange (surfacePath ["Root"] "Missing") 0 2)) =
      some (.resolve (.invalidEntity (surfacePath ["Root"] "Missing"))) ∧
    checkedErrorOf (.atom (.stringRange (surfacePath ["Root"] "Source") 0 2)) =
      some (.invalidStringRange 0 2) ∧
    checkedErrorOf (.atom (.stringRange (surfacePath ["Root"] "Source") 1 2)) =
      some (.rangeOperandNotString ["Root", "Source"]) := by
  native_decide


end A12Kernel.Conformance.NumericComputation.Conversion
