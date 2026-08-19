import A12Kernel.Elaboration.DateRangeConstructionComputation

/-! # Checked DateRange construction computation locks -/

namespace A12Kernel.Conformance.DateRangeConstructionComputation

open A12Kernel

private def dateField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "yyyy-MM-dd"
    partialMode := .full
  }
}

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (format : String := "dd.MM.yyyy") (separator : String := "-")
    (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id
  groupPath
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
  repeatableScope := scope
}

private def start := dateField 1 "Start"
private def finish := dateField 2 "Finish"
private def target := rangeField 3 ["Order"] "Window"
private def isoTarget :=
  rangeField 4 ["Order"] "IsoWindow" "yyyy-MM-dd" "/"
private def fragmentTarget :=
  rangeField 9 ["Order"] "YearWindow" "yyyy" "/"
private def yearMonthTarget :=
  rangeField 10 ["Order"] "YearMonthWindow" "yyyy-MM" "/"
private def wrongGroupTarget := rangeField 5 ["Elsewhere"] "OtherWindow"
private def repeatedTarget :=
  rangeField 6 ["Order", "Rows"] "RepeatedWindow" "dd.MM.yyyy" "-" [10]
private def fragmentStart : FlatFieldDecl := {
  dateField 7 "FragmentStart" with
  temporalTargetPolicy := some {
    format := "yyyy"
    partialMode := .yearOptional
  }
}
private def fragmentFinish : FlatFieldDecl := {
  fragmentStart with id := 8, name := "FragmentFinish"
}

private def model : FlatModel := {
  fields := [start, finish, target, isoTarget, wrongGroupTarget,
    repeatedTarget, fragmentStart, fragmentFinish, fragmentTarget,
    yearMonthTarget]
  repeatableGroups := [{ level := 10, path := ["Order", "Rows"] }]
  timeZoneId := "UTC"
}

private def dateValue (epochMillis : Int) (year : Int)
    (month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def startValue := dateValue 1717200000000 2024 6 1
private def finishValue := dateValue 1719705600000 2024 6 30
private def fragmentStartValue := dateValue 1704067200000 2024 1 1
private def fragmentFinishValue := dateValue 1735689600000 2025 1 1

private def expectedStored : StoredDateRange := {
  text := "01.06.2024-30.06.2024"
  nonempty := by decide
}

private def expectedInvertedStored : StoredDateRange := {
  text := "30.06.2024-01.06.2024"
  nonempty := by decide
}

private def expectedIsoStored : StoredDateRange := {
  text := "2024-06-01/2024-06-30"
  nonempty := by decide
}

private def expectedIsoInvertedStored : StoredDateRange := {
  text := "2024-06-30/2024-06-01"
  nonempty := by decide
}

private def expectedYearStored : StoredDateRange := {
  text := "2024/2025"
  nonempty := by decide
}

private def expectedYearInvertedStored : StoredDateRange := {
  text := "2025/2024"
  nonempty := by decide
}

private def inputCell (field : FlatFieldDecl) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field := field.id, path := [] }
  stored
  raw
}

private def checkedInputFor? (startField finishField : FlatFieldDecl)
    (startStored finishStored : String)
    (startRaw finishRaw : RawCell) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      inputCell startField startStored startRaw,
      inputCell finishField finishStored finishRaw
    ]
  }).toOption

private def operationFor? (target start finish : FlatFieldDecl) :=
  (elaborateDateRangeConstructionComputation model ["Order"]
    target.id start.id finish.id).toOption

private def operation? := operationFor? target start finish

private def executeFor? (target start finish : FlatFieldDecl)
    (startStored finishStored : String)
    (startRaw finishRaw : RawCell) :
    Option DateRangeConstructionComputationResult := do
  let input ← checkedInputFor? start finish startStored finishStored
    startRaw finishRaw
  let operation ← operationFor? target start finish
  (operation.execute input).toOption

private def execute? := executeFor? target start finish

private def executeFragment? :=
  executeFor? fragmentTarget fragmentStart fragmentFinish

/- Full-Date constructions reach both exact targets, and matching year fragments reach the year target. -/
example :
    (elaborateDateRangeConstructionComputation model ["Order"] target.id
      start.id finish.id).isOk = true ∧
    (elaborateDateRangeConstructionComputation model ["Order"] isoTarget.id
      start.id finish.id).isOk = true ∧
    (elaborateDateRangeConstructionComputation model ["Order"] fragmentTarget.id
      fragmentStart.id fragmentFinish.id).isOk = true := by
  native_decide

/- Unsupported target profiles, component mismatch, direct placement, declaring group, and target kind remain separate static gates. -/
example :
    (match elaborateDateRangeConstructionComputation model ["Order"]
        yearMonthTarget.id fragmentStart.id fragmentFinish.id with
      | .error (.targetFormat .yearMonthFragment) => true
      | _ => false) &&
    (match elaborateDateRangeConstructionComputation model ["Order"]
        fragmentTarget.id start.id finish.id with
      | .error (.endpointFormat (.full _) (.full _)) => true
      | _ => false) &&
    (match elaborateDateRangeConstructionComputation model ["Order"]
        target.id fragmentStart.id fragmentFinish.id with
      | .error (.endpointFormat .yearFragment .yearFragment) => true
      | _ => false) &&
    (match elaborateDateRangeConstructionComputation model ["Order"]
        repeatedTarget.id start.id finish.id with
      | .error (.target (.source (.repeatableReference path))) =>
          path == repeatedTarget.path
      | _ => false) &&
    (match elaborateDateRangeConstructionComputation model ["Order"]
        wrongGroupTarget.id start.id finish.id with
      | .error (.targetGroup actual expected) =>
          actual == ["Elsewhere"] && expected == ["Order"]
      | _ => false) &&
    (match elaborateDateRangeConstructionComputation model ["Order"] start.id
        start.id finish.id with
      | .error (.target (.sourceNotDateRange source (.temporal .date))) =>
          source == start.id
      | _ => false) = true := by
  native_decide

/- The second exact target policy renders the same typed endpoints through ISO/slash and preserves inversion errors. -/
example :
    (executeFor? isoTarget start finish "2024-06-01" "2024-06-30"
      (.parsed (.temporal (.date startValue)))
      (.parsed (.temporal (.date finishValue)))).map (·.outcome) =
        some (.accepted expectedIsoStored) ∧
    (executeFor? isoTarget start finish "2024-06-30" "2024-06-01"
      (.parsed (.temporal (.date finishValue)))
      (.parsed (.temporal (.date startValue)))).map (·.outcome) =
        some (.errored expectedIsoInvertedStored .inverted) := by
  native_decide

/- Year fragments complete by endpoint position, then render only the declared year labels while retaining inversion as a target error. -/
example :
    executeFragment? "2024" "2025"
      (.parsed (.temporal (.date fragmentStartValue)))
      (.parsed (.temporal (.date fragmentFinishValue))) = some {
        construction := {
          start := .value (.exact fragmentStartValue)
          finish := .value (.exact {
            instant := { epochMillis := 1767139200000 }
            parts := { year := 2025, month := 12, day := 31 }
            basis := .storedGregorian
          })
        }
        outcome := .accepted expectedYearStored
      } ∧
    (executeFragment? "2025" "2024"
      (.parsed (.temporal (.date fragmentFinishValue)))
      (.parsed (.temporal (.date fragmentStartValue)))).map (·.outcome) =
        some (.errored expectedYearInvertedStored .inverted) := by
  native_decide

/- Filled endpoints retain their exact observations and render through the target declaration rather than either source label. -/
example :
    execute? "2024-06-01" "2024-06-30"
      (.parsed (.temporal (.date startValue)))
      (.parsed (.temporal (.date finishValue))) = some {
      construction := {
        start := .value (.exact startValue)
        finish := .value (.exact finishValue)
      }
      outcome := .accepted expectedStored
    } := by
  native_decide

/- Formal unavailability dominates emptiness; ordinary emptiness clears through the existing target application. -/
example :
    (execute? "" "2024-06-30" .presentEmpty
      (.parsed (.temporal (.date finishValue)))).map (·.outcome) =
        some .noValue ∧
    (execute? "bad" "" (.rejected .malformed) .presentEmpty).map
      (·.outcome) = some (.poison .malformed) ∧
    (DateRangeTargetOutcome.accepted expectedStored).applyTo .presentEmpty =
      .presentValue expectedStored ∧
    DateRangeTargetOutcome.noValue.applyTo
      (.presentValue expectedStored) = .presentEmpty := by
  native_decide

/- An inverted construction retains its rendered attempt and is rejected by the target basic check. -/
example :
    execute? "2024-06-30" "2024-06-01"
      (.parsed (.temporal (.date finishValue)))
      (.parsed (.temporal (.date startValue))) = some {
        construction := {
          start := .value (.exact finishValue)
          finish := .value (.exact startValue)
        }
        outcome := .errored expectedInvertedStored .inverted
      } ∧
    (DateRangeTargetOutcome.errored expectedInvertedStored .inverted).applyTo
        (.presentValue expectedStored) = .presentEmpty := by
  native_decide

end A12Kernel.Conformance.DateRangeConstructionComputation
