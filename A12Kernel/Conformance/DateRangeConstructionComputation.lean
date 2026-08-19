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
    repeatedTarget, fragmentStart, fragmentFinish]
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
private def rangeValue : DateRangeValue := {
  start := startValue
  finish := finishValue
}

private def expectedStored : StoredDateRange := {
  text := "01.06.2024-30.06.2024"
  nonempty := by decide
}

private def expectedInvertedStored : StoredDateRange := {
  text := "30.06.2024-01.06.2024"
  nonempty := by decide
}

private def inputCell (field : FlatFieldDecl) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field := field.id, path := [] }
  stored
  raw
}

private def checkedInput? (startStored finishStored : String)
    (startRaw finishRaw : RawCell) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      inputCell start startStored startRaw,
      inputCell finish finishStored finishRaw,
      inputCell target "01.06.2024-30.06.2024"
        (.parsed (.dateRange (.exact rangeValue)))
    ]
  }).toOption

private def operation? :=
  (elaborateDateRangeConstructionComputation model ["Order"] target.id
    start.id finish.id).toOption

private def execute? (startStored finishStored : String)
    (startRaw finishRaw : RawCell) :
    Option DateRangeConstructionComputationResult := do
  let input ← checkedInput? startStored finishStored startRaw finishRaw
  let operation ← operation?
  (operation.execute input).toOption

/- The measured full-Date construction and dotted/dash target are admitted through one checked model. -/
example :
    (elaborateDateRangeConstructionComputation model ["Order"] target.id
      start.id finish.id).isOk = true := by
  native_decide

/- Target presentation, direct placement, declaring group, and full-Date endpoint precision remain separate static gates. -/
example :
    (match elaborateDateRangeConstructionComputation model ["Order"]
        isoTarget.id start.id finish.id with
      | .error (.targetFormat (.exact .isoSlash)) => true
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
      | _ => false) &&
    (match elaborateDateRangeConstructionComputation model ["Order"] target.id
        fragmentStart.id fragmentFinish.id with
      | .error (.endpointFormat .yearFragment .yearFragment) => true
      | _ => false) = true := by
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
