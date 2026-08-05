import A12Kernel.Elaboration.TemporalValuesNotUnique

/-! # `FieldValuesNotUnique` conformance locks over the temporal overload

Two axes are separated here, because the temporal arm differs from its Number and token siblings in exactly two places. **Admission** keys on the declared format string rather than the kind, so the matrix has to fail a kind-equality reading in both directions. **Identity** is the exact stored text, so the matrix has to fail a decoded-value reading where the two disagree.

Everything else is inherited rather than restated: the ordered fused scan, the skip of empty and formally unavailable cells alike, and the positional filter escalation are locked once over the Number overload.
-/

namespace A12Kernel.Conformance.TemporalValuesNotUnique

open A12Kernel

/-- A full DATE declaration. -/
private def dateField (id : FieldId) (name : String) (format : String) :
    FlatFieldDecl := {
  id
  groupPath := ["Form"]
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format }
}

/-- A DATE_FRAGMENT declaration: the same `.date` kind with a partial mode, which is how the
    kernel's fragment kind surfaces at this flat boundary. -/
private def fragmentField (id : FieldId) (name : String) (format : String) :
    FlatFieldDecl := {
  dateField id name format with
    temporalTargetPolicy := some { format, partialMode := .yearOptional }
}

private def timeField (id : FieldId) (name : String) (format : String) :
    FlatFieldDecl := {
  id
  groupPath := ["Form"]
  name
  policy := { kind := .temporal .time TemporalComponents.now }
  temporalTargetPolicy := some { format }
}

private def stringField (id : FieldId) (name : String) : FlatFieldDecl :=
  { id, groupPath := ["Form"], name, policy := { kind := .string },
    stringPolicy := { lineBreaksPermitted := true } }

/-- A Boolean declaration, which the Kernel refuses by kind rather than by category. -/
private def booleanField : FlatFieldDecl :=
  { id := 10, groupPath := ["Form"], name := "Flag",
    policy := { kind := .boolean } }

/-- A temporal declaration carrying no declared format at all, which this operator needs and
    therefore refuses to default. -/
private def formatlessField : FlatFieldDecl :=
  { id := 9, groupPath := ["Form"], name := "Formatless",
    policy := { kind := .temporal .date TemporalComponents.fullDate } }

private def model : FlatModel := {
  fields := [
    dateField 1 "Start" "dd.MM.yyyy",
    dateField 2 "End" "dd.MM.yyyy",
    dateField 3 "Other" "yyyy-MM-dd",
    dateField 4 "Year" "yyyy",
    fragmentField 5 "YearFragment" "yyyy",
    timeField 6 "Clock" "HH:mm:ss",
    stringField 7 "Code",
    stringField 8 "Alternate",
    formatlessField,
    booleanField]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def source? (first second : String) :
    Option (CheckedTemporalValuesNotUniqueSource model) :=
  (elaborateTemporalValuesNotUniqueSource model ["Form"]
    { first := .field (bare first), rest := [.field (bare second)] }).toOption

private def error? (first second : String) :
    Option TemporalValuesNotUniqueElabError :=
  match elaborateTemporalValuesNotUniqueSource model ["Form"]
      { first := .field (bare first), rest := [.field (bare second)] } with
  | .error error => some error
  | .ok _ => none

private def diagnostic? (first second : String) :
    Option KernelStaticDiagnostic :=
  (error? first second).bind TemporalValuesNotUniqueElabError.diagnostic?

private def tripleDiagnostic? (first second third : String) :
    Option KernelStaticDiagnostic :=
  match elaborateTemporalValuesNotUniqueSource model ["Form"]
      { first := .field (bare first)
        rest := [.field (bare second), .field (bare third)] } with
  | .error error => error.diagnostic?
  | .ok _ => none

/-! ## Admission keys on the format, not the kind -/

/- Two DATE fields of the same kind, differing only in declared format, are **refused**. This is the
   row that kills a kind-equality reading of the gate: under kind equality these two are identical
   and would be admitted. -/
example : (source? "Start" "Other").isNone = true := by
  native_decide

/- A DATE beside a DATE_FRAGMENT sharing one format is **admitted**. This row does *not* separate
   format equality from kind equality at this boundary, because the kernel's fragment kind surfaces
   here as the same `.date` policy distinguished only by its partial mode. What it does kill is the
   next-nearest rival — a gate comparing the whole declared temporal policy rather than its format —
   which would refuse this pair over the differing partial mode. The kernel admits it. -/
example : (source? "Year" "YearFragment").isSome = true := by
  native_decide

/- Two operands of one declared format are admitted, and the certificate exposes that format. -/
example :
    (source? "Start" "End").map (·.format) = some "dd.MM.yyyy" := by
  native_decide

/- A cross-temporal list is refused by the same format rule rather than by a separate kind rule, so
   the refusal reports mixed formats. This is what places Time inside the temporal category rather
   than outside it: it is not rejected for being a Time. -/
example :
    error? "Start" "Clock" =
      some (.mixedDeclaredFormats ["Form", "Clock"] "HH:mm:ss" "dd.MM.yyyy") := by
  native_decide

/- A non-temporal operand of an admissible kind is a category mismatch, reported with the offending
   kind in either operand position, and it is a different refusal from a format mismatch. -/
example :
    error? "Start" "Code" = some (.mixedCategories ["Form", "Code"] .string) ∧
    error? "Code" "Start" = some (.mixedCategories ["Form", "Code"] .string) := by
  native_decide

/- A temporal operand whose declaration carries no format fails closed rather than defaulting to
   some format, because both the gate and the compared identity need the exact declared format. -/
example :
    error? "Start" "Formatless" =
      some (.missingDeclaredFormat ["Form", "Formatless"]) := by
  native_decide

/- The shared shape's rules still apply: a single direct operand is refused, and a repeated direct
   field is refused, neither of which is a temporal rule. -/
example :
    (elaborateTemporalValuesNotUniqueSource model ["Form"]
      { first := .field (bare "Start"), rest := [] }).toOption.isNone = true ∧
    (elaborateTemporalValuesNotUniqueSource model ["Form"]
      { first := .field (bare "Start")
        rest := [.field (bare "Start")] }).toOption.isNone = true := by
  native_decide

/-! ## The compared identity is the exact stored text -/

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (year month day : Nat) : TemporalValue :=
  .date { epochMillis := 0 }
    { year := (year : Int), month, day } .storedGregorian

/-- One placed temporal cell: its stored text and its decoded value are supplied independently, so a
    case can hold the decoded value fixed while varying the text. -/
private def temporalCell (field : FieldId) (stored : String)
    (value : TemporalValue) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw := .parsed (.temporal value) }

private def rejectedCell (field : FieldId) (stored : String) :
    ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw := .rejected .malformed }

private def presentEmptyCell (field : FieldId) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := "", raw := .presentEmpty }

private def verdict? (first second : String)
    (cells : List ClassifiedCellInput) : Option Verdict := do
  let source ← source? first second
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption
  (CheckedTemporalValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
    source document []).toOption

/- Equal stored texts duplicate; distinct stored texts do not. -/
example :
    verdict? "Start" "End"
        [temporalCell 1 "01.02.2020" (dateValue 2020 2 1),
          temporalCell 2 "01.02.2020" (dateValue 2020 2 1)] =
      some (.fired .value) ∧
    verdict? "Start" "End"
        [temporalCell 1 "01.02.2020" (dateValue 2020 2 1),
          temporalCell 2 "02.02.2020" (dateValue 2020 2 2)] =
      some .notFired := by
  native_decide

/- The separator against a decoded-value account. Two cells carrying the **same decoded date** under
   two **distinct stored texts** do not duplicate, because the stored text is what is compared. A
   decoded-value reading fires here. Whether such a pair is storable in a real model is the
   unmeasured residual under `SPEC-2026-08-05-03`; this case pins which account the clause states,
   not that the kernel admits the input. -/
example :
    verdict? "Start" "End"
        [temporalCell 1 "01.02.2020" (dateValue 2020 2 1),
          temporalCell 2 "1.2.2020" (dateValue 2020 2 1)] =
      some .notFired := by
  native_decide

/- Its converse pins the same seam from the other side: two cells with **equal stored text** but
   different decoded values still duplicate. Together the pair shows the comparison reads the text
   and nothing else, which a case on agreeing text and value could not show. -/
example :
    verdict? "Start" "End"
        [temporalCell 1 "01.02.2020" (dateValue 2020 2 1),
          temporalCell 2 "01.02.2020" (dateValue 1999 12 31)] =
      some (.fired .value) := by
  native_decide

/- The cross-kind admitted list compares the same way: a DATE and a DATE_FRAGMENT sharing a format
   duplicate on equal stored text. This is the evaluation half of the admission discriminator above. -/
example :
    verdict? "Year" "YearFragment"
        [temporalCell 4 "2020" (dateValue 2020 1 1),
          temporalCell 5 "2020" (dateValue 2020 1 1)] =
      some (.fired .value) := by
  native_decide

/- Absent, present-empty, and formally unavailable cells are skipped alike, exactly as on the Number
   overload, so a duplicate beside one still fires and two equal *unavailable* texts are not a
   duplicate at all. The stored text of a rejected cell is deliberately never compared. -/
example :
    verdict? "Start" "End" [] = some .notFired ∧
    verdict? "Start" "End"
        [temporalCell 1 "01.02.2020" (dateValue 2020 2 1),
          presentEmptyCell 2] = some .notFired ∧
    verdict? "Start" "End"
        [rejectedCell 1 "01.02.2020", rejectedCell 2 "01.02.2020"] =
      some .notFired := by
  native_decide

/-! ## Kernel diagnostic classes, and the gate order that selects them

The Kernel runs two independent gates and **the kind gate runs first**. That order is observable
because the pre-empted code is measured *absent*, not merely because one code appears.
-/

/- An inadmissible kind and a category mismatch are different Kernel classes, so they must not
   collapse into one local refusal. -/
example :
    diagnostic? "Start" "Flag" =
      some .onlyStringEnumNumberDateAllowed ∧
    diagnostic? "Start" "Code" = some .varyingTypesNotAllowed := by
  native_decide

/- The temporal format rule reports the **kind** code rather than a format-specific one, both for two
   temporal operands whose formats disagree and for a cross-temporal list. -/
example :
    diagnostic? "Start" "Other" =
      some .onlyStringEnumNumberDateAllowed ∧
    diagnostic? "Start" "Clock" =
      some .onlyStringEnumNumberDateAllowed := by
  native_decide

/- Below the required arity, the class is the arity code. -/
example :
    (match elaborateTemporalValuesNotUniqueSource model ["Form"]
        { first := .field (bare "Start"), rest := [] } with
     | .error error => error.diagnostic?
     | .ok _ => none) = some .paramSizeInvalidN := by
  native_decide

/- **Gate order.** With an inadmissible Boolean authored *after* a category-mismatched String, the
   Kernel still reports the kind code and measures the mixing code absent. A fail-fast elaborator
   walking operands in authored order reports the String's category mismatch instead, which is the
   wrong class for a legal-model consumer to act on. Both orders must therefore answer with the kind
   code. -/
example :
    tripleDiagnostic? "Start" "Code" "Flag" =
      some .onlyStringEnumNumberDateAllowed ∧
    tripleDiagnostic? "Start" "Flag" "Code" =
      some .onlyStringEnumNumberDateAllowed := by
  native_decide

end A12Kernel.Conformance.TemporalValuesNotUnique
