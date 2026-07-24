import A12Kernel.Elaboration.NumberEntityValueList

/-! # Checked mixed Number entity-list value-list locks -/

namespace A12Kernel.Conformance.NumberEntityValueList

open A12Kernel

private def matchField : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Match"
    policy := { kind := .number { scale := 0, signed := false } } }

private def otherField : FlatFieldDecl :=
  { matchField with id := 2, name := "Other" }

private def needleField : FlatFieldDecl :=
  { matchField with id := 3, name := "Needle" }

private def spareField : FlatFieldDecl :=
  { matchField with id := 4, name := "Spare" }

private def repeatedField : FlatFieldDecl :=
  { matchField with
    id := 5
    groupPath := ["Form", "Rows"]
    name := "Amount"
    repeatableScope := [10] }

private def nestedField : FlatFieldDecl :=
  { matchField with
    id := 6
    groupPath := ["Form", "Rows", "Details"]
    name := "NestedAmount"
    repeatableScope := [10, 20] }

private def model : FlatModel :=
  { fields := [
      matchField, otherField, needleField, spareField, repeatedField, nestedField]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows", "Details"],
        repeatability := some 2 }] }

private def world : World := { now := { epochMillis := 0 } }

private def direct (name : String) : SurfaceNumberEntityOperand :=
  .field { base := .absolute, groups := ["Form"], field := name }

private def star : SurfaceNumberEntityOperand :=
  .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Amount" }

private def nestedChildStar : SurfaceNumberEntityOperand :=
  .star {
    base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows" },
      { name := "Details", starred := true }]
    field := "NestedAmount" }

private def rowsPath : SurfaceGroupPath :=
  { base := .absolute, groups := ["Form", "Rows"] }

private def falseHaving : SurfaceCorrelatedHaving :=
  .compareRepetitions .less
    { origin := .inner, group := .path rowsPath }
    { origin := .inner, group := .path rowsPath }

private def filteredStar : SurfaceNumberEntityOperand :=
  .starHaving {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Amount" } falseHaving

private def entitySource (first : SurfaceNumberEntityOperand)
    (rest : List SurfaceNumberEntityOperand) : SurfaceNumberEntitySource :=
  { first, rest }

private def authored (quantifier : ValueListQuantifier)
    (fields values : SurfaceNumberEntitySource) :
    SurfaceNumberEntityValueListSource :=
  { quantifier, fields, values }

private def row1 : RowAddr := { group := 10, path := [1] }

private inductive RepeatedFixture where
  | seven
  | presentEmpty
  | malformed

private def RepeatedFixture.stored : RepeatedFixture → String
  | .seven => "7"
  | .presentEmpty => ""
  | .malformed => "bad"

private def RepeatedFixture.raw : RepeatedFixture → RawCell
  | .seven => .parsed (.num 7)
  | .presentEmpty => .presentEmpty
  | .malformed => .rejected .malformed

private def data (repeated : RepeatedFixture) : DocumentData :=
  { instantiatedRows := [row1]
    cells := [
      { address := { field := 1, path := [] }
        stored := "5", raw := .parsed (.num 5) },
      { address := { field := 2, path := [] }
        stored := "7", raw := .parsed (.num 7) },
      { address := { field := 3, path := [] }
        stored := "5", raw := .parsed (.num 5) },
      { address := { field := 4, path := [] }
        stored := "9", raw := .parsed (.num 9) },
      { address := { field := 5, path := [1] }
        stored := repeated.stored
        raw := repeated.raw }] }

private def checkedDocument? (source : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" source).toOption

private def values : SurfaceNumberEntitySource :=
  entitySource (direct "Needle") [direct "Spare"]

private inductive Snapshot where
  | verdict (verdict : Verdict)
  | structural (cause : CheckedAddressingError)
  | elaboration
  deriving Repr, DecidableEq

private def fullSnapshot (surface : SurfaceNumberEntityValueListSource)
    (source : DocumentData) (outer : Env := []) : Snapshot :=
  match elaborateNumberEntityValueListSource model ["Form"] surface with
  | .error _ => .elaboration
  | .ok checked =>
      match checkedDocument? source with
      | none => .elaboration
      | some document =>
          match checked.evaluateFull document outer with
          | .ok verdict => .verdict verdict
          | .error cause => .structural cause

private def relevance (path : List String)
    (indices : List RelevanceIndex) : RelevantEntityPattern :=
  { path, indices }

private def directOnlyScope : ValidationRelevanceScope :=
  .partialSet [
    relevance matchField.path [.concrete 1, .concrete 1],
    relevance needleField.path [.concrete 1, .concrete 1],
    relevance spareField.path [.concrete 1, .concrete 1]]

private def partialSnapshot (surface : SurfaceNumberEntityValueListSource)
    (source : DocumentData) : Snapshot :=
  match elaborateNumberEntityValueListSource model ["Form"] surface with
  | .error _ => .elaboration
  | .ok checked =>
      match checkedDocument? source with
      | none => .elaboration
      | some document =>
          match checked.evaluatePartial document [] directOnlyScope with
          | .ok (.evaluated verdict) => .verdict verdict
          | .ok .skippedHaving => .elaboration
          | .error cause => .structural cause

/- A fields-side `No` match hides a later semantic UNKNOWN, while reversing the same operands exposes it. -/
example :
    fullSnapshot
        (authored .no
          (entitySource (direct "Match") [star]) values)
        (data .malformed) = .verdict .notFired ∧
      fullSnapshot
        (authored .no
          (entitySource star [direct "Match"]) values)
        (data .malformed) = .verdict .unknown := by
  native_decide

/- A filtered nonwitness before an unfiltered witness does not escalate the deciding match to OMISSION. -/
example :
    fullSnapshot
        (authored .atLeastOne
          (entitySource filteredStar [direct "Match"]) values)
        (data .seven) = .verdict (.fired .value) := by
  native_decide

/- Partial nonrelevance remains attached to its authored operand position for the ordered `No` scan. -/
example :
    partialSnapshot
        (authored .no
          (entitySource (direct "Match") [star]) values)
        (data .seven) = .verdict .notFired ∧
      partialSnapshot
        (authored .no
          (entitySource star [direct "Match"]) values)
        (data .seven) = .verdict .unknown := by
  native_decide

/- A missing fixed outer binding is a structural addressing failure, never semantic UNKNOWN. -/
example :
    fullSnapshot
        (authored .no
          (entitySource nestedChildStar [direct "Match"]) values)
        { instantiatedRows := [], cells := (data .presentEmpty).cells.take 4 } =
      .structural (.addressing (.missingBinding 10)) := by
  native_decide

private inductive OperandShape where
  | direct
  | star
  | filteredStar
  deriving Repr, DecidableEq

private def operandShape :
    CheckedNumberEntityOperand model → OperandShape
  | .field _ => .direct
  | .star _ => .star
  | .starHaving _ => .filteredStar

private def operandField :
    CheckedNumberEntityOperand model → FieldId
  | .field source => source.field.id
  | .star source => source.field.id
  | .starHaving source => source.source.field.id

private structure OperandView where
  shape : OperandShape
  field : FieldId
  topology : Option (List Env)
  addressed : List (CellAddr × Option String)
  deriving Repr, DecidableEq

private def operandView
    (resolved : ResolvedCheckedNumberEntityOperand model) : OperandView :=
  { shape := operandShape resolved.source
    field := operandField resolved.source
    topology := resolved.topology.map (·.environments)
    addressed := resolved.addressedCells.map fun cell =>
      (cell.address, cell.stored) }

private structure ConsumerView where
  fields : List OperandView
  values : List OperandView
  verdict : Verdict
  deriving Repr, DecidableEq

private inductive ConsumerQuery where
  | numberValueList (surface : SurfaceNumberEntityValueListSource)
      (source : DocumentData)
  | tokenValueList

private inductive ConsumerResult where
  | available (view : ConsumerView)
  | structural (cause : CheckedAddressingError)
  | rejected
  | insufficientInformation
  deriving Repr, DecidableEq

/-- The same-context Execute/Transform/Explain probe consumes only the public checked route. It can execute the verdict, traverse source-preserving operand boundaries, and explain topology, selected addresses, and exact stored payload. Unsupported token metadata is reported as insufficient instead of guessed. -/
private def inspectForConsumer : ConsumerQuery → ConsumerResult
  | .tokenValueList => .insufficientInformation
  | .numberValueList surface source =>
      match elaborateNumberEntityValueListSource model ["Form"] surface with
      | .error _ => .rejected
      | .ok checked =>
          match checkedDocument? source with
          | none => .rejected
          | some document =>
              match checked.resolveFull document [] with
              | .error cause => .structural cause
              | .ok resolved =>
                  .available {
                    fields := resolved.fields.map operandView
                    values := resolved.values.map operandView
                    verdict := resolved.evaluate }

/- The consumer sees the filtered operand's complete candidate topology but no selected cell, then the direct deciding witness. Flattening would erase that distinction and cannot satisfy this query. -/
example :
    inspectForConsumer (.numberValueList
      (authored .atLeastOne
        (entitySource filteredStar [direct "Match"]) values)
      (data .seven)) =
      .available {
        fields := [
          { shape := .filteredStar
            field := 5
            topology := some [[(10, 1)]]
            addressed := [] },
          { shape := .direct
            field := 1
            topology := none
            addressed := [({ field := 1, path := [] }, some "5")] }]
        values := [
          { shape := .direct
            field := 3
            topology := none
            addressed := [({ field := 3, path := [] }, some "5")] },
          { shape := .direct
            field := 4
            topology := none
            addressed := [({ field := 4, path := [] }, some "9")] }]
        verdict := .fired .value } ∧
      inspectForConsumer .tokenValueList =
        .insufficientInformation := by
  native_decide

end A12Kernel.Conformance.NumberEntityValueList
